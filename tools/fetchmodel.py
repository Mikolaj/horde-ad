"""What align-as.py and the fetch probes share, kept once so a fix lands once.

Imported by align-as.py, probe-fetch-model.py and probe-entries-sweep.py,
never run: each puts its own directory first on sys.path, as for
common.py.

block_rules is the front end's cost of a loop's cycle at a head offset, as
probe-fetch-model.py fits it to the machine and align-as.py charges it when
it places a head. build and counts are the probes' harness: a kernel
assembled at a head offset, and its perf counters over one process.
"""

import os
import re
import subprocess
import sys
import tempfile

# The first of a pair the decoder fuses with the conditional jump after it:
# GHC's assembly writes the suffixed forms, objdump the bare ones.
FUSABLE = {'cmp', 'test', 'add', 'sub', 'and', 'or', 'xor', 'inc', 'dec',
           'cmpq', 'cmpl', 'testq', 'testl', 'addq', 'addl', 'subq', 'subl',
           'andq', 'andl', 'orq', 'orl', 'xorq', 'xorl', 'incq', 'incl',
           'decq', 'decl'}
HEAD_TAIL = 8             # a head this close to the line's end pays a cycle
REGS = ['%rcx', '%rdx', '%rsi', '%r8', '%r9', '%r10', '%r11', '%r12',
        '%r13', '%r14', '%r15', '%rbx']


def is_cond(mn):
    # jmp with an operand-size suffix, LLVM's jmpq, is no conditional branch
    # either.
    return mn.startswith('j') and not re.fullmatch(r'jmp[qlw]?', mn)


def prepared(segs, at_head=None):
    """The per-segment figures `block_rules` needs at every residue, taken
    once: instruction starts, ends and mnemonics, the op count less fused
    pairs, and the taken branch's own bytes. SEGS are lists of (start, end,
    mnemonic) from the head, each ending in its taken branch, every branch
    inside it not taken; AT_HEAD holds the indices of those entered at the
    head, the first non-empty one where it is None. A build prices 1874
    heads at 64 residues each, so what is per segment and not per residue is
    done here -- 419 of 452 seconds went to redoing it, profiled
    2026-09-15."""
    out = []
    for n, seg in enumerate(segs):
        if not seg:
            continue
        starts = [s for s, _, _ in seg]
        ends = [e for _, e, _ in seg]
        mns = [m for _, _, m in seg]
        fusedpairs = sum(1 for x, y in zip(mns, mns[1:])
                         if x in FUSABLE and y.startswith('j'))
        last = mns[-1]
        fused = len(seg) >= 2 and mns[-2] in FUSABLE and is_cond(last)
        prev = [k for k in range(len(seg) - 1) if mns[k].startswith('j')
                and not (fused and k == len(seg) - 2)]
        out.append(dict(starts=starts, ends=ends, mns=mns,
                        ops=len(seg) - fusedpairs, last=last, fused=fused,
                        pair_start=starts[-2] if fused else starts[-1],
                        prev_end=ends[prev[-1]] if prev else None,
                        head=not out if at_head is None else n in at_head))
    return out


def block_rules(segs, r):
    """-> (ops, blocks, whole, half, predicted cycles) of a cycle placed
    with its head at residue R, SEGS being `prepared`'s.

    Whole-cycle penalties, the rules the sweeps of 2026-09-15 bear out in
    every regime: `cut`, a segment's taken conditional branch, or the fused
    pair it belongs to, astride a line boundary or in a different line from
    the segment's previous predicted branch; `head`, the loop head within
    HEAD_TAIL bytes of its line's end, charged on the segments entered at
    the head alone, a tail or re-entry entered that close to its line's
    end paying only the empty block.
    Half ones: a last block with three or fewer instructions starting in its
    line, a block holding only an unconditional jump, and a quarter for an
    unfused taken conditional. A first instruction astride the boundary adds
    the empty block it leaves. Predicted cycles are max(ops / 6, blocks)
    plus the penalties, whole where the fetch bounds the loop and halved
    where the dispatcher does: the 64-byte straight loop pays 0.5 at a cut
    its 3.5-cycle dispatch floor absorbs, the fill pays 1 at 4 blocks over a
    3.67 floor.
    """
    ops, blocks, whole, half = 0, 0, 0, 0.0
    for sg in segs:
        ends, starts = sg['ends'], sg['starts']
        ops += sg['ops']
        lines = {(r + e - 1) >> 6 for e in ends}
        blocks += len(lines)
        if (r + starts[0]) >> 6 != (r + ends[0] - 1) >> 6:
            blocks += 1                              # the empty block left
        if sg['head'] and r % 64 >= 64 - HEAD_TAIL:
            whole += 1                               # a head near the end
        last_line = (r + ends[-1] - 1) >> 6
        whole_in_last = 0
        for n in range(len(ends) - 1, -1, -1):
            if (r + ends[n] - 1) >> 6 != last_line:
                break
            if (r + starts[n]) >> 6 == last_line:
                whole_in_last += 1
        last = sg['last']
        if is_cond(last):
            lb = r + ends[-1] - 1
            cut = (r + sg['pair_start']) >> 6 != lb >> 6
            if not cut and sg['prev_end'] is not None:
                cut = (r + sg['prev_end'] - 1) >> 6 != lb >> 6
            if cut:
                whole += 1
            if not sg['fused']:
                half += 0.5
            if len(lines) > 1 and whole_in_last <= 3 and not cut:
                half += 1
        elif last == 'jmp' and whole_in_last <= 1:
            half += 1
    floor = max(ops / 6.0, blocks)
    w = 1.0 if blocks >= ops / 6.0 else 0.5
    return ops, blocks, whole, half, floor + w * (whole + half / 2.0)


def die(msg):
    """Exit 2 -- did not run -- rather than `sys.exit(str)`'s 1, which is
    the code a finding gets (2026-09-25, by review)."""
    sys.stderr.write(msg.rstrip('\n') + '\n')
    sys.exit(2)


def build(tmp, asm, cmain, k, prog):
    """-> the binary for head offset k, or None with the error printed,
    under PROG's name."""
    s, c, b = (os.path.join(tmp, f) for f in ('k.S', 'main.c', 'k%d' % k))
    with open(s, 'w') as f:
        f.write(asm)
    with open(c, 'w') as f:
        f.write(cmain)
    got = subprocess.run(['gcc', '-O1', '-DK=%d' % k, c, s, '-o', b],
                         capture_output=True, text=True)
    if got.returncode:
        print('%s: gcc failed at K=%d: %s'
              % (prog, k, got.stderr.strip().split('\n')[-1]), file=sys.stderr)
        return None
    return b


def counts(binary, arg, events):
    """The counters of EVENTS, comma-separated, over one process, or None
    when perf did not count every one."""
    with tempfile.NamedTemporaryFile(delete=False) as f:
        out = f.name
    ran = subprocess.run(['perf', 'stat', '-x,', '-e', events, '-o', out,
                          binary, str(arg)], stdout=subprocess.DEVNULL,
                         stderr=subprocess.DEVNULL)
    if ran.returncode:
        os.unlink(out)
        return None
    vals = []
    with open(out) as f:
        for line in f:
            p = line.split(',')
            if len(p) > 3 and p[0].strip().isdigit():
                vals.append(int(p[0]))
    os.unlink(out)
    return vals if len(vals) == len(events.split(',')) else None
