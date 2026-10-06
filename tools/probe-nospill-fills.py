#!/usr/bin/env python3
"""Read the LLVM build's own loops for a named fill, and say whether they spill.

Written for orthotope's micro-regime3 benchmark and kept there until
2026-10-06, so the -fllvm build, its dumps and the arms named below are that
directory's, at
https://github.com/Mikolaj/orthotope/tree/speedup-strided-tovector/micro-regime3

Exit 2 on usage or an input this cannot read, 0 otherwise -- the
convention every script in this directory keeps.

The -fllvm build carries neither .debug_line nor per-worker symbols, so a
fill cannot be found in it the way loop-offsets.py finds one in a native
build.  What it does carry is GHC's block uniques: every basic block
reaches the assembler as `_blk_Q<unique>$def`, and the same uniques label
the blocks of the -ddump-cmm dump, where the procs are named.  So the map
from an arm to its loops is: the dump's proc names give a line range, the
range gives a set of uniques, and the uniques select blocks in the .s.

Both inputs come from ONE recipe and that recipe's binary reproduces byte
for byte with either dump flag added (measured 2026-08-30, three builds,
md5 a341a984fe2d24a7f3286975a6b18490 throughout), so the assembly read
here is the timed binary's and not a twin's -- which is what a -g3 twin
could not have given, GHC's LLVM backend emitting no line table under -g3.

A self-loop is a block whose last transfer targets its own label.  For
each one it prints the instruction count, the loads and stores of doubles,
and the accesses through Sp (%rbp) and the C stack (%rsp), which is what
"spill-free" is a claim about.

    ./probe-nospill-fills.py CMMDUMP ASM ARM [ARM ...]

The arm is the Haskell binding's name, e.g. fbMutOdoVecdimsAddInLeafU2.
A proc's nested workers ($wgo, $wrun) carry no such name, so the range is
taken from the first mention of the arm's worker to the first mention of
the next arm's, which is how GHC clusters them in the dump; the range's
own bounds are printed so a wrong one is visible rather than silent.
"""
import re
import sys


def die(msg):
    """Exit 2 -- did not run -- rather than `sys.exit(str)`'s 1, which is
    the code a finding gets."""
    sys.stderr.write(msg.rstrip('\n') + '\n')
    sys.exit(2)


WORKER = re.compile(r'\$w(fb[A-Za-z0-9]+)_')


def procs_of(dump, arms):
    """line ranges, in dump order, one per arm named

    The bound is the next ARM'S start and not the next NAMED one: the
    workers of an arm not asked about would otherwise be attributed to
    whichever named arm precedes them, which is silent and wrong -- and
    `fbMutOdoVecdimsAddInLeafU2Down` sits between the two arms this was
    written for.  So every `$wfb*` in the dump delimits, and only the
    ranges asked for are returned.
    """
    # The delimiters are the `fb*` fills PLUS whatever was asked for, and
    # not every `$w` in the dump: a nested worker (`$wgo`, `$wrun`) belongs
    # to the binding above it and must not cut the range that binding's
    # loops live in. `fillStage2` is the case that made this explicit --
    # it is a fill and carries no `fb` prefix.
    starts = {}
    for i, ln in enumerate(dump):
        for m in WORKER.finditer(ln):
            starts.setdefault(m.group(1), i)
        for a in arms:
            if a not in starts and ('$w' + a + '_') in ln:
                starts[a] = i
    order = sorted(starts.items(), key=lambda kv: kv[1])
    out = {}
    for k, (a, s) in enumerate(order):
        if a in arms:
            out[a] = (s, order[k + 1][1] if k + 1 < len(order) else len(dump))
    return out


LBL = re.compile(r'^\s*(Q[A-Za-z0-9]+):')
# TWO BACKENDS, TWO LABEL FORMS, and the same uniques under both. LLVM
# emits one `_blk_Q<unique>$def` symbol per Cmm block and cuts it into
# `.LBB` blocks of its own; the native code generator emits `.LQ<unique>`
# per Cmm block and no sub-blocks at all, so under it every self-loop is
# one Cmm block jumping to itself. Both are matched here because the
# question the script answers -- which loop does this arm run, and what
# does it touch -- is the same question on either.
ASM_LBL = re.compile(r'^(?:_blk_(Q[A-Za-z0-9]+)\$def|\.L(Q[A-Za-z0-9]+)):')
JMP = re.compile(r'^\s+j\w+\s+(?:_blk_(Q[A-Za-z0-9]+)\$def'
                 r'|(\.LBB[0-9_]+)|\.L(Q[A-Za-z0-9]+))')
SUB_LBL = re.compile(r'^(\.LBB[0-9_]+):')
# A function's entry region -- everything from its `Q<unique>_info$def`
# label to its first `_blk_` label -- belongs to that function's own
# worker, and LLVM's loop rotation is what puts the hot loop there. It
# is owned here by the proc's unique, which the dump carries in the
# proc header (`..._Q<unique>_entry()`) and never as a block label.
# Case: `fills-entry-region-goes-to-the-previous-proc`.
FUNC_LBL = re.compile(r'^(?:[\w$]+_)?(Q[A-Za-z0-9]+)_info\$def:')
PROC = re.compile(r'(Q[A-Za-z0-9]+)_entry\(\)')


def cycles(mine, blocks, order_asm):
    """the loops among these blocks, smallest first

    The native code generator does not leave a loop in one block the way
    LLVM's rotation does -- a `go` level is a header that tests and a body
    that jumps back -- so a self-loop finder reports nothing at all on it,
    which is what this reads as "no loop" and is not. Tarjan over the jump
    graph, plus fallthrough where a block does not end in an unconditional
    transfer, finds the loop whatever it is cut into.
    """
    idx = {b: i for i, b in enumerate(order_asm)}
    mineset = set(mine)
    succ = {}
    for b in mine:
        out = set()
        body = blocks[b]
        for ln in body:
            m = JMP.search(ln)
            if m:
                t = m.group(1) or m.group(2) or m.group(3)
                if t in mineset:
                    out.add(t)
        last = [l for l in body if l.startswith('\t')]
        ends = last and re.match(r'\s+(jmp|ret|ud2)\b', last[-1])
        if not ends and b in idx and idx[b] + 1 < len(order_asm):
            nxt = order_asm[idx[b] + 1]
            if nxt in mineset:
                out.add(nxt)
        succ[b] = out
    # Tarjan, iterative
    index, low, onstk, stack, out, counter = {}, {}, set(), [], [], [0]
    for root in mine:
        if root in index:
            continue
        work = [(root, iter(sorted(succ[root])))]
        index[root] = low[root] = counter[0]; counter[0] += 1
        stack.append(root); onstk.add(root)
        while work:
            v, it = work[-1]
            adv = False
            for w in it:
                if w not in index:
                    index[w] = low[w] = counter[0]; counter[0] += 1
                    stack.append(w); onstk.add(w)
                    work.append((w, iter(sorted(succ[w]))))
                    adv = True
                    break
                if w in onstk:
                    low[v] = min(low[v], index[w])
            if adv:
                continue
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[v])
            if low[v] == index[v]:
                comp = []
                while True:
                    w = stack.pop(); onstk.discard(w); comp.append(w)
                    if w == v:
                        break
                if len(comp) > 1 or v in succ[v]:
                    out.append(sorted(comp, key=lambda b: idx.get(b, 0)))
    return sorted(out, key=len)


def main():
    if len(sys.argv) < 4:
        die(__doc__)
    dump = open(sys.argv[1]).read().splitlines()
    asm = open(sys.argv[2]).read().splitlines()
    arms = sys.argv[3:]
    ranges = procs_of(dump, arms)
    missing = [a for a in arms if a not in ranges]
    if missing:
        die('not in the dump: ' + ', '.join(missing))

    # LLVM lowers each Cmm block to a `_blk_Q<unique>$def` symbol and then
    # cuts it into `.LBB` blocks of its own, so a loop is a .LBB block and
    # never the `_blk_` one -- which is why the split below tracks both and
    # attributes each .LBB to the `_blk_` it sits under.
    blocks, owner, order_asm = {}, {}, []
    cur = own = None
    for ln in asm:
        m = ASM_LBL.match(ln) or FUNC_LBL.match(ln)
        m2 = SUB_LBL.match(ln)
        if m:
            own = cur = m.group(1) or (m.group(2) if m.re is ASM_LBL
                                        else None)
            blocks[cur] = []
            owner[cur] = own
            order_asm.append(cur)
        elif m2:
            cur = m2.group(1)
            blocks[cur] = []
            owner[cur] = own
            order_asm.append(cur)
        elif (ln.strip().startswith(('.section', '.size'))
              or re.match(r'^[A-Za-z_$][^\s:]*:', ln)):
            # The directives are tab-indented, so an unstripped test never
            # fired and ownership leaked from one function into the next.
            cur = own = None
        elif cur is not None:
            blocks[cur].append(ln)

    for a in arms:
        s, e = ranges[a]
        want = {m.group(1) for ln in dump[s:e] if (m := LBL.match(ln))}
        want |= {m.group(1) for ln in dump[s:e]
                 for m in PROC.finditer(ln)}
        print(f'{a}: dump lines {s + 1}..{e}, {len(want)} Cmm block(s), '
              f'{len([b for b in owner.values() if b in want])} assembly '
              f'block(s) under them')
        found = 0
        mine = [b for b in order_asm if owner.get(b) in want]
        loops = cycles(mine, blocks, order_asm)
        for grp in loops:
            body = [ln for q in grp for ln in blocks[q]]
            q = ' + '.join(grp) if len(grp) > 1 else grp[0]
            found += 1
            ins = [ln for ln in body
                   if ln.startswith('\t') and not ln.lstrip().startswith('.')]
            ld = sum(1 for ln in ins if re.search(r'movsd\s+[^,]*\(', ln))
            st = sum(1 for ln in ins if re.search(r'movsd\s+%xmm[0-9]+, ', ln))
            sp = sum(1 for ln in ins if '(%rbp)' in ln or re.search(r'\(%rbp,', ln))
            cs = sum(1 for ln in ins if '(%rsp)' in ln or re.search(r'\(%rsp,', ln))
            print(f'    {owner[grp[0]]}/{q}: {len(ins):3d} instructions, '
                  f'{ld} double load(s), {st} double store(s), '
                  f'Sp(%rbp) {sp}, C stack(%rsp) {cs}')
        if not found:
            print('    no loop found under this arm')
        print()


main()
