#!/usr/bin/env python3
"""Find loops that unbox, on every iteration, a value captured from outside.

Usage: python3 tools/captured-unbox.py DUMP...
       python3 tools/captured-unbox.py --self-test

Each DUMP is a `-ddump-simpl` dump made with `-dsuppress-uniques`, with or
without `-dsuppress-all`, of a client calling a library's operations at
concrete element types. In it, this finds every `case X of { B# y` --- B# any box,
`D#`, `F#`, `I#`, `W#`, `C#` or a sized one, `I8#` to `W64#` --- inside
a `joinrec` or `letrec` block, where X is not mentioned between the block's
header and the case and so is bound outside the loop: a boxed value the
loop captured and unboxes again on each iteration. Prints the top-level
binding, the loop's first binder, X, the line number and the line.

It found 908 in orthotope's `allSameT`, and `zipWithT`'s broadcast
branches and Unboxed `padT`'s padding value beside it
(docs/perf-checklist.md, L2). A hit in the client's own closures is set
aside by reading the binding it names.

Exit 0 when nothing was found, 1 when something was, 2 when a DUMP cannot
be read or holds no Tidy Core.
"""

import re
import sys

# The box with its package and module qualifiers where the dump keeps them.
BOX = re.compile(r"case ([\w$']+) of \{ (?:[\w.'-]+:)?(?:[A-Z][\w']*\.)*"
                 r"(?:[IW](?:8|16|32|64)?|D|F|C)# ")
HEADER = re.compile(r"\b(joinrec|letrec) \{\s*$")


def indent(line):
    return len(line) - len(line.lstrip(' '))


def hits(text):
    lines = text.split('\n')
    tops, top = [], None
    for line in lines:
        m = re.match(r"^[\w$'.]+", line)
        if m:
            top = m.group(0)
        tops.append(top)
    out = []
    for i, line in enumerate(lines):
        for m in BOX.finditer(line):
            x, k, hdr = m.group(1), indent(line), None
            for j in range(i - 1, -1, -1):
                lj = lines[j]
                if not lj.strip():
                    continue
                if HEADER.search(lj) and indent(lj) < k:
                    # Open iff no line in between is indented at or below it.
                    if all(indent(lines[t]) > indent(lj) or not lines[t].strip()
                           for t in range(j + 1, i)):
                        hdr = j
                        break
                if not lj.startswith(' '):
                    break
            if hdr is None:
                continue
            region = '\n'.join(lines[hdr:i]) + '\n' + line[:m.start()]
            if re.search(r"(?<![\w$'])" + re.escape(x) + r"(?![\w$'])", region):
                continue
            loop = lines[hdr + 1].split()[0] if lines[hdr + 1].split() else '?'
            out.append(f'{tops[i]}\t{loop}\t{x}\t{i + 1}\t{line.strip()[:90]}')
    return out


def self_test():
    """A dump with a captured Double and a captured Int unboxed in loops,
    the Double again with its qualifiers under a qualified binding, a loop
    unboxing its own parameter, and a case outside any loop."""
    import os
    import tempfile
    dump = ('\n==================== Tidy Core ====================\n'
            'Result size of Tidy Core\n  = {terms: 1, types: 1}\n\n'
            'allSame\n'
            '  = \\ x v ->\n'
            '      joinrec {\n'
            '        go i\n'
            '          = case x of { D# y ->\n'
            '            case i of { I# j -> jump go (I# (+# j 1#)) } }; } in\n'
            '      jump go 0\n\n'
            'countTo\n'
            '  = \\ n ->\n'
            '      letrec {\n'
            '        loop k\n'
            '          = case n of { I# m -> case k of { W8# kk -> loop k } }; } in\n'
            '      loop 0\n\n'
            'fine\n'
            '  = \\ v ->\n'
            '      joinrec {\n'
            '        go2 acc\n'
            '          = case acc of { W8# w -> jump go2 acc }; } in\n'
            '      jump go2 v\n\n'
            'outside = \\ z -> case z of { I# k -> k }\n\n'
            'Client.qual\n'
            '  = \\ x ->\n'
            '      joinrec {\n'
            '        go3 i\n'
            '          = case x of { ghc-internal:GHC.Internal.Types.D# y ->\n'
            '            jump go3 i }; } in\n'
            '      jump go3 0\n')
    bad = []
    with tempfile.TemporaryDirectory() as td:
        p, q = os.path.join(td, 'Client.dump-simpl'), os.path.join(td, 'none')
        with open(p, 'w') as fh:
            fh.write(dump)
        with open(q, 'w') as fh:
            fh.write('no Core here\n')
        got = hits(dump)
        want = ['allSame\tgo\tx\t10\t= case x of { D# y ->',
                'countTo\tloop\tn\t18\t= case n of { I# m -> case k of '
                '{ W8# kk -> loop k } }; } in',
                'Client.qual\tgo3\tx\t34\t= case x of { '
                'ghc-internal:GHC.Internal.Types.D# y ->']
        if got != want:
            bad.append('hits:\n  ' + '\n  '.join(got))
        if main([p]) != 1:
            bad.append('hits did not exit 1')
        if main([q]) != 2:
            bad.append('a file without Tidy Core did not exit 2')
    for b in bad:
        print('FAIL', b)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    if not argv or any(a.startswith('--') for a in argv):
        print(__doc__.split('\n\n')[1], file=sys.stderr)
        return 2
    found = 0
    for path in argv:
        try:
            with open(path, errors='replace') as fh:
                text = fh.read()
        except OSError as e:
            print(f'cannot read {path}: {e.strerror}', file=sys.stderr)
            return 2
        if 'Tidy Core' not in text:
            print(f'{path} holds no Tidy Core; was it made with -ddump-simpl?',
                  file=sys.stderr)
            return 2
        for h in hits(text):
            print(f'{path}\t{h}')
            found += 1
    return 1 if found else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
