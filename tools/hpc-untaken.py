#!/usr/bin/env python3
"""List what a run of an -fhpc build left untaken, from its `hpc draft`.

Usage: python3 tools/hpc-untaken.py DRAFT [--src DIR] [--trivial NAME]...
       python3 tools/hpc-untaken.py --self-test

`hpc draft --hpcdir=.hpc/PKG RUN.tix` prints, per module, a tick for each
function and expression the run never entered. This lists them per module:
the functions on one line, then each expression with its line and the
bindings it sits in, leaving out an error call (`error`,
`errorWithoutStackTrace`, `throw`), a type-only placeholder
`(undefined :: T)` or `(Proxy :: T)`, `coerce` and each `--trivial` NAME,
such as a newtype's field, none of which marks a path a benchmark should
take. With `--src DIR`, the directory the module names are paths under,
each expression comes with its source line. Read the draft of every run
of a benchmark combined (`hpc combine`) to see which paths of an operation
it never measures.

Exit 0 when nothing is left untaken, 1 when something is, 2 when DRAFT
holds no module or a source file is missing.
"""

import os
import re
import sys

ERR = re.compile(r'(?:error|errorWithoutStackTrace|throw)\b')
TRIV = re.compile(r'coerce|\(undefined :: [^()]*\)|\(Proxy :: .*\)')


def untaken(text, trivial=()):
    """{module: ([(line, function)], [(line, bindings, expression)])}."""
    out, mod, inside = {}, None, []
    for raw in text.split('\n'):
        s = raw.strip()
        m = re.match(r'module "[^:"]*:(\S+)" \{$', s)
        if m:
            mod, inside = m.group(1), []
            out[mod] = ([], [])
            continue
        m = re.match(r'inside "(.*)" \{$', s)
        if m:
            inside.append(m.group(1))
            continue
        if s == '}':
            if inside:
                inside.pop()
            continue
        m = re.match(r'tick function "(.*)" on line (\d+);$', s)
        if m and mod:
            name = '/'.join(inside + [m.group(1)])
            out[mod][0].append((int(m.group(2)), name))
            continue
        m = re.match(r'tick "(.*)" on line (\d+);$', s)
        if m and mod:
            e = m.group(1).replace('\\"', '"')
            if ERR.match(e) or TRIV.fullmatch(e) or e in trivial:
                continue
            out[mod][1].append((int(m.group(2)), '/'.join(inside), e))
    return out


def report(found, src=None):
    """The lines printed, or the module whose source file is missing."""
    lines = []
    for mod in sorted(found):
        fns, exs = found[mod]
        if not fns and not exs:
            continue
        lines.append('== ' + mod)
        if fns:
            lines.append('  unused functions: ' + ' '.join(
                f'{n}:{ln}' for ln, n in sorted(fns)))
        text = None
        if src and exs:
            path = os.path.join(src, mod.replace('.', '/') + '.hs')
            if not os.path.isfile(path):
                return mod
            with open(path) as fh:
                text = fh.read().split('\n')
        for ln, where, e in sorted(exs):
            row = f'  {ln:5d} {where:<28} {e[:60]}'
            if text is not None:
                row += ' | ' + (text[ln - 1].strip() if ln <= len(text)
                                else '')
            lines.append(row)
    return lines


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    src, trivial, rest = None, set(), []
    while argv:
        if argv[0] in ('--src', '--trivial') and len(argv) > 1:
            if argv[0] == '--src':
                src = argv[1]
            else:
                trivial.add(argv[1])
            argv = argv[2:]
        elif argv[0].startswith('--'):
            rest = []
            break
        else:
            rest.append(argv[0])
            argv = argv[1:]
    if len(rest) != 1 or not os.path.isfile(rest[0]):
        print(__doc__.split('\n\n')[1], file=sys.stderr)
        return 2
    with open(rest[0]) as fh:
        found = untaken(fh.read(), trivial)
    if not found:
        print(f'no module in {rest[0]}', file=sys.stderr)
        return 2
    lines = report(found, src)
    if isinstance(lines, str):
        print(f'{lines} of {rest[0]} has no source under {src}',
              file=sys.stderr)
        return 2
    print('\n'.join(lines))
    return 1 if lines else 0


def self_test():
    """A draft of two modules, nested bindings, every kind of tick left out
    and an escaped quote, read plain, with --trivial and with --src; then
    the exits of a draft with nothing untaken, of one with no module and
    of a source tree missing a module."""
    import contextlib
    import io
    import tempfile
    draft = ('module "pkg-0.1-inplace:A.B" {\n'
             '  inside "f" {\n'
             '    tick "unT" on line 3;\n'
             '    inside "go" {\n'
             '      tick "x + 1" on line 5;\n'
             '    }\n'
             '    tick "error $ \\"f: \\" ++ show n" on line 6;\n'
             '    tick "(undefined :: b)" on line 7;\n'
             '  }\n'
             '  tick "coerce" on line 8;\n'
             '  tick "show \\"q\\"" on line 9;\n'
             '  tick function "g" on line 12;\n'
             '}\n'
             'module "pkg-0.1-inplace:C" {\n'
             '  tick function "h" on line 2;\n'
             '  inside "k" {\n'
             '    tick "throw e" on line 4;\n'
             '    tick "(Proxy :: Proxy n)" on line 4;\n'
             '  }\n'
             '}\n')
    plain = ['== A.B',
             '  unused functions: g:12',
             '      3 f                            unT',
             '      5 f/go                         x + 1',
             '      9                              show "q"',
             '== C',
             '  unused functions: h:2']
    srcd = ['== A.B',
            '  unused functions: g:12',
            '      5 f/go                         x + 1 | five',
            '      9                              show "q" | nine',
            '== C',
            '  unused functions: h:2']
    bad = []
    with tempfile.TemporaryDirectory() as td:
        def run(text, *flags):
            with open(os.path.join(td, 'draft'), 'w') as fh:
                fh.write(text)
            with contextlib.redirect_stdout(io.StringIO()) as so, \
                    contextlib.redirect_stderr(io.StringIO()):
                code = main([os.path.join(td, 'draft')] + list(flags))
            return code, so.getvalue().rstrip('\n').split('\n')

        os.makedirs(os.path.join(td, 'A'))
        with open(os.path.join(td, 'A', 'B.hs'), 'w') as fh:
            fh.write('\n'.join(f'  {w}' for w in (
                'one two three four five six seven eight nine'.split())))
        for flags, want, code in (([], plain, 1),
                                  (['--trivial', 'unT', '--src', td], srcd,
                                   1)):
            got = run(draft, *flags)
            if got != (code, want):
                bad.append(f'{flags}: {got[0]}\n  ' + '\n  '.join(got[1]))
        for why, text, flags, code in (
                ('nothing untaken', 'module "p:M" {\n  tick "coerce" on'
                 ' line 1;\n}\n', [], 0),
                ('no module', 'tick "x" on line 1;\n', [], 2),
                ('a module without its source', draft, ['--src',
                                                        os.path.join(td, 'A')],
                 2)):
            if run(text, *flags)[0] != code:
                bad.append(f'{why} did not exit {code}')
    for b in bad:
        print('FAIL', b)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
