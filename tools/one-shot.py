#!/usr/bin/env python3
"""Recompile one module of a cabal build alone, with GHC flags added.

Usage: python3 tools/one-shot.py LOG MODULE OUTDIR [--cwd DIR] [-- FLAG...]
       python3 tools/one-shot.py --self-test

LOG is what `cabal build -v2` printed for a build that compiled MODULE, a
module name or a source path; DIR is the package directory GHC ran in,
the current directory by default. The script takes GHC and its arguments
for MODULE's component from LOG --- the `--make` invocation naming MODULE
that does not link --- and runs GHC in one-shot mode (`-c`) on MODULE alone
with every FLAG after `--` appended: the other modules' interfaces are read
as that build left them, so a flag's effect on one module costs one
module's compilation, not a component's: one of orthotope's test modules
alone took 83 s where its whole build took seven and a half minutes, and
gave the build's Core to the term.

Nothing of the build is written to: its output directories are mirrored
under OUTDIR/out, every file a symlink but MODULE's own outputs, which GHC
writes afresh there. Dumps go to OUTDIR/dump (pass `-ddump-to-file` with
the dump flags), GHC's output to OUTDIR/ghc.txt, its RTS statistics, which
give its allocation and peak memory, to OUTDIR/rts.txt, and the command run
to OUTDIR/command.txt. The wall time is printed. OUTDIR is created; an
existing one is emptied only if an earlier run made it, its `.one-shot`
marker saying so.

Exit 0 when MODULE compiled, 2 when it did not or could not be tried: LOG
unreadable or without GHC's `Running: ... --numeric-version` line, no
invocation or more than one naming MODULE, its source in no `-i` directory,
an OUTDIR some other program made, or GHC failing, its output in ghc.txt.
"""

import os
import re
import shlex
import shutil
import subprocess
import sys
import time

MARKER = '.one-shot'
OUT_FLAGS = ('-outputdir', '-odir', '-hidir', '-hiedir', '-stubdir')
# Flags whose value is the next argument, so that a value that looks like a
# module name is not taken for a target.
ARG_FLAGS = set(OUT_FLAGS) | {
    '-dumpdir', '-this-unit-id', '-package-db', '-package-id', '-package',
    '-hide-package', '-ignore-package', '-o', '-dynosuf', '-dynhisuf',
    '-osuf', '-hisuf', '-pgmc', '-pgml', '-pgma', '-pgmP', '-main-is', '-x',
    '-working-dir', '-package-env', '-ghcversion-file', '-trust', '-distrust'}
MODNAME = re.compile(r"[A-Z][\w']*(?:\.[A-Z][\w']*)*$")
OWN = ('.o', '.hi', '.dyn_o', '.dyn_hi', '.p_o', '.p_hi', '.hie', '_stub.h')


def targets(args):
    """Indices of the module names and source files GHC is asked to build."""
    out = []
    for i, a in enumerate(args):
        if a.startswith('-') or (i and args[i - 1] in ARG_FLAGS):
            continue
        if MODNAME.match(a) or a.endswith(('.hs', '.lhs')):
            out.append(i)
    return out


def invocation(log, module):
    """(ghc, args) of the one compiling invocation naming module, or a
    reason why there is none."""
    m = re.search(r'^Running: (\S+) --numeric-version$', log, re.M)
    if not m:
        return None, "the log has no 'Running: GHC --numeric-version' line"
    found = []
    for line in log.split('\n'):
        if not line.startswith('GHC response file arguments: '):
            continue
        args = shlex.split(line[len('GHC response file arguments: '):])
        names = [args[i] for i in targets(args)]
        if '--make' in args and '-o' not in args and module in names:
            found.append(args)
    if len(found) != 1:
        return None, (f'{len(found)} compiling invocations in the log name '
                      f'{module}; one is needed')
    return (m.group(1), found[0]), None


def source(args, module, cwd):
    """MODULE's source file, a target path or found in the -i directories."""
    if module.endswith(('.hs', '.lhs')):
        return module if os.path.exists(os.path.join(cwd, module)) else None
    rel = module.replace('.', '/')
    for a in args:
        if a.startswith('-i') and len(a) > 2:
            for ext in ('.hs', '.lhs'):
                p = os.path.join(a[2:], rel + ext)
                if os.path.exists(os.path.join(cwd, p)):
                    return p
    return None


def mirror(src, dst, module):
    """dst a tree of symlinks to src's files, but module's own outputs."""
    rel = module.replace('.', '/')
    own = {rel + e for e in OWN}
    for dp, _, fs in os.walk(src):
        here = os.path.relpath(dp, src)
        os.makedirs(os.path.join(dst, here), exist_ok=True)
        for f in fs:
            r = os.path.normpath(os.path.join(here, f))
            if r not in own:
                os.symlink(os.path.join(dp, f), os.path.join(dst, r))


def prepare(args, module, outdir):
    """The arguments for `ghc -c` on module: targets and --make dropped, the
    output directories mirrored and replaced, the dump directory redirected."""
    tgt = set(targets(args))
    args = [a for i, a in enumerate(args)
            if i not in tgt and a not in ('--make', '-no-link')]
    dirs = {args[i + 1] for i, a in enumerate(args[:-1]) if a in OUT_FLAGS}
    for n, d in enumerate(sorted(dirs, key=len, reverse=True)):
        new = os.path.join(outdir, 'out', str(n))
        mirror(d, new, module)
        args = [new + a[len(d):] if a == d or a.startswith(d + '/')
                else '-i' + new + a[2 + len(d):]
                if a == '-i' + d or a.startswith('-i' + d + '/')
                else a for a in args]
    dump = os.path.join(outdir, 'dump') + '/'
    if '-dumpdir' in args:
        args[args.index('-dumpdir') + 1] = dump
    else:
        args += ['-dumpdir', dump]
    return args


def run(logpath, module, outdir, cwd, extra):
    try:
        with open(logpath, errors='replace') as fh:
            log = fh.read()
    except OSError as e:
        return f'cannot read {logpath}: {e}', None
    found, why = invocation(log, module)
    if why:
        return why, None
    ghc, args = found
    src = source(args, module, cwd)
    if src is None:
        return f'no source of {module} under {cwd} in the -i directories', None
    if os.path.exists(outdir) and os.listdir(outdir):
        if not os.path.exists(os.path.join(outdir, MARKER)):
            return (f'{outdir} exists and no earlier run of this script '
                    'made it; name a new directory'), None
        shutil.rmtree(outdir)
    os.makedirs(os.path.join(outdir, 'dump'), exist_ok=True)
    open(os.path.join(outdir, MARKER), 'w').close()
    args = prepare(args, module, outdir)
    rts = '-s' + os.path.join(outdir, 'rts.txt')
    cmd = [ghc, '-c'] + args + extra + [src, '+RTS', rts, '-RTS']
    with open(os.path.join(outdir, 'command.txt'), 'w') as fh:
        fh.write(shlex.join(cmd) + '\n')
    t0 = time.monotonic()
    with open(os.path.join(outdir, 'ghc.txt'), 'w') as fh:
        r = subprocess.run(cmd, cwd=cwd, stdout=fh, stderr=subprocess.STDOUT)
    secs = time.monotonic() - t0
    if r.returncode != 0:
        return (f'GHC exited {r.returncode} on {module}; its output is in '
                f'{os.path.join(outdir, "ghc.txt")}'), None
    return None, secs


def self_test():
    """A fake GHC that records its arguments and writes the object it is
    asked for, and a log of a library and a test suite, each compiled and
    linked."""
    import json
    import tempfile
    bad = []
    with tempfile.TemporaryDirectory() as td:
        pkg, lib, tst = (os.path.join(td, x)
                         for x in ('pkg', 'libout', 'tstout'))
        for d in (os.path.join(pkg, 'src', 'A'), os.path.join(pkg, 'tests'),
                  os.path.join(lib, 'A'), tst):
            os.makedirs(d)
        for f in ('src/A/B.hs', 'src/M.hs', 'tests/T.hs', 'tests/Views.hs',
                  'tests/Tests.hs'):
            open(os.path.join(pkg, f), 'w').close()
        for f in ('A/B.o', 'A/B.hi', 'A/B.dyn_hi', 'M.hi'):
            open(os.path.join(lib, f), 'w').close()
        for f in ('T.o', 'T.hi', 'Views.hi', 'Views.o'):
            open(os.path.join(tst, f), 'w').close()
        fake = os.path.join(td, 'ghc')
        with open(fake, 'w') as fh:
            fh.write('#!' + sys.executable + '\n'
                     'import json, os, sys\n'
                     'a = sys.argv[1:]\n'
                     'if "-fail-please" in a: sys.exit(1)\n'
                     'src = [x for x in a if x.endswith(".hs")][-1]\n'
                     'odir = a[a.index("-odir") + 1]\n'
                     'inc = [x[2:] for x in a if x.startswith("-i")'
                     ' and len(x) > 2 and src.startswith(x[2:] + "/")][0]\n'
                     'rel = src[len(inc) + 1:-3]\n'
                     'obj = os.path.join(odir, rel + ".o")\n'
                     'os.makedirs(os.path.dirname(obj), exist_ok=True)\n'
                     'open(obj, "w").write(json.dumps(a))\n')
        os.chmod(fake, 0o755)
        common = (f'-i -isrc -outputdir {lib} -odir {lib} -hidir {lib}'
                  ' -dynosuf dyn_o')
        tcommon = (f'-i -itests -i{tst} -outputdir {tst} -odir {tst}'
                   f' -hidir {tst} -dumpdir /old/dump/ -main-is Main')
        tests = 'Views T tests/Tests.hs'
        rf = 'GHC response file arguments:'
        log = '\n'.join([
            f'Running: {fake} --numeric-version',
            f'{rf} --make -this-unit-id pkg-1 {common} A.B M',
            f'{rf} -shared -o {lib}/libpkg.so {lib}/A/B.dyn_o',
            f'{rf} --make -no-link {tcommon} {tests}',
            f'{rf} --make -o {tst}/tests {tcommon} {tests}',
            ''])
        lp = os.path.join(td, 'log.txt')
        with open(lp, 'w') as fh:
            fh.write(log)
        out = os.path.join(td, 'one')
        why, _ = run(lp, 'T', out, pkg, ['-ddump-simpl'])
        if why:
            bad.append(f'T: {why}')
        else:
            with open(os.path.join(out, 'out', '0', 'T.o')) as fh:
                got = json.load(fh)
            want_tail = ['-ddump-simpl', 'tests/T.hs', '+RTS',
                         '-s' + os.path.join(out, 'rts.txt'), '-RTS']
            if got[-5:] != want_tail or got[0] != '-c':
                bad.append(f'T: arguments {got}')
            if '--make' in got or '-no-link' in got or 'Views' in got:
                bad.append(f'T: a target or --make kept: {got}')
            dumpdir = os.path.join(out, 'dump') + '/'
            if got[got.index('-dumpdir') + 1] != dumpdir:
                bad.append('T: dump directory not redirected')
            if got[got.index('-odir') + 1] != os.path.join(out, 'out', '0'):
                bad.append('T: output directory not replaced by its mirror')
            if '-i' + os.path.join(out, 'out', '0') not in got:
                bad.append('T: the output directory as an -i path not replaced')
            if got[got.index('-main-is') + 1] != 'Main':
                bad.append('T: the value of -main-is taken for a target')
            if not os.path.islink(os.path.join(out, 'out', '0', 'Views.hi')):
                bad.append("T: another module's interface not mirrored")
            if os.path.islink(os.path.join(out, 'out', '0', 'T.hi')):
                bad.append("T: the module's own interface kept in the mirror")
            if not os.path.exists(os.path.join(tst, 'T.o')) or os.path.getsize(
                    os.path.join(tst, 'T.o')):
                bad.append("T: the build's own object written to")
        why, _ = run(lp, 'A.B', os.path.join(td, 'lib1'), pkg, [])
        if why:
            bad.append(f'A.B: {why}')
        elif os.path.islink(os.path.join(td, 'lib1', 'out', '0', 'A',
                                         'B.dyn_hi')):
            bad.append("A.B: the module's own .dyn_hi kept in the mirror")
        if not run(lp, 'Nope', os.path.join(td, 'n'), pkg, [])[0]:
            bad.append('a module no invocation names was compiled')
        if not run(lp, 'T', out, pkg, ['-fail-please'])[0]:
            bad.append('a failing GHC read as a compiled module')
        if run(lp, 'T', out, pkg, [])[0]:
            bad.append('an OUTDIR an earlier run made not reused')
        foreign = os.path.join(td, 'foreign')
        os.makedirs(foreign)
        open(os.path.join(foreign, 'keep.txt'), 'w').close()
        if not run(lp, 'T', foreign, pkg, [])[0] or not os.path.exists(
                os.path.join(foreign, 'keep.txt')):
            bad.append('an OUTDIR some other program made was emptied')
        dup = os.path.join(td, 'dup.txt')
        with open(dup, 'w') as fh:
            fh.write(log + log.split('\n')[3] + '\n')
        if not run(dup, 'T', os.path.join(td, 'd'), pkg, [])[0]:
            bad.append('two compiling invocations naming T not refused')
        nogh = os.path.join(td, 'noghc.txt')
        with open(nogh, 'w') as fh:
            fh.write('\n'.join(log.split('\n')[1:]))
        if not run(nogh, 'T', os.path.join(td, 'g'), pkg, [])[0]:
            bad.append("a log without GHC's Running line not refused")
        if main([lp, 'Nope', os.path.join(td, 'n2')]) != 2:
            bad.append('main: a module no invocation names did not exit 2')
    for b_ in bad:
        print('FAIL', b_)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    extra = []
    if '--' in argv:
        k = argv.index('--')
        argv, extra = argv[:k], argv[k + 1:]
    cwd = '.'
    if len(argv) == 5 and argv[3] == '--cwd':
        cwd, argv = argv[4], argv[:3]
    if len(argv) != 3:
        print(__doc__.split('\n\n')[1], file=sys.stderr)
        return 2
    logpath, module, outdir = argv
    why, secs = run(logpath, module, os.path.abspath(outdir), cwd, extra)
    if why:
        print(why, file=sys.stderr)
        return 2
    print(f'{module} compiled in {secs:.1f} s; dumps in {outdir}/dump, GHC '
          f'output in {outdir}/ghc.txt, RTS statistics in {outdir}/rts.txt')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
