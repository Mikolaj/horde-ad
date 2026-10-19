#!/usr/bin/env python3
"""A census of orthotope's specialisation benchmark: the cells two builds
count differently by instructions a call, chosen from what their Core and
their tables say moved, counted with tools/perf-per-call.py, and read.

Usage: python3 tools/census.py cells ROWS FORCED SUMMED OUT
       python3 tools/census.py movers FORCED_A FORCED_B SUMMED_A SUMMED_B OUT
       python3 tools/census.py count [--cpus LIST] [--reps R]
                                     BIN_A BIN_B FORCED SUMMED CELLS OUT
       python3 tools/census.py read COUNTS [COUNTS ...]
       python3 tools/census.py noise [--cpus LIST] [--reps R]
                                     BIN_A BIN_B OUT COUNTS [COUNTS ...]
       python3 tools/census.py --self-test

A table is the benchmark's of one build, of its forced functions (FORCED)
or its summing ones (SUMMED): a line per row `Family/op/size/view` with six
figures, the time of each kind, boxed, Storable and Unboxed, in ns, then
its bytes, an element at the size `large` and a call at the others, `-`
where the kind has no such row. A cell is a row and a kind,
`Family/op/size/view/kind`, and a cells file lists one a line, a line
`summed` switching the cells after it to the summing function.

cells writes to OUT the cells of the rows that tools/row-core.py's `rows`
output ROWS marks `differs` in its full verdicts, the forced function's
and the summing one's, those of each the table has, a family being a
module's name without its `Ops`; a row marked `literals` is not counted,
nor one UNMATCHED, whose number is printed. movers writes the cells whose
bytes differ between the two builds' tables.

count counts each cell of CELLS with perf-per-call at N and 2N calls of
BIN_A and BIN_B, the two builds' benchmark executables, N such that N calls
take about 20 ms by A's table of the cell's mode, at least 10 and at most
300000, no call taken to cost under 100 ns, which a time rounded to 0.00
hides; a summed cell runs through a script, written for the run, passing
`--summed`. It appends a line to OUT as each cell is counted, tab-separated:
mode, cell, N, instructions a call of A and of B, B/A to four decimals and
perf-per-call's exit (1 where a build's repetitions spread over 1%), or `-`
for the three figures and then the tool's output where it printed none.
Cells already in OUT are skipped, so a count interrupted resumes.
`--cpus` splits the cells over lanes, one a CPU, every run of a lane
pinned to its CPU (`2,3,4,5`, four on separate cores, in the study this
was written for); `--reps` is perf-per-call's. Differences between N and 2N
calls are what perf-per-call reports, so the two runs the harness makes of
a row before its batch of N, which lift one run's count over N by (N + 2)/N,
cancel.

read summarises count files: the cells counted, those whose count failed
and those whose repetitions spread, the cells whose B/A moves by 0.2% or
more either way, a ratio exactly at 0.2% included, and a line per group of
operation, kind, size, family (Shaped apart, Dynamic and Ranked together)
and mode: the moving cells over the cells counted, the range of their
change a call and per cent, and their views where fewer than nine. Then,
apart, the moving cells counted over fewer than 200 calls in groups not
every cell of which moves, the shape a census's noise has taken, to be
counted again; noise counts them again at ten times N, five repetitions
unless `--reps` says otherwise, and writes a line per cell to OUT: mode,
cell, `exit` and perf-per-call's exit, and its output.

Exit 0 when the work was done and printed, read 1 when some cell is to be
counted again, its count failed or it is listed apart, and 2 when the run
did not happen: an input missing or unreadable, a cell absent from the
table that sizes it, tables of two builds whose rows differ, or, for count
and noise, any cell whose count printed no figures, the other cells' lines
written.
"""

import collections
import contextlib
import io
import os
import re
import shlex
import subprocess
import sys
import tempfile
import threading
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
# The self-test points it at the fakes' PATH; the tool itself is the real one.
PER_CALL = os.path.join(HERE, 'perf-per-call.py')

KINDS = ('boxed', 'Storable', 'Unboxed')
LETTERS = {'B': 0, 'S': 1, 'U': 2}
# The table's time of a large row is an element's, of 400 by 500.
LARGE = 200000
SIZES = {'small': '[3,3]', 'large': '[400,500]', 'empty': 'empty'}
# A ratio moves at 0.2% either way, one printed exactly at it included.
MOVE = 0.002 - 1e-12
FEW = 200


class Unreadable(Exception):
    """The run cannot happen; the message says why."""


def lines_of(path):
    try:
        with open(path) as fh:
            return fh.read().split('\n')
    except OSError as e:
        raise Unreadable(f'{path}: {e.strerror}')


def table(path):
    """Row -> its six figures as written."""
    t = {}
    for line in lines_of(path):
        f = line.split()
        if len(f) == 7 and '/' in f[0]:
            t[f[0]] = f[1:]
    if not t:
        raise Unreadable(f'{path} has no table row')
    return t


def cell_parts(cell):
    """(row, kind index) of a cell, or Unreadable."""
    row, _, kind = cell.rpartition('/')
    if kind not in KINDS or row.count('/') != 3:
        raise Unreadable(f'{cell!r} is not a cell `Family/op/size/view/kind`')
    return row, KINDS.index(kind)


def cells_file(path):
    """[(mode, cell)] of a cells file."""
    out, mode = [], 'forced'
    for line in lines_of(path):
        c = line.strip()
        if c == 'summed':
            mode = 'summed'
        elif c:
            cell_parts(c)
            out.append((mode, c))
    if not out:
        raise Unreadable(f'{path} lists no cell')
    return out


def write_cells(path, forced, summed):
    with open(path, 'w') as fh:
        fh.write('\n'.join(forced) + '\nsummed\n' + '\n'.join(summed) + '\n')


def cells(rows, forced, summed, out):
    tabs = {'forced': table(forced), 'summed': table(summed)}
    res, marked, unmatched = {'forced': [], 'summed': []}, 0, 0
    for line in lines_of(rows):
        f = line.split('\t')
        if len(f) == 5 and f[4].startswith('UNMATCHED'):
            unmatched += 1
        if len(f) < 8 or not f[0].startswith('Ops') or f[2] not in LETTERS:
            continue
        family, size, k, op = f[0][3:], f[1], LETTERS[f[2]], f[3]
        moved = {'forced': f[6] == 'differs', 'summed': f[7] == 'differs'}
        marked += any(moved.values())
        for mode, t in tabs.items():
            if moved[mode]:
                res[mode] += [f'{r}/{KINDS[k]}' for r in t
                              if r.startswith(f'{family}/{op}/{size}/')
                              and r.count('/') == 3 and t[r][k + 3] != '-']
    write_cells(out, res['forced'], res['summed'])
    return [f'{rows}: {marked} rows differ, {unmatched} unmatched left out;'
            f' cells {len(res["forced"])} forced, {len(res["summed"])} summed,'
            f' written to {out}']


def movers(fa, fb, sa, sb, out):
    res = {}
    for mode, pa, pb in (('forced', fa, fb), ('summed', sa, sb)):
        x, y = table(pa), table(pb)
        if set(x) != set(y):
            raise Unreadable(f'{pa} and {pb} list different rows,'
                             f' {len(x)} and {len(y)}: an unfinished table?')
        res[mode] = [f'{r}/{KINDS[k]}' for r in x for k in range(3)
                     if x[r][k + 3] != '-' and y[r][k + 3] != x[r][k + 3]]
    write_cells(out, res['forced'], res['summed'])
    return [f'{len(res["forced"])} forced and {len(res["summed"])} summed'
            f' cells whose bytes differ, written to {out}']


def calls(tab, cell):
    """N such that N calls take about 20 ms by the table."""
    row, k = cell_parts(cell)
    if row not in tab or tab[row][k] == '-':
        raise Unreadable(f'no time of {cell} in the table')
    ns = float(tab[row][k]) * (LARGE if row.split('/')[2] == 'large' else 1)
    return max(10, min(300000, int(2e7 / max(ns, 100))))


def wrappers(td, bins):
    """The two binaries as their modes run them: as they are, and through a
    script passing --summed."""
    out = {'forced': tuple(bins), 'summed': []}
    for label, b in zip('AB', bins):
        w = os.path.join(td, f'{label}-summed')
        with open(w, 'w') as fh:
            fh.write(f'#!/bin/sh\nexec {shlex.quote(os.path.abspath(b))}'
                     ' --summed "$@"\n')
        os.chmod(w, 0o755)
        out['summed'].append(w)
    out['summed'] = tuple(out['summed'])
    return out


def per_call(bins, cell, n, cpu, reps):
    """(perf-per-call's exit, its output, instructions A and B or None)."""
    cmd = ([sys.executable, PER_CALL] + (['--cpu', cpu] if cpu else [])
           + (['--reps', str(reps)] if reps else [])
           + list(bins) + [cell, str(n)])
    r = subprocess.run(cmd, capture_output=True, text=True)
    ins = re.findall(r'instructions ([\d.]+)', r.stdout)
    figures = (float(ins[0]), float(ins[1])) if len(ins) >= 2 else None
    return r.returncode, (r.stdout + r.stderr).replace('\n', ' '), figures


def lanes(todo, cpus, work):
    """Run work(item, cpu) over todo, the items split over one lane a CPU
    (one unpinned lane without cpus); True where every call returned
    True. A call that raises counts as False and its lane goes on, where
    the lane's thread would end and leave its other items undone."""
    cpus = cpus or [None]
    ok = []

    def lane(j, cpu):
        for x in todo[j::len(cpus)]:
            try:
                ok.append(work(x, cpu))
            except Exception as e:
                print(f'census: {x}: {type(e).__name__}: {e}',
                      file=sys.stderr)
                ok.append(False)
    ts = [threading.Thread(target=lane, args=(j, c))
          for j, c in enumerate(cpus)]
    for t in ts:
        t.start()
    for t in ts:
        t.join()
    return all(ok)


def count(bins, forced, summed, cells_path, out, cpus, reps):
    tabs = {'forced': table(forced), 'summed': table(summed)}
    want = cells_file(cells_path)
    sized = {(m, c): calls(tabs[m], c) for m, c in want}
    done = set()
    if os.path.exists(out):
        done = {tuple(line.split('\t')[:2]) for line in lines_of(out)}
    todo = [mc for mc in want if mc not in done]
    if not todo:
        return [f'all {len(want)} cells of {cells_path} are in {out}'], 0
    lock = threading.Lock()
    with tempfile.TemporaryDirectory() as td, open(out, 'a') as fo:
        run = wrappers(td, bins)

        def work(mc, cpu):
            mode, cell = mc
            n = sized[mc]
            rc, text, fig = per_call(run[mode], cell, n, cpu, reps)
            if fig and fig[0] > 0:
                line = (f'{mode}\t{cell}\t{n}\t{fig[0]}\t{fig[1]}'
                        f'\t{fig[1] / fig[0]:.4f}\t{rc}')
            else:
                line = f'{mode}\t{cell}\t{n}\t-\t-\t-\t{rc}\t{text[:300]}'
            with lock:
                fo.write(line + '\n')
                fo.flush()
            return fig is not None and fig[0] > 0
        ok = lanes(todo, cpus, work)
    return [f'{len(todo)} cells counted into {out}'
            + ('' if ok else ', some without figures')], 0 if ok else 2


def counts(paths):
    """(counted rows, failed rows) of count files."""
    rows, bad = [], []
    for p in paths:
        for k, line in enumerate(lines_of(p), 1):
            if not line:
                continue
            r = line.split('\t')
            try:
                if len(r) < 7 or r[0] not in ('forced', 'summed'):
                    raise ValueError
                cell_parts(r[1])
                int(r[2])
                if r[5] == '-':
                    bad.append(r)
                else:
                    float(r[3]), float(r[4]), float(r[5])
                    rows.append(r)
            except (ValueError, Unreadable):
                raise Unreadable(f'{p}:{k}: not a count line: {line[:80]!r}')
    if not rows and not bad:
        raise Unreadable('no count line in ' + ' '.join(paths))
    return rows, bad


def group(r):
    fam, op, size, view, kind = r[1].split('/')
    return (op, kind, SIZES.get(size, size), 'Sh' if fam == 'Shaped' else 'DR',
            r[0])


def few_calls(rows):
    """The moving cells counted over fewer than FEW calls in groups not
    every cell of which moves."""
    g, n = collections.defaultdict(list), collections.Counter()
    for r in rows:
        n[group(r)] += 1
        if abs(float(r[5]) - 1) >= MOVE:
            g[group(r)].append(r)
    return g, n, [r for k in sorted(g) if len(g[k]) < n[k]
                  for r in g[k] if int(r[2]) < FEW]


def read(paths):
    rows, bad = counts(paths)
    spread = [r for r in rows if r[6] != '0']
    g, n, few = few_calls(rows)
    mv = [r for v in g.values() for r in v]
    out = [f'{len(rows) + len(bad)} cells, {len(bad)} failed, {len(spread)}'
           f' spread; {len(mv)} move by 0.2%:'
           f' {sum(float(r[5]) < 1 for r in mv)} fewer,'
           f' {sum(float(r[5]) > 1 for r in mv)} more']
    out += ['failed ' + ' '.join(r[:3] + r[7:]) for r in bad]
    for k in sorted(g):
        v = g[k]
        d = sorted(float(r[4]) - float(r[3]) for r in v)
        q = sorted(100 * (float(r[5]) - 1) for r in v)
        views = sorted({r[1].split('/')[3] for r in v})
        out.append(f'{k[0]:20s} {k[1]:8s} {k[2]:9s} {k[3]} {k[4]:6s}'
                   f' {len(v):3d}/{n[k]:<3d}'
                   f'  {d[0]:+10.1f} .. {d[-1]:+10.1f}'
                   f'  {q[0]:+6.2f}% .. {q[-1]:+6.2f}%'
                   + ('  ' + ' '.join(views) if len(views) < 9 else ''))
    if few:
        out.append(f'moving, counted over fewer than {FEW} calls:')
        out += ['  ' + '\t'.join(r[:7]) for r in few]
    return out, 1 if bad or few else 0


def noise(bins, out, paths, cpus, reps):
    rows, _ = counts(paths)
    few = few_calls(rows)[2]
    if not few:
        return ['no moving cell counted over fewer than'
                f' {FEW} calls; nothing to count again'], 0
    lock = threading.Lock()
    with tempfile.TemporaryDirectory() as td, open(out, 'w') as fo:
        run = wrappers(td, bins)

        def work(r, cpu):
            rc, text, fig = per_call(run[r[0]], r[1], 10 * int(r[2]), cpu,
                                     reps)
            with lock:
                fo.write(f'{r[0]} {r[1]} exit {rc} {text}\n')
                fo.flush()
            return fig is not None
        ok = lanes(few, cpus, work)
    return [f'{len(few)} cells counted again into {out}'
            + ('' if ok else ', some without figures')], 0 if ok else 2


def options(argv, reps):
    cpus = None
    while argv[:1] in (['--cpus'], ['--reps']):
        if len(argv) < 2:
            raise Unreadable(f'{argv[0]} needs a value')
        if argv[0] == '--cpus':
            cpus = [c for c in re.split(r'[,\s]+', argv[1]) if c]
            if not cpus or not all(c.isdigit() for c in cpus):
                raise Unreadable(f'--cpus {argv[1]!r} is not a list of CPUs')
        else:
            if not argv[1].isdigit() or int(argv[1]) < 1:
                raise Unreadable('--reps needs a positive count')
            reps = int(argv[1])
        argv = argv[2:]
    return cpus, reps, argv


def need(argv, k, more=False):
    if len(argv) < k if more else len(argv) != k:
        raise Unreadable('usage:\n' + __doc__.split('\n\n')[1])


def run(argv):
    cmd, argv = argv[0], argv[1:]
    if cmd == 'cells':
        need(argv, 4)
        return cells(*argv), 0
    if cmd == 'movers':
        need(argv, 5)
        return movers(*argv), 0
    if cmd == 'count':
        cpus, reps, argv = options(argv, None)
        need(argv, 6)
        return count(argv[:2], argv[2], argv[3], argv[4], argv[5], cpus, reps)
    if cmd == 'read':
        need(argv, 1, True)
        return read(argv)
    if cmd == 'noise':
        cpus, reps, argv = options(argv, 5)
        need(argv, 4, True)
        return noise(argv[:2], argv[2], argv[3:], cpus, reps)
    raise Unreadable(f'no subcommand {cmd}')


HEADER = ('                          ns, then bytes\n'
          '               boxed Storable Unboxed boxed Storable Unboxed\n')
FORCED_A = HEADER + '''\
Dynamic/fold/small/dense      10.00  12.00  -      16.00  16.00  -
Dynamic/fold/small/strided    10.00  12.00  -      16.00  24.00  -
Dynamic/fold/large/dense       1.00   0.20  1.00    0.00   0.00  0.00
Dynamic/fold/large/strided     0.10   0.20  1.00    0.00   0.00  0.00
Shaped/fold/small/dense       10.00  12.00  13.00  16.00  16.00  16.00
'''
SUMMED_A = HEADER + '''\
Dynamic/fold/small/dense      10.00  12.00  -       8.00   8.00  -
Shaped/fold/small/dense       10.00  12.00  13.00   8.00   8.00   8.00
'''
ROWS = '\t'.join(['module', 'size', 'kind', 'name', 'forced local',
                  'summed local', 'forced full', 'summed full', 'calls',
                  'changed library callees']) + '''
OpsDynamic\tsmall\tB\tfold\tsame\tsame\tdiffers\tsame\t\t
OpsDynamic\tlarge\tU\tfold\tsame\tsame\tdiffers\tsame\t\t
OpsDynamic\tsmall\tS\tfold\tsame\tsame\tliterals\tsame\t\t
OpsShaped\tsmall\tS\tfold\tsame\tsame\tsame\tdiffers\t\t
OpsRanked\tsmall\tB\tfold\tUNMATCHED 1 0
'''
CELLS = '''Dynamic/fold/small/dense/boxed
Dynamic/fold/small/dense/Storable
Dynamic/fold/small/strided/boxed
Dynamic/fold/large/dense/Unboxed
Dynamic/fold/large/strided/Unboxed
Dynamic/fold/large/dense/boxed
summed
Shaped/fold/small/dense/boxed
Shaped/fold/small/dense/Storable
'''
# Instructions a call by build and cell, the summed ones run with --summed;
# a cell run in the other mode costs 7.
COSTS = {('forced', 'Dynamic/fold/small/dense/boxed'): (100, 110),
         ('forced', 'Dynamic/fold/small/dense/Storable'): (100, 100),
         ('forced', 'Dynamic/fold/small/strided/boxed'): (100, 100.1),
         ('forced', 'Dynamic/fold/large/dense/Unboxed'): (1000, 1010),
         ('forced', 'Dynamic/fold/large/strided/Unboxed'): (1000, 1000),
         ('forced', 'Dynamic/fold/large/dense/boxed'): (1000, 1020),
         ('summed', 'Shaped/fold/small/dense/boxed'): (50, 50.1),
         ('summed', 'Shaped/fold/small/dense/Storable'): (50, 49.9)}
BENCH = '''#!/usr/bin/env python3
import os, sys
a = sys.argv
mode = 'summed' if '--summed' in a else 'forced'
iters, name = int(a[a.index('--iters') + 1]), a[a.index('glob') + 1]
per = {costs!r}.get((mode, name), (7, 7))[os.path.basename(a[0]) == 'B']
with open(os.path.join(os.path.dirname(a[0]), 'iters.log'), 'a') as fh:
    fh.write(str(iters) + chr(10))
with open(os.environ['FAKE_COUNT'], 'w') as fh:
    fh.write(str(round(1000 + per * iters)))
'''
PERF = '''#!/usr/bin/env python3
import os, subprocess, sys
a = sys.argv
out, rest = a[a.index('-o') + 1], a[a.index('--') + 1:]
subprocess.run(rest, env=dict(os.environ, FAKE_COUNT=out + '.n'), check=True)
n = int(open(out + '.n').read())
with open(out, 'w') as fh:
    fh.write(str(n) + ',,instructions:u,100,100.00,,' + chr(10)
             + str(n // 2) + ',,cycles:u,100,100.00,,' + chr(10))
'''
TASKSET = '#!/bin/sh\necho "$2" >> "{log}"\nshift 2\nexec "$@"\n'


def checks(bad, td):
    """The self-test's cases, each failure appended to bad."""
    def put(name, text, mode=None):
        p = os.path.join(td, name)
        with open(p, 'w') as fh:
            fh.write(text)
        if mode:
            os.chmod(p, mode)
        return p
    fa, sa = put('fa.txt', FORCED_A), put('sa.txt', SUMMED_A)
    fb = put('fb.txt', FORCED_A.replace(
        'small/dense      10.00  12.00  -      16.00', 'small/dense      '
        '10.00  12.00  -      24.00'))
    sb = put('sb.txt', SUMMED_A.replace('13.00   8.00   8.00   8.00',
                                        '13.00   8.00   0.00   8.00'))
    rows = put('rows.tsv', ROWS)
    out = os.path.join(td, 'out.txt')
    msg = run(['cells', rows, fa, sa, out])[0]
    if lines_of(out) != ['Dynamic/fold/small/dense/boxed',
                         'Dynamic/fold/small/strided/boxed',
                         'Dynamic/fold/large/dense/Unboxed',
                         'Dynamic/fold/large/strided/Unboxed', 'summed',
                         'Shaped/fold/small/dense/Storable', ''] \
            or '3 rows differ, 1 unmatched' not in msg[0]:
        bad.append(f'cells: {msg} {lines_of(out)}')
    run(['movers', fa, fb, sa, sb, out])
    if lines_of(out) != ['Dynamic/fold/small/dense/boxed', 'summed',
                         'Shaped/fold/small/dense/Storable', '']:
        bad.append(f'movers: {lines_of(out)}')
    shim = os.path.join(td, 'shim')
    os.makedirs(shim)
    log = os.path.join(td, 'cpus.log')
    put('shim/perf', PERF, 0o755)
    put('shim/taskset', TASKSET.format(log=log), 0o755)
    bins = [put(b, BENCH.format(costs=COSTS), 0o755) for b in 'AB']
    cells_path = put('cells.txt', CELLS)
    counted = os.path.join(td, 'count.tsv')
    env = {'PATH': shim + os.pathsep + os.environ.get('PATH', '')}
    with mock.patch.dict(os.environ, env):
        msg, rc = run(['count', '--cpus', '0,1', '--reps', '1'] + bins
                      + [fa, sa, cells_path, counted])
        got = sorted(lines_of(counted)[:-1])
        d, sh = 'Dynamic/fold/', 'Shaped/fold/'
        want = sorted('\t'.join(r.split()) for r in [
            f'forced {d}small/dense/boxed 200000 100.0 110.0 1.1000 0',
            f'forced {d}small/dense/Storable 200000 100.0 100.0 1.0000 0',
            f'forced {d}small/strided/boxed 200000 100.0 100.1 1.0010 0',
            f'forced {d}large/dense/Unboxed 100 1000.0 1010.0 1.0100 0',
            f'forced {d}large/strided/Unboxed 100 1000.0 1000.0 1.0000 0',
            f'forced {d}large/dense/boxed 100 1000.0 1020.0 1.0200 0',
            f'summed {sh}small/dense/boxed 200000 50.0 50.1 1.0020 0',
            f'summed {sh}small/dense/Storable 200000 50.0 49.9 0.9980 0'])
        if rc != 0 or got != want:
            bad.append(f'count: {rc} {msg}\n  ' + '\n  '.join(got))
        if sorted(set(lines_of(log)) - {''}) != ['0', '1']:
            bad.append(f'lanes not pinned to 0 and 1: {lines_of(log)}')
        iters = os.path.join(td, 'iters.log')
        if set(lines_of(iters)) - {''} != {'100', '200', '200000', '400000'}:
            bad.append(f'count ran other N: {set(lines_of(iters))}')
        os.remove(iters)
        msg, rc = run(['count'] + bins + [fa, sa, cells_path, counted])
        if rc != 0 or not msg[0].startswith('all 8 cells') \
                or len(lines_of(counted)) != 9:
            bad.append(f'a count resumed counted again: {msg}')
        got, rc = read([counted])
        if rc != 1 or got[0] != ('8 cells, 0 failed, 0 spread; 5 move by'
                                 ' 0.2%: 1 fewer, 4 more') \
                or [x.split()[:6] for x in got[1:6]] != [
                    ['fold', 'Storable', '[3,3]', 'Sh', 'summed', '1/1'],
                    ['fold', 'Unboxed', '[400,500]', 'DR', 'forced', '1/2'],
                    ['fold', 'boxed', '[3,3]', 'DR', 'forced', '1/2'],
                    ['fold', 'boxed', '[3,3]', 'Sh', 'summed', '1/1'],
                    ['fold', 'boxed', '[400,500]', 'DR', 'forced', '1/1']] \
                or got[6:] != ['moving, counted over fewer than 200 calls:',
                               '  forced\tDynamic/fold/large/dense/Unboxed'
                               '\t100\t1000.0\t1010.0\t1.0100\t0']:
            bad.append('read:\n  ' + '\n  '.join(got))
        noisy = os.path.join(td, 'noise.txt')
        msg, rc = run(['noise', '--reps', '2'] + bins + [noisy, counted])
        got = lines_of(noisy)
        if set(lines_of(iters)) - {''} != {'1000', '2000'}:
            bad.append(f'noise ran other N: {set(lines_of(iters))}')
        if rc != 0 or len(got) != 2 or not got[0].startswith(
                'forced Dynamic/fold/large/dense/Unboxed exit 0 ') \
                or 'of 2 repetitions' not in got[0] \
                or 'A instructions 1000.0 [1000.0..1000.0]' not in got[0] \
                or 'B instructions 1010.0 [1010.0..1010.0] B/A 1.0100' \
                not in got[0]:
            bad.append(f'noise: {rc} {got}')
        put('shim/perf', '#!/bin/sh\nexit 1\n', 0o755)
        failing = os.path.join(td, 'failing.tsv')
        with contextlib.redirect_stdout(io.StringIO()):
            rc = main(['count'] + bins + [fa, sa, cells_path, failing])
        got = lines_of(failing)
        if rc != 2 or len(got) != 9 or got[0].split('\t')[3:7] != [
                '-', '-', '-', '2']:
            bad.append(f'a failing count: {rc} {got[:1]}')
        got, rc = read([failing])
        if rc != 1 or not got[0].startswith('8 cells, 8 failed'):
            bad.append(f'read of a failing count: {rc} {got[:1]}')
    seen = []

    def raising(x, cpu):
        seen.append(x)
        if x == 1:
            raise ValueError('planted')
        return True
    with contextlib.redirect_stderr(io.StringIO()):
        if lanes([0, 1, 2], ['0'], raising) or seen != [0, 1, 2]:
            bad.append(f'a raising cell ended its lane or passed: {seen}')
    absent = put('c2', 'Dynamic/nosuch/small/dense/boxed\n')
    kindless = put('c3', 'Dynamic/fold/small/dense/Boxed\n')
    for argv, what in ((['cells', rows, fa, os.path.join(td, 'none'), out],
                        'a missing table'),
                       (['movers', fa, sa, sa, sb, out],
                        'tables listing different rows'),
                       (['count'] + bins + [fa, sa, absent, counted],
                        'a cell not in the table'),
                       (['count'] + bins + [fa, sa, kindless, counted],
                        'a cell of no kind'),
                       (['read', rows], 'a read of no count file'),
                       (['count', '--cpus', 'x'] + bins
                        + [fa, sa, cells_path, counted], 'CPUs not a list'),
                       (['read'], 'nothing to read')):
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            rc = main(argv)
        if rc != 2 or not err.getvalue().startswith('census: '):
            bad.append(f'{what} did not exit 2 with a reason: {rc}')


def self_test():
    """The five subcommands over tables, a row-core output and cells files
    written here, count and noise driving the real perf-per-call.py through
    a fake perf, a fake taskset and two fake benchmark binaries whose
    instructions a call each cell fixes, the summed cells costing what they
    do only when run with --summed."""
    bad = []
    try:
        with tempfile.TemporaryDirectory() as td:
            checks(bad, td)
    except Unreadable as e:
        bad.append(f'a run the self-test needs did not happen: {e}')
    for x in bad:
        print('FAIL', x)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    if not argv:
        print(__doc__.split('\n\n')[1], file=sys.stderr)
        return 2
    try:
        out, rc = run(argv)
    except Unreadable as e:
        print(f'census: {e}', file=sys.stderr)
        return 2
    for line in out:
        print(line)
    return rc


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
