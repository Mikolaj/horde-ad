#!/usr/bin/env python3
"""Where a running binary's code lines sit in PHYSICAL memory, and whether
the page cache holds them as huge pages -- the reading README's placement
section prices, 2026-09-16: run33-exit ran `runs-16384/lib-stage2-lean-u1`
15 percent slower an iteration than a byte-identical copy of itself, every
extra cycle in the fill loop's own line at 0x430980, so what differs is the
physical placement of that file instance's pages and not its bytes.

Written for orthotope's micro-regime3 benchmark and kept there until
2026-10-06, so the README, the binaries and the benches named below are
that directory's, at
https://github.com/Mikolaj/orthotope/tree/speedup-strided-tovector/micro-regime3

    sudo python3 probe-pageflags.py PID VADDR [VADDR ...] [--heap]

PID is a live process of the binary, VADDR a virtual address in it. For
each address: the page frame from /proc/PID/pagemap, its flags from
/proc/kpageflags, the physical address, and whether the physical and the
virtual address agree modulo 2 MiB -- which is what a 2 MiB huge page
forces and a 4 KiB page leaves to chance, one in 512. Both files give
zeros or refuse without CAP_SYS_ADMIN, which this script reports rather
than reads as `not present`. The launch that pairs with it, the bench
kept alive long enough to be read AND given ten seconds to reach the
loop, a read taken before that finding the page `not present`:

    ./run33-exit classes runs -m glob 'runs-16384/lib-stage2-lean-u1' -L 60 \\
      > /dev/null & sleep 10; sudo python3 probe-pageflags.py $! 0x430980 0x4bad80; wait

0x430980 is the u1 fill loop and 0x4bad80 the sum loop in run33-exit and
in any byte-identical copy of it; in run32-nospec they are 0x430380 and
0x4b56c0. `--heap` then reads the frames of the resident pages of the
process's largest anonymous mapping, the RTS heap, and says for each
width of physical address bits above the page offset how many of them
share those bits with the FIRST address's frame, against the share a
random draw would give: what the code frame collided in is unread as of
2026-09-16, the slow frame having been evicted before its address was
taken, and a store-side check on a partial physical tag would show here
as a width where the heap's share sits far above chance. A probe and
never a check: exits 0 whatever it finds.
"""
import os
import struct
import sys


def heap_frames(pid, code_pfn):
    """The frames of the largest anonymous rw mapping, against one frame."""
    best = None
    with open(f'/proc/{pid}/maps') as f:
        for line in f:
            p = line.split()
            if len(p) >= 6 or p[1] != 'rw-p':
                continue
            lo, hi = (int(x, 16) for x in p[0].split('-'))
            if best is None or hi - lo > best[1] - best[0]:
                best = (lo, hi)
    if best is None:
        print('--heap: no anonymous rw mapping found')
        return
    lo, hi = best
    pfns = []
    with open(f'/proc/{pid}/pagemap', 'rb') as f:
        f.seek((lo >> 12) * 8)
        raw = f.read(((hi - lo) >> 12) * 8)
    for i in range(0, len(raw), 8):
        e = struct.unpack('<Q', raw[i:i + 8])[0]
        if e >> 63 & 1 and e & ((1 << 55) - 1):
            pfns.append(e & ((1 << 55) - 1))
    print(f'--heap: mapping {lo:#x}-{hi:#x}, {len(pfns)} resident page(s)')
    if not pfns:
        return
    print('  bits of the frame number shared with the code frame, width'
          ' by width: heap share against a random draw')
    for width in range(1, 13):
        mask = (1 << width) - 1
        n = sum(1 for p in pfns if (p & mask) == (code_pfn & mask))
        print(f'    low {width:2d} bit(s) above the page offset:'
              f' {n:7d} of {len(pfns)}  {n / len(pfns):.4f}'
              f'  random {1 / (1 << width):.4f}')

KPF = {0: 'LOCKED', 2: 'REFERENCED', 3: 'UPTODATE', 4: 'DIRTY', 5: 'LRU',
       6: 'ACTIVE', 11: 'MMAP', 12: 'ANON', 15: 'COMPOUND_HEAD',
       16: 'COMPOUND_TAIL', 17: 'HUGE', 18: 'UNEVICTABLE', 22: 'THP'}
HUGE = 1 << 21


def main():
    if len(sys.argv) < 3:
        sys.exit(__doc__)
    pid = int(sys.argv[1])
    heap = '--heap' in sys.argv
    first_pfn = None
    if os.geteuid() != 0:
        print('not root: /proc/PID/pagemap hides frame numbers and'
              ' /proc/kpageflags refuses, so run this under sudo')
    for a in [x for x in sys.argv[2:] if x != '--heap']:
        va = int(a, 16)
        with open(f'/proc/{pid}/pagemap', 'rb') as f:
            f.seek((va >> 12) * 8)
            e = struct.unpack('<Q', f.read(8))[0]
        present, pfn = e >> 63 & 1, e & ((1 << 55) - 1)
        if not present:
            print(f'{a}: not present in the process')
            continue
        if pfn == 0:
            print(f'{a}: present, frame number hidden (not root)')
            continue
        try:
            with open('/proc/kpageflags', 'rb') as f:
                f.seek(pfn * 8)
                fl = struct.unpack('<Q', f.read(8))[0]
        except OSError as exc:
            print(f'{a}: pfn {pfn:#x}, kpageflags refused: {exc}')
            continue
        if first_pfn is None:
            first_pfn = pfn
        phys = pfn << 12 | va & 0xfff
        names = [n for b, n in sorted(KPF.items()) if fl >> b & 1]
        same = phys % HUGE == va % HUGE
        # How far the frames run contiguous around this page, in pages:
        # a large folio is contiguous and file-offset aligned, so the run
        # says its order where kpageflags does not, and a 4 KiB page
        # breaks at once. Within a run of 16 or more, the physical L2
        # set (bits 15:6) equals the virtual one by construction.
        lo = hi = va >> 12
        with open(f'/proc/{pid}/pagemap', 'rb') as f:
            def pfn_at(page):
                f.seek(page * 8)
                e = struct.unpack('<Q', f.read(8))[0]
                return e & ((1 << 55) - 1) if e >> 63 & 1 else None
            while lo > 0 and pfn_at(lo - 1) == pfn - ((va >> 12) - lo) - 1:
                lo -= 1
            while pfn_at(hi + 1) == pfn + (hi - (va >> 12)) + 1:
                hi += 1
        run = hi - lo + 1
        print(f'{a}: phys {phys:#x}  L2 set phys {(phys >> 6) & 0x3ff:#x}'
              f' virt {(va >> 6) & 0x3ff:#x}  contiguous run {run} page(s)'
              f' from {lo << 12:#x}  phys==virt mod 2MiB: {same}'
              f'  flags {" ".join(names)}')
    if heap:
        if first_pfn is None:
            print('--heap: no frame was read, so the heap was not compared')
        else:
            heap_frames(pid, first_pfn)


if __name__ == '__main__':
    main()
