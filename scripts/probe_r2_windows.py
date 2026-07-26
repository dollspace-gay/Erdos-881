#!/usr/bin/env python3
"""Measure r2 statistics on dyadic windows in the probe worlds:
min / median / max r2 per window, and poor-target (r2 <= 4)
density — the oscillation theorem's empirical portrait."""

import sys
sys.path.insert(0, 'scripts')
from probe_three_rooms import build_world, N, N0


def r2(A, Aset, n):
    return sum(1 for a in A if a <= n and (n - a) in Aset)


def main():
    for room in ("R1", "DD", "TD"):
        A = sorted(build_world(0, room))
        Aset = set(A)
        print(f"\n{room} world |A|={len(A)}")
        M = 64
        while 2 * M <= N - 200:
            vals = sorted(r2(A, Aset, n) for n in range(M, 2 * M))
            poor = sum(1 for v in vals if v <= 4)
            print(f"  [{M},{2*M}): min={vals[0]} "
                  f"med={vals[len(vals)//2]} max={vals[-1]} "
                  f"poor%={100*poor//len(vals)}")
            M *= 2


if __name__ == "__main__":
    main()
