#!/usr/bin/env python3
"""Finite diagnostic for wealth density."""

import sys
sys.path.insert(0, 'scripts')
from probe_three_rooms import build_world, N


def main():
    for room in ("R1", "DD"):
        A = sorted(build_world(0, room))
        Aset = set(A)
        print(f"\n{room} world |A|={len(A)}")
        M = 128
        while 2 * M <= N - 200:
            wealthy = poor = 0
            thresh = 8  # log-sparse deletion cap surrogate
            for n in range(M, 2 * M):
                r2 = sum(1 for a in A if a <= n and (n - a) in Aset)
                if r2 > thresh:
                    wealthy += 1
                elif r2 <= 4:
                    poor += 1
            print(f"  [{M},{2*M}): wealthy(r2>{thresh})="
                  f"{100*wealthy//M}%  poor(r2<=4)={100*poor//M}%")
            M *= 2


if __name__ == "__main__":
    main()
