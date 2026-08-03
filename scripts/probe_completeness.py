#!/usr/bin/env python3
"""Finite diagnostic for completeness."""

import sys
sys.path.insert(0, 'scripts')
from probe_three_rooms import build_world, N


def main():
    for room in ("R1", "DD"):
        A = sorted(build_world(0, room))
        Aset = set(A)
        r2 = {}
        for w in range(N):
            r2[w] = sum(1 for a in A if a <= w and (w - a) in Aset)
        for T in (8, 16, 32):
            W = [w for w in range(N) if r2[w] > T]
            Wset = set(W)
            lo, hi = N // 2, N - 200
            uncovered = []
            servers = []
            for n in range(lo, hi):
                cnt = sum(1 for w in W
                          if w <= n and (n - w) in Aset)
                servers.append(cnt)
                if cnt == 0:
                    uncovered.append(n)
            servers.sort()
            print(f"{room} T={T:2d} |W|={len(W):4d} "
                  f"uncovered={len(uncovered):3d}/{hi-lo} "
                  f"servers min/med={servers[0]}/"
                  f"{servers[len(servers)//2]}"
                  f"  {'TAIL-COMPLETE' if not uncovered else uncovered[:3]}")


if __name__ == "__main__":
    main()
