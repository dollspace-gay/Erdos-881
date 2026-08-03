#!/usr/bin/env python3
"""Finite diagnostic for en escape."""

from __future__ import annotations

import sys
from itertools import combinations

sys.path.insert(0, '/home/doll/erdos881/scripts')
from probe_order3_private_structure import SLACK, pair_sums_mask
from probe_team_guardians import covered_until, team_targets


def en_basis(K: int, T: int):
    """Finite diagnostic for en basis."""
    A = set(range(0, SLACK + 2))
    q = SLACK + 2
    while q < T:
        top = q + max(2, q // 2)
        A |= set(range(q, min(top, T) + 1))
        q = int(top * 1.8) + 1
    return sorted(a for a in A if a <= T)


def two_necessary(A, lo, hi):
    """Finite diagnostic for two necessary."""
    As = set(A)
    out = {}
    for u in A:
        if u == 0:
            continue
        for n in range(max(u, lo), hi + 1):
            reps = [(y, n - y) for y in As
                    if 2 * y <= n and (n - y) in As]
            if not reps:
                continue
            if all(u in r for r in reps):
                out.setdefault(u, []).append(n)
                break
    return out


def main() -> None:
    T = 400
    A = en_basis(12, T)
    H = covered_until(A, SLACK)
    print(f"E-N window basis: |A|={len(A)}, covered to {H}")
    nec = two_necessary(A, SLACK, min(H, T) - 10)
    print(f"E1: 2-necessary elements: {len(nec)} "
          f"(sample: {sorted(nec)[:10]})")

    # E2: order-3 pair transversal edges among necessary elements
    necs = sorted(nec)
    edges = []
    for u, v in combinations(necs, 2):
        ts = team_targets(A, (u, v), max(u, v) + 1, min(H, T) - 5)
        if ts:
            edges.append((u, v, ts[:2]))
    print(f"E2: team edges among necessary elements: {len(edges)}")
    for e in edges[:8]:
        print(f"   edge {e}")
    # triangles?
    adj = {}
    for u, v, _ in edges:
        adj.setdefault(u, set()).add(v)
        adj.setdefault(v, set()).add(u)
    tris = []
    for u, v, _ in edges:
        for w in adj.get(u, set()) & adj.get(v, set()):
            tris.append(tuple(sorted((u, v, w))))
    print(f"E2: triangles among necessary elements: "
          f"{sorted(set(tris))[:5] if tris else 'NONE'}")


if __name__ == "__main__":
    main()
