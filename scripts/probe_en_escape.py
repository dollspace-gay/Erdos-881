#!/usr/bin/env python3
"""Escape-shape probe on Erdős–Nathanson-style minimal bases.

The final clique escape of `erdos881_grand_assembly''` needs an
infinite team clique of vertices that are 2-necessary at their own
scale (¬TwoRedundant at thresholds ≤ u).  The only known ℵ₀-minimal
bases are the Erdős–Nathanson block constructions, where every
element IS necessary for its block targets.  Question: do such bases
carry the order-3 TEAM CLIQUE the escape requires?

  E1  build an E–N-style block basis in a window; find its 2-necessary
      elements and their witnesses.
  E2  among necessary elements, enumerate order-3 TeamEdges
      (pair-destroyed targets) and look for triangles / cliques.
"""

from __future__ import annotations

import sys
from itertools import combinations

sys.path.insert(0, '/home/doll/erdos881/scripts')
from probe_order3_private_structure import SLACK, pair_sums_mask
from probe_team_guardians import covered_until, team_targets


def en_basis(K: int, T: int):
    """Erdős–Nathanson flavored blocks: A = {0} ∪ ⋃_k [q_k, 3*q_k/2]
    with q_{k+1} ≈ 2.7 q_k, patched to pair-cover [SLACK, T]."""
    A = set(range(0, SLACK + 2))
    q = SLACK + 2
    while q < T:
        top = q + max(2, q // 2)
        A |= set(range(q, min(top, T) + 1))
        q = int(top * 1.8) + 1
    return sorted(a for a in A if a <= T)


def two_necessary(A, lo, hi):
    """Elements u with some n ∈ [max(u,lo), hi] whose every 2-rep
    meets u."""
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

    # E2: order-3 team edges among necessary elements
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
