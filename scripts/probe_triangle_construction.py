#!/usr/bin/env python3
"""Greedy triangle construction in the even/odd basis (Erdős 881, part 8).

Phase-2a decisive experiment.  In the even/odd binary basis the team
graph is the chain …a_i–a_{i+1}…  A triangle {a_i, a_{i+1}, a_{i+2}}
needs only the closing edge {a_i, a_{i+2}}: make target m = a_i + a_{i+2}
guarded by that pair by DELETING a hitting set of its pair-free
representations.  Questions:

  1. Can one closing edge be bought while covering survives?
  2. Do purchases at consecutive scales compose, or do the deletions
     destroy covering / earlier edges as they accumulate?
  3. How does the hitting-set price scale?

If greedy interlocking succeeds scale after scale with covering intact,
the NO-side construction is live (goal gate 2b).  If covering or old
edges collapse, the YES-side (triangle-poorness is forced) strengthens.
"""

from __future__ import annotations

from itertools import combinations

from probe_order3_private_structure import SLACK, even_odd_basis
from probe_team_guardians import covered_until, has_rep3_avoiding


def free_reps(A, m: int, banned: set[int]) -> list[tuple[int, int, int]]:
    As = sorted(A)
    Aset = set(A)
    out = []
    for xi, x in enumerate(As):
        if 3 * x > m:
            break
        if x in banned:
            continue
        for y in As[xi:]:
            if x + 2 * y > m:
                break
            if y in banned:
                continue
            z = m - x - y
            if z >= y and z in Aset and z not in banned:
                out.append((x, y, z))
    return out


def min_hitting_set(reps, protect: set[int], cap: int = 6):
    """Smallest deletion set hitting every rep, avoiding `protect`."""
    pool = sorted({t for r in reps for t in r if t not in protect and t > 0})
    for size in range(1, cap + 1):
        for cand in combinations(pool, size):
            cs = set(cand)
            if all(cs & set(r) for r in reps):
                return list(cand)
    return None


def is_team_edge(A, u: int, v: int, m: int) -> bool:
    return (not has_rep3_avoiding(A, m, {u, v})
            and has_rep3_avoiding(A, m, {u})
            and has_rep3_avoiding(A, m, {v}))


def main() -> None:
    A = set(even_odd_basis(13))
    hi_cov = 2 * max(A) // 2
    chain = [5, 10, 21, 42, 85, 170, 341, 682, 1365, 2730]
    chain_targets = [15, 31, 63, 127, 255, 511, 1023, 2047, 4095]
    protect = set(chain) | {0}
    print(f"scaffold: even/odd 13-bit basis, |A|={len(A)}, "
          f"covering to {covered_until(sorted(A), SLACK)}")
    print()
    bought = []
    for i in range(len(chain) - 2):
        u, w = chain[i], chain[i + 2]
        m = u + w
        reps = free_reps(A, m, {u, w})
        hs = min_hitting_set(reps, protect | {m}, cap=6)
        if hs is None:
            print(f"scale {i}: closing edge ({u},{w}) m={m}: "
                  f"{len(reps)} free reps — NO hitting set ≤ 6 avoiding "
                  f"protected elements")
            continue
        A2 = A - set(hs)
        H = covered_until(sorted(A2), SLACK)
        edge_ok = is_team_edge(sorted(A2), u, w, m)
        old_edges = all(
            is_team_edge(sorted(A2), chain[j], chain[j + 1],
                         chain_targets[j])
            for j in range(min(i + 3, len(chain) - 1))
            if chain_targets[j] <= H)
        cover_ok = H >= m
        verdict = ("BOUGHT" if (edge_ok and cover_ok and old_edges)
                   else "FAILED")
        print(f"scale {i}: edge ({u},{w}) m={m}: {len(reps)} free reps, "
              f"hitting set {hs}")
        print(f"    covering to {H} ({'ok' if cover_ok else 'BROKEN'}), "
              f"new edge {'ok' if edge_ok else 'ABSENT'}, "
              f"chain edges {'ok' if old_edges else 'BROKEN'} -> {verdict}")
        if verdict == "BOUGHT":
            A = A2                      # accumulate purchases
            bought.append((u, w, m, tuple(hs)))
    print()
    print(f"cumulative purchases that stuck: {len(bought)}")
    for u, w, m, hs in bought:
        print(f"  edge ({u},{w}) via deleting {hs}")
    if bought:
        # final audit on the accumulated basis
        H = covered_until(sorted(A), SLACK)
        tri = sum(
            1 for i in range(len(chain) - 2)
            if any(b[0] == chain[i] and b[1] == chain[i + 2]
                   for b in bought)
            and all(chain_targets[j] > H or
                    is_team_edge(sorted(A), chain[j], chain[j + 1],
                                 chain_targets[j])
                    for j in (i, i + 1)))
        print(f"final basis: covering to {H}, surviving TRIANGLES: {tri}")


if __name__ == "__main__":
    main()
