#!/usr/bin/env python3
"""Finite diagnostic for pair transversal interlock."""

from __future__ import annotations

import random
from argparse import ArgumentParser
from collections import Counter

from probe_order3_private_structure import SLACK, pair_sums_mask, even_odd_basis
from probe_team_guardians import covered_until, has_rep3_avoiding
from probe_thin_bases import gadic_basis, guard_census


# ------------------------------------------------------------------ A

def team_graph(name: str, A, lo: int, hi: int) -> None:
    cen = guard_census(A, lo, hi)
    edges = Counter()
    for m, (kind, g) in cen.items():
        if kind == "team":
            edges[tuple(sorted(g))] += 1
    verts = Counter()
    for (u, v), c in edges.items():
        verts[u] += 1
        verts[v] += 1
    print(f"{name}: {len(edges)} team edges, {len(verts)} guard vertices")
    print(f"  edges (pair -> #targets): {dict(edges)}")
    print(f"  guard degrees: {dict(verts.most_common())}")
    tri = 0
    vs = list(verts)
    for i, u in enumerate(vs):
        for v in vs[i + 1:]:
            if tuple(sorted((u, v))) in edges:
                for w in vs:
                    if w > v and tuple(sorted((u, w))) in edges \
                            and tuple(sorted((v, w))) in edges:
                        tri += 1
                        print(f"  TRIANGLE: {u},{v},{w}")
    print(f"  triangles: {tri}  "
          f"({'path/forest — maximally dodgeable' if tri == 0 else 'ALARM'})")


# ------------------------------------------------------------------ B

def edge_cost(A, guards, label: str) -> None:
    A_sorted = sorted(A)
    Aset = set(A)
    print(f"{label}: cost to create edge {{a_i, a_j}} "
          f"(# reps of a_i + a_j avoiding the pair):")
    for i in range(len(guards)):
        for j in range(i + 1, min(i + 4, len(guards))):
            u, v = guards[i], guards[j]
            m = u + v
            cnt = 0
            wit = None
            for xi, x in enumerate(A_sorted):
                if 3 * x > m:
                    break
                if x in (u, v):
                    continue
                for y in A_sorted[xi:]:
                    if x + 2 * y > m:
                        break
                    if y in (u, v):
                        continue
                    z = m - x - y
                    if z >= y and z in Aset and z not in (u, v):
                        cnt += 1
                        wit = wit or (x, y, z)
            gap = "adjacent" if j == i + 1 else f"dist {j - i}"
            print(f"  ({u:5d},{v:5d}) [{gap:8s}] m={m:5d}: "
                  f"{cnt:4d} free reps"
                  + (f", e.g. {wit}" if wit and cnt <= 6 else ""))


# ------------------------------------------------------------------ C

def random_thin_basis(N: int, rng: random.Random) -> list[int]:
    A = {0, 1}
    P = 3  # pair-sums bitmask
    for a in list(A):
        for b in list(A):
            P |= 1 << (a + b)
    for n in range(2, N):
        if not (P >> n) & 1:
            choices = [a for a in A if a <= n and (n - a) not in A]
            new = n - rng.choice(choices) if choices else n
            A.add(new)
            for a in A:
                P |= 1 << (a + new)
    return sorted(A)


def part_c(N: int, trials: int, rng: random.Random) -> None:
    maxdeg_hist = Counter()
    tri_total = 0
    for t in range(trials):
        A = random_thin_basis(N, rng)
        cen = guard_census(A, N // 2, N - 1)
        verts = Counter()
        edges = set()
        for m, (kind, g) in cen.items():
            if kind == "single":
                verts[g] += 1
            elif kind == "team":
                e = tuple(sorted(g))
                if e not in edges:
                    edges.add(e)
                    verts[e[0]] += 1
                    verts[e[1]] += 1
        md = max(verts.values()) if verts else 0
        maxdeg_hist[md] += 1
        es = list(edges)
        for i, (u, v) in enumerate(es):
            for (x, y) in es[i + 1:]:
                shared = {u, v} & {x, y}
                if shared:
                    a = ({u, v} - shared).pop()
                    b = ({x, y} - shared).pop()
                    if tuple(sorted((a, b))) in edges:
                        tri_total += 1
    print(f"{trials} random thin bases on [0,{N}] "
          f"(density ~ sqrt): max guard-degree histogram: "
          f"{dict(sorted(maxdeg_hist.items()))}")
    print(f"total triangles across all trials: {tri_total}"
          + ("  — no clique seed ever appears" if tri_total == 0 else ""))


# ------------------------------------------------------------------ D

def part_d(M: int = 6) -> None:
    hits = 0
    tried = 0
    for g1 in range(M + 1, 2 * M + 3):
        for g2 in range(2 * M + 3, 4 * M + 5, 2):
            for g3 in range(4 * M + 5, 8 * M + 9, 3):
                A = sorted(set(range(M + 1)) | {g1, g2, g3})
                H = covered_until(A, SLACK)
                if H < g3 + M:
                    continue
                tried += 1
                ok = 0
                for (u, v) in [(g1, g2), (g1, g3), (g2, g3)]:
                    found = False
                    for m in range(3 * M + 1, H + 1):
                        if not has_rep3_avoiding(A, m, {u, v}) and \
                                has_rep3_avoiding(A, m, {u}) and \
                                has_rep3_avoiding(A, m, {v}):
                            found = True
                            break
                    if found:
                        ok += 1
                if ok == 3:
                    hits += 1
                    print(f"  CROSS-SCALE CLIQUE: M={M} "
                          f"guards ({g1},{g2},{g3})")
    print(f"cross-scale triples tried: {tried}, pairwise-guarding cliques: "
          f"{hits}" + ("  — none (as the rigidity predicts)" if hits == 0
                       else "  — ALARM"))


def main() -> None:
    ap = ArgumentParser()
    ap.add_argument("--seed", type=int, default=881)
    args = ap.parse_args()
    rng = random.Random(args.seed)

    print("=" * 72)
    print("A: exact team graphs of the digit bases")
    print("=" * 72)
    team_graph("even/odd binary (12 bits)", even_odd_basis(12), SLACK, 4095)
    print()
    team_graph("even/odd base-3 (8 digits)", gadic_basis(3, 8), SLACK, 4096)

    print()
    print("=" * 72)
    print("B: cost of creating a team edge between distant chain guards")
    print("=" * 72)
    EO = even_odd_basis(12)
    chain = [5, 10, 21, 42, 85, 170, 341, 682, 1365, 2730]
    edge_cost(EO, chain, "even/odd binary")

    print()
    print("=" * 72)
    print("C: guard structure of randomized greedy thin bases")
    print("=" * 72)
    part_c(1200, 8, rng)

    print()
    print("=" * 72)
    print("D: exhaustive cross-scale clique search")
    print("=" * 72)
    part_d()


if __name__ == "__main__":
    main()
