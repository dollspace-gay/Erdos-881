#!/usr/bin/env python3
"""Team-guardian probe (Erdős 881 lab, part 3).

A target m is TEAM-GUARDED by {x, y} if every exact-3 representation of m
meets {x, y}, and genuinely so: some rep avoids x and some rep avoids y
(else it degenerates to a singleton guardian).

Why this matters: by infinite Ramsey, a counterexample to Erdős 881 whose
destroyed targets have 2-point destroyer funnels needs an infinite CLIQUE
of mutual guardianship — every pair from an infinite set guarding its own
target.  The finite shadow: how large can a guardian clique be, and can
team-guarded targets stack across scales?

Experiments:
  T1  verify the canonical 2-team [0,M] ∪ {2M+1, 3M+2} guarding 4M+2.
  T2  exhaustive clique scan over A = [0,M] ∪ {g1,g2,g3}: does any config
      give all three pairs their own team target (a 3-clique)?  Also count
      configs realizing 1 or 2 pair-targets, and star patterns (two teams
      sharing one anchor).
  T3  stacking sweep: mirror-close a level-1 team below M2, add a new
      guardian pair; does any (M2, p2, q2, m2) keep BOTH team targets?
  T4  mixed stacks: singleton guardian above a team level, team above a
      singleton level.
"""

from __future__ import annotations

from argparse import ArgumentParser

from probe_order3_private_structure import (
    SLACK, pair_sums_mask, range_mask,
)


# ------------------------------------------------------------- helpers

def has_rep3_avoiding(A, m: int, banned: set[int]) -> bool:
    keep = [x for x in A if x not in banned]
    P = pair_sums_mask(keep)
    return any((P >> (m - z)) & 1 for z in keep if z <= m)


def covered_until(A, lo: int) -> int:
    """Largest H such that [lo, H] ⊆ A+A (H = lo-1 if lo uncovered)."""
    P = pair_sums_mask(A)
    H = lo - 1
    limit = 2 * max(A) + 1
    for n in range(lo, limit + 1):
        if (P >> n) & 1:
            H = n
        else:
            break
    return H


def team_targets(A, pair: tuple[int, int], lo: int, hi: int) -> list[int]:
    """Targets in [lo, hi] genuinely team-guarded by `pair`."""
    x, y = pair
    out = []
    for m in range(lo, hi + 1):
        if not has_rep3_avoiding(A, m, {x, y}):
            if has_rep3_avoiding(A, m, {x}) and has_rep3_avoiding(A, m, {y}):
                out.append(m)
    return out


def singleton_targets(A, g: int, lo: int, hi: int) -> list[int]:
    return [m for m in range(lo, hi + 1)
            if has_rep3_avoiding(A, m, set()) and
            not has_rep3_avoiding(A, m, {g})]


# ---------------------------------------------------------------- T1/T2

def t1(Ms) -> None:
    for M in Ms:
        p, q = 2 * M + 1, 3 * M + 2
        A = sorted(set(range(M + 1)) | {p, q})
        H = covered_until(A, SLACK)
        ts = team_targets(A, (p, q), 3 * M + 1, min(H, 5 * M))
        print(f"M={M:3d}: A=[0,{M}]∪{{{p},{q}}} covered to {H}; "
              f"{{p,q}}-team targets: {ts if ts else 'NONE'}")


def t2(Ms) -> None:
    total = {1: 0, 2: 0, 3: 0}
    stars = 0
    examples = {}
    for M in Ms:
        for g1 in range(M + 1, 2 * M + 2):
            for g2 in range(g1 + 1, g1 + M + 3):
                for g3 in range(g2 + 1, g2 + M + 3):
                    A = sorted(set(range(M + 1)) | {g1, g2, g3})
                    H = covered_until(A, SLACK)
                    if H < 3 * M + 2:
                        continue
                    pairs = [(g1, g2), (g1, g3), (g2, g3)]
                    got = [pr for pr in pairs
                           if team_targets(A, pr, 3 * M + 1, H)]
                    k = len(got)
                    if k:
                        total[k] += 1
                        if k not in examples:
                            examples[k] = (M, g1, g2, g3, got)
                    anchors = {}
                    for (u, v) in got:
                        anchors[u] = anchors.get(u, 0) + 1
                        anchors[v] = anchors.get(v, 0) + 1
                    if any(c >= 2 for c in anchors.values()):
                        stars += 1
    print(f"configs with ≥1 pair-target: {sum(total.values())} "
          f"(1 pair: {total[1]}, 2 pairs: {total[2]}, "
          f"3-CLIQUES: {total[3]})")
    print(f"star patterns (one anchor in ≥2 teams): {stars}")
    for k in sorted(examples):
        M, g1, g2, g3, got = examples[k]
        print(f"  example with {k} pair(s): M={M}, guardians "
              f"({g1},{g2},{g3}), teams {got}")


# ------------------------------------------------------------------- T3

def level1_team(M: int):
    p, q = 2 * M + 1, 3 * M + 2
    A = sorted(set(range(M + 1)) | {p, q})
    return A, (p, q), 4 * M + 2


def t3(M: int, factor: int = 3) -> None:
    A1, (p1, q1), m1 = level1_team(M)
    hits, fresh_hits, tried = [], [], 0
    for M2 in range(m1 + 1, factor * m1 + 1):
        base = set(A1) | {M2 - t for t in A1 if t <= M2}
        for p2 in range(M2 + 1, 2 * M2 + 2):
            for q2 in range(p2 + 1, 2 * M2 + 3):
                A2 = sorted(base | {p2, q2})
                H = covered_until(A2, SLACK)
                if H <= 3 * M2:
                    continue
                cand = [m for m in range(3 * M2 + 1, H + 1)]
                for m2 in cand:
                    tried += 1
                    if has_rep3_avoiding(A2, m2, {p2, q2}):
                        continue
                    if not (has_rep3_avoiding(A2, m2, {p2})
                            and has_rep3_avoiding(A2, m2, {q2})):
                        continue
                    fresh_hits.append((M2, p2, q2, m2))
                    old_ok = (not has_rep3_avoiding(A2, m1, {p1, q1})
                              and has_rep3_avoiding(A2, m1, {p1})
                              and has_rep3_avoiding(A2, m1, {q1}))
                    if old_ok:
                        hits.append((M2, p2, q2, m2))
    print(f"level-1 team M={M} (m1={m1}): {tried} (M2,p2,q2,m2) candidates")
    print(f"  fresh team above (old may die): "
          f"{fresh_hits[:5] if fresh_hits else 'NONE'}"
          f"{' …total ' + str(len(fresh_hits)) if len(fresh_hits) > 5 else ''}")
    print(f"  BOTH teams alive (true stacking): "
          f"{hits[:5] if hits else 'NONE'}"
          f"{' …total ' + str(len(hits)) if len(hits) > 5 else ''}")


# ------------------------------------------------------------------- T4

def t4(M: int, factor: int = 3) -> None:
    # (a) singleton guardian above a team level
    A1, (p1, q1), m1 = level1_team(M)
    single_hits = []
    for M2 in range(m1 + 1, factor * m1 + 1):
        base = set(A1) | {M2 - t for t in A1 if t <= M2}
        for a2 in range(M2 + 1, 2 * M2 + 2):
            m2 = a2 + M2
            A2 = sorted(base | {a2})
            if covered_until(A2, SLACK) < m2:
                continue
            if has_rep3_avoiding(A2, m2, {a2}):
                continue
            if not has_rep3_avoiding(A2, m2, set()):
                continue
            old_ok = (not has_rep3_avoiding(A2, m1, {p1, q1})
                      and has_rep3_avoiding(A2, m1, {p1})
                      and has_rep3_avoiding(A2, m1, {q1}))
            single_hits.append((M2, a2, old_ok))
    alive = [h for h in single_hits if h[2]]
    print(f"(a) singleton above team, M={M}: fresh singletons "
          f"{len(single_hits)}, with team alive: "
          f"{alive[:5] if alive else 'NONE'}")

    # (b) team above the singleton level [0,M'] ∪ {2M'+1}
    Mp = M
    A1s = sorted(set(range(Mp + 1)) | {2 * Mp + 1})
    a1, m1s = 2 * Mp + 1, 3 * Mp + 1
    team_hits = []
    for M2 in range(m1s + 1, factor * m1s + 1):
        base = set(A1s) | {M2 - t for t in A1s if t <= M2}
        for p2 in range(M2 + 1, 2 * M2 + 2):
            for q2 in range(p2 + 1, 2 * M2 + 3):
                A2 = sorted(base | {p2, q2})
                H = covered_until(A2, SLACK)
                if H <= 3 * M2:
                    continue
                for m2 in range(3 * M2 + 1, H + 1):
                    if has_rep3_avoiding(A2, m2, {p2, q2}):
                        continue
                    if not (has_rep3_avoiding(A2, m2, {p2})
                            and has_rep3_avoiding(A2, m2, {q2})):
                        continue
                    old_ok = not has_rep3_avoiding(A2, m1s, {a1})
                    team_hits.append((M2, p2, q2, m2, old_ok))
    alive_b = [h for h in team_hits if h[4]]
    print(f"(b) team above singleton, M'={Mp}: fresh teams "
          f"{len(team_hits)}, with singleton alive: "
          f"{alive_b[:5] if alive_b else 'NONE'}")
    if team_hits and not alive_b:
        print(f"    (fresh-team examples, singleton dead: {team_hits[:3]})")


def main() -> None:
    ap = ArgumentParser()
    ap.add_argument("--Ms", type=int, nargs="*", default=[8, 10, 12])
    ap.add_argument("--stackM", type=int, default=8)
    args = ap.parse_args()

    print("=" * 72)
    print("T1: canonical 2-team structures")
    print("=" * 72)
    t1(args.Ms)

    print()
    print("=" * 72)
    print("T2: exhaustive guardian-clique scan (A = [0,M] ∪ {g1,g2,g3})")
    print("=" * 72)
    t2(args.Ms)

    print()
    print("=" * 72)
    print("T3: can a second team stack above a team level?")
    print("=" * 72)
    t3(args.stackM)

    print()
    print("=" * 72)
    print("T4: mixed stacks (singleton/team cross combinations)")
    print("=" * 72)
    t4(args.stackM)


if __name__ == "__main__":
    main()
