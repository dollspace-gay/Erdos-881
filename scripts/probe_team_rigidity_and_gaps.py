#!/usr/bin/env python3
"""Finite diagnostic for pair transversal rigidity and gaps."""

from __future__ import annotations

import random
from argparse import ArgumentParser

from probe_order3_private_structure import (
    SLACK, pair_sums_mask, missing_in_range, destroyed_targets,
)
from probe_team_guardians import (
    has_rep3_avoiding, covered_until, team_targets,
)


# ------------------------------------------------------------- PART A

def check_team_rigidity(A, p: int, q: int, m: int) -> list[str]:
    """Finite diagnostic for check pair transversal rigidity."""
    Aset = set(A)
    Dp, Dq = m - p, m - q
    bad = []
    for z in Aset:
        if z not in (p, q) and Dp < z and z + SLACK <= m:
            bad.append(f"desert: element {z} in ({Dp},{m - SLACK})")
    for z in Aset:
        if 0 < z and z not in (p, q) and z + q < m:
            if (Dp - z) not in Aset and (Dq - z) not in Aset:
                bad.append(f"bimirror: z={z}, neither {Dp - z} nor {Dq - z}")
    for z in Aset:
        if z not in (p, q) and Dq < z and z + p + SLACK <= m:
            if (Dp - z) not in Aset:
                bad.append(f"upper: z={z} in ({Dq},..), {Dp - z} not in A")
    return bad


def part_a(Ms) -> None:
    checked = failed = 0
    for M in Ms:
        for g1 in range(M + 1, 2 * M + 2):
            for g2 in range(g1 + 1, g1 + M + 3):
                for g3 in range(g2 + 1, g2 + M + 3):
                    A = sorted(set(range(M + 1)) | {g1, g2, g3})
                    H = covered_until(A, SLACK)
                    if H < 3 * M + 2:
                        continue
                    for (u, v) in [(g1, g2), (g1, g3), (g2, g3)]:
                        for m in team_targets(A, (u, v), 3 * M + 1, H)[:2]:
                            checked += 1
                            bad = check_team_rigidity(A, min(u, v),
                                                      max(u, v), m)
                            if bad:
                                failed += 1
                                if failed <= 5:
                                    print(f"  FAIL M={M} team=({u},{v}) "
                                          f"m={m}: {bad[:2]}")
    print(f"team-guarded targets checked: {checked}, "
          f"rigidity violations: {failed}"
          + ("  — ALL PREDICTIONS HOLD" if failed == 0 else ""))


# ------------------------------------------------------------- PART B

def mirror_fractal(b: int, K: int):
    """Finite diagnostic for mirror fractal."""
    T = set(range(b + 1))
    M = b
    levels = [M]
    for _ in range(K):
        M2 = 3 * M
        T |= {M2 - t for t in T}
        M = M2
        levels.append(M)
    return sorted(T), levels


def is_reflection_level(A, M: int) -> bool:
    Aset = set(A)
    return all((M - z) in Aset for z in Aset if 0 < z < M)


def part_b(b: int, K: int, rng: random.Random) -> None:
    T, levels = mirror_fractal(b, K)
    Mtop = levels[-1]
    holes = missing_in_range(pair_sums_mask(T), SLACK, 2 * Mtop)
    gaps = [levels[i + 1] - levels[i] for i in range(len(levels) - 1)]
    print(f"fractal b={b}, K={K}: |T|={len(T)}, top level {Mtop}, "
          f"covering holes in [{SLACK},{2 * Mtop}]: {len(holes)}")
    print(f"  reflection levels {levels}: "
          f"{[is_reflection_level(T, M) for M in levels]}")
    print(f"  level gaps {gaps}  (UNBOUNDED: ratio 2·M_k)")

    Tset = set(T)
    lo, hi = SLACK, 2 * Mtop

    def report(name: str, B: list[int]) -> None:
        dead = destroyed_targets(T, B, lo, hi)
        print(f"  giveaway {name:28s} |B|={len(B):4d}: "
              f"{'SURVIVES (0 destroyed)' if not dead else f'{len(dead)} destroyed, e.g. {dead[:6]}'}")

    worst = 0
    for trial in range(10):
        B = []
        for z in T:
            if 0 < z < Mtop - z and (Mtop - z) in Tset:
                B.append(z if rng.random() < 0.5 else Mtop - z)
        dead = destroyed_targets(T, B, lo, hi)
        worst = max(worst, len(dead))
    print(f"  giveaway one-per-mirror-pair (10 random draws): worst "
          f"destroyed count = {worst}"
          + ("  — ALL SURVIVE" if worst == 0 else ""))

    report("level tops {M_k}", levels[1:])
    top_layer = [z for z in T if z > levels[-2]]
    report("entire top mirror copy", top_layer)
    for trial in range(3):
        B = [z for z in T if 0 < z and rng.random() < 0.1]
        report(f"random 10% sample #{trial + 1}", B)


def main() -> None:
    ap = ArgumentParser()
    ap.add_argument("--seed", type=int, default=881)
    ap.add_argument("--Ms", type=int, nargs="*", default=[8, 10])
    args = ap.parse_args()
    rng = random.Random(args.seed)

    print("=" * 72)
    print("PART A: verify team rigidity (desert / bimirror / upper mirror)")
    print("=" * 72)
    part_a(args.Ms)

    print()
    print("=" * 72)
    print("PART B: unbounded-gap mirror fractals — do they survive deletion?")
    print("=" * 72)
    for (b, K) in [(4, 5), (6, 4)]:
        part_b(b, K, rng)
        print()


if __name__ == "__main__":
    main()
