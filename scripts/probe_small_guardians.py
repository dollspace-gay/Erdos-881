#!/usr/bin/env python3
"""Finite diagnostic for small required elements."""

from __future__ import annotations

from argparse import ArgumentParser
from collections import Counter

from probe_order3_private_structure import SLACK, pair_sums_mask
from probe_team_guardians import covered_until, has_rep3_avoiding


def is_private(A, a: int, m: int) -> bool:
    rest = [x for x in A if x != a]
    P = pair_sums_mask(rest)
    if any((P >> (m - z)) & 1 for z in rest if z <= m):
        return False
    Pf = pair_sums_mask(A)
    return any((Pf >> (m - z)) & 1 for z in A if z <= m)


# ------------------------------------------------------------- PART 1

def part1(Ms) -> None:
    total = hits = 0
    examples = []
    for M in Ms:
        half = M // 2
        for bits in range(1 << half):
            S = {0, M}
            for i in range(1, half + 1):
                if i == half and M % 2 == 0:
                    if bits >> (i - 1) & 1:
                        S.add(i)
                else:
                    if bits >> (i - 1) & 1:
                        S.add(i)
                        S.add(M - i)
            A = sorted(S)
            H = covered_until(A, SLACK)
            for a in A:
                if a == 0 or a == M or 2 * a >= a + M:
                    continue
                m = a + M
                if H < m:
                    continue
                total += 1
                if is_private(A, a, m):
                    hits += 1
                    if len(examples) < 5:
                        examples.append((M, a, m, A))
    print(f"small-guardian candidates tested: {total}, private pairs: {hits}")
    for M, a, m, A in examples:
        print(f"  FOUND: M={M} a={a} m={m} A={A}")
    if hits == 0:
        print("  none exist in the exhaustive symmetric family "
              f"(all M in {list(Ms)})")


# ------------------------------------------------------------- PART 2

def part2(M: int = 8, factor: int = 2) -> None:
    A1 = sorted(set(range(M + 1)) | {2 * M + 1, 3 * M + 2})
    m1 = 4 * M + 2
    cover_block = Counter()
    kill_types = Counter()
    samples = []
    for M2 in range(m1 + 1, factor * m1 + 1):
        base = sorted(set(A1) | {M2 - t for t in A1 if t <= M2})
        for p2 in range(M2 + 1, 2 * M2 + 2, 3):
            for q2 in range(p2 + 1, 2 * M2 + 3, 3):
                A2 = sorted(set(base) | {p2, q2})
                delta = q2 - p2
                H = covered_until(A2, SLACK)
                if H <= 3 * M2:
                    bucket = ("cover-hole",
                              "low" if H < 2 * M2 else "high")
                    cover_block[bucket] += 1
                    continue
                m2 = 3 * M2 + 1
                A2s = set(A2)
                rep = None
                srt = [t for t in A2 if t not in (p2, q2)]
                for xi, x in enumerate(srt):
                    if 3 * x > m2 or rep:
                        break
                    for y in srt[xi:]:
                        if x + 2 * y > m2:
                            break
                        z = m2 - x - y
                        if z >= y and z in A2s and z not in (p2, q2):
                            rep = (x, y, z)
                            break
                if rep is None:
                    kill_types[("no-free-rep(δ=" +
                                ("small" if delta <= M else
                                 "mid" if delta <= m1 else "large") + ")",)] += 1
                    continue
                kind = tuple(sorted(
                    "old" if t <= m1 else
                    ("mirror" if t >= M2 - m1 else "middle") for t in rep))
                bucket = "small" if delta <= M else \
                    "mid" if delta <= m1 else "large"
                kill_types[(kind, bucket)] += 1
                if len(samples) < 4:
                    samples.append((M2, p2, q2, delta, rep))
    print("coverage blockers:", dict(cover_block))
    print("kill classification ((summand kinds), δ-bucket) -> count:")
    for k, v in sorted(kill_types.items(), key=lambda kv: -kv[1])[:10]:
        print(f"  {k}: {v}")
    for M2, p2, q2, d, rep in samples:
        print(f"  sample: M2={M2} team=({p2},{q2}) δ={d} killing rep {rep}")


# ------------------------------------------------------------- PART 3

def part3() -> None:
    """Finite diagnostic for part3."""
    A1, a1, m1 = [0, 1, 2, 5, 11, 14, 15, 16], 5, 21
    fresh = hits = tried = 0
    for M2 in range(m1 + 1, 5 * m1 + 1):
        base = sorted(set(A1) | {M2 - t for t in A1 if t <= M2})
        H = covered_until(base, SLACK)
        for a2 in base:
            if a2 == 0 or a2 >= M2 or H < a2 + M2:
                continue
            tried += 1
            if is_private(base, a2, a2 + M2):
                fresh += 1
                if is_private(base, a1, m1):
                    hits += 1
    print(f"small-above-small: {tried} candidates, fresh {fresh}, "
          f"stacked {hits}")


def main() -> None:
    ap = ArgumentParser()
    ap.add_argument("--Ms", type=int, nargs="*", default=[16, 20, 24, 26])
    args = ap.parse_args()
    print("=" * 72)
    print("PART 1: exhaustive small-guardian search (symmetric family)")
    print("=" * 72)
    part1(args.Ms)
    print()
    print("=" * 72)
    print("PART 2: what kills stacked teams (coverage vs free reps, by δ)")
    print("=" * 72)
    part2()
    print()
    print("=" * 72)
    print("PART 3: small-above-small stacking sweep")
    print("=" * 72)
    part3()


if __name__ == "__main__":
    main()


