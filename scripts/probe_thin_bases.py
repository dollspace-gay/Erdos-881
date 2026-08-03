#!/usr/bin/env python3
"""Finite diagnostic for thin bases."""

from __future__ import annotations

from argparse import ArgumentParser
from collections import Counter

from probe_order3_private_structure import (
    SLACK, pair_sums_mask, destroyed_targets, even_odd_basis,
)
from probe_team_guardians import covered_until
from probe_small_guardians import is_private


# ------------------------------------------------------------- helpers

def gadic_basis(g: int, ndigits: int) -> list[int]:
    """Finite diagnostic for gadic basis."""
    evens = [i for i in range(ndigits) if i % 2 == 0]
    odds = [i for i in range(ndigits) if i % 2 == 1]
    out = set()
    for positions in (evens, odds):
        vals = [0]
        for p in positions:
            vals = [v + d * g ** p for v in vals for d in range(g)]
        out.update(vals)
    return sorted(out)


def guard_census(A, lo: int, hi: int):
    """Finite diagnostic for guard census."""
    A_sorted = sorted(A)
    Aset = set(A)
    out = {}
    for m in range(lo, hi + 1):
        supports = []
        for xi, x in enumerate(A_sorted):
            if 3 * x > m:
                break
            for y in A_sorted[xi:]:
                if x + 2 * y > m:
                    break
                z = m - x - y
                if z >= y and z in Aset:
                    supports.append(frozenset((x, y, z)))
        if not supports:
            continue
        inter = set(supports[0])
        for s in supports[1:]:
            inter &= s
            if not inter:
                break
        if inter:
            out[m] = ("single", max(inter))
            continue
        team = None
        for u in supports[0]:
            rest = [s for s in supports if u not in s]
            common = set(rest[0])
            for s in rest[1:]:
                common &= s
                if not common:
                    break
            if common:
                team = (u, max(common))
                break
        out[m] = ("team", team) if team else ("free", None)
    return out


def census_report(name: str, A, lo: int, hi: int) -> None:
    cen = guard_census(A, lo, hi)
    kinds = Counter(k for k, _ in cen.values())
    print(f"{name}: |A|={len(A)}, targets with reps in [{lo},{hi}]: "
          f"{len(cen)}")
    print(f"  singleton-guarded: {kinds.get('single', 0)}, "
          f"team-guarded: {kinds.get('team', 0)}, "
          f"free: {kinds.get('free', 0)}")
    guarded = [(m, v) for m, v in sorted(cen.items()) if v[0] != "free"]
    scales = Counter(m.bit_length() for m, _ in guarded)
    if guarded:
        print(f"  guarded targets by dyadic scale: {dict(sorted(scales.items()))}")
        print(f"  examples: {guarded[:6]}")
        guards = Counter()
        for _, (kind, g) in guarded:
            if kind == "single":
                guards[g] += 1
            else:
                guards[g[0]] += 1
                guards[g[1]] += 1
        print(f"  most-used guards: {guards.most_common(6)}")


# ------------------------------------------------------------------ T2

def all_small_structures(M: int):
    half = M // 2
    for bits in range(1 << half):
        S = {0, M}
        for i in range(1, half + 1):
            if bits >> (i - 1) & 1:
                S.add(i)
                S.add(M - i)
        A = sorted(S)
        H = covered_until(A, SLACK)
        for a in A:
            if a in (0, M):
                continue
            m = a + M
            if H >= m and is_private(A, a, m):
                yield A, a, m


def t2(M: int = 16, extra_pairs: bool = True) -> None:
    structures = list(all_small_structures(M))
    print(f"level-1 small-guardian structures at M={M}: {len(structures)}")
    total_fresh = total_stacked = swept = 0
    for A1, a1, m1 in structures:
        for M2 in range(m1 + 1, 4 * m1 + 1):
            base0 = set(A1) | {M2 - t for t in A1 if t <= M2}
            variants = [sorted(base0)]
            if extra_pairs:
                for e in range(m1 + 1, (M2 + 1) // 2, 2):
                    variants.append(sorted(base0 | {e, M2 - e}))
            for A2 in variants:
                H = covered_until(A2, SLACK)
                for a2 in A2:
                    if a2 == 0 or a2 >= M2 or H < a2 + M2:
                        continue
                    swept += 1
                    if is_private(A2, a2, a2 + M2):
                        total_fresh += 1
                        if is_private(A2, a1, m1):
                            total_stacked += 1
                            print(f"  STACK: A1={A1} a1={a1} "
                                  f"M2={M2} a2={a2}")
    print(f"swept {swept} second-scale candidates over "
          f"{len(structures)} structures (closure + one-pair variants)")
    print(f"fresh guardians above: {total_fresh}, "
          f"true stacks: {total_stacked}"
          + ("  — NOTHING STACKS" if total_stacked == 0 else "  — ALARM"))


# ------------------------------------------------------------------ T3

def t3(nbits: int = 12) -> None:
    A = even_odd_basis(nbits)
    hi = (1 << nbits) - 1
    for layer in range(nbits - 4, nbits - 1):
        B = [a for a in A if a.bit_length() - 1 == layer]
        dead = destroyed_targets(A, B, SLACK, hi - (1 << (nbits - 1)))
        print(f"delete layer 2^{layer} (|B|={len(B)}): "
              f"{'survives' if not dead else f'{len(dead)} destroyed, e.g. {dead[:6]}'}")
    Bhalf = [a for a in A if a % 4 == 1]
    dead = destroyed_targets(A, Bhalf, SLACK, hi - (1 << (nbits - 1)))
    print(f"delete residue class 1 mod 4 (|B|={len(Bhalf)}): "
          f"{'survives' if not dead else f'{len(dead)} destroyed, e.g. {dead[:6]}'}")


def main() -> None:
    ap = ArgumentParser()
    ap.add_argument("--nbits", type=int, default=12)
    args = ap.parse_args()
    print("=" * 72)
    print("T1: guardian census in canonical thin bases")
    print("=" * 72)
    EO = even_odd_basis(args.nbits)
    hi = min((1 << args.nbits) - 1, 4096)
    census_report(f"even/odd binary ({args.nbits} bits)", EO, SLACK, hi)
    print()
    G3 = gadic_basis(3, 8)
    census_report("even/odd base-3 (8 digits)", G3, SLACK,
                  min(max(G3) * 2, 4096))
    print()
    print("=" * 72)
    print("T2: mass stacking sweep over ALL small-guardian structures")
    print("=" * 72)
    t2()
    print()
    print("=" * 72)
    print("T3: adversarial layer deletions in the even/odd basis")
    print("=" * 72)
    t3(args.nbits)


if __name__ == "__main__":
    main()
