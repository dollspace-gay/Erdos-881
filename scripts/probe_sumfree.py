#!/usr/bin/env python3
"""Finite diagnostic for sumfree."""

import sys

sys.path.insert(0, 'scripts')
from probe_mixing_survival import build_world as build_mixing
from probe_three_rooms import build_world as build_room
from probe_construction import cantor_world, N


def odds_world(_seed=0):
    """Finite diagnostic for odds world."""
    return {0} | {n for n in range(1, N + 1) if n % 2 == 1}


def pos_pair_counts(A, Bset, hi):
    """Finite diagnostic for pos pair counts."""
    S = [x for x in sorted(A) if x > 0 and x not in Bset]
    cnt2 = [0] * (hi + 1)
    for i, x in enumerate(S):
        if 2 * x > hi:
            break
        for y in S[i:]:
            if x + y > hi:
                break
            cnt2[x + y] += 1
    return cnt2


def sumfree_greedy(A, hi, start):
    As = sorted(A)
    Aset = set(A)
    B, Bset = [], set()
    cnt2 = pos_pair_counts(A, Bset, hi)
    live = lambda z: z > 0 and z in Aset and z not in Bset

    def reps_after(n, b):
        """Finite diagnostic for reps after."""
        if n > hi:
            return 99
        lost = 1 if (n - b > 0 and live(n - b)) else 0
        return cnt2[n] - lost

    for b in As:
        if b < start or b == 0:
            continue
        if B and b <= 3 * B[-1]:
            continue
        # (1) b reachable by a surviving positive triple
        served = any(live(z) and z != b and b - z > 0
                     and reps_after(b - z, b) >= 1
                     for z in As if 0 < z < b)
        if not served:
            continue
        # (2) every non-basis target through b keeps a live pair
        ok = True
        for y in As:
            n = b + y
            if n > hi:
                break
            if y == 0 or not live(y) or n in Aset:
                continue
            if reps_after(n, b) < 1:
                ok = False
                break
        if ok and reps_after(2 * b, b) < 1 and 2 * b <= hi \
                and 2 * b not in Aset:
            ok = False
        if not ok:
            continue
        B.append(b)
        Bset.add(b)
        cnt2 = pos_pair_counts(A, Bset, hi)
    return B, Bset


def order3_bad(A, Bset, lo, hi):
    S = sorted(x for x in A if x not in Bset and x <= hi)
    pairs = set()
    for i, x in enumerate(S):
        for y in S[i:]:
            if x + y > hi:
                break
            pairs.add(x + y)
    return [n for n in range(lo, hi + 1)
            if not any((n - x) in pairs for x in S if x <= n)]


def sumfree_frac(A, lo, hi):
    """Finite diagnostic for sumfree frac."""
    As = sorted(A)
    Aset = set(A)
    tot = triv = 0
    for b in As:
        if not (lo <= b <= hi):
            continue
        tot += 1
        if not any(0 < u <= b // 2 and (b - u) in Aset for u in As):
            triv += 1
    return triv, tot


FAMILIES = [
    ("odds", odds_world),
    ("mix-thin", lambda s: build_mixing(s, "thin")),
    ("room-TD", lambda s: build_room(s, "TD")),
    ("cantor", cantor_world),
]


def main():
    lo, hi = 300, 2000
    for name, mk in FAMILIES:
        for seed in range(2):
            A = set(mk(seed)) | {0}
            triv, tot = sumfree_frac(A, 64, 1500)
            B, Bset = sumfree_greedy(A, N, 64)
            bad = order3_bad(A, Bset, lo, hi)
            status = "SURVIVES" if not bad else f"FAILS {bad[:3]}"
            print(f"{name:10s} s={seed} |A|={len(A):4d} "
                  f"trivial-only={triv}/{tot:3d}  |B|={len(B):2d} "
                  f"B={B[:5]}{'...' if len(B) > 5 else ''}  {status}")


if __name__ == "__main__":
    main()
