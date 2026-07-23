#!/usr/bin/env python3
"""Stacking test for order-3 private pairs (Erdős 881 lab, part 2).

Hand-derived claims to verify:

CLAIM 1 (level-1 exists, uniquely shaped): A = [0, M] ∪ {2M+1} is an
order-2-covering set in which m = 3M+1 is private to a = 2M+1, and within
the family "symmetric S plus one guardian above max(S)" this boundary
structure is essentially the only shape (interior guardians a <= 2M all
fail: covering 2a - M forces the element M - (2M - a), which yields the
guardian-free representation {M, M, M - (2M - a)}).

CLAIM 2 (big guardians cannot stack): there is NO second pair (a2, m2)
with a2 > M2 on top of the level-1 structure.  Rigidity forces A below M2
to be the mirror closure of the level-1 set, so we sweep ALL (M2, a2) with
mirror closure and test both privates plus covering.  Expected: zero hits.

CLAIM 3 (probe, not proof): small guardians (a2 < M2) would need
"unsplittable" elements; a crude local search looks for ANY covering set
with a private pair whose guardian sits below m - guardian, i.e. any
counterexample to the big-guardian shape.
"""

from __future__ import annotations

import random
from argparse import ArgumentParser

from probe_order3_private_structure import (
    SLACK, covers, is_private, rigidity_report, missing_in_range,
    pair_sums_mask, triple_sums_mask, scan_private_owners,
    destroyed_targets,
)


def level1(M: int):
    A = sorted(set(range(M + 1)) | {2 * M + 1})
    return A, 2 * M + 1, 3 * M + 1


def check_claim1(Ms) -> bool:
    ok = True
    for M in Ms:
        A, a, m = level1(M)
        good = covers(A, SLACK, m) and is_private(A, a, m)
        bad = rigidity_report(A, a, m) if good else ["not private/covering"]
        print(f"M={M:4d}: [0,{M}] ∪ {{{a}}}, m={m}: "
              f"{'PRIVATE+COVERING' if good else 'FAIL'}"
              f"{' rigidity OK' if good and not bad else ''}")
        ok = ok and good and not bad
        # interior guardians must all fail
        interior_hits = [aa for aa in range(M + 1, 2 * M + 1)
                         if is_private(sorted(set(range(M + 1)) | {aa}),
                                       aa, aa + M)
                         and covers(sorted(set(range(M + 1)) | {aa}),
                                    SLACK, aa + M)]
        print(f"          interior guardians a in ({M},{2*M}] that work: "
              f"{interior_hits if interior_hits else 'none (as predicted)'}")
        ok = ok and not interior_hits
    return ok


def check_claim2(M: int, factor: int = 4) -> list[tuple[int, int]]:
    """Sweep all (M2, a2) with a2 > M2; A2 = mirror closure of level-1
    below M2 plus a2.  Return list of successes (expected empty)."""
    A1, a1, m1 = level1(M)
    hits = []
    tried = 0
    for M2 in range(m1 + 1, factor * m1 + 1):
        base = set(A1) | {M2 - t for t in A1 if t <= M2}
        for a2 in range(M2 + 1, 2 * M2 + 2):
            m2 = a2 + M2
            A2 = sorted(base | {a2})
            tried += 1
            if not is_private(A2, a2, m2):
                continue
            if not covers(A2, SLACK, m2):
                continue
            if not is_private(A2, a1, m1):
                continue
            hits.append((M2, a2))
    print(f"level-1 M={M} (m1={m1}): swept {tried} (M2,a2) configs, "
          f"successes: {hits if hits else 'NONE — big guardians cannot stack'}")
    return hits


def check_claim2_fresh(M: int, factor: int = 4) -> list[tuple[int, int]]:
    """Same sweep but WITHOUT requiring pair 1 to survive: does ANY big
    guardian exist above the level-1 structure at all?"""
    A1, a1, m1 = level1(M)
    hits = []
    for M2 in range(m1 + 1, factor * m1 + 1):
        base = set(A1) | {M2 - t for t in A1 if t <= M2}
        for a2 in range(M2 + 1, 2 * M2 + 2):
            m2 = a2 + M2
            A2 = sorted(base | {a2})
            if is_private(A2, a2, m2) and covers(A2, SLACK, m2):
                hits.append((M2, a2, m2))
    label = f"{len(hits)} hits" if hits else "NONE"
    print(f"level-1 M={M}: new-pair-only sweep (old pair may die): {label}")
    for M2, a2, m2 in hits[:6]:
        A1_, a1_, m1_ = level1(M)
        base = set(A1_) | {M2 - t for t in A1_ if t <= M2}
        A2 = sorted(base | {a2})
        old = is_private(A2, a1_, m1_)
        print(f"    M2={M2} a2={a2} (a2-2*M2={a2 - 2 * M2:+d}) m2={m2}; "
              f"old pair survives: {old}")
    return hits


def check_claim3(rng: random.Random, span: int = 120, tries: int = 40,
                 iters: int = 4000):
    """Local search for ANY covering set on [0, span] with a private pair
    (a, m) where a < m - a (small guardian).  Score-guided bit flips."""
    best_report = None
    for t in range(tries):
        memb = bytearray(span + 1)
        memb[0] = 1
        for i in range(1, span + 1):
            if rng.random() < 0.5:
                memb[i] = 1
        target_m = rng.randint(span + SLACK, 3 * span)
        guard = rng.choice([i for i in range(SLACK, span) if memb[i]]
                           or [span // 2])
        memb[guard] = 1

        def state():
            A = [i for i in range(span + 1) if memb[i]]
            holes = missing_in_range(pair_sums_mask(A), SLACK, target_m)
            rest = [x for x in A if x != guard]
            P = pair_sums_mask(rest)
            badreps = sum(1 for z in rest if z <= target_m
                          and (P >> (target_m - z)) & 1)
            hasrep = any((pair_sums_mask(A) >> (target_m - z)) & 1
                         for z in A if z <= target_m)
            return A, 30 * len(holes) + 3 * badreps + (0 if hasrep else 100)

        A, score = state()
        for _ in range(iters):
            if score == 0:
                break
            i = rng.randint(1, span)
            if i == guard:
                continue
            memb[i] ^= 1
            A2, s2 = state()
            if s2 <= score or rng.random() < 0.03:
                A, score = A2, s2
            else:
                memb[i] ^= 1
        if score == 0 and guard < target_m - guard:
            print(f"  SMALL-GUARDIAN HIT: a={guard}, m={target_m}, "
                  f"|A|={len(A)}")
            print(f"    A={A}")
            return A, guard, target_m
        if best_report is None or score < best_report[0]:
            best_report = (score, guard, target_m)
    print(f"  no small-guardian private pair found in {tries} searches "
          f"(best residual score {best_report[0]})")
    return None


def main() -> None:
    ap = ArgumentParser()
    ap.add_argument("--seed", type=int, default=881)
    ap.add_argument("--Ms", type=int, nargs="*", default=[20, 30, 40])
    args = ap.parse_args()
    rng = random.Random(args.seed)

    print("=" * 72)
    print("CLAIM 1: boundary level-1 structure [0,M] ∪ {2M+1}")
    print("=" * 72)
    check_claim1(args.Ms)

    print()
    print("=" * 72)
    print("CLAIM 2: exhaustive (M2, a2) sweep — can big guardians stack?")
    print("=" * 72)
    for M in args.Ms:
        check_claim2(M)
    print()
    print("secondary sweep: is a NEW big guardian even possible if we let")
    print("the old private pair die?")
    for M in args.Ms[:2]:
        check_claim2_fresh(M)

    print()
    print("=" * 72)
    print("CLAIM 3 (probe): any small-guardian private pair at all?")
    print("=" * 72)
    check_claim3(rng)

    print()
    print("=" * 72)
    print("BONUS: giveaway test on the level-1 structure")
    print("=" * 72)
    A, a, m = level1(30)
    B = [z for z in range(1, 31, 2)]  # delete odd half of the interval
    dead = destroyed_targets(A, B, SLACK, m)
    print(f"A=[0,30] ∪ {{61}}, delete odds of [1,30]: destroyed targets in "
          f"[{SLACK},{m}]: {dead if dead else 'none — survives'}")


if __name__ == "__main__":
    main()
