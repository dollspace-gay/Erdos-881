#!/usr/bin/env python3
"""Diffuse-destruction hunt (Erdős 881 lab, Link A decisive probe).

Link A's only remaining enemy is HEREDITARILY DIFFUSE destruction:
targets m destroyed by B whose representation B-parts admit no
transversal of size ≤ 2 (τ ≥ 3).  This probe hunts for ANY instance
of τ ≥ 3 in covering models — randomly and adversarially.

  D1  random sweep: structured/random covering sets A, random sparse
      B, all destroyed targets, τ census.
  D2  adversarial constructor: pick m with ≥ 3 disjoint-support reps,
      seed B with one element from each, then try to kill all
      remaining B-avoiding reps of m by deleting elements — while
      keeping pair-covering intact and the three seed reps distinct.
      Report any success (a genuine τ ≥ 3 instance).
"""

from __future__ import annotations

import random
import sys
from itertools import combinations

sys.path.insert(0, '/home/doll/erdos881/scripts')
from probe_order3_private_structure import SLACK, pair_sums_mask


def covers(A, lo, hi):
    P = pair_sums_mask(A)
    return all((P >> n) & 1 for n in range(lo, hi + 1))


def three_reps(A, m):
    out = []
    As = set(A)
    Al = sorted(As)
    for i, x in enumerate(Al):
        if 3 * x > m:
            break
        for y in Al[i:]:
            if x + 2 * y > m:
                break
            z = m - x - y
            if z >= y and z in As:
                out.append((x, y, z))
    return out


def tau(reps, B):
    """Min size of a subset of B hitting every rep; None if some rep
    misses B entirely (target not destroyed)."""
    parts = []
    for r in reps:
        p = frozenset(r) & B
        if not p:
            return None
        parts.append(p)
    # dedupe
    parts = set(parts)
    # tau = 1?
    universe = set().union(*parts)
    for b in universe:
        if all(b in p for p in parts):
            return 1
    for b1, b2 in combinations(sorted(universe), 2):
        if all(b1 in p or b2 in p for p in parts):
            return 2
    # tau >= 3: verify 3 suffices or more (report 3+)
    return 3


def d1(trials=4000, seed=881):
    rng = random.Random(seed)
    hits = []
    census = {1: 0, 2: 0, 3: 0}
    tested = 0
    for _ in range(trials):
        T = rng.randrange(40, 100)
        style = rng.randrange(4)
        if style == 0:
            A = set(range(0, T, 1))
            A = {a for a in A if rng.random() < 0.6} | {0}
        elif style == 1:
            M = rng.randrange(5, 12)
            A = set(range(M + 1)) | {rng.randrange(M + 1, 2 * M + 2)}
            A |= set(range(2 * M + 2, T, rng.randrange(2, 5)))
            A |= {0}
        elif style == 2:
            A = {0} | {n for n in range(1, T) if n % 2 == 1}
            A |= {n for n in range(1, T)
                  if n % 2 == 0 and rng.random() < 0.2}
        else:
            A = {0, 1} | {rng.randrange(1, T)
                          for _ in range(int(T ** 0.5) * 3)}
        A = sorted(A)
        if not covers(A, SLACK, max(A)):
            continue
        nz = [a for a in A if a > 0]
        if len(nz) < 6:
            continue
        B = set(rng.sample(nz, min(len(nz), rng.randrange(3, 9))))
        for m in range(SLACK, max(A)):
            reps = three_reps(A, m)
            if not reps:
                continue
            t = tau(reps, B)
            if t is None:
                continue
            tested += 1
            census[t] += 1
            if t >= 3:
                hits.append((A, sorted(B), m))
    print(f"D1: {tested} destroyed targets, tau census {census}")
    for A, B, m in hits[:3]:
        print(f"  TAU>=3: m={m} B={B} A={A}")
    return hits


def d2(trials=400, seed=1975):
    rng = random.Random(seed)
    successes = []
    attempts = 0
    for _ in range(trials):
        T = rng.randrange(50, 90)
        A = {0} | {a for a in range(1, T) if rng.random() < 0.55}
        A = sorted(A)
        if not covers(A, SLACK, max(A)):
            continue
        m = rng.randrange(3 * SLACK, max(A))
        reps = three_reps(A, m)
        # find 3 pairwise support-disjoint reps
        found = None
        for tri in combinations(range(len(reps)), 3):
            s = [set(reps[i]) - {0} for i in tri]
            if s[0] & s[1] or s[0] & s[2] or s[1] & s[2]:
                continue
            if not (s[0] and s[1] and s[2]):
                continue
            found = [reps[i] for i in tri]
            break
        if not found:
            continue
        attempts += 1
        seeds = [rng.choice(sorted(set(r) - {0})) for r in found]
        B = set(seeds)
        cur = set(A)
        # kill every other B-avoiding rep by deleting a non-seed part
        ok = True
        for _ in range(200):
            bad = None
            for r in three_reps(sorted(cur), m):
                pb = set(r) & B
                if not pb:
                    bad = r
                    break
            if bad is None:
                break
            cands = [p for p in set(bad)
                     if p != 0 and p not in B and
                     all(p not in set(fr) for fr in found)]
            if not cands:
                # forced to grow B instead: absorb one part
                grow = [p for p in set(bad) if p != 0 and
                        all(p not in set(fr) for fr in found)]
                if not grow:
                    ok = False
                    break
                B.add(rng.choice(sorted(grow)))
                continue
            cur.discard(rng.choice(sorted(cands)))
            if not covers(sorted(cur), SLACK, max(cur)):
                ok = False
                break
        else:
            ok = False
        if not ok:
            continue
        if not covers(sorted(cur), SLACK, max(cur)):
            continue
        reps2 = three_reps(sorted(cur), m)
        if not reps2:
            continue
        t = tau(reps2, B)
        if t is not None and t >= 3:
            successes.append((sorted(cur), sorted(B), m, t))
    print(f"D2: {attempts} adversarial attempts, "
          f"tau>=3 constructed: {len(successes)}")
    for A, B, m, t in successes[:3]:
        print(f"  CONSTRUCTED tau={t}: m={m} B={B}")
        print(f"    A={A}")
    return successes


if __name__ == "__main__":
    d1()
    d2()
