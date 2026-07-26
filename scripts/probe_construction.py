#!/usr/bin/env python3
"""Probe: THE CONSTRUCTION (2026-07-26 pivot).

Instead of contradiction-mining a hypothetical enemy, BUILD the
deletion.  Repair Lemma: if 0 in A, 0 not in B, and

  (1) every b in B splits as b = u + v with u, v in A \\ B,
  (2) every large n has a pair rep with a part outside B,

then A \\ B is a basis of order 3  (n = x+y+0, or n = u+v+y).

Greedy construction: walk A upward, delete b when
  - lacunary:      b > 3 * (largest deleted so far),
  - splittable:    some rep b = u+v with u,v not already deleted
                   (parts are smaller than b, later deletions are
                   larger, so parts protect themselves),
  - independent:   r2(b + b') >= 2 for every already-deleted b'
                   (never delete both ends of a unique pair).

Then verify: conditions (1),(2) hold, and A\\B covers at order 3.
Report which hypothesis fails if any world resists.
"""

import sys

sys.path.insert(0, 'scripts')
from probe_three_rooms import build_world as build_room
from probe_mixing_survival import build_world as build_mixing
from probe_hall_strong import build_world as build_hall

N = 3000
N0 = 20


def cantor_world(_seed=0, _s=None):
    """Base-3 digit set {0,1}: the campaign's verified instance."""
    A = set()
    for n in range(N + 1):
        m, ok = n, True
        while m:
            if m % 3 > 1:
                ok = False
                break
            m //= 3
        if ok:
            A.add(n)
    return A


def r2_table(A, hi):
    """r2[n] = number of unordered pairs {x,y} in A with x+y = n."""
    As = sorted(A)
    r2 = [0] * (hi + 1)
    for i, x in enumerate(As):
        if 2 * x > hi:
            break
        for y in As[i:]:
            s = x + y
            if s > hi:
                break
            r2[s] += 1
    return r2


def served(A, Bset, m):
    """Is m in (A\\B) + (A\\B) + (A\\B)?"""
    S = [x for x in sorted(A) if x not in Bset and x <= m]
    Sset = set(S)
    pairs = set()
    for i, x in enumerate(S):
        for y in S[i:]:
            if x + y > m:
                break
            pairs.add(x + y)
    return any((m - x) in pairs for x in S)


def build_deletion(A, r2, hi, start):
    """The greedy construction."""
    As = sorted(A)
    Aset = set(A)
    B, Bset = [], set()
    splits = {}
    for b in As:
        if b < start:
            continue
        if B and b <= 3 * B[-1]:
            continue
        # splittable: a rep b = u+v with both parts undeleted
        split = None
        for u in As:
            if u == 0:
                continue
            if 2 * u > b:
                break
            v = b - u
            if v in Aset and u not in Bset and v not in Bset:
                split = (u, v)
                break
        if split is None:
            continue
        # independent: never delete both ends of a unique pair
        if any(b + c <= hi and r2[b + c] < 2 for c in B):
            continue
        if 2 * b <= hi and not served(A, Bset | {b}, 2 * b):
            continue
        B.append(b)
        Bset.add(b)
        splits[b] = split
    return B, Bset, splits


def check_conditions(A, Bset, splits, hi, lo):
    """Verify Repair Lemma hypotheses (1) and (2) empirically."""
    fails = []
    # (1) every deleted element splits into undeleted parts
    for b in Bset:
        u, v = splits[b]
        if u in Bset or v in Bset:
            fails.append(("split", b))
    # (2) every large n has a pair rep with a part outside B
    As = sorted(A)
    Aset = set(A)
    bad2 = []
    for n in range(lo, hi + 1):
        good = False
        for x in As:
            if 2 * x > n:
                break
            y = n - x
            if y in Aset and (x not in Bset or y not in Bset):
                good = True
                break
        if not good and not served(A, Bset, n):
            bad2.append(n)
    if bad2:
        fails.append(("pair-cond", bad2[:3]))
    return fails


def order3_ok(A, Bset, lo, hi):
    S = sorted(x for x in A if x not in Bset and x <= hi)
    Sset = set(S)
    pairs = set()
    for i, x in enumerate(S):
        for y in S[i:]:
            if x + y > hi:
                break
            pairs.add(x + y)
    bad = []
    for n in range(lo, hi + 1):
        if not any((n - x) in pairs for x in S if x <= n):
            bad.append(n)
    return bad


FAMILIES = [
    ("room-R1", lambda s: build_room(s, "R1")),
    ("room-DD", lambda s: build_room(s, "DD")),
    ("room-TD", lambda s: build_room(s, "TD")),
    ("mix-thin", lambda s: build_mixing(s, "thin")),
    ("mix-low", lambda s: build_mixing(s, "low")),
    ("mix-parity", lambda s: build_mixing(s, "parity_starve_odd")),
    ("mix-random", lambda s: build_mixing(s, "random")),
    ("mix-spite", lambda s: build_mixing(s, "spite_load")),
    ("hall-h0", lambda s: build_hall(s, "h0")[0]),
    ("hall-both", lambda s: build_hall(s, "both")[0]),
    ("cantor", cantor_world),
]


def main():
    hi_test = 2000
    lo_test = 300
    total = wins = 0
    for name, mk in FAMILIES:
        for seed in range(3):
            A = mk(seed)
            A = set(A) | {0}
            r2 = r2_table(A, N)
            B, Bset, splits = build_deletion(A, r2, N, 64)
            total += 1
            if len(B) < 3:
                print(f"{name:12s} s={seed}  |A|={len(A):4d}  "
                      f"|B|={len(B)}  CONSTRUCTION STALLED")
                continue
            fails = check_conditions(A, Bset, splits, hi_test, lo_test)
            bad = order3_ok(A, Bset, lo_test, hi_test)
            status = "SURVIVES" if not bad else f"FAILS at {bad[:3]}"
            if not bad:
                wins += 1
            hyp = "hyps ok" if not fails else f"HYP FAIL {fails}"
            print(f"{name:12s} s={seed}  |A|={len(A):4d}  |B|={len(B):2d} "
                  f"B={B[:5]}{'...' if len(B) > 5 else ''}  "
                  f"{status}  {hyp}")
    print(f"\n{wins}/{total} worlds: constructed deletion survives at order 3")


if __name__ == "__main__":
    main()
