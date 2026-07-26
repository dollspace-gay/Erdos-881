#!/usr/bin/env python3
"""Probe: THE MASTER CRITERION (deletion_criterion_local).

Only targets in B + A are ever at risk; everything else keeps
its covering pair.  Greedy: delete b iff every target in
b + A stays served (surviving triple) once b is gone.
"""
import sys
sys.path.insert(0, 'scripts')
from probe_mixing_survival import build_world as build_mixing
from probe_three_rooms import build_world as build_room
from probe_construction import cantor_world, N
from probe_sumfree import odds_world, order3_bad


def pair_counts(A, Bset, hi):
    S = [x for x in sorted(A) if x not in Bset]
    cnt = [0] * (hi + 1)
    for i, x in enumerate(S):
        if 2 * x > hi:
            break
        for y in S[i:]:
            if x + y > hi:
                break
            cnt[x + y] += 1
    return cnt


def greedy(A, hi, start):
    As = sorted(A)
    B, Bset = [], set()
    cnt = pair_counts(A, Bset, hi)
    for b in As:
        if b <= 0 or b < start:
            continue
        if B and b <= 3 * B[-1]:
            continue
        alive = [z for z in As if z not in Bset and z != b]
        aliveset = set(alive)
        # targets m whose rep count drops when b goes
        T = bytearray(hi + 1)
        for m in range(hi + 1):
            if cnt[m] >= 1:
                T[m] = 1
        for t in alive:
            m = b + t
            if m <= hi and cnt[m] == 1:
                T[m] = 0
        if 2 * b <= hi and cnt[2 * b] == 1:
            T[2 * b] = 0
        ok = True
        for a in As:                      # targets in b + A
            n = b + a
            if n > hi:
                break
            if a in Bset:
                continue
            if not any(T[n - z] for z in alive if z <= n):
                ok = False
                break
        if not ok:
            continue
        B.append(b)
        Bset.add(b)
        cnt = pair_counts(A, Bset, hi)
    return B, Bset


FAMILIES = [
    ("room-R1", lambda s: build_room(s, "R1")),
    ("room-DD", lambda s: build_room(s, "DD")),
    ("room-TD", lambda s: build_room(s, "TD")),
    ("mix-thin", lambda s: build_mixing(s, "thin")),
    ("mix-low", lambda s: build_mixing(s, "low")),
    ("mix-parity", lambda s: build_mixing(s, "parity_starve_odd")),
    ("mix-random", lambda s: build_mixing(s, "random")),
    ("mix-spite", lambda s: build_mixing(s, "spite_load")),
    ("odds", lambda s: odds_world(s)),
    ("cantor", lambda s: cantor_world(s)),
]

wins = tot = 0
for name, mk in FAMILIES:
  for seed in range(2):
    A = set(mk(seed)) | {0}
    B, Bset = greedy(A, 2400, 64)
    bad = order3_bad(A, Bset, 300, 2000)
    tot += 1
    if not bad and len(B) >= 3:
        wins += 1
    print(f"{name:10s} s={seed} |A|={len(A):4d} |B|={len(B):2d} "
          f"B={B[:5]}{'...' if len(B) > 5 else ''}  "
          f"{'SURVIVES' if not bad else 'FAILS ' + str(bad[:3])}")
print(f"\n{wins}/{tot} worlds: greedy under the master criterion "
      f"builds a surviving deletion")
