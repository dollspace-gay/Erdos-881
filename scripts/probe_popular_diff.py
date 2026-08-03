#!/usr/bin/env python3
"""Finite diagnostic for popular diff."""

import sys

sys.path.insert(0, 'scripts')
from probe_three_rooms import build_world as build_room
from probe_mixing_survival import build_world as build_mixing
from probe_construction import cantor_world
from probe_sumfree import odds_world

X = 2000


def analyse(name, A):
    A = set(A) | {0}
    Aset = A
    As = sorted(a for a in A if a <= X)
    alpha = len(As)

    # (a) difference multiplicities
    mult = {}
    for i, y in enumerate(As):
        for z in As[i + 1:]:
            d = z - y
            mult[d] = mult.get(d, 0) + 1
    top = sorted(mult.items(), key=lambda kv: -kv[1])[:8]
    in_a = sum(1 for d, _ in top if d in Aset)

    # popular = multiplicity at least half the max
    mx = top[0][1] if top else 0
    popular = [d for d, m in mult.items() if m >= mx / 2]
    pop_in_a = sum(1 for d in popular if d in Aset)

    # is d a sum of two positive basis elements?
    def splits(d):
        return any(0 < u <= d // 2 and (d - u) in Aset for u in As)

    pop_split = sum(1 for d in popular if splits(d))

    # (b) chain-produced differences from the two wealthiest targets
    r2 = {}
    for i, y in enumerate(As):
        for z in As[i:]:
            n = y + z
            if n <= X:
                r2[n] = r2.get(n, 0) + 1
    wealthy = sorted(r2.items(), key=lambda kv: -kv[1])[:6]
    chain = []
    for i in range(len(wealthy)):
        for j in range(i + 1, len(wealthy)):
            M1, M2 = sorted((wealthy[i][0], wealthy[j][0]))
            S1 = {z for z in As if z <= M1 and (M1 - z) in Aset}
            S2 = {z for z in As if z <= M2 and (M2 - z) in Aset}
            inter = S1 & S2
            if inter:
                d = M2 - M1
                chain.append((d, len(inter), d in Aset, splits(d)))
    chain.sort(key=lambda t: -t[1])

    print(f"\n=== {name}  |A∩[0,{X}]|={alpha} ===")
    print(f"  top differences (d, mult, d∈A): "
          f"{[(d, m, d in Aset) for d, m in top[:5]]}")
    print(f"  popular d (mult ≥ max/2): {len(popular)} of them, "
          f"{pop_in_a} in A ({100 * pop_in_a // max(1, len(popular))}%), "
          f"{pop_split} split in A "
          f"({100 * pop_split // max(1, len(popular))}%)")
    if chain:
        print(f"  chain-produced (d, |S1∩S2|, d∈A, d splits): "
              f"{chain[:4]}")
        got = sum(1 for c in chain if c[2])
        print(f"  chain differences in A: {got}/{len(chain)}")
    else:
        print("  chain: no overlapping symmetry sets among top targets")


FAMILIES = [
    ("room-R1", lambda: build_room(0, "R1")),
    ("room-DD", lambda: build_room(0, "DD")),
    ("room-TD", lambda: build_room(0, "TD")),
    ("mix-thin", lambda: build_mixing(0, "thin")),
    ("mix-random", lambda: build_mixing(0, "random")),
    ("mix-spite", lambda: build_mixing(0, "spite_load")),
    ("odds", lambda: odds_world(0)),
    ("cantor", lambda: cantor_world(0)),
]

for nm, mk in FAMILIES:
    analyse(nm, mk())
