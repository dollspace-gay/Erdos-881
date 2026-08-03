#!/usr/bin/env python3
"""Finite diagnostic for exclusion cost."""
import itertools, random

def analyze(name, A, T, W):
    Aset = set(A)
    markers = [b for b in A if W <= b <= 2 * W]
    tot_excl = 0
    collisions = 0
    served = 0
    for b in markers:
        # find a serving partner q (unique fiber through (b, q))
        partner = None
        for q in A:
            s = b + q
            if s > T or q == 0:
                continue
            reps = [(x, s - x) for x in A if x <= s - x and (s - x) in Aset]
            if reps == [(min(b, q), max(b, q))]:
                partner = q
                break
        if partner is None:
            continue
        served += 1
        s = b + partner
        for a in A:
            if a in (b, partner) or a > s:
                continue
            tot_excl += 1
            if (s - a) in Aset:
                collisions += 1
    frac = (collisions / tot_excl) if tot_excl else float('nan')
    print(f"{name}: served={served}/{len(markers)} exclusions={tot_excl} "
          f"collisions={collisions} ({frac:.1%})")

def main():
    rng = random.Random(3)
    K = 6
    pows = [3**i for i in range(K + 1)]
    C = sorted({sum(c) for r in range(K + 2)
                for c in itertools.combinations(pows, r)})
    T = 2 * 3**K
    analyze("cantor", [x for x in C if x <= T], T, 3**5)
    R = {0, 1}
    while True:
        holes = [n for n in range(2, T + 1)
                 if not any((n - x) in R for x in R if x <= n)]
        if not holes:
            break
        n = holes[0]
        R.add(n - rng.choice([x for x in R if x <= n]))
    analyze("greedy-cover", sorted(R), T, 3**5)

if __name__ == "__main__":
    main()
