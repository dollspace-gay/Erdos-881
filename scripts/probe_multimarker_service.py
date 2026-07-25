#!/usr/bin/env python3
"""Multi-marker (log-budget) service demand (post-correction).

Corrected demand: for geometric B = {b_1 < b_2 < ...} (b_{k+1} > 2 b_k),
a failing team-target n (team {u, v}) needs BOTH translates n-u, n-v
2-destroyed by B: every 2-rep of each translate passes through SOME
marker <= translate.  Measure: over covering structures, how many
targets n in a range have both translates B-confined, for the WORST
geometric B we can pick (adversarially for the enemy: B chosen to
dodge)?  Easier version measured here: for a FIXED geometric B, count
targets with both translates confined; compare Cantor vs generic.
"""
import itertools, random

def confined(t, A, Aset, Bset):
    reps = [(x, t - x) for x in A if x <= t - x and (t - x) in Aset]
    if not reps:
        return False  # not covered -> not a legit enemy anyway
    return all((x in Bset) or (y in Bset) for x, y in reps)

def run(name, A, T, u, v, rng):
    Aset = set(A)
    # geometric B inside A
    B = []
    cur = 8
    while cur <= T:
        cands = [a for a in A if a >= cur and a not in (0, u, v)]
        if not cands:
            break
        b = min(cands)
        B.append(b)
        cur = 2 * b + 1
    Bset = set(B)
    good = 0
    total = 0
    for n in range(T // 3, T - v):
        t1, t2 = n - u, n - v
        if t1 < 2 or t2 < 2:
            continue
        total += 1
        if confined(t1, A, Aset, Bset) and confined(t2, A, Aset, Bset):
            good += 1
    print(f"{name}: |B|={len(B)} targets-with-both-translates-confined:"
          f" {good}/{total}")

def main():
    rng = random.Random(5)
    K = 6
    pows = [3**i for i in range(K + 1)]
    C = sorted({sum(c) for r in range(K + 2)
                for c in itertools.combinations(pows, r)})
    T = 2 * 3**K
    run("cantor", [x for x in C if x <= T], T, 1, 4, rng)
    R = {0, 1}
    while True:
        holes = [m for m in range(2, T + 1)
                 if not any((m - x) in R for x in R if x <= m)]
        if not holes:
            break
        m = holes[0]
        R.add(m - rng.choice([x for x in R if x <= m]))
    run("greedy-cover", sorted(R), T, 1, 4, rng)

if __name__ == "__main__":
    main()
