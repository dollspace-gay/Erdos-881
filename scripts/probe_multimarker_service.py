#!/usr/bin/env python3
"""Finite diagnostic for multimarker coverage."""
import itertools, random

def confined(t, A, Aset, Bset):
    reps = [(x, t - x) for x in A if x <= t - x and (t - x) in Aset]
    if not reps:
        return False  # not covered -> not a legit candidate counterexample anyway
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
