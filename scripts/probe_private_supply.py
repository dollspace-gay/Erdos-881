#!/usr/bin/env python3
"""Finite diagnostic for private supply."""
import itertools, random
from collections import Counter

def private_targets(A, Aset, T):
    """Finite diagnostic for private targets."""
    priv = {b: [] for b in A}
    for t in range(2, T + 1):
        reps = [(x, t - x) for x in A if x <= t - x and (t - x) in Aset]
        if not reps:
            continue
        used = set()
        for r in reps:
            used.update(r)
        # b covers all reps?
        for b in used:
            if all(b in r for r in reps):
                priv[b].append(t)
    return priv

def census(name, A, T):
    Aset = set(A)
    priv = private_targets(A, Aset, T)
    counts = Counter(len(v) for v in priv.values())
    multi = {b: v for b, v in priv.items() if len(v) >= 2}
    print(f"{name}: |A|={len(A)} T={T}")
    print(f"  S1 private-count distribution: {dict(sorted(counts.items()))}")
    print(f"  S2 elements with >=2 private targets: {len(multi)}")
    diffs = Counter()
    for b, v in multi.items():
        for i in range(len(v)):
            for j in range(i + 1, len(v)):
                diffs[v[j] - v[i]] += 1
    top = diffs.most_common(6)
    print(f"  S3 recurring private-list differences (top): {top}")

def main():
    rng = random.Random(7)
    K = 7
    pows = [3**i for i in range(K + 1)]
    C = sorted({sum(c) for r in range(K + 2)
                for c in itertools.combinations(pows, r)})
    T = 2 * 3**K
    census("cantor", [x for x in C if x <= T], T)
    R = {0, 1}
    while True:
        holes = [n for n in range(2, T + 1)
                 if not any((n - x) in R for x in R if x <= n)]
        if not holes:
            break
        n = holes[0]
        R.add(n - rng.choice([x for x in R if x <= n]))
    census("greedy-cover", sorted(R), T)
    # random sqrt-dense covering-ish
    S = {0, 1}
    for _ in range(3 * int(T ** 0.5)):
        S.add(rng.randrange(T))
    census("random-sqrt", sorted(S), T)

if __name__ == "__main__":
    main()
