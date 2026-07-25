#!/usr/bin/env python3
"""Pair-destruction supply census (Erdős 881, spread-B endgame).

The enemy needs: for EVERY spread choice (one marker per geometric
window), cofinally many targets whose 3-reps all pass through chosen
markers.  Singleton-owned targets (IsPrivateTriple) are dead (stream
kill), so targets must be owned by PAIRS of markers across scales.
Demand: essentially all cross-scale pairs loaded at cofinal scales.

Census: in covering structures, for cross-scale element pairs (x, y),
count pairs owning >=1 target n <= T with every 3-rep of n hitting
{x, y} (and both actually used, and n has some 3-rep).
"""
import itertools, random

def three_reps(n, A, Aset):
    reps = []
    for a in A:
        if a > n: break
        for b in A:
            if a + b > n: break
            c = n - a - b
            if c >= b and c in Aset:
                reps.append((a, b, c))
    return reps

def main():
    rng = random.Random(42)
    K = 7
    pows = [3**i for i in range(K+1)]
    C = sorted({sum(c) for r in range(K+2) for c in itertools.combinations(pows, r)})
    T = 2 * 3**K
    structures = [("cantor", [x for x in C if x <= T])]
    A0 = set(x for x in C if x <= T)
    for t in range(2):
        A2 = set(A0)
        for _ in range(8): A2.add(rng.randrange(T))
        structures.append((f"cantor+noise{t}", sorted(A2)))
    # random covering-ish sqrt-dense
    R = {0, 1}
    while True:
        holes = [n for n in range(2, T+1)
                 if not any((n-x) in R for x in R if x <= n)]
        if not holes: break
        n = holes[0]
        R.add(n - rng.choice([x for x in R if x <= n]))
    structures.append(("greedy-cover", sorted(R)))

    for name, A in structures:
        Aset = set(A)
        # precompute 3-rep supports for targets in top half
        lo, hi = T//3, T
        loaded_pairs = {}
        singleton = 0
        total_targets = 0
        for n in range(lo, hi+1):
            reps = three_reps(n, A, Aset)
            if not reps: continue
            total_targets += 1
            # support cover analysis: find if a small hitting set exists
            supp = set()
            for r in reps: supp.update(r)
            # try singletons
            sing = [s for s in supp if all(s in r for r in reps)]
            if sing:
                singleton += 1
                continue
            # try pairs (only if few reps)
            if len(reps) <= 12:
                for x, y in itertools.combinations(sorted(supp), 2):
                    if all((x in r) or (y in r) for r in reps):
                        loaded_pairs.setdefault((x, y), []).append(n)
                        break
        npairs_tested = "cross-scale pairs in A: ~{}".format(len(A)*(len(A)-1)//2)
        print(f"{name}: |A|={len(A)} targets[{lo},{hi}] with 3-reps: {total_targets}")
        print(f"   singleton-covered (stream-killed shape): {singleton}")
        print(f"   pair-covered targets: {sum(len(v) for v in loaded_pairs.values())}"
              f" owned by {len(loaded_pairs)} distinct pairs ({npairs_tested})")
        for pr, ns in list(loaded_pairs.items())[:5]:
            print(f"     pair {pr}: targets {ns[:4]}")

if __name__ == "__main__":
    main()
