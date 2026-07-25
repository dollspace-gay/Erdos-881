#!/usr/bin/env python3
"""Universal ownership census (the classification statement, direct).

OwnsTarget(a, n): a < n < 2a, n-a in A, and a is the ONLY big fiber
element of n (for y in A, n/2 < y <= n, y != a: n-y not in A).

Classification claim: covering + (every late element owns a target)
forces digit structure.  Search: local search for covering sets
maximizing ownership coverage; compare Cantor; inspect survivors.
"""
import itertools, random

def owns(A, Aset, a, T):
    for n in range(a + 1, min(2 * a, T + 1)):
        if (n - a) not in Aset:
            continue
        ok = True
        for y in A:
            if y <= n // 2 or y > n or y == a:
                continue
            if (n - y) in Aset:
                ok = False
                break
        if ok:
            return n
    return None

def coverage(A, T, N0):
    Aset = set(A)
    holes = sum(1 for n in range(N0, T + 1)
                if not any((n - x) in Aset for x in A if x <= n))
    late = [a for a in A if T // 8 <= a <= T // 2]
    owned = sum(1 for a in late if owns(A, Aset, a, T) is not None)
    return holes, owned, len(late)

def main():
    rng = random.Random(17)
    K = 6
    pows = [3**i for i in range(K + 1)]
    C = sorted({sum(c) for r in range(K + 2)
                for c in itertools.combinations(pows, r)})
    T = 2 * 3**K
    h, o, L = coverage([x for x in C if x <= T], T, 10)
    print(f"cantor: holes={h} ownership={o}/{L}")
    # greedy cover baseline
    R = {0, 1}
    while True:
        holes = [m for m in range(2, T + 1)
                 if not any((m - x) in R for x in R if x <= m)]
        if not holes:
            break
        m = holes[0]
        R.add(m - rng.choice([x for x in R if x <= m]))
    h, o, L = coverage(sorted(R), T, 10)
    print(f"greedy: holes={h} ownership={o}/{L}")
    # local search maximizing ownership subject to covering
    A = set(R)
    best = None
    for it in range(400):
        h, o, L = coverage(sorted(A), T, 10)
        score = -h * 100 + o
        if best is None or score > best[0]:
            best = (score, h, o, L, set(A))
        # mutation: remove a big-fiber polluter or add a helper
        a = rng.choice([x for x in sorted(A) if x > 4])
        trial = set(A)
        if rng.random() < 0.5:
            trial.discard(a)
        else:
            trial.add(rng.randrange(5, T))
        th, to, tl = coverage(sorted(trial), T, 10)
        if -th * 100 + to >= score - 2:
            A = trial
    _, h, o, L, Abest = best
    print(f"local-search best: holes={h} ownership={o}/{L} |A|={len(Abest)}")
    # digit signature of the best
    from collections import Counter
    sig = Counter()
    for a in Abest:
        x = a
        while x:
            sig[x % 3] += 1
            x //= 3
    tot = sum(sig.values()) or 1
    print(f"   digit-3 signature: { {d: round(c/tot,2) for d,c in sig.items()} }")

if __name__ == "__main__":
    main()
