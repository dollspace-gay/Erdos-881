#!/usr/bin/env python3
"""Total rigidity + covering search (Erdős 881, V11 classification).

Demand: A covers [N0, T] at order 2 AND every b in A with
2b <= T has r2(2b) = 1 (only rep (b, b)).  Cantor satisfies both.
Question: does anything else?  Greedy + local search + structure
signature of survivors (base-3 digit histogram).
"""
import itertools, random

def check(A, N0, T):
    Aset = set(A)
    holes = [n for n in range(N0, T + 1)
             if not any((n - x) in Aset for x in A if x <= n - x >= 0 and x <= n)]
    viol = []
    for b in A:
        if 2 * b > T or b == 0:
            continue
        reps = [(x, 2 * b - x) for x in A
                if x <= b and (2 * b - x) in Aset]
        extra = [r for r in reps if r != (b, b)]
        if extra:
            viol.append((b, extra[:2]))
    return holes, viol

def greedy_rigid_cover(T, N0, rng, order):
    """add elements to fix coverage holes, skipping additions that
    break rigidity of existing doubles."""
    A = {0, 1}
    for n in order:
        Aset = A
        if any((n - x) in Aset for x in A if x <= n):
            continue
        # choose a pair (a, n-a) minimizing rigidity damage
        best = None
        cands = list(range(0, n // 2 + 1))
        rng.shuffle(cands)
        for a in cands[:60]:
            b = n - a
            trial = A | {a, b}
            tset = trial
            damage = 0
            for c in (a, b):
                for x in trial:
                    if x == c:
                        continue
                    # does adding c create a non-diagonal rep of some 2y?
                    s = c + x
                    if s % 2 == 0 and s // 2 in trial and s // 2 != c and s // 2 != x:
                        damage += 1
            if best is None or damage < best[0]:
                best = (damage, a, b)
            if best[0] == 0:
                break
        _, a, b = best
        A.add(a)
        A.add(b)
    return sorted(A)

def digit3_signature(A):
    from collections import Counter
    sig = Counter()
    for a in A:
        x = a
        while x:
            sig[x % 3] += 1
            x //= 3
    tot = sum(sig.values()) or 1
    return {d: round(c / tot, 2) for d, c in sig.items()}

def main():
    rng = random.Random(11)
    T, N0 = 1200, 6
    for trial, order in [("inorder", list(range(N0, T + 1))),
                         ("random", rng.sample(range(N0, T + 1), T + 1 - N0))]:
        A = greedy_rigid_cover(T, N0, rng, order)
        holes, viol = check(A, N0, T)
        print(f"greedy({trial}): |A|={len(A)} holes={len(holes)} "
              f"rigidity-violations={len(viol)}")
        print(f"   digit-3 signature: {digit3_signature(A)} "
              f"(Cantor would be ~{{0: .67, 1: .33}} with no 2s)")
        if viol[:2]:
            print(f"   sample violations: {viol[:2]}")
    K = 6
    pows = [3**i for i in range(K + 1)]
    C = sorted({sum(c) for r in range(K + 2)
                for c in itertools.combinations(pows, r)})
    holes, viol = check([x for x in C if x <= 1200], N0, 1200)
    print(f"cantor: holes={len(holes)} rigidity-violations={len(viol)}")

if __name__ == "__main__":
    main()
