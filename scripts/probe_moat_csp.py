#!/usr/bin/env python3
"""Moat-CSP enumeration (chain-coherence kernel search).

Small-scale exhaustive: sets A on [0, T] with 0,1 in A, covering
[N0, T], and UNIVERSAL ownership for all a in A with [W1 <= a <= W2]
(each owns some n in (a, 2a): n-a in A, unique big fiber).

Enumerate ALL satisfying A (or sample the space), measure:
  - solution count
  - digit-3 signature / structure of solutions
  - completion-map coherence: do owners share completions?
"""
import itertools

def covers(A, N0, T):
    S = set(A)
    return all(any((n - x) in S for x in A if x <= n)
               for n in range(N0, T + 1))

def owns_some(A, S, a, T):
    for n in range(a + 1, min(2 * a, T + 1)):
        if (n - a) not in S:
            continue
        if all((n - y) not in S
               for y in A if 2 * y > n and y <= n and y != a):
            return n
    return None

def main():
    T, N0, W1, W2 = 26, 4, 8, 13
    base = [0, 1]
    free = list(range(2, T + 1))
    sols = []
    for bits in range(1 << len(free)):
        A = base + [free[i] for i in range(len(free)) if bits >> i & 1]
        if len(A) > 12:  # covering needs some, ownership few; prune size
            continue
        S = set(A)
        if not covers(A, N0, T):
            continue
        mids = [a for a in A if W1 <= a <= W2]
        if not mids:
            continue
        if all(owns_some(A, S, a, T) is not None for a in mids):
            sols.append(A)
    print(f"T={T}: solutions with universal mid-ownership: {len(sols)}")
    from collections import Counter
    sig = Counter()
    comp_share = 0
    for A in sols[:2000]:
        S = set(A)
        mids = [a for a in A if W1 <= a <= W2]
        comps = [owns_some(A, S, a, T) - a for a in mids]
        if len(set(comps)) < len(comps):
            comp_share += 1
        for a in A:
            x = a
            while x:
                sig[x % 3] += 1
                x //= 3
    tot = sum(sig.values()) or 1
    print(f"digit-3 signature over solutions: "
          f"{ {d: round(c/tot, 2) for d, c in sig.items()} }")
    print(f"solutions where owners share completions: {comp_share}/{len(sols)}")
    for A in sols[:6]:
        print("  ", A)

if __name__ == "__main__":
    main()
