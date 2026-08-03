#!/usr/bin/env python3
"""Finite diagnostic for mixing survival."""

import random

N = 3000
N0 = 20


def build_world(seed, strategy):
    rng = random.Random(seed)
    A = {0, 1, 2, 3}

    def covered(n):
        return any((n - a) in A for a in A if n - a >= 0)

    for n in range(N0, N + 1):
        if covered(n):
            continue
        cands = []
        for a in sorted(A):
            b = n - a
            if b >= 0 and b != a:
                cands.append(b)
        if strategy == "thin":
            # greedy minimal: add the single largest complement
            x = max(cands) if cands else n
            A.add(x)
        elif strategy == "low":
            # prefer small new elements (dense head)
            x = min(c for c in cands if c > 0) if cands else n
            A.add(x)
        elif strategy == "parity_starve_odd":
            # adversary keeps odd channel as thin as possible
            evens = [c for c in cands if c % 2 == 0]
            x = (min(evens) if evens else (max(cands) if cands else n))
            A.add(x)
        elif strategy == "random":
            x = rng.choice(cands) if cands else n
            A.add(x)
        elif strategy == "spite_load":
            # concentrate criticality: reuse one designated partner
            # pool so deletions of it are lethal
            pool = [c for c in cands if c % 8 == 5]
            x = (min(pool) if pool else (max(cands) if cands else n))
            A.add(x)
    # ensure mixing: both parities cofinal (inject sparse fixers)
    step = 97
    for t in range(N0, N, step):
        for par in (0, 1):
            if not any(a >= t and a % 2 == par for a in A):
                A.add(t + (par - t) % 2)
    return A


def order3_covers(S, lo, hi):
    Sl = sorted(x for x in S if x <= hi)
    Sset = set(Sl)
    pair = set()
    for i, a in enumerate(Sl):
        for b in Sl[i:]:
            if a + b > hi:
                break
            pair.add(a + b)
    for n in range(lo, hi + 1):
        ok = False
        for a in Sl:
            if a > n:
                break
            if (n - a) in pair or (n - a) == 0 or (n - a) in Sset:
                # a + (pair) = n (triple), a + 0 + (n-a): needs n-a in S
                if (n - a) in pair:
                    ok = True
                    break
                if (n - a) in Sset:  # a + (n-a) + 0
                    ok = True
                    break
                if n - a == 0:  # a + 0 + 0
                    ok = True
                    break
        if not ok:
            return False, n
    return True, None


def cylinder_deletions(A, m, c):
    """Finite diagnostic for cylinder deletions."""
    W = sorted(x for x in range(N) if (c + (1 << m) * x) in A)
    lift = lambda xs: set(c + (1 << m) * x for x in xs)
    big = [x for x in W if c + (1 << m) * x > 100]
    fams = {
        "every_3rd": lift(big[::3]),
        "every_7th": lift(big[::7]),
        "geometric": lift([x for x in big
                           if any(abs(x - 2 ** k) < 2 for k in range(4, 12))]),
        "back_half_sparse": lift(big[len(big) // 2::5]),
    }
    return {k: v for k, v in fams.items() if len(v) >= 4}


def main():
    tally = {}
    strategies = ["thin", "low", "parity_starve_odd", "random",
                  "spite_load"]
    for seed in range(4):
        for st in strategies:
            A = build_world(seed, st)
            odd_cof = sum(1 for a in A if a > N - 600 and a % 2 == 1)
            even_cof = sum(1 for a in A if a > N - 600 and a % 2 == 0)
            for (m, c) in [(0, 0), (1, 0), (1, 1), (2, 3)]:
                for name, D in cylinder_deletions(A, m, c).items():
                    S = A - D
                    ok, wit = order3_covers(S, N0 + 60, N - 700)
                    key = (st, m, c, name)
                    tally.setdefault(key, []).append(
                        (seed, ok, wit, len(D), odd_cof, even_cof))
    fails = 0
    total = 0
    for k, v in sorted(tally.items()):
        oks = sum(1 for _, ok, *_ in v if ok)
        total += len(v)
        fails += len(v) - oks
        if oks < len(v):
            print("FAIL", k, f"{oks}/{len(v)}",
                  [w for _, ok, w, *_ in v if not ok][:3])
    print(f"\nTOTAL: {total - fails}/{total} deletions survive "
          f"across {len(tally)} (world, cylinder, family) combos")


if __name__ == "__main__":
    main()
