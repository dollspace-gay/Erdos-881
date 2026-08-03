#!/usr/bin/env python3
"""Finite diagnostic for profile region."""

import math

def feasible(n, a1, W1, a2, W2, c, df):
    # 1. sqrt-growth
    if a1 * a1 < n - 50 or a2 * a2 < 2 * n - 50:
        return False, "growth"
    # 2. closed two-scale funding
    lhs = a1 ** 4
    rhs = (2 * n + 1) * ((n + 1) * c * c + W1 * a1 * a1 +
                         (2 * n + 1) * c * c + W2 * a2 * a2)
    if lhs > rhs:
        return False, "funding"
    # 3. census at both scales
    if a1 + W1 > n + 1 + 2 * df or a2 + W2 > 2 * n + 1 + 2 * df:
        return False, "census"
    # 4. basic sanity
    if a1 > n + 1 or a2 > 2 * n + 1 or a2 < a1:
        return False, "sanity"
    return True, ""

def main():
    n = 10 ** 6
    c = df = 20
    print(f"n={n:.0e} c=df={c}")
    # scan alpha as fraction of n; W minimal to satisfy funding
    print("alpha/n : minimal W1 satisfying funding (W2=W1*2) : census ok?")
    for frac in (0.001, 0.01, 0.05, 0.1, 0.3, 0.5, 0.7, 0.73,
                 0.75, 0.8, 0.9, 1.0):
        a1 = int(frac * n)
        if a1 * a1 < n:
            a1 = int(math.isqrt(n)) + 1
        a2 = 2 * a1
        # minimal W1 from funding (W2 = 2*W1 heuristic)
        noise = (n + 1) * c * c + (2 * n + 1) * c * c
        need = a1 ** 4 / (2 * n + 1) - noise
        if need <= 0:
            W1min = 0
        else:
            W1min = need / (a1 * a1 + 2 * (a2 * a2))
        W1 = int(W1min) + 1
        ok, why = feasible(n, a1, W1, a2, 2 * W1, c, df)
        print(f"  {frac:5.3f} : W1_min={W1:>9d} : "
              f"{'FEASIBLE' if ok else 'INFEASIBLE (' + why + ')'}")

if __name__ == "__main__":
    main()
