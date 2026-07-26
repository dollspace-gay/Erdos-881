#!/usr/bin/env python3
"""Probe: the bypass question (eleventh summit follow-up).

For a deletion confined to class c* mod 2^j, failing targets are
residue-chained: EVERY pair rep touches c*.  The kill would be:
in mixing covering worlds, for every deep class c*, only
finitely many targets are chained to c*.

Count chained targets per (world, modulus 2^j, class c*):
n in [lo, hi] is CHAINED to c* iff n has >= 1 pair rep and every
pair rep (x, n-x) has x = c* or n-x = c* (mod 2^j).

Also count chained-with-poverty (r2 <= cap) since failing
targets must be poor too.
"""

import random
import sys
sys.path.insert(0, 'scripts')
from probe_mixing_survival import build_world, N, N0


def chained_counts(A, j, lo, hi):
    mod = 1 << j
    As = sorted(A)
    Aset = set(As)
    out = {}
    for cstar in range(mod):
        chained = []
        for n in range(lo, hi):
            reps = [(x, n - x) for x in As
                    if x <= n // 2 and (n - x) in Aset]
            if not reps:
                continue
            if all(x % mod == cstar or y % mod == cstar
                   for x, y in reps):
                chained.append(n)
        out[cstar] = chained
    return out


def main():
    strategies = ["thin", "low", "parity_starve_odd", "random",
                  "spite_load"]
    print(f"window [{N//2}, {N-50}], moduli 4 and 8")
    worst = 0
    for seed in range(3):
        for st in strategies:
            A = build_world(seed, st)
            for j in (2, 3):
                out = chained_counts(A, j, N // 2, N - 50)
                tot = {c: len(v) for c, v in out.items() if v}
                late = {c: len([n for n in v if n > N - 400])
                        for c, v in out.items()
                        if any(n > N - 400 for n in v)}
                if tot:
                    worst = max(worst, max(tot.values()))
                    print(f"seed={seed} {st:18s} mod {1<<j}: "
                          f"chained={tot} late-chained={late}")
    print(f"\nworst chained count in any class: {worst}")
    print("(cofinal chaining would show large late-chained counts)")


if __name__ == "__main__":
    main()
