#!/usr/bin/env python3
"""Essential-element structure probe (Erdős 881 lab, Link B1).

Grekos/E–G: an order-2 basis has finitely many 2-essential elements.
For the formalization we need the h = 2 mechanism.  Classical route:
if a is essential, T := co(S+S) (S := A∖{a}) is infinite with
T - a ⊆ S and S ∩ (a + T - T) forced small — congruence structure.

  G1  census: in windowed covering models, how many elements are
      2-essential (removal breaks covering in-window)?  What do the
      broken targets T look like (congruence classes)?
  G2  interaction: for two essentials a < a', is there a shared
      modulus?  (E–G predicts congruence obstructions.)
"""

from __future__ import annotations

import random
import sys

sys.path.insert(0, '/home/doll/erdos881/scripts')
from probe_order3_private_structure import SLACK, pair_sums_mask


def broken(A, T):
    P = pair_sums_mask(A)
    return [n for n in range(SLACK, T + 1) if not ((P >> n) & 1)]


def main() -> None:
    rng = random.Random(2026)
    census = {}
    examples = []
    for trial in range(3000):
        T = rng.randrange(60, 140)
        style = rng.randrange(4)
        if style == 0:
            A = {a for a in range(T) if rng.random() < 0.5} | {0, 1}
        elif style == 1:
            M = rng.randrange(4, 10)
            A = set(range(M + 1))
            q = 2 * M + 1
            while q < T:
                A.add(q)
                A |= set(range(q + 1, min(q + M // 2 + 1, T)))
                q = 2 * q + 1
        elif style == 2:
            A = {0} | {n for n in range(1, T) if n % 2 == 1}
            A |= {2, 4}
        else:
            A = {0, 1, 2} | {rng.randrange(1, T)
                             for _ in range(int(T ** 0.55) * 2)}
        A = sorted(a for a in A if a <= T)
        if broken(A, T - 5):
            continue        # not covering to start with
        ess = []
        for a in A:
            if a == 0:
                continue
            S = [x for x in A if x != a]
            bt = broken(S, T - 5)
            if bt:
                ess.append((a, bt[:6]))
        key = len(ess)
        census[key] = census.get(key, 0) + 1
        if key >= 2 and len(examples) < 4:
            examples.append((A, ess))
    print(f"G1: #essential-elements census over covering models: "
          f"{dict(sorted(census.items()))}")
    for A, ess in examples:
        print(f"  example |A|={len(A)}: essentials:")
        for a, bt in ess[:4]:
            gaps = set(x % 2 for x in bt), set(x % 3 for x in bt)
            print(f"    a={a}: broken targets {bt} "
                  f"(mod2 {gaps[0]}, mod3 {gaps[1]})")


if __name__ == "__main__":
    main()
