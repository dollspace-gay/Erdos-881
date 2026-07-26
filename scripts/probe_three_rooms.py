#!/usr/bin/env python3
"""Probe: the three terminal rooms (twentieth summit).

Build adversarial covering worlds for each terminal geometry:
  R1  - delta-coherent worlds (rich fixed-difference pairs)
  DD  - doored-desert worlds (one small server u, balanced tails)
  TD  - total-desert worlds (Sidon-ish, all pairs balanced)
Test sparse deletions at order 3 AND record the survival
mechanism per target: pair+0 (order-2 material) vs genuine
triple (three positive parts).  The dominant mechanism per room
tells which formal survival engine to aim there.
"""

import random

N = 3000
N0 = 20


def covered(A, n):
    return any((n - a) in A for a in A if 0 <= n - a)


def build_world(seed, room):
    rng = random.Random(seed)
    A = {0}
    if room == "R1":
        d = 7
        A |= {1, 2, d, d + 1}
        for n in range(N0, N + 1):
            if covered(A, n):
                continue
            # prefer adding delta-paired material
            cands = [n - a for a in sorted(A) if 0 <= n - a]
            x = max(cands) if cands else n
            A.add(x)
            if x + d <= N and rng.random() < 0.8:
                A.add(x + d)
    elif room == "DD":
        u = 3
        A |= {u}
        for n in range(N0, N + 1):
            if covered(A, n):
                continue
            # door service: prefer n-u; else balanced mid pair
            if n - u > N0:
                A.add(n - u)
            else:
                A.add(n // 2)
                A.add(n - n // 2)
        # scrub other small elements to dig the moat
        for x in list(A):
            if 0 < x < 40 and x != u:
                # keep only if removal breaks nothing we can't refix
                A2 = A - {x}
                bad = [n for n in range(N0, N + 1)
                       if not covered(A2, n)]
                if not bad:
                    A = A2
    else:  # TD: balanced Sidon-ish covering
        for n in range(N0, N + 1):
            if covered(A, n):
                continue
            # add a balanced pair with jitter (keeps parts large)
            j = rng.randrange(1, max(2, n // 6))
            a, b = n // 2 - j, n - (n // 2 - j)
            if a > N0:
                A.add(a)
                A.add(b)
            else:
                A.add(n - 1)
                A.add(1)
    return A


def order3_mechanisms(S, lo, hi):
    Sl = sorted(x for x in S if x <= hi)
    Sset = set(Sl)
    pair = set()
    for i, a in enumerate(Sl):
        for b in Sl[i:]:
            if a + b > hi:
                break
            pair.add(a + b)
    fails, via_pair0, via_triple = [], 0, 0
    for n in range(lo, hi + 1):
        p0 = n in pair or (n in Sset)  # pair + 0 (or elt + 0 + 0)
        tri = False
        if not p0:
            for a in Sl:
                if a > n or a == 0:
                    break_ = a > n
                    if break_:
                        break
                if a > 0 and (n - a) in pair:
                    tri = True
                    break
        if p0:
            via_pair0 += 1
        elif tri:
            via_triple += 1
        else:
            fails.append(n)
    return fails, via_pair0, via_triple


def deletions(A):
    big = sorted(a for a in A if a > 150)
    return {
        "every_5th": set(big[::5]),
        "geometric": set(a for a in big
                         if any(abs(a - 2 ** k) < 3
                                for k in range(5, 12))),
        "back_sparse": set(big[len(big) // 2::7]),
    }


def main():
    for room in ("R1", "DD", "TD"):
        for seed in range(3):
            A = build_world(seed, room)
            for name, D in deletions(A).items():
                if len(D) < 4:
                    continue
                S = A - D
                fails, p0, tri = order3_mechanisms(
                    S, N // 2, N - 400)
                status = "SURVIVES" if not fails else \
                    f"FAILS at {fails[:3]}"
                print(f"{room} seed={seed} |A|={len(A):4d} "
                      f"{name:12s} {status}  "
                      f"mech: pair0={p0} triple={tri}")
    print("\n(mechanism counts show which survival engine "
          "each room relies on)")


if __name__ == "__main__":
    main()
