#!/usr/bin/env python3
"""Probe: adversarial hall worlds vs deletion patterns.

Build A subseteq [0, N] with:
  - pair coverage of [N0, N]
  - a fixed 2-element hall H = {h0, h1} pair-hubbing a sparse cofinal
    target family T (all pairs of t in T meet H), targets are ghosts
  - adversary tries to break candidate deletions' order-3 survival

Then test deletion families B for order-3 coverage of A \\ B on a
safe window. Report survivors."""

import random
import sys

N = 3000
N0 = 20
h0, h1 = 3, 5
H = {h0, h1}


def build_world(seed, partner_choice="h0", spite=None):
    """spite: an optional callable(A, n) -> preferred pair to
    adversarially avoid certain survivals."""
    rng = random.Random(seed)
    A = {0, h0, h1}
    # sparse hubbed ghost targets
    T = []
    t = 64
    while t < N - 10:
        T.append(t)
        t = int(t * 2.1) + rng.randrange(5)
    Tset = set(T)

    def ok_to_add(x):
        # adding x must not give any t in T a non-hall pair
        if x in Tset:
            return False  # ghosts stay out
        for t in T:
            if 0 <= t - x <= N and (t - x) in A and x not in H and (t - x) not in H:
                return False
        return True

    # give each t its hall pairs (partner via h0 and/or h1)
    for t in T:
        if partner_choice in ("h0", "both"):
            if ok_to_add(t - h0):
                A.add(t - h0)
        if partner_choice in ("h1", "both"):
            if ok_to_add(t - h1):
                A.add(t - h1)

    # cover everything
    for n in range(N0, N + 1):
        covered = any((n - a) in A for a in A if 0 <= n - a <= n)
        if covered:
            continue
        # try candidate pairs, adversarially prefer spite's choice
        cands = []
        for a in range(0, n // 2 + 1):
            b = n - a
            if a in A and ok_to_add(b) and b != a:
                cands.append((a, b, 1))  # add one element
            elif ok_to_add(a) and ok_to_add(b) and (a != b):
                cands.append((a, b, 2))
        if not cands:
            continue
        if spite:
            pick = spite(A, n, cands, rng)
        else:
            ones = [c for c in cands if c[2] == 1]
            pick = rng.choice(ones if ones else cands)
        a, b, _ = pick
        if a not in A:
            A.add(a)
        if b not in A:
            A.add(b)
    return A, T


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
        if not any((n - p) in Sset for p in [0] + Sl if 0 <= n - p and ((n - p) in pair or (n - p) == 0 and n in pair)):
            # triple = pair + element
            good = False
            for a in Sl:
                if a > n:
                    break
                if (n - a) in pair or (n - a) == 0:
                    good = True
                    break
            if not good:
                return False, n
    return True, None


def deletions(A, T):
    As = sorted(A)
    parts_h0 = [t - h0 for t in T if (t - h0) in A]
    parts_h1 = [t - h1 for t in T if (t - h1) in A]
    strong = [z for z in As if z > 4 * N0 and (z + h0) not in A and (z + h1) not in A]
    big = [a for a in As if a > 100]
    return {
        "partners_h0": set(parts_h0),
        "partners_h1": set(parts_h1),
        "strong_sparse": set(strong[::3]),
        "every_4th_big": set(big[::4]),
        "geometric": set(a for a in big if any(abs(a - 2 ** k) < 3 for k in range(6, 13))),
    }


def main():
    tally = {}
    for seed in range(8):
        for pc in ("h0", "both"):
            A, T = build_world(seed, pc)
            # sanity: T hubbed & ghosts
            okhub = all(
                all((w in H) or ((t - w) in H) for w in A if 0 < w < t and (t - w) in A)
                for t in T
            )
            for name, B in deletions(A, T).items():
                if len(B) < 4:
                    continue
                S = A - B
                ok, wit = order3_covers(S, N0 + 50, N - 700)
                key = (pc, name)
                tally.setdefault(key, []).append((seed, ok, wit, len(B), okhub))
    for k, v in sorted(tally.items()):
        oks = sum(1 for _, ok, _, _, _ in v if ok)
        print(k, f"{oks}/{len(v)} survive", [w for _, ok, w, _, _ in v if not ok][:3])


if __name__ == "__main__":
    main()
