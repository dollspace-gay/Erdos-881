#!/usr/bin/env python3
"""Probe: are adversarial minimal order-3 bases forced to be
carry-poor, the way the verified enemy profile predicts?

The k = 2 engine and the Cantor instance say a counterexample must
be Cantor-like yet CARRY-POOR: no internal merge slack (few ways
to trade several elements for one), low additive energy, rigid
representations.  The verified positive digit worlds are the
opposite: carry-RICH by construction (k+1 ones merge into the next
scale), and that richness is exactly what the deletion theorem
spends.

This probe builds worlds that try their hardest to be carry-poor —
Sidon-biased greedy (minimize new pair-sum collisions) and
octave-spread greedy — trims them toward elementwise minimality,
and measures:

  - additive-energy excess (pair-sum collisions beyond the Sidon
    floor), before and after trim;
  - internal merge capacity: elements expressible as sums of m
    positive elements (m = 2, 3, 4) — the carry analogue;
  - order-3 representation multiplicity on the tail;
  - deletion survival at order 4 and the private-pair census.

The base-4 digit world runs as the carry-rich reference.

Reading: if even deliberately carry-poor minimal worlds either
(a) regrow carry events under the basis constraint, or (b) still
yield surviving deletions, the enemy's room shrinks from both
sides.
"""

import random

N = 20000
N0 = 12


def reach(elems, order, limit):
    cut = (1 << (limit + 1)) - 1
    r = 1
    for _ in range(order):
        nxt = 0
        for a in elems:
            nxt |= r << a
        r = nxt & cut
    return r


def build_world(strategy, seed):
    rng = random.Random(seed)
    cut = (1 << (N + 1)) - 1
    A = [0, 1]
    Aset = {0, 1}
    S1 = 0b11
    S2 = 0b111
    S3 = 0b1111
    pair_sums = {0: 1, 1: 2, 2: 1}

    def add(c):
        nonlocal S1, S2, S3
        for a in A:
            pair_sums[a + c] = pair_sums.get(a + c, 0) + 1
        pair_sums[2 * c] = pair_sums.get(2 * c, 0) + 1
        A.append(c)
        Aset.add(c)
        A.sort()
        S1 |= 1 << c
        S2 = (S2 | (S1 << c)) & cut
        S3 = (S3 | (S2 << c)) & cut

    for n in range(N0, N + 1):
        if (S3 >> n) & 1:
            continue
        cands = set()
        for a in A:
            if 0 < a <= n:
                cands.add(n - a)
            for b in A:
                if 0 < a + b <= n:
                    cands.add(n - a - b)
        cands = sorted(c for c in cands
                       if c > 0 and c not in Aset)
        if not cands:
            add(n)
            continue
        if strategy == "sidon":
            def collisions(c):
                s = sum(1 for a in A
                        if (a + c) in pair_sums)
                s += (2 * c) in pair_sums
                return s
            best = min(collisions(c) for c in cands)
            pick = max(c for c in cands
                       if collisions(c) == best)
        elif strategy == "spread":
            def crowding(c):
                oct_mates = sum(
                    1 for a in A
                    if a > 0 and
                    a.bit_length() == c.bit_length())
                near = sum(1 for a in A
                           if abs(a - c) < 16)
                return 4 * oct_mates + near
            best = min(crowding(c) for c in cands)
            pick = max(c for c in cands
                       if crowding(c) == best)
        else:
            pick = rng.choice(cands)
        add(pick)
        if len(A) > 400:
            return None
    return A


def trim(A):
    A = list(A)
    mask = (((1 << (N + 1)) - 1) >> N0) << N0
    for a in sorted((x for x in A if x > 1),
                    reverse=True):
        B = [x for x in A if x != a]
        if (reach(B, 3, N) & mask) == mask:
            A = B
    return A


def digit_world():
    e = [0]
    for pos in range(0, 20):
        if 4 ** pos > N:
            break
        e += [x + 4 ** pos for x in e
              if x + 4 ** pos <= N]
    return sorted(set(e))


def energy_excess(A):
    """Pair-sum collisions beyond the Sidon floor, per |A|^2."""
    sums = {}
    Apos = [a for a in A if a >= 0]
    n = len(Apos)
    for i in range(n):
        for j in range(i, n):
            s = Apos[i] + Apos[j]
            sums[s] = sums.get(s, 0) + 1
    excess = sum(c * (c - 1) // 2
                 for c in sums.values())
    return excess, excess / (n * n)


def merge_capacity(A):
    """Elements of A expressible as sums of m positive elements."""
    Apos = [a for a in A if a > 0]
    out = []
    for m in (2, 3, 4):
        r = reach(Apos, m, N)
        cnt = sum(1 for a in Apos if (r >> a) & 1)
        out.append(cnt)
    return out


def rep_multiplicity(A):
    """Order-3 multiset representation counts on the tail."""
    Apos = sorted(a for a in A if a >= 0)
    lo, hi = N // 2, N
    counts = {}
    n_ = len(Apos)
    for i in range(n_):
        ai = Apos[i]
        if 3 * ai > hi:
            break
        for j in range(i, n_):
            s2 = ai + Apos[j]
            if s2 + Apos[j] > hi:
                break
            for l in range(j, n_):
                s = s2 + Apos[l]
                if s > hi:
                    break
                if s >= lo:
                    counts[s] = counts.get(s, 0) + 1
    vals = [counts.get(x, 0) for x in range(lo, hi + 1)]
    covered = [v for v in vals if v > 0]
    if not covered:
        return 0, 0, 0
    mean = sum(covered) / len(covered)
    uniq = sum(1 for v in covered if v == 1)
    return mean, max(covered), uniq / len(covered)


def deletion_and_census(A):
    Apos = [a for a in A if a > 0]
    tail = N // 4
    fams = [
        ("every 2nd", Apos[::2]),
        ("every 3rd", Apos[::3]),
        ("every 5th", Apos[::5]),
        ("geometric ranks", [Apos[i] for i in
                             (2 ** j for j in range(20))
                             if i < len(Apos)]),
        ("random half", (lambda r: [a for a in Apos
            if r.random() < .5])(random.Random(7))),
        ("top half", Apos[len(Apos) // 2:]),
    ]
    survivors = 0
    for label, B in fams:
        if len(B) < 4:
            continue
        rest = [a for a in A if a not in set(B)]
        r = reach(rest, 4, N)
        ok = all((r >> n) & 1
                 for n in range(tail, N + 1))
        survivors += ok
    Aset = set(A)
    private = set()
    for n in range(N0, N + 1):
        reps = [(x, n - x) for x in Apos
                if 2 * x <= n and (n - x) in Aset]
        if len(reps) == 1:
            private.add(reps[0][0])
            private.add(reps[0][1])
    marked = sum(1 for a in Apos if a in private)
    return survivors, len(fams), marked, len(Apos)


def report(name, A, trimmed):
    tag = "trimmed" if trimmed else "raw    "
    exc, rate = energy_excess(A)
    m2, m3, m4 = merge_capacity(A)
    mean, mx, urate = rep_multiplicity(A)
    print(f"  {name:14s} {tag} |A|={len(A):4d}"
          f"  energy-excess={exc:6d}"
          f" ({rate:.3f}/elt^2)"
          f"  merge m2/m3/m4={m2}/{m3}/{m4}"
          f"  r3 mean={mean:6.1f} max={mx:5d}"
          f" unique={urate:.0%}")


def main():
    print("carry-poverty probe: can minimal order-3 worlds"
          " stay carry-poor?")
    D = digit_world()
    report("digit base-4", D, False)
    s, t, m, tot = deletion_and_census(D)
    print(f"    deletions survive {s}/{t};"
          f" private census {m}/{tot}")
    poor_stays_poor = 0
    complete = 0
    for strategy, seed in (("sidon", 1), ("sidon", 2),
                           ("spread", 3), ("random", 4)):
        A = build_world(strategy, seed)
        name = f"{strategy}/{seed}"
        if A is None:
            print(f"  {name}: build degenerate (cap hit)"
                  f" — skipped")
            continue
        complete += 1
        report(name, A, False)
        raw_exc, raw_rate = energy_excess(A)
        At = trim(A)
        report(name, At, True)
        exc, rate = energy_excess(At)
        m2, m3, m4 = merge_capacity(At)
        s, t, m, tot = deletion_and_census(At)
        print(f"    deletions survive {s}/{t};"
              f" private census {m}/{tot}")
        if m3 == 0 and m4 == 0:
            poor_stays_poor += 1
    print(f"\nVERDICT: {poor_stays_poor} of {complete}"
          f" adversarial worlds keep zero internal merge"
          f" capacity after trim;"
          f" carry events"
          f" {'CAN be starved' if poor_stays_poor else 'are FORCED back'}"
          f" in the lab")


if __name__ == "__main__":
    main()
