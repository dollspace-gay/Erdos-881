#!/usr/bin/env python3
"""Probe: does the positive pattern leave the digit family?

The verified positive instances (base-3, base-4, and the uniform
digit theorem) are all digit sets.  Erdős 881 asks about ALL
strongly minimal bases.  This probe builds greedy, adversarial,
NON-digit order-3 covering sets, trims them toward elementwise
minimality, and tests whether SOME infinite deletion always
survives at order 4.

It also measures the conjectured general mechanism: do private
(unique-representation) targets emerge in minimal worlds, marking
elements the way the digit diagonals `3b` mark digit worlds?

Verdict rule: a world RESISTS if every tested deletion family fails
at order 4 — such a world is a counterexample candidate.  If no
world resists, the general positive conjecture firms up.
"""

import random

N = 40000
N0 = 12


def covered3(n, A, Aset):
    for a in A:
        if a > n:
            break
        m = n - a
        if m == 0 or m in Aset:
            return True
        for b in A:
            if b > m:
                break
            if (m - b) in Aset:
                return True
    return False


def build_world(strategy, seed):
    """Greedy adversarial exact order-3 covering set (0 included)."""
    rng = random.Random(seed)
    A = [0, 1]
    Aset = {0, 1}
    for n in range(N0, N + 1):
        if covered3(n, A, Aset):
            continue
        cands = set()
        for a in A:
            if a <= n:
                cands.add(n - a)
                for b in A:
                    if a + b <= n:
                        cands.add(n - a - b)
        cands = sorted(c for c in cands
                       if c > 0 and c not in Aset)
        if not cands:
            A.append(n)
            Aset.add(n)
            A.sort()
            continue
        if strategy == "thin":
            pick = cands[-1]
        elif strategy == "low":
            pick = cands[0]
        elif strategy == "antidigit":
            # avoid digit-like structure: prefer candidates that are
            # NOT sums of few powers of any small base
            def digitness(c):
                s = 0
                for base in (3, 4, 5):
                    x = c
                    while x:
                        if x % base > 1:
                            break
                        x //= base
                    else:
                        s += 1
                return s
            nond = [c for c in cands if digitness(c) == 0]
            pick = (nond[len(nond) // 2] if nond
                    else cands[len(cands) // 2])
        else:
            pick = rng.choice(cands)
        A.append(pick)
        Aset.add(pick)
        A.sort()
    return A


def trim(A):
    """Elementwise minimality proxy: drop elements whose removal
    keeps exact order-3 coverage of [N0, N]."""
    A = list(A)
    for a in sorted((x for x in A if x > 1), reverse=True):
        B = [x for x in A if x != a]
        Bset = set(B)
        ok = True
        for n in range(N0, N + 1):
            if not covered3(n, B, Bset):
                ok = False
                break
        if ok:
            A = B
    return A


def reach4(elems, limit):
    cut = (1 << (limit + 1)) - 1
    r = 1
    for _ in range(4):
        nxt = 0
        for a in elems:
            nxt |= r << a
        r = nxt & cut
    return r


def is_digitlike(A):
    """Does A agree with a digit-{0,1} set of some base ≥ 3?"""
    for base in range(3, 12):
        digit = []
        e = [0]
        for pos in range(0, 20):
            if base ** pos > N:
                break
            e += [x + base ** pos for x in e if x + base ** pos <= N]
        dset = set(e)
        agree = sum(1 for a in A if a in dset)
        if agree >= 0.9 * len(A):
            return base
    return 0


def test_world(name, A):
    Apos = [a for a in A if a > 0]
    print(f"  world '{name}': |A|={len(A)}"
          f" digit-like base={is_digitlike(A) or 'no'}")
    tail = N // 4
    fams = [
        ("every 2nd", Apos[::2]),
        ("every 2nd b", Apos[1::2]),
        ("every 3rd", Apos[::3]),
        ("every 5th", Apos[::5]),
        ("geometric ranks", [Apos[i] for i in
                             (2 ** j for j in range(20))
                             if i < len(Apos)]),
        ("random half", [a for a in Apos
                         if random.Random(7).random() < .5]),
        ("random 1/6", [a for a in Apos
                        if random.Random(11).random() < 1 / 6]),
        ("top half", Apos[len(Apos) // 2:]),
    ]
    survivors = 0
    for label, B in fams:
        if len(B) < 4:
            continue
        rest = [a for a in A if a not in set(B)]
        r = reach4(rest, N)
        missed = [n for n in range(tail, N + 1)
                  if not (r >> n) & 1]
        ok = not missed
        survivors += ok
        print(f"    del {label:16s} |B|={len(B):5d}"
              f" order-4 {'SURVIVES' if ok else 'FAILS'}"
              f"{'' if ok else f'  (missed {len(missed)}, first {missed[0]})'}")
    verdict = "RESISTS (candidate!)" if survivors == 0 else "yields"
    print(f"    => world {verdict} ({survivors} surviving deletions)")

    # private-target census: unique order-2 decompositions marking
    # elements (the diagonal mechanism outside digit worlds)
    Aset = set(A)
    private = {}
    for n in range(N0, N + 1):
        reps = [(x, n - x) for x in Apos
                if 2 * x <= n and (n - x) in Aset]
        if len(reps) == 1:
            x, y = reps[0]
            private.setdefault(x, 0)
            private[x] += 1
            private.setdefault(y, 0)
            private[y] += 1
    marked = sum(1 for a in Apos if private.get(a, 0) > 0)
    print(f"    private-pair census: {marked}/{len(Apos)}"
          f" elements own a unique-pair target")
    return survivors


def main():
    print("non-digit minimal worlds, order-3 -> order-4 deletion"
          " survival")
    total_resist = 0
    for strategy, seed in (("thin", 1), ("low", 2),
                           ("antidigit", 3), ("random", 4),
                           ("random", 5)):
        A = build_world(strategy, seed)
        A = trim(A)
        s = test_world(f"{strategy}/{seed}", A)
        if s == 0:
            total_resist += 1
    print(f"\nVERDICT: {total_resist} resisting world(s);"
          f" the general positive conjecture"
          f" {'HOLDS in the lab' if total_resist == 0 else 'is CHALLENGED'}")


if __name__ == "__main__":
    main()
