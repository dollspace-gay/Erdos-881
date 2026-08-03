#!/usr/bin/env python3
"""Finite diagnostic for nondigit minimal."""

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
    """Finite diagnostic for build world."""
    rng = random.Random(seed)
    cut = (1 << (N + 1)) - 1
    A = [0, 1]
    Aset = {0, 1}
    S1 = 0b11
    S2 = 0b111          # {0,1,2}
    S3 = 0b1111         # {0,1,2,3}

    def add(c):
        nonlocal S1, S2, S3
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
        if strategy == "thin":
            pick = max(cands,
                key=lambda c: c - 40 * sum(
                    1 for x in A if abs(c - x) < 8))
        elif strategy == "low":
            pick = cands[0]
        elif strategy == "antidigit":
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
        add(pick)
        if len(A) > 400:
            return None
    return A


def trim(A):
    """Finite diagnostic for trim."""
    A = list(A)
    mask = (((1 << (N + 1)) - 1) >> N0) << N0
    for a in sorted((x for x in A if x > 1), reverse=True):
        B = [x for x in A if x != a]
        if (reach(B, 3, N) & mask) == mask:
            A = B
    return A





def is_digitlike(A):
    """Finite diagnostic for is digitlike."""
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
        ("random half", (lambda r: [a for a in Apos
                         if r.random() < .5])(random.Random(7))),
        ("random 1/6", (lambda r: [a for a in Apos
                        if r.random() < 1 / 6])(random.Random(11))),
        ("top half", Apos[len(Apos) // 2:]),
    ]
    survivors = 0
    for label, B in fams:
        if len(B) < 4:
            continue
        rest = [a for a in A if a not in set(B)]
        r = reach(rest, 4, N)
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
    complete = 0
    for strategy, seed in (("thin", 1), ("low", 2),
                           ("antidigit", 3), ("random", 4),
                           ("random", 5)):
        A = build_world(strategy, seed)
        if A is None:
            print(f"  world '{strategy}/{seed}':"
                  f" build degenerate (cap hit) — skipped")
            continue
        complete += 1
        A = trim(A)
        s = test_world(f"{strategy}/{seed}", A)
        if s == 0:
            total_resist += 1
    print(f"\nVERDICT: {total_resist} resisting of"
          f" {complete} complete world(s);"
          f" the general positive conjecture"
          f" {'HOLDS in the lab' if total_resist == 0 else 'is CHALLENGED'}")


if __name__ == "__main__":
    main()
