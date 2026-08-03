#!/usr/bin/env python3
"""Finite diagnostic for clean redundancy."""

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
            for b2 in A:
                if 0 < a + b2 <= n:
                    cands.add(n - a - b2)
        cands = sorted(c for c in cands
                       if c > 0 and c not in Aset)
        if not cands:
            add(n)
            continue
        if strategy == "antidigit":
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
        elif strategy == "sidon":
            pick = max(cands)
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


def clean_redundant(A, stack, b, order, horizon):
    """Finite diagnostic for clean redundant."""
    banned = set(stack) | {b}
    rest = [a for a in A if a not in banned]
    r = reach(rest, order, horizon)
    for n in range(b, horizon + 1):
        if not (r >> n) & 1:
            return False, n
    return True, None


def run_chain(name, A, order):
    Apos = [a for a in A if a > 0]
    horizon = N - max(Apos)  # windows fully testable
    stack = []
    rejects = 0
    near_fails = 0
    global_fails = 0
    prev = 0
    log = []
    while True:
        cands = [a for a in Apos
                 if a > prev and a <= horizon // 2]
        picked = None
        for b in cands:
            ok, fail = clean_redundant(
                A, stack, b, order, horizon)
            if ok:
                picked = b
                break
            rejects += 1
            if fail is not None and fail <= b + 64:
                near_fails += 1
            else:
                global_fails += 1
        if picked is None:
            break
        stack.append(picked)
        log.append(picked)
        prev = picked
    print(f"  world '{name}': |A|={len(A)}"
          f" chain length {len(stack)}"
          f" rejects {rejects}"
          f" (near {near_fails} / global {global_fails})")
    if stack:
        head = ", ".join(str(x) for x in stack[:10])
        print(f"    B = [{head}"
              f"{', ...' if len(stack) > 10 else ''}]"
              f" last={stack[-1]}")
    return len(stack), rejects


def main():
    print("clean-redundancy chain probe: does the direct"
          " construction run?")
    worlds = [("digit base-4", digit_world())]
    for strategy, seed in (("antidigit", 3),
                           ("random", 4), ("random", 5),
                           ("sidon", 6)):
        A = build_world(strategy, seed)
        if A is None:
            print(f"  world '{strategy}/{seed}':"
                  f" degenerate — skipped")
            continue
        worlds.append((f"{strategy}/{seed}", trim(A)))
    long_chains = 0
    for name, A in worlds:
        length, rejects = run_chain(name, A, 4)
        if length >= 8:
            long_chains += 1
    print(f"\nVERDICT: {long_chains}/{len(worlds)} worlds"
          f" sustain chains of length >= 8 within the"
          f" window; the clean-redundancy supply is"
          f" {'lab-TRUE' if long_chains == len(worlds) else 'PARTIAL'}")


if __name__ == "__main__":
    main()
