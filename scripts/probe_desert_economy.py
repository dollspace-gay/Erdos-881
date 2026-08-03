#!/usr/bin/env python3
"""Finite diagnostic for exclusion interval economy."""

import random

N = 60000
N0 = 10


def build_world(strategy, seed):
    rng = random.Random(seed)
    A = [0, 1]
    Aset = {0, 1}
    pair_sums = set()          # u + v for positive u, v in A
    diff_count = {}            # multiplicity of positive differences
    sumfree_viol = 0

    def register(c):
        nonlocal sumfree_viol
        if c in pair_sums and c > 0:
            sumfree_viol += 1
        for a in A:
            if a != c:
                g = abs(c - a)
                diff_count[g] = diff_count.get(g, 0) + 1
        for a in A:
            if a > 0 and c > 0:
                pair_sums.add(a + c)
        if c > 0:
            pair_sums.add(2 * c)
        A.append(c)
        Aset.add(c)

    def covered3(n):
        for a in A:
            if a > n:
                continue
            m = n - a
            if m == 0 or m in Aset:
                return True
            for b in A:
                if b <= m and (m - b) in Aset:
                    return True
        return False

    for n in range(N0, N + 1):
        if covered3(n):
            continue
        cands = set()
        for a in A:
            if a <= n:
                cands.add(n - a)
                for b in A:
                    if a + b <= n:
                        cands.add(n - a - b)
        cands = [c for c in cands if c > 0 and c not in Aset]
        if not cands:
            register(n)
            continue

        def score(c):
            s = 0.0
            if c in pair_sums:
                s += 1000            # sum-free violation
            for a in A:
                g = abs(c - a)
                if diff_count.get(g, 0) > 0:
                    s += diff_count[g]   # repeated differences
            if strategy == "spread":
                s += -0.001 * c          # prefer large (thin tail)
            elif strategy == "random":
                s += rng.random() * 10
            return s

        best = min(cands, key=score)
        register(best)

    max_fiber = max(diff_count.values()) if diff_count else 0
    return sorted(A), sumfree_viol, max_fiber


def pair_reps(q, Aset):
    reps = []
    for x in Aset:
        if x * 2 > q:
            break
        if (q - x) in Aset:
            reps.append((x, q - x))
    return reps


def economy(A, Z, label):
    Aset = set(A)
    Asorted = sorted(Aset)
    Zset = set(Z)
    survivors = [a for a in Asorted if a not in Zset]
    wounded = []
    for q in range(N0, N + 1):
        reps = [
            (x, q - x) for x in Asorted
            if 2 * x <= q and (q - x) in Aset
        ]
        if not reps:
            continue
        if all(x in Zset or y in Zset for x, y in reps):
            wounded.append(q)
    blocks = {}
    capture_pairs = {}
    deserts = captures = translates = 0
    for q in wounded:
        j = q.bit_length() // 2
        blocks[j] = blocks.get(j, 0) + 1
        caps = []
        for r in survivors:
            if r > q:
                break
            translates += 1
            if (q - r) in Aset:
                captures += 1
                caps.append(r)
            else:
                deserts += 1
        for i in range(len(caps)):
            for j2 in range(i + 1, len(caps)):
                key = (caps[i], caps[j2])
                capture_pairs[key] = capture_pairs.get(key, 0) + 1
    top = max(blocks) if blocks else 0
    cofinal = blocks.get(top, 0) > 0 and blocks.get(top - 1, 0) > 0
    maxmult = max(capture_pairs.values()) if capture_pairs else 0
    drate = deserts / translates if translates else 0.0
    print(f"    Z = {label:22s} |Z|={len(Z):4d} wounded={len(wounded):5d}"
          f" cofinal={'yes' if cofinal else 'NO'}"
          f" desert-rate={drate:.4f}"
          f" captures={captures}"
          f" max-double-capture-mult={maxmult}")
    return cofinal, drate


def main():
    global N
    print("PART A+B: adversarial good-horn worlds")
    affordable = False
    for strategy in ("spread", "random"):
        A, viol, max_fiber = build_world(strategy, seed=881)
        print(f"  world '{strategy}': |A|={len(A)},"
              f" sum-free violations={viol},"
              f" max difference-fiber={max_fiber}")
        Apos = [a for a in A if a > 0]
        zs = [
            ("every 2nd element", Apos[::2]),
            ("smaller pair parts", sorted({
                min(p) for q in range(N0, N + 1)
                for p in pair_reps(q, set(A)) if min(p) > 0})),
            ("upper half by rank", Apos[len(Apos) // 2:]),
        ]
        for label, Z in zs:
            if len(Z) < 5:
                continue
            cof, drate = economy(A, Z, label)
            if cof and drate > 0.95:
                affordable = True

    print("\nPART C: control, base-4 digit world (bad horns)")
    elems = [0]
    for pos in range(9):
        elems += [e + 4 ** pos for e in elems]
    A4 = sorted(e for e in set(elems) if e <= 4 ** 9)
    saveN = N
    N = 4 ** 9
    odd = [a for a in A4 if a % 2 == 1]
    economy(A4, odd, "odd elements (base-4)")
    N = saveN

    print(f"\nVERDICT: deserts"
          f" {'ARE AFFORDABLE' if affordable else 'are NOT affordable'}"
          f" in good-horn worlds"
          f" -> {'pivot to the POSITIVE side' if affordable else 'the counting theorem is the kill shape'}")


if __name__ == "__main__":
    main()
