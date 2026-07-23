#!/usr/bin/env python3
"""Probe finite prefixes for order-three private structure (Erdős 881 lab).

A finite set A with 0 ∈ A models a prefix of an exact order-two asymptotic
basis: pair sums must cover [SLACK, top].  A target m is *privately owned*
by a ∈ A if every representation of m as a sum of exactly three elements of
A (zeros allowed) uses a.  Private pairs (a, m) are the finite shadow of
the singleton-destroyer branch of the counterexample analysis.

Structure theory (derived by hand, verified here): a private pair (a, m)
with M := m - a forces
  * desert:  A ∩ (M, m - SLACK) = {a},  hence  a <= 2M (+1),
  * mirror:  A+ ∩ (0, M) symmetric under z -> M - z,
  * gap:     S+S must miss {a} ∪ (a + (S ∩ (0, 2M-a])),  which by the
             mirror symmetry of S+S about M forces  2M - a < SLACK.
So the only candidates are A = S ∪ {a} with S symmetric, a = 2M - D for
some 0 < D < SLACK, and all remaining freedom in S ∩ [0, SLACK].  That is
a small finite space: we enumerate it COMPLETELY (for full middle blocks).

Experiments:
  1. LEVEL-1 ENUMERATION over (D, S ∩ [0, SLACK]) for several M.
  2. STACKING: given a level-k structure, sweep ALL (M', D') for the next
     mirror level and ask whether every previous private pair survives.
     This is the finite version of "can a diabolical keyring exist".
  3. RIGIDITY CHECK on every private pair found (desert + mirror).
  4. OWNER SCAN: which elements own private targets (bulk vs desert).
  5. GIVEAWAY: delete one element per top-level mirror pair; count deaths.
  6. EVEN/ODD-BITS CONTROL: classical minimal order-2 basis.

Bitmask conventions: sets of naturals are Python ints, bit n = n ∈ set.
"""

from __future__ import annotations

import random
from argparse import ArgumentParser

SLACK = 12  # covering is only required from SLACK upward (asymptotic model)


# ---------------------------------------------------------------- masks

def mask_of(A) -> int:
    m = 0
    for x in A:
        m |= 1 << x
    return m


def pair_sums_mask(A) -> int:
    Am = mask_of(A)
    P = 0
    for x in A:
        P |= Am << x
    return P


def triple_sums_mask(A) -> int:
    P = pair_sums_mask(A)
    T = 0
    for x in A:
        T |= P << x
    return T


def range_mask(lo: int, hi: int) -> int:
    return ((1 << (hi + 1)) - 1) ^ ((1 << lo) - 1)


def missing_in_range(present: int, lo: int, hi: int) -> list[int]:
    gap = range_mask(lo, hi) & ~present
    out = []
    while gap:
        low = gap & -gap
        out.append(low.bit_length() - 1)
        gap ^= low
    return out


def covers(A, lo: int, hi: int) -> bool:
    return not (range_mask(lo, hi) & ~pair_sums_mask(A))


# ------------------------------------------------------- representations

def has_rep3(A, m: int) -> bool:
    P = pair_sums_mask(A)
    return any((P >> (m - z)) & 1 for z in A if z <= m)


def is_private(A, a: int, m: int) -> bool:
    """m has a 3-rep, and none avoiding a."""
    rest = [x for x in A if x != a]
    return has_rep3(A, m) and not has_rep3(rest, m)


def one_rep3(A_sorted, Aset, m: int):
    for i, x in enumerate(A_sorted):
        if 3 * x > m:
            break
        rem = m - x
        for y in A_sorted[i:]:
            if 2 * y > rem:
                break
            if (rem - y) in Aset:
                return (x, y, rem - y)
    return None


def essential3(A_sorted, Aset, m: int) -> set[int]:
    """Elements appearing in every exact-3 representation of m."""
    rep = one_rep3(A_sorted, Aset, m)
    if rep is None:
        return set()
    return {e for e in set(rep)
            if not has_rep3([x for x in A_sorted if x != e], m)}


# ------------------------------------------------------------ rigidity

def rigidity_report(A, a: int, m: int) -> list[str]:
    Aset = set(A)
    M = m - a
    bad = []
    for z in Aset:
        if z != a and M < z < m - SLACK:
            bad.append(f"desert violated by element {z} in ({M},{m - SLACK})")
    for z in Aset:
        if 0 < z < M and z != a and z <= m - SLACK and (M - z) not in Aset:
            bad.append(f"mirror violated: {z} in A, {M - z} not in A")
    return bad


# ------------------------------------------------- construction / search

def build_level1(M: int, D: int, small: frozenset[int]):
    """A = S ∪ {a}: S = small ∪ full middle ∪ (M - small), a = 2M - D."""
    if M < 3 * SLACK:
        return None
    S = set(small) | set(range(SLACK + 1, M - SLACK)) | {M - s for s in small}
    a = 2 * M - D
    m = a + M
    A = sorted(S | {a})
    if covers(A, SLACK, m) and is_private(A, a, m):
        return A, a, m
    return None


def enumerate_level1(M: int):
    """Complete enumeration over D in (0, SLACK) and small ⊆ [0, SLACK]
    with 0 ∈ small.  Returns list of (A, a, m)."""
    hits = []
    for D in range(1, SLACK):
        for bits in range(1 << SLACK):
            small = frozenset({0} | {i + 1 for i in range(SLACK)
                                     if bits >> i & 1})
            got = build_level1(M, D, small)
            if got:
                hits.append(got)
    return hits


def stack_level(A_prev, pairs_prev, M2: int, D2: int):
    """Mirror A_prev up to level M2, add a2 = 2*M2 - D2.  Succeeds iff the
    new set pair-covers [SLACK, m2] and ALL private pairs (old and new)
    hold simultaneously."""
    a2 = 2 * M2 - D2
    m2 = a2 + M2
    A2 = sorted(set(A_prev) | {M2 - t for t in A_prev if t <= M2} | {a2})
    if not covers(A2, SLACK, m2):
        return None
    if not is_private(A2, a2, m2):
        return None
    for (a, m) in pairs_prev:
        if not is_private(A2, a, m):
            return None
    return A2, a2, m2


def try_stack(A, pairs, verbose=True):
    """Sweep all (M2, D2) for the next level; return first success."""
    m_top = pairs[-1][1]
    windows = []
    for M2 in range(m_top - 2 * SLACK, 3 * m_top):
        for D2 in range(1, SLACK):
            got = stack_level(A, pairs, M2, D2)
            if got:
                windows.append((M2, D2))
                if len(windows) == 1 and verbose:
                    print(f"    first success at M'={M2}, D'={D2}")
    if not windows:
        return None
    M2, D2 = windows[0]
    if verbose:
        print(f"    {len(windows)} viable (M', D') choices in sweep range")
    A2, a2, m2 = stack_level(A, pairs, M2, D2)
    return A2, pairs + [(a2, m2)]


# ----------------------------------------------------- owners / giveaway

def scan_private_owners(A, lo: int, hi: int) -> dict[int, list[int]]:
    A_sorted = sorted(A)
    Aset = set(A)
    owners: dict[int, list[int]] = {}
    for m in range(lo, hi + 1):
        for e in essential3(A_sorted, Aset, m):
            if e > 0:
                owners.setdefault(e, []).append(m)
    return owners


def mirror_pair_giveaway(A, M: int, protected: set[int],
                         rng: random.Random) -> list[int]:
    B = []
    Aset = set(A)
    for z in sorted(Aset):
        if 0 < z < M - z and z not in protected and (M - z) in Aset \
                and (M - z) not in protected:
            B.append(z if rng.random() < 0.5 else M - z)
    return B


def destroyed_targets(A, B, lo: int, hi: int) -> list[int]:
    keep = sorted(set(A) - set(B))
    return missing_in_range(triple_sums_mask(keep), lo, hi)


# -------------------------------------------------------------- control

def even_odd_basis(nbits: int) -> list[int]:
    evens = [i for i in range(nbits) if i % 2 == 0]
    odds = [i for i in range(nbits) if i % 2 == 1]
    out = set()
    for positions in (evens, odds):
        for k in range(1 << len(positions)):
            out.add(sum(1 << p for j, p in enumerate(positions) if k >> j & 1))
    return sorted(out)


# ----------------------------------------------------------------- main

def main() -> None:
    ap = ArgumentParser()
    ap.add_argument("--seed", type=int, default=881)
    ap.add_argument("--Ms", type=int, nargs="*", default=[40, 50, 60])
    ap.add_argument("--max-depth", type=int, default=4)
    args = ap.parse_args()
    rng = random.Random(args.seed)

    print("=" * 72)
    print("EXPERIMENT 1: complete level-1 enumeration (full middle block)")
    print("=" * 72)
    base = None
    for M in args.Ms:
        hits = enumerate_level1(M)
        print(f"M={M:4d}: {len(hits)} private structures found")
        if hits and base is None:
            A, a, m = hits[0]
            base = (A, [(a, m)])
            print(f"    example: a={a}, m={m}, |A|={len(A)}")
            small = sorted(x for x in A if x <= SLACK)
            print(f"    A∩[0,{SLACK}]={small}, gap D={2*(m-a)-a}")

    if base is None:
        print("\nNO level-1 structure exists in the enumerated family.")
        print("(If the hand-derived shape theorem is right, this means no")
        print(" full-middle order-2-covering prefix has ANY private pair.)")
    else:
        print()
        print("=" * 72)
        print("EXPERIMENT 2: stacking — how deep can private pairs tower?")
        print("=" * 72)
        A, pairs = base
        depth = 1
        while depth < args.max_depth:
            print(f"depth {depth}: pairs={pairs}, |A|={len(A)}, "
                  f"top element={max(A)}")
            nxt = try_stack(A, pairs)
            if nxt is None:
                print(f"    STACKING FAILED: no (M', D') in sweep keeps all "
                      f"{len(pairs)}+1 pairs private")
                break
            A, pairs = nxt
            depth += 1
        else:
            print(f"depth {depth}: pairs={pairs}  (reached max depth)")

        print()
        print("=" * 72)
        print("EXPERIMENT 3: rigidity check on all stacked private pairs")
        print("=" * 72)
        for (a, m) in pairs:
            bad = rigidity_report(A, a, m)
            print(f"pair (a={a}, m={m}): "
                  f"{'PASS' if not bad else 'FAIL'}")
            for line in bad[:6]:
                print(f"    {line}")

        print()
        print("=" * 72)
        print("EXPERIMENT 4: owner scan on the deepest structure")
        print("=" * 72)
        top_m = pairs[-1][1]
        owners = scan_private_owners(A, SLACK, top_m)
        specials = {a for a, _ in pairs}
        bulk_owners = {e: t for e, t in owners.items() if e not in specials}
        print(f"elements owning private targets: {sorted(owners)}")
        print(f"desert guardians: {sorted(specials & set(owners))}")
        print(f"bulk owners (non-guardian): "
              f"{sorted(bulk_owners) if bulk_owners else 'NONE'}")

        print()
        print("=" * 72)
        print("EXPERIMENT 5: one-per-mirror-pair giveaway on deepest level")
        print("=" * 72)
        M_top = pairs[-1][1] - pairs[-1][0]
        protected = specials | {m for _, m in pairs}
        worst, example = 0, None
        for _ in range(20):
            B = mirror_pair_giveaway(A, M_top, protected, rng)
            dead = destroyed_targets(A, B, SLACK, top_m)
            if len(dead) > worst:
                worst, example = len(dead), (len(B), dead)
        if worst == 0:
            print(f"20 random giveaways (one per mirror pair, guardians "
                  f"kept): ALL targets in [{SLACK},{top_m}] survive")
        else:
            nB, dead = example
            print(f"worst giveaway (|B|={nB}) destroyed {len(dead)} targets:"
                  f" {dead[:12]}{'...' if len(dead) > 12 else ''}")

    print()
    print("=" * 72)
    print("EXPERIMENT 6: even/odd-bits minimal basis control")
    print("=" * 72)
    EO = even_odd_basis(12)
    hi = (1 << 12) - 1
    print(f"E∪O 12 bits: |A|={len(EO)}, covering holes: "
          f"{len(missing_in_range(pair_sums_mask(EO), SLACK, hi))}")
    owners = scan_private_owners(EO, SLACK, 2048)
    print(f"private owners in [{SLACK},2048]: "
          f"{sorted(owners) if owners else 'none'}")


if __name__ == "__main__":
    main()
