#!/usr/bin/env python3
"""Finite diagnostic for base4 instance."""

import random

BASE = 4          # k + 1 for k = 3
K = 9             # window exponent: targets in [0, BASE^K]


def digit_set(base, top):
    """Finite diagnostic for digit set."""
    elems = [0]
    for pos in range(top + 1):
        elems += [e + base ** pos for e in elems]
    return sorted(set(e for e in elems if e <= base ** top))


def support(n, base):
    pos, s = 0, []
    while n:
        if n % base:
            s.append(pos)
        n //= base
        pos += 1
    return s


def reach(elems, order, limit):
    """Finite diagnostic for reach."""
    cut = (1 << (limit + 1)) - 1
    r = 1
    for _ in range(order):
        nxt = 0
        for a in elems:
            nxt |= r << a
        r = nxt & cut
    return r


def missed(bits, lo, hi):
    return [n for n in range(lo, hi + 1) if not (bits >> n) & 1]


def blocks_profile(miss, base, kmax):
    """Finite diagnostic for blocks profile."""
    per_block = {}
    lower = middle = upper = 0
    for n in miss:
        j = 0
        while base ** (j + 1) <= n:
            j += 1
        per_block[j] = per_block.get(j, 0) + 1
        width = base ** (j + 1) - base ** j
        r = (n - base ** j) / width
        if r < 1 / 3:
            lower += 1
        elif r < 2 / 3:
            middle += 1
        else:
            upper += 1
    blocks = " ".join(f"b{j}:{per_block[j]}"
                      for j in sorted(per_block) if j >= 2)
    return blocks, lower, middle, upper


def main():
    X = BASE ** K
    A = digit_set(BASE, K)
    print(f"base {BASE}, window [0, {X}], |A| = {len(A)}")

    # -- 1: exact order-3 basis, threshold 0 --------------------
    m3 = missed(reach(A, 3, X), 0, X)
    print(f"claim 1  order-3 basis: missed targets = {len(m3)}"
          f"  ({'PASS' if not m3 else 'FAIL'})")

    # -- 2: not an exact order-2 basis --------------------------
    m2 = missed(reach(A, 2, X), 0, X)
    with_digit3 = sum(1 for n in range(X + 1)
                      if any(d == 3 for d in _digits(n)))
    print(f"claim 2  order-2 missed = {len(m2)} of {X + 1}"
          f"  (targets with a digit 3: {with_digit3})"
          f"  ({'PASS' if len(m2) == with_digit3 and m2 else 'FAIL'})")

    # -- 3: unique support at 3b (minimality mechanism) ---------
    sample = [a for a in A if 0 < a <= X // 3]
    bad = []
    for b in random.Random(0).sample(sample, min(40, len(sample))):
        others = [a for a in A if a != b]
        if (reach(others, 3, 3 * b) >> (3 * b)) & 1:
            bad.append(b)
    print(f"claim 3  minimality: 3b representable without b for"
          f" {len(bad)}/40 sampled b  ({'PASS' if not bad else 'FAIL'})")

    # -- 4 + sweep: order-4 survival of infinite deletions ------
    rng = random.Random(881)
    apos = [a for a in A if a > 0]
    powers = [BASE ** j for j in range(1, K + 1)]
    repunits = [(BASE ** m - 1) // (BASE - 1) for m in range(1, K + 1)]
    families = [
        ("pure powers 4^j (j>=1)", powers),
        ("all powers 4^j (j>=0)", [1] + powers),
        ("repunits 11..1", repunits),
        ("powers + repunits", sorted(set(powers + repunits))),
        ("every 2nd element", apos[::2]),
        ("every 2nd (other phase)", apos[1::2]),
        ("every 4th element", apos[::4]),
        ("random half", [a for a in apos if rng.random() < .5]),
        ("random 1/4", [a for a in apos if rng.random() < .25]),
        ("random 1/8", [a for a in apos if rng.random() < .125]),
        ("min digit position even", [a for a in apos
                                     if support(a, BASE)[0] % 2 == 0]),
        ("odd digit count", [a for a in apos
                             if len(support(a, BASE)) % 2 == 1]),
        ("contains position 0", [a for a in apos
                                 if support(a, BASE)[0] == 0]),
        ("top position even", [a for a in apos
                               if support(a, BASE)[-1] % 2 == 0]),
        ("ALL compound (control)", [a for a in apos
                                    if len(support(a, BASE)) >= 2]),
    ]
    tail = BASE ** (K - 2)     # survival = last two blocks clean
    print(f"\norder-4 sweep (survival judged on ({tail}, {X}]):")
    survivors = failures = 0
    for name, B in families:
        Bset = set(B)
        rest = [a for a in A if a not in Bset]
        # every family must destroy order 3 at the doubles 3b
        b0 = next(b for b in sorted(Bset) if 3 * b <= X)
        dead3 = not (reach(rest, 3, 3 * b0) >> (3 * b0)) & 1
        m4 = missed(reach(rest, 4, X), 1, X)
        late = [n for n in m4 if n > tail]
        verdict = "SURVIVES" if not late else "FAILS"
        if late:
            failures += 1
            blocks, low, mid, up = blocks_profile(
                [n for n in m4 if n >= 16], BASE, K)
            geo = (f"\n      per-block {blocks}"
                   f"  thirds: lower {low} middle {mid} upper {up}")
        else:
            survivors += 1
            geo = ""
        thr = (max(m4) + 1) if m4 else 0
        print(f"  {name:28s} |B|={len(B):4d} kills-order-3:"
              f"{'yes' if dead3 else 'NO!'}  order-4 {verdict}"
              f" (threshold {thr}){geo}")
    print(f"\nsweep: {survivors} survive, {failures} fail"
          f" of {len(families)} families")

    # -- generalization: k = 4 (base 5, order 4 -> 5) -----------------
    print("\ngeneralization check, k = 4 (base 5):")
    b5, k5 = 5, 7
    x5 = b5 ** k5
    A5 = digit_set(b5, k5)
    m_ok = missed(reach(A5, 4, x5), 0, x5)
    m_no2 = missed(reach(A5, 2, x5), 0, x5)
    p5 = set(b5 ** j for j in range(1, k5 + 1))
    r5 = [a for a in A5 if a not in p5]
    m_surv = [n for n in missed(reach(r5, 5, x5), 1, x5)
              if n > 3 * b5 ** (k5 - 1)]
    thr5 = missed(reach(r5, 5, x5), 1, x5)
    print(f"  order-4 basis: missed {len(m_ok)};"
          f" order-2 missed {len(m_no2)} of {x5 + 1};"
          f" powers-deletion order-5"
          f" {'SURVIVES' if not m_surv else 'FAILS'}"
          f" (threshold {(max(thr5) + 1) if thr5 else 0})")


def _digits(n):
    while n:
        yield n % BASE
        n //= BASE


if __name__ == "__main__":
    main()
