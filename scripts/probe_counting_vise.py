#!/usr/bin/env python3
"""Counting-vise probe (Erdős 881 lab, Link A / diffuse regime).

For a target m destroyed at order 3 by a deletion set B (0 ∉ B), the
order-2 shadow forces the 2-support S_m = {y ∈ A : m - y ∈ A} inside
B ∪ (m - B), so r₂(m) = |S_m| ≤ 2|B ∩ [0, m]|: destroyed targets of a
sparse B are 2-representation-poor.  The funnel trichotomy
(FunnelTrichotomy.lean) further sorts each destroyed target into
singleton funnel / pair funnel / diffuse.

Questions this probe answers on real basis models:
  C1  in the canonical thin minimal basis (Nathanson even/odd), what is
      the funnel profile of sparse-deletion destroyed targets?  Does
      the diffuse case occur AT ALL in the wild?
  C2  sanity: r₂(m) ≤ 2|B ∩ [0,m]| on every destroyed target (theorem),
      and how tight?
  C3  concentration: max_b r₂(m - b) over b ∈ B — the pigeonhole lever.
  C4  same for a dense basis and the 3-adic basis, and for B of several
      sparsities (every k-th element, geometric).
"""

from __future__ import annotations

import sys

sys.path.insert(0, '/home/doll/erdos881/scripts')

from probe_order3_private_structure import (
    SLACK, even_odd_basis, pair_sums_mask,
)
from probe_thin_bases import gadic_basis


def mask_of(A) -> int:
    m = 0
    for a in A:
        m |= 1 << a
    return m


def two_reps(Aset, m):
    return [(y, m - y) for y in Aset if 2 * y <= m and (m - y) in Aset]


def three_reps(A, m):
    """All 3-reps (x ≤ y ≤ z) of m over sorted A."""
    out = []
    Aset = set(A)
    for i, x in enumerate(A):
        if 3 * x > m:
            break
        for y in A[i:]:
            if x + 2 * y > m:
                break
            z = m - x - y
            if z >= y and z in Aset:
                out.append((x, y, z))
    return out

def destroyed_targets(A, B, lo, hi):
    """Targets in [lo,hi] with a 3-rep in A but none avoiding B."""
    keep = [a for a in A if a not in B]
    P = pair_sums_mask(keep)
    PA = pair_sums_mask(A)
    kset = set(keep)
    out = []
    for m in range(lo, hi + 1):
        # 3-rep in A: z + pair
        has_A = any((PA >> (m - z)) & 1 for z in A if z <= m)
        if not has_A:
            continue
        has_avoid = any((P >> (m - z)) & 1 for z in kset if z <= m)
        if not has_avoid:
            out.append(m)
    return out


def funnel_profile(A, B, m):
    """Classify m: 'singleton'/'pair'/'diffuse' + witness stats."""
    reps = three_reps(A, m)
    Bs = sorted(B)
    # singleton funnel from B?
    for u in Bs:
        if all(u in r for r in reps):
            return 'singleton', u
    for i, u in enumerate(Bs):
        for v in Bs[i + 1:]:
            if all(u in r or v in r for r in reps):
                return 'pair', (u, v)
    return 'diffuse', None


def run_model(name, A, B, lo, hi):
    Aset = set(A)
    Bset = set(B)
    assert 0 not in Bset
    dead = destroyed_targets(A, Bset, lo, hi)
    prof = {'singleton': 0, 'pair': 0, 'diffuse': 0}
    vise_max = 0.0
    conc = []
    diffuse_examples = []
    for m in dead:
        kind, wit = funnel_profile(A, Bset, m)
        prof[kind] += 1
        if kind == 'diffuse' and len(diffuse_examples) < 4:
            diffuse_examples.append(m)
        r2 = len(two_reps(Aset, m))
        beta = sum(1 for b in B if b <= m)
        if beta:
            vise_max = max(vise_max, r2 / (2 * beta))
        assert r2 <= 2 * beta or beta == 0, (m, r2, beta)
        cmax = 0
        for b in B:
            if b <= m:
                cmax = max(cmax, len(two_reps(Aset, m - b)))
        conc.append(cmax)
    print(f"{name}: |A∩[0,{hi}]|={len([a for a in A if a <= hi])} "
          f"|B|={len(B)} destroyed={len(dead)} profile={prof} "
          f"vise-tightness max r2/(2β)={vise_max:.2f} "
          f"concentration max={max(conc) if conc else '-'}")
    if diffuse_examples:
        print(f"    diffuse examples: {diffuse_examples}")
    return prof


def main() -> None:
    # C1: Nathanson even/odd thin basis
    A = even_odd_basis(14)          # covers [0, ~16k]
    hi = 6000
    Aw = [a for a in A if a <= 2 * hi]
    nz = [a for a in Aw if a > 0]
    for label, B in [
        ("evenodd, B=every 5th elt", nz[::5][:40]),
        ("evenodd, B=every 11th elt", nz[::11][:20]),
        ("evenodd, B=geometric", [nz[min(2 ** j, len(nz) - 1)]
                                  for j in range(2, 12)]),
    ]:
        run_model(label, Aw, sorted(set(B)), SLACK + 50, hi)

    # C4: 3-adic basis and a dense basis
    A3 = gadic_basis(3, 8)
    A3w = [a for a in A3 if a <= 6000]
    nz3 = [a for a in A3w if a > 0]
    run_model("3-adic, B=every 7th elt", A3w, sorted(set(nz3[::7][:30])),
              SLACK + 50, 3000)

    dense = sorted(set(range(0, 400)) | set(range(400, 6001, 3)))
    nzd = [a for a in dense if a > 0]
    run_model("dense, B=every 9th elt", dense, sorted(set(nzd[::9][:60])),
              SLACK + 50, 3000)


if __name__ == "__main__":
    main()
