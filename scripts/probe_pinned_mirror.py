#!/usr/bin/env python3
"""Finite diagnostic for pinned mirror."""

from __future__ import annotations

from probe_order3_private_structure import SLACK, pair_sums_mask
from probe_team_guardians import covered_until, has_rep3_avoiding, team_targets


def two_reps(A, n, banned=()):
    Aset = set(A) - set(banned)
    return [(s, n - s) for s in sorted(Aset)
            if 2 * s <= n and (n - s) in Aset]


# ------------------------------------------------------------------ V1

def v1() -> None:
    M = 8
    core = sorted(set(range(M + 1)) | {9} | set(range(18, 27)) | {53, 62})
    H = covered_until(core, SLACK)
    T = 400
    A = sorted(set(core) | set(range(H + 1, T + 1)))
    print(f"core covered to H={H}; A = core ∪ [{H + 1},{T}]")
    # full covering of [SLACK, T]?
    P = pair_sums_mask(A)
    gaps = [n for n in range(SLACK, T + 1) if not ((P >> n) & 1)]
    print(f"covering gaps in [{SLACK},{T}]: {gaps if gaps else 'NONE'}")
    guards = (9, 53, 62)
    pairs = [(9, 53), (9, 62), (53, 62)]
    for (p, q) in pairs:
        ts = team_targets(A, (p, q), max(p, q) + 1, T)
        print(f"  pair ({p},{q}): destroyed targets {ts if ts else 'NONE'}")
    ok = all(team_targets(A, pr, max(pr) + 1, T) for pr in pairs)
    print("V1 verdict:", "SEPARATED TRIANGLE IN A COVERING SET — "
          "no_separated_triangle as stated is FALSE" if ok else
          "extension killed the triangle (statement may survive)")


# ------------------------------------------------------------------ V2

def v2() -> None:
    # every edge in the V1 set + the P3 family: check the pinned mirror
    M = 8
    core = sorted(set(range(M + 1)) | {9} | set(range(18, 27)) | {53, 62})
    H = covered_until(core, SLACK)
    A = sorted(set(core) | set(range(H + 1, 401)))
    Aset = set(A)
    total = pinned = mirror_ok = 0
    fails = []
    for (u, v) in [(9, 53), (9, 62), (53, 62)]:
        for m in team_targets(A, (u, v), max(u, v) + 1, 400):
            for x in A:
                if x in (u, v) or x + SLACK > m:
                    continue
                total += 1
                # u-free (and v-free) 2-rep of u + x?
                if not two_reps(A, u + x, banned=(u, v)):
                    continue
                w = m - u - x
                if w in (u, v):
                    continue        # pinning needs the third part free
                pinned += 1
                if (m - v - x) in Aset:
                    mirror_ok += 1
                else:
                    fails.append((u, v, m, x))
    print(f"pinned instances: {pinned}/{total} bimirror-eligible x; "
          f"perfect v-mirror holds on {mirror_ok}/{pinned}")
    print("V2 verdict:", "PINNED PERFECT MIRROR CONFIRMED" if not fails
          else f"FAILURES: {fails[:10]}")


# ------------------------------------------------------------------ V3

def v3() -> None:
    # level-2 destroyed families in the V1 set and in a dense base
    M = 8
    core = sorted(set(range(M + 1)) | {9} | set(range(18, 27)) | {53, 62})
    H = covered_until(core, SLACK)
    A = sorted(set(core) | set(range(H + 1, 401)))
    Aset = set(A)
    N, T = SLACK, 380
    tally = {}
    for n in range(N, T + 1):
        reps = two_reps(A, n)
        if not reps:
            continue
        hitters = set(reps[0])
        for r in reps[1:]:
            hitters &= set(r) | set()
            hitters &= {a for a in hitters if a in r}
        # elements appearing in EVERY 2-rep of n
        common = [a for a in Aset
                  if all(a in r for r in reps)]
        for a in common:
            tally[a] = tally.get(a, 0) + 1
    dens = sorted(((c / (T - N + 1), a) for a, c in tally.items()),
                  reverse=True)
    s = sum(c for c in tally.values()) / (T - N + 1)
    print(f"sum of level-2 guard densities: {s:.3f} (bound: 2)")
    print("top guards:", [(a, f"{d:.3f}") for d, a in dens[:6]])


def main() -> None:
    print("=" * 72)
    print("V1: tail-extension counterexample to no_separated_triangle")
    print("=" * 72)
    v1()
    print()
    print("=" * 72)
    print("V2: the pinned perfect mirror")
    print("=" * 72)
    v2()
    print()
    print("=" * 72)
    print("V3: level-2 guard-density double count")
    print("=" * 72)
    v3()


if __name__ == "__main__":
    main()
