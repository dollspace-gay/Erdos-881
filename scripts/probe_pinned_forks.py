#!/usr/bin/env python3
"""Pinned-fork probe (Erdős 881 lab, attack on no_separated_triangle).

THE PINNING LEMMA (to be formalized): let m be destroyed by the team
{p, q} (every exact-3 rep meets the team), let z be an element with
z + max(p,q) < m, and suppose the p-channel of z's bimirror is realized:
w := m - p - z ∈ A.  If additionally p + z has a 2-representation
s + t = p + z with s, t ∈ A ∖ {p, q}, and w ∉ {p, q}, then
m = s + t + w is an exact-3 rep avoiding the team — CONTRADICTION.
Hence an avoiding 2-rep of p + z ("the pin") kills the p-channel: the
bimirror is pinned to the q-channel.

A separated triangle {u < v < w} generates three third-guard forks
(z = the guard not on the edge); each channel of each fork is killed by
an avoiding 2-rep of the corresponding cross-sum g_i + g_j.  The proof
of no_separated_triangle should close by showing every branch
assignment dies.  This probe:

  P1  clique census + fork audit: re-collect the single-scale 3-cliques,
      run every (edge, target, z) fork instance, numerically ASSERT the
      pinning lemma (no realized channel may carry an active pin), and
      tabulate which forks fire and which channels are realized.
  P2  pin census: which cross-sums have avoiding 2-reps (pins active)?
      Prediction: in the toy ground set [0,M] ∪ {g1,g2,g3} no pin can
      ever activate (parts below M sum below the cross-sums; guard
      parts are banned) — the cliques survive by poverty, not strength.
  P3  separated-guard hunt: enrich the ground set with a filler block
      [L, L+K] and search for triangles with g1 far below g2, g3.
      Measure the maximum separation ratio any triangle attains and
      what kills the rest.
  P4  near-miss autopsy: for pairs that fail to form the third edge,
      classify the killer representations — are they of pinned-fork
      type (s + t + w with s + t an avoiding 2-rep of guard + z)?
"""

from __future__ import annotations

from argparse import ArgumentParser
from itertools import combinations

from probe_order3_private_structure import SLACK, pair_sums_mask
from probe_team_guardians import (
    covered_until, has_rep3_avoiding, team_targets,
)


# ------------------------------------------------------------- helpers

def avoiding_2reps(A, n: int, banned: set[int]) -> list[tuple[int, int]]:
    """All 2-reps s + t = n with s <= t, both in A ∖ banned."""
    Aset = set(A) - banned
    out = []
    for s in A:
        if s in banned or 2 * s > n:
            continue
        t = n - s
        if t in Aset:
            out.append((s, t))
    return out


def fork_instances(A, p: int, q: int, m: int, zs) -> list[dict]:
    """Audit the bimirror fork of each z through edge {p,q} at target m.

    Returns one record per firing fork; asserts the bimirror and the
    pinning lemma on every instance (raises on any violation).
    """
    Aset = set(A)
    lo, hi = min(p, q), max(p, q)
    recs = []
    for z in zs:
        if z in (p, q) or z not in Aset:
            continue
        if z + hi >= m:            # bimirror hypothesis fails
            continue
        rec = {"z": z, "channels": {}, "pins": {}}
        for g in (p, q):
            w = m - g - z
            realized = w >= 0 and w in Aset
            w_ok = w not in (p, q)
            pin = bool(avoiding_2reps(A, g + z, {p, q}))
            rec["channels"][g] = realized
            rec["pins"][g] = pin
            # THE PINNING LEMMA, numerically:
            if realized and w_ok and pin:
                s, t = avoiding_2reps(A, g + z, {p, q})[0]
                raise AssertionError(
                    f"PINNING VIOLATED: m={m} team=({p},{q}) z={z} "
                    f"channel {g}: {m}={s}+{t}+{w} avoids the team!")
        # bimirror: some channel must be realized
        assert rec["channels"][p] or rec["channels"][q], (
            f"BIMIRROR VIOLATED: m={m} team=({p},{q}) z={z}")
        recs.append(rec)
    return recs


# ------------------------------------------------------------------ P1

def collect_cliques(Ms) -> list[tuple]:
    """(M, guards, {pair: targets}) for every 3-clique in the toy scan."""
    cliques = []
    for M in Ms:
        for g1 in range(M + 1, 2 * M + 2):
            for g2 in range(g1 + 1, g1 + M + 3):
                for g3 in range(g2 + 1, g2 + M + 3):
                    A = sorted(set(range(M + 1)) | {g1, g2, g3})
                    H = covered_until(A, SLACK)
                    if H < 3 * M + 2:
                        continue
                    pairs = [(g1, g2), (g1, g3), (g2, g3)]
                    tt = {pr: team_targets(A, pr, 3 * M + 1, H)
                          for pr in pairs}
                    if all(tt[pr] for pr in pairs):
                        cliques.append((M, (g1, g2, g3), tt))
    return cliques


def p1_p2(Ms) -> list[tuple]:
    cliques = collect_cliques(Ms)
    print(f"3-cliques collected: {len(cliques)} (Ms={list(Ms)})")
    fired = 0
    profile = {}          # (channels realized per fork) histogram
    pin_active = 0
    pin_total = 0
    for M, (g1, g2, g3), tt in cliques:
        A = sorted(set(range(M + 1)) | {g1, g2, g3})
        elements_small = [z for z in A if z <= M] + [g1, g2, g3]
        for (p, q), targets in tt.items():
            z3 = ({g1, g2, g3} - {p, q}).pop()
            for m in targets:
                recs = fork_instances(A, p, q, m, elements_small)
                for rec in recs:
                    fired += 1
                    key = (rec["channels"][p], rec["channels"][q])
                    profile[key] = profile.get(key, 0) + 1
                    for g in (p, q):
                        pin_total += 1
                        pin_active += rec["pins"][g]
                # the third-guard fork specifically
                third = [r for r in recs if r["z"] == z3]
                if third:
                    profile.setdefault("third-guard forks", 0)
                    profile["third-guard forks"] += len(third)
    print(f"fork instances fired: {fired}; "
          f"channel profile: {profile}")
    print(f"pins active: {pin_active}/{pin_total} channel-instances")
    print("(pinning lemma + bimirror asserted on every instance: "
          "no violation raised)")
    return cliques


# ------------------------------------------------------------------ P3

def p3(M: int, ratio_cap: int = 8) -> None:
    """Separated-guard triangles over [0,M] ∪ {g1} ∪ [L,L+K] ∪ {g2,g3}.

    g1 sits in the low zone; the filler block keeps coverage alive so
    g2, g3 can climb.  Record every triangle found and its separation
    ratio g2/g1; report the maximum, plus what fails beyond it.
    """
    best = []
    tried = 0
    for g1 in range(M + 1, 2 * M + 2):
        for L in range(g1 + 1, g1 + M + 2):
            for K in (M, M + 2):
                top = L + K
                base = set(range(M + 1)) | {g1} | set(range(L, top + 1))
                for g2 in range(top + 1, min(2 * top + 2, ratio_cap * g1)):
                    for g3 in range(g2 + 1, g2 + M + 3):
                        A = sorted(base | {g2, g3})
                        H = covered_until(A, SLACK)
                        if H < g3 + M:
                            continue
                        tried += 1
                        pairs = [(g1, g2), (g1, g3), (g2, g3)]
                        tt = {}
                        ok = True
                        for pr in pairs:
                            ts = team_targets(A, pr, max(pr) + 1, H)
                            if not ts:
                                ok = False
                                break
                            tt[pr] = ts
                        if ok:
                            best.append((g1, L, K, g2, g3,
                                         {pr: tt[pr][:3] for pr in pairs}))
    print(f"M={M}: {tried} covered configs tried; "
          f"separated triangles found: {len(best)}")
    if best:
        best.sort(key=lambda r: r[3] / r[0], reverse=True)
        for r in best[:5]:
            g1, L, K, g2, g3, tt = r
            print(f"  ratio {g2/g1:.2f}: g1={g1}, filler=[{L},{L+K}], "
                  f"g2={g2}, g3={g3}, targets {tt}")
    return best


# ------------------------------------------------------------------ P4

def p4(M: int, samples: int = 40) -> None:
    """Near-miss autopsy: base = toy clique family, but ask why the pair
    (g1, g3) fails when (g1,g2) and (g2,g3) succeed.  For each failed
    target m in range: find a witnessing avoiding rep and classify it:
    PINNED-FORK type if it has the shape s + t + w where s + t = g + z
    for some channel guard g ∈ {g1,g3} and element z (i.e. the rep
    routes through a killed channel), else OTHER."""
    shown = 0
    stats = {"pinned-fork": 0, "other": 0}
    for g1 in range(M + 1, 2 * M + 2):
        for g2 in range(g1 + 1, g1 + M + 3):
            for g3 in range(g2 + 1, g2 + M + 3):
                A = sorted(set(range(M + 1)) | {g1, g2, g3})
                H = covered_until(A, SLACK)
                if H < 3 * M + 2:
                    continue
                e12 = team_targets(A, (g1, g2), 3 * M + 1, H)
                e23 = team_targets(A, (g2, g3), 3 * M + 1, H)
                e13 = team_targets(A, (g1, g3), 3 * M + 1, H)
                if not (e12 and e23) or e13:
                    continue
                # (g1,g3) is the missing edge: autopsy each target
                Aset = set(A)
                for m in range(3 * M + 1, H + 1):
                    if not has_rep3_avoiding(A, m, {g1, g3}):
                        continue      # actually destroyed (can't happen)
                    # find one avoiding rep
                    rep = None
                    for x in A:
                        if x > m or x in (g1, g3):
                            continue
                        for y in A:
                            if y in (g1, g3) or x + y > m:
                                continue
                            zz = m - x - y
                            if zz in Aset and zz not in (g1, g3):
                                rep = (x, y, zz)
                                break
                        if rep:
                            break
                    if rep is None:
                        continue
                    kind = "other"
                    x, y, zz = rep
                    for (a, b, c) in ((x, y, zz), (x, zz, y), (y, zz, x)):
                        for g in (g1, g3):
                            z = a + b - g
                            if 0 <= z != g and z in Aset and z not in (g1, g3):
                                kind = "pinned-fork"
                    stats[kind] += 1
                    if shown < samples and kind == "pinned-fork":
                        shown += 1
                if shown >= samples:
                    break
    print(f"M={M} near-miss killer reps: {stats} "
          f"(pinned-fork = rep routes an avoiding 2-rep through a "
          f"killed channel)")


def main() -> None:
    ap = ArgumentParser()
    ap.add_argument("--Ms", type=int, nargs="*", default=[8, 10, 12])
    ap.add_argument("--sepM", type=int, default=8)
    args = ap.parse_args()

    print("=" * 72)
    print("P1+P2: fork audit + pin census on single-scale 3-cliques")
    print("=" * 72)
    p1_p2(args.Ms)

    print()
    print("=" * 72)
    print("P3: separated-guard triangle hunt (filler-block ground sets)")
    print("=" * 72)
    for M in (6, args.sepM):
        p3(M)

    print()
    print("=" * 72)
    print("P4: near-miss autopsy — what kills the third edge?")
    print("=" * 72)
    p4(args.sepM)


if __name__ == "__main__":
    main()
