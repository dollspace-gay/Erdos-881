#!/usr/bin/env python3
"""Adversarial checks for `AdaptiveDirect.lean`.

The first test exhausts small finite safe-prefix worlds and checks the exact
local implication used in `not_hasLocalCleanSupply_iff_atomicPinnedTail`.
The second records why the failure bound must be raised to the safe-prefix
coverage threshold.  The third is an exact base-4 digit witness for the
prefix-cleared cone split.  It checks that every cone is either already
destroyed by the old prefix, or every minimal hub destroyer has exactly the
new point outside that prefix.  It also rejects an over-strong cofinal rank
claim: a marked destroyer can still destroy tiny lower-rank targets for old
prefix reasons.  Once those stale targets are excluded, every remaining
lower-rank target is at least the new point.
"""

from itertools import combinations, combinations_with_replacement, product


def reach(elems, order, limit):
    """Bitset of exact `order`-fold sums, with repeated summands allowed."""
    cut = (1 << (limit + 1)) - 1
    result = 1
    for _ in range(order):
        nxt = 0
        for a in elems:
            nxt |= result << a
        result = nxt & cut
    return result


def represented(bits, n):
    return bool((bits >> n) & 1)


def tuple_reps(elems, order, target):
    return [rep for rep in combinations_with_replacement(sorted(elems), order)
            if sum(rep) == target]


def support_family(elems, order, target):
    return sorted({frozenset(rep) for rep in tuple_reps(elems, order, target)},
                  key=lambda s: (len(s), tuple(sorted(s))))


def minimal_destroyers(family, hub):
    """Inclusion-minimal subsets of `hub` hitting every represented support."""
    out = []
    hub = sorted(hub)
    for size in range(len(hub) + 1):
        for choice in combinations(hub, size):
            destroyer = frozenset(choice)
            if not all(support & destroyer for support in family):
                continue
            if any(old < destroyer for old in out):
                continue
            out.append(destroyer)
    return out


def destroys(family, destroyer):
    """The finite version of `DestroysAt`, requiring a represented target."""
    return bool(family) and all(support & destroyer for support in family)


def first_nontrivial_rank_destruction(elems, base_order, destroyer, limit):
    for rank in range(2, base_order):
        for target in range(limit + 1):
            family = support_family(elems, rank, target)
            if family and all(support & destroyer for support in family):
                return rank, target
    return None


def exhaustive_local_check():
    universe = 8
    safe_states = 0
    failures = 0
    for order in range(1, 5):
        horizon = order * universe
        for labels in product(range(3), repeat=universe + 1):
            # 0 = outside A, 1 = surviving A, 2 = prefix F contained in A.
            A = {i for i, label in enumerate(labels) if label}
            F = {i for i, label in enumerate(labels) if label == 2}
            survivors = A - F
            covered = reach(survivors, order, horizon)
            last_hole = max(
                (n for n in range(horizon + 1)
                 if not represented(covered, n)),
                default=-1,
            )
            threshold = last_hole + 1
            candidates = [b for b in survivors if threshold <= b]
            if candidates:
                safe_states += 1
            for b in candidates:
                after = reach(survivors - {b}, order, horizon)
                failure = next(
                    (n for n in range(b, horizon + 1)
                     if not represented(after, n)),
                    None,
                )
                if failure is None:
                    continue
                failures += 1
                # Safe-prefix coverage makes the same target represented
                # before b is removed: precisely the finite PinnedAt test.
                assert represented(covered, failure)
                assert not represented(after, failure)
    print("finite safe-prefix exhaustion")
    print(f"  nonvacuous safe states: {safe_states}")
    print(f"  failed clean candidates: {failures}")
    print("  pinned-tail violations: 0")


def threshold_warning():
    A = {4, 5, 6, 7, 8}
    order = 2
    horizon = 16
    covered = reach(A, order, horizon)
    threshold = max(n for n in range(horizon + 1)
                    if not represented(covered, n)) + 1
    b = 6
    after = reach(A - {b}, order, horizon)
    low_failure = next(n for n in range(b, horizon + 1)
                       if not represented(after, n))
    assert threshold == 8 and low_failure == 6
    assert all(represented(after, n) for n in range(threshold, horizon + 1))
    print("threshold guard")
    print("  h=2, A={4,5,6,7,8}, b=6: failure is only below safe T=8")


def digit_set(base, limit):
    out = set()
    for n in range(limit + 1):
        x = n
        while x:
            if x % base > 1:
                break
            x //= base
        else:
            out.add(n)
    return out


def fmt_set(values):
    return "{" + ",".join(str(x) for x in sorted(values)) + "}"


def base4_bridge_witness():
    A = digit_set(4, 140)
    F = {1, 4, 16}
    b = 65
    target = 70
    hub = F | {b}
    reps = tuple_reps(A, 4, target)
    surviving = [rep for rep in reps if not (set(rep) & F)]
    assert surviving == [(0, 0, 5, 65)]
    assert not [rep for rep in surviving if b not in rep]

    print("exact base-4 marker/rank audit")
    print(f"  all order-4 reps of 70: {len(reps)}")
    print(f"  reps avoiding F={fmt_set(F)}: {surviving}")

    rows = []
    old_cones = []
    marked_cones = []
    for x in sorted(A - hub):
        if target < x:
            continue
        q = target - x
        family = support_family(A, 3, q)
        if not family or not all(support & hub for support in family):
            continue
        for destroyer in minimal_destroyers(family, hub):
            old_cone = destroys(family, F)
            if old_cone:
                old_cones.append((x, q, destroyer))
            else:
                # This is the exact marked-cone conclusion: the hub is
                # F union {b}, and F itself does not hit every support.
                assert b in destroyer
                assert destroyer - F == {b}
                assert b <= q
                marked_cones.append((x, q, destroyer))
            descent = first_nontrivial_rank_destruction(
                A, 3, destroyer, target)
            rows.append((x, q, destroyer, old_cone, descent))
            print(f"  x={x:2d}, q={q:2d}, minimal D={fmt_set(destroyer)}, "
                  f"cone={'old' if old_cone else 'marked'}, "
                  f"first rank descent={descent}")

    owner_row = next(row for row in rows
                     if row[0] == 0 and row[2] == frozenset({1, 65}))
    assert owner_row[3] is False
    assert owner_row[4] == (2, 1)
    assert old_cones
    assert marked_cones

    pointwise_branches = []
    for x, q, destroyer in marked_cones:
        private_reps = [
            rep for rep in tuple_reps(A, 3, q)
            if set(rep) & set(destroyer) == {b}
        ]
        assert private_reps
        for rep in private_reps:
            multiplicity = rep.count(b)
            assert multiplicity
            if multiplicity == 3:
                assert q == 3 * b
                pointwise_branches.append((x, q, "diagonal"))
            elif 2 <= multiplicity:
                hit_target = multiplicity * b
                hit_family = support_family(A, multiplicity, hit_target)
                assert destroys(hit_family, destroyer)
                assert not destroys(hit_family, F)
                assert b <= hit_target
                pointwise_branches.append(
                    (x, q, f"fresh rank {multiplicity} at {hit_target}"))
            else:
                core = tuple(y for y in rep if y != b)
                assert len(core) == 2
                assert sum(core) == q - b
                assert not (set(core) & set(destroyer))
                pointwise_branches.append(
                    (x, q, f"private rank-2 core {core}"))
    print(f"  marked-point private-support forks: {pointwise_branches}")

    destroyer = owner_row[2]
    old_lower = []
    fresh_lower = []
    for rank in range(2, 3):
        for lower_target in range(141):
            family = support_family(A, rank, lower_target)
            if not destroys(family, destroyer):
                continue
            if destroys(family, F):
                old_lower.append((rank, lower_target))
            else:
                fresh_lower.append((rank, lower_target))
                # Any support avoiding F must meet D at its unique new
                # point b, and additive supports are bounded by the target.
                assert b <= lower_target

    assert (2, 1) in old_lower
    assert (2, 65) in fresh_lower
    assert (2, 70) in fresh_lower
    assert not all(b <= q for _rank, q in old_lower + fresh_lower)
    print(f"  old-prefix lower descents through 70: "
          f"{[q for rank, q in old_lower if q <= 70]}")
    print(f"  prefix-cleared lower descents through 70: "
          f"{[q for rank, q in fresh_lower if q <= 70]}")
    print("  rejected: every marked lower-rank descent is cofinal (target 1)")
    print("  survived: every prefix-cleared marked descent has target >= b=65")


def main():
    exhaustive_local_check()
    threshold_warning()
    base4_bridge_witness()


if __name__ == "__main__":
    main()
