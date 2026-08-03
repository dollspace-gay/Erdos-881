#!/usr/bin/env python3
"""Finite diagnostic for private core stream."""

from itertools import combinations, product

from probe_adaptive_local import (
    destroys,
    digit_set,
    support_family,
    tuple_reps,
)


def delta_root(cores):
    intersections = [cores[i] & cores[j]
                     for i in range(len(cores))
                     for j in range(i + 1, len(cores))]
    assert intersections
    root = intersections[0]
    assert all(intersection == root for intersection in intersections)
    return root


def base4_fixed_core_stream():
    """Finite diagnostic for base4 fixed core stream."""
    F = {1, 4, 16}
    cores = []
    rows = []
    old_parts = []
    for exponent in range(3, 7):
        b = 4 ** exponent + 1
        q = b + 5
        A = digit_set(4, q)
        D = {1, b}
        family = support_family(A, 3, q)
        assert destroys(family, D)
        assert not destroys(family, F)
        assert not destroys(family, {1})
        assert not destroys(family, {b})
        private = [rep for rep in tuple_reps(A, 3, q)
                   if set(rep) & D == {b}]
        assert private == [(0, 5, b)]
        # The fixed marked element is 0, so reinsertion reconstructs the original
        # successor-rank support without changing the target label.
        assert (0, 0, 5, b) in tuple_reps(A, 4, q)
        core = frozenset(x for x in private[0] if x != b)
        assert core == frozenset({0, 5})
        assert q - b == 5
        assert D - F == {b}
        old_parts.append(frozenset(D & F))
        cores.append(core)
        rows.append((b, q, tuple(sorted(core)), q - b))

    root = delta_root(cores)
    assert root == frozenset({0, 5})
    assert all(not (core - root) for core in cores)
    assert set(old_parts) == {frozenset({1})}
    # Exactness does not eliminate this case: the fixed digit basis realizes
    # it. Instead split the moving markers, delete one half, and lift the
    # retained order-three supports by the fixed apex 0 ∈ R. The support
    # finset stays {0,5,b}, while its tuple order rises from three to four.
    deleted_markers = {row[0] for row in rows[::2]}
    retained_rows = rows[1::2]
    assert deleted_markers
    assert all(not ({0, 5, b} & deleted_markers)
               for b, _q, _core, _residual in retained_rows)
    assert all((0, 0, 5, b) in
               tuple_reps(digit_set(4, q), 4, q)
               for b, q, _core, _residual in retained_rows)
    print("exact base-4 fixed-core stream")
    print(f"  rows (marker, cone, core, residual): {rows}")
    print("  horn: core {0,5}, residual 5, and old destroyer part {1} are fixed")
    print("  rejected: exactness eliminates the fixed horn")
    print("  survived: split markers convert the fixed horn to successor survival")


def moving_petal_deletion_stream():
    """Finite diagnostic for moving disjoint remainder deletion stream."""
    count = 20

    # Empty root: pairwise-disjoint order-two cores.
    markers = [1000 + 100 * i for i in range(count)]
    cores = [frozenset({10 * i + 2, 10 * i + 3})
             for i in range(count)]
    lower_supports = [core | {marker}
                      for marker, core in zip(markers, cores)]
    apices = [20000 + 100 * i for i in range(count)]
    supports = [lower | {apex}
                for lower, apex in zip(lower_supports, apices)]
    targets = [sum(support) for support in supports]
    assert delta_root(cores) == frozenset()
    deletion = set().union(*(cores[i] for i in range(0, count, 2)))
    assert deletion
    assert all(not (supports[i] & deletion) for i in range(1, count, 2))
    assert all(targets[i] < targets[i + 2]
               for i in range(1, count - 2, 2))

    # Fixed root with disjoint nonempty remainders. A fixed conflict alone
    # does not force termination; the moving remainders still yield deletion.
    rooted_cores = [frozenset({0, 5, 20 + 10 * i})
                    for i in range(count)]
    rooted_markers = [5000 + 100 * i for i in range(count)]
    rooted_lower_supports = [core | {marker}
                             for marker, core in
                             zip(rooted_markers, rooted_cores)]
    rooted_apices = [30000 + 100 * i for i in range(count)]
    rooted_supports = [lower | {apex}
                       for lower, apex in
                       zip(rooted_lower_supports, rooted_apices)]
    root = delta_root(rooted_cores)
    assert root == frozenset({0, 5})
    petals = [core - root for core in rooted_cores]
    rooted_deletion = set().union(*(petals[i]
                                    for i in range(0, count, 2)))
    assert all(not (rooted_supports[i] & rooted_deletion)
               for i in range(1, count, 2))

    # These labels are cofinal in the infinite pattern but sparse. Their
    # survival alone cannot be advertised as eventual basis coverage.
    assert any(targets[i + 2] - targets[i] > 1
               for i in range(1, count - 2, 2))

    # Fat/interval junk satisfies the same support/deletion endpoint. This
    # is a useful non-vacuity warning: arithmetic obstruction enters only in
    # the alternative fixed-core branch or in a later coverage argument.
    fat_A = set(range(max(rooted_apices) + 1))
    assert all(support <= fat_A for support in rooted_supports)

    # In contrast, the aligned terminal pattern retains a genuine
    # obstruction: one fixed old prefix P plus the moving marker must destroy
    # every order-three support at marker+t. No P inside this fat prefix does
    # that simultaneously at even these three sample markers.
    fat_prefix = set(range(6))
    fat_markers = [20, 30, 40]
    fat_small = set(range(50))
    old_parts = [set(choice)
                 for size in range(len(fat_prefix) + 1)
                 for choice in combinations(sorted(fat_prefix), size)]
    assert not any(
        all(destroys(support_family(fat_small, 3, marker + 5),
                     old_part | {marker})
            for marker in fat_markers)
        for old_part in old_parts)

    print("moving-petal stream")
    print(f"  empty-root deletion prefix size: {len(deletion)}")
    print(f"  rooted-petal deletion prefix size: {len(rooted_deletion)}")
    print("  survived: infinite-deletion/cofinal-successor-support endpoint")
    print("  rejected: cofinal surviving labels imply eventual coverage")
    print("  junk flag: fat interval worlds also satisfy the local endpoint")
    print("  survived: fixed-prefix destroyer provenance rejects the fat terminal model")


def selector_fusion_boundary():
    """Finite diagnostic for selector fusion boundary."""
    k = 3
    raw_cells = [frozenset({10 * i, 10 * i + 1}) for i in range(12)]
    X = set().union(*raw_cells)
    assert all(len(cell) <= k - 1 for cell in raw_cells)

    # Coarsen four small cells at a time. The resulting cells have the case
    # required by the selector/fusion theorem and still partition exactly X.
    cells = [frozenset().union(*raw_cells[4 * i:4 * i + 4])
             for i in range(3)]
    assert set().union(*cells) == X
    assert all(k < len(cell) for cell in cells)
    assert all(cells[i].isdisjoint(cells[j])
               for i in range(len(cells))
               for j in range(i + 1, len(cells)))

    stored_supports = [frozenset({1000 + i, 2000 + i})
                       for i in range(5)]
    assert all(support.isdisjoint(X) for support in stored_supports)
    selectors = [frozenset(choice)
                 for choice in product(*(sorted(cell) for cell in cells))]
    assert selectors
    assert all(selector <= X for selector in selectors)
    assert all(support.isdisjoint(selector)
               for support in stored_supports
               for selector in selectors)

    # Destruction by all of X does not descend to a selector subset. This is
    # why the formal terminal-fusion proof must reapply the counterexample to
    # its new infinite fused deletion instead of reusing X-destruction.
    arbitrary_family = [frozenset({x}) for x in X]
    selector = selectors[0]
    assert destroys(arbitrary_family, X)
    assert not destroys(arbitrary_family, selector)

    # The fusion theorem's positive-rank case really can stop at rank one.
    # Likewise, a large minimal transversal at one target says nothing by
    # itself about clean redundancy at every later target.
    chosen = next(iter(selector))
    assert destroys([frozenset({chosen})], {chosen})
    large_family = [frozenset({x}) for x in selector]
    assert destroys(large_family, selector)
    assert all(not destroys(large_family, selector - {x})
               for x in selector)
    essential_later_targets = {
        x: [frozenset({x})] for x in selector
    }
    assert all(destroys(essential_later_targets[x], {x})
               for x in selector)

    print("selector/fusion boundary")
    print("  survived: small blocks coarsen to large selector blocks")
    print("  survived: X-avoiding supports avoid every coarsened selector")
    print("  rejected: X-destruction automatically descends to selectors")
    print("  rejected: rank-one injury is a nontrivial rank descent")
    print("  rejected: one-target many-block growth alone is clean supply")


def certificate_synchronization_boundary():
    """Finite diagnostic for certificate synchronization boundary."""
    certificate = frozenset({10, 20, 30, 40})
    destroyed = set(certificate)
    maxima = []
    while destroyed:
        q = max(destroyed)
        maxima.append(q)
        # Target-local protected repair: q becomes surviving and no larger
        # certificate target is reintroduced. Smaller targets may remain.
        destroyed.remove(q)
        assert all(u < q for u in destroyed)
    assert maxima == [40, 30, 20, 10]

    # The cofinal protected-repair fork may choose q outside the certificate.
    # Repairing it leaves the certificate maximum unchanged, so it cannot be
    # substituted into the strict finite-descent argument.
    destroyed = set(certificate)
    unrelated_target = 999
    before = max(destroyed)
    _repaired = unrelated_target
    assert max(destroyed) == before

    # Padding blocks after a proposed bound C can force certificates larger
    # than C for purely combinatorial reasons. In this one-block hypergraph,
    # selector x destroys only target q_x, so every certificate needs one
    # target per block point. Large-certificate growth alone is therefore not
    # a clean-supply conclusion.
    C = 5
    block = tuple(range(C + 3))
    target_for = {x: 100 + x for x in block}
    minimal_certificate = frozenset(target_for.values())
    assert len(block) > C
    assert len(minimal_certificate) == len(block) > C
    assert all(target_for[x] in minimal_certificate for x in block)

    print("certificate synchronization boundary")
    print("  survived: repairing the protected certificate maximum strictly descends")
    print("  rejected: an unrelated cofinal repair descends the certificate")
    print("  warning: padded blocks can force large certificates combinatorially")


def main():
    base4_fixed_core_stream()
    moving_petal_deletion_stream()
    selector_fusion_boundary()
    certificate_synchronization_boundary()


if __name__ == "__main__":
    main()
