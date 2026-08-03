#!/usr/bin/env python3
"""Finite diagnostic for search additive repair obstructions."""

from argparse import ArgumentParser
from itertools import combinations, combinations_with_replacement


def supports_of(A: tuple[int, ...], target: int) -> set[frozenset[int]]:
    return {
        frozenset(triple)
        for triple in combinations_with_replacement(A, 3)
        if sum(triple) == target
    }


def is_minimal_transversal(
    supports: set[frozenset[int]], D: frozenset[int]
) -> bool:
    return (
        all(E & D for E in supports)
        and all(any(E & D == {d} for E in supports) for d in D)
    )


def unique_hit_repairs(
    supports: set[frozenset[int]], D: frozenset[int], d: int
) -> list[frozenset[int]]:
    return [E for E in supports if E & D == {d} and E - D]


def has_disjoint_cross_repairs(
    supports: set[frozenset[int]], D: frozenset[int]
) -> bool:
    for d, e in combinations(sorted(D), 2):
        for E in unique_hit_repairs(supports, D, d):
            for F in unique_hit_repairs(supports, D, e):
                if (E - D).isdisjoint(F - D):
                    return True
    return False


def search(max_element: int, min_a_size: int, max_destroyer_size: int):
    universe = tuple(range(max_element + 1))
    for a_size in range(min_a_size, len(universe) + 1):
        for A in combinations(universe, a_size):
            for target in range(3 * max_element + 1):
                supports = supports_of(A, target)
                if len(supports) < 2:
                    continue
                support_vertices = sorted(set().union(*supports))
                for d_size in range(2, min(max_destroyer_size, len(support_vertices)) + 1):
                    for raw_D in combinations(support_vertices, d_size):
                        D = frozenset(raw_D)
                        if not is_minimal_transversal(supports, D):
                            continue
                        repairs = {
                            d: unique_hit_repairs(supports, D, d) for d in D
                        }
                        if not all(repairs.values()):
                            continue
                        if not has_disjoint_cross_repairs(supports, D):
                            return {
                                "A": A,
                                "target": target,
                                "supports": sorted(map(sorted, supports)),
                                "destroyer": sorted(D),
                                "repairs": {
                                    d: sorted(map(sorted, edges))
                                    for d, edges in sorted(repairs.items())
                                },
                            }
    return None


def main() -> None:
    parser = ArgumentParser()
    parser.add_argument("--max-element", type=int, default=8)
    parser.add_argument("--min-a-size", type=int, default=4)
    parser.add_argument("--max-destroyer-size", type=int, default=4)
    args = parser.parse_args()
    result = search(args.max_element, args.min_a_size, args.max_destroyer_size)
    if result is None:
        print("No obstruction found in the requested range.")
        return
    for key, value in result.items():
        print(f"{key}: {value}")


if __name__ == "__main__":
    main()
