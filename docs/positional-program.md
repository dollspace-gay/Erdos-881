# Positional program for order two

Status: superseded historical program. The cited Lean theorems remain valid.

This program attempted to combine the positions of representation-rich
targets, failed targets, and finite support transversals. It was motivated by the observation
that counting bounds alone do not control where the corresponding targets
occur.

## Formal reduction

`counterexample_structure_coverage_breakdown` states a necessary condition for an order-two
counterexample: for every infinite deletion there are cofinally many targets
at which all available representation resources fail in a prescribed way.
`served_targets_never_fail` gives the elementary converse at a single target.

The intended contradiction was to construct one deletion for which cofinally
many targets remain served.

## Available positional constraints

The program used the following proved results:

- `nested_representation_wealth_addresses` and `two_adic_width_law` constrain certain
  representation-rich positions;
- `counterexample_structure_forced_mixing` records a mixing alternative;
- `counterexample_structure_canonical_core`, `small_lowpart_rigidity`, and
  `counterexample_structure_rigidity_pair_transversals` constrain finite support transversals;
- `cylinder_failure_residue_law`, `failing_target_in_sumset`, and
  `counterexample_structure_fan_poverty` constrain failed targets;
- `breakdown_pigeonhole` gives a finite counting reduction;
- `disjoint_matching_avoidance` constructs a deletion when the relevant finite
  matchings are sufficiently separated.

## Unresolved issue

The positional constraints apply to target sequences chosen by different
quantifiers. The program did not prove that they align on one cofinal
subsequence, nor did it construct a deletion that forces such alignment.

This route was replaced by the clean-supply construction in
`DirectConstruction.lean`. Its local selector certificates fix a finite target
set before applying protected repairs, which provides more precise control of
target dependence.
