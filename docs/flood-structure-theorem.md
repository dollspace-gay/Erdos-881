# Order-two counterexample structure

Status: historical program with Lean-verified conditional results.

This document summarizes the order-two analysis in
`DisjointRepEngine.lean`, `FreeRank.lean`, and `Endgame.lean`. It does not
claim a proof of Erdős problem 881. Every conclusion below assumes the
counterexample hypotheses appearing in the cited theorem.

## Representation and pair families

For a target `n`, the development studies:

- order-three support families representing `n`;
- order-two pairs representing auxiliary targets;
- finite support transversals meeting every support in a family;
- free finite sets that do not contain a complete obstruction.

The elementary method used throughout is a matching-versus-transversal
argument. A large disjoint matching supplies representations that avoid a
small deletion. If no such matching exists, a bounded support transversal
meets every representation.

## Conditional structural results

The following groups of results are proved in Lean.

### Representation supply

- `rep_cofinal_supply_of_hfail` produces finite representation support
  transversals under the counterexample hypothesis.
- `pair_cofinal_supply_of_hfail` gives the corresponding order-two structure.
- `double_cofinal_supply_of_counterexample` combines the two families.
- `r2_unbounded_of_hfail` proves unbounded order-two representation counts
  along a cofinal sequence.

These statements concern separately chosen cofinal targets. They do not imply
that two desired configurations occur at the same target.

### Failing targets

- `failing_target_poor` bounds the disjoint representation supply at a target
  destroyed by a chosen deletion.
- `poor_count_of_failing` converts this into a counting statement.
- `minimalSupportTransversals_from_infiniteDeletion` supplies finite support
  transversals contained in the deleted set.
- `failing_target_in_sumset` records the additive location of a failed target.

The target may depend on the deletion and on the lower bound. This target
dependence is a principal limitation of the order-two program.

### Free-set trees and ranks

- `hfail_iff_freeStep_wf` identifies the counterexample condition with
  well-foundedness of a finite free-set extension relation.
- `counterexample_iff_rep_tree_wf` gives a representation-tree formulation.
- `exists_strict_rank` assigns an ordinal rank to the well-founded relation.
- `absolute_rank_layer_stratification` decomposes the ground set into finite rank
  layers under its hypotheses.
- `depth_tax_of_hfail` gives a lower bound on the location of deep layers.

The existence of an ordinal rank does not itself provide an operation that
strictly decreases it.

### Composite classifications

- `counterexample_four_cases` packages four possible order-two structural
  regimes.
- `counterexample_structure_final_form` gives a compact equivalence between the counterexample
  condition and a well-founded avoidance tree.
- `combined_constraints` combines several necessary conditions for a
  counterexample.

These are classifications and equivalences, not contradictions. Earlier
documentation sometimes described them as if they completed the proof; that
interpretation is incorrect.

## What the program established

The verified order-two theory shows that a hypothetical counterexample must
simultaneously satisfy strong but compatible conditions:

- it must have cofinally many targets with bounded hitting sets;
- it must also have cofinally many targets with many order-two
  representations;
- its free-set extension relation must be well-founded;
- its rank layers must obey matching, transversal, and reflection constraints.

The theory does not force these separately quantified target families to
intersect in the manner required for a contradiction.

## Relation to the current direct approach

The current proof attempt no longer tries to derive a contradiction from the
entire counterexample classification. It constructs an infinite deletion and
uses the order-two theory only for local components such as:

- finite-transversal and matching alternatives;
- bounded free-set thinning;
- private-target and reflection lemmas;
- selector certificates and rank descent.

The remaining step is described in `solution-status.md`.
