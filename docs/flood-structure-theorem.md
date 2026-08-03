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
- finite hitting sets, called hubs, meeting every support in a family;
- free finite sets that do not contain a complete obstruction.

The elementary method used throughout is a matching-versus-transversal
argument. A large disjoint matching supplies representations that avoid a
small deletion. If no such matching exists, a bounded finite hub meets every
representation.

## Conditional structural results

The following groups of results are proved in Lean.

### Representation supply

- `rep_flood_of_hfail` produces finite representation hubs under the
  counterexample hypothesis.
- `pair_flood_of_hfail` gives the corresponding order-two structure.
- `double_flood_of_counterexample` combines the two families.
- `r2_unbounded_of_hfail` proves unbounded order-two representation counts
  along a cofinal sequence.

These statements concern separately chosen cofinal targets. They do not imply
that two desired configurations occur at the same target.

### Failing targets

- `failing_target_poor` bounds the disjoint representation supply at a target
  destroyed by a chosen deletion.
- `poor_count_of_failing` converts this into a counting statement.
- `guardian_team_hubs_of_deletion` supplies finite hubs made from deleted
  elements.
- `failing_target_in_sumset` records the additive location of a failed target.

The target may depend on the deletion and on the lower bound. This target
dependence is a principal limitation of the order-two program.

### Free-set trees and ranks

- `hfail_iff_freeStep_wf` identifies the counterexample condition with
  well-foundedness of a finite free-set extension relation.
- `counterexample_iff_rep_tree_wf` gives a representation-tree formulation.
- `exists_strict_rank` assigns an ordinal rank to the well-founded relation.
- `absolute_shell_stratification` decomposes the ground set into finite rank
  layers under its hypotheses.
- `depth_tax_of_hfail` gives a lower bound on the location of deep layers.

The existence of an ordinal rank does not itself provide an operation that
strictly decreases it.

### Composite classifications

- `counterexample_four_rooms` packages four possible order-two structural
  regimes.
- `endgame_final_form` gives a compact equivalence between the counterexample
  condition and a well-founded avoidance tree.
- `the_encirclement` combines several necessary conditions for a
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
- its rank layers must obey matching, hub, and reflection constraints.

The theory does not force these separately quantified target families to
intersect in the manner required for a contradiction.

## Relation to the current direct approach

The current proof attempt no longer tries to derive a contradiction from the
entire counterexample classification. It constructs an infinite deletion and
uses the order-two theory only for local components such as:

- finite-hub and matching alternatives;
- bounded free-set thinning;
- private-target and reflection lemmas;
- selector certificates and rank descent.

The current frontier is described in `solution-status.md`.
