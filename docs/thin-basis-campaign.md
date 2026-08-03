# Finite experiments on thin digit bases

Experiment date: 2026-07-24.

Status: computational observations. None of the statements in this document
is used as a proof of a universal theorem.

## Models

The scripts examine finite truncations of digit-type order-two bases,
including:

- the binary even-position/odd-position construction;
- a base-three analogue;
- randomized sparse order-two covering sets;
- finite modifications intended to create additional pair-transversal relations.

A target is called controlled by a pair in these experiments when every tested
representation contains at least one member of a specified pair.

## Observed pair-transversal graphs

In the binary digit model, successive alternating-digit elements control
targets of the form `2^m - 1`. The resulting finite pair-transversal graph is a
path. In the base-three model, the observed graph is a tree with a principal
path and several leaves.

Consequences within the tested finite models:

- the pair-transversal graphs are bipartite;
- choosing one color class gives a large independent set;
- deleting two adjacent transversal vertices destroys their shared target;
- deleting all sampled transversal vertices destroys many targets.

These observations show that cofinal pair transversals can occur in natural thin
bases while still allowing large independent deletions.

## Interlocking cost

`probe_team_interlock.py` measured the number of existing representations that
must be removed to create edges between nonadjacent transversal vertices. In the
tested digit models this number generally increases with the scale separation.
The data suggest that adding many cross-scale pair-transversal edges conflicts
with the covering property.

This is an empirical pattern, not a proved lower bound.

## Random sparse models

The sampled randomized sparse covering sets produced no pair-controlled targets in the
tested range. Thus pair-transversal structure was not generic in those samples. The
sample size and finite cutoff are too small to support a probabilistic or
asymptotic conclusion.

## Triangle experiment

`probe_triangle_construction.py` attempted to add a closing edge to three
successive transversal vertices by deleting representations that avoided the
desired edge. In the tested finite scales, every such modification destroyed
the covering property. One smallest-scale search was exhaustive up to the
recorded finite bound.

The experiment motivates the formal question addressed by
`SeparatedTriangle.lean`: under what hypotheses can a separated
pair-transversal triangle coexist with order-two covering?

## Valid conclusions

The experiments support the following uses:

- digit bases are important countermodels for overly strong local lemmas;
- pair transversals may persist across many scales;
- a path or tree in the pair-transversal graph still has large independent
  subsets;
- any proof that excludes dense pair-transversal graphs must use the additive
  covering constraints, not graph theory alone.

They do not prove that every pair-transversal graph is eventually a forest,
that every thin basis admits the required infinite deletion, or that Erdős
881 has a positive answer.
