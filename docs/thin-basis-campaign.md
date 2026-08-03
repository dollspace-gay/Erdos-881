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
- finite modifications intended to create additional guardian relations.

A target is called team-guarded in these experiments when every tested
representation contains at least one member of a specified pair.

## Observed guardian graphs

In the binary digit model, targets of the form `2^m - 1` are guarded by
successive alternating-digit elements. The resulting finite guardian graph is
a path. In the base-three model, the observed graph is a tree with a principal
path and several leaves.

Consequences within the tested finite models:

- the guardian graphs are bipartite;
- choosing one color class gives a large set containing no complete guardian
  edge;
- deleting two adjacent guards destroys their shared target;
- deleting all sampled guards destroys many targets.

These observations show that cofinal guardian pairs can occur in natural thin
bases while still allowing large independent deletions.

## Interlocking cost

`probe_team_interlock.py` measured the number of existing representations that
must be removed to create edges between nonadjacent guardian vertices. In the
tested digit models this number generally increases with the scale separation.
The data suggest that adding many cross-scale guardian edges conflicts with
the covering property.

This is an empirical pattern, not a proved lower bound.

## Random sparse models

The sampled randomized sparse covering sets produced no guarded targets in the
tested range. Thus guardian structure was not generic in those samples. The
sample size and finite cutoff are too small to support a probabilistic or
asymptotic conclusion.

## Triangle experiment

`probe_triangle_construction.py` attempted to add a closing edge to three
successive guardian vertices by deleting representations that avoided the
desired edge. In the tested finite scales, every such modification destroyed
the covering property. One smallest-scale search was exhaustive up to the
recorded finite bound.

The experiment motivates the formal question addressed by
`SeparatedTriangle.lean`: under what hypotheses can a separated guardian
triangle coexist with order-two covering?

## Valid conclusions

The experiments support the following uses:

- digit bases are important countermodels for overly strong local lemmas;
- guardian pairs may persist across many scales;
- a path or tree of guardian pairs still has large independent subsets;
- any proof that excludes dense guardian graphs must use the additive
  covering constraints, not graph theory alone.

They do not prove that every guardian graph is eventually a forest, that every
thin basis admits the required infinite deletion, or that Erdős 881 has a
positive answer.
