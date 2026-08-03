# Technical overview of the Erdős 881 formalization

Last updated: 2026-08-03.

This repository studies Erdős problem 881 by formalizing both structural
consequences of a hypothetical counterexample and a direct construction of the
required infinite deletion. The problem remains open in this repository.

## Formal setting

An exact asymptotic basis of order `k` is a set `A ⊆ ℕ` for which every
sufficiently large natural number is a sum of exactly `k` elements of `A`, with
repetition allowed. The strong minimality hypothesis used here states that
removing any infinite subset of `A` destroys the order-`k` basis property.

The desired conclusion is an infinite set `B ⊆ A` such that `A \ B` is an
exact asymptotic basis of order `k + 1`.

## Current proof architecture

The direct-construction route has the following dependency chain:

1. Clean supply implies an infinite basis-preserving deletion. Together with
   the existing easy-case reductions, it is enough to prove clean supply for
   the hard cases `3 ≤ k` that are not already exact order-two bases
   (`DirectConstruction.lean`).
2. Failure of local clean supply yields an atomic pinned tail
   (`AdaptiveDirect.lean`).
3. The private-core case yields either a moving-petal survival deletion or a
   fixed-core collision (`PrivateCoreStream.lean`).
4. The fixed-core collision also yields a survival deletion after splitting
   the marker set.
5. Under the counterexample assumption, the survival deletion yields a
   bracketed sequence of surviving and destroyed targets.
6. Target-local selector arguments turn the bracketed sequence into finite
   selector certificates of arbitrarily large cardinality.
7. Existing arithmetic classification reduces these certificates to three
   unresolved structural outcomes.

The last step is the current frontier. The missing theorem must convert each
arithmetic outcome to either a genuine lower-rank obstruction or uniform clean
supply.

## Earlier order-two program

The files `DisjointRepEngine.lean`, `FreeRank.lean`, and `Endgame.lean` contain
an earlier analysis specialized to order two. It proves many necessary
conditions for a counterexample, including:

- well-foundedness of finite free-set extension relations;
- rank assignments to those relations;
- bounded-hub and disjoint-representation alternatives;
- shell, matching, reflection, and guardian constraints;
- `endgame_final_form`, which reformulates the order-two counterexample
  condition using a well-founded representation-avoidance tree.

These results are valid conditional reductions, not a proof that a
counterexample exists or that the problem is solved. They remain useful as a
source of local combinatorial lemmas for the direct-construction program.

## Interpretation of experiments

Finite searches and digit-basis examples have two purposes:

- reject proposed universal lemmas by finding finite or exact structured
  countermodels;
- identify hypotheses that distinguish additive structure from arbitrary
  finite hypergraphs.

Experimental success is not reported as evidence of a theorem. In particular,
large finite certificates, cofinal surviving target sets, and behavior in
base-4 or Cantor-type examples do not imply the required uniform conclusion.

## Current conclusion

The formal development has isolated a precise issue: local protected repairs
can defeat every bounded target-local certificate, but the resulting
certificates vary with the bound. A complete proof needs additional coherence
or arithmetic structure across this family of finite certificates.

For the detailed theorem chain and verification status, see
`docs/solution-status.md`.
