# Current proof status

Last updated: 2026-08-03.

Erdős problem 881 is not proved in this repository. The current formal
development reduces the problem to a specific selector-certificate endpoint.
All statements described as proved below are checked by Lean. Computational
experiments are identified separately and are not used as proofs.

## Problem statement

Let `A ⊆ ℕ` be an asymptotic additive basis of order `k`. Assume that every
infinite set `B ⊆ A` destroys the order-`k` basis property of `A \ B`. The
problem asks whether there is an infinite `B ⊆ A` such that `A \ B` is an
asymptotic basis of order `k + 1`.

The repository uses `IsStronglyMinimalExactBasis A k` for the principal
hypothesis. The intended conclusion is represented by `Erdos881.erdos881`.

## Direct-construction reduction

The current proof strategy constructs the deletion directly.

`CleanlyRedundantAbove A h F b` means that every sufficiently large target
has an order-`h` representation avoiding the finite set `F ∪ {b}`.
`HasCleanSupply A h` means that, after every finite protected set and above
every lower bound, such an element `b` exists.

The following results are proved in `DirectConstruction.lean`:

- `exists_infiniteDeletion_of_cleanSupply`: clean supply produces an infinite
  deletion that preserves the order-`h` basis property.
- `erdos881_of_cleanSupply`: the required clean-supply statement at successor
  order implies Erdős 881.

The construction chooses an increasing sequence `b₀ < b₁ < ⋯`. Coverage of a
target is fixed before later choices can affect it, because every summand of a
representation of `n` is at most `n`.

`erdos881_of_cleanSupply` uses the general-order reductions already proved in
the repository. Its exact remaining sufficient hypothesis is:

> If `3 ≤ k`, `A` is a strongly minimal exact basis of order `k`, and `A` is
> not already an exact basis of order two, then `A` has clean supply at order
> `k + 1`.

## Failure of local clean supply

`AdaptiveDirect.lean` analyzes a finite stage of the direct construction.
Suppose `A \ F` is already an exact order-`h` basis. Then
`not_hasLocalCleanSupply_iff_atomicPinnedTail` identifies failure of local
clean supply with an atomic pinned tail.

The relevant proved reductions are:

- `safePrefix_excludes_fixedPinCase` excludes a pin contained in the protected
  prefix `F`.
- `PinnedAt.diagonal_or_privatePredecessorSupport` separates the diagonal case
  from a private lower-order support.
- `pinned_target_diagonal_or_markedMinimalDestroyer_rankFork` minimizes the
  obstruction while retaining its marked element.
- `markedMinimalDestroyer_cofinalRankDescent_or_privateCore` gives either a
  lower-rank obstruction or a private predecessor core.
- `HasAtomicPinnedTail.cofinal_markedConeRankFork` packages these alternatives
  cofinally along the atomic tail.

These results do not by themselves give clean supply. In particular, a
lower-rank obstruction may occur at a small target, and the private-core
alternative requires a separate argument.

## Private-core reduction

`PrivateCoreStream.lean` analyzes the private-core alternative by thinning a
uniformly bounded family of finite cores to a delta system.

`cofinalMarkedPrivateCoreSupply_deletion_or_fixedConflict` gives two cases:

1. The moving petals are nonempty. Their union defines an infinite deletion
   avoided by a cofinal sequence of successor-order supports.
2. Infinitely many cores are equal. Finite pigeonhole arguments then fix the
   old-prefix component `P`, a lower-order support `R`, and its residual target
   `t`. This is `HasFixedMarkedPrivateCoreConflict`.

The fixed conflict cannot be discarded without an additional argument. A
diagnostic computation in the exact base-4 digit basis realizes the pattern
with `P = {1}`, `R = {0,5}`, and `t = 5`. This example is recorded as a
computational check rather than as a Lean theorem.

`HasFixedMarkedPrivateCoreConflict.to_survivalDeletion` splits the injective
marker set into two infinite subsets. Deleting one subset leaves a cofinal
successor-order support stream on the other subset. Consequently:

- `HasAtomicPinnedTail.privateCoreCase_forces_survivalDeletion` sends both
  private-core cases to the same survival-deletion endpoint.
- Under the standing counterexample assumption,
  `HasAtomicPinnedTail.privateCoreCase_forces_bracketedConflict` converts that
  endpoint to `HasBracketedPrivatePetalCounterexampleConflict`.

This produces cofinally many surviving targets and intervening destroyed
targets. Cofinal survival is weaker than eventual coverage, so this is not yet
an infinite deletion preserving the basis property.

## Selector and repair reduction

The bracketed conflict carries a finite block partition. The blocks can be
coarsened to any prescribed finite lower bound while preserving the stored
supports. This permits use of the selector machinery in
`GeneralOrderAttack.lean`.

Two intermediate results are proved:

- `selectorFusion_forces_rankDescent_or_manyBlocks` gives either a represented
  destroyed rank `0 < ℓ < k`, or inclusion-minimal order-`k` destroyers of
  unbounded finite size across selector blocks.
- `selectorNontrivialRankDescent_or_boundedProtectedRepair` treats the
  automatic rank-one case as a protected repair. For a finite protected set
  `U`, it gives either a represented obstruction with `1 < ℓ < k`, or a new
  selector that avoids `U` and preserves the selected order-`k` target.

The target chosen by the second theorem depends on the selector. It need not
belong to a previously fixed finite certificate. Therefore this theorem alone
does not define a decreasing maximum on a certificate.

## Localized migrating certificates

The target-local selector results in `GeneralOrderAttack.lean` correct the
preceding target mismatch. The main wrapper is
`HasBracketedPrivatePetalCounterexampleConflict.forces_unboundedLocalizedMigratingCertificates`.

It fixes a quadratic coarsening of the original block partition. For every
cardinality bound `C` and index bound `L`, a sufficiently late tail admits a
finite set of targets `Q` satisfying:

- `Q` is nonempty and `C < Q.card`;
- every `q ∈ Q` is represented at order `k + 1`;
- every selector destroys at least one target in `Q`;
- for every `q ∈ Q`, some selector destroys `q` and preserves every other
  target in `Q`;
- every `q ∈ Q` lies strictly between consecutive targets of the original
  surviving stream, at an index at least `L`.

The proof uses cardinal-minimal target localization. For the selector that
localizes `q`, choose one surviving support for every other target in `Q` and
protect their finite union. A private repair of `q` avoiding this union would
preserve all targets in `Q`, contradicting the certificate property. Hence a
certificate fitting within the repair capacity cannot exist, and its
cardinality must exceed `C`.

This argument is stronger than repeated descent of the largest destroyed
target: localization gives a one-step contradiction for any bounded
certificate.

## Current unresolved endpoint

The proved conclusion is the existence of arbitrarily large finite,
target-localized, bracketed certificates. It is not clean supply and it is not
yet a nontrivial rank descent.

The following implications are not proved:

- Arbitrarily large finite certificates do not automatically form a nested or
  coherent infinite certificate.
- A certificate obtained for one value of `C` need not be related to the
  certificate obtained for a larger value.
- Large block cardinality can force large certificates for combinatorial
  reasons that do not imply additive redundancy.
- A cofinal set of surviving targets does not imply eventual coverage.
- A protected repair at a target outside a fixed certificate does not decrease
  any measure on that certificate.

The next available formal reduction is
`quadraticBlockTail_forces_targetLocalizedArithmeticOutcome`. It gives one of
three outcomes:

1. a large rooted matching at an exact target;
2. a reduced common-column cover stream;
3. an anchored lower-order arithmetic concentration.

No theorem currently converts all three outcomes to either a represented rank
descent with `1 < ℓ < k` or clean supply. Establishing those conversions is the
next proof obligation.

## Computational checks

The scripts in `scripts/` test finite models and proposed implications. They
are used to reject false lemmas before formalization.

- `probe_adaptive_local.py` checks the safe-prefix and marked-cone reductions
  on finite models and on the exact base-4 example.
- `probe_private_core_stream.py` checks the moving-petal and fixed-core cases,
  the selector coarsening, and the certificate-locality condition.

The latter script explicitly rejects the implication that repairing an
unrelated cofinal target decreases the maximum of a fixed certificate. It also
shows that block padding alone can create large finite certificates. These are
diagnostic countermodels, not mathematical counterexamples to Erdős 881.

## Verification

For the current certificate theorem:

- Lean compilation succeeds without `sorry` or `admit`;
- the axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`;
- the finite diagnostic scripts pass;
- `lake build Erdos881` completes successfully with 8321 jobs.

Historical development notes were removed from this file because they mixed
superseded strategies with the current proof state. Earlier versions remain
available in version control.
