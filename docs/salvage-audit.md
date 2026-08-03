# Reuse audit of the earlier counterexample program

Audit date: 2026-07-23. Terminology and status revised 2026-08-03.

This audit identifies earlier modules that remain useful for the current
direct-construction proof. A declaration described as unreferenced is not
mathematically false; it is simply not used by the current dependency chain.

## Main conclusion

The positive infinite-deletion criterion near the end of
`FreeSetTripleRepairs.lean` is derived through `StrongInfiniteDeletion`. Most
theorems named `counterexample_forces_*` are not used in that derivation. They
form a separate collection of necessary conditions for a hypothetical
counterexample.

Frequently reused intermediate objects include:

- `repairedCrossingReservoir`;
- `repairedOptionTower`;
- `disjointTargetStreams_or_migratedTwoRepairTraces`.

Exact reference counts and line numbers from the original audit are omitted
because they become stale as the files change.

## Reusable modules

| Component | Principal files | Current use |
|---|---|---|
| Free-set thinning for bounded pair maps | `BoundedPairFreeSet.lean` | Removes finitely controlled guardian and pair obstructions. |
| Matching-versus-star classification | `FreeSetTripleRepairs.lean` | Classifies infinite pair-survival structure. |
| Binary constraint machinery | `FreeSetTripleRepairs.lean` | Encodes finite two-option guardian constraints. |
| Block certificates | `FiniteBlocks.lean`, `CertificateAmplification.lean` | Supplies the selector-certificate interface used by the current proof. |
| Candidate deletion limits | `FreeSetTripleRepairs.lean` | Constructs infinite deletion objects from compatible finite stages. |
| Infinite pair Ramsey theory | `InfinitePairRamsey.lean` | Separates rigid and nonrigid pair configurations. |
| Reflection and private targets | `ReflectionDefects.lean` | Provides local translation and singleton-destruction bounds. |
| General selector attack | `GeneralOrderAttack.lean` | Supplies target localization, protected repair, and arithmetic classification. |

## Unreferenced or superseded groups

The following groups were identified as candidates for consolidation. They
should not be deleted without a fresh dependency check.

1. Option-reservoir and external-core certificate variants in
   `FreeSetTripleRepairs.lean`.
2. Multiple restatements of `disjointTargetStreams` migration results.
3. Specialized `fullyCritical*` cofinal-trace endpoints.
4. Successive `lateralSwitch` and `fixedTranslation` packaging theorems.
5. Certified sunflower endpoints that are not connected to the current block
   certificate interface.

## Core definitions

- `additiveSupportFamily`: finite supports representing a target at a fixed
  order.
- `IsExactTupleAsymptoticBasis`: exact-order asymptotic basis property.
- `IsFiniteBlockPartition`: a countable partition into finite nonempty blocks.
- `DestroysAt`: a deletion meets every support for a target.
- `StrongInfiniteDeletion`: an infinite deletion preserving the required
  support condition.
- `PairCovers`: pair-based covering relation.
- `IsPrivateTriple`: a representation private to a marked element.
- `IsReflectionLevel`: a finite reflection symmetry condition.

## Maintenance rule

New proof routes should depend on stable definitions and a small number of
general interfaces. Specialized endpoint restatements should be added only
when they remove a real hypothesis or close a new implication.
