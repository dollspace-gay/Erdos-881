# Salvage audit of the counterexample-mining tower

*2026-07-23. Method: exhaustive grep-based reference analysis over all
`Erdos881/*.lean`. "Terminal" = the theorem's name appears nowhere outside
its own declaration; "load-bearing (×N)" = referenced N times by later
material.*

## Headline finding

The final positive bridge — `exists_infiniteDeletion_threeBasis_iff_not_strongOrderThreeDeletion`
and `uniformCoveredTripleBlockChoices_gives_infiniteDeletion_threeBasis`
(tail of `FreeSetTripleRepairs.lean`) — is proved directly from
`StrongInfiniteDeletion`. **None of the 90 `counterexample_forces_*`
theorems is consumed by it.** The entire forced-structure tower is a
self-contained exploration; ~46 of its endpoints are terminal dead leaves.
Load-bearing spine hubs: `repairedCrossingReservoir` (×9),
`repairedOptionTower` (×8),
`disjointTargetStreams_or_migratedTwoRepairTraces` (×7).

## Machinery clusters and reusability

| Cluster | Location | Verdict |
|---|---|---|
| Free-set / bounded pair-map thinning | `BoundedPairFreeSet.lean` | **Reuse** — general engine for thinning away finite guardian/pair obstructions (both routes) |
| Star-vs-matching pair-survival dichotomy | `FreeSetTripleRepairs.lean` ~6291–6561, 41932–42180 | **Reuse for guardian teams** — literally classifies infinite pair survival as matching or star |
| 2-SAT / binary literals / implication edges | `FreeSetTripleRepairs.lean` ~5052–10800 | **Reuse for guardian teams** (a binary clause *is* a two-option guardian constraint); prune the migrated/SCC over-specializations |
| Covered-block certificate pivot | `FiniteBlocks.lean`, `CertificateAmplification.lean`, file tail | **Keep — canonical.** The actual contradiction interface; needed by every route |
| Candidate deletion / omega tower | `FreeSetTripleRepairs.lean` 31016–41470, 42480–42620 | **Reuse for the endgame** — produces the infinite surviving-deletion limit object |
| Two-point destroyer / pair Ramsey | `InfinitePairRamsey.lean`, scattered | **Highest value for guardian teams** — rigid/nonrigid pair-sum dichotomy is exactly the team analysis |
| Reflection / mirror | `ReflectionDefects.lean` (721 lines) | **Highest value for the mirror endgame** — already proves reflection + local translation for one destroyer, and ≤ 3 late singleton destroyers |

`ReflectionDefects.lean` deserves emphasis: it already contains
`privateOrderThree_implies_longReflection`,
`two_privateOrderThreeTargets_imply_localTranslation`,
`ncard_arbitrarilyLateSingletonDestruction_orderThree_le_three`, and
`infinitelyMany_singletonDeletions_preserve_orderThree` — the same circle
of ideas now completed by `GuardianRigidity.lean` (cross-guardian
no-stacking) and `MirrorPeriodicity.lean` (levels → periodicity →
surviving deletion). No periodicity predicate previously existed; the
nearest analog is `IsEventuallySyndetic` (`AdditiveSupports.lean:208`)
with its own surviving-deletion results at `AdditiveSupports.lean:4399+`.

## Prune candidates (dead branches)

1. **Option-reservoir / external-core-certificate cluster**,
   `FreeSetTripleRepairs.lean` ~43085–49159: ~14 declarations, mostly
   terminal (sextuply/six-option systems, sharp/even/two-third certificate
   tails). A parallel counting attempt that never reaches the pivot.
2. **`disjointTargetStreams` migration variants**, ~40022–40314: six
   terminal packagings hanging off the one live hub
   (`migratedTwoRepairTraces`). Collapse to the hub.
3. **`fullyCritical*` cofinal-trace leaves**, ~13849–14180: terminal
   variants off `fullyCriticalCofinalTraceDichotomy` (×7).
4. **`lateralSwitch`/`fixedTranslation` re-packaging ladder**,
   ~35973–36760: chain of superseded endpoint restatements.
5. **Certified sunflower bridge tail**, ~49434–49687: thematically
   adjacent to the pivot but not wired into it — either wire in or prune.

## Key definitions inventory

- `IsExactTupleAsymptoticBasis` — `AdditiveSupports.lean:2611`
- `additiveSupportFamily` — `AdditiveSupports.lean:20`
- `DestroysAt` — `FiniteBlocks.lean:32`
- `StrongInfiniteDeletion` — `FiniteBlocks.lean:51`
- `IsFiniteBlockPartition` — `FiniteBlocks.lean:19`
- `IsEventuallySyndetic` — `AdditiveSupports.lean:208`
- (new) `PairCovers`, `IsPrivateTriple` — `GuardianRigidity.lean`
- (new) `IsReflectionLevel` — `MirrorPeriodicity.lean`
