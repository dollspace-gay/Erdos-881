# Erdős problem 881 formalization

This repository formalizes results related to Erdős problem 881 in Lean 4.
The general-order problem is not solved. The current proof state is recorded
in `docs/solution-status.md`.

## Formal objective

For each order `k`, prove that a strongly minimal exact asymptotic basis
`A ⊆ ℕ` has an infinite subset `B` such that `A \ B` is an exact asymptotic
basis of order `k + 1`.

The cases `k = 0, 1, 2` are proved. For `k ≥ 3`, the remaining hard case is a
strongly minimal exact order-`k` basis that is not already an exact order-two
basis.

## Proof requirements

- Do not introduce `sorry` or `admit`.
- Compile every changed module and run `lake build Erdos881` before reporting
  completion.
- Audit every new theorem with `#print axioms`. Permitted axioms are
  `propext`, `Classical.choice`, and `Quot.sound`.
- Test proposed cofinal or structural implications against arbitrary support
  families, interval-like sets, and high-density sets before formalization.
- Do not infer eventual coverage from a cofinal set of covered targets.
- Do not infer a decreasing certificate measure from a repair at a target
  outside that certificate.
- A conclusion of the form `x ∈ A + A` is generally automatic for late
  targets of an order-two basis. Such a conclusion requires an additional
  restriction or quantitative bound to be informative.

## Build commands

- Full project: `lake build Erdos881`
- Single module: `lake build Erdos881.<Module>`
- Direct Lean check: `lake env lean Erdos881/<Module>.lean`

Lean implementation notes:

- Introduce explicit type information before `omega` when beta reduction
  obscures an arithmetic expression.
- Inspect the result of `push Not` before destructuring it; the generated
  proposition can vary with expression shape.
- Use quoted heredoc delimiters for temporary Lean files containing special
  characters.

## Current proof route

1. `DirectConstruction.lean` proves that `HasCleanSupply` yields an infinite
   deletion preserving the successor-order basis property.
2. `AdaptiveDirect.lean` identifies failure of local clean supply with an
   atomic pinned tail and separates lower-rank and private-core cases.
3. `PrivateCoreStream.lean` converts both private-core cases to a bracketed
   sequence of surviving and destroyed targets.
4. `GeneralOrderAttack.lean` supplies block selectors, target-localized finite
   certificates, protected repairs, and the remaining arithmetic
   classification.

The current endpoint is a family of arbitrarily large finite target-localized
certificates. The certificates are not known to be nested or coherent across
cardinality bounds. The next required result must convert each branch of
`quadraticBlockTail_forces_targetLocalizedArithmeticOutcome` into either a
nontrivial rank reduction or clean supply.

## Principal modules

- `GeneralOrder.lean`: statement of the problem at arbitrary order and the
  proved easy-order reductions.
- `GeneralOrderAttack.lean`: general-order obstruction and selector theory.
- `DirectConstruction.lean`: clean-supply construction.
- `AdaptiveDirect.lean`: safe-prefix analysis.
- `PrivateCoreStream.lean`: private-core and certificate synchronization.
- `DisjointRepEngine.lean`: order-two matching and finite-transversal tools.
- `FreeRank.lean`: well-founded free-set relations and ordinal ranks.
- `Endgame.lean`: historical order-two classifications.
- `DigitSieve.lean`: verified digit-basis examples at every order.

## Documentation conventions

- “Proved” means checked by Lean.
- “Computational observation” refers to a finite script or explicit finite
  calculation and is not a universal theorem.
- “Open” means that no proof is present in the repository.
- Use standard mathematical terminology. Avoid narrative descriptions,
  anthropomorphic language, and claims of completion for conditional
  classifications.

## Repository policy

Preserve unrelated working-tree changes. Use explicit file lists when staging.
Publishing branches or pull requests requires an explicit user request.
