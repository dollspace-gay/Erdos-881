# Erdős 881 (k = 2) — Lean 4 campaign

Goal: decide whether every ℵ₀-minimal exact order-2 additive basis
`A ⊆ ℕ` contains an infinite `B` with `A ∖ B` an exact order-3
basis.  Method: contradiction-mining a hypothetical counterexample
(`hfail`); lab-first probes in `scripts/`, then Lean.

## Hard rules

- ZERO SORRIES, always.  Gate every commit on a successful build;
  if a commit slipped in broken, fix forward and `--amend`.
- Axiom-check every new theorem: `#print axioms` must show only
  `propext, Classical.choice, Quot.sound`.
- JUNK-TEST every new cofinal-structure statement before building
  on it: can an interval / fat set / arbitrary covering set satisfy
  it?  (The 2026-07-25 audit found a whole "trap tower" layer that
  was true but vacuous; the repair is recording envelope FREENESS.
  Certificates: `trap_conclusion_trivial`, `tower_branch_trivial`.)
- Theorem-shape filter: `x ∈ A + A` conclusions are vacuous for a
  basis.  Only `x ∈ A` forced, `x ∉ A` forced, or counting bounds
  carry information.

## Build

- `~/.elan/bin/lake build` (full), or
  `~/.elan/bin/lake build Erdos881.<Module>` per module.
- Heredocs: Lean prime/∅ identifiers collide with `'''` and are not
  valid in `h∅`-style names; write files via python with `r"""`.
- omega is beta-blind: `show`/ascribe before calling it.
- `push Not` output shapes vary; destructure what it actually gives.

## Map

- `Erdos881/Endgame.lean` — START HERE: the final statements
  (portrait, reduction, two rooms, universal classifications).
- `Erdos881/DisjointRepEngine.lean` — the main engine (~190
  theorems): floods, canonical core, routing, sharer/sum laws,
  Sidon walls, blowups, escalation ladder.
- `Erdos881/FreeRank.lean` — the rank framework: freeness trees,
  ordinal ranks, the reduction, crystals, classifications.
- `Erdos881/InfiniteRamsey.lean` — infinite Ramsey, every arity.
- `Erdos881/Cantor*.lean` — the verified positive instance (k = 2).
- `Erdos881/Base4*.lean` — the verified positive instance (k = 3):
  `erdos881_base4_full_instance` (Base4Master) = strongly minimal
  exact order-3 basis, NOT order-2, powers-deletion survives at
  order 4.  The hard case is inhabited and behaves positively.
- `Erdos881/DigitInstance.lean` — the uniform instance:
  `digit_uniform_hard_case` = for EVERY k ≥ 2 the base-(k+1) digit
  set is a strongly minimal exact order-k basis, not order-2 for
  k ≥ 3.  Every hard case inhabited in one theorem.
- `Erdos881/GeneralOrderAttack.lean` — the k ≥ 3 frontier (63k+
  lines): rank-descent injury streams, anchor forks, the descent
  highway to order 2, engine interface, transport levers, the
  three-anchor replay.
- `docs/flood-structure-theorem.md` — paper-grade statement list.
- `docs/rank-program.md` — the open question and its obstruction.
- `docs/solution-status.md` — campaign state; newest at top.
- Memory battle plan (`v11-battle-plan` in agent memory) — newest
  state block at top; dead routes listed there — do not revisit
  them.

## Current status (2026-07-27)

ORDERS 0, 1, 2 SOLVED in Lean; k ≥ 3 STILL OPEN.  Erdős 881 as
published quantifies over *every* order k ("`A` a basis of order
`k`, minimal; must some infinite `B ⊆ A` leave `A ∖ B` a basis of
order `k+1`?").  Do not describe the repository as solving #881.

- Order two (the main engine).
  `threeAnchor_forbids_terminalPrivateWounds` closes the
  moving-prefix endgame by combining the terminal private-wound
  field, the eventual positive sum-free tail, and finiteness of
  every fixed positive-difference fiber.
  `exists_infiniteDeletion_threeBasis_of_pairCovers` proves the
  stronger zero-normalized statement for every eventual order-two
  pair-cover; `erdos881` transports it to the unrestricted
  strongly minimal formulation.
- General order: `Erdos881/GeneralOrder.lean`.  `Erdos881At k` is
  the order-`k` statement, and `erdos881At_iff_elementary` (audit)
  confirms it is the official statement verbatim.  Settled:
  `erdos881_at_zero` (vacuous), `erdos881_at_one`,
  `erdos881_at_two`, plus `exists_infiniteDeletion_succBasis_of_basisTwo`
  — every `k ≥ 2` for `A` an exact order-two basis.
- THE REMAINING GAP is exactly `erdos881_general_of_hardCase`'s
  hypothesis: `k ≥ 3` with `A` NOT an exact order-two basis.  That
  case is non-empty — the base-`(k+1)` digit-`{0,1}` set is an
  exact order-`k` basis and misses many targets at order two — so
  it is a genuine open obligation, not a vacuous one.  The natural
  next target is the base-`(k+1)` analogue of the Cantor instance.

MINIMALITY IS NEVER USED in any settled case: each proof needs
only the basis half, so what is proved is strictly stronger than
the problem asks.

Full build: 8303 jobs.  Axiom audit: only `propext`,
`Classical.choice`, `Quot.sound` — repo-wide, including
`crossGap_finiteException_can_genuinely_stall` (was `native_decide`,
now `decide`).  Zero sorries.

## Build quirk (2026-07-25)

`lake build Erdos881` occasionally reports success while
`Erdos881/Endgame.olean` is stale (mtime race after a fresh edit);
`#print axioms` then fails with unknown constant.  Fix: run
`lake build Erdos881.Endgame` explicitly and re-check.

## FreeRank.lean section map (night block additions)

Absolute floods → shells/stratification → cap suite → depth tax →
higher caps + conflict law → robustness branch → reflection
ledger → street dichotomy + four rooms → ladder mining →
classical-minimality interface → Ramsey cascade → omega pinch.
Search for `/-! ##` to navigate.

## Maintenance notes (2026-07-26)

- All deprecated `push_neg` uses were migrated to `push Not`.
- Remote: github.com/dollspace-gay/Erdos-881.  Sessions commit
  locally; pushing is the user's call.
