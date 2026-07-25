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
- `push_neg` output shapes vary; destructure what it actually gives.

## Map

- `Erdos881/Endgame.lean` — START HERE: the final statements
  (portrait, reduction, two rooms, universal classifications).
- `Erdos881/DisjointRepEngine.lean` — the main engine (~190
  theorems): floods, canonical core, routing, sharer/sum laws,
  Sidon walls, blowups, escalation ladder.
- `Erdos881/FreeRank.lean` — the rank framework: freeness trees,
  ordinal ranks, the reduction, crystals, classifications.
- `Erdos881/InfiniteRamsey.lean` — infinite Ramsey, every arity.
- `Erdos881/Cantor*.lean` — the verified positive instance.
- `docs/flood-structure-theorem.md` — paper-grade statement list.
- `docs/rank-program.md` — the open question and its obstruction.
- `docs/solution-status.md` — campaign state; newest at top.
- Memory battle plan (`v11-battle-plan` in agent memory) — newest
  state block at top; dead routes listed there — do not revisit
  them.

## Current frontier (2026-07-25)

Everything reduces to: find a pool operation that strictly drops
the freeness-tree root rank (`no_pool_rank_descent` finishes from
there), or kill the perfect clique worlds (rank-stable,
hfail-self-serving — the descent must engage their outside), or
kill the infinite-rank rooms.  The user (Doll) steers via
metaphors and cannot answer technical questions; read the code.
