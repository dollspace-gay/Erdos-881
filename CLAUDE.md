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

## Current frontier (2026-07-25, night)

FINAL FORM: counterexample ⟺ WellFounded(FreeStep)
(`endgame_final_form`); 881 ⟺ every 2-covering set ∋ 0 has an
infinite hereditarily rep-free subset.  THE FOUR ROOMS
(`endgame_four_rooms`): every counterexample is in R1 (fixed
offset, A ∩ (A−δ) infinite), R2 (growing offsets), R3 (scattered
mirror halls), or R4 (street ladder — positions pinned at n + d,
pure-Q streets, arithmetic rung family, difference deserts).
Also: shell stratification + depth tax + rotation/6/18-level caps
+ conflict law; three branch mechanisms (counting/Sidon,
robustness/Cantor, and their mixed-regime gap); the anchor
trichotomy (anchored / g₀-routed / central-AP3-free); the
canonical grid.  NEWEST SUMMIT: `the_pair_flood_funnel` — every counterexample
funnels via its own pair flood (`personal_pair_guard_of_hfail`,
unconditional, density-free) into: P-centred members / rotator
ghosts / the pure hall — over ONE fixed free 0-less envelope.
Remaining core: the fixed-hall strong-horn problem + rank-ω.
NEWEST LAWS: `endgame_translate_laws` — UNCONDITIONAL: no
basis element's translate (single or in pairs) eventually
captures A (walk kills: `ap3_deletion_engine`,
`good_two_walk_killed`).  The door's good horn is EMPTY; strong
horn is ambient law.  k ≥ 3 set-translate law open (wandering
wall).
SUMMIT: `endgame_final_dichotomy` — TWO ROOMS, no anchor
condition: every counterexample drives the FOUR LANES (rank ω /
door / ghost street / member street) or lives in the CENTRAL
TAIL.  Enabled by the StreamSurvives oracle refactor (anchor
supply consumed at exactly one interface; almost-anchored worlds
implement it via the g₀-tower self-kill `g0_tower_killed`).
Previous summit: `endgame_collapsed_trichotomy` —
NO anchor hypothesis: every counterexample is ANCHORED (four
lanes: rank ω / fixed hall + door / ghost street / member
street), ALMOST-ANCHORED (member g₀, ladder 2c−g₀ ∈ A, anchors
at every g ≠ g₀ — one hole), or CENTRAL-TAIL (thresholded
pinning + auto-min + AP3-free).  Route in: 0-weld
(`pairHub_of_repHub`), welded fork, street trichotomy, four
lanes, member street verdict (`difference_blind_stream`!),
`the_routed_collapse`.  Next: plug the g₀-hole (anchors-off-g₀
through the private-stream chain) → trichotomy becomes
dichotomy.  The user (Doll) steers via
metaphors and cannot answer technical questions; read the code.

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

## Maintenance notes (2026-07-25 night)

- Mathlib now deprecates `push_neg` in favour of `push Not`
  (~300 warnings repo-wide, harmless).  A one-line macro shim in
  a root-most import would silence them; do it in a quiet session,
  not mid-campaign.
- Remote: github.com/dollspace-gay/Erdos-881.  Sessions commit
  locally; pushing is the user's call.
