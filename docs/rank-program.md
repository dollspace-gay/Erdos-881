# The Rank Program: design notes after the flood day

_2026-07-25.  Companion to docs/flood-structure-theorem.md.  This
document is analysis, not verified mathematics; every VERIFIED
citation refers to `Erdos881/DisjointRepEngine.lean`._

## The wall, named: TARGET LIBERTY

Twelve kill-routes were tested against the verified flood
configuration on 2026-07-25.  Every one failed the same way: the
enemy's obligations (flood targets, failing targets, blowup
translates) are anchored to cofinal quantifiers whose WITNESS
TARGETS the enemy chooses freely.  Two structured configurations
never collide because the enemy places them apart.  We call this
**target liberty**.  Facts:

- Order-2 structure alone can never kill: near-Sidon minimal bases
  (B₂[g]-like) satisfy every order-2 consequence we can derive —
  the pair flood, sum rigidity, deserts, offsets — with room to
  spare.  VERIFIED sanity: the Cantor world realizes the singleton
  pair flood.
- The only anti-Sidon lever we own is the blowup
  (`hub_fan_blowup` + `covering_sqrt_lower` ⟹
  `r2_unbounded_of_hfail`), an ORDER-3 phenomenon.
- The only devices that pin targets to structure are:
  (i) hub membership under a chosen deletion — hfail(B) failing
  targets have hubs MADE OF B-elements
  (`guardian_team_hubs_of_deletion`), so choosing B = structured
  elements plants structured teams at fresh targets;
  (ii) algebraic identity — sharing forces sums
  (`shared_pair_target_is_sum`, `_sum3`).

## The well-founded tree (VERIFIED foundation)

`free_prefixes_die_of_hfail` / `pair_free_prefixes_die_of_minimality`:
every infinite increasing positive A-sequence has a finite prefix
that is not free.  Hence the free finite subsets of A, under
increasing extension, form a well-founded tree T.  Its stalled
nodes (free P, no large free extension) exist and are exactly the
flood envelopes (`rep_flood_of_hfail`).  Every node of T therefore
has an ORDINAL RANK.

## What a closing rank must do

Wanted: an assignment ρ from stalled configurations to ordinals
(or naturals) such that some verified operation strictly decreases
it.  Candidate operations, with status:

1. **Pool descent** (`rep_flood_pool`): from a stalled envelope E
   over pool P₀, pass to pool P₀ ∖ E (unbounded, since E is
   finite).  Yields a NEW stalled envelope E' disjoint from E.
   Iterates forever — no known decreasing quantity; envelope
   cards can grow.  What DOES change: the guardians must carry one
   more simultaneous duty per level (k disjoint envelopes ⟹ every
   sufficiently large surviving b guards k targets with distinct
   coreps).  Candidate rank: NONE yet.  Candidate contradiction:
   guardian load vs some capacity bound — but order-2 capacity is
   infinite for Sidon-like sets (target liberty again).

2. **Guardian pools** (`pair_flood_cascade`): envelopes made of
   guardians.  Levels have disjoint cores.  Same non-descent.

3. **Deletion feedback** (the most promising): choose
   B := rotating guardians; failing targets acquire guardian teams
   (≥ 2, `guardian_team_hubs_of_deletion`).  Each team member b is
   necessary at the fresh target t AND carries its own hub at m_b.
   The unexplored resource: t's necessity witnesses route
   t − b ∈ (A∖junk) + (A∖junk) for EVERY team member — cross-sums
   of fresh targets against rotating guardians.  If the same b
   appears in teams at TWO fresh targets t, t' (it can — teams are
   not sharers), then t − b and t' − b both decompose.  A rank on
   the b-multiplicity across fresh targets?  Each b can serve
   boundedly many hubs?  NO — nothing bounds hub-service.
   Sub-question worth formalizing: CAN one b sit in minimal
   B-team-hubs of infinitely many targets?  If yes the deletion
   B ∖ {that b's tail} re-runs; if no, teams rotate fully and the
   team-supply is an injection-like map — either outcome is
   structure.

4. **Nash-Williams route**: on one geometric ground stream, the
   pair/rep transversal families are unavoidable in every infinite
   subset; by the (unformalized) Nash-Williams theorem they can be
   refined to barriers, whose ordinal rank is canonical.  The
   descent would compare barrier ranks across ground streams.
   Heavy machinery; Mathlib support unclear.

## Recommendation for the next session

(a) Formalize the disjoint-envelope iteration (finite level-k
version) to make the simultaneous-duty load exact.
(b) Attack the sub-question in (3): single-guardian hub-service
multiplicity under a fixed deletion.  It is a concrete dichotomy
both of whose branches are usable.
(c) Only then evaluate whether any rank closes; do not repeat the
twelve dead kill-routes (list in v11-battle-plan memory).
