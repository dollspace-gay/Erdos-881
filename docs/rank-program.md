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

## STATUS UPDATE (2026-07-25 17:00): the framework is FORMAL

`Erdos881/FreeRank.lean` now contains: `freeStep_wf`,
`exists_strict_rank`, the leaf law, the stalled zone (hereditary,
shallow, nonempty via the flood), `root_rank_dichotomy`, pool trees
(`poolFreeStep_wf`), **THE REDUCTION** (`no_pool_rank_descent`: one
strictly rank-dropping pool operation solves the problem),
`rank_le_of_subrel` + `pool_rank_mono` (weak monotonicity), and
`pool_rank_pos` (the stream kill gives rank ≥ 1).  Order-2 port:
every minimal basis carries an ordinal invariant
(`exists_strict_pair_rank`).  The open question is now exactly:
WHICH pool operation is strictly rank-dropping along its iterates?

## Recommendation for the next session

(a) Formalize the disjoint-envelope iteration (finite level-k
version) to make the simultaneous-duty load exact.
(b) Attack the sub-question in (3): single-guardian hub-service
multiplicity under a fixed deletion.  It is a concrete dichotomy
both of whose branches are usable.
(c) Only then evaluate whether any rank closes; do not repeat the
twelve dead kill-routes (list in v11-battle-plan memory).

## SESSION II SYNTHESIS (2026-07-25 evening): the frontier, exactly

Everything below is verified except where marked OPEN.

**The complete verified landscape.**  Streams classify (both
orders, hypothesis-free) into wide / total-guardian / crystal;
under the interfaces, order-3 total-guardianship dies, leaving per
pool: infinite rank or crystals.  Infinite-rank pools contain a
canonical ω-node (graded, with a diagonal of unboundedly free
extensions); crystals are rank-exact, rank-stable, (d+1)-uniform,
Sidon-targeted, fully dominated, with ≤3-pinned sharing.  Stalled
nodes are finitely ranked in every pool at once; narrowing elements
exist wherever rank is infinite.  One rank-dropping pool operation
would finish the problem (`no_pool_rank_descent`).

**The saturation lever** (`Saturated`, `saturated_mem_add`,
`saturated_count_bound`, `failing_fan_saturated`): failing targets
force √m-sized fans into the additively thin set Sat(B) ⊆ B + A.
At a single target this recovers the fan blowup (factor-|H| slack;
no contradiction).  The genuinely OPEN needle:

**The multi-target energy question.**  Distinct failing targets
m ≠ m′ of one deletion have fans that are shifted copies m − A,
m′ − A of the same set; forcing them into one thin Sat(B) requires
either near-disjoint placement (consuming the |Sat| budget at rate
√Y per target) or heavy fan overlap (requiring m − m′ ∈ A − A with
high multiplicity — additive energy the near-Sidon enemy lacks).
Cofinality alone demands only ~log Y failing targets below Y, which
fits the budget; no verified statement yet FORCES failure density.
Candidate forcing devices: aggregating over many deletions (the
union-deletion trichotomy pins straddling teams to shared targets);
the rep flood's per-element targets m_b (every large b, so ≥ |A|
targets — but these need not fail under any given B).  Closing the
gap between "cofinally many failures" and "densely many failures",
or showing the energy bound bites at density log, is the cleanest
route to the full solution currently visible.

**Alternative routes still open**: the rank-drop operation at the
ω-boundary (grade filtration + diagonal deletion, staged); the
relative theory above finite-rank extensions; Nash-Williams
barriers over the arity-general Ramsey (now fully available).

## THE ADAPTIVE CONCLUSION (2026-07-25, 18:15)

Static counting cannot cross the enemy's scale-staggering: witness
placement is asymptotically free (cofinality is cheap by the
problem's nature), even though witnesses are confined to sparse
immune-set translates and multiply under disjoint deletions.  The
final proof must therefore be ADAPTIVE: a priority-method
construction of a single deletion whose stages react to the
enemy's witness behaviour and herd it into prepared traps.  The
dodge state machines are the formal vehicle; the requirements list
and trap primitive are sketched in the battle plan.  This is the
program's endgame design.

## SHELL PROBE (2026-07-25, 19:20; scripts/probe_shells.py)

Truncated stratifications of NON-counterexamples are shallow and
fat: 3–4 shells regardless of window size, the first shell
absorbing a growing positive fraction (Cantor: 16/31/32 positives
→ 4 shells, sizes ~[19,8,3,1]; greedy-B₂: 3 shells, first shell
~3/4 of all elements).  A true counterexample must instead be
INFINITELY DEEP with every shell finite and nonempty
(`absolute_shell_stratification`) — depth is where the depth tax
(`depth_tax_of_hfail`, height ≥ N₀ + k/3) starts to bite.  The
tax is a LOCATION law for the adaptive program: obligations of
deep elements must sit at predictably linear heights; traps can
be scheduled there.  Rotation caps at both orders
(`four_disjoint_hubs_singleton`, 3 parts;
`three_disjoint_pair_hubs_singleton`, 2 parts) are the
hypothesis-free engines behind all of it.

## CONFLICT PLACEMENT PROBE (19:33; scripts/probe_conflicts.py)

Empirically the LEAST conflict target of shell-pair (j,k) is tiny
— min Q_k to 2·min Q_k in every tested model — but this is
honest-model behaviour, not forced: an adversary can make small
targets D-robust (D pairwise disjoint reps beat every union of
size < D), pushing conflicts high.  The price is the ROBUSTNESS
TRADE-OFF, the sharpest open sub-question the shell arc leaves:

  For a counterexample, blocking must happen at every level with
  FINITE shells; if the enemy makes all targets in [N₀, H]
  D-robust, then every conflict and every duty below H needs an
  envelope of size ≥ D, while Engine V10 guarantees cofinal
  BOUNDED hubs — so card-bounded blocking must recur cofinally
  HIGH, and the low window becomes permanently free territory for
  branch construction.  Formalizing "robust low windows are
  hereditarily-free-friendly" vs "fragile low targets confine
  conflicts" is the next dichotomy candidate: both branches are
  usable (one feeds the branch template, the other pins placement
  — the first crack in target liberty).

## MECHANISM UNIFICATION + MIXED REGIME (19:47)

`robustness_gives_hereditarily_free` (verified): uniformly growing
disjoint-rep counts give a branch by diagonal choice — the
branch-form of Engine V10's diagonal (`fragile_supply_of_hfail` is
its ν-form contrapositive; `cofinal_bounded_hubs_of_hfail` was
already the τ-form, and `hub_of_no_disjointReps` +
`disjoint_reps_le_hub_card` make ν and τ equivalent up to factor
3).  FRAGILITY (few disjoint reps ⟺ small hubs) is the single
currency of the whole quantitative theory.

probe_robustness.py: Cantor is UNIFORMLY ROBUST (min R over
windows: 1→4→5→8→9) — the Cantor branch is subsumed by the
robustness mechanism; carry-repair is disjoint-supply in
disguise.  Greedy-B₂ stays fragile forever (min R = 1, half of
each window at R ≤ 2) — its branch is the counting mechanism.
TWO mechanisms, and the enemy must live in the MIXED regime:
cofinally fragile (verified) with unbounded r₂ (verified), i.e.
fragile streets threaded through blown neighbourhoods forever.

Recombination audit: fragile+blown targets rederive the fan
blowup (covering forces nonzero completions m − z ∈ A + A for
every z, and a small cover concentrates them); every quantitative
consequence tested today is inter-derivable with the V10 core +
floods + caps.  The theory is CLOSED under recombination — new
inputs must come from (i) a mixed-regime branch construction,
(ii) Nash-Williams barriers, or (iii) explicit enemy-candidate
search.

## CRYSTAL HUNT, FIRST ATTEMPT (probe_crystal.py)

d=1 crystals (every tail pair a full hub) at Y=400: naive
covering sets score 0/1378 — no pair seals anything, because
covering density makes average r₃ ~ √Y and a full-hub pair must
carry a target's entire representation mass (the blown-translate
coincidence).  B₃-style uniqueness would do it but B₃ sets cannot
cover.  Crystal candidates must be engineered mirror-first, on
sparse Sidon streets; naive annealing cannot reach that geometry.
Next lab iteration: seed with designed reflection structure
(m − h* − A ⊆ A patterns) instead of random perturbation.

## CRYSTAL HUNT v2 + THE SLACK PARADOX (19:50)

Engineered hunt (probe_crystal2.py, coverage-enforced): in a
near-Sidon covering base at Y = 600, hole-punching seals 1 of 669
tail pairs.  Coverage duties protect nearly every element: each
seal wants several removals, every removal threatens covered
targets, and near-minimal bases have no slack.  This measures the
covering-vs-uniqueness interference the theory predicted.

**THE SLACK PARADOX (new attack angle, window-local).**  Sealing
a pair (making it a full hub) at a fragile target requires
removing/lacking the pair-avoiding representations — that costs
density slack.  But slack in [0, Y] produces disjoint-rep
robustness in [0, 3Y] (more elements, more completions), and
robust targets cannot be sealed at all.  Both quantities are
functions of the SAME window: unlike every counting law so far,
this coupling is local and cannot be dodged by placing targets
high.  Candidate quantitative form: seal-capacity(Y) ≤
f(slack(Y)) while crystal/shell demand in [Y/2, Y] grows like
(tail density)² — if f is subquadratic the mixed-regime enemy
dies in every sufficiently slack window, and zero-slack windows
feed the counting branch (near-Sidon ⟹ sidon_has_branch
machinery).  PRIORITY for next session: measure seal-capacity vs
slack empirically across density regimes, then attempt the
two-branch formal dichotomy (slack windows: robustness/sealing
tension; slackless windows: counting branch).  Height-pinning
helper: a genuine pair-hub needs m ≥ max(b, b'), so tail-pair
demand is bounded-below in height — the first demand-side height
pin in the whole program.

## SLACK MEASUREMENT + THE MASS-ACCOUNTING CORNER (19:55)

probe_slack.py (Y = 320): seal capacity is ZERO at every density.
Near-minimal (slack-free) bases: fragile targets exist (minR = 1)
but coverage protection blocks all 16/16 attempted seals.  Adding
slack: robustness explodes QUADRATICALLY — minR ≈ |A∩[0,Y]|²/(7Y)
(measured: slack +30% ⟹ minR 19; +70% ⟹ 29; +150% ⟹ 47) — and
robust targets cannot be sealed at all.  Both regimes kill seals.

**The ledger, with measured constants.**  (i) Sealing a pair at a
target costs ≥ R_avoid(m) removals (disjoint pair-avoiding reps
need distinct removals); removal budget per window ≈ slack.
(ii) Optimal slack s ≈ √(2Y) gives max seal capacity ~ (c/4)·√Y
per dyadic window, c ≈ 7.  (iii) Pair demand at scale k is ~2^k;
Hall's condition for the assignment (pairs of scale k seal at
scales ≥ k) is satisfied EXACTLY by quadratic height staggering
(scale-k pairs seal at scale ~2k) — target liberty's known
escape, now pinned to a specific schedule.  (iv) NEW: each seal
{b,b'} at m fires the fan blowup — r₂(m − b) ≳ √m/2 — and the
total pair mass of a window is |A∩[0,Y]|²/2; at capacity-full
sealing the blowup consumption is within a factor ~2 of the whole
window's pair supply.  The mixed-regime enemy survives on a
KNIFE-EDGE OF CONSTANTS in this mass account, exactly as the
order-2 telescope did.

Next session's sharpest program: verify each ledger line as an
inequality (seal cost ≥ disjoint avoiding reps — trivial from
disjoint_reps_le_hub_card relativized; blowup per seal —
hub_fan_blowup as-is; window pair mass — sum_pair_counts_le_sq
as-is; the staggering schedule — new), then tighten constants
until one side wins or the enemy's schedule is forced unique and
attacked structurally.

## R4 LADDER-WORLD LAB (20:49; probe_ladder_world.py)

Explicit R4 worlds exist in finite windows: |A| = 187 on [0,4000]
carries 20 pure-Q streets + all rungs + all b-pairs + full
coverage.  Scaling strains coverage (holes 0 → 4 → 18 as the
ladder densifies toward ~√Y/3 streets), so DENSE ladders are
incompatible with covering — but R4 only needs unboundedly many
rungs, and geometric spacing (L ~ log Y) never strains.  The
street ladder is a genuine refuge: the four-rooms theorem is a
classification, not yet a kill.  The refuge's cost profile is now
measured: each street consumes an anti-diagonal of pairing
freedom; the covering budget absorbs ~√Y/3 of them per window.
A real R4 counterexample must ALSO pay shells, floods, blowups
and minimality on top — the combined budget is the next lab
question.

## CROSS-AUDIT: LADDER × SHELLS (20:52; probe_ladder_shells.py)

The R4 ladder world stalls shallow-and-fat like every honest set
(3 shells, sizes [133, 51, 2]; rungs scattered through shells 0–1).
R4 structure contributes nothing to depth: streets constrain
PAIRS, depth needs rep-hub abundance at every level.  Across all
probed worlds the first shell holds a POSITIVE FRACTION of the
window basis (0.52 Cantor, 0.71 ladder world, 0.78 greedy-B₂).
Window free-fraction conjecture: every covering set's maximal
window-free subset is ≥ ε·|A ∩ window| — if true at the level of
TRUE freeness it would kill finite shells outright, but the
finite/infinite gap (window freeness ≪ true freeness) blocks the
transfer; thin TRUE shells need r₂ ≈ 1 supply which covering
forbids in windows yet fragile streets provide cofinally.  The
enemy's depth lives exactly in the window-invisible part of
freeness — consistent with the adaptive conclusion: no finite
probe sees the enemy.

## GREEDY SELF-AVOIDANCE PROBE (21:25; probe_greedy_avoiding.py)

Greedy (density-preserving, no Ramsey thinning) builds
self-avoiding families with density 0.68 (Cantor) and 0.90
(greedy-B₂) whose subset sums cover 97% of the window
(381/392).  On every tested world the COMPLETE SELF-AVOIDING
family — the sufficient condition of
`survival_of_complete_avoiding` — exists essentially outright.
The enemy cannot stop thin self-avoiding families (they don't
hurt it); its entire defence must concentrate on preventing
COMPLETENESS.  Program: formalize the greedy stall analysis at
the semigroup level (the self-avoiding analogue of the absolute
leaf) and characterize what blocking completeness costs the
enemy per window.

## THE COMPLETENESS CIRCLE, CLOSED HONESTLY (21:30)

Chasing the pinch to its end: covering forces |A ∩ [0,Y]| ≥ √Y,
so any positive-fraction subsequence T of A has k-th element
O(k²) — POLYNOMIAL — while its prefix sums grow cubically.  The
small-gaps criterion (`subset_sum_complete_of_small_gaps`) is
therefore EVENTUALLY AUTOMATIC for any spread-out co-thin
T ⊆ A (modulo initial-segment bootstrap).  Completeness is free;
the reduction `survival_of_complete_avoiding` is thus EQUIVALENT
to the original problem, not weaker: choosing U := A ∖ T, the
sufficient condition "T complete + self-avoiding" is literally
"U is a co-infinite order-3-covering subset" — Erdős 881 itself.

VALUE of the circle: it certifies that SELF-AVOIDANCE IS THE
ENTIRE CONTENT (density/completeness costs nothing), so the
ω-Ramsey machinery, the greedy probe, and the blocked-subset-sum
enemy obligations attack the true core with no loss.  The
enemy's whole existence is the statement: every spread-out dense
subfamily has cofinally many fully-blocked subset-sums.  Against
that stands the verified fact that blocking a D-robust target
needs D of its low elements inside the family — and the family
is 90% of the basis, so the enemy's blocks must sit at targets
robust ONLY through the thin co-part.  The battle line:
can a 10%-subset of a covering basis 3-cover the 90%-family's
semigroup?  Counting says yes with room (0.1³·Y^{3/2} ≫ Y);
the enemy must defeat counting with structure at every scale,
for every partition.  This is the sharpest quantitative form of
881 the campaign has reached.

## THE RIGIDITY SPECTRUM (21:36; probe_partition.py)

With 0 (never deletable) included, thin subsets 3-cover
everything in slack worlds at every tested thinning (greedy
model: zero holes down to 14% density).  In rigid worlds the
picture is structural: Cantor tolerates ONLY the thinning aligned
with its own ternary structure (every 3rd tail element: zero
holes with 54 elements; every 2nd/4th/6th/8th: 20–50% holes).
Aligned thinnings are exactly the surviving branches
(pure-powers).  THE SPECTRUM: slack worlds — everything
survives; Cantor-rigid — aligned subsets survive; a
counterexample — NOTHING survives, i.e. the enemy must be a set
with no self-consistent alignment whatsoever, misaligned with
every one of its own uncountably many thinnings.  Residue/digit
towers are the enemy's only known counting-defeating device, and
each tower level is itself an alignment the enemy would have to
break.  This is the battle line restated structurally: does
every covering set possess at least one self-alignment?

## SPINE LAB (21:55; probe_spine.py)

Truncated honest worlds have 3–4 shells of DECREASING size
([37,23,3,1] Cantor), so no Higman chain forms — correctly: the
spine needs infinitely many shells, which exist exactly when the
enemy does.  The spine is an enemy-exclusive object, like every
structure of the campaign: invisible in honest worlds, forced in
failing ones.  Consequence worth noting: along the spine, shell
sizes are non-decreasing (sublist embedding), so a counterexample
possesses arbitrarily large free shells along its own spine —
combined with size↔rank in the finite regime this pushes spine
pool ranks upward.  Next session: spine stall hubs (the game
board, spine_stalls_hereditarily) versus the caps.

## CENTRAL RESIDUE CENSUS (22:25; probe_central_residue.py)

Cantor's doubles get their order-3 life through: parity-escape
pairs (odd sum, ~50%), midpoint-gap pairs (even sum, midpoint
outside A, ~48%), semi-diagonals (~2%) — and NO double relies on
its 0-pad alone (0/127).  Midpoint-freeness confirmed at every
tested double.  Covering forbids all-even bases (odd targets
need odd parts), so the parity channel is always populated: the
central world's order-3 residue is structurally two-channelled,
and a central-branch kill must close parity-escape and
midpoint-gap simultaneously.  Both channels feed the robustness
mechanism (Cantor's min-R growth lives here).

## THE CANONICAL DELETION PROGRAM (22:28; closing design note)

Parity-escape triples always carry an odd part, so the CANONICAL
deletion B_odd = A ∩ (2ℕ+1) kills that channel wholesale; the
enemy must then fail on the all-even sector alone.  Generalizing:
residue-class deletions B_{r mod m} are ENEMY-INDEPENDENT — the
adaptive game can open with the full grid {B_{r mod m}} and the
enemy owes cofinal failures against every one: a profinite
obligation grid.  Each obligation constrains a different
congruence sector, and the sectors interlock (coverage couples
residues additively).  This is the alignment battle line
weaponized on the deletion side: the enemy must be misaligned
with every congruence structure while its failure schedule
against the grid IS a congruence-indexed structure.  First
concrete sub-question for next session: can the enemy fail
B_odd and B_even-style deletions simultaneously with all its
other duties in a finite window?  (Lab: extend the ladder-world
builder with the grid obligations and measure strain.)

## GRID STRAIN LAB (22:37; probe_grid_strain.py) — final lab

Single-class obligations are CHEAP: two-scale and Cantor worlds
both carry hundreds of naturally class-obligated targets
in-window (596 odd-obligated each; 794–1086 for mod 3).  The
canonical grid's pressure therefore cannot come from any single
obligation — only from the cap-forced interaction across all
moduli at once (the ≤3-per-modulus spread crossed with the
per-modulus narrow/wide alignment dichotomy).  Next session's
grid work should target the INTERACTION term directly: pick two
moduli with wide rows and measure whether their spread-streams
can share targets consistently with the 18-cap.

## THE GRID'S LIMIT (22:45; closing analysis)

Tested and closed: "every covering set is grid-spread at some
modulus" is FALSE as a uniform claim.  An all-aligned enemy
survives by THRESHOLD RACING — letting the alignment threshold
X_m grow so fast that at every window only a slow-growing set of
moduli is active, keeping the CRT-joint class count useless
against the √-covering bound.  This is the same staggering that
defeats every static counting family in the campaign, now
verified to defeat the grid too.  FINAL SHAPE OF THE NIGHT'S
LESSON: every static interrogation (windows, streets, grids,
ledgers) is beaten by racing; the only devices that survive
racing are self-referential ones that consume the enemy's own
choices — the Nash-Williams spine (built FROM the enemy's
shells), the game board (stalls ON the enemy's own canonical
material), and the completeness pinch (obligations against every
family INCLUDING adaptively chosen ones).  The final proof, if
881 is positive, lives there; the racing-proof formal frame is
the spine game.


## Hall-world lab (2026-07-26)

`scripts/probe_hall_strong.py`: adversarial hall worlds (fixed
2-element hall pair-hubbing sparse ghost targets, full pair
coverage, then thinned to minimality ~164 elements at N = 3000)
cannot defeat ANY tested deletion at order 3: partners, strong
elements, every-4th, geometric — 52/52 survive.  The order-3
repair richness (three slots, every survivor z opens a slice
n − z) overwhelms pair-hub corruption.  Formal counterpart
started: `deletion_failure_slices`.  The open formal step is
counting pressure: B must pair-hub every slice of every failure
target; slices overlap across failure targets; quantify against
B's own structure (the slice-hub cascade).


## The cascade counting audit (2026-07-26)

Composed `failure_slices_low_r2` + `r2_unbounded_of_hfail` (the
supply IS cofinal: ∀ C N ∃ v ≥ N with pair-count ≥ C) +
`covering_density`.  Findings, all checked by hand:

1. High-r₂ targets are never survivor-slices of failure targets
   (their pair count exceeds any sparse deletion's window), so
   failure targets dodge v + S for every high-r₂ v.  The dodge
   count is bounded by the deletion's window count — REAL
   pressure, but it needs DENSITY of high-r₂ targets, and the
   interface gives only cofinality.  The enemy's sparsity
   refuge — threshold racing — reappears exactly as recorded.
2. Triple-mass accounting dies differently: failure targets may
   route unlimited triple mass through DELETED slices (those
   triples contain a deleted part, consistent with failure), so
   Σ-r₃ caps are uninformative.  Junk-shape; not formalized.
3. Conclusion: the cascade cannot be closed by static counting.
   It must be composed with the self-referential devices — the
   flood (which forces per-element structure at EVERY basis
   element, density-free) or the spine.  Next design: flood the
   cascade — use rep_flood_of_hfail's per-b personal targets as
   the slice family, so the slice indices are enemy material
   rather than a static V.


## The free-tower kill requirements (2026-07-26, audited)

The free tower (face III, near-diagonal, singleton effective
envelope {p}, p in A automatically) has: levels L' = m - p in A
(`pair_hub_corep`), windowed exact mirror through L'
(`free_tower_singleton_levels`), strong translate law across
the window.  The g0-tower engine does NOT port verbatim; the
audit found exactly three gaps:

1. THE LADDER: one c in A, large, with 2c - p in A.  Equivalent
   form: one 3-term AP in A with endpoint p (midpoint c).  The
   enemy's only defense is A cap (2A - p) bounded — total
   AP3-freeness at p, the central branch's geometry localized.
2. SMALL-z MIRRORS: the free-tower window excludes z <= max(p, g);
   the engine reflects repair-pair parts that may be small.  At
   small z the rotator color is live (image g - z, tiny).  The
   engine needs either both-large repair pairs (uncontrolled) or
   a small-part bypass.
3. HIGH-z MIRRORS: window also stops 2M0 + N0 + 1 below the
   rotator; engine level-reflections need the full range.  Fix:
   space the level extraction so all reflected values sit inside
   successive windows (feasible: windows have width ~ b).

Gap 1 is the mathematical heart; gaps 2-3 are engineering.
If ladder: adapt engine with windowed levels.  If no ladder
(AP3-free at p): the free tower merges into central-tail
geometry — and the two remaining rooms begin to look like ONE:
midpoint-free worlds vs rank-omega.


## The parity escape at the affine desert (2026-07-26, honest)

theta(z) = 2L' - p - 2z is always congruent to p mod 2, so the
no-ladder affine desert constrains only the p-parity class; the
enemy parks the window's basis mass on the other parity with
L' = b + g - p even (mirror preserves single-parity windows when
L' is even).  The SAME two-channel escape as the central
branch's order-3 residue.  Emerging picture: every defense the
enemy has left is 2-adic/parity-layered midpoint-free — the
enemy converges to Cantor-shape, and the verified Cantor
instance is NOT a counterexample (robustness).  The formal
bridge to hunt: parity-layered midpoint-free tower worlds have
growing disjoint triple reps (Cantor does), feeding
robustness_gives_hereditarily_free.  Window mass for all such
arguments: `window_populated`.


## The robustness-bridge audit (2026-07-26, honest)

The naive Cantor-convergence bridge FAILS: tower worlds have
cofinal FRAGILE targets (personal_fragility — every large b
guards a target with <= |P|+1 disjoint triple reps), so uniform
robustness (the hypothesis of robustness_gives_hereditarily_free)
is impossible in any counterexample.  Cantor is uniformly
robust BECAUSE it has no towers; the enemy's parity-layered
convergence is toward Cantor's RESIDUE geometry while keeping
fragile towers — the mixed regime, precisely.  The real bridge
must therefore be the 2-ADIC DESCENT: the parity escape pushes
the enemy's game one layer down (A cap window single-parity =>
half-scale replay); the descent's well-foundedness lives in the
rank machinery.  Emerging final form of the whole problem:
EVERYTHING funnels to rank-omega/2-adic descent vs the ladder
engines.  Next formal target: the parity-descent step (tower
laws descend to the half-set), connecting to FreeStep rank.


## The completeness-road audit (2026-07-26, honest)

The enumeration build was audited BEFORE building: with the
syndetic window, A-onwards is subset-sum complete essentially by
coverage (2-element subset sums realize every covered target),
so completeness was never the obstruction — exactly as the
completeness-circle audit recorded weeks ago: SELF-AVOIDANCE is
the entire content of the pinch, and the omega-dichotomy's
routed branch reproduces the HALL.  The parity/syndetic road's
real yield is therefore: (1) the parity defence costs the enemy
LINEAR density on defended windows (`parity_window_syndetic`),
destroying Sidon-sparseness there; (2) all roads reconverge on
two cores — the hall/avoidance core and rank-omega/descent.
The night's map is bidirectionally confirmed: the funnel
reaches the same two cores from the flood side that the
final-form reduction reached from the rank side.  These two
cores ARE Erdos 881.

## 2026-07-26 — Threading impossibility audit + the repair mine

**Route-pruning metatheorem (core 4).**  `endgame_final_form`
says counterexample ⟺ WellFounded(FreeStep).  The chain branch
of `stall_chain_or_rank` (per-c prefix-free chains) is a THEOREM
of hfail.  Therefore no argument consuming only the per-c chain
supply can produce an infinite FreeStep chain: that would refute
WellFounded(FreeStep), i.e. derive False from facts consistent
with hfail — impossible unless the derivation also consumes
other hfail laws.  CONSEQUENCE: core 4 ("chain threading
compactness") is NOT a compactness problem.  Galvin/Nash-Williams
barrier machinery alone (absent from Mathlib anyway) cannot close
it.  Any kill of the rank branch must inject cross-branch
material: wealth laws, street poverty, translate laws.  Do not
attempt pure threading again.

**The corridor restated.**  `disjoint_reps_le_hub_card` bounds
hub width below by disjoint-triple wealth, so a c-element free
set's extension is blocked only by POOR targets (disjoint count
≤ c+1).  The street branch is exactly the enemy's organized
poverty supply; the rank branch dies iff poverty runs out at
some level.  The decisive collision to hunt: force the drain's
wealth ONTO the street's capped targets (same m), not merely
cofinally interleaved.

**New bricks.**  `cross_blowup_infinite` (drain carriers infinite
at every level), `drain_address_cluster` (nested 2-adic address
tower in root coordinates — JUNK-AUDITED: bare tower is König-
pigeonhole for any infinite set; wealth concentration is the real
content), `drain_repair_mine` (repair quadruples a, a+δ, b, b−δ
⊆ A with 2^k ∣ δ at every depth k beyond every bound — Sidon
sets have none; the translate-law/carry-repair fuel, now
guaranteed 2-adically deep).  All standard axioms.


## 2026-07-26 (late): the singular core after fourteen summits

Every remaining open front reduces to COMMITTEE-WIDTH CONTROL
inside chosen subsets: the funnels link (width 2 in every B),
the street branch (width <= L at packs), the class-vs-sparse
gap (width |D cap [0,n]| prefixes), and room II's wall
(width-2 {c,g0} double-hubs).  The committee floor proves
width >= 2 hereditarily; the wealth caps prove width bounds
tax the enemy's targets into poverty; the width-band question
— can the enemy hold committee width in a bounded band
against every subset forever — is the problem's residue.
Two formalizable attacks queued: the drift-vs-window dichotomy
inside B (window-split machinery accepts card-bounded
families), and the escalating-width horn via disjoint-witness
growth (audit disjointness first — witnesses may share
non-committee parts).
