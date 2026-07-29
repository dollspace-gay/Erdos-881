# GENERAL ORDER: COMPLETE ALIGNED DESTROYERS FUSED (2026-07-29)

The quadratic-tail construction no longer throws away the finite
destroyer attached to each protected source gap.  Every hypothetical
hard-order counterexample now produces one infinite deletion carrying
strictly interlaced translated pairs

\[
  t_n < q_n < t_{n+1},
  \qquad q_n=t_n+\delta_n,
\]

where `t_n` survives, `q_n` is destroyed, and a pairwise-disjoint finite
inclusion-minimal destroyer `D_n` of `q_n` is contained in the common
deletion.

- `AlignedTailSurvivalDestroyerPair` retains the source index, `q`,
  `δ`, a protected support, the full growing source rooted matching, and
  the finite minimal destroyer.  It also records that every destroyer
  coordinate lies beyond the requested ambient block floor.
- `HasQuadraticTailAlignedResolvedArithmeticAt.exists_alignedTailPair`
  compacts the private selector destroyer and minimizes it.  Every member
  of the retained source matching avoids the resulting `D`, while
  `q = target i + δ` remains unchanged.
- `cofinalAlignedTailPairs_fuse_translatedStream` recursively puts the
  finite destroyers in fresh block coordinates, thins them using
  whole-block cross-avoidance, and takes their union.  The retained source
  supports avoid the union, while every retained destroyer lies inside it.
- `exactBasis_counterexample_forces_alignedTranslatedStream` is the
  counterexample-level capstone.  It is stronger than the earlier generic
  fused endpoint because the actual destroyed targets, translations,
  minimal destroyers, and growing source matchings all survive fusion.

The translation law now gives a direct cardinal attack.  Let `V_n` be the
union of the disjoint petals of the source matching.  Any `a ∈ V_n` with
`a+δ_n ∈ A` must translate into `D_n`; translation is injective.  Hence at
most `|D_n|` petal points translate back into `A`, and every other petal
point is a literal translated hole.  The machine-checked theorem
`AlignedTailSurvivalDestroyerPair.largeHoles_or_largeDestroyer` proves

\[
  n+1 < 2\,|\operatorname{holes}_n|
  \quad\text{or}\quad
  n+1 < 2\,|D_n|
\]

at scale `n`.

This is genuine pressure, but it is not yet the general-order solution.
The junk test
`finiteComplement_alignedPair_forces_largeDestroyer` shows exactly how a
fat set can satisfy the geometry: its complement bounds the hole side, so
the minimal destroyers must grow without bound.  The next direct fork is
therefore operational rather than classificatory:

- unbounded holes feed the translated-hole infinite-deletion engine;
- unbounded pairwise-disjoint `D_n` feed co-singleton fusion, restoring
  one point of each minimal destroyer and producing an interlaced doubled
  survival stream.

The remaining mathematical task is to show that repeated co-singleton
restoration cannot self-replicate indefinitely, or that the hole branch
forces a deletion which survives every sufficiently large target.

# GENERAL ORDER: QUADRATIC-TAIL ARITHMETIC RESIDUE ELIMINATED (2026-07-29)

The entire non-fused quadratic-tail remainder has collapsed.  The key fact
is row-local and occurs before difference normalization, fixed-core
descent, or capacity feedback: every prescribed common-column cover row
already chooses a point in its covered tail block outside the distinguished
support.

- `HasPrescribedCommonColumnCover.exists_point_outside_commonSupport`
  uses the row's actual selector.  The distinguished support is one of the
  row's surviving columns and is disjoint from the whole selector, while
  the selector chooses a point of the covered block.  That point and the
  support are exactly a `ReducedStreamFusionStep`.
- `HasCommonColumnAnchoredArithmeticConcentration.
  exists_point_outside_commonSupport` applies this observation to any row
  in the repeated-block concentration.  The arithmetic fork therefore
  never needs to be opened.
- `HasCapacityResolvedTargetLocalizedArithmeticOutcome.
  exact_or_current_or_pointed` audits all seven former terminal branches.
  Every branch other than exact-target or current-order rooted matching is
  pointed-fusion-ready, including aligned differences and repeated-block
  concentration.
- `HasQuadraticTailAlignedResolvedArithmeticAt.fusionReady` promotes the
  audit while retaining the protected source block, bracket, and
  translation `q = target i + δ`.
- `cofinalQuadraticTailAlignedResolvedArithmetic_force_fusedStreams`
  combines this exhaustive three-way stage theorem with the existing
  recurrence resolver.  Its putative simultaneous-cutoff remainder is
  contradictory at the first late stage.
- The new counterexample-level theorem
  `exactBasis_counterexample_forces_fusedSuccessorPredecessorStreams`
  proves that every hypothetical hard-order counterexample with `k > 2`
  produces the full fused successor/predecessor deletion.

This is a direct branch elimination.  In particular, coherent-difference,
fixed-core, capacity, and certificate-linked two-rank outcomes are no
longer open leaves of the quadratic-tail attack.  It is not yet the full
solution: the remaining task is to contradict the single fused-stream
endpoint.  Existing machinery already reduces that endpoint to cofinal
boundary-repair self-replication or fixed-rank contained translated gaps,
so those are now the only live sides of the proof.

# GENERAL ORDER: REPEATED-BLOCK RESIDUE CONSUMED (2026-07-29)

The capacity-feedback repeated-block cluster is no longer a terminal
arithmetic branch.  Its exact cardinal threshold was already strong enough
to feed the anchored arithmetic fork, and the fixed-core leaf of that fork
is itself pointed-fusion-ready.

- `HasAlignedFixedCoreAnchorStar` retains the prescribed cover rows,
  private destroyer traces, one common order-`k` core, one common
  predecessor difference, and injectively many anchors in a literal tail
  block.
- `HasQuadraticTailArithmeticResidueAt.normalizeRepeatedBlock` applies the
  existing anchored arithmetic fork at the exact stored threshold.  The
  repeated cluster becomes aligned difference growth, current-order rooted
  matching, or the fixed-core anchor star.
- The already stored late current-order cutoff removes the matching leaf.
- `HasAlignedFixedCoreAnchorStar.exists_point_outside_support` observes
  that an order-`k+1` support has at most `k+1` points, while the star has
  more than `n+1+k` injective anchors.  One anchor therefore lies outside
  the distinguished support.  Because it lies in the same late tail block,
  that support and anchor form a `ReducedStreamFusionStep`.
- `onlyCoreArithmetic` uses the existing late pointed-fusion cutoff to
  remove the fixed-core leaf outright.  No cleared-marker iteration or new
  capacity assumption is needed.
- The strengthened counterexample capstone is
  `exactBasis_counterexample_forces_fusedStreams_or_eventualQuadraticTailCoreArithmetic`.

This is a genuine branch elimination, not merely a finer classification.
Every hypothetical hard-order counterexample now produces the fused
infinite deletion or, at every sufficiently late protected-gap-aligned
stage, exactly one of two remaining mechanisms: coherent anchored
difference growth or a represented two-rank destroyer.  General order is
still open; the next direct attack is the cardinal recurrence fork between
those two mechanisms, followed by difference composition in the first horn
and minimal-order descent in the second.

# GENERAL ORDER: ALL FUSION-READY TAIL BRANCHES CONSUMED (2026-07-29)

The capacity-resolved quadratic-tail endpoint has been passed through one
global recurrence fork.  Four more terminal geometries now feed a single
infinite-deletion engine.

- `le_localizedArithmeticDiagonalStart` proves that the prescribed
  arithmetic tail begins beyond its own diagonal scale.  Consequently a
  support avoiding a block of that tail supplies an ambient pointed
  support/block pair which clears both required fusion floors.
- `HasQuadraticTailAlignedResolvedArithmeticAt.fusionReady_or_arithmeticResidue`
  is the formal seven-branch audit.  It converts:
  exact-target matching to the existing aligned exact-matching interface;
  current-order matching to its existing interface; and both reduced
  common-column streams and later-block supports to
  `ReducedStreamFusionStep`.
- `cofinalReducedFusionSteps_force_fusedSuccessorPredecessorStreams`
  upgrades a cofinal pointed-step supply to the full fused endpoint,
  including counterexample destruction and represented predecessor
  differences on the same infinite deletion.
- `cofinalQuadraticTailAlignedResolvedArithmetic_resolveFusionReady`
  takes global cofinal/eventual forks over aligned exact matching,
  current-order matching, and pointed fusion.  Recurrence of any one is
  consumed; otherwise three simultaneous cutoffs exclude all four
  fusion-ready geometries at every later stage.
- `onlyArithmeticResidues` checks the remaining disjunction rather than
  relying on its intended reading.  It proves that every sufficiently late
  nonfused stage has exactly one of the three genuine arithmetic forms:
  coherent aligned difference growth, represented order-`k-1` two-rank
  destruction, or the repeated-block cluster created by capacity feedback.
- The counterexample capstone is
  `exactBasis_counterexample_forces_fusedStreams_or_eventualQuadraticTailArithmeticWithoutFusionReady`.

This is a strict branch reduction, not a full solution.  The old capacity
horn and all immediately fusion-ready descendants are gone.  The next
direct target is the repeated-block cluster: either extract a late pointed
block step from its many private rows, or force its common anchors to
produce the already-retained coherent difference-growth branch.  After
that, only difference composition and the genuine two-rank descent remain.

# GENERAL ORDER: ALIGNED QUADRATIC TAIL REMOVES CAPACITY (2026-07-29)

The protected-gap alignment and the quadratic after-the-fact rerun now act
on the same target-private certificate.  Literal block-capacity failure is
no longer a terminal alternative in this strengthened pipeline.

- `quadraticBlockTail_forces_largeTargetLocalizedCertificate` now retains
  both representation of every certificate target and disjointness from
  the complete set of targets which survive every selector of the chosen
  tail.
- `quadraticBlockTail_forces_largeBracketedTargetLocalizedCertificate`
  uses persistence of the protected target stream on every block tail.
  Consequently every large localized certificate label is strictly
  bracketed between consecutive protected targets, and its bracket index
  lies beyond the tail start.
- `quadraticBlockTail_forces_alignedTargetLocalizedArithmeticOutcome`
  extends the target-private tail selector over the discarded prefix and
  invokes the moving-root matching at the lower bracket endpoint.  It
  retains the same source block, the same selector, and
  `q = target i + δ` while applying the complete localized arithmetic fork
  on the tail.
- `HasCapacityResolvedTargetLocalizedArithmeticOutcome` has no bare
  small-block member.  If anchored concentration exposes one, the existing
  quadratic feedback reruns that same certificate and replaces it by an
  exact-target rooted matching, a support avoiding a strictly later tail
  block, or a repeated-block cluster above the full anchored threshold.
- The counterexample capstone
  `exactBasis_counterexample_forces_cofinalQuadraticTailAlignedResolvedArithmetic`
  supplies such a protected-gap-aligned, capacity-resolved stage at every
  diagonal scale.

This closes the old-block loophole in the capacity attack; it does not yet
settle general order.  The remaining diagonal alternatives are now
fusion-ready exact-target/reduced/later-block geometry, current-order
matching growth, coherent anchored difference growth, represented
two-rank destruction, and the repeated-block cluster.  The next direct
fork is to fuse every cofinally recurring fusion-ready alternative,
leaving only the last three arithmetic branches.

# GENERAL ORDER: MOVING-ROOT FUSION IS QUADRATIC AT SOURCE (2026-07-29)

The coherent moving-root construction now builds in the exact quadratic
block growth needed by the existing after-the-fact cardinal feedback
theorem.

- `freshPredecessorRootedMatchingSteps_have_commonSurvivalPartition_avoiding`
  requests `(i + k + 2)^2` fresh petals at stage `i`, rather than weakening
  its arbitrary-demand supply to a merely linear block.
- The recursive selector argument still leaves more than `i+1` surviving
  supports after an arbitrary block selector; the stronger block-cardinality
  conclusion is therefore obtained without weakening the protected-target
  survival stream.
- At successor order, the moving-root block `cell i` now satisfies
  `(i + k + 3)^2 < |cell i|`.  This bound is retained through the migrating
  certificate, translation-exit fan, aligned arithmetic, translated-hole,
  and current-order matching capstones.
- The older public common-survival wrapper continues to expose its original
  linear conclusion by deriving it from the square, so existing consumers
  that do not need cardinal feedback remain unchanged.

This is an enabling strengthening, not a solution by itself.  A capacity
witness for the full partition may still occur in an arbitrarily old block.
The next direct step is therefore to run the target-localized certificate on
the prescribed quadratic tail and bracket its target against the same
protected stream.  That discards every old block while retaining the source
block and translation, allowing the existing capacity rerun to act on the
aligned configuration rather than on a separate certificate.

# GENERAL ORDER: CURRENT-ORDER MATCHING INJURY CONSUMED (2026-07-29)

The unbounded order-`k` rooted-matching member of the final aligned
arithmetic fork is no longer a terminal alternative.

- `HasCurrentOrderRootedMatchingAt` records the nonvacuous geometry:
  arbitrarily many supports of one order-`k` target with a bounded common
  root and pairwise-disjoint nonempty petals.
- `freshSuccessorStepSupply` asks for enough of those supports to absorb
  the complete old-prefix and bounded-target thresholds.  The existing
  normalization theorem clears the old root and pads any descended rank
  to order `k+1`, preserving the petal cardinality.
- `HasCofinalCurrentOrderRootedMatchings.fusesInfiniteDeletion` runs the
  coherent rooted-matching recursion.  It produces one infinite deletion
  with a strict surviving successor stream; counterexample destruction and
  predecessor bracketing then supply the full
  `HasFusedSuccessorPredecessorStreams` endpoint on that same deletion.
- `resolveCurrentOrderRootedMatchings` applies the cofinal/eventual fork to
  the aligned arithmetic remainder.  Recurrence is consumed by the fusion
  above.  Otherwise one explicit cutoff excludes a diagonal-size
  order-`k` rooted matching at every later scale.
- The counterexample-level capstone
  `exactBasis_counterexample_forces_fusedStreams_or_eventualAlignedArithmeticWithoutCurrentMatching`
  therefore leaves, outside the fused engine, only coherent anchored
  difference growth, represented two-rank destruction, and the
  after-the-fact capacity-feedback branch.

This removes a genuine cardinal branch; it does not settle the theorem.
The next direct elimination target is capacity feedback, using the existing
quadratic-tail rerun to turn every small-block witness into a later
block-avoidance step or a repeated-block cluster.  After that, the
coherent-difference and two-rank branches are the remaining arithmetic
obstructions.

# GENERAL ORDER: LOWER-RANK TRANSLATION GAPS STABILIZE (2026-07-29)

The no-boundary side of the fused-stream fork can no longer escape by
changing lower rank from stage to stage.

- `cleanSupport_destroyedTranslate_forces_lowerGap_or_boundaryLanding`
  now retains the key localization invariant through the whole finite
  descent: every returned lower support `G` is contained in the original
  clean protected support `E`.  A rank-one boundary endpoint is likewise
  still an actual point of `E`.
- `forces_cofinalBoundaryRepairs_or_cofinalContainedLowerTranslationGaps`
  uses that containment to eliminate the boundary endpoint after one
  failed repair floor.  A boundary point would repair the same destroyed
  bracket, contradicting the chosen failure.  What remains cofinally is a
  literal translated gap
  `additiveSupportFamily A ℓ (u + δ) = ∅`, with `G ⊆ E`, at some
  `0 < ℓ < k` and with the exact bracket displacement
  `m = oldTarget n + δ`.
- `HasFusedContainedLowerTranslationGapAt` packages precisely this
  same-bracket, same-translation configuration.
- `forces_cofinalBoundaryRepairs_or_fixedRankCofinalContainedLowerTranslationGaps`
  applies the finite pigeonhole principle to the ranks `1,...,k-1`.
  Unless boundary repairs occur cofinally, one fixed rank `ℓ` supplies
  contained translated gaps above every floor.

This is a genuine stabilization result, not yet a contradiction.  The
rank may be `ℓ = 1`; then the conclusion is a protected basis point whose
translate is missing, information already present in the universal
literal-hole branch.  The missing amplification is therefore cardinal:
one must force many same-`δ` holes inside a single protected bracket (so
the existing translated-hole fusion applies), or, for `ℓ ≥ 2`, compose an
order-`k` representation of `u + δ` with `G ⊆ E` to repair the destroyed
target or descend a genuinely smaller invariant.  No full `k ≥ 3`
solution is claimed.

# GENERAL ORDER: FUSED STREAMS FORCE A LITERAL TRANSLATION BOUNDARY (2026-07-29)

The fused surviving/destroyed stream has now been converted into literal
membership information at cofinally large basis points.

- `additiveSupportFamily_exists_floorBoundedAnchor` is the large-anchor
  counterpart of the earlier average-bounded-anchor lemma: an order-`h`
  support of a target at least `h * L` contains an actual support point
  `c ≥ L`.
- `cleanSupport_destroyedTranslate_forces_lowerGap_or_boundaryLanding`
  verifies the proposed finite simultaneous rank descent.  It preserves
  the common translation and cofinal floor until it reaches either a
  strict lower-rank translated gap or a clean-to-deleted rank-one landing.
  This theorem is correct, but its lower-gap horn can end at rank one and
  is therefore not being treated as the endgame.
- `cleanSupport_destroyedTranslate_forces_largeHole_or_boundaryLanding`
  bypasses that weak escape.  Apply translation exit directly to the large
  point `c` in the original clean support.  Then `c + δ` is either
  literally absent from `A`, or is a point of the deletion `Y`.
  In the latter case the theorem constructs the translated repair and
  proves that restoring just `c + δ` makes the destroyed target survive.
- `HasFusedSuccessorPredecessorStreams.forces_cofinalLargeTranslationHole_or_boundaryLanding`
  retains the protected bracket, clean support, exact displacement,
  destroyed upper target, and the explicit co-singleton repair.
- `forces_cofinalLargeTranslationHoles_or_cofinalBoundaryRepairs`
  homogenizes the mixed outcome: every fused stream has either cofinally
  large missing translates or cofinally many one-point boundary repairs.
- `cofinalBoundaryRepairs_fuse_residualDeletion` performs the infinite
  co-singleton iteration.  It alternates a repaired landing with a later
  reserved point of `Y`, producing an infinite residual deletion `B`,
  an infinite restored part `Y \ B`, and one strict stream of formerly
  destroyed upper targets which all survive deletion by `B`.
- `cofinalBoundaryRepairs_regenerate_fusedStreams_on_strictSplit` applies
  counterexample destruction and predecessor bracketing on that same
  residual `B`.  Hence the boundary horn reproduces the complete fused
  endpoint on a strict infinite split, with a new interlaced survival
  stream.
- The boundary-first fork
  `forces_cofinalBoundaryRepairs_or_eventuallyPureLargeTranslationHoles`
  now isolates the other case sharply: if the repair iteration is not
  cofinal, then beyond one floor no boundary repair exists and every
  sufficiently late mixed stage is forced to be a literal translated
  hole.
- `not_boundaryRepairAt_forces_all_largeSupportPoint_translates_missing`
  upgrades that pure branch from an existential witness to a universal
  law.  Above the failed repair floor, for every protected gap, every
  clean lower-endpoint support, and every sufficiently large point `c` in
  that support, the aligned translate `c + δ` is outside `A`.  Otherwise
  `cleanSupport_boundaryPoint_survives_after_restoring` constructs exactly
  the forbidden co-singleton repair.

Both horns are nonvacuous membership statements; no bare “represented
target” conclusion is used.  This does **not** yet settle the general
problem.  The next direct attack is either to iterate the strict-split
self-replication while accumulating all repaired survival streams, or to
combine this universal hole law with the represented destroyed
order-`k` predecessor in the same bracket, forcing coordinate exchange or
a strict lower-rank translated gap.

# GENERAL ORDER: FOUR ALIGNED HORNS CONSUMED (2026-07-29)

The exact-target, reduced-stream, arithmetic-concentration, and
translated-hole program has now been carried through to one verified
counterexample-level endpoint.

- `HasCofinalAlignedExactTargetRootedMatchings.fusesInfiniteDeletion`
  prefix-clears recurrent exact-target matchings and fuses them into one
  infinite deletion carrying strict surviving successor targets, cofinal
  destroyed successor targets, and represented destroyed predecessor
  differences.
- `HasEventuallyAlignedHolesOrNonmatchingArithmetic.resolveReducedStreams`
  sends recurrent reduced common-column streams through the same endpoint.
- `HasEventuallyAlignedHolesOrAnchoredConcentration.resolveConcentrations`
  feeds anchored concentration through the localized arithmetic threshold.
  The concentration predicate disappears, leaving aligned anchored
  order-`k` difference growth, order-`k` rooted matching growth, a
  represented order-`k-1` two-rank injury, or a literal block-capacity
  failure.
- The difference-growth branch deliberately retains its certificate row
  label `p`, block anchor, lower core, private row trace, and equation
  `d = p - anchor p`.  The formal audit
  `HasAlignedAnchoredDifferenceGrowth.certificate_large` shows that its
  cardinal demand forces the localized certificate itself to grow.  The
  weaker statement “many order-`k` targets are represented” is automatic
  for a basis and is not used as a terminal outcome.
- The fusion interface now records a chosen point rather than requiring
  the preserved support to avoid its entire block.  This exact
  strengthening lets
  `HasCofinalAlignedTranslationHoles.fusesInfiniteDeletion` choose a hole
  in each late source block, preserve a different source petal at the same
  stage, and use the existing bounded cross-avoidance theorem to eliminate
  all interactions between different stages.
- `finiteComplement_forbids_cofinalAlignedTranslationHoles` is the formal
  junk test: a common shift injects every hole set into `Aᶜ`, so cofinite
  sets cannot satisfy the cofinal-hole hypothesis.
- The capstone
  `exactBasis_counterexample_forces_fusedStreams_or_eventualAlignedArithmeticInjuries`
  says that a hypothetical general-order counterexample (`k > 2`) now
  forces either the fused infinite deletion above or an eventual aligned
  stream of exactly the four explicit arithmetic injuries.

This is genuine branch elimination, but it is **not** yet the full
`k ≥ 3` solution.  The next mathematical obligation is to make the fused
surviving/destroyed streams contradict current-order minimality, or to show
that every one of the four retained injury streams feeds that same
contradiction.

# GENERAL ORDER: RANK-ONE AUDIT AND PRIVATE-CORE NORMAL FORM (2026-07-28)

The terminal-fusion attack produced a correct residue-collapse theorem, but
an adversarial audit found that its original hypothesis was too strong to
represent live mathematics.

- `minimalAdditiveDestroyer_noStrictRankDescent_forces_singletonDiagonal`
  shows that a minimal order-`h` destroyer with no represented destruction
  at any positive lower rank is a singleton diagonal.
- This yields affine matching and residue-collapse consequences, culminating
  in `terminalFusion_cofinalSuccessorDestruction_impossible`.
- However, the phrase "no positive lower-rank destruction" includes rank
  one.  For every basis point `x` in a nonempty destroyer, the order-one
  support of `x` is `{x}`, so that destroyer automatically destroys a
  represented rank-one target.  Thus the all-positive-ranks terminal horn
  is already degenerate.  Eliminating it does **not** settle the genuine
  root-capture/co-singleton obstruction, and the audit-level theorems which
  return some `0 < ℓ < h` may return only this automatic `ℓ = 1` case.

The attack has therefore been tightened to exclude only genuinely
nontrivial ranks `2,...,h-1`.

- `minimalAdditiveDestroyer_noNontrivialRankDescent_forces_privateCoreNormalForm`
  proves the resulting exact shape.  For each destroyer point `x`, either
  `q = h*x`, or a private support contains exactly one occurrence of `x`;
  deleting it leaves an order-`h-1` core at the coherent difference `q-x`
  which is disjoint from the entire destroyer.
- `minimalAdditiveDestroyer_noNontrivialRankDescent_forces_privateCores_off_oneDiagonal`
  shows that the diagonal escape occurs for at most one point.  Every other
  destroyer coordinate therefore owns one of these exact private
  predecessor cores.
- `minimalAdditiveDestroyer_nontrivialRankDescent_or_privateCores_off_oneDiagonal`
  is the corrected exhaustive fork: either there is a represented destroyed
  rank `ℓ` with `1 < ℓ < h`, or all but at most one coordinate have the
  coherent private-core form.
- `privateCores_largeSet_forces_protectedRepair_or_lowerDifferenceGrowth`
  performs the first cross-stage composition against a finite old prefix
  `U`.  A private core avoiding `U` is an immediately protected repair.  If
  every core meets `U`, one old point `u` occurs in many private supports;
  removing `u` gives the same number of distinct order-`h-1` supports at
  the single coherent difference `q-u`.
- `largeMinimalDestroyer_forces_nontrivialRankDescent_or_protectedRepair_or_lowerDifferenceRootedMatching`
  adds the exact cardinal threshold and normalizes the growth horn.  A
  destroyer larger than
  `|U| * additiveRootedMatchingBound (h-1) r + 1` forces genuine rank
  descent, a prefix-avoiding private repair, or a rooted matching larger
  than `r` at one exact old difference.

Thus the finite-prefix composition now pays exactly as desired for large
destroyers.  The live boundary is the complementary bounded-destroyer
regime: schedule a prefix-independent threshold, or fuse the protected
private repairs while preventing later blocks from hitting earlier repair
supports.  No full `k ≥ 3` solution is claimed.

# FRESH RECURRENT GAP REPAIRS (2026-07-27)

The remaining lower-gap branch can now be made genuinely fresh at every
finite stage.

- `eventually_lockedPrefix_matching_or_freshGap_or_rankGrowthDescent`
  threads an arbitrary bounded protected set through the locked-prefix
  composition and forces every predecessor-gap point outside it.
- `eventually_finiteCertificate_matching_or_freshLowerGap` preserves that
  exclusion through the terminating target descent.
- `cofinal_rootedMatching_or_freshLowerGap` globalizes the result with
  strong deletion.
- `cofinal_prefixDisjointRootedMatching_or_freshLowerGap` normalizes both
  matching-growth horns back to the original order.  Against the same
  arbitrary finite prefix, its matching root is disjoint from the prefix
  and its alternative gap-repair point is not in the prefix.

Thus recurrent gap repairs can no longer stall by recycling finitely many
old vertices.  The remaining task is persistence: fuse the fresh repairs
and fresh rooted-matching petals into one infinite deletion while ensuring
that later choices do not re-damage supports locked at earlier targets.

# GROWING-BLOCK BINARY MIGRATION (2026-07-27)

The binary repair obstruction no longer has permanently undersized blocks.

- `LowerTriangularBinaryRepairSequence.
  exists_growingBlockCommonSurvivalPartition` groups `i+2` mutually
  cross-disjoint binary cells into block `i`.  Its exact cardinality is
  `2(i+2)`, and every selector still preserves every subcell target: the
  selected point can touch only one subcell, where the opposite private
  repair survives.
- `boundedFullTranslateDestroyers_growingBlockCommonSurvival` applies this
  regrouping directly to the bounded-moving branch.
- `boundedFullTranslateDestroyers_forces_growingBlockCertificateMigration`
  combines the growing blocks with strong successor deletion and retains a
  target-localized late certificate disjoint from the infinite protected
  target stream.

Consequently the earlier binary certificate-migration branch can now be
fed into the same certificate-safe old/contemporary capacity argument as
the coherent matching reservoir.  The next step is to run that amplifier
on this grouped partition and dispose of its finite old prefix.

# CERTIFICATE-SAFE OLD-BLOCK COMPOSITION: MIGRATION TERMINATES (2026-07-27)

The old-coordinate branch has now crossed the certificate-safety barrier.
This is a genuine elimination of a former branch, not another reformulation
of it.

- `lockedPrefixSurvival_extends_avoiding_protected` is the support-local
  completion theorem.  If the intrinsic locked prefix does not destroy the
  current target, choose one surviving support and reroute only selector
  coordinates which hit that support.  No locked block is touched, and all
  new values avoid both the repair support and the stored supports of larger
  certificate targets.
- `exists_maximalDestroyedCertificateTarget` chooses the maximum target
  still destroyed by a selector.  It packages the exact invariant needed
  for iteration: every larger certificate target survives.
- `lockedPrefix_destroys_or_rankGrowthCertificateDescent` and
  `blockAligned_intrinsicLockedPrefix_destruction_or_rankGrowthDescent`
  show that failure of the protected completion is not an uncontrolled
  migration.  It returns a strictly smaller destroyed target together with
  the proof that every larger target survives for the new selector.
- The locked prefix has a target-independent bound in the absence of
  current-order rooted matching growth.  Therefore
  `eventually_lockedPrefix_matching_or_gap_or_rankGrowthDescent` feeds
  genuine locked-prefix destruction into the uniform
  finite-prefix/difference theorem.  Its represented-difference horn is
  normalized to a predecessor rooted matching; its only arithmetic escape
  is a real predecessor gap.
- `eventually_finiteCertificate_matching_or_lowerGap` terminates migration
  by strong induction.  Starting from the maximum destroyed certificate
  target, every descent moves to a strictly smaller target while retaining
  survival of all larger targets.  A finite certificate therefore cannot
  support endless repair migration.
- `cofinal_rootedMatching_or_lowerGap` composes the result directly with
  strong infinite deletion.  It needs neither a bound on certificate
  cardinality nor the diagonal-row hypothesis used by the earlier scheduled
  route.
- `largeSupportFamily_forces_cofinal_prefixDisjointRootedMatching` removes
  all three losses in the matching horn.  Common-root collisions are
  consumed by strict rank descent, a finite support count forces the
  translated target arbitrarily late, and fresh padding restores the
  original order without changing the petals.
- Consequently
  `cofinal_prefixDisjointRootedMatching_or_lowerGap` is the strongest
  unconditional endpoint of this attack: against every finite prefix and
  every size and target demand, a hypothetical strongly minimal
  order-`k+1` basis has a cofinal order-`k+1` rooted matching whose root
  avoids that prefix, or a late certificate target in a genuine translate
  `b + Gap_k(A)`.

Thus repeated old-coordinate collisions and certificate migration are no
longer open mathematics.  Erdős 881 for all `k ≥ 3` is still not claimed:
the remaining branch is the recurrent lower-gap translate.  Closing the
problem now requires either making those gap repairs persistent under all
later block choices, or converting their recurrence into the adaptive
matching-growth/cofinite-cover hypothesis already consumed by the sparse
infinite-deletion theorem.

# REPEATED OLD-COLLISION AMPLIFICATION AND UPPER-RANK DESCENT (2026-07-27)

The old-coordinate collision branch has now been split by actual block
capacity, and the bounded-certificate migration has been made to terminate.
This is new mathematical progress, not another renaming of the obstruction.

- `exists_localSupportChoiceSubcover` and
  `exists_point_avoiding_families_or_localSupportChoiceSubcover` remove the
  global certificate-cardinality loss.  If one old block has no point
  avoiding the immediate collision family and all protected supports, then
  at most the cardinality of that block's own vertices identifies a
  subcollection of protected targets which already covers the block.  The
  quantitative union bound retains the ranks of both support families.
- `oldBlock_exactGrowth_or_safeSecondChoice_or_localLargerDependency`
  applies this compression to the entire exact support family at the
  current target.  Its alternatives are exact support growth, a point which
  is a verified safe replacement and avoids all stored larger-target
  supports, or an explicit bounded set of strictly larger dependencies.
- `oldBlock_rootedMatching_or_safeSecondChoice_or_manyLargerDependencies`
  normalizes the first horn.  Once the block is larger than the rooted
  matching threshold plus `m` protected supports, the last horn contains
  more than `m` distinct strictly larger targets.
- `blockAligned_at_certificateMax_rootedMatching_or_strictDescent` observes
  that the dependency horn is impossible at the maximum certificate
  target.  A single large active block therefore forces an exact rooted
  matching or strict descent, with no dependence on `Q.card`.
- `blockAlignedRepairWitness_extends_protected_of_hitBlockCapacity` proves
  that selector completion needs capacity only in blocks actually met by
  the chosen repair support—at most `k+1` blocks—not in every block of the
  partition.
- `blockAligned_upperRankCapacity_rootedMatching_or_strictDescent` combines
  these gains at an arbitrary descent stage.  Every occurrence of the full
  certificate cardinality is replaced by
  `|{u ∈ Q : q < u}|`, and the completion capacity is required only at
  selected coordinates occurring in supports of `q`.
- `certificateUpperRank_strictly_grows_under_descent` makes termination
  quantitative: if the certificate moves from `q` to `u < q`, the number
  of certificate targets above the current one strictly increases.
  `blockAligned_upperRankCapacity_rootedMatching_or_rankGrowthDescent`
  records this monotone measure in the descent output.
- `blockAlignedRepairWitness_extends_protected_or_hitBlockCollision`
  removes the last irrelevant capacity assumptions.  A chosen repair
  support needs room only at selected coordinates which that very support
  hits; every untouched block is left unchanged.
- `blockAlignedSafeSwap_upperCertificate_forces_descent_or_oldCollision`
  retains the actual private collision support when support-local
  completion fails.  Its alternatives are now strict downward certificate
  migration or a support `E` with `E ∩ D = {d}` at an exceptional old
  block.
- `blockAligned_manyActivePoints_force_rootedMatching_or_rankGrowthDescent_or_oldGrowth`
  runs this fork at every contemporary active point.  If descent never
  occurs, the private supports inject those points into the lower-order
  support families at the exceptional old coordinates.  More than
  `|J|r` active points therefore force more than `r` coherent
  representations at one old coordinate.
- `blockAligned_manyActivePoints_force_matchingGrowth_or_rankGrowthDescent`
  normalizes that lower-order support growth.  Every output is now a
  genuine large rooted matching at order `k+1`, strict upper-rank descent,
  or a genuine large rooted matching at order `k`.
- `deficientRepairHitBlocks` makes `J` canonical: it contains exactly the
  blocks met by supports at `q` which fail the active-choice or completion
  threshold.  It has cardinality at most the number of support vertices at
  `q`.  `blockAligned_intrinsicDeficientBlocks_force_matchingGrowth_or_rankGrowthDescent`
  applies the amplification with this intrinsic set, so no externally
  chosen old prefix remains in the local theorem.
- `blockAligned_matchingGrowth_or_rankGrowthDescent_or_boundedDestroyer`
  removes even the density hypothesis.  If too few destroyer points lie
  outside the intrinsic deficient blocks, the old part contributes at most
  one point per block.  In the absence of current-order matching growth,
  the support family and hence its support-vertex union are bounded by the
  rooted-matching threshold.  The whole minimal destroyer is therefore
  bounded by the explicit target- and certificate-independent constant
  `oldCollisionConcentrationBound k r`.
- `additiveSupportFamily_hitFilter_card_le_lowerDifference` proves that all
  order-`k+1` supports at `q` containing one fixed old selected summand
  inject into the order-`k` supports at the corresponding difference.
  Consequently, if that lower family has at most `r` members, the union of
  every possible collision support at that coordinate has at most
  `(k+1)r` vertices.
- `exists_blockChoice_avoiding_protected_and_allHitSupports` uses that bound
  to choose one point of the old block outside both the protected
  certificate union and **every** possible repair support through the old
  coordinate.  This is a universal second choice, not a choice made after
  one collision witness has been fixed.
- `blockAlignedRepairWitness_extends_protected_or_smallOldCollision` and
  `blockAlignedSafeSwap_certificate_forces_smallOldCollision` show that a
  failed protected repair can now collide only at an old block of size at
  most `|U| + (k+1)r`.
- `positiveOrder_targetLocalized_manyContemporaryPoints_force_growth_usingSecondChoices`
  repeats the private-support injection using only those undersized old
  blocks.  The pigeonhole denominator is therefore the number of genuinely
  capacity-deficient blocks, not the size of the whole old prefix.
- `eventually_boundedMinimalDestroyer_protectedRepair_or_growth` closes the
  complementary all-block-capacity case for every bounded minimal
  destroyer, including the formerly troublesome small destroyers.
- `eventually_boundedCertificate_forces_supportGrowth` feeds those repairs
  into strict target descent and invokes
  `finiteSelectorCertificate_impossible_of_strictRepairStep`.  A bounded
  late certificate must force actual support growth; repeated migration
  cannot cycle.
- `eventually_boundedCertificate_forces_matching` normalizes that growth to
  a genuine matching.  Finally,
  `exists_fixedPartition_largeCertificate_or_arbitraryMatching` fixes one
  partition whose block size depends only on the proposed certificate bound
  `C`, then handles every later matching demand `r`.  The partition no
  longer has to be rebuilt as `r` grows.
- `lowerDifferenceSupportFamily_card_le_twice_exact` now prevents the
  difference horn from losing its target label.  Splitting the supports at
  `q-d` according to whether they contain `d` shows that their cardinality
  is at most twice the order-`k+1` support cardinality at the original
  target `q`.
- Consequently
  `eventually_boundedCertificate_forces_exactRootedMatching` and
  `exists_fixedPartition_largeCertificate_or_cofinalExactRootedMatching`
  strengthen the bounded-certificate payoff: the large delta systems occur
  cofinally at the original order and at actual late certificate targets,
  not at an uncontrolled lower-rank difference.

This still does **not** prove Erdős 881 for all `k ≥ 3`, but the repeated
old-collision branch requested in the preceding status is now closed
without a density assumption.  At each stage there are only four outcomes:
current-order matching growth, lower-order matching growth, strict descent
which consumes the finite upper-rank budget, or a minimal destroyer bounded
by `oldCollisionConcentrationBound k r`.  The remaining global composition
is now concrete: feed that last uniform bound into the existing late
finite-prefix/two-block repair theorem while retaining protection only for
the larger certificate targets.  The point requiring care is that the
older theorem localized every target other than `q`, whereas the new
terminating descent intentionally leaves smaller targets free to become the
next state.

# OLD-COLLISION AMPLIFICATION: REPRESENTED-DIFFERENCE ESCAPE CLOSED (2026-07-27)

The old collision left by the previous block split has now been amplified
into genuine matching growth.  This is a mathematical closure, not merely a
rephrasing of the obstruction.

- `blockAlignedRepairWitness_extends_protected_or_oldCollision` retains the
  actual support witnessing a safe finite swap.  It either completes the
  protected selector or returns an old selected point lying in that support.
- `blockAlignedSafeSwap_certificate_forces_oldCollision` adds the crucial
  private-hit identity
  `E ∩ D = {s i}`.  Hence collision supports obtained from different active
  points of one minimal destroyer are necessarily distinct.
- `positiveOrder_targetLocalized_activeBlock_growth_or_oldCollision`
  threads that private support through the active-block incidence fork.
- `positiveOrder_targetLocalized_manyContemporaryPoints_force_growth`
  performs the amplification.  For every contemporary `d ∈ D`, remove the
  returned old summand from its private collision support.  The map
  `d ↦ (old block index, lower support)` is injective: equal lower data
  reconstruct equal upper supports, and intersecting with `D` recovers
  `d`.  Thus more than `|J|r` contemporary points force more than `r`
  lower-order supports at one coherent difference.
- `eventually_targetLocalized_destroyer_growth_or_twoBlockRepair` closes the
  complementary case.  If there are at most `|J|r` contemporary points,
  the entire destroyer has a uniform bound: at most `|J|` old points plus
  `|J|r` contemporary points.  Uniform finite-prefix composition applies to
  the whole destroyer and yields support growth or a lower-order gap, which
  is converted to a complete selector repair.
- `eventually_targetLocalized_destroyer_matching_or_twoBlockRepair`
  normalizes either support-growth horn through the finite-rank descent.
  Its final outcome is exactly: an arbitrarily large genuine matching at
  some positive rank at most `k`, or a full selector preserving the repaired
  target.

This removes the former one-off represented-old-difference horn.  Erdős 881
for all `k ≥ 3` is still not claimed.  The remaining local branch is now the
complete selector repair: it preserves the localized target `q`, but may
destroy another member of the finite certificate.  Globally, the scheduled
partition must also synchronize the old cutoff `J` with the late threshold
and contemporary capacity.  The next attack is therefore certificate-safe
second-choice repair (or a strictly descending migration argument), followed
by that scheduled quantifier integration.

# OLD/CONTEMPORARY DESTROYER SPLIT COMPLETED (2026-07-27)

The proposed block split is now formalized as an exhaustive theorem, with
the lower-gap horn converted all the way to a full selector repair.

- `lowerGapRepair_extends_to_twoBlockSelectorSurvival` starts from a
  lower-order gap swap, selects the gap point in its actual partition block,
  retains every still-damaged selected value, and reroutes all other blocks
  outside one surviving support.  Thus a gap point in a different block is
  no longer an alignment obstruction.
- `blockAlignedSafeSwap_extends_protected_or_oldDifference` needs the large
  protected-union capacity only on contemporary blocks.  It either completes
  the protected repair, or identifies an old selected summand `d` for which
  `q-d` is represented one order lower.
- `blockAlignedSafeSwap_certificate_forces_oldDifference` uses the protected
  supports for the other certificate targets: the completed repair would
  contradict the entire certificate, so the old represented difference is
  forced.
- `positiveOrder_targetLocalized_activeBlock_growth_or_oldDifference`
  combines that completion with the same-block incidence count.  An active
  contemporary coordinate forces more than `r` supports at a coherent
  lower-order difference unless an old selected summand is exposed.
- `eventually_oldBlockDestroyer_growth_or_twoBlockRepair` handles the other
  side.  If the whole minimal destroyer lies in a prescribed finite set of
  old blocks, the corresponding old selector prefix destroys the target.
  The uniform finite-prefix theorem then forces a lower-order support family
  larger than the old prefix, or a lower-order gap; the gap is converted to
  a complete selector preserving the target.
- `eventually_targetLocalized_destroyer_oldContemporarySplit` packages the
  exhaustive classification: a minimal destroyer either has a contemporary
  coordinate and enters the protected incidence fork, or is wholly old and
  enters finite-prefix growth-or-repair.

This is genuine closure of the wholly-old horn, but it is not yet a proof of
all `k ≥ 3`.  The remaining contemporary escape is precise: a support
surviving the aligned repair may meet an old selected coordinate that is
*not itself in the minimal destroyer*.  Removing it represents `q-d`, but
the old prefix need not destroy `q`; consequently the finite-prefix theorem
cannot be applied to that one collision without an additional argument.
The next attack must either accumulate repeated old collisions into
large/matching growth at a fixed old difference, or obtain a second
old-block choice which avoids both the repair support and the protected
certificate supports.

# BLOCK-ALIGNED REPAIR WITH COLLATERAL TARGETS PROTECTED (2026-07-27)

The same-block repair branch has now been carried through a full finite
selector certificate.  This is stronger than the previous one-target
migration statement.

- `positiveOrder_minimalDestroyer_activeBlock_safeSwap_avoiding_or_differenceGrowth`
  runs the external-anchor incidence count using only alternatives outside
  an arbitrary protected finite union.
- `blockAlignedSafeSwap_extends_avoiding_protectedUnion` completes a finite
  safe swap to a full infinite block selector while avoiding that protected
  union and preserving the repaired target.
- `exists_protectedSupportUnion_of_targetLocalization` chooses one surviving
  support for every other target of a cardinal-minimal certificate.  Their
  union avoids the localized selector and has cardinality at most
  `(k+1)|Q|`.
- `blockAlignedSafeSwap_impossible_of_protectedCertificateSupports` shows
  that a replacement outside this union cannot merely migrate the
  obstruction: it would preserve every target in the certificate and hence
  contradict the certificate.
- `positiveOrder_targetLocalizedCertificate_largeBlocks_forces_supportGrowth`
  therefore eliminates the safe horn whenever the blocks contain both the
  incidence budget and the protected supports.
- `arbitrarilyLate_largeMinimalCertificate_or_supportGrowth`, followed by
  finite-rank normalization in
  `arbitrarilyLate_largeMinimalCertificate_or_matching`, gives the current
  exhaustive endpoint: for every prescribed `C` and `r`, either a
  cardinal-minimal target-localized certificate has more than `C` targets,
  or there is a genuine matching of more than `r` additive supports at some
  positive rank at most the original order.

The partition side has also been strengthened.
`IsFiniteBlockPartition.exists_coarsening_preserving_evenBlocks_with_cardLower`
uses even blocks as service cores and all odd blocks as finite fillers to
give independently prescribed lower cardinalities.
`exists_scheduledLargeAnchoredPartition` combines this with the scheduled
anchor construction, so large block capacities can be fixed before a
certificate is revealed.

This still does **not** settle all `k ≥ 3`.  The remaining horn is no longer
an unaligned safe replacement: it is an unbounded cardinal-minimal
certificate.  The precise scale issue is that a minimal destroyer for a very
large target may use an old block whose finite capacity was scheduled at an
earlier scale.  The next composition must either force an essential damaged
summand into a contemporaneous large service block, or use the coherent
finite-prefix difference theorem on the old-block part and the protected
repair theorem on the late-block part.

# SCHEDULED COHERENT DIFFERENCE COMPOSITION: MOVING PREFIX CLOSED (2026-07-27)

The finite-prefix/difference branch has advanced through its former
quantitative obstruction.  It is no longer necessary to compare a moving
target against a threshold chosen only after its deletion prefix is known.

- The universal diagonal is thinned to exactly one distinguished cell per
  row.  Consequently `damagePrefix M` now has exactly `M` points, rather than
  merely being finite.
- `card_rootedMatching_le_destroyer_of_rootDisjoint` proves the repair/counting
  step: if the common root avoids a destructive prefix, pairwise-disjoint
  petals inject into that prefix.
- `large_destroyedRootedMatching_descends_through_prefix` gives the opposite
  outcome.  A rooted matching larger than the prefix forces a deleted common
  summand `d`; removing it preserves the whole family at the coherent
  lower-order difference `q-d`.
- `eventually_boundedDestroyer_forces_largeDifferenceFamily_or_lowerGap`
  makes the late threshold uniform over every destroyer of cardinality at
  most `M`.  It depends on `M`, not on the destroyer's actual vertices.
- `exists_scheduledThinAnchoredPartition` schedules the `M`-th row anchor
  beyond the uniform `M`-point threshold and retains a bijection between rows
  and completed partition blocks.
- `strongDeletion_forces_scheduledCoherentDifferenceSystem` uses those
  anchors as one fixed selector.  Its destroyers are literal initial
  segments of that one infinite selector.  Arbitrarily long prefixes force
  either more than `M` lower-order supports at some `q-d` with `d` in the
  same prefix, or a genuine lower-order gap `q-b`.
- `strongDeletion_forces_cofinalDifferenceMatching_or_lowerGap` applies the
  finite-rank descent: the large-difference branch yields arbitrarily large
  genuine matchings at a positive rank at most `k`.
- `finiteTranslateGrowth_or_cofinalDifferenceMatching_or_lowerGap` packages
  the exhaustive outcome for a hypothetical strongly minimal order-`k+1`
  basis.
- `lowerOrderGap_point_avoids_successorSupports` and
  `swap_hit_for_lowerGap_repairs` identify the arithmetic value of the
  remaining horn: a witness `q-b ∈ Gap_k(A)` is absent from every
  order-`k+1` support of `q`, so replacing any private hit of an
  inclusion-minimal destroyer by `b` repairs `q` exactly.

This closes the moving-prefix synchronization and performs the requested
finite-prefix/difference composition.  It does **not** yet settle all
`k ≥ 3`.  The remaining mathematical branch is now explicit: in the
primitive-order case, the maximum certificate targets may repeatedly fall
in lower-gap translates `b + Gap_k(A)`.  The next attack must either align
those already verified safe gap replacements with the blocks of the
coherent deleted summands, or show that their recurrence upgrades the other
finite-translate matching-growth branch to a cofinite target cover.

# UNIVERSAL PRE-CERTIFICATE PARTITION: INFINITE TAIL NEUTRALIZED (2026-07-27)

The quantifier order has now been handled as far as bounded support alone
allows.  The new construction is genuinely universal: its partition, a base
selector, and a nested exhaustion of that selector are all fixed before any
strong-deletion certificate is returned.

- `exists_finiteBlockPartition_for_disjointRows` now retains the bijective
  cell-to-block locator already present in its construction.
- `HasDiagonalAnchoredAlignedTranslateCellRows.
  exists_universalPartition_localizingFiniteTargets` thins the diagonal to
  the nested labels `range (j+1)`, completes those cells to one partition, and
  fixes a base selector together with monotone finite sets
  `damagePrefix M`.  These prefixes exhaust the base selector.
- Once an arbitrary finite target set `Q` is revealed, the selector keeps the
  base choices in rows below `sum Q + 1` and chooses the distinguished large
  anchor in every later row.  Every later choice is larger than every target
  in `Q`, so it cannot meet any support at those targets.  Any destruction of
  a member of `Q` is therefore already caused by the single coherent finite
  prefix `damagePrefix (sum Q + 1)`.
- `finiteDestroyer_has_lowerOrderDifference` converts such finite-prefix
  destruction at a represented order-`k+1` target `q` into a concrete
  `d` in that prefix for which `q-d` is represented at order `k`.
- `finiteTranslateGrowth_or_universalFinitePrefixDifferences` is the
  exhaustive consequence for a hypothetical strongly minimal positive-order
  basis: either finite-translate matching growth occurs, or one universal
  partition and one coherent infinite base selector produce arbitrarily late
  finite-prefix destroyers with represented lower-order differences.

This is a substantive construction, but not yet the full `k ≥ 3` solution.
The infinite cross-block collision problem and the partition/certificate
quantifier swap are gone.  The remaining non-growth branch is now the
finite-prefix/difference composition problem: use the represented differences
`q-d`, with all `d` drawn from nested prefixes of one fixed infinite selector,
to construct a support avoiding the destructive prefix or force matching
growth.

# FINITE-CERTIFICATE FUSION: FIXED-Q SOLVED, QUANTIFIER BARRIER EXHIBITED (2026-07-27)

The shared-reservoir construction has now been completed for an arbitrary
fixed nonempty finite target set `Q`.

- `exists_lowerTriangularBinaryRepairSequence_avoiding_of_freshWitnesses`
  starts the infinite binary-cell recursion beyond any prescribed finite
  service set.
- `finiteTargets_have_sharedBinaryRepairReservoir` chooses one
  anchor-private successor repair for every `q ∈ Q`, puts all of those
  service cells and repairs into one protected first block, and grows one
  infinite tail of cells outside the entire finite service set.  A single
  selector—the guard core in block zero and the core in every tail
  block—avoids every service repair.  Removing each translate anchor yields
  a surviving support at the original target `q`.  Thus all targets in `Q`
  survive simultaneously on one infinite reservoir; there is no
  target-by-target Ramsey thinning and no lost label class.

This also identifies the exact limitation of that construction.  The
partition it produces depends on `Q`, whereas strong deletion returns its
finite certificate only after a partition has already been fixed.
`strongDeletion_coexists_with_targetDependentFiniteSurvival_univ_one`
formalizes a concrete counterconfiguration: at additive order one on
`A = ℕ`, strong infinite deletion holds, but every individual finite `Q`
admits a `Q`-dependent partition and selector preserving all of `Q`.
Therefore the quantifiers cannot be swapped.

The collision/fusion problem for a revealed finite certificate is solved.
The remaining global task is stricter: prebuild one universal partition,
independent of the future certificate, whose blocks contain enough guarded
service structure to run the fixed-`Q` selector after `Q` is revealed.  No
full `k ≥ 3` solution is claimed here.

# GENERAL-ORDER ATTACK: GAP-FREE BINARY REPAIRS AND CERTIFICATE MIGRATION (2026-07-27)

The bounded-successor-transversal branch has now advanced beyond the
primitive-gap restriction.

- `IsExactTupleAsymptoticBasis.eventually_not_anchorSingletonDestroyer`
  proves that for a fixed predecessor target `q`, the moving anchor `a`
  cannot remain a singleton destroyer of `q+a` arbitrarily far out.  Testing
  such a singleton against sufficiently many external basis elements would
  force strictly more order-`h` supports of the fixed `q` than its finite
  support family contains.
- `representedTranslate_destroyer_has_binaryRepairCell` minimizes a
  protected late destroyer.  The padded predecessor support forces the
  anchor into the minimal core; the singleton theorem forces a second core
  point; and minimality supplies two successor supports meeting the
  resulting binary cell at opposite endpoints.
- `boundedFullTranslateDestroyers_recurrentBinaryRepairCells` and
  `exists_lowerTriangularBinaryRepairSequence` iterate those cells while
  protecting every earlier cell and repair.  These theorems require only
  that `q` is represented.  No lower-order gap is used.
- `exists_infinite_crossDisjoint_binaryRepairs` Ramsey-thins the
  lower-triangular sequence.  Uniform support rank rules out the collision
  clique, so both repairs of every retained cell avoid every other retained
  cell.
- `LowerTriangularBinaryRepairSequence.exists_binaryCommonSurvivalPartition`
  reindexes the thinning as a genuine finite block partition.  Every
  selector leaves a successor support at every target in an infinite
  translate stream.
- `strongExactDeletion_of_counterexample` converts failure of every
  infinite successor deletion into strong successor-order deletion.
  `boundedFullTranslateDestroyers_forces_certificateMigration` then applies
  finite-block compactness: arbitrarily late minimal selector certificates
  exist, but all their targets must migrate away from the protected stream.
- `singletonTranslateGrowth_or_binaryCertificateMigration` is the resulting
  exhaustive fixed-translate alternative under a hypothetical
  counterexample.  Every represented `q` has either matching growth on
  `q+A`, or a binary common-survival partition with forced certificate
  migration.  The tail form
  `eventually_singletonTranslateGrowth_or_binaryMigration` holds for every
  sufficiently large `q`.

This is a genuine strengthening of the attack: the former terminal
gap-translate obstruction is no longer the boundary.  The remaining
mathematics is now a global fusion problem.  The local partitions and
relative matching-growth cores depend on `q`; one must combine enough of
them into a single infinite deletion whose protected target sets cover a
tail.  An arbitrary infinite Ramsey thinning is insufficient because it can
discard whole predecessor-label classes.  No full `k ≥ 3` solution is
claimed here.

# GENERAL-ORDER ATTACK: BOUNDED TRANSVERSALS DESCEND TO BOUNDED ROOTS (2026-07-27)

`Erdos881/GeneralOrderAttack.lean` now carries the most plausible
general-order contradiction route substantially past the former
moving-transversal endpoint.

The attack can first be reduced to a genuinely primitive order.

- `IsStronglyMinimalExactBasis.descend_to_exactOrder`: if `A` is already an
  exact basis at a lower order, strong minimality descends to that order;
- `IsStronglyMinimalExactBasis.exists_leastStrongOrder`: every instance
  therefore has a least positive exact order at which it is still strongly
  minimal;
- `IsStronglyMinimalExactBasis.exists_primitiveHardOrder`: in the remaining
  non-order-two case that least order is at least three, and its predecessor
  order is genuinely not a basis.  Thus the general problem reduces to
  primitive order-`h` bases with cofinal order-`h-1` gaps.
- `not_exactTupleAsymptoticBasis_iff_cofinal_emptySupport` and
  `cofinal_representedExtensions_of_lowerOrderGaps`: those gaps can be
  chosen arbitrarily late, and above any fixed `b∈A` their extensions
  `q=d+b` are nevertheless represented at order `h`.  Hence the input
  needed by the gap descent occurs cofinally, not exceptionally.

The new order-uniform incidence engine is:

- `crossAnchor_erasedCore_destroys_predecessor`: an earlier external anchor
  turns a later internal-anchor successor destroyer into an erased-core
  predecessor destroyer;
- `large_externalAnchorSet_forces_supportGrowth_anchorFork` and its rooted
  form: tests below the predecessor target retain its exact label.  Either
  the large (rooted) support family lands at the certificate target `q`
  itself, or its responsible hit is localized in `T.erase a`;
- `gapAnchor_erasedCore_destroys_predecessor`: if `q-b` is a genuine
  lower-order gap, a hit at the translate anchor is impossible, so
  `T.erase a` really does destroy the predecessor target `q+a-b`;
- `boundedFullTranslateDestroyers_descend_over_gap`: after protecting one
  support of `q=d+b`, the whole bounded recurrent obstruction descends from
  successor destroyers over `q+A` to one-order-lower destroyers over the gap
  translate `d+A`; because the translate anchor is genuinely present and
  erased, a uniform bound `m` improves to `m-1`;
- `additiveSupport_swap_external_succ`: swapping an external anchor with a
  chosen transversal hit preserves the representation order and moves the
  support to the common target `n-x`;
- `large_externalAnchorSet_forces_supportGrowth_succ`: a bounded successor
  transversal tested against sufficiently many external basis elements
  forces arbitrarily many predecessor supports at one translated target;
- `recurrentLargeSupportStars_of_boundedFullTranslateDestroyers`: the
  bounded recurrent moving branch therefore produces unbounded predecessor
  support stars at every positive order.

Large support count is then converted into actual matching structure by a
finite rank descent:

- `large_boundedHypergraph_matching_or_star`: a large rank-`d` hypergraph
  either has a large matching or a large one-vertex star;
- `additiveSupport_remove_hit_succ` and
  `additiveSupportStar_descends_card`: removing the common hit lowers the
  additive order by one without losing cardinality;
- `additiveSupportRankBound_forces_matching_below`: this process cannot pass
  order zero, whose support family has cardinality at most one;
- `additiveSupportSubfamily_has_large_rootedMatching`: retaining the removed
  summands gives a large delta system at the original order, with a root of
  cardinality strictly smaller than the order; the root is genuinely
  contained in every retained support;
- `recurrentRootedPredecessorMatchings_of_boundedMovingOnFiniteTranslates`:
  on every recurrent finite translate family, the bounded-transversal branch
  produces arbitrarily large predecessor matchings outside such a bounded
  root.

The finite-prefix synchronization has also been completed.

- `rootedMatching_disjointPrefix_or_descends`: a common root either avoids
  the current deletion prefix, or an old prefix summand lies in every
  support and can be removed without losing cardinality;
- `additiveSupportFamily_forces_prefixDisjointRootedMatching_below`: iterating
  that fork must terminate before order zero, producing a positive lower
  rank whose common root avoids the prescribed prefix;
- `recurrentPrefixDisjointRootedMatchings_of_boundedMovingOnFiniteTranslates`
  and
  `finiteCoreTranslateGrowth_or_recurrentPrefixDisjointRootedMatchings`:
  this fresh-rooted-matching output is now the exact exhaustive bad branch on
  every finite translate family.
- `cofinalPrefixDisjointRootedMatchings_of_boundedFullTranslateDestroyers`:
  the descended target can be forced arbitrarily late by requesting more
  supports than exist at all bounded lower-rank targets;
- `lift_rootedMatching_to_strictHigherOrder`: one fresh basis element,
  repeated as padding, lifts a lower-rank rooted matching back to the
  original order without changing its petals;
- `cofinalOriginalOrderRootedMatchings_of_boundedFullTranslateDestroyers`:
  consequently the moving branch has arbitrarily large, arbitrarily late
  rooted matchings at the original order, with roots disjoint from every
  prescribed finite prefix.

Thus the internal-anchor horn can no longer hide in an unstructured bounded
transversal or in repeated old-prefix overlap: all overlap is forced into
fewer than `k` fresh common summands at the original order.

The remaining synchronization problem has narrowed to the terminal
gap-translate obstruction.  Away from lower-order gaps, the distinguished
anchor fork keeps the certificate target exactly; over a gap `d`, bounded
successor transversals descend to bounded full destroyers of the *current*
order along `d+A`.  What is not yet proved is that strong order-`h` deletion
cannot coexist with this bounded gap-translate family.  That is now the
specific interface to attack; no further unlabelled rank or prefix descent
is required before it.

This is genuine progress on the open `k ≥ 3` case, not a solution claim.

# GENERAL ORDER: k = 0,1,2 SOLVED — k ≥ 3 OPEN (2026-07-27, later)

An independent audit established that the previous entry overstated
the result.  Erdős 881 as published quantifies over **every** order
`k`; this repository had settled `k = 2` only.  The headline
"ERDŐS 881 PROVED" was wrong and is retracted.

`Erdos881/GeneralOrder.lean` now supplies the layer uniform in `k`.

- `Erdos881At k` — the order-`k` statement.  The audit theorem
  `erdos881At_iff_elementary` proves, for every `k`, that this is
  *exactly* the official statement written out in plain arithmetic
  with no repository definitions.
- `IsExactTupleAsymptoticBasis.of_le` — order monotonicity, by
  iterating the existing padding lemma `.succ` (pad with a fixed
  basis element; no zero-normalization needed).
- `erdos881_at_zero` — vacuous: the empty sum is `0`, so nothing is
  an exact order-zero asymptotic basis.
- `exists_infiniteDeletion_twoBasis_of_basisOne` / `erdos881_at_one`
  — an exact order-one basis is a tail of `ℕ`; delete the
  progression `N + 4 + 2ℕ`, which has no two consecutive members, so
  one of `n = N + (n-N)` and `n = (N+1) + (n-N-1)` survives.
- `exists_infiniteDeletion_threeBasis_of_basisTwo` — the order-two
  engine with the `0 ∈ A` hypothesis discharged by translating `A`
  down by `sInf A`.
- `exists_infiniteDeletion_succBasis_of_basisTwo` — hence **every**
  `k ≥ 2`, for every `A` that is an exact order-two basis: the
  order-three deletion survives at every order `≥ 3`.

**The remaining gap**, isolated exactly by
`erdos881_general_of_hardCase`: order `k ≥ 3` with `A` *not* an
exact order-two basis.  This family is non-empty — the base-`(k+1)`
digit-`{0,1}` set is an exact order-`k` basis but misses many
targets at order two (checked numerically for `k = 3, 4`) — so the
hypothesis is a genuine open obligation, not a vacuum.  The natural
next target is the base-`(k+1)` analogue of the verified Cantor
instance, with carry repair at order `k + 1`.

Also fixed: `crossGap_finiteException_can_genuinely_stall` used
`native_decide` and so depended on a compiler-trusting axiom,
contradicting this file's own audit claim.  It is now `decide`, and
the standard-axioms claim holds repo-wide.

Note throughout: **the minimality hypothesis is never used**.  Every
settled case needs only the basis half, so what is proved is
strictly stronger than Erdős 881 asks at those orders.

Verification: full `lake build` 8303 jobs from scratch; zero
sorries; `#print axioms` on every headline theorem shows only
`propext`, `Classical.choice`, `Quot.sound`.

# THREE-ANCHOR COMPLETION — ERDŐS 881 PROVED (2026-07-27)

The formal order-two instance is complete.

`threeAnchor_forbids_terminalPrivateWounds` rules out the terminal
private-wound field forced by any hypothetical counterexample.  Choose
three fixed surviving anchors `r₀<r₁<r₂`.  Pair-covering a private target
after subtracting each anchor forces every resulting route through either
the moving guardian or the old finite prefix.

- At a self-risk, two guardian routes would identify the same risk offset
  with two distinct anchors.  Therefore two anchors route through the old
  prefix, producing an arbitrarily late edge of one bounded positive
  difference.
- At a collateral risk, any old-prefix route already produces such a
  bounded-difference edge.  Hence all three routes use the moving guardian.
  The first two bound their common co-part through the finite
  `(r₁-r₀)`-difference fiber, while `r₂` was chosen beyond that bound.

Both cases contradict finiteness of fixed positive-difference fibers.
Composing this lemma with
`counterexample_terminal_prefix_private_wound_fork`,
`counterexample_eventually_positive_sumFree`, and
`counterexample_all_positiveDifference_edges_finite` gives
`exists_infiniteDeletion_threeBasis_of_pairCovers`:

> Every zero-containing set that pair-covers all sufficiently large
> integers has an infinite subset whose deletion leaves an exact
> order-three asymptotic basis.

This is stronger than the required zero-normalized statement.
`erdos881_of_zero_normalized` then gives the final unrestricted theorem
`erdos881` for every strongly minimal exact order-two basis.

Verification:

- full `lake build Erdos881`: 8302 jobs;
- no `sorry` or `admit`;
- all new declarations depend only on `propext`, `Classical.choice`, and
  `Quot.sound`;
- `import Erdos881` exposes and kernel-checks `Erdos881.erdos881`.

The proof obligation is closed.  The remaining task is to produce a
paper-level exposition and independently audit correspondence with the
published wording.

# MOVING-PREFIX STALL + FRESH-SOURCE RESTART (2026-07-27)

The moving-prefix stall lemma is now verified in its full finite-schedule
form.

- `failure_with_finiteServiceSchedule_forces_cofinal_offScheduleStalls`
  says that after any finite lists of already served targets, failure forces
  arbitrarily late threatened targets outside every list with no surviving
  triple.
- `IsOffScheduleMinimalCommittee` and
  `failure_with_finiteServiceSchedule_forces_offSchedule_minimalCommittees`
  attach nonempty inclusion-minimal guardian committees to those stalls.
  Their recurrent/escaping, singleton/multiple, and block-separation
  consequences are all formal.
- `failed_uniformFiniteServiceSchedule_has_increment` shows that ordinary
  finite schedules always grow by one after an infinite thinning.  The
  verified parity example
  `uniformFiniteServiceSchedules_all_sizes_not_force_basis` proves that
  unbounded schedule size alone is not enough; the missing condition is
  fairness over all threatened targets.
- `HasSurvivingFiniteRiskSchedule` records the genuine label relation
  `n=b+a`, and
  `infiniteAlternativeRiskSources_scheduleIncrement` gives the bounded
  free-set increment when infinitely many distinct sources have
  source-avoiding representations.  Its hypothesis has been sharpened:
  the new target need only be absent from its own source's schedule.

The apparent fixed-source obstruction at a finite stage is now eliminated.

- `failed_riskSchedule_source_frontier` first gives an increment, unbounded
  private sources, or a recurrent fixed source.
- Under anchor supply, private streams contradict the global-counterexample
  hypothesis.
- `anchored_counterexample_freshAlternativeRiskSource` removes any finite
  set of earlier recurrent sources and restarts the theorem on the remaining
  infinite deletion.  A new cofinal target is chosen above every schedule
  value attached to those earlier sources, so it is off-schedule on the
  original deletion as well.
- `anchored_counterexample_riskSchedule_increment` iterates this restart.
  If no `k+1` schedule existed, it would construct injectively many fresh
  alternative sources; the bounded point-map free-set theorem would then
  produce exactly the forbidden `k+1` schedule.  Therefore every uniform
  finite genuine-risk schedule increments in an anchor-abundant global
  counterexample.

This supersedes the fixed/mobile collateral equations as a *finite-stage*
obstruction.  Those equations and their exact normalization split remain
verified (`fixedAlternativeRiskSource_fixed_or_mobileCollateralEquations`,
`mobileCollateralEquations_increment_or_collision_or_nonNormalizable`), but
fresh-source restart bypasses both horns before a limit is taken.

The strongest nearby fairness result is also verified:
`anchored_counterexample_serves_finite_translationSlices_on_tail`.  For
every finite `Q⊂ℕ` and every infinite source reservoir `C`, some infinite
`D⊂C` simultaneously has surviving triples for every target

`b + q,  b∈D, q∈Q`.

The proof removes the finite private-source fiber for each `q`, unions the
chosen three-point supports over the finite set `Q`, and applies the bounded
point-map free-set theorem.

`anchored_counterexample_has_prescribedFiniteRiskSchedule` packages this
when `Q⊂A`: the exact schedule at `b` is
`{b+q | q∈Q}`.  Hence
`anchored_counterexample_has_every_finite_fairWindow` proves the genuinely
fair finite statement

`∀ M, ∃ D_M infinite, every b∈D_M and q∈A∩[0,M] is served.`

`fixedDeletion_allFiniteFairWindows_implies_basis` proves the exact desired
quantifier-swapped bridge: if one fixed `D` works for every `M`, then
`A\D` is an exact asymptotic basis of order three.  The schedules need not
even be coherent between windows.

The exact first unsupported limit inference is now explicit.  Finite-slice
solvability does not by itself give one infinite deletion serving
countably many slices.  The verified counterexample
`finite_free_pointMaps_not_countably_fusible` uses

`f(q,b) = {q}` when `q<b`, and `∅` otherwise.

Inside every infinite reservoir, every finite family of these one-point
maps has an infinite common free subreservoir, but no infinite set is free
for all of them.  Thus even hereditary density of every finite window does
not justify the swap `∀M∃D_M → ∃D∀M`.  The remaining bridge must exploit
the additive equations of the repair supports; abstract compactness,
nested thinning, and unbounded finite schedule size are insufficient.

The additive composition analysis has now moved substantially past that
warning.

- `counterexample_pairSplittable_reservoir_finite` says that a counterexample
  has no infinite positive reservoir of basis points with nontrivial
  order-two supports.  The proof connects bounded point-map thinning to the
  completed zero/splitting-reservoir theorem.
- `counterexample_eventually_all_basisPoints_zeroAtomic` upgrades the former
  “extract one zero-atomic subreservoir” result to a global tail law: beyond
  one threshold, every `a∈A` has only the support `{a,0}`.
  Equivalently, `counterexample_eventually_positive_sumFree` says the whole
  positive tail of a counterexample is internally sum-free.
- `counterexample_basisDifference_edges_finite` follows immediately: for
  every positive `δ∈A`, only finitely many pairs `x,x+δ∈A` exist.  Hence
  `counterexample_popularDifference_not_mem` says every popular positive
  difference lies outside `A`.
- The one-scale theorem
  `counterexample_fixedDifference_split_filled_finite` is stronger than the
  earlier two-scale composition for intermediate membership.  If
  `δ=s+t`, `t∈A`, and `s≠δ`, then only finitely many `δ`-edges can also
  contain `x+s`.  For a popular `δ≥N₀`, applying this to both orientations
  of a covering split gives
  `counterexample_popularDifference_has_emptySplitDiamonds`: infinitely many
  edges satisfy

  `x,x+δ∈A`, but `x+s,x+t∉A`.

- `twoScale_fixedDifference_composition` and its missing-rectangle
  contrapositive remain verified, but the central branch is now impossible;
  `counterexample_popularDifference_has_twoScaleMissing` records the
  strengthened conclusion.
- Most importantly,
  `counterexample_growingDifferences_have_large_emptySplitRectangles`
  removes both the atomic and composable horns from the growing-difference
  room uniformly.  At arbitrary difference and multiplicity thresholds it
  supplies `d=u+v`, with `d∉A`, `u,v∈A` positive, and an arbitrarily large
  finite family on which

  `x,x+d∈A`, but `x+u,x+v∉A`.

Thus the surviving difference geometry is exactly the internally sum-free,
parity-like geometry (realized by `{0}∪ODDS`), not an unanalysed disjunction.
The first unsupported next inference is to turn these arbitrarily large
empty split rectangles into one deletion serving all mixed risks.  Pair
covering alone cannot rule out the rectangles; the next composition must use
their order-three repair supports together with the existing external
four-clique/block-certificate obstruction.

Erdős 881 is not yet solved.

# MOVING-PREFIX TERMINAL REDUCTION (2026-07-26)

The moving-prefix stall program now has a complete verified finite-to-infinite
interface (standard axioms, zero sorries).

- `unsafe_extension_self_risk_or_collateral_private` corrects the first
  tempting inference.  Failure of `B ∪ {b}` need not occur at a new target
  `b+a`; it can occur at an old risk `d+a`, `d∈B`, whose surviving
  representations were privately guarded by `b`.
- `moving_prefix_stalls_distinct_or_recurrent` proves the exact fiber
  alternative.  From
  `(card B+1)(KR) < card C`, moving stalls yield either more than `R`
  distinct wealthy offsets, more than `K` candidates with one fixed
  self-offset `n_b-b`, or more than `K` candidates with one fixed old charge
  `n_b-w`, `w∈B`.
- `greedy_batch_complete_structural_fork` consumes both the self-risk and
  collateral-private branches.  The latter is not discarded:
  `IsPrivateTriple.guardian_mem_le_and_complement_split` writes
  `n-b=u+v` with `u,v∈A\B`, and the same exact-fiber argument applies.
- `exists_large_ordered_candidate_batch_with_low_supply` removes the last
  candidate-supply hypothesis.  A reserved block of `(card B+1)L` basis
  elements, followed by a sufficiently large separated candidate block,
  supplies the required low mass uniformly.
- `finite_prefix_extension_or_complete_structure` is the resulting
  unconditional finite theorem: a safe extension exists, or there are many
  distinct wealthy offsets, a basis-translate affine wall, a
  survivor-co-sum affine wall, or a fixed-prefix stall.

The limit step is now also verified.  In
`infinite_deletion_of_safe_prefix_extensions`, positive extensions above the
whole prefix produce a strictly increasing sequence `b_i`.  For a fixed
target `n`, choose a stage `k` with `b_k>n`.  Every entry of a triple summing
to `n` is at most `n`, so no later deletion can damage the stage-`k`
representation.  Hence safe finite extensions glue to an infinite deletion
whose complement is an exact asymptotic basis of order three.

Taking the contrapositive gives a single zero-preserving terminal prefix
`B`.  At that same `B`, every requested scale `R,L` has a structural
obstruction.  The fixed-stall horn is actually impossible:
`safe_zero_surviving_prefix_has_no_fixed_stall` uses a covering pair
`x+y=m`; if neither endpoint is in `B`, pad by `0`, while if an endpoint is
in `B`, the safe-prefix invariant serves the risk.  Thus
`counterexample_terminal_prefix_has_mobile_structure` has only three horns.
Monotonicity in `R,L` then gives
`counterexample_terminal_prefix_cofinal_trichotomy`: at one fixed terminal
prefix, either

1. `ManyWealthyOffsets A R L` holds for every `R,L`;
2. `BasisAffineWall A B L` holds for every `L`; or
3. `SurvivorCosumAffineWall A B L` holds for every `L`.

The sharpest current object is
`counterexample_terminal_prefix_private_wound_fork`.  For every positive
`b∈A` above the terminal prefix there is a cofinal target `n≥b` such that
`b` is private over `A\B`.  Exactly one of the following proof obligations
remains:

- `b` is already an absolute private guardian in `A`; or
- a triple avoiding `b` exists in `A`, but it must route through the fixed
  finite prefix `B` (`HasPrefixRepairTriple A B b n`).

The finite routing loss is also closed:
`counterexample_cofinal_absolute_or_fixed_prefix_repairs` applies a cofinal
finite pigeonhole argument and leaves exactly two global branches:

- absolute private wounds occur on arbitrarily large guardians `b`; or
- one fixed `w∈B` lies in repair triples for arbitrarily large guardians.

The absolute branch is now sharpened by
`no_cofinal_big_absolute_private_guardians`.  Big guardians (`n<2b`) would
either have cofinal co-offsets `q=n-b≥N₀`, contradicting
`no_big_guardian_stacking`, or eventually bounded co-offsets.  In both
cases finite pigeonhole fixes one `q`; two separated guardians at that
offset contradict the private-desert law.  Hence
`counterexample_nonbig_absolute_or_fixed_prefix_repairs` is the final
two-way interface:

- cofinally many absolute private wounds satisfy `2b≤n`; or
- cofinally many prefix repairs pass through one fixed `w∈B`.

Finally, `strict_small_absolute_private_structure` splits the first horn.
If `2b<n` and `q=n-b`, then `q∈A`, `b<q`, `{b}` is a singleton pair hub
at `b`, and `A∩(q,n-N₀]=∅`.  Thus
`counterexample_double_or_strictSmall_or_fixedPrefixRepairs` leaves three
named cofinal models at the same terminal prefix:

1. private doubles `n=2b`;
2. strict-small zero-atomic guardians with long post-`q` deserts;
3. repairs through one fixed old `w`.

At the endpoints, `absolute_private_double_forces_unique_pair` proves that
the double branch has the unique order-two representation `2b=b+b`, while
`repairThrough_gives_shifted_pair` rewrites the fixed-channel branch as
`n=w+u+v` with `u,v≠b`.  These are respectively the pointwise central
geometry and the exact shifted-pair composition interface.

The fixed-channel interface has now been pushed through an infinite
collision-free thinning.  The new theorem
`cofinal_fixedRepairChannel_has_collisionFree_selector` produces an
infinite `C⊆A`, with `0,w∉C`, and one wound `τ(b)` for each `b∈C` such that
`τ(b)=w+u_b+v_b` with `u_b,v_b∈A\C`.  The free-set theorem for bounded
point maps supplies the thinning: each selected repair pair has at most
two entries and excludes its own guardian.

This also isolates the first invalid inference in the hoped-for
composition.  One repaired wound per `b` does not serve every threatened
target in `C+A`.  `deletion_of_selectedRepairs_and_offSelectorRisks` gives
the sufficient bridge at the original threshold `N₀`, while
`selectedRepairs_basis_iff_eventual_offSelectorRisks` proves the exact
statement: the deletion is an exact order-three asymptotic basis if and
only if every sufficiently late off-selector risk is served.  Conversely,
`counterexample_fixedRepairChannel_has_offSelectorStalls` proves that a
counterexample forces arbitrarily late off-selector targets in `C+A`,
different from every `τ(b)`, with no triple avoiding `C`.

Those residual targets now have finite structure.
`failure_with_selectedRepairs_forces_offSelector_minimalCommittees`
extracts a nonempty minimal representation hub
`H⊆C∩[0,n]` at every arbitrarily late off-selector stall.
`selectedRepairs_offSelector_window_core` then fixes any window `[0,W]`
and stabilizes one exact low committee `S`: cofinally many such minimal
hubs satisfy `H∩[0,W]=S`, while every remaining guardian lies above `W`.
Minimality supplies a witness for each `h∈H` avoiding `H\{h}`.  It does
not imply that `h` is an absolute private guardian, because the witness
may still use deleted points in `C\H`; that is the first exact remaining
inference which is not justified.

The source of the selected wounds is now stable as well.
`cofinal_fixedRepairChannel_self_or_fixedCollateral` gives either cofinally
many genuine self-risks `b+a`, or one fixed `d∈B` supplies cofinally many
collateral risks.  In the latter case
`collateralRepairWound_fixedShift_identity` gives the exact fixed-shift
equation

`d+a=w+u+v`,

equivalently `(d-w)+a=u+v` when `w≤d`, or
`a=(w-d)+u+v` when `d≤w`.

Thus the moving-prefix and repeated-offset losses are closed, and the
selected-repair collision problem is closed.  The remaining mathematics
is to defeat the private-double/strict-small central-atomic models or
prove that the forced cofinal off-selector stall stream cannot coexist
with the fixed-shift self/collateral geometry.  Erdős 881 is not yet
solved.

# NORMALIZATION + DIFFERENCE-COMPOSITION BRIDGES (2026-07-26)

New verified interfaces, all standard axioms and zero sorries:

- `erdos881_of_zero_normalized` (`Normalization.lean`): the standing
  `0 ∈ A` convention is now removed at the theorem level.  Shifting by
  `min A` preserves exact tuple bases, infinite deletions, and strong
  minimality; any zero-normalized order-two solution transports to the
  unrestricted statement.
- `many_difference_pairs_avoid_finset` and
  `difference_pair_family_many_fresh`: more than `2|F|` equal-difference
  pairs leave a pair avoiding any finite injury set `F`, quantitatively with
  arbitrarily many fresh pairs.
- `stall_family_mass_amplifier`: stalls against one fixed finite prefix
  pigeonhole to one deleted offset and produce a distinct target family
  with certified lower and upper symmetry-mass bounds.
- `moving_prefix_stalls_core_or_mobile`: the greedy construction's actual
  prefixes `B ∪ {b}` may move with the candidate.  More than
  `(|B|+1)K` stalled candidates force either `K+1` self-charged wealthy
  offsets `n_b-b`, or `K+1` wealthy offsets charged to one fixed old
  `w ∈ B`.
- `stall_mass_quantitative_of_single_inequality`: the unknown fiber size no
  longer requires a universally quantified numerical hypothesis.  With
  `s=|S|`, `k=|B|`, and `α=|A∩[0,X]|`, it is enough to check once that
  `α(sα+s²D) < (⌈s/k⌉L)²`.
- `stall_family_forces_popular_difference` packages the numerical payoff;
  `stall_mass_certificates_fixed_offset_or_growing` feeds certificates at
  every multiplicity directly into the existing fixed-offset/growing fork.
- `fixed_difference_deletion_of_shiftedPairSurvival`: the exact composition
  identity is `b+a = x+(a+δ)` for a deleted upper endpoint `b=x+δ`.
  Consequently `fixed_difference_forces_shifted_slice_obstruction` says a
  counterexample with cofinal fixed `δ`-pairs must destroy an order-two
  representation somewhere on the translated slice `A+δ`.
- `growing_differences_composable_or_missing_rectangles`: after finite
  avoidance, every growing popular difference is either itself a basis
  element, has a fresh edge with an intermediate basis point, or supplies
  arbitrarily many filled endpoint pairs whose two intermediate vertices
  are both absent.

The remaining mathematical pressure is now localized.  On the stall side,
one must manufacture the quantitative certificate family from the adaptive
extension game.  On the fixed side, analyze the forced shifted-slice
destroyers with the existing fixed-translate repair machinery.  On the
growing side, eliminate or exploit the atomic and missing-rectangle horns.

# THE POPULAR-DIFFERENCE MEASUREMENT (2026-07-26)

MEASURED (scripts/probe_popular_diff.py): are the differences
produced by the STALL → WEALTH → SYMMETRY → TRANSLATION chain
themselves basis elements?  The tempting route was to split
b = d + (b−d) and feed `deletion_criterion`.

ANSWER: NO, and structurally so.  Popular differences in A:
R1 0%, thin 0%, odds 0%, spite 2%, DD 11%, random 31%, TD 37%,
Cantor 57%.  Chain-produced differences (from pairs of the
wealthiest targets): 0/15 in R1, thin, spite, odds; 4–7/15 in
the looser worlds.  The odds world shows the obstruction is not
a lab artifact: A = ODDS, every difference of two odds is EVEN,
so d ∈ A is impossible in principle.  The two-part split route
is DEAD as a general mechanism.

BUT the same measurement found the real route: popular
differences SPLIT into two basis elements 95–100% of the time
(odds 100%, spite 100%, thin 98%, R1 97%, TD 96%, DD 95%,
Cantor 85%).  And that is not luck — it is forced:

`large_mem_or_splits` (verified): for d ≥ N₀, either d ∈ A or
d = u + v with u, v ∈ A both positive.  Covering leaves no
third option.

`difference_reaches_element` (verified): hence a basis pair
(y, y+d) makes y + d reachable from STRICTLY SMALLER basis
elements in at most three parts — y + d + 0, or y + u + v.
Strictly smaller parts are exactly what the greedy needs, since
every later deletion is larger.

So the chain feeds the SUM-FREE / master criterion route (serve
each deleted element by a triple), not the two-part split
criterion.  Corrected and verified.

# THE POPULAR DIFFERENCE LAW — TWENTY-NINTH SUMMIT (2026-07-26)

The chain from the join, completed and verified:

  STALL → WEALTH → SYMMETRY → TRANSLATION → FIXED DIFFERENCE.

- `endgame_join` / `stall_forces_wealth`: a stall of the
  constructive greedy at scale n forces a target of pair wealth
  ≳ α/k at a deleted-element offset.
- `wealthy_set_symm`: a wealthy target's representation set is
  reflection-invariant (x ↦ M − x) — wealth IS symmetry.
- `two_symmetries_translate`: reflecting about M₁/2 then M₂/2
  is translation by d = M₂ − M₁, so each element shared by two
  wealthy symmetry sets is a basis pair at difference d.
- `sum_pairwise_inter_lower`: Cauchy–Schwarz double count —
  many large sets in one universe must overlap.
- `endgame_popular_difference` (the summit): with
  α = |A ∩ [0,X]| and D a uniform bound on how often any
  genuine difference `1 ≤ d ≤ X` is realised below X,
    (Σ_{M∈T} |S M|)² ≤ α · (Σ_{M∈T} |S M| + |T|²·D).
  `endgame_popular_positive_difference` packages the usable
  contrapositive: enough wealth mass FORCES some positive
  `d ≤ X` to be realised more than D times.  The uninformative
  diagonal `d = 0` is explicitly excluded.

CONSEQUENCE: a counterexample that blocks the construction pays
in R1 structure.  The stall's wealth is not merely a number —
it is a symmetry, and symmetries compose into translations.
The fixed-difference room (`endgame_rigidity_teams`,
`translation_room_teams`, δ-coherent teams) is where the
payment lands, and it is the campaign's most developed room.

OPEN LINK: the difference produced is per-scale (d = M₂ − M₁
depends on the wealthy pair), while the R1 machinery consumes
one difference realised cofinally.  Closing that gap —
pigeonholing d across scales, or generalising the team
machinery to per-scale differences — is the next step.

# THE JOIN — TWENTY-EIGHTH SUMMIT (2026-07-26)

`endgame_join` / `stall_forces_wealth` (Endgame.lean, standard
axioms): the campaign's two halves welded together.

The constructive turn reduces Erdos 881 to building an infinite
B with B + A served (`endgame_master_criterion`).  The greedy
that builds it can fail only by STALLING at a target n that
resists every triple from A ∖ B.  This theorem prices the
stall:

    |A ∖ B ∩ [0, n−N₀]|  ≤  |B| · r₂(n − w)   for some w ∈ B.

With covering's √-growth (|A ∩ [0,X]| ≳ √X), a stall at scale n
against a size-k deletion manufactures a target of pair wealth
≳ √n / k — within a constant factor of the maximum possible,
i.e. served by a positive fraction of the whole basis below it,
sitting exactly one deleted element away from n.

CONSEQUENCE: every stall is an event in the wealth stream, and
the wealth stream is the object the entire contradiction-mining
campaign constrains — pinned to nested 2-adic addresses,
capped at 2L on streets, taxed against basis mass by the spike
census, forced to oscillate between a finite ceiling and
infinity.  The construction consumes every world where the
stall does not occur; the twenty-seven prior summits constrain
exactly the configuration where it does.

Proof: at a stalled n, each surviving z ≤ n−N₀ has n−z covered
by B (else a triple), so some w ∈ B has n−z−w ∈ A; pigeonhole
over B (biUnion + max fiber) and inject the fiber into the
representation set of n−w.

# THE MASTER CRITERION — TWENTY-SEVENTH SUMMIT (2026-07-26)

`endgame_master_criterion` (Endgame.lean, standard axioms):
a deletion B survives at order 3 as soon as every target in
B + A is served by a surviving triple.  Targets OUTSIDE B + A
keep their covering pair untouched (pad with 0), so the entire
burden is a thin union of translates — and B is ours to choose.

Erdos 881 restated constructively:
  CHOOSE A SPARSE INFINITE B ⊆ A KEEPING B + A SERVED.

Two verified local discharges:
- `deletion_criterion` — split each deleted element in two
  (splittable regime; includes the Cantor instance);
- `deletion_criterion_sumfree` + `sumfree_triple` — reach each
  deleted basis element by a POSITIVE triple (internally
  sum-free regime; includes {0} ∪ ODDS).  Sum-freeness supplies
  its own triples: a − x ∉ A for x ∈ A⁺, so a − x is a positive
  pair sum and a = x + u + v.  (`sumfree_triple` is
  CHOICE-FREE: axioms propext, Quot.sound only.)

LAB: greedy under the master criterion builds a surviving
deletion in 20/20 worlds across TEN families — R1, doored
desert, total desert, thin, low, parity-starved, random,
spite-loaded, odds, Cantor.  Every adversarial family the
campaign has ever built now yields to the construction.

REMAINING: prove the greedy never stalls in general, i.e. that
some sparse infinite B keeps B + A served.  That is the whole
of Erdos 881 (k = 2) now — one sentence, constructive, with
both discharge routes verified.

# THE CONSTRUCTIVE TURN — TWENTY-SIXTH SUMMIT (2026-07-26)

THE PIVOT: stop mining contradictions from a hypothetical
enemy; BUILD the deletion.

`endgame_construction` (Endgame.lean, standard axioms): given a
strictly increasing sequence of positive basis elements whose
(i) members each split as u+v with u,v off the sequence, and
(ii) pairwise sums are each served by a triple off the
sequence, the range is an infinite B ⊆ A with A∖B an exact
asymptotic basis of order 3.  Engine: `deletion_criterion` —
a covered target's guaranteed pair n = x+y is padded with 0 if
both parts survive, else the deleted part is replaced by its
own split.  Four lines of mathematics; no minimality, no
anchor, no failure interface.

LAB (scripts/probe_construction.py): the greedy construction
(lacunary + splittable + never delete both ends of a unique
pair + doubles served) produces a surviving deletion in 30/33
adversarial worlds across 11 families, INCLUDING the verified
Cantor instance.

THE ONE RESISTING FAMILY, and what it taught: the "thin"
worlds are INTERNALLY SUM-FREE — every element's only pair
representation is the trivial 0 + b, so nothing can ever be
split.  Two lab-driven corrections came out of this: splits
must be non-degenerate (0 ∈ A makes b = 0+b useless), and the
double 2b needs SERVICE, not multiplicity (Cantor's doubles are
uniquely represented yet served by carry triples).

STRUCTURAL DISCOVERY: internally sum-free bases are
AUTOMATICALLY ℵ₀-minimal — deleting any infinite B kills every
deleted element as a target (its only rep was 0+b).  So the
problem's true difficulty lives exactly in the internally
sum-free regime; the splittable regime is constructively
solved.  The next phase: serve the deleted elements themselves
by positive triples (b ∈ (A∖B)+(A∖B)+(A∖B)) and re-derive the
target service there.

# THE PROFILE VERDICT: COUNTING IS EXHAUSTED, POSITION IS THE FRONTIER (2026-07-26, verdict)

Numerical feasibility (scripts/probe_profile_region.py) of the
four verified books (sqrt-growth, two-scale funding, census,
oscillation): FEASIBLE at every density fraction up to ~0.9;
only full density dies (census).  The counting constraint
system is consistent — no cheap cardinal contradiction exists
in the current books.

DIRECTIONAL CONCLUSION for the campaign: the labs' universal
survival (347/347) is driven by POSITION, not cardinality —
deletions dodge because the enemy cannot control WHERE its
spikes, basis elements, and poor streams sit relative to each
other, under the verified positional laws (residue chaining,
2-adic address pinning, canonical cores, doors, the
disjoint-matching dodge).  The remaining mathematics of Erdos
881 k=2 is the POSITIONAL composition at the ET wall: proving
that no arrangement — not just no counting profile — sustains
total service breakdown against every deletion.  Counting
refinements are exhausted as a route; the position-based
assets are the inheritance for the next phase.

Twenty-five summits, ~105 theorems today, the complete two-book
system, and an honest map of exactly where the difficulty
lives.

# THE SPIKE CENSUS — TWENTY-FIFTH SUMMIT (2026-07-26, final)

`endgame_spike_census` (Endgame.lean, standard axioms): in
every counterexample, for every infinite deletion B, cofinally
many scales satisfy

  alpha(n) + W(n) <= n + 1 + 2|B cap [0,n]|

— at breakdown targets the surviving basis and the REFLECTED
SPIKES are disjoint subsets of [0,n] (each would serve the
other), so they pack (`breakdown_pigeonhole`).

THE TWO BOOKS: the closed two-scale law demands W*alpha^2-scale
spike mass to fund alpha^4; the census makes every spike
displace basis mass at failing scales.  The profile region now
has both its funding constraint and its coupling constraint,
machine-checked.  The remaining calculation: whether any
profile (alpha_k, W_k) survives both books plus sqrt-growth
plus oscillation across all dyadic towers — the sharpest and
final quantitative form of Erdos 881 k=2 this campaign has
produced.

Twenty-five summits.

# THE CASCADE LAW (2026-07-26, final)

`cascade_law` (pure counting, standard axioms): at every scale
n and threshold C,

  alpha^4 <= (2n+1) * ((n+1)C^2 + W_C*alpha^2 + upperSum)

— the covering demand funded by exactly three sources: poor
noise, in-window spikes (each also a service wall via
`served_targets_never_fail`), or upper-half energy (the next
scale's demand).  Built on the Mathlib bridge
(`window_energy_le_addEnergy`, `mathlib_energy_floor`,
`energy_upper_half_floor`).

The enemy's budget routing at every scale forever, as one
inequality.  The multiscale analysis of this law — how upper-
half transfers compound across dyadic scales against the
spike/wall duality — is the energy-cascade program, the
freshest road at the ET wall.

# SUMSET COMPLETENESS: LAB-TRUE, THE FINAL REDUCTION (2026-07-26)

LAB (scripts/probe_completeness.py): W_T + A is TAIL-COMPLETE
in every candidate world at every threshold (T = 8/16/32) —
zero uncovered integers, minimum server counts 2-152, median
~400.  Every integer has multiple wealthy servers.

THE FINAL REDUCTION (via `failing_avoids_wealthy_translates`):
if in every counterexample world, for some threshold family,
the wealthy sumset W_C(n) + (A minus D) contains a tail with
more than |D|-many servers per target, then no cofinal failing
stream exists and hfail dies.  Erdos 881 k=2 is REDUCED to a
sumset-completeness statement about the oscillation theorem's
own wealthy stream — a single, sharply-posed additive-
combinatorics conjecture, lab-true in all 6 campaigns,
supported by every verified law of the session.

The enemy's only remaining hope: worlds where the wealthy
stream is so sparse and so misaligned with A that its sumset
misses cofinally many integers — while surviving oscillation,
rigidity, the density law, the dodge, forced mixing, and the
width law simultaneously.  The corridor is one conjecture wide.

# THE MASTER LAW — TWENTY-THIRD SUMMIT, SESSION CAPSTONE (2026-07-26)

`endgame_master_law` (Endgame.lean, standard axioms): every
counterexample to Erdos 881 k=2 simultaneously (I) OSCILLATES,
(II) runs one of three RIGIDITY geometries, (III) pays the
DENSITY LAW at cofinal failing targets of every infinite
deletion.  Hypotheses: 0 in A, covering, hfail — nothing else.
The unconditional layer in one exported statement.

Twenty-three summits.  Session totals for 2026-07-26: ~70 new
verified theorems, 9 new summits, 1 complete branch defeat,
6 lab campaigns (347/347 survivals), the two-regime squeeze,
and the master law.  All standard axioms, zero sorries,
~716 commits.

# THE DENSITY LAW — TWENTY-SECOND SUMMIT (2026-07-26, close)

`endgame_density_law` (Endgame.lean, standard axioms; from the
tuple-failure alone): at every failing target,
alpha - DF <= P  and  alpha2^2 + P*(alpha - C) <= (n+1)*alpha.
Reflected embedding pushes the poor population up; the energy
Sigma r2 >= alpha2^2 (low-half pairs, sigma-counting) against
the poor/rich partition pushes the total down.

FIRST CONSEQUENCE: dense bases can NEVER fail — a set
containing [0,n] violates the inequality outright.  The fat
end of the two-regime squeeze now has its quantitative wall:
counterexamples' density profiles are bound at every failing
target of every deletion, forever.

Twenty-two summits.  The session's closing stack: fan poverty
-> reflected embedding -> THE DENSITY LAW; dodge + rigidity
trichotomy; oscillation layer; forced mixing.  All standard
axioms, zero sorries, ~715 commits.

# WEALTH DENSITY + THE TWO-REGIME SQUEEZE (2026-07-26, close)

Measurement (probe_wealth_density.py): wealthy targets (r2 > 8)
are 60-78% per dyadic window in R1/DD candidate worlds — but
thin/greedy worlds run near-zero wealthy density, so high
wealth density is NOT forced; the enemy plays thin against
composition (1).

THE TWO-REGIME SQUEEZE (final map of the campaign):
- FAT regime (wealth dense): `endgame_fan_poverty` is
  devastating — each failing target needs a sqrt(n)-sized fan
  avoiding a majority-dense wealthy set: reflected copies of A
  must embed in the thin poor set, cofinally, for every sparse
  deletion.  The kill here is a density/embedding counting
  argument.
- THIN regime (r2 small everywhere): matchings are tiny; the
  vertex-cover game rules — the disjoint-matching dodge kills
  spread streams, the rigidity trichotomy kills shared-low
  streams, and the residue is local sharing + unique-pair
  streams — Erdos-Turan-adjacent territory where even
  CONSTRUCTING candidate worlds is beyond current mathematics.

Every counterexample must run one of these regimes (or
oscillate between them — the oscillation theorem forces at
least the poor side to persist).  Twenty-one summits, the
dodge, fan poverty, and the full trichotomy suite stand
verified around this map.

# THE FAN POVERTY LAW — TWENTY-FIRST SUMMIT (2026-07-26, night)

`endgame_fan_poverty` (Endgame.lean, standard axioms; from the
tuple-failure alone — no 0, no covering, no anchor): a target
failing at order 3 against D has its ENTIRE non-deleted
translate fan uniformly poor — every x in A∖D below n gives
r2(n-x) <= 2|D cap [0,n]| + 2.  Via `wealthy_pair_survives`
(pair-form survival, hypothesis-free counting).

CONSEQUENCES NOW IN REACH:
- One failing target = a blanket poverty requirement across
  ~|A cap [0,n]| >= sqrt(n) translates at once (covering
  growth), all forced near-Sidon when D is log-sparse.
- The failing stream must avoid w + (A minus D) for every
  sufficiently wealthy w: failure lives OFF the sumset of the
  wealth stream with nearly all of A.
- Composition targets: (a) drain-pinned wealthy targets w:
  failing n avoid w + (A∖D) — with w in pinned cylinders and
  A's forced 2-adic width, these sumsets are enormous; (b) the
  poor stream's density: fans of failing targets must embed in
  the poor set — the poor set must be sqrt-dense reflected-A-
  rich; collide with oscillation bookkeeping.

Twenty-one summits.  The order-3 quantifier has finally been
made to PAY: fan poverty is strictly stronger than everything
the pair-level exclusion suite provided.

# THREE-ROOMS LAB + THE ERDOS-TURAN WALL (2026-07-26, night)

LAB (scripts/probe_three_rooms.py): 27/27 deletions survive in
adversarial R1 / doored-desert / total-desert worlds.  Decisive
mechanism data: survival is ~always PAIR+0 (order-2 redundancy
alone repairs the deletion); genuine triples are a <= 4%
correction.  The deletions never even reach the regime where
order 3's extra summand is needed.

HONEST LAB LIMIT: the 'total desert' worlds are not faithful —
greedy balanced-pair construction creates massive incidental
r2.  A faithful desert needs BOUNDED r2 on a covering set,
i.e. near-Erdos-Turan-violating structure — whose existence is
the famous open problem.  The lab cannot build what nobody can.

STRATEGIC READING: for the enemy's deletions to bite at all,
it needs bounded-r2 behavior on massive target families (the
lab can't reach it; Erdos-Turan says it may be impossible);
and `poor_stream_of_hfail` proves hfail FORCES bounded-r2 on a
cofinal stream — the enemy is REQUIRED to live at the edge of
the Erdos-Turan wall.  Erdos 881 k=2's difficulty is thus
precisely calibrated: its counterexamples inhabit the same
regime whose nonexistence is the Erdos-Turan conjecture's
content, but on cofinal streams rather than all targets — the
oscillation theorem is exactly the formal wedge between the
two.  A proof of 881 need not resolve Erdos-Turan: it needs
only that BOUNDED-r2 STREAMS INSIDE AN UNBOUNDED-r2 COVERING
WORLD cannot absorb every sparse deletion's failure demand —
the width-band question again, now placed in the classical
landscape.

# RIGIDITY WITH TEAMS — TWENTIETH SUMMIT (2026-07-26, night)

`endgame_rigidity_teams` (Endgame.lean, standard axioms): in
anchored worlds the terminal classification sharpens — every
counterexample runs (1) TRANSLATION-COHERENT TEAMS (fixed
d >= 1, cofinal minimal committees of size >= 2, every member
delta-paired h, h+d in A — each team shifts by d into fresh
representations: full R1 structure), or (2) a DOORED DESERT,
or (3) a TOTAL DESERT.

Tools: `fixed_difference_families` (supply -> families of every
size) welding the rigidity trichotomy's horn 1 to
`translation_room_teams`.  Twenty summits.

THE GEOGRAPHY IS NOW FULLY WELDED: oscillation layer
(unconditional) -> three terminal rooms, horn 1 carrying the
translation room's complete team structure.  The kills that
remain: delta-coherent teams (R1), the doored desert (door
kills + moat), the total desert (head-service bookkeeping).

# THE RIGIDITY TRICHOTOMY — NINETEENTH SUMMIT (2026-07-26, night)

`endgame_rigidity_trichotomy` (Endgame.lean, standard axioms,
UNCONDITIONAL): every counterexample runs one of three explicit
geometries — (1) FIXED DIFFERENCE (some d >= 1 with a, a+d in A
beyond every bound: the translation room's hR1 supply,
translation_room_teams' input, unlocked from the bare
interface); (2) DOORED DESERT (one u serving a cofinal poor
stream as its only small low part up to a window); (3) TOTAL
DESERT (no small low parts at any scale).

R1 / door / R4 — the campaign's oldest room names — now forced
UNCONDITIONALLY by the oscillation layer, poverty riding every
horn.  The conditional rooms (built through the anchor
trichotomy and the final fork) and the unconditional oscillation
layer now agree on the terminal geography from two independent
derivations.  Nineteen summits.

Next composition: horn (1) + translation_room_teams (needs
anchor) — or the unconditional δ-machinery; horn (2) door kills;
horn (3) desert vs head-service bookkeeping.

# THE DRIFT FORK — EIGHTEENTH SUMMIT (2026-07-26, night)

`endgame_drift_fork` (Endgame.lean, standard axioms,
UNCONDITIONAL): every counterexample either owns a UNIVERSAL
LOW PART (one fixed u inside the complete canonical hubs of
cofinally many poor targets — the door at a known member) or
runs TOTAL DRIFT (beyond every window, cofinal poor targets
with every low part above the window — complete bounded hubs
marching in formation).

The unconditional layer (oscillation -> canonical hubs ->
stable cores -> drift fork) now terminates in the SAME two
geometries the anchored rooms did — door or street — but with
NO anchor, NO trichotomy hypothesis, NO room assumption: the
enemy's final refuge shapes are forced from the bare failure
interface.  Eighteen summits.

The convergence of the conditional (rooms) and unconditional
(oscillation) analyses onto door/street geometry from
independent directions is the strongest structural signal of
the campaign: Erdos 881's counterexamples, if any exist, are
door-or-street objects, full stop.

# THE CANONICAL CORE — SEVENTEENTH SUMMIT (2026-07-26, night)

`endgame_canonical_core` (Endgame.lean, standard axioms,
UNCONDITIONAL): at every window W, a persistent core S of
low-part material recurs inside the COMPLETE canonical hubs
(card <= L) of cofinally many poor targets, every non-core
member beyond the window.

Tools: `pair_hub_window_split` — obtained FREE from the
rep-hub splitter by the vacuous-world trick (instantiate its
world at the empty set: rep-hubness trivializes, pair-hubness
rides the side-predicate slot).  Composed with
`poor_stream_canonical_hubs` (completeness from oscillation).

The poor stream's low material = stable finite core + marching
tails, at every scale.  Core members are universal low parts
(u in A with n - u in A for cofinally many poor n).

THE DRIFT FORK now has unconditional supply: either cores stay
nonempty at all windows (a FIXED low element serves cofinally
many poor targets through complete hubs => translate structure
at a known member), or some window has empty core (all low
material of cofinal poor targets marches wholly beyond every
bound => pure drift, the completeness makes this a strong
translation law on the poor stream).  Seventeen summits.

# THE OSCILLATION THEOREM — SIXTEENTH SUMMIT (2026-07-26, night)

`endgame_oscillation` (Endgame.lean, standard axioms): every
counterexample's r2 oscillates FOREVER between a fixed finite
ceiling and infinity.

New half: `poor_stream_of_hfail` — liminf r2 < INFINITY,
UNCONDITIONALLY (h0 + covering + hfail; no anchor, no subsets,
no rooms).  THE DIAGONAL: if r2 -> infinity, space a deletion's
i-th element beyond the threshold where r2 > 2i + 4; its
failing targets would need r2 <= 2|D cap [0,n]| + 2 = 2J + 2
with n beyond the (2J+2)-threshold — impossible; so D survives,
contradiction.  Junk test: fat sets FAIL the conclusion
(their r2 -> infinity): genuine counting content.

Old half: `r2_unbounded_of_hfail` (limsup = infinity).

CONSEQUENCE: the enemy's wealth function is pinned to a
permanent boom-and-bust cycle.  The bounded-poor stream that
the width band's bounded horn creates per-subset is now known
to exist GLOBALLY, and the whole two-streams geometry
(poverty chained + wealth pinned) is unconditional.

Sixteen summits.
# THE WIDTH BAND — FIFTEENTH SUMMIT (2026-07-26)

`endgame_width_band` (Endgame.lean, standard axioms): the
residue of Erdos 881 as ONE verified fork.  In anchored worlds,
every infinite positive subset B runs exactly one regime:

BOUNDED BAND: some width C works cofinally, and every such
committee target is pointwise pair-poor (r2 <= 2C) — a
hereditary poor street, segregated from the pinned unbounded
wealth stream forever; or

ESCALATION: beyond every width, cofinal targets carry wider
minimal committees from B — privately witnessed members,
sub-committees certified unable to pair-hub their member's
translates — unbounded freeness-certificate towers.

Fifteen summits now stand.  What remains: neither regime can
actually be sustained forever — the bounded horn against
wealth/covering geometry, the escalating horn against the rank
room fed by its own freeness certificates.

# HEREDITARY TEAMS OR EXOTIC GEOMETRY — FOURTEENTH SUMMIT (2026-07-26)

`endgame_hereditary_teams` (Endgame.lean, standard axioms,
ANCHOR-FREE): every counterexample either
(I) owes hereditary teams to its entire subset lattice — every
infinite positive B defends with cofinal minimal committees of
size >= 2 drawn from B, each member privately witnessed
(`committee_size_floor` through `streamSurvives_of_anchor` on
the trichotomy's anchored horn) — or
(II) runs a member router g0 ({c, g0} pair-hubs every
noncentral double), or
(III) is central-pinned (central-only doubles, singleton
double-hubs, no order-2-surviving deletion, AP3-free off
router).

The anchored world — the main room — now has its defense
obligations quantified hereditarily with a proven team floor.
Rooms II/III are the surviving exotic geometries with their own
recorded structure (routed collapse, Salem-Spencer).

# THE UNIVERSAL COMMITTEE LAW — THIRTEENTH SUMMIT (2026-07-26)

`endgame_universal_committee` (Endgame.lean; hypotheses: hfail
ALONE — no 0, no covering): every infinite B subseteq A owns a
cofinal stream of targets carrying MINIMAL order-3 guardian
committees drawn from B itself, each member with a private
witness (representation meeting the committee only there).
Composition: failing prefix is a rep hub + `exists_minimal_hub`
+ `minimal_hub_necessity`.

STRUCTURAL TRANSFER: the guardian/team/rigidity machinery
(GuardianRigidity, TeamGuardianRigidity, team-card escalation,
singleton-stream kill...) was built for committees in A.  It now
applies HEREDITARILY — inside every infinite subset.  In
particular: committee members' private witnesses, team stacking
bounds, and escalation ladders all constrain every B the
deleter proposes.  Next: replay the singleton-stream and
team-coverage kills INSIDE a chosen B (e.g. B = sparse cylinder
material), where the old kills' obstructions (enemy's placement
liberty in A) may vanish because WE choose B's geometry.

# THE UNIVERSAL PREFIX-HUB LAW — TWELFTH SUMMIT (2026-07-26)

`endgame_universal_hub` (Endgame.lean, standard axioms;
hypotheses 0 in A + hfail ONLY — no covering): every infinite
positive B subseteq A is owed a cofinal stream of targets at
which B's own prefix is an order-2 hub, with pair wealth capped
at 2|B cap [0,n]|.  The root obligation: all of today's
exclusion/residue/sumset/poverty laws are instances.

THE LEDGER QUESTION in final form: can one set A pay a cofinal
prefix-hub stream to EVERY infinite positive subset of itself,
while pair-covering, with support width 2^(j/2) at every 2-adic
depth, wealth pinned to nested towers, streets poor, forced
mixing, and its Cantor endpoint dead?  The lab's 320 worlds say
no.  The proof of that no is what remains of Erdos 881 k=2.

# THE 2-ADIC WIDTH LAW (2026-07-26)

`two_adic_width_law` (standard axioms, pure — only PairCovers):
at every depth j, with Y the exhaustion bound for finite
classes, 2^j <= |HC|*|WC| + |WC|^2 (HC = head classes of
A cap [0,Y], WC = infinitely-populated classes mod 2^j).
Every residue needs cofinal targets; each splits head+wide or
wide+wide.  Generalizes the convergence blade (|WC| = 1).

CONSEQUENCE: a counterexample's 2-adic support tree must have
width ~2^(j/2) at depth j (up to head mass) — no finite union
of 2-adic branches pair-covers.  Combined with forced mixing
and the exclusion suite: the enemy is exponentially wide in
addresses, while every sparse deletion pins a poor, chained,
sumset-confined failure stream.  The width law supplies what
the bypass audit found missing: unboundedly many
infinitely-populated deep classes = unboundedly many disjoint
cylinder deletions available AT EVERY DEPTH, each demanding
its own 3-wise-disjoint cofinal failure stream.

# THE THREE-DELETION EXCLUSION (2026-07-26)

`three_deletion_exclusion` (standard axioms): a covered target
cannot fail against three pairwise disjoint 0-free deletions
simultaneously — the 0-padded covering pair has two slots,
three disjoint sets need three.  CONSEQUENCE: for any splitting
of the mixing world into disjoint sparse deletions, the enemy
must run pairwise-overlapping-at-most, 3-wise disjoint COFINAL
failure streams — one per deletion.  Splitting into k disjoint
deletions forces k cofinal streams with 3-wise empty
intersections; the failure machinery must be spread across
unboundedly many essentially independent target families, each
poor, residue-chained, and sumset-confined (D_i + A).

The unified core's quantitative form: the enemy's failure
budget is one pair per target, two slots, against unboundedly
many disjoint demands.  Every additional structure law on
WHERE streams can live (residue, sumset, poverty) now
multiplies across the stream family.

# BYPASS AUDIT: refuted as stated; the true gap located (2026-07-26)

LAB (scripts/probe_bypass.py): class-chained targets (every
pair rep touches a fixed class c* mod 2^j) are COFINAL in
adversarial and even random mixing worlds — the naive bypass
claim ('no class is universally pair-touched') is FALSE.
Mechanism: thin covering worlds have r2 = O(1) for most
targets, and chaining is cheap when r2 is small.

Reconciliation with 268/268 survival: failure needs every pair
to touch the SPARSE DELETION ITSELF, not merely its residue
class.  The mathematical difficulty of Erdos 881 lives exactly
in the gap between class-chaining (cheap, cofinal) and
sparse-set-chaining (never observed).  Sparse-set-chaining at
target n = a bounded hub (card <= |D cap [0,n]|) — the mixing
sub-instance failure reconnects to the BOUNDED-HUB STREET
supply, now in cylinder coordinates: the two remaining tracks
(mixing sub-instance, rank/street fork) are ONE track.

New brick: `failing_target_in_sumset` — failing targets live in
D + A; with D log-sparse the failure stream is confined to an
arbitrarily thin sumset.  Together with poverty + residue laws:
failing targets are poor, residue-chained, and sumset-confined.

ALSO recorded: the convergence blade is level-agnostic BUT
covering does not descend through a MIXING step
(half_world_covers needs saturation) — 'infinitely many mixing
levels' is NOT free; do not claim it.

# THE TWO STREAMS — ELEVENTH SUMMIT (2026-07-26)

`endgame_two_streams` (Endgame.lean, standard axioms): inside
every counterexample's located mixing world, each infinite
cylinder deletion generates cofinal failing targets obeying TWO
laws — the RESIDUE LAW (`cylinder_failure_residue_law`: every
pair rep of a failing target touches the deletion's class c mod
2^m; the 0-pad turns any class-avoiding pair into a surviving
triple) and the POVERTY LAW (`failing_target_poor`: pair wealth
<= 2 * deletion's local mass + 2, via `wealthy_target_survives`).

The counterexample is now formally TWO DISJOINT COFINAL
STREAMS: poor residue-chained failures, and rich wealth pinned
to a nested 2-adic tower (`drain_wealth_addresses`) — running
forever through one covering mixing world.  The remaining
question of Erdos 881 along this track: is the segregation
sustainable?  Lab: 52/52 + 268/268 say NO.

Kill geometry now visible: failing targets' pair reps all touch
class c; but the mixing world pair-covers and has both parities
cofinal — choosing the deletion's cylinder INSIDE a class the
covering can bypass (both-parities-off-c pairs exist for
cofinally many targets) would leave no legal address for
failure.  The residue law is the lever: pick B' whose class c
is AVOIDABLE.  Next: formalize bypass-ability in the mixing
world (a pair with both parts off a fixed deep cylinder for
cofinally many targets — counting vs the 2^m - 1 free classes).

# THE MIXING LAB + WEALTHY TARGETS SURVIVE (2026-07-26)

LAB (scripts/probe_mixing_survival.py): 268/268 cylinder-drawn
deletions survive at order 3 across 67 (adversarial mixing
world, cylinder, deletion family) combos — five world
strategies including parity-starving and criticality-
concentrating adversaries.  Mixing worlds cannot defend in the
lab, matching hall worlds (52/52) and the Cantor instance.
The evidence keeps pointing to answer YES for Erdos 881 k=2.

FORMALIZED MECHANISM: `wealthy_target_survives` — a target
whose pair wealth exceeds 2x the deletion's local mass + 2 has
a full triple avoiding the deletion (pair off the deletion +
the 0-weld).  Contrapositive: FAILING TARGETS ARE PAIR-POOR
relative to the deletion's mass below them.  With
`drain_wealth_addresses`: the enemy's failures must live
strictly off its own 2-adically pinned wealth stream.  Next:
turn this into the sub-instance kill — a deletion whose local
mass grows slower than the wealth stream's concentration,
positioned so every candidate failing target is wealthy.

# THE SELF-SIMILAR ENEMY — TENTH SUMMIT (2026-07-26)

`endgame_self_similar` (Endgame.lean, standard axioms): every
counterexample reproduces the problem's COMPLETE hypothesis
package inside a located cylinder — first mixing level m,
address c, world W = {x | c + 2^m x in A} with: covering,
unbounded wealth, both parities cofinal, infinitude, and the
lifted failure interface (`mixing_deletion_wounds_root`: every
infinite deletion from W wounds the root at order 3 through
x -> c + 2^m x).

The enemy one window down is the enemy again.  The remaining
mathematical content along the cascade track is exactly the
sub-instance analysis: either the lifted interface
self-destructs under iteration, or a mixing world survives a
deletion — and mixing IS the carry liberty that powered the
verified Cantor repair (`cantor_carry_repair`).

Ten summits: dichotomy, translate laws, collapsed trichotomy,
parity fork, omega drain, poor street, cascade fork, forced
mixing, mixing world, self-similar enemy.

# THE MIXING WORLD — NINTH SUMMIT (2026-07-26)

`endgame_mixing_world` (Endgame.lean, standard axioms): every
counterexample owns a LOCATED COMPLETE mixing sub-instance — a
cylinder world {x | c + 2^m x in A} that pair-covers beyond a
threshold (covering descends the saturated prefix half-world by
half-world via `half_world_covers`), carries unbounded pair
wealth, has both parities cofinal, and is infinite.  The mixed
regime is SELF-SIMILAR: the enemy reproduces the problem's own
hypotheses one 2-adic window down.

Not yet descending unconditionally: the failure interface (the
(2,3)-mixed hfail descent — `descent_invariant` needs the
saturated horn's single-parity structure, which the mixing
world by definition lacks).  The remaining mathematical content
of the cascade track: what replaces hfail inside a mixing
world, i.e. the mixed-interface descent or a survival
construction exploiting mixing (both parities cofinal = carry
liberty = the Cantor instance's repair mechanism).

# FORCED MIXING — EIGHTH SUMMIT, A COMPLETE BRANCH DEFEAT (2026-07-26)

`endgame_forced_mixing` (Endgame.lean, standard axioms): THE
DETERMINED HORN OF THE CASCADE FORK IS EMPTY.

The kill chain: permanent saturation => the drain is a
determined 2-adic point (`saturated_cascade_determined`) => the
root basis's tail concentrates into one residue class mod 2^k
for EVERY k (concentration induction: cylinders + per-level
saturation + digit/parity link via level-infinitude) =>
`two_adic_convergence_kills_covering` (pure counting: choose K
with 2^(K-1) > head size; large-large sums have pinned parity,
small-large sums land in <= |head| classes mod 2^K; some
wrong-parity class mod 2^K has cofinally many uncovered
targets) => contradiction with PairCovers.

CONSEQUENCE: every counterexample's drain reaches a FIRST
MIXING LEVEL m with exact coordinates — twin channels equal to
the cylinder slice {x | c + 2^m x in A}, both parities cofinal,
blowup wealth flowing through.  The Cantor-like endpoint cannot
be run by any counterexample; mixing is the ONLY surviving
regime of the 2-adic descent.

Remaining: the located mixing world (cross-slice laws, mixed
hfail descent, carry-repair survival) and the rank/street fork
upstream.  The problem's open core is now: one located mixing
cylinder world with wealth, against the survival machinery.

# THE CASCADE FORK — SEVENTH SUMMIT (2026-07-26)

`endgame_cascade_fork` (Endgame.lean, standard axioms): every
counterexample's drain either stays saturated at every level —
then it is COMPLETELY DETERMINED (explicit digits eps', addresses
alpha = partial sums eps'_k 2^k, channels equal, every level the
literal cylinder slice {x | alpha_k + 2^k x in A}: the enemy IS
a 2-adic point, the Cantor-like endpoint) — or hits a FIRST
MIXING LEVEL m: twin channels, explicit cylinder coordinates
{x | c + 2^m x in A}, both parities cofinal, blowup wealth
flowing through.  Chain: `saturated_kills_antidiagonal` (pure) →
`saturated_cascade_step` (pure, level-free) →
`saturated_cascade_determined` → `cascade_mixing_fork` (Nat.find
first-failure + prefix induction).

The two remaining regimes now have exact coordinates.  Attack
next: (1) the determined horn — its cylinder worlds inherit
covering/wealth and should meet `cantor_carry_repair`'s
carry-poor geometry (the verified positive-instance kill); (2)
the mixing horn — both parities cofinal INSIDE a located
cylinder slice + mixing cross-slice law/poverty.

# THE FORCED FIRST MOVE (2026-07-26)

`saturated_kills_antidiagonal` (PURE counting law, no hfail):
in a single-parity world, a level-1 cross-system with blowing
cross-pair wealth cannot mix parities — antidiagonal channels
(p ≠ q) make odd wealthy targets w = 2v+1, and
`global_parity_odd_ordered_cap` caps every odd target at 2Y+2.
`saturated_drain_diagonal`: in saturated counterexamples the
ω-drain's first step is FORCED DIAGONAL (p = q) — the first
confirmed forced move of the descent dynamics.  Saturated
enemies must send wealth down the doubled channel; iterating
this through the half-world descent (needs the MIXED parity
fork — racing-lane work) is the saturated-cascade road toward
Cantor-like worlds, where `cantor_carry_repair` kills.

# THE POOR STREET — SIXTH SUMMIT (2026-07-26)

`endgame_poor_street` (Endgame.lean, standard axioms): every
counterexample funds free sets of every size (root rank >= omega)
OR runs a street of targets with pair wealth UNIFORMLY CAPPED at
2L.  Chain: 0-weld (`pairHub_of_repHub`) + unordered pair
counting (`pair_hub_pair_count`) + high/low reflection
(`repHub_caps_pair_wealth`) + window positivity
(`street_is_sidon_poor`) composed onto the final fork's street
horn.

The collision program: `r2_unbounded_of_hfail` makes wealth
cofinal; `drain_wealth_addresses` pins wealthy targets along one
nested 2-adic tower (w = e_k + 2^k y, e nested, every depth,
every bound).  The street branch is now a segregation regime —
an infinite uniformly poor lane dodging 2-adically clustered
wealth forever.  The remaining kill shape for this branch: force
one wealthy address onto the street (odd-step streets hit every
2-adic cylinder; the enemy must run 2-power-aligned steps to
dodge — a dichotomy to mine next).

# THE REPAIR MINE + THREADING IMPOSSIBILITY (2026-07-26)

Three drain exports: `cross_blowup_infinite` (both carriers
infinite at every level), `drain_address_cluster` (nested 2-adic
address tower inside A — junk-audited: the wealth concentration,
not the bare tower, is the content), `drain_repair_mine` (repair
quadruples a, a+δ, b, b−δ ∈ A, 2^k ∣ δ, every depth, every
bound — Sidon-impossible, so genuine counting content).

Strategic audit: core 4 (chain threading) is NOT closable by
compactness/barrier arguments alone — the per-c chain supply is
an hfail theorem, so threading it into an infinite chain would
refute hfail from its own consequences.  The rank-branch kill
must inject wealth/street/translate material.  The decisive
target: a collision law putting drain wealth on the street's
width-capped hub targets.

# UPDATE (2026-07-26): THE ω-DRAIN — FIFTH SUMMIT

**Arc 34 — the tree completed and globalized** (all verified):
covering splits (`even_target_channel_split`,
`odd_target_cross_split`, `half_worlds_joint_cover`,
`half_cover_dichotomy` — every node passes covering to a live
child); the mixing descent of obligations
(`mixing_cross_slice_law`, `mixing_cross_slice_poverty` — hfail
speaks downstairs in mixing worlds; the cascade blade cuts in
the cross-channel); the generic iterating drain
(`cross_channel_split`, `cross_channel_descends`,
`cross_blowup_descends` — all four parity edges, closed under
iteration); and the capstone:

**`endgame_omega_drain`** — every counterexample owns an
infinite path through the 2-adic tree of cross-systems, from
(A, A) down parity children forever, with pair wealth
persisting at EVERY level.  The enemy's riches trace an
infinite 2-adic address, from hfail alone.

FIVE SUMMITS now in Endgame.lean: final dichotomy, translate
laws, collapsed trichotomy, parity fork, ω-drain.

The remaining mathematics: the drained path's worlds carry
Cantor-cascade structure — the survival argument on such
cascades (template: the verified `cantor_carry_repair`) is the
mixing core; the saturated halls and street analysis the
second; racing termination and chain threading the rank side.
The problem's open heart is now framed by a complete verified
dynamical system on the 2-adic tree.

All verified, zero sorries, standard axioms.

---

# UPDATE (2026-07-26): THE CORRIDOR AND THE CHAIN FORK

**Arcs 32-33 — the rank room opened** (all verified):

- `free_sets_dodge`, `free_disjoint_stream` — the rank branch's
  bare supply self-organizes: dodging any finite obstruction,
  pairwise-disjoint growing shells.
- `finset_stream_higman` — the Nash-Williams door DETACHED:
  any finset sequence has a sorted-list Higman chain
  subsequence, zero hypotheses.
- `rank_room_chain`, `rank_room_spine` — the rank room builds
  its own shell chain and threads its own strictly increasing
  canonical lineage: the spine interface inside the rank
  refuge, no oracle.
- **`stall_chain_or_rank`** — the fork strengthened at source:
  minimal stall windows kill every shorter width at the same
  base, so the rank supply is ascending windows with ALL
  initial segments free — FreeStep CHAINS of every length on
  the canonical spine.  The corridor's prefix-freeness gap
  closes at the fork itself.

**The sharpest form of the compactness core**: FreeStep chains
of every finite length, each riding one spine window, every
initial segment free — versus ONE infinite hereditarily free
chain (= a surviving deletion = the positive answer).  The
between-window threading is the entire remaining gap; the
chains-to-ordinal-rank bridge already exists in the codebase
(the downward induction inside the root-rank theorems).

THE REMAINING BATTLEFIELD (interconnected): the street/hall
core under total saturation and ambient laws; the mixing-world
survival (Cantor template); the racing lane's termination; and
the chain-threading compactness gap — with the corridor now
connecting the last to the first.

All verified, zero sorries, standard axioms.

---

# UPDATE (2026-07-26): THE DESCENT ARC COMPLETE — SESSION CAP

**Arcs 28-31 — the parity/descent suite** (all verified):

- `global_parity_dichotomy` — the last splitter.
- `global_parity_odd_fringe/_hall/_ordered_cap` — single-parity
  worlds hand their ENTIRE odd channel to the finite
  opposite-parity fringe: total door saturation, r₂ ≤ 2Y + 2 on
  every odd target, no placement liberty (the campaign's first
  immovable hall).
- `r2_witnesses_even` — the canonical blowups forced onto the
  even channel.
- `half_world_covers`, `half_world_lift_channel`,
  `half_world_lift_offchannel`, `descent_invariant` — covering
  descends; survival ascends (2,3)-mixed; hfail DESCENDS.  The
  recursion is armed (`endgame_parity_fork` exports the whole
  package).
- `saturated_fringe_nonempty`, `saturated_popular_fringe` — the
  hall's door supply.
- `two_level_descent`, `omega_descent_cylinder` — cylinder
  pinning at every depth: descending worlds are ONE 2-adic lane.
- `cylinder_sparsity`, `descent_threshold_race`,
  `descent_depth_cost` — the lane priced: ≤ 1 element per 2^k,
  thresholds ≥ 2^(k−2) − N₀ − 2 per depth: geometric racing,
  closed form.

**Correction recorded**: literal Cantor is a MIXING world (base-3
digits produce both parities); the single-parity horn is a lone
racing lane, more constrained than Cantor.  The Cantor
generalization target belongs to the mixing horn.

**THE THREE CORES** (all that remains of Erdős 881):
1. MIXING-WORLD SURVIVAL — generalize `cantor_carry_repair`'s
   surviving deletion to digit-rich mixing worlds.
2. THE RACING LANE — terminate the single-parity ω-descent
   (thresholds race geometrically; the mixed interface + hall
   saturation at every level; termination ordinal = rank
   machinery).
3. RANK-ω — the compactness heart (`endgame_final_form`).

Everything else is DEAD or REDUCED to these, bidirectionally
verified.  Summit exports in Endgame.lean: final dichotomy,
translate laws, collapsed trichotomy, parity fork.

All verified, zero sorries, standard axioms.

---

# UPDATE (2026-07-26, cont. 9): FACE MAP COMPLETE + JUNK REPAIR

Face III: `face_three_gap_dichotomy` (dead spectrum in the
unbounded-gap horn: every large basis element translate-poor
against face III's own material) + `near_diagonal_stabilized`
(bounded horn: ONE offset g ≥ 1, cofinal fixed-offset ghosts,
pure-P mirrors above g — the FREE TOWER: the g₀-tower minus
routing; the tower kill's ladder has no substitute yet).

Face I: **junk flag caught and repaired** — P-centredness is
vacuous for additively primitive elements (no positive pair);
`face_one_split` separates the horns: genuine-pair P-routing
vs cofinal primitives.  Primitives are unique-pair targets with
spouse 0 — another marriage-shaped horn.

The counterexample's complete verified map: two rooms; three
faces; face III split twice (gap regime × envelope size);
face I split (routing vs primitivity); every region with named
partial machinery; open cores: strong-horn repair pair, free
tower ladder substitute, face II rotator escalation, rank-ω.

All verified, zero sorries, standard axioms.

---

# UPDATE (2026-07-26, cont. 8): THE PAIR-FLOOD FUNNEL

**Arc 27 — the funnel** (`the_pair_flood_funnel`).  Composing
ghost-or-centre with two cofinality splits: every counterexample
world funnels through its own pair flood into ONE of three
cofinal configurations over ONE fixed free 0-less envelope P:

I. P-CENTRED MEMBERS — cofinal basis elements whose every
   positive pair routes through P;
II. ROTATOR GHOSTS — cofinal b with partner w, sum b + w out of
   A and pair-hubbed by P ∪ {b} (the canonical core-rotator);
III. THE PURE HALL — cofinal ghosts pair-hubbed by P alone.

The door is not a lane; it is a face of the flood.  Combined
with the final dichotomy, the campaign's remaining core is:
defeat faces I–III (fixed-hall analysis with the ambient
translate laws) and the rank-ω room.  Face III with |P| = 1 is
the marriage/unique-pair configuration; |P| = 2 is the door
whose good horn is already empty; the general strong-horn hall
is THE open combinatorial core.

All verified, zero sorries, standard axioms.

---

# UPDATE (2026-07-26, cont. 7): THE PAIR FLOOD

**Arc 26 — the flood welded, unconditional.**
`rep_flood_pos_of_hfail` — the rep flood re-proved with a
0-free envelope (the dodge chain's picks are all ≥ 1; the
strengthened by-contradiction threads 0-freeness through the
whole recursion).  Then the 0-weld:

- **`personal_pair_guard_of_hfail`** — every counterexample
  carries a constant C = |P| + 1 and a free 0-less envelope P
  with: EVERY large basis element b personally guards a target
  m ≥ b whose entire pair life routes through P ∪ {b}, with
  r₂(m) ≤ C.  Pair-poverty pinned to every basis element,
  density-free.
- **`pair_flood_ghost_or_center`** — the placement law: each
  personal target IS its guard (all nontrivial pairs through
  the fixed P) or is a GHOST (m ∉ A).

**Reframing.**  Fixed-hall/door configurations are not lane 2's
special case — they are AMBIENT: every large basis element
carries one personally.  The cascade's counting now has a
density-free supply: the slice spectrum can be tested against
the personal targets of the survivors themselves.  Next: play
the cascade against the pair flood — a deletion B's failure
target n has all survivor-slices pair-poor AND every survivor
s carries a personal pair-poor target m_s; the two supplies
must coexist with coverage's pair-square mass.

All verified, zero sorries, standard axioms.

---

# UPDATE (2026-07-26, cont. 6): THE CASCADE'S TWO AXIOMS

`deletion_failure_slices` + `deletion_failure_double_slice`
(both verified): at any deletion's failure targets, (1) every
survivor-slice is pair-hubbed by the deleted set, and (2) the
survivor set is SUM-FREE against every slice — every A-element
of n − s − S is deleted.  These are the cascade's working
axioms; the open step is the counting/structural pressure that
shows some B's demand is unmeetable (the lab says almost every
B qualifies in hall worlds).

**JUNK FLAG (audit)**: `odd_deletion_obligation` is trivially
witnessed by odd targets (an all-even triple cannot sum to an
odd n), so its conclusion carries no information beyond parity;
treat it as the obligation METHOD's illustration only, not as
structure.  Deletion candidates must keep the survivor set
parity-complete (and residue-complete) — the canonical grid's
old lesson, now sharpened by the slice laws.

All verified, zero sorries, standard axioms.

---

# UPDATE (2026-07-26, cont. 5): THE TRANSLATE LAWS — UNCONDITIONAL

**Arc 25 — the walk kills and the laws.**

- `ap3_deletion_engine` — cofinal fixed-difference AP3s through
  the basis force a surviving deletion (midpoint deletion;
  down-step and up-step repairs).
- `good_two_walk_killed` — if every large basis element keeps a
  good translate among two fixed positive basis elements, a
  surviving deletion exists: the good-translate walk either
  repeats a colour consecutively at cofinal heights (AP3 engine)
  or eventually alternates perfectly (two-step sums constant,
  every-fifth-element deletion, index arithmetic).
- **`single_translate_law`** — UNCONDITIONAL: in any
  counterexample, for EVERY positive basis element c, cofinally
  many z ∈ A have z + c ∉ A.
- **`pair_translate_law`** — UNCONDITIONAL: for every pair
  (h₀, h₁), cofinally many z ∈ A have BOTH translates out.

**Consequences.**  The door world's good horn is EMPTY under
hfail — the strong horn is not a case but the law.  The
good-horn arcs (difference law, good-deep engine, assembly) are
subsumed: still true, now about a vacuous region.  The door
kill reduces to: door world + ambient pair law → find the
repair pair for the strong-horn engine.  The k ≥ 3 finite-set
translate law is open (the walk's wandering wall).

All verified, zero sorries, standard axioms.

---

# UPDATE (2026-07-26, cont. 4): GOOD-DEEP DOOR DEAD, ASSEMBLED

`door_two_good_deep_killed` — no longer modulo anything: from
(|H| = 2, eventually-good, cofinal deep-partner supply), a
surviving deletion exists outright.  The stream extraction
derives ghostliness, pins every level's good translate to h₁,
threads the pairwise difference law, and feeds the good-deep
engine.  Under hfail this horn of the door world is
CONTRADICTORY.

Door status (|H| = 2): good+deep DEAD.  Remaining: good without
deep partners (forced law v − h₀ − h₁ ∉ A: the M-deletion
engine kills the γ(M) = h₁ sub-case — designed, unformalized;
the γ(M) = h₀ sub-case yields v + h₁ ∈ A members to mine);
strong horn.  |H| ≥ 3: open (bad-set pinning is k = 2 specific).

All verified, zero sorries, standard axioms.

---

# UPDATE (2026-07-26, cont. 3): THE GOOD-DEEP DOOR ENGINE

**Arc 24 — the both-in-B wall breached in the deep horn.**
`door_good_deep_engine`: given a geometric door stream with the
four supplies — levels v − h₀ ∈ A, good-translated levels
v − h₀ + h₁ ∈ A (forced in the good horn: the level's bad set
is pinned to {h₀}, so its GOOD translate is h₁), deep partners
v − h₀ − h₁ ∈ A, and the difference law — the deletion of the
even levels SURVIVES.  The double-hit repair is
(v_i − h₀ + h₁) + (v_{j+1} − v_j) + (v_j − h₀ − h₁): the h₁'s
cancel, the sum closes with NO constraint between the hit
indices, and parity/scale separate every part from the
deletion.  Same architecture as the g₀-tower kill.

**Door kill map (k = 2)** after this arc:
- good horn + cofinal deep partners: DEAD (engine above;
  assembly wrapper from the door world = next step: stream
  extraction threading popular shift, goodness, deep-partner
  refinement, difference law).
- good horn + deep partners dying out: v − h₀ − h₁ ∉ A
  eventually — a NEW forced non-membership to mine.
- strong horn (all translates dead cofinally): tower-style
  repair-pair analysis pending.

All verified, zero sorries, standard axioms.

---

# UPDATE (2026-07-26, cont. 2): THE DOOR'S DIFFERENCE LADDER

**Arc 23 — the two-member good horn.**
`door_translate_dichotomy`: cofinal strong-translate elements
(tower law verbatim) or eventually-good.
`door_two_difference_law`: |H| = 2, good horn — door-target
differences are FORCED INTO A.  Proof mechanism: the partner
L = v − h₀ has h₀ bad (v is a ghost), goodness pins bad(L) =
{h₀} exactly, the colour law forces the mirror colour h₀, and
the mirror image collapses to the pure difference v' − v.

**Engine progress (k = 2, good horn), verified reasoning:**
- single-hit repair CLOSES: x = v_{2i} − v₀ deleted, triple
  (v_{2i} − v_{2i−1}) + (v_{2i−1} − v₀) + y — all parts are
  door differences, parity separates them from B.
- both-in-B WALL: residual 2(v_w − v₀) must split into two
  non-deleted A-parts; candidate splits land on the deleted
  difference or need membership at the 2v₀ scale (values
  z + bad(z) = 2v₀ − h forms) which nothing yet controls.

**Next attack on the wall**: Ramsey on the difference algebra
(d_ik = d_ij + d_jk telescopes — consecutive-difference sums
are differences); two-base-point geometry; or the strong-horn
side first (tower repair-pair analysis with ∀-bad translates).

All verified, zero sorries, standard axioms.

---

# UPDATE (2026-07-26, cont.): THE DOOR WORLD OPENED

**Arc 22 — lane 2 at full strength.**  The weld had discarded
order-3 information; re-running the fixed-hall pigeonhole
without it: `bounded_street_fixed_hall_rep` (one window
REP-hubs unboundedly many targets, hall = known positive basis
material), `the_door_world` (2 ≤ |H| ≤ L — teamness forced by
the stream-kill oracle: a singleton hall is a refuted stream —
with cofinal targets carrying BOTH hubs).  The door world's
verified laws:

- `hall_mirror` — defective mirror: v − z − h ∈ A for SOME
  h ∈ H (multivalued where the tower's was exact);
- `hall_weak_translate` — every large z ∈ A escapes at least
  one hall translate (singleton case = the g₀-translate law);
- `hall_mirror_color_law` — mirrors and translates are LOCKED:
  the mirror colour is always a BAD translate (z + h ∉ A);
- `door_targets_ghost` — door targets are forced OUT of A.

**The honest team wall.**  The singleton tower kill does NOT
lift directly: defective mirror residues (which h fired) cannot
be cancelled in 3 repair slots when colours are uncontrolled.
The colour law cuts the space: colours live in H ∖ G_z (bad
translates only).  Next session's engine dichotomy: if some
offset has a UNIQUE bad translate, its mirrors are exact and
the tower engine runs; if all bad sets are full (strong
translate law), the repair-pair analysis of the tower kill
applies instead.  |H| = 2 is the critical first case.

All verified, zero sorries, standard axioms.

---

# UPDATE (2026-07-26): THE FINAL DICHOTOMY — TWO ROOMS

**Arc 21 — the stream-kill oracle refactor.**  Audit finding:
the entire modern chain consumes anchor supply through EXACTLY
two lines — the two `hanchor` applications inside
`surviving_deletion_of_cofinal_privateStream`.  Refactor: new
interface `StreamSurvives A N₀` (every cofinal positive private
stream yields a surviving deletion); all 53 chain hypotheses
re-typed (mechanical sed, zero variants); implemented on both
sides: `streamSurvives_of_anchor` (rotating/fixed kills) and
`streamSurvives_of_almost_anchored` (the g₀-tower self-kill).

**`the_final_dichotomy` / `endgame_final_dichotomy`** — the new
summit.  Every counterexample world (0 ∈ A, covering, hfail):

- FOUR LANES: root rank ≥ ω, or fixed hall + door, or ghost
  street, or member street — now running in anchored AND
  almost-anchored worlds alike; or
- CENTRAL TAIL: thresholded total pinning + automatic
  minimality + midpoint-freeness.

The anchor wall is gone from the final statement.  Five explicit
verified configurations remain: rank, door, ghosts, members,
Salem–Spencer tail.

**Remaining program.**  (1) Kill lanes: door (fixed hall
counting?), ghosts, members (difference-blind stream /
completeness pinch), rank ω (the deep branch).  (2) Kill the
central tail: order-3 residue channels (parity escape + midpoint
gap); note Cantor LIVES in the central tail and is NOT a
counterexample — the tail kill must use hfail, not just
structure.  All verified, zero sorries, standard axioms.

---

# UPDATE (2026-07-26, small hours): THE TOWER KILLS ITSELF

**Arc 20 — the g₀-hole and its plug.**  The almost-anchored
branch's anchor wall has one hole, at the member g₀.  Chasing it:

- `almost_anchored_privateStream` (surgical transplant of the
  rotating-guardian kill): with anchors at every g ≠ g₀, the
  private-stream kill runs EXCEPT when the recurring guardian is
  g₀ itself — the residual configuration is exactly a cofinal
  g₀-private stream.
- `g0_tower` — that stream condenses: cofinal levels L ∈ A,
  singleton pair hub {g₀} at g₀ + L, full mirror law at L.
- `g0_translate_law` — the tower ALONE forces A off its own
  g₀-translate: g₀ + z ∉ A for every positive z ∈ A ∖ {g₀}.
- `routed_tower_mirror_lock` — with routing, the slot L − g₀ is
  forced empty at every high level (else the mirrored ladder
  route hands 2(L−c) a g₀-free noncentral decomposition).
- **`g0_tower_killed`** (+ `g0_tower_engine`): THE KILL.  The
  translate law forbids 2c ∈ A and c + g₀ ∈ A at a ladder
  anchor c, so every pair of the covered target 2c + g₀ is
  automatically g₀-free AND c-free — precisely the repair pair
  the geometric extraction lacked.  Deletion {L(2k+2) − c}
  survives: double hits repaired by (L−u) + (L'−u') + g₀, single
  hits by the c-mirror at the odd level.
- `almost_anchored_stream_killed`, 
  `almost_anchored_singletons_refuted` — the assembly: in
  almost-anchored worlds EVERY cofinal positive private stream
  yields a surviving deletion; under hfail there are NO cofinal
  positive singleton rep-hubs.  The hole admits nothing at the
  singleton level.

**Where this leaves the map.**  Anchored and almost-anchored
worlds now agree at the singleton-hub layer.  Next phase: push
the plug up the chain (hub-card ≥ 2 → teams → shells → spine →
lanes) — each hanchor consumer needs the (anchors-off-g₀ +
ladder + g₀ ∈ A) replacement checked.  If all pass, ALMOST-
ANCHORED = ANCHORED and the collapsed trichotomy becomes a
DICHOTOMY: anchored fork vs central tail.

All verified, zero sorries, standard axioms.

---

# NEW BLOCK (2026-07-25/26 night, post-fork): THE COLLAPSED TRICHOTOMY

**Summit moved twice.**  `endgame_global_trichotomy` then
`endgame_collapsed_trichotomy` (Endgame.lean) — the first final
statements of the campaign with NO anchor hypothesis: only
0 ∈ A, PairCovers, hfail.

**Arc 14 — the welded fork.**  The 0-weld (`pairHub_of_repHub`):
over a basis containing 0, any order-3 hub avoiding 0 is an
order-2 hub.  The final fork's street windows are positive spine
material, so the entire street is an ORDER-2 object
(`the_final_fork_welded`): street targets have ≤ L unordered
pairs (`pair_hub_pair_count` — injective donation into the hub),
pair supply pinned to located windows (`street_target_desert`).

**Arc 15 — the street trichotomy.**  Generic splitting
(`street_position_dichotomy`) + double pigeonhole
(`bounded_street_fixed_hall`) + door extraction
(`fixed_hall_popular_shift`): `the_street_trichotomy` — rank ω,
or a FIXED finite hall with one door element h carrying
unboundedly many targets onto h + A, or a MARCHING street
(windows beyond every spine position, each below its target,
`street_window_below_target`).

**Arc 16 — the four lanes.**  The 0-pair placement law
(`street_target_notMem_or_window`): a pair-hubbed target is out
of A or INSIDE its own window.  `marching_member_dichotomy`
splits the marching street into GHOSTS (targets forced out of A
— forced non-membership, the informative shape) and MEMBERS
(targets = window values, middle pairs banned:
`street_member_small_part`).  Summit: `the_four_lanes` — rank,
door, ghost street, member street.

**Arc 17 — the member street verdict.**  Members expel
differences (`member_difference_out`).  Span dichotomy + stream
extraction (`difference_blind_stream`, Nat.rec supply):
`member_street_verdict` — bounded spans give an infinite
ascending stream y ⊆ A with EVERY pairwise difference OUT of A;
unbounded spans tear the spine (unbounded consecutive gaps).
Lane 4 ends in a Sidon-flavoured stream or a torn spine.

**Arc 18 — THE GLOBAL TRICHOTOMY** (`the_global_trichotomy`,
exported `endgame_global_trichotomy`).  anchor_dichotomy resolved
INSIDE the statement: every counterexample world is
I. ANCHORED (four lanes), II. ROUTED (member g₀ routes all
noncentral doubles: hubs {c, g₀} at 2c), III. CENTRAL (pure
central doubles + total pinning + automatic minimality +
midpoint-freeness).  The fused export the audit addendum asked
for.

**Arc 19 — THE ROUTED COLLAPSE** (`the_routed_collapse`,
summit `the_collapsed_trichotomy` / `endgame_collapsed_trichotomy`).
The middle room is DEFEATED as a separate case: cofinal
g₀-routes give the explicit ladder 2c − g₀ ∈ A plus full anchor
supply at every g ≠ g₀ (ALMOST-ANCHORED — one hole in the anchor
wall, at a known member); dying routes give the ENTIRE central
suite beyond an explicit threshold (CENTRAL-TAIL, subsuming pure
central at threshold 1).  Two live geometries remain:
anchored/almost-anchored fork frontier, and Salem–Spencer
central tail.

**Open next.**  (1) Plug the g₀-hole: can the anchored chain
(private-stream kill onward) run on anchors-off-g₀ + the ladder?
The g₀-singleton-hub case is the fixed-guardian configuration —
the old rotating-guardian endgame killed positive fixed
guardians; if that kill composes, ALMOST-ANCHORED = ANCHORED and
the trichotomy becomes a DICHOTOMY.  (2) Difference-blind stream
vs completeness pinch: the stream is sum-free-relative-to-A;
completeness is the missing half.  (3) Central-tail order-3
residue: the two channels (parity escape + midpoint gap).

All verified, zero sorries, standard axioms.

---

# Erdős 881 (k=2) — Campaign State
_Last full update: 2026-07-25 17:40.  Lean entry point for the
final statements: `Erdos881/Endgame.lean` (the portrait, the
reduction, the two rooms, the universal classifications)._

## CURRENT STATE, ONE SCREEN

**The problem**: must a minimal order-2 basis contain an infinite
subset whose deletion leaves an order-3 basis? The campaign mines a
hypothetical counterexample for contradictions.

**THE 14:35 AUDIT (major, honest, formalized)**: the dodge/trap
block (`dodge_or_trap`, `trap_level`, `trap_tower`, and the tower
branch of `grand_dichotomy`) is TRUE BUT VACUOUS — its conclusions
are satisfiable without `hfail`.  Two in-repo certificates prove
this: `trap_conclusion_trivial` (junk envelope `A ∩ [0,N0]`) and
`tower_branch_trivial` (interval escape: every rep of `n ≥ 3Y`
carries a part `≥ Y`).  Nothing built ON those statements survives
as content EXCEPT the minimality-guarded flood branch.  Do not
build on the bare trap shape; content requires card bounds +
minimality + membership.

**THE SOUND SPINE (all verified, standard axioms)**:
- `cofinal_bounded_hubs_of_hfail` (V10): cofinal targets with
  card-bounded hubs — real, since fat junk hubs are excluded by the
  card bound.
- `stable_core_card_of_hfail` / `hub_endgame_of_hfail`: exact
  recurring card `c ≥ 2`, stable core `S ⊆ H`, rest arbitrarily
  high, cofinally.
- **`stable_core_trichotomy` (NEW)**: every counterexample is
  (T) TIGHT TEAM `c = |S|`: one fixed team of size ≥ 2 hubs
  cofinal targets (pipeline entry at card 2);
  (F) THE FLOOD `c = |S|+1`: canonical nonempty fixed core `S*`
  with cofinal minimal hubs EXACTLY `S* ∪ {a}`, rotating guardian
  (`flood_of_singleton_rotator` + `flood_canonical`; empty core
  dies by the stream kill);
  (R) MULTI-ROTATION `c ≥ |S|+2`: exact-card hubs with ≥ 2
  arbitrarily high members over the fixed core.
- **The pair shadow (NEW)**: a 0-free hub is a transversal of the
  target's order-2 reps (`pair_shadow_of_hub`), so flood targets
  are essentially-Sidon: `r₂(n) ≤ 2(|S*|+1)` cofinally
  (`flood_pair_shadow`), with the routing dichotomy
  (`flood_routing_dichotomy`): a recurring fixed-core corep, or the
  rotating guardian owns its target's entire order-2 life.
- **The log wall (NEW, unconditional)**: `log_sidon_of_hfail` — a
  geometric deletion forces cofinal targets with
  `r₂(n) ≤ 2(log₃ n + 1)`.  Sound quantitative replacement for
  everything the trap was supposed to do.

**THE KILL HOUR (15:10–15:20)**:
- `pair_flood_of_minimality`: the pair flood holds for EVERY
  ℵ₀-minimal order-2 covering set — a structure theorem needing no
  counterexample at all.
- `double_flood_of_counterexample`: both rails align on the SAME
  guardian — every large element guards at both orders at once.
- `two_guardians_per_pair_target` / `three_guardians_per_rep_target`:
  one envelope-avoiding representation pins all guardians of a
  target to its parts — the guardian→target maps are ≤2-to-1 and
  ≤3-to-1.
- **`r2_unbounded_of_hfail` — THE SIDON DOOR CLOSED**: rep flood →
  fan blowup → √-growth forces `r₂` unbounded in any
  counterexample.  Erdős–Turán holds for 881-counterexamples.  The
  enemy's `r₂` must oscillate between a constant (its flood
  targets) and infinity (its blown hub-translates) forever.
- `counterexample_portrait`: the four-part structure theorem in one
  statement (central administration / full employment / Sidon
  streets / blown avenues).
- `guardian_team_hubs_of_deletion`: every 0-free deletion's late
  failing targets carry minimal hubs of card ≥ 2 made of deleted
  elements — the legacy team hypothesis, derived.

**THE FLOOD IS UNCONDITIONAL (15:05, the landmark hour)**:
`rep_flood_of_hfail` — the SAME dodge trick at order 3: hfail
yields one finite REP-FREE envelope `P` such that EVERY large basis
element `b` guards a personal order-3 target `m ≥ b` (all
3-representations through `P ∪ {b}`).  Then, end to end:
- `rep_flood_minimal_of_hfail`: the rotator survives
  minimalization (freeness pins it);
- `rep_flood_pool`: envelope made of pool elements — run in the
  positive pool, the core is positive (zero sliver closed
  structurally);
- `canonical_flood_pos_of_hfail`: NONEMPTY POSITIVE fixed core
  `S*`, cofinal rotating guardians, minimal hubs EXACTLY
  `S* ∪ {b}`;
- `routing_dichotomy_of_hfail`: cofinally, either one fixed core
  element owns coreps, or the rotating guardian owns its target''s
  entire order-2 life.
The configuration the whole campaign assumed as hypothesis is now
a THEOREM from covering + 0 + anchors.  The stable-core trichotomy
and V10 remain as complementary structure; the trap vacuities are
repaired by freeness (junk envelopes are never free).

**THE PAIR FLOOD ARC (15:00, unconditional, the sound trap found)**:
- `pair_flood_of_hfail`: hfail yields ONE finite pair-free envelope
  `P` such that EVERY large basis element `b` pair-guards a
  personal target `m ≥ b`: all order-2 reps of `m` route through
  `P ∪ {b}`.  Constant card; junk-proof; only covering + 0 ∈ A.
  Key: pair-hub-ness is up-monotone, so dodge freeness is a
  one-line invariant, and 0-padding turns surviving pair reps into
  order-3 reps.
- `pair_flood_canonical`: exact core `S* ⊆ P`; hubs EXACTLY
  `S* ∪ {b}`, `b` always necessary (freeness of `P`).
- `constant_sidon_of_hfail` + `constant_sidon_of_minimality`: BOTH
  rails force constant-Sidon streams, unconditionally.
- `pair_flood_pool` + `pair_flood_cascade`: sound descent — the
  level-2 envelope is MADE OF GUARDIANS.
- `singleton_pair_guardian_notMem_free`: empty-core guardians live
  outside every free set; cascade envelopes then vanish.  CAVEAT:
  the empty-core (singleton) world is realized by unique-rep
  targets of any Sidon-like basis — it cannot die from order-2
  structure alone; the kill must couple back to order-3 poverty.

**THE RAMSEY LADDER (16:05)**: `InfiniteRamsey.lean` — infinite
Ramsey for pairs AND triples (not in Mathlib; anchor recursion with
the new anchor drawn from the homogeneous subsequence).  Harvests:
`rep_pair_clique_or_triple_teams`, `team_card_escalation_two(')`
(any ground stream refines to pair-clique / triple-clique-with-
pair-freeness / doubly-free with teams of card ≥ 4),
`injective_pair_flood` (guardian→target map made injective via the
sharer law), `clique_rows_march`, `team_target_dominates` +
`clique_targets_dominate` (choice-free: clique targets ≥ largest
member under exported freeness), `hub_server_dichotomy`,
`pair_flood_two_envelopes` (double duty over disjoint envelopes).
The arity ladder is mechanical now (quadruple Ramsey +
`team_card_escalation_three`: cliques at arity ≤ 4 or teams of
card ≥ 5; dominations at arities 3 and 4); the ω-limit needs
barriers.

**THE FINAL FORM + BRANCH TEMPLATE (18:40)**: the day's summit.
`hfail_iff_no_hereditarily_free` (the characterization) →
`freeStep_wf_iff_no_hereditarilyFree` (the triangle, combinatorial)
→ `counterexample_iff_rep_tree_wf` (THE COLLAPSE: minimality is a
subtree consequence; also in original vocabulary via
`basis3_of_basis2` + `hmin_tuple_of_hfail`).  FINAL FORM:

  Erdős 881 (k = 2) ⟺ no 2-covering set containing 0 has a
  well-founded rep-freeness tree ⟺ every such set contains an
  infinite hereditarily rep-free subset.

Concrete branches: `cantor_powers_hereditarilyFree` (the verified
instance) and **`sidon_has_branch`** (THE BRANCH TEMPLATE: under
any global pair-count bound, an explicit geometric subset is a
branch — candidates beat window fibers; the constructive Sidon
door).  The adaptive toolkit (immunity, count-to-disjointness,
witness location, saturation, witness multiplication, the
3-never-4 cap) bounds where branch obstructions can sit.  Open
core: extend the template past bounded pair-counts (blown-fiber
terms are the exact obstruction = the enemy's hubs), or the
priority construction.  All of it in `Endgame.lean`.

**THE BLOCK TRICHOTOMY (17:20)**: `infinite_ramsey_tuples` —
INFINITE RAMSEY AT EVERY ARITY (induction on arity over the anchor
recursion; `tuple_step` needs only propext) — plus
`sorted_indices_of_card` / `tuple_finset_card` (general
tuple↔Finset bridges), `clique_descent`, and
**`rank_lt_omega_perfect_clique`**: a pool of finite root rank
contains a PERFECT CLIQUE WORLD — an infinite subsequence and a
level `d ≥ 1` with every `d`-subset free and every `(d+1)`-subset
a full hub of a late target; `perfect_world_small_sets_free` makes
its hub hypergraph exactly `(d+1)`-uniform.  Every counterexample
pool is therefore INFINITE-RANK or a PERFECT CLIQUE WORLD.  The
rank program's descent instrument, the reduction, monotonicity,
positivity, and both regime endpoints are now all machine-checked.

**THE RANK IS FORMAL (16:55, FreeRank.lean)**: the rank program's
centerpiece is now an object.  `FreeNode`/`FreeStep` (the freeness
tree), `freeStep_wf` (well-founded in any counterexample — chains
glue into monotone sequences with free prefixes), `exists_strict_rank`
(ordinal rank strictly decreasing along extensions),
`freeNode_extension_iff` (THE LEAF LAW: the tree's boundary is
exactly the hubs), `Stalled` + `Stalled.of_step` (trapped stays
trapped) + `stalled_chain_bound` (stalled zones are shallow:
chains ≤ |A ∩ [0, X)|), `stalled_exists_of_hfail` (the flood IS a
stalled node), `root_rank_dichotomy` (free cards unbounded — root
rank ≥ ω — or universal hubbing at one size), and the ORDER-2 PORT:
`pairFreeStep_wf` + `exists_strict_pair_rank` — every ℵ₀-minimal
basis carries an ordinal invariant, no counterexample needed.
Plus `union_deletion_trichotomy` (splitting deletions: concentration
or straddling teams — two structures pinned to one target).

**Open frontier (post-flood, 15:30)**: the configuration space is
now fully verified and SMALL — see docs/flood-structure-theorem.md
for the complete statement list.  Everything local is mutually
consistent (near-Sidon minimal bases realize the order-2 half); a
contradiction needs an OVERLAP-FORCER between two verified
configurations.  The two known overlap-forcer types: (1) window
counting — blocked, Sidon-points are not scarce (B₂[g] bases);
(2) algebraic identity — the sum-rigidity laws
(shared targets = guardian sums) and the offset dichotomy (blowups
at FIXED distance s₀ from Sidon flood-targets, or at the rotating
corep) are the live leads.  Rank program: freeness trees are
well-founded (free_prefixes_die_of_hfail,
pair_free_prefixes_die_of_minimality); the floods are the stalled
nodes; an ordinal-rank descent across pool-relativized floods is
the structural route.  0 ∈ S* sliver: CLOSED (positive pool).

---

# Erdős 881 (k = 2): solution status

*Updated 2026-07-24, overnight campaign. VERIFIED = machine-checked in
Lean, zero sorries. LAB = machine-tested, not formalized. OPEN =
neither. This document supersedes all earlier versions.*

## The grand assembly (VERIFIED)

`erdos881_grand_assembly''` (`RedundantVertexKill.lean`) is the
sharpest verified statement of the campaign — superseding the earlier
forms.  For any `A` with `0 ∈ A`,
`PairCovers A N₀`, cofinal pair funnels (Link A's interface), and
anchor abundance:

> **either** a surviving infinite deletion exists (`A \ B` still
> order-3-represents every large target — so `A` is *not* a
> counterexample),
> **or** zero privately guards arbitrarily late targets,
> **or** an infinite team clique survives **all of whose positive,
> above-threshold vertices fail 2-redundancy at every threshold up to
> their own scale** — an infinite clique of self-scale 2-guardians
> (`escape_vertex_witness`: each such vertex two-guards a witness
> `n ≥ u` with support exactly `{u, n-u}`), the Grekos-type
> configuration of Open Link B1.

Everything else is dead, by the following verified kills.

## The kills (all VERIFIED tonight)

1. **The singleton stream** (`RotatingGuardianEndgame.lean`).  Any
   cofinal stream of positive singleton guardians forces a surviving
   deletion.  The extraction engine only reflects the anchor data and
   lower levels — all known before each level is chosen — so per-level
   defects are dodged through finite forbidden sets, and a stream
   refusing to dodge has a recurring guardian, killed by the fixed
   engine.  Big/small/fixed/rotating guardians: all dead.  Corollary
   (`FixedGuardianEndgame.lean`): **counterexamples have no
   order-three-essential element.**
2. **Clear clique edges** (`CliqueSplice.lean`).  A 2-redundant vertex
   whose clear edges (`3v ≤ m`) reach arbitrarily high partners runs
   the windowed engine: windows outgrow levels by partner choice.
   (Level hitting — the old B3 interface — is no longer needed.)
3. **ALL edges of any 2-redundant vertex** — the total clique kill
   (`RedundantVertexKill.lean`).  Single redundancy suffices: the
   avoiding representation of `u + x` dodges the partner free below
   the window, the upper desert and level lower bound need no joint
   hypothesis, truncation makes the out-of-window mirror promise
   vacuous, and the quad-defect engine runs on any destroyer supply.
   No hugging, clearance, or joint-redundancy hypothesis remains.
   (Known limit: the corep pin needs the redundancy threshold
   `N₁ ≤ u`; vertices redundant only at higher thresholds are not yet
   killed — this is exactly why the escape says "at every threshold
   up to its own scale".)
4. **Pair-redundant clique edges at any altitude**
   (`HuggingSplice.lean`).  Sharp pinning (`pinned_mirror_sharp`)
   needs no room — only two diagonal exclusions — so a jointly
   2-redundant pair's target carries a full-range mirror at `m - v`
   with four defects (`hugging_level`), levels are pinned near `v`
   (`level_lower_of_pairRedundant`: otherwise a covering window
   starves in the upper desert), and the quad-defect engine runs.
   **Hugging is no refuge.**
5. **Naive separated triangles** (`SeparatedTriangle.lean`): refuted
   by explicit witness — guard separation alone kills nothing.

## What remains open

**Link A (funnels).**  The trichotomy is VERIFIED
(`FunnelTrichotomy.lean`): every destroyed target of any deletion set
`B` carries a singleton funnel from `B`, a pair funnel from `B`, or
two representations with disjoint `B`-parts.  Since singleton funnels
satisfy the pair interface (`u = v`), Link A is *exactly*: no
infinite `B₀` has hereditarily diffuse destruction.  Verified tools
against it: the counting vise (`translate_two_support_card_le` —
destroyed targets and their whole translate families have
`r₂ ≤ 2|B∩[0,m]|`), the elementwise fork trichotomy
(`fork_trichotomy_elt` — every undeleted element below a destroyed
target either lands in `B + B` or plants a two-destroyed cross-sum),
and `TwoDestroyedBySet`-avoidance for undeleted elements.  Lab: the
diffuse regime never occurs in the wild (`probe_counting_vise.py`:
zero destroyed targets for sparse deletions in all models).

**Link B1 (self-scale guardians).**  The clique escape is an
infinite clique of vertices each two-guarding a witness at or above
its own scale (`escape_vertex_witness`).  Full 2-essentiality
(cofinal witnesses) is finite by Grekos-type counting (literature);
the self-scale form is weaker — it is exactly the behavior of
Erdős–Nathanson block bases at order two, so what must be excluded is
the order-three team-clique structure on top of it (lab: cross-scale
team stacking among tight-chained guards dies by coverage flooding —
the old T3 experiments).  Verified support: `TwoLevelDestroyers.lean`
(a genuinely pair-2-destroyed target has exactly two representations
and at most six destroying pairs).

**The zero residue.**  Cofinal `IsPrivateTriple A 0 m`.  Verified
squeezes: the target family's differences are never elements
(`zero_guardian_no_element_gap`) and separated targets are never
elements themselves (`zero_guardian_target_not_elt`) — the residue
needs cofinal non-element targets with an `A`-free difference set.

**Anchor abundance.**  `∀ g, ∃ c ∈ A` positive, `≠ g`, with an
unbalanced representation `w + w' = 2c` dodging `g`.  Fails only for
Sidon-like structure at every doubled point; two disjoint anchor
packages suffice.  Mild; formal supply lemma open.

**Eligibility edge cases.**  The clique escape only constrains
vertices with `0 < u`, `N₀ ≤ u`, redundancy threshold `N₁ ≤ u`.  A
clique of ineligible vertices (all 2-essential, or all below `N₀`)
escapes vacuously — B1 covers the essential case; small vertices are
finitely many.

## THE CAPSTONE: THREE INTERFACES (seventh form)

`erdos881_interfaces_refute_counterexample₇` (`Capstone.lean`).  The
zero residue is **derived away**: cofinal zero-guardianship forces
`A⁺` sum-free (`zero_residue_sum_free`), sum-freeness forbids
doubling elements, and doubling supply is already an interface — so
the residue refutes itself (`not_zero_residue_of_doubling`).  Along
the way the residue's full structure was verified: exact partition
`A⁺+A⁺ = co-A`, automatic ℵ₀-minimality, guaranteed positive triples,
primitive translation ladders.

**The three remaining interfaces:**
1. **Link A** — no cofinal diffuse destruction (`hnodiffuse`);
2. **Link B1** — no infinite clique of vertices each primitive, or
   fully 2-essential and anchor-starved-or-W-aligned;
3. **Supply** — infinitely many doubling elements plus one nonzero
   unbalanced package (near-trivial; fails only for globally
   sum-free-at-doubles structures).

## The earlier sharpest capstone

`erdos881_interfaces_refute_counterexample'` (`Capstone.lean`) +
`erdos881_grand_assembly₄` (`NonEssentialKill.lean`): with **doubling
supply** (infinitely many `c` with `c, 2c ∈ A`) and **one nonzero
package**, the interfaces are: no cofinal diffuse destruction
(Link A), no cofinal zero-guardianship, and no infinite clique of
vertices each **primitive or fully 2-essential**.  The pointwise kill
(`surviving_deletion_of_nonessential_edges`) eliminates every vertex
that is 2-redundant at any threshold and non-primitive: floored
engine, doubling anchors `(c, 0, 2c)`, zero-reflections free,
corep via non-primitivity.  Verified constraints on the survivors:
an infinite primitive clique makes zero fully 2-essential
(`zero_essential_of_infinite_primitives`); essential vertices' witness
sets repel element translates (`essential_witness_repels_translate`)
and their witnesses are never elements with two-point supports
(`escape_vertex_witness`).

## The cross-edge program (next)

The W-aligned enemy's forced families (`anchor_fork_forced`: translates
`m_k - u - C_u` below every edge top; ladders `L_k ∈ A` with
`u`-translate exits) live near the partner tops `v_k` — exactly where
the deserts of the partners' own edges `(v_i, v_j)` sit
(`IsPairDestroyer.desert`: `A ∩ (m' - v_i, m' - N₀) ⊆ {v_i, v_j}`).
Every clique pair is simultaneously constrained, so the `(v_i, v_j)`
targets must dodge windows around every `u`-forced point, for every
`u` below them, at every scale.  The composition of
`anchor_fork_forced` with the partners' deserts — quantified over the
whole clique — is the queued kill for the W-aligned escape.

## The earlier capstone

`erdos881_interfaces_refute_counterexample` (`Capstone.lean`): the
four remaining interfaces — no cofinal diffuse destruction (Link A),
anchor abundance, no cofinal zero-guardianship, no infinite clique of
self-scale 2-guardians (Link B1) — jointly refute counterexamplehood.
Link A's funnel interface is now itself a theorem
(`hasCofinalPairFunnels_of_diffuse_free`): its entire content is the
`hnodiffuse` hypothesis.

## Assessment

The problem's positive direction (YES for k = 2) is now reduced,
machine-verified end to end, to: **Link A diffuse-exclusion + Grekos
finiteness (a known theorem) + the zero residue + anchor supply.**
Every guardian-shaped mechanism — singleton, team, clear, hugging,
big, small, fixed, rotating — is formally dead.  The negative
direction would need a counterexample built entirely from
hereditarily diffuse destruction or ineligible-vertex cliques, for
which the lab finds no seed whatsoever.

## The Cantor demonstrator (2026-07-24, verified)

`Erdos881/CantorCarryRepair.lean` — the 881 repair mechanism on a
concrete basis, machine-verified end to end:

- `cantor_pair_basis`: the base-3 digit-{0,1} numbers ("Cantor basis"
  C) form an order-2 basis of ALL of ℕ (constructive layer split).
- `cantor_powers_destroyed` / `cantor_doubles_destroyed`: deleting the
  pure powers {3^k} removes EVERY 2-representation of 3^k and of
  2·3^k, at every scale (no-carry rigidity: digit-{0,1} numbers add
  without carries, so 2-reps of single-digit targets are trivial).
- `cantor_carry_repair` / `cantor_carry_repair_double`: order 3
  repairs every casualty — 3^k = (13+10+4)·3^(k-3) and
  2·3^k = (13+37+4)·3^(k-3), all parts in C, none a pure power.
  The third summand unlocks base-3 carries (1+1+1 = 3) that order 2
  cannot produce.

Significance for the recurring-pair leaf: the lab showed the leaf's
"AP3-free fork image" residue is realizable by exactly these digit
structures (AP3-free + interval sumset + cofinal fixed-pair
destruction, e.g. pair (1,4) destroying 3^k+5 with reps
{(1,3^k+4),(4,3^k+1)}), so no counting kill exists — but such
structures are NOT 881-counterexamples: the very rigidity that
starves order 2 hands order 3 its carry repairs. The enemy must be
simultaneously digit-rigid (to dodge the matching) and carry-poor
(to satisfy hfail) — the Cantor case proves these pull in opposite
directions.

Open matching residue (exact form): adversary must fork-2-color
every A-window so no v-v pair sums to T, mixed to T+d, u-u to T+2d,
for every achievable T = 2·(realized value)+e. For e=d a per-class
parity pattern dodges V9's identities; for e=0 the image must be
AP3-free (Behrend-type) — realizable as a 2-basis but then
carry-repairable at order 3.

## VERIFIED 881 INSTANCE (2026-07-24 00:00, commit 7945673)

`erdos881_cantor_instance` (CantorCarryRepair.lean, zero sorries):
the Cantor basis C realizes the full Erdős 881 (k=2) pattern:

1. **Order-2 basis**: every n ∈ ℕ is a sum of two members of C
   (`cantor_pair_basis`, constructive layer split).
2. **ℵ₀-minimal**: deleting ANY infinite B ⊆ C destroys order 2 —
   for each deleted b, the target 2b has unique representation
   (b, b) by no-carry rigidity (`cantor_double_unique`,
   `cantor_minimal`). This is exactly the minimality hypothesis of
   Erdős 881.
3. **Order-3 survival**: deleting the infinite set of pure powers
   {3^k} leaves an asymptotic order-3 basis — every n ≥ 3^7 is a
   sum of three non-pure members (`cantor_deletion_order_three`,
   full digit case tree with carry-constant menu).

So the first machine-verified nontrivial minimal order-2 basis
answers Erdős 881's question POSITIVELY for itself: the required
infinite B exists (the pure powers). The problem asks whether every
minimal basis behaves this way; the counterexample structure the
contradiction-mining campaign hunts must therefore be non-Cantor in
an essential way, while the campaign's verified interfaces already
force it to be Cantor-LIKE (2-rep poverty, AP3-free fork images) —
the pincer the remaining leaves must close.

## Endgame map after the Cantor arc (2026-07-24 00:20)

Open leaves, with tonight's dodge analysis folded in:

1. **Recurring-pair matching** (the only open leaf of the fixed-pair
   kill; everything else verified through ENGINE V9).  Image-only
   kills are now PROVEN impossible: for Ramsey color e = d the
   adversary parity-dodges V9's identities per residue class mod d;
   for e = 0 the image must be AP3-free, and AP3-free + covering +
   cofinal fixed-pair destruction is realizable (Cantor windows,
   pair (1,4), targets 3^k+5).  The leaf's true closure must couple
   the matching to hfail: a Cantor-like window structure admits
   carry repairs (verified: cantor_rigidity_conflict), so the enemy
   needs digit-rigid windows WITHOUT carry-repairable deletions —
   candidate theorem: 'fixed-pair unique-rep rigidity at cofinal
   scales ⟹ some marker deletion is order-3 repaired' (the general
   carry lemma). Lab first: build any 2-basis with fixed-pair
   destruction whose marker deletions all fail order 3 — if none
   exists, the general carry lemma is true and kills the leaf.
2. **Link A (diffuse exclusion)** — unchanged.
3. **B1 vertex classes** (primitive / essential-starved) — unchanged.
4. **Supply (hdb + hnz)** — near-trivial, unchanged.

Verified tonight: PinnedMirror sharp pinning; SeparatedTriangle
refutation; zero-residue elimination (capstone at 3 interfaces);
trichotomy→dichotomy; complete B1 case tree; fixed-pair pipeline
(corep dichotomy → fork pigeonhole → channel Ramsey → point splits →
composition) + engines V2–V9; the Cantor instance
(erdos881_cantor_full_instance) and the rigidity conflict.

## THE HUB REDUCTION (2026-07-25 00:30, commits 1ce42f1..91030a3)

New first-principles chain, machine-verified:

    hfail (order-3 failure vs every infinite deletion)
      ⟹ [Engine V10] disjoint-rep growth is bounded: some K
      ⟹ [hub extraction] cofinal targets carry rep-hubs ≤ 3(K−1)

`cofinal_bounded_hubs_of_hfail` — the counterexample MUST
concentrate all 3-representations of infinitely many targets on
constant-size hub sets. The fixed-pair pipeline (corep dichotomy →
forks → Ramsey → engines) was the |hub| = 2 case; it is now the
provably general configuration, entered from raw hfail rather than
through the funnel case analysis. Supporting verified facts:
marker deletions never fail on their own pair-destroyed targets
(MarkerRepairs.lean), and the lab finds ZERO singleton/pair-covered
targets in every buildable covering structure.

Escalation plan: hub tower extraction (iterated pigeonhole →
fixed small hub part + level-like large part), then the |S|-fold
generalization of the fixed-pair machinery.

## The hub tree completed (2026-07-25 00:40)

DisjointRepEngine.lean now derives, from raw hfail + interfaces,
machine-verified with zero sorries:

1. Bounded disjoint reps (V10) → bounded hubs → window-split tower
   (fixed core S per window, rest large) — `team_configuration_of_hfail`.
2. Small cores are dead: empty (covering), zero singleton
   (zero-residue kill), positive singleton (stream kill) —
   `hub_card_ge_two_of_hfail`. THE PAIR IS THE BASE CASE.
3. Minimal hubs exist and every element owns a private witness
   (`minimal_hub_necessity`) — the guardian structure from first
   principles. Exact-pair hubs are pair destroyers.

The campaign tree is now rooted: hfail itself forces the
guardian-team configurations all previous arcs studied. Open
branches: exact-pair recurrence (→ fixed-pair pipeline), half-fixed
pairs (S = 1 + rotating), all-large coreps (S = 0), plus the
matching/identity acquisition and diffuse exclusion.

## THE STABLE CORE (2026-07-25 00:45, commits d82b614+)

`stable_core_of_hfail` — machine-verified: a counterexample has ONE
fixed finite guardian set S* such that at EVERY window, cofinally
many targets carry minimal hubs = S* ∪ {elements above the window},
each hub member owning a private witness. The enemy's entire
order-3 failure concentrates on a single finite team plus
level-scale escorts, at all scales simultaneously.

The endgame is now a two-branch tree on S*:
- **S* = ∅**: `large_team_shadow_of_empty_core` — both 3-reps AND
  2-reps of cofinal targets confine to bounded rotating teams above
  every window (the order-2 shadow via 0 ∉ H). Level-scale
  destroyer teams: counting-vise + team-rigidity territory.
- **S* ≠ ∅**: eternal guardians — fixed elements in cofinal minimal
  hubs at all scales, with necessity witnesses. Essential-element /
  fixed-guardian-with-escorts territory.

Both branches land on partially-killed configurations with verified
machinery pointing at them. The remaining open work: finish either
branch (plus matching acquisition and diffuse exclusion for the
legacy tree).

## Final form of the night (00:50): the canonical enemy

`hub_endgame_of_hfail` — everything a counterexample can be, in one
verified statement: fixed guardian core S*, fixed hub size c* ≥ 2
(≥ |S*|), minimal witnessed hubs of exactly that shape at every
window cofinally; tight case = one recurring finite team (c* = 2
enters the fixed-pair pipeline via `pipeline_entry_of_tight_pair`);
escort case = rotating level-scale guards with the order-2 shadow
when S* = ∅. DisjointRepEngine.lean: ~1100 lines, zero sorries,
one night, raw hfail to canonical shape.

## Supply census closes the night (00:55)

probe_private_supply.py: the alignment supply required by
tight-team simultaneity (recurring differences across elements'
private-2-target lists at every scale) exists ONLY in digit-rigid
structures — Cantor's recurring differences are exactly the powers
of 3 — and digit-rigid structures are carry-repairable
(cantor_rigidity_conflict, verified). Generic covering structures
have near-zero supply. Both remaining branch families (matching
acquisition, tight-team simultaneity) now face the same verified
pincer: the structure the enemy needs to dodge our engines is the
structure that repairs at order 3.

## The convergence (2026-07-25 01:05)

probe_window_sat.py: the tight-pair enemy's single-window demand is
UNREACHABLE by search from generic covering (service stalls at
~15%) and PERFECTLY satisfied by the Cantor structure (16/16
markers), whose service mechanism is exactly its doubles — the
verified minimality mechanism, whose order-3 carry-repair is also
verified. All three independent lines of the night (matching
dodges, alignment supply census, window satisfiability) converge:
the only structures that can satisfy the enemy's demands are
digit towers, and digit towers satisfy Erdős 881's conclusion.
Remaining mathematical gap, now singular: the general carry lemma
(Engine V11) — rigidity all the way down forces order-3 repairs.

## THE DUAL RAILS COMPLETE (2026-07-25 01:20)

The digit recursion's two rails are now fully verified and
canonical, both derived from Erdős 881's raw hypotheses:

- **Order-2 rail** (from minimality): the engine ported one level
  down — minimality forces canonical pair-hubs, a stable
  2-destroyer core across all scales, and in the tight case THE
  RECURRING FIXED PAIR {u, v} (`recurring_destroyer_pair_of_
  tight_core`) — the exact configuration the legacy fixed-pair
  campaign assumed, now a theorem.
- **Order-3 rail** (from hfail): the canonical hub tree with
  eliminations, alignment demands, the P/D digit-split, and the
  service structure theorems.

The final wall is the rails' interaction (the second digit and
beyond). DisjointRepEngine.lean: ~1950 lines, zero sorries, one
session.

## THE COMPLETE TWO-RAIL CASE TREE (2026-07-25 01:25, final form)

Both rails verified from raw hypotheses; every branch lands on
named machinery:

**Order-2 rail** (minimality ⟹ canonical (S₂, c₂) pair-hubs):
- c₂ = |S₂| = 1: one universal 2-guardian a; cofinal a-private
  sums = the doubles/service regime (U-density supply through a).
  Vise-consistent; the alignment/service theorems constrain it.
- c₂ = |S₂| = 2: THE RECURRING DESTROYER PAIR {u,v}, derived
  (legacy_twoDestruction_of_tight_core) → the entire
  PinnedMirror/fork/funnel arsenal engages with d = v−u; the P/D
  split is the first digit.
- c₂ > |S₂|: rotating 2-escorts above every window — level-scale
  2-destroyer teams (TwoLevelDestroyers vise territory).

**Order-3 rail** (hfail ⟹ canonical (S₃, c₃) rep-hubs):
- c₃ = |S₃| tight: recurring team; c₃ = 2 → fixed-pair pipeline
  (V2–V9 + open matching); c₃ ≥ 3 → team-translate simultaneity
  (alignment demand, forced blocks, block self-interaction).
- escorts (c₃ > |S₃|): rotating guards; S₃ = ∅ has the order-2
  shadow (2-reps confined) → pair-funnels.

**Cross-rail structure** (verified): P/D split with bipartite
service wiring; chains ≤ 2; doubles-mode dead; rigidity =
reflection-freeness; rigid markers erase mirror levels; service
sums = injective valley points (U-density in co-A).

**The one remaining wall**: the digit recursion's upper rungs —
re-running the rails inside the structured parts to force digit 2,
3, … (the full tower), whose carry-repair
(cantor_rigidity_conflict) then contradicts hfail. Everything else
is machine-verified.

## Correction (2026-07-25 01:40, self-audit)

The service/alignment/P-D chain (all *verified* as stated) is
CONDITIONAL: its single-marker window hypothesis is not yet derived
from hfail — geometric deletions have log-many markers below their
failing targets, and hfail doesn't promise failures in the single-
marker stretch. Unconditionally derived from hfail remain: the
canonical hub tree, the stable core and canonical shape, the
eliminations, and the team-translate equivalence. Priority zero
next session: the multi-marker (log-budget) service analysis — the
dominant-marker candidate fix (geometric gaps make the nearest
marker dominate the translate scale) may rescue the chain nearly
verbatim.

## The problem's core, in final form (2026-07-25 01:50)

After the night's full excavation: Erdős 881 (k=2)'s difficulty is
exactly the CONSTANT-vs-LOG hub gap. Unconditionally verified:
every counterexample has cofinal constant-size rep-hubs (canonical
tree, B-independent), and per every geometric deletion B its
failing targets carry O(log)-size B-relative hubs (injection
lemma). The refutation machinery (towers, stable cores,
pigeonholes) runs on constants; the per-deletion failures only
guarantee logs. Every sound total-repair engine and every
structural forcing built tonight lives on one side of this gap;
the enemy lives in the sliver between. Routes recorded: bootstrap
hub-shrinking, slow-deletion diagonalization, log-budget Ramsey.

## The single remaining statement (2026-07-25 01:50, night's end)

Per-deletion tree complete (super-geometric deletions): escape
branch dead by singleton collapse + stream kill; failures need
prefix guardians with recurring exact cores over OUR marker
alphabet. Every route of the entire night — matching, alignment,
service, window-SAT, escape — terminates at one statement:

  INFINITE PER-ELEMENT GUARDING SUPPLY + COVERING ⟹ DIGIT-LIKE.

Digit-like structures verifiably satisfy Erdős 881's conclusion
(carry repair). Proving that one classification closes the
problem; every supporting wall is machine-verified.

## The squeeze's working suite (2026-07-25 02:10)

Verified in the night's final stretch: the complete per-owner and
per-pair constraint system of the classification — mid-window
reflection, the strip counting atom, cross-owner exclusion, the
consecutive-owner dichotomy (the gaps are the moduli), completion
isolation (each completion sits alone, insulated by its owner's
difference structure), and completion mutual avoidance (the
difference-splitting seed). The coherence conjecture now reads:
per-octave difference structure splits into disjoint owner and
completion layers; the layer hierarchy is the digit system. All
seeds verified; the aggregation and octave induction remain.

## THE PAYMENT THEOREMS (2026-07-25 02:30 — the night's summit)

Machine-verified in the final hours, the squeeze's payment side in
full:

- `zero_payment_squeeze` + `zero_payment_gap_bound`: payment-free
  owners repel all neighbors past half their target — giant-gap
  valleys only.
- `no_five_zero_payers`: five zero-payers overfill their octave.
- `cube_le_two_pow` + `octave_rich_of_covering`: covering's
  √-supply cannot live in octaves of four — rich octaves cofinal.
- `paying_owner_in_rich_octave` + `paying_owners_cofinal`:
  **THE OPTIMIZATION LOWER BOUND** — the enemy cannot live
  payment-free at any scale.
- `payment_demand` + `payer_in_five`: each payer writes a fresh
  co-A ledger entry below half its target, at rate ≥ 1 per five
  octave elements.

Remaining single computation: THE LEDGER TELESCOPE — control entry
multiplicity across payers and scales; overflow forces digit
routing; digit routing has verified carry-repair contradicting
hfail. Everything else — two canonical rails, the per-deletion
capstone, the ownership calculus, the payment theorems — is
machine-checked, zero sorries, standard axioms.

## Telescope audit (02:32)

Honest correction: the ledger telescope cannot close by pure
counting — co-A entries are reusable across payers, and the
fiber-clearing identity balances at the knife-edge. The payment
theorems stand as structural inputs (cofinal inhabited big
windows), but the final argument is the coherence classification
itself, now to be attacked with every structural input of the
night. The problem's core is, and was, exactly that
classification.

## THE CANTOR FIXED POINT + THE LOCALITY BOUNDARY (03:15)

`cantor_fixed_point` (verified): a positive number is outside the
Cantor set exactly when it is some forest-owner's moat value —
co-C = Sieve(C) as one iff, the classification's model half
complete. And the boundary is now definitive: exhaustive and
randomized searches show the local laws admit alternate fixed
points at every tested radius. The uniqueness — hence Erdős 881
itself — lives exactly in the global rails' selection power, with
everything below them machine-verified.

## THE SHELL ENDGAME + DEPTH TAX (2026-07-25, 19:20)

Verified arc (FreeRank.lean; all standard axioms, zero sorries):
`freeSup_wf` / `pairSup_wf` (no ascending inclusion-chains of free
sets — unions would be branches), `exists_absolute_leaf` (+ pool
and pair versions; the pair version is a standalone structure
theorem for EVERY ℵ₀-minimal order-2 basis),
`absolute_leaf_personal_target`, `absolute_shell_stratification`
(disjoint nonempty free shells, hierarchical total guardianship),
rotation caps `four_disjoint_hubs_singleton` /
`three_disjoint_pair_hubs_singleton` (hypothesis-free pigeonhole),
`eternal_survivor_dichotomy`, `shell_survivors_unbounded_targets`,
`shell_depth_forces_scale`, `depth_tax_of_hfail` (every large
element clear of shells 0..k guards at height ≥ N₀ + k/3),
capstone `shell_endgame` / `endgame_shells`.

Enemy shapes remaining: perfect stratification (shells tile A⁺ up
to a finite set) or an infinite crowd of infinitely-employed
survivors; in both, deep elements pay linear-height guardian
duties.  Probes (scripts/probe_shells.py): honest models are
shallow-and-fat; the enemy must be an infinitely deep onion of
finite shells.  The open core is unchanged (target liberty /
witness confinement), but the adaptive program now has a verified
LOCATION LAW for where deep elements' obligations sit.

## THE STREET DICHOTOMY + REFLECTION LEDGER (2026-07-25, 20:29)

Verified tonight (FreeRank.lean, standard axioms, zero sorries):
`seal_cost_of_disjoint_avoiding`, `two_hubs_common_reflection`,
`double_reflection_supply_of_hfail`, `street_dichotomy_of_hfail`,
`difference_blowup_or_affine_corners`, `fixed_offset_or_growing`.
Every counterexample must either repeat DIFFERENCES beyond any
bound (one fixed offset with infinite multiplicity, or
arbitrarily large offsets at every multiplicity — closing the
difference door as Erdős–Turán closed the sum door), or run an
affine sealing schedule m_b = b + n with blown points coupled to
pair streets by s + b₂ = n + b₃.  Also verified this block: the
absolute flood / shell stratification / depth tax / rotation caps
/ six-level and 18-level caps / shell-conflict law / robustness
branch (third branch mechanism; Cantor is uniformly robust) /
fragility laws.  The enemy's remaining configuration space: the
mixed fragile-blown regime, now further split into echo-hoarder
vs mirror-hall.

## CLASSICAL-MINIMALITY + RAMSEY ARCS (2026-07-25, 21:05)

New verified interfaces for the TRUE 881 hypothesis (classical
minimality, previously unused): essential_private_pair_stream,
shared_private_target_is_sum, unique_pair_graph_infinite_degree,
disjoint_unique_pairs_of_essential, matched_deletion_teams,
hmin_of_essential (glue: classical ⟹ elementwise, all hmin
machinery now applies), unique_sum_ramsey +
all_unique_pair_hubs/all_unique_is_sidon.  Also this block: R1
translation teams; R4 ladder mining (pure streets, concentrated
shadow, difference deserts); ladder-world labs (R4 realizable
with geometric rungs; strain at √Y/3 density).  Zero sorries
throughout; standard axioms.

## NIGHT INDEX — 2026-07-25 evening block (16:41 → ~00:41)

~140 commits, ~50 new verified theorems, zero sorries, all
standard axioms.  The complete arc list, in order:

1. ABSOLUTE FLOODS: freeSup_wf, pairSup_wf, exists_absolute_leaf
   (+ _pool, pair version = standalone ℵ₀-minimal-basis theorem),
   absolute_leaf_personal_target.
2. SHELLS: absolute_shell_stratification, shell_endgame,
   endgame_shells, stratified_tax_portrait; depth tax
   (shell_depth_forces_scale, depth_tax_of_hfail);
   eternal_survivor_dichotomy, shell_survivors_unbounded_targets.
3. CAP SUITE: four_disjoint_hubs_singleton,
   three_disjoint_pair_hubs_singleton, seven_level_hub_impossible,
   eighteen_level_cap, five_shell_conflict_impossible,
   four_shell_pair_conflict_impossible, shell_pairs_conflict,
   IsRepHub.mono.
4. ROBUSTNESS: robustness_gives_hereditarily_free,
   fragile_supply_of_hfail, duty/conflict_targets_fragile;
   Cantor uniformly robust (probe), mechanism unification.
5. REFLECTION LEDGER: seal_cost_of_disjoint_avoiding,
   two_hubs_common_reflection, double_reflection_supply_of_hfail.
6. THE FOUR ROOMS: street_dichotomy_of_hfail (+_uniform),
   difference_blowup_or_affine_corners, nat_param_stabilize,
   affine_corner_fixed_or_scattered,
   fixed_hall_extracts_difference, fixed_offset_or_growing,
   counterexample_four_rooms, endgame_four_rooms.
7. LADDER MINING: street_ladder_pure,
   ladder_shadow_concentrates, ladder_difference_desert;
   ladder-world labs.
8. CLASSICAL MINIMALITY (881's own hypothesis, first use):
   essential_private_pair_stream, shared_private_target_is_sum,
   unique_pair_graph_infinite_degree,
   disjoint_unique_pairs_of_essential, matched_deletion_teams,
   hmin_of_essential, translation_room_teams.
9. RAMSEY CASCADE: unique_sum_ramsey, all_unique_pair_hubs,
   all_unique_is_sidon, clique_or_independent_teams,
   independent_alternatives_ramsey, surviving_sum_square,
   ramsey_trichotomy_of_covering, cube_avoidance_ramsey,
   endgame_ramsey_trichotomy.
10. THE ω-PINCH: omega_avoidance_dichotomy, endgame_omega_pinch,
    survival_of_complete_avoiding,
    complete_families_blocked_of_hfail,
    subset_sum_complete_of_small_gaps; greedy probe (0.9 density,
    97% coverage); the circle closed honestly — self-avoidance is
    the entire content.

STATUS: Erdős 881 (k = 2) remains open.  Every local attack
tonight terminated in configurations the enemy can satisfy;
every reformulation is provably equivalent to the original.  The
remaining programs, ranked: (i) the 90/10 partition battle line
(counting vs structure at every scale); (ii) mass-accounting
constants; (iii) Abel-summation automatic-completeness; (iv)
Nash-Williams barriers; (v) the adaptive/priority construction.

## NIGHT INDEX, APPENDIX (22:03) — the drive-home cascade

After the user's "bring it together": the_encirclement (six
pillars, one theorem), docs/big-picture.md (the synthesis:
theory closed, no-man's-land, self-avoidance is everything, the
enemy's material is the constructor's), then the Nash-Williams
arc: shell_higman_chain, spine_lineage,
spine_stalls_hereditarily, spine_rank_or_lockstep,
root_rank_omega_or_lockstep, lockstep_columns, endgame_spine.
Entry points: Erdos881/Endgame.lean (the_encirclement,
endgame_spine, endgame_four_rooms, endgame_omega_pinch,
endgame_final_form).

## HYPOTHESIS AUDIT TABLE (22:20) — what needs anchors

ANCHOR-FREE (apply to ALL counterexamples, incl. carry-free):
four rooms, street dichotomy, reflection ledger, ω-pinch, cube
dichotomy, Ramsey cascade, r₂-unbounded, floods, cap suite,
conflict law, fragility/robustness suite, seal cost,
completeness criteria, hmin_of_essential, classical-minimality
suite (needs hess, not anchors), anchor trichotomy + central
branch laws.

ANCHOR-CONDITIONED (excluded in carry-free worlds; rescued by
the anchor trichotomy's other branches): rotating-guardian kill,
cofinite_free_singletons, shell stratification + depth tax +
shell endgame, spine arc (Higman chain through highway tax),
matched_deletion_teams, translation_room_teams,
the_encirclement pillars (1) and (3), endgame_spine.

Every counterexample falls under: anchored (full machinery) OR
g₀-routed OR central (total order-2 pinning).  No gap.

## NIGHT INDEX, APPENDIX 2 (22:35) — the late arcs

11. NASH-WILLIAMS/SPINE: shell_higman_chain, spine_lineage,
    spine_stalls_hereditarily, spine_rank_or_lockstep (+',
    +root_rank_omega_or_lockstep), lockstep_columns,
    lockstep_lane_guardianship, highway_tax,
    lockstep_one_lane_clique, lockstep_uniform_streets,
    endgame_spine, the_encirclement.
12. ANCHOR TRICHOTOMY: probe_anchor (Cantor anchor-free!),
    anchor_dichotomy, no_anchor_doubles_thin,
    no_anchor_central_or_member, central_branch_singleton_hubs,
    central_branch_hmin, central_branch_no_three_AP (central =
    Salem–Spencer), residue census (two-channel order-3 life).
13. CANONICAL GRID: odd_deletion_obligation,
    canonical_deletion_obligation, grid_cap_three_classes;
    width-claim corrected (two-scale escape: the grid is a
    per-modulus alignment dichotomy engine).

## AUDIT ADDENDUM (23:05) — the fork's anchor condition

The Nash-Williams chain (spine → game board → width-or-rank →
THE FINAL FORK) inherits the anchor hypothesis through the shell
stratification.  The complete final picture is therefore a
TRICHOTOMY of endgames:

  ANCHORED counterexamples → the final fork (rank ≥ ω, or the
  located uniform-width street on the spine);
  g₀-ROUTED counterexamples → universal two-element double-hubs
  through one basis element (concentration laws);
  CENTRAL counterexamples → total order-2 pinning, automatic
  minimality, AP3-freeness, two-channel order-3 residue.

No counterexample escapes all three.  Building fork-analogues
for the g₀-routed and central branches (their own spines exist
if their own stratifications do — the absolute flood needed only
h0/hcov/hfail, but shell NONEMPTINESS used anchors via
cofinite_free_singletons) is a recorded next-session task: the
central branch may admit a direct spine from its pinned
structure instead.
