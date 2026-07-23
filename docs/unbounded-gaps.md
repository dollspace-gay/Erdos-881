# The unbounded-gap frontier

*2026-07-23. Status: the **geometric regime is now proven**
(`Erdos881/UnboundedMirrorGaps.lean`,
`surviving_deletion_of_geometric_reflectionLevels`): levels that are
elements and more than double each step — gaps unbounded — admit a
surviving deletion, given an anchor `c < L 0` with an unbalanced
representation `2c = w + w'`, `w ≠ c`.  The deleted set is the anchor's
mirror at every second level; doubling growth kills every collision case,
and the unbalanced `2c`-representation repairs the both-deleted case via
`(L a − L (b−1)) + (L (b−1) − w) + (L b − w')`.  The general-spacing
conjecture below remains open.  Companion experiments:
`scripts/probe_team_rigidity_and_gaps.py`.*

## Where the master chain stops today

`MirrorPeriodicity.lean` proves: reflection levels with **bounded gaps**
⇒ periodicity ⇒ surviving infinite deletion
(`surviving_deletion_of_boundedGap_reflectionLevels`, and in repo
vocabulary `exactTupleBasis_orderThree_deletion_of_boundedGap_reflectionLevels`).
The open question is what happens when the gaps grow.

## Unbounded gaps are realizable

The Cantor-style mirror fractal `T₀ = [0, b]`,
`T_{k+1} = T_k ∪ (3·M_k − T_k)`, `M_{k+1} = 3·M_k` satisfies, verified
computationally at two parameter choices:

- perfect pair-covering of `[N₀, 2·M_K]` (zero holes),
- genuine reflection levels at every `M_k`,
- level gaps `2·M_k` — unbounded, so outside the formalized chain.

Density `|T ∩ [0,x]| ≍ x^{log 2 / log 3}`: these are sparse covering sets.

## Conjecture (unbounded-gap spare keys)

**Any order-two covering set with cofinal reflection levels admits an
infinite deletion that survives at order three** — no gap bound needed.

Evidence: on the fractals, random sparse deletions (10% samples, three
seeds each) destroy **zero** targets; deleting all level tops `{M_k}`
destroys zero targets. The only deletions observed to destroy anything
are aggressive ones: one-per-mirror-pair transversals (half the set)
destroy a handful of targets, and deleting an entire top mirror copy
destroys everything above it (a finite-boundary artifact — in the
infinite set the next level's copy repairs it).

## Proof sketch to attempt

For `x` in the deleted set with `x = M_j − c` (a mirror image at level
`j`), the translation `IsReflectionLevel.translation` between levels
`j−1` and `j` lets a damaged representation `x + y + 0 = n` be repaired as
`(x − d) + (y + d) + 0` with `d = M_j − M_{j−1}`, valid when
`0 < y < M_{j−1}`.  Choose the deletion `B = {M_{j_k} − c}` along a
sparse subsequence `j_k` so that (i) the shift-collision cases (`y` large
or `y + d` deleted) can always switch to a different level's gap, and
(ii) the `n ∈ B` case is repaired through the covering of `d` itself
(note `d = 2·M_{j−1} = M_j − M_{j−1}` is the reflection of `M_{j−1}` at
level `j`, hence an element in the fractal — in general this needs the
levels to be elements, a hypothesis worth adding).  The bookkeeping is
the per-level analog of the mod-4 escape argument in
`periodic_covering_admits_surviving_deletion`; the missing piece is a
uniform choice of shift level when `y` sits high in the hierarchy.

## Why this matters

If the conjecture holds, the bounded-gap hypothesis is an artifact and
the wallpaper endgame needs only *cofinal mirrors of any spacing* — which
is much closer to what guardian rigidity actually forces.  Combined with
`no_big_guardian_stacking` / `no_big_guardian_above_team`, the remaining
counterexample space would shrink to sets with cofinal destroyed targets
whose funnels are neither singletons nor teams with separated scales, and
whose mirror levels are *not* cofinal — a strange beast worth trying to
rule out directly.
