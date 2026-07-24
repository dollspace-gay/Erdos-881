# Thin-basis campaign results (2026-07-24)

*Companion script: `scripts/probe_thin_bases.py` (+ inline chain-dodge
verification). Motivation: the disputed NO-claim for problem 881 uses
thin bases, and all small-guardian structures found by exhaustive search
are sparse — thin bases are the serious counterexample zone.*

## Headline: cofinal team protection exists in the wild

In Nathanson's canonical thin minimal basis (numbers with binary digits
on even positions ∪ odd positions), the census found **team-guarded
targets at every dyadic scale**: the all-ones targets
`2^k − 1 = 15, 31, 63, 127, 255, …` are each guarded by the pair of
alternating-bit numbers `{a_k, 2a_k}` (…, {21,42}, {42,85}, {85,170} …).
The base-3 analog shows the same phenomenon (guards 6, 20, 60, 182,
546, …). Zero singleton-guarded targets in either basis.

This kills the hope that guardian protection is inherently single-scale:
**teams stack cofinally in natural thin bases.** Our earlier stacking
sweeps missed this because their families had free-standing guardians;
the wild mechanism is *chained sharing* — consecutive teams share a
guard, forming an infinite path.

## Why these bases are still not counterexamples (verified)

The chain is dodgeable. Machine-checked in the 12-bit model:

- delete every other chain guard (either parity): **survives — zero
  destroyed targets**;
- delete two consecutive guards {21, 42}: destroys exactly their joint
  lock 63;
- delete all chain guards: destroys the cofinal family
  {15, 31, 47, 63, 95, 127, 191, 255, …};
- delete a whole dyadic layer of one digit class, or a residue class:
  hundreds destroyed (structured deletions fail, as always).

So the surviving infinite deletion exists — an independent set in the
team chain — and the even/odd bases sit on the positive side.

## The sharpened battle line

A genuine counterexample to 881 (k=2) must be a thin basis whose
cross-scale team hypergraph has **no infinite dodgeable set**: every
infinite subset of A must contain a complete guarding team for
infinitely many targets. A path (each guard in ≤ 2 teams) is maximally
dodgeable; the census shows guard-degrees 2–3 in both digit bases. The
question is whether guard-degree can be made to grow so fast that
independent sets die — an infinite-Ramsey-flavored density question, and
exactly what the repo's star-vs-matching and pair-Ramsey machinery
(`InfinitePairRamsey.lean`, the matching/star dichotomy) was built to
attack. Single-scale 3-cliques of mutual guardianship exist
(`probe_team_guardians.py`); cross-scale cliques have never been
observed.

## Also settled this campaign

Mass stacking sweep over **all 13** small-guardian structures at M=16,
closure plus one-symmetric-pair variants, 3,716 second-scale candidates:
zero fresh guardians, zero stacks. Singleton/small-guardian protection
remains strictly single-scale — consistent with Erdős–Graham and
Cassaigne–Plagne (S(2)=3) on the literature side.

## Interlock experiments (`scripts/probe_team_interlock.py`, same day)

**A — exact team graphs.** Even/odd binary: the team graph is exactly the
path 1–5–10–21–42–85–170–341–682–1365–2730, every guard-degree ≤ 2, zero
triangles. Base-3: a caterpillar tree — spine 6–20–60–182–546 with
degrees 3–4 and pendant leaves — still zero triangles. Trees are
2-colorable, so an infinite dodge always exists. Guard-degree can exceed
2 in the wild, but no clique seed (triangle) has ever been observed.

**B — the cost of interlocking.** For non-adjacent chain guards
(a_i, a_j), the number of representations of a_i + a_j that a builder
would have to destroy to create the team edge grows geometrically with
scale: distance-2 costs run 5, 6, 15, 18, 45, 52, 135, 150 up the chain
(≈ ×3 per scale); distance-3 costs 2, 3, 4, 5, 8, 9, 16. Interlocking
the chain cofinally means paying a geometrically growing restructuring
bill at every scale — quantified evidence that dense team hypergraphs
fight the covering constraint harder and harder.

**C — random thin bases have no protection at all.** Eight randomized
greedy order-2 coverings of [0,1200] (√-density): max guard-degree 0 in
every trial — not a single guarded target. Team structure never arises
generically; it requires deliberate digit-style design.

**D — caveat.** The naive cross-scale triple family (one small block +
three separated guards) cannot even maintain covering, so the exhaustive
clique search was vacuous in that family; cross-scale cliques remain
unobserved but also under-explored. A scaffolded family (chained blocks,
E-O style) is the right next vehicle.

**Verdict.** Every measurement points the same way: wild protection is
tree-structured and dodgeable, interlocking costs grow geometrically,
and generic thin bases have no protection whatsoever. A NO-construction
must beat geometric edge costs at infinitely many scales simultaneously
— nothing observed comes within sight of that. The dodge (choose an
independent set in the team forest) is now the concrete YES-side proof
strategy: prove team graphs of order-2 coverings are (eventually)
triangle-poor / degenerate, and the surviving deletion follows.
