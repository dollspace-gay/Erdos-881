# Literature relevant to Erdős problem 881

Last checked: 2026-08-03.

## Problem statement and status

The [Erdős Problems entry for problem 881](https://www.erdosproblems.com/881)
states the following question.

Let `A ⊆ ℕ` be an asymptotic additive basis of order `k`. Assume that for
every infinite `B ⊆ A`, the set `A \ B` is not an asymptotic basis of order
`k`. Must there be an infinite `B ⊆ A` such that `A \ B` is an asymptotic
basis of order `k + 1`?

The problem entry attributes the question to Erdős [Er98] and currently marks
it open. This repository does not claim a solution.

The hypothesis is often described as strong minimality under infinite
deletions or `ℵ₀`-minimality. It is stronger than ordinary minimality, which
only requires every proper subset, or equivalently every singleton deletion
in the standard setting, to destroy the original-order basis property.

## Early constructions

Erdős and Nathanson constructed `ℵ₀`-minimal order-two bases in:

- P. Erdős and M. B. Nathanson, “Oscillations of bases for the natural
  numbers,” *Proceedings of the American Mathematical Society* 53 (1975),
  253–258. [PDF](https://www.renyi.hu/~p_erdos/1975-29.pdf)

Their Theorem 2 constructs an order-two basis that remains a basis after every
finite deletion but ceases to be a basis after every infinite deletion. The
construction uses separated intervals and a prescribed sequence of exceptional
targets. It is directly relevant to the hypothesis of problem 881.

Nathanson’s binary digit construction gives a standard thin minimal basis of
order two. Related digit constructions provide useful exact test cases for
this repository, but behavior in those examples is not a proof of the general
problem.

## Deleting one element from an exact basis

The literature on essential elements and the order of a basis after a
singleton deletion is related but does not settle problem 881.

Relevant references include:

- P. Erdős and R. L. Graham, “On bases with an exact order,” *Acta
  Arithmetica* 37 (1980), 201–207.
- B. Deschamps and G. Grekos, “Estimation du nombre d’exceptions à ce qu’un
  ensemble de base privé d’un point reste un ensemble de base,” *Journal für
  die reine und angewandte Mathematik* 539 (2001), 45–53.
- J. Cassaigne and A. Plagne, “Grekos’ S function has a linear growth,”
  *Proceedings of the American Mathematical Society* 132 (2004), 2833–2840.
  [Bibliographic entry](https://www.cmls.polytechnique.fr/perso/plagne/publications.html)

These works bound the exceptional elements of an exact basis and the possible
exact order after removing a nonessential element. The equality `S(2) = 3`
describes the sharp singleton-deletion behavior for exact order-two bases. It
does not provide one infinite deletion, so it is not the `k = 2` case of
problem 881.

## Relation to the formal development

The repository’s order-two guardian and private-target results overlap in
subject with the singleton-deletion literature. No novelty claim should be
made for a local conclusion until it has been compared with the essential
element and `S(h)` literature.

The current formal route concerns simultaneous avoidance of an infinite
deletion. Its principal objects are:

- finite support families and their hitting sets;
- block selectors and finite target certificates;
- private supports attached to a marked element;
- exact-order changes under finite and infinite deletions.

The most relevant distinction is quantifier order. Singleton-deletion results
control one removed element at a time. Erdős 881 asks for one infinite set of
removed elements whose effects are controlled simultaneously.

## Claims not used as literature

Online comments or model-generated proof sketches are not treated as
published results. Any claimed solution should be checked against the exact
quantifiers in the problem and against the possibility that a cofinal target
sequence is not eventually exhaustive.

## Literature tasks

Before claiming a new general theorem, the following checks remain useful:

1. Compare private-target lemmas with the essential-element arguments of
   Erdős–Graham, Deschamps–Grekos, and Cassaigne–Plagne.
2. Compare the strong-minimality formulation in Lean with the `ℵ₀`-minimal
   construction in Erdős–Nathanson.
3. Search specifically for infinite simultaneous deletion results, rather than
   results about one or finitely many deleted elements.
4. Treat finite digit-basis experiments as tests of candidate lemmas, not as
   evidence of a universal conclusion.
