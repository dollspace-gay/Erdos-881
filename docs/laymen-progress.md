# Progress summary in non-specialist language

Last updated: 2026-08-03.

## The question

An additive basis of order `k` is a set of natural numbers from which every
sufficiently large number can be formed by adding exactly `k` members of the
set. Repeated summands are allowed.

Erdős problem 881 starts with a basis that is strongly minimal: deleting any
infinite subset stops it from being a basis of order `k`. It asks whether one
can nevertheless delete an infinite subset and retain a basis of order
`k + 1`.

The problem is not yet solved in this repository.

## The direct construction

The current approach tries to choose deleted elements one at a time.
Suppose that finitely many elements have already been selected for deletion.
An element is called cleanly redundant if it can also be deleted while every
sufficiently large target still has a representation avoiding all selected
elements.

If a cleanly redundant element can always be found, then the choices can be
continued indefinitely. This produces the required infinite deletion. Lean
has verified this construction.

Therefore the main question is what happens when no new cleanly redundant
element is available.

## What failure looks like

After the other formal alternatives have been separated, failure produces a
sequence of targets whose representations depend on marked basis elements.
These are called pinned targets. Minimizing the obstruction gives either:

- a lower-order obstruction, which may support induction on the order; or
- a private lower-order core attached to the marked element.

The private cores have bounded size. An infinite delta-system argument splits
them into a fixed common part and pairwise disjoint moving parts.

If infinitely many moving parts are nonempty, their union gives an infinite
set avoided by a cofinal sequence of representations. If the moving parts
eventually vanish, the common core and its target become fixed. This second
case also gives an infinite avoided set after the marker sequence is divided
into two infinite subsets.

The result is a sequence of large targets that survive one deletion, with
destroyed targets occurring between consecutive surviving targets.

## Why this is not yet enough

Having surviving targets arbitrarily far out does not mean that every
sufficiently large target survives. The basis property requires the latter.

The proof therefore partitions the deletion into finite blocks and studies
selectors that choose one element from each block. A finite selector
certificate is a finite set of targets such that every selector destroys at
least one of them.

The current theorem proves that, for every integer `C`, there is a later
certificate containing more than `C` targets. Each target can be isolated:
there is a selector that destroys that target while preserving all other
targets in the same certificate.

This is useful because a repair of an isolated target can be required to avoid
representations protecting all the other certificate targets. Such a repair
would preserve the entire certificate, which is impossible. Lean has verified
this argument.

## The remaining difficulty

The certificate for one bound `C` may be unrelated to the certificate for a
larger bound. Thus arbitrarily large finite certificates do not automatically
produce one coherent infinite object or one deletion preserving all late
targets.

Existing theorems classify the remaining certificate structure into three
cases involving rooted matchings, common-column covers, or lower-order
arithmetic concentration. The next task is to prove that every one of these
cases gives either:

- a genuine reduction to a smaller nontrivial order; or
- enough uniform redundancy to continue the direct deletion construction.

## How to read the project documents

Statements marked “proved” refer to Lean declarations. Statements marked
“computational observation” describe finite scripts and examples. Statements
marked “open” are proposed proof obligations. The detailed current statement
is in `docs/solution-status.md`.
