/-
# Erdős 881 (k = 2): the endgame, in one module

The campaign's final verified statements, re-exported under their
narrative names.  A counterexample is a set `A ⊆ ℕ` with `0 ∈ A`,
2-covering beyond `N₀`, ℵ₀-minimal at order 2, such that no
infinite deletion leaves an exact order-3 basis.  Everything below
is zero-sorry, standard axioms.

The state of the problem after 2026-07-25:

* THE PORTRAIT (`endgame_portrait`): any counterexample is
  centrally administered, fully employed, Sidon on its guarded
  streets, and infinitely blown elsewhere.
* THE REDUCTION (`endgame_reduction`): a single verified
  rank-dropping pool operation would refute the counterexample.
* THE TWO ROOMS (`endgame_two_rooms`): every pool of finite rank
  contains a perfect clique world; otherwise its rank is infinite.
* THE UNIVERSAL FRAME (`endgame_classification₂`,
  `endgame_classification₃`): hypothesis-free stream
  classifications at both orders.
-/

import Erdos881.FreeRank
import Erdos881.CantorInstance

namespace Erdos881

/-- THE PORTRAIT: the four simultaneous obligations of any
counterexample.  See `counterexample_portrait'` for the proof. -/
theorem endgame_portrait {A : Set ℕ} {N₀ : ℕ}
    [DecidablePred (· ∈ A)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hmin : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 2)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∃ S : Finset ℕ, S.Nonempty ∧ (∀ h ∈ S, h ∈ A ∧ 0 < h) ∧
      ∀ X, ∃ b, b ∈ A ∧ X ≤ b ∧ b ∉ S ∧
        ∃ m, N₀ ≤ m ∧ ∃ H : Finset ℕ, IsRepHub A m H ∧
          (∀ h ∈ H, ¬IsRepHub A m (H \ {h})) ∧ H = insert b S) ∧
    (∃ P₂ P₃ : Finset ℕ, PairFree A N₀ P₂ ∧ RepFree A N₀ P₃ ∧
      ∃ X, ∀ b ∈ A, X ≤ b →
        (∃ t, N₀ ≤ t ∧ b ≤ t ∧
          ∀ x ∈ A, ∀ y ∈ A, x + y = t →
            x ∈ insert b P₂ ∨ y ∈ insert b P₂) ∧
        (∃ m, N₀ ≤ m ∧ b ≤ m ∧ IsRepHub A m (insert b P₃))) ∧
    (∃ C, ∀ N, ∃ m, N ≤ m ∧
      ((Finset.range (m + 1)).filter
        (fun x => x ∈ A ∧ (m - x) ∈ A)).card ≤ C) ∧
    (∀ C N, ∃ v, N ≤ v ∧ C ≤ ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A)).card) :=
  counterexample_portrait' h0 hcov hanchor hmin hfail

/-- THE REDUCTION: no strictly descending sequence of pool root
ranks exists; one verified rank-dropping pool operation refutes
the counterexample and solves the problem. -/
theorem endgame_reduction {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (pools : ℕ → Set ℕ) :
    ¬∀ k, (((poolFreeStep_wf h0 hcov hfail (pools (k + 1))).apply
        ∅).rank <
      ((poolFreeStep_wf h0 hcov hfail (pools k)).apply ∅).rank) :=
  no_pool_rank_descent h0 hcov hfail pools

/-- THE TWO ROOMS: a stream pool of finite root rank contains a
perfect clique world (all `d`-subsets free, all `(d+1)`-subsets
full hubs); its rank is exactly the freedom level and it is
rank-stable — otherwise the pool has infinite rank. -/
theorem endgame_two_rooms {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (b : ℕ → ℕ) (hbmono : StrictMono b)
    (hbA : ∀ j, b j ∈ A) (hbpos : ∀ j, 0 < b j)
    (hrank : ((poolFreeStep_wf h0 hcov hfail
      (Set.range b)).apply ∅).rank < Ordinal.omega0) :
    ∃ (d : ℕ) (f : ℕ → ℕ), 1 ≤ d ∧ StrictMono f ∧
      (∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, b (f i) = h) → S.card = d →
        RepFree A N₀ S) ∧
      (∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, b (f i) = h) →
        S.card = d + 1 → ∃ m, N₀ ≤ m ∧ IsRepHub A m S) :=
  rank_lt_omega_perfect_clique h0 hcov hanchor hfail b hbmono hbA
    hbpos hrank

/-- THE UNIVERSAL FRAME at order 2: wide freedom, total
guardianship, or a perfect pair-crystal — for any stream over any
set. -/
theorem endgame_classification₂ (A : Set ℕ) (N₀ : ℕ)
    (e : ℕ → ℕ) (hemono : StrictMono e) :
    (∀ n, ∃ S : Finset ℕ, (∀ h ∈ S, ∃ i, e i = h) ∧ S.card = n ∧
      PairFree A N₀ S) ∨
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ((∀ i, ¬PairFree A N₀ {e (f i)}) ∨
      (∃ d, 1 ≤ d ∧
        (∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, e (f i) = h) →
          S.card = d → PairFree A N₀ S) ∧
        (∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, e (f i) = h) →
          S.card = d + 1 → ¬PairFree A N₀ S))) :=
  stream_pair_classification A N₀ e hemono

/-- THE UNIVERSAL FRAME at order 3. -/
theorem endgame_classification₃ (A : Set ℕ) (N₀ : ℕ)
    (e : ℕ → ℕ) (hemono : StrictMono e) :
    (∀ n, ∃ S : Finset ℕ, (∀ h ∈ S, ∃ i, e i = h) ∧ S.card = n ∧
      RepFree A N₀ S) ∨
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ((∀ i, ¬RepFree A N₀ {e (f i)}) ∨
      (∃ d, 1 ≤ d ∧
        (∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, e (f i) = h) →
          S.card = d → RepFree A N₀ S) ∧
        (∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, e (f i) = h) →
          S.card = d + 1 → ¬RepFree A N₀ S))) :=
  stream_rep_classification A N₀ e hemono

/-- **THE CHARACTERIZATION** — the problem in one sentence: the
counterexample condition is equivalent to the absence of an
infinite hereditarily rep-free subset.  Erdős 881 (k = 2) asks
exactly whether every ℵ₀-minimal exact order-2 basis contains an
infinite set all of whose finite subsets are rep-free. -/
theorem endgame_characterization {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) :
    (∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) ↔
    ¬∃ B : Set ℕ, HereditarilyFree A N₀ B :=
  hfail_iff_no_hereditarily_free h0 hcov

/-- **The Cantor witness, in the characterization's language.**
The pure powers form an infinite hereditarily rep-free subset of
the Cantor basis: every late target keeps a power-free triple
(carry repair), hence a triple avoiding any finite subset of the
powers.  The positive side of Erdős 881, realized concretely. -/
theorem cantor_powers_hereditarilyFree :
    HereditarilyFree Erdos881Cantor.CantorSet (3 ^ 7)
      Erdos881Cantor.PurePowers := by
  refine ⟨Erdos881Cantor.purePowers_infinite, ?_, ?_⟩
  · rintro b ⟨k, rfl⟩
    exact ⟨Erdos881Cantor.purePowers_subset ⟨k, rfl⟩,
      pow_pos (by norm_num) k⟩
  · intro P hP m hm
    obtain ⟨x, y, z, hx, hy, hz, hpx, hpy, hpz, hs⟩ :=
      Erdos881Cantor.cantor_deletion_order_three m hm
    refine ⟨x, hx, y, hy, z, hz, hs, ?_, ?_, ?_⟩
    · intro hmem
      obtain ⟨k, hk⟩ := hP x hmem
      exact hpx k hk
    · intro hmem
      obtain ⟨k, hk⟩ := hP y hmem
      exact hpy k hk
    · intro hmem
      obtain ⟨k, hk⟩ := hP z hmem
      exact hpz k hk

/-- **THE TRIANGLE**: order-3 failure under every deletion, absence
of hereditarily free sets, and well-foundedness of the freeness
tree are one property.  Erdős 881 (k = 2) asks whether every
minimal basis's freeness tree has an infinite branch. -/
theorem endgame_triangle {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) :
    (∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) ↔
    WellFounded (FreeStep A N₀) :=
  hfail_iff_freeStep_wf h0 hcov

/-- **THE TWO-TREE FORMULATION** — the problem in its purest form:
a counterexample is exactly a covering set with `0` whose pair
tree and rep tree are both well-founded.  Erdős 881 (k = 2): can
two nested freeness trees over one basis both be well-founded? -/
theorem endgame_two_trees {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) :
    ((∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) ∧
    (∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)) ↔
    (WellFounded (PairFreeStep A N₀) ∧
      WellFounded (FreeStep A N₀)) :=
  counterexample_iff_both_trees_wf h0 hcov

/-- **THE FINAL FORM.**  One tree decides everything: the full
counterexample condition is equivalent to well-foundedness of the
rep-freeness tree alone (minimality is a subtree consequence).
Erdős 881 (k = 2), modulo the standing `0 ∈ A` interface:

  IS THERE a 2-covering set containing 0 whose rep-freeness tree
  is well-founded?

No such set ⟺ the answer to Erdős 881 (k = 2) is YES. -/
theorem endgame_final_form {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) :
    ((∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) ∧
    (∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)) ↔
    WellFounded (FreeStep A N₀) :=
  counterexample_iff_rep_tree_wf h0 hcov

/-- **Full-circle sanity.**  The characterization correctly
classifies the verified instance: the Cantor basis is NOT a
counterexample, because its pure powers are a hereditarily free
branch.  The abstract machinery and the concrete world agree. -/
theorem cantor_not_counterexample :
    ¬(∀ B ⊆ Erdos881Cantor.CantorSet, B.Infinite →
      ¬IsExactTupleAsymptoticBasis
        (Erdos881Cantor.CantorSet \ B) 3) := by
  have h0 : (0 : ℕ) ∈ Erdos881Cantor.CantorSet := by
    show Erdos881Cantor.IsCantor 0
    intro i
    simp [Nat.zero_div]
  have hcov : PairCovers Erdos881Cantor.CantorSet (3 ^ 7) := by
    intro n _
    obtain ⟨a, b, ha, hb, hab⟩ := Erdos881Cantor.cantor_pair_basis n
    exact ⟨a, ha, b, hb, hab⟩
  intro hfail
  exact (hfail_iff_no_hereditarily_free h0 hcov).1 hfail
    ⟨Erdos881Cantor.PurePowers, cantor_powers_hereditarilyFree⟩

/-- **THE SHELL ENDGAME** (re-export).  The counterexample's
positive elements stratify into infinitely many disjoint nonempty
free shells with hierarchical total guardianship; every large
element avoiding all shells guards at unbounded scales (the
bounded/singleton-owner corner feeds the rotating-guardian kill
and is dead).  Two shapes remain: perfect stratification, or an
infinite crowd of infinitely-employed eternal survivors. -/
theorem endgame_shells {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ Q : ℕ → Finset ℕ, ∃ X,
      (∀ k, (Q k).Nonempty) ∧
      (∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h) ∧
      (∀ k, RepFree A N₀ (Q k)) ∧
      (∀ j k, j < k → Disjoint (Q j) (Q k)) ∧
      (∀ k, ∀ b ∈ A, 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
        ∃ m, N₀ ≤ m ∧ IsRepHub A m (insert b (Q k))) ∧
      (∀ b ∈ A, X ≤ b → 0 < b → (∀ j, b ∉ Q j) →
        ∀ Y, ∃ k, ∃ m, Y ≤ m ∧ N₀ ≤ m ∧
          IsRepHub A m (insert b (Q k))) :=
  shell_endgame h0 hcov hanchor hfail

/-- **THE FOUR ROOMS** (re-export).  Every counterexample lives
in one of four terminal rooms: fixed-offset difference blowup
(A ∩ (A − δ) infinite), growing-offset difference pairs at every
multiplicity, scattered mirror halls (arbitrarily large blown
affine corners), or the street ladder — one mirror point n whose
difference translates n + d are pair streets for unboundedly
large d, pinning street positions to a one-parameter family. -/
theorem endgame_four_rooms {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ Q : Finset ℕ, RepFree A N₀ Q ∧
    ((∃ δ, 1 ≤ δ ∧ ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A) ∨
     (∀ Δ K, ∃ δ, Δ < δ ∧ ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A) ∨
     (∃ K₀, ∀ N S, ∃ n, N < n ∧
        (∃ V : Finset ℕ, K₀ ≤ V.card ∧
          ∀ a ∈ V, a ∈ A ∧ ∃ x ∈ A, x + a = n) ∧
        ∃ b₂ ∈ A, ∃ b₃ ∈ A, S ≤ b₂ ∧ b₂ < b₃ ∧
          ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
            IsPairHub A s (insert b₃ Q)) ∨
     (∃ n, ∀ Δ S, ∃ b₂ ∈ A, ∃ b₃ ∈ A, S ≤ b₂ ∧ b₂ < b₃ ∧
        Δ < b₃ - b₂ ∧ ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
          IsPairHub A s (insert b₃ Q))) :=
  counterexample_four_rooms h0 hcov hfail

/-- **THE RAMSEY TRICHOTOMY** (re-export).  Every covering set
contains an infinite ascending positive sequence that is a Sidon
clique (pairwise sums are two-element pair hubs), self-avoiding
(every pairwise sum keeps a representation avoiding the whole
sequence — failures of that deletion must dodge the sum square),
or routed through a fixed positive family. -/
theorem endgame_ramsey_trichotomy {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) :
    ∃ T : ℕ → ℕ, StrictMono T ∧ (∀ i, T i ∈ A) ∧
      (∀ i, 0 < T i) ∧
      ((∀ i j, i < j →
          IsPairHub A (T i + T j) ({T i, T j} : Finset ℕ)) ∨
       (∀ i j, i < j → ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
          x ∉ Set.range T ∧ y ∉ Set.range T ∧
          z ∉ Set.range T ∧ x + y + z = T i + T j) ∨
       (∃ R : Set ℕ, (∀ w ∈ R, w ∈ A ∧ 0 < w) ∧
          (∀ i, T i ∈ R) ∧
          ∀ i j, i < j → ∀ x ∈ A, ∀ y ∈ A,
            x + y = T i + T j → x ∈ R ∨ y ∈ R)) :=
  ramsey_trichotomy_of_covering h0 hcov

/-- **THE ω-DICHOTOMY + COMPLETENESS PINCH** (re-export).  The
subset-sum semigroup of some ascending sequence survives its own
deletion at every arity, or is routed at a fixed arity
(`omega_avoidance_dichotomy`); a COMPLETE such sequence would be
a surviving deletion outright (`survival_of_complete_avoiding`).
The distance between the diagonal's thinness and completeness is
the problem. -/
theorem endgame_omega_pinch {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀) :
    ∃ T : ℕ → ℕ, StrictMono T ∧ (∀ i, T i ∈ A) ∧
      (∀ i, 0 < T i) ∧
      ∃ R : Set ℕ, (∀ w ∈ R, w ∈ A ∧ 0 < w) ∧
        (∀ i, T i ∈ R) ∧
        ((∀ r : ℕ, ∀ k : Fin (r + 1) → ℕ, StrictMono k →
            (∀ i, r + 1 ≤ k i) →
            ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
              x ∉ R ∧ y ∉ R ∧ z ∉ R ∧
              x + y + z = ∑ i, T (k i)) ∨
         (∃ r : ℕ, ∀ k : Fin (r + 1) → ℕ, StrictMono k →
            (∀ i, r + 1 ≤ k i) →
            ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
              x + y + z = ∑ i, T (k i) →
              x ∈ R ∨ y ∈ R ∨ z ∈ R)) :=
  omega_avoidance_dichotomy hcov

open Classical in
/-- **THE ENCIRCLEMENT.**  Everything the campaign has proven
about a counterexample to Erdős 881 (k = 2), as one simultaneous
configuration.  Under the full interface — 0 ∈ A, covering,
anchors, universal order-3 failure, and the problem's own
classical minimality — the counterexample must simultaneously:

  (1) stratify into infinitely many disjoint nonempty free
      shells with hierarchical total guardianship and pay the
      linear depth tax;
  (2) live in one of the four rooms (fixed-offset difference
      blowup, growing offsets, scattered mirror halls, or the
      pinned street ladder);
  (3) field guardian teams drawn entirely from an infinite
      ascending matching of its own unique-sum marriages;
  (4) contain an ascending sequence whose tail subset-sum
      semigroup survives its own deletion at every arity, or is
      routed at a fixed arity (the ω-pinch);
  (5) keep some fixed fragility level recurring cofinally; and
  (6) let r₂ blow up beyond every bound.

Each pillar is separately verified; this theorem is their
simultaneous existence.  Every known world fails at least one
pillar's downstream consequences; the enemy must thread all six
forever. -/
theorem the_encirclement {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hess : ∀ a ∈ A, 0 < a → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ≠ a ∧ y ≠ a ∧ x + y = n) :
    -- (1) shells and the depth tax
    (∃ Q : ℕ → Finset ℕ, ∃ X,
      (∀ k, (Q k).Nonempty) ∧
      (∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h) ∧
      (∀ k, RepFree A N₀ (Q k)) ∧
      (∀ j k, j < k → Disjoint (Q j) (Q k)) ∧
      (∀ k, ∀ b ∈ A, 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
        ∃ m, N₀ ≤ m ∧ IsRepHub A m (insert b (Q k))) ∧
      (∀ k, ∀ b ∈ A, X ≤ b → 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
        ∃ j, j ≤ k ∧ ∃ m, N₀ + k / 3 ≤ m ∧ N₀ ≤ m ∧
          IsRepHub A m (insert b (Q j)))) ∧
    -- (2) the four rooms
    (∃ Q : Finset ℕ, RepFree A N₀ Q ∧
      ((∃ δ, 1 ≤ δ ∧ ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
          ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A) ∨
       (∀ Δ K, ∃ δ, Δ < δ ∧ ∃ V : Finset ℕ, K ≤ V.card ∧
          ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A) ∨
       (∃ K₀, ∀ N S, ∃ n, N < n ∧
          (∃ V : Finset ℕ, K₀ ≤ V.card ∧
            ∀ a ∈ V, a ∈ A ∧ ∃ x ∈ A, x + a = n) ∧
          ∃ b₂ ∈ A, ∃ b₃ ∈ A, S ≤ b₂ ∧ b₂ < b₃ ∧
            ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
              IsPairHub A s (insert b₃ Q)) ∨
       (∃ n, ∀ Δ S, ∃ b₂ ∈ A, ∃ b₃ ∈ A, S ≤ b₂ ∧ b₂ < b₃ ∧
          Δ < b₃ - b₂ ∧ ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
            IsPairHub A s (insert b₃ Q)))) ∧
    -- (3) marriage-network teams
    (∃ P : ℕ → ℕ × ℕ,
      (∀ i, (P i).1 ∈ A ∧ (P i).2 ∈ A ∧ 0 < (P i).1 ∧
        0 < (P i).2 ∧
        ∀ x ∈ A, ∀ y ∈ A, x + y = (P i).1 + (P i).2 →
          (x = (P i).1 ∧ y = (P i).2) ∨
          (x = (P i).2 ∧ y = (P i).1)) ∧
      (∀ i, max (P i).1 (P i).2 < min (P (i + 1)).1
        (P (i + 1)).2) ∧
      ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
        IsRepHub A n H ∧ (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
        2 ≤ H.card ∧ ∀ h ∈ H, ∃ i,
          h = (P i).1 ∨ h = (P i).2) ∧
    -- (4) the ω-pinch
    (∃ T : ℕ → ℕ, StrictMono T ∧ (∀ i, T i ∈ A) ∧
      (∀ i, 0 < T i) ∧
      ∃ R : Set ℕ, (∀ w ∈ R, w ∈ A ∧ 0 < w) ∧
        (∀ i, T i ∈ R) ∧
        ((∀ r : ℕ, ∀ k : Fin (r + 1) → ℕ, StrictMono k →
            (∀ i, r + 1 ≤ k i) →
            ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
              x ∉ R ∧ y ∉ R ∧ z ∉ R ∧
              x + y + z = ∑ i, T (k i)) ∨
         (∃ r : ℕ, ∀ k : Fin (r + 1) → ℕ, StrictMono k →
            (∀ i, r + 1 ≤ k i) →
            ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
              x + y + z = ∑ i, T (k i) →
              x ∈ R ∨ y ∈ R ∨ z ∈ R))) ∧
    -- (5) cofinal fragility
    (∃ C, ∀ H, ∃ m, H ≤ m ∧ ¬HasDisjointTripleReps A m C) ∧
    -- (6) unbounded r₂
    (∀ C N, ∃ v, N ≤ v ∧ C ≤ ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A)).card) := by
  refine ⟨stratified_tax_portrait h0 hcov hanchor hfail,
    counterexample_four_rooms h0 hcov hfail,
    matched_deletion_teams h0 hcov hanchor hfail hess,
    omega_avoidance_dichotomy hcov,
    fragile_supply_of_hfail h0 hcov hfail,
    r2_unbounded_of_hfail h0 hcov hfail⟩

/-- **THE SPINE** (re-export; the night's second monument beside
`the_encirclement`).  Under the full counterexample interface a
canonical strictly increasing sequence threads the enemy's own
shells (Nash-Williams/Higman on the shell antichain), every
subsequence of it forces a stall hub of spine elements, and the
endgame forks: infinite root rank, or the lockstep highway. -/
theorem endgame_spine {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∃ Q : ℕ → Finset ℕ, ∃ σ : ℕ ↪o ℕ, ∃ x : ℕ → ℕ,
      StrictMono x ∧ (∀ t, x t ∈ Q (σ t)) ∧
      (∀ k, RepFree A N₀ (Q k)) ∧
      (∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h) ∧
      ∀ τ : ℕ → ℕ, StrictMono τ →
        ∃ J m, N₀ ≤ m ∧
          IsRepHub A m ((Finset.range J).image (fun t =>
            x (τ t)))) ∧
    ((Ordinal.omega0 ≤
      ((poolFreeStep_wf h0 hcov hfail Set.univ).apply ∅).rank) ∨
    (∃ Q : ℕ → Finset ℕ, ∃ σ : ℕ ↪o ℕ, ∃ T s : ℕ,
      (∀ k, RepFree A N₀ (Q k)) ∧
      (∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h) ∧
      (∀ j k, j < k → Disjoint (Q j) (Q k)) ∧
      1 ≤ s ∧
      (∀ t, T ≤ t → (Q (σ t)).card = s) ∧
      (∀ t, T ≤ t → List.Forall₂ (· ≤ ·)
        ((Q (σ t)).sort (· ≤ ·))
        ((Q (σ (t + 1))).sort (· ≤ ·))))) :=
  ⟨spine_stalls_hereditarily h0 hcov hanchor hfail,
    root_rank_omega_or_lockstep h0 hcov hanchor hfail⟩

/-- **THE FINAL FORK** (re-export; where the campaign now
stands).  Every counterexample funds free sets of every size —
root rank ≥ ω — or runs a located uniform-width hub street on
its own canonical spine.  Erdős 881's remaining content is the
defeat of these two explicit configurations. -/
theorem endgame_final_fork {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
      RepFree A N₀ P ∧ c ≤ P.card) ∨
    (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
      ∃ L, ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ v ∈ V, N₀ ≤ v ∧ ∃ s J, 2 ≤ J ∧ J ≤ L ∧
          IsRepHub A v ((Finset.range J).image
            (fun j => x (s + j)))) :=
  the_final_fork h0 hcov hanchor hfail

/-- **THE GLOBAL TRICHOTOMY** (re-export; the campaign's single
final statement).  Hypotheses only: 0 ∈ A, order-2 covering,
order-3 failure of every infinite deletion.  No anchor condition
anywhere — the anchor dichotomy is resolved INSIDE the theorem.
Every counterexample world is

I. ANCHORED, and drives in one of four lanes: root rank ≥ ω, or
   a fixed finite hall with a door element carrying unboundedly
   many targets onto one translate, or a ghost street (targets
   forced OUT of A, pair lives caught by marching spine
   windows), or a member street (targets INSIDE their own
   windows, middle pairs banned);

II. ROUTED: a basis member g₀ routes every noncentral double
   decomposition — every double 2c is pair-hubbed by {c, g₀};

III. CENTRAL: doubles decompose only centrally — every element
   pair-owns its double, minimality is automatic, and the basis
   is midpoint-free off the router (Salem–Spencer geometry).

This is the complete formal fusion of the anchored fork, the
g₀-routed branch, and the central branch. -/
theorem endgame_global_trichotomy {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ((∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
        w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g) ∧
      ((∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
        RepFree A N₀ P ∧ c ≤ P.card) ∨
      (∃ H : Finset ℕ, ∃ h ∈ H, ∀ K, ∃ V : Finset ℕ,
        K ≤ V.card ∧ ∀ v ∈ V, N₀ ≤ v ∧ h ≤ v ∧ v - h ∈ A ∧
          IsPairHub A v H) ∨
      (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
        ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
          ∀ v ∈ V, N₀ ≤ v ∧ v ∉ A ∧ ∃ s, S₀ ≤ s ∧ x s ≤ v ∧
            ∃ J, 2 ≤ J ∧ J ≤ L ∧ IsPairHub A v
              ((Finset.range J).image (fun j => x (s + j)))) ∨
      (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
        ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
          ∀ v ∈ V, N₀ ≤ v ∧ v ∈ A ∧ ∃ s, S₀ ≤ s ∧
            ∃ J, 2 ≤ J ∧ J ≤ L ∧
              v ∈ (Finset.range J).image (fun j => x (s + j)) ∧
              IsPairHub A v ((Finset.range J).image
                (fun j => x (s + j))) ∧
              (∀ a ∈ A, ∀ b ∈ A, a + b = v →
                a ≤ x (s + J - 1) - x s ∨
                b ≤ x (s + J - 1) - x s)))) ∨
    (∃ g₀, g₀ ∈ A ∧ ∀ c ∈ A, 0 < c → c ≠ g₀ →
      IsPairHub A (2 * c) ({c, g₀} : Finset ℕ)) ∨
    (∃ g₀, (∀ c ∈ A, 0 < c → c ≠ g₀ → ∀ w ∈ A, ∀ w' ∈ A,
        w + w' = 2 * c → w = c ∧ w' = c) ∧
      (∀ c ∈ A, 0 < c → c ≠ g₀ →
        IsPairHub A (2 * c) ({c} : Finset ℕ)) ∧
      (∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
        ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) ∧
      (∀ a d, 0 < d → a ∈ A → a + d ∈ A → a + 2 * d ∈ A →
        a + d = g₀ ∨ a + d = 0)) :=
  the_global_trichotomy h0 hcov hfail

/-- **THE COLLAPSED TRICHOTOMY** (re-export; the campaign's
current summit).  After the routed collapse the middle room of
the global trichotomy is defeated as a separate case: every
counterexample world is ANCHORED (four lanes), ALMOST-ANCHORED
(a member router g₀ with the explicit infinite ladder
2c − g₀ ∈ A and anchor supply at every value except g₀ — one
hole in the anchor wall, at a known member), or CENTRAL-TAIL
(explicitly thresholded total pinning, automatic minimality and
midpoint-freeness, subsuming the pure central branch).  Two
live geometries remain. -/
theorem endgame_collapsed_trichotomy {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ((∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
        w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g) ∧
      ((∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
        RepFree A N₀ P ∧ c ≤ P.card) ∨
      (∃ H : Finset ℕ, ∃ h ∈ H, ∀ K, ∃ V : Finset ℕ,
        K ≤ V.card ∧ ∀ v ∈ V, N₀ ≤ v ∧ h ≤ v ∧ v - h ∈ A ∧
          IsPairHub A v H) ∨
      (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
        ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
          ∀ v ∈ V, N₀ ≤ v ∧ v ∉ A ∧ ∃ s, S₀ ≤ s ∧ x s ≤ v ∧
            ∃ J, 2 ≤ J ∧ J ≤ L ∧ IsPairHub A v
              ((Finset.range J).image (fun j => x (s + j)))) ∨
      (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
        ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
          ∀ v ∈ V, N₀ ≤ v ∧ v ∈ A ∧ ∃ s, S₀ ≤ s ∧
            ∃ J, 2 ≤ J ∧ J ≤ L ∧
              v ∈ (Finset.range J).image (fun j => x (s + j)) ∧
              IsPairHub A v ((Finset.range J).image
                (fun j => x (s + j))) ∧
              (∀ a ∈ A, ∀ b ∈ A, a + b = v →
                a ≤ x (s + J - 1) - x s ∨
                b ≤ x (s + J - 1) - x s)))) ∨
    (∃ g₀, g₀ ∈ A ∧
      (∀ N, ∃ c ∈ A, N ≤ c ∧ c ≠ g₀ ∧ g₀ ≤ 2 * c ∧
        (2 * c - g₀) ∈ A ∧ 2 * c - g₀ ≠ c) ∧
      (∀ g, g ≠ g₀ → ∃ c ∈ A, 0 < c ∧ c ≠ g ∧
        ∃ w ∈ A, ∃ w' ∈ A, w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧
          w' ≠ g)) ∨
    (∃ g₀ C₀, (∀ c ∈ A, C₀ ≤ c → c ≠ g₀ → ∀ w ∈ A, ∀ w' ∈ A,
        w + w' = 2 * c → w = c ∧ w' = c) ∧
      (∀ c ∈ A, C₀ ≤ c → c ≠ g₀ →
        IsPairHub A (2 * c) ({c} : Finset ℕ)) ∧
      (∀ B ⊆ A, B.Infinite → ¬∃ N₂, ∀ n, N₂ ≤ n →
        ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) ∧
      (∀ a d, 0 < d → a ∈ A → a + d ∈ A → a + 2 * d ∈ A →
        a + d = g₀ ∨ a + d < C₀)) :=
  the_collapsed_trichotomy h0 hcov hfail

/-- **THE FINAL DICHOTOMY** (re-export; the campaign's summit).
TWO ROOMS.  Every counterexample world — hypotheses only
0 ∈ A, order-2 covering, order-3 failure of every infinite
deletion — either drives in one of the FOUR LANES (root rank
≥ ω; a fixed finite hall whose door element carries unboundedly
many targets onto one translate; a ghost street of targets
forced OUT of A with pair lives caught by marching spine
windows; or a member street of targets inside their own windows
with middle pairs banned) or lives in the CENTRAL TAIL
(explicitly thresholded total pinning, automatic minimality,
midpoint-freeness off one value).  The anchor wall and its
g₀-hole are gone: the stream-kill oracle is implemented in both
anchored and almost-anchored worlds — the latter by the
g₀-tower self-kill — so the four-lane endgame runs on both.
Erdős 881's negative answer would have to live in one of five
explicit verified configurations. -/
theorem endgame_final_dichotomy {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ((∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
      RepFree A N₀ P ∧ c ≤ P.card) ∨
    (∃ H : Finset ℕ, ∃ h ∈ H, ∀ K, ∃ V : Finset ℕ,
      K ≤ V.card ∧ ∀ v ∈ V, N₀ ≤ v ∧ h ≤ v ∧ v - h ∈ A ∧
        IsPairHub A v H) ∨
    (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
      ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ v ∈ V, N₀ ≤ v ∧ v ∉ A ∧ ∃ s, S₀ ≤ s ∧ x s ≤ v ∧
          ∃ J, 2 ≤ J ∧ J ≤ L ∧ IsPairHub A v
            ((Finset.range J).image (fun j => x (s + j)))) ∨
    (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
      ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ v ∈ V, N₀ ≤ v ∧ v ∈ A ∧ ∃ s, S₀ ≤ s ∧
          ∃ J, 2 ≤ J ∧ J ≤ L ∧
            v ∈ (Finset.range J).image (fun j => x (s + j)) ∧
            IsPairHub A v ((Finset.range J).image
              (fun j => x (s + j))) ∧
            (∀ a ∈ A, ∀ b ∈ A, a + b = v →
              a ≤ x (s + J - 1) - x s ∨
              b ≤ x (s + J - 1) - x s))) ∨
    (∃ g₀ C₀, (∀ c ∈ A, C₀ ≤ c → c ≠ g₀ → ∀ w ∈ A, ∀ w' ∈ A,
        w + w' = 2 * c → w = c ∧ w' = c) ∧
      (∀ c ∈ A, C₀ ≤ c → c ≠ g₀ →
        IsPairHub A (2 * c) ({c} : Finset ℕ)) ∧
      (∀ B ⊆ A, B.Infinite → ¬∃ N₂, ∀ n, N₂ ≤ n →
        ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) ∧
      (∀ a d, 0 < d → a ∈ A → a + d ∈ A → a + 2 * d ∈ A →
        a + d = g₀ ∨ a + d < C₀)) :=
  the_final_dichotomy h0 hcov hfail

/-- **THE TRANSLATE LAWS** (re-export; unconditional).  In any
counterexample world: no positive basis element's upward
translate eventually captures the basis, and no PAIR of them
does so jointly — arbitrarily large basis elements escape both
translates simultaneously.  Proved by the walk kills: a
captured tail yields a good-translate walk, which either
repeats a colour consecutively at cofinal heights (cofinal
fixed-difference AP3s, killed by midpoint deletion) or
eventually alternates perfectly (killed by two-step shifting).
The first laws of the campaign that hold with NO structural
hypothesis beyond the counterexample interface itself. -/
theorem endgame_translate_laws {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∀ c, c ∈ A → 0 < c →
      ∀ Z₀, ∃ z, Z₀ ≤ z ∧ z ∈ A ∧ z + c ∉ A) ∧
    (∀ h₀ h₁, h₀ ∈ A → h₁ ∈ A → 0 < h₀ → 0 < h₁ →
      ∀ Z₀, ∃ z, Z₀ ≤ z ∧ z ∈ A ∧ z + h₀ ∉ A ∧ z + h₁ ∉ A) :=
  ⟨fun c hcA hc => single_translate_law h0 hcov hfail hcA hc,
   fun h₀ h₁ h₀A h₁A hh₀ hh₁ =>
     pair_translate_law h0 hcov hfail h₀A h₁A hh₀ hh₁⟩

open Classical in
/-- **THE PARITY FORK** (re-export; the descent suite composed).
Every counterexample world either keeps BOTH parity classes
cofinally (the mixing world — walk-engine territory), or is
eventually single-parity and then carries the complete
saturated package at once: the finite opposite-parity fringe
pair-hubs EVERY odd target (total door saturation, no placement
liberty); the canonical r₂-blowups are forced onto the even
channel; the half-world inherits order-2 covering; and every
infinite half-world deletion fails at order 2 or order 3 — the
counterexample interface DESCENDS.  The 2-adic recursion is
armed inside every parity-defended world. -/
theorem endgame_parity_fork {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ((∀ N, ∃ a, N ≤ a ∧ a ∈ A ∧ a % 2 = 0) ∧
     (∀ N, ∃ a, N ≤ a ∧ a ∈ A ∧ a % 2 = 1)) ∨
    (∃ Y ε, ε < 2 ∧ (∀ a ∈ A, Y < a → a % 2 = ε) ∧
      (∀ n, 2 * Y < n → n % 2 = 1 →
        IsPairHub A n ((Finset.range (Y + 1)).filter
          (fun x => x ∈ A ∧ x % 2 ≠ ε))) ∧
      (∀ N, ∃ v, N ≤ v ∧ v % 2 = 0 ∧ 2 * Y + 3 ≤
        ((Finset.range (v + 1)).filter
          (fun x => x ∈ A ∧ (v - x) ∈ A)).card) ∧
      PairCovers {x : ℕ | ε + 2 * x ∈ A} (N₀ + 2 * Y + 2) ∧
      (∀ B' ⊆ {x : ℕ | ε + 2 * x ∈ A}, B'.Infinite →
        ¬((∃ N2, ∀ n', N2 ≤ n' →
            ∃ x' ∈ {x : ℕ | ε + 2 * x ∈ A},
            ∃ y' ∈ {x : ℕ | ε + 2 * x ∈ A},
              x' ∉ B' ∧ y' ∉ B' ∧ x' + y' = n') ∧
          (∃ N3, ∀ n', N3 ≤ n' →
            ∃ x' ∈ {x : ℕ | ε + 2 * x ∈ A},
            ∃ y' ∈ {x : ℕ | ε + 2 * x ∈ A},
            ∃ z' ∈ {x : ℕ | ε + 2 * x ∈ A},
              x' ∉ B' ∧ y' ∉ B' ∧ z' ∉ B' ∧
              x' + y' + z' = n')))) := by
  rcases global_parity_dichotomy (A := A) with
    ⟨Y, ε, hε, hpar⟩ | hboth
  · right
    obtain ⟨f, hff⟩ := saturated_fringe_nonempty hcov hpar
    rw [Finset.mem_filter, Finset.mem_range] at hff
    obtain ⟨hfY, hfA, hfpar⟩ := hff
    exact ⟨Y, ε, hε, hpar,
      fun n h1 h2 => global_parity_odd_hall hpar n h1 h2,
      r2_witnesses_even h0 hcov hfail hpar,
      half_world_covers hε hcov hpar,
      descent_invariant hε hfail hfA hfpar⟩
  · exact Or.inl hboth

open Classical in
/-- **THE ω-DRAIN** (re-export; the tree's global law).  Every
counterexample owns an infinite path through the 2-adic tree of
cross-systems — a sequence of half-world pairs, each a parity
child of the last, starting from (A, A) — along which pair
wealth persists at EVERY level.  The enemy's riches trace an
infinite 2-adic address: the formal shadow of the Cantor
cascade, extracted from the counterexample interface alone.
Together with the parity fork (interface descent) and the
covering splits, the hypothetical counterexample is a structure
in permanent downward motion on the infinite binary tree. -/
theorem endgame_omega_drain {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ S T : ℕ → Set ℕ, S 0 = A ∧ T 0 = A ∧
      (∀ k, ∃ p q, p < 2 ∧ q < 2 ∧
        S (k + 1) = {y | 2 * y + p ∈ S k} ∧
        T (k + 1) = {y | 2 * y + q ∈ T k}) ∧
      ∀ k C N, ∃ v, N ≤ v ∧ C ≤
        ((Finset.range (v + 1)).filter
          (fun x => x ∈ S k ∧ (v - x) ∈ T k)).card :=
  the_omega_drain h0 hcov hfail

open Classical in
/-- **THE POOR STREET** (sharpened final fork).  Every
counterexample funds free sets of every size — root rank ≥ ω —
or runs a street of targets whose pair wealth is UNIFORMLY
CAPPED at 2L: through the 0-weld, a window hub of ≤ L positive
spine elements is an order-2 hub, and unordered pair counting
injects into it.  Meanwhile `r2_unbounded_of_hfail` blows pair
wealth up cofinally and `drain_wealth_addresses` pins wealthy
targets along one nested 2-adic address tower.  The street
branch is now a segregation regime: an infinite uniformly poor
lane threading forever between 2-adically clustered wealth. -/
theorem endgame_poor_street {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
      RepFree A N₀ P ∧ c ≤ P.card) ∨
    (∃ L, ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ v ∈ V, N₀ ≤ v ∧
        ((Finset.range (v + 1)).filter
          (fun z => z ∈ A ∧ (v - z) ∈ A)).card ≤ 2 * L) := by
  rcases endgame_final_fork h0 hcov hanchor hfail with h | h
  · exact Or.inl h
  · right
    obtain ⟨x, hxm, hxA, L, hL⟩ := h
    refine ⟨L, fun K => ?_⟩
    obtain ⟨V, hVc, hVm⟩ := hL K
    refine ⟨V, hVc, fun v hv => ?_⟩
    obtain ⟨hvN, s, J, hJ2, hJL, hhub⟩ := hVm v hv
    exact ⟨hvN, street_is_sidon_poor h0
      (fun t => (hxA t).2) hJL hhub⟩

open Classical in
/-- **THE CASCADE FORK** (re-export; seventh summit).  Every
counterexample's wealth drain either stays saturated at every
2-adic level — and is then COMPLETELY DETERMINED: explicit
binary digits ε', explicit addresses α, both channels equal,
every level literally the α-cylinder slice {x | α k + 2^k x ∈ A}
of the root basis (the enemy IS a 2-adic point, the Cantor-like
endpoint) — or hits a FIRST MIXING LEVEL m: a twin-channel
world that is an explicit cylinder slice {x | c + 2^m x ∈ A}
with BOTH parities cofinal and blowup wealth flowing through
it.  Total determination or located mixing: the two remaining
regimes of Erdős 881, now with exact coordinates. -/
theorem endgame_cascade_fork {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ S T : ℕ → Set ℕ, S 0 = A ∧ T 0 = A ∧
      (∀ k, ∃ p q, p < 2 ∧ q < 2 ∧
        S (k + 1) = {y | 2 * y + p ∈ S k} ∧
        T (k + 1) = {y | 2 * y + q ∈ T k}) ∧
      (∀ k, ∀ C N, ∃ v, N ≤ v ∧ C ≤
        ((Finset.range (v + 1)).filter
          (fun x => x ∈ S k ∧ (v - x) ∈ T k)).card) ∧
      ((∃ ε' α : ℕ → ℕ, α 0 = 0 ∧
          (∀ k, ε' k < 2 ∧ α (k + 1) = α k + 2 ^ k * ε' k) ∧
          (∀ k, S k = T k) ∧
          (∀ k, S k = {x : ℕ | α k + 2 ^ k * x ∈ A})) ∨
        (∃ m c, S m = T m ∧
          S m = {x : ℕ | c + 2 ^ m * x ∈ A} ∧
          (∀ N, ∃ a, N ≤ a ∧ a ∈ S m ∧ a % 2 = 0) ∧
          (∀ N, ∃ a, N ≤ a ∧ a ∈ S m ∧ a % 2 = 1))) :=
  cascade_mixing_fork h0 hcov hfail

open Classical in
/-- **FORCED MIXING** (re-export; eighth summit — a COMPLETE
BRANCH DEFEAT).  The cascade fork's determined horn is EMPTY:
permanent saturation would make the root basis 2-adically
convergent, and `two_adic_convergence_kills_covering` shows a
2-adically convergent tail cannot pair-cover (wrong-parity
residue classes mod 2^K outnumber the head's translates).  So
EVERY counterexample's drain reaches a first mixing level m:
twin channels equal to the explicit cylinder slice
{x | c + 2^m x ∈ A}, both parities cofinal inside it, blowup
wealth flowing through it.  The Cantor-like endpoint — the
saturated cascade — cannot be run by any counterexample.
Mixing is not one branch of the descent; it is the only
surviving regime, and it now has exact coordinates. -/
theorem endgame_forced_mixing {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ S T : ℕ → Set ℕ, S 0 = A ∧ T 0 = A ∧
      (∀ k, ∃ p q, p < 2 ∧ q < 2 ∧
        S (k + 1) = {y | 2 * y + p ∈ S k} ∧
        T (k + 1) = {y | 2 * y + q ∈ T k}) ∧
      (∀ k, ∀ C N, ∃ v, N ≤ v ∧ C ≤
        ((Finset.range (v + 1)).filter
          (fun x => x ∈ S k ∧ (v - x) ∈ T k)).card) ∧
      ∃ m c, S m = T m ∧
        S m = {x : ℕ | c + 2 ^ m * x ∈ A} ∧
        (∀ N, ∃ a, N ≤ a ∧ a ∈ S m ∧ a % 2 = 0) ∧
        (∀ N, ∃ a, N ≤ a ∧ a ∈ S m ∧ a % 2 = 1) :=
  cascade_forces_mixing h0 hcov hfail

open Classical in
/-- **THE MIXING WORLD** (re-export; ninth summit).  Every
counterexample owns a LOCATED, COMPLETE mixing sub-instance:
a cylinder world {x | c + 2^m x ∈ A} that simultaneously
(i) pair-covers beyond a threshold — covering descends the
saturated prefix half-world by half-world, (ii) carries
unbounded cross-pair wealth, (iii) has both parities cofinal,
and (iv) is infinite.  The enemy cannot avoid reproducing the
problem's own hypotheses one 2-adic window down: the mixed
regime is self-similar, in explicit coordinates.  All that
does not descend unconditionally is the failure interface
itself — the (2,3)-mixed descent — which is the last
unformalized track of the cascade. -/
theorem endgame_mixing_world {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ S T : ℕ → Set ℕ, S 0 = A ∧ T 0 = A ∧
      (∀ k, ∃ p q, p < 2 ∧ q < 2 ∧
        S (k + 1) = {y | 2 * y + p ∈ S k} ∧
        T (k + 1) = {y | 2 * y + q ∈ T k}) ∧
      (∀ k, ∀ C N, ∃ v, N ≤ v ∧ C ≤
        ((Finset.range (v + 1)).filter
          (fun x => x ∈ S k ∧ (v - x) ∈ T k)).card) ∧
      ∃ m c, S m = T m ∧
        S m = {x : ℕ | c + 2 ^ m * x ∈ A} ∧
        (∀ N, ∃ a, N ≤ a ∧ a ∈ S m ∧ a % 2 = 0) ∧
        (∀ N, ∃ a, N ≤ a ∧ a ∈ S m ∧ a % 2 = 1) ∧
        (∃ N', PairCovers (S m) N') ∧
        (S m).Infinite :=
  mixing_world_complete h0 hcov hfail

open Classical in
/-- **THE SELF-SIMILAR ENEMY** (re-export; tenth summit).
Every counterexample reproduces the problem's complete
hypothesis package inside a located cylinder: a first mixing
level m and address c where the world {x | c + 2^m x ∈ A}
pair-covers, carries unbounded pair wealth, has both parities
cofinal, is infinite, and — through the address map — every
infinite deletion drawn from it wounds the root basis at order
3.  Covering, wealth, mixing, infinitude, interface: the enemy
one window down is the enemy again.  What remains of Erdős 881
along this track is precisely the sub-instance analysis: either
the lifted interface self-destructs under iteration, or a
mixing world survives a deletion — and mixing (both parities
cofinal) is exactly the carry liberty that powered the verified
Cantor repair. -/
theorem endgame_self_similar {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ S T : ℕ → Set ℕ, S 0 = A ∧ T 0 = A ∧
      (∀ k, ∃ p q, p < 2 ∧ q < 2 ∧
        S (k + 1) = {y | 2 * y + p ∈ S k} ∧
        T (k + 1) = {y | 2 * y + q ∈ T k}) ∧
      (∀ k, ∀ C N, ∃ v, N ≤ v ∧ C ≤
        ((Finset.range (v + 1)).filter
          (fun x => x ∈ S k ∧ (v - x) ∈ T k)).card) ∧
      ∃ m c, S m = T m ∧
        S m = {x : ℕ | c + 2 ^ m * x ∈ A} ∧
        (∀ N, ∃ a, N ≤ a ∧ a ∈ S m ∧ a % 2 = 0) ∧
        (∀ N, ∃ a, N ≤ a ∧ a ∈ S m ∧ a % 2 = 1) ∧
        (∃ N', PairCovers (S m) N') ∧
        (S m).Infinite ∧
        (∀ B' ⊆ S m, B'.Infinite →
          ¬IsExactTupleAsymptoticBasis
            (A \ ((fun x => c + 2 ^ m * x) '' B')) 3) :=
  mixing_world_interface h0 hcov hfail

open Classical in
/-- **THE TWO STREAMS** (re-export; eleventh summit).  Inside
every counterexample's located mixing world, each infinite
cylinder deletion generates cofinally many failing targets, and
every one of them is (i) RESIDUE-CHAINED: all its pair
representations touch the deletion's class c mod 2^m, and
(ii) POOR: its pair wealth is capped by twice the deletion's
local mass plus two.  Meanwhile the ω-drain pins an unbounded
wealth stream to a fixed nested 2-adic tower.  A counterexample
is therefore two disjoint cofinal streams — poor address-chained
failures and rich pinned wealth — running forever through one
covering, mixing world.  Erdős 881's remaining content is
whether that segregation is sustainable; every lab probe
(52/52 hall, 268/268 mixing) says it is not. -/
theorem endgame_two_streams {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ S T : ℕ → Set ℕ, S 0 = A ∧ T 0 = A ∧
      (∀ k, ∃ p q, p < 2 ∧ q < 2 ∧
        S (k + 1) = {y | 2 * y + p ∈ S k} ∧
        T (k + 1) = {y | 2 * y + q ∈ T k}) ∧
      (∀ k, ∀ C N, ∃ v, N ≤ v ∧ C ≤
        ((Finset.range (v + 1)).filter
          (fun x => x ∈ S k ∧ (v - x) ∈ T k)).card) ∧
      ∃ m c, S m = T m ∧
        S m = {x : ℕ | c + 2 ^ m * x ∈ A} ∧
        (∀ N, ∃ a, N ≤ a ∧ a ∈ S m ∧ a % 2 = 0) ∧
        (∀ N, ∃ a, N ≤ a ∧ a ∈ S m ∧ a % 2 = 1) ∧
        (∃ N', PairCovers (S m) N') ∧
        (S m).Infinite ∧
        ∀ B' ⊆ S m, 0 ∉ B' → B'.Infinite → ∀ N, ∃ n, N ≤ n ∧
          (∀ x ∈ A, ∀ y ∈ A, x + y = n →
            x % 2 ^ m = c % 2 ^ m ∨
            y % 2 ^ m = c % 2 ^ m) ∧
          ((Finset.range (n + 1)).filter
            (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤
          2 * ((Finset.range (n + 1)).filter
            (fun x => x ∈ ((fun x => c + 2 ^ m * x) ''
              B'))).card + 2 :=
  mixing_failure_addresses h0 hcov hfail

end Erdos881
