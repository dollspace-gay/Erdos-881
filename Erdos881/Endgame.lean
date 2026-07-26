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
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
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
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
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
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
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

end Erdos881
