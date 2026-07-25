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

end Erdos881
