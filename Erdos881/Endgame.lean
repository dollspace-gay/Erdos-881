import Erdos881.FreeRank
import Erdos881.CantorInstance

namespace Erdos881

theorem counterexample_structure_summary {A : Set ℕ} {N₀ : ℕ}
    [DecidablePred (· ∈ A)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hmin : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 2)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∃ S : Finset ℕ, S.Nonempty ∧ (∀ h ∈ S, h ∈ A ∧ 0 < h) ∧
      ∀ X, ∃ b, b ∈ A ∧ X ≤ b ∧ b ∉ S ∧
        ∃ m, N₀ ≤ m ∧ ∃ H : Finset ℕ, IsRepSupportTransversal A m H ∧
          (∀ h ∈ H, ¬IsRepSupportTransversal A m (H \ {h})) ∧ H = insert b S) ∧
    (∃ P₂ P₃ : Finset ℕ, PairFree A N₀ P₂ ∧ RepFree A N₀ P₃ ∧
      ∃ X, ∀ b ∈ A, X ≤ b →
        (∃ t, N₀ ≤ t ∧ b ≤ t ∧
          ∀ x ∈ A, ∀ y ∈ A, x + y = t →
            x ∈ insert b P₂ ∨ y ∈ insert b P₂) ∧
        (∃ m, N₀ ≤ m ∧ b ≤ m ∧ IsRepSupportTransversal A m (insert b P₃))) ∧
    (∃ C, ∀ N, ∃ m, N ≤ m ∧
      ((Finset.range (m + 1)).filter
        (fun x => x ∈ A ∧ (m - x) ∈ A)).card ≤ C) ∧
    (∀ C N, ∃ v, N ≤ v ∧ C ≤ ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A)).card) :=
  counterexample_summary' h0 hcov hanchor hmin hfail

theorem counterexample_structure_reduction {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (pools : ℕ → Set ℕ) :
    ¬∀ k, (((poolFreeStep_wf h0 hcov hfail (pools (k + 1))).apply
        ∅).rank <
      ((poolFreeStep_wf h0 hcov hfail (pools k)).apply ∅).rank) :=
  no_pool_rank_descent h0 hcov hfail pools

theorem counterexample_structure_two_cases {A : Set ℕ} {N₀ : ℕ}
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
        S.card = d + 1 → ∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m S) :=
  rank_lt_omega_perfect_clique h0 hcov hanchor hfail b hbmono hbA
    hbpos hrank

theorem counterexample_structure_classification₂ (A : Set ℕ) (N₀ : ℕ)
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

theorem counterexample_structure_classification₃ (A : Set ℕ) (N₀ : ℕ)
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

theorem counterexample_structure_characterization {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) :
    (∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) ↔
    ¬∃ B : Set ℕ, HereditarilyFree A N₀ B :=
  hfail_iff_no_hereditarily_free h0 hcov

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

theorem counterexample_structure_triangle {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) :
    (∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) ↔
    WellFounded (FreeStep A N₀) :=
  hfail_iff_freeStep_wf h0 hcov

theorem counterexample_structure_two_trees {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) :
    ((∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) ∧
    (∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)) ↔
    (WellFounded (PairFreeStep A N₀) ∧
      WellFounded (FreeStep A N₀)) :=
  counterexample_iff_both_trees_wf h0 hcov

theorem counterexample_structure_final_form {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) :
    ((∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) ∧
    (∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)) ↔
    WellFounded (FreeStep A N₀) :=
  counterexample_iff_rep_tree_wf h0 hcov

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

theorem counterexample_structure_rank_layers {A : Set ℕ} {N₀ : ℕ}
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
        ∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m (insert b (Q k))) ∧
      (∀ b ∈ A, X ≤ b → 0 < b → (∀ j, b ∉ Q j) →
        ∀ Y, ∃ k, ∃ m, Y ≤ m ∧ N₀ ≤ m ∧
          IsRepSupportTransversal A m (insert b (Q k))) :=
  rank_layer_counterexample_structure h0 hcov hanchor hfail

theorem counterexample_structure_four_cases {A : Set ℕ} {N₀ : ℕ}
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
            IsPairSupportTransversal A s (insert b₃ Q)) ∨
     (∃ n, ∀ Δ S, ∃ b₂ ∈ A, ∃ b₃ ∈ A, S ≤ b₂ ∧ b₂ < b₃ ∧
        Δ < b₃ - b₂ ∧ ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
          IsPairSupportTransversal A s (insert b₃ Q))) :=
  counterexample_four_cases h0 hcov hfail

theorem counterexample_structure_ramsey_trichotomy {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) :
    ∃ T : ℕ → ℕ, StrictMono T ∧ (∀ i, T i ∈ A) ∧
      (∀ i, 0 < T i) ∧
      ((∀ i j, i < j →
          IsPairSupportTransversal A (T i + T j) ({T i, T j} : Finset ℕ)) ∨
       (∀ i j, i < j → ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
          x ∉ Set.range T ∧ y ∉ Set.range T ∧
          z ∉ Set.range T ∧ x + y + z = T i + T j) ∨
       (∃ R : Set ℕ, (∀ w ∈ R, w ∈ A ∧ 0 < w) ∧
          (∀ i, T i ∈ R) ∧
          ∀ i j, i < j → ∀ x ∈ A, ∀ y ∈ A,
            x + y = T i + T j → x ∈ R ∨ y ∈ R)) :=
  ramsey_trichotomy_of_covering h0 hcov

theorem counterexample_structure_omega_restriction {A : Set ℕ} {N₀ : ℕ}
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

theorem combined_constraints {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hess : ∀ a ∈ A, 0 < a → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ≠ a ∧ y ≠ a ∧ x + y = n) :
    -- (1) rank layers and the depth tax
    (∃ Q : ℕ → Finset ℕ, ∃ X,
      (∀ k, (Q k).Nonempty) ∧
      (∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h) ∧
      (∀ k, RepFree A N₀ (Q k)) ∧
      (∀ j k, j < k → Disjoint (Q j) (Q k)) ∧
      (∀ k, ∀ b ∈ A, 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
        ∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m (insert b (Q k))) ∧
      (∀ k, ∀ b ∈ A, X ≤ b → 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
        ∃ j, j ≤ k ∧ ∃ m, N₀ + k / 3 ≤ m ∧ N₀ ≤ m ∧
          IsRepSupportTransversal A m (insert b (Q j)))) ∧
    -- (2) the four cases
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
              IsPairSupportTransversal A s (insert b₃ Q)) ∨
       (∃ n, ∀ Δ S, ∃ b₂ ∈ A, ∃ b₃ ∈ A, S ≤ b₂ ∧ b₂ < b₃ ∧
          Δ < b₃ - b₂ ∧ ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
            IsPairSupportTransversal A s (insert b₃ Q)))) ∧
    -- (3) marriage-network pair transversals
    (∃ P : ℕ → ℕ × ℕ,
      (∀ i, (P i).1 ∈ A ∧ (P i).2 ∈ A ∧ 0 < (P i).1 ∧
        0 < (P i).2 ∧
        ∀ x ∈ A, ∀ y ∈ A, x + y = (P i).1 + (P i).2 →
          (x = (P i).1 ∧ y = (P i).2) ∨
          (x = (P i).2 ∧ y = (P i).1)) ∧
      (∀ i, max (P i).1 (P i).2 < min (P (i + 1)).1
        (P (i + 1)).2) ∧
      ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
        IsRepSupportTransversal A n H ∧ (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
        2 ≤ H.card ∧ ∀ h ∈ H, ∃ i,
          h = (P i).1 ∨ h = (P i).2) ∧
    -- (4) the ω-restriction
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
  refine ⟨stratified_tax_summary h0 hcov hanchor hfail,
    counterexample_four_cases h0 hcov hfail,
    matched_deletion_pair_transversals h0 hcov hanchor hfail hess,
    omega_avoidance_dichotomy hcov,
    fragile_supply_of_hfail h0 hcov hfail,
    r2_unbounded_of_hfail h0 hcov hfail⟩

theorem counterexample_structure_subsequence {A : Set ℕ} {N₀ : ℕ}
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
          IsRepSupportTransversal A m ((Finset.range J).image (fun t =>
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
  ⟨subsequence_stalls_hereditarily h0 hcov hanchor hfail,
    root_rank_omega_or_aligned h0 hcov hanchor hfail⟩

theorem counterexample_structure_final_fork {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
      RepFree A N₀ P ∧ c ≤ P.card) ∨
    (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
      ∃ L, ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ v ∈ V, N₀ ≤ v ∧ ∃ s J, 2 ≤ J ∧ J ≤ L ∧
          IsRepSupportTransversal A v ((Finset.range J).image
            (fun j => x (s + j)))) :=
  final_fork h0 hcov hanchor hfail

theorem counterexample_structure_global_trichotomy {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ((∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
        w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g) ∧
      ((∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
        RepFree A N₀ P ∧ c ≤ P.card) ∨
      (∃ H : Finset ℕ, ∃ h ∈ H, ∀ K, ∃ V : Finset ℕ,
        K ≤ V.card ∧ ∀ v ∈ V, N₀ ≤ v ∧ h ≤ v ∧ v - h ∈ A ∧
          IsPairSupportTransversal A v H) ∨
      (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
        ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
          ∀ v ∈ V, N₀ ≤ v ∧ v ∉ A ∧ ∃ s, S₀ ≤ s ∧ x s ≤ v ∧
            ∃ J, 2 ≤ J ∧ J ≤ L ∧ IsPairSupportTransversal A v
              ((Finset.range J).image (fun j => x (s + j)))) ∨
      (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
        ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
          ∀ v ∈ V, N₀ ≤ v ∧ v ∈ A ∧ ∃ s, S₀ ≤ s ∧
            ∃ J, 2 ≤ J ∧ J ≤ L ∧
              v ∈ (Finset.range J).image (fun j => x (s + j)) ∧
              IsPairSupportTransversal A v ((Finset.range J).image
                (fun j => x (s + j))) ∧
              (∀ a ∈ A, ∀ b ∈ A, a + b = v →
                a ≤ x (s + J - 1) - x s ∨
                b ≤ x (s + J - 1) - x s)))) ∨
    (∃ g₀, g₀ ∈ A ∧ ∀ c ∈ A, 0 < c → c ≠ g₀ →
      IsPairSupportTransversal A (2 * c) ({c, g₀} : Finset ℕ)) ∨
    (∃ g₀, (∀ c ∈ A, 0 < c → c ≠ g₀ → ∀ w ∈ A, ∀ w' ∈ A,
        w + w' = 2 * c → w = c ∧ w' = c) ∧
      (∀ c ∈ A, 0 < c → c ≠ g₀ →
        IsPairSupportTransversal A (2 * c) ({c} : Finset ℕ)) ∧
      (∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
        ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) ∧
      (∀ a d, 0 < d → a ∈ A → a + d ∈ A → a + 2 * d ∈ A →
        a + d = g₀ ∨ a + d = 0)) :=
  global_trichotomy h0 hcov hfail

theorem counterexample_structure_collapsed_trichotomy {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ((∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
        w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g) ∧
      ((∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
        RepFree A N₀ P ∧ c ≤ P.card) ∨
      (∃ H : Finset ℕ, ∃ h ∈ H, ∀ K, ∃ V : Finset ℕ,
        K ≤ V.card ∧ ∀ v ∈ V, N₀ ≤ v ∧ h ≤ v ∧ v - h ∈ A ∧
          IsPairSupportTransversal A v H) ∨
      (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
        ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
          ∀ v ∈ V, N₀ ≤ v ∧ v ∉ A ∧ ∃ s, S₀ ≤ s ∧ x s ≤ v ∧
            ∃ J, 2 ≤ J ∧ J ≤ L ∧ IsPairSupportTransversal A v
              ((Finset.range J).image (fun j => x (s + j)))) ∨
      (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
        ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
          ∀ v ∈ V, N₀ ≤ v ∧ v ∈ A ∧ ∃ s, S₀ ≤ s ∧
            ∃ J, 2 ≤ J ∧ J ≤ L ∧
              v ∈ (Finset.range J).image (fun j => x (s + j)) ∧
              IsPairSupportTransversal A v ((Finset.range J).image
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
        IsPairSupportTransversal A (2 * c) ({c} : Finset ℕ)) ∧
      (∀ B ⊆ A, B.Infinite → ¬∃ N₂, ∀ n, N₂ ≤ n →
        ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) ∧
      (∀ a d, 0 < d → a ∈ A → a + d ∈ A → a + 2 * d ∈ A →
        a + d = g₀ ∨ a + d < C₀)) :=
  collapsed_trichotomy h0 hcov hfail

theorem counterexample_structure_final_dichotomy {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ((∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
      RepFree A N₀ P ∧ c ≤ P.card) ∨
    (∃ H : Finset ℕ, ∃ h ∈ H, ∀ K, ∃ V : Finset ℕ,
      K ≤ V.card ∧ ∀ v ∈ V, N₀ ≤ v ∧ h ≤ v ∧ v - h ∈ A ∧
        IsPairSupportTransversal A v H) ∨
    (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
      ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ v ∈ V, N₀ ≤ v ∧ v ∉ A ∧ ∃ s, S₀ ≤ s ∧ x s ≤ v ∧
          ∃ J, 2 ≤ J ∧ J ≤ L ∧ IsPairSupportTransversal A v
            ((Finset.range J).image (fun j => x (s + j)))) ∨
    (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
      ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ v ∈ V, N₀ ≤ v ∧ v ∈ A ∧ ∃ s, S₀ ≤ s ∧
          ∃ J, 2 ≤ J ∧ J ≤ L ∧
            v ∈ (Finset.range J).image (fun j => x (s + j)) ∧
            IsPairSupportTransversal A v ((Finset.range J).image
              (fun j => x (s + j))) ∧
            (∀ a ∈ A, ∀ b ∈ A, a + b = v →
              a ≤ x (s + J - 1) - x s ∨
              b ≤ x (s + J - 1) - x s))) ∨
    (∃ g₀ C₀, (∀ c ∈ A, C₀ ≤ c → c ≠ g₀ → ∀ w ∈ A, ∀ w' ∈ A,
        w + w' = 2 * c → w = c ∧ w' = c) ∧
      (∀ c ∈ A, C₀ ≤ c → c ≠ g₀ →
        IsPairSupportTransversal A (2 * c) ({c} : Finset ℕ)) ∧
      (∀ B ⊆ A, B.Infinite → ¬∃ N₂, ∀ n, N₂ ≤ n →
        ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) ∧
      (∀ a d, 0 < d → a ∈ A → a + d ∈ A → a + 2 * d ∈ A →
        a + d = g₀ ∨ a + d < C₀)) :=
  final_dichotomy h0 hcov hfail

theorem counterexample_structure_translate_laws {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∀ c, c ∈ A → 0 < c →
      ∀ Z₀, ∃ z, Z₀ ≤ z ∧ z ∈ A ∧ z + c ∉ A) ∧
    (∀ h₀ h₁, h₀ ∈ A → h₁ ∈ A → 0 < h₀ → 0 < h₁ →
      ∀ Z₀, ∃ z, Z₀ ≤ z ∧ z ∈ A ∧ z + h₀ ∉ A ∧ z + h₁ ∉ A) :=
  ⟨fun _c hcA hc => single_translate_law h0 hcov hfail hcA hc,
   fun _h₀ _h₁ h₀A h₁A hh₀ hh₁ =>
     pair_translate_law h0 hcov hfail h₀A h₁A hh₀ hh₁⟩

open Classical in

theorem counterexample_structure_parity_fork {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ((∀ N, ∃ a, N ≤ a ∧ a ∈ A ∧ a % 2 = 0) ∧
     (∀ N, ∃ a, N ≤ a ∧ a ∈ A ∧ a % 2 = 1)) ∨
    (∃ Y ε, ε < 2 ∧ (∀ a ∈ A, Y < a → a % 2 = ε) ∧
      (∀ n, 2 * Y < n → n % 2 = 1 →
        IsPairSupportTransversal A n ((Finset.range (Y + 1)).filter
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
      half_model_covers hε hcov hpar,
      descent_invariant hε hfail hfA hfpar⟩
  · exact Or.inl hboth

open Classical in

theorem counterexample_structure_omega_nested_representation {A : Set ℕ} {N₀ : ℕ}
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
  omega_nested_representation h0 hcov hfail

open Classical in

theorem counterexample_structure_poor_target_sequence {A : Set ℕ} {N₀ : ℕ}
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
  rcases counterexample_structure_final_fork h0 hcov hanchor hfail with h | h
  · exact Or.inl h
  · right
    obtain ⟨x, hxm, hxA, L, hL⟩ := h
    refine ⟨L, fun K => ?_⟩
    obtain ⟨V, hVc, hVm⟩ := hL K
    refine ⟨V, hVc, fun v hv => ?_⟩
    obtain ⟨hvN, s, J, hJ2, hJL, hhub⟩ := hVm v hv
    exact ⟨hvN, target_sequence_is_sidon_poor h0
      (fun t => (hxA t).2) hJL hhub⟩

open Classical in

theorem counterexample_structure_iteration_fork {A : Set ℕ} {N₀ : ℕ}
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
  iteration_mixing_fork h0 hcov hfail

open Classical in

theorem counterexample_structure_forced_mixing {A : Set ℕ} {N₀ : ℕ}
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
  iteration_forces_mixing h0 hcov hfail

open Classical in

theorem counterexample_structure_mixing_model {A : Set ℕ} {N₀ : ℕ}
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
  mixing_model_complete h0 hcov hfail

open Classical in

theorem counterexample_structure_self_similar {A : Set ℕ} {N₀ : ℕ}
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
  mixing_model_interface h0 hcov hfail

open Classical in

theorem counterexample_structure_two_streams {A : Set ℕ} {N₀ : ℕ}
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

open Classical in

theorem counterexample_structure_universal_support_transversal {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ B ⊆ A, 0 ∉ B → B.Infinite → ∀ N, ∃ n, N ≤ n ∧
      IsPairSupportTransversal A n ((Finset.range (n + 1)).filter
        (fun x => x ∈ B)) ∧
      ((Finset.range (n + 1)).filter
        (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤
      2 * ((Finset.range (n + 1)).filter
        (fun x => x ∈ B)).card :=
  universal_prefix_support_transversal_law (N₀ := N₀) h0 hfail

open Classical in

theorem counterexample_structure_universal_deletion_transversal {A : Set ℕ}
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ B ⊆ A, B.Infinite → ∀ N, ∃ n, N ≤ n ∧
      ∃ H ⊆ (Finset.range (n + 1)).filter (fun x => x ∈ B),
        IsRepSupportTransversal A n H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
        ∀ h ∈ H, ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = n ∧
          (x = h ∨ y = h ∨ z = h) ∧
          ∀ g ∈ H, g ≠ h → x ≠ g ∧ y ≠ g ∧ z ≠ g :=
  universal_deletion_transversal_law hfail

open Classical in

theorem counterexample_structure_hereditary_pair_transversals {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∀ B ⊆ A, (∀ b ∈ B, 0 < b) → B.Infinite →
      ∀ N, ∃ n, N ≤ n ∧
      ∃ H ⊆ (Finset.range (n + 1)).filter (fun x => x ∈ B),
        2 ≤ H.card ∧ IsRepSupportTransversal A n H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
        ∀ h ∈ H, ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = n ∧
          (x = h ∨ y = h ∨ z = h) ∧
          ∀ g ∈ H, g ≠ h → x ≠ g ∧ y ≠ g ∧ z ≠ g) ∨
    (∃ g₀, g₀ ∈ A ∧ ∀ c ∈ A, 0 < c → c ≠ g₀ →
      IsPairSupportTransversal A (2 * c) ({c, g₀} : Finset ℕ)) ∨
    (∃ g₀, (∀ c ∈ A, 0 < c → c ≠ g₀ → ∀ w ∈ A, ∀ w' ∈ A,
        w + w' = 2 * c → w = c ∧ w' = c) ∧
      (∀ c ∈ A, 0 < c → c ≠ g₀ →
        IsPairSupportTransversal A (2 * c) ({c} : Finset ℕ)) ∧
      (∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
        ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) ∧
      (∀ a d, 0 < d → a ∈ A → a + d ∈ A → a + 2 * d ∈ A →
        a + d = g₀ ∨ a + d = 0)) := by
  rcases counterexample_structure_global_trichotomy h0 hcov hfail with
    ⟨hanc, -⟩ | h | h
  · exact Or.inl (deletion_transversal_size_floor h0 hcov
      (streamSurvives_of_anchor h0 hcov hanc) hfail)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

open Classical in

theorem counterexample_structure_width_band {A B : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B' ⊆ A, B'.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B') 3)
    (hBA : B ⊆ A) (hBpos : ∀ b ∈ B, 0 < b)
    (hBinf : B.Infinite) :
    (∃ C, ∀ N, ∃ n, N ≤ n ∧
      (∃ H ⊆ (Finset.range (n + 1)).filter (fun x => x ∈ B),
        H.card ≤ C ∧ 2 ≤ H.card ∧ IsRepSupportTransversal A n H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h}))) ∧
      ((Finset.range (n + 1)).filter
        (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ 2 * C) ∨
    (∀ C N, ∃ n, N ≤ n ∧
      ∃ H ⊆ (Finset.range (n + 1)).filter (fun x => x ∈ B),
        C < H.card ∧ IsRepSupportTransversal A n H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
        (∀ h ∈ H, ¬IsPairSupportTransversal A (n - h) (H \ {h})) ∧
        ∀ h ∈ H, ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = n ∧
          (x = h ∨ y = h ∨ z = h) ∧
          ∀ g ∈ H, g ≠ h → x ≠ g ∧ y ≠ g ∧ z ≠ g) :=
  counterexample_structure_width_band_local h0 hcov hanchor hfail hBA hBpos
    hBinf

open Classical in

theorem counterexample_structure_oscillation {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∃ L, ∀ N, ∃ n, N ≤ n ∧
      ((Finset.range (n + 1)).filter
        (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ L) ∧
    (∀ C N, ∃ v, N ≤ v ∧ C ≤
      ((Finset.range (v + 1)).filter
        (fun x => x ∈ A ∧ (v - x) ∈ A)).card) := by
  constructor
  · exact poor_stream_of_hfail h0 hcov hfail
  · intro C N
    exact r2_unbounded_of_hfail h0 hcov hfail C N

open Classical in

theorem counterexample_structure_canonical_core {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ L, ∀ W, ∃ S : Finset ℕ, S ⊆ Finset.range (W + 1) ∧
      ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ L ∧
        IsPairSupportTransversal A n H ∧
        (∀ h ∈ H, h ∈ A ∧ (n - h) ∈ A ∧ 2 * h ≤ n) ∧
        (∀ x, 2 * x ≤ n → x ∈ A → (n - x) ∈ A → x ∈ H) ∧
        S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h :=
  canonical_core_of_hfail h0 hcov hfail

open Classical in

theorem counterexample_structure_drift_fork {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ L,
    (∃ u, ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ L ∧
      IsPairSupportTransversal A n H ∧
      (∀ h ∈ H, h ∈ A ∧ (n - h) ∈ A ∧ 2 * h ≤ n) ∧
      (∀ x, 2 * x ≤ n → x ∈ A → (n - x) ∈ A → x ∈ H) ∧
      u ∈ H) ∨
    (∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ L ∧
      IsPairSupportTransversal A n H ∧
      (∀ h ∈ H, h ∈ A ∧ (n - h) ∈ A ∧ 2 * h ≤ n) ∧
      (∀ x, 2 * x ≤ n → x ∈ A → (n - x) ∈ A → x ∈ H) ∧
      ∀ h ∈ H, W < h) :=
  poor_drift_fork h0 hcov hfail

open Classical in

theorem counterexample_structure_rigidity_trichotomy {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∃ d, 1 ≤ d ∧ ∀ N, ∃ a, N ≤ a ∧ a ∈ A ∧ a + d ∈ A) ∨
    (∃ L u W, u ≤ W ∧ ∀ N, ∃ n, N ≤ n ∧
      ((Finset.range (n + 1)).filter
        (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ 2 * L ∧
      (u ∈ A ∧ (n - u) ∈ A ∧ 2 * u ≤ n) ∧
      ∀ x, x ≤ W → x ≠ u →
        ¬(x ∈ A ∧ (n - x) ∈ A ∧ 2 * x ≤ n)) ∨
    (∃ L, ∀ W N, ∃ n, N ≤ n ∧
      ((Finset.range (n + 1)).filter
        (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ 2 * L ∧
      ∀ x, x ≤ W → ¬(x ∈ A ∧ (n - x) ∈ A ∧ 2 * x ≤ n)) :=
  rigidity_trichotomy h0 hcov hfail

open Classical in

theorem counterexample_structure_rigidity_pair_transversals {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∃ d, 1 ≤ d ∧ ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      IsRepSupportTransversal A n H ∧ (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
      2 ≤ H.card ∧ ∀ h ∈ H, h ∈ A ∧ h + d ∈ A ∧ 0 < h) ∨
    (∃ L u W, u ≤ W ∧ ∀ N, ∃ n, N ≤ n ∧
      ((Finset.range (n + 1)).filter
        (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ 2 * L ∧
      (u ∈ A ∧ (n - u) ∈ A ∧ 2 * u ≤ n) ∧
      ∀ x, x ≤ W → x ≠ u →
        ¬(x ∈ A ∧ (n - x) ∈ A ∧ 2 * x ≤ n)) ∨
    (∃ L, ∀ W N, ∃ n, N ≤ n ∧
      ((Finset.range (n + 1)).filter
        (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ 2 * L ∧
      ∀ x, x ≤ W → ¬(x ∈ A ∧ (n - x) ∈ A ∧ 2 * x ≤ n)) :=
  rigidity_trichotomy_pair_transversals h0 hcov hanchor hfail

open Classical in

theorem counterexample_structure_fan_poverty {A D : Set ℕ} {n : ℕ}
    (hfailn : ∀ v : Fin 3 → ℕ, (∀ i, v i ∈ A \ D) →
      ∑ i, v i ≠ n) :
    ∀ x, x ∈ A → x ∉ D → x ≤ n →
      ((Finset.range (n - x + 1)).filter
        (fun y => y ∈ A ∧ (n - x - y) ∈ A)).card ≤
      2 * ((Finset.range (n + 1)).filter
        (fun d => d ∈ D)).card + 2 :=
  fan_poverty_of_failing hfailn

open Classical in

theorem counterexample_structure_density_law {A D : Set ℕ} {n : ℕ}
    (hfailn : ∀ v : Fin 3 → ℕ, (∀ i, v i ∈ A \ D) →
      ∑ i, v i ≠ n) :
    ((Finset.range (n + 1)).filter (fun x => x ∈ A)).card -
      ((Finset.range (n + 1)).filter (fun d => d ∈ D)).card ≤
    ((Finset.range (n + 1)).filter (fun m =>
      ((Finset.range (m + 1)).filter
        (fun y => y ∈ A ∧ (m - y) ∈ A)).card ≤
      2 * ((Finset.range (n + 1)).filter
        (fun d => d ∈ D)).card + 2)).card ∧
    ((Finset.range (n / 2 + 1)).filter
        (fun x => x ∈ A)).card *
      ((Finset.range (n / 2 + 1)).filter
        (fun x => x ∈ A)).card +
    ((Finset.range (n + 1)).filter (fun m =>
      ((Finset.range (m + 1)).filter
        (fun y => y ∈ A ∧ (m - y) ∈ A)).card ≤
      2 * ((Finset.range (n + 1)).filter
        (fun d => d ∈ D)).card + 2)).card *
      (((Finset.range (n + 1)).filter
        (fun x => x ∈ A)).card -
       (2 * ((Finset.range (n + 1)).filter
        (fun d => d ∈ D)).card + 2)) ≤
    (n + 1) * ((Finset.range (n + 1)).filter
      (fun x => x ∈ A)).card :=
  density_law_of_failing hfailn

open Classical in

theorem counterexample_structure_combined_law {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ((∃ L, ∀ N, ∃ n, N ≤ n ∧
      ((Finset.range (n + 1)).filter
        (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ L) ∧
     (∀ C N, ∃ v, N ≤ v ∧ C ≤
      ((Finset.range (v + 1)).filter
        (fun x => x ∈ A ∧ (v - x) ∈ A)).card)) ∧
    ((∃ d, 1 ≤ d ∧ ∀ N, ∃ a, N ≤ a ∧ a ∈ A ∧ a + d ∈ A) ∨
     (∃ L u W, u ≤ W ∧ ∀ N, ∃ n, N ≤ n ∧
       ((Finset.range (n + 1)).filter
         (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ 2 * L ∧
       (u ∈ A ∧ (n - u) ∈ A ∧ 2 * u ≤ n) ∧
       ∀ x, x ≤ W → x ≠ u →
         ¬(x ∈ A ∧ (n - x) ∈ A ∧ 2 * x ≤ n)) ∨
     (∃ L, ∀ W N, ∃ n, N ≤ n ∧
       ((Finset.range (n + 1)).filter
         (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ 2 * L ∧
       ∀ x, x ≤ W → ¬(x ∈ A ∧ (n - x) ∈ A ∧ 2 * x ≤ n))) ∧
    (∀ B ⊆ A, B.Infinite → ∀ N, ∃ n, N ≤ n ∧
      (((Finset.range (n + 1)).filter
          (fun x => x ∈ A)).card -
        ((Finset.range (n + 1)).filter
          (fun d => d ∈ B)).card ≤
       ((Finset.range (n + 1)).filter (fun m =>
         ((Finset.range (m + 1)).filter
           (fun y => y ∈ A ∧ (m - y) ∈ A)).card ≤
         2 * ((Finset.range (n + 1)).filter
           (fun d => d ∈ B)).card + 2)).card) ∧
      ((Finset.range (n / 2 + 1)).filter
          (fun x => x ∈ A)).card *
        ((Finset.range (n / 2 + 1)).filter
          (fun x => x ∈ A)).card +
      ((Finset.range (n + 1)).filter (fun m =>
        ((Finset.range (m + 1)).filter
          (fun y => y ∈ A ∧ (m - y) ∈ A)).card ≤
        2 * ((Finset.range (n + 1)).filter
          (fun d => d ∈ B)).card + 2)).card *
        (((Finset.range (n + 1)).filter
          (fun x => x ∈ A)).card -
         (2 * ((Finset.range (n + 1)).filter
          (fun d => d ∈ B)).card + 2)) ≤
      (n + 1) * ((Finset.range (n + 1)).filter
        (fun x => x ∈ A)).card) :=
  combined_law h0 hcov hfail

open Classical in

theorem counterexample_structure_coverage_breakdown {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ B ⊆ A, B.Infinite → ∀ N, ∃ n, N ≤ n ∧
      ∀ w, w ≤ n →
        2 * ((Finset.range (n + 1)).filter
          (fun d => d ∈ B)).card + 2 <
        ((Finset.range (w + 1)).filter
          (fun y => y ∈ A ∧ (w - y) ∈ A)).card →
        (n - w) ∉ A ∨ (n - w) ∈ B :=
  coverage_breakdown_of_hfail h0 hcov hfail

open Classical in

theorem counterexample_structure_spike_census {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ B ⊆ A, B.Infinite → ∀ N, ∃ n, N ≤ n ∧
      ((Finset.range (n + 1)).filter
        (fun x => x ∈ A)).card +
      ((Finset.range (n + 1)).filter (fun w =>
        2 * ((Finset.range (n + 1)).filter
          (fun d => d ∈ B)).card + 2 <
        ((Finset.range (w + 1)).filter
          (fun y => y ∈ A ∧ (w - y) ∈ A)).card)).card ≤
      n + 1 + 2 * ((Finset.range (n + 1)).filter
        (fun d => d ∈ B)).card :=
  spike_census_of_hfail h0 hcov hfail

open Classical in

theorem counterexample_structure_construction {A : Set ℕ} {N₀ : ℕ} {b : ℕ → ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hbA : ∀ k, b k ∈ A) (hbpos : ∀ k, 0 < b k)
    (hbmono : StrictMono b)
    (hsplit : ∀ k, ∃ u ∈ A, ∃ v ∈ A,
      (∀ j, u ≠ b j) ∧ (∀ j, v ≠ b j) ∧ u + v = b k)
    (hboth : ∀ i j, N₀ ≤ b i + b j →
      ∃ p ∈ A, ∃ q ∈ A, ∃ r ∈ A,
        (∀ k, p ≠ b k) ∧ (∀ k, q ≠ b k) ∧ (∀ k, r ≠ b k) ∧
        p + q + r = b i + b j) :
    ∃ B ⊆ A, B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) 3 :=
  deletion_exists_of_construction h0 hcov hbA hbpos hbmono
    hsplit hboth

open Classical in

theorem counterexample_structure_combined_criterion {A B : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (h0B : 0 ∉ B) (hcov : PairCovers A N₀)
    (hrisk : ∀ n, N₀ ≤ n → (∃ b ∈ B, ∃ a ∈ A, b + a = n) →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n) :
    IsExactTupleAsymptoticBasis (A \ B) 3 :=
  deletion_criterion_local h0 h0B hcov hrisk

open Classical in

theorem counterexample_structure_join {A : Set ℕ} {N₀ n : ℕ} {B : Finset ℕ}
    (hcov : PairCovers A N₀) (hB : B.Nonempty) (hn : N₀ ≤ n)
    (hunserved : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
      x ∉ B → y ∉ B → z ∉ B → x + y + z ≠ n) :
    ∃ w ∈ B,
      ((Finset.range (n - N₀ + 1)).filter
        (fun z => z ∈ A ∧ z ∉ B)).card ≤
      B.card * ((Finset.range (n - w + 1)).filter
        (fun x => x ∈ A ∧ (n - w - x) ∈ A)).card :=
  stall_forces_wealth hcov hB hn hunserved

open Classical in

theorem counterexample_structure_popular_difference {A : Set ℕ} {X D : ℕ}
    {T : Finset ℕ} (hTX : ∀ M ∈ T, M ≤ X)
    (hD : ∀ d, 0 < d → d ≤ X →
      ((Finset.range (X + 1)).filter
        (fun y => y ∈ A ∧ (y + d) ∈ A)).card ≤ D) :
    (∑ M ∈ T, ((Finset.range (M + 1)).filter
        (fun z => z ∈ A ∧ (M - z) ∈ A)).card) ^ 2 ≤
    ((Finset.range (X + 1)).filter (fun x => x ∈ A)).card *
      ((∑ M ∈ T, ((Finset.range (M + 1)).filter
        (fun z => z ∈ A ∧ (M - z) ∈ A)).card) +
        T.card * T.card * D) :=
  popular_difference_bound hTX hD

open Classical in

theorem counterexample_structure_popular_positive_difference {A : Set ℕ} {X D : ℕ}
    {T : Finset ℕ} (hTX : ∀ M ∈ T, M ≤ X)
    (hmass :
      ((Finset.range (X + 1)).filter (fun x => x ∈ A)).card *
        ((∑ M ∈ T, ((Finset.range (M + 1)).filter
          (fun z => z ∈ A ∧ (M - z) ∈ A)).card) +
          T.card * T.card * D) <
      (∑ M ∈ T, ((Finset.range (M + 1)).filter
        (fun z => z ∈ A ∧ (M - z) ∈ A)).card) ^ 2) :
    ∃ d, 0 < d ∧ d ≤ X ∧ D <
      ((Finset.range (X + 1)).filter
        (fun y => y ∈ A ∧ (y + d) ∈ A)).card :=
  exists_popular_positive_difference hTX hmass

end Erdos881
