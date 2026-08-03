import Erdos881.DesertConcentration

namespace Erdos881

open Classical

/-- Covered but has a support transversal: order-`h` representations of `m` exist,
and every one meets the finite support transversal `H`. -/
def HasSupportTransversalAt (A : Set ℕ) (h : ℕ) (H : Finset ℕ)
    (m : ℕ) : Prop :=
  (∃ w : Fin h → ℕ, (∀ i, w i ∈ A) ∧ ∑ i, w i = m) ∧
  ∀ w : Fin h → ℕ, (∀ i, w i ∈ A) → ∑ i, w i = m →
    ∃ i, w i ∈ H

/-- Pinnedness is strandedness after inserting the pin. -/
theorem PinnedAt.stranded_insert {A : Set ℕ} {h : ℕ}
    {F : Finset ℕ} {f n : ℕ}
    (hpin : PinnedAt A h F f n) :
    StrandedAt A h (insert f F) n := by
  rintro ⟨v, hv, hsum⟩
  obtain ⟨i, hi⟩ := hpin.2 v
    (fun i => ⟨(hv i).1, fun hmem => (hv i).2
      (Finset.mem_insert_of_mem hmem)⟩) hsum
  exact (hv i).2 (by rw [hi]; exact
    Finset.mem_insert_self f F)

theorem pinned_cone_has_support_transversal {A : Set ℕ} {k : ℕ}
    {G : Finset ℕ} {f n N₀ : ℕ}
    (hcov : ∀ m, N₀ ≤ m → ∃ w : Fin k → ℕ,
      (∀ i, w i ∈ A) ∧ ∑ i, w i = m)
    (hpin : PinnedAt A (k + 1) G f n)
    {x : ℕ} (hx : x ∈ A) (hxG : x ∉ insert f G)
    (hxn : x + N₀ ≤ n) :
    HasSupportTransversalAt A k (insert f G) (n - x) := by
  have hstr : StrandedAt A k (insert f G) (n - x) :=
    hpin.stranded_insert.descend hx hxG (by omega)
  refine ⟨hcov (n - x) (by omega), ?_⟩
  intro w hw hsum
  by_contra hcon
  push Not at hcon
  exact hstr ⟨w, fun i => ⟨hw i, hcon i⟩, hsum⟩

theorem pinned_reflects_basis {A : Set ℕ} {k : ℕ}
    {G : Finset ℕ} {f n N₀ : ℕ}
    (hcov : ∀ m, N₀ ≤ m → ∃ w : Fin k → ℕ,
      (∀ i, w i ∈ A) ∧ ∑ i, w i = m)
    (hpin : PinnedAt A (k + 1) G f n)
    (y : ℕ) (hy : y + N₀ ≤ n) :
    ((Finset.range (y + 1)).filter
      (fun x => x ∈ A ∧
        x ∉ (insert f G : Finset ℕ))).card ≤
    ((Finset.Icc (n - y) n).filter
      (fun m =>
        HasSupportTransversalAt A k (insert f G) m)).card := by
  refine Finset.card_le_card_of_injOn
    (fun x => n - x) ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range] at hx
    obtain ⟨hxy, hxA, hxG⟩ := hx
    simp only [Finset.mem_coe, Finset.mem_filter,
      Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    exact pinned_cone_has_support_transversal hcov hpin hxA hxG
      (by omega)
  · intro x₁ h₁ x₂ h₂ heq
    simp only [Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range] at h₁ h₂
    simp only at heq
    omega

theorem pinned_pair_fiber {A : Set ℕ} {k : ℕ}
    {G : Finset ℕ} {f n n' N₀ : ℕ}
    (hcov : ∀ m, N₀ ≤ m → ∃ w : Fin k → ℕ,
      (∀ i, w i ∈ A) ∧ ∑ i, w i = m)
    (hpin : PinnedAt A (k + 1) G f n)
    (hpin' : PinnedAt A (k + 1) G f n')
    (hle : n ≤ n')
    {x : ℕ} (hx : x ∈ A) (hxG : x ∉ insert f G)
    (hxn : x + N₀ ≤ n) :
    HasSupportTransversalAt A k (insert f G) (n - x) ∧
    HasSupportTransversalAt A k (insert f G)
      ((n - x) + (n' - n)) := by
  refine ⟨pinned_cone_has_support_transversal hcov hpin hx hxG hxn, ?_⟩
  have h1 : (n - x) + (n' - n) = n' - x := by omega
  rw [h1]
  exact pinned_cone_has_support_transversal hcov hpin' hx hxG
    (by omega)

theorem caseA_large_fibers {A : Set ℕ} {k : ℕ}
    {G : Finset ℕ} {f : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hp : ∀ M, ∃ n, M ≤ n ∧
      PinnedAt A (k + 1) G f n) :
    ∀ L, ∃ d, 0 < d ∧ ∃ S : Finset ℕ, L ≤ S.card ∧
      ∀ m ∈ S, HasSupportTransversalAt A k (insert f G) m ∧
        HasSupportTransversalAt A k (insert f G) (m + d) := by
  intro L
  have hinf : A.Infinite :=
    IsExactTupleAsymptoticBasis.infinite hbasis
  obtain ⟨N₀, hcov⟩ := hbasis
  obtain ⟨T, hTsub, hTcard⟩ :=
    hinf.exists_subset_card_eq
      (L + (insert f G).card)
  have hTA : ∀ x ∈ T, x ∈ A := fun x hx => hTsub hx
  set T' := T \ insert f G with hT'
  have hT'card : L ≤ T'.card := by
    have hsd : T.card - (insert f G).card ≤
        T'.card := by
      rw [hT']
      exact Finset.le_card_sdiff _ _
    omega
  set y := T.sup id with hy
  have hTy : ∀ x ∈ T, x ≤ y := fun x hx =>
    Finset.le_sup (f := id) hx
  obtain ⟨n, hn, hpin⟩ := hp (y + N₀)
  obtain ⟨n', hn', hpin'⟩ := hp (n + 1)
  refine ⟨n' - n, by omega, T'.image (fun x => n - x),
    ?_, ?_⟩
  · rw [Finset.card_image_of_injOn]
    · exact hT'card
    · intro x₁ h₁ x₂ h₂ heq
      have hx₁ := hTy x₁ (Finset.mem_sdiff.mp h₁).1
      have hx₂ := hTy x₂ (Finset.mem_sdiff.mp h₂).1
      simp only at heq
      omega
  · intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨x, hxT', rfl⟩ := hm
    rw [Finset.mem_sdiff] at hxT'
    obtain ⟨hxT, hxG⟩ := hxT'
    have hxy := hTy x hxT
    have hcone := pinned_pair_fiber hcov hpin hpin'
      (by omega) (hTA x hxT) hxG (by omega)
    exact ⟨hcone.1, by
      have h1 : n - x + (n' - n) =
          (n - x) + (n' - n) := rfl
      exact hcone.2⟩

theorem cleanSupply_failure_forces_fibers {A : Set ℕ}
    {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hfail : ¬ HasCleanSupply A (k + 1)) :
    (∃ H : Finset ℕ, ∀ L, ∃ d, 0 < d ∧
      ∃ S : Finset ℕ, L ≤ S.card ∧
        ∀ m ∈ S, HasSupportTransversalAt A k H m ∧
          HasSupportTransversalAt A k H (m + d)) ∨
    (∃ F : Finset ℕ, ∃ M, ∀ b, b ∈ A → M ≤ b →
      ∃ n, b ≤ n ∧ PinnedAt A (k + 1) F b n) := by
  obtain ⟨F, hclass⟩ :=
    cleanSupply_failure_classification
      (hbasis.of_le (by omega)) hfail
  rcases hclass with ⟨f, _, G, _, _, hp⟩ | htail
  · exact Or.inl ⟨insert f G,
      caseA_large_fibers hbasis hp⟩
  · exact Or.inr ⟨F, htail⟩

end Erdos881
