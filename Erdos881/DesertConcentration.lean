import Erdos881.DirectConstruction

namespace Erdos881

/-- No order-`h` representation over `A` avoids the finite
obstruction `F`. -/
def StrandedAt (A : Set ℕ) (h : ℕ) (F : Finset ℕ)
    (n : ℕ) : Prop :=
  ¬ ∃ v : Fin h → ℕ,
    (∀ i, v i ∈ A ∧ v i ∉ F) ∧ ∑ i, v i = n

/-- Representations avoiding `F` exist and every one uses `f`:
`n` is pinned to `f` in the codeleted model. -/
def PinnedAt (A : Set ℕ) (h : ℕ) (F : Finset ℕ)
    (f n : ℕ) : Prop :=
  (∃ v : Fin h → ℕ,
    (∀ i, v i ∈ A ∧ v i ∉ F) ∧ ∑ i, v i = n) ∧
  ∀ v : Fin h → ℕ, (∀ i, v i ∈ A ∧ v i ∉ F) →
    ∑ i, v i = n → ∃ i, v i = f

/-- Strandedness splits one obstruction element at a time. -/
theorem stranded_insert_split {A : Set ℕ} {h : ℕ}
    {G : Finset ℕ} {f n : ℕ}
    (hn : StrandedAt A h (insert f G) n) :
    StrandedAt A h G n ∨ PinnedAt A h G f n := by
  classical
  by_cases hex : ∃ v : Fin h → ℕ,
      (∀ i, v i ∈ A ∧ v i ∉ G) ∧ ∑ i, v i = n
  · right
    refine ⟨hex, ?_⟩
    intro v hv hsum
    by_contra hcon
    push Not at hcon
    refine hn ⟨v, fun i => ⟨(hv i).1, ?_⟩, hsum⟩
    rw [Finset.mem_insert]
    push Not
    exact ⟨hcon i, (hv i).2⟩
  · exact Or.inl hex

/-- Stranded targets descend along codeleted summands: appending
`a` to a surviving representation of `n - a` would revive `n`. -/
theorem StrandedAt.descend {A : Set ℕ} {h : ℕ}
    {F : Finset ℕ} {n a : ℕ}
    (hn : StrandedAt A (h + 1) F n)
    (ha : a ∈ A) (haF : a ∉ F) (hle : a ≤ n) :
    StrandedAt A h F (n - a) := by
  rintro ⟨w, hw, hwsum⟩
  refine hn ⟨Fin.cons a w, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ ?_ i
    · simp only [Fin.cons_zero]
      exact ⟨ha, haF⟩
    · intro j
      simp only [Fin.cons_succ]
      exact hw j
  · rw [Fin.sum_cons, hwsum]
    omega

theorem stranded_concentration (A : Set ℕ) (h : ℕ)
    (F : Finset ℕ)
    (hunb : ∀ M, ∃ n, M ≤ n ∧ StrandedAt A h F n) :
    (∀ M, ∃ n, M ≤ n ∧ StrandedAt A h ∅ n) ∨
    ∃ f ∈ F, ∃ G ⊆ F, f ∉ G ∧
      ∀ M, ∃ n, M ≤ n ∧ PinnedAt A h G f n := by
  classical
  revert hunb
  induction F using Finset.induction_on with
  | empty => exact fun hunb => Or.inl hunb
  | @insert f G hf ih =>
    intro hunb
    by_cases hG : ∀ M, ∃ n, M ≤ n ∧
        StrandedAt A h G n
    · rcases ih hG with h1 | ⟨f', hf', G', hG', hfG', hp⟩
      · exact Or.inl h1
      · exact Or.inr ⟨f',
          Finset.mem_insert_of_mem hf', G',
          hG'.trans (Finset.subset_insert f G),
          hfG', hp⟩
    · push Not at hG
      obtain ⟨T, hT⟩ := hG
      right
      refine ⟨f, Finset.mem_insert_self f G, G,
        Finset.subset_insert f G, hf, ?_⟩
      intro M
      obtain ⟨n, hn, hstr⟩ := hunb (max M T)
      rcases stranded_insert_split hstr with h1 | h1
      · exact absurd h1
          (hT n (le_trans (le_max_right _ _) hn))
      · exact ⟨n, le_trans (le_max_left _ _) hn, h1⟩

/-- A basis has no unbounded empty-obstruction exclusion interval. -/
theorem stranded_empty_bounded {A : Set ℕ} {h : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A h) :
    ∃ T, ∀ n, T ≤ n → ¬ StrandedAt A h ∅ n := by
  obtain ⟨N, hN⟩ := hbasis
  refine ⟨N, fun n hn hstr => ?_⟩
  obtain ⟨v, hv, hsum⟩ := hN n hn
  exact hstr ⟨v, fun i =>
    ⟨hv i, Finset.notMem_empty _⟩, hsum⟩

theorem exclusion_interval_forces_pinned {A : Set ℕ} {h : ℕ}
    {F : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A h)
    (hunb : ∀ M, ∃ n, M ≤ n ∧ StrandedAt A h F n) :
    ∃ f ∈ F, ∃ G ⊆ F, f ∉ G ∧
      ∀ M, ∃ n, M ≤ n ∧ PinnedAt A h G f n := by
  rcases stranded_concentration A h F hunb with h1 | h1
  · obtain ⟨T, hT⟩ := stranded_empty_bounded hbasis
    obtain ⟨n, hn, hstr⟩ := h1 T
    exact absurd hstr (hT n hn)
  · exact h1

theorem pinned_unbounded_iff_deletion_fails {A : Set ℕ}
    {h : ℕ} {F : Finset ℕ} {f : ℕ}
    (hbasis :
      IsExactTupleAsymptoticBasis (A \ ↑F) h) :
    (∀ M, ∃ n, M ≤ n ∧ PinnedAt A h F f n) ↔
    ¬ IsExactTupleAsymptoticBasis
      ((A \ ↑F) \ {f}) h := by
  constructor
  · rintro hp ⟨N, hN⟩
    obtain ⟨n, hn, hex, hall⟩ := hp N
    obtain ⟨v, hv, hsum⟩ := hN n hn
    obtain ⟨i, hi⟩ := hall v
      (fun i => ⟨(hv i).1.1, fun hmem =>
        (hv i).1.2 (Finset.mem_coe.mpr hmem)⟩)
      hsum
    exact (hv i).2 (by rw [hi]; rfl)
  · intro hfail
    obtain ⟨N₁, hN₁⟩ := hbasis
    intro M
    unfold IsExactTupleAsymptoticBasis at hfail
    push Not at hfail
    obtain ⟨n, hn, hno⟩ := hfail (max M N₁)
    obtain ⟨w, hw, hwsum⟩ :=
      hN₁ n (le_trans (le_max_right _ _) hn)
    have hglue : ∀ v : Fin h → ℕ,
        (∀ i, v i ∈ A ∧ v i ∉ F) →
        ∑ i, v i = n → ∃ i, v i = f := by
      intro v hv hsum
      by_contra hcon
      push Not at hcon
      exact hno v (fun i =>
        ⟨⟨(hv i).1, fun hmem =>
          (hv i).2 (Finset.mem_coe.mp hmem)⟩,
          hcon i⟩) hsum
    refine ⟨n, le_trans (le_max_left _ _) hn,
      ⟨w, fun i => ⟨(hw i).1, fun hmem =>
        (hw i).2 (Finset.mem_coe.mpr hmem)⟩,
        hwsum⟩, hglue⟩

theorem pinned_forces_gap {A : Set ℕ} {k : ℕ}
    {F : Finset ℕ} {b n : ℕ}
    (hpin : PinnedAt A (k + 1) F b n)
    (a : Fin k → ℕ)
    (ha : ∀ i, a i ∈ A ∧ a i ∉ F ∧ a i ≠ b)
    (hle : ∑ i, a i ≤ n) :
    n - ∑ i, a i = b ∨ n - ∑ i, a i ∉ A ∨
      n - ∑ i, a i ∈ F := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hne, hmem, hF⟩ := hcon
  obtain ⟨-, hall⟩ := hpin
  set w : Fin (k + 1) → ℕ :=
    Fin.cons (n - ∑ i, a i) a with hw
  have hmemall : ∀ i, w i ∈ A ∧ w i ∉ F := by
    intro i
    refine Fin.cases ?_ ?_ i
    · rw [hw]
      simp only [Fin.cons_zero]
      exact ⟨hmem, hF⟩
    · intro j
      rw [hw]
      simp only [Fin.cons_succ]
      exact ⟨(ha j).1, (ha j).2.1⟩
  obtain ⟨i, hi⟩ := hall w hmemall
    (by rw [hw, Fin.sum_cons]; omega)
  have hnotb : ∀ i, w i ≠ b := by
    intro i
    refine Fin.cases ?_ ?_ i
    · rw [hw]
      simp only [Fin.cons_zero]
      exact hne
    · intro j
      rw [hw]
      simp only [Fin.cons_succ]
      exact (ha j).2.2
  exact hnotb i hi

theorem cleanSupply_failure_classification {A : Set ℕ}
    {h : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A h)
    (hfail : ¬ HasCleanSupply A h) :
    ∃ F : Finset ℕ,
      (∃ f ∈ F, ∃ G ⊆ F, f ∉ G ∧
        ∀ M, ∃ n, M ≤ n ∧ PinnedAt A h G f n) ∨
      (∃ M, ∀ b, b ∈ A → M ≤ b →
        ∃ n, b ≤ n ∧ PinnedAt A h F b n) := by
  classical
  unfold HasCleanSupply at hfail
  push Not at hfail
  obtain ⟨F, M₀, hM₀⟩ := hfail
  refine ⟨F, ?_⟩
  have hwit : ∀ b, b ∈ A → M₀ ≤ b → ∃ n, b ≤ n ∧
      StrandedAt A h (insert b F) n := by
    intro b hbA hbM
    have hnc := hM₀ b hbA hbM
    unfold CleanlyRedundantAbove at hnc
    push Not at hnc
    obtain ⟨n, hn, hno⟩ := hnc
    refine ⟨n, hn, ?_⟩
    rintro ⟨v, hv, hsum⟩
    refine hno v (fun i => ?_) hsum
    have h2 := (hv i).2
    rw [Finset.mem_insert] at h2
    push Not at h2
    exact ⟨(hv i).1, h2.2, h2.1⟩
  by_cases hdes : ∀ M, ∃ n, M ≤ n ∧
      StrandedAt A h F n
  · exact Or.inl (exclusion_interval_forces_pinned hbasis hdes)
  · push Not at hdes
    obtain ⟨T, hT⟩ := hdes
    right
    refine ⟨max M₀ T, ?_⟩
    intro b hbA hbM
    obtain ⟨n, hn, hstr⟩ := hwit b hbA
      (le_trans (le_max_left _ _) hbM)
    rcases stranded_insert_split hstr with h1 | h1
    · exact absurd h1 (hT n (by
        have := le_max_right M₀ T
        omega))
    · exact ⟨n, hn, h1⟩

end Erdos881
