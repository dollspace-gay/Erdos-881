import Erdos881.InfiniteTripleRamsey

namespace Erdos881

private def PairMapHitsEarly
    (f : ℕ → ℕ → Finset ℕ) (x y z : ℕ) : Prop :=
  x ∈ f y z

private def PairMapHitsMiddle
    (f : ℕ → ℕ → Finset ℕ) (x y z : ℕ) : Prop :=
  if y < z then y ∈ f x z else z ∈ f x y

private def PairMapHitsLate
    (f : ℕ → ℕ → Finset ℕ) (x y z : ℕ) : Prop :=
  if y < z then z ∈ f x y else y ∈ f x z

private theorem pairMapHitsEarly_symmetric
    {f : ℕ → ℕ → Finset ℕ}
    (hsymm : ∀ x y, f x y = f y x) :
    ∀ x, Symmetric (PairMapHitsEarly f x) := by
  intro x y z hyz
  simpa [PairMapHitsEarly, hsymm y z] using hyz

private theorem pairMapHitsMiddle_symmetric
    (f : ℕ → ℕ → Finset ℕ) :
    ∀ x, Symmetric (PairMapHitsMiddle f x) := by
  intro x y z
  by_cases hyz : y < z
  · have hzy : ¬ z < y := Nat.not_lt_of_ge (Nat.le_of_lt hyz)
    simp [PairMapHitsMiddle, hyz, hzy]
  · by_cases hzy : z < y
    · simp [PairMapHitsMiddle, hyz, hzy]
    · have hyEq : y = z := Nat.le_antisymm
        (Nat.le_of_not_gt hzy) (Nat.le_of_not_gt hyz)
      subst z
      simp [PairMapHitsMiddle]

private theorem pairMapHitsLate_symmetric
    (f : ℕ → ℕ → Finset ℕ) :
    ∀ x, Symmetric (PairMapHitsLate f x) := by
  intro x y z
  by_cases hyz : y < z
  · have hzy : ¬ z < y := Nat.not_lt_of_ge (Nat.le_of_lt hyz)
    simp [PairMapHitsLate, hyz, hzy]
  · by_cases hzy : z < y
    · simp [PairMapHitsLate, hyz, hzy]
    · have hyEq : y = z := Nat.le_antisymm
        (Nat.le_of_not_gt hzy) (Nat.le_of_not_gt hyz)
      subst z
      simp [PairMapHitsLate]

private theorem not_infinite_homogeneous_pairMapHitsEarly
    {K : Set ℕ} {f : ℕ → ℕ → Finset ℕ} {r : ℕ}
    (hcard : ∀ x ∈ K, ∀ y ∈ K, x ≠ y → (f x y).card ≤ r) :
    ¬ ∃ L, L ⊆ K ∧ L.Infinite ∧
      ∀ x ∈ L, ∀ y ∈ L, ∀ z ∈ L,
        x < y → y < z → PairMapHitsEarly f x y z := by
  rintro ⟨L, hLK, hL, hhom⟩
  obtain ⟨F, hFL, hFcard⟩ := hL.exists_subset_card_eq (r + 1)
  have hFnonempty : F.Nonempty := by
    apply Finset.card_pos.mp
    rw [hFcard]
    omega
  obtain ⟨y, hyL, hyF⟩ := hL.exists_gt (F.max' hFnonempty)
  obtain ⟨z, hzL, hyz⟩ := hL.exists_gt y
  have hFsub : F ⊆ f y z := by
    intro x hxF
    have hxL : x ∈ L := hFL hxF
    have hxy : x < y := lt_of_le_of_lt
      (Finset.le_max' F x hxF) hyF
    exact hhom x hxL y hyL z hzL hxy hyz
  have hle : r + 1 ≤ (f y z).card := by
    rw [← hFcard]
    exact Finset.card_le_card hFsub
  have hyzNe : y ≠ z := Nat.ne_of_lt hyz
  have := hcard y (hLK hyL) z (hLK hzL) hyzNe
  omega

private theorem not_infinite_homogeneous_pairMapHitsMiddle
    {K : Set ℕ} {f : ℕ → ℕ → Finset ℕ} {r : ℕ}
    (hcard : ∀ x ∈ K, ∀ y ∈ K, x ≠ y → (f x y).card ≤ r) :
    ¬ ∃ L, L ⊆ K ∧ L.Infinite ∧
      ∀ x ∈ L, ∀ y ∈ L, ∀ z ∈ L,
        x < y → y < z → PairMapHitsMiddle f x y z := by
  rintro ⟨L, hLK, hL, hhom⟩
  obtain ⟨x, hxL⟩ := hL.nonempty
  let tail : Set ℕ := L \ Set.Iic x
  have htail : tail.Infinite := hL.diff (Set.finite_Iic x)
  obtain ⟨F, hFtail, hFcard⟩ := htail.exists_subset_card_eq (r + 1)
  have hFnonempty : F.Nonempty := by
    apply Finset.card_pos.mp
    rw [hFcard]
    omega
  obtain ⟨z, hzL, hzF⟩ := hL.exists_gt (F.max' hFnonempty)
  have hFsub : F ⊆ f x z := by
    intro y hyF
    have hyTail := hFtail hyF
    have hyL : y ∈ L := hyTail.1
    have hxy : x < y := Nat.lt_of_not_ge hyTail.2
    have hyz : y < z := lt_of_le_of_lt
      (Finset.le_max' F y hyF) hzF
    have hhit := hhom x hxL y hyL z hzL hxy hyz
    simpa [PairMapHitsMiddle, hyz] using hhit
  have hle : r + 1 ≤ (f x z).card := by
    rw [← hFcard]
    exact Finset.card_le_card hFsub
  have hxz : x < z := by
    obtain ⟨y, hyF⟩ := hFnonempty
    have hyTail := hFtail hyF
    exact lt_trans (Nat.lt_of_not_ge hyTail.2)
      (lt_of_le_of_lt (Finset.le_max' F y hyF) hzF)
  have := hcard x (hLK hxL) z (hLK hzL) (Nat.ne_of_lt hxz)
  omega

private theorem not_infinite_homogeneous_pairMapHitsLate
    {K : Set ℕ} {f : ℕ → ℕ → Finset ℕ} {r : ℕ}
    (hcard : ∀ x ∈ K, ∀ y ∈ K, x ≠ y → (f x y).card ≤ r) :
    ¬ ∃ L, L ⊆ K ∧ L.Infinite ∧
      ∀ x ∈ L, ∀ y ∈ L, ∀ z ∈ L,
        x < y → y < z → PairMapHitsLate f x y z := by
  rintro ⟨L, hLK, hL, hhom⟩
  obtain ⟨x, hxL⟩ := hL.nonempty
  obtain ⟨y, hyL, hxy⟩ := hL.exists_gt x
  let tail : Set ℕ := L \ Set.Iic y
  have htail : tail.Infinite := hL.diff (Set.finite_Iic y)
  obtain ⟨F, hFtail, hFcard⟩ := htail.exists_subset_card_eq (r + 1)
  have hFsub : F ⊆ f x y := by
    intro z hzF
    have hzTail := hFtail hzF
    have hzL : z ∈ L := hzTail.1
    have hyz : y < z := Nat.lt_of_not_ge hzTail.2
    have hhit := hhom x hxL y hyL z hzL hxy hyz
    simpa [PairMapHitsLate, hyz] using hhit
  have hle : r + 1 ≤ (f x y).card := by
    rw [← hFcard]
    exact Finset.card_le_card hFsub
  have := hcard x (hLK hxL) y (hLK hyL) (Nat.ne_of_lt hxy)
  omega

/-- A symmetric uniformly bounded map on unordered pairs has an infinite
free set, provided neither endpoint is assigned to its own pair. -/
theorem exists_infinite_freeSet_of_symmetric_bounded_pairMap
    {K : Set ℕ} (hK : K.Infinite)
    (f : ℕ → ℕ → Finset ℕ) (r : ℕ)
    (hsymm : ∀ x y, f x y = f y x)
    (hcard : ∀ x ∈ K, ∀ y ∈ K, x ≠ y → (f x y).card ≤ r)
    (havoid : ∀ x ∈ K, ∀ y ∈ K, x ≠ y →
      x ∉ f x y ∧ y ∉ f x y) :
    ∃ L, L ⊆ K ∧ L.Infinite ∧
      ∀ x ∈ L, ∀ y ∈ L, x ≠ y →
        Disjoint (f x y : Set ℕ) L := by
  obtain hearly | hearly := infinite_tripleRamsey_nat hK
    (PairMapHitsEarly f) (pairMapHitsEarly_symmetric hsymm)
  · exact (not_infinite_homogeneous_pairMapHitsEarly hcard hearly).elim
  · obtain ⟨K₁, hK₁K, hK₁, hearly⟩ := hearly
    have hcard₁ : ∀ x ∈ K₁, ∀ y ∈ K₁, x ≠ y →
        (f x y).card ≤ r := by
      intro x hx y hy hxy
      exact hcard x (hK₁K hx) y (hK₁K hy) hxy
    obtain hmiddle | hmiddle := infinite_tripleRamsey_nat hK₁
      (PairMapHitsMiddle f) (pairMapHitsMiddle_symmetric f)
    · exact (not_infinite_homogeneous_pairMapHitsMiddle hcard₁ hmiddle).elim
    · obtain ⟨K₂, hK₂K₁, hK₂, hmiddle⟩ := hmiddle
      have hK₂K : K₂ ⊆ K := hK₂K₁.trans hK₁K
      have hcard₂ : ∀ x ∈ K₂, ∀ y ∈ K₂, x ≠ y →
          (f x y).card ≤ r := by
        intro x hx y hy hxy
        exact hcard x (hK₂K hx) y (hK₂K hy) hxy
      obtain hlate | hlate := infinite_tripleRamsey_nat hK₂
        (PairMapHitsLate f) (pairMapHitsLate_symmetric f)
      · exact (not_infinite_homogeneous_pairMapHitsLate hcard₂ hlate).elim
      · obtain ⟨L, hLK₂, hL, hlate⟩ := hlate
        have hLK₁ : L ⊆ K₁ := hLK₂.trans hK₂K₁
        have hLK : L ⊆ K := hLK₂.trans hK₂K
        refine ⟨L, hLK, hL, ?_⟩
        intro x hxL y hyL hxy
        rw [Set.disjoint_left]
        intro z hzMap hzL
        have hxK := hLK hxL
        have hyK := hLK hyL
        have hzNeX : z ≠ x := by
          intro hzx
          subst z
          exact (havoid x hxK y hyK hxy).1 hzMap
        have hzNeY : z ≠ y := by
          intro hzy
          subst z
          exact (havoid x hxK y hyK hxy).2 hzMap
        rcases lt_or_gt_of_ne hxy with hxylt | hyxlt
        · rcases lt_trichotomy z x with hzx | hzx | hxz
          · exact hearly z (hLK₁ hzL) x (hLK₁ hxL)
              y (hLK₁ hyL) hzx hxylt hzMap
          · exact (hzNeX hzx).elim
          · rcases lt_trichotomy z y with hzy | hzy | hyz
            · have hnot := hmiddle x (hLK₂ hxL) z (hLK₂ hzL)
                y (hLK₂ hyL) hxz hzy
              exact hnot (by simpa [PairMapHitsMiddle, hzy] using hzMap)
            · exact (hzNeY hzy).elim
            · have hnot := hlate x hxL y hyL z hzL hxylt hyz
              exact hnot (by simpa [PairMapHitsLate, hyz] using hzMap)
        · have hzMap' : z ∈ f y x := by simpa [hsymm x y] using hzMap
          rcases lt_trichotomy z y with hzy | hzy | hyz
          · exact hearly z (hLK₁ hzL) y (hLK₁ hyL)
              x (hLK₁ hxL) hzy hyxlt hzMap'
          · exact (hzNeY hzy).elim
          · rcases lt_trichotomy z x with hzx | hzx | hxz
            · have hnot := hmiddle y (hLK₂ hyL) z (hLK₂ hzL)
                x (hLK₂ hxL) hyz hzx
              exact hnot (by simpa [PairMapHitsMiddle, hzx] using hzMap')
            · exact (hzNeX hzx).elim
            · have hnot := hlate y hyL x hxL z hzL hyxlt hxz
              exact hnot (by simpa [PairMapHitsLate, hxz] using hzMap')

/-- A uniformly bounded map on individual points also has an infinite free
set when no point is assigned to itself.  Pair Ramsey makes the cross-hit
graph either independent or complete.  A complete infinite graph is
impossible: after choosing `r+1` old vertices, take a new vertex outside all
of their finite images; its own image would then have to contain all `r+1`.
-/
theorem exists_infinite_freeSet_of_bounded_pointMap
    {K : Set ℕ} (hK : K.Infinite)
    (f : ℕ → Finset ℕ) (r : ℕ)
    (hcard : ∀ x ∈ K, (f x).card ≤ r)
    (havoid : ∀ x ∈ K, x ∉ f x) :
    ∃ L, L ⊆ K ∧ L.Infinite ∧
      ∀ x ∈ L, Disjoint (f x : Set ℕ) L := by
  classical
  let R : ℕ → ℕ → Prop := fun x y => y ∈ f x ∨ x ∈ f y
  have hRcomm : Symmetric R := by
    intro x y hxy
    exact hxy.symm
  obtain ⟨L, hLK, hL, hcomplete⟩ | ⟨L, hLK, hL, hindependent⟩ :=
    infinite_pairRamsey_nat hK R hRcomm
  · exfalso
    obtain ⟨F, hFL, hFcard⟩ := hL.exists_subset_card_eq (r + 1)
    let U : Finset ℕ := F ∪ F.biUnion f
    obtain ⟨y, hyL, hyU⟩ := hL.exists_notMem_finset U
    have hyF : y ∉ F := fun hy => hyU (Finset.mem_union_left _ hy)
    have hFsub : F ⊆ f y := by
      intro x hxF
      have hxL : x ∈ L := hFL hxF
      have hxy : x ≠ y := fun hxy => hyF (hxy ▸ hxF)
      rcases hcomplete hxL hyL hxy with hyfx | hxfy
      · apply (hyU (Finset.mem_union_right F ?_)).elim
        exact Finset.mem_biUnion.mpr ⟨x, hxF, hyfx⟩
      · exact hxfy
    have hlower : r + 1 ≤ (f y).card := by
      rw [← hFcard]
      exact Finset.card_le_card hFsub
    have hupper := hcard y (hLK hyL)
    omega
  · refine ⟨L, hLK, hL, ?_⟩
    intro x hxL
    rw [Set.disjoint_left]
    intro y hyfx hyL
    by_cases hxy : x = y
    · subst y
      exact havoid x (hLK hxL) hyfx
    · exact (hindependent hxL hyL hxy) (Or.inl hyfx)

end Erdos881
