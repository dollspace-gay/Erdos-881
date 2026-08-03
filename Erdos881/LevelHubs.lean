import Erdos881.FunnelTrichotomy

namespace Erdos881

/-- A covering set has at least `√(W + 1 - N₀)` elements up to `W`:
the pairs from `A ∩ [0, W]` must cover the whole interval `[N₀, W]`. -/
theorem pairCovers_card_lower {A : Set ℕ} [DecidablePred (· ∈ A)]
    {N₀ W : ℕ} (hcov : PairCovers A N₀) (_hW : N₀ ≤ W) :
    W + 1 - N₀ ≤
      ((Finset.range (W + 1)).filter fun a => a ∈ A).card ^ 2 := by
  set T := (Finset.range (W + 1)).filter fun a => a ∈ A with hT
  have hsub : Finset.Icc N₀ W ⊆ (T ×ˢ T).image fun p => p.1 + p.2 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    obtain ⟨x, hx, y, hy, hxy⟩ := hcov n hn.1
    refine Finset.mem_image.mpr
      ⟨(x, y), Finset.mem_product.mpr ⟨?_, ?_⟩, hxy⟩
    · simp only [hT, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hx⟩
    · simp only [hT, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hy⟩
  calc W + 1 - N₀
      = (Finset.Icc N₀ W).card := by rw [Nat.card_Icc]
    _ ≤ ((T ×ˢ T).image fun p => p.1 + p.2).card :=
        Finset.card_le_card hsub
    _ ≤ (T ×ˢ T).card := Finset.card_image_le
    _ = T.card * T.card := Finset.card_product T T
    _ = T.card ^ 2 := by ring

theorem level_avoiding_pair {A D : Set ℕ}
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ D)]
    {N₀ u v M : ℕ}
    (hcov : PairCovers A N₀)
    (hmir : ∀ x ∈ A, x ≠ u → u + x < v → M - x ∈ A)
    (hvM : v ≤ M)
    (hsparse : N₀ + u + 1 +
      (2 * ((Finset.range (M + 1)).filter fun d => d ∈ D).card + 2) ^ 2
        ≤ v) :
    ∃ x ∈ A, x ≠ u ∧ u + x < v ∧ x ∉ D ∧ M - x ∉ D ∧ M - x ∈ A := by
  set δ := ((Finset.range (M + 1)).filter fun d => d ∈ D).card with hδ
  set W := v - u - 1 with hW
  set T := (Finset.range (W + 1)).filter fun a => a ∈ A with hT
  have hcard : W + 1 - N₀ ≤ T.card ^ 2 :=
    pairCovers_card_lower hcov (by omega)
  have hTlarge : 2 * δ + 2 ≤ T.card := by
    by_contra hsmall
    push Not at hsmall
    have h1 : T.card ^ 2 ≤ (2 * δ + 1) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    have h2 : (2 * δ + 1) ^ 2 < (2 * δ + 2) ^ 2 :=
      Nat.pow_lt_pow_left (by omega) (by omega)
    omega
  -- bad elements: u itself, window elements in D, reflections in D
  set badD := T.filter fun x => x ∈ D with hbadD
  set badR := T.filter fun x => M - x ∈ D with hbadR
  have hbadD_le : badD.card ≤ δ := by
    refine Finset.card_le_card ?_
    intro x hx
    simp only [hbadD, hT, Finset.mem_filter, Finset.mem_range] at hx
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hx.2⟩
  have hbadR_le : badR.card ≤ δ := by
    have hinj : Set.InjOn (fun x => M - x) badR := by
      intro a ha b hb hab
      simp only [hbadR, hT, Finset.mem_filter, Finset.mem_range,
        Finset.coe_filter, Set.mem_setOf_eq] at ha hb
      simp only at hab
      omega
    calc badR.card
        = (badR.image fun x => M - x).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ δ := by
          refine Finset.card_le_card ?_
          intro y hy
          simp only [Finset.mem_image] at hy
          obtain ⟨x, hx, rfl⟩ := hy
          simp only [hbadR, hT, Finset.mem_filter, Finset.mem_range]
            at hx
          simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, hx.2⟩
  have hgood : (T \ (badD ∪ badR ∪ {u})).Nonempty := by
    rw [← Finset.card_pos]
    have hle : (badD ∪ badR ∪ {u}).card ≤ 2 * δ + 1 := by
      calc (badD ∪ badR ∪ {u}).card
          ≤ (badD ∪ badR).card + ({u} : Finset ℕ).card :=
            Finset.card_union_le _ _
        _ ≤ badD.card + badR.card + 1 := by
            have := Finset.card_union_le badD badR
            simp only [Finset.card_singleton]
            omega
        _ ≤ 2 * δ + 1 := by omega
    have := Finset.le_card_sdiff (badD ∪ badR ∪ {u}) T
    omega
  obtain ⟨x, hx⟩ := hgood
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton,
    hbadD, hbadR, hT, Finset.mem_filter, Finset.mem_range] at hx
  push Not at hx
  obtain ⟨⟨hxr, hxA⟩, hxbad⟩ := hx
  have hxu : x ≠ u := hxbad.2
  have hxD : x ∉ D := hxbad.1.1 ⟨hxr, hxA⟩
  have hxR : M - x ∉ D := hxbad.1.2 ⟨hxr, hxA⟩
  exact ⟨x, hxA, hxu, by omega, hxD, hxR,
    hmir x hxA hxu (by omega)⟩

theorem survives_through_level {A D : Set ℕ}
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ D)]
    {N₀ u v M n : ℕ}
    (hcov : PairCovers A N₀)
    (hmir : ∀ x ∈ A, x ≠ u → u + x < v → M - x ∈ A)
    (hvM : v ≤ M)
    (hsparse : N₀ + u + 1 +
      (2 * ((Finset.range (M + 1)).filter fun d => d ∈ D).card + 2) ^ 2
        ≤ v)
    (hMn : M ≤ n) (hnA : n - M ∈ A) (hnD : n - M ∉ D) :
    ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
      x ∉ D ∧ y ∉ D ∧ z ∉ D ∧ x + y + z = n := by
  obtain ⟨x, hxA, hxu, hxv, hxD, hxR, hxM⟩ :=
    level_avoiding_pair hcov hmir hvM hsparse
  exact ⟨n - M, hnA, x, hxA, M - x, hxM, hnD, hxD, hxR, by omega⟩

theorem levelHitting_survival {A D : Set ℕ}
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ D)]
    {N₀ N₁ : ℕ} (hcov : PairCovers A N₀)
    (Lev win₁ win₂ : ℕ → ℕ)
    (hmir : ∀ k, ∀ x ∈ A, x ≠ win₁ k → win₁ k + x < win₂ k →
      Lev k - x ∈ A)
    (hvM : ∀ k, win₂ k ≤ Lev k)
    (hsparse : ∀ k, N₀ + win₁ k + 1 +
      (2 * ((Finset.range (Lev k + 1)).filter fun d => d ∈ D).card
        + 2) ^ 2 ≤ win₂ k)
    (hhit : ∀ n, N₁ ≤ n → ∃ k, Lev k ≤ n ∧
      n - Lev k ∈ A ∧ n - Lev k ∉ D) :
    IsExactTupleAsymptoticBasis (A \ D) 3 := by
  refine exactTupleBasis_diff_of_survival (N₁ := N₁) ?_
  intro n hn
  obtain ⟨k, hkn, hkA, hkD⟩ := hhit n hn
  obtain ⟨x, hx, y, hy, z, hz, hxD, hyD, hzD, hsum⟩ :=
    survives_through_level hcov (hmir k) (hvM k) (hsparse k)
      hkn hkA hkD
  exact ⟨x, hx, y, hy, z, hz, hxD, hyD, hzD, hsum⟩

end Erdos881
