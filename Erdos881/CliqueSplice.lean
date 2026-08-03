import Erdos881.RotatingGuardianEndgame
import Erdos881.PinnedMirror

namespace Erdos881

theorem surviving_deletion_of_geometric_windowedDefects
    {A : Set ℕ} {N₀ c w w' : ℕ} (L W d : ℕ → ℕ)
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hmono : StrictMono L)
    (hlev : ∀ k, ∀ z ∈ A, z ≠ d k → z + N₀ < W k → L k - z ∈ A)
    (hmem : ∀ k, L k ∈ A)
    (hgrow : ∀ k, 2 * L k < L (k + 1))
    (hc : c ∈ A) (hc0 : 0 < c) (hcL : c + N₀ < L 0)
    (hcW : ∀ k, 2 * c + N₀ < W k)
    (hLW : ∀ j k, j < k → L j + N₀ < W k)
    (hwA : w ∈ A) (hw'A : w' ∈ A) (hww : w + w' = 2 * c) (hwc : w ≠ c)
    (hcd : ∀ k, c ≠ d k) (hwd : ∀ k, w ≠ d k) (hw'd : ∀ k, w' ≠ d k)
    (hLd : ∀ j k, j < k → L j ≠ d k) :
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
  classical
  have hdiff : ∀ i j, i < j → L 0 + L i < L j :=
    fun i j h => geometric_level_separation hmono hgrow h
  have hcLk : ∀ k, c + N₀ < L k := by
    intro k
    have := hmono.monotone (Nat.zero_le k)
    omega
  have hLpos : ∀ k, 0 < L k := fun k => by have := hcLk k; omega
  have h2cL : ∀ k, 1 ≤ k → 2 * c + N₀ < L k := by
    intro k hk
    have h1 : 2 * L 0 < L 1 := hgrow 0
    have h2 : L 1 ≤ L k := hmono.monotone hk
    omega
  set f : ℕ → ℕ := fun k => L (2 * k + 2) - c with hfdef
  have hmirror : ∀ k, L k - c ∈ A := fun k =>
    hlev k c hc (hcd k) (by have := hcW k; omega)
  have hfA : ∀ k, f k ∈ A := fun k => hmirror _
  have hfinj : Function.Injective f := by
    intro i j hij
    simp only [hfdef] at hij
    have h1 : L (2 * i + 2) = L (2 * j + 2) := by
      have := hcLk (2 * i + 2); have := hcLk (2 * j + 2); omega
    have := hmono.injective h1
    omega
  have hBsub : Set.range f ⊆ A := by rintro v ⟨k, rfl⟩; exact hfA k
  have h0B : (0 : ℕ) ∉ Set.range f := by
    rintro ⟨r, hr⟩
    simp only [hfdef] at hr
    have := hcLk (2 * r + 2)
    omega
  have hgapB : ∀ i j, j < i → L i - L j ∉ Set.range f := by
    rintro i j hji ⟨r, hr⟩
    simp only [hfdef] at hr
    have hLj : L j < L i := hmono hji
    have e : L (2 * r + 2) + L j = L i + c := by
      have := hcLk (2 * r + 2); omega
    rcases Nat.lt_trichotomy i (2 * r + 2) with h | h | h
    · have := hdiff i (2 * r + 2) h
      have : L j ≤ L i := le_of_lt hLj
      omega
    · rw [h] at e
      have := hcLk j
      omega
    · have h2 : L (2 * r + 2) ≤ L (i - 1) := hmono.monotone (by omega)
      have h3 : L j ≤ L (i - 1) := hmono.monotone (by omega)
      have h4 := hgrow (i - 1)
      have h5 : i - 1 + 1 = i := by omega
      rw [h5] at h4
      omega
  have hnearB : ∀ k v, v ≤ 2 * c → v ≠ c → v < L k →
      L k - v ∉ Set.range f := by
    rintro k v hv2 hvc hvk ⟨r, hr⟩
    simp only [hfdef] at hr
    have e : L (2 * r + 2) + v = L k + c := by
      have := hcLk (2 * r + 2); omega
    rcases Nat.lt_trichotomy k (2 * r + 2) with h | h | h
    · have := hdiff k (2 * r + 2) h
      omega
    · rw [h] at e
      omega
    · have := hdiff (2 * r + 2) k h
      omega
  refine ⟨Set.range f, hBsub, Set.infinite_range_of_injective hfinj, ?_⟩
  intro n hn
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov n hn
  by_cases hxB : x ∈ Set.range f
  · obtain ⟨i, hix⟩ := hxB
    simp only [hfdef] at hix
    by_cases hyB : y ∈ Set.range f
    · obtain ⟨j, hjy⟩ := hyB
      simp only [hfdef] at hjy
      have hw'c : w' ≠ c := by omega
      have hwle : w ≤ 2 * c := by omega
      have hw'le : w' ≤ 2 * c := by omega
      rcases le_total j i with hji | hij
      · have hp₁A : L (2 * i + 2) - L (2 * j + 1) ∈ A :=
          hlev (2 * i + 2) _ (hmem (2 * j + 1))
            (hLd (2 * j + 1) (2 * i + 2) (by omega))
            (hLW (2 * j + 1) (2 * i + 2) (by omega))
        have hp₂A : L (2 * j + 1) - w ∈ A :=
          hlev (2 * j + 1) w hwA (hwd _)
            (by have := hcW (2 * j + 1); omega)
        have hp₃A : L (2 * j + 2) - w' ∈ A :=
          hlev (2 * j + 2) w' hw'A (hw'd _)
            (by have := hcW (2 * j + 2); omega)
        refine ⟨_, hp₁A, _, hp₂A, _, hp₃A,
          hgapB (2 * i + 2) (2 * j + 1) (by omega),
          hnearB (2 * j + 1) w hwle hwc
            (by have := h2cL (2 * j + 1) (by omega); omega),
          hnearB (2 * j + 2) w' hw'le hw'c
            (by have := h2cL (2 * j + 2) (by omega); omega), ?_⟩
        have hb1 : L (2 * j + 1) ≤ L (2 * i + 2) :=
          hmono.monotone (by omega)
        have hb2 : w < L (2 * j + 1) := by
          have := h2cL (2 * j + 1) (by omega); omega
        have hb3 : w' < L (2 * j + 2) := by
          have := h2cL (2 * j + 2) (by omega); omega
        have := hcLk (2 * i + 2); have := hcLk (2 * j + 2)
        omega
      · have hp₁A : L (2 * j + 2) - L (2 * i + 1) ∈ A :=
          hlev (2 * j + 2) _ (hmem (2 * i + 1))
            (hLd (2 * i + 1) (2 * j + 2) (by omega))
            (hLW (2 * i + 1) (2 * j + 2) (by omega))
        have hp₂A : L (2 * i + 1) - w ∈ A :=
          hlev (2 * i + 1) w hwA (hwd _)
            (by have := hcW (2 * i + 1); omega)
        have hp₃A : L (2 * i + 2) - w' ∈ A :=
          hlev (2 * i + 2) w' hw'A (hw'd _)
            (by have := hcW (2 * i + 2); omega)
        refine ⟨_, hp₁A, _, hp₂A, _, hp₃A,
          hgapB (2 * j + 2) (2 * i + 1) (by omega),
          hnearB (2 * i + 1) w hwle hwc
            (by have := h2cL (2 * i + 1) (by omega); omega),
          hnearB (2 * i + 2) w' hw'le hw'c
            (by have := h2cL (2 * i + 2) (by omega); omega), ?_⟩
        have hb1 : L (2 * i + 1) ≤ L (2 * j + 2) :=
          hmono.monotone (by omega)
        have hb2 : w < L (2 * i + 1) := by
          have := h2cL (2 * i + 1) (by omega); omega
        have hb3 : w' < L (2 * i + 2) := by
          have := h2cL (2 * i + 2) (by omega); omega
        have := hcLk (2 * i + 2); have := hcLk (2 * j + 2)
        omega
    · have hp₁A : L (2 * i + 1) - c ∈ A := hmirror (2 * i + 1)
      have hp₂A : L (2 * i + 2) - L (2 * i + 1) ∈ A :=
        hlev (2 * i + 2) _ (hmem (2 * i + 1))
          (hLd (2 * i + 1) (2 * i + 2) (by omega))
          (hLW (2 * i + 1) (2 * i + 2) (by omega))
      have hp₁B : L (2 * i + 1) - c ∉ Set.range f := by
        rintro ⟨r, hr⟩
        simp only [hfdef] at hr
        have e : L (2 * i + 1) = L (2 * r + 2) := by
          have := hcLk (2 * i + 1); have := hcLk (2 * r + 2); omega
        have := hmono.injective e
        omega
      refine ⟨_, hp₁A, _, hp₂A, y, hy, hp₁B,
        hgapB (2 * i + 2) (2 * i + 1) (by omega), hyB, ?_⟩
      have hb1 : L (2 * i + 1) ≤ L (2 * i + 2) := hmono.monotone (by omega)
      have := hcLk (2 * i + 1); have := hcLk (2 * i + 2)
      omega
  · by_cases hyB : y ∈ Set.range f
    · obtain ⟨j, hjy⟩ := hyB
      simp only [hfdef] at hjy
      have hp₁A : L (2 * j + 1) - c ∈ A := hmirror (2 * j + 1)
      have hp₂A : L (2 * j + 2) - L (2 * j + 1) ∈ A :=
        hlev (2 * j + 2) _ (hmem (2 * j + 1))
          (hLd (2 * j + 1) (2 * j + 2) (by omega))
          (hLW (2 * j + 1) (2 * j + 2) (by omega))
      have hp₁B : L (2 * j + 1) - c ∉ Set.range f := by
        rintro ⟨r, hr⟩
        simp only [hfdef] at hr
        have e : L (2 * j + 1) = L (2 * r + 2) := by
          have := hcLk (2 * j + 1); have := hcLk (2 * r + 2); omega
        have := hmono.injective e
        omega
      refine ⟨_, hp₁A, _, hp₂A, x, hx, hp₁B,
        hgapB (2 * j + 2) (2 * j + 1) (by omega), hxB, ?_⟩
      have hb1 : L (2 * j + 1) ≤ L (2 * j + 2) := hmono.monotone (by omega)
      have := hcLk (2 * j + 1); have := hcLk (2 * j + 2)
      omega
    · exact ⟨x, hx, y, hy, 0, h0, hxB, hyB, h0B, by omega⟩

theorem surviving_deletion_of_clear_pinned_edges
    {A : Set ℕ} {N₀ N₁ u c : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hred : TwoRedundant A u N₁)
    (hu0 : 0 < u) (hN₀ : N₀ ≤ u) (hN₁ : N₁ ≤ u)
    (hclear : ∀ K, ∃ v m, K < v ∧ u < v ∧ 3 * v ≤ m ∧
      IsPairDestroyer A u v m)
    (hc : c ∈ A) (hc0 : 0 < c) (hcu : c ≠ u)
    (hw : ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ u ∧ w' ≠ u) :
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
  classical
  obtain ⟨w, hwA, w', hw'A, hww, hwc, hwu, hw'u⟩ := hw
  -- level supplier: for any bound K, a level above K whose window
  -- exceeds K as well
  have hsup : ∀ K, ∃ M W', K < M ∧ K + N₀ + 1 < W' ∧ M ∈ A ∧
      W' ≤ M ∧ ∀ z ∈ A, z ≠ u → z + N₀ < W' → M - z ∈ A := by
    intro K
    obtain ⟨v, m, hKv, huv, hclr, hdes⟩ :=
      hclear (K + N₀ + u + 2 * c + 2)
    obtain ⟨hcorep, hmir⟩ :=
      hdes.pinned_level h0 hcov hred hu0 huv hN₀ hN₁ hclr
    refine ⟨m - v, v - u, by omega, by omega, hcorep, by omega, ?_⟩
    intro z hz hzu hzW
    exact hmir z hz hzu (by omega)
  choose nextL nextW hnextM hnextW hnextMem hnextWM hnextMir using hsup
  let L : ℕ → ℕ := fun k =>
    Nat.rec (nextL (2 * c + N₀ + u)) (fun _ prev => nextL (2 * prev)) k
  have hL0 : L 0 = nextL (2 * c + N₀ + u) := rfl
  have hLs : ∀ k, L (k + 1) = nextL (2 * L k) := fun _ => rfl
  have hgrow : ∀ k, 2 * L k < L (k + 1) := by
    intro k
    rw [hLs]
    exact hnextM (2 * L k)
  have hseed : 2 * c + N₀ + u < L 0 := by rw [hL0]; exact hnextM _
  have hmono : StrictMono L := by
    apply strictMono_nat_of_lt_succ
    intro k
    have h1 := hgrow k
    have h2 : 0 < L k := by
      induction k with
      | zero => omega
      | succ k ih => have := hgrow k; omega
    omega
  refine surviving_deletion_of_geometric_windowedDefects L
    (fun k => Nat.rec (nextW (2 * c + N₀ + u))
      (fun j _ => nextW (2 * L j)) k)
    (fun _ => u) h0 hcov hmono ?_ ?_ hgrow hc hc0 (by omega) ?_ ?_
    hwA hw'A hww hwc (fun _ => hcu) (fun _ => hwu) (fun _ => hw'u)
    (fun j k _ => by
      have h1 := hmono.monotone (Nat.zero_le j)
      show L j ≠ u
      omega)
  · intro k
    cases k with
    | zero => exact hnextMir (2 * c + N₀ + u)
    | succ k => exact hnextMir (2 * L k)
  · intro k
    cases k with
    | zero => exact hnextMem (2 * c + N₀ + u)
    | succ k => rw [hLs]; exact hnextMem (2 * L k)
  · intro k
    cases k with
    | zero =>
        have := hnextW (2 * c + N₀ + u)
        show 2 * c + N₀ <
          nextW (2 * c + N₀ + u)
        omega
    | succ k =>
        have h1 := hnextW (2 * L k)
        have h2 : 0 < L k := by
          have := hmono.monotone (Nat.zero_le k)
          omega
        show 2 * c + N₀ < nextW (2 * L k)
        have h3 : c + N₀ < L k := by
          have := hmono.monotone (Nat.zero_le k)
          omega
        omega
  · intro j k hjk
    cases k with
    | zero => omega
    | succ k =>
        have h1 := hnextW (2 * L k)
        have h2 : L j ≤ L k := hmono.monotone (by omega)
        show L j + N₀ < nextW (2 * L k)
        omega

theorem erdos881_combined_criterion {A : Set ℕ} {N₀ : ℕ}
    (hA : A.Infinite) (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfunnel : HasCofinalPairTransversalFamilies A)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g) :
    (∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n) ∨
    (∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A 0 m) ∨
    (∃ L, L ⊆ A ∧ L.Infinite ∧ L.Pairwise (PairTransversalEdge A) ∧
      ∀ u ∈ L, 0 < u → N₀ ≤ u → ∀ N₁, N₁ ≤ u →
        TwoRedundant A u N₁ →
        ∃ K, ∀ v m, K < v → u < v → 3 * v ≤ m →
          ¬ IsPairDestroyer A u v m) := by
  rcases infinite_pairTransversalClique_or_cofinal_privatePairs hA hfunnel with
    ⟨L, hLA, hLinf, hLcl⟩ | ⟨L, hLA, hLinf, hstream⟩
  · by_cases hhug : ∀ u ∈ L, 0 < u → N₀ ≤ u → ∀ N₁, N₁ ≤ u →
        TwoRedundant A u N₁ →
        ∃ K, ∀ v m, K < v → u < v → 3 * v ≤ m →
          ¬ IsPairDestroyer A u v m
    · exact Or.inr (Or.inr ⟨L, hLA, hLinf, hLcl, hhug⟩)
    · push Not at hhug
      obtain ⟨u, huL, hu0, huN₀, N₁, hN₁u, hred, hclear⟩ := hhug
      obtain ⟨c, hc, hc0, hcu, w, hwA, w', hw'A, hww, hwc, hwu, hw'u⟩ :=
        hanchor u
      exact Or.inl (surviving_deletion_of_clear_pinned_edges h0 hcov
        hred hu0 huN₀ hN₁u hclear hc hc0 hcu
        ⟨w, hwA, w', hw'A, hww, hwc, hwu, hw'u⟩)
  · by_cases hz : ∀ N, ∃ a m, N ≤ m ∧ 0 < a ∧ IsPrivateTriple A a m
    · exact Or.inl
        (surviving_deletion_of_cofinal_privateStream h0 hcov hz hanchor)
    · push Not at hz
      obtain ⟨N₂, hN₂⟩ := hz
      refine Or.inr (Or.inl fun N => ?_)
      obtain ⟨v, hvL, m, hm, hpriv⟩ := hstream (max N N₂)
      rcases Nat.eq_zero_or_pos v with hv0 | hv0
      · exact ⟨m, le_trans (le_max_left _ _) hm, hv0 ▸ hpriv⟩
      · exact absurd hpriv
          (hN₂ v m (le_trans (le_max_right _ _) hm) hv0)

end Erdos881
