import Erdos881.RedundantVertexKill
import Erdos881.FunnelTrichotomy

namespace Erdos881

/-- Upper exclusion interval, arbitrary threshold: the per-point condition
`N₁ ≤ u + x` replaces `N₁ ≤ u`. -/
theorem IsPairDestroyer.upper_exclusion_interval_of_redundant'
    {A : Set ℕ} {N₀ N₁ u v m x : ℕ}
    (hcov : PairCovers A N₀)
    (hred : TwoRedundant A u N₁)
    (hdes : IsPairDestroyer A u v m)
    (huv : u < v)
    (hx : x ∈ A) (hxu : x ≠ u) (hxN : N₁ ≤ u + x)
    (hxm : x + N₀ ≤ m) (hxum : u + x ≤ m) (hwin : u + x < v)
    (hxvm : m < v + x)
    (hd1 : m ≠ 2 * u + x) (hd2 : m ≠ u + v + x) :
    False := by
  obtain ⟨s, hs, t, ht, hst, hsu, htu⟩ := hred (u + x) hxN
  obtain ⟨y, hy, z, hz, hyz⟩ := hcov (m - x) (by omega)
  rcases hdes.2 x hx y hy z hz (by omega) with h | h | h | h | h | h
  · exact absurd h hxu
  · have hw : m - u - x ∈ A := by
      have hz' : z = m - u - x := by omega
      exact hz' ▸ hz
    exact hdes.pinned_sharp hs ht hst hsu (by omega) htu (by omega)
      hxum hd1 hd2 hw
  · have hw : m - u - x ∈ A := by
      have hy' : y = m - u - x := by omega
      exact hy' ▸ hy
    exact hdes.pinned_sharp hs ht hst hsu (by omega) htu (by omega)
      hxum hd1 hd2 hw
  · omega
  · omega
  · omega

/-- Levels cannot lag, arbitrary threshold: windows floored at `N₁`. -/
theorem IsPairDestroyer.level_lower_of_redundant'
    {A : Set ℕ} {N₀ N₁ u v m : ℕ}
    (hcov : PairCovers A N₀)
    (hred : TwoRedundant A u N₁)
    (hdes : IsPairDestroyer A u v m)
    (hu0 : 0 < u) (huv : u < v) (hvm : v ≤ m)
    (hbig : 100 * ((m - v) + u + N₀ + N₁ + 3) ≤ v) :
    False := by
  set W := (m - v) + u + N₀ + N₁ + 2 with hW
  have hkill : ∀ x ∈ A, m - v < x → u + x < v → x + N₀ ≤ m →
      N₁ ≤ x → x ≠ u → x ≠ m - 2 * u → x ≠ m - u - v → False := by
    intro x hxA hxl hxw hxm hxN hxu hxd1 hxd2
    exact hdes.upper_exclusion_interval_of_redundant' hcov hred huv hxA hxu
      (by omega) hxm (by omega) hxw (by omega) (by omega) (by omega)
  have hwin : ∀ q, W ≤ q → q + u + N₀ < v →
      ∃ x ∈ A, 2 * x ≥ q ∧ x ≤ q := by
    intro q hql hqh
    obtain ⟨y, hy, z, hz, hyz⟩ := hcov q (by omega)
    rcases le_total y z with h | h
    · exact ⟨z, hz, by omega, by omega⟩
    · exact ⟨y, hy, by omega, by omega⟩
  obtain ⟨x₁, hx₁A, hx₁l, hx₁r⟩ := hwin (2 * W) (by omega) (by omega)
  obtain ⟨x₂, hx₂A, hx₂l, hx₂r⟩ := hwin (10 * W) (by omega) (by omega)
  obtain ⟨x₃, hx₃A, hx₃l, hx₃r⟩ := hwin (50 * W) (by omega) (by omega)
  by_cases e₁ : x₁ = m - 2 * u ∨ x₁ = m - u - v
  · by_cases e₂ : x₂ = m - 2 * u ∨ x₂ = m - u - v
    · exact hkill x₃ hx₃A (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)
    · push Not at e₂
      exact hkill x₂ hx₂A (by omega) (by omega) (by omega) (by omega)
        (by omega) e₂.1 e₂.2
  · push Not at e₁
    exact hkill x₁ hx₁A (by omega) (by omega) (by omega) (by omega)
      (by omega) e₁.1 e₁.2

/-- The fork mirror, arbitrary threshold: valid for `z = 0` (via the
non-primitivity of `u`) and for `z` above the floor. -/
theorem IsPairDestroyer.redundant_edge_mirror''
    {A : Set ℕ} {N₀ N₁ u v m z : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hred : TwoRedundant A u N₁)
    (hprim : ∃ s ∈ A, ∃ t ∈ A, s + t = u ∧ s ≠ u ∧ t ≠ u)
    (hdes : IsPairDestroyer A u v m)
    (huv : u < v) (hvm : v ≤ m)
    (hz : z ∈ A) (hzu : z ≠ u) (hzfloor : z = 0 ∨ N₁ ≤ u + z)
    (hd1 : m ≠ 2 * u + z) (hd2 : m ≠ u + v + z)
    (hzw : z + N₀ + u < v) :
    m - v - z ∈ A := by
  rcases Nat.lt_or_ge (m - v) z with hzM | hzM
  · have : m - v - z = 0 := by omega
    rw [this]
    exact h0
  · have hrep : ∃ s ∈ A, ∃ t ∈ A,
        s + t = u + z ∧ s ≠ u ∧ s ≠ v ∧ t ≠ u ∧ t ≠ v := by
      rcases hzfloor with hz0 | hzN
      · obtain ⟨s, hs, t, ht, hst, hsu, htu⟩ := hprim
        subst hz0
        exact ⟨s, hs, t, ht, by omega, hsu, by omega, htu, by omega⟩
      · obtain ⟨s, hs, t, ht, hst, hsu, htu⟩ := hred (u + z) hzN
        exact ⟨s, hs, t, ht, hst, hsu, by omega, htu, by omega⟩
    have hzv : z ≠ v := by omega
    have hzm : z + N₀ ≤ m := by omega
    have hzum : u + z ≤ m := by omega
    exact hdes.pinned_mirror_sharp hcov hz hzu hzv hzm hzum hrep
      hd1 hd2

theorem surviving_deletion_of_flooredQuadDefects
    {A : Set ℕ} {N₀ c w w' F : ℕ} (L W d₁ d₂ d₃ d₄ : ℕ → ℕ)
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hmono : StrictMono L)
    (hlev : ∀ k, ∀ z ∈ A, (z = 0 ∨ F ≤ z) → z ≠ d₁ k → z ≠ d₂ k →
      z ≠ d₃ k → z ≠ d₄ k → z + N₀ < W k → L k - z ∈ A)
    (hmem : ∀ k, L k ∈ A)
    (hgrow : ∀ k, 2 * L k < L (k + 1))
    (hc : c ∈ A) (hc0 : 0 < c) (hcL : c + N₀ < L 0)
    (hcF : F ≤ c) (hLF : F ≤ L 0)
    (hwF : w = 0 ∨ F ≤ w) (hw'F : w' = 0 ∨ F ≤ w')
    (hcW : ∀ k, 2 * c + N₀ < W k)
    (hLW : ∀ j k, j < k → L j + N₀ < W k)
    (hwA : w ∈ A) (hw'A : w' ∈ A) (hww : w + w' = 2 * c) (hwc : w ≠ c)
    (hcd : ∀ k, c ≠ d₁ k ∧ c ≠ d₂ k ∧ c ≠ d₃ k ∧ c ≠ d₄ k)
    (hwd : ∀ k, w ≠ d₁ k ∧ w ≠ d₂ k ∧ w ≠ d₃ k ∧ w ≠ d₄ k)
    (hw'd : ∀ k, w' ≠ d₁ k ∧ w' ≠ d₂ k ∧ w' ≠ d₃ k ∧ w' ≠ d₄ k)
    (hLd : ∀ j k, j < k →
      L j ≠ d₁ k ∧ L j ≠ d₂ k ∧ L j ≠ d₃ k ∧ L j ≠ d₄ k) :
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
    hlev k c hc (Or.inr hcF) (hcd k).1 (hcd k).2.1 (hcd k).2.2.1 (hcd k).2.2.2
      (by have := hcW k; omega)
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
            (Or.inr (le_trans hLF
              (hmono.monotone (Nat.zero_le _))))
            (hLd (2 * j + 1) (2 * i + 2) (by omega)).1
            (hLd (2 * j + 1) (2 * i + 2) (by omega)).2.1
            (hLd (2 * j + 1) (2 * i + 2) (by omega)).2.2.1
            (hLd (2 * j + 1) (2 * i + 2) (by omega)).2.2.2
            (hLW (2 * j + 1) (2 * i + 2) (by omega))
        have hp₂A : L (2 * j + 1) - w ∈ A :=
          hlev (2 * j + 1) w hwA hwF (hwd _).1 (hwd _).2.1 (hwd _).2.2.1
            (hwd _).2.2.2
            (by have := hcW (2 * j + 1); omega)
        have hp₃A : L (2 * j + 2) - w' ∈ A :=
          hlev (2 * j + 2) w' hw'A hw'F (hw'd _).1 (hw'd _).2.1 (hw'd _).2.2.1
            (hw'd _).2.2.2
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
            (Or.inr (le_trans hLF
              (hmono.monotone (Nat.zero_le _))))
            (hLd (2 * i + 1) (2 * j + 2) (by omega)).1
            (hLd (2 * i + 1) (2 * j + 2) (by omega)).2.1
            (hLd (2 * i + 1) (2 * j + 2) (by omega)).2.2.1
            (hLd (2 * i + 1) (2 * j + 2) (by omega)).2.2.2
            (hLW (2 * i + 1) (2 * j + 2) (by omega))
        have hp₂A : L (2 * i + 1) - w ∈ A :=
          hlev (2 * i + 1) w hwA hwF (hwd _).1 (hwd _).2.1 (hwd _).2.2.1
            (hwd _).2.2.2
            (by have := hcW (2 * i + 1); omega)
        have hp₃A : L (2 * i + 2) - w' ∈ A :=
          hlev (2 * i + 2) w' hw'A hw'F (hw'd _).1 (hw'd _).2.1 (hw'd _).2.2.1
            (hw'd _).2.2.2
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
          (Or.inr (le_trans hLF
            (hmono.monotone (Nat.zero_le _))))
          (hLd (2 * i + 1) (2 * i + 2) (by omega)).1
          (hLd (2 * i + 1) (2 * i + 2) (by omega)).2.1
          (hLd (2 * i + 1) (2 * i + 2) (by omega)).2.2.1
          (hLd (2 * i + 1) (2 * i + 2) (by omega)).2.2.2
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
          (Or.inr (le_trans hLF
            (hmono.monotone (Nat.zero_le _))))
          (hLd (2 * j + 1) (2 * j + 2) (by omega)).1
          (hLd (2 * j + 1) (2 * j + 2) (by omega)).2.1
          (hLd (2 * j + 1) (2 * j + 2) (by omega)).2.2.1
          (hLd (2 * j + 1) (2 * j + 2) (by omega)).2.2.2
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

theorem surviving_deletion_of_nonessential_edges
    {A : Set ℕ} {N₀ N₁ u c : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hred : TwoRedundant A u N₁)
    (hprim : ∃ s ∈ A, ∃ t ∈ A, s + t = u ∧ s ≠ u ∧ t ≠ u)
    (hu0 : 0 < u)
    (hsupply : ∀ K, ∃ v m, K < v ∧ u < v ∧ v ≤ m ∧
      IsPairDestroyer A u v m)
    (hc : c ∈ A) (h2c : 2 * c ∈ A) (hc0 : 0 < c)
    (hcN : N₁ ≤ c) (hcu : c ≠ u) (h2cu : 2 * c ≠ u) :
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
  classical
  choose pv pm hpK hpu hpvm hpdes using hsupply
  set b : ℕ → ℕ := fun x =>
    200 * (x + c + u + N₀ + N₁ + 3) with hb
  set κ : ℕ → ℕ := fun k =>
    Nat.rec (u + c + N₀ + N₁ + 1)
      (fun _ p => pm (b p) - pv (b p)) k with hκ
  set L : ℕ → ℕ := fun k => κ (k + 1) with hLdef
  have hLeq : ∀ k, L k = pm (b (κ k)) - pv (b (κ k)) := fun _ => rfl
  have hstep : ∀ k, 2 * κ k + 2 * c + 2 < L k ∧ L k ∈ A ∧
      u < L k ∧
      u < pv (b (κ k)) ∧ pv (b (κ k)) ≤ pm (b (κ k)) ∧
      200 * (κ k + c + u + N₀ + N₁ + 3) < pv (b (κ k)) ∧
      ∀ z ∈ A, (z = 0 ∨ N₁ ≤ z) → z ≠ u → z ≠ pv (b (κ k)) →
        z ≠ pm (b (κ k)) - 2 * u →
        z ≠ pm (b (κ k)) - u - pv (b (κ k)) →
        z + N₀ + u < pv (b (κ k)) - u → L k - z ∈ A := by
    intro k
    have h1 := hpK (b (κ k))
    have h2 := hpu (b (κ k))
    have h3 := hpvm (b (κ k))
    have h5 := hpdes (b (κ k))
    have hbk : b (κ k) = 200 * (κ k + c + u + N₀ + N₁ + 3) := rfl
    have h1' : 200 * (κ k + c + u + N₀ + N₁ + 3) < pv (b (κ k)) :=
      lt_of_eq_of_lt hbk.symm h1
    have hlow : ¬ (100 * ((pm (b (κ k)) - pv (b (κ k))) +
        u + N₀ + N₁ + 3) ≤ pv (b (κ k))) :=
      fun h => h5.level_lower_of_redundant' hcov hred hu0 h2 h3 h
    have hLk : L k = pm (b (κ k)) - pv (b (κ k)) := hLeq k
    have hLbig : 2 * κ k + 2 * c + 2 < L k := by
      rw [hLk]; omega
    have hLu : u < L k := by rw [hLk]; omega
    have hLu' : u < pm (b (κ k)) - pv (b (κ k)) := by
      have h := hLu
      rw [hLk] at h
      exact h
    have hd1 : pm (b (κ k)) ≠ 2 * u := by omega
    have hd2 : pm (b (κ k)) ≠ u + pv (b (κ k)) := by omega
    refine ⟨hLbig, ?_, hLu, h2, h3, h1', ?_⟩
    · rw [hLk]
      have hcor := h5.redundant_edge_mirror'' h0 hcov hred hprim h2 h3
        h0 (by omega) (Or.inl rfl) (by omega) (by omega) (by omega)
      simpa using hcor
    · intro z hz hzfl hzu hzv hzd1 hzd2 hzw
      rw [hLk]
      exact h5.redundant_edge_mirror'' h0 hcov hred hprim h2 h3
        hz hzu (by omega) (by omega) (by omega) (by omega)
  have hκmono : ∀ k, κ k < κ (k + 1) := by
    intro k
    have h1 := (hstep k).1
    have h2 : L k = κ (k + 1) := rfl
    omega
  have hκK₀ : ∀ k, u + c + N₀ + N₁ + 1 ≤ κ k := by
    intro k
    induction k with
    | zero => exact le_refl _
    | succ k ih => have := hκmono k; omega
  have hgrow : ∀ k, 2 * L k < L (k + 1) := by
    intro k
    have h1 := (hstep (k + 1)).1
    have h2 : κ (k + 1) = L k := rfl
    omega
  have hmono : StrictMono L := by
    apply strictMono_nat_of_lt_succ
    intro k
    have h1 := hgrow k
    have h2 := (hstep k).1
    omega
  have hκle : ∀ i₂ i₁, i₁ ≤ i₂ → κ i₁ ≤ κ i₂ := by
    intro i₂
    induction i₂ with
    | zero =>
        intro i₁ h
        have h0' : i₁ = 0 := by omega
        subst h0'
        exact le_refl _
    | succ i₂ ih =>
        intro i₁ h
        rcases Nat.lt_or_ge i₁ (i₂ + 1) with h' | h'
        · have hm := hκmono i₂
          have h2 := ih i₁ (by omega)
          omega
        · have he : i₁ = i₂ + 1 := by omega
          subst he
          exact le_refl _
  have hLκ : ∀ j k, j < k → L j ≤ κ k := by
    intro j k hjk
    have h1 : L j = κ (j + 1) := rfl
    have := hκle k (j + 1) (by omega)
    omega
  have hvbig : ∀ k,
      200 * (κ k + c + u + N₀ + N₁ + 3) < pv (b (κ k)) :=
    fun k => (hstep k).2.2.2.2.2.1
  refine surviving_deletion_of_flooredQuadDefects (F := N₁) L
    (fun k => pv (b (κ k)) - u - u - N₀)
    (fun _ => u) (fun k => pv (b (κ k)))
    (fun k => pm (b (κ k)) - 2 * u)
    (fun k => pm (b (κ k)) - u - pv (b (κ k)))
    h0 hcov hmono ?_
    (fun k => (hstep k).2.1) hgrow hc hc0 ?_ hcN ?_
    (Or.inl rfl) (Or.inr (by omega)) ?_ ?_
    h0 h2c (by omega) (by omega) ?_ ?_ ?_ ?_
  · intro k z hz hzfl hz1 hz2 hz3 hz4 hzW
    have h := (hstep k).2.2.2.2.2.2 z hz hzfl hz1 hz2 hz3 hz4
    have hW : z + N₀ + u < pv (b (κ k)) - u := by
      show z + N₀ + u < pv (b (κ k)) - u
      have h1 := hvbig k
      have hzW' : z + N₀ < pv (b (κ k)) - u - u - N₀ := hzW
      omega
    exact h hW
  · have h1 := (hstep 0).1
    have h2 := hκK₀ 0
    omega
  · have h1 := (hstep 0).1
    have h2 := hκK₀ 0
    show N₁ ≤ L 0
    omega
  · intro k
    have h1 := hvbig k
    show 2 * c + N₀ < pv (b (κ k)) - u - u - N₀
    omega
  · intro j k hjk
    have h1 := hvbig k
    have h3 := hLκ j k hjk
    show L j + N₀ < pv (b (κ k)) - u - u - N₀
    omega
  · intro k
    have h1 := hvbig k
    have h2 := (hstep k).2.2.2.1
    have h3 := (hstep k).2.2.2.2.1
    have h5 := (hstep k).1
    have h6 := hLeq k
    have h7 := hκK₀ k
    show c ≠ u ∧ c ≠ pv (b (κ k)) ∧
      c ≠ pm (b (κ k)) - 2 * u ∧
      c ≠ pm (b (κ k)) - u - pv (b (κ k))
    exact ⟨hcu, by omega, by omega, by omega⟩
  · intro k
    have h1 := hvbig k
    have h2 := (hstep k).2.2.2.1
    have h3 := (hstep k).2.2.2.2.1
    have h5 := (hstep k).1
    have h6 := hLeq k
    have h7 := hκK₀ k
    show (0 : ℕ) ≠ u ∧ (0 : ℕ) ≠ pv (b (κ k)) ∧
      (0 : ℕ) ≠ pm (b (κ k)) - 2 * u ∧
      (0 : ℕ) ≠ pm (b (κ k)) - u - pv (b (κ k))
    exact ⟨by omega, by omega, by omega, by omega⟩
  · intro k
    have h1 := hvbig k
    have h2 := (hstep k).2.2.2.1
    have h3 := (hstep k).2.2.2.2.1
    have h5 := (hstep k).1
    have h6 := hLeq k
    have h7 := hκK₀ k
    show 2 * c ≠ u ∧ 2 * c ≠ pv (b (κ k)) ∧
      2 * c ≠ pm (b (κ k)) - 2 * u ∧
      2 * c ≠ pm (b (κ k)) - u - pv (b (κ k))
    exact ⟨h2cu, by omega, by omega, by omega⟩
  · intro j k hjk
    have h1 := hvbig k
    have h2 := (hstep k).2.2.2.1
    have h3 := (hstep k).2.2.2.2.1
    have h5 := (hstep k).1
    have h6 := hLeq k
    have h7 := hLκ j k hjk
    have h8 := (hstep j).1
    have h9 := hκK₀ j
    have h10 := (hstep j).2.2.1
    show L j ≠ u ∧ L j ≠ pv (b (κ k)) ∧
      L j ≠ pm (b (κ k)) - 2 * u ∧
      L j ≠ pm (b (κ k)) - u - pv (b (κ k))
    exact ⟨by omega, by omega, by omega, by omega⟩

theorem erdos881_combined_criterion₄ {A : Set ℕ} {N₀ : ℕ}
    (hA : A.Infinite) (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfunnel : HasCofinalPairTransversalFamilies A)
    (hdb : {c | c ∈ A ∧ 2 * c ∈ A ∧ 0 < c}.Infinite)
    (hnz : ∃ c ∈ A, 0 < c ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ 0 < w ∧ 0 < w') :
    (∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n) ∨
    (∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A 0 m) ∨
    (∃ L, L ⊆ A ∧ L.Infinite ∧ L.Pairwise (PairTransversalEdge A) ∧
      ∀ u ∈ L, 0 < u →
        (¬ ∃ s ∈ A, ∃ t ∈ A, s + t = u ∧ s ≠ u ∧ t ≠ u) ∨
        (∀ N₁, ¬ TwoRedundant A u N₁)) := by
  have hanchor := anchor_abundance_of_doubling h0 hdb hnz
  rcases infinite_pairTransversalClique_or_cofinal_privatePairs hA hfunnel with
    ⟨L, hLA, hLinf, hLcl⟩ | ⟨L, hLA, hLinf, hstream⟩
  · by_cases hesc : ∀ u ∈ L, 0 < u →
        (¬ ∃ s ∈ A, ∃ t ∈ A, s + t = u ∧ s ≠ u ∧ t ≠ u) ∨
        (∀ N₁, ¬ TwoRedundant A u N₁)
    · exact Or.inr (Or.inr ⟨L, hLA, hLinf, hLcl, hesc⟩)
    · push Not at hesc
      obtain ⟨u, huL, hu0, hprim, N₁, hred⟩ := hesc
      obtain ⟨c, hcmem, hcg⟩ := hdb.exists_gt (max N₁ u)
      obtain ⟨hcA, h2cA, hc0⟩ := hcmem
      refine Or.inl (surviving_deletion_of_nonessential_edges h0 hcov
        hred hprim hu0 (fun K => ?_) hcA h2cA hc0
        (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hcg))
        (by have := lt_of_le_of_lt (le_max_right _ _) hcg; omega)
        (by have := lt_of_le_of_lt (le_max_right _ _) hcg; omega))
      obtain ⟨v, hvL, hv⟩ := hLinf.exists_gt (max K u)
      have hKv : K < v := lt_of_le_of_lt (le_max_left _ _) hv
      have huv : u < v := lt_of_le_of_lt (le_max_right _ _) hv
      obtain ⟨-, m, hum, hvm, hdes⟩ := hLcl huL hvL (by omega)
      exact ⟨v, m, hKv, huv, hvm, hdes⟩
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

/-- A primitive element is two-required by zero: its only two-term
representation is `0 + u`. -/
theorem primitive_zero_required {A : Set ℕ} {u : ℕ}
    (hu0 : 0 < u)
    (hprim : ¬ ∃ s ∈ A, ∃ t ∈ A, s + t = u ∧ s ≠ u ∧ t ≠ u) :
    ∀ y ∈ A, ∀ z ∈ A, y + z = u → y = 0 ∨ z = 0 := by
  intro y hy z hz hyz
  by_contra hne
  push Not at hne
  exact hprim ⟨y, hy, z, hz, hyz, by omega, by omega⟩

theorem zero_essential_of_infinite_primitives {A L : Set ℕ}
    (hL : L.Infinite) (hLA : L ⊆ A)
    (hprims : ∀ u ∈ L, 0 < u ∧
      ¬ ∃ s ∈ A, ∃ t ∈ A, s + t = u ∧ s ≠ u ∧ t ≠ u) :
    ∀ N, ¬ TwoRedundant A 0 N := by
  intro N hred
  obtain ⟨u, huL, huN⟩ := hL.exists_gt N
  obtain ⟨hu0, hprim⟩ := hprims u huL
  obtain ⟨s, hs, t, ht, hst, hs0, ht0⟩ := hred u (by omega)
  rcases primitive_zero_required hu0 hprim s hs t ht hst with h | h
  · exact hs0 h
  · exact ht0 h

theorem essential_witness_repels_translate {A : Set ℕ} {u c : ℕ}
    (h0 : 0 ∈ A) (hu0 : 0 < u) (hc0 : 0 < c)
    (hwit : ∀ y ∈ A, ∀ z ∈ A, y + z = u + c → y = u ∨ z = u)
    (hmem : u + c ∈ A) :
    False := by
  rcases hwit 0 h0 (u + c) hmem (by omega) with h | h <;> omega

theorem surviving_deletion_of_reflectionFamilies
    {A : Set ℕ} {N₀ c w w' : ℕ} (L : ℕ → ℕ)
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hmono : StrictMono L)
    (hgrow : ∀ k, 2 * L k < L (k + 1))
    (hc : c ∈ A) (hc0 : 0 < c) (hcL : c + N₀ < L 0)
    (hwA : w ∈ A) (hw'A : w' ∈ A) (hww : w + w' = 2 * c) (hwc : w ≠ c)
    (hLc : ∀ k, L k - c ∈ A)
    (hLw : ∀ k, L k - w ∈ A)
    (hLw' : ∀ k, L k - w' ∈ A)
    (hLL : ∀ j k, j < k → L k - L j ∈ A) :
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
  have hmirror : ∀ k, L k - c ∈ A := hLc
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
          hLL (2 * j + 1) (2 * i + 2) (by omega)
        have hp₂A : L (2 * j + 1) - w ∈ A :=
          hLw (2 * j + 1)
        have hp₃A : L (2 * j + 2) - w' ∈ A :=
          hLw' (2 * j + 2)
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
          hLL (2 * i + 1) (2 * j + 2) (by omega)
        have hp₂A : L (2 * i + 1) - w ∈ A :=
          hLw (2 * i + 1)
        have hp₃A : L (2 * i + 2) - w' ∈ A :=
          hLw' (2 * i + 2)
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
        hLL (2 * i + 1) (2 * i + 2) (by omega)
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
        hLL (2 * j + 1) (2 * j + 2) (by omega)
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

theorem surviving_deletion_of_avoidable_levels
    {A : Set ℕ} {N₀ u c : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hprim : ∃ s ∈ A, ∃ t ∈ A, s + t = u ∧ s ≠ u ∧ t ≠ u)
    (hu0 : 0 < u)
    (hc : c ∈ A) (hc0 : 0 < c) (hcu : c ≠ u)
    (hac : ∃ s ∈ A, ∃ t ∈ A, s + t = u + c ∧ s ≠ u ∧ t ≠ u)
    (h2c : 2 * c ∈ A) (h2cu : 2 * c ≠ u)
    (ha2c : ∃ s ∈ A, ∃ t ∈ A, s + t = u + 2 * c ∧ s ≠ u ∧ t ≠ u)
    (hsupply : ∀ K, ∃ v m, K < v ∧ u < v ∧ v ≤ m ∧ K < m - v ∧
      IsPairDestroyer A u v m ∧
      ∃ s ∈ A, ∃ t ∈ A, s + t = u + (m - v) ∧ s ≠ u ∧ t ≠ u) :
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
  classical
  choose pv pm hpK hpu hpvm hpL hpdes hpav using hsupply
  set b : ℕ → ℕ := fun x => 2 * x + u + 2 * c + N₀ + 2 with hb
  set κ : ℕ → ℕ := fun k =>
    Nat.rec (u + 2 * c + N₀ + 2)
      (fun _ p => pm (b p) - pv (b p)) k with hκ
  set L : ℕ → ℕ := fun k => κ (k + 1) with hLdef
  have hLeq : ∀ k, L k = pm (b (κ k)) - pv (b (κ k)) := fun _ => rfl
  -- the generic mirror at level k
  have hmirror : ∀ k, ∀ z ∈ A, z ≠ u → z + u + N₀ + 1 < pv (b (κ k)) →
      (∃ s ∈ A, ∃ t ∈ A, s + t = u + z ∧ s ≠ u ∧ t ≠ u) →
      pm (b (κ k)) ≠ 2 * u + z →
      pm (b (κ k)) ≠ u + pv (b (κ k)) + z →
      L k - z ∈ A := by
    intro k z hz hzu hzw hrep hd1 hd2
    obtain ⟨s, hs, t, ht, hst, hsu, htu⟩ := hrep
    have h2 := hpu (b (κ k))
    have h3 := hpvm (b (κ k))
    have h5 := hpdes (b (κ k))
    have hLk : L k = pm (b (κ k)) - pv (b (κ k)) := hLeq k
    rw [hLk]
    exact h5.pinned_mirror_sharp hcov hz hzu (by omega) (by omega)
      (by omega)
      ⟨s, hs, t, ht, hst, hsu, by omega, htu, by omega⟩ hd1 hd2
  -- level facts
  have hstep : ∀ k, 2 * κ k + u + 2 * c + N₀ + 2 < L k ∧ L k ∈ A ∧
      b (κ k) < pv (b (κ k)) := by
    intro k
    have h1 := hpK (b (κ k))
    have h2 := hpu (b (κ k))
    have h3 := hpvm (b (κ k))
    have h4 := hpL (b (κ k))
    have h5 := hpdes (b (κ k))
    have hbk : b (κ k) = 2 * κ k + u + 2 * c + N₀ + 2 := rfl
    have hLk : L k = pm (b (κ k)) - pv (b (κ k)) := hLeq k
    have hLbig : 2 * κ k + u + 2 * c + N₀ + 2 < L k := by
      rw [hLk]; omega
    refine ⟨hLbig, ?_, h1⟩
    obtain ⟨s, hs, t, ht, hst, hsu, htu⟩ := hprim
    have hcor := hmirror k 0 h0 (by omega) (by omega)
      ⟨s, hs, t, ht, by omega, hsu, htu⟩ (by omega) (by omega)
    simpa using hcor
  have hκmono : ∀ k, κ k < κ (k + 1) := by
    intro k
    have h1 := (hstep k).1
    have h2 : L k = κ (k + 1) := rfl
    omega
  have hκK₀ : ∀ k, u + 2 * c + N₀ + 2 ≤ κ k := by
    intro k
    induction k with
    | zero => exact le_refl _
    | succ k ih => have := hκmono k; omega
  have hgrow : ∀ k, 2 * L k < L (k + 1) := by
    intro k
    have h1 := (hstep (k + 1)).1
    have h2 : κ (k + 1) = L k := rfl
    omega
  have hmono : StrictMono L := by
    apply strictMono_nat_of_lt_succ
    intro k
    have h1 := hgrow k
    have h2 := (hstep k).1
    omega
  have hκle : ∀ i₂ i₁, i₁ ≤ i₂ → κ i₁ ≤ κ i₂ := by
    intro i₂
    induction i₂ with
    | zero =>
        intro i₁ h
        have h0' : i₁ = 0 := by omega
        subst h0'
        exact le_refl _
    | succ i₂ ih =>
        intro i₁ h
        rcases Nat.lt_or_ge i₁ (i₂ + 1) with h' | h'
        · have hm := hκmono i₂
          have h2 := ih i₁ (by omega)
          omega
        · have he : i₁ = i₂ + 1 := by omega
          subst he
          exact le_refl _
  have hLκ : ∀ j k, j < k → L j ≤ κ k := by
    intro j k hjk
    have h1 : L j = κ (j + 1) := rfl
    have := hκle k (j + 1) (by omega)
    omega
  refine surviving_deletion_of_reflectionFamilies L h0 hcov hmono
    hgrow hc hc0 ?_ h0 h2c (by omega) (by omega) ?_ ?_ ?_ ?_
  · have h1 := (hstep 0).1
    have h2 := hκK₀ 0
    omega
  -- hLc
  · intro k
    have hs := hstep k
    have h2 := hpu (b (κ k))
    have h3 := hpvm (b (κ k))
    have hκb := hκK₀ k
    have hbk : b (κ k) = 2 * κ k + u + 2 * c + N₀ + 2 := rfl
    have hLk : L k = pm (b (κ k)) - pv (b (κ k)) := hLeq k
    exact hmirror k c hc hcu (by omega)
      hac (by omega) (by omega)
  -- hLw (w = 0)
  · intro k
    have hs := hstep k
    have h := hs.2.1
    simpa using h
  -- hLw' (w' = 2c)
  · intro k
    have hs := hstep k
    have h2 := hpu (b (κ k))
    have h3 := hpvm (b (κ k))
    have hκb := hκK₀ k
    have hbk : b (κ k) = 2 * κ k + u + 2 * c + N₀ + 2 := rfl
    have hLk : L k = pm (b (κ k)) - pv (b (κ k)) := hLeq k
    exact hmirror k (2 * c) h2c h2cu (by omega)
      ha2c (by omega) (by omega)
  -- hLL
  · intro j k hjk
    have hsj := hstep j
    have hsk := hstep k
    have h2 := hpu (b (κ k))
    have h3 := hpvm (b (κ k))
    have hκb := hκK₀ k
    have hLjκ := hLκ j k hjk
    have hLj := hLeq j
    have hbk : b (κ k) = 2 * κ k + u + 2 * c + N₀ + 2 := rfl
    have hLk : L k = pm (b (κ k)) - pv (b (κ k)) := hLeq k
    have hκbj := hκK₀ j
    have hav := hpav (b (κ j))
    obtain ⟨s, hs, t, ht, hst, hsu, htu⟩ := hav
    exact hmirror k (L j) hsj.2.1 (by omega) (by omega)
      ⟨s, hs, t, ht, by omega, hsu, htu⟩ (by omega) (by omega)

theorem erdos881_combined_criterion₅ {A : Set ℕ} {N₀ : ℕ}
    (hA : A.Infinite) (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfunnel : HasCofinalPairTransversalFamilies A)
    (hdb : {c | c ∈ A ∧ 2 * c ∈ A ∧ 0 < c}.Infinite)
    (hnz : ∃ c ∈ A, 0 < c ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ 0 < w ∧ 0 < w') :
    (∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n) ∨
    (∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A 0 m) ∨
    (∃ L, L ⊆ A ∧ L.Infinite ∧ L.Pairwise (PairTransversalEdge A) ∧
      ∀ u ∈ L, 0 < u →
        (¬ ∃ s ∈ A, ∃ t ∈ A, s + t = u ∧ s ≠ u ∧ t ≠ u) ∨
        (∀ c, c ∈ A → 2 * c ∈ A → u < c →
          (¬ ∃ s ∈ A, ∃ t ∈ A, s + t = u + c ∧ s ≠ u ∧ t ≠ u) ∨
          (¬ ∃ s ∈ A, ∃ t ∈ A, s + t = u + 2 * c ∧ s ≠ u ∧ t ≠ u)) ∨
        (∃ K, ∀ v m, K < v → u < v → v ≤ m →
          IsPairDestroyer A u v m →
          m - v ≤ K ∨
          ¬ ∃ s ∈ A, ∃ t ∈ A, s + t = u + (m - v) ∧ s ≠ u ∧ t ≠ u)) := by
  rcases infinite_pairTransversalClique_or_cofinal_privatePairs hA hfunnel with
    ⟨L, hLA, hLinf, hLcl⟩ | ⟨L, hLA, hLinf, hstream⟩
  · by_cases hesc : ∀ u ∈ L, 0 < u →
        (¬ ∃ s ∈ A, ∃ t ∈ A, s + t = u ∧ s ≠ u ∧ t ≠ u) ∨
        (∀ c, c ∈ A → 2 * c ∈ A → u < c →
          (¬ ∃ s ∈ A, ∃ t ∈ A, s + t = u + c ∧ s ≠ u ∧ t ≠ u) ∨
          (¬ ∃ s ∈ A, ∃ t ∈ A, s + t = u + 2 * c ∧ s ≠ u ∧ t ≠ u)) ∨
        (∃ K, ∀ v m, K < v → u < v → v ≤ m →
          IsPairDestroyer A u v m →
          m - v ≤ K ∨
          ¬ ∃ s ∈ A, ∃ t ∈ A, s + t = u + (m - v) ∧ s ≠ u ∧ t ≠ u)
    · exact Or.inr (Or.inr ⟨L, hLA, hLinf, hLcl, hesc⟩)
    · push Not at hesc
      obtain ⟨u, huL, hu0, hprim, hanch, halign⟩ := hesc
      obtain ⟨cc, hccA, h2cc, hccu, hacc, ha2cc⟩ := hanch
      refine Or.inl (surviving_deletion_of_avoidable_levels h0 hcov
        hprim hu0 hccA (by omega) (by omega) hacc h2cc (by omega)
        ha2cc (fun K => ?_))
      obtain ⟨v, m, hKv, huv, hvm, hdes, hlev, hav⟩ := halign K
      exact ⟨v, m, hKv, huv, hvm, by omega, hdes, hav⟩
  · have hanchor := anchor_abundance_of_doubling h0 hdb hnz
    by_cases hz : ∀ N, ∃ a m, N ≤ m ∧ 0 < a ∧ IsPrivateTriple A a m
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

theorem witness_level_translate_exit {A : Set ℕ} {u L c : ℕ}
    (hwit : ∀ y ∈ A, ∀ z ∈ A, y + z = u + L → y = u ∨ z = u)
    (hcL : c ≤ L) (hLuc : L ≠ u + c) (hc0 : 0 < c)
    (huc : u + c ∈ A) (hLc : L - c ∈ A) :
    False := by
  rcases hwit (L - c) hLc (u + c) huc (by omega) with h | h <;> omega

theorem witness_levels_difference_exit {A : Set ℕ} {u L₁ L₂ : ℕ}
    (hwit₂ : ∀ y ∈ A, ∀ z ∈ A, y + z = u + L₂ → y = u ∨ z = u)
    (hL₁A : L₁ ∈ A) (hlt : L₁ < L₂) (hL₁u : L₁ ≠ u)
    (hmem : u + L₂ - L₁ ∈ A) :
    False := by
  rcases hwit₂ (u + L₂ - L₁) hmem L₁ hL₁A (by omega) with h | h
  · omega
  · exact hL₁u h

theorem witness_branch_level_mem {A : Set ℕ} {N₀ u v m : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hprim : ∃ s ∈ A, ∃ t ∈ A, s + t = u ∧ s ≠ u ∧ t ≠ u)
    (hdes : IsPairDestroyer A u v m)
    (hu0 : 0 < u) (huv : u < v) (hvm : v < m)
    (hN₀ : N₀ ≤ m) (h2u : 2 * u ≠ m) (hLu : m - v ≠ u)
    (hwit : ∀ y ∈ A, ∀ z ∈ A, y + z = u + (m - v) → y = u ∨ z = u) :
    m - v ∈ A ∧ u + (m - v) ∉ A := by
  obtain ⟨s, hs, t, ht, hst, hsu, htu⟩ := hprim
  constructor
  · have hsv : s ≠ v := by omega
    have htv : t ≠ v := by omega
    have hsum0 : s + t = u + 0 := by omega
    have hd1' : m ≠ 2 * u + 0 := by omega
    have hd2' : m ≠ u + v + 0 := by omega
    have h := hdes.pinned_mirror_sharp hcov h0 (by omega) (by omega)
      (by omega) (by omega)
      ⟨s, hs, t, ht, hsum0, hsu, hsv, htu, htv⟩
      hd1' hd2'
    simpa using h
  · intro hmem
    rcases hwit 0 h0 (u + (m - v)) hmem (by omega) with h | h <;>
      omega

theorem anchor_fork_forced {A : Set ℕ} {N₀ u v m c : ℕ}
    (hcov : PairCovers A N₀)
    (hdes : IsPairDestroyer A u v m)
    (hwit : ∀ y ∈ A, ∀ z ∈ A, y + z = u + (m - v) → y = u ∨ z = u)
    (hcA : c ∈ A) (hucA : u + c ∈ A)
    (hc0 : 0 < c) (hcu : c ≠ u) (hcv : c ≠ v)
    (hcm : c + N₀ ≤ m) (hcL : c ≤ m - v) (hLuc : m - v ≠ u + c)
    (hvm : v ≤ m) :
    m - u - c ∈ A := by
  obtain ⟨y, hy, z, hz, hyz⟩ := hcov (m - c) (by omega)
  rcases hdes.2 c hcA y hy z hz (by omega) with h | h | h | h | h | h
  · exact absurd h hcu
  · have hz' : z = m - u - c := by omega
    exact hz' ▸ hz
  · have hy' : y = m - u - c := by omega
    exact hy' ▸ hy
  · exact absurd h hcv
  · have hz' : z = m - v - c := by omega
    exact absurd (hz' ▸ hz)
      (fun hmem => witness_level_translate_exit hwit hcL hLuc hc0
        hucA (by
          have : m - v - c = m - v - c := rfl
          exact hmem))
  · have hy' : y = m - v - c := by omega
    exact absurd (hy' ▸ hy)
      (fun hmem => witness_level_translate_exit hwit hcL hLuc hc0
        hucA hmem)

theorem cross_edge_catch {A : Set ℕ} {N₀ u v₁ v₂ m₂ m' c : ℕ}
    (hcov : PairCovers A N₀)
    (hdes₂ : IsPairDestroyer A u v₂ m₂)
    (hwit : ∀ y ∈ A, ∀ z ∈ A, y + z = u + (m₂ - v₂) → y = u ∨ z = u)
    (hdes' : IsPairDestroyer A v₁ v₂ m')
    (hcA : c ∈ A) (hucA : u + c ∈ A)
    (hc0 : 0 < c) (hcu : c ≠ u) (hcv : c ≠ v₂)
    (hcm : c + N₀ ≤ m₂) (hcL : c ≤ m₂ - v₂) (hLuc : m₂ - v₂ ≠ u + c)
    (hv₂m : v₂ ≤ m₂)
    (hv₁0 : 0 < v₁) (hv₁₂ : v₁ < v₂)
    (hpv₁ : v₁ < m₂ - u - c) (hpv₂ : m₂ - u - c ≠ v₂)
    (hlow : m' < v₁ + (m₂ - u - c))
    (hhigh : (m₂ - u - c) + N₀ ≤ m') :
    False := by
  have hp := anchor_fork_forced hcov hdes₂ hwit hcA hucA hc0 hcu hcv
    hcm hcL hLuc hv₂m
  have h := hdes'.exclusion_interval hcov hv₁0 hv₁₂ hp hlow hhigh
  omega

theorem erdos881_combined_criterion₆ {A : Set ℕ} {N₀ : ℕ}
    (hA : A.Infinite) (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfunnel : HasCofinalPairTransversalFamilies A)
    (hdb : {c | c ∈ A ∧ 2 * c ∈ A ∧ 0 < c}.Infinite)
    (hnz : ∃ c ∈ A, 0 < c ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ 0 < w ∧ 0 < w') :
    (∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n) ∨
    (∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A 0 m) ∨
    (∃ L, L ⊆ A ∧ L.Infinite ∧ L.Pairwise (PairTransversalEdge A) ∧
      ∀ u ∈ L, 0 < u →
        (¬ ∃ s ∈ A, ∃ t ∈ A, s + t = u ∧ s ≠ u ∧ t ≠ u) ∨
        ((∀ N₁, ¬ TwoRedundant A u N₁) ∧
          ((∀ c, c ∈ A → 2 * c ∈ A → u < c →
            (¬ ∃ s ∈ A, ∃ t ∈ A, s + t = u + c ∧ s ≠ u ∧ t ≠ u) ∨
            (¬ ∃ s ∈ A, ∃ t ∈ A,
              s + t = u + 2 * c ∧ s ≠ u ∧ t ≠ u)) ∨
          (∃ K, ∀ v m, K < v → u < v → v ≤ m →
            IsPairDestroyer A u v m →
            m - v ≤ K ∨
            ¬ ∃ s ∈ A, ∃ t ∈ A,
              s + t = u + (m - v) ∧ s ≠ u ∧ t ≠ u)))) := by
  rcases infinite_pairTransversalClique_or_cofinal_privatePairs hA hfunnel with
    ⟨L, hLA, hLinf, hLcl⟩ | ⟨L, hLA, hLinf, hstream⟩
  · by_cases hesc : ∀ u ∈ L, 0 < u →
        (¬ ∃ s ∈ A, ∃ t ∈ A, s + t = u ∧ s ≠ u ∧ t ≠ u) ∨
        ((∀ N₁, ¬ TwoRedundant A u N₁) ∧
          ((∀ c, c ∈ A → 2 * c ∈ A → u < c →
            (¬ ∃ s ∈ A, ∃ t ∈ A, s + t = u + c ∧ s ≠ u ∧ t ≠ u) ∨
            (¬ ∃ s ∈ A, ∃ t ∈ A,
              s + t = u + 2 * c ∧ s ≠ u ∧ t ≠ u)) ∨
          (∃ K, ∀ v m, K < v → u < v → v ≤ m →
            IsPairDestroyer A u v m →
            m - v ≤ K ∨
            ¬ ∃ s ∈ A, ∃ t ∈ A,
              s + t = u + (m - v) ∧ s ≠ u ∧ t ≠ u)))
    · exact Or.inr (Or.inr ⟨L, hLA, hLinf, hLcl, hesc⟩)
    · push Not at hesc
      obtain ⟨u, huL, hu0, hprim, hrest⟩ := hesc
      by_cases hred : ∃ N₁, TwoRedundant A u N₁
      · -- non-essential: the pointwise contradiction
        obtain ⟨N₁, hredN⟩ := hred
        obtain ⟨c, hcmem, hcg⟩ := hdb.exists_gt (max N₁ u)
        obtain ⟨hcA, h2cA, hc0⟩ := hcmem
        refine Or.inl (surviving_deletion_of_nonessential_edges h0
          hcov hredN hprim hu0 (fun K => ?_) hcA h2cA hc0
          (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hcg))
          (by have := lt_of_le_of_lt (le_max_right _ _) hcg; omega)
          (by have := lt_of_le_of_lt (le_max_right _ _) hcg; omega))
        obtain ⟨v, hvL, hv⟩ := hLinf.exists_gt (max K u)
        have hKv : K < v := lt_of_le_of_lt (le_max_left _ _) hv
        have huv : u < v := lt_of_le_of_lt (le_max_right _ _) hv
        obtain ⟨-, m, hum, hvm, hdes⟩ := hLcl huL hvL (by omega)
        exact ⟨v, m, hKv, huv, hvm, hdes⟩
      · -- essential: the avoidable-levels contradiction
        push Not at hred
        have hess : ∀ N₁, ¬ TwoRedundant A u N₁ := hred
        have hWneg := hrest hess
        obtain ⟨hanch, halign⟩ := hWneg
        obtain ⟨cc, hccA, h2cc, hccu, hacc, ha2cc⟩ := hanch
        refine Or.inl (surviving_deletion_of_avoidable_levels h0 hcov
          hprim hu0 hccA (by omega) (by omega) hacc h2cc (by omega)
          ha2cc (fun K => ?_))
        obtain ⟨v, m, hKv, huv, hvm, hdes, hlev, hav⟩ := halign K
        exact ⟨v, m, hKv, huv, hvm, by omega, hdes, hav⟩
  · have hanchor := anchor_abundance_of_doubling h0 hdb hnz
    by_cases hz : ∀ N, ∃ a m, N ≤ m ∧ 0 < a ∧ IsPrivateTriple A a m
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

theorem zero_required_iff_primitive {A : Set ℕ} {N₀ n : ℕ}
    (hcov : PairCovers A N₀) (hn : N₀ ≤ n) (hn0 : 0 < n) :
    (∀ y ∈ A, ∀ z ∈ A, y + z = n → y = 0 ∨ z = 0) ↔
    (n ∈ A ∧ ¬ ∃ s ∈ A, ∃ t ∈ A, s + t = n ∧ 0 < s ∧ 0 < t) := by
  constructor
  · intro hguard
    obtain ⟨y, hy, z, hz, hyz⟩ := hcov n hn
    constructor
    · rcases hguard y hy z hz hyz with h | h
      · have : z = n := by omega
        exact this ▸ hz
      · have : y = n := by omega
        exact this ▸ hy
    · rintro ⟨s, hs, t, ht, hst, hs0, ht0⟩
      rcases hguard s hs t ht hst with h | h <;> omega
  · rintro ⟨hnA, hprim⟩ y hy z hz hyz
    by_contra hne
    push Not at hne
    exact hprim ⟨y, hy, z, hz, hyz, by omega, by omega⟩

theorem deletion_dichotomy_of_anchors {A B : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ C ⊆ A, C.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ C) 3)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hBA : B ⊆ A) (h0B : 0 ∉ B) (hBpos : ∀ b ∈ B, 0 < b)
    (hBinf : B.Infinite) :
    ∀ N, ∃ m, N ≤ m ∧
      ((∃ u ∈ B, ∃ v ∈ B, IsPairDestroyer A u v m) ∨
      (∃ y ∈ A, ∃ z ∈ A, y + z = m ∧ (y ∈ B ∨ z ∈ B) ∧
        ∃ x' ∈ A, ∃ y' ∈ A, ∃ z' ∈ A, x' + y' + z' = m ∧
          (y ∈ B → x' ≠ y ∧ y' ≠ y ∧ z' ≠ y) ∧
          (z ∈ B → x' ≠ z ∧ y' ≠ z ∧ z' ≠ z))) := by
  by_cases hsing : ∀ N, ∃ m, N ≤ m ∧
      ∃ u ∈ B, u ∈ A ∧ IsPrivateTriple A u m
  · -- cofinal singleton transversal_families: the stream contradiction fires
    exfalso
    have hstream : ∀ N, ∃ a m, N ≤ m ∧ 0 < a ∧
        IsPrivateTriple A a m := by
      intro N
      obtain ⟨m, hm, u, huB, huA, hpriv⟩ := hsing N
      exact ⟨u, m, hm, hBpos u huB, hpriv⟩
    obtain ⟨C, hCA, hCinf, hsurv⟩ :=
      surviving_deletion_of_cofinal_privateStream h0 hcov hstream
        hanchor
    exact hfail C hCA hCinf (exactTupleBasis_diff_of_survival hsurv)
  · push Not at hsing
    obtain ⟨N₁, hN₁⟩ := hsing
    intro N
    obtain ⟨m, hm, htri⟩ :=
      cofinal_transversal_family_trichotomy_of_deletionFailure h0 h0B hcov
        (hfail B hBA hBinf) (max N N₁)
    rcases htri with h | h | h
    · obtain ⟨u, huB, huA, hpriv⟩ := h
      exact absurd hpriv
        (hN₁ m (le_trans (le_max_right _ _) hm) u huB huA)
    · exact ⟨m, le_trans (le_max_left _ _) hm, Or.inl h⟩
    · exact ⟨m, le_trans (le_max_left _ _) hm, Or.inr h⟩

theorem fixed_pair_corep_dichotomy {A : Set ℕ} {N₀ u v : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hu0 : 0 < u) (huv : u < v)
    (hcof : ∀ N, ∃ m, N ≤ m ∧ IsPairDestroyer A u v m) :
    (∀ N, ∃ m, N ≤ m ∧ IsPairDestroyer A u v m ∧ m - u ∈ A) ∨
    (∀ N, ∃ m, N ≤ m ∧ IsPairDestroyer A u v m ∧ m - v ∈ A) := by
  have hcorep : ∀ m, N₀ ≤ m → IsPairDestroyer A u v m →
      m - u ∈ A ∨ m - v ∈ A := by
    intro m hm hdes
    obtain ⟨y, hy, z, hz, hyz⟩ := hcov m hm
    rcases hdes.2 0 h0 y hy z hz (by omega) with h | h | h | h | h | h
    · omega
    · exact Or.inl (by
        have : z = m - u := by omega
        exact this ▸ hz)
    · exact Or.inl (by
        have : y = m - u := by omega
        exact this ▸ hy)
    · omega
    · exact Or.inr (by
        have : z = m - v := by omega
        exact this ▸ hz)
    · exact Or.inr (by
        have : y = m - v := by omega
        exact this ▸ hy)
  by_cases hleft : ∀ N, ∃ m, N ≤ m ∧ IsPairDestroyer A u v m ∧
      m - u ∈ A
  · exact Or.inl hleft
  · push Not at hleft
    obtain ⟨N₁, hN₁⟩ := hleft
    refine Or.inr fun N => ?_
    obtain ⟨m, hm, hdes⟩ := hcof (max N (max N₁ N₀))
    rcases hcorep m (by omega) hdes with h | h
    · exact absurd h (hN₁ m (by omega) hdes)
    · exact ⟨m, by omega, hdes, h⟩

theorem fixed_pair_fork_pigeonhole {A : Set ℕ} {N₀ u v z₀ : ℕ}
    (D : ℕ → Prop)
    (hcov : PairCovers A N₀)
    (hcof : ∀ N, ∃ m, N ≤ m ∧ D m)
    (hDdes : ∀ m, D m → IsPairDestroyer A u v m)
    (hz : z₀ ∈ A) (hzu : z₀ ≠ u) (hzv : z₀ ≠ v)
    (hDb : ∀ m, D m → z₀ + N₀ ≤ m) :
    (∀ N, ∃ m, N ≤ m ∧ D m ∧ m - u - z₀ ∈ A) ∨
    (∀ N, ∃ m, N ≤ m ∧ D m ∧ m - v - z₀ ∈ A) := by
  have hfork : ∀ m, D m → m - u - z₀ ∈ A ∨ m - v - z₀ ∈ A := by
    intro m hDm
    have hdes := hDdes m hDm
    have hb := hDb m hDm
    obtain ⟨y, hy, z, hz', hyz⟩ := hcov (m - z₀) (by omega)
    rcases hdes.2 z₀ hz y hy z hz' (by omega) with
      h | h | h | h | h | h
    · exact absurd h hzu
    · exact Or.inl (by
        have : z = m - u - z₀ := by omega
        exact this ▸ hz')
    · exact Or.inl (by
        have : y = m - u - z₀ := by omega
        exact this ▸ hy)
    · exact absurd h hzv
    · exact Or.inr (by
        have : z = m - v - z₀ := by omega
        exact this ▸ hz')
    · exact Or.inr (by
        have : y = m - v - z₀ := by omega
        exact this ▸ hy)
  by_cases hleft : ∀ N, ∃ m, N ≤ m ∧ D m ∧ m - u - z₀ ∈ A
  · exact Or.inl hleft
  · push Not at hleft
    obtain ⟨N₁, hN₁⟩ := hleft
    refine Or.inr fun N => ?_
    obtain ⟨m, hm, hDm⟩ := hcof (max N N₁)
    rcases hfork m hDm with h | h
    · exact absurd h (hN₁ m (le_trans (le_max_right _ _) hm) hDm)
    · exact ⟨m, le_trans (le_max_left _ _) hm, hDm, h⟩

theorem pair_escape_dichotomy {A B : Set ℕ}
    (hpf : ∀ N, ∃ m, N ≤ m ∧ ∃ u ∈ B, ∃ v ∈ B,
      IsPairDestroyer A u v m) :
    (∃ u ∈ B, ∃ v ∈ B, ∀ N, ∃ m, N ≤ m ∧ IsPairDestroyer A u v m) ∨
    (∀ F : Finset (ℕ × ℕ), ∃ N, ∀ m, N ≤ m →
      ∀ p ∈ F, p.1 ∈ B → p.2 ∈ B →
        ¬ IsPairDestroyer A p.1 p.2 m) := by
  by_cases hrec : ∃ u ∈ B, ∃ v ∈ B, ∀ N, ∃ m, N ≤ m ∧
      IsPairDestroyer A u v m
  · exact Or.inl hrec
  · push Not at hrec
    right
    -- every individual pair has bounded targets
    have hbnd : ∀ p : ℕ × ℕ, ∃ Np, ∀ m, Np ≤ m →
        p.1 ∈ B → p.2 ∈ B → ¬ IsPairDestroyer A p.1 p.2 m := by
      intro p
      by_cases h1 : p.1 ∈ B
      · by_cases h2 : p.2 ∈ B
        · obtain ⟨Np, hNp⟩ := hrec p.1 h1 p.2 h2
          exact ⟨Np, fun m hm _ _ => hNp m hm⟩
        · exact ⟨0, fun m _ _ hb => absurd hb h2⟩
      · exact ⟨0, fun m _ hb _ => absurd hb h1⟩
    choose Np hNp using hbnd
    intro F
    refine ⟨F.sup Np, fun m hm p hp h1 h2 => ?_⟩
    exact hNp p m (le_trans (Finset.le_sup hp) hm) h1 h2

theorem spread_pairs_extraction {A B : Set ℕ}
    (hpf : ∀ N, ∃ m, N ≤ m ∧ ∃ u ∈ B, ∃ v ∈ B,
      IsPairDestroyer A u v m)
    (hesc : ∀ F : Finset (ℕ × ℕ), ∃ N, ∀ m, N ≤ m →
      ∀ p ∈ F, p.1 ∈ B → p.2 ∈ B →
        ¬ IsPairDestroyer A p.1 p.2 m) :
    ∀ (F : Finset (ℕ × ℕ)) (N : ℕ), ∃ m, N ≤ m ∧
      ∃ u ∈ B, ∃ v ∈ B, IsPairDestroyer A u v m ∧ (u, v) ∉ F := by
  intro F N
  obtain ⟨N₁, hN₁⟩ := hesc F
  obtain ⟨m, hm, u, huB, v, hvB, hdes⟩ := hpf (max N N₁)
  refine ⟨m, le_trans (le_max_left _ _) hm, u, huB, v, hvB, hdes, ?_⟩
  intro hmem
  exact hN₁ m (le_trans (le_max_right _ _) hm) (u, v) hmem huB hvB
    hdes

theorem spread_pairs_unbounded_required_elements {A B : Set ℕ}
    (hpf : ∀ N, ∃ m, N ≤ m ∧ ∃ u ∈ B, ∃ v ∈ B,
      IsPairDestroyer A u v m)
    (hesc : ∀ F : Finset (ℕ × ℕ), ∃ N, ∀ m, N ≤ m →
      ∀ p ∈ F, p.1 ∈ B → p.2 ∈ B →
        ¬ IsPairDestroyer A p.1 p.2 m) :
    ∀ K N, ∃ m, N ≤ m ∧ ∃ u ∈ B, ∃ v ∈ B,
      IsPairDestroyer A u v m ∧ (K < u ∨ K < v) := by
  intro K N
  obtain ⟨m, hm, u, huB, v, hvB, hdes, hfresh⟩ :=
    spread_pairs_extraction hpf hesc
      ((Finset.range (K + 1)) ×ˢ (Finset.range (K + 1))) N
  refine ⟨m, hm, u, huB, v, hvB, hdes, ?_⟩
  by_contra hsmall
  push Not at hsmall
  exact hfresh (Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩)

theorem spread_min_required_element_dichotomy {A B : Set ℕ}
    (hsup : ∀ N, ∃ m, N ≤ m ∧ ∃ u ∈ B, ∃ v ∈ B, u ≤ v ∧
      IsPairDestroyer A u v m) :
    (∃ u ∈ B, ∀ N, ∃ m, N ≤ m ∧ ∃ v ∈ B, u ≤ v ∧
      IsPairDestroyer A u v m) ∨
    (∀ K N, ∃ m, N ≤ m ∧ ∃ u ∈ B, ∃ v ∈ B, K < u ∧ u ≤ v ∧
      IsPairDestroyer A u v m) := by
  by_cases hrec : ∃ u ∈ B, ∀ N, ∃ m, N ≤ m ∧ ∃ v ∈ B, u ≤ v ∧
      IsPairDestroyer A u v m
  · exact Or.inl hrec
  · push Not at hrec
    right
    have hbnd : ∀ u, ∃ Nu, ∀ m, Nu ≤ m → u ∈ B →
        ¬ ∃ v ∈ B, u ≤ v ∧ IsPairDestroyer A u v m := by
      intro u
      by_cases huB : u ∈ B
      · obtain ⟨Nu, hNu⟩ := hrec u huB
        exact ⟨Nu, fun m hm _ => by
          rintro ⟨v, hvB, huv, hdes⟩
          exact hNu m hm v hvB huv hdes⟩
      · exact ⟨0, fun m _ hb => absurd hb huB⟩
    choose Nu hNu using hbnd
    intro K N
    obtain ⟨m, hm, u, huB, v, hvB, huv, hdes⟩ :=
      hsup (max N ((Finset.range (K + 1)).sup Nu))
    refine ⟨m, le_trans (le_max_left _ _) hm, u, huB, v, hvB, ?_,
      huv, hdes⟩
    by_contra hsmall
    push Not at hsmall
    have hbound : Nu u ≤ m :=
      le_trans (le_trans (Finset.le_sup
        (Finset.mem_range.mpr (by omega))) (le_max_right _ _)) hm
    exact hNu u m hbound huB ⟨v, hvB, huv, hdes⟩

theorem recurring_equal_required_element_contradiction {A : Set ℕ} {N₀ u c : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hu0 : 0 < u)
    (hrec : ∀ N, ∃ m, N ≤ m ∧ IsPairDestroyer A u u m)
    (hc : c ∈ A) (hc0 : 0 < c) (hca : c ≠ u)
    (hw : ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ u ∧ w' ≠ u) :
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
  refine surviving_deletion_of_cofinal_fixedRequiredElement' h0 hcov hu0
    (fun N => ?_) hc hc0 hca hw
  obtain ⟨m, hm, hdes⟩ := hrec N
  exact ⟨m, hm, hdes.privateTriple_of_eq⟩

theorem fixed_pair_level_sequence {A : Set ℕ} {u v : ℕ}
    (hrec : ∀ N, ∃ m, N ≤ m ∧ IsPairDestroyer A u v m ∧ m - v ∈ A) :
    ∃ M : ℕ → ℕ, (∀ k, IsPairDestroyer A u v (M k) ∧ M k - v ∈ A) ∧
      (∀ k, 2 * M k + v + 1 ≤ M (k + 1)) := by
  classical
  choose f hf1 hf2 using hrec
  set M : ℕ → ℕ := fun k =>
    Nat.rec (f 0) (fun _ prev => f (2 * prev + v + 1)) k with hM
  have hMs : ∀ k, M (k + 1) = f (2 * M k + v + 1) := fun _ => rfl
  refine ⟨M, fun k => ?_, fun k => ?_⟩
  · cases k with
    | zero => exact hf2 0
    | succ k => exact hf2 (2 * M k + v + 1)
  · have := hf1 (2 * M k + v + 1)
    have hs : M (k + 1) = f (2 * M k + v + 1) := hMs k
    omega

theorem fixed_pair_channel_ramsey {A : Set ℕ} {N₀ u v : ℕ}
    (hcov : PairCovers A N₀)
    (M : ℕ → ℕ)
    (hM : ∀ k, IsPairDestroyer A u v (M k) ∧ M k - v ∈ A)
    (hgrow : ∀ k, 2 * M k + v + 1 ≤ M (k + 1))
    (hbig : ∀ k, u + v + N₀ < M k - v)
    (huv : u < v) :
    ∃ S : Set ℕ, S.Infinite ∧
      ((∀ j ∈ S, ∀ k ∈ S, j < k → M k - v - (M j - v) ∈ A) ∨
       (∀ j ∈ S, ∀ k ∈ S, j < k → M k - u - (M j - v) ∈ A)) := by
  classical
  have hmono : StrictMono M := by
    apply strictMono_nat_of_lt_succ
    intro k
    have := hgrow k
    omega
  have hfork : ∀ j k, j < k →
      M k - v - (M j - v) ∈ A ∨ M k - u - (M j - v) ∈ A := by
    intro j k hjk
    have hdj := hM j
    have hdk := hM k
    have hb := hbig j
    have hmk : M j < M k := hmono hjk
    have hg : 2 * M j + v + 1 ≤ M k := by
      have h1 : M (j + 1) ≤ M k := hmono.monotone (by omega)
      have := hgrow j
      omega
    obtain ⟨y, hy, z, hz, hyz⟩ := hcov (M k - (M j - v)) (by omega)
    rcases hdk.1.2 (M j - v) hdj.2 y hy z hz (by omega) with
      h | h | h | h | h | h
    · exact absurd h (by have := hbig j; omega)
    · exact Or.inr (by
        have : z = M k - u - (M j - v) := by omega
        exact this ▸ hz)
    · exact Or.inr (by
        have : y = M k - u - (M j - v) := by omega
        exact this ▸ hy)
    · exact absurd h (by have := hbig j; omega)
    · exact Or.inl (by
        have : z = M k - v - (M j - v) := by omega
        exact this ▸ hz)
    · exact Or.inl (by
        have : y = M k - v - (M j - v) := by omega
        exact this ▸ hy)
  set R : ℕ → ℕ → Prop := fun a b =>
    M (max a b) - v - (M (min a b) - v) ∈ A with hR
  have hsymm : Symmetric R := by
    intro a b h
    simpa [hR, max_comm, min_comm] using h
  rcases infinite_pairRamsey_nat (Set.infinite_univ (α := ℕ)) R hsymm
    with ⟨L, -, hLinf, hLcl⟩ | ⟨L, -, hLinf, hLcl⟩
  · refine ⟨L, hLinf, Or.inl fun j hj k hk hjk => ?_⟩
    have := hLcl hj hk (by omega)
    simpa [hR, max_eq_right (le_of_lt hjk),
      min_eq_left (le_of_lt hjk)] using this
  · refine ⟨L, hLinf, Or.inr fun j hj k hk hjk => ?_⟩
    have hnR := hLcl hj hk (by omega)
    have hnotv : ¬ (M k - v - (M j - v) ∈ A) := by
      simpa [hR, max_eq_right (le_of_lt hjk),
        min_eq_left (le_of_lt hjk)] using hnR
    rcases hfork j k hjk with h | h
    · exact absurd h hnotv
    · exact h

/-- Monotone enumeration of an infinite set of naturals. -/
theorem infinite_subset_mono_enum {S : Set ℕ} (hS : S.Infinite) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, φ k ∈ S := by
  classical
  have hnext : ∀ K, ∃ s, s ∈ S ∧ K < s := fun K => by
    obtain ⟨s, hs, hKs⟩ := hS.exists_gt K
    exact ⟨s, hs, hKs⟩
  choose f hfS hfK using hnext
  set φ : ℕ → ℕ := fun k =>
    Nat.rec (f 0) (fun _ prev => f prev) k with hφ
  have hφs : ∀ k, φ (k + 1) = f (φ k) := fun _ => rfl
  refine ⟨φ, strictMono_nat_of_lt_succ fun k => ?_, fun k => ?_⟩
  · have := hfK (φ k)
    have hs : φ (k + 1) = f (φ k) := hφs k
    omega
  · cases k with
    | zero => exact hfS 0
    | succ k => exact hfS (φ k)

theorem fixed_pair_v_channel_family {A : Set ℕ} {u v : ℕ}
    (M : ℕ → ℕ) (S : Set ℕ)
    (hM : ∀ k, IsPairDestroyer A u v (M k) ∧ M k - v ∈ A)
    (hgrow : ∀ k, 2 * M k + v + 1 ≤ M (k + 1))
    (hMv : ∀ k, v < M k)
    (hSinf : S.Infinite)
    (hchan : ∀ j ∈ S, ∀ k ∈ S, j < k → M k - v - (M j - v) ∈ A) :
    ∃ L : ℕ → ℕ, StrictMono L ∧ (∀ i, L i ∈ A) ∧
      (∀ i, 2 * L i < L (i + 1)) ∧
      (∀ i j, i < j → L j - L i ∈ A) ∧
      (∀ i, ∃ m, IsPairDestroyer A u v m ∧ m - v = L i) := by
  obtain ⟨φ, hφmono, hφS⟩ := infinite_subset_mono_enum hSinf
  have hMmono : StrictMono M := by
    apply strictMono_nat_of_lt_succ
    intro k
    have := hgrow k
    omega
  refine ⟨fun i => M (φ i) - v, ?_, fun i => (hM (φ i)).2, ?_, ?_,
    fun i => ⟨M (φ i), (hM (φ i)).1, rfl⟩⟩
  · intro i j hij
    have h1 : φ i < φ j := hφmono hij
    have h2 : M (φ i) < M (φ j) := hMmono h1
    have h5 := hMv (φ i)
    show M (φ i) - v < M (φ j) - v
    omega
  · intro i
    have h1 : φ i < φ (i + 1) := hφmono (by omega)
    have h3 := hgrow (φ i)
    have h4 : M (φ i + 1) ≤ M (φ (i + 1)) := hMmono.monotone (by omega)
    have h5 := hMv (φ i)
    show 2 * (M (φ i) - v) < M (φ (i + 1)) - v
    omega
  · intro i j hij
    exact hchan (φ i) (hφS i) (φ j) (hφS j) (hφmono hij)

/-- Two-color pigeonhole for infinite sets. -/
theorem infinite_two_color {S P : Set ℕ} (hS : S.Infinite) :
    (S ∩ P).Infinite ∨ (S \ P).Infinite := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  exact hS (by
    have : S ⊆ (S ∩ P) ∪ (S \ P) := by
      intro x hx
      by_cases hxP : x ∈ P
      · exact Or.inl ⟨hx, hxP⟩
      · exact Or.inr ⟨hx, hxP⟩
    exact Set.Finite.subset (h1.union h2) this)

theorem fixed_pair_point_channel {A : Set ℕ} {N₀ u v z₀ : ℕ}
    (hcov : PairCovers A N₀)
    (M : ℕ → ℕ) (S : Set ℕ)
    (hM : ∀ k, IsPairDestroyer A u v (M k))
    (hz : z₀ ∈ A) (hzu : z₀ ≠ u) (hzv : z₀ ≠ v)
    (hb : ∀ k, z₀ + N₀ ≤ M k)
    (hSinf : S.Infinite) :
    ∃ T ⊆ S, T.Infinite ∧
      ((∀ k ∈ T, M k - v - z₀ ∈ A) ∨ (∀ k ∈ T, M k - u - z₀ ∈ A)) := by
  have hfork : ∀ k, M k - v - z₀ ∈ A ∨ M k - u - z₀ ∈ A := by
    intro k
    obtain ⟨y, hy, z, hz', hyz⟩ := hcov (M k - z₀) (by have := hb k; omega)
    rcases (hM k).2 z₀ hz y hy z hz' (by have := hb k; omega) with
      h | h | h | h | h | h
    · exact absurd h hzu
    · exact Or.inr (by
        have : z = M k - u - z₀ := by omega
        exact this ▸ hz')
    · exact Or.inr (by
        have : y = M k - u - z₀ := by omega
        exact this ▸ hy)
    · exact absurd h hzv
    · exact Or.inl (by
        have : z = M k - v - z₀ := by omega
        exact this ▸ hz')
    · exact Or.inl (by
        have : y = M k - v - z₀ := by omega
        exact this ▸ hy)
  rcases infinite_two_color (P := {k | M k - v - z₀ ∈ A}) hSinf with
    h | h
  · exact ⟨S ∩ {k | M k - v - z₀ ∈ A}, Set.inter_subset_left, h,
      Or.inl fun k hk => hk.2⟩
  · refine ⟨S \ {k | M k - v - z₀ ∈ A}, Set.diff_subset, h,
      Or.inr fun k hk => ?_⟩
    rcases hfork k with h' | h'
    · exact absurd h' hk.2
    · exact h'

theorem fixed_pair_v_engine_feed {A : Set ℕ} {N₀ c w w' : ℕ}
    (L : ℕ → ℕ)
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hmono : StrictMono L)
    (hgrow : ∀ k, 2 * L k < L (k + 1))
    (hc : c ∈ A) (hc0 : 0 < c) (hcL : c + N₀ < L 0)
    (hwA : w ∈ A) (hw'A : w' ∈ A) (hww : w + w' = 2 * c)
    (hwc : w ≠ c)
    (hLc : ∀ k, L k - c ∈ A)
    (hLw : ∀ k, L k - w ∈ A)
    (hLw' : ∀ k, L k - w' ∈ A)
    (hLL : ∀ i j, i < j → L j - L i ∈ A) :
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n :=
  surviving_deletion_of_reflectionFamilies L h0 hcov hmono hgrow
    hc hc0 hcL hwA hw'A hww hwc hLc hLw hLw'
    (fun i j hij => hLL i j hij)

/-- Generic doubling-growth sequence extraction: any cofinal predicate
family yields a sequence with prescribed growth, carrying the
predicate at every term. -/
theorem generic_growth_sequence {v s : ℕ} (D : ℕ → Prop)
    (hrec : ∀ N, ∃ m, N ≤ m ∧ D m) :
    ∃ M : ℕ → ℕ, (∀ k, D (M k)) ∧
      (∀ k, 2 * M k + v + 1 ≤ M (k + 1)) ∧ s ≤ M 0 := by
  classical
  choose f hf1 hf2 using hrec
  set M : ℕ → ℕ := fun k =>
    Nat.rec (f s) (fun _ prev => f (2 * prev + v + 1)) k with hM
  have hMs : ∀ k, M (k + 1) = f (2 * M k + v + 1) := fun _ => rfl
  refine ⟨M, fun k => ?_, fun k => ?_, hf1 s⟩
  · cases k with
    | zero => exact hf2 s
    | succ k => exact hf2 (2 * M k + v + 1)
  · have := hf1 (2 * M k + v + 1)
    have hs : M (k + 1) = f (2 * M k + v + 1) := hMs k
    omega

theorem fixed_pair_composition {A : Set ℕ} {N₀ u v c w w' : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hu0 : 0 < u) (huv : u < v)
    (hrec : ∀ N, ∃ m, N ≤ m ∧ IsPairDestroyer A u v m ∧ m - v ∈ A)
    (hc : c ∈ A) (hc0 : 0 < c) (hcu : c ≠ u) (hcv : c ≠ v)
    (hwA : w ∈ A) (hw'A : w' ∈ A) (hww : w + w' = 2 * c)
    (hwc : w ≠ c) (hwu : w ≠ u) (hwv : w ≠ v)
    (hw'u : w' ≠ u) (hw'v : w' ≠ v) :
    (∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n) ∨
    (∃ M : ℕ → ℕ, (∀ k, IsPairDestroyer A u v (M k) ∧ M k - v ∈ A) ∧
      ∃ T : Set ℕ, T.Infinite ∧
        ((∀ j ∈ T, ∀ k ∈ T, j < k → M k - u - (M j - v) ∈ A) ∨
         (∀ k ∈ T, M k - u - c ∈ A) ∨
         (∀ k ∈ T, M k - u - w ∈ A) ∨
         (∀ k ∈ T, M k - u - w' ∈ A))) := by
  classical
  set Q := u + v + N₀ + 2 * c + 3 with hQ
  set D : ℕ → Prop := fun m => (IsPairDestroyer A u v m ∧ m - v ∈ A)
    ∧ Q + v ≤ m with hD
  obtain ⟨M, hMD, hgrow, hM0⟩ :=
    generic_growth_sequence (v := v) (s := 0) D (fun N => by
      obtain ⟨m, hm, h1, h2⟩ := hrec (N + Q + v)
      exact ⟨m, by omega, ⟨h1, h2⟩, by omega⟩)
  have hM : ∀ k, IsPairDestroyer A u v (M k) ∧ M k - v ∈ A :=
    fun k => (hMD k).1
  have hMQ : ∀ k, Q ≤ M k - v := fun k => by
    have := (hMD k).2
    omega
  have hbig : ∀ k, u + v + N₀ < M k - v := fun k => by
    have := hMQ k
    omega
  -- LL channel Ramsey
  obtain ⟨S, hSinf, hSchan⟩ :=
    fixed_pair_channel_ramsey hcov M hM hgrow hbig huv
  rcases hSchan with hLLv | hLLu
  · -- LL is v-mono: split the three points
    have hMk : ∀ k, IsPairDestroyer A u v (M k) := fun k => (hM k).1
    obtain ⟨T₁, hT₁S, hT₁inf, hc₁⟩ :=
      fixed_pair_point_channel hcov M S hMk hc hcu hcv
        (fun k => by have := hMQ k; omega) hSinf
    rcases hc₁ with hcv₁ | hcu₁
    · obtain ⟨T₂, hT₂T₁, hT₂inf, hc₂⟩ :=
        fixed_pair_point_channel hcov M T₁ hMk hwA hwu hwv
          (fun k => by have := hMQ k; omega) hT₁inf
      rcases hc₂ with hwv₂ | hwu₂
      · obtain ⟨T₃, hT₃T₂, hT₃inf, hc₃⟩ :=
          fixed_pair_point_channel hcov M T₂ hMk hw'A hw'u hw'v
            (fun k => by have := hMQ k; omega) hT₂inf
        rcases hc₃ with hw'v₃ | hw'u₃
        · -- ALL-V: the engine fires
          left
          obtain ⟨L, hLmono, hLA, hLgrow, hLL, hLwit⟩ :=
            fixed_pair_v_channel_family M T₃ hM hgrow
              (fun k => by have := hMQ k; omega) hT₃inf
              (fun j hj k hk hjk =>
                hLLv j (hT₁S (hT₂T₁ (hT₃T₂ hj)))
                  k (hT₁S (hT₂T₁ (hT₃T₂ hk))) hjk)
          obtain ⟨ψ, hψmono, hψT⟩ := infinite_subset_mono_enum hT₃inf
          -- rebuild the four families on the enumeration of T₃
          refine fixed_pair_v_engine_feed
            (fun i => M (ψ i) - v) h0 hcov ?_ ?_ hc hc0 ?_
            hwA hw'A hww hwc ?_ ?_ ?_ ?_
          · intro i j hij
            have h1 : ψ i < ψ j := hψmono hij
            have hMmono : StrictMono M := by
              apply strictMono_nat_of_lt_succ
              intro k
              have := hgrow k
              omega
            have h2 : M (ψ i) < M (ψ j) := hMmono h1
            have h5 := hMQ (ψ i)
            show M (ψ i) - v < M (ψ j) - v
            omega
          · intro i
            have h1 : ψ i < ψ (i + 1) := hψmono (by omega)
            have hMmono : StrictMono M := by
              apply strictMono_nat_of_lt_succ
              intro k
              have := hgrow k
              omega
            have h3 := hgrow (ψ i)
            have h4 : M (ψ i + 1) ≤ M (ψ (i + 1)) :=
              hMmono.monotone (by omega)
            have h5 := hMQ (ψ i)
            show 2 * (M (ψ i) - v) < M (ψ (i + 1)) - v
            omega
          · have := hMQ (ψ 0)
            show c + N₀ < M (ψ 0) - v
            omega
          · intro i
            have h := hcv₁ (ψ i) (hT₂T₁ (hT₃T₂ (hψT i)))
            show M (ψ i) - v - c ∈ A
            exact h
          · intro i
            have h := hwv₂ (ψ i) (hT₃T₂ (hψT i))
            show M (ψ i) - v - w ∈ A
            exact h
          · intro i
            have h := hw'v₃ (ψ i) (hψT i)
            show M (ψ i) - v - w' ∈ A
            exact h
          · intro i j hij
            have h1 : ψ i < ψ j := hψmono hij
            exact hLLv (ψ i) (hT₁S (hT₂T₁ (hT₃T₂ (hψT i))))
              (ψ j) (hT₁S (hT₂T₁ (hT₃T₂ (hψT j)))) h1
        · exact Or.inr ⟨M, hM, T₃, hT₃inf,
            Or.inr (Or.inr (Or.inr hw'u₃))⟩
      · exact Or.inr ⟨M, hM, T₂, hT₂inf,
          Or.inr (Or.inr (Or.inl hwu₂))⟩
    · exact Or.inr ⟨M, hM, T₁, hT₁inf, Or.inr (Or.inl hcu₁)⟩
  · exact Or.inr ⟨M, hM, S, hSinf, Or.inl hLLu⟩

theorem surviving_deletion_of_shiftedFamilies
    {A : Set ℕ} {N₀ a₁ a₂ a₄ a₅ e V : ℕ} (L : ℕ → ℕ)
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hmono : StrictMono L)
    (hgrow : ∀ k, 2 * L k < L (k + 1))
    (hid1 : a₂ = a₁ + e) (hid2 : a₄ + a₅ = 2 * a₁ + e)
    (ha₁ : 0 < a₁) (ha₅₁ : a₅ ≠ a₁)
    (hbV : a₁ ≤ V ∧ a₂ ≤ V ∧ a₄ ≤ V ∧ a₅ ≤ V ∧ e ≤ V)
    (hVL : 4 * V + N₀ + 2 < L 0)
    (h₁ : ∀ k, L k - a₁ ∈ A)
    (h₂ : ∀ j k, j < k → L k - L j + e ∈ A)
    (h₃ : ∀ k, L k - a₂ ∈ A)
    (h₄ : ∀ k, L k - a₄ ∈ A)
    (h₅ : ∀ k, L k - a₅ ∈ A) :
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
  classical
  obtain ⟨hb₁, hb₂, hb₄, hb₅, hbe⟩ := hbV
  have hdiff : ∀ i j, i < j → L 0 + L i < L j :=
    fun i j h => geometric_level_separation hmono hgrow h
  have hVk : ∀ k, 4 * V + N₀ + 2 < L k := by
    intro k
    have := hmono.monotone (Nat.zero_le k)
    omega
  set f : ℕ → ℕ := fun k => L (2 * k + 2) - a₁ with hfdef
  have hfA : ∀ k, f k ∈ A := fun k => h₁ _
  have hfinj : Function.Injective f := by
    intro i j hij
    simp only [hfdef] at hij
    have h1 : L (2 * i + 2) = L (2 * j + 2) := by
      have := hVk (2 * i + 2); have := hVk (2 * j + 2); omega
    have := hmono.injective h1
    omega
  have hBsub : Set.range f ⊆ A := by rintro t ⟨k, rfl⟩; exact hfA k
  have h0B : (0 : ℕ) ∉ Set.range f := by
    rintro ⟨r, hr⟩
    simp only [hfdef] at hr
    have := hVk (2 * r + 2)
    omega
  -- shifted level-differences avoidance B
  have hgapB : ∀ i j, j < i → L i - L j + e ∉ Set.range f := by
    rintro i j hji ⟨r, hr⟩
    simp only [hfdef] at hr
    have hLj : L j < L i := hmono hji
    have hE : L (2 * r + 2) + L j = L i + e + a₁ := by
      have := hVk (2 * r + 2); omega
    rcases Nat.lt_trichotomy i (2 * r + 2) with h | h | h
    · have := hdiff i (2 * r + 2) h
      have h0' := hVk 0
      omega
    · subst h
      have := hVk j
      omega
    · have h2 : L (2 * r + 2) ≤ L (i - 1) := hmono.monotone (by omega)
      have h3 : L j ≤ L (i - 1) := hmono.monotone (by omega)
      have h4 := hgrow (i - 1)
      have h5 : i - 1 + 1 = i := by omega
      rw [h5] at h4
      have h0' := hVk 0
      omega
  -- odd-level point values avoidance B by parity/separation
  have hoddB : ∀ k t, t ≤ 2 * V → Odd k → L k - t ∉ Set.range f := by
    rintro k t htV ⟨ko, hko⟩ ⟨r, hr⟩
    simp only [hfdef] at hr
    have hE : L (2 * r + 2) + t = L k + a₁ := by
      have := hVk (2 * r + 2); have := hVk k; omega
    rcases Nat.lt_trichotomy k (2 * r + 2) with h | h | h
    · have := hdiff k (2 * r + 2) h
      have h0' := hVk 0
      omega
    · omega
    · have := hdiff (2 * r + 2) k h
      have h0' := hVk 0
      omega
  -- even-level values avoidance B unless the value is a₁
  have hevenB : ∀ k t, t ≤ 2 * V → t ≠ a₁ → L k - t ∉ Set.range f := by
    rintro k t htV hta ⟨r, hr⟩
    simp only [hfdef] at hr
    have hE : L (2 * r + 2) + t = L k + a₁ := by
      have := hVk (2 * r + 2); have := hVk k; omega
    rcases Nat.lt_trichotomy k (2 * r + 2) with h | h | h
    · have := hdiff k (2 * r + 2) h
      have h0' := hVk 0
      omega
    · subst h
      omega
    · have := hdiff (2 * r + 2) k h
      have h0' := hVk 0
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
      rcases le_total j i with hji | hij
      · have hp₁ : L (2 * i + 2) - L (2 * j + 1) + e ∈ A :=
          h₂ (2 * j + 1) (2 * i + 2) (by omega)
        have hp₂ : L (2 * j + 1) - a₄ ∈ A := h₄ (2 * j + 1)
        have hp₃ : L (2 * j + 2) - a₅ ∈ A := h₅ (2 * j + 2)
        refine ⟨_, hp₁, _, hp₂, _, hp₃,
          hgapB (2 * i + 2) (2 * j + 1) (by omega),
          hoddB (2 * j + 1) a₄ (by omega) ⟨j, by omega⟩,
          hevenB (2 * j + 2) a₅ (by omega) ha₅₁, ?_⟩
        have hb1 : L (2 * j + 1) ≤ L (2 * i + 2) :=
          hmono.monotone (by omega)
        have := hVk (2 * i + 2); have := hVk (2 * j + 2)
        have := hVk (2 * j + 1)
        omega
      · have hp₁ : L (2 * j + 2) - L (2 * i + 1) + e ∈ A :=
          h₂ (2 * i + 1) (2 * j + 2) (by omega)
        have hp₂ : L (2 * i + 1) - a₄ ∈ A := h₄ (2 * i + 1)
        have hp₃ : L (2 * i + 2) - a₅ ∈ A := h₅ (2 * i + 2)
        refine ⟨_, hp₁, _, hp₂, _, hp₃,
          hgapB (2 * j + 2) (2 * i + 1) (by omega),
          hoddB (2 * i + 1) a₄ (by omega) ⟨i, by omega⟩,
          hevenB (2 * i + 2) a₅ (by omega) ha₅₁, ?_⟩
        have hb1 : L (2 * i + 1) ≤ L (2 * j + 2) :=
          hmono.monotone (by omega)
        have := hVk (2 * i + 2); have := hVk (2 * j + 2)
        have := hVk (2 * i + 1)
        omega
    · have hp₁ : L (2 * i + 1) - a₂ ∈ A := h₃ (2 * i + 1)
      have hp₂ : L (2 * i + 2) - L (2 * i + 1) + e ∈ A :=
        h₂ (2 * i + 1) (2 * i + 2) (by omega)
      refine ⟨_, hp₁, _, hp₂, y, hy,
        hoddB (2 * i + 1) a₂ (by omega) ⟨i, by omega⟩,
        hgapB (2 * i + 2) (2 * i + 1) (by omega), hyB, ?_⟩
      have hb1 : L (2 * i + 1) ≤ L (2 * i + 2) := hmono.monotone (by omega)
      have := hVk (2 * i + 1); have := hVk (2 * i + 2)
      omega
  · by_cases hyB : y ∈ Set.range f
    · obtain ⟨j, hjy⟩ := hyB
      simp only [hfdef] at hjy
      have hp₁ : L (2 * j + 1) - a₂ ∈ A := h₃ (2 * j + 1)
      have hp₂ : L (2 * j + 2) - L (2 * j + 1) + e ∈ A :=
        h₂ (2 * j + 1) (2 * j + 2) (by omega)
      refine ⟨_, hp₁, _, hp₂, x, hx,
        hoddB (2 * j + 1) a₂ (by omega) ⟨j, by omega⟩,
        hgapB (2 * j + 2) (2 * j + 1) (by omega), hxB, ?_⟩
      have hb1 : L (2 * j + 1) ≤ L (2 * j + 2) := hmono.monotone (by omega)
      have := hVk (2 * j + 1); have := hVk (2 * j + 2)
      omega
    · exact ⟨x, hx, y, hy, 0, h0, hxB, hyB, h0B, by omega⟩

end Erdos881
