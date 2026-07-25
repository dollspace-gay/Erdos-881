import Erdos881.RedundantVertexKill

/-!
# The non-essential kill: pointwise thresholds

`RedundantVertexKill` needed the redundancy threshold below the guard
(`N₁ ≤ u`) — a crude wrapper.  Pointwise, each ingredient needs only:

* window and desert elements `x` with `N₂ ≤ u + x` — arranged by
  flooring the windows at `N₂`, whatever its size;
* the corep pin at `x = 0` needs only `u ∉ W_u`: **`u` has a proper
  two-term representation** (`u` is not primitive);
* the reflection of `w = 0` is free (`L - 0 = L ∈ A`).

Consequence: a guard that is 2-redundant at *any* threshold, not
primitive, with destroyer supply, forces a surviving deletion.  The
clique escape shrinks to vertices that are **primitive or fully
2-essential** — the Grekos class plus primitives.
-/

namespace Erdos881

/-- Upper desert, arbitrary threshold: the per-point condition
`N₁ ≤ u + x` replaces `N₁ ≤ u`. -/
theorem IsPairDestroyer.upper_desert_of_redundant'
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
    exact hdes.upper_desert_of_redundant' hcov hred huv hxA hxu
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


end Erdos881
