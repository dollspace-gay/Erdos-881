import Erdos881.CliqueSplice

/-!
# The hugging splice: pair-redundant edges die at every altitude

Sharp pinning (`pinned_mirror_sharp`) needs no room, so it bites in
the hugging regime too.  For a jointly 2-redundant pair `{u, v}`
destroying `m`:

* `upper_desert_of_pairRedundant` — no element can sit strictly
  between the channels away from the two diagonals: above the
  `v`-channel every fork branch is dead;
* `level_lower_of_pairRedundant` — if the level `m - v` lagged far
  behind `v`, a covering window would land inside that desert with
  all four permitted values out of range: covering starves.  So
  **levels grow with partners automatically**;
* `surviving_deletion_of_quadDefects` — the windowed extraction
  engine tolerating four rotating defects per level;
* `surviving_deletion_of_pairRedundant_edges` — a 2-redundant guard
  with jointly-redundant partners above every bound forces a
  surviving deletion, clearance or no clearance: hugging is no
  refuge.

Together with `surviving_deletion_of_clear_pinned_edges`, the genuine
clique branch is reduced to pair-*essential* partners — for a
2-redundant `u`, partners essential in `A \ {u}`, a finite set by
Grekos-type counting (literature; Open Link B1).
-/

namespace Erdos881

/-- **Upper desert.**  Between the channels, away from the guards and
the two diagonals, a jointly 2-redundant pair's destroyed target
tolerates no element at all: the `v`-branch is out of range and the
`u`-branch is sharply pinned. -/
theorem IsPairDestroyer.upper_desert_of_pairRedundant
    {A : Set ℕ} {N₀ N₂ u v m x : ℕ}
    (hcov : PairCovers A N₀)
    (hpair : TwoRedundantPair A u v N₂)
    (hdes : IsPairDestroyer A u v m)
    (huv : u < v)
    (hN₂ : N₂ ≤ u)
    (hx : x ∈ A) (hxu : x ≠ u) (hxv : x ≠ v)
    (hxm : x + N₀ ≤ m) (hxum : u + x ≤ m) (hxvm : m < v + x)
    (hd1 : m ≠ 2 * u + x) (hd2 : m ≠ u + v + x) :
    False := by
  obtain ⟨s, hs, t, ht, hst, hsu, hsv, htu, htv⟩ :=
    hpair (u + x) (by omega)
  obtain ⟨y, hy, z, hz, hyz⟩ := hcov (m - x) (by omega)
  rcases hdes.2 x hx y hy z hz (by omega) with h | h | h | h | h | h
  · exact absurd h hxu
  · have hw : m - u - x ∈ A := by
      have hz' : z = m - u - x := by omega
      exact hz' ▸ hz
    exact hdes.pinned_sharp hs ht hst hsu hsv htu htv hxum hd1 hd2 hw
  · have hw : m - u - x ∈ A := by
      have hy' : y = m - u - x := by omega
      exact hy' ▸ hy
    exact hdes.pinned_sharp hs ht hst hsu hsv htu htv hxum hd1 hd2 hw
  · exact absurd h hxv
  · omega
  · omega

/-- **Levels cannot lag their partners.**  If `m - v` were much
smaller than `v`, the covering window at
`q = 2(m - v) + 2u + N₀ + N₂ + 4` would land inside the upper desert
with `u` below it, `v` and `m - 2u` above it, and `m - u - v` under
its floor: nothing could cover `q`. -/
theorem IsPairDestroyer.level_lower_of_pairRedundant
    {A : Set ℕ} {N₀ N₂ u v m : ℕ}
    (hcov : PairCovers A N₀)
    (hpair : TwoRedundantPair A u v N₂)
    (hdes : IsPairDestroyer A u v m)
    (hu0 : 0 < u) (huv : u < v) (hvm : v ≤ m)
    (hN₂ : N₂ ≤ u)
    (hbig : 2 * (m - v) + 8 * (u + N₀ + N₂ + 2) ≤ v) :
    False := by
  set q := 2 * (m - v) + 2 * u + N₀ + N₂ + 4 with hq
  obtain ⟨y, hy, z, hz, hyz⟩ := hcov q (by omega)
  have hkill : ∀ x ∈ A, 2 * x ≥ q → x ≤ q → False := by
    intro x hxA hxl hxr
    exact hdes.upper_desert_of_pairRedundant hcov hpair huv hN₂
      hxA (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
  rcases le_total y z with h | h
  · exact hkill z hz (by omega) (by omega)
  · exact hkill y hy (by omega) (by omega)

/-- **Spare keys from four rotating defects.**  The windowed
extraction engine tolerating four defect values at each level. -/
theorem surviving_deletion_of_quadDefects
    {A : Set ℕ} {N₀ c w w' : ℕ} (L W d₁ d₂ d₃ d₄ : ℕ → ℕ)
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hmono : StrictMono L)
    (hlev : ∀ k, ∀ z ∈ A, z ≠ d₁ k → z ≠ d₂ k → z ≠ d₃ k →
      z ≠ d₄ k → z + N₀ < W k → L k - z ∈ A)
    (hmem : ∀ k, L k ∈ A)
    (hgrow : ∀ k, 2 * L k < L (k + 1))
    (hc : c ∈ A) (hc0 : 0 < c) (hcL : c + N₀ < L 0)
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
    hlev k c hc (hcd k).1 (hcd k).2.1 (hcd k).2.2.1 (hcd k).2.2.2
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
            (hLd (2 * j + 1) (2 * i + 2) (by omega)).1
            (hLd (2 * j + 1) (2 * i + 2) (by omega)).2.1
            (hLd (2 * j + 1) (2 * i + 2) (by omega)).2.2.1
            (hLd (2 * j + 1) (2 * i + 2) (by omega)).2.2.2
            (hLW (2 * j + 1) (2 * i + 2) (by omega))
        have hp₂A : L (2 * j + 1) - w ∈ A :=
          hlev (2 * j + 1) w hwA (hwd _).1 (hwd _).2.1 (hwd _).2.2.1
            (hwd _).2.2.2
            (by have := hcW (2 * j + 1); omega)
        have hp₃A : L (2 * j + 2) - w' ∈ A :=
          hlev (2 * j + 2) w' hw'A (hw'd _).1 (hw'd _).2.1 (hw'd _).2.2.1
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
            (hLd (2 * i + 1) (2 * j + 2) (by omega)).1
            (hLd (2 * i + 1) (2 * j + 2) (by omega)).2.1
            (hLd (2 * i + 1) (2 * j + 2) (by omega)).2.2.1
            (hLd (2 * i + 1) (2 * j + 2) (by omega)).2.2.2
            (hLW (2 * i + 1) (2 * j + 2) (by omega))
        have hp₂A : L (2 * i + 1) - w ∈ A :=
          hlev (2 * i + 1) w hwA (hwd _).1 (hwd _).2.1 (hwd _).2.2.1
            (hwd _).2.2.2
            (by have := hcW (2 * i + 1); omega)
        have hp₃A : L (2 * i + 2) - w' ∈ A :=
          hlev (2 * i + 2) w' hw'A (hw'd _).1 (hw'd _).2.1 (hw'd _).2.2.1
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

/-- **Pair-redundant partners run the extraction at any altitude.**
A 2-redundant guard `u` with jointly-redundant partners above every
bound forces a surviving deletion: each edge's level `m - v` is pinned
near `v` by `level_lower_of_pairRedundant`, so levels grow with
partners, and the four defects `u, v, m - 2u, m - u - v` are dodged
arithmetically.  No clearance hypothesis appears. -/
theorem surviving_deletion_of_pairRedundant_edges
    {A : Set ℕ} {N₀ N₂ u c : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hu0 : 0 < u) (hN₀ : N₀ ≤ u) (hN₂ : N₂ ≤ u)
    (hsupply : ∀ K, ∃ v m, K < v ∧ u < v ∧ v ≤ m ∧
      TwoRedundantPair A u v N₂ ∧ IsPairDestroyer A u v m)
    (hc : c ∈ A) (hc0 : 0 < c) (hcu : c ≠ u)
    (hw : ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ u ∧ w' ≠ u) :
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
  classical
  obtain ⟨w, hwA, w', hw'A, hww, hwc, hwu, hw'u⟩ := hw
  choose pv pm hpK hpu hpvm hppair hpdes using hsupply
  set b : ℕ → ℕ := fun x => 8 * (x + c + 2 * u + N₀ + N₂ + 4) with hb
  set κ : ℕ → ℕ := fun k =>
    Nat.rec (u + c + N₀ + N₂ + 1)
      (fun _ p => pm (b p) - pv (b p)) k with hκ
  set L : ℕ → ℕ := fun k => κ (k + 1) with hLdef
  have hLeq : ∀ k, L k = pm (b (κ k)) - pv (b (κ k)) := fun _ => rfl
  -- per-step facts
  have hstep : ∀ k, 4 * κ k + 4 * c + 8 < L k ∧ L k ∈ A ∧
      u < L k ∧
      u < pv (b (κ k)) ∧ pv (b (κ k)) ≤ pm (b (κ k)) ∧
      8 * (κ k + c + 2 * u + N₀ + N₂ + 4) < pv (b (κ k)) ∧
      ∀ z ∈ A, z ≠ u → z ≠ pv (b (κ k)) →
        z ≠ pm (b (κ k)) - 2 * u →
        z ≠ pm (b (κ k)) - u - pv (b (κ k)) →
        z + N₀ < pm (b (κ k)) - u → L k - z ∈ A := by
    intro k
    have h1 := hpK (b (κ k))
    have h2 := hpu (b (κ k))
    have h3 := hpvm (b (κ k))
    have h4 := hppair (b (κ k))
    have h5 := hpdes (b (κ k))
    have hbk : b (κ k) = 8 * (κ k + c + 2 * u + N₀ + N₂ + 4) := rfl
    have h1' : 8 * (κ k + c + 2 * u + N₀ + N₂ + 4) < pv (b (κ k)) :=
      lt_of_eq_of_lt hbk.symm h1
    have hlow : ¬ (2 * (pm (b (κ k)) - pv (b (κ k))) +
        8 * (u + N₀ + N₂ + 2) ≤ pv (b (κ k))) :=
      fun h => h5.level_lower_of_pairRedundant hcov h4 hu0 h2 h3 hN₂ h
    have hLk : L k = pm (b (κ k)) - pv (b (κ k)) := hLeq k
    have hLbig : 4 * κ k + 4 * c + 8 < L k := by
      rw [hLk]; omega
    have hLu : u < L k := by rw [hLk]; omega
    have hLu' : u < pm (b (κ k)) - pv (b (κ k)) := by
      rw [hLk] at hLu; exact hLu
    have hd0 : pm (b (κ k)) ≠ 2 * u := by omega
    have hd0' : pm (b (κ k)) ≠ u + pv (b (κ k)) := by omega
    obtain ⟨hcorep, hmir⟩ :=
      h4.hugging_level h0 hcov h5 hu0 h2 h3 hN₂ hN₀ hd0 hd0'
    refine ⟨hLbig, hLk ▸ hcorep, by rw [hLk]; omega, h2, h3, h1', ?_⟩
    intro z hz hzu hzv hzd3 hzd4 hzW
    rw [hLk]
    exact hmir z hz hzu hzv (by omega) (by omega) (by omega)
  have hκmono : ∀ k, κ k < κ (k + 1) := by
    intro k
    have h1 := (hstep k).1
    have h2 : L k = κ (k + 1) := rfl
    omega
  have hκK₀ : ∀ k, u + c + N₀ + N₂ + 1 ≤ κ k := by
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
  have hvbig : ∀ k, 8 * (κ k + c + 2 * u + N₀ + N₂ + 4) < pv (b (κ k)) :=
    fun k => (hstep k).2.2.2.2.2.1
  refine surviving_deletion_of_quadDefects L
    (fun k => pm (b (κ k)) - u)
    (fun _ => u) (fun k => pv (b (κ k)))
    (fun k => pm (b (κ k)) - 2 * u)
    (fun k => pm (b (κ k)) - u - pv (b (κ k)))
    h0 hcov hmono
    (fun k => (hstep k).2.2.2.2.2.2)
    (fun k => (hstep k).2.1) hgrow hc hc0 ?_ ?_ ?_
    hwA hw'A hww hwc ?_ ?_ ?_ ?_
  · have h1 := (hstep 0).1
    have h2 := hκK₀ 0
    omega
  · intro k
    have h1 := hvbig k
    have h2 := (hstep k).2.2.2.2.1
    show 2 * c + N₀ < pm (b (κ k)) - u
    omega
  · intro j k hjk
    have h1 := hvbig k
    have h2 := (hstep k).2.2.2.2.1
    have h3 := hLκ j k hjk
    show L j + N₀ < pm (b (κ k)) - u
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
    show w ≠ u ∧ w ≠ pv (b (κ k)) ∧
      w ≠ pm (b (κ k)) - 2 * u ∧
      w ≠ pm (b (κ k)) - u - pv (b (κ k))
    exact ⟨hwu, by omega, by omega, by omega⟩
  · intro k
    have h1 := hvbig k
    have h2 := (hstep k).2.2.2.1
    have h3 := (hstep k).2.2.2.2.1
    have h5 := (hstep k).1
    have h6 := hLeq k
    have h7 := hκK₀ k
    show w' ≠ u ∧ w' ≠ pv (b (κ k)) ∧
      w' ≠ pm (b (κ k)) - 2 * u ∧
      w' ≠ pm (b (κ k)) - u - pv (b (κ k))
    exact ⟨hw'u, by omega, by omega, by omega⟩
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

/-- **The grand assembly, second form.**  With the hugging splice the
clique escape shrinks again: beyond some bound, every destroyer of an
eligible 2-redundant vertex's edges must hug (`m < 3v`) *and* certify
joint essentiality of its pair.  For a 2-redundant `u` that means all
high partners are essential in `A \ {u}` — a finite set by Grekos-type
counting (Open Link B1, literature). -/
theorem erdos881_grand_assembly' {A : Set ℕ} {N₀ : ℕ}
    (hA : A.Infinite) (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfunnel : HasCofinalPairFunnels A)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g) :
    (∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n) ∨
    (∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A 0 m) ∨
    (∃ L, L ⊆ A ∧ L.Infinite ∧ L.Pairwise (TeamEdge A) ∧
      ∀ u ∈ L, 0 < u → N₀ ≤ u → ∀ N₁, N₁ ≤ u →
        TwoRedundant A u N₁ → ∀ N₂, N₂ ≤ u →
        ∃ K, ∀ v m, K < v → u < v → v ≤ m →
          IsPairDestroyer A u v m →
          m < 3 * v ∧ ¬ TwoRedundantPair A u v N₂) := by
  rcases infinite_teamClique_or_cofinal_privatePairs hA hfunnel with
    ⟨L, hLA, hLinf, hLcl⟩ | ⟨L, hLA, hLinf, hstream⟩
  · by_cases hhug : ∀ u ∈ L, 0 < u → N₀ ≤ u → ∀ N₁, N₁ ≤ u →
        TwoRedundant A u N₁ → ∀ N₂, N₂ ≤ u →
        ∃ K, ∀ v m, K < v → u < v → v ≤ m →
          IsPairDestroyer A u v m →
          m < 3 * v ∧ ¬ TwoRedundantPair A u v N₂
    · exact Or.inr (Or.inr ⟨L, hLA, hLinf, hLcl, hhug⟩)
    · push Not at hhug
      obtain ⟨u, huL, hu0, huN₀, N₁, hN₁u, hred, N₂, hN₂u, hmix⟩ := hhug
      obtain ⟨c, hc, hc0, hcu, w, hwA, w', hw'A, hww, hwc, hwu, hw'u⟩ :=
        hanchor u
      by_cases hcl : ∀ K, ∃ v m, K < v ∧ u < v ∧ 3 * v ≤ m ∧
          IsPairDestroyer A u v m
      · exact Or.inl (surviving_deletion_of_clear_pinned_edges h0 hcov
          hred hu0 huN₀ hN₁u hcl hc hc0 hcu
          ⟨w, hwA, w', hw'A, hww, hwc, hwu, hw'u⟩)
      · push Not at hcl
        obtain ⟨K₀, hK₀⟩ := hcl
        refine Or.inl (surviving_deletion_of_pairRedundant_edges h0 hcov
          hu0 huN₀ hN₂u (fun K => ?_) hc hc0 hcu
          ⟨w, hwA, w', hw'A, hww, hwc, hwu, hw'u⟩)
        obtain ⟨v, m, hKv, huv, hvm, hdes, hbad⟩ := hmix (max K K₀)
        have hK : K < v := lt_of_le_of_lt (le_max_left _ _) hKv
        have hK₀v : K₀ < v := lt_of_le_of_lt (le_max_right _ _) hKv
        rcases Nat.lt_or_ge m (3 * v) with hm3 | hm3
        · exact ⟨v, m, hK, huv, hvm, hbad hm3, hdes⟩
        · exact absurd hdes (hK₀ v m hK₀v huv hm3)
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
