import Erdos881.TeamGraphRamsey

namespace Erdos881

/-- Exclusion interval under destruction alone: an element strictly above the
larger channel `m - u` and at least `N₀` below `m` is one of the two
required elements.  (`IsPairTransversalPrivateTriple.exclusion_interval` restated for a bare
`IsPairDestroyer`, whose hypotheses are all the proof ever used.) -/
theorem IsPairDestroyer.exclusion_interval {A : Set ℕ} {N₀ u v m : ℕ}
    (hcov : PairCovers A N₀)
    (hdes : IsPairDestroyer A u v m)
    (hu : 0 < u) (huv : u < v)
    {z : ℕ} (hz : z ∈ A) (hlow : m < u + z) (hhigh : z + N₀ ≤ m) :
    z = u ∨ z = v := by
  by_contra hne
  push Not at hne
  obtain ⟨y, hy, w, hw, hyw⟩ := hcov (m - z) (by omega)
  rcases hdes.2 z hz y hy w hw (by omega) with h | h | h | h | h | h <;>
    omega

theorem IsPairDestroyer.pinned {A : Set ℕ} {u v m x s t : ℕ}
    (hdes : IsPairDestroyer A u v m)
    (huv : u < v)
    (hs : s ∈ A) (ht : t ∈ A) (hsum : s + t = u + x)
    (hsu : s ≠ u) (hsv : s ≠ v) (htu : t ≠ u) (htv : t ≠ v)
    (hroom : x + 2 * v < m)
    (hw : m - u - x ∈ A) :
    False := by
  have h := hdes.2 s hs t ht (m - u - x) hw (by omega)
  omega

theorem IsPairDestroyer.pinned_mirror {A : Set ℕ} {N₀ u v m x : ℕ}
    (hcov : PairCovers A N₀)
    (hdes : IsPairDestroyer A u v m)
    (huv : u < v)
    (hx : x ∈ A) (hxu : x ≠ u) (hxv : x ≠ v) (hxm : x + N₀ ≤ m)
    (hrep : ∃ s ∈ A, ∃ t ∈ A,
      s + t = u + x ∧ s ≠ u ∧ s ≠ v ∧ t ≠ u ∧ t ≠ v)
    (hroom : x + 2 * v < m) :
    m - v - x ∈ A := by
  obtain ⟨s, hs, t, ht, hst, hsu, hsv, htu, htv⟩ := hrep
  obtain ⟨y, hy, z, hz, hyz⟩ := hcov (m - x) (by omega)
  rcases hdes.2 x hx y hy z hz (by omega) with h | h | h | h | h | h
  · exact absurd h hxu
  · have hw : m - u - x ∈ A := by
      have hz' : z = m - u - x := by omega
      exact hz' ▸ hz
    exact (hdes.pinned huv hs ht hst hsu hsv htu htv hroom hw).elim
  · have hw : m - u - x ∈ A := by
      have hy' : y = m - u - x := by omega
      exact hy' ▸ hy
    exact (hdes.pinned huv hs ht hst hsu hsv htu htv hroom hw).elim
  · exact absurd h hxv
  · have hz' : z = m - v - x := by omega
    exact hz' ▸ hz
  · have hy' : y = m - v - x := by omega
    exact hy' ▸ hy

theorem IsPairDestroyer.double_pin_exclusion_interval {A : Set ℕ} {N₀ u v m x : ℕ}
    (hcov : PairCovers A N₀)
    (hdes : IsPairDestroyer A u v m)
    (huv : u < v)
    (hx : x ∈ A) (hxu : x ≠ u) (hxv : x ≠ v) (hxm : x + N₀ ≤ m)
    (hrepu : ∃ s ∈ A, ∃ t ∈ A,
      s + t = u + x ∧ s ≠ u ∧ s ≠ v ∧ t ≠ u ∧ t ≠ v)
    (hrepv : ∃ s ∈ A, ∃ t ∈ A,
      s + t = v + x ∧ s ≠ u ∧ s ≠ v ∧ t ≠ u ∧ t ≠ v)
    (hroom : x + 2 * v < m) :
    False := by
  have hmv := hdes.pinned_mirror hcov huv hx hxu hxv hxm hrepu hroom
  obtain ⟨s, hs, t, ht, hst, hsu, hsv, htu, htv⟩ := hrepv
  have h := hdes.2 s hs t ht (m - v - x) hmv (by omega)
  omega

theorem IsPairDestroyer.pinned_sharp {A : Set ℕ} {u v m x s t : ℕ}
    (hdes : IsPairDestroyer A u v m)
    (hs : s ∈ A) (ht : t ∈ A) (hsum : s + t = u + x)
    (hsu : s ≠ u) (hsv : s ≠ v) (htu : t ≠ u) (htv : t ≠ v)
    (hxm : u + x ≤ m)
    (hd1 : m ≠ 2 * u + x) (hd2 : m ≠ u + v + x)
    (hw : m - u - x ∈ A) :
    False := by
  have h := hdes.2 s hs t ht (m - u - x) hw (by omega)
  omega

theorem IsPairDestroyer.pinned_mirror_sharp {A : Set ℕ} {N₀ u v m x : ℕ}
    (hcov : PairCovers A N₀)
    (hdes : IsPairDestroyer A u v m)
    (hx : x ∈ A) (hxu : x ≠ u) (hxv : x ≠ v) (hxm : x + N₀ ≤ m)
    (hxum : u + x ≤ m)
    (hrep : ∃ s ∈ A, ∃ t ∈ A,
      s + t = u + x ∧ s ≠ u ∧ s ≠ v ∧ t ≠ u ∧ t ≠ v)
    (hd1 : m ≠ 2 * u + x) (hd2 : m ≠ u + v + x) :
    m - v - x ∈ A := by
  obtain ⟨s, hs, t, ht, hst, hsu, hsv, htu, htv⟩ := hrep
  obtain ⟨y, hy, z, hz, hyz⟩ := hcov (m - x) (by omega)
  rcases hdes.2 x hx y hy z hz (by omega) with h | h | h | h | h | h
  · exact absurd h hxu
  · have hw : m - u - x ∈ A := by
      have hz' : z = m - u - x := by omega
      exact hz' ▸ hz
    exact (hdes.pinned_sharp hs ht hst hsu hsv htu htv hxum hd1 hd2
      hw).elim
  · have hw : m - u - x ∈ A := by
      have hy' : y = m - u - x := by omega
      exact hy' ▸ hy
    exact (hdes.pinned_sharp hs ht hst hsu hsv htu htv hxum hd1 hd2
      hw).elim
  · exact absurd h hxv
  · have hz' : z = m - v - x := by omega
    exact hz' ▸ hz
  · have hy' : y = m - v - x := by omega
    exact hy' ▸ hy

/-- `u` is *2-redundant above `N₁`*: every integer from `N₁` on has a
two-term representation avoiding `u`.  Equivalently, `A \ {u}` is still
an asymptotic order-two covering set.  By Erdős–Graham/Grekos, all but
finitely many elements of an order-two basis are 2-redundant. -/
def TwoRedundant (A : Set ℕ) (u N₁ : ℕ) : Prop :=
  ∀ n, N₁ ≤ n → ∃ s ∈ A, ∃ t ∈ A, s + t = n ∧ s ≠ u ∧ t ≠ u

/-- For `x` below the window `v - u`, an avoiding representation of
`u + x` supplied by 2-redundancy automatically avoids `v` as well, so
the pinned mirror fires with no further hypotheses on `v`. -/
theorem TwoRedundant.pinned_mirror {A : Set ℕ} {N₀ N₁ u v m x : ℕ}
    (hred : TwoRedundant A u N₁)
    (hcov : PairCovers A N₀)
    (hdes : IsPairDestroyer A u v m)
    (huv : u < v)
    (hx : x ∈ A) (hxu : x ≠ u) (hxm : x + N₀ ≤ m)
    (hN₁ : N₁ ≤ u + x) (hwin : u + x < v)
    (hroom : x + 2 * v < m) :
    m - v - x ∈ A := by
  obtain ⟨s, hs, t, ht, hst, hsu, htu⟩ := hred (u + x) hN₁
  exact hdes.pinned_mirror hcov huv hx hxu (by omega) hxm
    ⟨s, hs, t, ht, hst, hsu, by omega, htu, by omega⟩ hroom

/-- The corep of a pinned edge is an element: taking `x = 0` in the
pinned mirror forces `m - v ∈ A`. -/
theorem TwoRedundant.corep_mem {A : Set ℕ} {N₀ N₁ u v m : ℕ}
    (hred : TwoRedundant A u N₁)
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hdes : IsPairDestroyer A u v m)
    (hu0 : 0 < u) (huv : u < v)
    (hN₀ : N₀ ≤ m) (hN₁ : N₁ ≤ u) (hroom : 2 * v < m) :
    m - v ∈ A := by
  have h := hred.pinned_mirror hcov hdes huv h0 (by omega) (by omega)
    (by omega) (by omega) (by omega)
  simpa using h

theorem IsPairDestroyer.pinned_level {A : Set ℕ} {N₀ N₁ u v m : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hred : TwoRedundant A u N₁)
    (hdes : IsPairDestroyer A u v m)
    (hu0 : 0 < u) (huv : u < v)
    (hN₀ : N₀ ≤ u) (hN₁ : N₁ ≤ u)
    (hclear : 3 * v ≤ m) :
    m - v ∈ A ∧
      ∀ x ∈ A, x ≠ u → u + x < v → m - v - x ∈ A := by
  refine ⟨hred.corep_mem h0 hcov hdes hu0 huv (by omega) hN₁ (by omega),
    ?_⟩
  intro x hx hxu hwin
  exact hred.pinned_mirror hcov hdes huv hx hxu (by omega) (by omega)
    hwin (by omega)

/-- The pair `{u, v}` is *jointly 2-redundant above `N₂`*: every
integer from `N₂` on has a two-term representation avoiding both.
Equivalently, `A \ {u, v}` still pair-covers asymptotically. -/
def TwoRedundantPair (A : Set ℕ) (u v N₂ : ℕ) : Prop :=
  ∀ n, N₂ ≤ n → ∃ s ∈ A, ∃ t ∈ A,
    s + t = n ∧ s ≠ u ∧ s ≠ v ∧ t ≠ u ∧ t ≠ v

theorem IsPairDestroyer.hugging_of_pairRedundant
    {A : Set ℕ} {N₀ N₂ u v m : ℕ}
    (hcov : PairCovers A N₀)
    (hpair : TwoRedundantPair A u v N₂)
    (hdes : IsPairDestroyer A u v m)
    (huv : u < v) (hN₀ : N₀ ≤ v) (hN₂ : N₂ ≤ v)
    (hbig : 4 * v + N₀ + 4 ≤ m) :
    False := by
  obtain ⟨y, hy, z, hz, hyz⟩ := hcov (2 * v + 2) (by omega)
  have hkill : ∀ w ∈ A, v < w → w ≤ 2 * v + 2 → False := by
    intro w hw hvw hwv
    have hrepu := hpair (u + w) (by omega)
    have hrepv := hpair (v + w) (by omega)
    exact hdes.double_pin_exclusion_interval hcov huv hw (by omega) (by omega)
      (by omega) hrepu hrepv (by omega)
  rcases Nat.le_total y z with h | h
  · exact hkill z hz (by omega) (by omega)
  · exact hkill y hy (by omega) (by omega)

theorem IsPairDestroyer.sharp_hugging_of_pairRedundant
    {A : Set ℕ} {N₀ N₂ u v m : ℕ}
    (hcov : PairCovers A N₀)
    (hpair : TwoRedundantPair A u v N₂)
    (hdes : IsPairDestroyer A u v m)
    (huv : u < v) (hN₀ : N₀ ≤ v)
    (hbig : 2 * v + 20 * (N₀ + N₂ + 2) ≤ m) :
    False := by
  have hguard : ∀ w ∈ A, N₂ ≤ w → w + 2 * v < m →
      w = u ∨ w = v := by
    intro w hw hN hroom
    by_contra hne
    push Not at hne
    exact hdes.double_pin_exclusion_interval hcov huv hw hne.1 hne.2 (by omega)
      (hpair (u + w) (by omega)) (hpair (v + w) (by omega)) hroom
  have hwin : ∀ q, N₀ ≤ q → N₂ ≤ q / 2 → q + 2 * v < m →
      ∃ w, (w = u ∨ w = v) ∧ 2 * w ≥ q ∧ w ≤ q := by
    intro q hq hq2 hqm
    obtain ⟨y, hy, z, hz, hyz⟩ := hcov q hq
    rcases Nat.le_total y z with h | h
    · exact ⟨z, hguard z hz (by omega) (by omega), by omega, by omega⟩
    · exact ⟨y, hguard y hy (by omega) (by omega), by omega, by omega⟩
  obtain ⟨w₁, hw₁, hw₁l, hw₁r⟩ :=
    hwin (m - 2 * v - 1) (by omega) (by omega) (by omega)
  obtain ⟨w₂, hw₂, hw₂l, hw₂r⟩ :=
    hwin ((m - 2 * v - 1) / 3) (by omega) (by omega) (by omega)
  obtain ⟨w₃, hw₃, hw₃l, hw₃r⟩ :=
    hwin ((m - 2 * v - 1) / 9) (by omega) (by omega) (by omega)
  omega

theorem TwoRedundantPair.hugging_level {A : Set ℕ} {N₀ N₂ u v m : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hpair : TwoRedundantPair A u v N₂)
    (hdes : IsPairDestroyer A u v m)
    (hu0 : 0 < u) (huv : u < v) (hvm : v ≤ m)
    (hN₂ : N₂ ≤ u) (hN₀ : N₀ ≤ u)
    (hd0 : m ≠ 2 * u) (hd0' : m ≠ u + v) :
    m - v ∈ A ∧ ∀ x ∈ A, x ≠ u → x ≠ v → u + x ≤ m →
      m ≠ 2 * u + x → m ≠ u + v + x → m - v - x ∈ A := by
  constructor
  · obtain ⟨s, hs, t, ht, hst, hsu, hsv, htu, htv⟩ :=
      hpair u (by omega)
    have h := hdes.pinned_mirror_sharp hcov h0 (by omega) (by omega)
      (by omega) (by omega)
      ⟨s, hs, t, ht, by omega, hsu, hsv, htu, htv⟩
      (by omega) (by omega)
    simpa using h
  · intro x hx hxu hxv hxum hd1 hd2
    obtain ⟨s, hs, t, ht, hst, hsu, hsv, htu, htv⟩ :=
      hpair (u + x) (by omega)
    exact hdes.pinned_mirror_sharp hcov hx hxu hxv (by omega) hxum
      ⟨s, hs, t, ht, hst, hsu, hsv, htu, htv⟩ hd1 hd2

theorem pinned_translation {A : Set ℕ} {N₀ N₁ u v₁ m₁ v₂ m₂ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hred : TwoRedundant A u N₁)
    (hdes₁ : IsPairDestroyer A u v₁ m₁)
    (hdes₂ : IsPairDestroyer A u v₂ m₂)
    (hu0 : 0 < u) (huv₁ : u < v₁)
    (hN₀ : N₀ ≤ u) (hN₁ : N₁ ≤ u)
    (hclear₁ : 3 * v₁ ≤ m₁) (hclear₂ : 3 * v₂ ≤ m₂)
    (hwide : m₁ - v₁ + u < v₂)
    {x : ℕ} (hx : x ∈ A) (hxu : x ≠ u) (hwin : u + x < v₁)
    (hdef : m₁ - v₁ - x ≠ u) :
    x + ((m₂ - v₂) - (m₁ - v₁)) ∈ A := by
  have huv₂ : u < v₂ := by omega
  have hy : m₁ - v₁ - x ∈ A :=
    (hdes₁.pinned_level h0 hcov hred hu0 huv₁ hN₀ hN₁ hclear₁).2
      x hx hxu hwin
  have hz : m₂ - v₂ - (m₁ - v₁ - x) ∈ A :=
    (hdes₂.pinned_level h0 hcov hred hu0 huv₂ hN₀ hN₁ hclear₂).2
      (m₁ - v₁ - x) hy hdef (by omega)
  have he : m₂ - v₂ - (m₁ - v₁ - x) = x + ((m₂ - v₂) - (m₁ - v₁)) := by
    omega
  exact he ▸ hz

theorem cofinal_pinned_levels {A L : Set ℕ} {N₀ N₁ u : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hL : L.Infinite)
    (hred : TwoRedundant A u N₁)
    (hu0 : 0 < u) (hN₀ : N₀ ≤ u) (hN₁ : N₁ ≤ u)
    (hclear : ∀ v ∈ L, u < v →
      ∃ m, 3 * v ≤ m ∧ IsPairDestroyer A u v m) :
    ∀ K, ∃ v m, K ≤ v ∧ u < v ∧ 3 * v ≤ m ∧ K ≤ m - v ∧
      m - v ∈ A ∧ ∀ x ∈ A, x ≠ u → u + x < v → m - v - x ∈ A := by
  intro K
  obtain ⟨v, hvL, hv⟩ := hL.exists_gt (max K u)
  have hKv : K < v := lt_of_le_of_lt (le_max_left _ _) hv
  have huv : u < v := lt_of_le_of_lt (le_max_right _ _) hv
  obtain ⟨m, hm, hdes⟩ := hclear v hvL huv
  obtain ⟨hcorep, hmirror⟩ :=
    hdes.pinned_level h0 hcov hred hu0 huv hN₀ hN₁ hm
  exact ⟨v, m, by omega, huv, hm, by omega, hcorep, hmirror⟩

end Erdos881
