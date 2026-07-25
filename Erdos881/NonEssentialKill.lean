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

end Erdos881
