import Erdos881.HuggingSplice

/-!
# The total clique kill: single redundancy suffices

The hugging splice still assumed *joint* redundancy of each pair.
This file removes that: for `x` below the window `v - u`, the
avoiding representation of `u + x` supplied by single redundancy of
`u` dodges `v` automatically.  Consequently, for **any** destroyer of
an edge at a 2-redundant guard:

* `upper_desert_of_redundant` — between the channels (inside the
  window) no element exists away from the two diagonals;
* `level_lower_of_redundant` — the level `m - v` cannot lag far
  behind the window `v - u`: three stacked covering windows would
  starve in that desert (two diagonal values spoil at most two);
* `redundant_edge_mirror` — the fork mirror at level `m - v` on the
  full window, with truncation handling the out-of-range promise;
* `surviving_deletion_of_redundant_edges` — **a 2-redundant guard
  with partners carrying destroyers above every bound forces a
  surviving deletion.  No hugging, clearance, or joint-redundancy
  hypothesis remains.**

With this, the only clique escape left is a clique of *ineligible*
vertices: members `u` that are 2-necessary at some witness above
every threshold `N₁ ≤ u` — the Grekos-type finiteness object
(Open Link B1).
-/

namespace Erdos881

/-- **Upper desert, single redundancy.**  Inside the window
(`u + x < v`) and above the `v`-channel (`m < v + x`), away from the
two diagonals, no element can exist: redundancy of `u` alone pins the
`u`-channel shut and the `v`-channel is out of range. -/
theorem IsPairDestroyer.upper_desert_of_redundant
    {A : Set ℕ} {N₀ N₁ u v m x : ℕ}
    (hcov : PairCovers A N₀)
    (hred : TwoRedundant A u N₁)
    (hdes : IsPairDestroyer A u v m)
    (huv : u < v) (hN₁ : N₁ ≤ u)
    (hx : x ∈ A) (hxu : x ≠ u)
    (hxm : x + N₀ ≤ m) (hxum : u + x ≤ m) (hwin : u + x < v)
    (hxvm : m < v + x)
    (hd1 : m ≠ 2 * u + x) (hd2 : m ≠ u + v + x) :
    False := by
  obtain ⟨s, hs, t, ht, hst, hsu, htu⟩ := hred (u + x) (by omega)
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

/-- **Levels cannot lag the window.**  If `m - v` were far below
`v - u`, three stacked covering windows would land in the upper
desert; the two diagonal values spoil at most two of them. -/
theorem IsPairDestroyer.level_lower_of_redundant
    {A : Set ℕ} {N₀ N₁ u v m : ℕ}
    (hcov : PairCovers A N₀)
    (hred : TwoRedundant A u N₁)
    (hdes : IsPairDestroyer A u v m)
    (hu0 : 0 < u) (huv : u < v) (hvm : v ≤ m)
    (hN₁ : N₁ ≤ u)
    (hbig : 100 * ((m - v) + u + N₀ + N₁ + 3) ≤ v) :
    False := by
  set W := (m - v) + u + N₀ + 2 with hW
  have hkill : ∀ x ∈ A, m - v < x → u + x < v → x + N₀ ≤ m →
      x ≠ u → x ≠ m - 2 * u → x ≠ m - u - v → False := by
    intro x hxA hxl hxw hxm hxu hxd1 hxd2
    exact hdes.upper_desert_of_redundant hcov hred huv hN₁ hxA hxu
      hxm (by omega) hxw (by omega) (by omega) (by omega)
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
  -- windows [W,2W], [5W,10W], [25W,50W] are disjoint; the two
  -- diagonal values spoil at most two of them
  by_cases e₁ : x₁ = m - 2 * u ∨ x₁ = m - u - v
  · by_cases e₂ : x₂ = m - 2 * u ∨ x₂ = m - u - v
    · exact hkill x₃ hx₃A (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)
    · push Not at e₂
      exact hkill x₂ hx₂A (by omega) (by omega) (by omega) (by omega)
        e₂.1 e₂.2
  · push Not at e₁
    exact hkill x₁ hx₁A (by omega) (by omega) (by omega) (by omega)
      e₁.1 e₁.2

/-- **The fork mirror at a redundant edge.**  Every element inside
the window reflects through the level `m - v` (truncation makes the
out-of-range promise vacuous), with defects only at `u` and the two
diagonals. -/
theorem IsPairDestroyer.redundant_edge_mirror
    {A : Set ℕ} {N₀ N₁ u v m z : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hred : TwoRedundant A u N₁)
    (hdes : IsPairDestroyer A u v m)
    (huv : u < v) (hvm : v ≤ m) (hN₁ : N₁ ≤ u)
    (hz : z ∈ A) (hzu : z ≠ u)
    (hd1 : m ≠ 2 * u + z) (hd2 : m ≠ u + v + z)
    (hzw : z + N₀ + u < v) :
    m - v - z ∈ A := by
  rcases Nat.lt_or_ge (m - v) z with hzM | hzM
  · have : m - v - z = 0 := by omega
    rw [this]
    exact h0
  · obtain ⟨s, hs, t, ht, hst, hsu, htu⟩ := hred (u + z) (by omega)
    have hzv : z ≠ v := by omega
    have hzm : z + N₀ ≤ m := by omega
    have hzum : u + z ≤ m := by omega
    have hsv : s ≠ v := by omega
    have htv : t ≠ v := by omega
    exact hdes.pinned_mirror_sharp hcov hz hzu hzv hzm hzum
      ⟨s, hs, t, ht, hst, hsu, hsv, htu, htv⟩ hd1 hd2

/-- The corep of a redundant edge is an element whenever the level is
positive and off-diagonal. -/
theorem IsPairDestroyer.redundant_corep
    {A : Set ℕ} {N₀ N₁ u v m : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hred : TwoRedundant A u N₁)
    (hdes : IsPairDestroyer A u v m)
    (hu0 : 0 < u) (huv : u < v) (hvm : v ≤ m) (hN₁ : N₁ ≤ u)
    (hN₀ : N₀ ≤ u)
    (hd1 : m ≠ 2 * u) (hd2 : m ≠ u + v) (hwin : N₀ + u < v) :
    m - v ∈ A := by
  have h := hdes.redundant_edge_mirror h0 hcov hred huv hvm hN₁
    h0 (by omega) (by omega) (by omega) (by omega)
  simpa using h

set_option linter.unusedVariables false in
/-- The mirror in engine-ready defect form: `z` avoiding the two
diagonal *values* suffices. -/
theorem IsPairDestroyer.redundant_edge_mirror'
    {A : Set ℕ} {N₀ N₁ u v m z : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hred : TwoRedundant A u N₁)
    (hdes : IsPairDestroyer A u v m)
    (huv : u < v) (hvm : v ≤ m) (hN₁ : N₁ ≤ u)
    (hz : z ∈ A) (hzu : z ≠ u)
    (hzd1 : z ≠ m - 2 * u) (hzd2 : z ≠ m - u - v)
    (h2u : 2 * u < m) (huvm : u + v < m)
    (hzw : z + N₀ + u < v) :
    m - v - z ∈ A :=
  hdes.redundant_edge_mirror h0 hcov hred huv hvm hN₁ hz hzu
    (by omega) (by omega) hzw

/-- **The total clique kill.**  A 2-redundant guard whose partners
carry destroyers above every bound forces a surviving infinite
deletion — no hugging, clearance, or joint-redundancy hypothesis.
Levels are at least `~(v - u)/18` by `level_lower_of_redundant`, so
they grow with partners; windows swallow all lower data by partner
choice; the quad-defect engine runs with defects
`u, v, m - 2u, m - u - v`. -/
theorem surviving_deletion_of_redundant_edges
    {A : Set ℕ} {N₀ N₁ u c : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hred : TwoRedundant A u N₁)
    (hu0 : 0 < u) (hN₀ : N₀ ≤ u) (hN₁ : N₁ ≤ u)
    (hsupply : ∀ K, ∃ v m, K < v ∧ u < v ∧ v ≤ m ∧
      IsPairDestroyer A u v m)
    (hc : c ∈ A) (hc0 : 0 < c) (hcu : c ≠ u)
    (hw : ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ u ∧ w' ≠ u) :
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
  classical
  obtain ⟨w, hwA, w', hw'A, hww, hwc, hwu, hw'u⟩ := hw
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
      ∀ z ∈ A, z ≠ u → z ≠ pv (b (κ k)) →
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
      fun h => h5.level_lower_of_redundant hcov hred hu0 h2 h3 hN₁ h
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
      exact h5.redundant_corep h0 hcov hred hu0 h2 h3 hN₁ hN₀
        hd1 hd2 (by omega)
    · intro z hz hzu hzv hzd1 hzd2 hzw
      rw [hLk]
      exact h5.redundant_edge_mirror' h0 hcov hred h2 h3 hN₁
        hz hzu hzd1 hzd2 (by omega) (by omega) (by omega)
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
  refine surviving_deletion_of_quadDefects L
    (fun k => pv (b (κ k)) - u - u - N₀)
    (fun _ => u) (fun k => pv (b (κ k)))
    (fun k => pm (b (κ k)) - 2 * u)
    (fun k => pm (b (κ k)) - u - pv (b (κ k)))
    h0 hcov hmono ?_
    (fun k => (hstep k).2.1) hgrow hc hc0 ?_ ?_ ?_
    hwA hw'A hww hwc ?_ ?_ ?_ ?_
  · intro k z hz hz1 hz2 hz3 hz4 hzW
    have h := (hstep k).2.2.2.2.2.2 z hz hz1 hz2 hz3 hz4
    have hW : z + N₀ + u < pv (b (κ k)) - u := by
      show z + N₀ + u < pv (b (κ k)) - u
      have h1 := hvbig k
      have hzW' : z + N₀ < pv (b (κ k)) - u - u - N₀ := hzW
      omega
    exact h hW
  · have h1 := (hstep 0).1
    have h2 := hκK₀ 0
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

/-- **The grand assembly, final form.**  Under cofinal pair funnels
and anchor abundance, a counterexample structure has exactly three
escapes: a surviving deletion (contradiction with counterexamplehood),
cofinal zero-guardianship, or an infinite team clique **all of whose
positive, above-threshold vertices fail 2-redundancy at every
eligible threshold** — the Grekos-type finiteness object of Open Link
B1.  Every redundant vertex, whatever its edges look like, is dead. -/
theorem erdos881_grand_assembly'' {A : Set ℕ} {N₀ : ℕ}
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
        ¬ TwoRedundant A u N₁) := by
  rcases infinite_teamClique_or_cofinal_privatePairs hA hfunnel with
    ⟨L, hLA, hLinf, hLcl⟩ | ⟨L, hLA, hLinf, hstream⟩
  · by_cases hel : ∃ u ∈ L, 0 < u ∧ N₀ ≤ u ∧ ∃ N₁, N₁ ≤ u ∧
        TwoRedundant A u N₁
    · obtain ⟨u, huL, hu0, huN₀, N₁, hN₁u, hred⟩ := hel
      obtain ⟨c, hc, hc0, hcu, w, hwA, w', hw'A, hww, hwc, hwu, hw'u⟩ :=
        hanchor u
      refine Or.inl (surviving_deletion_of_redundant_edges h0 hcov
        hred hu0 huN₀ hN₁u (fun K => ?_) hc hc0 hcu
        ⟨w, hwA, w', hw'A, hww, hwc, hwu, hw'u⟩)
      obtain ⟨v, hvL, hv⟩ := hLinf.exists_gt (max K u)
      have hKv : K < v := lt_of_le_of_lt (le_max_left _ _) hv
      have huv : u < v := lt_of_le_of_lt (le_max_right _ _) hv
      obtain ⟨-, m, hum, hvm, hdes⟩ :=
        hLcl huL hvL (by omega)
      exact ⟨v, m, hKv, huv, hvm, hdes⟩
    · push Not at hel
      exact Or.inr (Or.inr ⟨L, hLA, hLinf, hLcl,
        fun u huL hu0 huN₀ N₁ hN₁u => hel u huL hu0 huN₀ N₁ hN₁u⟩)
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

/-- **The escape vertices are self-scale 2-guardians.**  A vertex
failing 2-redundancy at its own scale has a witness `n ≥ u` whose
every two-term representation passes through `u`; its corep `n - u`
is an element and the entire two-support is `{u, n - u}`.  The final
clique escape of `erdos881_grand_assembly''` is therefore an infinite
clique of elements each two-guarding a target at or above its own
scale — the Grekos-type configuration of Open Link B1. -/
theorem escape_vertex_witness {A : Set ℕ} {N₀ u : ℕ}
    (hcov : PairCovers A N₀)
    (hu : ¬ TwoRedundant A u u) (huN : N₀ ≤ u) :
    ∃ n, u ≤ n ∧ n - u ∈ A ∧
      ∀ y ∈ A, y ≤ n → n - y ∈ A → y = u ∨ y = n - u := by
  rw [TwoRedundant] at hu
  push Not at hu
  obtain ⟨n, hn, hno⟩ := hu
  have hall : ∀ y ∈ A, ∀ z ∈ A, y + z = n → y = u ∨ z = u := by
    intro y hy z hz hyz
    by_cases hyu : y = u
    · exact Or.inl hyu
    · exact Or.inr (hno y hy z hz hyz hyu)
  obtain ⟨y, hy, z, hz, hyz⟩ := hcov n (by omega)
  refine ⟨n, hn, ?_, ?_⟩
  · rcases hall y hy z hz hyz with h | h
    · have : z = n - u := by omega
      exact this ▸ hz
    · have : y = n - u := by omega
      exact this ▸ hy
  · intro y' hy' hy'n hny'
    rcases hall y' hy' (n - y') hny' (by omega) with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)

/-- **The final conditional theorem.**  Modulo the three remaining
open interfaces — cofinal pair funnels (Link A), no infinite clique of
self-scale 2-guardians (Link B1, the Grekos configuration), and no
cofinal zero-guardianship — plus anchor abundance, every counterexample
structure admits a surviving infinite deletion: the positive answer to
Erdős 881 (k = 2). -/
theorem erdos881_positive_conditional {A : Set ℕ} {N₀ : ℕ}
    (hA : A.Infinite) (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfunnel : HasCofinalPairFunnels A)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hzero : ¬ ∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A 0 m)
    (hB1 : ¬ ∃ L, L ⊆ A ∧ L.Infinite ∧ L.Pairwise (TeamEdge A) ∧
      ∀ u ∈ L, 0 < u → N₀ ≤ u → ∀ N₁, N₁ ≤ u →
        ¬ TwoRedundant A u N₁) :
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
  rcases erdos881_grand_assembly'' hA h0 hcov hfunnel hanchor with
    h | h | h
  · exact h
  · exact absurd h hzero
  · exact absurd h hB1

end Erdos881
