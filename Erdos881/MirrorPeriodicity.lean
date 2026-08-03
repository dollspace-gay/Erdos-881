import Erdos881.GuardianRigidity

namespace Erdos881

/-- `M` is a reflection level of `A`: strictly below `M`, positive
membership is symmetric under `z ↦ M - z`. -/
def IsReflectionLevel (A : Set ℕ) (M : ℕ) : Prop :=
  ∀ z, 0 < z → z < M → (z ∈ A ↔ M - z ∈ A)

/-- A big-required element private pair forces a reflection level at its
co-representative `M = m - a`. -/
theorem IsPrivateTriple.reflectionLevel {A : Set ℕ} {N₀ a m : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hpriv : IsPrivateTriple A a m)
    (hbig : m < 2 * a) (haN : N₀ + a ≤ m) :
    IsReflectionLevel A (m - a) := by
  have dir : ∀ z, 0 < z → z < m - a → z ∈ A → (m - a) - z ∈ A := by
    intro z hz0 hzM hz
    obtain ⟨w, hw, hws⟩ := hpriv.mirror h0 hcov hbig haN hz hz0 (by omega)
    have hwe : w = (m - a) - z := by omega
    exact hwe ▸ hw
  intro z hz0 hzM
  constructor
  · exact dir z hz0 hzM
  · intro h
    have hz' := dir ((m - a) - z) (by omega) (by omega) h
    have heq : (m - a) - ((m - a) - z) = z := by omega
    exact heq ▸ hz'

/-- Two reflection levels compose to a translation by their gap on the
range below the lower level. -/
theorem IsReflectionLevel.translation {A : Set ℕ} {M₁ M₂ : ℕ}
    (h₁ : IsReflectionLevel A M₁) (h₂ : IsReflectionLevel A M₂)
    (hlt : M₁ < M₂) {z : ℕ} (hz0 : 0 < z) (hzM : z < M₁) :
    (z ∈ A ↔ z + (M₂ - M₁) ∈ A) := by
  have e1 : z ∈ A ↔ M₁ - z ∈ A := h₁ z hz0 hzM
  have e2 : M₁ - z ∈ A ↔ M₂ - (M₁ - z) ∈ A :=
    h₂ (M₁ - z) (by omega) (by omega)
  have e3 : M₂ - (M₁ - z) = z + (M₂ - M₁) := by omega
  rw [e1, e2, e3]

/-- A cofinally recurring gap between reflection levels upgrades the local
translations to full periodicity on the positive integers. -/
theorem periodic_of_recurring_reflectionLevels {A : Set ℕ} {d : ℕ}
    (h : ∀ K, ∃ M₁ M₂, K ≤ M₁ ∧ M₁ < M₂ ∧ M₂ - M₁ = d ∧
      IsReflectionLevel A M₁ ∧ IsReflectionLevel A M₂) :
    ∀ z, 0 < z → (z ∈ A ↔ z + d ∈ A) := by
  intro z hz0
  obtain ⟨M₁, M₂, hK, hlt, hgap, h₁, h₂⟩ := h (z + 1)
  have ht := h₁.translation h₂ hlt hz0 (by omega)
  rwa [hgap] at ht

/-- Bounded-gap pigeonhole: a strictly monotone stream of reflection
levels with gaps at most `C` yields one gap value recurring cofinally. -/
theorem exists_recurring_gap {A : Set ℕ} {C : ℕ} (L : ℕ → ℕ)
    (hmono : StrictMono L)
    (hlev : ∀ k, IsReflectionLevel A (L k))
    (hgap : ∀ k, L (k + 1) ≤ L k + C) :
    ∃ d, 0 < d ∧ d ≤ C ∧ ∀ K, ∃ M₁ M₂, K ≤ M₁ ∧ M₁ < M₂ ∧
      M₂ - M₁ = d ∧ IsReflectionLevel A M₁ ∧ IsReflectionLevel A M₂ := by
  classical
  have hC : ∀ k, 1 ≤ L (k + 1) - L k ∧ L (k + 1) - L k ≤ C := by
    intro k
    have h1 : L k < L (k + 1) := hmono (by omega)
    have h2 := hgap k
    omega
  have hCpos : 0 < C := by have := hC 0; omega
  have hle : ∀ k, k ≤ L k := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
        have h1 : L k < L (k + 1) := hmono (by omega)
        omega
  let f : ℕ → Fin C := fun k => ⟨L (k + 1) - L k - 1, by have := hC k; omega⟩
  obtain ⟨b, hb⟩ := Finite.exists_infinite_fiber f
  rw [Set.infinite_coe_iff] at hb
  have hbval := b.isLt
  refine ⟨b.val + 1, by omega, by omega, ?_⟩
  intro K
  obtain ⟨k, hkfib, hkK⟩ := hb.exists_gt K
  have hfk : f k = b := by simpa using hkfib
  have hval : L (k + 1) - L k - 1 = b.val := by
    have := congrArg Fin.val hfk
    simpa [f] using this
  have hgk : L (k + 1) - L k = b.val + 1 := by
    have := hC k
    omega
  exact ⟨L k, L (k + 1), by have := hle k; omega,
    hmono (Nat.lt_succ_self k), hgk, hlev k, hlev (k + 1)⟩

theorem periodic_covering_admits_surviving_deletion
    {A : Set ℕ} {N₀ d : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) (hd : 0 < d)
    (hper : ∀ z, 0 < z → (z ∈ A ↔ z + d ∈ A)) :
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
  classical
  obtain ⟨c, hc, hc0⟩ := hcov.exists_pos_mem
  have hclass : ∀ j : ℕ, c + j * d ∈ A := by
    intro j
    induction j with
    | zero => simpa using hc
    | succ j ih =>
        have hpos : 0 < c + j * d := by omega
        have h := (hper _ hpos).mp ih
        have he : c + j * d + d = c + (j + 1) * d := by ring
        rwa [he] at h
  have hup : ∀ y, 0 < y → y ∈ A → ∀ k : ℕ, y + k * d ∈ A := by
    intro y hy0 hy k
    induction k with
    | zero => simpa using hy
    | succ k ih =>
        have hpos : 0 < y + k * d := by omega
        have h := (hper _ hpos).mp ih
        have he : y + k * d + d = y + (k + 1) * d := by ring
        rwa [he] at h
  set k₀ := 8 * N₀ + 16 with hk₀def
  set f : ℕ → ℕ := fun k => c + (k₀ + 4 * k) * d with hfdef
  have hfA : ∀ k, f k ∈ A := fun k => hclass _
  have hfinj : Function.Injective f := by
    intro i j hij
    simp only [hfdef] at hij
    have h1 : (k₀ + 4 * i) * d = (k₀ + 4 * j) * d := by omega
    have h2 := Nat.eq_of_mul_eq_mul_right hd h1
    omega
  have h0B : (0 : ℕ) ∉ Set.range f := by
    rintro ⟨k, hk⟩
    simp only [hfdef] at hk
    omega
  have hminB : ∀ w ∈ Set.range f, c + k₀ * d ≤ w := by
    rintro w ⟨k, rfl⟩
    simp only [hfdef]
    have h1 : k₀ * d ≤ (k₀ + 4 * k) * d := Nat.mul_le_mul (by omega) (le_refl d)
    omega
  have hnotB : ∀ (i k : ℕ), k ≤ k₀ + 4 * i → ¬ (4 ∣ k) →
      c + (k₀ + 4 * i - k) * d ∉ Set.range f := by
    intro i k hkle h4
    rintro ⟨i', hi'⟩
    simp only [hfdef] at hi'
    have h1 : (k₀ + 4 * i') * d = (k₀ + 4 * i - k) * d := by omega
    have h2 := Nat.eq_of_mul_eq_mul_right hd h1
    exact h4 ⟨i - i', by omega⟩
  have hone : ∀ w : ℕ, w + 1 * d ∈ Set.range f → w + 2 * d ∈ Set.range f →
      False := by
    intro w h1 h2
    obtain ⟨i₁, hi₁⟩ := h1
    obtain ⟨i₂, hi₂⟩ := h2
    simp only [hfdef] at hi₁ hi₂
    have he : (k₀ + 4 * i₁ + 1) * d = (k₀ + 4 * i₁) * d + d := by ring
    have h3 : (k₀ + 4 * i₂) * d = (k₀ + 4 * i₁ + 1) * d := by omega
    have h4 := Nat.eq_of_mul_eq_mul_right hd h3
    omega
  have hsplitk : ∀ (j k : ℕ), k ≤ j → (j - k) * d + k * d = j * d := by
    intro j k hk
    have h : (j - k) + k = j := by omega
    calc (j - k) * d + k * d = ((j - k) + k) * d := by ring
      _ = j * d := by rw [h]
  -- repair a target that is itself a deleted element
  have hrepair_mem : ∀ i : ℕ, ∃ x' ∈ A, ∃ u ∈ A, ∃ v ∈ A,
      x' ∉ Set.range f ∧ u ∉ Set.range f ∧ v ∉ Set.range f ∧
      x' + u + v = f i := by
    intro i
    set k := 4 * N₀ + 5 with hkdef
    have hkle : k ≤ k₀ + 4 * i := by omega
    have hx' : c + (k₀ + 4 * i - k) * d ∈ A := hclass _
    have hx'B : c + (k₀ + 4 * i - k) * d ∉ Set.range f :=
      hnotB i k hkle (by rintro ⟨t, ht⟩; omega)
    have hkd : N₀ ≤ k * d := by
      have h1 : k ≤ k * d := by
        calc k = k * 1 := by ring
          _ ≤ k * d := Nat.mul_le_mul (le_refl k) (by omega)
      omega
    obtain ⟨u, hu, v, hv, huv⟩ := hcov (k * d) hkd
    have hsmall : k * d < c + k₀ * d := by
      have h1 : k * d < k₀ * d := mul_lt_mul_of_pos_right (by omega) hd
      omega
    have huB : u ∉ Set.range f := fun hmem => by
      have := hminB _ hmem; omega
    have hvB : v ∉ Set.range f := fun hmem => by
      have := hminB _ hmem; omega
    refine ⟨_, hx', u, hu, v, hv, hx'B, huB, hvB, ?_⟩
    have hsplit := hsplitk (k₀ + 4 * i) k (by omega)
    simp only [hfdef]
    omega
  refine ⟨Set.range f, ?_, Set.infinite_range_of_injective hfinj, ?_⟩
  · rintro w ⟨k, rfl⟩; exact hfA k
  intro n hn
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov n hn
  by_cases hxB : x ∈ Set.range f
  · obtain ⟨i, hix⟩ := hxB
    rcases Nat.eq_zero_or_pos y with hy0 | hy0
    · obtain ⟨x', hx', u, hu, v, hv, hx'B, huB, hvB, hsum⟩ := hrepair_mem i
      exact ⟨x', hx', u, hu, v, hv, hx'B, huB, hvB, by omega⟩
    · by_cases h1B : y + 1 * d ∈ Set.range f
      · refine ⟨c + (k₀ + 4 * i - 2) * d, hclass _, y + 2 * d,
          hup y hy0 hy 2, 0, h0,
          hnotB i 2 (by omega) (by rintro ⟨t, ht⟩; omega),
          (fun h2B => hone y h1B h2B), h0B, ?_⟩
        have hsplit := hsplitk (k₀ + 4 * i) 2 (by omega)
        simp only [hfdef] at hix
        omega
      · refine ⟨c + (k₀ + 4 * i - 1) * d, hclass _, y + 1 * d,
          hup y hy0 hy 1, 0, h0,
          hnotB i 1 (by omega) (by rintro ⟨t, ht⟩; omega), h1B, h0B, ?_⟩
        have hsplit := hsplitk (k₀ + 4 * i) 1 (by omega)
        simp only [hfdef] at hix
        omega
  · by_cases hyB : y ∈ Set.range f
    · obtain ⟨i, hiy⟩ := hyB
      rcases Nat.eq_zero_or_pos x with hx0 | hx0
      · obtain ⟨x', hx', u, hu, v, hv, hx'B, huB, hvB, hsum⟩ := hrepair_mem i
        exact ⟨x', hx', u, hu, v, hv, hx'B, huB, hvB, by omega⟩
      · by_cases h1B : x + 1 * d ∈ Set.range f
        · refine ⟨c + (k₀ + 4 * i - 2) * d, hclass _, x + 2 * d,
            hup x hx0 hx 2, 0, h0,
            hnotB i 2 (by omega) (by rintro ⟨t, ht⟩; omega),
            (fun h2B => hone x h1B h2B), h0B, ?_⟩
          have hsplit := hsplitk (k₀ + 4 * i) 2 (by omega)
          simp only [hfdef] at hiy
          omega
        · refine ⟨c + (k₀ + 4 * i - 1) * d, hclass _, x + 1 * d,
            hup x hx0 hx 1, 0, h0,
            hnotB i 1 (by omega) (by rintro ⟨t, ht⟩; omega), h1B, h0B, ?_⟩
          have hsplit := hsplitk (k₀ + 4 * i) 1 (by omega)
          simp only [hfdef] at hiy
          omega
    · exact ⟨x, hx, y, hy, 0, h0, hxB, hyB, h0B, by omega⟩

/-- Mirrors → repetition → spare keys, for a recurring gap. -/
theorem surviving_deletion_of_recurring_reflectionLevels
    {A : Set ℕ} {N₀ d : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) (hd : 0 < d)
    (hlev : ∀ K, ∃ M₁ M₂, K ≤ M₁ ∧ M₁ < M₂ ∧ M₂ - M₁ = d ∧
      IsReflectionLevel A M₁ ∧ IsReflectionLevel A M₂) :
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n :=
  periodic_covering_admits_surviving_deletion h0 hcov hd
    (periodic_of_recurring_reflectionLevels hlev)

theorem surviving_deletion_of_boundedGap_reflectionLevels
    {A : Set ℕ} {N₀ C : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (L : ℕ → ℕ) (hmono : StrictMono L)
    (hlev : ∀ k, IsReflectionLevel A (L k))
    (hgap : ∀ k, L (k + 1) ≤ L k + C) :
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
  obtain ⟨d, hd0, _, hrec⟩ := exists_recurring_gap L hmono hlev hgap
  exact surviving_deletion_of_recurring_reflectionLevels h0 hcov hd0 hrec

end Erdos881
