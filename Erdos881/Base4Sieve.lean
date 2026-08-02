/-
# The base-4 sieve, part one: mixed carry menus below scale

Toward the full deletion theorem (every large `n` has an order-4
representation from the base-4 set avoiding all pure powers), this
file repairs the mixed degenerate digit shapes with the offending
scale on top:

* `2·4^p + 4^v`  (`v < p`)  — `base4_repair_double_mixed`,
* `3·4^p + 4^v`  (`v < p`)  — `base4_repair_triple_mixed`,
* `3·4^p + 2·4^v` (`v < p`) — `base4_repair_triple_mixedTwo`.

Method: expand the top block by one of the verified carry menus and
attach the stray bits to menu parts whose digit windows avoid them;
the four near-collision positions `v ∈ {p-1, p-2, p-3, p-4}` get
explicit constant menus, everything lower attaches generically via
`isBase4_scaled_add`.  All parts are digit-{0,1} and strictly
between consecutive powers or scaled non-powers, so none is pure.
-/

import Erdos881.Base4CarryRepair

namespace Erdos881Base4

/-- Split a power at a lower scale. -/
lemma pow_shift_eq (p t : ℕ) (h : t ≤ p) :
    (4 : ℕ) ^ p = 4 ^ t * 4 ^ (p - t) := by
  rw [← pow_add]
  congr 1
  omega

/-- Attach a small tail below a scaled digit block. -/
lemma isBase4_scaled_add {y m x : ℕ} (hy : IsBase4 y)
    (hx : IsBase4 x) (hlt : x < 4 ^ m) :
    IsBase4 (y * 4 ^ m + x) := by
  intro i
  rcases Nat.lt_or_ge i m with h | h
  · have hsplit :
        y * 4 ^ m = 4 ^ i * (y * 4 ^ (m - i)) := by
      rw [pow_shift_eq m i (Nat.le_of_lt h)]
      ring
    have hdiv :
        (y * 4 ^ m + x) / 4 ^ i =
          y * 4 ^ (m - i) + x / 4 ^ i := by
      rw [hsplit, Nat.mul_add_div (pow4_pos i)]
    rw [hdiv]
    have h4 : m - i = (m - i - 1) + 1 := by omega
    have hxi := hx i
    rw [h4, pow_succ]
    have hres :
        y * (4 ^ (m - i - 1) * 4) + x / 4 ^ i =
          4 * (y * 4 ^ (m - i - 1)) + x / 4 ^ i := by
      ring
    rw [hres]
    omega
  · have hdd :
        (y * 4 ^ m + x) / 4 ^ i =
          (y * 4 ^ m + x) / 4 ^ m / 4 ^ (i - m) := by
      rw [Nat.div_div_eq_div_mul, ← pow_add]
      congr 2
      omega
    have hin : (y * 4 ^ m + x) / 4 ^ m = y := by
      rw [Nat.mul_comm,
        Nat.mul_add_div (pow4_pos m),
        Nat.div_eq_of_lt hlt]
      omega
    rw [hdd, hin]
    exact hy (i - m)

/-- Scaled digit constants are base-4. -/
lemma isBase4_scaledConst {c L : ℕ} (m : ℕ)
    (hc : c < 4 ^ L)
    (h : ∀ i < L, c / 4 ^ i % 4 ≤ 1) :
    IsBase4 (c * 4 ^ m) := by
  rw [Nat.mul_comm]
  exact isBase4_shift m (isBase4_of_digits hc h)

/-- **Mixed repair `2·4^p + 4^v`, stray bit below scale.** -/
theorem base4_repair_double_mixed (p v : ℕ)
    (hp : 8 ≤ p) (hvp : v < p) :
    ∃ a b c d, IsBase4 a ∧ IsBase4 b ∧ IsBase4 c ∧
      IsBase4 d ∧
      (∀ j, a ≠ 4 ^ j) ∧ (∀ j, b ≠ 4 ^ j) ∧
      (∀ j, c ≠ 4 ^ j) ∧ (∀ j, d ≠ 4 ^ j) ∧
      a + b + c + d = 2 * 4 ^ p + 4 ^ v := by
  have h256 : (4 : ℕ) ^ p = 256 * 4 ^ (p - 4) := by
    have h := pow_shift_eq p 4 (by omega)
    norm_num at h
    exact h
  rcases Nat.lt_or_ge v (p - 4) with hlow | hhigh
  · refine
      ⟨272 * 4 ^ (p - 4) + 4 ^ v, 80 * 4 ^ (p - 4),
        80 * 4 ^ (p - 4), 80 * 4 ^ (p - 4),
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact isBase4_scaled_add
        (isBase4_of_digits (c := 272) (L := 5)
          (by norm_num) (by decide))
        (isBase4_pow v)
        (Nat.pow_lt_pow_right (by norm_num) hlow)
    · exact isBase4_scaledConst (c := 80) (L := 4)
        (p - 4) (by norm_num) (by decide)
    · exact isBase4_scaledConst (c := 80) (L := 4)
        (p - 4) (by norm_num) (by decide)
    · exact isBase4_scaledConst (c := 80) (L := 4)
        (p - 4) (by norm_num) (by decide)
    · have hvw : (4 : ℕ) ^ v < 4 ^ (p - 4) :=
        Nat.pow_lt_pow_right (by norm_num) hlow
      have h1024 : (4 : ℕ) ^ (p + 1) =
          1024 * 4 ^ (p - 4) := by
        have h := pow_shift_eq (p + 1) 5 (by omega)
        have he : p + 1 - 5 = p - 4 := by omega
        rw [he] at h
        norm_num at h
        exact h
      have hl :
          (4 : ℕ) ^ p < 272 * 4 ^ (p - 4) + 4 ^ v :=
        calc (4 : ℕ) ^ p = 256 * 4 ^ (p - 4) := h256
          _ < 272 * 4 ^ (p - 4) :=
            Nat.mul_lt_mul_of_pos_right (by norm_num)
              (pow4_pos _)
          _ ≤ 272 * 4 ^ (p - 4) + 4 ^ v :=
            Nat.le_add_right _ _
      have hr :
          272 * 4 ^ (p - 4) + 4 ^ v < 4 ^ (p + 1) :=
        calc 272 * 4 ^ (p - 4) + 4 ^ v <
            272 * 4 ^ (p - 4) + 4 ^ (p - 4) :=
              Nat.add_lt_add_left hvw _
          _ = 273 * 4 ^ (p - 4) := by ring
          _ ≤ 1024 * 4 ^ (p - 4) :=
            Nat.mul_le_mul_right _ (by norm_num)
          _ = (4 : ℕ) ^ (p + 1) := h1024.symm
      exact fun j hj =>
        not_pure_of_bounds (L := p) hl hr ⟨j, hj⟩
    · exact fun j => not_pure_of_scaled
        (not_pure_of_bounds (c := 80) (L := 3)
          (by norm_num) (by norm_num)) j
    · exact fun j => not_pure_of_scaled
        (not_pure_of_bounds (c := 80) (L := 3)
          (by norm_num) (by norm_num)) j
    · exact fun j => not_pure_of_scaled
        (not_pure_of_bounds (c := 80) (L := 3)
          (by norm_num) (by norm_num)) j
    · rw [h256]
      ring
  · have hcase :
        v = p - 4 ∨ v = p - 3 ∨ v = p - 2 ∨
          v = p - 1 := by
      omega
    have hbody :
        ∀ c₁ c₂ c₃ c₄ : ℕ,
          c₁ < 4 ^ 5 → c₂ < 4 ^ 5 → c₃ < 4 ^ 5 →
          c₄ < 4 ^ 5 →
          (∀ i < 5, c₁ / 4 ^ i % 4 ≤ 1) →
          (∀ i < 5, c₂ / 4 ^ i % 4 ≤ 1) →
          (∀ i < 5, c₃ / 4 ^ i % 4 ≤ 1) →
          (∀ i < 5, c₄ / 4 ^ i % 4 ≤ 1) →
          (¬∃ t, c₁ = 4 ^ t) → (¬∃ t, c₂ = 4 ^ t) →
          (¬∃ t, c₃ = 4 ^ t) → (¬∃ t, c₄ = 4 ^ t) →
          c₁ * 4 ^ (p - 4) + c₂ * 4 ^ (p - 4) +
              c₃ * 4 ^ (p - 4) + c₄ * 4 ^ (p - 4) =
            2 * 4 ^ p + 4 ^ v →
          ∃ a b c d, IsBase4 a ∧ IsBase4 b ∧
            IsBase4 c ∧ IsBase4 d ∧
            (∀ j, a ≠ 4 ^ j) ∧ (∀ j, b ≠ 4 ^ j) ∧
            (∀ j, c ≠ 4 ^ j) ∧ (∀ j, d ≠ 4 ^ j) ∧
            a + b + c + d = 2 * 4 ^ p + 4 ^ v := by
      intro c₁ c₂ c₃ c₄ hb₁ hb₂ hb₃ hb₄
        hd₁ hd₂ hd₃ hd₄ hn₁ hn₂ hn₃ hn₄ hsum
      exact
        ⟨c₁ * 4 ^ (p - 4), c₂ * 4 ^ (p - 4),
          c₃ * 4 ^ (p - 4), c₄ * 4 ^ (p - 4),
          isBase4_scaledConst (p - 4) hb₁ hd₁,
          isBase4_scaledConst (p - 4) hb₂ hd₂,
          isBase4_scaledConst (p - 4) hb₃ hd₃,
          isBase4_scaledConst (p - 4) hb₄ hd₄,
          fun j => not_pure_of_scaled hn₁ j,
          fun j => not_pure_of_scaled hn₂ j,
          fun j => not_pure_of_scaled hn₃ j,
          fun j => not_pure_of_scaled hn₄ j,
          hsum⟩
    have hpow :
        ∀ t : ℕ, t ≤ 4 →
          (4 : ℕ) ^ (p - t) =
            4 ^ (4 - t) * 4 ^ (p - 4) := by
      intro t ht
      have h := pow_shift_eq (p - t) (4 - t)
        (by omega)
      have he : p - t - (4 - t) = p - 4 := by omega
      rw [he] at h
      exact h
    rcases hcase with hv | hv | hv | hv
    · subst hv
      refine hbody 273 80 80 80 (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
        (by decide) (by decide) (by decide)
        (by decide)
        (not_pure_of_bounds (L := 4) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num)) ?_
      rw [h256]
      ring
    · subst hv
      refine hbody 276 80 80 80 (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
        (by decide) (by decide) (by decide)
        (by decide)
        (not_pure_of_bounds (L := 4) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num)) ?_
      have h4 := hpow 3 (by norm_num)
      norm_num at h4
      rw [h256, h4]
      ring
    · subst hv
      refine hbody 337 85 85 21 (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
        (by decide) (by decide) (by decide)
        (by decide)
        (not_pure_of_bounds (L := 4) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 2) (by norm_num)
          (by norm_num)) ?_
      have h4 := hpow 2 (by norm_num)
      norm_num at h4
      rw [h256, h4]
      ring
    · subst hv
      refine hbody 336 80 80 80 (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
        (by decide) (by decide) (by decide)
        (by decide)
        (not_pure_of_bounds (L := 4) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num)) ?_
      have h4 := hpow 1 (by norm_num)
      norm_num at h4
      rw [h256, h4]
      ring

/-- Four scaled digit constants assemble a repaired target. -/
lemma base4_menu_of_constants
    {c₁ c₂ c₃ c₄ L₁ L₂ L₃ L₄ m target : ℕ}
    (hb₁ : c₁ < 4 ^ L₁)
    (hd₁ : ∀ i < L₁, c₁ / 4 ^ i % 4 ≤ 1)
    (hb₂ : c₂ < 4 ^ L₂)
    (hd₂ : ∀ i < L₂, c₂ / 4 ^ i % 4 ≤ 1)
    (hb₃ : c₃ < 4 ^ L₃)
    (hd₃ : ∀ i < L₃, c₃ / 4 ^ i % 4 ≤ 1)
    (hb₄ : c₄ < 4 ^ L₄)
    (hd₄ : ∀ i < L₄, c₄ / 4 ^ i % 4 ≤ 1)
    (hn₁ : ¬∃ t, c₁ = 4 ^ t)
    (hn₂ : ¬∃ t, c₂ = 4 ^ t)
    (hn₃ : ¬∃ t, c₃ = 4 ^ t)
    (hn₄ : ¬∃ t, c₄ = 4 ^ t)
    (hsum :
      c₁ * 4 ^ m + c₂ * 4 ^ m + c₃ * 4 ^ m +
        c₄ * 4 ^ m = target) :
    ∃ a b c d, IsBase4 a ∧ IsBase4 b ∧ IsBase4 c ∧
      IsBase4 d ∧
      (∀ j, a ≠ 4 ^ j) ∧ (∀ j, b ≠ 4 ^ j) ∧
      (∀ j, c ≠ 4 ^ j) ∧ (∀ j, d ≠ 4 ^ j) ∧
      a + b + c + d = target :=
  ⟨c₁ * 4 ^ m, c₂ * 4 ^ m, c₃ * 4 ^ m, c₄ * 4 ^ m,
    isBase4_scaledConst m hb₁ hd₁,
    isBase4_scaledConst m hb₂ hd₂,
    isBase4_scaledConst m hb₃ hd₃,
    isBase4_scaledConst m hb₄ hd₄,
    fun j => not_pure_of_scaled hn₁ j,
    fun j => not_pure_of_scaled hn₂ j,
    fun j => not_pure_of_scaled hn₃ j,
    fun j => not_pure_of_scaled hn₄ j,
    hsum⟩

/-- **Mixed repair `3·4^p + 4^v`, stray bit below scale.** -/
theorem base4_repair_triple_mixed (p v : ℕ)
    (hp : 8 ≤ p) (hvp : v < p) :
    ∃ a b c d, IsBase4 a ∧ IsBase4 b ∧ IsBase4 c ∧
      IsBase4 d ∧
      (∀ j, a ≠ 4 ^ j) ∧ (∀ j, b ≠ 4 ^ j) ∧
      (∀ j, c ≠ 4 ^ j) ∧ (∀ j, d ≠ 4 ^ j) ∧
      a + b + c + d = 3 * 4 ^ p + 4 ^ v := by
  have h256 : (4 : ℕ) ^ p = 256 * 4 ^ (p - 4) := by
    have h := pow_shift_eq p 4 (by omega)
    norm_num at h
    exact h
  rcases Nat.lt_or_ge v (p - 4) with hlow | hhigh
  · have hvw : (4 : ℕ) ^ v < 4 ^ (p - 4) :=
      Nat.pow_lt_pow_right (by norm_num) hlow
    have h4w : (4 : ℕ) ^ (p - 3) = 4 * 4 ^ (p - 4) := by
      have h := pow_shift_eq (p - 3) 1 (by omega)
      have he : p - 3 - 1 = p - 4 := by omega
      rw [he] at h
      norm_num at h
      exact h
    have h16w :
        (4 : ℕ) ^ (p - 3 + 1) = 16 * 4 ^ (p - 4) := by
      have h := pow_shift_eq (p - 3 + 1) 2 (by omega)
      have he : p - 3 + 1 - 2 = p - 4 := by omega
      rw [he] at h
      norm_num at h
      exact h
    refine
      ⟨341 * 4 ^ (p - 4), 337 * 4 ^ (p - 4),
        85 * 4 ^ (p - 4), 5 * 4 ^ (p - 4) + 4 ^ v,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact isBase4_scaledConst (c := 341) (L := 5)
        (p - 4) (by norm_num) (by decide)
    · exact isBase4_scaledConst (c := 337) (L := 5)
        (p - 4) (by norm_num) (by decide)
    · exact isBase4_scaledConst (c := 85) (L := 4)
        (p - 4) (by norm_num) (by decide)
    · exact isBase4_scaled_add
        (isBase4_of_digits (c := 5) (L := 2)
          (by norm_num) (by decide))
        (isBase4_pow v) hvw
    · exact fun j => not_pure_of_scaled
        (not_pure_of_bounds (c := 341) (L := 4)
          (by norm_num) (by norm_num)) j
    · exact fun j => not_pure_of_scaled
        (not_pure_of_bounds (c := 337) (L := 4)
          (by norm_num) (by norm_num)) j
    · exact fun j => not_pure_of_scaled
        (not_pure_of_bounds (c := 85) (L := 3)
          (by norm_num) (by norm_num)) j
    · have hl :
          (4 : ℕ) ^ (p - 3) <
            5 * 4 ^ (p - 4) + 4 ^ v :=
        calc (4 : ℕ) ^ (p - 3) = 4 * 4 ^ (p - 4) :=
            h4w
          _ < 5 * 4 ^ (p - 4) :=
            Nat.mul_lt_mul_of_pos_right (by norm_num)
              (pow4_pos _)
          _ ≤ 5 * 4 ^ (p - 4) + 4 ^ v :=
            Nat.le_add_right _ _
      have hr :
          5 * 4 ^ (p - 4) + 4 ^ v <
            4 ^ (p - 3 + 1) :=
        calc 5 * 4 ^ (p - 4) + 4 ^ v <
            5 * 4 ^ (p - 4) + 4 ^ (p - 4) :=
              Nat.add_lt_add_left hvw _
          _ = 6 * 4 ^ (p - 4) := by ring
          _ ≤ 16 * 4 ^ (p - 4) :=
            Nat.mul_le_mul_right _ (by norm_num)
          _ = (4 : ℕ) ^ (p - 3 + 1) := h16w.symm
      exact fun j hj =>
        not_pure_of_bounds (L := p - 3) hl hr ⟨j, hj⟩
    · rw [h256]
      ring
  · have hcase :
        v = p - 4 ∨ v = p - 3 ∨ v = p - 2 ∨
          v = p - 1 := by
      omega
    have hpow :
        ∀ t : ℕ, 1 ≤ t → t ≤ 4 →
          (4 : ℕ) ^ (p - t) =
            4 ^ (4 - t) * 4 ^ (p - 4) := by
      intro t ht1 ht4
      have h := pow_shift_eq (p - t) (4 - t)
        (by omega)
      have he : p - t - (4 - t) = p - 4 := by omega
      rw [he] at h
      exact h
    rcases hcase with hv | hv | hv | hv
    · subst hv
      refine base4_menu_of_constants
        (c₁ := 340) (L₁ := 5) (c₂ := 340) (L₂ := 5)
        (c₃ := 68) (L₃ := 4) (c₄ := 21) (L₄ := 3)
        (m := p - 4)
        (by norm_num) (by decide) (by norm_num)
        (by decide) (by norm_num) (by decide)
        (by norm_num) (by decide)
        (not_pure_of_bounds (L := 4) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 4) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 2) (by norm_num)
          (by norm_num)) ?_
      rw [h256]
      ring
    · subst hv
      have h4 := hpow 3 (by norm_num) (by norm_num)
      norm_num at h4
      refine base4_menu_of_constants
        (c₁ := 341) (L₁ := 5) (c₂ := 341) (L₂ := 5)
        (c₃ := 85) (L₃ := 4) (c₄ := 5) (L₄ := 2)
        (m := p - 4)
        (by norm_num) (by decide) (by norm_num)
        (by decide) (by norm_num) (by decide)
        (by norm_num) (by decide)
        (not_pure_of_bounds (L := 4) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 4) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 1) (by norm_num)
          (by norm_num)) ?_
      rw [h256, h4]
      ring
    · subst hv
      have h4 := hpow 2 (by norm_num) (by norm_num)
      norm_num at h4
      refine base4_menu_of_constants
        (c₁ := 341) (L₁ := 5) (c₂ := 337) (L₂ := 5)
        (c₃ := 85) (L₃ := 4) (c₄ := 21) (L₄ := 3)
        (m := p - 4)
        (by norm_num) (by decide) (by norm_num)
        (by decide) (by norm_num) (by decide)
        (by norm_num) (by decide)
        (not_pure_of_bounds (L := 4) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 4) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 2) (by norm_num)
          (by norm_num)) ?_
      rw [h256, h4]
      ring
    · subst hv
      have h4 := hpow 1 (by norm_num) (by norm_num)
      norm_num at h4
      refine base4_menu_of_constants
        (c₁ := 341) (L₁ := 5) (c₂ := 337) (L₂ := 5)
        (c₃ := 85) (L₃ := 4) (c₄ := 69) (L₄ := 4)
        (m := p - 4)
        (by norm_num) (by decide) (by norm_num)
        (by decide) (by norm_num) (by decide)
        (by norm_num) (by decide)
        (not_pure_of_bounds (L := 4) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 4) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num)) ?_
      rw [h256, h4]
      ring

/-- **Mixed repair `3·4^p + 2·4^v`, doubled stray bit below scale.** -/
theorem base4_repair_triple_mixedTwo (p v : ℕ)
    (hp : 8 ≤ p) (hvp : v < p) :
    ∃ a b c d, IsBase4 a ∧ IsBase4 b ∧ IsBase4 c ∧
      IsBase4 d ∧
      (∀ j, a ≠ 4 ^ j) ∧ (∀ j, b ≠ 4 ^ j) ∧
      (∀ j, c ≠ 4 ^ j) ∧ (∀ j, d ≠ 4 ^ j) ∧
      a + b + c + d = 3 * 4 ^ p + 2 * 4 ^ v := by
  have h256 : (4 : ℕ) ^ p = 256 * 4 ^ (p - 4) := by
    have h := pow_shift_eq p 4 (by omega)
    norm_num at h
    exact h
  rcases Nat.lt_or_ge v (p - 4) with hlow | hhigh
  · have hvw : (4 : ℕ) ^ v < 4 ^ (p - 4) :=
      Nat.pow_lt_pow_right (by norm_num) hlow
    have h4w : (4 : ℕ) ^ (p - 3) = 4 * 4 ^ (p - 4) := by
      have h := pow_shift_eq (p - 3) 1 (by omega)
      have he : p - 3 - 1 = p - 4 := by omega
      rw [he] at h
      norm_num at h
      exact h
    have h16w :
        (4 : ℕ) ^ (p - 3 + 1) = 16 * 4 ^ (p - 4) := by
      have h := pow_shift_eq (p - 3 + 1) 2 (by omega)
      have he : p - 3 + 1 - 2 = p - 4 := by omega
      rw [he] at h
      norm_num at h
      exact h
    have h64w :
        (4 : ℕ) ^ (p - 1) = 64 * 4 ^ (p - 4) := by
      have h := pow_shift_eq (p - 1) 3 (by omega)
      have he : p - 1 - 3 = p - 4 := by omega
      rw [he] at h
      norm_num at h
      exact h
    have h256w :
        (4 : ℕ) ^ (p - 1 + 1) = 256 * 4 ^ (p - 4) := by
      have he : p - 1 + 1 = p := by omega
      rw [he]
      exact h256
    refine
      ⟨341 * 4 ^ (p - 4), 337 * 4 ^ (p - 4),
        85 * 4 ^ (p - 4) + 4 ^ v,
        5 * 4 ^ (p - 4) + 4 ^ v,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact isBase4_scaledConst (c := 341) (L := 5)
        (p - 4) (by norm_num) (by decide)
    · exact isBase4_scaledConst (c := 337) (L := 5)
        (p - 4) (by norm_num) (by decide)
    · exact isBase4_scaled_add
        (isBase4_of_digits (c := 85) (L := 4)
          (by norm_num) (by decide))
        (isBase4_pow v) hvw
    · exact isBase4_scaled_add
        (isBase4_of_digits (c := 5) (L := 2)
          (by norm_num) (by decide))
        (isBase4_pow v) hvw
    · exact fun j => not_pure_of_scaled
        (not_pure_of_bounds (c := 341) (L := 4)
          (by norm_num) (by norm_num)) j
    · exact fun j => not_pure_of_scaled
        (not_pure_of_bounds (c := 337) (L := 4)
          (by norm_num) (by norm_num)) j
    · have hl :
          (4 : ℕ) ^ (p - 1) <
            85 * 4 ^ (p - 4) + 4 ^ v :=
        calc (4 : ℕ) ^ (p - 1) = 64 * 4 ^ (p - 4) :=
            h64w
          _ < 85 * 4 ^ (p - 4) :=
            Nat.mul_lt_mul_of_pos_right (by norm_num)
              (pow4_pos _)
          _ ≤ 85 * 4 ^ (p - 4) + 4 ^ v :=
            Nat.le_add_right _ _
      have hr :
          85 * 4 ^ (p - 4) + 4 ^ v <
            4 ^ (p - 1 + 1) :=
        calc 85 * 4 ^ (p - 4) + 4 ^ v <
            85 * 4 ^ (p - 4) + 4 ^ (p - 4) :=
              Nat.add_lt_add_left hvw _
          _ = 86 * 4 ^ (p - 4) := by ring
          _ ≤ 256 * 4 ^ (p - 4) :=
            Nat.mul_le_mul_right _ (by norm_num)
          _ = (4 : ℕ) ^ (p - 1 + 1) := h256w.symm
      exact fun j hj =>
        not_pure_of_bounds (L := p - 1) hl hr ⟨j, hj⟩
    · have hl :
          (4 : ℕ) ^ (p - 3) <
            5 * 4 ^ (p - 4) + 4 ^ v :=
        calc (4 : ℕ) ^ (p - 3) = 4 * 4 ^ (p - 4) :=
            h4w
          _ < 5 * 4 ^ (p - 4) :=
            Nat.mul_lt_mul_of_pos_right (by norm_num)
              (pow4_pos _)
          _ ≤ 5 * 4 ^ (p - 4) + 4 ^ v :=
            Nat.le_add_right _ _
      have hr :
          5 * 4 ^ (p - 4) + 4 ^ v <
            4 ^ (p - 3 + 1) :=
        calc 5 * 4 ^ (p - 4) + 4 ^ v <
            5 * 4 ^ (p - 4) + 4 ^ (p - 4) :=
              Nat.add_lt_add_left hvw _
          _ = 6 * 4 ^ (p - 4) := by ring
          _ ≤ 16 * 4 ^ (p - 4) :=
            Nat.mul_le_mul_right _ (by norm_num)
          _ = (4 : ℕ) ^ (p - 3 + 1) := h16w.symm
      exact fun j hj =>
        not_pure_of_bounds (L := p - 3) hl hr ⟨j, hj⟩
    · rw [h256]
      ring
  · have hcase :
        v = p - 4 ∨ v = p - 3 ∨ v = p - 2 ∨
          v = p - 1 := by
      omega
    rcases hcase with hv | hv | hv | hv
    · subst hv
      have h4p :
          (4 : ℕ) ^ p = 65536 * 4 ^ (p - 8) := by
        have h := pow_shift_eq p 8 (by omega)
        norm_num at h
        exact h
      have h4v :
          (4 : ℕ) ^ (p - 4) = 256 * 4 ^ (p - 8) := by
        have h := pow_shift_eq (p - 4) 4 (by omega)
        have he : p - 4 - 4 = p - 8 := by omega
        rw [he] at h
        norm_num at h
        exact h
      refine base4_menu_of_constants
        (c₁ := 65876) (L₁ := 9) (c₂ := 65620)
        (L₂ := 9) (c₃ := 65604) (L₃ := 9)
        (c₄ := 20) (L₄ := 3) (m := p - 8)
        (by norm_num) (by decide) (by norm_num)
        (by decide) (by norm_num) (by decide)
        (by norm_num) (by decide)
        (not_pure_of_bounds (L := 8) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 8) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 8) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 2) (by norm_num)
          (by norm_num)) ?_
      rw [h4p, h4v]
      ring
    · subst hv
      have h4p :
          (4 : ℕ) ^ p = 16384 * 4 ^ (p - 7) := by
        have h := pow_shift_eq p 7 (by omega)
        norm_num at h
        exact h
      have h4v :
          (4 : ℕ) ^ (p - 3) = 256 * 4 ^ (p - 7) := by
        have h := pow_shift_eq (p - 3) 4 (by omega)
        have he : p - 3 - 4 = p - 7 := by omega
        rw [he] at h
        norm_num at h
        exact h
      refine base4_menu_of_constants
        (c₁ := 16724) (L₁ := 8) (c₂ := 16468)
        (L₂ := 8) (c₃ := 16452) (L₃ := 8)
        (c₄ := 20) (L₄ := 3) (m := p - 7)
        (by norm_num) (by decide) (by norm_num)
        (by decide) (by norm_num) (by decide)
        (by norm_num) (by decide)
        (not_pure_of_bounds (L := 7) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 7) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 7) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 2) (by norm_num)
          (by norm_num)) ?_
      rw [h4p, h4v]
      ring
    · subst hv
      have h4p :
          (4 : ℕ) ^ p = 4096 * 4 ^ (p - 6) := by
        have h := pow_shift_eq p 6 (by omega)
        norm_num at h
        exact h
      have h4v :
          (4 : ℕ) ^ (p - 2) = 256 * 4 ^ (p - 6) := by
        have h := pow_shift_eq (p - 2) 4 (by omega)
        have he : p - 2 - 4 = p - 6 := by omega
        rw [he] at h
        norm_num at h
        exact h
      refine base4_menu_of_constants
        (c₁ := 4436) (L₁ := 7) (c₂ := 4180)
        (L₂ := 7) (c₃ := 4164) (L₃ := 7)
        (c₄ := 20) (L₄ := 3) (m := p - 6)
        (by norm_num) (by decide) (by norm_num)
        (by decide) (by norm_num) (by decide)
        (by norm_num) (by decide)
        (not_pure_of_bounds (L := 6) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 6) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 6) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 2) (by norm_num)
          (by norm_num)) ?_
      rw [h4p, h4v]
      ring
    · subst hv
      have h4p :
          (4 : ℕ) ^ p = 1024 * 4 ^ (p - 5) := by
        have h := pow_shift_eq p 5 (by omega)
        norm_num at h
        exact h
      have h4v :
          (4 : ℕ) ^ (p - 1) = 256 * 4 ^ (p - 5) := by
        have h := pow_shift_eq (p - 1) 4 (by omega)
        have he : p - 1 - 4 = p - 5 := by omega
        rw [he] at h
        norm_num at h
        exact h
      refine base4_menu_of_constants
        (c₁ := 1364) (L₁ := 6) (c₂ := 1108)
        (L₂ := 6) (c₃ := 1092) (L₃ := 6)
        (c₄ := 20) (L₄ := 3) (m := p - 5)
        (by norm_num) (by decide) (by norm_num)
        (by decide) (by norm_num) (by decide)
        (by norm_num) (by decide)
        (not_pure_of_bounds (L := 5) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 5) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 5) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 2) (by norm_num)
          (by norm_num)) ?_
      rw [h4p, h4v]
      ring

/-- **Mixed repair `4^u + 2·4^a`, doubled block below the top bit.** -/
theorem base4_repair_double_mixedAbove (u a : ℕ)
    (hu : 8 ≤ u) (hau : a < u) :
    ∃ x y z t, IsBase4 x ∧ IsBase4 y ∧ IsBase4 z ∧
      IsBase4 t ∧
      (∀ j, x ≠ 4 ^ j) ∧ (∀ j, y ≠ 4 ^ j) ∧
      (∀ j, z ≠ 4 ^ j) ∧ (∀ j, t ≠ 4 ^ j) ∧
      x + y + z + t = 4 ^ u + 2 * 4 ^ a := by
  have h256 : (4 : ℕ) ^ u = 256 * 4 ^ (u - 4) := by
    have h := pow_shift_eq u 4 (by omega)
    norm_num at h
    exact h
  rcases Nat.lt_or_ge a (u - 4) with hlow | hhigh
  · have haw : (4 : ℕ) ^ a < 4 ^ (u - 4) :=
      Nat.pow_lt_pow_right (by norm_num) hlow
    have h64w :
        (4 : ℕ) ^ (u - 1) = 64 * 4 ^ (u - 4) := by
      have h := pow_shift_eq (u - 1) 3 (by omega)
      have he : u - 1 - 3 = u - 4 := by omega
      rw [he] at h
      norm_num at h
      exact h
    have h256w :
        (4 : ℕ) ^ (u - 1 + 1) = 256 * 4 ^ (u - 4) := by
      have he : u - 1 + 1 = u := by omega
      rw [he]
      exact h256
    have hbig :
        ∀ c : ℕ, 64 < c → c ≤ 85 →
          (∀ j, c * 4 ^ (u - 4) + 4 ^ a ≠ 4 ^ j) := by
      intro c hc1 hc2
      have hl :
          (4 : ℕ) ^ (u - 1) <
            c * 4 ^ (u - 4) + 4 ^ a :=
        calc (4 : ℕ) ^ (u - 1) = 64 * 4 ^ (u - 4) :=
            h64w
          _ < c * 4 ^ (u - 4) :=
            Nat.mul_lt_mul_of_pos_right hc1
              (pow4_pos _)
          _ ≤ c * 4 ^ (u - 4) + 4 ^ a :=
            Nat.le_add_right _ _
      have hr :
          c * 4 ^ (u - 4) + 4 ^ a <
            4 ^ (u - 1 + 1) :=
        calc c * 4 ^ (u - 4) + 4 ^ a <
            c * 4 ^ (u - 4) + 4 ^ (u - 4) :=
              Nat.add_lt_add_left haw _
          _ = (c + 1) * 4 ^ (u - 4) := by ring
          _ ≤ 256 * 4 ^ (u - 4) :=
            Nat.mul_le_mul_right _ (by omega)
          _ = (4 : ℕ) ^ (u - 1 + 1) := h256w.symm
      exact fun j hj =>
        not_pure_of_bounds (L := u - 1) hl hr ⟨j, hj⟩
    refine
      ⟨84 * 4 ^ (u - 4) + 4 ^ a,
        84 * 4 ^ (u - 4) + 4 ^ a,
        68 * 4 ^ (u - 4), 20 * 4 ^ (u - 4),
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact isBase4_scaled_add
        (isBase4_of_digits (c := 84) (L := 4)
          (by norm_num) (by decide))
        (isBase4_pow a) haw
    · exact isBase4_scaled_add
        (isBase4_of_digits (c := 84) (L := 4)
          (by norm_num) (by decide))
        (isBase4_pow a) haw
    · exact isBase4_scaledConst (c := 68) (L := 4)
        (u - 4) (by norm_num) (by decide)
    · exact isBase4_scaledConst (c := 20) (L := 3)
        (u - 4) (by norm_num) (by decide)
    · exact hbig 84 (by norm_num) (by norm_num)
    · exact hbig 84 (by norm_num) (by norm_num)
    · exact fun j => not_pure_of_scaled
        (not_pure_of_bounds (c := 68) (L := 3)
          (by norm_num) (by norm_num)) j
    · exact fun j => not_pure_of_scaled
        (not_pure_of_bounds (c := 20) (L := 2)
          (by norm_num) (by norm_num)) j
    · rw [h256]
      ring
  · have hcase :
        a = u - 4 ∨ a = u - 3 ∨ a = u - 2 ∨
          a = u - 1 := by
      omega
    rcases hcase with ha | ha | ha | ha
    · subst ha
      refine base4_menu_of_constants
        (c₁ := 85) (L₁ := 4) (c₂ := 85) (L₂ := 4)
        (c₃ := 68) (L₃ := 4) (c₄ := 20) (L₄ := 3)
        (m := u - 4)
        (by norm_num) (by decide) (by norm_num)
        (by decide) (by norm_num) (by decide)
        (by norm_num) (by decide)
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 2) (by norm_num)
          (by norm_num)) ?_
      rw [h256]
      ring
    · subst ha
      have h4u :
          (4 : ℕ) ^ u = 16384 * 4 ^ (u - 7) := by
        have h := pow_shift_eq u 7 (by omega)
        norm_num at h
        exact h
      have h4a :
          (4 : ℕ) ^ (u - 3) = 256 * 4 ^ (u - 7) := by
        have h := pow_shift_eq (u - 3) 4 (by omega)
        have he : u - 3 - 4 = u - 7 := by omega
        rw [he] at h
        norm_num at h
        exact h
      refine base4_menu_of_constants
        (c₁ := 16724) (L₁ := 8) (c₂ := 84)
        (L₂ := 4) (c₃ := 68) (L₃ := 4)
        (c₄ := 20) (L₄ := 3) (m := u - 7)
        (by norm_num) (by decide) (by norm_num)
        (by decide) (by norm_num) (by decide)
        (by norm_num) (by decide)
        (not_pure_of_bounds (L := 7) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 2) (by norm_num)
          (by norm_num)) ?_
      rw [h4u, h4a]
      ring
    · subst ha
      have h4u :
          (4 : ℕ) ^ u = 4096 * 4 ^ (u - 6) := by
        have h := pow_shift_eq u 6 (by omega)
        norm_num at h
        exact h
      have h4a :
          (4 : ℕ) ^ (u - 2) = 256 * 4 ^ (u - 6) := by
        have h := pow_shift_eq (u - 2) 4 (by omega)
        have he : u - 2 - 4 = u - 6 := by omega
        rw [he] at h
        norm_num at h
        exact h
      refine base4_menu_of_constants
        (c₁ := 4180) (L₁ := 7) (c₂ := 340)
        (L₂ := 5) (c₃ := 68) (L₃ := 4)
        (c₄ := 20) (L₄ := 3) (m := u - 6)
        (by norm_num) (by decide) (by norm_num)
        (by decide) (by norm_num) (by decide)
        (by norm_num) (by decide)
        (not_pure_of_bounds (L := 6) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 4) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 2) (by norm_num)
          (by norm_num)) ?_
      rw [h4u, h4a]
      ring
    · subst ha
      have h4u :
          (4 : ℕ) ^ u = 1024 * 4 ^ (u - 5) := by
        have h := pow_shift_eq u 5 (by omega)
        norm_num at h
        exact h
      have h4a :
          (4 : ℕ) ^ (u - 1) = 256 * 4 ^ (u - 5) := by
        have h := pow_shift_eq (u - 1) 4 (by omega)
        have he : u - 1 - 4 = u - 5 := by omega
        rw [he] at h
        norm_num at h
        exact h
      refine base4_menu_of_constants
        (c₁ := 1108) (L₁ := 6) (c₂ := 340)
        (L₂ := 5) (c₃ := 68) (L₃ := 4)
        (c₄ := 20) (L₄ := 3) (m := u - 5)
        (by norm_num) (by decide) (by norm_num)
        (by decide) (by norm_num) (by decide)
        (by norm_num) (by decide)
        (not_pure_of_bounds (L := 5) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 4) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 2) (by norm_num)
          (by norm_num)) ?_
      rw [h4u, h4a]
      ring

/-- **Mixed repair `4^u + 3·4^a`, tripled block below the top bit.** -/
theorem base4_repair_triple_mixedAbove (u a : ℕ)
    (hu : 8 ≤ u) (hau : a < u) :
    ∃ x y z t, IsBase4 x ∧ IsBase4 y ∧ IsBase4 z ∧
      IsBase4 t ∧
      (∀ j, x ≠ 4 ^ j) ∧ (∀ j, y ≠ 4 ^ j) ∧
      (∀ j, z ≠ 4 ^ j) ∧ (∀ j, t ≠ 4 ^ j) ∧
      x + y + z + t = 4 ^ u + 3 * 4 ^ a := by
  have h256 : (4 : ℕ) ^ u = 256 * 4 ^ (u - 4) := by
    have h := pow_shift_eq u 4 (by omega)
    norm_num at h
    exact h
  rcases Nat.lt_or_ge a (u - 4) with hlow | hhigh
  · have haw : (4 : ℕ) ^ a < 4 ^ (u - 4) :=
      Nat.pow_lt_pow_right (by norm_num) hlow
    have h64w :
        (4 : ℕ) ^ (u - 1) = 64 * 4 ^ (u - 4) := by
      have h := pow_shift_eq (u - 1) 3 (by omega)
      have he : u - 1 - 3 = u - 4 := by omega
      rw [he] at h
      norm_num at h
      exact h
    have h256w :
        (4 : ℕ) ^ (u - 1 + 1) = 256 * 4 ^ (u - 4) := by
      have he : u - 1 + 1 = u := by omega
      rw [he]
      exact h256
    have hbig :
        ∀ c : ℕ, 64 < c → c ≤ 85 →
          (∀ j, c * 4 ^ (u - 4) + 4 ^ a ≠ 4 ^ j) := by
      intro c hc1 hc2
      have hl :
          (4 : ℕ) ^ (u - 1) <
            c * 4 ^ (u - 4) + 4 ^ a :=
        calc (4 : ℕ) ^ (u - 1) = 64 * 4 ^ (u - 4) :=
            h64w
          _ < c * 4 ^ (u - 4) :=
            Nat.mul_lt_mul_of_pos_right hc1
              (pow4_pos _)
          _ ≤ c * 4 ^ (u - 4) + 4 ^ a :=
            Nat.le_add_right _ _
      have hr :
          c * 4 ^ (u - 4) + 4 ^ a <
            4 ^ (u - 1 + 1) :=
        calc c * 4 ^ (u - 4) + 4 ^ a <
            c * 4 ^ (u - 4) + 4 ^ (u - 4) :=
              Nat.add_lt_add_left haw _
          _ = (c + 1) * 4 ^ (u - 4) := by ring
          _ ≤ 256 * 4 ^ (u - 4) :=
            Nat.mul_le_mul_right _ (by omega)
          _ = (4 : ℕ) ^ (u - 1 + 1) := h256w.symm
      exact fun j hj =>
        not_pure_of_bounds (L := u - 1) hl hr ⟨j, hj⟩
    refine
      ⟨84 * 4 ^ (u - 4) + 4 ^ a,
        84 * 4 ^ (u - 4) + 4 ^ a,
        68 * 4 ^ (u - 4) + 4 ^ a, 20 * 4 ^ (u - 4),
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact isBase4_scaled_add
        (isBase4_of_digits (c := 84) (L := 4)
          (by norm_num) (by decide))
        (isBase4_pow a) haw
    · exact isBase4_scaled_add
        (isBase4_of_digits (c := 84) (L := 4)
          (by norm_num) (by decide))
        (isBase4_pow a) haw
    · exact isBase4_scaled_add
        (isBase4_of_digits (c := 68) (L := 4)
          (by norm_num) (by decide))
        (isBase4_pow a) haw
    · exact isBase4_scaledConst (c := 20) (L := 3)
        (u - 4) (by norm_num) (by decide)
    · exact hbig 84 (by norm_num) (by norm_num)
    · exact hbig 84 (by norm_num) (by norm_num)
    · exact hbig 68 (by norm_num) (by norm_num)
    · exact fun j => not_pure_of_scaled
        (not_pure_of_bounds (c := 20) (L := 2)
          (by norm_num) (by norm_num)) j
    · rw [h256]
      ring
  · have hcase :
        a = u - 4 ∨ a = u - 3 ∨ a = u - 2 ∨
          a = u - 1 := by
      omega
    rcases hcase with ha | ha | ha | ha
    · subst ha
      refine base4_menu_of_constants
        (c₁ := 85) (L₁ := 4) (c₂ := 85) (L₂ := 4)
        (c₃ := 69) (L₃ := 4) (c₄ := 20) (L₄ := 3)
        (m := u - 4)
        (by norm_num) (by decide) (by norm_num)
        (by decide) (by norm_num) (by decide)
        (by norm_num) (by decide)
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 2) (by norm_num)
          (by norm_num)) ?_
      rw [h256]
      ring
    · subst ha
      have h4u :
          (4 : ℕ) ^ u = 16384 * 4 ^ (u - 7) := by
        have h := pow_shift_eq u 7 (by omega)
        norm_num at h
        exact h
      have h4a :
          (4 : ℕ) ^ (u - 3) = 256 * 4 ^ (u - 7) := by
        have h := pow_shift_eq (u - 3) 4 (by omega)
        have he : u - 3 - 4 = u - 7 := by omega
        rw [he] at h
        norm_num at h
        exact h
      refine base4_menu_of_constants
        (c₁ := 16724) (L₁ := 8) (c₂ := 340)
        (L₂ := 5) (c₃ := 68) (L₃ := 4)
        (c₄ := 20) (L₄ := 3) (m := u - 7)
        (by norm_num) (by decide) (by norm_num)
        (by decide) (by norm_num) (by decide)
        (by norm_num) (by decide)
        (not_pure_of_bounds (L := 7) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 4) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 2) (by norm_num)
          (by norm_num)) ?_
      rw [h4u, h4a]
      ring
    · subst ha
      have h4u :
          (4 : ℕ) ^ u = 4096 * 4 ^ (u - 6) := by
        have h := pow_shift_eq u 6 (by omega)
        norm_num at h
        exact h
      have h4a :
          (4 : ℕ) ^ (u - 2) = 256 * 4 ^ (u - 6) := by
        have h := pow_shift_eq (u - 2) 4 (by omega)
        have he : u - 2 - 4 = u - 6 := by omega
        rw [he] at h
        norm_num at h
        exact h
      refine base4_menu_of_constants
        (c₁ := 4436) (L₁ := 7) (c₂ := 340)
        (L₂ := 5) (c₃ := 68) (L₃ := 4)
        (c₄ := 20) (L₄ := 3) (m := u - 6)
        (by norm_num) (by decide) (by norm_num)
        (by decide) (by norm_num) (by decide)
        (by norm_num) (by decide)
        (not_pure_of_bounds (L := 6) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 4) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 3) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 2) (by norm_num)
          (by norm_num)) ?_
      rw [h4u, h4a]
      ring
    · subst ha
      have h4u :
          (4 : ℕ) ^ u = 1024 * 4 ^ (u - 5) := by
        have h := pow_shift_eq u 5 (by omega)
        norm_num at h
        exact h
      have h4a :
          (4 : ℕ) ^ (u - 1) = 256 * 4 ^ (u - 5) := by
        have h := pow_shift_eq (u - 1) 4 (by omega)
        have he : u - 1 - 4 = u - 5 := by omega
        rw [he] at h
        norm_num at h
        exact h
      refine base4_menu_of_constants
        (c₁ := 1108) (L₁ := 6) (c₂ := 340)
        (L₂ := 5) (c₃ := 324) (L₃ := 5)
        (c₄ := 20) (L₄ := 3) (m := u - 5)
        (by norm_num) (by decide) (by norm_num)
        (by decide) (by norm_num) (by decide)
        (by norm_num) (by decide)
        (not_pure_of_bounds (L := 5) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 4) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 4) (by norm_num)
          (by norm_num))
        (not_pure_of_bounds (L := 2) (by norm_num)
          (by norm_num)) ?_
      rw [h4u, h4a]
      ring

end Erdos881Base4
