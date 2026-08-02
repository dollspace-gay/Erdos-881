/-
# The base-4 carry repair (Erdős 881, k = 3 positive mechanism)

`CantorCarryRepair` one order up.  Deleting the pure powers `{4^k}`
from the base-4 digit-{0,1} set destroys the diagonal targets `3·4^k`
at order 3 completely — the diagonal is rigid
(`base4_triple_of_three_mul`), so its unique representation
`(4^k, 4^k, 4^k)` dies with the deletion.  Order 4 repairs every
destroyed scale through the base-4 carry `1+1+1+1 = 10₄`, which no
order-3 sum of digit-{0,1} numbers can produce:

* `4^k   = (84 + 84 + 68 + 20)·4^(k-4)`  (256 = 4⁴),
* `2·4^k = (272 + 80 + 80 + 80)·4^(k-4)` (512),
* `3·4^k = (341 + 337 + 85 + 5)·4^(k-4)` (768),

with every part a base-4 digit-{0,1} number that is not a pure power.
The 2026-08-02 laboratory verified the full deletion survives at
order 4 with threshold 54; these menus are the creative core of that
theorem, and the general-target sieve is the remaining assembly.
-/

import Erdos881.Base4Instance

namespace Erdos881Base4

/-- Powers are base-4 digit numbers. -/
lemma isBase4_pow (k : ℕ) : IsBase4 (4 ^ k) := by
  intro i
  rcases Nat.lt_trichotomy i k with h | h | h
  · have h3 : 4 ^ k / 4 ^ i = 4 ^ (k - i) := by
      rw [Nat.pow_div (Nat.le_of_lt h) (by norm_num)]
    rw [h3]
    have h4 : k - i = (k - i - 1) + 1 := by omega
    rw [h4, pow_succ]
    simp
  · subst h
    simp [Nat.div_self (pow4_pos i)]
  · have h3 : 4 ^ k < 4 ^ i :=
      Nat.pow_lt_pow_right (by norm_num) h
    rw [Nat.div_eq_of_lt h3]
    simp

/-- Digit-shift: multiplying by `4^m` shifts digits up. -/
lemma isBase4_shift {n : ℕ} (m : ℕ) (hn : IsBase4 n) :
    IsBase4 (4 ^ m * n) := by
  intro i
  rcases Nat.lt_or_ge i m with h | h
  · have h2 : 4 ^ m * n / 4 ^ i = 4 ^ (m - i) * n := by
      have hsplit : (4 : ℕ) ^ m = 4 ^ i * 4 ^ (m - i) := by
        rw [← pow_add]; congr 1; omega
      rw [hsplit, Nat.mul_assoc,
        Nat.mul_div_cancel_left _ (pow4_pos i)]
    rw [h2]
    have h4 : m - i = (m - i - 1) + 1 := by omega
    rw [h4, pow_succ]
    have hres :
        4 ^ (m - i - 1) * 4 * n =
          4 * (4 ^ (m - i - 1) * n) := by
      ring
    rw [hres]
    simp [Nat.mul_mod_right]
  · have h2 : (4 : ℕ) ^ i = 4 ^ m * 4 ^ (i - m) := by
      rw [← pow_add]; congr 1; omega
    rw [h2, ← Nat.div_div_eq_div_mul,
      Nat.mul_div_cancel_left _ (pow4_pos m)]
    exact hn (i - m)

/-- A bounded digit check suffices for `IsBase4`. -/
lemma isBase4_of_digits {c L : ℕ} (hc : c < 4 ^ L)
    (h : ∀ i < L, c / 4 ^ i % 4 ≤ 1) : IsBase4 c := by
  intro i
  rcases Nat.lt_or_ge i L with hiL | hLi
  · exact h i hiL
  · have hlt : c < 4 ^ i :=
      lt_of_lt_of_le hc
        (Nat.pow_le_pow_right (by norm_num) hLi)
    rw [Nat.div_eq_of_lt hlt]
    simp

/-- Strictly between consecutive powers means not a power. -/
lemma not_pure_of_bounds {c L : ℕ}
    (h1 : 4 ^ L < c) (h2 : c < 4 ^ (L + 1)) :
    ¬∃ t, c = 4 ^ t := by
  rintro ⟨t, rfl⟩
  rcases Nat.lt_or_ge t (L + 1) with hlt | hge
  · have : (4 : ℕ) ^ t ≤ 4 ^ L :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have : (4 : ℕ) ^ (L + 1) ≤ 4 ^ t :=
      Nat.pow_le_pow_right (by norm_num) hge
    omega

/-- Scaled non-purity. -/
lemma not_pure_of_scaled {c m : ℕ}
    (hc : ¬∃ t, c = 4 ^ t) (j : ℕ) :
    c * 4 ^ m ≠ 4 ^ j := by
  intro h
  rcases Nat.lt_or_ge j m with hjm | hmj
  · have hlt : (4 : ℕ) ^ j < 4 ^ m :=
      Nat.pow_lt_pow_right (by norm_num) hjm
    rcases Nat.eq_zero_or_pos c with rfl | hcpos
    · have := pow4_pos j
      omega
    · have hle : 4 ^ m ≤ c * 4 ^ m :=
        Nat.le_mul_of_pos_left _ hcpos
      omega
  · have hsplit : (4 : ℕ) ^ j = 4 ^ (j - m) * 4 ^ m := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit] at h
    have hcancel : c = 4 ^ (j - m) :=
      Nat.eq_of_mul_eq_mul_right (pow4_pos m) h
    exact hc ⟨j - m, hcancel⟩

/- The menu constants: `84 = 1110₄`, `68 = 1010₄`, `20 = 110₄`,
`272 = 10100₄`, `80 = 1100₄`, `341 = 11111₄`, `337 = 11101₄`,
`85 = 1111₄`, `5 = 11₄`. -/

lemma isBase4_84 : IsBase4 84 :=
  isBase4_of_digits (L := 4) (by norm_num) (by decide)

lemma isBase4_68 : IsBase4 68 :=
  isBase4_of_digits (L := 4) (by norm_num) (by decide)

lemma isBase4_20 : IsBase4 20 :=
  isBase4_of_digits (L := 3) (by norm_num) (by decide)

lemma isBase4_272 : IsBase4 272 :=
  isBase4_of_digits (L := 5) (by norm_num) (by decide)

lemma isBase4_80 : IsBase4 80 :=
  isBase4_of_digits (L := 4) (by norm_num) (by decide)

lemma isBase4_341 : IsBase4 341 :=
  isBase4_of_digits (L := 5) (by norm_num) (by decide)

lemma isBase4_337 : IsBase4 337 :=
  isBase4_of_digits (L := 5) (by norm_num) (by decide)

lemma isBase4_85 : IsBase4 85 :=
  isBase4_of_digits (L := 4) (by norm_num) (by decide)

lemma isBase4_5 : IsBase4 5 :=
  isBase4_of_digits (L := 2) (by norm_num) (by decide)

lemma not_pure_84 : ¬∃ t, (84 : ℕ) = 4 ^ t :=
  not_pure_of_bounds (L := 3) (by norm_num) (by norm_num)

lemma not_pure_68 : ¬∃ t, (68 : ℕ) = 4 ^ t :=
  not_pure_of_bounds (L := 3) (by norm_num) (by norm_num)

lemma not_pure_20 : ¬∃ t, (20 : ℕ) = 4 ^ t :=
  not_pure_of_bounds (L := 2) (by norm_num) (by norm_num)

lemma not_pure_272 : ¬∃ t, (272 : ℕ) = 4 ^ t :=
  not_pure_of_bounds (L := 4) (by norm_num) (by norm_num)

lemma not_pure_80 : ¬∃ t, (80 : ℕ) = 4 ^ t :=
  not_pure_of_bounds (L := 3) (by norm_num) (by norm_num)

lemma not_pure_341 : ¬∃ t, (341 : ℕ) = 4 ^ t :=
  not_pure_of_bounds (L := 4) (by norm_num) (by norm_num)

lemma not_pure_337 : ¬∃ t, (337 : ℕ) = 4 ^ t :=
  not_pure_of_bounds (L := 4) (by norm_num) (by norm_num)

lemma not_pure_85 : ¬∃ t, (85 : ℕ) = 4 ^ t :=
  not_pure_of_bounds (L := 3) (by norm_num) (by norm_num)

lemma not_pure_5 : ¬∃ t, (5 : ℕ) = 4 ^ t :=
  not_pure_of_bounds (L := 1) (by norm_num) (by norm_num)

/-- **The carry menu for `4^k`** (`k ≥ 4`):
`84 + 84 + 68 + 20 = 256`, all parts digit-{0,1}, none a power.
The four 1-bits in the `4¹` column carry: `1+1+1+1 = 10₄`. -/
theorem base4_carry_repair (k : ℕ) (hk : 4 ≤ k) :
    ∃ w x y z, IsBase4 w ∧ IsBase4 x ∧ IsBase4 y ∧
      IsBase4 z ∧
      (∀ j, w ≠ 4 ^ j) ∧ (∀ j, x ≠ 4 ^ j) ∧
      (∀ j, y ≠ 4 ^ j) ∧ (∀ j, z ≠ 4 ^ j) ∧
      w + x + y + z = 4 ^ k := by
  refine
    ⟨84 * 4 ^ (k - 4), 84 * 4 ^ (k - 4),
      68 * 4 ^ (k - 4), 20 * 4 ^ (k - 4),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := isBase4_shift (k - 4) isBase4_84
    rwa [Nat.mul_comm] at this
  · have := isBase4_shift (k - 4) isBase4_84
    rwa [Nat.mul_comm] at this
  · have := isBase4_shift (k - 4) isBase4_68
    rwa [Nat.mul_comm] at this
  · have := isBase4_shift (k - 4) isBase4_20
    rwa [Nat.mul_comm] at this
  · exact not_pure_of_scaled not_pure_84
  · exact not_pure_of_scaled not_pure_84
  · exact not_pure_of_scaled not_pure_68
  · exact not_pure_of_scaled not_pure_20
  · have h1 : 4 ^ (k - 4 + 4) = 4 ^ (k - 4) * 4 ^ 4 :=
      pow_add 4 (k - 4) 4
    have h2 : k - 4 + 4 = k := by omega
    rw [h2] at h1
    have h3 : (4 : ℕ) ^ 4 = 256 := by norm_num
    rw [h1, h3]
    ring

/-- **The carry menu for `2·4^k`** (`k ≥ 4`):
`272 + 80 + 80 + 80 = 512`, all parts digit-{0,1}, none a power. -/
theorem base4_carry_repair_double (k : ℕ) (hk : 4 ≤ k) :
    ∃ w x y z, IsBase4 w ∧ IsBase4 x ∧ IsBase4 y ∧
      IsBase4 z ∧
      (∀ j, w ≠ 4 ^ j) ∧ (∀ j, x ≠ 4 ^ j) ∧
      (∀ j, y ≠ 4 ^ j) ∧ (∀ j, z ≠ 4 ^ j) ∧
      w + x + y + z = 2 * 4 ^ k := by
  refine
    ⟨272 * 4 ^ (k - 4), 80 * 4 ^ (k - 4),
      80 * 4 ^ (k - 4), 80 * 4 ^ (k - 4),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := isBase4_shift (k - 4) isBase4_272
    rwa [Nat.mul_comm] at this
  · have := isBase4_shift (k - 4) isBase4_80
    rwa [Nat.mul_comm] at this
  · have := isBase4_shift (k - 4) isBase4_80
    rwa [Nat.mul_comm] at this
  · have := isBase4_shift (k - 4) isBase4_80
    rwa [Nat.mul_comm] at this
  · exact not_pure_of_scaled not_pure_272
  · exact not_pure_of_scaled not_pure_80
  · exact not_pure_of_scaled not_pure_80
  · exact not_pure_of_scaled not_pure_80
  · have h1 : 4 ^ (k - 4 + 4) = 4 ^ (k - 4) * 4 ^ 4 :=
      pow_add 4 (k - 4) 4
    have h2 : k - 4 + 4 = k := by omega
    rw [h2] at h1
    have h3 : (4 : ℕ) ^ 4 = 256 := by norm_num
    have h4 : 2 * 4 ^ k = 512 * 4 ^ (k - 4) := by
      rw [h1, h3]
      ring
    rw [h4]
    ring

/-- **The carry menu for the diagonal casualties `3·4^k`** (`k ≥ 4`):
`341 + 337 + 85 + 5 = 768`, all parts digit-{0,1}, none a power. -/
theorem base4_carry_repair_triple (k : ℕ) (hk : 4 ≤ k) :
    ∃ w x y z, IsBase4 w ∧ IsBase4 x ∧ IsBase4 y ∧
      IsBase4 z ∧
      (∀ j, w ≠ 4 ^ j) ∧ (∀ j, x ≠ 4 ^ j) ∧
      (∀ j, y ≠ 4 ^ j) ∧ (∀ j, z ≠ 4 ^ j) ∧
      w + x + y + z = 3 * 4 ^ k := by
  refine
    ⟨341 * 4 ^ (k - 4), 337 * 4 ^ (k - 4),
      85 * 4 ^ (k - 4), 5 * 4 ^ (k - 4),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := isBase4_shift (k - 4) isBase4_341
    rwa [Nat.mul_comm] at this
  · have := isBase4_shift (k - 4) isBase4_337
    rwa [Nat.mul_comm] at this
  · have := isBase4_shift (k - 4) isBase4_85
    rwa [Nat.mul_comm] at this
  · have := isBase4_shift (k - 4) isBase4_5
    rwa [Nat.mul_comm] at this
  · exact not_pure_of_scaled not_pure_341
  · exact not_pure_of_scaled not_pure_337
  · exact not_pure_of_scaled not_pure_85
  · exact not_pure_of_scaled not_pure_5
  · have h1 : 4 ^ (k - 4 + 4) = 4 ^ (k - 4) * 4 ^ 4 :=
      pow_add 4 (k - 4) 4
    have h2 : k - 4 + 4 = k := by omega
    rw [h2] at h1
    have h3 : (4 : ℕ) ^ 4 = 256 := by norm_num
    have h4 : 3 * 4 ^ k = 768 * 4 ^ (k - 4) := by
      rw [h1, h3]
      ring
    rw [h4]
    ring

/-- **The demonstrator.**  At every scale `k ≥ 4` the powers deletion
kills the diagonal `3·4^k` at order 3 completely — every order-3
representation uses a pure power — while order 4 repairs it with four
digit-{0,1} parts, none a power.  The deletion that destroys order 3
is invisible to order 4: the exact conclusion pattern of Erdős 881
for `k = 3`, on the verified hard-case instance. -/
theorem base4_demonstrator (k : ℕ) (hk : 4 ≤ k) :
    (∀ x y z, IsBase4 x → IsBase4 y → IsBase4 z →
      x + y + z = 3 * 4 ^ k → ∃ j, x = 4 ^ j) ∧
    ∃ w x y z, IsBase4 w ∧ IsBase4 x ∧ IsBase4 y ∧
      IsBase4 z ∧
      (∀ j, w ≠ 4 ^ j) ∧ (∀ j, x ≠ 4 ^ j) ∧
      (∀ j, y ≠ 4 ^ j) ∧ (∀ j, z ≠ 4 ^ j) ∧
      w + x + y + z = 3 * 4 ^ k := by
  constructor
  · intro x y z hx hy hz hsum
    obtain ⟨hxb, _hyb, _hzb⟩ :=
      base4_triple_of_three_mul (4 ^ k)
        (isBase4_pow k) x y z hx hy hz hsum
    exact ⟨k, hxb⟩
  · exact base4_carry_repair_triple k hk

end Erdos881Base4
