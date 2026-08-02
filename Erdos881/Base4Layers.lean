/-
# Base-4 digit layers and bit surgery

Infrastructure for the master classifier of the base-4 sieve: the
three digit layers `layer t n` (a 1-bit at every position whose digit
is at least `t`, so `layer 1 n + layer 2 n + layer 3 n = n`), the
digit-clearing subtraction `x - 4^p`, digit extraction for nonzero
numbers, and the two-digit purity tests.  Ported from the base-3
machinery of `CantorCarryRepair` one order up.
-/

import Erdos881.Base4Sieve

namespace Erdos881Base4

/-- Digits of a pure power. -/
lemma pow_digit4 (j i : ℕ) :
    4 ^ j / 4 ^ i % 4 = if i = j then 1 else 0 := by
  rcases Nat.lt_trichotomy i j with h | h | h
  · rw [if_neg (by omega)]
    have h3 : 4 ^ j / 4 ^ i = 4 ^ (j - i) := by
      rw [Nat.pow_div (Nat.le_of_lt h) (by norm_num)]
    rw [h3]
    have h4 : j - i = (j - i - 1) + 1 := by omega
    rw [h4, pow_succ]
    simp
  · subst h
    rw [if_pos rfl, Nat.div_self (pow4_pos i)]
  · rw [if_neg (by omega),
      Nat.div_eq_of_lt
        (Nat.pow_lt_pow_right (by norm_num) h)]

/-- A set digit bounds the number from below. -/
lemma pow_le_of_digit4 {x p : ℕ}
    (hd : x / 4 ^ p % 4 = 1) : 4 ^ p ≤ x := by
  by_contra hlt
  rw [Nat.div_eq_of_lt (by omega)] at hd
  norm_num at hd

/-- A number with digit 1 at two distinct positions is not a pure
power. -/
lemma not_pure_of_two_digits {x p q : ℕ}
    (hd1 : x / 4 ^ p % 4 = 1) (hd2 : x / 4 ^ q % 4 = 1)
    (hpq : p ≠ q) : ∀ j, x ≠ 4 ^ j := by
  intro j hx
  subst hx
  have h1 := pow_digit4 j p
  have h2 := pow_digit4 j q
  by_cases hpj : p = j
  · subst hpj
    rw [if_neg (by omega)] at h2
    omega
  · rw [if_neg hpj] at h1
    omega

/-- Clearing a set digit: digits of `x - 4^p` when `x` is base-4 with
digit 1 at `p`. -/
lemma sub_pow_digit4 {x p : ℕ} (hx : IsBase4 x)
    (hd : x / 4 ^ p % 4 = 1) :
    ∀ i, (x - 4 ^ p) / 4 ^ i % 4 =
      if i = p then 0 else x / 4 ^ i % 4 := by
  induction p generalizing x with
  | zero =>
    intro i
    have h1 : x % 4 = 1 := by simpa using hd
    rcases i with _ | i
    · rw [if_pos rfl]
      simp only [pow_zero, Nat.div_one]
      omega
    · rw [if_neg (by omega)]
      have hx1 : x - 4 ^ 0 = 4 * (x / 4) := by
        have := Nat.div_add_mod x 4
        simp only [pow_zero]
        omega
      rw [hx1]
      have hstep :
          4 * (x / 4) / 4 ^ (i + 1) = x / 4 / 4 ^ i := by
        rw [pow_succ, Nat.mul_comm (4 ^ i) 4,
          ← Nat.div_div_eq_div_mul,
          Nat.mul_div_cancel_left _
            (by norm_num : (0 : ℕ) < 4)]
      rw [hstep]
      have hnd : x / 4 ^ (i + 1) = x / 4 / 4 ^ i := by
        rw [pow_succ, Nat.mul_comm (4 ^ i) 4,
          ← Nat.div_div_eq_div_mul]
      rw [hnd]
  | succ p ihp =>
    intro i
    have hq : IsBase4 (x / 4) := by
      intro k
      have hnd : x / 4 / 4 ^ k = x / 4 ^ (k + 1) := by
        rw [pow_succ, Nat.mul_comm (4 ^ k) 4,
          ← Nat.div_div_eq_div_mul]
      rw [hnd]
      exact hx (k + 1)
    have hdq : x / 4 / 4 ^ p % 4 = 1 := by
      have hnd : x / 4 / 4 ^ p = x / 4 ^ (p + 1) := by
        rw [pow_succ, Nat.mul_comm (4 ^ p) 4,
          ← Nat.div_div_eq_div_mul]
      rw [hnd]
      exact hd
    have hge : 4 ^ p ≤ x / 4 := pow_le_of_digit4 hdq
    have hsub :
        x - 4 ^ (p + 1) =
          4 * (x / 4 - 4 ^ p) + x % 4 := by
      have h2 := Nat.div_add_mod x 4
      have h3 : 4 ^ (p + 1) = 4 * 4 ^ p := by
        rw [pow_succ]
        ring
      omega
    rw [hsub]
    rcases i with _ | i
    · rw [if_neg (by omega)]
      simp only [pow_zero, Nat.div_one]
      omega
    · have h40 :
          (4 * (x / 4 - 4 ^ p) + x % 4) / 4 =
            x / 4 - 4 ^ p := by
        omega
      have hstep :
          (4 * (x / 4 - 4 ^ p) + x % 4) / 4 ^ (i + 1) =
            (x / 4 - 4 ^ p) / 4 ^ i := by
        rw [pow_succ, Nat.mul_comm (4 ^ i) 4,
          ← Nat.div_div_eq_div_mul, h40]
      rw [hstep, ihp hq hdq i]
      have hnd : x / 4 / 4 ^ i = x / 4 ^ (i + 1) := by
        rw [pow_succ, Nat.mul_comm (4 ^ i) 4,
          ← Nat.div_div_eq_div_mul]
      by_cases hip : i = p
      · rw [if_pos hip, if_pos (by omega)]
      · rw [if_neg hip, if_neg (by omega), hnd]

/-- Clearing a set digit keeps the number base-4. -/
lemma isBase4_sub_bit {x p : ℕ} (hx : IsBase4 x)
    (hd : x / 4 ^ p % 4 = 1) :
    IsBase4 (x - 4 ^ p) := by
  intro i
  rw [sub_pow_digit4 hx hd i]
  by_cases hip : i = p
  · rw [if_pos hip]
    omega
  · rw [if_neg hip]
    exact hx i

/-- Every nonzero base-4 number has a digit equal to 1 somewhere. -/
lemma exists_digit_one4 :
    ∀ {m : ℕ}, IsBase4 m → m ≠ 0 →
      ∃ v, m / 4 ^ v % 4 = 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm h0
    have h3 : m % 4 ≤ 1 := by simpa using hm 0
    rcases Nat.eq_zero_or_pos (m % 4) with hz | hpz
    · have hq0 : m / 4 ≠ 0 := by
        intro hq
        have := Nat.div_add_mod m 4
        omega
      have hqc : IsBase4 (m / 4) := by
        intro k
        have hnd :
            m / 4 / 4 ^ k = m / 4 ^ (k + 1) := by
          rw [pow_succ, Nat.mul_comm (4 ^ k) 4,
            ← Nat.div_div_eq_div_mul]
        rw [hnd]
        exact hm (k + 1)
      have hlt : m / 4 < m :=
        Nat.div_lt_self (by omega) (by norm_num)
      obtain ⟨v, hv⟩ := ih (m / 4) hlt hqc hq0
      refine ⟨v + 1, ?_⟩
      have hnd : m / 4 ^ (v + 1) = m / 4 / 4 ^ v := by
        rw [pow_succ, Nat.mul_comm (4 ^ v) 4,
          ← Nat.div_div_eq_div_mul]
      rw [hnd]
      exact hv
    · refine ⟨0, ?_⟩
      simp only [pow_zero, Nat.div_one]
      omega

/-- A nonzero base-4 non-power carries two distinct set digits. -/
lemma two_digits_of_nonpure {x : ℕ} (hx : IsBase4 x)
    (h0 : x ≠ 0) (hnp : ∀ j, x ≠ 4 ^ j) :
    ∃ p q, p ≠ q ∧
      x / 4 ^ p % 4 = 1 ∧ x / 4 ^ q % 4 = 1 := by
  obtain ⟨p, hp⟩ := exists_digit_one4 hx h0
  have hxs : IsBase4 (x - 4 ^ p) := isBase4_sub_bit hx hp
  have hge : 4 ^ p ≤ x := pow_le_of_digit4 hp
  have hs0 : x - 4 ^ p ≠ 0 := by
    intro hz
    exact hnp p (by omega)
  obtain ⟨q, hq⟩ := exists_digit_one4 hxs hs0
  have hqp : q ≠ p := by
    intro hqp
    rw [hqp, sub_pow_digit4 hx hp p, if_pos rfl] at hq
    omega
  have hxq : x / 4 ^ q % 4 = 1 := by
    have h := sub_pow_digit4 hx hp q
    rw [if_neg hqp] at h
    omega
  exact ⟨p, q, Ne.symm hqp, hp, hxq⟩

/-- The digit-threshold layer: a 1-bit at every position whose base-4
digit is at least `t`. -/
def layer (t n : ℕ) : ℕ :=
  if n = 0 then 0
  else 4 * layer t (n / 4) +
    (if t ≤ n % 4 then 1 else 0)
termination_by n
decreasing_by
  exact Nat.div_lt_self (by omega) (by norm_num)

lemma layer_zero (t : ℕ) : layer t 0 = 0 := by
  rw [layer]
  simp

lemma layer_pos_def (t : ℕ) {n : ℕ} (hn : n ≠ 0) :
    layer t n =
      4 * layer t (n / 4) +
        (if t ≤ n % 4 then 1 else 0) := by
  rw [layer]
  simp [hn]

/-- The three layers reassemble the number. -/
lemma layer_sum (n : ℕ) :
    layer 1 n + layer 2 n + layer 3 n = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [layer_zero]
    have hlt : n / 4 < n :=
      Nat.div_lt_self (by omega) (by norm_num)
    have hs := ih (n / 4) hlt
    have hmod : n % 4 < 4 := Nat.mod_lt n (by norm_num)
    have hdm := Nat.div_add_mod n 4
    rw [layer_pos_def 1 (by omega),
      layer_pos_def 2 (by omega),
      layer_pos_def 3 (by omega)]
    split_ifs <;> omega

/-- Layers are base-4 numbers. -/
lemma layer_isBase4 (t n : ℕ) : IsBase4 (layer t n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [layer_zero]
      exact isBase4_zero
    have hlt : n / 4 < n :=
      Nat.div_lt_self (by omega) (by norm_num)
    rw [layer_pos_def t (by omega)]
    exact isBase4_scale_add (ih (n / 4) hlt)
      (by split_ifs <;> omega)

/-- Layer digits read the threshold test off the original digits. -/
lemma layer_digit (t : ℕ) (ht : 1 ≤ t) :
    ∀ (i n : ℕ),
      layer t n / 4 ^ i % 4 =
        if t ≤ n / 4 ^ i % 4 then 1 else 0 := by
  intro i
  induction i with
  | zero =>
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [layer_zero]
      simp only [pow_zero, Nat.div_one,
        Nat.zero_div, Nat.zero_mod]
      rw [if_neg (by omega)]
    · rw [layer_pos_def t (by omega)]
      simp only [pow_zero, Nat.div_one]
      rw [Nat.mul_add_mod]
      split_ifs <;> omega
  | succ i ihi =>
    intro n
    have hstep :
        ∀ c : ℕ, c / 4 ^ (i + 1) = c / 4 / 4 ^ i := by
      intro c
      rw [pow_succ, Nat.mul_comm (4 ^ i) 4,
        ← Nat.div_div_eq_div_mul]
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [layer_zero]
      simp only [Nat.zero_div, Nat.zero_mod]
      rw [if_neg (by omega)]
    · have hquot : layer t n / 4 = layer t (n / 4) := by
        rw [layer_pos_def t (by omega),
          Nat.mul_add_div (by norm_num)]
        split_ifs <;> omega
      rw [hstep (layer t n), hquot, ihi (n / 4),
        hstep n]

/-- A base-4 number whose digits all vanish is zero. -/
lemma eq_zero_of_digits4 {x : ℕ}
    (h : ∀ i, x / 4 ^ i % 4 = 0) : x = 0 := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hpos
    · rfl
    have h0 : x % 4 = 0 := by simpa using h 0
    have hq : ∀ i, x / 4 / 4 ^ i % 4 = 0 := by
      intro i
      have hnd : x / 4 / 4 ^ i = x / 4 ^ (i + 1) := by
        rw [pow_succ, Nat.mul_comm (4 ^ i) 4,
          ← Nat.div_div_eq_div_mul]
      rw [hnd]
      exact h (i + 1)
    have hlt : x / 4 < x :=
      Nat.div_lt_self (by omega) (by norm_num)
    have := ih (x / 4) hlt hq
    omega

/-- If the second layer vanishes, the number is base-4. -/
lemma isBase4_of_layer2_zero {n : ℕ}
    (h : layer 2 n = 0) : IsBase4 n := by
  intro i
  have hd := layer_digit 2 (by norm_num) i n
  rw [h] at hd
  simp only [Nat.zero_div, Nat.zero_mod] at hd
  by_cases hle : 2 ≤ n / 4 ^ i % 4
  · rw [if_pos hle] at hd
    omega
  · omega

/-- Adding a small tail below a pure power stays base-4. -/
lemma isBase4_pow_add {q x : ℕ} (hx : IsBase4 x)
    (hlt : x < 4 ^ q) : IsBase4 (4 ^ q + x) := by
  have h := isBase4_scaled_add (y := 1) (m := q)
    (isBase4_of_digits (c := 1) (L := 1)
      (by norm_num) (by decide)) hx hlt
  rwa [one_mul] at h

/-- A pure power with a positive small tail is not pure. -/
lemma not_pure_pow_add {q x : ℕ} (hx0 : 0 < x)
    (hlt : x < 4 ^ q) :
    ∀ j, 4 ^ q + x ≠ 4 ^ j := by
  intro j hj
  have hl : (4 : ℕ) ^ q < 4 ^ q + x := by omega
  have hr : (4 : ℕ) ^ q + x < 4 ^ (q + 1) :=
    calc (4 : ℕ) ^ q + x < 4 ^ q + 4 ^ q := by omega
      _ = 2 * 4 ^ q := by ring
      _ ≤ 4 * 4 ^ q :=
        Nat.mul_le_mul_right _ (by norm_num)
      _ = 4 ^ (q + 1) := by
        rw [pow_succ]
        ring
  exact not_pure_of_bounds (L := q) hl hr ⟨j, hj⟩

/-- **Mixed repair `3·4^a + 2·4^b`, doubled stray above the trey.** -/
theorem base4_repair_tripleTwo_above (a b : ℕ)
    (hb : 8 ≤ b) (hab : a < b) :
    ∃ x y z t, IsBase4 x ∧ IsBase4 y ∧ IsBase4 z ∧
      IsBase4 t ∧
      (∀ j, x ≠ 4 ^ j) ∧ (∀ j, y ≠ 4 ^ j) ∧
      (∀ j, z ≠ 4 ^ j) ∧ (∀ j, t ≠ 4 ^ j) ∧
      x + y + z + t = 3 * 4 ^ a + 2 * 4 ^ b := by
  rcases Nat.lt_or_ge a 4 with halow | hahigh
  · -- small trey: expand the doubled block, attach the three
    -- trey bits below its windows
    have h256 : (4 : ℕ) ^ b = 256 * 4 ^ (b - 4) := by
      have h := pow_shift_eq b 4 (by omega)
      norm_num at h
      exact h
    have haw : (4 : ℕ) ^ a < 4 ^ (b - 4) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h64w :
        (4 : ℕ) ^ (b - 1) = 64 * 4 ^ (b - 4) := by
      have h := pow_shift_eq (b - 1) 3 (by omega)
      have he : b - 1 - 3 = b - 4 := by omega
      rw [he] at h
      norm_num at h
      exact h
    have h256w :
        (4 : ℕ) ^ (b - 1 + 1) = 256 * 4 ^ (b - 4) := by
      have he : b - 1 + 1 = b := by omega
      rw [he]
      exact h256
    have h1024w :
        (4 : ℕ) ^ (b + 1) = 1024 * 4 ^ (b - 4) := by
      have h := pow_shift_eq (b + 1) 5 (by omega)
      have he : b + 1 - 5 = b - 4 := by omega
      rw [he] at h
      norm_num at h
      exact h
    refine
      ⟨272 * 4 ^ (b - 4) + 4 ^ a,
        80 * 4 ^ (b - 4) + 4 ^ a,
        80 * 4 ^ (b - 4) + 4 ^ a, 80 * 4 ^ (b - 4),
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact isBase4_scaled_add
        (isBase4_of_digits (c := 272) (L := 5)
          (by norm_num) (by decide))
        (isBase4_pow a) haw
    · exact isBase4_scaled_add
        (isBase4_of_digits (c := 80) (L := 4)
          (by norm_num) (by decide))
        (isBase4_pow a) haw
    · exact isBase4_scaled_add
        (isBase4_of_digits (c := 80) (L := 4)
          (by norm_num) (by decide))
        (isBase4_pow a) haw
    · exact isBase4_scaledConst (c := 80) (L := 4)
        (b - 4) (by norm_num) (by decide)
    · have hl :
          (4 : ℕ) ^ b < 272 * 4 ^ (b - 4) + 4 ^ a :=
        calc (4 : ℕ) ^ b = 256 * 4 ^ (b - 4) := h256
          _ < 272 * 4 ^ (b - 4) :=
            Nat.mul_lt_mul_of_pos_right (by norm_num)
              (pow4_pos _)
          _ ≤ 272 * 4 ^ (b - 4) + 4 ^ a :=
            Nat.le_add_right _ _
      have hr :
          272 * 4 ^ (b - 4) + 4 ^ a < 4 ^ (b + 1) :=
        calc 272 * 4 ^ (b - 4) + 4 ^ a <
            272 * 4 ^ (b - 4) + 4 ^ (b - 4) :=
              Nat.add_lt_add_left haw _
          _ = 273 * 4 ^ (b - 4) := by ring
          _ ≤ 1024 * 4 ^ (b - 4) :=
            Nat.mul_le_mul_right _ (by norm_num)
          _ = (4 : ℕ) ^ (b + 1) := h1024w.symm
      exact fun j hj =>
        not_pure_of_bounds (L := b) hl hr ⟨j, hj⟩
    · have hl :
          (4 : ℕ) ^ (b - 1) <
            80 * 4 ^ (b - 4) + 4 ^ a :=
        calc (4 : ℕ) ^ (b - 1) = 64 * 4 ^ (b - 4) :=
            h64w
          _ < 80 * 4 ^ (b - 4) :=
            Nat.mul_lt_mul_of_pos_right (by norm_num)
              (pow4_pos _)
          _ ≤ 80 * 4 ^ (b - 4) + 4 ^ a :=
            Nat.le_add_right _ _
      have hr :
          80 * 4 ^ (b - 4) + 4 ^ a <
            4 ^ (b - 1 + 1) :=
        calc 80 * 4 ^ (b - 4) + 4 ^ a <
            80 * 4 ^ (b - 4) + 4 ^ (b - 4) :=
              Nat.add_lt_add_left haw _
          _ = 81 * 4 ^ (b - 4) := by ring
          _ ≤ 256 * 4 ^ (b - 4) :=
            Nat.mul_le_mul_right _ (by norm_num)
          _ = (4 : ℕ) ^ (b - 1 + 1) := h256w.symm
      exact fun j hj =>
        not_pure_of_bounds (L := b - 1) hl hr ⟨j, hj⟩
    · have hl :
          (4 : ℕ) ^ (b - 1) <
            80 * 4 ^ (b - 4) + 4 ^ a :=
        calc (4 : ℕ) ^ (b - 1) = 64 * 4 ^ (b - 4) :=
            h64w
          _ < 80 * 4 ^ (b - 4) :=
            Nat.mul_lt_mul_of_pos_right (by norm_num)
              (pow4_pos _)
          _ ≤ 80 * 4 ^ (b - 4) + 4 ^ a :=
            Nat.le_add_right _ _
      have hr :
          80 * 4 ^ (b - 4) + 4 ^ a <
            4 ^ (b - 1 + 1) :=
        calc 80 * 4 ^ (b - 4) + 4 ^ a <
            80 * 4 ^ (b - 4) + 4 ^ (b - 4) :=
              Nat.add_lt_add_left haw _
          _ = 81 * 4 ^ (b - 4) := by ring
          _ ≤ 256 * 4 ^ (b - 4) :=
            Nat.mul_le_mul_right _ (by norm_num)
          _ = (4 : ℕ) ^ (b - 1 + 1) := h256w.symm
      exact fun j hj =>
        not_pure_of_bounds (L := b - 1) hl hr ⟨j, hj⟩
    · exact fun j => not_pure_of_scaled
        (not_pure_of_bounds (c := 80) (L := 3)
          (by norm_num) (by norm_num)) j
    · rw [h256]
      ring
  · -- large trey: expand the trey, both stray bits ride above the
    -- windows without collision
    have h256 : (4 : ℕ) ^ a = 256 * 4 ^ (a - 4) := by
      have h := pow_shift_eq a 4 (by omega)
      norm_num at h
      exact h
    have hwb : ∀ c : ℕ, c ≤ 1024 →
        c * 4 ^ (a - 4) ≤ 4 ^ (b - 1 + 1) → True :=
      fun _ _ _ => trivial
    have hcw : ∀ c : ℕ, c < 1024 →
        c * 4 ^ (a - 4) < 4 ^ b := by
      intro c hc
      calc c * 4 ^ (a - 4) < 1024 * 4 ^ (a - 4) :=
          Nat.mul_lt_mul_of_pos_right hc (pow4_pos _)
        _ = 4 ^ (a + 1) := by
          have h := pow_shift_eq (a + 1) 5 (by omega)
          have he : a + 1 - 5 = a - 4 := by omega
          rw [he] at h
          norm_num at h
          omega
        _ ≤ 4 ^ b :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
    refine
      ⟨4 ^ b + 341 * 4 ^ (a - 4),
        4 ^ b + 337 * 4 ^ (a - 4),
        85 * 4 ^ (a - 4), 5 * 4 ^ (a - 4),
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact isBase4_pow_add
        (isBase4_scaledConst (c := 341) (L := 5)
          (a - 4) (by norm_num) (by decide))
        (hcw 341 (by norm_num))
    · exact isBase4_pow_add
        (isBase4_scaledConst (c := 337) (L := 5)
          (a - 4) (by norm_num) (by decide))
        (hcw 337 (by norm_num))
    · exact isBase4_scaledConst (c := 85) (L := 4)
        (a - 4) (by norm_num) (by decide)
    · exact isBase4_scaledConst (c := 5) (L := 2)
        (a - 4) (by norm_num) (by decide)
    · exact not_pure_pow_add
        (by positivity) (hcw 341 (by norm_num))
    · exact not_pure_pow_add
        (by positivity) (hcw 337 (by norm_num))
    · exact fun j => not_pure_of_scaled
        (not_pure_of_bounds (c := 85) (L := 3)
          (by norm_num) (by norm_num)) j
    · exact fun j => not_pure_of_scaled
        (not_pure_of_bounds (c := 5) (L := 1)
          (by norm_num) (by norm_num)) j
    · rw [h256]
      ring

end Erdos881Base4
