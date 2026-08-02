/-
# The base-4 master sieve: rich constructions

The carry-free half of the classifier.  When a digit profile carries
enough companion material, the four slots fill by layer surgery alone:
no carries, no menus.  Together with the menu families of
`Base4Sieve`/`Base4Layers`, every digit profile of a large number is
covered; the dispatch and the official-predicate assembly follow in
this file's second half.
-/

import Erdos881.Base4Layers

namespace Erdos881Base4

lemma not_pure_zero4 : ∀ j, (0 : ℕ) ≠ 4 ^ j := by
  intro j
  have := pow4_pos j
  omega

/-- Two distinct powers add to a base-4 number. -/
lemma isBase4_two_pow {i j : ℕ} (hij : i ≠ j) :
    IsBase4 (4 ^ i + 4 ^ j) := by
  rcases Nat.lt_or_ge i j with h | h
  · rw [Nat.add_comm]
    exact isBase4_pow_add (isBase4_pow i)
      (Nat.pow_lt_pow_right (by norm_num) h)
  · exact isBase4_pow_add (isBase4_pow j)
      (Nat.pow_lt_pow_right (by norm_num) (by omega))

/-- Two distinct powers add to a non-power. -/
lemma not_pure_two_pow {i j : ℕ} (hij : i ≠ j) :
    ∀ t, 4 ^ i + 4 ^ j ≠ 4 ^ t := by
  rcases Nat.lt_or_ge i j with h | h
  · intro t
    rw [Nat.add_comm]
    exact not_pure_pow_add (pow4_pos i)
      (Nat.pow_lt_pow_right (by norm_num) h) t
  · intro t
    exact not_pure_pow_add (pow4_pos j)
      (Nat.pow_lt_pow_right (by norm_num) (by omega)) t

/-- Layer digits are inherited downward. -/
lemma layer_digit_le {s t n i : ℕ} (h1 : 1 ≤ s)
    (hst : s ≤ t)
    (hd : layer t n / 4 ^ i % 4 = 1) :
    layer s n / 4 ^ i % 4 = 1 := by
  rw [layer_digit t (by omega) i n] at hd
  rw [layer_digit s h1 i n]
  by_cases hc : t ≤ n / 4 ^ i % 4
  · rw [if_pos (le_trans hst hc)]
  · rw [if_neg hc] at hd
    omega

/-- If the second layer vanishes so does the third. -/
lemma layer3_zero_of_layer2 {n : ℕ}
    (h : layer 2 n = 0) : layer 3 n = 0 := by
  apply eq_zero_of_digits4
  intro i
  have h2 := layer_digit 2 (by norm_num) i n
  rw [h] at h2
  simp only [Nat.zero_div, Nat.zero_mod] at h2
  have h3 := layer_digit 3 (by norm_num) i n
  by_cases hc : 3 ≤ n / 4 ^ i % 4
  · exfalso
    rw [if_pos (by omega)] at h2
    omega
  · rw [h3, if_neg hc]

/-- A power-valued layer reads a digit bound at its position. -/
lemma digit_ge_of_layer_pow {t n b : ℕ} (ht : 1 ≤ t)
    (h : layer t n = 4 ^ b) :
    t ≤ n / 4 ^ b % 4 := by
  have hd := layer_digit t ht b n
  rw [h, pow_digit4 b b, if_pos rfl] at hd
  by_cases hc : t ≤ n / 4 ^ b % 4
  · exact hc
  · rw [if_neg hc] at hd
    omega

/-- A layer-1 digit from a raw digit bound. -/
lemma layer1_digit_of_ge {n b : ℕ}
    (h : 1 ≤ n / 4 ^ b % 4) :
    layer 1 n / 4 ^ b % 4 = 1 := by
  rw [layer_digit 1 (by norm_num) b n, if_pos h]

/-- The first layer of a large number is nonzero. -/
lemma layer1_ne_zero {n : ℕ} (hn : n ≠ 0) :
    layer 1 n ≠ 0 := by
  intro h
  apply hn
  apply eq_zero_of_digits4
  intro i
  have h1 := layer_digit 1 (by norm_num) i n
  rw [h] at h1
  simp only [Nat.zero_div, Nat.zero_mod] at h1
  by_cases hc : 1 ≤ n / 4 ^ i % 4
  · rw [if_pos hc] at h1
    omega
  · omega

/-- **Rich order-2 world**: the second layer carries two digits, the
first inherits them, and the pair of layers is a legal split. -/
lemma rich_two_layers {n : ℕ}
    (hL3 : layer 3 n = 0) (h0 : layer 2 n ≠ 0)
    (hnp : ∀ j, layer 2 n ≠ 4 ^ j) :
    ∃ x y z t, IsBase4 x ∧ IsBase4 y ∧ IsBase4 z ∧
      IsBase4 t ∧
      (∀ j, x ≠ 4 ^ j) ∧ (∀ j, y ≠ 4 ^ j) ∧
      (∀ j, z ≠ 4 ^ j) ∧ (∀ j, t ≠ 4 ^ j) ∧
      x + y + z + t = n := by
  obtain ⟨p, q, hpq, hp, hq⟩ :=
    two_digits_of_nonpure (layer_isBase4 2 n) h0
      (fun j hj => hnp j hj)
  have hp1 := layer_digit_le (s := 1) (by norm_num)
    (by norm_num) hp
  have hq1 := layer_digit_le (s := 1) (by norm_num)
    (by norm_num) hq
  have hsum := layer_sum n
  refine
    ⟨layer 1 n, layer 2 n, 0, 0,
      layer_isBase4 1 n, layer_isBase4 2 n,
      isBase4_zero, isBase4_zero,
      not_pure_of_two_digits hp1 hq1 hpq,
      not_pure_of_two_digits hp hq hpq,
      not_pure_zero4, not_pure_zero4, ?_⟩
  omega

/-- **Rich order-3 world**: the third layer carries two digits. -/
lemma rich_three_layers {n : ℕ}
    (h0 : layer 3 n ≠ 0)
    (hnp : ∀ j, layer 3 n ≠ 4 ^ j) :
    ∃ x y z t, IsBase4 x ∧ IsBase4 y ∧ IsBase4 z ∧
      IsBase4 t ∧
      (∀ j, x ≠ 4 ^ j) ∧ (∀ j, y ≠ 4 ^ j) ∧
      (∀ j, z ≠ 4 ^ j) ∧ (∀ j, t ≠ 4 ^ j) ∧
      x + y + z + t = n := by
  obtain ⟨p, q, hpq, hp, hq⟩ :=
    two_digits_of_nonpure (layer_isBase4 3 n) h0
      (fun j hj => hnp j hj)
  have hp2 := layer_digit_le (s := 2) (by norm_num)
    (by norm_num) hp
  have hq2 := layer_digit_le (s := 2) (by norm_num)
    (by norm_num) hq
  have hp1 := layer_digit_le (le_refl 1)
    (by norm_num) hp2
  have hq1 := layer_digit_le (le_refl 1)
    (by norm_num) hq2
  have hsum := layer_sum n
  refine
    ⟨layer 1 n, layer 2 n, layer 3 n, 0,
      layer_isBase4 1 n, layer_isBase4 2 n,
      layer_isBase4 3 n, isBase4_zero,
      not_pure_of_two_digits hp1 hq1 hpq,
      not_pure_of_two_digits hp2 hq2 hpq,
      not_pure_of_two_digits hp hq hpq,
      not_pure_zero4, ?_⟩
  omega

/-- **Rich single-deuce surgery**: one deuce, at least two extra
first-layer digits — move one across. -/
lemma rich_deuce_surgery {n b : ℕ}
    (hL3 : layer 3 n = 0)
    (hL2 : layer 2 n = 4 ^ b)
    (hR0 : layer 1 n - 4 ^ b ≠ 0)
    (hRnp : ∀ j, layer 1 n - 4 ^ b ≠ 4 ^ j) :
    ∃ x y z t, IsBase4 x ∧ IsBase4 y ∧ IsBase4 z ∧
      IsBase4 t ∧
      (∀ j, x ≠ 4 ^ j) ∧ (∀ j, y ≠ 4 ^ j) ∧
      (∀ j, z ≠ 4 ^ j) ∧ (∀ j, t ≠ 4 ^ j) ∧
      x + y + z + t = n := by
  have hdb : 2 ≤ n / 4 ^ b % 4 :=
    digit_ge_of_layer_pow (by norm_num) hL2
  have hb1 : layer 1 n / 4 ^ b % 4 = 1 :=
    layer1_digit_of_ge (by omega)
  have hL1b : IsBase4 (layer 1 n) := layer_isBase4 1 n
  have hRb : IsBase4 (layer 1 n - 4 ^ b) :=
    isBase4_sub_bit hL1b hb1
  obtain ⟨p, q, hpq, hpd, hqd⟩ :=
    two_digits_of_nonpure hRb hR0 hRnp
  have hRdig := sub_pow_digit4 hL1b hb1
  have hpb : p ≠ b := by
    intro h
    rw [h, hRdig b, if_pos rfl] at hpd
    omega
  have hqb : q ≠ b := by
    intro h
    rw [h, hRdig b, if_pos rfl] at hqd
    omega
  have hpL1 : layer 1 n / 4 ^ p % 4 = 1 := by
    have h := hRdig p
    rw [if_neg hpb] at h
    omega
  have hqL1 : layer 1 n / 4 ^ q % 4 = 1 := by
    have h := hRdig q
    rw [if_neg hqb] at h
    omega
  -- move bit q: S₁ = L₁ - 4^q keeps digits b and p
  have hS1b : IsBase4 (layer 1 n - 4 ^ q) :=
    isBase4_sub_bit hL1b hqL1
  have hS1dig := sub_pow_digit4 hL1b hqL1
  have hS1p : (layer 1 n - 4 ^ q) / 4 ^ p % 4 = 1 := by
    have h := hS1dig p
    rw [if_neg (by omega : p ≠ q)] at h
    omega
  have hS1bb :
      (layer 1 n - 4 ^ q) / 4 ^ b % 4 = 1 := by
    have h := hS1dig b
    rw [if_neg (by omega : b ≠ q)] at h
    omega
  have hqle : 4 ^ q ≤ layer 1 n :=
    pow_le_of_digit4 hqL1
  have hsum := layer_sum n
  refine
    ⟨layer 1 n - 4 ^ q, 4 ^ b + 4 ^ q, 0, 0,
      hS1b, isBase4_two_pow (by omega : b ≠ q),
      isBase4_zero, isBase4_zero,
      not_pure_of_two_digits hS1bb hS1p
        (by omega : b ≠ p),
      not_pure_two_pow (by omega : b ≠ q),
      not_pure_zero4, not_pure_zero4, ?_⟩
  omega

/-- **Rich single-trey surgery, plentiful companions**: three extra
first-layer digits feed all three trey slots. -/
lemma rich_trey_surgery {n a p q : ℕ}
    (hL3 : layer 3 n = 4 ^ a)
    (hL2 : layer 2 n = 4 ^ a)
    (hpq : p ≠ q) (hpa : p ≠ a) (hqa : q ≠ a)
    (hpd : layer 1 n / 4 ^ p % 4 = 1)
    (hqd : layer 1 n / 4 ^ q % 4 = 1)
    (hres : layer 1 n - 4 ^ a - 4 ^ p - 4 ^ q ≠ 0) :
    ∃ x y z t, IsBase4 x ∧ IsBase4 y ∧ IsBase4 z ∧
      IsBase4 t ∧
      (∀ j, x ≠ 4 ^ j) ∧ (∀ j, y ≠ 4 ^ j) ∧
      (∀ j, z ≠ 4 ^ j) ∧ (∀ j, t ≠ 4 ^ j) ∧
      x + y + z + t = n := by
  have hda : 3 ≤ n / 4 ^ a % 4 :=
    digit_ge_of_layer_pow (by norm_num) hL3
  have haL1 : layer 1 n / 4 ^ a % 4 = 1 :=
    layer1_digit_of_ge (by omega)
  have hL1b : IsBase4 (layer 1 n) := layer_isBase4 1 n
  -- S₁ = L₁ - 4^p - 4^q keeps digit a and the residual digit
  have hS1b' : IsBase4 (layer 1 n - 4 ^ p) :=
    isBase4_sub_bit hL1b hpd
  have hdig' := sub_pow_digit4 hL1b hpd
  have hq' : (layer 1 n - 4 ^ p) / 4 ^ q % 4 = 1 := by
    have h := hdig' q
    rw [if_neg (by omega : q ≠ p)] at h
    omega
  have hS1b : IsBase4 (layer 1 n - 4 ^ p - 4 ^ q) :=
    isBase4_sub_bit hS1b' hq'
  have hdig'' := sub_pow_digit4 hS1b' hq'
  have haS1 :
      (layer 1 n - 4 ^ p - 4 ^ q) / 4 ^ a % 4 = 1 := by
    have h2 := hdig' a
    rw [if_neg (by omega : a ≠ p)] at h2
    have h3 := hdig'' a
    rw [if_neg (by omega : a ≠ q)] at h3
    omega
  -- the residual supplies a second digit for S₁
  have hrb : IsBase4
      (layer 1 n - 4 ^ p - 4 ^ q - 4 ^ a) := by
    exact isBase4_sub_bit hS1b haS1
  obtain ⟨r, hr⟩ := exists_digit_one4 hrb (by
    have hple : 4 ^ p ≤ layer 1 n :=
      pow_le_of_digit4 hpd
    have hqle : 4 ^ q ≤ layer 1 n - 4 ^ p :=
      pow_le_of_digit4 hq'
    have hale :
        4 ^ a ≤ layer 1 n - 4 ^ p - 4 ^ q :=
      pow_le_of_digit4 haS1
    omega)
  have hdig''' := sub_pow_digit4 hS1b haS1
  have hra : r ≠ a := by
    intro h
    rw [h, hdig''' a, if_pos rfl] at hr
    omega
  have hrS1 :
      (layer 1 n - 4 ^ p - 4 ^ q) / 4 ^ r % 4 = 1 := by
    have h := hdig''' r
    rw [if_neg hra] at h
    omega
  have hple : 4 ^ p ≤ layer 1 n :=
    pow_le_of_digit4 hpd
  have hqle : 4 ^ q ≤ layer 1 n - 4 ^ p :=
    pow_le_of_digit4 hq'
  have hsum := layer_sum n
  refine
    ⟨layer 1 n - 4 ^ p - 4 ^ q, 4 ^ a + 4 ^ p,
      4 ^ a + 4 ^ q, 0,
      hS1b, isBase4_two_pow (by omega : a ≠ p),
      isBase4_two_pow (by omega : a ≠ q),
      isBase4_zero,
      not_pure_of_two_digits haS1 hrS1
        (by omega : a ≠ r),
      not_pure_two_pow (by omega : a ≠ p),
      not_pure_two_pow (by omega : a ≠ q),
      not_pure_zero4, ?_⟩
  omega

/-- **Rich trey with a busy second layer**: an extra second-layer
digit funds the third slot, and a residual first-layer digit keeps
the donor slot honest.  The profile with NO residual is exactly
`3·4^a + 2·4^q` and is routed to the carry menus instead. -/
lemma rich_trey_deuce {n a q : ℕ}
    (hL3 : layer 3 n = 4 ^ a)
    (hqa : q ≠ a)
    (hq2 : layer 2 n / 4 ^ q % 4 = 1)
    (hL2np : ∀ j, layer 2 n ≠ 4 ^ j)
    (hres : layer 1 n - 4 ^ q - 4 ^ a ≠ 0) :
    ∃ x y z t, IsBase4 x ∧ IsBase4 y ∧ IsBase4 z ∧
      IsBase4 t ∧
      (∀ j, x ≠ 4 ^ j) ∧ (∀ j, y ≠ 4 ^ j) ∧
      (∀ j, z ≠ 4 ^ j) ∧ (∀ j, t ≠ 4 ^ j) ∧
      x + y + z + t = n := by
  have hq1 : layer 1 n / 4 ^ q % 4 = 1 :=
    layer_digit_le (le_refl 1) (by norm_num) hq2
  have hda : 3 ≤ n / 4 ^ a % 4 :=
    digit_ge_of_layer_pow (by norm_num) hL3
  have ha1 : layer 1 n / 4 ^ a % 4 = 1 :=
    layer1_digit_of_ge (by omega)
  have hL1b : IsBase4 (layer 1 n) := layer_isBase4 1 n
  have hS1b : IsBase4 (layer 1 n - 4 ^ q) :=
    isBase4_sub_bit hL1b hq1
  have hdig := sub_pow_digit4 hL1b hq1
  have haS1 :
      (layer 1 n - 4 ^ q) / 4 ^ a % 4 = 1 := by
    have h := hdig a
    rw [if_neg (by omega : a ≠ q)] at h
    omega
  have hresb :
      IsBase4 (layer 1 n - 4 ^ q - 4 ^ a) :=
    isBase4_sub_bit hS1b haS1
  obtain ⟨r, hr⟩ := exists_digit_one4 hresb hres
  have hdig' := sub_pow_digit4 hS1b haS1
  have hra : r ≠ a := by
    intro h
    rw [h, hdig' a, if_pos rfl] at hr
    omega
  have hrS1 :
      (layer 1 n - 4 ^ q) / 4 ^ r % 4 = 1 := by
    have h := hdig' r
    rw [if_neg hra] at h
    omega
  have hqle : 4 ^ q ≤ layer 1 n :=
    pow_le_of_digit4 hq1
  have hsum := layer_sum n
  refine
    ⟨layer 1 n - 4 ^ q, layer 2 n, 4 ^ a + 4 ^ q, 0,
      hS1b, layer_isBase4 2 n,
      isBase4_two_pow (by omega : a ≠ q),
      isBase4_zero,
      not_pure_of_two_digits haS1 hrS1
        (by omega : a ≠ r),
      hL2np,
      not_pure_two_pow (by omega : a ≠ q),
      not_pure_zero4, ?_⟩
  omega

end Erdos881Base4
