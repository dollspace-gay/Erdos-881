/-
# The Cantor carry-repair demonstrator (Erdős 881 mechanism)

The base-3 digit-{0,1} set `C` (Cantor basis) is an order-2 basis of ℕ
in the strongest sense: every `n : ℕ` is a sum of two members.  Deleting
the infinite set of pure powers `{3^k}` destroys order 2 *cofinally and
completely*: `3^k` loses every 2-representation.  Yet order 3 survives at
every destroyed scale: `3^k = 13·3^(k-3) + 10·3^(k-3) + 4·3^(k-3)` with
all three parts in `C` and none a pure power — the third summand unlocks
base-3 carries (`1+1+1 = 3`) that no 2-sum of digit-{0,1} numbers can
produce.

This is the exact repair mechanism the Erdős 881 (k = 2) positive
direction predicts: 2-rep poverty caused by digit rigidity is invisible
to order 3.  It also documents why the "Behrend/AP3-free adversary" for
the recurring-pair leaf fails to be a counterexample: the very digit
structure that keeps fork images AP3-free hands order 3 its carry
repairs.
-/

import Mathlib

namespace Erdos881Cantor

/-- Base-3 digits all ≤ 1. -/
def IsCantor (n : ℕ) : Prop := ∀ i, n / 3 ^ i % 3 ≤ 1

lemma isCantor_zero : IsCantor 0 := by intro i; simp [Nat.zero_div]

lemma pow3_pos (i : ℕ) : 0 < 3 ^ i := by positivity

lemma isCantor_pow (k : ℕ) : IsCantor (3 ^ k) := by
  intro i
  rcases Nat.lt_trichotomy i k with h | h | h
  · have h3 : 3 ^ k / 3 ^ i = 3 ^ (k - i) := by
      rw [Nat.pow_div (Nat.le_of_lt h) (by norm_num)]
    rw [h3]
    have h4 : k - i = (k - i - 1) + 1 := by omega
    rw [h4, pow_succ]
    simp [Nat.mul_mod]
  · subst h
    simp [Nat.div_self (pow3_pos i)]
  · have h3 : 3 ^ k < 3 ^ i := Nat.pow_lt_pow_right (by norm_num) h
    rw [Nat.div_eq_of_lt h3]
    simp

/-- Digit-shift: multiplying by `3^m` shifts digits up. -/
lemma isCantor_shift {n : ℕ} (m : ℕ) (hn : IsCantor n) :
    IsCantor (3 ^ m * n) := by
  intro i
  rcases Nat.lt_or_ge i m with h | h
  · have h2 : 3 ^ m * n / 3 ^ i = 3 ^ (m - i) * n := by
      have : 3 ^ m = 3 ^ i * 3 ^ (m - i) := by
        rw [← pow_add]; congr 1; omega
      rw [this, Nat.mul_assoc, Nat.mul_div_cancel_left _
        (pow3_pos i)]
    rw [h2]
    have h4 : m - i = (m - i - 1) + 1 := by omega
    rw [h4, pow_succ]
    have : 3 ^ (m - i - 1) * 3 * n = 3 * (3 ^ (m - i - 1) * n) := by ring
    rw [this]
    simp [Nat.mul_mod_right]
  · have h2 : 3 ^ i = 3 ^ m * 3 ^ (i - m) := by
      rw [← pow_add]; congr 1; omega
    rw [h2, ← Nat.div_div_eq_div_mul,
      Nat.mul_div_cancel_left _ (pow3_pos m)]
    exact hn (i - m)

/-- Low-part bound: a Cantor number's residue mod `3^i` is at most
`(3^i - 1)/2` — in the form avoiding division. -/
lemma isCantor_mod_bound {a : ℕ} (ha : IsCantor a) :
    ∀ i, 2 * (a % 3 ^ i) + 1 ≤ 3 ^ i := by
  intro i
  induction i with
  | zero => simp [Nat.mod_one]
  | succ i ih =>
    have hd : a / 3 ^ i % 3 ≤ 1 := ha i
    have hp : 0 < 3 ^ i := pow3_pos i
    have hmm : a % (3 ^ i * 3) = a % 3 ^ i + 3 ^ i * (a / 3 ^ i % 3) :=
      Nat.mod_mul
    rw [pow_succ, hmm]
    nlinarith [ih, hd, hp]

/-- No-carry addition of Cantor numbers: quotients add. -/
lemma isCantor_add_div {a b : ℕ} (ha : IsCantor a) (hb : IsCantor b)
    (i : ℕ) : (a + b) / 3 ^ i = a / 3 ^ i + b / 3 ^ i := by
  have hp : 0 < 3 ^ i := pow3_pos i
  have hma := isCantor_mod_bound ha i
  have hmb := isCantor_mod_bound hb i
  have hda := Nat.div_add_mod a (3 ^ i)
  have hdb := Nat.div_add_mod b (3 ^ i)
  have hsum : a + b = 3 ^ i * (a / 3 ^ i + b / 3 ^ i)
      + (a % 3 ^ i + b % 3 ^ i) := by
    rw [Nat.mul_add]; omega
  have hlt : a % 3 ^ i + b % 3 ^ i < 3 ^ i := by omega
  rw [hsum, Nat.mul_add_div hp, Nat.div_eq_of_lt hlt]
  omega

/-- No-carry addition of Cantor numbers: digits add. -/
lemma isCantor_add_digit {a b : ℕ} (ha : IsCantor a) (hb : IsCantor b)
    (i : ℕ) :
    (a + b) / 3 ^ i % 3 = a / 3 ^ i % 3 + b / 3 ^ i % 3 := by
  have h1 := isCantor_add_div ha hb i
  have h2 := isCantor_add_div ha hb (i + 1)
  have hstep : ∀ c : ℕ, c / 3 ^ (i + 1) = c / 3 ^ i / 3 := by
    intro c
    rw [pow_succ, ← Nat.div_div_eq_div_mul]
  rw [hstep] at h2
  rw [hstep a, hstep b] at h2
  have hda := Nat.div_add_mod (a / 3 ^ i) 3
  have hdb := Nat.div_add_mod (b / 3 ^ i) 3
  have hds := Nat.div_add_mod ((a + b) / 3 ^ i) 3
  have hla : a / 3 ^ i % 3 ≤ 1 := ha i
  have hlb : b / 3 ^ i % 3 ≤ 1 := hb i
  omega

/-- A Cantor number below `3^j` with all digits `< j` equal to zero
is zero. -/
lemma isCantor_eq_zero_of_digits {a j : ℕ} (hlt : a < 3 ^ j)
    (hz : ∀ i, i < j → a / 3 ^ i % 3 = 0) : a = 0 := by
  induction j generalizing a with
  | zero => simpa using hlt
  | succ j ih =>
    have h0 : a % 3 = 0 := by simpa using hz 0 (by omega)
    have hq : a / 3 < 3 ^ j := by
      have h3 : a < 3 * 3 ^ j := by
        rw [pow_succ] at hlt; omega
      omega
    have hqz : ∀ i, i < j → a / 3 / 3 ^ i % 3 = 0 := by
      intro i hi
      have := hz (i + 1) (by omega)
      rwa [pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul] at this
    have := ih hq hqz
    omega

/-- Digit reconstruction: a number below `3^j` whose base-3 digits are
a single 1 at position `k < j` equals `3^k`. -/
lemma digit_single {x k j : ℕ} (hlt : x < 3 ^ j) (hk : k < j)
    (hd1 : x / 3 ^ k % 3 = 1)
    (hz : ∀ i, i < j → i ≠ k → x / 3 ^ i % 3 = 0) : x = 3 ^ k := by
  induction j generalizing x k with
  | zero => omega
  | succ j ih =>
    have hshift : ∀ i, x / 3 / 3 ^ i = x / 3 ^ (i + 1) := by
      intro i
      rw [pow_succ, Nat.mul_comm (3 ^ i) 3, ← Nat.div_div_eq_div_mul]
    have hqlt : x / 3 < 3 ^ j := by
      have h1 : x < 3 * 3 ^ j := by
        rw [pow_succ, Nat.mul_comm] at hlt; exact hlt
      omega
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      have h0 : x % 3 = 1 := by simpa using hd1
      have hqz : x / 3 = 0 := by
        refine isCantor_eq_zero_of_digits hqlt ?_
        intro i hi
        rw [hshift i]
        exact hz (i + 1) (by omega) (by omega)
      have := Nat.div_add_mod x 3
      simp only [pow_zero]
      omega
    · have h0 : x % 3 = 0 := by
        have := hz 0 (by omega) (by omega)
        simpa using this
      have hd1' : x / 3 / 3 ^ (k - 1) % 3 = 1 := by
        rw [hshift (k - 1)]
        have hkk : k - 1 + 1 = k := by omega
        rwa [hkk]
      have hz' : ∀ i, i < j → i ≠ k - 1 → x / 3 / 3 ^ i % 3 = 0 := by
        intro i hi hik
        rw [hshift i]
        exact hz (i + 1) (by omega) (by omega)
      have hq := ih hqlt (by omega) hd1' hz'
      have hpow : 3 ^ k = 3 * 3 ^ (k - 1) := by
        have h1 : 3 ^ ((k - 1) + 1) = 3 ^ (k - 1) * 3 := pow_succ 3 (k - 1)
        have h2 : k - 1 + 1 = k := by omega
        rw [h2] at h1
        omega
      have := Nat.div_add_mod x 3
      omega

/-- Rigidity: two Cantor numbers cannot sum to a pure power unless one
of them is zero — 2-representations of `3^k` are trivial. -/
theorem cantor_two_rep_rigid {a b k : ℕ} (ha : IsCantor a)
    (hb : IsCantor b) (hab : a + b = 3 ^ k) : a = 0 ∨ b = 0 := by
  have hdig : ∀ i, i < k → a / 3 ^ i % 3 = 0 ∧ b / 3 ^ i % 3 = 0 := by
    intro i hik
    have h1 := isCantor_add_digit ha hb i
    rw [hab] at h1
    have h2 : 3 ^ k / 3 ^ i = 3 ^ (k - i) := by
      rw [Nat.pow_div (Nat.le_of_lt hik) (by norm_num)]
    have h3 : k - i = (k - i - 1) + 1 := by omega
    rw [h2, h3, pow_succ] at h1
    have h4 : 3 ^ (k - i - 1) * 3 % 3 = 0 := by simp [Nat.mul_mod]
    omega
  -- the digit at position k is 1, carried by exactly one summand
  have hk := isCantor_add_digit ha hb k
  rw [hab] at hk
  have hkk : 3 ^ k / 3 ^ k % 3 = 1 := by
    rw [Nat.div_self (pow3_pos k)]
  rw [hkk] at hk
  have hlta : a < 3 ^ (k + 1) := by
    have : 3 ^ k < 3 ^ (k + 1) := by
      rw [pow_succ]; have := pow3_pos k; omega
    omega
  have hltb : b < 3 ^ (k + 1) := by
    have : 3 ^ k < 3 ^ (k + 1) := by
      rw [pow_succ]; have := pow3_pos k; omega
    omega
  rcases Nat.eq_zero_or_pos (a / 3 ^ k % 3) with hza | hpa
  · left
    refine isCantor_eq_zero_of_digits hlta ?_
    intro i hik
    rcases Nat.lt_or_ge i k with h | h
    · exact (hdig i h).1
    · have hik' : i = k := by omega
      rwa [hik']
  · right
    have hzb : b / 3 ^ k % 3 = 0 := by omega
    refine isCantor_eq_zero_of_digits hltb ?_
    intro i hik
    rcases Nat.lt_or_ge i k with h | h
    · exact (hdig i h).2
    · have hik' : i = k := by omega
      rwa [hik']

/-- Digit extraction (`min` of the low digit with 1), the "first layer"
of the canonical 2-decomposition. -/
def layer : ℕ → ℕ
  | 0 => 0
  | n + 1 => 3 * layer ((n + 1) / 3) + min ((n + 1) % 3) 1
decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by norm_num)

lemma layer_zero : layer 0 = 0 := by simp [layer]

lemma layer_eq (n : ℕ) (hn : 0 < n) :
    layer n = 3 * layer (n / 3) + min (n % 3) 1 := by
  rcases n with _ | m
  · omega
  · simp [layer]

lemma layer_le (n : ℕ) : layer n ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [layer_zero]
    · rw [layer_eq n h]
      have hq : n / 3 < n := Nat.div_lt_self h (by norm_num)
      have h1 := ih (n / 3) hq
      have h2 := Nat.div_add_mod n 3
      have h3 : min (n % 3) 1 ≤ n % 3 := Nat.min_le_left _ _
      omega

/-- Digit identity for `layer`: its base-3 digits are the truncated
digits of `n`. -/
lemma layer_digit (n : ℕ) :
    ∀ i, layer n / 3 ^ i % 3 = min (n / 3 ^ i % 3) 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [layer_zero, Nat.zero_div]
    · rw [layer_eq n h]
      rcases i with _ | i
      · simp only [pow_zero, Nat.div_one]
        omega
      · have hq : n / 3 < n := Nat.div_lt_self h (by norm_num)
        have h30 : (3 * layer (n / 3) + min (n % 3) 1) / 3
            = layer (n / 3) := by omega
        have hstep : (3 * layer (n / 3) + min (n % 3) 1) / 3 ^ (i + 1)
            = layer (n / 3) / 3 ^ i := by
          rw [pow_succ, Nat.mul_comm (3 ^ i) 3, ← Nat.div_div_eq_div_mul, h30]
        have hnd : n / 3 ^ (i + 1) = n / 3 / 3 ^ i := by
          rw [pow_succ, Nat.mul_comm (3 ^ i) 3, ← Nat.div_div_eq_div_mul]
        rw [hstep, ih (n / 3) hq i, hnd]

lemma isCantor_layer (n : ℕ) : IsCantor (layer n) := by
  intro i
  rw [layer_digit n i]
  exact Nat.min_le_right _ _

/-- The complementary layer is also Cantor: digits `d - min d 1 ≤ 1`
for base-3 digits `d ≤ 2`. -/
lemma isCantor_complement (n : ℕ) : IsCantor (n - layer n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [layer_zero, Nat.zero_div]
    · have hq : n / 3 < n := Nat.div_lt_self h (by norm_num)
      have hrec : n - layer n = 3 * (n / 3 - layer (n / 3))
          + (n % 3 - min (n % 3) 1) := by
        have h1 := layer_eq n h
        have h2 := Nat.div_add_mod n 3
        have h3 := layer_le (n / 3)
        have h4 : min (n % 3) 1 ≤ n % 3 := Nat.min_le_left _ _
        have h5 : layer n ≤ n := layer_le n
        omega
      rcases i with _ | i
      · rw [hrec]
        simp only [pow_zero, Nat.div_one]
        omega
      · rw [hrec]
        have h30 : (3 * (n / 3 - layer (n / 3)) + (n % 3 - min (n % 3) 1)) / 3
            = n / 3 - layer (n / 3) := by omega
        have hstep : (3 * (n / 3 - layer (n / 3)) + (n % 3 - min (n % 3) 1))
            / 3 ^ (i + 1) = (n / 3 - layer (n / 3)) / 3 ^ i := by
          rw [pow_succ, Nat.mul_comm (3 ^ i) 3, ← Nat.div_div_eq_div_mul, h30]
        rw [hstep]
        exact ih (n / 3) hq i

/-- **The Cantor set is an order-2 basis of all of ℕ**: every natural
number is the sum of two digit-{0,1} numbers. -/
theorem cantor_pair_basis (n : ℕ) :
    ∃ a b, IsCantor a ∧ IsCantor b ∧ a + b = n :=
  ⟨layer n, n - layer n, isCantor_layer n, isCantor_complement n,
    by have := layer_le n; omega⟩

/-- **Power deletion destroys order 2 cofinally**: after removing the
pure powers, `3^k` has no 2-representation at all (`k ≥ 1`; even `0`
as a summand forces the pure power as the other part). -/
theorem cantor_powers_destroyed (k : ℕ) :
    ¬∃ a b, IsCantor a ∧ IsCantor b ∧ (∀ j, a ≠ 3 ^ j) ∧
      (∀ j, b ≠ 3 ^ j) ∧ a + b = 3 ^ k := by
  rintro ⟨a, b, ha, hb, hpa, hpb, hab⟩
  rcases cantor_two_rep_rigid ha hb hab with h | h
  · subst h
    exact hpb k (by omega)
  · subst h
    exact hpa k (by omega)

/-- The three carry parts are Cantor numbers: 13 = 111₃, 10 = 101₃,
4 = 11₃. -/
lemma isCantor_13 : IsCantor 13 := by
  intro i
  match i with
  | 0 => norm_num
  | 1 => norm_num
  | 2 => norm_num
  | (j + 3) =>
    have h27 : (27 : ℕ) ∣ 3 ^ (j + 3) := by
      have : (27 : ℕ) = 3 ^ 3 := by norm_num
      rw [this]
      exact pow_dvd_pow 3 (by omega)
    have : 13 / 3 ^ (j + 3) = 0 := by
      apply Nat.div_eq_of_lt
      calc (13 : ℕ) < 27 := by norm_num
        _ ≤ 3 ^ (j + 3) := Nat.le_of_dvd (pow3_pos _) h27
    simp [this]

lemma isCantor_10 : IsCantor 10 := by
  intro i
  match i with
  | 0 => norm_num
  | 1 => norm_num
  | 2 => norm_num
  | (j + 3) =>
    have h27 : (27 : ℕ) ∣ 3 ^ (j + 3) := by
      have : (27 : ℕ) = 3 ^ 3 := by norm_num
      rw [this]
      exact pow_dvd_pow 3 (by omega)
    have : 10 / 3 ^ (j + 3) = 0 := by
      apply Nat.div_eq_of_lt
      calc (10 : ℕ) < 27 := by norm_num
        _ ≤ 3 ^ (j + 3) := Nat.le_of_dvd (pow3_pos _) h27
    simp [this]

lemma isCantor_4 : IsCantor 4 := by
  intro i
  match i with
  | 0 => norm_num
  | 1 => norm_num
  | (j + 2) =>
    have h9 : (9 : ℕ) ∣ 3 ^ (j + 2) := by
      have : (9 : ℕ) = 3 ^ 2 := by norm_num
      rw [this]
      exact pow_dvd_pow 3 (by omega)
    have : 4 / 3 ^ (j + 2) = 0 := by
      apply Nat.div_eq_of_lt
      calc (4 : ℕ) < 9 := by norm_num
        _ ≤ 3 ^ (j + 2) := Nat.le_of_dvd (pow3_pos _) h9
    simp [this]

/-- A number of the form `c * 3^m` with `3 ∤ c`, `c` not a power of 3,
is not a pure power of 3. -/
lemma not_pure_of_scaled {c m : ℕ} (hc : ¬∃ t, c = 3 ^ t)
    (j : ℕ) : c * 3 ^ m ≠ 3 ^ j := by
  intro h
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0, Nat.zero_mul] at h
      have := pow3_pos j
      omega
    · exact h0
  rcases Nat.lt_or_ge j m with hj | hj
  · have h1 : 3 ^ m ≤ c * 3 ^ m := by
      calc 3 ^ m = 1 * 3 ^ m := by ring
        _ ≤ c * 3 ^ m := Nat.mul_le_mul_right _ hc0
    have h2 : 3 ^ j < 3 ^ m := Nat.pow_lt_pow_right (by norm_num) hj
    omega
  · have hsplit : 3 ^ j = 3 ^ (j - m) * 3 ^ m := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit] at h
    have hp : 0 < 3 ^ m := pow3_pos m
    have hcancel : c = 3 ^ (j - m) := Nat.eq_of_mul_eq_mul_right hp h
    exact hc ⟨j - m, hcancel⟩

lemma thirteen_not_pure : ¬∃ t, (13 : ℕ) = 3 ^ t := by
  rintro ⟨t, ht⟩
  match t with
  | 0 => norm_num at ht
  | 1 => norm_num at ht
  | 2 => norm_num at ht
  | (s + 3) =>
    have : 27 ≤ 3 ^ (s + 3) := by
      calc (27 : ℕ) = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ (s + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

lemma ten_not_pure : ¬∃ t, (10 : ℕ) = 3 ^ t := by
  rintro ⟨t, ht⟩
  match t with
  | 0 => norm_num at ht
  | 1 => norm_num at ht
  | 2 => norm_num at ht
  | (s + 3) =>
    have : 27 ≤ 3 ^ (s + 3) := by
      calc (27 : ℕ) = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ (s + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

lemma four_not_pure : ¬∃ t, (4 : ℕ) = 3 ^ t := by
  rintro ⟨t, ht⟩
  match t with
  | 0 => norm_num at ht
  | 1 => norm_num at ht
  | (s + 2) =>
    have : 9 ≤ 3 ^ (s + 2) := by
      calc (9 : ℕ) = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ (s + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- **The carry repair**: every destroyed power `3^k` (`k ≥ 3`) has an
order-3 representation by three Cantor numbers, none a pure power —
the deletion that kills order 2 is invisible to order 3. -/
theorem cantor_carry_repair (k : ℕ) (hk : 3 ≤ k) :
    ∃ x y z, IsCantor x ∧ IsCantor y ∧ IsCantor z ∧
      (∀ j, x ≠ 3 ^ j) ∧ (∀ j, y ≠ 3 ^ j) ∧ (∀ j, z ≠ 3 ^ j) ∧
      x + y + z = 3 ^ k := by
  refine ⟨13 * 3 ^ (k - 3), 10 * 3 ^ (k - 3), 4 * 3 ^ (k - 3),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := isCantor_shift (k - 3) isCantor_13
    rwa [Nat.mul_comm] at this
  · have := isCantor_shift (k - 3) isCantor_10
    rwa [Nat.mul_comm] at this
  · have := isCantor_shift (k - 3) isCantor_4
    rwa [Nat.mul_comm] at this
  · exact not_pure_of_scaled thirteen_not_pure
  · exact not_pure_of_scaled ten_not_pure
  · exact not_pure_of_scaled four_not_pure
  · have h1 : 3 ^ ((k - 3) + 3) = 3 ^ (k - 3) * 3 ^ 3 := pow_add 3 (k - 3) 3
    have h2 : k - 3 + 3 = k := by omega
    rw [h2] at h1
    have h3 : (3 : ℕ) ^ 3 = 27 := by norm_num
    rw [h1, h3]
    ring

/-- The doubled powers `2·3^k` are the *other* casualties: their unique
2-representation is `3^k + 3^k`, both parts deleted. -/
theorem cantor_doubles_destroyed (k : ℕ) :
    ¬∃ a b, IsCantor a ∧ IsCantor b ∧ (∀ j, a ≠ 3 ^ j) ∧
      (∀ j, b ≠ 3 ^ j) ∧ a + b = 2 * 3 ^ k := by
  rintro ⟨a, b, ha, hb, hpa, hpb, hab⟩
  -- digits add without carries, so both parts carry digit 1 at k and
  -- nothing elsewhere: a = b = 3^k, both pure.
  have hdig : ∀ i, i ≠ k → a / 3 ^ i % 3 = 0 ∧ b / 3 ^ i % 3 = 0 := by
    intro i hik
    have h1 := isCantor_add_digit ha hb i
    rw [hab] at h1
    rcases Nat.lt_or_ge i k with h | h
    · have h2 : 2 * 3 ^ k / 3 ^ i = 2 * 3 ^ (k - i) := by
        have hsplit : 3 ^ k = 3 ^ (k - i) * 3 ^ i := by
          rw [← pow_add]; congr 1; omega
        rw [hsplit, ← Nat.mul_assoc,
          Nat.mul_div_cancel _ (pow3_pos i)]
      have h3 : k - i = (k - i - 1) + 1 := by omega
      rw [h2, h3, pow_succ] at h1
      have h4 : 2 * (3 ^ (k - i - 1) * 3) % 3 = 0 := by
        rw [← Nat.mul_assoc]
        simp [Nat.mul_mod]
      omega
    · have hik' : k < i := by omega
      have h2 : 2 * 3 ^ k < 3 ^ i := by
        have hstep : 3 ^ (k + 1) ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [pow_succ] at hstep
        have := pow3_pos k
        omega
      rw [Nat.div_eq_of_lt h2] at h1
      simp only [Nat.zero_mod] at h1
      omega
  have hk := isCantor_add_digit ha hb k
  rw [hab] at hk
  have hkk : 2 * 3 ^ k / 3 ^ k % 3 = 2 := by
    rw [Nat.mul_div_cancel _ (pow3_pos k)]
  rw [hkk] at hk
  have hda : a / 3 ^ k % 3 = 1 := by
    have := ha k; have := hb k; omega
  have hlta : a < 3 ^ (k + 1) := by
    have h1 : 3 ^ (k + 1) = 3 ^ k * 3 := pow_succ 3 k
    have := pow3_pos k
    omega
  have hae : a = 3 ^ k :=
    digit_single hlta (by omega) hda (fun i _ hik => (hdig i hik).1)
  exact hpa k hae

/-- Two numbers agreeing on all base-3 digits below a common bound are
equal. -/
lemma eq_of_digits {a x j : ℕ} (ha : a < 3 ^ j) (hx : x < 3 ^ j)
    (h : ∀ i, i < j → a / 3 ^ i % 3 = x / 3 ^ i % 3) : a = x := by
  induction j generalizing a x with
  | zero => omega
  | succ j ih =>
    have h0 : a % 3 = x % 3 := by simpa using h 0 (by omega)
    have hqa : a / 3 < 3 ^ j := by
      have : a < 3 * 3 ^ j := by rw [pow_succ, Nat.mul_comm] at ha; exact ha
      omega
    have hqx : x / 3 < 3 ^ j := by
      have : x < 3 * 3 ^ j := by rw [pow_succ, Nat.mul_comm] at hx; exact hx
      omega
    have hq : ∀ i, i < j → a / 3 / 3 ^ i % 3 = x / 3 / 3 ^ i % 3 := by
      intro i hi
      have hsh : ∀ c : ℕ, c / 3 / 3 ^ i = c / 3 ^ (i + 1) := by
        intro c
        rw [pow_succ, Nat.mul_comm (3 ^ i) 3, ← Nat.div_div_eq_div_mul]
      rw [hsh, hsh]
      exact h (i + 1) (by omega)
    have := ih hqa hqx hq
    have hda := Nat.div_add_mod a 3
    have hdx := Nat.div_add_mod x 3
    omega

/-- **Doubling rigidity**: the only Cantor 2-representation of `2x`
(`x` Cantor) is `x + x`.  Every element's double is privately owned. -/
theorem cantor_double_unique {x a b : ℕ} (hx : IsCantor x)
    (ha : IsCantor a) (hb : IsCantor b) (hab : a + b = 2 * x) :
    a = x ∧ b = x := by
  have hxx : x + x = 2 * x := by ring
  -- digits of a + b and of x + x agree
  have hdig : ∀ i, a / 3 ^ i % 3 + b / 3 ^ i % 3 = 2 * (x / 3 ^ i % 3) := by
    intro i
    have h1 := isCantor_add_digit ha hb i
    have h2 := isCantor_add_digit hx hx i
    rw [hab] at h1
    rw [hxx] at h2
    omega
  have hbound : ∃ j, a < 3 ^ j ∧ b < 3 ^ j ∧ x < 3 ^ j := by
    refine ⟨a + b + x + 1, ?_, ?_, ?_⟩ <;>
      have := Nat.lt_pow_self (by norm_num : 1 < 3) (n := a + b + x + 1) <;>
      omega
  obtain ⟨j, hja, hjb, hjx⟩ := hbound
  have haeq : a = x := by
    refine eq_of_digits hja hjx ?_
    intro i _
    have h1 := hdig i
    have h2 := ha i
    have h3 := hb i
    have h4 := hx i
    omega
  refine ⟨haeq, by omega⟩

/-- **ℵ₀-minimality of the Cantor basis**: deleting any infinite subset
`B` destroys order 2 — for every `b ∈ B`, the target `2b` loses its
unique representation `(b, b)`.  Together with `cantor_pair_basis`
this makes `C` a minimal order-2 basis in the exact sense of
Erdős 881's hypothesis. -/
theorem cantor_minimal {B : Set ℕ} (hB : ∀ b ∈ B, IsCantor b) (b : ℕ)
    (hb : b ∈ B) :
    ¬∃ p q, IsCantor p ∧ IsCantor q ∧ p ∉ B ∧ q ∉ B ∧ p + q = 2 * b := by
  rintro ⟨p, q, hp, hq, hpB, _, hpq⟩
  obtain ⟨hpb, _⟩ := cantor_double_unique (hB b hb) hp hq hpq
  exact hpB (hpb ▸ hb)

/-- 37 = 1101₃ is a Cantor number. -/
lemma isCantor_37 : IsCantor 37 := by
  intro i
  match i with
  | 0 => norm_num
  | 1 => norm_num
  | 2 => norm_num
  | 3 => norm_num
  | (j + 4) =>
    have h81 : (81 : ℕ) ≤ 3 ^ (j + 4) := by
      calc (81 : ℕ) = 3 ^ 4 := by norm_num
        _ ≤ 3 ^ (j + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 37 / 3 ^ (j + 4) = 0 := Nat.div_eq_of_lt (by omega)
    simp [this]

lemma thirtyseven_not_pure : ¬∃ t, (37 : ℕ) = 3 ^ t := by
  rintro ⟨t, ht⟩
  match t with
  | 0 => norm_num at ht
  | 1 => norm_num at ht
  | 2 => norm_num at ht
  | 3 => norm_num at ht
  | (s + 4) =>
    have : 81 ≤ 3 ^ (s + 4) := by
      calc (81 : ℕ) = 3 ^ 4 := by norm_num
        _ ≤ 3 ^ (s + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- **Carry repair of the doubled casualties**: `2·3^k = (13+37+4)·3^(k-3)`
with all parts Cantor and non-pure. -/
theorem cantor_carry_repair_double (k : ℕ) (hk : 3 ≤ k) :
    ∃ x y z, IsCantor x ∧ IsCantor y ∧ IsCantor z ∧
      (∀ j, x ≠ 3 ^ j) ∧ (∀ j, y ≠ 3 ^ j) ∧ (∀ j, z ≠ 3 ^ j) ∧
      x + y + z = 2 * 3 ^ k := by
  refine ⟨13 * 3 ^ (k - 3), 37 * 3 ^ (k - 3), 4 * 3 ^ (k - 3),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := isCantor_shift (k - 3) isCantor_13
    rwa [Nat.mul_comm] at this
  · have := isCantor_shift (k - 3) isCantor_37
    rwa [Nat.mul_comm] at this
  · have := isCantor_shift (k - 3) isCantor_4
    rwa [Nat.mul_comm] at this
  · exact not_pure_of_scaled thirteen_not_pure
  · exact not_pure_of_scaled thirtyseven_not_pure
  · exact not_pure_of_scaled four_not_pure
  · have h1 : 3 ^ ((k - 3) + 3) = 3 ^ (k - 3) * 3 ^ 3 := pow_add 3 (k - 3) 3
    have h2 : k - 3 + 3 = k := by omega
    rw [h2] at h1
    have h3 : (3 : ℕ) ^ 3 = 27 := by norm_num
    rw [h1, h3]
    ring

/-- The Erdős 881 mechanism in one statement: the Cantor basis covers
ℕ at order 2, the power deletion is fatal to order 2 at every scale,
and order 3 repairs every casualty. -/
theorem cantor_demonstrator :
    (∀ n, ∃ a b, IsCantor a ∧ IsCantor b ∧ a + b = n) ∧
    (∀ k, ¬∃ a b, IsCantor a ∧ IsCantor b ∧ (∀ j, a ≠ 3 ^ j) ∧
      (∀ j, b ≠ 3 ^ j) ∧ a + b = 3 ^ k) ∧
    (∀ k, 3 ≤ k → ∃ x y z, IsCantor x ∧ IsCantor y ∧ IsCantor z ∧
      (∀ j, x ≠ 3 ^ j) ∧ (∀ j, y ≠ 3 ^ j) ∧ (∀ j, z ≠ 3 ^ j) ∧
      x + y + z = 3 ^ k) :=
  ⟨cantor_pair_basis, cantor_powers_destroyed, cantor_carry_repair⟩

end Erdos881Cantor
