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
    simp
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
    have h4 : 3 ^ (k - i - 1) * 3 % 3 = 0 := by simp
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
        simp
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


/-- Digits of a pure power: a single 1 at its exponent. -/
lemma pow_digit (j i : ℕ) : 3 ^ j / 3 ^ i % 3 = if i = j then 1 else 0 := by
  rcases Nat.lt_trichotomy i j with h | h | h
  · rw [if_neg (by omega)]
    have h3 : 3 ^ j / 3 ^ i = 3 ^ (j - i) := by
      rw [Nat.pow_div (Nat.le_of_lt h) (by norm_num)]
    rw [h3]
    have h4 : j - i = (j - i - 1) + 1 := by omega
    rw [h4, pow_succ]
    simp
  · subst h
    rw [if_pos rfl, Nat.div_self (pow3_pos i)]
  · rw [if_neg (by omega),
      Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) h)]

/-- Digits of a shifted number. -/
lemma shift_digit (n m i : ℕ) :
    3 ^ m * n / 3 ^ i % 3 = if i < m then 0 else n / 3 ^ (i - m) % 3 := by
  rcases Nat.lt_or_ge i m with h | h
  · rw [if_pos h]
    have h2 : 3 ^ m * n / 3 ^ i = 3 ^ (m - i) * n := by
      have h5 : 3 ^ m = 3 ^ i * 3 ^ (m - i) := by
        rw [← pow_add]; congr 1; omega
      rw [h5, Nat.mul_assoc, Nat.mul_div_cancel_left _ (pow3_pos i)]
    rw [h2]
    have h4 : m - i = (m - i - 1) + 1 := by omega
    rw [h4, pow_succ]
    have h6 : 3 ^ (m - i - 1) * 3 * n = 3 * (3 ^ (m - i - 1) * n) := by ring
    rw [h6]
    simp [Nat.mul_mod_right]
  · rw [if_neg (by omega)]
    have h2 : 3 ^ i = 3 ^ m * 3 ^ (i - m) := by
      rw [← pow_add]; congr 1; omega
    rw [h2, ← Nat.div_div_eq_div_mul,
      Nat.mul_div_cancel_left _ (pow3_pos m)]

/-- Addition of digit-disjoint Cantor numbers is Cantor. -/
lemma isCantor_add_disjoint {p q : ℕ} (hp : IsCantor p) (hq : IsCantor q)
    (hd : ∀ i, p / 3 ^ i % 3 = 0 ∨ q / 3 ^ i % 3 = 0) :
    IsCantor (p + q) := by
  intro i
  have h1 := isCantor_add_digit hp hq i
  have h2 := hp i
  have h3 := hq i
  rcases hd i with h | h <;> omega

/-- A number with digit 1 at `p` that differs from `3^p` is not a pure
power. -/
lemma not_pure_of_extra {x p : ℕ} (hdig : x / 3 ^ p % 3 = 1)
    (hne : x ≠ 3 ^ p) : ∀ j, x ≠ 3 ^ j := by
  intro j hx
  subst hx
  have h := pow_digit j p
  by_cases hpj : p = j
  · exact hne (by rw [hpj])
  · rw [if_neg hpj] at h
    omega

/-- A set digit bounds the number from below. -/
lemma pow_le_of_digit {x p : ℕ} (hd : x / 3 ^ p % 3 = 1) : 3 ^ p ≤ x := by
  by_contra hlt
  rw [Nat.div_eq_of_lt (by omega)] at hd
  norm_num at hd

lemma not_pure_zero : ∀ j, (0 : ℕ) ≠ 3 ^ j := by
  intro j
  have := pow3_pos j
  omega

/-- Scaled non-purity, shift-on-the-left form. -/
lemma not_pure_of_scaled' {c m : ℕ} (hc : ¬∃ t, c = 3 ^ t) (j : ℕ) :
    3 ^ m * c ≠ 3 ^ j := by
  rw [Nat.mul_comm]
  exact not_pure_of_scaled hc j

/-- Clearing a set digit: digits of `x - 3^p` when `x` is Cantor with
digit 1 at `p`. -/
lemma sub_pow_digit {x p : ℕ} (hx : IsCantor x) (hd : x / 3 ^ p % 3 = 1) :
    ∀ i, (x - 3 ^ p) / 3 ^ i % 3 = if i = p then 0 else x / 3 ^ i % 3 := by
  induction p generalizing x with
  | zero =>
    intro i
    have h1 : x % 3 = 1 := by simpa using hd
    rcases i with _ | i
    · rw [if_pos rfl]
      simp only [pow_zero, Nat.div_one]
      omega
    · rw [if_neg (by omega)]
      have hx1 : x - 3 ^ 0 = 3 * (x / 3) := by
        have := Nat.div_add_mod x 3
        simp only [pow_zero]
        omega
      rw [hx1]
      have hstep : 3 * (x / 3) / 3 ^ (i + 1) = x / 3 / 3 ^ i := by
        rw [pow_succ, Nat.mul_comm (3 ^ i) 3, ← Nat.div_div_eq_div_mul,
          Nat.mul_div_cancel_left _ (by norm_num : (0:ℕ) < 3)]
      rw [hstep]
      have hnd : x / 3 ^ (i + 1) = x / 3 / 3 ^ i := by
        rw [pow_succ, Nat.mul_comm (3 ^ i) 3, ← Nat.div_div_eq_div_mul]
      rw [hnd]
  | succ p ihp =>
    intro i
    have hq : IsCantor (x / 3) := by
      intro k
      have hnd : x / 3 / 3 ^ k = x / 3 ^ (k + 1) := by
        rw [pow_succ, Nat.mul_comm (3 ^ k) 3, ← Nat.div_div_eq_div_mul]
      rw [hnd]; exact hx (k + 1)
    have hdq : x / 3 / 3 ^ p % 3 = 1 := by
      have hnd : x / 3 / 3 ^ p = x / 3 ^ (p + 1) := by
        rw [pow_succ, Nat.mul_comm (3 ^ p) 3, ← Nat.div_div_eq_div_mul]
      rw [hnd]; exact hd
    have hge : 3 ^ p ≤ x / 3 := pow_le_of_digit hdq
    have hsub : x - 3 ^ (p + 1) = 3 * (x / 3 - 3 ^ p) + x % 3 := by
      have h2 := Nat.div_add_mod x 3
      have h3 : 3 ^ (p + 1) = 3 * 3 ^ p := by
        rw [pow_succ]; ring
      omega
    rw [hsub]
    rcases i with _ | i
    · rw [if_neg (by omega)]
      simp only [pow_zero, Nat.div_one]
      omega
    · have h30 : (3 * (x / 3 - 3 ^ p) + x % 3) / 3 = x / 3 - 3 ^ p := by
        omega
      have hstep : (3 * (x / 3 - 3 ^ p) + x % 3) / 3 ^ (i + 1)
          = (x / 3 - 3 ^ p) / 3 ^ i := by
        rw [pow_succ, Nat.mul_comm (3 ^ i) 3, ← Nat.div_div_eq_div_mul, h30]
      rw [hstep, ihp hq hdq i]
      have hnd : x / 3 / 3 ^ i = x / 3 ^ (i + 1) := by
        rw [pow_succ, Nat.mul_comm (3 ^ i) 3, ← Nat.div_div_eq_div_mul]
      by_cases hip : i = p
      · rw [if_pos hip, if_pos (by omega)]
      · rw [if_neg hip, if_neg (by omega), hnd]

/-- Every nonzero Cantor number has a digit equal to 1 somewhere. -/
lemma exists_digit_one : ∀ {m : ℕ}, IsCantor m → m ≠ 0 →
    ∃ v, m / 3 ^ v % 3 = 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm h0
    have h3 : m % 3 ≤ 1 := by simpa using hm 0
    rcases Nat.eq_zero_or_pos (m % 3) with hz | hpz
    · have hq0 : m / 3 ≠ 0 := by
        intro hq
        have := Nat.div_add_mod m 3
        omega
      have hqc : IsCantor (m / 3) := by
        intro k
        have hnd : m / 3 / 3 ^ k = m / 3 ^ (k + 1) := by
          rw [pow_succ, Nat.mul_comm (3 ^ k) 3, ← Nat.div_div_eq_div_mul]
        rw [hnd]; exact hm (k + 1)
      have hlt : m / 3 < m := Nat.div_lt_self (by omega) (by norm_num)
      obtain ⟨v, hv⟩ := ih (m / 3) hlt hqc hq0
      refine ⟨v + 1, ?_⟩
      have hnd : m / 3 ^ (v + 1) = m / 3 / 3 ^ v := by
        rw [pow_succ, Nat.mul_comm (3 ^ v) 3, ← Nat.div_div_eq_div_mul]
      rw [hnd]; exact hv
    · refine ⟨0, ?_⟩
      simp only [pow_zero, Nat.div_one]
      omega

/-- Digit formula for the complementary layer: digit `d` becomes
`d - min d 1`. -/
lemma complement_digit (n : ℕ) :
    ∀ i, (n - layer n) / 3 ^ i % 3
      = n / 3 ^ i % 3 - min (n / 3 ^ i % 3) 1 := by
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
        have hnd : n / 3 ^ (i + 1) = n / 3 / 3 ^ i := by
          rw [pow_succ, Nat.mul_comm (3 ^ i) 3, ← Nat.div_div_eq_div_mul]
        rw [hstep, ih (n / 3) hq i, hnd]

/-- 12 = 110₃, 28 = 1001₃, 39 = 1110₃, 40 = 1111₃ are Cantor. -/
lemma isCantor_12 : IsCantor 12 := by
  intro i
  match i with
  | 0 => norm_num
  | 1 => norm_num
  | 2 => norm_num
  | (j + 3) =>
    have h27 : (27 : ℕ) ≤ 3 ^ (j + 3) := by
      calc (27 : ℕ) = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ (j + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 12 / 3 ^ (j + 3) = 0 := Nat.div_eq_of_lt (by omega)
    simp [this]

lemma isCantor_28 : IsCantor 28 := by
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
    have : 28 / 3 ^ (j + 4) = 0 := Nat.div_eq_of_lt (by omega)
    simp [this]

lemma isCantor_39 : IsCantor 39 := by
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
    have : 39 / 3 ^ (j + 4) = 0 := Nat.div_eq_of_lt (by omega)
    simp [this]

lemma isCantor_40 : IsCantor 40 := by
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
    have : 40 / 3 ^ (j + 4) = 0 := Nat.div_eq_of_lt (by omega)
    simp [this]

lemma twelve_not_pure : ¬∃ t, (12 : ℕ) = 3 ^ t := by
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

lemma twentyeight_not_pure : ¬∃ t, (28 : ℕ) = 3 ^ t := by
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

lemma thirtynine_not_pure : ¬∃ t, (39 : ℕ) = 3 ^ t := by
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

lemma forty_not_pure : ¬∃ t, (40 : ℕ) = 3 ^ t := by
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

lemma isCantor_10' : IsCantor 10 := isCantor_10

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



/-- **The surviving deletion, in full**: after removing all pure powers
from the Cantor basis, order 3 still covers every `n ≥ 3^7`. -/
theorem cantor_deletion_order_three (n : ℕ) (hn : 3 ^ 7 ≤ n) :
    ∃ x y z, IsCantor x ∧ IsCantor y ∧ IsCantor z ∧
      (∀ j, x ≠ 3 ^ j) ∧ (∀ j, y ≠ 3 ^ j) ∧ (∀ j, z ≠ 3 ^ j) ∧
      x + y + z = n := by
  classical
  have h37 : (3 : ℕ) ^ 7 = 2187 := by norm_num
  have hlay := layer_le n
  have hc1 : IsCantor (layer n) := isCantor_layer n
  have hc2 : IsCantor (n - layer n) := isCantor_complement n
  by_cases hz2 : n - layer n = 0
  · -- no 2-digits: n itself is Cantor
    have hnl : layer n = n := by omega
    have hnc : IsCantor n := hnl ▸ hc1
    by_cases hpure : ∃ a, n = 3 ^ a
    · obtain ⟨a, ha⟩ := hpure
      have ha3 : 3 ≤ a := by
        by_contra hlt
        have h1 : n ≤ 3 ^ 2 := by
          rw [ha]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 : (3 : ℕ) ^ 2 = 9 := by norm_num
        omega
      obtain ⟨x, y, z, hx, hy, hz, hpx, hpy, hpz, hs⟩ :=
        cantor_carry_repair a ha3
      exact ⟨x, y, z, hx, hy, hz, hpx, hpy, hpz, by rw [ha]; exact hs⟩
    · push Not at hpure
      exact ⟨n, 0, 0, hnc, isCantor_zero, isCantor_zero, hpure,
        not_pure_zero, not_pure_zero, by omega⟩
  · by_cases hp2 : ∃ b, n - layer n = 3 ^ b
    · obtain ⟨b, hb⟩ := hp2
      have hdb : n / 3 ^ b % 3 = 2 := by
        have h1 := complement_digit n b
        rw [hb] at h1
        have h2 := pow_digit b b
        rw [if_pos rfl] at h2
        omega
      have hg1b : layer n / 3 ^ b % 3 = 1 := by
        have h1 := layer_digit n b
        rw [hdb] at h1
        simpa using h1
      have honesd := sub_pow_digit hc1 hg1b
      have honesc : IsCantor (layer n - 3 ^ b) := by
        intro i
        rw [honesd i]
        by_cases hib : i = b
        · rw [if_pos hib]; omega
        · rw [if_neg hib]; exact hc1 i
      have hg1ge : 3 ^ b ≤ layer n := pow_le_of_digit hg1b
      by_cases hones0 : layer n - 3 ^ b = 0
      · -- n = 2 * 3^b: the doubled-power casualty
        have hn2 : n = 2 * 3 ^ b := by omega
        have hb3 : 3 ≤ b := by
          by_contra hlt
          have h1 : 3 ^ b ≤ 3 ^ 2 :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          have h2 : (3 : ℕ) ^ 2 = 9 := by norm_num
          omega
        obtain ⟨x, y, z, hx, hy, hz, hpx, hpy, hpz, hs⟩ :=
          cantor_carry_repair_double b hb3
        exact ⟨x, y, z, hx, hy, hz, hpx, hpy, hpz, by rw [hn2]; exact hs⟩
      · obtain ⟨v, hv⟩ := exists_digit_one honesc hones0
        have honesb : (layer n - 3 ^ b) / 3 ^ b % 3 = 0 := by
          have h1 := honesd b
          rwa [if_pos rfl] at h1
        have hvb : v ≠ b := by
          intro hvb
          rw [hvb, honesb] at hv
          omega
        have hrestd := sub_pow_digit honesc hv
        have hrestc : IsCantor (layer n - 3 ^ b - 3 ^ v) := by
          intro i
          rw [hrestd i]
          by_cases hiv : i = v
          · rw [if_pos hiv]; omega
          · rw [if_neg hiv]; exact honesc i
        have hvge : 3 ^ v ≤ layer n - 3 ^ b := pow_le_of_digit hv
        by_cases hrest0 : layer n - 3 ^ b - 3 ^ v = 0
        · -- n = 2*3^b + 3^v: the constant menu
          have hnval : n = 2 * 3 ^ b + 3 ^ v := by omega
          rcases Nat.lt_or_ge v b with hvb' | hbv'
          · -- v < b: b dominant
            have hb7 : 7 ≤ b := by
              by_contra hlt
              have h1 : 3 ^ b ≤ 3 ^ 6 :=
                Nat.pow_le_pow_right (by norm_num) (by omega)
              have h2 : 3 ^ v ≤ 3 ^ 5 :=
                Nat.pow_le_pow_right (by norm_num) (by omega)
              have h3 : (3 : ℕ) ^ 6 = 729 := by norm_num
              have h4 : (3 : ℕ) ^ 5 = 243 := by norm_num
              omega
            have hu : 3 ^ b = 3 ^ (b - 3) * 27 := by
              have h1 : 3 ^ (b - 3 + 3) = 3 ^ (b - 3) * 3 ^ 3 :=
                pow_add 3 (b - 3) 3
              have h2 : b - 3 + 3 = b := by omega
              rw [h2] at h1
              have h3 : (3 : ℕ) ^ 3 = 27 := by norm_num
              rw [h3] at h1
              exact h1
            have hmenu : v ≤ b - 4 ∨ v = b - 3 ∨ v = b - 2 ∨ v = b - 1 := by
              omega
            rcases hmenu with hm4 | hm3 | hm2 | hm1
            · -- absorb 3^v into the 4-part: (13u, 37u, 4u + 3^v)
              refine ⟨3 ^ (b - 3) * 13, 3 ^ (b - 3) * 37,
                3 ^ (b - 3) * 4 + 3 ^ v,
                isCantor_shift _ isCantor_13, isCantor_shift _ isCantor_37,
                ?_, not_pure_of_scaled' thirteen_not_pure,
                not_pure_of_scaled' thirtyseven_not_pure, ?_, ?_⟩
              · refine isCantor_add_disjoint (isCantor_shift _ isCantor_4)
                  (isCantor_pow v) ?_
                intro i
                by_cases hiv : i = v
                · left
                  rw [shift_digit, if_pos (by omega)]
                · right
                  rw [pow_digit, if_neg hiv]
              · have hd4 : 3 ^ (b - 3) * 4 / 3 ^ v % 3 = 0 := by
                  rw [shift_digit, if_pos (by omega)]
                have h1 := isCantor_add_digit (isCantor_shift (b - 3) isCantor_4)
                  (isCantor_pow v) v
                have h2 := pow_digit v v
                rw [if_pos rfl] at h2
                have hdig : (3 ^ (b - 3) * 4 + 3 ^ v) / 3 ^ v % 3 = 1 := by
                  omega
                refine not_pure_of_extra hdig ?_
                have h5 : 3 ^ v ≤ 3 ^ (b - 3) :=
                  Nat.pow_le_pow_right (by norm_num) (by omega)
                have h6 := pow3_pos (b - 3)
                omega
              · omega
            · -- v = b-3: (39u, 12u, 4u) with 39+12+4 = 55 = 54+1
              have hvA : 3 ^ v = 3 ^ (b - 3) := by rw [hm3]
              exact ⟨3 ^ (b - 3) * 39, 3 ^ (b - 3) * 12, 3 ^ (b - 3) * 4,
                isCantor_shift _ isCantor_39, isCantor_shift _ isCantor_12,
                isCantor_shift _ isCantor_4,
                not_pure_of_scaled' thirtynine_not_pure,
                not_pure_of_scaled' twelve_not_pure,
                not_pure_of_scaled' four_not_pure, by omega⟩
            · -- v = b-2: (13u, 40u, 4u) with 13+40+4 = 57 = 54+3
              have hw : 3 ^ (b - 2) = 3 ^ (b - 3) * 3 := by
                have h1 : 3 ^ (b - 3 + 1) = 3 ^ (b - 3) * 3 :=
                  pow_succ 3 (b - 3)
                have h2 : b - 3 + 1 = b - 2 := by omega
                rw [h2] at h1
                exact h1
              have hvA : 3 ^ v = 3 ^ (b - 3) * 3 := by rw [hm2]; exact hw
              exact ⟨3 ^ (b - 3) * 13, 3 ^ (b - 3) * 40, 3 ^ (b - 3) * 4,
                isCantor_shift _ isCantor_13, isCantor_shift _ isCantor_40,
                isCantor_shift _ isCantor_4,
                not_pure_of_scaled' thirteen_not_pure,
                not_pure_of_scaled' forty_not_pure,
                not_pure_of_scaled' four_not_pure, by omega⟩
            · -- v = b-1: (13w, 4w, 4w) with 13+4+4 = 21 = 18+3, w = 3^(b-2)
              have hw9 : 3 ^ b = 3 ^ (b - 2) * 9 := by
                have h1 : 3 ^ (b - 2 + 2) = 3 ^ (b - 2) * 3 ^ 2 :=
                  pow_add 3 (b - 2) 2
                have h2 : b - 2 + 2 = b := by omega
                rw [h2] at h1
                have h3 : (3 : ℕ) ^ 2 = 9 := by norm_num
                rw [h3] at h1
                exact h1
              have hw3 : 3 ^ (b - 1) = 3 ^ (b - 2) * 3 := by
                have h1 : 3 ^ (b - 2 + 1) = 3 ^ (b - 2) * 3 :=
                  pow_succ 3 (b - 2)
                have h2 : b - 2 + 1 = b - 1 := by omega
                rw [h2] at h1
                exact h1
              have hvA : 3 ^ v = 3 ^ (b - 2) * 3 := by rw [hm1]; exact hw3
              exact ⟨3 ^ (b - 2) * 13, 3 ^ (b - 2) * 4, 3 ^ (b - 2) * 4,
                isCantor_shift _ isCantor_13, isCantor_shift _ isCantor_4,
                isCantor_shift _ isCantor_4,
                not_pure_of_scaled' thirteen_not_pure,
                not_pure_of_scaled' four_not_pure,
                not_pure_of_scaled' four_not_pure, by omega⟩
          · -- b < v: v dominant
            have hbv : b < v := by omega
            have hv7 : 7 ≤ v := by
              by_contra hlt
              have h1 : 3 ^ v ≤ 3 ^ 6 :=
                Nat.pow_le_pow_right (by norm_num) (by omega)
              have h2 : 3 ^ b ≤ 3 ^ 5 :=
                Nat.pow_le_pow_right (by norm_num) (by omega)
              have h3 : (3 : ℕ) ^ 6 = 729 := by norm_num
              have h4 : (3 : ℕ) ^ 5 = 243 := by norm_num
              omega
            have hmenu : v = b + 1 ∨ v = b + 2 ∨ v = b + 3 ∨ b + 4 ≤ v := by
              omega
            rcases hmenu with hm1 | hm2 | hm3 | hm4
            · -- v = b+1: (13w, 28w, 4w), 45 = 18+27, w = 3^(b-2)
              have hw9 : 3 ^ b = 3 ^ (b - 2) * 9 := by
                have h1 : 3 ^ (b - 2 + 2) = 3 ^ (b - 2) * 3 ^ 2 :=
                  pow_add 3 (b - 2) 2
                have h2 : b - 2 + 2 = b := by omega
                rw [h2] at h1
                have h3 : (3 : ℕ) ^ 2 = 9 := by norm_num
                rw [h3] at h1
                exact h1
              have hw27 : 3 ^ v = 3 ^ (b - 2) * 27 := by
                have h1 : 3 ^ (b - 2 + 3) = 3 ^ (b - 2) * 3 ^ 3 :=
                  pow_add 3 (b - 2) 3
                have h2 : b - 2 + 3 = b + 1 := by omega
                rw [h2] at h1
                have h3 : (3 : ℕ) ^ 3 = 27 := by norm_num
                rw [h3] at h1
                rw [hm1]
                exact h1
              exact ⟨3 ^ (b - 2) * 13, 3 ^ (b - 2) * 28, 3 ^ (b - 2) * 4,
                isCantor_shift _ isCantor_13, isCantor_shift _ isCantor_28,
                isCantor_shift _ isCantor_4,
                not_pure_of_scaled' thirteen_not_pure,
                not_pure_of_scaled' twentyeight_not_pure,
                not_pure_of_scaled' four_not_pure, by omega⟩
            · -- v = b+2: (13t, 10t, 10t), 33 = 6+27, t = 3^(b-1)
              have ht3 : 3 ^ b = 3 ^ (b - 1) * 3 := by
                have h1 : 3 ^ (b - 1 + 1) = 3 ^ (b - 1) * 3 :=
                  pow_succ 3 (b - 1)
                have h2 : b - 1 + 1 = b := by omega
                rw [h2] at h1
                exact h1
              have ht27 : 3 ^ v = 3 ^ (b - 1) * 27 := by
                have h1 : 3 ^ (b - 1 + 3) = 3 ^ (b - 1) * 3 ^ 3 :=
                  pow_add 3 (b - 1) 3
                have h2 : b - 1 + 3 = b + 2 := by omega
                rw [h2] at h1
                have h3 : (3 : ℕ) ^ 3 = 27 := by norm_num
                rw [h3] at h1
                rw [hm2]
                exact h1
              exact ⟨3 ^ (b - 1) * 13, 3 ^ (b - 1) * 10, 3 ^ (b - 1) * 10,
                isCantor_shift _ isCantor_13, isCantor_shift _ isCantor_10,
                isCantor_shift _ isCantor_10,
                not_pure_of_scaled' thirteen_not_pure,
                not_pure_of_scaled' ten_not_pure,
                not_pure_of_scaled' ten_not_pure, by omega⟩
            · -- v = b+3: (13s, 12s, 4s), 29 = 2+27, s = 3^b
              have hs27 : 3 ^ v = 3 ^ b * 27 := by
                have h1 : 3 ^ (b + 3) = 3 ^ b * 3 ^ 3 := pow_add 3 b 3
                have h3 : (3 : ℕ) ^ 3 = 27 := by norm_num
                rw [h3] at h1
                rw [hm3]
                exact h1
              exact ⟨3 ^ b * 13, 3 ^ b * 12, 3 ^ b * 4,
                isCantor_shift _ isCantor_13, isCantor_shift _ isCantor_12,
                isCantor_shift _ isCantor_4,
                not_pure_of_scaled' thirteen_not_pure,
                not_pure_of_scaled' twelve_not_pure,
                not_pure_of_scaled' four_not_pure, by omega⟩
            · -- v ≥ b+4: split 3^v, absorb 3^b twice:
              -- (13w + 3^b, 10w + 3^b, 4w), w = 3^(v-3)
              have hw27 : 3 ^ v = 3 ^ (v - 3) * 27 := by
                have h1 : 3 ^ (v - 3 + 3) = 3 ^ (v - 3) * 3 ^ 3 :=
                  pow_add 3 (v - 3) 3
                have h2 : v - 3 + 3 = v := by omega
                rw [h2] at h1
                have h3 : (3 : ℕ) ^ 3 = 27 := by norm_num
                rw [h3] at h1
                exact h1
              have hdisj13 : ∀ i : ℕ, 3 ^ (v - 3) * 13 / 3 ^ i % 3 = 0 ∨
                  3 ^ b / 3 ^ i % 3 = 0 := by
                intro i
                by_cases hib : i = b
                · left
                  rw [shift_digit, if_pos (by omega)]
                · right
                  rw [pow_digit, if_neg hib]
              have hdisj10 : ∀ i : ℕ, 3 ^ (v - 3) * 10 / 3 ^ i % 3 = 0 ∨
                  3 ^ b / 3 ^ i % 3 = 0 := by
                intro i
                by_cases hib : i = b
                · left
                  rw [shift_digit, if_pos (by omega)]
                · right
                  rw [pow_digit, if_neg hib]
              have hnp13 : ∀ j, 3 ^ (v - 3) * 13 + 3 ^ b ≠ 3 ^ j := by
                have hd0 : 3 ^ (v - 3) * 13 / 3 ^ b % 3 = 0 := by
                  rw [shift_digit, if_pos (by omega)]
                have h1 := isCantor_add_digit
                  (isCantor_shift (v - 3) isCantor_13) (isCantor_pow b) b
                have h2 := pow_digit b b
                rw [if_pos rfl] at h2
                have hdig : (3 ^ (v - 3) * 13 + 3 ^ b) / 3 ^ b % 3 = 1 := by
                  omega
                refine not_pure_of_extra hdig ?_
                have h6 := pow3_pos (v - 3)
                omega
              have hnp10 : ∀ j, 3 ^ (v - 3) * 10 + 3 ^ b ≠ 3 ^ j := by
                have hd0 : 3 ^ (v - 3) * 10 / 3 ^ b % 3 = 0 := by
                  rw [shift_digit, if_pos (by omega)]
                have h1 := isCantor_add_digit
                  (isCantor_shift (v - 3) isCantor_10) (isCantor_pow b) b
                have h2 := pow_digit b b
                rw [if_pos rfl] at h2
                have hdig : (3 ^ (v - 3) * 10 + 3 ^ b) / 3 ^ b % 3 = 1 := by
                  omega
                refine not_pure_of_extra hdig ?_
                have h6 := pow3_pos (v - 3)
                omega
              exact ⟨3 ^ (v - 3) * 13 + 3 ^ b, 3 ^ (v - 3) * 10 + 3 ^ b,
                3 ^ (v - 3) * 4,
                isCantor_add_disjoint (isCantor_shift _ isCantor_13)
                  (isCantor_pow b) hdisj13,
                isCantor_add_disjoint (isCantor_shift _ isCantor_10)
                  (isCantor_pow b) hdisj10,
                isCantor_shift _ isCantor_4,
                hnp13, hnp10, not_pure_of_scaled' four_not_pure, by omega⟩
        · -- generic split: (3^b + 3^v, 3^b + rest, 0)
          have hrestb : (layer n - 3 ^ b - 3 ^ v) / 3 ^ b % 3 = 0 := by
            have h1 := hrestd b
            rw [if_neg (fun h => hvb h.symm)] at h1
            rw [h1]
            exact honesb
          have hxc : IsCantor (3 ^ b + 3 ^ v) := by
            refine isCantor_add_disjoint (isCantor_pow b) (isCantor_pow v) ?_
            intro i
            by_cases hib : i = b
            · right
              rw [pow_digit, if_neg (by omega)]
            · left
              rw [pow_digit, if_neg hib]
          have hyc : IsCantor (3 ^ b + (layer n - 3 ^ b - 3 ^ v)) := by
            refine isCantor_add_disjoint (isCantor_pow b) hrestc ?_
            intro i
            by_cases hib : i = b
            · right
              rw [hib]
              exact hrestb
            · left
              rw [pow_digit, if_neg hib]
          have hxnp : ∀ j, 3 ^ b + 3 ^ v ≠ 3 ^ j := by
            have h1 := isCantor_add_digit (isCantor_pow b) (isCantor_pow v) b
            have h2 := pow_digit b b
            rw [if_pos rfl] at h2
            have h3 := pow_digit v b
            rw [if_neg (fun h => hvb h.symm)] at h3
            have hdig : (3 ^ b + 3 ^ v) / 3 ^ b % 3 = 1 := by omega
            refine not_pure_of_extra hdig ?_
            have h6 := pow3_pos v
            omega
          have hynp : ∀ j, 3 ^ b + (layer n - 3 ^ b - 3 ^ v) ≠ 3 ^ j := by
            have h1 := isCantor_add_digit (isCantor_pow b) hrestc b
            have h2 := pow_digit b b
            rw [if_pos rfl] at h2
            have hdig : (3 ^ b + (layer n - 3 ^ b - 3 ^ v)) / 3 ^ b % 3 = 1 := by
              omega
            refine not_pure_of_extra hdig ?_
            omega
          exact ⟨3 ^ b + 3 ^ v, 3 ^ b + (layer n - 3 ^ b - 3 ^ v), 0,
            hxc, hyc, isCantor_zero, hxnp, hynp, not_pure_zero, by omega⟩
    · -- the 2-digit part is composite: (layer n, n - layer n, 0)
      have hg1np : ∀ j, layer n ≠ 3 ^ j := by
        intro a hga
        have hd : ∀ i, i ≠ a → n / 3 ^ i % 3 = 0 := by
          intro i hia
          have h1 := layer_digit n i
          rw [hga] at h1
          have h2 := pow_digit a i
          rw [if_neg hia] at h2
          omega
        have hg2z : ∀ i, i ≠ a → (n - layer n) / 3 ^ i % 3 = 0 := by
          intro i hia
          have h1 := complement_digit n i
          rw [hd i hia] at h1
          simpa using h1
        have hbnd : n - layer n < 3 ^ (n - layer n + a + 1) := by
          have h1 : n - layer n < 3 ^ (n - layer n) :=
            Nat.lt_pow_self (by norm_num) (n := n - layer n)
          have h2 : 3 ^ (n - layer n) ≤ 3 ^ (n - layer n + a + 1) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        rcases Nat.eq_zero_or_pos ((n - layer n) / 3 ^ a % 3) with hza | hpa
        · refine hz2 (isCantor_eq_zero_of_digits hbnd ?_)
          intro i _
          by_cases hia : i = a
          · rwa [hia]
          · exact hg2z i hia
        · have h1 : (n - layer n) / 3 ^ a % 3 = 1 := by
            have := hc2 a
            omega
          refine hp2 ⟨a, digit_single hbnd (by omega) h1 ?_⟩
          intro i _ hia
          exact hg2z i hia
      exact ⟨layer n, n - layer n, 0, hc1, hc2, isCantor_zero, hg1np,
        fun j h => hp2 ⟨j, h⟩, not_pure_zero, by omega⟩

/-- **A complete verified Erdős 881 instance.**  The Cantor set is an
order-2 basis of ℕ; it is ℵ₀-minimal — deleting ANY infinite subset
destroys order 2 (each deleted element's double loses its unique
representation); yet deleting the infinite set of pure powers leaves an
asymptotic order-3 basis.  This realizes the conclusion pattern of
Erdős 881 (k = 2) end to end on a concrete minimal basis. -/
theorem erdos881_cantor_instance :
    (∀ n, ∃ a b, IsCantor a ∧ IsCantor b ∧ a + b = n) ∧
    (∀ B : Set ℕ, (∀ b ∈ B, IsCantor b) → ∀ b ∈ B,
      ¬∃ p q, IsCantor p ∧ IsCantor q ∧ p ∉ B ∧ q ∉ B ∧ p + q = 2 * b) ∧
    (∀ k, IsCantor (3 ^ k)) ∧
    (∀ n, 3 ^ 7 ≤ n → ∃ x y z, IsCantor x ∧ IsCantor y ∧ IsCantor z ∧
      (∀ j, x ≠ 3 ^ j) ∧ (∀ j, y ≠ 3 ^ j) ∧ (∀ j, z ≠ 3 ^ j) ∧
      x + y + z = n) :=
  ⟨cantor_pair_basis, fun _ hB b hb => cantor_minimal hB b hb,
    isCantor_pow, cantor_deletion_order_three⟩

end Erdos881Cantor
