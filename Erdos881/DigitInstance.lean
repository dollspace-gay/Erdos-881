/-
# The uniform digit instance: every base, every order, one theorem

For every `k ≥ 2` the base-`(k+1)` digit-{0,1} set is a strongly
minimal exact order-`k` basis, and for `k ≥ 3` it is NOT an exact
order-2 basis — so every hard case of the general-order campaign is
inhabited, uniformly in `k`, by one theorem
(`digit_uniform_hard_case`).

The two verified instances (`Cantor*`, base 3, k = 2 and `Base4*`,
base 4, k = 3) are the special cases; this file proves the pattern in
a single stroke.  The mechanisms are uniform: sums of at most `k`
digit numbers never carry (`k` ones fit below the base `k+1`), so
order-`k` representations are digit assignments, targets with a digit
`k` defeat every lower order, and the diagonal `k·x` has the unique
representation `(x, …, x)`.

Base convention: everything is phrased over base `k + 1` literally,
so `base - 1 = k` holds definitionally and no truncated subtraction
appears.
-/

import Erdos881.AdditiveSupports

namespace Erdos881Digit

open Erdos881

/-- Base-`(k+1)` digits all ≤ 1. -/
def IsDigitK (k n : ℕ) : Prop :=
  ∀ i, n / (k + 1) ^ i % (k + 1) ≤ 1

/-- The uniform digit basis. -/
def DigitSet (k : ℕ) : Set ℕ := {n | IsDigitK k n}

lemma isDigitK_zero (k : ℕ) : IsDigitK k 0 := by
  intro i
  simp [Nat.zero_div]

lemma basePow_pos (k i : ℕ) : 0 < (k + 1) ^ i := by
  positivity

/-- Quotient step for digit access. -/
lemma div_pow_succ (k n i : ℕ) :
    n / (k + 1) ^ (i + 1) =
      n / (k + 1) / (k + 1) ^ i := by
  rw [pow_succ, Nat.mul_comm ((k + 1) ^ i) (k + 1),
    ← Nat.div_div_eq_div_mul]

/-- Residue step for digit access. -/
lemma mod_pow_succ (k n i : ℕ) :
    n % (k + 1) ^ (i + 1) =
      n % (k + 1) ^ i +
        (k + 1) ^ i * (n / (k + 1) ^ i % (k + 1)) := by
  rw [pow_succ]
  exact Nat.mod_mul

/-- Powers are digit numbers. -/
lemma isDigitK_pow (k m : ℕ) (hk : 1 ≤ k) :
    IsDigitK k ((k + 1) ^ m) := by
  intro i
  rcases Nat.lt_trichotomy i m with h | h | h
  · have h3 : (k + 1) ^ m / (k + 1) ^ i =
        (k + 1) ^ (m - i) := by
      rw [Nat.pow_div (Nat.le_of_lt h) (by omega)]
    rw [h3]
    have h4 : m - i = (m - i - 1) + 1 := by omega
    rw [h4, pow_succ]
    simp
  · subst h
    simp only [Nat.div_self (basePow_pos k i)]
    exact Nat.mod_le 1 (k + 1)
  · have h3 : (k + 1) ^ m < (k + 1) ^ i :=
      Nat.pow_lt_pow_right (by omega) h
    rw [Nat.div_eq_of_lt h3]
    simp

/-- Quotients of digit numbers are digit numbers. -/
lemma isDigitK_div {k n : ℕ} (hn : IsDigitK k n) :
    IsDigitK k (n / (k + 1)) := by
  intro i
  rw [← div_pow_succ]
  exact hn (i + 1)

/-- A number with all base-`(k+1)` digits zero is zero. -/
lemma eq_zero_of_digitsK {k x : ℕ} (hk : 1 ≤ k)
    (h : ∀ i, x / (k + 1) ^ i % (k + 1) = 0) :
    x = 0 := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hpos
    · rfl
    have h0 : x % (k + 1) = 0 := by simpa using h 0
    have hq : ∀ i,
        x / (k + 1) / (k + 1) ^ i % (k + 1) = 0 := by
      intro i
      rw [← div_pow_succ]
      exact h (i + 1)
    have hlt : x / (k + 1) < x :=
      Nat.div_lt_self (by omega) (by omega)
    have hz := ih (x / (k + 1)) hlt hq
    have hdm := Nat.div_add_mod x (k + 1)
    rw [hz, Nat.mul_zero] at hdm
    omega

/-- The scaled residue bound: a digit number's residue at scale `i`
is at most the repunit `((k+1)^i - 1)/k`, in additive form. -/
lemma digit_mod_bound {k x : ℕ} (hx : IsDigitK k x) :
    ∀ i, k * (x % (k + 1) ^ i) + 1 ≤ (k + 1) ^ i := by
  intro i
  induction i with
  | zero =>
    simp [Nat.mod_one]
  | succ i ih =>
    rw [mod_pow_succ]
    have hd : x / (k + 1) ^ i % (k + 1) ≤ 1 := hx i
    calc k * (x % (k + 1) ^ i +
          (k + 1) ^ i *
            (x / (k + 1) ^ i % (k + 1))) + 1
        = (k * (x % (k + 1) ^ i) + 1) +
            k * ((k + 1) ^ i *
              (x / (k + 1) ^ i % (k + 1))) := by
          ring
      _ ≤ (k + 1) ^ i + k * ((k + 1) ^ i * 1) := by
          refine Nat.add_le_add ih ?_
          exact Nat.mul_le_mul_left _
            (Nat.mul_le_mul_left _ hd)
      _ = (k + 1) ^ (i + 1) := by
          rw [pow_succ]
          ring

/-- Carry-free division of a pair with small residues. -/
lemma add_div_of_res {a c m : ℕ} (hm : 0 < m)
    (h : a % m + c % m < m) :
    (a + c) / m = a / m + c / m ∧
      (a + c) % m = a % m + c % m := by
  have ha := Nat.div_add_mod a m
  have hc := Nat.div_add_mod c m
  have hsplit : a + c =
      m * (a / m + c / m) + (a % m + c % m) := by
    rw [Nat.mul_add]
    omega
  constructor
  · rw [hsplit, Nat.mul_add_div hm,
      Nat.div_eq_of_lt h]
    omega
  · rw [hsplit, Nat.mul_add_mod,
      Nat.mod_eq_of_lt h]

/-- Residue sums of at most `k` digit numbers stay below the scale. -/
lemma tuple_res_lt {k : ℕ} (j : ℕ) (v : Fin j → ℕ)
    (hj : j ≤ k) (hv : ∀ l, IsDigitK k (v l)) (i : ℕ) :
    (∑ l, v l % (k + 1) ^ i) < (k + 1) ^ i := by
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · simpa using basePow_pos k i
  have hbound :
      k * (∑ l, v l % (k + 1) ^ i) + j ≤
        j * (k + 1) ^ i := by
    have h1 :
        (∑ l, (k * (v l % (k + 1) ^ i) + 1)) ≤
          ∑ _l : Fin j, ((k + 1) ^ i : ℕ) := by
      refine Finset.sum_le_sum ?_
      intro l _
      exact digit_mod_bound (hv l) i
    have h2 :
        (∑ l, (k * (v l % (k + 1) ^ i) + 1)) =
          k * (∑ l, v l % (k + 1) ^ i) + j := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    have h3 :
        (∑ _l : Fin j, ((k + 1) ^ i : ℕ)) =
          j * (k + 1) ^ i := by
      simp [Finset.sum_const, Finset.card_univ,
        smul_eq_mul]
    omega
  have hjk :
      j * (k + 1) ^ i ≤ k * (k + 1) ^ i :=
    Nat.mul_le_mul_right _ hj
  have hklt :
      k * (∑ l, v l % (k + 1) ^ i) <
        k * (k + 1) ^ i := by
    omega
  exact Nat.lt_of_mul_lt_mul_left hklt

/-- **Uniform no-carry law**: sums of at most `k` digit numbers split
at every scale. -/
lemma tuple_split {k : ℕ} :
    ∀ (j : ℕ) (v : Fin j → ℕ), j ≤ k →
      (∀ l, IsDigitK k (v l)) →
      ∀ i, ((∑ l, v l) / (k + 1) ^ i =
              ∑ l, v l / (k + 1) ^ i) ∧
           ((∑ l, v l) % (k + 1) ^ i =
              ∑ l, v l % (k + 1) ^ i) := by
  intro j
  induction j with
  | zero =>
    intro v _ _ i
    simp
  | succ j ih =>
    intro v hj hv i
    have htail := ih (fun l => v l.succ) (by omega)
      (fun l => hv l.succ) i
    have hres := tuple_res_lt (k := k) (j + 1) v hj
      hv i
    have hresc :
        v 0 % (k + 1) ^ i +
          (∑ l : Fin j, v l.succ) % (k + 1) ^ i <
            (k + 1) ^ i := by
      rw [htail.2]
      calc v 0 % (k + 1) ^ i +
            ∑ l : Fin j, v l.succ % (k + 1) ^ i
          = ∑ l : Fin (j + 1),
              v l % (k + 1) ^ i := by
            rw [Fin.sum_univ_succ]
        _ < (k + 1) ^ i := hres
    have hpair := add_div_of_res (basePow_pos k i)
      hresc
    constructor
    · calc (∑ l : Fin (j + 1), v l) / (k + 1) ^ i
          = (v 0 + ∑ l : Fin j, v l.succ) /
              (k + 1) ^ i := by
            rw [Fin.sum_univ_succ]
        _ = v 0 / (k + 1) ^ i +
              (∑ l : Fin j, v l.succ) /
                (k + 1) ^ i := hpair.1
        _ = v 0 / (k + 1) ^ i +
              ∑ l : Fin j, v l.succ / (k + 1) ^ i := by
            rw [htail.1]
        _ = ∑ l : Fin (j + 1), v l / (k + 1) ^ i :=
            (Fin.sum_univ_succ
              (f := fun l : Fin (j + 1) =>
                v l / (k + 1) ^ i)).symm
    · calc (∑ l : Fin (j + 1), v l) % (k + 1) ^ i
          = (v 0 + ∑ l : Fin j, v l.succ) %
              (k + 1) ^ i := by
            rw [Fin.sum_univ_succ]
        _ = v 0 % (k + 1) ^ i +
              (∑ l : Fin j, v l.succ) %
                (k + 1) ^ i := hpair.2
        _ = v 0 % (k + 1) ^ i +
              ∑ l : Fin j, v l.succ % (k + 1) ^ i := by
            rw [htail.2]
        _ = ∑ l : Fin (j + 1), v l % (k + 1) ^ i :=
            (Fin.sum_univ_succ
              (f := fun l : Fin (j + 1) =>
                v l % (k + 1) ^ i)).symm

/-- **Uniform digit additivity**: the digit of a sum of at most `k`
digit numbers is the sum of the digits. -/
lemma tuple_digit {k : ℕ} (j : ℕ) (v : Fin j → ℕ)
    (hj : j ≤ k) (hv : ∀ l, IsDigitK k (v l))
    (i : ℕ) :
    (∑ l, v l) / (k + 1) ^ i % (k + 1) =
      ∑ l, v l / (k + 1) ^ i % (k + 1) := by
  have h1 := (tuple_split (k := k) j v hj hv i).1
  have hstep : ∀ c : ℕ,
      c / (k + 1) ^ (i + 1) =
        c / (k + 1) ^ i / (k + 1) := by
    intro c
    rw [pow_succ, ← Nat.div_div_eq_div_mul]
  have hsmall :
      (∑ l, v l / (k + 1) ^ i % (k + 1)) <
        k + 1 := by
    calc (∑ l, v l / (k + 1) ^ i % (k + 1)) ≤
        ∑ _l : Fin j, 1 := by
          refine Finset.sum_le_sum ?_
          intro l _
          exact hv l i
      _ = j := by simp
      _ < k + 1 := by omega
  have hdm : ∀ l : Fin j,
      v l / (k + 1) ^ i =
        (k + 1) * (v l / (k + 1) ^ (i + 1)) +
          v l / (k + 1) ^ i % (k + 1) := by
    intro l
    rw [hstep (v l)]
    have := Nat.div_add_mod
      (v l / (k + 1) ^ i) (k + 1)
    omega
  have hsum :
      (∑ l, v l / (k + 1) ^ i) =
        (k + 1) *
            (∑ l, v l / (k + 1) ^ (i + 1)) +
          ∑ l, v l / (k + 1) ^ i % (k + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro l _
    exact hdm l
  rw [h1, hsum, Nat.mul_add_mod,
    Nat.mod_eq_of_lt hsmall]

/-- The indicator sum below a cutoff. -/
lemma sum_bits (j r : ℕ) (h : r ≤ j) :
    (∑ l : Fin j,
      (if (l : ℕ) < r then 1 else 0)) = r := by
  rw [Fin.sum_univ_eq_sum_range
    (fun i => if i < r then (1 : ℕ) else 0) j]
  have hfilter :
      (Finset.range j).filter (fun i => i < r) =
        Finset.range r := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [Finset.sum_ite]
  simp [hfilter]

/-- **Uniform order-`k` covering, threshold 0**: every number splits
digit by digit into `k` digit numbers. -/
theorem digit_basis (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    ∃ v : Fin k → ℕ, (∀ l, IsDigitK k (v l)) ∧
      (∑ l, v l) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact ⟨fun _ => 0, fun _ => isDigitK_zero k,
        by simp⟩
    obtain ⟨w, hw, hwsum⟩ :=
      ih (n / (k + 1))
        (Nat.div_lt_self hpos (by omega))
    have hr : n % (k + 1) < k + 1 :=
      Nat.mod_lt n (by omega)
    refine
      ⟨fun l => (k + 1) * w l +
        (if (l : ℕ) < n % (k + 1) then 1 else 0),
        ?_, ?_⟩
    · intro l i
      have hbit :
          (if (l : ℕ) < n % (k + 1) then 1 else 0) ≤
            1 := by
        split_ifs <;> omega
      cases i with
      | zero =>
        simp only [pow_zero, Nat.div_one]
        rw [Nat.mul_add_mod]
        rw [Nat.mod_eq_of_lt (by omega)]
        exact hbit
      | succ i =>
        rw [div_pow_succ]
        have hq :
            ((k + 1) * w l +
              (if (l : ℕ) < n % (k + 1) then 1
                else 0)) / (k + 1) = w l := by
          rw [Nat.mul_add_div (by omega)]
          rw [Nat.div_eq_of_lt (by omega)]
          omega
        rw [hq]
        exact hw l i
    · have hbits :
          (∑ l : Fin k,
            (if (l : ℕ) < n % (k + 1) then 1
              else 0)) = n % (k + 1) :=
        sum_bits k (n % (k + 1)) (by omega)
      calc (∑ l : Fin k, ((k + 1) * w l +
            (if (l : ℕ) < n % (k + 1) then 1
              else 0)))
          = (k + 1) * (∑ l, w l) +
              ∑ l : Fin k,
                (if (l : ℕ) < n % (k + 1) then 1
                  else 0) := by
            rw [Finset.sum_add_distrib,
              Finset.mul_sum]
        _ = (k + 1) * (n / (k + 1)) +
              n % (k + 1) := by
            rw [hwsum, hbits]
        _ = n := Nat.div_add_mod n (k + 1)

/-- A digit number with a single set digit is that power. -/
lemma eq_pow_of_single_digit {k m : ℕ} (hk : 1 ≤ k) :
    ∀ {x : ℕ}, IsDigitK k x →
      (∀ i, x / (k + 1) ^ i % (k + 1) =
        if i = m then 1 else 0) →
      x = (k + 1) ^ m := by
  induction m with
  | zero =>
    intro x _hx hd
    have h0 : x % (k + 1) = 1 := by
      have := hd 0
      simpa using this
    have hq : x / (k + 1) = 0 := by
      apply eq_zero_of_digitsK hk
      intro i
      rw [← div_pow_succ]
      have := hd (i + 1)
      rw [if_neg (by omega)] at this
      exact this
    have hdm := Nat.div_add_mod x (k + 1)
    rw [hq, Nat.mul_zero] at hdm
    simp only [pow_zero]
    omega
  | succ m ihm =>
    intro x hx hd
    have h0 : x % (k + 1) = 0 := by
      have := hd 0
      rw [if_neg (by omega)] at this
      simpa using this
    have hq : IsDigitK k (x / (k + 1)) :=
      isDigitK_div hx
    have hqd : ∀ i,
        x / (k + 1) / (k + 1) ^ i % (k + 1) =
          if i = m then 1 else 0 := by
      intro i
      rw [← div_pow_succ]
      have := hd (i + 1)
      by_cases him : i = m
      · rw [if_pos him]
        rw [if_pos (by omega)] at this
        exact this
      · rw [if_neg him]
        rw [if_neg (by omega)] at this
        exact this
    have hrec := ihm hq hqd
    have hdm := Nat.div_add_mod x (k + 1)
    rw [hrec, Nat.mul_comm] at hdm
    rw [pow_succ]
    omega

/-- Equal digit profiles force equal numbers. -/
lemma eq_of_digitsK {k : ℕ} (hk : 1 ≤ k) :
    ∀ {a : ℕ} {c : ℕ},
      (∀ i, a / (k + 1) ^ i % (k + 1) =
        c / (k + 1) ^ i % (k + 1)) → a = c := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro c h
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · symm
      apply eq_zero_of_digitsK hk
      intro i
      have := h i
      simpa using this.symm
    · have h0 : a % (k + 1) = c % (k + 1) := by
        simpa using h 0
      have htail : ∀ i,
          a / (k + 1) / (k + 1) ^ i % (k + 1) =
            c / (k + 1) / (k + 1) ^ i % (k + 1) := by
        intro i
        rw [← div_pow_succ, ← div_pow_succ]
        exact h (i + 1)
      have hlt : a / (k + 1) < a :=
        Nat.div_lt_self (by omega) (by omega)
      have hq := ih (a / (k + 1)) hlt htail
      have hda := Nat.div_add_mod a (k + 1)
      have hdc := Nat.div_add_mod c (k + 1)
      rw [hq] at hda
      omega

/-- The scaled diagonal's digits. -/
lemma diag_digit {k x : ℕ} (hx : IsDigitK k x)
    (i : ℕ) :
    k * x / (k + 1) ^ i % (k + 1) =
      k * (x / (k + 1) ^ i % (k + 1)) := by
  have h := tuple_digit (k := k) k (fun _ => x)
    (le_refl k) (fun _ => hx) i
  have hs : (∑ _l : Fin k, x) = k * x := by
    simp [Finset.sum_const, Finset.card_univ,
      smul_eq_mul]
  have hs2 :
      (∑ _l : Fin k,
        x / (k + 1) ^ i % (k + 1)) =
        k * (x / (k + 1) ^ i % (k + 1)) := by
    simp [Finset.sum_const, Finset.card_univ,
      smul_eq_mul]
  rw [hs, hs2] at h
  exact h

/-- A saturated bounded sum forces every entry to one. -/
lemma sum_saturated {k : ℕ} (f : Fin k → ℕ)
    (hle : ∀ l, f l ≤ 1) (hsum : (∑ l, f l) = k) :
    ∀ l, f l = 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨l₀, hl₀⟩ := hcon
  have hz : f l₀ = 0 := by
    have := hle l₀
    omega
  have hkpos : 0 < k := l₀.pos
  have hsplit :
      (∑ l, f l) =
        f l₀ + ∑ l ∈ Finset.univ.erase l₀, f l :=
    (Finset.add_sum_erase _ f
      (Finset.mem_univ l₀)).symm
  have hbound :
      (∑ l ∈ Finset.univ.erase l₀, f l) ≤
        (Finset.univ.erase l₀).card * 1 := by
    have := Finset.sum_le_card_nsmul
      (Finset.univ.erase l₀) f 1
      (fun x _ => hle x)
    simpa [smul_eq_mul] using this
  have hcard :
      (Finset.univ.erase l₀).card = k - 1 := by
    rw [Finset.card_erase_of_mem
      (Finset.mem_univ l₀), Finset.card_univ]
    simp
  omega

/-- **Uniform diagonal rigidity**: the only order-`k` representation
of `k·x` by digit numbers is `(x, …, x)`. -/
theorem digit_diag_rigid {k x : ℕ} (hk : 1 ≤ k)
    (hx : IsDigitK k x) (v : Fin k → ℕ)
    (hv : ∀ l, IsDigitK k (v l))
    (hsum : (∑ l, v l) = k * x) :
    ∀ l, v l = x := by
  intro l₀
  apply eq_of_digitsK hk
  intro i
  have hdig := tuple_digit (k := k) k v (le_refl k)
    hv i
  rw [hsum, diag_digit hx] at hdig
  have hd : x / (k + 1) ^ i % (k + 1) ≤ 1 := hx i
  rcases Nat.eq_zero_or_pos
    (x / (k + 1) ^ i % (k + 1)) with hz | hone
  · rw [hz, Nat.mul_zero] at hdig
    have hsingle :
        v l₀ / (k + 1) ^ i % (k + 1) ≤
          ∑ l, v l / (k + 1) ^ i % (k + 1) :=
      Finset.single_le_sum
        (f := fun l => v l / (k + 1) ^ i % (k + 1))
        (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ l₀)
    rw [hz]
    omega
  · have h1 : x / (k + 1) ^ i % (k + 1) = 1 := by
      omega
    rw [h1, Nat.mul_one] at hdig
    have hall := sum_saturated
      (fun l => v l / (k + 1) ^ i % (k + 1))
      (fun l => hv l i) hdig.symm
    have hvl :
        v l₀ / (k + 1) ^ i % (k + 1) = 1 := hall l₀
    rw [hvl, h1]

/-- **Uniform low-order impossibility**: no `j < k` digit numbers sum
to the digit-`k` target `k·(k+1)^m`. -/
theorem digit_low_order_miss {k j : ℕ} (hjk : j < k)
    (m : ℕ) (v : Fin j → ℕ)
    (hv : ∀ l, IsDigitK k (v l)) :
    (∑ l, v l) ≠ k * (k + 1) ^ m := by
  intro hsum
  have hdig := tuple_digit (k := k) j v
    (by omega) hv m
  rw [hsum] at hdig
  have hkd :
      k * (k + 1) ^ m / (k + 1) ^ m % (k + 1) =
        k := by
    rw [Nat.mul_div_cancel _ (basePow_pos k m)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hkd] at hdig
  have hbound :
      (∑ l, v l / (k + 1) ^ m % (k + 1)) ≤ j := by
    calc (∑ l, v l / (k + 1) ^ m % (k + 1)) ≤
        ∑ _l : Fin j, 1 := by
          refine Finset.sum_le_sum ?_
          intro l _
          exact hv l m
      _ = j := by simp
  omega

/-- The uniform basis in the official predicate. -/
theorem digit_basis_official (k : ℕ) (hk : 1 ≤ k) :
    IsExactTupleAsymptoticBasis (DigitSet k) k := by
  refine ⟨0, fun n _ => ?_⟩
  obtain ⟨v, hv, hsum⟩ := digit_basis k hk n
  exact ⟨v, hv, hsum⟩

/-- The uniform hard-case badge: for `k ≥ 3` the digit set misses
order 2 cofinally. -/
theorem digit_not_basis_two (k : ℕ) (hk : 3 ≤ k) :
    ¬ IsExactTupleAsymptoticBasis (DigitSet k) 2 := by
  rintro ⟨N, hN⟩
  have hbig : N ≤ k * (k + 1) ^ N := by
    have h1 : N < (k + 1) ^ N :=
      Nat.lt_pow_self (by omega)
    have h2 : (k + 1) ^ N ≤ k * (k + 1) ^ N :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  obtain ⟨v, hvmem, hvsum⟩ :=
    hN (k * (k + 1) ^ N) hbig
  exact digit_low_order_miss (by omega) N v
    (fun l => hvmem l) hvsum

/-- **Uniform strong minimality**: deleting any infinite subset
destroys the diagonal targets `k·x`, `x ∈ B`, cofinally — the
diagonal representation is unique, so its support `{x}` meets `B`. -/
theorem digit_strong_deletion (k : ℕ) (hk : 1 ≤ k) :
    StrongInfiniteDeletion
      (additiveSupportFamily (DigitSet k) k)
      (DigitSet k) := by
  intro B hBsub hBinf N
  obtain ⟨x, hxB, hNx⟩ := hBinf.exists_gt N
  refine ⟨k * x, ?_, ?_⟩
  · have hxk : x ≤ k * x :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  intro E hE
  obtain ⟨w, hwA, hwsum, hEw⟩ :=
    mem_additiveSupportFamily_iff.mp hE
  have hxd : IsDigitK k x := hBsub hxB
  have hall :=
    digit_diag_rigid hk hxd (fun l => (w l).1)
      (fun l => hwA l) hwsum
  rw [Set.not_disjoint_iff]
  refine ⟨x, ?_, hxB⟩
  rw [← hEw]
  exact Finset.mem_coe.mpr
    (mem_tupleSupport_iff.mpr
      ⟨⟨0, by omega⟩, hall ⟨0, by omega⟩⟩)

/-- **The uniform hard-case theorem**: for every `k ≥ 2` the
base-`(k+1)` digit set is a strongly minimal exact order-`k` basis,
and for every `k ≥ 3` it is not an exact order-2 basis.  Every hard
case of the general-order campaign is inhabited, in one stroke. -/
theorem digit_uniform_hard_case (k : ℕ) (hk : 2 ≤ k) :
    IsStronglyMinimalExactBasis (DigitSet k) k ∧
      (3 ≤ k →
        ¬ IsExactTupleAsymptoticBasis
          (DigitSet k) 2) :=
  ⟨⟨digit_basis_official k (by omega),
    digit_strong_deletion k (by omega)⟩,
    fun h3 => digit_not_basis_two k h3⟩

end Erdos881Digit
