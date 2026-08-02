/-
# The uniform carry repair: every base, every order

The creative core of the uniform deletion theorem.  For every
`k ≥ 2`, every multiplicity `1 ≤ c ≤ k`, and every scale `a ≥ 3`,
the target `c·(k+1)^a` splits into `k+1` digit-{0,1} parts, none a
pure power (`digit_carry_menu`).  The construction is one closed
form: with `b := k+1`,

`c·b^a = [(c-1)·(b³+b²+b+1) + (k-c)·(b²+b+1) + (b²+1) + (b+1)]·b^(a-3)`,

whose bottom column is full — the uniform carry `1+⋯+1 = b` over
`k+1` slots that no `k` digit numbers can imitate.  Non-purity is
uniform and free: every part is `≡ 1 (mod b)` and exceeds 1, and no
power of `b` beyond `b^0 = 1` has that residue.

`digit_demonstrator` assembles the uniform Erdős 881 conclusion
pattern at the casualties: for every `k`, deleting the pure powers
kills the diagonal `k·(k+1)^m` at order `k` completely (diagonal
rigidity), while order `k+1` repairs it with `k+1` non-power parts.
-/

import Erdos881.DigitInstance

namespace Erdos881Digit

open Erdos881

/-- The uniform non-power test: residue 1 above 1 is never a power. -/
lemma not_pure_of_mod {k x : ℕ}
    (h1 : x % (k + 1) = 1) (h2 : 1 < x) :
    ∀ j, x ≠ (k + 1) ^ j := by
  intro j hx
  cases j with
  | zero =>
    rw [hx] at h2
    simp at h2
  | succ j =>
    rw [hx, pow_succ, Nat.mul_mod_left] at h1
    omega

/-- Digit numbers absorb a fresh low digit. -/
lemma isDigitK_scale_add {k x r : ℕ} (hk : 1 ≤ k)
    (hx : IsDigitK k x) (hr : r ≤ 1) :
    IsDigitK k ((k + 1) * x + r) := by
  intro i
  cases i with
  | zero =>
    simp only [pow_zero, Nat.div_one]
    rw [Nat.mul_add_mod]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact hr
  | succ i =>
    rw [div_pow_succ]
    have hq : ((k + 1) * x + r) / (k + 1) = x := by
      rw [Nat.mul_add_div (by omega)]
      rw [Nat.div_eq_of_lt (by omega)]
      omega
    rw [hq]
    exact hx i

/-- Tiny values are digit numbers. -/
lemma isDigitK_of_le_one {k x : ℕ} (hk : 1 ≤ k)
    (hx : x ≤ 1) :
    IsDigitK k x := by
  intro i
  cases i with
  | zero =>
    simp only [pow_zero, Nat.div_one]
    exact le_trans (Nat.mod_le x (k + 1)) hx
  | succ i =>
    have hlt : x < (k + 1) ^ (i + 1) := by
      have h1 : (2 : ℕ) ≤ (k + 1) ^ (i + 1) := by
        calc (2 : ℕ) ≤ k + 1 := by omega
          _ = (k + 1) ^ 1 := by ring
          _ ≤ (k + 1) ^ (i + 1) :=
            Nat.pow_le_pow_right (by omega) (by omega)
      omega
    rw [Nat.div_eq_of_lt hlt]
    simp

/-- Digit-shift: multiplying by a power shifts digits up. -/
lemma isDigitK_shift {k n : ℕ} (hk : 1 ≤ k) (m : ℕ)
    (hn : IsDigitK k n) :
    IsDigitK k ((k + 1) ^ m * n) := by
  induction m with
  | zero =>
    simpa using hn
  | succ m ih =>
    have h : (k + 1) ^ (m + 1) * n =
        (k + 1) * ((k + 1) ^ m * n) := by
      rw [pow_succ]
      ring
    rw [h]
    simpa using isDigitK_scale_add hk ih
      (by omega : (0 : ℕ) ≤ 1)

/-- Scaled non-purity. -/
lemma not_pure_of_scaledK {k c m : ℕ} (hk : 1 ≤ k)
    (hc : ∀ t, c ≠ (k + 1) ^ t) (j : ℕ) :
    c * (k + 1) ^ m ≠ (k + 1) ^ j := by
  intro h
  rcases Nat.lt_or_ge j m with hjm | hmj
  · have hlt : (k + 1) ^ j < (k + 1) ^ m :=
      Nat.pow_lt_pow_right (by omega) hjm
    rcases Nat.eq_zero_or_pos c with rfl | hcpos
    · have := basePow_pos k j
      omega
    · have hle : (k + 1) ^ m ≤ c * (k + 1) ^ m :=
        Nat.le_mul_of_pos_left _ hcpos
      omega
  · have hsplit : (k + 1) ^ j =
        (k + 1) ^ (j - m) * (k + 1) ^ m := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit] at h
    have hcancel : c = (k + 1) ^ (j - m) :=
      Nat.eq_of_mul_eq_mul_right (basePow_pos k m) h
    exact hc (j - m) hcancel

/-- The menu bracket at slot `l`: which of the three upper columns
the slot receives. -/
def menuBracket (k c : ℕ) (l : ℕ) : ℕ :=
  (if l < c - 1 then (k + 1) ^ 3 else 0) +
    (if l < k then (k + 1) ^ 2 else 0) +
    (if l < k - 1 ∨ l = k then (k + 1) else 0) + 1

lemma menuBracket_digit {k c l : ℕ} (hk : 1 ≤ k) :
    IsDigitK k (menuBracket k c l) := by
  have h :
      menuBracket k c l =
        (k + 1) *
          ((k + 1) *
            ((k + 1) *
              (if l < c - 1 then 1 else 0) +
              (if l < k then 1 else 0)) +
            (if l < k - 1 ∨ l = k then 1 else 0)) +
          1 := by
    unfold menuBracket
    split_ifs <;> ring
  rw [h]
  refine isDigitK_scale_add hk ?_ (by omega)
  refine isDigitK_scale_add hk ?_
    (by split_ifs <;> omega)
  refine isDigitK_scale_add hk ?_
    (by split_ifs <;> omega)
  exact isDigitK_of_le_one hk (by split_ifs <;> omega)

lemma menuBracket_mod {k c l : ℕ} (hk : 1 ≤ k) :
    menuBracket k c l % (k + 1) = 1 := by
  have h :
      menuBracket k c l =
        (k + 1) *
          ((k + 1) ^ 2 *
              (if l < c - 1 then 1 else 0) +
            (k + 1) * (if l < k then 1 else 0) +
            (if l < k - 1 ∨ l = k then 1 else 0)) +
          1 := by
    unfold menuBracket
    split_ifs <;> ring
  rw [h, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (by omega)

lemma menuBracket_big {k c : ℕ} (hk : 1 ≤ k)
    (l : ℕ) (hl : l ≤ k) :
    1 < menuBracket k c l := by
  unfold menuBracket
  rcases Nat.lt_or_ge l k with hlk | hlk
  · have h2 : (1 : ℕ) ≤ (k + 1) ^ 2 :=
      Nat.one_le_pow _ _ (by omega)
    split_ifs <;> omega
  · have hleq : l = k := by omega
    have hor : l < k - 1 ∨ l = k := Or.inr hleq
    rw [if_pos hor]
    split_ifs <;> omega

/-- **The uniform carry menu**: for every `k ≥ 2`, `1 ≤ c ≤ k`,
`a ≥ 3`, the target `c·(k+1)^a` is a sum of `k+1` digit-{0,1}
parts, none a pure power. -/
theorem digit_carry_menu (k c a : ℕ) (hk : 2 ≤ k)
    (hc : 1 ≤ c) (hck : c ≤ k) (ha : 3 ≤ a) :
    ∃ v : Fin (k + 1) → ℕ,
      (∀ l, IsDigitK k (v l)) ∧
      (∀ l j, v l ≠ (k + 1) ^ j) ∧
      (∑ l, v l) = c * (k + 1) ^ a := by
  refine
    ⟨fun l => menuBracket k c (l : ℕ) *
      (k + 1) ^ (a - 3), ?_, ?_, ?_⟩
  · intro l
    have h := isDigitK_shift (k := k) (by omega)
      (a - 3)
      (menuBracket_digit (k := k) (c := c)
        (l := (l : ℕ)) (by omega))
    rwa [Nat.mul_comm] at h
  · intro l j
    refine not_pure_of_scaledK (by omega) ?_ j
    intro t
    exact fun hcon =>
      (not_pure_of_mod
        (menuBracket_mod (k := k) (c := c)
          (l := (l : ℕ)) (by omega))
        (menuBracket_big (by omega) (l : ℕ)
          (by omega)) t) hcon
  · have hsum :
        (∑ l : Fin (k + 1),
          menuBracket k c (l : ℕ)) =
          c * (k + 1) ^ 3 := by
      unfold menuBracket
      have h3 :
          (∑ l : Fin (k + 1),
            (if (l : ℕ) < c - 1 then
              (k + 1) ^ 3 else 0)) =
            (c - 1) * (k + 1) ^ 3 := by
        have hb := sum_bits (k + 1) (c - 1)
          (by omega)
        calc (∑ l : Fin (k + 1),
              (if (l : ℕ) < c - 1 then
                (k + 1) ^ 3 else 0))
            = (∑ l : Fin (k + 1),
                (if (l : ℕ) < c - 1 then 1
                  else 0) * (k + 1) ^ 3) := by
              refine Finset.sum_congr rfl ?_
              intro l _
              split_ifs <;> ring
          _ = (∑ l : Fin (k + 1),
                (if (l : ℕ) < c - 1 then 1
                  else 0)) * (k + 1) ^ 3 := by
              rw [Finset.sum_mul]
          _ = (c - 1) * (k + 1) ^ 3 := by
              rw [hb]
      have h2 :
          (∑ l : Fin (k + 1),
            (if (l : ℕ) < k then
              (k + 1) ^ 2 else 0)) =
            k * (k + 1) ^ 2 := by
        have hb := sum_bits (k + 1) k (by omega)
        calc (∑ l : Fin (k + 1),
              (if (l : ℕ) < k then
                (k + 1) ^ 2 else 0))
            = (∑ l : Fin (k + 1),
                (if (l : ℕ) < k then 1
                  else 0) * (k + 1) ^ 2) := by
              refine Finset.sum_congr rfl ?_
              intro l _
              split_ifs <;> ring
          _ = (∑ l : Fin (k + 1),
                (if (l : ℕ) < k then 1 else 0)) *
                (k + 1) ^ 2 := by
              rw [Finset.sum_mul]
          _ = k * (k + 1) ^ 2 := by
              rw [hb]
      have h1 :
          (∑ l : Fin (k + 1),
            (if (l : ℕ) < k - 1 ∨ (l : ℕ) = k then
              (k + 1) else 0)) =
            k * (k + 1) := by
        have hsplit :
            ∀ l : Fin (k + 1),
              (if (l : ℕ) < k - 1 ∨ (l : ℕ) = k then
                (k + 1) else 0) =
                (if (l : ℕ) < k - 1 then (k + 1)
                  else 0) +
                (if (l : ℕ) = k then (k + 1)
                  else 0) := by
          intro l
          by_cases hp : (l : ℕ) < k - 1
          · rw [if_pos (Or.inl hp), if_pos hp,
              if_neg (by omega)]
          · by_cases hq : (l : ℕ) = k
            · rw [if_pos (Or.inr hq), if_neg hp,
                if_pos hq]
              omega
            · rw [if_neg (by tauto), if_neg hp,
                if_neg hq]
        rw [Finset.sum_congr rfl
          (fun l _ => hsplit l),
          Finset.sum_add_distrib]
        have ha1 :
            (∑ l : Fin (k + 1),
              (if (l : ℕ) < k - 1 then (k + 1)
                else 0)) = (k - 1) * (k + 1) := by
          have hb := sum_bits (k + 1) (k - 1)
            (by omega)
          calc (∑ l : Fin (k + 1),
                (if (l : ℕ) < k - 1 then (k + 1)
                  else 0))
              = (∑ l : Fin (k + 1),
                  (if (l : ℕ) < k - 1 then 1
                    else 0) * (k + 1)) := by
                refine Finset.sum_congr rfl ?_
                intro l _
                split_ifs <;> ring
            _ = (∑ l : Fin (k + 1),
                  (if (l : ℕ) < k - 1 then 1
                    else 0)) * (k + 1) := by
                rw [Finset.sum_mul]
            _ = (k - 1) * (k + 1) := by
                rw [hb]
        have ha2 :
            (∑ l : Fin (k + 1),
              (if (l : ℕ) = k then (k + 1)
                else 0)) = k + 1 := by
          have hcongr :
              ∀ l : Fin (k + 1),
                (if (l : ℕ) = k then (k + 1)
                  else 0) =
                  (if l =
                    (⟨k, by omega⟩ : Fin (k + 1))
                    then (k + 1) else 0) := by
            intro l
            by_cases h : (l : ℕ) = k
            · rw [if_pos h, if_pos (Fin.ext h)]
            · rw [if_neg h,
                if_neg (fun hcon => h (by rw [hcon]))]
          rw [Finset.sum_congr rfl
            (fun l _ => hcongr l)]
          rw [Finset.sum_ite_eq' Finset.univ
            (⟨k, by omega⟩ : Fin (k + 1))
            (fun _ => k + 1)]
          simp
        rw [ha1, ha2]
        have hke : k - 1 + 1 = k := by omega
        calc (k - 1) * (k + 1) + (k + 1)
            = ((k - 1) + 1) * (k + 1) := by ring
          _ = k * (k + 1) := by rw [hke]
      have hconst :
          (∑ _l : Fin (k + 1), (1 : ℕ)) = k + 1 := by
        simp
      calc (∑ l : Fin (k + 1),
            ((if (l : ℕ) < c - 1 then
              (k + 1) ^ 3 else 0) +
              (if (l : ℕ) < k then
                (k + 1) ^ 2 else 0) +
              (if (l : ℕ) < k - 1 ∨ (l : ℕ) = k then
                (k + 1) else 0) + 1))
          = (∑ l : Fin (k + 1),
              (if (l : ℕ) < c - 1 then
                (k + 1) ^ 3 else 0)) +
            (∑ l : Fin (k + 1),
              (if (l : ℕ) < k then
                (k + 1) ^ 2 else 0)) +
            (∑ l : Fin (k + 1),
              (if (l : ℕ) < k - 1 ∨ (l : ℕ) = k then
                (k + 1) else 0)) +
            (∑ _l : Fin (k + 1), (1 : ℕ)) := by
            rw [Finset.sum_add_distrib,
              Finset.sum_add_distrib,
              Finset.sum_add_distrib]
        _ = (c - 1) * (k + 1) ^ 3 +
              k * (k + 1) ^ 2 + k * (k + 1) +
              (k + 1) := by
            rw [h3, h2, h1, hconst]
        _ = c * (k + 1) ^ 3 := by
            have hce : c - 1 + 1 = c := by omega
            have hexp :
                ((c - 1) + 1) * (k + 1) ^ 3 =
                  (c - 1) * (k + 1) ^ 3 +
                    k * (k + 1) ^ 2 + k * (k + 1) +
                    (k + 1) := by
              ring
            calc (c - 1) * (k + 1) ^ 3 +
                  k * (k + 1) ^ 2 + k * (k + 1) +
                  (k + 1)
                = ((c - 1) + 1) * (k + 1) ^ 3 :=
                  hexp.symm
              _ = c * (k + 1) ^ 3 := by rw [hce]
    calc (∑ l : Fin (k + 1),
          menuBracket k c (l : ℕ) *
            (k + 1) ^ (a - 3))
        = (∑ l : Fin (k + 1),
            menuBracket k c (l : ℕ)) *
            (k + 1) ^ (a - 3) := by
          rw [Finset.sum_mul]
      _ = c * (k + 1) ^ 3 * (k + 1) ^ (a - 3) := by
          rw [hsum]
      _ = c * (k + 1) ^ a := by
          rw [Nat.mul_assoc, ← pow_add]
          congr 2
          omega

/-- **The uniform demonstrator.**  For every `k ≥ 2` and every scale
`m ≥ 3`, deleting the pure powers kills the diagonal `k·(k+1)^m` at
order `k` COMPLETELY — every order-`k` digit representation is the
all-power diagonal — while order `k+1` repairs it with `k+1` digit
parts, none a power.  The Erdős 881 conclusion pattern at the
casualties, at every order in one stroke. -/
theorem digit_demonstrator (k m : ℕ) (hk : 2 ≤ k)
    (hm : 3 ≤ m) :
    (∀ v : Fin k → ℕ, (∀ l, IsDigitK k (v l)) →
      (∑ l, v l) = k * (k + 1) ^ m →
      ∀ l, v l = (k + 1) ^ m) ∧
    ∃ v : Fin (k + 1) → ℕ,
      (∀ l, IsDigitK k (v l)) ∧
      (∀ l j, v l ≠ (k + 1) ^ j) ∧
      (∑ l, v l) = k * (k + 1) ^ m := by
  constructor
  · intro v hv hsum
    exact digit_diag_rigid (by omega)
      (isDigitK_pow k m (by omega)) v hv hsum
  · exact digit_carry_menu k k m hk (by omega)
      (le_refl k) hm

end Erdos881Digit
