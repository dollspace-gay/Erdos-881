/-
# The general carry menu: arbitrary multiplicity, every order

The theorem that dissolves the adjacent-block wall.  For every
`k ≥ 2`, EVERY `C ≥ 1`, and every scale `a ≥ 3`,

  `C·(k+1)^a  =  Σ_l  (layer (l+1) (C-1) · b³ + ε₂(l)·b² + ε₁(l)·b + 1) · b^(a-3)`

over the `k+1` slots `l`, where `layer t d` is the digit-threshold
layer of `d` (a 1-bit wherever the base-`b` digit is at least `t`)
and the ε-columns supply `k·b² + k·b + (k+1) = b³`.  Every part is a
digit number (`layers` are digit numbers for ANY `d`), every part is
`≡ 1 (mod b)` and exceeds 1 — hence never a power — and the sum
telescopes to `(C-1)·b³ + b³ = C·b³` at scale `a-3`, with no
assumption whatsoever on the digit shape of `C`.

This subsumes `digit_carry_menu` (`C = c ≤ k`) and repairs every
block profile `C·b^a` with three clear columns below it — including
all the adjacent-block shapes that the instance sieves handled with
bespoke constants.
-/

import Erdos881.DigitCarryRepair

namespace Erdos881Digit

open Erdos881

/-- The digit-threshold layer over base `k+1`. -/
def layerK (k t n : ℕ) : ℕ :=
  if h : n = 0 ∨ k = 0 then 0
  else (k + 1) * layerK k t (n / (k + 1)) +
    (if t ≤ n % (k + 1) then 1 else 0)
termination_by n
decreasing_by
  push Not at h
  exact Nat.div_lt_self (by omega) (by omega)

lemma layerK_zero (k t : ℕ) : layerK k t 0 = 0 := by
  rw [layerK]
  simp

lemma layerK_pos_def (k t : ℕ) (hkk : k ≠ 0)
    {n : ℕ} (hn : n ≠ 0) :
    layerK k t n =
      (k + 1) * layerK k t (n / (k + 1)) +
        (if t ≤ n % (k + 1) then 1 else 0) := by
  rw [layerK]
  simp [hn, hkk]

/-- Layers are digit numbers — for every `n`. -/
lemma layerK_isDigit (k t n : ℕ) (hk : 1 ≤ k) :
    IsDigitK k (layerK k t n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [layerK_zero]
      exact isDigitK_zero k
    have hlt : n / (k + 1) < n :=
      Nat.div_lt_self (by omega) (by omega)
    rw [layerK_pos_def k t (by omega) (by omega)]
    exact isDigitK_scale_add hk (ih (n / (k + 1)) hlt)
      (by split_ifs <;> omega)

/-- The first `k` layers reassemble the number (digits are at most
`k`), and the `k+1`-st layer vanishes; summed over `Fin (k+1)` with
threshold `l+1`, the layers give the number back. -/
lemma layerK_sum (k n : ℕ) (hk : 1 ≤ k) :
    (∑ l : Fin (k + 1), layerK k ((l : ℕ) + 1) n) =
      n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [layerK_zero]
    have hlt : n / (k + 1) < n :=
      Nat.div_lt_self (by omega) (by omega)
    have hs := ih (n / (k + 1)) hlt
    have hmod : n % (k + 1) < k + 1 :=
      Nat.mod_lt n (by omega)
    have hdm := Nat.div_add_mod n (k + 1)
    have hexp :
        (∑ l : Fin (k + 1),
          layerK k ((l : ℕ) + 1) n) =
          (k + 1) *
            (∑ l : Fin (k + 1),
              layerK k ((l : ℕ) + 1) (n / (k + 1))) +
            ∑ l : Fin (k + 1),
              (if (l : ℕ) + 1 ≤ n % (k + 1) then 1
                else 0) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro l _
      exact layerK_pos_def k ((l : ℕ) + 1) (by omega)
        (by omega)
    have hbits :
        (∑ l : Fin (k + 1),
          (if (l : ℕ) + 1 ≤ n % (k + 1) then 1
            else 0)) = n % (k + 1) := by
      have hb := sum_bits (k + 1) (n % (k + 1))
        (by omega)
      calc (∑ l : Fin (k + 1),
            (if (l : ℕ) + 1 ≤ n % (k + 1) then 1
              else 0))
          = (∑ l : Fin (k + 1),
              (if (l : ℕ) < n % (k + 1) then 1
                else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro l _
            by_cases h : (l : ℕ) < n % (k + 1)
            · rw [if_pos h, if_pos (by omega)]
            · rw [if_neg h, if_neg (by omega)]
        _ = n % (k + 1) := hb
    rw [hexp, hs, hbits]
    omega

/-- The general bracket at slot `l`. -/
def genBracket (k C l : ℕ) : ℕ :=
  layerK k (l + 1) (C - 1) * (k + 1) ^ 3 +
    (if l < k then (k + 1) ^ 2 else 0) +
    (if 1 ≤ l then (k + 1) else 0) + 1

lemma genBracket_digit {k C l : ℕ} (hk : 1 ≤ k) :
    IsDigitK k (genBracket k C l) := by
  have h :
      genBracket k C l =
        (k + 1) *
          ((k + 1) *
            ((k + 1) * layerK k (l + 1) (C - 1) +
              (if l < k then 1 else 0)) +
            (if 1 ≤ l then 1 else 0)) + 1 := by
    unfold genBracket
    split_ifs <;> ring
  rw [h]
  refine isDigitK_scale_add hk ?_ (by omega)
  refine isDigitK_scale_add hk ?_
    (by split_ifs <;> omega)
  refine isDigitK_scale_add hk ?_
    (by split_ifs <;> omega)
  exact layerK_isDigit k (l + 1) (C - 1) hk

lemma genBracket_mod {k C l : ℕ} (hk : 1 ≤ k) :
    genBracket k C l % (k + 1) = 1 := by
  have h :
      genBracket k C l =
        (k + 1) *
          ((k + 1) ^ 2 * layerK k (l + 1) (C - 1) +
            (k + 1) * (if l < k then 1 else 0) +
            (if 1 ≤ l then 1 else 0)) + 1 := by
    unfold genBracket
    split_ifs <;> ring
  rw [h, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (by omega)

lemma genBracket_big {k C : ℕ} (hk : 1 ≤ k) (l : ℕ)
    (hl : l ≤ k) :
    1 < genBracket k C l := by
  unfold genBracket
  have h2 : (1 : ℕ) ≤ (k + 1) ^ 2 :=
    Nat.one_le_pow _ _ (by omega)
  rcases Nat.eq_zero_or_pos l with rfl | hpos
  · rw [if_pos (by omega : (0 : ℕ) < k)]
    omega
  · split_ifs <;> omega

/-- **The general carry menu**: for every `k ≥ 2`, every `C ≥ 1`,
every `a ≥ 3`, the block `C·(k+1)^a` is a sum of `k+1` digit-{0,1}
parts, none a pure power — with no assumption on the digit shape of
`C`. -/
theorem digit_general_menu (k C a : ℕ) (hk : 2 ≤ k)
    (hC : 1 ≤ C) (ha : 3 ≤ a) :
    ∃ v : Fin (k + 1) → ℕ,
      (∀ l, IsDigitK k (v l)) ∧
      (∀ l j, v l ≠ (k + 1) ^ j) ∧
      (∑ l, v l) = C * (k + 1) ^ a := by
  refine
    ⟨fun l => genBracket k C (l : ℕ) *
      (k + 1) ^ (a - 3), ?_, ?_, ?_⟩
  · intro l
    have h := isDigitK_shift (k := k) (by omega)
      (a - 3) (genBracket_digit (k := k) (C := C)
        (l := (l : ℕ)) (by omega))
    rwa [Nat.mul_comm] at h
  · intro l j
    refine not_pure_of_scaledK (by omega) ?_ j
    intro t
    exact fun hcon =>
      (not_pure_of_mod
        (genBracket_mod (k := k) (C := C)
          (l := (l : ℕ)) (by omega))
        (genBracket_big (by omega) (l : ℕ)
          (by omega)) t) hcon
  · have hsum :
        (∑ l : Fin (k + 1),
          genBracket k C (l : ℕ)) =
          C * (k + 1) ^ 3 := by
      unfold genBracket
      have hlay :
          (∑ l : Fin (k + 1),
            layerK k ((l : ℕ) + 1) (C - 1) *
              (k + 1) ^ 3) =
            (C - 1) * (k + 1) ^ 3 := by
        rw [← Finset.sum_mul,
          layerK_sum k (C - 1) (by omega)]
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
                (if (l : ℕ) < k then 1 else 0) *
                  (k + 1) ^ 2) := by
              refine Finset.sum_congr rfl ?_
              intro l _
              split_ifs <;> ring
          _ = (∑ l : Fin (k + 1),
                (if (l : ℕ) < k then 1 else 0)) *
                (k + 1) ^ 2 := by
              rw [Finset.sum_mul]
          _ = k * (k + 1) ^ 2 := by rw [hb]
      have h1 :
          (∑ l : Fin (k + 1),
            (if 1 ≤ (l : ℕ) then (k + 1) else 0)) =
            k * (k + 1) := by
        have hone :
            (∑ l : Fin (k + 1),
              (if (l : ℕ) < 1 then (k + 1)
                else 0)) = k + 1 := by
          have hb := sum_bits (k + 1) 1 (by omega)
          calc (∑ l : Fin (k + 1),
                (if (l : ℕ) < 1 then (k + 1)
                  else 0))
              = (∑ l : Fin (k + 1),
                  (if (l : ℕ) < 1 then 1 else 0) *
                    (k + 1)) := by
                refine Finset.sum_congr rfl ?_
                intro l _
                split_ifs <;> ring
            _ = (∑ l : Fin (k + 1),
                  (if (l : ℕ) < 1 then 1
                    else 0)) * (k + 1) := by
                rw [Finset.sum_mul]
            _ = 1 * (k + 1) := by rw [hb]
            _ = k + 1 := by ring
        have hsplit :
            ∀ l : Fin (k + 1),
              (if 1 ≤ (l : ℕ) then (k + 1)
                else 0) +
                (if (l : ℕ) < 1 then (k + 1)
                  else 0) = k + 1 := by
          intro l
          by_cases h : 1 ≤ (l : ℕ)
          · rw [if_pos h, if_neg (by omega)]
          · rw [if_neg h, if_pos (by omega)]
            omega
        have htot :
            (∑ l : Fin (k + 1),
              ((if 1 ≤ (l : ℕ) then (k + 1)
                else 0) +
                (if (l : ℕ) < 1 then (k + 1)
                  else 0))) =
              (k + 1) * (k + 1) := by
          rw [Finset.sum_congr rfl
            (fun l _ => hsplit l)]
          simp [Finset.sum_const, Finset.card_univ,
            smul_eq_mul]
        rw [Finset.sum_add_distrib] at htot
        rw [hone] at htot
        have : (k + 1) * (k + 1) =
            k * (k + 1) + (k + 1) := by ring
        omega
      have hconst :
          (∑ _l : Fin (k + 1), (1 : ℕ)) = k + 1 := by
        simp
      calc (∑ l : Fin (k + 1),
            (layerK k ((l : ℕ) + 1) (C - 1) *
                (k + 1) ^ 3 +
              (if (l : ℕ) < k then
                (k + 1) ^ 2 else 0) +
              (if 1 ≤ (l : ℕ) then (k + 1)
                else 0) + 1))
          = (∑ l : Fin (k + 1),
              layerK k ((l : ℕ) + 1) (C - 1) *
                (k + 1) ^ 3) +
            (∑ l : Fin (k + 1),
              (if (l : ℕ) < k then
                (k + 1) ^ 2 else 0)) +
            (∑ l : Fin (k + 1),
              (if 1 ≤ (l : ℕ) then (k + 1)
                else 0)) +
            (∑ _l : Fin (k + 1), (1 : ℕ)) := by
            rw [Finset.sum_add_distrib,
              Finset.sum_add_distrib,
              Finset.sum_add_distrib]
        _ = (C - 1) * (k + 1) ^ 3 +
              k * (k + 1) ^ 2 + k * (k + 1) +
              (k + 1) := by
            rw [hlay, h2, h1, hconst]
        _ = C * (k + 1) ^ 3 := by
            have hce : C - 1 + 1 = C := by omega
            have hexp :
                ((C - 1) + 1) * (k + 1) ^ 3 =
                  (C - 1) * (k + 1) ^ 3 +
                    k * (k + 1) ^ 2 + k * (k + 1) +
                    (k + 1) := by
              ring
            calc (C - 1) * (k + 1) ^ 3 +
                  k * (k + 1) ^ 2 + k * (k + 1) +
                  (k + 1)
                = ((C - 1) + 1) * (k + 1) ^ 3 :=
                  hexp.symm
              _ = C * (k + 1) ^ 3 := by rw [hce]
    calc (∑ l : Fin (k + 1),
          genBracket k C (l : ℕ) *
            (k + 1) ^ (a - 3))
        = (∑ l : Fin (k + 1),
            genBracket k C (l : ℕ)) *
            (k + 1) ^ (a - 3) := by
          rw [Finset.sum_mul]
      _ = C * (k + 1) ^ 3 * (k + 1) ^ (a - 3) := by
          rw [hsum]
      _ = C * (k + 1) ^ a := by
          rw [Nat.mul_assoc, ← pow_add]
          congr 2
          omega

/-- **Every multiple of `b³` splits after the deletion** — the
sieve on the full lattice `b³·ℕ`, for every order in one stroke. -/
theorem digit_deletion_covers_multiples
    (k C : ℕ) (hk : 2 ≤ k) (hC : 1 ≤ C) :
    ∃ v : Fin (k + 1) → ℕ,
      (∀ l, v l ∈ DigitSet k \ DigitPowers k) ∧
      (∑ l, v l) = C * (k + 1) ^ 3 := by
  obtain ⟨v, hv, hnp, hsum⟩ :=
    digit_general_menu k C 3 hk hC (le_refl 3)
  refine ⟨v, ?_, hsum⟩
  intro l
  exact ⟨hv l, fun hmem => by
    obtain ⟨m, hm⟩ := hmem
    exact hnp l m hm⟩

end Erdos881Digit
