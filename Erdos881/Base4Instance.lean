/-
# The base-4 instance: the hard case is inhabited (Erdős 881, k = 3)

The base-4 digit-{0,1} set `Base4Set` is the order-3 analogue of the
verified Cantor instance (`CantorInstance.lean`, base 3 / order 2):

* it is an exact asymptotic basis of order 3 with threshold 0 — three
  digit-{0,1} numbers add without carries (digit sums ≤ 3 < 4), so
  every `n` splits digit by digit;
* it is NOT an exact basis of order 2 — two digit-{0,1} numbers also
  never carry, so their sums have digits ≤ 2 and the targets `3·4^m`
  are missed cofinally;
* it is strongly minimal at order 3: the target `3b` has digits
  `{0,3}`, digit 3 puts a 1 in all three summands, so `(b, b, b)` is
  the UNIQUE representation and deleting any infinite `B` destroys
  the cofinal targets `{3b : b ∈ B}`.

Together: `base4_hard_case_instance` shows the hard case of the
general-order campaign — `k ≥ 3`, strongly minimal exact order-`k`
basis, not an exact order-2 basis — is formally non-empty.  The
2026-08-02 laboratory (`scripts/probe_base4_instance.py`) verified all
of this numerically and further measured that deleting the pure powers
`{4^j}` leaves an exact order-4 basis with threshold 54; that
carry-repair half (the `CantorCarryRepair` analogue one order up) is
the remaining formal target of the positive side.
-/

import Erdos881.AdditiveSupports

namespace Erdos881Base4

open Erdos881

/-- Base-4 digits all ≤ 1. -/
def IsBase4 (n : ℕ) : Prop := ∀ i, n / 4 ^ i % 4 ≤ 1

/-- The base-4 basis as a set. -/
def Base4Set : Set ℕ := {n | IsBase4 n}

lemma isBase4_zero : IsBase4 0 := by
  intro i
  simp [Nat.zero_div]

lemma pow4_pos (i : ℕ) : 0 < 4 ^ i := by positivity

/-- Strip the lowest digit. -/
lemma isBase4_div4 {a : ℕ} (ha : IsBase4 a) :
    IsBase4 (a / 4) := by
  intro i
  have hsplit : a / 4 / 4 ^ i = a / 4 ^ (i + 1) := by
    rw [Nat.div_div_eq_div_mul, ← pow_succ']
  rw [hsplit]
  exact ha (i + 1)

/-- Attach a fresh low digit `r ≤ 1`. -/
lemma isBase4_scale_add {a r : ℕ} (ha : IsBase4 a)
    (hr : r ≤ 1) :
    IsBase4 (4 * a + r) := by
  intro i
  have h4 : (4 * a + r) / 4 = a := by
    rw [Nat.mul_add_div (by norm_num)]
    omega
  cases i with
  | zero =>
    simp only [pow_zero, Nat.div_one]
    rw [Nat.mul_add_mod]
    omega
  | succ i =>
    have hsplit :
        (4 * a + r) / 4 ^ (i + 1) =
          (4 * a + r) / 4 / 4 ^ i := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ']
    rw [hsplit, h4]
    exact ha i

/-- **Order 3 covers everything, threshold 0.**  Split each base-4
digit `d ≤ 3` into three bits. -/
theorem base4_triple_basis (n : ℕ) :
    ∃ a b c, IsBase4 a ∧ IsBase4 b ∧ IsBase4 c ∧
      a + b + c = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact ⟨0, 0, 0, isBase4_zero, isBase4_zero,
        isBase4_zero, rfl⟩
    obtain ⟨a', b', c', ha', hb', hc', hsum'⟩ :=
      ih (n / 4) (Nat.div_lt_self hpos (by norm_num))
    have hr : n % 4 < 4 := Nat.mod_lt n (by norm_num)
    refine
      ⟨4 * a' + min (n % 4) 1,
        4 * b' + min (n % 4 - 1) 1,
        4 * c' + min (n % 4 - 2) 1,
        isBase4_scale_add ha' (Nat.min_le_right _ _),
        isBase4_scale_add hb' (Nat.min_le_right _ _),
        isBase4_scale_add hc' (Nat.min_le_right _ _),
        ?_⟩
    have hdm := Nat.div_add_mod n 4
    omega

/-- **Order 2 misses `3·4^m`.**  Two digit-{0,1} numbers never carry,
so their sums have base-4 digits at most 2. -/
theorem base4_pair_miss (m : ℕ) :
    ¬∃ a b, IsBase4 a ∧ IsBase4 b ∧
      a + b = 3 * 4 ^ m := by
  induction m with
  | zero =>
    rintro ⟨a, b, ha, hb, hab⟩
    have ha0 := ha 0
    have hb0 := hb 0
    simp only [pow_zero, Nat.div_one] at ha0 hb0
    simp only [pow_zero, mul_one] at hab
    omega
  | succ m ih =>
    rintro ⟨a, b, ha, hb, hab⟩
    have ha0 := ha 0
    have hb0 := hb 0
    simp only [pow_zero, Nat.div_one] at ha0 hb0
    have hab' : a + b = 12 * 4 ^ m := by
      rw [hab, pow_succ]
      ring
    refine ih ⟨a / 4, b / 4, isBase4_div4 ha,
      isBase4_div4 hb, ?_⟩
    omega

/-- **The diagonal is rigid.**  Three digit-{0,1} numbers summing to
`3b` (digits `{0,3}`) are all equal to `b`: digit 3 needs a 1 from
every summand, digit 0 needs a 0 from every summand, and order-3
addition never carries. -/
theorem base4_triple_of_three_mul :
    ∀ b, IsBase4 b → ∀ x y z,
      IsBase4 x → IsBase4 y → IsBase4 z →
      x + y + z = 3 * b →
      x = b ∧ y = b ∧ z = b := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hb x y z hx hy hz hsum
    rcases Nat.eq_zero_or_pos b with rfl | hbpos
    · omega
    have hx0 := hx 0
    have hy0 := hy 0
    have hz0 := hz 0
    have hb0 := hb 0
    simp only [pow_zero, Nat.div_one] at hx0 hy0 hz0 hb0
    have h1 : (x + y + z) % 4 = (3 * b) % 4 := by
      rw [hsum]
    have hkey :
        x % 4 + y % 4 + z % 4 = 3 * (b % 4) := by
      omega
    have hdiv :
        x / 4 + y / 4 + z / 4 = 3 * (b / 4) := by
      omega
    obtain ⟨hx4, hy4, hz4⟩ :=
      ih (b / 4)
        (Nat.div_lt_self hbpos (by norm_num))
        (isBase4_div4 hb) (x / 4) (y / 4) (z / 4)
        (isBase4_div4 hx) (isBase4_div4 hy)
        (isBase4_div4 hz) hdiv
    omega

/-- The base-4 set is an exact asymptotic basis of order 3 (threshold
0), in the campaign's official predicate. -/
theorem base4_basis_three :
    IsExactTupleAsymptoticBasis Base4Set 3 := by
  refine ⟨0, fun n _ => ?_⟩
  obtain ⟨a, b, c, ha, hb, hc, habc⟩ :=
    base4_triple_basis n
  refine ⟨![a, b, c], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact hc
  · simpa [Fin.sum_univ_three] using habc

/-- The base-4 set is NOT an exact basis of order 2: the targets
`3·4^m` are missed cofinally. -/
theorem base4_not_basis_two :
    ¬ IsExactTupleAsymptoticBasis Base4Set 2 := by
  rintro ⟨N, hN⟩
  have hNlt : N < 3 * 4 ^ N := by
    have h1 : N < 4 ^ N :=
      Nat.lt_pow_self (by norm_num)
    have h2 : 4 ^ N ≤ 3 * 4 ^ N := by omega
    omega
  obtain ⟨v, hvmem, hvsum⟩ :=
    hN (3 * 4 ^ N) (by omega)
  exact
    base4_pair_miss N
      ⟨v 0, v 1, hvmem 0, hvmem 1, by
        simpa [Fin.sum_univ_two] using hvsum⟩

/-- Strong minimality at order 3: deleting any infinite `B` destroys
every diagonal target `3b`, `b ∈ B`, cofinally — `(b, b, b)` is the
unique representation, so its support `{b}` meets `B`. -/
theorem base4_strong_deletion :
    StrongInfiniteDeletion
      (additiveSupportFamily Base4Set 3) Base4Set := by
  intro B hBsub hBinf N
  obtain ⟨b, hbB, hNb⟩ := hBinf.exists_gt N
  refine ⟨3 * b, by omega, ?_⟩
  intro E hE
  obtain ⟨w, hwA, hwsum, hEw⟩ :=
    mem_additiveSupportFamily_iff.mp hE
  have hsum3 :
      (w 0).1 + (w 1).1 + (w 2).1 = 3 * b := by
    simpa [Fin.sum_univ_three] using hwsum
  have hbB4 : IsBase4 b := hBsub hbB
  obtain ⟨hxb, _hyb, _hzb⟩ :=
    base4_triple_of_three_mul b hbB4
      ((w 0).1) ((w 1).1) ((w 2).1)
      (hwA 0) (hwA 1) (hwA 2) hsum3
  rw [Set.not_disjoint_iff]
  refine ⟨b, ?_, hbB⟩
  rw [← hEw]
  exact
    Finset.mem_coe.mpr
      (mem_tupleSupport_iff.mpr ⟨0, hxb⟩)

/-- **The hard case is inhabited.**  `Base4Set` is a strongly minimal
exact order-3 basis that is not an exact order-2 basis — a verified
member of the exact hypothesis class of the open `k ≥ 3` obligation. -/
theorem base4_hard_case_instance :
    IsStronglyMinimalExactBasis Base4Set 3 ∧
      ¬ IsExactTupleAsymptoticBasis Base4Set 2 :=
  ⟨⟨base4_basis_three, base4_strong_deletion⟩,
    base4_not_basis_two⟩

end Erdos881Base4
