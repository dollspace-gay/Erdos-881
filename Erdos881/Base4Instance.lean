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

theorem base4_hard_case_instance :
    IsStronglyMinimalExactBasis Base4Set 3 ∧
      ¬ IsExactTupleAsymptoticBasis Base4Set 2 :=
  ⟨⟨base4_basis_three, base4_strong_deletion⟩,
    base4_not_basis_two⟩

end Erdos881Base4
