/-
# The Cantor fixed point, membership half

Sieve-stack completeness of the Cantor world: every non-element is
some owner's moat value.  The owner family is the shifted doubles —
`3^m + h` owns `3^m + 2h`, uniqueness by doubling rigidity — and the
victim equation `v = 2h - c''` is solved by the layer decomposition
`h = layer v`, `c'' = 2·layer v - v`.

This establishes `co-C ⊆ Sieve(C)`: the Cantor set is contained in
and (with the laws' consistency) equals the complement of its own
forest's sieve — the model half of the classification's fixed point.
-/

import Erdos881.CantorCarryRepair
import Erdos881.DisjointRepEngine

namespace Erdos881Cantor

open Erdos881

/-- The Cantor set, as a set. -/
def CSet : Set ℕ := {n | IsCantor n}

/-- Digit window bound in usable form. -/
lemma cantor_small_bound {y m : ℕ} (hy : IsCantor y) (hlt : y < 3 ^ m) :
    2 * y + 1 ≤ 3 ^ m := by
  have h := isCantor_mod_bound hy m
  have hmod : y % 3 ^ m = y := Nat.mod_eq_of_lt hlt
  omega

/-- A number in `[3^m, 2·3^m)` has digit 1 at position `m`. -/
lemma digit_one_of_between {y m : ℕ} (h1 : 3 ^ m ≤ y)
    (h2 : y < 2 * 3 ^ m) : y / 3 ^ m % 3 = 1 := by
  have hq : y / 3 ^ m = 1 := by
    have hp := pow3_pos m
    have hlo : 1 ≤ y / 3 ^ m := (Nat.one_le_div_iff hp).2 h1
    have hhi : y / 3 ^ m < 2 := by
      by_contra hge
      push_neg at hge
      have := Nat.div_mul_le_self y (3 ^ m)
      have h3 : 2 * 3 ^ m ≤ y / 3 ^ m * 3 ^ m :=
        Nat.mul_le_mul_right _ hge
      have h4 : y / 3 ^ m * 3 ^ m ≤ y := Nat.div_mul_le_self y (3 ^ m)
      omega
    omega
  rw [hq]

/-- The doubled layer dominates: `v ≤ 2 · layer v`. -/
lemma le_two_layer (v : ℕ) : v ≤ 2 * layer v := by
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    rcases Nat.eq_zero_or_pos v with h | h
    · subst h
      simp [layer_zero]
    · rw [layer_eq v h]
      have hq : v / 3 < v := Nat.div_lt_self h (by norm_num)
      have h1 := ih (v / 3) hq
      have h2 := Nat.div_add_mod v 3
      have h3 : v % 3 < 3 := Nat.mod_lt _ (by norm_num)
      omega

/-- The layer defect `2 · layer v - v` is a Cantor number. -/
lemma isCantor_layer_defect (v : ℕ) : IsCantor (2 * layer v - v) := by
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro i
    rcases Nat.eq_zero_or_pos v with h | h
    · subst h
      simp [layer_zero, Nat.zero_div]
    · have hq : v / 3 < v := Nat.div_lt_self h (by norm_num)
      have hrec : 2 * layer v - v =
          3 * (2 * layer (v / 3) - v / 3) + (2 * min (v % 3) 1 - v % 3) := by
        have h1 := layer_eq v h
        have h2 := Nat.div_add_mod v 3
        have h3 := le_two_layer (v / 3)
        have h4 : v % 3 < 3 := Nat.mod_lt _ (by norm_num)
        omega
      rcases i with _ | i
      · rw [hrec]
        simp only [pow_zero, Nat.div_one]
        omega
      · rw [hrec]
        have h30 : (3 * (2 * layer (v / 3) - v / 3) +
            (2 * min (v % 3) 1 - v % 3)) / 3
            = 2 * layer (v / 3) - v / 3 := by omega
        have hstep : (3 * (2 * layer (v / 3) - v / 3) +
            (2 * min (v % 3) 1 - v % 3)) / 3 ^ (i + 1)
            = (2 * layer (v / 3) - v / 3) / 3 ^ i := by
          rw [pow_succ, Nat.mul_comm (3 ^ i) 3, ← Nat.div_div_eq_div_mul,
            h30]
        rw [hstep]
        exact ih (v / 3) hq i

/-- **The shifted-doubles ownership family.**  `3^m + h` owns
`3^m + 2h`: big-window inhabitants are `3^m + c''` with `c''` Cantor,
and `2h - c'' ∈ C` forces `c'' = h` by doubling rigidity. -/
theorem shifted_double_owns {h m : ℕ} (hh : IsCantor h)
    (hpos : 0 < h) (hroom : 4 * h + 1 < 3 ^ m) :
    OwnsTarget CSet (3 ^ m + h) (3 ^ m + 2 * h) := by
  refine ⟨by omega, by omega, ?_, ?_⟩
  · show 3 ^ m + 2 * h - (3 ^ m + h) ∈ CSet
    have hval : 3 ^ m + 2 * h - (3 ^ m + h) = h := by omega
    rw [hval]
    exact hh
  · intro y hy hbig hlt hya
    have hyC : IsCantor y := hy
    -- y is in the top half: it must carry the power
    have hyge : 3 ^ m ≤ y := by
      by_contra hsm
      push_neg at hsm
      have := cantor_small_bound hyC hsm
      omega
    have hylt2 : y < 2 * 3 ^ m := by omega
    have hdig : y / 3 ^ m % 3 = 1 := digit_one_of_between hyge hylt2
    -- strip the power: the residue is Cantor
    have hsub := sub_pow_digit hyC hdig
    have hcC : IsCantor (y - 3 ^ m) := by
      intro i
      rw [hsub i]
      by_cases him : i = m
      · rw [if_pos him]; omega
      · rw [if_neg him]; exact hyC i
    set c := y - 3 ^ m with hc
    have hclt : c < 2 * h := by omega
    have hval : 3 ^ m + 2 * h - y = 2 * h - c := by omega
    rw [hval]
    intro hmem
    have hmemC : IsCantor (2 * h - c) := hmem
    have hsum : c + (2 * h - c) = 2 * h := by omega
    obtain ⟨hch, _⟩ := cantor_double_unique hh hcC hmemC hsum
    exact hya (by omega)

/-- **The Cantor sieve is complete on non-elements.**  Every positive
non-element `v` is a moat value: with `h := layer v` and
`c'' := 2h - v`, the owner `3^m + h` of `3^m + 2h` excludes exactly
`v` at the window element `3^m + c''`.  The membership half of the
fixed point `co-C = Sieve(C)`. -/
theorem cantor_sieve_complete {v : ℕ} (hv : ¬IsCantor v) (hv1 : 1 ≤ v) :
    ∃ a t z, OwnsTarget CSet a t ∧ z ∈ CSet ∧
      2 * z > t ∧ z < t ∧ z ≠ a ∧ t - z = v := by
  set h := layer v with hh
  have hhC : IsCantor h := isCantor_layer v
  have hv2h : v ≤ 2 * h := le_two_layer v
  have hpos : 0 < h := by
    by_contra h0
    push_neg at h0
    omega
  set c := 2 * h - v with hcdef
  have hcC : IsCantor c := isCantor_layer_defect v
  have hch : c ≠ h := by
    intro heq
    apply hv
    have hvh : v = h := by omega
    rw [hvh]
    exact hhC
  -- choose the power with room
  set m := 4 * h + 2 with hm
  have hroom : 4 * h + 1 < 3 ^ m := by
    have h1 : m < 3 ^ m := Nat.lt_two_pow_self.trans_le
      (Nat.pow_le_pow_left (by norm_num) m)
    omega
  have hown := shifted_double_owns hhC hpos hroom
  refine ⟨3 ^ m + h, 3 ^ m + 2 * h, 3 ^ m + c, hown, ?_, ?_, ?_, ?_, ?_⟩
  · show IsCantor (3 ^ m + c)
    have hcsm : c < 3 ^ m := by omega
    refine isCantor_add_disjoint (isCantor_pow m) hcC ?_
    intro i
    rcases Nat.lt_or_ge i m with hi | hi
    · left
      have := pow_digit m i
      rw [if_neg (by omega)] at this
      exact this
    · right
      have hlt : c < 3 ^ i := by
        calc c < 3 ^ m := hcsm
          _ ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) hi
      rw [Nat.div_eq_of_lt hlt]
  · omega
  · omega
  · intro heq
    have : c = h := by omega
    exact hch this
  · omega

/-- **THE CANTOR FIXED POINT.**  A positive number is OUTSIDE the
Cantor set exactly when it is some owner''s moat value: the set is
precisely the complement of its own forest''s sieve.
`co-C = Sieve(C)`, as one theorem — the model of the classification:
a universally-owned covering world IS the fixed point of its own
exclusion laws, and the ternary world realizes it. -/
theorem cantor_fixed_point {v : ℕ} (hv1 : 1 ≤ v) :
    (¬IsCantor v) ↔
    ∃ a t z, OwnsTarget CSet a t ∧ z ∈ CSet ∧
      2 * z > t ∧ z < t ∧ z ≠ a ∧ t - z = v := by
  constructor
  · intro hv
    exact cantor_sieve_complete hv hv1
  · rintro ⟨a, t, z, hown, hz, hbig, hlt, hza, hval⟩ hvC
    have := hown.2.2.2 z hz hbig hlt hza
    rw [hval] at this
    exact this hvC

end Erdos881Cantor
