import Erdos881.GeneralOrder

/-!
# The base-`(h + 1)` digit laboratory

For `h ≥ 1`, let `A_h` consist of the natural numbers having a finite
base-`(h + 1)` expansion with digits in `{0, 1}`.  Distributing each base
digit of a target among `h` binary layers proves directly that `A_h` is an
exact order-`h` basis.

The pure powers form an infinite subset of `A_h`.  At order `h`, the base is
too large for `h` binary summands to create a carry.  At the successor order,
there is a uniform three-column repair:

* one summand has mask `101`;
* one summand has mask `011`;
* the remaining `h - 1` summands have mask `111`.

In base `g = h + 1`, their column totals are `g, g - 1, g - 1`, so the
successive carries give `g^3`.  Prefixing zeros shifts this repair to every
power `g^(m + 3)`.  Every repair summand has at least two nonzero digits, and
therefore survives deletion of the pure powers.

This is deliberately a laboratory for the local carry mechanism.  It does
not assert that independently repairing every deleted summand composes into
one global successor-order representation; that is the unrestricted
normalization/composition issue isolated by the general-order attack.
-/

open scoped BigOperators

namespace Erdos881

/-- Numbers admitting a finite base-`g` expansion whose digits are at most
one.  The existential presentation permits harmless leading zeroes. -/
def binaryDigitBasis (g : ℕ) : Set ℕ :=
  {n | ∃ L : List ℕ, (∀ d ∈ L, d ≤ 1) ∧ Nat.ofDigits g L = n}

/-- The base-`(h + 1)` binary-digit basis. -/
def baseSuccDigitBasis (h : ℕ) : Set ℕ :=
  binaryDigitBasis (h + 1)

/-- The pure powers deleted in the base-`(h + 1)` laboratory. -/
def baseSuccPowerDeletion (h : ℕ) : Set ℕ :=
  {n | ∃ j : ℕ, n = (h + 1) ^ j}

/-- A digit `d ≤ h` is the sum of the `h` threshold indicators
`1_{r < d}`. -/
private theorem sum_fin_digitMask {h d : ℕ} (hd : d ≤ h) :
    (∑ r : Fin h, if r.val < d then 1 else 0) = d := by
  induction h generalizing d with
  | zero =>
      have : d = 0 := by omega
      subst d
      simp
  | succ h ih =>
      rw [Fin.sum_univ_succ]
      cases d with
      | zero => simp
      | succ d =>
          have hd' : d ≤ h := by omega
          simp only [Fin.val_zero, Nat.zero_lt_succ, ↓reduceIte, Fin.val_succ]
          have heq :
              (∑ x : Fin h, if x.val + 1 < d + 1 then 1 else 0) =
                ∑ x : Fin h, if x.val < d then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro x _hx
            simp
          calc
            1 + (∑ x : Fin h, if x.val + 1 < d + 1 then 1 else 0) =
                1 + ∑ x : Fin h, if x.val < d then 1 else 0 :=
              congrArg (fun z : ℕ => 1 + z) heq
            _ = d + 1 := by rw [ih hd']; omega

/-- Summing the binary threshold layers of a bounded digit list reconstructs
the original list value. -/
private theorem sum_ofDigits_digitMasks
    {h : ℕ} (L : List ℕ) (hL : ∀ d ∈ L, d ≤ h) :
    (∑ r : Fin h,
      Nat.ofDigits (h + 1) (L.map fun d => if r.val < d then 1 else 0)) =
      Nat.ofDigits (h + 1) L := by
  induction L with
  | nil => simp
  | cons d L ih =>
      have hd : d ≤ h := hL d List.mem_cons_self
      have htail : ∀ e ∈ L, e ≤ h := by
        intro e he
        exact hL e (List.mem_cons_of_mem d he)
      simp only [List.map_cons, Nat.ofDigits_cons]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ih htail, sum_fin_digitMask hd]

/-- Every target is the sum of its `h` binary threshold layers in base
`h + 1`. -/
theorem baseSuccDigitBasis_exactOrder
    {h : ℕ} (hh : 0 < h) :
    IsExactTupleAsymptoticBasis (baseSuccDigitBasis h) h := by
  refine ⟨0, ?_⟩
  intro n _hn
  let L := Nat.digits (h + 1) n
  let layer : Fin h → ℕ := fun r =>
    Nat.ofDigits (h + 1) (L.map fun d => if r.val < d then 1 else 0)
  refine ⟨layer, ?_, ?_⟩
  · intro r
    refine ⟨L.map (fun d => if r.val < d then 1 else 0), ?_, rfl⟩
    intro e he
    obtain ⟨d, hdL, rfl⟩ := List.mem_map.mp he
    split <;> simp
  · have hbase : 1 < h + 1 := by omega
    have hdigits : ∀ d ∈ L, d ≤ h := by
      intro d hd
      have := Nat.digits_lt_base hbase hd
      omega
    simp only [layer, L, sum_ofDigits_digitMasks _ hdigits,
      Nat.ofDigits_digits]

/-- Pure base-`(h + 1)` powers belong to the binary-digit basis. -/
theorem baseSuccPowerDeletion_subset_basis (h : ℕ) :
    baseSuccPowerDeletion h ⊆ baseSuccDigitBasis h := by
  rintro n ⟨j, rfl⟩
  refine ⟨List.replicate j 0 ++ [1], ?_, ?_⟩
  · intro d hd
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hd
    rcases hd with ⟨_, rfl⟩ | rfl <;> omega
  · simp [Nat.ofDigits_append]

/-- When `h ≥ 1`, the pure-power deletion is infinite. -/
theorem baseSuccPowerDeletion_infinite
    {h : ℕ} (hh : 0 < h) :
    (baseSuccPowerDeletion h).Infinite := by
  have hrange :
      Set.range (fun j : ℕ => (h + 1) ^ j) = baseSuccPowerDeletion h := by
    ext n
    simp [baseSuccPowerDeletion, eq_comm]
  rw [← hrange]
  apply Set.infinite_range_of_injective
  exact Nat.pow_right_injective (by omega)

/-- A canonical binary digit list containing more than one `1` cannot
represent a pure power. -/
private theorem ofDigits_not_mem_powerDeletion
    {h : ℕ} (hh : 0 < h) (L : List ℕ)
    (hsmall : ∀ d ∈ L, d < h + 1)
    (hlast : ∀ hne : L ≠ [], L.getLast hne ≠ 0)
    (hsum : L.sum ≠ 1) :
    Nat.ofDigits (h + 1) L ∉ baseSuccPowerDeletion h := by
  rintro ⟨j, hj⟩
  let P := List.replicate j 0 ++ [1]
  have hPsmall : ∀ d ∈ P, d < h + 1 := by
    intro d hd
    simp only [P, List.mem_append, List.mem_replicate, List.mem_singleton] at hd
    rcases hd with ⟨_, rfl⟩ | rfl <;> omega
  have hPlast : ∀ hne : P ≠ [], P.getLast hne ≠ 0 := by
    intro hne
    simp [P]
  have hPvalue : Nat.ofDigits (h + 1) P = (h + 1) ^ j := by
    simp [P, Nat.ofDigits_append]
  have hdigitsL :
      Nat.digits (h + 1) (Nat.ofDigits (h + 1) L) = L :=
    Nat.digits_ofDigits (h + 1) (by omega) L hsmall hlast
  have hdigitsP :
      Nat.digits (h + 1) (Nat.ofDigits (h + 1) P) = P :=
    Nat.digits_ofDigits (h + 1) (by omega) P hPsmall hPlast
  have hLP : L = P := by
    rw [← hdigitsL, ← hdigitsP, hPvalue, ← hj]
  apply hsum
  rw [hLP]
  simp [P]

/-- The three-column `101` carry summand, shifted by `m` zero digits. -/
def carryRepairA (h m : ℕ) : ℕ :=
  Nat.ofDigits (h + 1) (List.replicate m 0 ++ [1, 0, 1])

/-- The three-column `011` carry summand, shifted by `m` zero digits. -/
def carryRepairB (h m : ℕ) : ℕ :=
  Nat.ofDigits (h + 1) (List.replicate m 0 ++ [1, 1])

/-- The three-column `111` carry summand, shifted by `m` zero digits. -/
def carryRepairC (h m : ℕ) : ℕ :=
  Nat.ofDigits (h + 1) (List.replicate m 0 ++ [1, 1, 1])

/-- The repair list contains `101`, `011`, and `h - 1` copies of `111`.
Its total length is `h + 1`. -/
def baseSuccCarryRepair (h m : ℕ) : List ℕ :=
  [carryRepairA h m, carryRepairB h m] ++
    List.replicate (h - 1) (carryRepairC h m)

private theorem replicate_zero_append_le_one
    (m : ℕ) {T : List ℕ} (hT : ∀ d ∈ T, d ≤ 1) :
    ∀ d ∈ List.replicate m 0 ++ T, d ≤ 1 := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · have := (List.mem_replicate.mp hd).2
    omega
  · exact hT d hd

private theorem carryRepairA_survives
    {h m : ℕ} (hh : 0 < h) :
    carryRepairA h m ∈
      baseSuccDigitBasis h \ baseSuccPowerDeletion h := by
  let L := List.replicate m 0 ++ [1, 0, 1]
  have hsmall : ∀ d ∈ L, d < h + 1 := by
    intro d hd
    have hle := replicate_zero_append_le_one m (T := [1, 0, 1]) (by simp) d hd
    omega
  have hlast : ∀ hne : L ≠ [], L.getLast hne ≠ 0 := by
    intro hne
    simp [L]
  constructor
  · refine ⟨L, ?_, rfl⟩
    exact replicate_zero_append_le_one m (by simp)
  · exact ofDigits_not_mem_powerDeletion hh L hsmall hlast (by simp [L])

private theorem carryRepairB_survives
    {h m : ℕ} (hh : 0 < h) :
    carryRepairB h m ∈
      baseSuccDigitBasis h \ baseSuccPowerDeletion h := by
  let L := List.replicate m 0 ++ [1, 1]
  have hsmall : ∀ d ∈ L, d < h + 1 := by
    intro d hd
    have hle := replicate_zero_append_le_one m (T := [1, 1]) (by simp) d hd
    omega
  have hlast : ∀ hne : L ≠ [], L.getLast hne ≠ 0 := by
    intro hne
    simp [L]
  constructor
  · refine ⟨L, ?_, rfl⟩
    exact replicate_zero_append_le_one m (by simp)
  · exact ofDigits_not_mem_powerDeletion hh L hsmall hlast (by simp [L])

private theorem carryRepairC_survives
    {h m : ℕ} (hh : 0 < h) :
    carryRepairC h m ∈
      baseSuccDigitBasis h \ baseSuccPowerDeletion h := by
  let L := List.replicate m 0 ++ [1, 1, 1]
  have hsmall : ∀ d ∈ L, d < h + 1 := by
    intro d hd
    have hle := replicate_zero_append_le_one m (T := [1, 1, 1]) (by simp) d hd
    omega
  have hlast : ∀ hne : L ≠ [], L.getLast hne ≠ 0 := by
    intro hne
    simp [L]
  constructor
  · refine ⟨L, ?_, rfl⟩
    exact replicate_zero_append_le_one m (by simp)
  · exact ofDigits_not_mem_powerDeletion hh L hsmall hlast (by simp [L])

/-- The uniform carry list has exactly `h + 1` retained binary-digit
summands and sums to the deleted power `(h + 1)^(m + 3)`. -/
theorem baseSuccCarryRepair_spec
    {h m : ℕ} (hh : 0 < h) :
    (baseSuccCarryRepair h m).length = h + 1 ∧
    (∀ x ∈ baseSuccCarryRepair h m,
      x ∈ baseSuccDigitBasis h \ baseSuccPowerDeletion h) ∧
    (baseSuccCarryRepair h m).sum = (h + 1) ^ (m + 3) := by
  constructor
  · simp [baseSuccCarryRepair]
    omega
  constructor
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have hx' : x = carryRepairA h m ∨ x = carryRepairB h m := by
        simpa using hx
      rcases hx' with rfl | rfl
      · exact carryRepairA_survives hh
      · exact carryRepairB_survives hh
    · have hxC : x = carryRepairC h m := List.eq_of_mem_replicate hx
      rw [hxC]
      exact carryRepairC_survives hh
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hh
    simp [baseSuccCarryRepair, carryRepairA, carryRepairB, carryRepairC,
      Nat.ofDigits_append, Nat.ofDigits, pow_succ]
    ring

/-- Every deleted power from exponent three onward has an explicit
successor-order repair entirely in the complement. -/
theorem baseSuccPower_has_retained_successorRepair
    {h k : ℕ} (hh : 0 < h) (hk : 3 ≤ k) :
    ∃ parts : List ℕ,
      parts.length = h + 1 ∧
      (∀ x ∈ parts,
        x ∈ baseSuccDigitBasis h \ baseSuccPowerDeletion h) ∧
      parts.sum = (h + 1) ^ k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨baseSuccCarryRepair h m, ?_⟩
  simpa [Nat.add_comm] using baseSuccCarryRepair_spec (h := h) (m := m) hh

end Erdos881
