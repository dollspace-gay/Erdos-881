import Erdos881.DigitGeneralMenu

namespace Erdos881Digit

open Erdos881

/-- The base-`(k+1)` digit of `n` at position `i`. -/
def digitAt (k i n : ℕ) : ℕ := n / (k + 1) ^ i % (k + 1)

lemma digitAt_le (k i n : ℕ) : digitAt k i n ≤ k := by
  have := Nat.mod_lt (n / (k + 1) ^ i)
    (show 0 < k + 1 by omega)
  unfold digitAt
  omega

/-! ## The window case -/

theorem digit_window_split (k n z : ℕ) (hk : 2 ≤ k)
    (htop : (k + 1) ^ (z + 3) ≤ n)
    (h0 : digitAt k z n = 0)
    (h1 : digitAt k (z + 1) n = 0)
    (h2 : digitAt k (z + 2) n = 0) :
    ∃ v : Fin (k + 1) → ℕ,
      (∀ l, IsDigitK k (v l)) ∧
      (∀ l j, v l ≠ (k + 1) ^ j) ∧
      (∑ l, v l) = n := by
  have h32 : n % (k + 1) ^ (z + 3) =
      n % (k + 1) ^ (z + 2) +
        (k + 1) ^ (z + 2) * digitAt k (z + 2) n := by
    rw [show z + 3 = (z + 2) + 1 by omega]
    exact mod_pow_succ k n (z + 2)
  have h21 : n % (k + 1) ^ (z + 2) =
      n % (k + 1) ^ (z + 1) +
        (k + 1) ^ (z + 1) * digitAt k (z + 1) n := by
    rw [show z + 2 = (z + 1) + 1 by omega]
    exact mod_pow_succ k n (z + 1)
  have h10 : n % (k + 1) ^ (z + 1) =
      n % (k + 1) ^ z +
        (k + 1) ^ z * digitAt k z n :=
    mod_pow_succ k n z
  have hm3 : n % (k + 1) ^ (z + 3) =
      n % (k + 1) ^ z := by
    rw [h32, h21, h10, h0, h1, h2]
    ring
  have hmlt : n % (k + 1) ^ (z + 3) < (k + 1) ^ z := by
    rw [hm3]
    exact Nat.mod_lt n (basePow_pos k z)
  have hC : 1 ≤ n / (k + 1) ^ (z + 3) :=
    (Nat.one_le_div_iff (basePow_pos k (z + 3))).mpr htop
  obtain ⟨v, hv, hnp, hsum⟩ :=
    digit_cut_merge k (n / (k + 1) ^ (z + 3)) (z + 3)
      (n % (k + 1) ^ (z + 3)) hk hC (by omega)
      (by
        rw [show z + 3 - 3 = z by omega]
        exact hmlt)
  refine ⟨v, hv, hnp, ?_⟩
  rw [hsum]
  exact Nat.div_add_mod' n ((k + 1) ^ (z + 3))

/-! ## Bit sums: digit profiles of column supports -/

/-- Sum of distinct scale markers over a finite support. -/
def bitSum (k : ℕ) (s : Finset ℕ) : ℕ :=
  ∑ p ∈ s, (k + 1) ^ p

lemma sum_pow_range_lt (k i : ℕ) (hk : 1 ≤ k) :
    (∑ p ∈ Finset.range i, (k + 1) ^ p) <
      (k + 1) ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h2 : (k + 1) ^ i * 2 ≤
        (k + 1) ^ i * (k + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

lemma bitSum_lt (k : ℕ) (hk : 1 ≤ k) {s : Finset ℕ}
    {i : ℕ} (hs : ∀ p ∈ s, p < i) :
    bitSum k s < (k + 1) ^ i := by
  have hsub : s ⊆ Finset.range i := fun p hp =>
    Finset.mem_range.mpr (hs p hp)
  calc bitSum k s
      ≤ ∑ p ∈ Finset.range i, (k + 1) ^ p :=
        Finset.sum_le_sum_of_subset hsub
    _ < (k + 1) ^ i := sum_pow_range_lt k i hk

/-- The digit profile of a bit sum is its indicator. -/
lemma bitSum_digit (k : ℕ) (hk : 1 ≤ k)
    (s : Finset ℕ) (i : ℕ) :
    bitSum k s / (k + 1) ^ i % (k + 1) =
      if i ∈ s then 1 else 0 := by
  classical
  have hsplit1 := Finset.sum_filter_add_sum_filter_not
    s (fun p => p < i) (fun p => (k + 1) ^ p)
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
    (s.filter (fun p => ¬ p < i)) (fun p => p = i)
    (fun p => (k + 1) ^ p)
  have heq : (s.filter (fun p => ¬ p < i)).filter
      (fun p => p = i) =
      if i ∈ s then {i} else ∅ := by
    split_ifs with h
    · ext q
      simp only [Finset.mem_filter,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨_, _⟩, hq⟩
        exact hq
      · rintro rfl
        exact ⟨⟨h, by omega⟩, rfl⟩
    · ext q
      simp only [Finset.mem_filter,
        Finset.notMem_empty, iff_false]
      rintro ⟨⟨hq, _⟩, rfl⟩
      exact h hq
  have hhi : ∀ p ∈ (s.filter (fun p => ¬ p < i)).filter
      (fun p => ¬ p = i), i + 1 ≤ p := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    omega
  set H := ∑ p ∈ (s.filter (fun p => ¬ p < i)).filter
    (fun p => ¬ p = i), (k + 1) ^ (p - (i + 1)) with hH
  have hhiSum : (∑ p ∈ (s.filter
      (fun p => ¬ p < i)).filter (fun p => ¬ p = i),
        (k + 1) ^ p) = (k + 1) ^ (i + 1) * H := by
    rw [hH, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [← pow_add]
    congr 1
    have := hhi p hp
    omega
  have hmid : (∑ p ∈ (s.filter
      (fun p => ¬ p < i)).filter (fun p => p = i),
        (k + 1) ^ p) =
      (if i ∈ s then 1 else 0) * (k + 1) ^ i := by
    rw [heq]
    split_ifs
    · simp
    · simp
  set L := ∑ p ∈ s.filter (fun p => p < i),
    (k + 1) ^ p with hL
  have hLlt : L < (k + 1) ^ i := by
    rw [hL]
    exact bitSum_lt k hk (fun p hp => by
      simp only [Finset.mem_filter] at hp
      exact hp.2)
  have hdecomp : bitSum k s =
      (k + 1) ^ i *
        ((k + 1) * H + (if i ∈ s then 1 else 0)) +
        L := by
    unfold bitSum
    rw [← hsplit1, ← hsplit2, hhiSum, hmid]
    rw [show (k + 1) ^ (i + 1) = (k + 1) ^ i * (k + 1)
      by rw [pow_succ]]
    ring
  rw [hdecomp,
    Nat.mul_add_div (basePow_pos k i),
    Nat.div_eq_of_lt hLlt, Nat.add_zero,
    Nat.mul_add_mod]
  split_ifs
  · exact Nat.mod_eq_of_lt (by omega)
  · exact Nat.mod_eq_of_lt (by omega)

lemma bitSum_isDigit (k : ℕ) (hk : 1 ≤ k)
    (s : Finset ℕ) : IsDigitK k (bitSum k s) := by
  intro i
  rw [bitSum_digit k hk s i]
  split_ifs <;> omega

/-- The digit profile of a pure power. -/
lemma pow_digit (k : ℕ) (hk : 1 ≤ k) (j i : ℕ) :
    (k + 1) ^ j / (k + 1) ^ i % (k + 1) =
      if i = j then 1 else 0 := by
  have h := bitSum_digit k hk {j} i
  simpa [bitSum, Finset.mem_singleton] using h

/-- Two set columns forbid pure powers. -/
lemma bitSum_ne_pow (k : ℕ) (hk : 1 ≤ k)
    {s : Finset ℕ} (hcard : 2 ≤ s.card) :
    ∀ j, bitSum k s ≠ (k + 1) ^ j := by
  intro j hj
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    Finset.one_lt_card.mp
      (show 1 < s.card by omega)
  have h1 := bitSum_digit k hk s p
  have h2 := bitSum_digit k hk s q
  rw [hj, pow_digit k hk j p] at h1
  rw [hj, pow_digit k hk j q] at h2
  rw [if_pos hp] at h1
  rw [if_pos hq] at h2
  by_cases hpj : p = j
  · by_cases hqj : q = j
    · exact hpq (hpj.trans hqj.symm)
    · rw [if_neg hqj] at h2
      omega
  · rw [if_neg hpj] at h1
    omega

/-! ## Base expansion -/

/-- Base expansion below a height. -/
lemma digit_expansion (k : ℕ) :
    ∀ L n : ℕ, n < (k + 1) ^ L →
      (∑ p ∈ Finset.range L,
        digitAt k p n * (k + 1) ^ p) = n := by
  intro L
  induction L with
  | zero =>
    intro n hn
    simp only [pow_zero, Nat.lt_one_iff] at hn
    simp [hn]
  | succ L ih =>
    intro n hn
    have hq : n / (k + 1) < (k + 1) ^ L := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      rw [← pow_succ]
      exact hn
    have hrec := ih (n / (k + 1)) hq
    rw [Finset.sum_range_succ']
    have h0 : digitAt k 0 n * (k + 1) ^ 0 =
        n % (k + 1) := by
      simp [digitAt]
    have hstep : ∀ p, digitAt k (p + 1) n =
        digitAt k p (n / (k + 1)) := by
      intro p
      unfold digitAt
      rw [div_pow_succ]
    calc (∑ p ∈ Finset.range L,
          digitAt k (p + 1) n * (k + 1) ^ (p + 1)) +
            digitAt k 0 n * (k + 1) ^ 0
        = (∑ p ∈ Finset.range L,
            (k + 1) *
              (digitAt k p (n / (k + 1)) *
                (k + 1) ^ p)) + n % (k + 1) := by
          rw [h0]
          congr 1
          refine Finset.sum_congr rfl ?_
          intro p _
          rw [hstep, pow_succ]
          ring
      _ = (k + 1) *
            (∑ p ∈ Finset.range L,
              digitAt k p (n / (k + 1)) *
                (k + 1) ^ p) + n % (k + 1) := by
          rw [Finset.mul_sum]
      _ = (k + 1) * (n / (k + 1)) + n % (k + 1) := by
          rw [hrec]
      _ = n := Nat.div_add_mod n (k + 1)

/-! ## Interval columns -/

/-- The interval column: `d` part indices containing the seed
`σ ≤ k`, never wrapping. -/
def colSet (k σ d : ℕ) : Finset ℕ :=
  if σ + d ≤ k + 1 then Finset.Ico σ (σ + d)
  else Finset.Ico (k + 1 - d) (k + 1)

lemma colSet_card (k σ d : ℕ) (hd : d ≤ k + 1) :
    (colSet k σ d).card = d := by
  unfold colSet
  split_ifs with h <;> rw [Nat.card_Ico] <;> omega

lemma colSet_lt (k σ d : ℕ) {p : ℕ}
    (hp : p ∈ colSet k σ d) : p < k + 1 := by
  unfold colSet at hp
  split_ifs at hp with h <;>
    rw [Finset.mem_Ico] at hp <;> omega

lemma seed_mem_colSet (k σ d : ℕ) (hσ : σ ≤ k)
    (hd : 1 ≤ d) : σ ∈ colSet k σ d := by
  unfold colSet
  split_ifs with h <;> rw [Finset.mem_Ico] <;> omega

/-! ## The dense case -/

/-- Occupied columns below height `L`. -/
def nzSet (k n L : ℕ) : Finset ℕ :=
  (Finset.range L).filter (fun p => digitAt k p n ≠ 0)

/-- An enumeration of the occupied columns. -/
noncomputable def enumNz (k n L : ℕ) :
    Fin (nzSet k n L).card → ℕ :=
  fun i => ((nzSet k n L).equivFin.symm i : ℕ)

lemma enumNz_mem (k n L : ℕ)
    (i : Fin (nzSet k n L).card) :
    enumNz k n L i ∈ nzSet k n L :=
  ((nzSet k n L).equivFin.symm i).2

lemma enumNz_inj (k n L : ℕ) :
    Function.Injective (enumNz k n L) := by
  intro a b h
  exact (nzSet k n L).equivFin.symm.injective
    (Subtype.ext h)

lemma enumNz_digit_pos (k n L : ℕ)
    (i : Fin (nzSet k n L).card) :
    1 ≤ digitAt k (enumNz k n L i) n := by
  have h := enumNz_mem k n L i
  unfold nzSet at h
  rw [Finset.mem_filter] at h
  omega

/-- The token column at enumerated occupied position `i`. -/
noncomputable def tokCol (k n L : ℕ)
    (i : Fin (nzSet k n L).card) : Finset ℕ :=
  colSet k (min ((i : ℕ) / 2) k)
    (digitAt k (enumNz k n L i) n)

/-- The column support of part index `j`. -/
noncomputable def partSet (k n L j : ℕ) : Finset ℕ :=
  (Finset.univ.filter
    (fun i => j ∈ tokCol k n L i)).image
    (enumNz k n L)

lemma mem_partSet_of_tok (k n L j : ℕ)
    (i : Fin (nzSet k n L).card)
    (h : j ∈ tokCol k n L i) :
    enumNz k n L i ∈ partSet k n L j := by
  unfold partSet
  exact Finset.mem_image.mpr
    ⟨i, Finset.mem_filter.mpr
      ⟨Finset.mem_univ i, h⟩, rfl⟩

theorem digit_dense_split (k n L : ℕ) (hk : 2 ≤ k)
    (hL : n < (k + 1) ^ L)
    (hr : 2 * (k + 1) ≤ (nzSet k n L).card) :
    ∃ v : Fin (k + 1) → ℕ,
      (∀ l, IsDigitK k (v l)) ∧
      (∀ l j, v l ≠ (k + 1) ^ j) ∧
      (∑ l, v l) = n := by
  classical
  refine
    ⟨fun l => bitSum k (partSet k n L (l : ℕ)),
      ?_, ?_, ?_⟩
  · intro l
    exact bitSum_isDigit k (by omega) _
  · intro l j
    have hlk : (l : ℕ) ≤ k := by
      have := l.isLt
      omega
    have h2l : 2 * (l : ℕ) + 1 <
        (nzSet k n L).card := by
      have := l.isLt
      omega
    have hcard : 2 ≤ (partSet k n L (l : ℕ)).card := by
      set i0 : Fin (nzSet k n L).card :=
        ⟨2 * (l : ℕ), by omega⟩ with hi0
      set i1 : Fin (nzSet k n L).card :=
        ⟨2 * (l : ℕ) + 1, by omega⟩ with hi1
      have hσ0 : min ((i0 : ℕ) / 2) k = (l : ℕ) := by
        rw [hi0]
        simp only []
        omega
      have hσ1 : min ((i1 : ℕ) / 2) k = (l : ℕ) := by
        rw [hi1]
        simp only []
        omega
      have hm0 : (l : ℕ) ∈ tokCol k n L i0 := by
        unfold tokCol
        rw [hσ0]
        exact seed_mem_colSet k (l : ℕ) _ hlk
          (enumNz_digit_pos k n L i0)
      have hm1 : (l : ℕ) ∈ tokCol k n L i1 := by
        unfold tokCol
        rw [hσ1]
        exact seed_mem_colSet k (l : ℕ) _ hlk
          (enumNz_digit_pos k n L i1)
      have hne : enumNz k n L i0 ≠ enumNz k n L i1 := by
        intro hcon
        have := enumNz_inj k n L hcon
        rw [hi0, hi1] at this
        have := Fin.mk.injEq (2 * (l : ℕ)) _
          (2 * (l : ℕ) + 1) _ ▸ this
        omega
      have h1c : 1 < (partSet k n L (l : ℕ)).card :=
        Finset.one_lt_card.mpr
          ⟨enumNz k n L i0,
            mem_partSet_of_tok k n L _ i0 hm0,
            enumNz k n L i1,
            mem_partSet_of_tok k n L _ i1 hm1, hne⟩
      omega
    exact bitSum_ne_pow k (by omega) hcard j
  · calc ∑ l : Fin (k + 1),
          bitSum k (partSet k n L (l : ℕ))
        = ∑ j ∈ Finset.range (k + 1),
            bitSum k (partSet k n L j) :=
          Fin.sum_univ_eq_sum_range
            (fun j => bitSum k (partSet k n L j))
            (k + 1)
      _ = ∑ j ∈ Finset.range (k + 1),
            ∑ i ∈ Finset.univ.filter
              (fun i => j ∈ tokCol k n L i),
              (k + 1) ^ (enumNz k n L i) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          unfold partSet bitSum
          exact Finset.sum_image
            (fun a _ b _ hab => enumNz_inj k n L hab)
      _ = ∑ j ∈ Finset.range (k + 1),
            ∑ i : Fin (nzSet k n L).card,
              (if j ∈ tokCol k n L i then
                (k + 1) ^ (enumNz k n L i) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          exact Finset.sum_filter _ _
      _ = ∑ i : Fin (nzSet k n L).card,
            ∑ j ∈ Finset.range (k + 1),
              (if j ∈ tokCol k n L i then
                (k + 1) ^ (enumNz k n L i) else 0) :=
          Finset.sum_comm
      _ = ∑ i : Fin (nzSet k n L).card,
            digitAt k (enumNz k n L i) n *
              (k + 1) ^ (enumNz k n L i) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          have hsub : tokCol k n L i ⊆
              Finset.range (k + 1) := fun p hp =>
            Finset.mem_range.mpr (colSet_lt _ _ _ hp)
          rw [Finset.sum_ite_mem,
            Finset.inter_eq_right.mpr hsub,
            Finset.sum_const, smul_eq_mul]
          congr 1
          exact colSet_card _ _ _
            (le_trans (digitAt_le k _ n) (by omega))
      _ = ∑ p ∈ nzSet k n L,
            digitAt k p n * (k + 1) ^ p := by
          rw [Fintype.sum_equiv
            (nzSet k n L).equivFin.symm
            (fun i => digitAt k (enumNz k n L i) n *
              (k + 1) ^ (enumNz k n L i))
            (fun x => digitAt k (x : ℕ) n *
              (k + 1) ^ (x : ℕ))
            (fun i => rfl)]
          exact Finset.sum_coe_sort (nzSet k n L)
            (fun p => digitAt k p n * (k + 1) ^ p)
      _ = ∑ p ∈ Finset.range L,
            digitAt k p n * (k + 1) ^ p := by
          symm
          rw [← Finset.sum_filter_add_sum_filter_not
            (Finset.range L)
            (fun p => digitAt k p n ≠ 0)
            (fun p => digitAt k p n * (k + 1) ^ p)]
          have hzero : (∑ p ∈ (Finset.range L).filter
              (fun p => ¬ digitAt k p n ≠ 0),
              digitAt k p n * (k + 1) ^ p) = 0 := by
            refine Finset.sum_eq_zero ?_
            intro p hp
            rw [Finset.mem_filter] at hp
            have : digitAt k p n = 0 := by
              rcases Nat.eq_zero_or_pos
                (digitAt k p n) with h | h
              · exact h
              · exact absurd (by omega) hp.2
            rw [this, Nat.zero_mul]
          rw [hzero, Nat.add_zero]
          rfl
      _ = n := digit_expansion k L n hL

/-! ## The dichotomy and the uniform deletion theorem -/

theorem digit_deletion_order (k n : ℕ) (hk : 2 ≤ k)
    (hn : (k + 1) ^ (6 * k + 12) ≤ n) :
    ∃ v : Fin (k + 1) → ℕ,
      (∀ l, IsDigitK k (v l)) ∧
      (∀ l j, v l ≠ (k + 1) ^ j) ∧
      (∑ l, v l) = n := by
  classical
  by_cases hwin : ∃ z, (k + 1) ^ (z + 3) ≤ n ∧
      digitAt k z n = 0 ∧ digitAt k (z + 1) n = 0 ∧
      digitAt k (z + 2) n = 0
  · obtain ⟨z, h1, h2, h3, h4⟩ := hwin
    exact digit_window_split k n z hk h1 h2 h3 h4
  · have hdense : ∀ z, (k + 1) ^ (z + 3) ≤ n →
        ¬ (digitAt k z n = 0 ∧
          digitAt k (z + 1) n = 0 ∧
          digitAt k (z + 2) n = 0) :=
      fun z hz hcon =>
        hwin ⟨z, hz, hcon.1, hcon.2.1, hcon.2.2⟩
    have hbig : 6 * k + 12 < n :=
      lt_of_lt_of_le (Nat.lt_pow_self (by omega)) hn
    have hchoose : ∀ w : Fin (2 * (k + 1)),
        ∃ p, 3 * (w : ℕ) ≤ p ∧
          p < 3 * (w : ℕ) + 3 ∧
          digitAt k p n ≠ 0 := by
      intro w
      have hw : (w : ℕ) < 2 * (k + 1) := w.isLt
      have hle : (k + 1) ^ (3 * (w : ℕ) + 3) ≤ n :=
        le_trans
          (Nat.pow_le_pow_right (by omega) (by omega))
          hn
      have h := hdense (3 * (w : ℕ)) hle
      by_contra hcon
      push Not at hcon
      refine h ⟨?_, ?_, ?_⟩
      · exact hcon (3 * (w : ℕ)) (by omega) (by omega)
      · exact hcon (3 * (w : ℕ) + 1) (by omega)
          (by omega)
      · exact hcon (3 * (w : ℕ) + 2) (by omega)
          (by omega)
    choose f hf1 hf2 hf3 using hchoose
    have hinj : Function.Injective f := by
      intro a b hab
      have ha1 := hf1 a
      have ha2 := hf2 a
      have hb1 := hf1 b
      have hb2 := hf2 b
      rw [hab] at ha1 ha2
      exact Fin.ext (by omega)
    have hmaps : ∀ w : Fin (2 * (k + 1)),
        f w ∈ nzSet k n (n + 1) := by
      intro w
      unfold nzSet
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, hf3 w⟩
      have h2 := hf2 w
      have hw := w.isLt
      omega
    have hcard : 2 * (k + 1) ≤
        (nzSet k n (n + 1)).card := by
      have h := Finset.card_le_card_of_injOn
        (s := (Finset.univ : Finset (Fin (2 * (k + 1)))))
        (t := nzSet k n (n + 1)) f
        (fun w _ => hmaps w)
        (fun a _ b _ hab => hinj hab)
      simpa using h
    exact digit_dense_split k n (n + 1) hk
      (lt_trans (Nat.lt_pow_self (by omega))
        (Nat.pow_lt_pow_right (by omega) (by omega)))
      hcard

theorem digit_deletion_basis (k : ℕ) (hk : 2 ≤ k) :
    IsExactTupleAsymptoticBasis
      (DigitSet k \ DigitPowers k) (k + 1) := by
  refine ⟨(k + 1) ^ (6 * k + 12), fun n hn => ?_⟩
  obtain ⟨v, hv, hnp, hsum⟩ :=
    digit_deletion_order k n hk hn
  refine ⟨v, fun l => ⟨hv l, ?_⟩, hsum⟩
  rintro ⟨m, hm⟩
  exact hnp l m hm

theorem erdos881_digit_full_instance (k : ℕ)
    (hk : 2 ≤ k) :
    IsStronglyMinimalExactBasis (DigitSet k) k ∧
      (3 ≤ k →
        ¬ IsExactTupleAsymptoticBasis
          (DigitSet k) 2) ∧
      DigitPowers k ⊆ DigitSet k ∧
      (DigitPowers k).Infinite ∧
      IsExactTupleAsymptoticBasis
        (DigitSet k \ DigitPowers k) (k + 1) :=
  ⟨(digit_uniform_hard_case k hk).1,
    (digit_uniform_hard_case k hk).2,
    digitPowers_subset k (by omega),
    digitPowers_infinite k (by omega),
    digit_deletion_basis k hk⟩

end Erdos881Digit
