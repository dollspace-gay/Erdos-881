/-
# Infinite Ramsey theorem for pairs (two colours)

Every two-colouring of the pairs of naturals admits an infinite
homogeneous subsequence.  Proved by the classical pre-homogeneous
construction: a choice recursion picks anchors whose colour towards
the surviving infinite pool is constant per stage, and a pigeonhole
on the stage tags extracts the homogeneous subsequence.

Infrastructure for the Nash-Williams / barrier-rank program on the
Erdős 881 hub hypergraph: the team supply lives inside every
infinite deletion, and Ramsey extraction is the tool that will
canonicalize team shapes inside a fixed ground stream.
-/

import Mathlib

namespace Erdos881

/-- One pre-homogeneous step: from an anchor `a` and an infinite
pool `S`, produce a new anchor `x ∈ S` above `a`, a colour tag, and
an infinite sub-pool all of whose members are above `x` and receive
the tag colour from `a`. -/
theorem prehomogeneous_step (c : ℕ → ℕ → Bool) (a : ℕ) (S : Set ℕ)
    (hS : S.Infinite) :
    ∃ (x : ℕ) (T : Set ℕ) (bt : Bool), T.Infinite ∧ a < x ∧
      x ∈ S ∧ c a x = bt ∧
      ∀ y ∈ T, y ∈ S ∧ c a y = bt ∧ x < y := by
  classical
  by_cases hT : {z ∈ S | c a z = true}.Infinite
  · obtain ⟨hx, hax⟩ := (hT.exists_gt a).choose_spec
    refine ⟨(hT.exists_gt a).choose,
      {z ∈ S | c a z = true} \
        {z | z ≤ (hT.exists_gt a).choose}, true,
      hT.diff (Set.finite_le_nat _), hax, hx.1, hx.2, ?_⟩
    intro y hy
    obtain ⟨⟨hyS, hyc⟩, hyx⟩ := hy
    have hyx' : ¬y ≤ (hT.exists_gt a).choose := hyx
    exact ⟨hyS, hyc, by omega⟩
  · have hF : {z ∈ S | c a z = false}.Infinite := by
      have hsplit : S ⊆ {z ∈ S | c a z = true} ∪
          {z ∈ S | c a z = false} := by
        intro z hz
        rcases Bool.eq_false_or_eq_true (c a z) with h | h
        · exact Or.inl ⟨hz, h⟩
        · exact Or.inr ⟨hz, h⟩
      by_contra hFf
      rw [Set.not_infinite] at hFf hT
      exact hS (Set.Finite.subset (hT.union hFf) hsplit)
    obtain ⟨hx, hax⟩ := (hF.exists_gt a).choose_spec
    refine ⟨(hF.exists_gt a).choose,
      {z ∈ S | c a z = false} \
        {z | z ≤ (hF.exists_gt a).choose}, false,
      hF.diff (Set.finite_le_nat _), hax, hx.1, hx.2, ?_⟩
    intro y hy
    obtain ⟨⟨hyS, hyc⟩, hyx⟩ := hy
    have hyx' : ¬y ≤ (hF.exists_gt a).choose := hyx
    exact ⟨hyS, hyc, by omega⟩

/-- **Infinite Ramsey, pairs, two colours.**  For any pair colouring
`c` there is a strictly monotone `f` and a colour `b` with
`c (f i) (f j) = b` for all `i < j`. -/
theorem infinite_ramsey_pairs (c : ℕ → ℕ → Bool) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∃ b : Bool,
      ∀ i j, i < j → c (f i) (f j) = b := by
  classical
  choose xf Tf btf hTinf hax hxS hcx hTy using prehomogeneous_step c
  set st : ℕ → ℕ × {S : Set ℕ // S.Infinite} := fun k =>
    Nat.rec (0, ⟨Set.univ, Set.infinite_univ⟩)
      (fun _ p => (xf p.1 p.2.1 p.2.2,
        ⟨Tf p.1 p.2.1 p.2.2, hTinf p.1 p.2.1 p.2.2⟩)) k with hst
  have hstS : ∀ k, st (k + 1) = (xf (st k).1 (st k).2.1 (st k).2.2,
      ⟨Tf (st k).1 (st k).2.1 (st k).2.2,
        hTinf (st k).1 (st k).2.1 (st k).2.2⟩) := fun _ => rfl
  set t : ℕ → Bool := fun k => btf (st k).1 (st k).2.1 (st k).2.2
    with ht
  have hanchor : ∀ k, (st k).1 < (st (k + 1)).1 ∧
      (st (k + 1)).1 ∈ (st k).2.1 ∧
      c (st k).1 (st (k + 1)).1 = t k := by
    intro k
    rw [hstS]
    exact ⟨hax _ _ _, hxS _ _ _, hcx _ _ _⟩
  have hpoolstep : ∀ k, ∀ y ∈ (st (k + 1)).2.1,
      y ∈ (st k).2.1 ∧ c (st k).1 y = t k := by
    intro k y hy
    rw [hstS] at hy
    obtain ⟨h1, h2, -⟩ := hTy _ _ _ y hy
    exact ⟨h1, h2⟩
  have hamono : StrictMono (fun k => (st k).1) :=
    strictMono_nat_of_lt_succ (fun k => (hanchor k).1)
  have hnest : ∀ k l, k ≤ l → (st l).2.1 ⊆ (st k).2.1 := by
    intro k l hkl
    induction l with
    | zero =>
      have h0 : k = 0 := by omega
      subst h0
      exact fun y hy => hy
    | succ l ih =>
      rcases Nat.lt_or_ge k (l + 1) with h' | h'
      · intro y hy
        exact ih (by omega) ((hpoolstep l y hy).1)
      · have h1 : k = l + 1 := by omega
        subst h1
        exact fun y hy => hy
  have hpool : ∀ k j, k < j → c (st k).1 (st j).1 = t k := by
    intro k j hkj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hmem1 : (st (j' + 1)).1 ∈ (st j').2.1 := (hanchor j').2.1
    rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hkj) with heq | hlt
    · have h1 : k = j' := by omega
      subst h1
      exact (hanchor k).2.2
    · have hmem2 : (st (j' + 1)).1 ∈ (st (k + 1)).2.1 :=
        hnest (k + 1) j' (by omega) hmem1
      exact (hpoolstep k _ hmem2).2
  have htag : ∃ b : Bool, {k | t k = b}.Infinite := by
    by_contra hno
    push_neg at hno
    have h1 : {k | t k = true}.Finite := by
      simpa [Set.not_infinite] using hno true
    have h2 : {k | t k = false}.Finite := by
      simpa [Set.not_infinite] using hno false
    have hsplit : (Set.univ : Set ℕ) ⊆ {k | t k = true} ∪
        {k | t k = false} := by
      intro k _
      rcases Bool.eq_false_or_eq_true (t k) with h | h
      · exact Or.inl h
      · exact Or.inr h
    exact Set.infinite_univ (Set.Finite.subset (h1.union h2) hsplit)
  obtain ⟨b, hb⟩ := htag
  have hpick : ∀ X : ℕ, ∃ k, X < k ∧ t k = b := by
    intro X
    obtain ⟨k, hk, hkX⟩ := hb.exists_gt X
    exact ⟨k, hkX, hk⟩
  choose nxt hnxt htnxt using hpick
  set g : ℕ → ℕ := fun i => Nat.rec (nxt 0) (fun _ prev => nxt prev) i
    with hg
  have hgS : ∀ i, g (i + 1) = nxt (g i) := fun _ => rfl
  have hgmono : StrictMono g := by
    apply strictMono_nat_of_lt_succ
    intro i
    rw [hgS]
    exact hnxt (g i)
  have hgt : ∀ i, t (g i) = b := by
    intro i
    cases i with
    | zero => exact htnxt 0
    | succ i =>
      rw [hgS]
      exact htnxt (g i)
  refine ⟨fun i => (st (g i)).1, fun i j hij => hamono (hgmono hij),
    b, fun i j hij => ?_⟩
  rw [hpool (g i) (g j) (hgmono hij)]
  exact hgt i

end Erdos881
