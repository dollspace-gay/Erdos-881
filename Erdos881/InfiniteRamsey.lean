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

/-- One pre-homogeneous step at arity three: given an anchor and a
strictly monotone pool above it, the pairs theorem inside the pool
yields a new anchor FROM the homogeneous subsequence, a colour tag,
and the subsequence tail as the next pool — with the tag colour
against the anchor on all pool pairs AND on all (new anchor, pool)
pairs. -/
theorem prehomogeneous_step₃ (c : ℕ → ℕ → ℕ → Bool) (a : ℕ)
    (e : ℕ → ℕ) (he : StrictMono e) (hea : ∀ i, a < e i) :
    ∃ (x : ℕ) (e' : ℕ → ℕ) (bt : Bool), StrictMono e' ∧ a < x ∧
      (∃ i0, x = e i0) ∧ (∀ i, ∃ i', e' i = e i') ∧
      (∀ i, x < e' i) ∧
      (∀ i j, i < j → c a (e' i) (e' j) = bt) ∧
      (∀ i, c a x (e' i) = bt) := by
  obtain ⟨f, hf, bt, hhom⟩ :=
    infinite_ramsey_pairs (fun i j => c a (e i) (e j))
  refine ⟨e (f 0), fun i => e (f (i + 1)), bt,
    fun i j hij => he (hf (by omega)), hea _, ⟨f 0, rfl⟩,
    fun i => ⟨f (i + 1), rfl⟩, fun i => he (hf (by omega)),
    ?_, ?_⟩
  · intro i j hij
    exact hhom (i + 1) (j + 1) (by omega)
  · intro i
    exact hhom 0 (i + 1) (by omega)

/-- **Infinite Ramsey, triples, two colours.**  By anchor recursion
over the pairs theorem: each stage recolours its pool against the
new anchor and keeps the homogeneous tail. -/
theorem infinite_ramsey_triples (c : ℕ → ℕ → ℕ → Bool) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∃ b : Bool,
      ∀ i j k, i < j → j < k → c (f i) (f j) (f k) = b := by
  classical
  choose xf ef btf hmono' hax hxmem hsub hxab hhomp hhoma using
    prehomogeneous_step₃ c
  set st : ℕ → {p : ℕ × (ℕ → ℕ) //
      StrictMono p.2 ∧ ∀ i, p.1 < p.2 i} := fun k =>
    Nat.rec ⟨((0 : ℕ), fun i => i + 1),
        fun _ _ h => Nat.succ_lt_succ h, fun i => Nat.succ_pos i⟩
      (fun _ q => ⟨(xf q.1.1 q.1.2 q.2.1 q.2.2,
          ef q.1.1 q.1.2 q.2.1 q.2.2),
        hmono' q.1.1 q.1.2 q.2.1 q.2.2,
        fun i => hxab q.1.1 q.1.2 q.2.1 q.2.2 i⟩) k with hst
  have hstS : ∀ k, (st (k + 1)).1 =
      (xf (st k).1.1 (st k).1.2 (st k).2.1 (st k).2.2,
       ef (st k).1.1 (st k).1.2 (st k).2.1 (st k).2.2) :=
    fun _ => rfl
  set t : ℕ → Bool := fun k =>
    btf (st k).1.1 (st k).1.2 (st k).2.1 (st k).2.2 with ht
  have hanchorlt : ∀ k, (st k).1.1 < (st (k + 1)).1.1 := by
    intro k
    have h1 : (st (k + 1)).1.1 =
        xf (st k).1.1 (st k).1.2 (st k).2.1 (st k).2.2 :=
      congrArg Prod.fst (hstS k)
    rw [h1]
    exact hax _ _ _ _
  have hamono : StrictMono (fun k => (st k).1.1) :=
    strictMono_nat_of_lt_succ hanchorlt
  have hpoolsub : ∀ k i, ∃ i',
      (st (k + 1)).1.2 i = (st k).1.2 i' := by
    intro k i
    have h1 : (st (k + 1)).1.2 =
        ef (st k).1.1 (st k).1.2 (st k).2.1 (st k).2.2 :=
      congrArg Prod.snd (hstS k)
    rw [h1]
    exact hsub _ _ _ _ i
  have hchain : ∀ k j, k ≤ j → ∀ i, ∃ i',
      (st j).1.2 i = (st k).1.2 i' := by
    intro k j hkj
    induction j with
    | zero =>
      have h0 : k = 0 := by omega
      subst h0
      exact fun i => ⟨i, rfl⟩
    | succ j ih =>
      rcases Nat.lt_or_ge k (j + 1) with h' | h'
      · intro i
        obtain ⟨i₁, hi₁⟩ := hpoolsub j i
        obtain ⟨i', hi'⟩ := ih (by omega) i₁
        exact ⟨i', by rw [hi₁, hi']⟩
      · have h1 : k = j + 1 := by omega
        subst h1
        exact fun i => ⟨i, rfl⟩
  -- every later anchor is a pool value at every intermediate stage
  have hanchormem : ∀ l j, l < j → ∃ γ,
      (st j).1.1 = (st l).1.2 γ := by
    intro l j hlj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have h1 : (st (j' + 1)).1.1 =
        xf (st j').1.1 (st j').1.2 (st j').2.1 (st j').2.2 :=
      congrArg Prod.fst (hstS j')
    obtain ⟨i0, hi0⟩ := hxmem (st j').1.1 (st j').1.2
      (st j').2.1 (st j').2.2
    have h2 : (st (j' + 1)).1.1 = (st j').1.2 i0 := by
      rw [h1, hi0]
    obtain ⟨γ, hγ⟩ := hchain l j' (by omega) i0
    exact ⟨γ, by rw [h2, hγ]⟩
  -- the triple colour law across stages
  have hpool3 : ∀ k i j, k < i → i < j →
      c (st k).1.1 (st i).1.1 (st j).1.1 = t k := by
    intro k i j hki hij
    have hepool : (st (k + 1)).1.2 =
        ef (st k).1.1 (st k).1.2 (st k).2.1 (st k).2.2 :=
      congrArg Prod.snd (hstS k)
    rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hki) with heq | hlt
    · -- i = k + 1 : anchor-vs-pool pairs
      obtain ⟨γ, hγ⟩ := hanchormem (k + 1) j (by omega)
      have hxk : (st i).1.1 =
          xf (st k).1.1 (st k).1.2 (st k).2.1 (st k).2.2 := by
        rw [← heq]
      rw [hxk, hγ, hepool]
      exact hhoma _ _ _ _ γ
    · -- both later anchors are stage-(k+1) pool values
      obtain ⟨α, hα⟩ := hanchormem (k + 1) i hlt
      obtain ⟨β, hβ⟩ := hanchormem (k + 1) j (by omega)
      have haij : (st i).1.1 < (st j).1.1 := hamono hij
      have hαβ : α < β := by
        rw [hα, hβ] at haij
        exact (st (k + 1)).2.1.lt_iff_lt.1 haij
      rw [hα, hβ, hepool]
      exact hhomp _ _ _ _ α β hαβ
  -- pigeonhole the tags and extract
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
  refine ⟨fun i => (st (g i)).1.1,
    fun i j hij => hamono (hgmono hij), b, fun i j k hij hjk => ?_⟩
  rw [hpool3 (g i) (g j) (g k) (hgmono hij) (hgmono hjk)]
  exact hgt i

end Erdos881
