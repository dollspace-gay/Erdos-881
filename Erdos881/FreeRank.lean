import Erdos881.DisjointRepEngine
import Erdos881.Normalization
import Erdos881.BoundedPairFreeSet
import Erdos881.InfiniteSunflower
import Erdos881.FreeSetTripleRepairs

namespace Erdos881

/-- A node of the freeness tree: a finite set of positive basis
elements that is rep-free. -/
def FreeNode (A : Set ℕ) (N₀ : ℕ) (P : Finset ℕ) : Prop :=
  (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧ RepFree A N₀ P

/-- One tree step, oriented for well-foundedness: `Q` extends the
free node `P` by one element above all of `P`, staying free. -/
def FreeStep (A : Set ℕ) (N₀ : ℕ) (Q P : Finset ℕ) : Prop :=
  FreeNode A N₀ P ∧ FreeNode A N₀ Q ∧
  ∃ b, b ∈ A ∧ 0 < b ∧ (∀ h ∈ P, h < b) ∧ Q = insert b P

/-- Freeness is downward closed: avoiding a superset is harder. -/
theorem RepFree.mono {A : Set ℕ} {N₀ : ℕ} {P P' : Finset ℕ}
    (hsub : P' ⊆ P) (hfree : RepFree A N₀ P) : RepFree A N₀ P' := by
  intro m hm
  obtain ⟨x, hx, y, hy, z, hz, hs, hxP, hyP, hzP⟩ := hfree m hm
  exact ⟨x, hx, y, hy, z, hz, hs, fun h => hxP (hsub h),
    fun h => hyP (hsub h), fun h => hzP (hsub h)⟩

theorem freeStep_wf {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    WellFounded (FreeStep A N₀) := by
  classical
  rw [wellFounded_iff_isEmpty_descending_chain]
  constructor
  rintro ⟨f, hf⟩
  have hb : ∀ n, ∃ b, b ∈ A ∧ 0 < b ∧ (∀ h ∈ f n, h < b) ∧
      f (n + 1) = insert b (f n) := fun n => (hf n).2.2
  choose b hbA hbpos hbmax hbins using hb
  have hbmem : ∀ n, b n ∈ f (n + 1) := by
    intro n
    rw [hbins n]
    exact Finset.mem_insert_self _ _
  have hbstep : ∀ n, b n < b (n + 1) := fun n =>
    hbmax (n + 1) (b n) (hbmem n)
  have hbmono : StrictMono b := strictMono_nat_of_lt_succ hbstep
  set k₀ := (f 0).card with hk₀
  set emb := (f 0).orderEmbOfFin rfl with hemb
  set e : ℕ → ℕ := fun j =>
    if h : j < k₀ then emb ⟨j, h⟩ else b (j - k₀) with he
  have heval_lo : ∀ j (h : j < k₀), e j = emb ⟨j, h⟩ := by
    intro j h
    simp [he, h]
  have heval_hi : ∀ j, k₀ ≤ j → e j = b (j - k₀) := by
    intro j h
    have h' : ¬j < k₀ := by omega
    simp [he, h']
  have hembf : ∀ (i : Fin k₀), emb i ∈ f 0 :=
    fun i => (f 0).orderEmbOfFin_mem rfl i
  have hb0big : ∀ x ∈ f 0, x < b 0 := hbmax 0
  have hemono : StrictMono e := by
    intro i j hij
    rcases Nat.lt_or_ge j k₀ with hj | hj
    · have hi : i < k₀ := by omega
      rw [heval_lo i hi, heval_lo j hj]
      exact emb.strictMono (by exact Fin.mk_lt_mk.2 hij)
    · rcases Nat.lt_or_ge i k₀ with hi | hi
      · rw [heval_lo i hi, heval_hi j hj]
        have h1 : emb ⟨i, hi⟩ < b 0 := hb0big _ (hembf _)
        have h2 : b 0 ≤ b (j - k₀) := hbmono.monotone (Nat.zero_le _)
        omega
      · rw [heval_hi i hi, heval_hi j hj]
        exact hbmono (by omega)
  have heA : ∀ j, e j ∈ A := by
    intro j
    rcases Nat.lt_or_ge j k₀ with h | h
    · rw [heval_lo j h]
      exact ((hf 0).1.1 _ (hembf _)).1
    · rw [heval_hi j h]
      exact hbA _
  have hepos : ∀ j, 0 < e j := by
    intro j
    rcases Nat.lt_or_ge j k₀ with h | h
    · rw [heval_lo j h]
      exact ((hf 0).1.1 _ (hembf _)).2
    · rw [heval_hi j h]
      exact hbpos _
  -- prefix identification
  have hbase : (Finset.range k₀).image e = f 0 := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj, hjx⟩ := Finset.mem_image.1 hx
      have hj' : j < k₀ := Finset.mem_range.1 hj
      rw [← hjx, heval_lo j hj']
      exact hembf _
    · intro hx
      have hx' : x ∈ Set.range (emb : Fin k₀ → ℕ) := by
        rw [Finset.range_orderEmbOfFin]
        exact hx
      obtain ⟨i, hi⟩ := hx'
      refine Finset.mem_image.2 ⟨i.1, Finset.mem_range.2 i.2, ?_⟩
      rw [heval_lo i.1 i.2]
      simpa using hi
  have hprefix : ∀ m, (Finset.range (k₀ + m)).image e = f m := by
    intro m
    induction m with
    | zero => simpa using hbase
    | succ m ih =>
      have h1 : k₀ + (m + 1) = (k₀ + m) + 1 := by omega
      rw [h1, Finset.range_add_one, Finset.image_insert, ih,
        heval_hi (k₀ + m) (by omega),
        show k₀ + m - k₀ = m from by omega, ← hbins m]
  -- all prefixes are free
  have hallfree : ∀ J, RepFree A N₀ ((Finset.range J).image e) := by
    intro J
    rcases Nat.lt_or_ge J k₀ with h | h
    · refine RepFree.mono ?_ (hf 0).1.2
      rw [← hbase]
      intro x hx
      obtain ⟨j, hj, hjx⟩ := Finset.mem_image.1 hx
      exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 (by
        have := Finset.mem_range.1 hj
        omega), hjx⟩
    · have h1 : J = k₀ + (J - k₀) := by omega
      rw [h1, hprefix (J - k₀)]
      exact (hf (J - k₀)).1.2
  exact free_prefixes_die_of_hfail h0 hcov hfail e hemono heA hepos
    hallfree

theorem exists_strict_rank {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ ρ : Finset ℕ → Ordinal.{0},
      ∀ P Q, FreeStep A N₀ Q P → ρ Q < ρ P := by
  have hwf := freeStep_wf h0 hcov hfail
  exact ⟨fun P => (hwf.apply P).rank,
    fun P Q h => Acc.rank_lt_of_rel (hwf.apply P) h⟩

theorem freeNode_extension_iff {A : Set ℕ} {N₀ : ℕ} {P : Finset ℕ}
    {b : ℕ} (hP : FreeNode A N₀ P) (hbA : b ∈ A) (hbpos : 0 < b) :
    ¬FreeNode A N₀ (insert b P) ↔
      ∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m (insert b P) := by
  have hposins : ∀ h ∈ insert b P, h ∈ A ∧ 0 < h := by
    intro h hh
    rcases Finset.mem_insert.1 hh with h' | h'
    · rw [h']
      exact ⟨hbA, hbpos⟩
    · exact hP.1 h h'
  constructor
  · intro hnot
    have hnotfree : ¬RepFree A N₀ (insert b P) := by
      intro hfree
      exact hnot ⟨hposins, hfree⟩
    rw [RepFree] at hnotfree
    push Not at hnotfree
    obtain ⟨m, hm, hall⟩ := hnotfree
    refine ⟨m, hm, ?_⟩
    intro x hx y hy z hz hsum
    by_contra hmiss
    push Not at hmiss
    obtain ⟨hxm, hym, hzm⟩ := hmiss
    exact hzm (hall x hx y hy z hz hsum hxm hym)
  · rintro ⟨m, hm, hhub⟩ ⟨-, hfree⟩
    obtain ⟨x, hx, y, hy, z, hz, hsum, hxP, hyP, hzP⟩ := hfree m hm
    rcases hhub x hx y hy z hz hsum with h | h | h
    · exact hxP h
    · exact hyP h
    · exact hzP h

/-- A stalled node: free, but no extension by a large positive
basis element stays free.  The rep cofinal supply asserts such nodes exist;
the leaf law identifies their boundary with support transversals. -/
def Stalled (A : Set ℕ) (N₀ X : ℕ) (P : Finset ℕ) : Prop :=
  FreeNode A N₀ P ∧
  ∀ b, b ∈ A → 0 < b → X ≤ b → ¬RepFree A N₀ (insert b P)

theorem Stalled.of_step {A : Set ℕ} {N₀ X : ℕ} {P Q : Finset ℕ}
    (hst : Stalled A N₀ X P) (hstep : FreeStep A N₀ Q P) :
    Stalled A N₀ X Q := by
  obtain ⟨-, hQnode, c, hcA, hcpos, hcmax, hQeq⟩ := hstep
  refine ⟨hQnode, fun b hbA hbpos hXb hfree => ?_⟩
  refine hst.2 b hbA hbpos hXb (RepFree.mono ?_ hfree)
  rw [hQeq]
  intro x hx
  rcases Finset.mem_insert.1 hx with h | h
  · rw [h]
    exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)

theorem stalled_chain_bound {A : Set ℕ} {N₀ X : ℕ}
    [DecidablePred (· ∈ A)]
    {P : Finset ℕ} (hst : Stalled A N₀ X P)
    (f : ℕ → Finset ℕ) (L : ℕ) (hf0 : f 0 = P)
    (hstep : ∀ i, i < L → FreeStep A N₀ (f (i + 1)) (f i)) :
    L ≤ ((Finset.range X).filter (· ∈ A)).card := by
  classical
  -- every prefix node is stalled
  have hstall : ∀ i, i ≤ L → Stalled A N₀ X (f i) := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [hf0]
      exact hst
    | succ i ih =>
      intro hiL
      exact (ih (by omega)).of_step (hstep i (by omega))
  -- extract the picks
  have hpick : ∀ i, i < L → ∃ b, b ∈ A ∧ 0 < b ∧
      (∀ h ∈ f i, h < b) ∧ f (i + 1) = insert b (f i) ∧ b < X := by
    intro i hiL
    obtain ⟨-, hQnode, b, hbA, hbpos, hbmax, hQeq⟩ := hstep i hiL
    refine ⟨b, hbA, hbpos, hbmax, hQeq, ?_⟩
    by_contra hbX
    push Not at hbX
    exact (hstall i (by omega)).2 b hbA hbpos hbX
      (hQeq ▸ hQnode.2)
  choose b hbA hbpos hbmax hbins hbX using hpick
  -- picks are strictly increasing along the chain
  have hbmem : ∀ i (h : i < L), b i h ∈ f (i + 1) := by
    intro i h
    rw [hbins i h]
    exact Finset.mem_insert_self _ _
  have hchainmem : ∀ i j (hi : i < L), i < j → j ≤ L →
      b i hi ∈ f j := by
    intro i j hi hij
    induction j with
    | zero => omega
    | succ j ih =>
      intro hjL
      rcases Nat.lt_or_ge i j with h' | h'
      · have h1 := ih h' (by omega)
        rw [hbins j (by omega)]
        exact Finset.mem_insert_of_mem h1
      · have h1 : i = j := by omega
        subst h1
        exact hbmem i hi
  have hbinc : ∀ i j (hi : i < L) (hj : j < L), i < j →
      b i hi < b j hj := by
    intro i j hi hj hij
    exact hbmax j hj _ (hchainmem i j hi hij (by omega))
  -- inject the picks into the window
  have hinj : ∀ i j (hi : i < L) (hj : j < L),
      b i hi = b j hj → i = j := by
    intro i j hi hj heq
    rcases Nat.lt_trichotomy i j with h | h | h
    · have := hbinc i j hi hj h
      omega
    · exact h
    · have := hbinc j i hj hi h
      omega
  have hmaps : ∀ i (hi : i < L),
      b i hi ∈ (Finset.range X).filter (· ∈ A) := by
    intro i hi
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (hbX i hi),
      hbA i hi⟩
  -- count
  have hcard := Finset.card_le_card_of_injOn
    (f := fun i : ℕ => if h : i < L then b i h else 0)
    (s := Finset.range L)
    (t := (Finset.range X).filter (· ∈ A))
    (by
      intro i hi
      have hi' : i < L := Finset.mem_range.1 hi
      simp only [dif_pos hi']
      exact hmaps i hi')
    (by
      intro i hi j hj heq
      have hi' : i < L := Finset.mem_range.1 (by simpa using hi)
      have hj' : j < L := Finset.mem_range.1 (by simpa using hj)
      have heq' : (if h : i < L then b i h else 0) =
          (if h : j < L then b j h else 0) := heq
      rw [dif_pos hi', dif_pos hj'] at heq'
      exact hinj i j hi' hj' heq')
  simpa using hcard

theorem stalled_exists_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ X P, Stalled A N₀ X P := by
  classical
  have hunb : ∀ X : ℕ, ∃ p ∈ {a | a ∈ A ∧ 0 < a}, X ≤ p := by
    intro X
    obtain ⟨a, ha, hXa⟩ := pairCovers_unbounded hcov (max X 1)
    refine ⟨a, ⟨ha, ?_⟩, le_trans (le_max_left _ _) hXa⟩
    have := le_trans (le_max_right _ _) hXa
    omega
  obtain ⟨P, hPpos, hPfree, X, hstall⟩ :=
    rep_cofinal_supply_pool (P₀ := {a | a ∈ A ∧ 0 < a}) h0 hcov
      (fun a ha => ha.1) (fun h => by have := h.2; omega) hunb hfail
  refine ⟨X, P, ⟨fun h hh => ⟨(hPpos h hh).1, (hPpos h hh).2⟩,
    hPfree⟩, ?_⟩
  intro b hbA hbpos hXb hfree
  obtain ⟨m, hmN, hbm, hhub⟩ := hstall b ⟨hbA, hbpos⟩ hXb
  obtain ⟨x, hx, y, hy, z, hz, hsum, hxP, hyP, hzP⟩ := hfree m hmN
  rcases hhub x hx y hy z hz hsum with h | h | h
  · exact hxP h
  · exact hyP h
  · exact hzP h

theorem root_rank_dichotomy (A : Set ℕ) (N₀ : ℕ) :
    (∀ n, ∃ P : Finset ℕ, FreeNode A N₀ P ∧ n ≤ P.card) ∨
    (∃ D, ∀ S : Finset ℕ, (∀ h ∈ S, h ∈ A ∧ 0 < h) →
      S.card = D + 1 → ∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m S) := by
  classical
  by_cases support_transversal : ∀ n, ∃ P : Finset ℕ, FreeNode A N₀ P ∧ n ≤ P.card
  · exact Or.inl support_transversal
  · right
    push Not at support_transversal
    obtain ⟨D, hD⟩ := support_transversal
    refine ⟨D, fun S hSpos hScard => ?_⟩
    have hnotfree : ¬RepFree A N₀ S := by
      intro hfree
      have := hD S ⟨hSpos, hfree⟩
      omega
    rw [RepFree] at hnotfree
    push Not at hnotfree
    obtain ⟨m, hm, hall⟩ := hnotfree
    refine ⟨m, hm, ?_⟩
    intro x hx y hy z hz hsum
    by_contra hmiss
    push Not at hmiss
    obtain ⟨hxm, hym, hzm⟩ := hmiss
    exact hzm (hall x hx y hy z hz hsum hxm hym)

/-- Pair-freeness node: order-2 version, for arbitrary minimal
bases. -/
def PairFreeNode (A : Set ℕ) (N₀ : ℕ) (P : Finset ℕ) : Prop :=
  (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧ PairFree A N₀ P

/-- Pair-freeness tree step. -/
def PairFreeStep (A : Set ℕ) (N₀ : ℕ) (Q P : Finset ℕ) : Prop :=
  PairFreeNode A N₀ P ∧ PairFreeNode A N₀ Q ∧
  ∃ b, b ∈ A ∧ 0 < b ∧ (∀ h ∈ P, h < b) ∧ Q = insert b P

/-- Pair-freeness is downward closed. -/
theorem PairFree.mono {A : Set ℕ} {N₀ : ℕ} {P P' : Finset ℕ}
    (hsub : P' ⊆ P) (hfree : PairFree A N₀ P) :
    PairFree A N₀ P' := by
  intro m hm
  obtain ⟨x, hx, y, hy, hs, hxP, hyP⟩ := hfree m hm
  exact ⟨x, hx, y, hy, hs, fun h => hxP (hsub h),
    fun h => hyP (hsub h)⟩

theorem pairFreeStep_wf {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hmin : ∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) :
    WellFounded (PairFreeStep A N₀) := by
  classical
  rw [wellFounded_iff_isEmpty_descending_chain]
  constructor
  rintro ⟨f, hf⟩
  have hb : ∀ n, ∃ b, b ∈ A ∧ 0 < b ∧ (∀ h ∈ f n, h < b) ∧
      f (n + 1) = insert b (f n) := fun n => (hf n).2.2
  choose b hbA hbpos hbmax hbins using hb
  have hbmem : ∀ n, b n ∈ f (n + 1) := by
    intro n
    rw [hbins n]
    exact Finset.mem_insert_self _ _
  have hbstep : ∀ n, b n < b (n + 1) := fun n =>
    hbmax (n + 1) (b n) (hbmem n)
  have hbmono : StrictMono b := strictMono_nat_of_lt_succ hbstep
  set k₀ := (f 0).card with hk₀
  set emb := (f 0).orderEmbOfFin rfl with hemb
  set e : ℕ → ℕ := fun j =>
    if h : j < k₀ then emb ⟨j, h⟩ else b (j - k₀) with he
  have heval_lo : ∀ j (h : j < k₀), e j = emb ⟨j, h⟩ := by
    intro j h
    simp [he, h]
  have heval_hi : ∀ j, k₀ ≤ j → e j = b (j - k₀) := by
    intro j h
    have h' : ¬j < k₀ := by omega
    simp [he, h']
  have hembf : ∀ (i : Fin k₀), emb i ∈ f 0 :=
    fun i => (f 0).orderEmbOfFin_mem rfl i
  have hb0big : ∀ x ∈ f 0, x < b 0 := hbmax 0
  have hemono : StrictMono e := by
    intro i j hij
    rcases Nat.lt_or_ge j k₀ with hj | hj
    · have hi : i < k₀ := by omega
      rw [heval_lo i hi, heval_lo j hj]
      exact emb.strictMono (by exact Fin.mk_lt_mk.2 hij)
    · rcases Nat.lt_or_ge i k₀ with hi | hi
      · rw [heval_lo i hi, heval_hi j hj]
        have h1 : emb ⟨i, hi⟩ < b 0 := hb0big _ (hembf _)
        have h2 : b 0 ≤ b (j - k₀) := hbmono.monotone (Nat.zero_le _)
        omega
      · rw [heval_hi i hi, heval_hi j hj]
        exact hbmono (by omega)
  have heA : ∀ j, e j ∈ A := by
    intro j
    rcases Nat.lt_or_ge j k₀ with h | h
    · rw [heval_lo j h]
      exact ((hf 0).1.1 _ (hembf _)).1
    · rw [heval_hi j h]
      exact hbA _
  have hepos : ∀ j, 0 < e j := by
    intro j
    rcases Nat.lt_or_ge j k₀ with h | h
    · rw [heval_lo j h]
      exact ((hf 0).1.1 _ (hembf _)).2
    · rw [heval_hi j h]
      exact hbpos _
  have hbase : (Finset.range k₀).image e = f 0 := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj, hjx⟩ := Finset.mem_image.1 hx
      have hj' : j < k₀ := Finset.mem_range.1 hj
      rw [← hjx, heval_lo j hj']
      exact hembf _
    · intro hx
      have hx' : x ∈ Set.range (emb : Fin k₀ → ℕ) := by
        rw [Finset.range_orderEmbOfFin]
        exact hx
      obtain ⟨i, hi⟩ := hx'
      refine Finset.mem_image.2 ⟨i.1, Finset.mem_range.2 i.2, ?_⟩
      rw [heval_lo i.1 i.2]
      simpa using hi
  have hprefix : ∀ m, (Finset.range (k₀ + m)).image e = f m := by
    intro m
    induction m with
    | zero => simpa using hbase
    | succ m ih =>
      have h1 : k₀ + (m + 1) = (k₀ + m) + 1 := by omega
      rw [h1, Finset.range_add_one, Finset.image_insert, ih,
        heval_hi (k₀ + m) (by omega),
        show k₀ + m - k₀ = m from by omega, ← hbins m]
  have hallfree : ∀ J, PairFree A N₀ ((Finset.range J).image e) := by
    intro J
    rcases Nat.lt_or_ge J k₀ with h | h
    · refine PairFree.mono ?_ (hf 0).1.2
      rw [← hbase]
      intro x hx
      obtain ⟨j, hj, hjx⟩ := Finset.mem_image.1 hx
      exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 (by
        have := Finset.mem_range.1 hj
        omega), hjx⟩
    · have h1 : J = k₀ + (J - k₀) := by omega
      rw [h1, hprefix (J - k₀)]
      exact (hf (J - k₀)).1.2
  exact pair_free_prefixes_die_of_minimality hcov hmin e hemono heA
    hepos hallfree

theorem exists_strict_pair_rank {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hmin : ∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) :
    ∃ ρ : Finset ℕ → Ordinal.{0},
      ∀ P Q, PairFreeStep A N₀ Q P → ρ Q < ρ P := by
  have hwf := pairFreeStep_wf hcov hmin
  exact ⟨fun P => (hwf.apply P).rank,
    fun P Q h => Acc.rank_lt_of_rel (hwf.apply P) h⟩

/-- The pool-relative freeness tree: picks restricted to a pool. -/
def PoolFreeStep (A : Set ℕ) (N₀ : ℕ) (P₀ : Set ℕ)
    (Q P : Finset ℕ) : Prop :=
  FreeStep A N₀ Q P ∧ ∀ h ∈ Q, h ∈ P₀

/-- Every pool tree is well-founded, as a subrelation of the full
freeness tree. -/
theorem poolFreeStep_wf {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (P₀ : Set ℕ) : WellFounded (PoolFreeStep A N₀ P₀) :=
  Subrelation.wf (fun h => h.1) (freeStep_wf h0 hcov hfail)

theorem no_pool_rank_descent {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (pools : ℕ → Set ℕ) :
    ¬∀ k, (((poolFreeStep_wf h0 hcov hfail (pools (k + 1))).apply
        ∅).rank <
      ((poolFreeStep_wf h0 hcov hfail (pools k)).apply ∅).rank) := by
  intro hdesc
  have hempty : IsEmpty {f : ℕ → Ordinal.{0} //
      ∀ n, f (n + 1) < f n} := by
    rw [← wellFounded_iff_isEmpty_descending_chain]
    exact Ordinal.lt_wf
  exact hempty.false ⟨fun k =>
    ((poolFreeStep_wf h0 hcov hfail (pools k)).apply ∅).rank, hdesc⟩

/-- Rank is monotone under subrelations: shrinking the tree never
raises a node's rank.  (Not in Mathlib.) -/
theorem rank_le_of_subrel {α : Type*} {r r' : α → α → Prop}
    (hsub : ∀ ⦃x y⦄, r' x y → r x y) :
    ∀ {a : α} (h : Acc r a) (h' : Acc r' a), h'.rank ≤ h.rank := by
  intro a h
  induction h with
  | intro a ha ih =>
    intro h'
    rw [Acc.rank_eq, Acc.rank_eq]
    apply Ordinal.iSup_le
    rintro ⟨b, hb'⟩
    have hb : r b a := hsub hb'
    have h1 := ih b hb (h'.inv hb')
    calc Order.succ ((h'.inv hb').rank)
        ≤ Order.succ ((ha b hb).rank) := Order.succ_le_succ h1
      _ ≤ _ := Ordinal.le_iSup
          (fun c : {c // r c a} => Order.succ ((ha c.1 c.2).rank))
          (⟨b, hb⟩ : {c // r c a})

theorem pool_rank_mono {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {P₀ P₀' : Set ℕ} (hsub : P₀' ⊆ P₀) :
    ((poolFreeStep_wf h0 hcov hfail P₀').apply ∅).rank ≤
    ((poolFreeStep_wf h0 hcov hfail P₀).apply ∅).rank :=
  rank_le_of_subrel
    (fun _ _ h => ⟨h.1, fun a ha => hsub (h.2 a ha)⟩) _ _

theorem pool_rank_pos {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {P₀ : Set ℕ} (hP₀A : P₀ ⊆ A) (h0P : 0 ∉ P₀)
    (hunb : ∀ X, ∃ p ∈ P₀, X ≤ p) :
    0 < ((poolFreeStep_wf h0 hcov hfail P₀).apply ∅).rank := by
  classical
  have hfree0 : RepFree A N₀ ∅ := by
    intro m hm
    obtain ⟨x, hx, y, hy, hxy⟩ := hcov m hm
    exact ⟨x, hx, y, hy, 0, h0, by omega, Finset.notMem_empty x,
      Finset.notMem_empty y, Finset.notMem_empty 0⟩
  -- some pool singleton is free
  have hchild : ∃ b, b ∈ P₀ ∧ 0 < b ∧ RepFree A N₀ {b} := by
    by_contra hno
    push Not at hno
    refine singleton_support_transversals_refuted h0 hcov hanchor hfail ?_
    intro N
    obtain ⟨b, hbP, hNb⟩ := hunb (max N 1)
    have hbpos : 0 < b := by
      rcases Nat.eq_zero_or_pos b with h | h
      · exact absurd (h ▸ hbP) h0P
      · exact h
    have hnotfree := hno b hbP hbpos
    rw [RepFree] at hnotfree
    push Not at hnotfree
    obtain ⟨m, hm, hall⟩ := hnotfree
    have hhub : IsRepSupportTransversal A m {b} := by
      intro x hx y hy z hz hsum
      by_contra hmiss
      push Not at hmiss
      obtain ⟨hxm, hym, hzm⟩ := hmiss
      exact hzm (hall x hx y hy z hz hsum hxm hym)
    -- the target dominates the required element, so targets are cofinal
    obtain ⟨x, hx, y, hy, hxy⟩ := hcov m hm
    have hbm : b ≤ m := by
      rcases hhub x hx y hy 0 h0 (by omega) with h | h | h
      · have := Finset.mem_singleton.1 h
        omega
      · have := Finset.mem_singleton.1 h
        omega
      · have := Finset.mem_singleton.1 h
        omega
    exact ⟨m, by
      have := le_trans (le_max_left _ _) hNb
      omega, b, hbpos, hhub⟩
  obtain ⟨b, hbP, hbpos, hbfree⟩ := hchild
  have hstep : PoolFreeStep A N₀ P₀ {b} ∅ := by
    refine ⟨⟨⟨fun h hh => absurd hh (Finset.notMem_empty h), hfree0⟩,
      ⟨?_, hbfree⟩, b, hP₀A hbP, hbpos,
      fun h hh => absurd hh (Finset.notMem_empty h), rfl⟩, ?_⟩
    · intro h hh
      rw [Finset.mem_singleton.1 hh]
      exact ⟨hP₀A hbP, hbpos⟩
    · intro h hh
      rw [Finset.mem_singleton.1 hh]
      exact hbP
  have hlt := Acc.rank_lt_of_rel
    ((poolFreeStep_wf h0 hcov hfail P₀).apply ∅) hstep
  exact lt_of_le_of_lt (zero_le _) hlt

theorem free_set_card_le_rank {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {P₀ : Set ℕ} {Q : Finset ℕ}
    (hQnode : FreeNode A N₀ Q) (hQpool : ∀ h ∈ Q, h ∈ P₀) :
    (Q.card : Ordinal.{0}) ≤
      ((poolFreeStep_wf h0 hcov hfail P₀).apply ∅).rank := by
  classical
  set hwf := poolFreeStep_wf h0 hcov hfail P₀ with hhwf
  set n := Q.card with hn
  set emb := Q.orderEmbOfFin hn.symm with hemb
  set e : ℕ → ℕ := fun j => if h : j < n then emb ⟨j, h⟩ else 0
    with he
  have heval : ∀ j (h : j < n), e j = emb ⟨j, h⟩ := by
    intro j h
    simp [he, h]
  have hembQ : ∀ (i : Fin n), emb i ∈ Q :=
    fun i => Q.orderEmbOfFin_mem hn.symm i
  set pre : ℕ → Finset ℕ := fun i => (Finset.range i).image e
    with hpre
  have hpresub : ∀ i, i ≤ n → pre i ⊆ Q := by
    intro i hin x hx
    obtain ⟨j, hj, hjx⟩ := Finset.mem_image.1 hx
    have hj' : j < n := by
      have := Finset.mem_range.1 hj
      omega
    rw [← hjx, heval j hj']
    exact hembQ _
  have hprenode : ∀ i, i ≤ n → FreeNode A N₀ (pre i) := by
    intro i hin
    exact ⟨fun h hh => hQnode.1 h (hpresub i hin hh),
      RepFree.mono (hpresub i hin) hQnode.2⟩
  have hprestep : ∀ i, i < n →
      PoolFreeStep A N₀ P₀ (pre (i + 1)) (pre i) := by
    intro i hin
    have hstep1 : pre (i + 1) = insert (e i) (pre i) := by
      show (Finset.range (i + 1)).image e =
        insert (e i) ((Finset.range i).image e)
      rw [Finset.range_add_one, Finset.image_insert]
    refine ⟨⟨hprenode i (by omega), ?_, e i, ?_, ?_, ?_, hstep1⟩,
      fun h hh => hQpool h (hpresub (i + 1) (by omega) hh)⟩
    · exact hprenode (i + 1) (by omega)
    · rw [heval i hin]
      exact (hQnode.1 _ (hembQ _)).1
    · rw [heval i hin]
      exact (hQnode.1 _ (hembQ _)).2
    · intro h hh
      obtain ⟨j, hj, hjx⟩ := Finset.mem_image.1 hh
      have hj' : j < i := Finset.mem_range.1 hj
      have hjn : j < n := by omega
      rw [← hjx, heval j hjn, heval i hin]
      exact emb.strictMono (Fin.mk_lt_mk.2 hj')
  -- downward induction on remaining depth
  have hrank : ∀ d i, i + d ≤ n →
      ((d : ℕ) : Ordinal.{0}) ≤ (hwf.apply (pre i)).rank := by
    intro d
    induction d with
    | zero =>
      intro i _
      simp
    | succ d ih =>
      intro i hin
      have hin' : i < n := by omega
      have hlt := Acc.rank_lt_of_rel (hwf.apply (pre i))
        (hprestep i hin')
      have hih := ih (i + 1) (by omega)
      have h1 : ((d : ℕ) : Ordinal.{0}) <
          (hwf.apply (pre i)).rank := lt_of_le_of_lt hih hlt
      have h2 : ((d + 1 : ℕ) : Ordinal.{0}) =
          Order.succ ((d : ℕ) : Ordinal.{0}) := by
        rw [Nat.cast_succ, Order.succ_eq_add_one]
      rw [h2]
      exact Order.succ_le_of_lt h1
  have h0pre : pre 0 = ∅ := by
    show (Finset.range 0).image e = ∅
    simp
  have := hrank n 0 (by omega)
  rw [h0pre] at this
  exact this

theorem rank_ge_imp_free_set {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {P₀ : Set ℕ} :
    ∀ (n : ℕ) (P : Finset ℕ), FreeNode A N₀ P → (∀ h ∈ P, h ∈ P₀) →
      ((n : ℕ) : Ordinal.{0}) ≤
        ((poolFreeStep_wf h0 hcov hfail P₀).apply P).rank →
      ∃ Q : Finset ℕ, FreeNode A N₀ Q ∧ (∀ h ∈ Q, h ∈ P₀) ∧
        Q.card = P.card + n := by
  classical
  set hwf := poolFreeStep_wf h0 hcov hfail P₀ with hhwf
  intro n
  induction n with
  | zero =>
    intro P hPnode hPpool _
    exact ⟨P, hPnode, hPpool, by omega⟩
  | succ n ih =>
    intro P hPnode hPpool hrank
    have hpos : ((n : ℕ) : Ordinal.{0}) < (hwf.apply P).rank := by
      have h1 : ((n : ℕ) : Ordinal.{0}) <
          ((n + 1 : ℕ) : Ordinal.{0}) := by
        exact_mod_cast Nat.lt_succ_self n
      exact lt_of_lt_of_le h1 hrank
    rw [Acc.rank_eq] at hpos
    rw [Ordinal.lt_iSup_iff] at hpos
    obtain ⟨⟨C, hC⟩, hlt⟩ := hpos
    have hCrank : ((n : ℕ) : Ordinal.{0}) ≤
        (hwf.apply C).rank := by
      have h1 := Order.lt_succ_iff.1 hlt
      exact h1
    have hCnode : FreeNode A N₀ C := hC.1.2.1
    have hCpool : ∀ h ∈ C, h ∈ P₀ := hC.2
    obtain ⟨Q, hQnode, hQpool, hQcard⟩ := ih C hCnode hCpool hCrank
    obtain ⟨-, -, b, hbA, hbpos, hbmax, hCeq⟩ := hC.1
    have hbP : b ∉ P := fun h => by
      have := hbmax b h
      omega
    have hCcard : C.card = P.card + 1 := by
      rw [hCeq]
      rw [Finset.card_insert_of_notMem hbP]
    exact ⟨Q, hQnode, hQpool, by omega⟩

/-- SupportTransversal-freeness of a set is exactly rep-freeness: `S` is rep-free
iff no late target has `S` as a full support transversal. -/
theorem repFree_iff_no_support_transversal {A : Set ℕ} {N₀ : ℕ} {S : Finset ℕ} :
    RepFree A N₀ S ↔ ¬∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m S := by
  constructor
  · rintro hfree ⟨m, hm, hhub⟩
    obtain ⟨x, hx, y, hy, z, hz, hs, hxS, hyS, hzS⟩ := hfree m hm
    rcases hhub x hx y hy z hz hs with h | h | h
    · exact hxS h
    · exact hyS h
    · exact hzS h
  · intro hno m hm
    by_contra hall
    push Not at hall
    refine hno ⟨m, hm, ?_⟩
    intro x hx y hy z hz hs
    by_contra hmiss
    push Not at hmiss
    obtain ⟨h1, h2, h3⟩ := hmiss
    exact h3 (hall x hx y hy z hz hs h1 h2)

theorem escalation_rank_certificate {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {P₀ : Set ℕ}
    (b : ℕ → ℕ) (hmono : StrictMono b)
    (hbA : ∀ j, b j ∈ A) (hbpos : ∀ j, 0 < b j)
    (hbpool : ∀ j, b j ∈ P₀) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ((∀ i j, i < j → ∃ n, N₀ ≤ n ∧
        IsRepSupportTransversal A n {b (f i), b (f j)}) ∨
      (∀ i j k, i < j → j < k → ∃ n, N₀ ≤ n ∧
        IsRepSupportTransversal A n {b (f i), b (f j), b (f k)}) ∨
      (3 : Ordinal.{0}) ≤
        ((poolFreeStep_wf h0 hcov hfail P₀).apply ∅).rank) := by
  classical
  obtain ⟨f, hf, hout⟩ := pair_transversal_card_escalation_two' h0 hcov hanchor
    hfail b hmono hbA hbpos
  rcases hout with hcl | ⟨-, hcl⟩ | ⟨-, htf, -⟩
  · exact ⟨f, hf, Or.inl hcl⟩
  · exact ⟨f, hf, Or.inr (Or.inl hcl)⟩
  · refine ⟨f, hf, Or.inr (Or.inr ?_)⟩
    set S : Finset ℕ := {b (f 0), b (f 1), b (f 2)} with hS
    have h01 : b (f 0) < b (f 1) := hmono (hf (by omega))
    have h12 : b (f 1) < b (f 2) := hmono (hf (by omega))
    have hSfree : RepFree A N₀ S :=
      repFree_iff_no_support_transversal.2 (htf 0 1 2 (by omega) (by omega))
    have hSnode : FreeNode A N₀ S := by
      refine ⟨?_, hSfree⟩
      intro h hh
      rw [hS] at hh
      rcases Finset.mem_insert.1 hh with h' | h'
      · rw [h']
        exact ⟨hbA _, hbpos _⟩
      rcases Finset.mem_insert.1 h' with h'' | h''
      · rw [h'']
        exact ⟨hbA _, hbpos _⟩
      · rw [Finset.mem_singleton.1 h'']
        exact ⟨hbA _, hbpos _⟩
    have hSpool : ∀ h ∈ S, h ∈ P₀ := by
      intro h hh
      rw [hS] at hh
      rcases Finset.mem_insert.1 hh with h' | h'
      · rw [h']
        exact hbpool _
      rcases Finset.mem_insert.1 h' with h'' | h''
      · rw [h'']
        exact hbpool _
      · rw [Finset.mem_singleton.1 h'']
        exact hbpool _
    have hScard : S.card = 3 := by
      rw [hS, Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          push Not
          omega),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_singleton]
          omega),
        Finset.card_singleton]
    have := free_set_card_le_rank h0 hcov hfail hSnode hSpool
    rw [hScard] at this
    exact_mod_cast this

theorem clique_descent {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ (d : ℕ) (e : ℕ → ℕ), 1 ≤ d → StrictMono e →
    (∀ j, e j ∈ A) → (∀ j, 0 < e j) →
    (∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, e i = h) → S.card = d + 1 →
      ¬RepFree A N₀ S) →
    ∃ (d' : ℕ) (f : ℕ → ℕ), 1 ≤ d' ∧ d' ≤ d ∧ StrictMono f ∧
      (∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, e (f i) = h) → S.card = d' →
        RepFree A N₀ S) ∧
      (∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, e (f i) = h) →
        S.card = d' + 1 → ¬RepFree A N₀ S) := by
  classical
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
    intro e hd1 hemono heA hepos hnonfree
    obtain ⟨r, rfl⟩ : ∃ r, d = r + 1 := ⟨d - 1, by omega⟩
    set c : (Fin (r + 1) → ℕ) → Bool := fun t =>
      if RepFree A N₀ (Finset.univ.image (fun i => e (t i)))
      then true else false with hc
    have hciff : ∀ t : Fin (r + 1) → ℕ, c t = true ↔
        RepFree A N₀ (Finset.univ.image (fun i => e (t i))) := by
      intro t
      by_cases h : RepFree A N₀
        (Finset.univ.image (fun i => e (t i)))
      · simp [hc, h]
      · simp [hc, h]
    obtain ⟨f₁, hf₁, bt, hhom⟩ := infinite_ramsey_tuples r c
    rcases Bool.eq_false_or_eq_true bt with hbt | hbt
    · -- all (r+1)-subsets of the refined stream are free: perfect
      subst hbt
      refine ⟨r + 1, f₁, by omega, le_refl _, hf₁, ?_, ?_⟩
      · intro S hSmem hScard
        obtain ⟨u, humono, huim⟩ := sorted_indices_of_card
          (fun i j hij => hemono (hf₁ hij)) hScard hSmem
        have h1 := hhom u humono
        rw [hciff] at h1
        have h2 : (Finset.univ.image fun i => e (f₁ (u i))) = S :=
          huim
        rw [h2] at h1
        exact h1
      · intro S hSmem hScard
        refine hnonfree S ?_ hScard
        intro h hh
        obtain ⟨i, hi⟩ := hSmem h hh
        exact ⟨f₁ i, hi⟩
    · -- all (r+1)-subsets of the refined stream are non-free
      subst hbt
      have hallnonfree : ∀ S : Finset ℕ,
          (∀ h ∈ S, ∃ i, e (f₁ i) = h) → S.card = r + 1 →
          ¬RepFree A N₀ S := by
        intro S hSmem hScard hfree
        obtain ⟨u, humono, huim⟩ := sorted_indices_of_card
          (fun i j hij => hemono (hf₁ hij)) hScard hSmem
        have h1 := hhom u humono
        have h2 : c (fun i => f₁ (u i)) = true := by
          rw [hciff]
          have h3 : (Finset.univ.image fun i => e (f₁ (u i))) = S :=
            huim
          rw [h3]
          exact hfree
        rw [h1] at h2
        exact Bool.false_ne_true h2
      rcases Nat.lt_or_ge r 1 with hr0 | hr1
      · -- r = 0: every refined singleton is non-free: stream contradiction
        exfalso
        have hr0' : r = 0 := by omega
        subst hr0'
        refine singleton_support_transversals_refuted h0 hcov hanchor hfail ?_
        intro N
        set v := e (f₁ N) with hv
        have hvpos : 0 < v := hepos _
        have hnf : ¬RepFree A N₀ {v} := by
          refine hallnonfree {v} ?_ (Finset.card_singleton v)
          intro h hh
          exact ⟨N, by rw [Finset.mem_singleton.1 hh]⟩
        rw [repFree_iff_no_support_transversal, not_not] at hnf
        obtain ⟨m, hm, hhub⟩ := hnf
        obtain ⟨x, hx, y, hy, hxy⟩ := hcov m hm
        have hvm : v ≤ m := by
          rcases hhub x hx y hy 0 h0 (by omega) with h | h | h
          · have := Finset.mem_singleton.1 h
            omega
          · have := Finset.mem_singleton.1 h
            omega
          · have := Finset.mem_singleton.1 h
            omega
        have hNv : N ≤ v := by
          have h1 : N ≤ f₁ N := hf₁.le_apply
          have h2 : f₁ N ≤ e (f₁ N) := hemono.le_apply
          omega
        exact ⟨m, by omega, v, hvpos, hhub⟩
      · -- recurse one level down on the refined stream
        obtain ⟨d', f₂, hd'1, hd'le, hf₂, hfree', hnonfree'⟩ :=
          ihd r (by omega) (fun i => e (f₁ i)) hr1
            (fun i j hij => hemono (hf₁ hij))
            (fun j => heA _) (fun j => hepos _)
            (by
              intro S hSmem hScard
              exact hallnonfree S hSmem (by omega))
        refine ⟨d', f₁ ∘ f₂, hd'1, by omega, hf₁.comp hf₂, ?_, ?_⟩
        · intro S hSmem hScard
          exact hfree' S hSmem hScard
        · intro S hSmem hScard
          exact hnonfree' S hSmem hScard

theorem rank_lt_omega_perfect_clique {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (b : ℕ → ℕ) (hbmono : StrictMono b)
    (hbA : ∀ j, b j ∈ A) (hbpos : ∀ j, 0 < b j)
    (hrank : ((poolFreeStep_wf h0 hcov hfail
      (Set.range b)).apply ∅).rank < Ordinal.omega0) :
    ∃ (d : ℕ) (f : ℕ → ℕ), 1 ≤ d ∧ StrictMono f ∧
      (∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, b (f i) = h) → S.card = d →
        RepFree A N₀ S) ∧
      (∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, b (f i) = h) →
        S.card = d + 1 → ∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m S) := by
  classical
  obtain ⟨D, hD⟩ := Ordinal.lt_omega0.1 hrank
  have hDpos : 1 ≤ D := by
    have h1 := pool_rank_pos h0 hcov hanchor hfail
      (P₀ := Set.range b) (by rintro x ⟨j, rfl⟩; exact hbA j)
      (by rintro ⟨j, hj⟩
          have h2 : b j = 0 := hj
          have := hbpos j
          omega)
      (by intro X
          refine ⟨b X, ⟨X, rfl⟩, ?_⟩
          exact hbmono.le_apply)
    rw [hD] at h1
    exact_mod_cast h1
  have hnonfree : ∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, b i = h) →
      S.card = D + 1 → ¬RepFree A N₀ S := by
    intro S hSmem hScard hfree
    have hSnode : FreeNode A N₀ S := by
      refine ⟨?_, hfree⟩
      intro h hh
      obtain ⟨i, hi⟩ := hSmem h hh
      rw [← hi]
      exact ⟨hbA i, hbpos i⟩
    have hSpool : ∀ h ∈ S, h ∈ Set.range b := by
      intro h hh
      obtain ⟨i, hi⟩ := hSmem h hh
      exact ⟨i, hi⟩
    have h1 := free_set_card_le_rank h0 hcov hfail hSnode hSpool
    rw [hScard, hD] at h1
    have h2 : D + 1 ≤ D := by exact_mod_cast h1
    omega
  obtain ⟨d, f, hd1, hdle, hf, hfree, hnf⟩ := clique_descent h0 hcov
    hanchor hfail D b hDpos hbmono hbA hbpos hnonfree
  refine ⟨d, f, hd1, hf, hfree, ?_⟩
  intro S hSmem hScard
  have h1 := hnf S hSmem hScard
  rw [repFree_iff_no_support_transversal, not_not] at h1
  exact h1

theorem perfect_model_small_sets_free {A : Set ℕ} {N₀ : ℕ}
    {e : ℕ → ℕ} {d : ℕ} (hemono : StrictMono e)
    (hfree : ∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, e i = h) →
      S.card = d → RepFree A N₀ S)
    {H : Finset ℕ} (hHmem : ∀ h ∈ H, ∃ i, e i = h)
    (hHcard : H.card ≤ d) : RepFree A N₀ H := by
  classical
  set M := H.sup id with hM
  have hMbound : ∀ h ∈ H, h ≤ M := fun h hh =>
    Finset.le_sup (f := id) hh
  set K := M + 1 with hK
  set T := (Finset.range (d - H.card)).image
    (fun j => e (K + j)) with hT
  have hTbig : ∀ t ∈ T, M < t := by
    intro t ht
    obtain ⟨j, -, hjt⟩ := Finset.mem_image.1 ht
    have h1 : K + j ≤ e (K + j) := hemono.le_apply
    omega
  have hdisj : Disjoint H T := by
    rw [Finset.disjoint_left]
    intro h hh hT'
    have h1 := hMbound h hh
    have h2 := hTbig h hT'
    omega
  have hTcard : T.card = d - H.card := by
    rw [hT, Finset.card_image_of_injective _
      (fun i j hij => by
        have := hemono.injective hij
        omega),
      Finset.card_range]
  have hUcard : (H ∪ T).card = d := by
    rw [Finset.card_union_of_disjoint hdisj]
    omega
  have hUmem : ∀ h ∈ H ∪ T, ∃ i, e i = h := by
    intro h hh
    rcases Finset.mem_union.1 hh with h' | h'
    · exact hHmem h h'
    · obtain ⟨j, -, hjt⟩ := Finset.mem_image.1 h'
      exact ⟨K + j, hjt⟩
  exact RepFree.mono Finset.subset_union_left
    (hfree (H ∪ T) hUmem hUcard)

theorem perfect_model_rank {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {e : ℕ → ℕ} {d : ℕ} (hemono : StrictMono e)
    (heA : ∀ j, e j ∈ A) (hepos : ∀ j, 0 < e j)
    (hfree : ∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, e i = h) → S.card = d →
      RepFree A N₀ S)
    (hhub : ∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, e i = h) →
      S.card = d + 1 → ¬RepFree A N₀ S) :
    ((poolFreeStep_wf h0 hcov hfail (Set.range e)).apply ∅).rank
      = (d : Ordinal.{0}) := by
  classical
  apply le_antisymm
  · -- rank ≤ d: a free (d+1)-set from the pool would contradict hhub
    by_contra hgt
    push Not at hgt
    have hge : ((d + 1 : ℕ) : Ordinal.{0}) ≤
        ((poolFreeStep_wf h0 hcov hfail (Set.range e)).apply
          ∅).rank := by
      have h1 : ((d : ℕ) : Ordinal.{0}) <
          ((poolFreeStep_wf h0 hcov hfail (Set.range e)).apply
            ∅).rank := hgt
      have h2 : ((d + 1 : ℕ) : Ordinal.{0}) =
          Order.succ ((d : ℕ) : Ordinal.{0}) := by
        rw [Nat.cast_succ, Order.succ_eq_add_one]
      rw [h2]
      exact Order.succ_le_of_lt h1
    obtain ⟨Q, hQnode, hQpool, hQcard⟩ := rank_ge_imp_free_set
      h0 hcov hfail (d + 1) ∅
      ⟨fun h hh => absurd hh (Finset.notMem_empty h), by
        intro m hm
        obtain ⟨x, hx, y, hy, hxy⟩ := hcov m hm
        exact ⟨x, hx, y, hy, 0, h0, by omega,
          Finset.notMem_empty x, Finset.notMem_empty y,
          Finset.notMem_empty 0⟩⟩
      (fun h hh => absurd hh (Finset.notMem_empty h)) hge
    refine hhub Q ?_ (by simpa using hQcard) hQnode.2
    intro h hh
    exact hQpool h hh
  · -- rank ≥ d: any free d-subset of the stream certifies it
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · subst hd0
      simp
    · -- build a free d-set: the first d stream values
      set S := (Finset.range d).image e with hS
      have hSmem : ∀ h ∈ S, ∃ i, e i = h := by
        intro h hh
        obtain ⟨j, -, hjh⟩ := Finset.mem_image.1 hh
        exact ⟨j, hjh⟩
      have hScard : S.card = d := by
        rw [hS, Finset.card_image_of_injective _ hemono.injective,
          Finset.card_range]
      have hSfree : RepFree A N₀ S := hfree S hSmem hScard
      have hSnode : FreeNode A N₀ S := by
        refine ⟨?_, hSfree⟩
        intro h hh
        obtain ⟨i, hi⟩ := hSmem h hh
        rw [← hi]
        exact ⟨heA i, hepos i⟩
      have hSpool : ∀ h ∈ S, h ∈ Set.range e := by
        intro h hh
        obtain ⟨i, hi⟩ := hSmem h hh
        exact ⟨i, hi⟩
      have := free_set_card_le_rank h0 hcov hfail hSnode hSpool
      rw [hScard] at this
      exact this

theorem perfect_model_target_dominates_all {A : Set ℕ} {N₀ : ℕ}
    {e : ℕ → ℕ} {d : ℕ} (hemono : StrictMono e)
    (hfree : ∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, e i = h) → S.card = d →
      RepFree A N₀ S)
    {S : Finset ℕ} (hSmem : ∀ h ∈ S, ∃ i, e i = h)
    (hScard : S.card = d + 1)
    {m : ℕ} (hm : N₀ ≤ m) (hhub : IsRepSupportTransversal A m S) :
    ∀ s ∈ S, s ≤ m := by
  intro s hs
  have herase : (S.erase s).card ≤ d := by
    have := Finset.card_erase_of_mem hs
    omega
  have heraseF : RepFree A N₀ (S.erase s) :=
    perfect_model_small_sets_free hemono hfree
      (fun h hh => hSmem h (Finset.mem_of_mem_erase hh)) herase
  obtain ⟨x, hx, y, hy, z, hz, hsum, hxE, hyE, hzE⟩ := heraseF m hm
  rcases hhub x hx y hy z hz hsum with h | h | h
  · have hxs : x = s := by
      by_contra hne
      exact hxE (Finset.mem_erase.2 ⟨hne, h⟩)
    omega
  · have hys : y = s := by
      by_contra hne
      exact hyE (Finset.mem_erase.2 ⟨hne, h⟩)
    omega
  · have hzs : z = s := by
      by_contra hne
      exact hzE (Finset.mem_erase.2 ⟨hne, h⟩)
    omega

theorem perfect_model_sidon_targets {A : Set ℕ} {N₀ : ℕ}
    [DecidablePred (· ∈ A)]
    (h0 : 0 ∈ A) {e : ℕ → ℕ} {d : ℕ} (hepos : ∀ j, 0 < e j)
    {S : Finset ℕ} (hSmem : ∀ h ∈ S, ∃ i, e i = h)
    (hScard : S.card = d + 1)
    {m : ℕ} (hhub : IsRepSupportTransversal A m S) :
    ((Finset.range (m + 1)).filter
      (fun x => x ∈ A ∧ (m - x) ∈ A)).card ≤ 2 * (d + 1) := by
  have h0S : 0 ∉ S := by
    intro h
    obtain ⟨i, hi⟩ := hSmem 0 h
    have := hepos i
    omega
  have := pair_count_of_support_transversal h0 hhub h0S
  omega

theorem perfect_model_deletion_support_transversals_card {A B : Set ℕ} {N₀ : ℕ}
    [DecidablePred (· ∈ B)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B' ⊆ A, B'.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B') 3)
    {e : ℕ → ℕ} {d : ℕ} (hemono : StrictMono e)
    (heA : ∀ j, e j ∈ A) (hepos : ∀ j, 0 < e j)
    (hfree : ∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, e i = h) → S.card = d →
      RepFree A N₀ S)
    (hBsub : B ⊆ Set.range e) (hBinf : B.Infinite) :
    ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      IsRepSupportTransversal A n H ∧ (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
      d + 1 ≤ H.card ∧ ∀ h ∈ H, h ∈ B := by
  classical
  have hBA : B ⊆ A := fun x hx => by
    obtain ⟨j, rfl⟩ := hBsub hx
    exact heA j
  have h0B : 0 ∉ B := by
    intro h
    obtain ⟨j, hj⟩ := hBsub h
    have h1 : e j = 0 := hj
    have := hepos j
    omega
  have hteams := minimalSupportTransversals_from_infiniteDeletion h0 hcov hanchor
    hfail hBA hBinf h0B
  intro N
  obtain ⟨n, hn, H, hhub, hmin, hcard2, hHB⟩ := hteams (max N N₀)
  refine ⟨n, le_trans (le_max_left _ _) hn, H, hhub, hmin, ?_, hHB⟩
  by_contra hlt
  push Not at hlt
  have hHmem : ∀ h ∈ H, ∃ i, e i = h := by
    intro h hh
    obtain ⟨j, hj⟩ := hBsub (hHB h hh)
    exact ⟨j, hj⟩
  have hHfree : RepFree A N₀ H :=
    perfect_model_small_sets_free hemono hfree hHmem (by omega)
  obtain ⟨x, hx, y, hy, z, hz, hsum, hxH, hyH, hzH⟩ :=
    hHfree n (le_trans (le_max_right _ _) hn)
  rcases hhub x hx y hy z hz hsum with h | h | h
  · exact hxH h
  · exact hyH h
  · exact hzH h

/-- Pair-freeness implies rep-freeness for 0-free sets: a surviving
pair padded with `0` is a surviving triple. -/
theorem repFree_of_pairFree {A : Set ℕ} {N₀ : ℕ} {P : Finset ℕ}
    (h0 : 0 ∈ A) (h0P : 0 ∉ P) (hfree : PairFree A N₀ P) :
    RepFree A N₀ P := by
  intro m hm
  obtain ⟨x, hx, y, hy, hxy, hxP, hyP⟩ := hfree m hm
  exact ⟨x, hx, y, hy, 0, h0, by omega, hxP, hyP, h0P⟩

/-- The order-2 tree embeds in the order-3 tree: every pair-free
step is a rep-free step (nodes have positive elements, so `0` never
occurs). -/
theorem freeStep_of_pairFreeStep {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) {Q P : Finset ℕ}
    (h : PairFreeStep A N₀ Q P) : FreeStep A N₀ Q P := by
  obtain ⟨⟨hPpos, hPfree⟩, ⟨hQpos, hQfree⟩, b, hbA, hbpos, hbmax,
    hQeq⟩ := h
  have h0P : 0 ∉ P := fun hh => by
    have := (hPpos 0 hh).2
    omega
  have h0Q : 0 ∉ Q := fun hh => by
    have := (hQpos 0 hh).2
    omega
  exact ⟨⟨hPpos, repFree_of_pairFree h0 h0P hPfree⟩,
    ⟨hQpos, repFree_of_pairFree h0 h0Q hQfree⟩,
    b, hbA, hbpos, hbmax, hQeq⟩

theorem pair_rank_le_rep_rank {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hmin : ∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (P : Finset ℕ) :
    ((pairFreeStep_wf hcov hmin).apply P).rank ≤
    ((freeStep_wf h0 hcov hfail).apply P).rank :=
  rank_le_of_subrel (fun _ _ h => freeStep_of_pairFreeStep h0 h) _ _

/-- Pair-support transversal-freeness of a set is exactly pair-freeness. -/
theorem pairFree_iff_no_pairSupportTransversal {A : Set ℕ} {N₀ : ℕ}
    {S : Finset ℕ} :
    PairFree A N₀ S ↔ ¬∃ m, N₀ ≤ m ∧ IsPairSupportTransversal A m S := by
  constructor
  · rintro hfree ⟨m, hm, hhub⟩
    obtain ⟨x, hx, y, hy, hs, hxS, hyS⟩ := hfree m hm
    rcases hhub x hx y hy hs with h | h
    · exact hxS h
    · exact hyS h
  · intro hno m hm
    by_contra hall
    push Not at hall
    refine hno ⟨m, hm, ?_⟩
    intro x hx y hy hs
    by_contra hmiss
    push Not at hmiss
    obtain ⟨h1, h2⟩ := hmiss
    exact h2 (hall x hx y hy hs h1)

theorem pair_clique_descent {A : Set ℕ} {N₀ : ℕ} :
    ∀ (d : ℕ) (e : ℕ → ℕ), 1 ≤ d → StrictMono e →
    (∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, e i = h) → S.card = d + 1 →
      ¬PairFree A N₀ S) →
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ((∀ i, ¬PairFree A N₀ {e (f i)}) ∨
      (∃ d', 1 ≤ d' ∧ d' ≤ d ∧
        (∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, e (f i) = h) →
          S.card = d' → PairFree A N₀ S) ∧
        (∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, e (f i) = h) →
          S.card = d' + 1 → ¬PairFree A N₀ S))) := by
  classical
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
    intro e hd1 hemono hnonfree
    obtain ⟨r, rfl⟩ : ∃ r, d = r + 1 := ⟨d - 1, by omega⟩
    set c : (Fin (r + 1) → ℕ) → Bool := fun t =>
      if PairFree A N₀ (Finset.univ.image (fun i => e (t i)))
      then true else false with hc
    have hciff : ∀ t : Fin (r + 1) → ℕ, c t = true ↔
        PairFree A N₀ (Finset.univ.image (fun i => e (t i))) := by
      intro t
      by_cases h : PairFree A N₀
        (Finset.univ.image (fun i => e (t i)))
      · simp [hc, h]
      · simp [hc, h]
    obtain ⟨f₁, hf₁, bt, hhom⟩ := infinite_ramsey_tuples r c
    rcases Bool.eq_false_or_eq_true bt with hbt | hbt
    · -- perfect pair-uniform_structure at level r + 1
      subst hbt
      refine ⟨f₁, hf₁, Or.inr ⟨r + 1, by omega, le_refl _, ?_, ?_⟩⟩
      · intro S hSmem hScard
        obtain ⟨u, humono, huim⟩ := sorted_indices_of_card
          (fun i j hij => hemono (hf₁ hij)) hScard hSmem
        have h1 := hhom u humono
        rw [hciff] at h1
        have h2 : (Finset.univ.image fun i => e (f₁ (u i))) = S :=
          huim
        rw [h2] at h1
        exact h1
      · intro S hSmem hScard
        refine hnonfree S ?_ hScard
        intro h hh
        obtain ⟨i, hi⟩ := hSmem h hh
        exact ⟨f₁ i, hi⟩
    · subst hbt
      have hallnonfree : ∀ S : Finset ℕ,
          (∀ h ∈ S, ∃ i, e (f₁ i) = h) → S.card = r + 1 →
          ¬PairFree A N₀ S := by
        intro S hSmem hScard hfree
        obtain ⟨u, humono, huim⟩ := sorted_indices_of_card
          (fun i j hij => hemono (hf₁ hij)) hScard hSmem
        have h1 := hhom u humono
        have h2 : c (fun i => f₁ (u i)) = true := by
          rw [hciff]
          have h3 : (Finset.univ.image fun i => e (f₁ (u i))) = S :=
            huim
          rw [h3]
          exact hfree
        rw [h1] at h2
        exact Bool.false_ne_true h2
      rcases Nat.lt_or_ge r 1 with hr0 | hr1
      · -- r = 0: every refined singleton 2-required elements — the legal floor
        have hr0' : r = 0 := by omega
        subst hr0'
        refine ⟨f₁, hf₁, Or.inl ?_⟩
        intro i
        refine hallnonfree {e (f₁ i)} ?_ (Finset.card_singleton _)
        intro h hh
        exact ⟨i, by rw [Finset.mem_singleton.1 hh]⟩
      · obtain ⟨f₂, hf₂, hout⟩ := ihd r (by omega)
          (fun i => e (f₁ i)) hr1
          (fun i j hij => hemono (hf₁ hij))
          (by
            intro S hSmem hScard
            exact hallnonfree S hSmem (by omega))
        rcases hout with hguard | ⟨d', hd'1, hd'le, hfree', hnf'⟩
        · exact ⟨f₁ ∘ f₂, hf₁.comp hf₂, Or.inl hguard⟩
        · exact ⟨f₁ ∘ f₂, hf₁.comp hf₂, Or.inr
            ⟨d', hd'1, by omega, hfree', hnf'⟩⟩

theorem stream_pair_classification (A : Set ℕ) (N₀ : ℕ)
    (e : ℕ → ℕ) (hemono : StrictMono e) :
    (∀ n, ∃ S : Finset ℕ, (∀ h ∈ S, ∃ i, e i = h) ∧ S.card = n ∧
      PairFree A N₀ S) ∨
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ((∀ i, ¬PairFree A N₀ {e (f i)}) ∨
      (∃ d, 1 ≤ d ∧
        (∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, e (f i) = h) →
          S.card = d → PairFree A N₀ S) ∧
        (∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, e (f i) = h) →
          S.card = d + 1 → ¬PairFree A N₀ S))) := by
  classical
  by_cases hwide : ∀ n, ∃ S : Finset ℕ,
      (∀ h ∈ S, ∃ i, e i = h) ∧ S.card = n ∧ PairFree A N₀ S
  · exact Or.inl hwide
  · right
    push Not at hwide
    obtain ⟨n, hn⟩ := hwide
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · -- n ≤ 1: every singleton is non-free (directly, or via ∅)
      refine ⟨id, fun i j hij => hij, Or.inl ?_⟩
      intro i
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        have hempt : ¬PairFree A N₀ (∅ : Finset ℕ) := by
          intro hfree
          exact absurd hfree (hn ∅ (fun h hh =>
            absurd hh (Finset.notMem_empty h)) rfl)
        intro hfree
        exact hempt (PairFree.mono (Finset.empty_subset _) hfree)
      · have hn1 : n = 1 := by omega
        subst hn1
        intro hfree
        exact hn {e (id i)} (fun h hh =>
          ⟨i, (Finset.mem_singleton.1 hh).symm⟩)
          (Finset.card_singleton _) hfree
    · -- n ≥ 2: run the descent at level n − 1
      have hnonfree : ∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, e i = h) →
          S.card = (n - 1) + 1 → ¬PairFree A N₀ S := by
        intro S hSmem hScard hfree
        exact hn S hSmem (by omega) hfree
      obtain ⟨f, hf, hout⟩ := pair_clique_descent (n - 1) e
        (by omega) hemono hnonfree
      rcases hout with hguard | ⟨d, hd1, -, hfree', hnf'⟩
      · exact ⟨f, hf, Or.inl hguard⟩
      · exact ⟨f, hf, Or.inr ⟨d, hd1, hfree', hnf'⟩⟩

theorem stream_rep_classification (A : Set ℕ) (N₀ : ℕ)
    (e : ℕ → ℕ) (hemono : StrictMono e) :
    (∀ n, ∃ S : Finset ℕ, (∀ h ∈ S, ∃ i, e i = h) ∧ S.card = n ∧
      RepFree A N₀ S) ∨
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ((∀ i, ¬RepFree A N₀ {e (f i)}) ∨
      (∃ d, 1 ≤ d ∧
        (∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, e (f i) = h) →
          S.card = d → RepFree A N₀ S) ∧
        (∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, e (f i) = h) →
          S.card = d + 1 → ¬RepFree A N₀ S))) := by
  classical
  by_cases hwide : ∀ n, ∃ S : Finset ℕ,
      (∀ h ∈ S, ∃ i, e i = h) ∧ S.card = n ∧ RepFree A N₀ S
  · exact Or.inl hwide
  · right
    push Not at hwide
    obtain ⟨n, hn⟩ := hwide
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · refine ⟨id, fun i j hij => hij, Or.inl ?_⟩
      intro i
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        have hempt : ¬RepFree A N₀ (∅ : Finset ℕ) := by
          intro hfree
          exact absurd hfree (hn ∅ (fun h hh =>
            absurd hh (Finset.notMem_empty h)) rfl)
        intro hfree
        exact hempt (RepFree.mono (Finset.empty_subset _) hfree)
      · have hn1 : n = 1 := by omega
        subst hn1
        intro hfree
        exact hn {e (id i)} (fun h hh =>
          ⟨i, (Finset.mem_singleton.1 hh).symm⟩)
          (Finset.card_singleton _) hfree
    · -- run an inline descent at level n − 1 (mirror of
      -- pair_clique_descent with the floor kept as a branch)
      suffices hdesc : ∀ (d : ℕ) (e' : ℕ → ℕ), 1 ≤ d →
          StrictMono e' →
          (∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, e' i = h) →
            S.card = d + 1 → ¬RepFree A N₀ S) →
          ∃ f : ℕ → ℕ, StrictMono f ∧
            ((∀ i, ¬RepFree A N₀ {e' (f i)}) ∨
            (∃ d', 1 ≤ d' ∧
              (∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, e' (f i) = h) →
                S.card = d' → RepFree A N₀ S) ∧
              (∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, e' (f i) = h) →
                S.card = d' + 1 → ¬RepFree A N₀ S))) by
        obtain ⟨f, hf, hout⟩ := hdesc (n - 1) e (by omega) hemono
          (by
            intro S hSmem hScard hfree
            exact hn S hSmem (by omega) hfree)
        exact ⟨f, hf, hout⟩
      intro d
      induction d using Nat.strong_induction_on with
      | _ d ihd =>
        intro e' hd1 hemono' hnonfree
        obtain ⟨r, rfl⟩ : ∃ r, d = r + 1 := ⟨d - 1, by omega⟩
        set c : (Fin (r + 1) → ℕ) → Bool := fun t =>
          if RepFree A N₀ (Finset.univ.image (fun i => e' (t i)))
          then true else false with hc
        have hciff : ∀ t : Fin (r + 1) → ℕ, c t = true ↔
            RepFree A N₀
              (Finset.univ.image (fun i => e' (t i))) := by
          intro t
          by_cases h : RepFree A N₀
            (Finset.univ.image (fun i => e' (t i)))
          · simp [hc, h]
          · simp [hc, h]
        obtain ⟨f₁, hf₁, bt, hhom⟩ := infinite_ramsey_tuples r c
        rcases Bool.eq_false_or_eq_true bt with hbt | hbt
        · subst hbt
          refine ⟨f₁, hf₁, Or.inr ⟨r + 1, by omega, ?_, ?_⟩⟩
          · intro S hSmem hScard
            obtain ⟨u, humono, huim⟩ := sorted_indices_of_card
              (fun i j hij => hemono' (hf₁ hij)) hScard hSmem
            have h1 := hhom u humono
            rw [hciff] at h1
            have h2 : (Finset.univ.image
                fun i => e' (f₁ (u i))) = S := huim
            rw [h2] at h1
            exact h1
          · intro S hSmem hScard
            refine hnonfree S ?_ hScard
            intro h hh
            obtain ⟨i, hi⟩ := hSmem h hh
            exact ⟨f₁ i, hi⟩
        · subst hbt
          have hallnonfree : ∀ S : Finset ℕ,
              (∀ h ∈ S, ∃ i, e' (f₁ i) = h) → S.card = r + 1 →
              ¬RepFree A N₀ S := by
            intro S hSmem hScard hfree
            obtain ⟨u, humono, huim⟩ := sorted_indices_of_card
              (fun i j hij => hemono' (hf₁ hij)) hScard hSmem
            have h1 := hhom u humono
            have h2 : c (fun i => f₁ (u i)) = true := by
              rw [hciff]
              have h3 : (Finset.univ.image
                  fun i => e' (f₁ (u i))) = S := huim
              rw [h3]
              exact hfree
            rw [h1] at h2
            exact Bool.false_ne_true h2
          rcases Nat.lt_or_ge r 1 with hr0 | hr1
          · have hr0' : r = 0 := by omega
            subst hr0'
            refine ⟨f₁, hf₁, Or.inl ?_⟩
            intro i
            refine hallnonfree {e' (f₁ i)} ?_
              (Finset.card_singleton _)
            intro h hh
            exact ⟨i, (Finset.mem_singleton.1 hh).symm⟩
          · obtain ⟨f₂, hf₂, hout⟩ := ihd r (by omega)
              (fun i => e' (f₁ i)) hr1
              (fun i j hij => hemono' (hf₁ hij))
              (by
                intro S hSmem hScard
                exact hallnonfree S hSmem (by omega))
            rcases hout with hguard | ⟨d', hd'1, hfree', hnf'⟩
            · exact ⟨f₁ ∘ f₂, hf₁.comp hf₂, Or.inl hguard⟩
            · exact ⟨f₁ ∘ f₂, hf₁.comp hf₂, Or.inr
                ⟨d', hd'1, hfree', hnf'⟩⟩

theorem rank_ge_imp_free_superset {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {P₀ : Set ℕ} :
    ∀ (n : ℕ) (P : Finset ℕ), FreeNode A N₀ P → (∀ h ∈ P, h ∈ P₀) →
      ((n : ℕ) : Ordinal.{0}) ≤
        ((poolFreeStep_wf h0 hcov hfail P₀).apply P).rank →
      ∃ Q : Finset ℕ, FreeNode A N₀ Q ∧ (∀ h ∈ Q, h ∈ P₀) ∧
        P ⊆ Q ∧ Q.card = P.card + n := by
  classical
  set hwf := poolFreeStep_wf h0 hcov hfail P₀ with hhwf
  intro n
  induction n with
  | zero =>
    intro P hPnode hPpool _
    exact ⟨P, hPnode, hPpool, Finset.Subset.refl P, by omega⟩
  | succ n ih =>
    intro P hPnode hPpool hrank
    have hpos : ((n : ℕ) : Ordinal.{0}) < (hwf.apply P).rank := by
      have h1 : ((n : ℕ) : Ordinal.{0}) <
          ((n + 1 : ℕ) : Ordinal.{0}) := by
        exact_mod_cast Nat.lt_succ_self n
      exact lt_of_lt_of_le h1 hrank
    rw [Acc.rank_eq] at hpos
    rw [Ordinal.lt_iSup_iff] at hpos
    obtain ⟨⟨C, hC⟩, hlt⟩ := hpos
    have hCrank : ((n : ℕ) : Ordinal.{0}) ≤
        (hwf.apply C).rank := by
      have h1 := Order.lt_succ_iff.1 hlt
      exact h1
    have hCnode : FreeNode A N₀ C := hC.1.2.1
    have hCpool : ∀ h ∈ C, h ∈ P₀ := hC.2
    obtain ⟨Q, hQnode, hQpool, hCQ, hQcard⟩ :=
      ih C hCnode hCpool hCrank
    obtain ⟨-, -, b, hbA, hbpos, hbmax, hCeq⟩ := hC.1
    have hbP : b ∉ P := fun h => by
      have := hbmax b h
      omega
    have hCcard : C.card = P.card + 1 := by
      rw [hCeq]
      rw [Finset.card_insert_of_notMem hbP]
    have hPC : P ⊆ C := by
      rw [hCeq]
      exact Finset.subset_insert _ _
    exact ⟨Q, hQnode, hQpool, Finset.Subset.trans hPC hCQ,
      by omega⟩

theorem stalled_pool_rank_bound {A : Set ℕ} {N₀ X : ℕ}
    [DecidablePred (· ∈ A)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {P₀ : Set ℕ} {P : Finset ℕ}
    (hst : Stalled A N₀ X P) (hPpool : ∀ h ∈ P, h ∈ P₀) :
    ((poolFreeStep_wf h0 hcov hfail P₀).apply P).rank ≤
      (((Finset.range X).filter (· ∈ A)).card : Ordinal.{0}) := by
  classical
  set W := ((Finset.range X).filter (· ∈ A)).card with hW
  by_contra hgt
  push Not at hgt
  have hge : ((W + 1 : ℕ) : Ordinal.{0}) ≤
      ((poolFreeStep_wf h0 hcov hfail P₀).apply P).rank := by
    have h2 : ((W + 1 : ℕ) : Ordinal.{0}) =
        Order.succ ((W : ℕ) : Ordinal.{0}) := by
      rw [Nat.cast_succ, Order.succ_eq_add_one]
    rw [h2]
    exact Order.succ_le_of_lt hgt
  obtain ⟨Q, hQnode, hQpool, hPQ, hQcard⟩ :=
    rank_ge_imp_free_superset h0 hcov hfail (W + 1) P hst.1
      hPpool hge
  -- every fresh element sits below the stall threshold
  have hfresh : ∀ q ∈ Q, q ∉ P → q < X := by
    intro q hq hqP
    by_contra hqX
    push Not at hqX
    have hqA : q ∈ A := (hQnode.1 q hq).1
    have hqpos : 0 < q := (hQnode.1 q hq).2
    refine hst.2 q hqA hqpos hqX ?_
    refine RepFree.mono ?_ hQnode.2
    intro x hx
    rcases Finset.mem_insert.1 hx with h | h
    · rw [h]
      exact hq
    · exact hPQ h
  -- count: Q ∖ P injects into the window
  have hsub : Q \ P ⊆ (Finset.range X).filter (· ∈ A) := by
    intro q hq
    obtain ⟨hqQ, hqP⟩ := Finset.mem_sdiff.1 hq
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2
      (hfresh q hqQ hqP), (hQnode.1 q hqQ).1⟩
  have h1 := Finset.card_le_card hsub
  have h2 : (Q \ P).card = Q.card - P.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hPQ]
  omega

theorem crossing_edge_exists {A : Set ℕ} {N₀ X : ℕ}
    [DecidablePred (· ∈ A)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {P₀ : Set ℕ}
    (hroot : Ordinal.omega0 ≤
      ((poolFreeStep_wf h0 hcov hfail P₀).apply ∅).rank)
    {P : Finset ℕ} (hst : Stalled A N₀ X P)
    (hPpool : ∀ h ∈ P, h ∈ P₀) :
    ∃ (R : Finset ℕ) (b : ℕ), FreeNode A N₀ R ∧
      (∀ h ∈ R, h ∈ P₀) ∧
      PoolFreeStep A N₀ P₀ (insert b R) R ∧
      Ordinal.omega0 ≤
        ((poolFreeStep_wf h0 hcov hfail P₀).apply R).rank ∧
      ((poolFreeStep_wf h0 hcov hfail P₀).apply
        (insert b R)).rank < Ordinal.omega0 := by
  classical
  set hwf := poolFreeStep_wf h0 hcov hfail P₀ with hhwf
  set n := P.card with hn
  set emb := P.orderEmbOfFin hn.symm with hemb
  set e : ℕ → ℕ := fun j => if h : j < n then emb ⟨j, h⟩ else 0
    with he
  have heval : ∀ j (h : j < n), e j = emb ⟨j, h⟩ := by
    intro j h
    simp [he, h]
  have hembP : ∀ (i : Fin n), emb i ∈ P :=
    fun i => P.orderEmbOfFin_mem hn.symm i
  set pre : ℕ → Finset ℕ := fun i => (Finset.range i).image e
    with hpre
  have hpresub : ∀ i, i ≤ n → pre i ⊆ P := by
    intro i hin x hx
    obtain ⟨j, hj, hjx⟩ := Finset.mem_image.1 hx
    have hj' : j < n := by
      have := Finset.mem_range.1 hj
      omega
    rw [← hjx, heval j hj']
    exact hembP _
  have hprenode : ∀ i, i ≤ n → FreeNode A N₀ (pre i) := by
    intro i hin
    exact ⟨fun h hh => hst.1.1 h (hpresub i hin hh),
      RepFree.mono (hpresub i hin) hst.1.2⟩
  have hprepool : ∀ i, i ≤ n → ∀ h ∈ pre i, h ∈ P₀ :=
    fun i hin h hh => hPpool h (hpresub i hin hh)
  have hprestep : ∀ i, i < n →
      PoolFreeStep A N₀ P₀ (pre (i + 1)) (pre i) := by
    intro i hin
    have hstep1 : pre (i + 1) = insert (e i) (pre i) := by
      show (Finset.range (i + 1)).image e =
        insert (e i) ((Finset.range i).image e)
      rw [Finset.range_add_one, Finset.image_insert]
    refine ⟨⟨hprenode i (by omega), hprenode (i + 1) (by omega),
      e i, ?_, ?_, ?_, hstep1⟩,
      fun h hh => hprepool (i + 1) (by omega) h hh⟩
    · rw [heval i hin]
      exact (hst.1.1 _ (hembP _)).1
    · rw [heval i hin]
      exact (hst.1.1 _ (hembP _)).2
    · intro h hh
      obtain ⟨j, hj, hjx⟩ := Finset.mem_image.1 hh
      have hj' : j < i := Finset.mem_range.1 hj
      have hjn : j < n := by omega
      rw [← hjx, heval j hjn, heval i hin]
      exact emb.strictMono (Fin.mk_lt_mk.2 hj')
  have hpreP : pre n = P := by
    apply Finset.eq_of_subset_of_card_le (hpresub n (le_refl n))
    have hcard : (pre n).card = n := by
      show ((Finset.range n).image e).card = n
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro i hi j hj hij
      have hi' : i < n := Finset.mem_range.1 (by simpa using hi)
      have hj' : j < n := Finset.mem_range.1 (by simpa using hj)
      rw [heval i hi', heval j hj'] at hij
      exact congrArg Fin.val (emb.injective hij)
    omega
  -- the last prefix has finite rank; find the first finite one
  have hlast : (hwf.apply (pre n)).rank < Ordinal.omega0 := by
    rw [hpreP]
    calc (hwf.apply P).rank
        ≤ (((Finset.range X).filter (· ∈ A)).card :
            Ordinal.{0}) :=
          stalled_pool_rank_bound h0 hcov hfail hst hPpool
      _ < Ordinal.omega0 := Ordinal.natCast_lt_omega0 _
  have hex : ∃ i, i ≤ n ∧ (hwf.apply (pre i)).rank <
      Ordinal.omega0 := ⟨n, le_refl n, hlast⟩
  have h0pre : pre 0 = ∅ := by
    show (Finset.range 0).image e = ∅
    simp
  -- minimal such index is positive
  have hspec := Nat.find_spec hex
  set i₀ := Nat.find hex with hi₀
  obtain ⟨hi₀n, hi₀fin⟩ := hspec
  have hi₀pos : 0 < i₀ := by
    rcases Nat.eq_zero_or_pos i₀ with h | h
    · exfalso
      have := hi₀fin
      rw [h, h0pre] at this
      exact absurd hroot (by
        push Not
        exact this)
    · exact h
  have hprev : ¬((hwf.apply (pre (i₀ - 1))).rank <
      Ordinal.omega0) := by
    intro hfin
    have := Nat.find_min hex (m := i₀ - 1) (by omega)
    exact this ⟨by omega, hfin⟩
  push Not at hprev
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, i₀ = j₀ + 1 := ⟨i₀ - 1, by omega⟩
  have hj₀prev : ¬((hwf.apply (pre j₀)).rank <
      Ordinal.omega0) := by
    have h1 : j₀ = i₀ - 1 := by omega
    rw [h1]
    exact fun h => absurd h (by
      push Not
      exact hprev)
  push Not at hj₀prev
  have hstep := hprestep j₀ (by omega)
  have hkey : insert (e j₀) (pre j₀) = pre (j₀ + 1) := by
    show _ = (Finset.range (j₀ + 1)).image e
    rw [Finset.range_add_one, Finset.image_insert]
  have hfin' : (hwf.apply (pre (j₀ + 1))).rank <
      Ordinal.omega0 := by
    rw [← hj₀]
    exact hi₀fin
  refine ⟨pre j₀, e j₀, hprenode j₀ (by omega),
    hprepool j₀ (by omega), ?_, hj₀prev, ?_⟩
  · rw [hkey]
    exact hstep
  · rw [hkey]
    exact hfin'

theorem cofinite_free_singletons {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ X, ∀ b ∈ A, X ≤ b → 0 < b → RepFree A N₀ {b} := by
  classical
  by_contra hno
  push Not at hno
  refine singleton_support_transversals_refuted h0 hcov hanchor hfail ?_
  intro N
  obtain ⟨b, hbA, hNb, hbpos, hnotfree⟩ := hno N
  rw [repFree_iff_no_support_transversal, not_not] at hnotfree
  obtain ⟨m, hm, hhub⟩ := hnotfree
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov m hm
  have hbm : b ≤ m := by
    rcases hhub x hx y hy 0 h0 (by omega) with h | h | h
    · have := Finset.mem_singleton.1 h
      omega
    · have := Finset.mem_singleton.1 h
      omega
    · have := Finset.mem_singleton.1 h
      omega
  exact ⟨m, by omega, b, hbpos, hhub⟩

theorem root_omega_dichotomy {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {P₀ : Set ℕ}
    (hroot : Ordinal.omega0 ≤
      ((poolFreeStep_wf h0 hcov hfail P₀).apply ∅).rank) :
    (∃ C : Finset ℕ, PoolFreeStep A N₀ P₀ C ∅ ∧
      Ordinal.omega0 ≤
        ((poolFreeStep_wf h0 hcov hfail P₀).apply C).rank) ∨
    ((poolFreeStep_wf h0 hcov hfail P₀).apply ∅).rank =
      Ordinal.omega0 := by
  classical
  set hwf := poolFreeStep_wf h0 hcov hfail P₀ with hhwf
  by_cases hwide : ∃ C : Finset ℕ, PoolFreeStep A N₀ P₀ C ∅ ∧
      Ordinal.omega0 ≤ (hwf.apply C).rank
  · exact Or.inl hwide
  · right
    push Not at hwide
    apply le_antisymm _ hroot
    rw [Acc.rank_eq]
    apply Ordinal.iSup_le
    rintro ⟨C, hC⟩
    have h1 : (hwf.apply C).rank < Ordinal.omega0 := hwide C hC
    exact Order.succ_le_of_lt h1

/-- The node-level ω-dichotomy: same as at the root. -/
theorem node_omega_dichotomy {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {P₀ : Set ℕ} (R : Finset ℕ)
    (hR : Ordinal.omega0 ≤
      ((poolFreeStep_wf h0 hcov hfail P₀).apply R).rank) :
    (∃ C : Finset ℕ, PoolFreeStep A N₀ P₀ C R ∧
      Ordinal.omega0 ≤
        ((poolFreeStep_wf h0 hcov hfail P₀).apply C).rank) ∨
    ((poolFreeStep_wf h0 hcov hfail P₀).apply R).rank =
      Ordinal.omega0 := by
  classical
  set hwf := poolFreeStep_wf h0 hcov hfail P₀ with hhwf
  by_cases hwide : ∃ C : Finset ℕ, PoolFreeStep A N₀ P₀ C R ∧
      Ordinal.omega0 ≤ (hwf.apply C).rank
  · exact Or.inl hwide
  · right
    push Not at hwide
    apply le_antisymm _ hR
    rw [Acc.rank_eq]
    apply Ordinal.iSup_le
    rintro ⟨C, hC⟩
    exact Order.succ_le_of_lt (hwide C hC)

theorem omega_node_exists {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {P₀ : Set ℕ}
    (hroot : Ordinal.omega0 ≤
      ((poolFreeStep_wf h0 hcov hfail P₀).apply ∅).rank) :
    ∃ R : Finset ℕ,
      ((poolFreeStep_wf h0 hcov hfail P₀).apply R).rank =
        Ordinal.omega0 := by
  classical
  set hwf := poolFreeStep_wf h0 hcov hfail P₀ with hhwf
  set S : Set Ordinal.{0} :=
    {o | ∃ R : Finset ℕ, (hwf.apply R).rank = o ∧
      Ordinal.omega0 ≤ o} with hS
  have hSne : S.Nonempty :=
    ⟨(hwf.apply ∅).rank, ∅, rfl, hroot⟩
  obtain ⟨R₀, hR₀rank, hR₀ge⟩ := Ordinal.lt_wf.min_mem S hSne
  rcases node_omega_dichotomy h0 hcov hfail R₀
    (by rw [hR₀rank]; exact hR₀ge) with ⟨C, hC, hCge⟩ | heq
  · exfalso
    have hmemC : (hwf.apply C).rank ∈ S := ⟨C, rfl, hCge⟩
    have hlt : (hwf.apply C).rank <
        Ordinal.lt_wf.min S ⟨_, hmemC⟩ := by
      have h1 : Ordinal.lt_wf.min S ⟨_, hmemC⟩ =
          Ordinal.lt_wf.min S hSne := by
        congr 1
      rw [h1, ← hR₀rank]
      exact Acc.rank_lt_of_rel _ hC
    exact Ordinal.lt_wf.not_lt_min S hmemC hlt
  · exact ⟨R₀, heq⟩

theorem omega_node_children_unbounded {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {P₀ : Set ℕ} {R : Finset ℕ}
    (hR : ((poolFreeStep_wf h0 hcov hfail P₀).apply R).rank =
      Ordinal.omega0) :
    ∀ (k X : ℕ), ∃ b, X ≤ b ∧
      PoolFreeStep A N₀ P₀ (insert b R) R ∧
      ((k : ℕ) : Ordinal.{0}) ≤
        ((poolFreeStep_wf h0 hcov hfail P₀).apply
          (insert b R)).rank := by
  classical
  set hwf := poolFreeStep_wf h0 hcov hfail P₀ with hhwf
  intro k X
  by_contra hno
  push Not at hno
  have hchildlt : ∀ C, PoolFreeStep A N₀ P₀ C R →
      (hwf.apply C).rank < Ordinal.omega0 := by
    intro C hC
    have := Acc.rank_lt_of_rel (hwf.apply R) hC
    rw [hR] at this
    exact this
  set g : ℕ → ℕ := fun b =>
    if h : PoolFreeStep A N₀ P₀ (insert b R) R then
      (Ordinal.lt_omega0.1 (hchildlt _ h)).choose
    else 0 with hg
  have hgspec : ∀ b (h : PoolFreeStep A N₀ P₀ (insert b R) R),
      (hwf.apply (insert b R)).rank = ((g b : ℕ) : Ordinal.{0}) := by
    intro b h
    have h1 : g b = (Ordinal.lt_omega0.1 (hchildlt _ h)).choose := by
      simp [hg, dif_pos h]
    rw [h1]
    exact (Ordinal.lt_omega0.1 (hchildlt _ h)).choose_spec
  set K := max k ((Finset.range X).sup g) + 1 with hK
  have hbound : (hwf.apply R).rank ≤ ((K : ℕ) : Ordinal.{0}) := by
    rw [Acc.rank_eq]
    apply Ordinal.iSup_le
    rintro ⟨C, hC⟩
    obtain ⟨-, -, b, hbA, hbpos, hbmax, hCeq⟩ := hC.1
    have hCstep : PoolFreeStep A N₀ P₀ (insert b R) R := by
      rw [← hCeq]
      exact hC
    rcases Nat.lt_or_ge b X with hbX | hbX
    · -- window child: capped by the finite sup
      have h1 : (hwf.apply C).rank = ((g b : ℕ) : Ordinal.{0}) := by
        rw [hCeq]
        exact hgspec b hCstep
      have h2 : g b ≤ (Finset.range X).sup g :=
        Finset.le_sup (Finset.mem_range.2 hbX)
      have h3 : g b + 1 ≤ K := by omega
      calc Order.succ ((hwf.apply C).rank)
          = ((g b + 1 : ℕ) : Ordinal.{0}) := by
            rw [h1, Nat.cast_succ, Order.succ_eq_add_one]
        _ ≤ ((K : ℕ) : Ordinal.{0}) := by exact_mod_cast h3
    · -- large child: capped by k
      have h1 : (hwf.apply (insert b R)).rank <
          ((k : ℕ) : Ordinal.{0}) := hno b hbX hCstep
      have h2 : (hwf.apply C).rank < ((k : ℕ) : Ordinal.{0}) := by
        rw [hCeq]
        exact h1
      have h3 : k ≤ K := by omega
      calc Order.succ ((hwf.apply C).rank)
          ≤ ((k : ℕ) : Ordinal.{0}) := Order.succ_le_of_lt h2
        _ ≤ ((K : ℕ) : Ordinal.{0}) := by exact_mod_cast h3
  rw [hR] at hbound
  exact absurd hbound (by
    push Not
    exact Ordinal.natCast_lt_omega0 K)

theorem omega_node_diagonal {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {P₀ : Set ℕ} {R : Finset ℕ}
    (hR : ((poolFreeStep_wf h0 hcov hfail P₀).apply R).rank =
      Ordinal.omega0) :
    ∃ b : ℕ → ℕ, StrictMono b ∧
      (∀ j, PoolFreeStep A N₀ P₀ (insert (b j) R) R) ∧
      ∀ j, ((j : ℕ) : Ordinal.{0}) ≤
        ((poolFreeStep_wf h0 hcov hfail P₀).apply
          (insert (b j) R)).rank := by
  classical
  have hpick := omega_node_children_unbounded h0 hcov hfail hR
  have hpick' : ∀ (k X : ℕ), ∃ b, X ≤ b ∧
      (PoolFreeStep A N₀ P₀ (insert b R) R ∧
      ((k : ℕ) : Ordinal.{0}) ≤
        ((poolFreeStep_wf h0 hcov hfail P₀).apply
          (insert b R)).rank) := by
    intro k X
    obtain ⟨b, h1, h2, h3⟩ := hpick k X
    exact ⟨b, h1, h2, h3⟩
  choose pk hpkX hpkdata using hpick'
  set b : ℕ → ℕ := fun j =>
    Nat.rec (pk 0 0) (fun j prev => pk (j + 1) (prev + 1)) j with hb
  have hbS : ∀ j, b (j + 1) = pk (j + 1) (b j + 1) := fun _ => rfl
  have hbmono : StrictMono b := by
    apply strictMono_nat_of_lt_succ
    intro j
    have h1 := hpkX (j + 1) (b j + 1)
    rw [hbS]
    omega
  have hbdata : ∀ j, PoolFreeStep A N₀ P₀ (insert (b j) R) R ∧
      ((j : ℕ) : Ordinal.{0}) ≤
        ((poolFreeStep_wf h0 hcov hfail P₀).apply
          (insert (b j) R)).rank := by
    intro j
    cases j with
    | zero => exact hpkdata 0 0
    | succ j =>
      rw [hbS]
      exact hpkdata (j + 1) (b j + 1)
  exact ⟨b, hbmono, fun j => (hbdata j).1, fun j => (hbdata j).2⟩

/-- An infinite set is hereditarily free when all its finite
subsets are rep-free: exactly a surviving deletion, since its
prefixes never obstruction any target. -/
def HereditarilyFree (A : Set ℕ) (N₀ : ℕ) (B : Set ℕ) : Prop :=
  B.Infinite ∧ (∀ b ∈ B, b ∈ A ∧ 0 < b) ∧
  ∀ P : Finset ℕ, (∀ h ∈ P, h ∈ B) → RepFree A N₀ P

theorem hfail_iff_no_hereditarily_free {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) :
    (∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) ↔
    ¬∃ B : Set ℕ, HereditarilyFree A N₀ B := by
  classical
  constructor
  · -- a hereditarily free set survives as a deletion
    rintro hfail ⟨B, hBinf, hBpos, hBfree⟩
    have hBA : B ⊆ A := fun b hb => (hBpos b hb).1
    refine hfail B hBA hBinf ⟨N₀, fun m hm => ?_⟩
    have hfree := hBfree ((Finset.range (m + 1)).filter
      (fun b => b ∈ B))
      (fun h hh => (Finset.mem_filter.1 hh).2)
    obtain ⟨x, hx, y, hy, z, hz, hsum, hxP, hyP, hzP⟩ :=
      hfree m hm
    have havoid : ∀ w, w ≤ m →
        w ∉ (Finset.range (m + 1)).filter (fun b => b ∈ B) →
        w ∉ B := by
      intro w hwm hwP hwB
      exact hwP (Finset.mem_filter.2
        ⟨Finset.mem_range.2 (by omega), hwB⟩)
    refine ⟨![x, y, z], ?_, by simp [Fin.sum_univ_three]; omega⟩
    intro i
    match i with
    | 0 => exact ⟨hx, havoid x (by omega) hxP⟩
    | 1 => exact ⟨hy, havoid y (by omega) hyP⟩
    | 2 => exact ⟨hz, havoid z (by omega) hzP⟩
  · -- without hereditarily free sets, every deletion fails
    intro hno B hBA hBinf hbasis
    obtain ⟨N₁, hN₁⟩ := hbasis
    set B' := {b ∈ B | 0 < b ∧ N₁ + 1 ≤ b} with hB'
    have hB'inf : B'.Infinite := by
      have h1 : B ⊆ B' ∪ {b | b ≤ N₁} := by
        intro b hb
        rcases Nat.lt_or_ge b (N₁ + 1) with h | h
        · exact Or.inr (by
            simp only [Set.mem_setOf_eq]
            omega)
        · exact Or.inl ⟨hb, by omega, h⟩
      by_contra hfin
      rw [Set.not_infinite] at hfin
      exact hBinf (Set.Finite.subset
        (hfin.union (Set.finite_le_nat _)) h1)
    have hnother : ¬HereditarilyFree A N₀ B' :=
      fun h => hno ⟨B', h⟩
    rw [HereditarilyFree] at hnother
    push Not at hnother
    obtain ⟨Q, hQB', hQnotfree⟩ := hnother hB'inf
      (fun b hb => ⟨hBA hb.1, hb.2.1⟩)
    rw [RepFree] at hQnotfree
    push Not at hQnotfree
    obtain ⟨n, hn, halln⟩ := hQnotfree
    have hhub : IsRepSupportTransversal A n Q := by
      intro x hx y hy z hz hsum
      by_contra hmiss
      push Not at hmiss
      obtain ⟨h1, h2, h3⟩ := hmiss
      exact h3 (halln x hx y hy z hz hsum h1 h2)

    obtain ⟨x, hx, y, hy, hxy⟩ := hcov n hn
    have hn₁ : N₁ ≤ n := by
      rcases hhub x hx y hy 0 h0 (by omega) with h | h | h
      · have := (hQB' x h).2.2
        omega
      · have := (hQB' y h).2.2
        omega
      · have := (hQB' 0 h).2.1
        omega
    -- but the basis provides an untouched representation
    obtain ⟨v, hv, hvsum⟩ := hN₁ n hn₁
    have hsum3 : v 0 + v 1 + v 2 = n := by
      have := hvsum
      simpa [Fin.sum_univ_three] using this
    rcases hhub (v 0) (hv 0).1 (v 1) (hv 1).1 (v 2) (hv 2).1 hsum3
      with h | h | h
    · exact (hv 0).2 ((hQB' _ h).1)
    · exact (hv 1).2 ((hQB' _ h).1)
    · exact (hv 2).2 ((hQB' _ h).1)

theorem freeStep_wf_iff_no_hereditarilyFree {A : Set ℕ} {N₀ : ℕ} :
    WellFounded (FreeStep A N₀) ↔
    ¬∃ B : Set ℕ, HereditarilyFree A N₀ B := by
  classical
  constructor
  · -- WF contradicts hereditarily free sets: their prefixes descend
    rintro hwf ⟨B, hBinf, hBpos, hBfree⟩
    rw [wellFounded_iff_isEmpty_descending_chain] at hwf
    -- enumerate B increasingly
    have hpick : ∀ X : ℕ, ∃ b ∈ B, X < b := by
      intro X
      obtain ⟨b, hb, hXb⟩ := hBinf.exists_gt X
      exact ⟨b, hb, hXb⟩
    choose nx hnxB hnxgt using hpick
    set e : ℕ → ℕ := fun j =>
      Nat.rec (nx 0) (fun _ prev => nx prev) j with he
    have heS : ∀ j, e (j + 1) = nx (e j) := fun _ => rfl
    have heB : ∀ j, e j ∈ B := by
      intro j
      cases j with
      | zero => exact hnxB 0
      | succ j =>
        rw [heS]
        exact hnxB _
    have hemono : StrictMono e := by
      apply strictMono_nat_of_lt_succ
      intro j
      rw [heS]
      exact hnxgt (e j)
    set f : ℕ → Finset ℕ := fun n => (Finset.range n).image e
      with hf
    have hfnode : ∀ n, FreeNode A N₀ (f n) := by
      intro n
      have hsub : ∀ h ∈ f n, h ∈ B := by
        intro h hh
        obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hh
        rw [← hj]
        exact heB j
      exact ⟨fun h hh => hBpos h (hsub h hh), hBfree (f n) hsub⟩
    have hfstep : ∀ n, FreeStep A N₀ (f (n + 1)) (f n) := by
      intro n
      have hins : f (n + 1) = insert (e n) (f n) := by
        show (Finset.range (n + 1)).image e = _
        rw [Finset.range_add_one, Finset.image_insert]
      refine ⟨hfnode n, hfnode (n + 1), e n,
        (hBpos _ (heB n)).1, (hBpos _ (heB n)).2, ?_, hins⟩
      intro h hh
      obtain ⟨j, hj, hjh⟩ := Finset.mem_image.1 hh
      have hj' : j < n := Finset.mem_range.1 hj
      rw [← hjh]
      exact hemono hj'
    exact hwf.false ⟨f, hfstep⟩
  · -- no hereditarily free set: chains terminate
    intro hno
    rw [wellFounded_iff_isEmpty_descending_chain]
    constructor
    rintro ⟨f, hf⟩
    -- the chain's union is hereditarily free
    have hbmem : ∀ n, ∃ b, b ∈ A ∧ 0 < b ∧ (∀ h ∈ f n, h < b) ∧
        f (n + 1) = insert b (f n) := fun n => (hf n).2.2
    choose b hbA hbpos hbmax hbins using hbmem
    have hbin : ∀ n, b n ∈ f (n + 1) := by
      intro n
      rw [hbins n]
      exact Finset.mem_insert_self _ _
    have hchain : ∀ n, f n ⊆ f (n + 1) := by
      intro n
      rw [hbins n]
      exact Finset.subset_insert _ _
    have hchain' : ∀ m n, m ≤ n → f m ⊆ f n := by
      intro m n hmn
      induction n with
      | zero =>
        have h0 : m = 0 := by omega
        subst h0
        exact Finset.Subset.refl _
      | succ n ih =>
        rcases Nat.lt_or_ge m (n + 1) with h | h
        · exact Finset.Subset.trans (ih (by omega)) (hchain n)
        · have h1 : m = n + 1 := by omega
          subst h1
          exact Finset.Subset.refl _
    have hbmono : StrictMono b := by
      apply strictMono_nat_of_lt_succ
      intro n
      exact hbmax (n + 1) (b n) (hbin n)
    set U : Set ℕ := {x | ∃ n, x ∈ f n} with hU
    refine hno ⟨U, ?_, ?_, ?_⟩
    · -- infinite via the strictly monotone picks
      have hsub : Set.range b ⊆ U := by
        rintro x ⟨n, rfl⟩
        exact ⟨n + 1, hbin n⟩
      exact Set.Infinite.mono hsub
        (Set.infinite_range_of_injective hbmono.injective)
    · rintro x ⟨n, hxn⟩
      exact (hf n).1.1 x hxn
    · intro P hP

      have hstage : ∀ h ∈ P, ∃ n, h ∈ f n := hP
      choose st hst using hstage
      set N := P.sup (fun h => if hh : h ∈ P then st h hh else 0)
        with hN
      have hPN : ∀ h ∈ P, h ∈ f N := by
        intro h hh
        have h1 : st h hh ≤ N := by
          have := Finset.le_sup (f := fun h' =>
            if hh' : h' ∈ P then st h' hh' else 0) hh
          simpa [hh] using this
        exact hchain' (st h hh) N h1 (hst h hh)
      exact RepFree.mono hPN (hf N).1.2

theorem hfail_iff_freeStep_wf {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) :
    (∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) ↔
    WellFounded (FreeStep A N₀) :=
  (hfail_iff_no_hereditarily_free h0 hcov).trans
    freeStep_wf_iff_no_hereditarilyFree.symm

/-- Hereditarily pair-free sets: all finite subsets pair-free —
exactly the deletions that leave order 2 alive. -/
def HereditarilyPairFree (A : Set ℕ) (N₀ : ℕ) (B : Set ℕ) : Prop :=
  B.Infinite ∧ (∀ b ∈ B, b ∈ A ∧ 0 < b) ∧
  ∀ P : Finset ℕ, (∀ h ∈ P, h ∈ B) → PairFree A N₀ P

theorem hmin_iff_no_hereditarilyPairFree {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀) :
    (∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) ↔
    ¬∃ B : Set ℕ, HereditarilyPairFree A N₀ B := by
  classical
  constructor
  · rintro hmin ⟨B, hBinf, hBpos, hBfree⟩
    have hBA : B ⊆ A := fun b hb => (hBpos b hb).1
    refine hmin B hBA hBinf ⟨N₀, fun m hm => ?_⟩
    have hfree := hBfree ((Finset.range (m + 1)).filter
      (fun b => b ∈ B))
      (fun h hh => (Finset.mem_filter.1 hh).2)
    obtain ⟨x, hx, y, hy, hxy, hxP, hyP⟩ := hfree m hm
    have havoid : ∀ w, w ≤ m →
        w ∉ (Finset.range (m + 1)).filter (fun b => b ∈ B) →
        w ∉ B := by
      intro w hwm hwP hwB
      exact hwP (Finset.mem_filter.2
        ⟨Finset.mem_range.2 (by omega), hwB⟩)
    exact ⟨x, hx, y, hy, havoid x (by omega) hxP,
      havoid y (by omega) hyP, hxy⟩
  · intro hno B hBA hBinf hbasis
    obtain ⟨N₁, hN₁⟩ := hbasis
    set B' := {b ∈ B | 0 < b ∧ N₁ + 1 ≤ b} with hB'
    have hB'inf : B'.Infinite := by
      have h1 : B ⊆ B' ∪ {b | b ≤ N₁} := by
        intro b hb
        rcases Nat.lt_or_ge b (N₁ + 1) with h | h
        · exact Or.inr (by
            simp only [Set.mem_setOf_eq]
            omega)
        · exact Or.inl ⟨hb, by omega, h⟩
      by_contra hfin
      rw [Set.not_infinite] at hfin
      exact hBinf (Set.Finite.subset
        (hfin.union (Set.finite_le_nat _)) h1)
    have hnother : ¬HereditarilyPairFree A N₀ B' :=
      fun h => hno ⟨B', h⟩
    rw [HereditarilyPairFree] at hnother
    push Not at hnother
    obtain ⟨Q, hQB', hQnotfree⟩ := hnother hB'inf
      (fun b hb => ⟨hBA hb.1, hb.2.1⟩)
    rw [PairFree] at hQnotfree
    push Not at hQnotfree
    obtain ⟨n, hn, halln⟩ := hQnotfree
    have hhub : IsPairSupportTransversal A n Q := by
      intro x hx y hy hsum
      by_contra hmiss
      push Not at hmiss
      obtain ⟨h1, h2⟩ := hmiss
      exact h2 (halln x hx y hy hsum h1)
    obtain ⟨x, hx, y, hy, hxy⟩ := hcov n hn
    have hn₁ : N₁ ≤ n := by
      rcases hhub x hx y hy hxy with h | h
      · have := (hQB' x h).2.2
        omega
      · have := (hQB' y h).2.2
        omega
    obtain ⟨x', hx', y', hy', hx'B, hy'B, hxy'⟩ := hN₁ n hn₁
    rcases hhub x' hx' y' hy' hxy' with h | h
    · exact hx'B ((hQB' _ h).1)
    · exact hy'B ((hQB' _ h).1)

theorem pairFreeStep_wf_iff_no_hereditarilyPairFree
    {A : Set ℕ} {N₀ : ℕ} :
    WellFounded (PairFreeStep A N₀) ↔
    ¬∃ B : Set ℕ, HereditarilyPairFree A N₀ B := by
  classical
  constructor
  · rintro hwf ⟨B, hBinf, hBpos, hBfree⟩
    rw [wellFounded_iff_isEmpty_descending_chain] at hwf
    have hpick : ∀ X : ℕ, ∃ b ∈ B, X < b := by
      intro X
      obtain ⟨b, hb, hXb⟩ := hBinf.exists_gt X
      exact ⟨b, hb, hXb⟩
    choose nx hnxB hnxgt using hpick
    set e : ℕ → ℕ := fun j =>
      Nat.rec (nx 0) (fun _ prev => nx prev) j with he
    have heS : ∀ j, e (j + 1) = nx (e j) := fun _ => rfl
    have heB : ∀ j, e j ∈ B := by
      intro j
      cases j with
      | zero => exact hnxB 0
      | succ j =>
        rw [heS]
        exact hnxB _
    have hemono : StrictMono e := by
      apply strictMono_nat_of_lt_succ
      intro j
      rw [heS]
      exact hnxgt (e j)
    set f : ℕ → Finset ℕ := fun n => (Finset.range n).image e
      with hf
    have hfnode : ∀ n, PairFreeNode A N₀ (f n) := by
      intro n
      have hsub : ∀ h ∈ f n, h ∈ B := by
        intro h hh
        obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hh
        rw [← hj]
        exact heB j
      exact ⟨fun h hh => hBpos h (hsub h hh), hBfree (f n) hsub⟩
    have hfstep : ∀ n, PairFreeStep A N₀ (f (n + 1)) (f n) := by
      intro n
      have hins : f (n + 1) = insert (e n) (f n) := by
        show (Finset.range (n + 1)).image e = _
        rw [Finset.range_add_one, Finset.image_insert]
      refine ⟨hfnode n, hfnode (n + 1), e n,
        (hBpos _ (heB n)).1, (hBpos _ (heB n)).2, ?_, hins⟩
      intro h hh
      obtain ⟨j, hj, hjh⟩ := Finset.mem_image.1 hh
      have hj' : j < n := Finset.mem_range.1 hj
      rw [← hjh]
      exact hemono hj'
    exact hwf.false ⟨f, hfstep⟩
  · intro hno
    rw [wellFounded_iff_isEmpty_descending_chain]
    constructor
    rintro ⟨f, hf⟩
    have hbmem : ∀ n, ∃ b, b ∈ A ∧ 0 < b ∧ (∀ h ∈ f n, h < b) ∧
        f (n + 1) = insert b (f n) := fun n => (hf n).2.2
    choose b hbA hbpos hbmax hbins using hbmem
    have hbin : ∀ n, b n ∈ f (n + 1) := by
      intro n
      rw [hbins n]
      exact Finset.mem_insert_self _ _
    have hchain' : ∀ m n, m ≤ n → f m ⊆ f n := by
      intro m n hmn
      induction n with
      | zero =>
        have h0 : m = 0 := by omega
        subst h0
        exact Finset.Subset.refl _
      | succ n ih =>
        rcases Nat.lt_or_ge m (n + 1) with h | h
        · refine Finset.Subset.trans (ih (by omega)) ?_
          rw [hbins n]
          exact Finset.subset_insert _ _
        · have h1 : m = n + 1 := by omega
          subst h1
          exact Finset.Subset.refl _
    have hbmono : StrictMono b := by
      apply strictMono_nat_of_lt_succ
      intro n
      exact hbmax (n + 1) (b n) (hbin n)
    refine hno ⟨{x | ∃ n, x ∈ f n}, ?_, ?_, ?_⟩
    · have hsub : Set.range b ⊆ {x | ∃ n, x ∈ f n} := by
        rintro x ⟨n, rfl⟩
        exact ⟨n + 1, hbin n⟩
      exact Set.Infinite.mono hsub
        (Set.infinite_range_of_injective hbmono.injective)
    · rintro x ⟨n, hxn⟩
      exact (hf n).1.1 x hxn
    · intro P hP
      choose st hst using hP
      set N := P.sup (fun h => if hh : h ∈ P then st h hh else 0)
        with hN
      have hPN : ∀ h ∈ P, h ∈ f N := by
        intro h hh
        have h1 : st h hh ≤ N := by
          have := Finset.le_sup (f := fun h' =>
            if hh' : h' ∈ P then st h' hh' else 0) hh
          simpa [hh] using this
        exact hchain' (st h hh) N h1 (hst h hh)
      exact PairFree.mono hPN (hf N).1.2

theorem counterexample_iff_both_trees_wf {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) :
    ((∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) ∧
    (∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)) ↔
    (WellFounded (PairFreeStep A N₀) ∧
      WellFounded (FreeStep A N₀)) := by
  constructor
  · rintro ⟨hmin, hfail⟩
    exact ⟨pairFreeStep_wf_iff_no_hereditarilyPairFree.2
      ((hmin_iff_no_hereditarilyPairFree hcov).1 hmin),
      (hfail_iff_freeStep_wf h0 hcov).1 hfail⟩
  · rintro ⟨hwf₂, hwf₃⟩
    exact ⟨(hmin_iff_no_hereditarilyPairFree hcov).2
      (pairFreeStep_wf_iff_no_hereditarilyPairFree.1 hwf₂),
      (hfail_iff_freeStep_wf h0 hcov).2 hwf₃⟩

/-- The pair tree inherits well-foundedness from the rep tree: it
is a subrelation (`freeStep_of_pairFreeStep`). -/
theorem pairFreeStep_wf_of_freeStep_wf {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hwf : WellFounded (FreeStep A N₀)) :
    WellFounded (PairFreeStep A N₀) :=
  Subrelation.wf (fun {_ _} h => freeStep_of_pairFreeStep h0 h) hwf

theorem counterexample_iff_rep_tree_wf {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) :
    ((∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) ∧
    (∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)) ↔
    WellFounded (FreeStep A N₀) := by
  rw [counterexample_iff_both_trees_wf h0 hcov]
  constructor
  · rintro ⟨-, hwf₃⟩
    exact hwf₃
  · intro hwf₃
    exact ⟨pairFreeStep_wf_of_freeStep_wf h0 hwf₃, hwf₃⟩

theorem sidon_has_branch {A : Set ℕ} {N₀ C : ℕ}
    [DecidablePred (· ∈ A)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hC : ∀ v, N₀ ≤ v → ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A)).card ≤ C) :
    ∃ B : Set ℕ, HereditarilyFree A N₀ B := by
  classical
  set D := C + N₀ + 2 with hD
  set thr : ℕ → ℕ := fun k =>
    ((D + 2) * (k + 2) + 2 * N₀ + 3) *
      ((D + 2) * (k + 2) + 2 * N₀ + 3) + 2 * N₀ with hthr
  have hpick : ∀ X : ℕ, ∃ a, a ∈ A ∧ X < a := by
    intro X
    obtain ⟨a, ha, hXa⟩ := pairCovers_unbounded hcov (X + 1)
    exact ⟨a, ha, by omega⟩
  choose nx hnxA hnxgt using hpick
  set b : ℕ → ℕ := fun j =>
    Nat.rec (nx (thr 0)) (fun j prev =>
      nx (max (thr (j + 1)) prev)) j with hb
  have hbS : ∀ j, b (j + 1) = nx (max (thr (j + 1)) (b j)) :=
    fun _ => rfl
  have hbA : ∀ j, b j ∈ A := by
    intro j
    cases j with
    | zero => exact hnxA _
    | succ j =>
      rw [hbS]
      exact hnxA _
  have hbthr : ∀ j, thr j < b j := by
    intro j
    cases j with
    | zero => exact hnxgt _
    | succ j =>
      rw [hbS]
      have h1 := hnxgt (max (thr (j + 1)) (b j))
      have h2 := le_max_left (thr (j + 1)) (b j)
      omega
  have hbmono : StrictMono b := by
    apply strictMono_nat_of_lt_succ
    intro j
    rw [hbS]
    have h1 := hnxgt (max (thr (j + 1)) (b j))
    have h2 := le_max_right (thr (j + 1)) (b j)
    omega
  have hbpos : ∀ j, 0 < b j := by
    intro j
    have h1 := hbthr j
    have h2 : 0 ≤ ((D + 2) * (j + 2) + 2 * N₀ + 3) *
        ((D + 2) * (j + 2) + 2 * N₀ + 3) := Nat.zero_le _
    have h3 : 2 * N₀ ≤ thr j := by
      show 2 * N₀ ≤ _ * _ + 2 * N₀
      omega
    omega

  have hcore : ∀ m, N₀ ≤ m → ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
      x + y + z = m ∧
      ∀ j, b j ≤ m → x ≠ b j ∧ y ≠ b j ∧ z ≠ b j := by
    intro m hm
    by_cases hwin : ∃ j, b j ≤ m
    · -- the window is present: count fibers against candidates
      obtain ⟨j₀, hj₀⟩ := hwin
      set idxF := (Finset.range (m + 1)).filter
        (fun j => b j ≤ m) with hidxF
      have hidxne : idxF.Nonempty := by
        refine ⟨j₀, Finset.mem_filter.2 ⟨?_, hj₀⟩⟩
        have : j₀ ≤ b j₀ := hbmono.le_apply
        exact Finset.mem_range.2 (by omega)
      set M := idxF.max' hidxne with hM
      have hMmem := idxF.max'_mem hidxne
      have hbMm : b M ≤ m := (Finset.mem_filter.1 hMmem).2
      have hidxbound : ∀ j, b j ≤ m → j ≤ M := by
        intro j hj
        refine idxF.le_max' j (Finset.mem_filter.2 ⟨?_, hj⟩)
        have : j ≤ b j := hbmono.le_apply
        exact Finset.mem_range.2 (by omega)
      set L := (D + 2) * (M + 2) + 2 * N₀ + 3 with hL
      have hLsq : L * L + 2 * N₀ < m :=
        lt_of_le_of_lt (le_of_eq rfl) (lt_of_lt_of_le
          (hbthr M) hbMm)
      have hm2N : 2 * N₀ ≤ m := by
        have : 0 ≤ L * L := Nat.zero_le _
        omega
      have hsqrt := covering_sqrt_lower (A := A) (N₀ := N₀)
        (n := m - N₀) hcov (by omega)
      set F := (Finset.range (m - N₀ + 1)).filter (· ∈ A) with hF
      have hLF : L ≤ F.card := by
        have h1 : L * L ≤ F.card * F.card := by omega
        have h2 := Nat.sqrt_le_sqrt h1
        rw [Nat.sqrt_eq, Nat.sqrt_eq] at h2
        exact h2
      set cand := (Finset.range (m - N₀ + 1)).filter
        (fun z => z ∈ A ∧ z ∉ Set.range b) with hcand
      set Wfin := (Finset.range (m - N₀ + 1)).filter
        (· ∈ Set.range b) with hWfin
      have hWcard : Wfin.card ≤ M + 1 := by
        have hsub : Wfin ⊆ (Finset.range (M + 1)).image b := by
          intro w hw
          obtain ⟨hwr, j, hj⟩ := Finset.mem_filter.1 hw
          have hwm : w ≤ m - N₀ := by
            have := Finset.mem_range.1 hwr
            omega
          have hjM : j ≤ M := hidxbound j (by
            rw [hj]
            omega)
          exact Finset.mem_image.2 ⟨j, Finset.mem_range.2
            (by omega), hj⟩
        calc Wfin.card ≤ _ := Finset.card_le_card hsub
          _ ≤ (Finset.range (M + 1)).card := Finset.card_image_le
          _ = M + 1 := Finset.card_range _
      have hcandF : F \ Wfin ⊆ cand := by
        intro z hz
        obtain ⟨hzF, hzW⟩ := Finset.mem_sdiff.1 hz
        obtain ⟨hzr, hzA⟩ := Finset.mem_filter.1 hzF
        refine Finset.mem_filter.2 ⟨hzr, hzA, ?_⟩
        intro hzb
        exact hzW (Finset.mem_filter.2 ⟨hzr, hzb⟩)
      have hcandcard : L - (M + 1) ≤ cand.card := by
        have h1 := Finset.card_le_card hcandF
        have h2 := Finset.le_card_sdiff Wfin F
        omega
      -- the good candidates admit a stream-avoiding pair
      by_cases hgood : ∃ z ∈ cand, ∃ x ∈ A, ∃ y ∈ A,
          x + y = m - z ∧ x ∉ Set.range b ∧ y ∉ Set.range b
      · obtain ⟨z, hzc, x, hx, y, hy, hxy, hxb, hyb⟩ := hgood
        obtain ⟨hzr, hzA, hzb⟩ := Finset.mem_filter.1 hzc
        have hzm : z ≤ m - N₀ := by
          have := Finset.mem_range.1 hzr
          omega
        refine ⟨x, hx, y, hy, z, hzA, by omega, ?_⟩
        intro j hj
        exact ⟨fun h => hxb ⟨j, h.symm⟩,
          fun h => hyb ⟨j, h.symm⟩, fun h => hzb ⟨j, h.symm⟩⟩
      · -- otherwise the candidates inject into the window fibers
        exfalso
        push Not at hgood
        set fib : ℕ → Finset ℕ := fun j =>
          (Finset.range (m - N₀ + 1)).filter
            (fun z => z ∈ A ∧ z + b j ≤ m ∧ m - z - b j ∈ A)
          with hfib
        have hcsub : cand ⊆ (Finset.range (M + 1)).biUnion fib := by
          intro z hzc
          obtain ⟨hzr, hzA, hzb⟩ := Finset.mem_filter.1 hzc
          have hzm : z ≤ m - N₀ := by
            have := Finset.mem_range.1 hzr
            omega
          obtain ⟨x, hx, y, hy, hxy⟩ := hcov (m - z) (by omega)
          have hbad := hgood z hzc
          have hxyb : x ∈ Set.range b ∨ y ∈ Set.range b := by
            by_cases hxb : x ∈ Set.range b
            · exact Or.inl hxb
            · exact Or.inr (hbad x hx y hy (by omega) hxb)
          rcases hxyb with ⟨j, hj⟩ | ⟨j, hj⟩
          · have hjM : j ≤ M := hidxbound j (by
              rw [hj]
              omega)
            refine Finset.mem_biUnion.2 ⟨j,
              Finset.mem_range.2 (by omega),
              Finset.mem_filter.2 ⟨hzr, hzA, ?_, ?_⟩⟩
            · rw [hj]
              omega
            · rw [hj]
              have h1 : m - z - x = y := by omega
              rw [h1]
              exact hy
          · have hjM : j ≤ M := hidxbound j (by
              rw [hj]
              omega)
            refine Finset.mem_biUnion.2 ⟨j,
              Finset.mem_range.2 (by omega),
              Finset.mem_filter.2 ⟨hzr, hzA, ?_, ?_⟩⟩
            · rw [hj]
              omega
            · rw [hj]
              have h1 : m - z - y = x := by omega
              rw [h1]
              exact hx
        have hfibcard : ∀ j ∈ Finset.range (M + 1),
            (fib j).card ≤ C + N₀ := by
          intro j _
          rcases Nat.lt_or_ge (m - b j) N₀ with hsmall | hbig
          · -- tiny window: members are below N₀
            have hsub : fib j ⊆ Finset.range N₀ := by
              intro z hz
              obtain ⟨-, -, hzb, -⟩ := Finset.mem_filter.1 hz
              exact Finset.mem_range.2 (by omega)
            calc (fib j).card ≤ _ := Finset.card_le_card hsub
              _ = N₀ := Finset.card_range _
              _ ≤ C + N₀ := by omega
          · -- genuine fiber: bounded by the Sidon count at m − b j
            have hsub : fib j ⊆ (Finset.range (m - b j + 1)).filter
                (fun z => z ∈ A ∧ (m - b j - z) ∈ A) := by
              intro z hz
              obtain ⟨hzr, hzA, hzb, hzA'⟩ := Finset.mem_filter.1 hz
              refine Finset.mem_filter.2
                ⟨Finset.mem_range.2 (by omega), hzA, ?_⟩
              have h1 : m - b j - z = m - z - b j := by omega
              rw [h1]
              exact hzA'
            calc (fib j).card ≤ _ := Finset.card_le_card hsub
              _ ≤ C := hC (m - b j) hbig
              _ ≤ C + N₀ := by omega
        have hcount : cand.card ≤ (M + 1) * (C + N₀) := by
          calc cand.card
              ≤ ((Finset.range (M + 1)).biUnion fib).card :=
                Finset.card_le_card hcsub
            _ ≤ ∑ j ∈ Finset.range (M + 1), (fib j).card :=
                Finset.card_biUnion_le
            _ ≤ (Finset.range (M + 1)).card * (C + N₀) := by
                have := Finset.sum_le_card_nsmul
                  (Finset.range (M + 1)) (fun j => (fib j).card)
                  (C + N₀) hfibcard
                simpa using this
            _ = (M + 1) * (C + N₀) := by
                rw [Finset.card_range]
        -- the arithmetic clash
        have hexp1 : (D + 2) * (M + 2) =
            D * M + 2 * M + 2 * D + 4 := by ring
        have hexp2 : (M + 1) * (C + N₀) =
            M * C + M * N₀ + C + N₀ := by ring
        have hexp3 : D * M = M * C + M * N₀ + 2 * M := by
          rw [hD]
          ring
        omega
    · -- no window at all: the covering pair suffices
      obtain ⟨x, hx, y, hy, hxy⟩ := hcov m hm
      refine ⟨x, hx, y, hy, 0, h0, by omega, ?_⟩
      intro j hj
      exact absurd ⟨j, hj⟩ hwin

  refine ⟨Set.range b, Set.infinite_range_of_injective
    hbmono.injective, ?_, ?_⟩
  · rintro w ⟨j, rfl⟩
    exact ⟨hbA j, hbpos j⟩
  · intro P hP m hm
    obtain ⟨x, hx, y, hy, z, hz, hsum, havoid⟩ := hcore m hm
    refine ⟨x, hx, y, hy, z, hz, hsum, ?_, ?_, ?_⟩
    · intro hxP
      obtain ⟨j, hj⟩ := hP x hxP
      exact (havoid j (by omega)).1 hj.symm
    · intro hyP
      obtain ⟨j, hj⟩ := hP y hyP
      exact (havoid j (by omega)).2.1 hj.symm
    · intro hzP
      obtain ⟨j, hj⟩ := hP z hzP
      exact (havoid j (by omega)).2.2 hj.symm

/-- Converse adapter: elementwise minimality implies tuple-form
minimality (a surviving tuple basis provides elementwise pairs). -/
theorem minimality_tuple_of_elementwise {A : Set ℕ}
    (hmin : ∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) :
    ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 2 := by
  rintro B hBA hBinf ⟨N₁, hN₁⟩
  refine hmin B hBA hBinf ⟨N₁, fun n hn => ?_⟩
  obtain ⟨v, hv, hvsum⟩ := hN₁ n hn
  have hsum2 : v 0 + v 1 = n := by
    have := hvsum
    simpa [Fin.sum_univ_two] using this
  exact ⟨v 0, (hv 0).1, v 1, (hv 1).1, (hv 0).2, (hv 1).2, hsum2⟩

theorem basis3_of_basis2 {S : Set ℕ}
    (hS : IsExactTupleAsymptoticBasis S 2) (hne : S.Nonempty) :
    IsExactTupleAsymptoticBasis S 3 := by
  obtain ⟨N₁, hN₁⟩ := hS
  obtain ⟨z₀, hz₀⟩ := hne
  refine ⟨N₁ + z₀, fun n hn => ?_⟩
  obtain ⟨v, hv, hvsum⟩ := hN₁ (n - z₀) (by omega)
  have hsum2 : v 0 + v 1 = n - z₀ := by
    have := hvsum
    simpa [Fin.sum_univ_two] using this
  refine ⟨![v 0, v 1, z₀], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hv 0
    · exact hv 1
    · exact hz₀
  · simp [Fin.sum_univ_three]
    omega

theorem hmin_tuple_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 2 := by
  intro B hBA hBinf hbasis2
  refine hfail B hBA hBinf (basis3_of_basis2 hbasis2 ?_)
  -- the surviving order-2 basis is nonempty: it represents targets
  obtain ⟨N₁, hN₁⟩ := hbasis2
  obtain ⟨v, hv, -⟩ := hN₁ N₁ (le_refl _)
  exact ⟨v 0, hv 0⟩

/-- Hereditary freeness passes to infinite subsets: branches
contain branches. -/
theorem HereditarilyFree.mono {A B B' : Set ℕ} {N₀ : ℕ}
    (hB : HereditarilyFree A N₀ B) (hsub : B' ⊆ B)
    (hinf : B'.Infinite) : HereditarilyFree A N₀ B' :=
  ⟨hinf, fun b hb => hB.2.1 b (hsub hb),
    fun P hP => hB.2.2 P (fun h hh => hsub (hP h hh))⟩

/-- Hereditary freeness survives removing finitely many elements:
branches are tail-robust. -/
theorem HereditarilyFree.diff_finite {A B : Set ℕ} {N₀ : ℕ}
    {S : Set ℕ} (hB : HereditarilyFree A N₀ B) (hS : S.Finite) :
    HereditarilyFree A N₀ (B \ S) :=
  hB.mono Set.diff_subset (hB.1.diff hS)

/-- The union of a branch with any subset of another branch need
not be free — but a branch always yields branches above any
threshold: the tail form used by deletion arguments. -/
theorem HereditarilyFree.tail {A B : Set ℕ} {N₀ : ℕ}
    (hB : HereditarilyFree A N₀ B) (X : ℕ) :
    HereditarilyFree A N₀ (B \ {b | b ≤ X}) :=
  hB.diff_finite (Set.finite_le_nat X)

theorem hereditarilyFree_iff_uniform {A : Set ℕ} {N₀ : ℕ}
    {B : Set ℕ} (hBinf : B.Infinite)
    (hBpos : ∀ b ∈ B, b ∈ A ∧ 0 < b) :
    HereditarilyFree A N₀ B ↔
    ∀ m, N₀ ≤ m → ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = m ∧
      x ∉ B ∧ y ∉ B ∧ z ∉ B := by
  classical
  constructor
  · rintro ⟨-, -, hfree⟩ m hm
    obtain ⟨x, hx, y, hy, z, hz, hsum, hxP, hyP, hzP⟩ :=
      hfree ((Finset.range (m + 1)).filter (fun b => b ∈ B))
        (fun h hh => (Finset.mem_filter.1 hh).2) m hm
    have havoid : ∀ w, w ≤ m →
        w ∉ (Finset.range (m + 1)).filter (fun b => b ∈ B) →
        w ∉ B := by
      intro w hwm hwP hwB
      exact hwP (Finset.mem_filter.2
        ⟨Finset.mem_range.2 (by omega), hwB⟩)
    exact ⟨x, hx, y, hy, z, hz, hsum, havoid x (by omega) hxP,
      havoid y (by omega) hyP, havoid z (by omega) hzP⟩
  · intro huni
    refine ⟨hBinf, hBpos, fun P hP m hm => ?_⟩
    obtain ⟨x, hx, y, hy, z, hz, hsum, hxB, hyB, hzB⟩ := huni m hm
    exact ⟨x, hx, y, hy, z, hz, hsum, fun h => hxB (hP x h),
      fun h => hyB (hP y h), fun h => hzB (hP z h)⟩

theorem sidon_not_counterexample {A : Set ℕ} {N₀ C : ℕ}
    [DecidablePred (· ∈ A)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hC : ∀ v, N₀ ≤ v → ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A)).card ≤ C) :
    ¬(∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) := by
  intro hfail
  exact (hfail_iff_no_hereditarily_free h0 hcov).1 hfail
    (sidon_has_branch h0 hcov hC)

/-- Pair-level uniformity: hereditary pair-freeness equals uniform
whole-set pair avoidance. -/
theorem hereditarilyPairFree_iff_uniform {A : Set ℕ} {N₀ : ℕ}
    {B : Set ℕ} (hBinf : B.Infinite)
    (hBpos : ∀ b ∈ B, b ∈ A ∧ 0 < b) :
    HereditarilyPairFree A N₀ B ↔
    ∀ m, N₀ ≤ m → ∃ x ∈ A, ∃ y ∈ A, x + y = m ∧
      x ∉ B ∧ y ∉ B := by
  classical
  constructor
  · rintro ⟨-, -, hfree⟩ m hm
    obtain ⟨x, hx, y, hy, hsum, hxP, hyP⟩ :=
      hfree ((Finset.range (m + 1)).filter (fun b => b ∈ B))
        (fun h hh => (Finset.mem_filter.1 hh).2) m hm
    have havoid : ∀ w, w ≤ m →
        w ∉ (Finset.range (m + 1)).filter (fun b => b ∈ B) →
        w ∉ B := by
      intro w hwm hwP hwB
      exact hwP (Finset.mem_filter.2
        ⟨Finset.mem_range.2 (by omega), hwB⟩)
    exact ⟨x, hx, y, hy, hsum, havoid x (by omega) hxP,
      havoid y (by omega) hyP⟩
  · intro huni
    refine ⟨hBinf, hBpos, fun P hP m hm => ?_⟩
    obtain ⟨x, hx, y, hy, hsum, hxB, hyB⟩ := huni m hm
    exact ⟨x, hx, y, hy, hsum, fun h => hxB (hP x h),
      fun h => hyB (hP y h)⟩

theorem exists_maximal_free_node {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (P : Finset ℕ) (hP : FreeNode A N₀ P) :
    ∃ Q : Finset ℕ, FreeNode A N₀ Q ∧ P ⊆ Q ∧
      ∀ R : Finset ℕ, ¬FreeStep A N₀ R Q := by
  classical
  have hwf := freeStep_wf h0 hcov hfail
  revert hP
  induction P using hwf.induction with
  | _ P ih =>
    intro hP
    by_cases hmax : ∀ R : Finset ℕ, ¬FreeStep A N₀ R P
    · exact ⟨P, hP, Finset.Subset.refl P, hmax⟩
    · push Not at hmax
      obtain ⟨R, hR⟩ := hmax
      obtain ⟨Q, hQnode, hRQ, hQmax⟩ := ih R hR hR.2.1
      refine ⟨Q, hQnode, ?_, hQmax⟩
      obtain ⟨-, -, b, -, -, -, hReq⟩ := hR
      calc P ⊆ insert b P := Finset.subset_insert _ _
        _ = R := hReq.symm
        _ ⊆ Q := hRQ

/-- The strict-superset relation on free nodes. -/
def FreeSup (A : Set ℕ) (N₀ : ℕ) (Q P : Finset ℕ) : Prop :=
  FreeNode A N₀ P ∧ FreeNode A N₀ Q ∧ P ⊂ Q

theorem freeSup_wf {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    WellFounded (FreeSup A N₀) := by
  classical
  have hno := (hfail_iff_no_hereditarily_free h0 hcov).1 hfail
  rw [wellFounded_iff_isEmpty_descending_chain]
  constructor
  rintro ⟨f, hf⟩
  have hchain : ∀ n, f n ⊂ f (n + 1) := fun n => (hf n).2.2
  have hchain' : ∀ m n, m ≤ n → f m ⊆ f n := by
    intro m n hmn
    induction n with
    | zero =>
      have h0' : m = 0 := by omega
      subst h0'
      exact Finset.Subset.refl _
    | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with h | h
      · exact Finset.Subset.trans (ih (by omega))
          (hchain n).subset
      · have h1 : m = n + 1 := by omega
        subst h1
        exact Finset.Subset.refl _
  have hcard : ∀ n, n ≤ (f n).card := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      have := Finset.card_lt_card (hchain n)
      omega
  refine hno ⟨{x | ∃ n, x ∈ f n}, ?_, ?_, ?_⟩
  · -- infinite: cards grow without bound
    intro hfin
    obtain ⟨F, hF⟩ := Set.Finite.exists_finset_coe hfin
    have hsub : ∀ n, f n ⊆ F := by
      intro n x hx
      have h1 : x ∈ {x | ∃ n, x ∈ f n} := ⟨n, hx⟩
      rw [← hF] at h1
      exact h1
    have h1 := Finset.card_le_card (hsub (F.card + 1))
    have h2 := hcard (F.card + 1)
    omega
  · rintro x ⟨n, hxn⟩
    exact (hf n).1.1 x hxn
  · intro P hP
    choose st hst using hP
    set N := P.sup (fun h => if hh : h ∈ P then st h hh else 0)
      with hN
    have hPN : ∀ h ∈ P, h ∈ f N := by
      intro h hh
      have h1 : st h hh ≤ N := by
        have := Finset.le_sup (f := fun h' =>
          if hh' : h' ∈ P then st h' hh' else 0) hh
        simpa [hh] using this
      exact hchain' (st h hh) N h1 (hst h hh)
    exact RepFree.mono hPN (hf N).1.2

theorem exists_absolute_leaf {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (P : Finset ℕ) (hP : FreeNode A N₀ P) :
    ∃ Q : Finset ℕ, FreeNode A N₀ Q ∧ P ⊆ Q ∧
      ∀ b ∈ A, 0 < b → b ∉ Q →
        ∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m (insert b Q) := by
  classical
  have hwf := freeSup_wf h0 hcov hfail
  revert hP
  induction P using hwf.induction with
  | _ P ih =>
    intro hP
    by_cases hmax : ∀ b ∈ A, 0 < b → b ∉ P →
        ¬FreeNode A N₀ (insert b P)
    · refine ⟨P, hP, Finset.Subset.refl P, ?_⟩
      intro b hbA hbpos hbP
      have hnot := hmax b hbA hbpos hbP
      have hnotfree : ¬RepFree A N₀ (insert b P) := by
        intro hfree
        refine hnot ⟨?_, hfree⟩
        intro h hh
        rcases Finset.mem_insert.1 hh with h' | h'
        · rw [h']
          exact ⟨hbA, hbpos⟩
        · exact hP.1 h h'
      rw [RepFree] at hnotfree
      push Not at hnotfree
      obtain ⟨m, hm, hall⟩ := hnotfree
      refine ⟨m, hm, ?_⟩
      intro x hx y hy z hz hsum
      by_contra hmiss
      push Not at hmiss
      obtain ⟨h1, h2, h3⟩ := hmiss
      exact h3 (hall x hx y hy z hz hsum h1 h2)
    · push Not at hmax
      obtain ⟨b, hbA, hbpos, hbP, hbfree⟩ := hmax
      have hstep : FreeSup A N₀ (insert b P) P :=
        ⟨hP, hbfree, Finset.ssubset_insert hbP⟩
      obtain ⟨Q, hQnode, hQsub, hQmax⟩ := ih _ hstep hbfree
      exact ⟨Q, hQnode, Finset.Subset.trans
        (Finset.subset_insert _ _) hQsub, hQmax⟩

/-- Strict-superset relation on pair-free nodes. -/
def PairSup (A : Set ℕ) (N₀ : ℕ) (Q P : Finset ℕ) : Prop :=
  PairFreeNode A N₀ P ∧ PairFreeNode A N₀ Q ∧ P ⊂ Q

/-- Order-2 mirror of `freeSup_wf`: under elementwise minimality
alone, no infinite ascending inclusion-chain of pair-free sets. -/
theorem pairSup_wf {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hmin : ∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) :
    WellFounded (PairSup A N₀) := by
  classical
  have hno := (hmin_iff_no_hereditarilyPairFree hcov).1 hmin
  rw [wellFounded_iff_isEmpty_descending_chain]
  constructor
  rintro ⟨f, hf⟩
  have hchain : ∀ n, f n ⊂ f (n + 1) := fun n => (hf n).2.2
  have hchain' : ∀ m n, m ≤ n → f m ⊆ f n := by
    intro m n hmn
    induction n with
    | zero =>
      have h0' : m = 0 := by omega
      subst h0'
      exact Finset.Subset.refl _
    | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with h | h
      · exact Finset.Subset.trans (ih (by omega))
          (hchain n).subset
      · have h1 : m = n + 1 := by omega
        subst h1
        exact Finset.Subset.refl _
  have hcard : ∀ n, n ≤ (f n).card := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      have := Finset.card_lt_card (hchain n)
      omega
  refine hno ⟨{x | ∃ n, x ∈ f n}, ?_, ?_, ?_⟩
  · intro hfin
    obtain ⟨F, hF⟩ := Set.Finite.exists_finset_coe hfin
    have hsub : ∀ n, f n ⊆ F := by
      intro n x hx
      have h1 : x ∈ {x | ∃ n, x ∈ f n} := ⟨n, hx⟩
      rw [← hF] at h1
      exact h1
    have h1 := Finset.card_le_card (hsub (F.card + 1))
    have h2 := hcard (F.card + 1)
    omega
  · rintro x ⟨n, hxn⟩
    exact (hf n).1.1 x hxn
  · intro P hP
    choose st hst using hP
    set N := P.sup (fun h => if hh : h ∈ P then st h hh else 0)
      with hN
    have hPN : ∀ h ∈ P, h ∈ f N := by
      intro h hh
      have h1 : st h hh ≤ N := by
        have := Finset.le_sup (f := fun h' =>
          if hh' : h' ∈ P then st h' hh' else 0) hh
        simpa [hh] using this
      exact hchain' (st h hh) N h1 (hst h hh)
    exact PairFree.mono hPN (hf N).1.2

theorem exists_absolute_pair_leaf {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hmin : ∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n)
    (P : Finset ℕ) (hP : PairFreeNode A N₀ P) :
    ∃ Q : Finset ℕ, PairFreeNode A N₀ Q ∧ P ⊆ Q ∧
      ∀ b ∈ A, 0 < b → b ∉ Q →
        ∃ m, N₀ ≤ m ∧ IsPairSupportTransversal A m (insert b Q) := by
  classical
  have hwf := pairSup_wf hcov hmin
  revert hP
  induction P using hwf.induction with
  | _ P ih =>
    intro hP
    by_cases hmax : ∀ b ∈ A, 0 < b → b ∉ P →
        ¬PairFreeNode A N₀ (insert b P)
    · refine ⟨P, hP, Finset.Subset.refl P, ?_⟩
      intro b hbA hbpos hbP
      have hnot := hmax b hbA hbpos hbP
      have hnotfree : ¬PairFree A N₀ (insert b P) := by
        intro hfree
        refine hnot ⟨?_, hfree⟩
        intro h hh
        rcases Finset.mem_insert.1 hh with h' | h'
        · rw [h']
          exact ⟨hbA, hbpos⟩
        · exact hP.1 h h'
      rw [PairFree] at hnotfree
      push Not at hnotfree
      obtain ⟨m, hm, hall⟩ := hnotfree
      refine ⟨m, hm, ?_⟩
      intro x hx y hy hsum
      by_cases hxin : x ∈ insert b P
      · exact Or.inl hxin
      · exact Or.inr (hall x hx y hy hsum hxin)
    · push Not at hmax
      obtain ⟨b, hbA, hbpos, hbP, hbfree⟩ := hmax
      have hstep : PairSup A N₀ (insert b P) P :=
        ⟨hP, hbfree, Finset.ssubset_insert hbP⟩
      obtain ⟨Q, hQnode, hQsub, hQmax⟩ := ih _ hstep hbfree
      exact ⟨Q, hQnode, Finset.Subset.trans
        (Finset.subset_insert _ _) hQsub, hQmax⟩

/-- Personal-target geometry at an absolute leaf: the envelope is
free, so any envelope-avoiding representation of the support transversal target
must use the new element itself — hence the target sits at or
above its required element, which appears as a part. -/
theorem absolute_leaf_personal_target {A : Set ℕ} {N₀ : ℕ}
    {Q : Finset ℕ} {b m : ℕ}
    (hQ : FreeNode A N₀ Q) (hm : N₀ ≤ m)
    (hhub : IsRepSupportTransversal A m (insert b Q)) :
    b ≤ m ∧ ∃ y ∈ A, ∃ z ∈ A, y ∉ Q ∧ z ∉ Q ∧ b + y + z = m := by
  classical
  obtain ⟨x, hx, y, hy, z, hz, hsum, hxQ, hyQ, hzQ⟩ := hQ.2 m hm
  have hhit := hhub x hx y hy z hz hsum
  have hxb : x = b ∨ y = b ∨ z = b := by
    rcases hhit with h | h | h
    · rcases Finset.mem_insert.1 h with h' | h'
      · exact Or.inl h'
      · exact absurd h' hxQ
    · rcases Finset.mem_insert.1 h with h' | h'
      · exact Or.inr (Or.inl h')
      · exact absurd h' hyQ
    · rcases Finset.mem_insert.1 h with h' | h'
      · exact Or.inr (Or.inr h')
      · exact absurd h' hzQ
  rcases hxb with rfl | rfl | rfl
  · exact ⟨by omega, y, hy, z, hz, hyQ, hzQ, hsum⟩
  · exact ⟨by omega, x, hx, z, hz, hxQ, hzQ, by omega⟩
  · exact ⟨by omega, x, hx, y, hy, hxQ, hyQ, by omega⟩

/-! ## The cap suite (hypothesis-free pigeonholes) -/

theorem four_disjoint_support_transversals_singleton {A : Set ℕ} {m b : ℕ}
    {Q : Fin 4 → Finset ℕ}
    (hdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j))
    (hb : ∀ i, b ∉ Q i)
    (hhub : ∀ i, IsRepSupportTransversal A m (insert b (Q i))) :
    IsRepSupportTransversal A m {b} := by
  classical
  intro x hx y hy z hz hsum
  by_contra hmiss
  push Not at hmiss
  obtain ⟨hxb, hyb, hzb⟩ := hmiss
  have hxb' : x ≠ b := by simpa using hxb
  have hyb' : y ≠ b := by simpa using hyb
  have hzb' : z ≠ b := by simpa using hzb
  -- each envelope is hit by one of the three parts
  have hhit : ∀ i : Fin 4, x ∈ Q i ∨ y ∈ Q i ∨ z ∈ Q i := by
    intro i
    rcases hhub i x hx y hy z hz hsum with h | h | h
    · rcases Finset.mem_insert.1 h with h' | h'
      · exact absurd h' hxb'
      · exact Or.inl h'
    · rcases Finset.mem_insert.1 h with h' | h'
      · exact absurd h' hyb'
      · exact Or.inr (Or.inl h')
    · rcases Finset.mem_insert.1 h with h' | h'
      · exact absurd h' hzb'
      · exact Or.inr (Or.inr h')
  -- x hits at most one envelope, likewise y, z: pick the hit part
  -- for each of the four indices; two indices share a part; that
  -- part lies in two disjoint envelopes — contradiction.
  have hpick : ∀ i : Fin 4, ∃ p : Fin 3,
      (if p = 0 then x else if p = 1 then y else z) ∈ Q i := by
    intro i
    rcases hhit i with h | h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
    · exact ⟨2, by simpa using h⟩
  choose pk hpk using hpick
  -- pigeonhole: 4 indices, 3 parts
  have hcard : ¬Function.Injective pk := by
    intro hinj
    have := Fintype.card_le_of_injective pk hinj
    simp at this
  rw [Function.not_injective_iff] at hcard
  obtain ⟨i, j, hpij, hij⟩ := hcard
  have h1 := hpk i
  have h2 := hpk j
  rw [hpij] at h1
  exact (Finset.disjoint_left.1 (hdisj i j hij)) h1 h2

/-! ## RankLayers: pool leaves and the stratification -/

/-- Pool form of the absolute cofinal supply: within any pool of positive
basis elements, every free set of pool elements extends to a
pool-inclusion-maximal one, over which every remaining pool
element is a required element. -/
theorem exists_absolute_leaf_pool {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (C : Set ℕ) (hC : ∀ c ∈ C, c ∈ A ∧ 0 < c)
    (P : Finset ℕ) (hPC : ∀ h ∈ P, h ∈ C)
    (hPfree : RepFree A N₀ P) :
    ∃ Q : Finset ℕ, (∀ h ∈ Q, h ∈ C) ∧ RepFree A N₀ Q ∧ P ⊆ Q ∧
      ∀ b ∈ C, b ∉ Q → ∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m (insert b Q) := by
  classical
  have hwf := freeSup_wf h0 hcov hfail
  revert hPC hPfree
  induction P using hwf.induction with
  | _ P ih =>
    intro hPC hPfree
    by_cases hmax : ∀ b ∈ C, b ∉ P → ¬RepFree A N₀ (insert b P)
    · refine ⟨P, hPC, hPfree, Finset.Subset.refl P, ?_⟩
      intro b hbC hbP
      have hnotfree := hmax b hbC hbP
      rw [RepFree] at hnotfree
      push Not at hnotfree
      obtain ⟨m, hm, hall⟩ := hnotfree
      refine ⟨m, hm, ?_⟩
      intro x hx y hy z hz hsum
      by_contra hmiss
      push Not at hmiss
      obtain ⟨h1, h2, h3⟩ := hmiss
      exact h3 (hall x hx y hy z hz hsum h1 h2)
    · push Not at hmax
      obtain ⟨b, hbC, hbP, hbfree⟩ := hmax
      have hnodeP : FreeNode A N₀ P :=
        ⟨fun h hh => hC h (hPC h hh), hPfree⟩
      have hnodeQ : FreeNode A N₀ (insert b P) := by
        refine ⟨?_, hbfree⟩
        intro h hh
        rcases Finset.mem_insert.1 hh with h' | h'
        · rw [h']
          exact hC b hbC
        · exact hC h (hPC h h')
      have hstep : FreeSup A N₀ (insert b P) P :=
        ⟨hnodeP, hnodeQ, Finset.ssubset_insert hbP⟩
      have hinsC : ∀ h ∈ insert b P, h ∈ C := by
        intro h hh
        rcases Finset.mem_insert.1 hh with h' | h'
        · rw [h']
          exact hbC
        · exact hPC h h'
      obtain ⟨Q, hQC, hQfree, hQsub, hQmax⟩ :=
        ih _ hstep hinsC hbfree
      exact ⟨Q, hQC, hQfree, Finset.Subset.trans
        (Finset.subset_insert _ _) hQsub, hQmax⟩

theorem absolute_rank_layer_stratification {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ Q : ℕ → Finset ℕ,
      (∀ k, (Q k).Nonempty) ∧
      (∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h) ∧
      (∀ k, RepFree A N₀ (Q k)) ∧
      (∀ j k, j < k → Disjoint (Q j) (Q k)) ∧
      (∀ k, ∀ b ∈ A, 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
        ∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m (insert b (Q k))) := by
  classical
  -- one rank layer over the pool avoiding a given finite past
  have hstep : ∀ U : Finset ℕ, ∃ Q : Finset ℕ, Q.Nonempty ∧
      (∀ h ∈ Q, h ∈ A ∧ 0 < h ∧ h ∉ U) ∧ RepFree A N₀ Q ∧
      ∀ b ∈ A, 0 < b → b ∉ U → b ∉ Q →
        ∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m (insert b Q) := by
    intro U
    obtain ⟨X, hX⟩ := cofinite_free_singletons h0 hcov hanchor hfail
    obtain ⟨a, haA, hage⟩ :=
      pairCovers_unbounded hcov (X + (U.sup id) + 1)
    have hapos : 0 < a := by omega
    have haU : a ∉ U := by
      intro hmem
      have h2 : a ≤ U.sup id := Finset.le_sup (f := id) hmem
      omega
    have hafree : RepFree A N₀ {a} := hX a haA (by omega) hapos
    obtain ⟨Q, hQC, hQfree, hQsub, hQmax⟩ :=
      exists_absolute_leaf_pool h0 hcov hfail
        {x | x ∈ A ∧ 0 < x ∧ x ∉ U}
        (fun c hc => ⟨hc.1, hc.2.1⟩)
        {a}
        (fun h hh => by
          rw [Finset.mem_singleton] at hh
          subst hh
          exact ⟨haA, hapos, haU⟩)
        hafree
    refine ⟨Q, ⟨a, hQsub (Finset.mem_singleton_self a)⟩,
      fun h hh => hQC h hh, hQfree, ?_⟩
    intro b hbA hbpos hbU hbQ
    exact hQmax b ⟨hbA, hbpos, hbU⟩ hbQ
  choose F hFne hFmem hFfree hFmax using hstep
  -- iterate, carrying the cumulative union
  obtain ⟨g, hg0, hgs⟩ : ∃ g : ℕ → Finset ℕ × Finset ℕ,
      g 0 = (F ∅, F ∅) ∧
      ∀ k, g (k + 1) = (F (g k).2, (g k).2 ∪ F (g k).2) :=
    ⟨fun k => Nat.rec (F ∅, F ∅)
      (fun _ p => (F p.2, p.2 ∪ F p.2)) k, rfl, fun _ => rfl⟩
  have hQ0 : (g 0).1 = F ∅ := by rw [hg0]
  have hU0 : (g 0).2 = F ∅ := by rw [hg0]
  have hQs : ∀ k, (g (k + 1)).1 = F ((g k).2) :=
    fun k => by rw [hgs k]
  have hUs : ∀ k, (g (k + 1)).2 = (g k).2 ∪ F ((g k).2) :=
    fun k => by rw [hgs k]
  -- the cumulative union is exactly the union of rank layers so far
  have hUmem : ∀ k x, x ∈ (g k).2 ↔ ∃ j, j ≤ k ∧ x ∈ (g j).1 := by
    intro k
    induction k with
    | zero =>
      intro x
      rw [hU0]
      constructor
      · intro hx
        exact ⟨0, le_refl 0, by rw [hQ0]; exact hx⟩
      · rintro ⟨j, hj, hx⟩
        have hj0 : j = 0 := by omega
        subst hj0
        rw [hQ0] at hx
        exact hx
    | succ k ihk =>
      intro x
      rw [hUs, Finset.mem_union]
      constructor
      · rintro (hx | hx)
        · obtain ⟨j, hj, hx'⟩ := (ihk x).1 hx
          exact ⟨j, by omega, hx'⟩
        · exact ⟨k + 1, le_refl _, by rw [hQs]; exact hx⟩
      · rintro ⟨j, hj, hx⟩
        rcases Nat.lt_or_ge j (k + 1) with h | h
        · exact Or.inl ((ihk x).2 ⟨j, by omega, hx⟩)
        · have hj1 : j = k + 1 := by omega
          subst hj1
          rw [hQs] at hx
          exact Or.inr hx
  refine ⟨fun k => (g k).1, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    cases k with
    | zero =>
      show ((g 0).1).Nonempty
      rw [hQ0]
      exact hFne ∅
    | succ k =>
      show ((g (k + 1)).1).Nonempty
      rw [hQs]
      exact hFne _
  · intro k h hh
    cases k with
    | zero =>
      have hh' : h ∈ (g 0).1 := hh
      rw [hQ0] at hh'
      exact ⟨(hFmem ∅ h hh').1, (hFmem ∅ h hh').2.1⟩
    | succ k =>
      have hh' : h ∈ (g (k + 1)).1 := hh
      rw [hQs] at hh'
      exact ⟨(hFmem _ h hh').1, (hFmem _ h hh').2.1⟩
  · intro k
    cases k with
    | zero =>
      show RepFree A N₀ (g 0).1
      rw [hQ0]
      exact hFfree ∅
    | succ k =>
      show RepFree A N₀ (g (k + 1)).1
      rw [hQs]
      exact hFfree _
  · intro j k hjk
    show Disjoint (g j).1 (g k).1
    rw [Finset.disjoint_left]
    intro x hxj hxk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 :=
      ⟨k - 1, by omega⟩
    rw [hQs] at hxk
    have hxU : x ∉ (g k').2 := (hFmem _ x hxk).2.2
    exact hxU ((hUmem k' x).2 ⟨j, by omega, hxj⟩)
  · intro k b hbA hbpos hbQ
    cases k with
    | zero =>
      have hb0 : b ∉ (g 0).1 := hbQ 0 (le_refl 0)
      show ∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m (insert b (g 0).1)
      rw [hQ0] at hb0 ⊢
      exact hFmax ∅ b hbA hbpos (Finset.notMem_empty b) hb0
    | succ k =>
      have hbU : b ∉ (g k).2 := by
        intro hmem
        obtain ⟨j, hj, hx⟩ := (hUmem k b).1 hmem
        exact hbQ j (by omega) hx
      have hb1 : b ∉ (g (k + 1)).1 := hbQ (k + 1) (le_refl _)
      show ∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m (insert b (g (k + 1)).1)
      rw [hQs] at hb1 ⊢
      exact hFmax _ b hbA hbpos hbU hb1

theorem eternal_survivor_dichotomy {A : Set ℕ} {N₀ : ℕ}
    {Q : ℕ → Finset ℕ} {b : ℕ}
    (hdisj : ∀ j k, j < k → Disjoint (Q j) (Q k))
    (hb : ∀ j, b ∉ Q j)
    (hguard : ∀ k, ∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m (insert b (Q k))) :
    (∀ Y, ∃ k, ∃ m, Y ≤ m ∧ N₀ ≤ m ∧
      IsRepSupportTransversal A m (insert b (Q k))) ∨
    ∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m {b} := by
  classical
  choose m hm₁ hm₂ using hguard
  by_cases hunb : ∀ Y, ∃ k, Y ≤ m k
  · left
    intro Y
    obtain ⟨k, hk⟩ := hunb Y
    exact ⟨k, m k, hk, hm₁ k, hm₂ k⟩
  · right
    push Not at hunb
    obtain ⟨Y, hY⟩ := hunb
    have hmaps : ∀ k ∈ Finset.range (3 * Y + 1),
        m k ∈ Finset.range Y := by
      intro k _
      rw [Finset.mem_range]
      exact hY k
    have hlt : (Finset.range Y).card * 3 <
        (Finset.range (3 * Y + 1)).card := by
      rw [Finset.card_range, Finset.card_range]
      omega
    obtain ⟨v, hvt, hfib⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        hmaps hlt
    set s := (Finset.range (3 * Y + 1)).filter
      (fun k => m k = v) with hs
    have hcard4 : 4 ≤ s.card := hfib
    obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq hcard4
    let e := t.orderIsoOfFin htcard
    have hmem : ∀ i : Fin 4, (e i : ℕ) ∈ s := fun i => hts (e i).2
    have hval : ∀ i : Fin 4, m (e i : ℕ) = v := by
      intro i
      have h1 := hmem i
      rw [hs, Finset.mem_filter] at h1
      exact h1.2
    have hinj : ∀ i j : Fin 4, i ≠ j → (e i : ℕ) ≠ (e j : ℕ) := by
      intro i j hij hne
      exact hij (e.injective (Subtype.ext hne))
    have hNv : N₀ ≤ v := by
      have h1 := hm₁ (e 0 : ℕ)
      rw [hval 0] at h1
      exact h1
    refine ⟨v, hNv, ?_⟩
    refine four_disjoint_support_transversals_singleton
      (Q := fun i => Q (e i : ℕ)) ?_ ?_ ?_
    · intro i j hij
      rcases Nat.lt_or_ge (e i : ℕ) (e j : ℕ) with h | h
      · exact hdisj _ _ h
      · have hne := hinj i j hij
        have h' : (e j : ℕ) < (e i : ℕ) := by omega
        exact (hdisj _ _ h').symm
    · intro i
      exact hb _
    · intro i
      have h1 := hm₂ (e i : ℕ)
      rw [hval i] at h1
      exact h1

theorem rank_layer_survivors_unbounded_targets {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {Q : ℕ → Finset ℕ}
    (hdisj : ∀ j k, j < k → Disjoint (Q j) (Q k))
    (hguard : ∀ k, ∀ b ∈ A, 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
      ∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m (insert b (Q k))) :
    ∃ X, ∀ b ∈ A, X ≤ b → 0 < b → (∀ j, b ∉ Q j) →
      ∀ Y, ∃ k, ∃ m, Y ≤ m ∧ N₀ ≤ m ∧
        IsRepSupportTransversal A m (insert b (Q k)) := by
  classical
  by_contra hno
  push Not at hno
  have hstream : ∀ N, ∃ a m, N ≤ m ∧ 0 < a ∧
      IsPrivateTriple A a m := by
    intro N
    obtain ⟨b, hbA, hbX, hbpos, hbQ, Y, hY⟩ := hno N
    have hg : ∀ k, ∃ m, N₀ ≤ m ∧
        IsRepSupportTransversal A m (insert b (Q k)) := by
      intro k
      exact hguard k b hbA hbpos (fun j _ => hbQ j)
    have hnotleft : ¬(∀ Y', ∃ k, ∃ m, Y' ≤ m ∧ N₀ ≤ m ∧
        IsRepSupportTransversal A m (insert b (Q k))) := by
      intro hall
      obtain ⟨k, m, h1, h2, h3⟩ := hall Y
      exact hY k m h1 h2 h3
    rcases eternal_survivor_dichotomy hdisj hbQ hg with hL | hR
    · exact absurd hL hnotleft
    obtain ⟨m, hm, hhub⟩ := hR
    obtain ⟨x, hx, y, hy, hxy⟩ := hcov m hm
    have h3 : x + y + 0 = m := by omega
    have hbm : b ≤ m := by
      rcases hhub x hx y hy 0 h0 h3 with h | h | h
      · have hxb : x = b := by simpa using h
        omega
      · have hyb : y = b := by simpa using h
        omega
      · have h0b : (0 : ℕ) = b := by simpa using h
        omega
    refine ⟨b, m, by omega, hbpos,
      ⟨x, hx, y, hy, 0, h0, h3⟩, ?_⟩
    intro x' hx' y' hy' z' hz' hsum
    rcases hhub x' hx' y' hy' z' hz' hsum with h | h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr (Or.inl (by simpa using h))
    · exact Or.inr (Or.inr (by simpa using h))
  obtain ⟨B, hBA, hBinf, hsurv⟩ := hanchor hstream
  refine hfail B hBA hBinf ⟨N₀, ?_⟩
  intro n hn
  obtain ⟨x, hx, y, hy, z, hz, hxB, hyB, hzB, hsum⟩ := hsurv n hn
  refine ⟨![x, y, z], ?_, by
    simpa [Fin.sum_univ_three] using hsum⟩
  intro i
  match i with
  | 0 => exact ⟨hx, hxB⟩
  | 1 => exact ⟨hy, hyB⟩
  | 2 => exact ⟨hz, hzB⟩

theorem rank_layer_counterexample_structure {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ Q : ℕ → Finset ℕ, ∃ X,
      (∀ k, (Q k).Nonempty) ∧
      (∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h) ∧
      (∀ k, RepFree A N₀ (Q k)) ∧
      (∀ j k, j < k → Disjoint (Q j) (Q k)) ∧
      (∀ k, ∀ b ∈ A, 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
        ∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m (insert b (Q k))) ∧
      (∀ b ∈ A, X ≤ b → 0 < b → (∀ j, b ∉ Q j) →
        ∀ Y, ∃ k, ∃ m, Y ≤ m ∧ N₀ ≤ m ∧
          IsRepSupportTransversal A m (insert b (Q k))) := by
  obtain ⟨Q, hne, hmem, hfree, hdisj, hguard⟩ :=
    absolute_rank_layer_stratification h0 hcov hanchor hfail
  obtain ⟨X, hX⟩ :=
    rank_layer_survivors_unbounded_targets h0 hcov hanchor hfail
      hdisj hguard
  exact ⟨Q, X, hne, hmem, hfree, hdisj, hguard, hX⟩

/-! ## The depth tax -/

theorem rank_layer_depth_forces_scale {A : Set ℕ} {N₀ : ℕ}
    {Q : ℕ → Finset ℕ} {k b : ℕ}
    (hdisj : ∀ j k', j < k' → Disjoint (Q j) (Q k'))
    (hguard : ∀ j, j ≤ k → ∃ m, N₀ ≤ m ∧
      IsRepSupportTransversal A m (insert b (Q j)))
    (hb : ∀ j, j ≤ k → b ∉ Q j) :
    (∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m {b}) ∨
    (∃ j, j ≤ k ∧ ∃ m, N₀ + k / 3 ≤ m ∧ N₀ ≤ m ∧
      IsRepSupportTransversal A m (insert b (Q j))) := by
  classical
  have hg : ∀ j, ∃ m, N₀ ≤ m ∧
      (j ≤ k → IsRepSupportTransversal A m (insert b (Q j))) := by
    intro j
    by_cases hj : j ≤ k
    · obtain ⟨m, h1, h2⟩ := hguard j hj
      exact ⟨m, h1, fun _ => h2⟩
    · exact ⟨N₀, le_refl _, fun h => absurd h hj⟩
  choose m hm₁ hm₂ using hg
  by_cases hbig : ∃ j, j ≤ k ∧ N₀ + k / 3 ≤ m j
  · right
    obtain ⟨j, hj, hbigj⟩ := hbig
    exact ⟨j, hj, m j, hbigj, hm₁ j, hm₂ j hj⟩
  · left
    push Not at hbig
    have hmaps : ∀ j ∈ Finset.range (k + 1),
        m j ∈ Finset.Ico N₀ (N₀ + k / 3) := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [Finset.mem_Ico]
      exact ⟨hm₁ j, hbig j (by omega)⟩
    have hlt : (Finset.Ico N₀ (N₀ + k / 3)).card * 3 <
        (Finset.range (k + 1)).card := by
      rw [Nat.card_Ico, Finset.card_range]
      omega
    obtain ⟨v, hvt, hfib⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        hmaps hlt
    set s := (Finset.range (k + 1)).filter (fun j => m j = v)
      with hs
    have hcard4 : 4 ≤ s.card := hfib
    obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq hcard4
    let e := t.orderIsoOfFin htcard
    have hmem' : ∀ i : Fin 4, (e i : ℕ) ∈ s := fun i => hts (e i).2
    have hjk : ∀ i : Fin 4, (e i : ℕ) ≤ k := by
      intro i
      have h1 := hmem' i
      rw [hs, Finset.mem_filter, Finset.mem_range] at h1
      omega
    have hval : ∀ i : Fin 4, m (e i : ℕ) = v := by
      intro i
      have h1 := hmem' i
      rw [hs, Finset.mem_filter] at h1
      exact h1.2
    have hinj : ∀ i j : Fin 4, i ≠ j → (e i : ℕ) ≠ (e j : ℕ) := by
      intro i j hij hne
      exact hij (e.injective (Subtype.ext hne))
    have hNv : N₀ ≤ v := by
      have h1 := hm₁ (e 0 : ℕ)
      rw [hval 0] at h1
      exact h1
    refine ⟨v, hNv, ?_⟩
    refine four_disjoint_support_transversals_singleton
      (Q := fun i => Q (e i : ℕ)) ?_ ?_ ?_
    · intro i j hij
      rcases Nat.lt_or_ge (e i : ℕ) (e j : ℕ) with h | h
      · exact hdisj _ _ h
      · have hne := hinj i j hij
        have h' : (e j : ℕ) < (e i : ℕ) := by omega
        exact (hdisj _ _ h').symm
    · intro i
      exact hb _ (hjk i)
    · intro i
      have h1 := hm₂ (e i : ℕ) (hjk i)
      rw [hval i] at h1
      exact h1

theorem depth_tax_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {Q : ℕ → Finset ℕ}
    (hdisj : ∀ j k, j < k → Disjoint (Q j) (Q k))
    (hguard : ∀ k, ∀ b ∈ A, 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
      ∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m (insert b (Q k))) :
    ∃ X, ∀ k, ∀ b ∈ A, X ≤ b → 0 < b →
      (∀ j, j ≤ k → b ∉ Q j) →
      ∃ j, j ≤ k ∧ ∃ m, N₀ + k / 3 ≤ m ∧ N₀ ≤ m ∧
        IsRepSupportTransversal A m (insert b (Q j)) := by
  classical
  by_contra hno
  push Not at hno
  have hstream : ∀ N, ∃ a m', N ≤ m' ∧ 0 < a ∧
      IsPrivateTriple A a m' := by
    intro N
    obtain ⟨k, b, hbA, hbX, hbpos, hbQ, hbdd⟩ := hno N
    have hg : ∀ j, j ≤ k → ∃ m, N₀ ≤ m ∧
        IsRepSupportTransversal A m (insert b (Q j)) := by
      intro j hj
      exact hguard j b hbA hbpos (fun j' hj' => hbQ j' (by omega))
    rcases rank_layer_depth_forces_scale hdisj hg
      (fun j hj => hbQ j hj) with hown | hbig
    · obtain ⟨m, hm, hhub⟩ := hown
      obtain ⟨x, hx, y, hy, hxy⟩ := hcov m hm
      have h3 : x + y + 0 = m := by omega
      have hbm : b ≤ m := by
        rcases hhub x hx y hy 0 h0 h3 with h | h | h
        · have hxb : x = b := by simpa using h
          omega
        · have hyb : y = b := by simpa using h
          omega
        · have h0b : (0 : ℕ) = b := by simpa using h
          omega
      refine ⟨b, m, by omega, hbpos,
        ⟨x, hx, y, hy, 0, h0, h3⟩, ?_⟩
      intro x' hx' y' hy' z' hz' hsum
      rcases hhub x' hx' y' hy' z' hz' hsum with h | h | h
      · exact Or.inl (by simpa using h)
      · exact Or.inr (Or.inl (by simpa using h))
      · exact Or.inr (Or.inr (by simpa using h))
    · obtain ⟨j, hj, m, h1, h2, h3⟩ := hbig
      exact absurd h3 (hbdd j hj m h1 h2)
  obtain ⟨B, hBA, hBinf, hsurv⟩ := hanchor hstream
  refine hfail B hBA hBinf ⟨N₀, ?_⟩
  intro n hn
  obtain ⟨x, hx, y, hy, z, hz, hxB, hyB, hzB, hsum⟩ := hsurv n hn
  refine ⟨![x, y, z], ?_, by
    simpa [Fin.sum_univ_three] using hsum⟩
  intro i
  match i with
  | 0 => exact ⟨hx, hxB⟩
  | 1 => exact ⟨hy, hyB⟩
  | 2 => exact ⟨hz, hzB⟩

/-- Order-2 rotation cap: a pair has TWO parts, so three pairwise
disjoint b-free envelope-support transversals at one target already force
singleton ownership at order 2.  Hypothesis-free. -/
theorem three_disjoint_pair_support_transversals_singleton {A : Set ℕ} {m b : ℕ}
    {Q : Fin 3 → Finset ℕ}
    (hdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j))
    (hb : ∀ i, b ∉ Q i)
    (hhub : ∀ i, IsPairSupportTransversal A m (insert b (Q i))) :
    IsPairSupportTransversal A m {b} := by
  classical
  intro x hx y hy hsum
  by_contra hmiss
  push Not at hmiss
  obtain ⟨hxb, hyb⟩ := hmiss
  have hxb' : x ≠ b := by simpa using hxb
  have hyb' : y ≠ b := by simpa using hyb
  have hhit : ∀ i : Fin 3, x ∈ Q i ∨ y ∈ Q i := by
    intro i
    rcases hhub i x hx y hy hsum with h | h
    · rcases Finset.mem_insert.1 h with h' | h'
      · exact absurd h' hxb'
      · exact Or.inl h'
    · rcases Finset.mem_insert.1 h with h' | h'
      · exact absurd h' hyb'
      · exact Or.inr h'
  have hpick : ∀ i : Fin 3, ∃ p : Fin 2,
      (if p = 0 then x else y) ∈ Q i := by
    intro i
    rcases hhit i with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  choose pk hpk using hpick
  have hcard : ¬Function.Injective pk := by
    intro hinj
    have := Fintype.card_le_of_injective pk hinj
    simp at this
  rw [Function.not_injective_iff] at hcard
  obtain ⟨i, j, hpij, hij⟩ := hcard
  have h1 := hpk i
  have h2 := hpk j
  rw [hpij] at h1
  exact (Finset.disjoint_left.1 (hdisj i j hij)) h1 h2

theorem stratified_tax_summary {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ Q : ℕ → Finset ℕ, ∃ X,
      (∀ k, (Q k).Nonempty) ∧
      (∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h) ∧
      (∀ k, RepFree A N₀ (Q k)) ∧
      (∀ j k, j < k → Disjoint (Q j) (Q k)) ∧
      (∀ k, ∀ b ∈ A, 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
        ∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m (insert b (Q k))) ∧
      (∀ k, ∀ b ∈ A, X ≤ b → 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
        ∃ j, j ≤ k ∧ ∃ m, N₀ + k / 3 ≤ m ∧ N₀ ≤ m ∧
          IsRepSupportTransversal A m (insert b (Q j))) := by
  obtain ⟨Q, hne, hmem, hfree, hdisj, hguard⟩ :=
    absolute_rank_layer_stratification h0 hcov hanchor hfail
  obtain ⟨X, hX⟩ :=
    depth_tax_of_hfail h0 hcov hanchor hfail hdisj hguard
  exact ⟨Q, X, hne, hmem, hfree, hdisj, hguard, hX⟩

/-! ## Higher caps and the conflict law -/

theorem seven_level_support_transversal_impossible {A : Set ℕ} {m : ℕ}
    {Q : Fin 7 → Finset ℕ} {b : Fin 7 → ℕ}
    (hdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j))
    (hbinj : Function.Injective b)
    (hrep : ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = m)
    (hhub : ∀ i, IsRepSupportTransversal A m (insert (b i) (Q i))) :
    False := by
  classical
  obtain ⟨x, hx, y, hy, z, hz, hsum⟩ := hrep
  have hpick : ∀ i : Fin 7, ∃ pm : Fin 3 × Fin 2,
      (pm.2 = 0 ∧
        (if pm.1 = 0 then x else if pm.1 = 1 then y else z)
          ∈ Q i) ∨
      (pm.2 = 1 ∧
        (if pm.1 = 0 then x else if pm.1 = 1 then y else z)
          = b i) := by
    intro i
    rcases hhub i x hx y hy z hz hsum with h | h | h
    · rcases Finset.mem_insert.1 h with h' | h'
      · exact ⟨(0, 1), Or.inr ⟨rfl, by simpa using h'⟩⟩
      · exact ⟨(0, 0), Or.inl ⟨rfl, by simpa using h'⟩⟩
    · rcases Finset.mem_insert.1 h with h' | h'
      · exact ⟨(1, 1), Or.inr ⟨rfl, by simpa using h'⟩⟩
      · exact ⟨(1, 0), Or.inl ⟨rfl, by simpa using h'⟩⟩
    · rcases Finset.mem_insert.1 h with h' | h'
      · exact ⟨(2, 1), Or.inr ⟨rfl, by simpa using h'⟩⟩
      · exact ⟨(2, 0), Or.inl ⟨rfl, by simpa using h'⟩⟩
  choose pk hpk using hpick
  have hcard : ¬Function.Injective pk := by
    intro hinj
    have := Fintype.card_le_of_injective pk hinj
    simp at this
  rw [Function.not_injective_iff] at hcard
  obtain ⟨i, j, hpij, hij⟩ := hcard
  have h1 := hpk i
  have h2 := hpk j
  rw [hpij] at h1
  rcases h1 with ⟨hm1, hin1⟩ | ⟨hm1, heq1⟩ <;>
    rcases h2 with ⟨hm2, hin2⟩ | ⟨hm2, heq2⟩
  · exact (Finset.disjoint_left.1 (hdisj i j hij)) hin1 hin2
  · rw [hm1] at hm2
    exact absurd hm2 (by decide)
  · rw [hm1] at hm2
    exact absurd hm2 (by decide)
  · exact hij (hbinj (heq1 ▸ heq2 ▸ rfl))

theorem eighteen_level_cap {A : Set ℕ} {m : ℕ}
    {Q : Fin 19 → Finset ℕ} {b : Fin 19 → ℕ}
    (hdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j))
    (hb : ∀ i j, b i ∉ Q j)
    (hrep : ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = m)
    (hhub : ∀ i, IsRepSupportTransversal A m (insert (b i) (Q i))) :
    ∃ i, IsRepSupportTransversal A m {b i} := by
  classical
  by_cases hfib : ∃ v ∈ Finset.univ.image b,
      4 ≤ (Finset.univ.filter (fun i => b i = v)).card
  · obtain ⟨v, hv, hvc⟩ := hfib
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hvc
    let e := t.orderIsoOfFin htc
    have hbv : ∀ i : Fin 4, b (e i : Fin 19) = v := by
      intro i
      have h1 := hts (e i).2
      rw [Finset.mem_filter] at h1
      exact h1.2
    have hown : IsRepSupportTransversal A m {v} := by
      refine four_disjoint_support_transversals_singleton
        (Q := fun i => Q (e i : Fin 19)) ?_ ?_ ?_
      · intro i j hij
        exact hdisj _ _
          (fun heq => hij (e.injective (Subtype.ext heq)))
      · intro i
        rw [← hbv i]
        exact hb _ _
      · intro i
        have h1 := hhub (e i : Fin 19)
        rw [hbv i] at h1
        exact h1
    obtain ⟨i0, hi0⟩ : ∃ i : Fin 19, b i = v := by
      rw [Finset.mem_image] at hv
      obtain ⟨i, _, hi⟩ := hv
      exact ⟨i, hi⟩
    rw [← hi0] at hown
    exact ⟨i0, hown⟩
  · exfalso
    push Not at hfib
    have hcount : (Finset.univ : Finset (Fin 19)).card ≤
        3 * (Finset.univ.image b).card := by
      refine Finset.card_le_mul_card_image (f := b)
        Finset.univ 3 ?_
      intro v hv
      have h1 := hfib v hv
      omega
    have h19 : (Finset.univ : Finset (Fin 19)).card = 19 := by
      simp
    have h7 : 7 ≤ (Finset.univ.image b).card := by omega
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq h7
    let e := t.orderIsoOfFin htc
    have hpre : ∀ i : Fin 7, ∃ i' : Fin 19,
        b i' = (e i : ℕ) := by
      intro i
      have h1 := hts (e i).2
      rw [Finset.mem_image] at h1
      obtain ⟨i', _, hi'⟩ := h1
      exact ⟨i', hi'⟩
    choose c hc using hpre
    refine seven_level_support_transversal_impossible (A := A) (m := m)
      (Q := fun i => Q (c i)) (b := fun i => b (c i))
      ?_ ?_ hrep ?_
    · intro i j hij
      refine hdisj _ _ (fun heq => hij ?_)
      apply e.injective
      apply Subtype.ext
      rw [← hc i, ← hc j, heq]
    · intro i j hij
      have hij' : b (c i) = b (c j) := hij
      rw [hc i, hc j] at hij'
      exact e.injective (Subtype.ext hij')
    · intro i
      exact hhub (c i)

theorem five_rank_layer_conflict_impossible {A : Set ℕ} {N₀ m : ℕ}
    {Q : Fin 5 → Finset ℕ}
    (hdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j))
    (hfree : RepFree A N₀ (Q 0))
    (hm : N₀ ≤ m)
    (hhub : ∀ i : Fin 4, IsRepSupportTransversal A m (Q 0 ∪ Q i.succ)) :
    False := by
  classical
  obtain ⟨x, hx, y, hy, z, hz, hsum, hxQ, hyQ, hzQ⟩ := hfree m hm
  have hhit : ∀ i : Fin 4, x ∈ Q i.succ ∨ y ∈ Q i.succ ∨
      z ∈ Q i.succ := by
    intro i
    rcases hhub i x hx y hy z hz hsum with h | h | h
    · rcases Finset.mem_union.1 h with h' | h'
      · exact absurd h' hxQ
      · exact Or.inl h'
    · rcases Finset.mem_union.1 h with h' | h'
      · exact absurd h' hyQ
      · exact Or.inr (Or.inl h')
    · rcases Finset.mem_union.1 h with h' | h'
      · exact absurd h' hzQ
      · exact Or.inr (Or.inr h')
  have hpick : ∀ i : Fin 4, ∃ p : Fin 3,
      (if p = 0 then x else if p = 1 then y else z)
        ∈ Q i.succ := by
    intro i
    rcases hhit i with h | h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
    · exact ⟨2, by simpa using h⟩
  choose pk hpk using hpick
  have hcard : ¬Function.Injective pk := by
    intro hinj
    have := Fintype.card_le_of_injective pk hinj
    simp at this
  rw [Function.not_injective_iff] at hcard
  obtain ⟨i, j, hpij, hij⟩ := hcard
  have h1 := hpk i
  have h2 := hpk j
  rw [hpij] at h1
  have hne : i.succ ≠ j.succ := fun h =>
    hij (Fin.succ_injective 4 h)
  exact (Finset.disjoint_left.1 (hdisj i.succ j.succ hne)) h1 h2

/-- SupportTransversal-ness is up-monotone in the envelope. -/
theorem IsRepSupportTransversal.mono {A : Set ℕ} {m : ℕ} {H H' : Finset ℕ}
    (hsub : H ⊆ H') (h : IsRepSupportTransversal A m H) : IsRepSupportTransversal A m H' := by
  intro x hx y hy z hz hsum
  rcases h x hx y hy z hz hsum with h' | h' | h'
  · exact Or.inl (hsub h')
  · exact Or.inr (Or.inl (hsub h'))
  · exact Or.inr (Or.inr (hsub h'))

theorem rank_layer_pairs_conflict {A : Set ℕ} {N₀ : ℕ}
    {Q : ℕ → Finset ℕ}
    (hne : ∀ k, (Q k).Nonempty)
    (hmem : ∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h)
    (hdisj : ∀ j k, j < k → Disjoint (Q j) (Q k))
    (hguard : ∀ k, ∀ b ∈ A, 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
      ∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m (insert b (Q k))) :
    ∀ j k, j < k → ∃ m, N₀ ≤ m ∧
      IsRepSupportTransversal A m (Q j ∪ Q k) := by
  intro j k hjk
  obtain ⟨b, hb⟩ := hne k
  have hbA := (hmem k b hb).1
  have hbpos := (hmem k b hb).2
  have hbavoid : ∀ j', j' ≤ j → b ∉ Q j' := by
    intro j' hj' hmem'
    exact (Finset.disjoint_left.1 (hdisj j' k (by omega)))
      hmem' hb
  obtain ⟨m, hm, hhub⟩ := hguard j b hbA hbpos hbavoid
  refine ⟨m, hm, IsRepSupportTransversal.mono ?_ hhub⟩
  intro w hw
  rcases Finset.mem_insert.1 hw with h' | h'
  · rw [h']
    exact Finset.mem_union_right _ hb
  · exact Finset.mem_union_left _ h'

/-- Order-2 conflict bound: the escape pair from a pair-free rank layer must
meet every conflict partner, and a pair has two parts — so at
order 2 the per-target conflict degree is at most 2; a fourth
disjoint partner is impossible. -/
theorem four_rank_layer_pair_conflict_impossible {A : Set ℕ}
    {N₀ m : ℕ} {Q : Fin 4 → Finset ℕ}
    (hdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j))
    (hfree : PairFree A N₀ (Q 0))
    (hm : N₀ ≤ m)
    (hhub : ∀ i : Fin 3, IsPairSupportTransversal A m (Q 0 ∪ Q i.succ)) :
    False := by
  classical
  obtain ⟨x, hx, y, hy, hsum, hxQ, hyQ⟩ := hfree m hm
  have hhit : ∀ i : Fin 3, x ∈ Q i.succ ∨ y ∈ Q i.succ := by
    intro i
    rcases hhub i x hx y hy hsum with h | h
    · rcases Finset.mem_union.1 h with h' | h'
      · exact absurd h' hxQ
      · exact Or.inl h'
    · rcases Finset.mem_union.1 h with h' | h'
      · exact absurd h' hyQ
      · exact Or.inr h'
  have hpick : ∀ i : Fin 3, ∃ p : Fin 2,
      (if p = 0 then x else y) ∈ Q i.succ := by
    intro i
    rcases hhit i with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  choose pk hpk using hpick
  have hcard : ¬Function.Injective pk := by
    intro hinj
    have := Fintype.card_le_of_injective pk hinj
    simp at this
  rw [Function.not_injective_iff] at hcard
  obtain ⟨i, j, hpij, hij⟩ := hcard
  have h1 := hpk i
  have h2 := hpk j
  rw [hpij] at h1
  have hne : i.succ ≠ j.succ := fun h =>
    hij (Fin.succ_injective 3 h)
  exact (Finset.disjoint_left.1 (hdisj i.succ j.succ hne)) h1 h2

/-- Duty targets are fragile: a level-k duty target admits at
most |Q k| + 1 pairwise disjoint representations.  Contrapositive:
windows whose targets are all (|Q k| + 2)-robust repel every
level-k duty — the first placement constraint on the ledger. -/
theorem duty_targets_fragile {A : Set ℕ} {N₀ : ℕ}
    {Q : ℕ → Finset ℕ} {k b m K : ℕ}
    (hhub : IsRepSupportTransversal A m (insert b (Q k)))
    (hrob : HasDisjointTripleReps A m K) :
    K ≤ (Q k).card + 1 := by
  have h1 := disjoint_reps_le_support_transversal_card hhub hrob
  have h2 := Finset.card_insert_le b (Q k)
  omega

/-- Conflict targets are fragile: a conflict target of the rank layer
pair (j,k) admits at most |Q j| + |Q k| pairwise disjoint
representations.  Robust windows repel rank layer conflicts too. -/
theorem conflict_targets_fragile {A : Set ℕ} {N₀ : ℕ}
    {Q : ℕ → Finset ℕ} {j k m K : ℕ}
    (hhub : IsRepSupportTransversal A m (Q j ∪ Q k))
    (hrob : HasDisjointTripleReps A m K) :
    K ≤ (Q j).card + (Q k).card := by
  have h1 := disjoint_reps_le_support_transversal_card hhub hrob
  have h2 := Finset.card_union_le (Q j) (Q k)
  omega

/-! ## The robustness branch mechanism -/

theorem robustness_gives_hereditarily_free {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hrob : ∀ C, ∃ H, ∀ m, H ≤ m →
      HasDisjointTripleReps A m C) :
    ∃ B : Set ℕ, HereditarilyFree A N₀ B := by
  classical
  choose Hf hHf using hrob
  set M : ℕ → ℕ := fun C => (Finset.range (C + 1)).sup Hf
    with hM
  have hMrob : ∀ C m, M C ≤ m → HasDisjointTripleReps A m C := by
    intro C m hm
    refine hHf C m ?_
    have h1 : Hf C ≤ M C :=
      Finset.le_sup (Finset.mem_range.2 (by omega))
    omega
  have hMmono : ∀ C C', C ≤ C' → M C ≤ M C' := by
    intro C C' hCC
    exact Finset.sup_mono (by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega)
  have hstep : ∀ (i x : ℕ), ∃ a, a ∈ A ∧ x < a ∧
      M (i + 2) < a := by
    intro i x
    obtain ⟨a, ha, hge⟩ :=
      pairCovers_unbounded hcov (max x (M (i + 2)) + 1)
    have h1 : x ≤ max x (M (i + 2)) := le_max_left _ _
    have h2 : M (i + 2) ≤ max x (M (i + 2)) := le_max_right _ _
    exact ⟨a, ha, by omega, by omega⟩
  choose F hFA hFgt hFM using hstep
  obtain ⟨g, hg0, hgs⟩ : ∃ g : ℕ → ℕ, g 0 = F 0 0 ∧
      ∀ i, g (i + 1) = F (i + 1) (g i) :=
    ⟨fun i => Nat.rec (F 0 0) (fun i' prev => F (i' + 1) prev) i,
      rfl, fun _ => rfl⟩
  have hgA : ∀ i, g i ∈ A := by
    intro i
    cases i with
    | zero => rw [hg0]; exact hFA 0 0
    | succ i => rw [hgs]; exact hFA (i + 1) (g i)
  have hgM : ∀ i, M (i + 2) < g i := by
    intro i
    cases i with
    | zero => rw [hg0]; exact hFM 0 0
    | succ i => rw [hgs]; exact hFM (i + 1) (g i)
  have hgmono : StrictMono g := by
    apply strictMono_nat_of_lt_succ
    intro i
    rw [hgs]
    exact hFgt (i + 1) (g i)
  have hgpos : ∀ i, 0 < g i := by
    intro i
    cases i with
    | zero =>
      rw [hg0]
      exact lt_of_le_of_lt (Nat.zero_le _) (hFgt 0 0)
    | succ i =>
      rw [hgs]
      exact lt_of_le_of_lt (Nat.zero_le _) (hFgt (i + 1) (g i))
  have hgi : ∀ i, i ≤ g i := fun i => hgmono.le_apply
  refine ⟨Set.range g, Set.infinite_range_of_injective
    hgmono.injective, ?_, ?_⟩
  · rintro b ⟨i, rfl⟩
    exact ⟨hgA i, hgpos i⟩
  · intro P hP m hm
    have hidx : ∀ t ∈ P, ∃ i, g i = t := by
      intro t ht
      exact hP t ht
    choose idx hidx' using hidx
    set T := P.filter (fun t => t ≤ m) with hT
    set J := (Finset.range (m + 1)).filter (fun i => g i ≤ m)
      with hJ
    have hTJ : T.card ≤ J.card := by
      refine Finset.card_le_card_of_injOn
        (fun t => if ht : t ∈ P then idx t ht else 0) ?_ ?_
      · intro t ht
        have ht2 : t ∈ P ∧ t ≤ m := by simpa [hT] using ht
        have hgoal : (if ht : t ∈ P then idx t ht else 0) ∈ J := by
          rw [dif_pos ht2.1]
          have h1 : g (idx t ht2.1) = t := hidx' t ht2.1
          have h2 := hgi (idx t ht2.1)
          simp only [hJ, Finset.mem_filter, Finset.mem_range]
          omega
        exact hgoal
      · intro t ht t' ht' heq
        have ht2 : t ∈ P ∧ t ≤ m := by simpa [hT] using ht
        have ht'2 : t' ∈ P ∧ t' ≤ m := by simpa [hT] using ht'
        have heq' : (if ht : t ∈ P then idx t ht else 0) =
            (if ht' : t' ∈ P then idx t' ht' else 0) := heq
        rw [dif_pos ht2.1, dif_pos ht'2.1] at heq'
        have h1 : g (idx t ht2.1) = t := hidx' t ht2.1
        have h2 : g (idx t' ht'2.1) = t' := hidx' t' ht'2.1
        rw [← h1, ← h2, heq']
    by_cases hJ0 : J.card = 0
    · obtain ⟨x, hx, y, hy, hxy⟩ := hcov m hm
      have havoid : ∀ w, w ≤ m → w ∉ P := by
        intro w hw hwP
        have hwT : w ∈ T := by
          rw [hT, Finset.mem_filter]
          exact ⟨hwP, hw⟩
        have h1 : 0 < T.card := Finset.card_pos.2 ⟨w, hwT⟩
        omega
      refine ⟨x, hx, y, hy, 0, h0, by omega, ?_, ?_, ?_⟩
      · exact havoid x (by omega)
      · exact havoid y (by omega)
      · exact havoid 0 (by omega)
    · have hJne : J.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨imax, himax, himax'⟩ :=
        Finset.exists_max_image J id hJne
      have himaxJ : g imax ≤ m := by
        have h1 := himax
        rw [hJ, Finset.mem_filter] at h1
        exact h1.2
      have himax_ge : J.card ≤ imax + 1 := by
        have hsub : J ⊆ Finset.range (imax + 1) := by
          intro i hi
          rw [Finset.mem_range]
          have h2 : i ≤ imax := himax' i hi
          omega
        have h3 := Finset.card_le_card hsub
        rw [Finset.card_range] at h3
        omega
      have hMle : M (J.card + 1) ≤ m := by
        have h1 : M (J.card + 1) ≤ M (imax + 2) :=
          hMmono _ _ (by omega)
        have h2 := hgM imax
        omega
      obtain ⟨R, hRA, hRsum, hRdis⟩ :=
        hMrob (J.card + 1) m hMle
      by_contra hall
      push Not at hall
      have hpickP : ∀ i : Fin (J.card + 1), ∃ k : Fin 3,
          R i k ∈ P := by
        intro i
        by_cases hp0 : R i 0 ∈ P
        · exact ⟨0, hp0⟩
        by_cases hp1 : R i 1 ∈ P
        · exact ⟨1, hp1⟩
        exact ⟨2, hall (R i 0) (hRA i 0) (R i 1) (hRA i 1)
          (R i 2) (hRA i 2) (hRsum i) hp0 hp1⟩
      choose pk hpk using hpickP
      have hinjT : ∀ i : Fin (J.card + 1), R i (pk i) ∈ T := by
        intro i
        rw [hT, Finset.mem_filter]
        refine ⟨hpk i, ?_⟩
        have hle : ∀ k : Fin 3, R i k ≤ m := by
          have hs := hRsum i
          intro k
          match k with
          | 0 => omega
          | 1 => omega
          | 2 => omega
        exact hle (pk i)
      have hcard : (J.card + 1) ≤ T.card := by
        have h4 := Finset.card_le_card_of_injOn
          (f := fun i : Fin (J.card + 1) => R i (pk i))
          (s := Finset.univ) (t := T)
          (fun i _ => hinjT i)
          (by
            intro i _ i' _ heq
            by_contra hne
            exact hRdis i i' (pk i) (pk i') hne heq)
        rw [Finset.card_univ, Fintype.card_fin] at h4
        exact h4
      omega

theorem fragile_supply_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ C, ∀ H, ∃ m, H ≤ m ∧ ¬HasDisjointTripleReps A m C := by
  by_contra hno
  push Not at hno
  exact (hfail_iff_no_hereditarily_free h0 hcov).1 hfail
    (robustness_gives_hereditarily_free h0 hcov hno)

/-! ## The reflection ledger -/

theorem seal_cost_of_disjoint_avoiding {A : Set ℕ} {m K : ℕ}
    {S D : Finset ℕ} (P : Fin K → Fin 3 → ℕ)
    (hPA : ∀ i k, P i k ∈ A)
    (hPsum : ∀ i, P i 0 + P i 1 + P i 2 = m)
    (hPdis : ∀ i j k l, i ≠ j → P i k ≠ P j l)
    (hPavoid : ∀ i k, P i k ∉ S)
    (hseal : IsRepSupportTransversal (A \ ↑D) m S) :
    K ≤ D.card := by
  classical
  have hpick : ∀ i : Fin K, ∃ k : Fin 3, P i k ∈ D := by
    intro i
    by_contra hnone
    push Not at hnone
    have hmem : ∀ k : Fin 3, P i k ∈ A \ ↑D := by
      intro k
      exact ⟨hPA i k, by simpa using hnone k⟩
    rcases hseal (P i 0) (hmem 0) (P i 1) (hmem 1) (P i 2)
      (hmem 2) (hPsum i) with h | h | h
    · exact hPavoid i 0 h
    · exact hPavoid i 1 h
    · exact hPavoid i 2 h
  choose pk hpk using hpick
  have h1 := Finset.card_le_card_of_injOn
    (f := fun i : Fin K => P i (pk i))
    (s := Finset.univ) (t := D)
    (fun i _ => hpk i)
    (by
      intro i _ j _ heq
      by_contra hne
      exact hPdis i j (pk i) (pk j) hne heq)
  rw [Finset.card_univ, Fintype.card_fin] at h1
  exact h1

theorem two_support_transversals_common_reflection {A : Set ℕ} {N₀ m m' : ℕ}
    {H H' : Finset ℕ} (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hm : N₀ ≤ m) (hm' : N₀ ≤ m')
    (hhub : IsRepSupportTransversal A m H) (hhub' : IsRepSupportTransversal A m' H')
    (W : Finset ℕ)
    (hW : ∀ a ∈ W, a ∈ A ∧ a ∉ H ∧ a ∉ H' ∧
      a + N₀ ≤ m ∧ a + N₀ ≤ m') :
    ∃ h ∈ H, ∃ h' ∈ H', ∃ V ⊆ W,
      W.card ≤ H.card * H'.card * V.card ∧
      ∀ a ∈ V, (∃ x ∈ A, x + h + a = m) ∧
        (∃ x' ∈ A, x' + h' + a = m') := by
  classical
  -- envelopes are nonempty: the padded covering pair is a rep
  have hHne : H.Nonempty := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hcov m hm
    rcases hhub x hx y hy 0 h0 (by omega) with h | h | h
    · exact ⟨x, h⟩
    · exact ⟨y, h⟩
    · exact ⟨0, h⟩
  have hH'ne : H'.Nonempty := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hcov m' hm'
    rcases hhub' x hx y hy 0 h0 (by omega) with h | h | h
    · exact ⟨x, h⟩
    · exact ⟨y, h⟩
    · exact ⟨0, h⟩
  -- fan routing at each target sequence
  have hroute : ∀ a, ∃ hh xx, a ∈ W →
      hh ∈ H ∧ xx ∈ A ∧ xx + hh + a = m := by
    intro a
    by_cases haW : a ∈ W
    · obtain ⟨haA, haH, haH', ham, ham'⟩ := hW a haW
      obtain ⟨x, hx, y, hy, hxy⟩ := hcov (m - a) (by omega)
      have hsum : a + x + y = m := by omega
      rcases hhub a haA x hx y hy hsum with h | h | h
      · exact absurd h haH
      · exact ⟨x, y, fun _ => ⟨h, hy, by omega⟩⟩
      · exact ⟨y, x, fun _ => ⟨h, hx, by omega⟩⟩
    · exact ⟨hHne.choose, 0, fun hc => absurd hc haW⟩
  have hroute' : ∀ a, ∃ hh xx, a ∈ W →
      hh ∈ H' ∧ xx ∈ A ∧ xx + hh + a = m' := by
    intro a
    by_cases haW : a ∈ W
    · obtain ⟨haA, haH, haH', ham, ham'⟩ := hW a haW
      obtain ⟨x, hx, y, hy, hxy⟩ := hcov (m' - a) (by omega)
      have hsum : a + x + y = m' := by omega
      rcases hhub' a haA x hx y hy hsum with h | h | h
      · exact absurd h haH'
      · exact ⟨x, y, fun _ => ⟨h, hy, by omega⟩⟩
      · exact ⟨y, x, fun _ => ⟨h, hx, by omega⟩⟩
    · exact ⟨hH'ne.choose, 0, fun hc => absurd hc haW⟩
  choose f p hfp using hroute
  choose f' p' hf'p' using hroute'
  have hmaps : ∀ a ∈ W, (f a, f' a) ∈ H ×ˢ H' := by
    intro a ha
    rw [Finset.mem_product]
    exact ⟨(hfp a ha).1, (hf'p' a ha).1⟩
  obtain ⟨b₀, hb₀mem, hb₀max⟩ :=
    Finset.exists_max_image (H ×ˢ H')
      (fun b => (W.filter (fun a => (f a, f' a) = b)).card)
      ⟨(hHne.choose, hH'ne.choose), Finset.mem_product.2
        ⟨hHne.choose_spec, hH'ne.choose_spec⟩⟩
  obtain ⟨h₀, h₀'⟩ := b₀
  have hh₀ : h₀ ∈ H ∧ h₀' ∈ H' := Finset.mem_product.1 hb₀mem
  set V := W.filter (fun a => (f a, f' a) = (h₀, h₀')) with hV
  have hcount : W.card ≤ H.card * H'.card * V.card := by
    have h5 := Finset.card_le_mul_card_image_of_maps_to hmaps
      V.card
      (fun b hb => hb₀max b hb)
    rw [Finset.card_product] at h5
    calc W.card ≤ V.card * (H.card * H'.card) := h5
      _ = H.card * H'.card * V.card := by ring
  refine ⟨h₀, hh₀.1, h₀', hh₀.2, V, Finset.filter_subset _ _,
    hcount, ?_⟩
  intro a ha
  rw [hV, Finset.mem_filter] at ha
  obtain ⟨haW, haeq⟩ := ha
  have heq1 : f a = h₀ := by
    have := congrArg Prod.fst haeq
    simpa using this
  have heq2 : f' a = h₀' := by
    have := congrArg Prod.snd haeq
    simpa using this
  constructor
  · obtain ⟨_, hpA, hpsum⟩ := hfp a haW
    exact ⟨p a, hpA, by rw [← heq1]; exact hpsum⟩
  · obtain ⟨_, hpA, hpsum⟩ := hf'p' a haW
    exact ⟨p' a, hpA, by rw [← heq2]; exact hpsum⟩

theorem double_reflection_supply_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ K, ∃ u u' : ℕ, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ a ∈ V, a ∈ A ∧ (∃ x ∈ A, x + a = u) ∧
        (∃ x' ∈ A, x' + a = u') := by
  classical
  obtain ⟨P, hPfree, X, hflood⟩ := rep_cofinal_supply_of_hfail h0 hcov hfail
  intro K
  set C := P.card + 1 with hC
  set T := K * C * C + 2 * C + 1 with hT
  -- target sequence 1: a large required element with its personal support transversal
  obtain ⟨b, hbA, hbge⟩ :=
    pairCovers_unbounded hcov (X + T * T + 2 * N₀ + 1)
  obtain ⟨m, hm, hbm, hhub⟩ := hflood b hbA (by omega)
  -- target sequence 2: strictly beyond target sequence 1
  obtain ⟨b', hb'A, hb'ge⟩ := pairCovers_unbounded hcov (X + m + 1)
  obtain ⟨m', hm', hb'm', hhub'⟩ := hflood b' hb'A (by omega)
  -- the window: A-elements below target sequence 1's horizon
  haveI : DecidablePred (· ∈ A) := Classical.decPred _
  set F := ((Finset.range (b - N₀ + 1)).filter (· ∈ A)) with hF
  have hFcard : T ≤ F.card := by
    have h1 := covering_sqrt_lower (A := A) (N₀ := N₀) hcov
      (n := b - N₀) (by omega)
    by_contra hlt
    push Not at hlt
    have h2 : F.card * F.card < T * T :=
      Nat.mul_lt_mul_of_lt_of_le hlt (le_of_lt hlt) (by omega)
    rw [← hF] at h1
    omega
  set H := insert b P with hH
  set H' := insert b' P with hH'
  have hHc : H.card ≤ C := by
    rw [hH, hC]
    exact Finset.card_insert_le b P
  have hH'c : H'.card ≤ C := by
    rw [hH', hC]
    exact Finset.card_insert_le b' P
  set W := F \ (H ∪ H') with hW
  have hWcard : K * C * C + 1 ≤ W.card := by
    have h1 := Finset.card_le_card_sdiff_add_card (s := F)
      (t := H ∪ H')
    rw [← hW] at h1
    have h2 : (H ∪ H').card ≤ 2 * C := by
      have h3 := Finset.card_union_le H H'
      omega
    omega
  have hWmem : ∀ a ∈ W, a ∈ A ∧ a ∉ H ∧ a ∉ H' ∧
      a + N₀ ≤ m ∧ a + N₀ ≤ m' := by
    intro a ha
    rw [hW, Finset.mem_sdiff, Finset.mem_union] at ha
    obtain ⟨haF, haHH⟩ := ha
    rw [hF, Finset.mem_filter, Finset.mem_range] at haF
    push Not at haHH
    refine ⟨haF.2, haHH.1, haHH.2, ?_, ?_⟩
    · omega
    · omega
  obtain ⟨h₀, hh₀, h₀', hh₀', V, hVW, hcount, hVrefl⟩ :=
    two_support_transversals_common_reflection h0 hcov hm hm' hhub hhub' W hWmem
  refine ⟨m - h₀, m' - h₀', V, ?_, ?_⟩
  · -- K ≤ V.card from the pigeonhole count
    have h1 : H.card * H'.card ≤ C * C :=
      Nat.mul_le_mul hHc hH'c
    have h2 : H.card * H'.card * V.card ≤ C * C * V.card :=
      Nat.mul_le_mul h1 (le_refl V.card)
    by_contra hVK
    push Not at hVK
    have hVK' : V.card + 1 ≤ K := hVK
    have h3 : C * C * (V.card + 1) ≤ C * C * K :=
      Nat.mul_le_mul (le_refl (C * C)) hVK'
    rw [Nat.mul_add, Nat.mul_one] at h3
    have h4 : K * C * C = C * C * K := by ring
    omega
  · intro a ha
    obtain ⟨hx, hx'⟩ := hVrefl a ha
    obtain ⟨x, hxA, hxeq⟩ := hx
    obtain ⟨x', hx'A, hx'eq⟩ := hx'
    have haW := hVW ha
    have haA := (hWmem a haW).1
    exact ⟨haA, ⟨x, hxA, by omega⟩, ⟨x', hx'A, by omega⟩⟩

/-! ## The target sequence dichotomy and the four cases -/

theorem target_sequence_dichotomy_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ K S,
    (∃ δ, 1 ≤ δ ∧ ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A) ∨
    (∃ n, (∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ a ∈ V, a ∈ A ∧ ∃ x ∈ A, x + a = n) ∧
      ∃ Q : Finset ℕ, RepFree A N₀ Q ∧ ∃ b₂ ∈ A, ∃ b₃ ∈ A,
        S ≤ b₂ ∧ b₂ < b₃ ∧ ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
          IsPairSupportTransversal A s (insert b₃ Q)) := by
  classical
  obtain ⟨P, hPfree, X, hflood⟩ := rep_cofinal_supply_of_hfail h0 hcov hfail
  intro K S
  rcases Nat.eq_zero_or_pos K with hK0 | hK0
  · left
    refine ⟨1, le_refl 1, ∅, by simp [hK0], ?_⟩
    intro x hx
    exact absurd hx (Finset.notMem_empty x)
  set C := P.card + 1 with hC
  set D := C * C * C * C with hD
  set T := K * D + 3 * C + 1 with hT
  obtain ⟨b₁, hb₁A, hb₁ge⟩ :=
    pairCovers_unbounded hcov (X + T * T + 2 * N₀ + 1)
  obtain ⟨m₁, hm₁, hb₁m₁, hhub₁⟩ := hflood b₁ hb₁A (by omega)
  obtain ⟨b₂, hb₂A, hb₂ge⟩ := pairCovers_unbounded hcov
    (X + S + m₁ + P.sup id + N₀ + 1)
  obtain ⟨m₂, hm₂, hb₂m₂, hhub₂⟩ := hflood b₂ hb₂A (by omega)
  obtain ⟨b₃, hb₃A, hb₃ge⟩ := pairCovers_unbounded hcov
    (X + m₂ + P.sup id + N₀ + 1)
  obtain ⟨m₃, hm₃, hb₃m₃, hhub₃⟩ := hflood b₃ hb₃A (by omega)
  haveI : DecidablePred (· ∈ A) := Classical.decPred _
  set F := ((Finset.range (b₁ - N₀ + 1)).filter (· ∈ A)) with hF
  have hFcard : T ≤ F.card := by
    have h1 := covering_sqrt_lower (A := A) (N₀ := N₀) hcov
      (n := b₁ - N₀) (by omega)
    by_contra hlt
    push Not at hlt
    have h2 : F.card * F.card < T * T :=
      Nat.mul_lt_mul_of_lt_of_le hlt (le_of_lt hlt) (by omega)
    rw [← hF] at h1
    omega
  set H₁ := insert b₁ P with hH₁
  set H₂ := insert b₂ P with hH₂
  set H₃ := insert b₃ P with hH₃
  have hH₁c : H₁.card ≤ C := by
    rw [hH₁, hC]; exact Finset.card_insert_le b₁ P
  have hH₂c : H₂.card ≤ C := by
    rw [hH₂, hC]; exact Finset.card_insert_le b₂ P
  have hH₃c : H₃.card ≤ C := by
    rw [hH₃, hC]; exact Finset.card_insert_le b₃ P
  set W := F \ (H₁ ∪ H₂ ∪ H₃) with hW
  have hWcard : K * D + 1 ≤ W.card := by
    have h1 := Finset.card_le_card_sdiff_add_card (s := F)
      (t := H₁ ∪ H₂ ∪ H₃)
    rw [← hW] at h1
    have h2 : (H₁ ∪ H₂ ∪ H₃).card ≤ 3 * C := by
      have h3 := Finset.card_union_le (H₁ ∪ H₂) H₃
      have h4 := Finset.card_union_le H₁ H₂
      omega
    omega
  have hWmem : ∀ a ∈ W, a ∈ A ∧ a ∉ H₁ ∧ a ∉ H₂ ∧ a ∉ H₃ ∧
      a + N₀ ≤ m₁ ∧ a + N₀ ≤ m₂ ∧ a + N₀ ≤ m₃ := by
    intro a ha
    rw [hW, Finset.mem_sdiff, Finset.mem_union,
      Finset.mem_union] at ha
    obtain ⟨haF, haH⟩ := ha
    rw [hF, Finset.mem_filter, Finset.mem_range] at haF
    push Not at haH
    exact ⟨haF.2, haH.1.1, haH.1.2, haH.2, by omega, by omega,
      by omega⟩
  obtain ⟨g₁, hg₁, g₂, hg₂, V₁, hV₁W, hcount₁, hrefl₁⟩ :=
    two_support_transversals_common_reflection h0 hcov hm₁ hm₂ hhub₁ hhub₂ W
      (fun a ha => ⟨(hWmem a ha).1, (hWmem a ha).2.1,
        (hWmem a ha).2.2.1, (hWmem a ha).2.2.2.2.1,
        (hWmem a ha).2.2.2.2.2.1⟩)
  obtain ⟨g₁', hg₁', g₃, hg₃, V₂, hV₂V₁, hcount₂, hrefl₂⟩ :=
    two_support_transversals_common_reflection h0 hcov hm₁ hm₃ hhub₁ hhub₃ V₁
      (fun a ha => ⟨(hWmem a (hV₁W ha)).1,
        (hWmem a (hV₁W ha)).2.1,
        (hWmem a (hV₁W ha)).2.2.2.1,
        (hWmem a (hV₁W ha)).2.2.2.2.1,
        (hWmem a (hV₁W ha)).2.2.2.2.2.2⟩)
  have hVK : K ≤ V₂.card := by
    have e₁ : W.card ≤ C * C * V₁.card :=
      le_trans hcount₁
        (Nat.mul_le_mul (Nat.mul_le_mul hH₁c hH₂c)
          (le_refl V₁.card))
    have e₂ : V₁.card ≤ C * C * V₂.card :=
      le_trans hcount₂
        (Nat.mul_le_mul (Nat.mul_le_mul hH₁c hH₃c)
          (le_refl V₂.card))
    have e₃ : C * C * V₁.card ≤ C * C * (C * C * V₂.card) :=
      Nat.mul_le_mul (le_refl (C * C)) e₂
    have e₄ : C * C * (C * C * V₂.card) = D * V₂.card := by
      rw [hD]; ring
    by_contra hK
    push Not at hK
    have hK' : V₂.card + 1 ≤ K := hK
    have e₅ : D * (V₂.card + 1) ≤ D * K :=
      Nat.mul_le_mul (le_refl D) hK'
    rw [Nat.mul_add, Nat.mul_one] at e₅
    have e₆ : K * D = D * K := by ring
    omega
  obtain ⟨a₀, ha₀⟩ := Finset.card_pos.1
    (lt_of_lt_of_le hK0 hVK)
  obtain ⟨⟨xw₁, hxw₁A, hxw₁⟩, ⟨xw₂, hxw₂A, hxw₂⟩⟩ :=
    hrefl₁ a₀ (hV₂V₁ ha₀)
  obtain ⟨⟨xw₁', hxw₁'A, hxw₁'⟩, ⟨xw₃, hxw₃A, hxw₃⟩⟩ :=
    hrefl₂ a₀ ha₀
  set u₁ := m₁ - g₁ with hu₁
  set u₂ := m₂ - g₂ with hu₂
  set u₁' := m₁ - g₁' with hu₁'
  set u₃ := m₃ - g₃ with hu₃
  have hpt₁ : u₁ + g₁ = m₁ := by omega
  have hpt₂ : u₂ + g₂ = m₂ := by omega
  have hpt₁' : u₁' + g₁' = m₁ := by omega
  have hpt₃ : u₃ + g₃ = m₃ := by omega
  have hrA : ∀ a ∈ V₂, a ∈ A ∧
      (∃ x ∈ A, x + a = u₁) ∧ (∃ x ∈ A, x + a = u₂) ∧
      (∃ x ∈ A, x + a = u₁') ∧ (∃ x ∈ A, x + a = u₃) := by
    intro a ha
    obtain ⟨⟨x₁, hx₁A, hx₁⟩, ⟨x₂, hx₂A, hx₂⟩⟩ :=
      hrefl₁ a (hV₂V₁ ha)
    obtain ⟨⟨x₁', hx₁'A, hx₁'⟩, ⟨x₃, hx₃A, hx₃⟩⟩ := hrefl₂ a ha
    exact ⟨(hWmem a (hV₁W (hV₂V₁ ha))).1,
      ⟨x₁, hx₁A, by omega⟩, ⟨x₂, hx₂A, by omega⟩,
      ⟨x₁', hx₁'A, by omega⟩, ⟨x₃, hx₃A, by omega⟩⟩
  have mkdiff : ∀ p q : ℕ, p < q →
      (∀ a ∈ V₂, ∃ x ∈ A, x + a = p) →
      (∀ a ∈ V₂, ∃ x ∈ A, x + a = q) →
      (∃ δ, 1 ≤ δ ∧ ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A) := by
    intro p q hpq hp hq
    refine ⟨q - p, by omega, V₂.image (fun a => p - a), ?_, ?_⟩
    · rw [Finset.card_image_of_injOn]
      · exact hVK
      · intro a ha a' ha' heq
        obtain ⟨x, hxA, hx⟩ := hp a ha
        obtain ⟨x', hx'A, hx'⟩ := hp a' ha'
        simp only at heq
        omega
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨w, hwA, hw⟩ := hp a ha
      obtain ⟨w', hw'A, hw'⟩ := hq a ha
      have hwe : w = p - a := by omega
      have hw2 : w + (q - p) = w' := by omega
      rw [← hwe, hw2]
      exact ⟨hwA, hw'A⟩
  have proj₁ : ∀ a ∈ V₂, ∃ x ∈ A, x + a = u₁ :=
    fun a ha => (hrA a ha).2.1
  have proj₂ : ∀ a ∈ V₂, ∃ x ∈ A, x + a = u₂ :=
    fun a ha => (hrA a ha).2.2.1
  have proj₁' : ∀ a ∈ V₂, ∃ x ∈ A, x + a = u₁' :=
    fun a ha => (hrA a ha).2.2.2.1
  have proj₃ : ∀ a ∈ V₂, ∃ x ∈ A, x + a = u₃ :=
    fun a ha => (hrA a ha).2.2.2.2
  by_cases h12 : u₁ = u₂
  · by_cases h11' : u₁ = u₁'
    · by_cases h13 : u₁ = u₃
      · -- the affine corner
        right
        have hg₂P : g₂ = b₂ := by
          rcases Finset.mem_insert.1 hg₂ with h | h
          · exact h
          · exfalso
            have hle : g₂ ≤ P.sup id :=
              Finset.le_sup (f := id) h
            omega
        have hg₃P : g₃ = b₃ := by
          rcases Finset.mem_insert.1 hg₃ with h | h
          · exact h
          · exfalso
            have hle : g₃ ≤ P.sup id :=
              Finset.le_sup (f := id) h
            omega
        refine ⟨u₁, ⟨V₂, hVK, fun a ha =>
          ⟨(hrA a ha).1, proj₁ a ha⟩⟩, P, hPfree,
          b₂, hb₂A, b₃, hb₃A, by omega, by omega,
          m₃ - b₂, by omega, by omega, ?_⟩
        intro x hx y hy hxy
        have hsum : b₂ + x + y = m₃ := by omega
        rcases hhub₃ b₂ hb₂A x hx y hy hsum with h | h | h
        · exfalso
          rcases Finset.mem_insert.1 h with h' | h'
          · omega
          · have hle : b₂ ≤ P.sup id :=
              Finset.le_sup (f := id) h'
            omega
        · exact Or.inl h
        · exact Or.inr h
      · left
        rcases Nat.lt_or_ge u₁ u₃ with h | h
        · exact mkdiff u₁ u₃ h proj₁ proj₃
        · exact mkdiff u₃ u₁ (by omega) proj₃ proj₁
    · left
      rcases Nat.lt_or_ge u₁ u₁' with h | h
      · exact mkdiff u₁ u₁' h proj₁ proj₁'
      · exact mkdiff u₁' u₁ (by omega) proj₁' proj₁
  · left
    rcases Nat.lt_or_ge u₁ u₂ with h | h
    · exact mkdiff u₁ u₂ h proj₁ proj₂
    · exact mkdiff u₂ u₁ (by omega) proj₂ proj₁

theorem difference_amplification_or_affine_corners {A : Set ℕ}
    {N₀ : ℕ} (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∀ K, ∃ δ, 1 ≤ δ ∧ ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A) ∨
    (∃ K₀, ∀ S, ∃ n, (∃ V : Finset ℕ, K₀ ≤ V.card ∧
        ∀ a ∈ V, a ∈ A ∧ ∃ x ∈ A, x + a = n) ∧
      ∃ Q : Finset ℕ, RepFree A N₀ Q ∧ ∃ b₂ ∈ A, ∃ b₃ ∈ A,
        S ≤ b₂ ∧ b₂ < b₃ ∧ ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
          IsPairSupportTransversal A s (insert b₃ Q)) := by
  by_cases hdiff : ∀ K, ∃ δ, 1 ≤ δ ∧ ∃ V : Finset ℕ,
      K ≤ V.card ∧ ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A
  · exact Or.inl hdiff
  · push Not at hdiff
    obtain ⟨K₀, hK₀⟩ := hdiff
    refine Or.inr ⟨K₀, fun S => ?_⟩
    rcases target_sequence_dichotomy_of_hfail h0 hcov hfail K₀ S with
      h | h
    · exfalso
      obtain ⟨δ, hδ, V, hV, hVmem⟩ := h
      obtain ⟨x, hxV, hximp⟩ := hK₀ δ hδ V hV
      obtain ⟨hxA, hxδ⟩ := hVmem x hxV
      exact hximp hxA hxδ
    · exact h

/-- Refinement of the difference branch: unbounded multiplicity
either concentrates at ONE fixed offset δ — infinitely many
x ∈ A with x + δ ∈ A, near-translation-invariance — or escapes
through arbitrarily large offsets at every multiplicity. -/
theorem fixed_offset_or_growing {A : Set ℕ}
    (hdiff : ∀ K, ∃ δ, 1 ≤ δ ∧ ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A) :
    (∃ δ, 1 ≤ δ ∧ ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A) ∨
    (∀ Δ K, ∃ δ, Δ < δ ∧ ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A) := by
  classical
  by_cases hfix : ∃ δ, 1 ≤ δ ∧ ∀ K, ∃ V : Finset ℕ,
      K ≤ V.card ∧ ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A
  · exact Or.inl hfix
  · push Not at hfix
    have hKf : ∀ δ, ∃ Kd, 1 ≤ δ → ∀ V : Finset ℕ,
        Kd ≤ V.card → ∃ x ∈ V, x ∈ A → x + δ ∉ A := by
      intro δ
      by_cases hδ : 1 ≤ δ
      · obtain ⟨Kd, hKd⟩ := hfix δ hδ
        exact ⟨Kd, fun _ => hKd⟩
      · exact ⟨0, fun h => absurd h hδ⟩
    choose Kf hKf' using hKf
    right
    intro Δ K
    set Ksup := (Finset.range (Δ + 1)).sup Kf with hKsup
    obtain ⟨δ₀, hδ₀, V₀, hV₀c, hV₀m⟩ := hdiff (K + Ksup)
    by_cases hle : δ₀ ≤ Δ
    · exfalso
      have hsup : Kf δ₀ ≤ Ksup := by
        rw [hKsup]
        exact Finset.le_sup (Finset.mem_range.2 (by omega))
      obtain ⟨x, hxV, himp⟩ :=
        hKf' δ₀ hδ₀ V₀ (by omega)
      obtain ⟨hxA, hxd⟩ := hV₀m x hxV
      exact himp hxA hxd
    · push Not at hle
      exact ⟨δ₀, hle, V₀, by omega, hV₀m⟩

/-- An affine corner at blown point n and size S: a K₀-fold
reflected point coupled to two basis elements beyond S and a pair
target sequence at the difference translate (s + b₂ = n + b₃). -/
def AffineCorner (A : Set ℕ) (N₀ K₀ n S : ℕ) : Prop :=
  (∃ V : Finset ℕ, K₀ ≤ V.card ∧
    ∀ a ∈ V, a ∈ A ∧ ∃ x ∈ A, x + a = n) ∧
  ∃ Q : Finset ℕ, RepFree A N₀ Q ∧ ∃ b₂ ∈ A, ∃ b₃ ∈ A,
    S ≤ b₂ ∧ b₂ < b₃ ∧ ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
      IsPairSupportTransversal A s (insert b₃ Q)

/-- Corners are antitone in the size threshold. -/
theorem AffineCorner.anti {A : Set ℕ} {N₀ K₀ n S S' : ℕ}
    (hSS : S ≤ S') (h : AffineCorner A N₀ K₀ n S') :
    AffineCorner A N₀ K₀ n S := by
  obtain ⟨hV, Q, hQ, b₂, hb₂, b₃, hb₃, hS, hlt, rest⟩ := h
  exact ⟨hV, Q, hQ, b₂, hb₂, b₃, hb₃, by omega, hlt, rest⟩

/-- Generic stabilize-or-escape for size-antitone ℕ-parametrized
families: a parameter valid beyond every size either stabilizes
(one value works at all sizes) or escapes (arbitrarily large
values occur at every size). -/
theorem nat_param_stabilize {C : ℕ → ℕ → Prop}
    (hanti : ∀ n S S', S ≤ S' → C n S' → C n S)
    (hex : ∀ S, ∃ n, C n S) :
    (∃ n, ∀ S, C n S) ∨ (∀ N S, ∃ n, N < n ∧ C n S) := by
  classical
  by_cases hstab : ∃ n, ∀ S, C n S
  · exact Or.inl hstab
  · push Not at hstab
    choose Sf hSf using hstab
    right
    intro N S
    set Ssup := max S ((Finset.range (N + 1)).sup Sf) with hSsup
    obtain ⟨n₀, hn₀⟩ := hex Ssup
    by_cases hle : n₀ ≤ N
    · exfalso
      have h1 : Sf n₀ ≤ Ssup := by
        have h2 : Sf n₀ ≤ (Finset.range (N + 1)).sup Sf :=
          Finset.le_sup (Finset.mem_range.2 (by omega))
        omega
      exact hSf n₀ (hanti n₀ (Sf n₀) Ssup h1 hn₀)
    · push Not at hle
      exact ⟨n₀, hle, hanti n₀ S Ssup (le_max_left _ _) hn₀⟩

theorem affine_corner_fixed_or_scattered {A : Set ℕ}
    {N₀ K₀ : ℕ}
    (hcorner : ∀ S, ∃ n, AffineCorner A N₀ K₀ n S) :
    (∃ n, ∀ S, AffineCorner A N₀ K₀ n S) ∨
    (∀ N S, ∃ n, N < n ∧ AffineCorner A N₀ K₀ n S) :=
  nat_param_stabilize
    (fun _ _ _ hSS h => AffineCorner.anti hSS h) hcorner

/-- Uniform-envelope form of the target sequence dichotomy: ONE free
envelope Q (the cofinal supply envelope) serves every K and S.  This is
what the proof always produced; recording it makes the affine
corners comparable across sizes. -/
theorem target_sequence_dichotomy_uniform {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ Q : Finset ℕ, RepFree A N₀ Q ∧ ∀ K S,
    (∃ δ, 1 ≤ δ ∧ ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A) ∨
    (∃ n, (∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ a ∈ V, a ∈ A ∧ ∃ x ∈ A, x + a = n) ∧
      ∃ b₂ ∈ A, ∃ b₃ ∈ A,
        S ≤ b₂ ∧ b₂ < b₃ ∧ ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
          IsPairSupportTransversal A s (insert b₃ Q)) := by
  classical
  obtain ⟨P, hPfree, X, hflood⟩ := rep_cofinal_supply_of_hfail h0 hcov hfail
  refine ⟨P, hPfree, ?_⟩
  intro K S
  rcases Nat.eq_zero_or_pos K with hK0 | hK0
  · left
    refine ⟨1, le_refl 1, ∅, by simp [hK0], ?_⟩
    intro x hx
    exact absurd hx (Finset.notMem_empty x)
  set C := P.card + 1 with hC
  set D := C * C * C * C with hD
  set T := K * D + 3 * C + 1 with hT
  obtain ⟨b₁, hb₁A, hb₁ge⟩ :=
    pairCovers_unbounded hcov (X + T * T + 2 * N₀ + 1)
  obtain ⟨m₁, hm₁, hb₁m₁, hhub₁⟩ := hflood b₁ hb₁A (by omega)
  obtain ⟨b₂, hb₂A, hb₂ge⟩ := pairCovers_unbounded hcov
    (X + S + m₁ + P.sup id + N₀ + 1)
  obtain ⟨m₂, hm₂, hb₂m₂, hhub₂⟩ := hflood b₂ hb₂A (by omega)
  obtain ⟨b₃, hb₃A, hb₃ge⟩ := pairCovers_unbounded hcov
    (X + m₂ + P.sup id + N₀ + 1)
  obtain ⟨m₃, hm₃, hb₃m₃, hhub₃⟩ := hflood b₃ hb₃A (by omega)
  haveI : DecidablePred (· ∈ A) := Classical.decPred _
  set F := ((Finset.range (b₁ - N₀ + 1)).filter (· ∈ A)) with hF
  have hFcard : T ≤ F.card := by
    have h1 := covering_sqrt_lower (A := A) (N₀ := N₀) hcov
      (n := b₁ - N₀) (by omega)
    by_contra hlt
    push Not at hlt
    have h2 : F.card * F.card < T * T :=
      Nat.mul_lt_mul_of_lt_of_le hlt (le_of_lt hlt) (by omega)
    rw [← hF] at h1
    omega
  set H₁ := insert b₁ P with hH₁
  set H₂ := insert b₂ P with hH₂
  set H₃ := insert b₃ P with hH₃
  have hH₁c : H₁.card ≤ C := by
    rw [hH₁, hC]; exact Finset.card_insert_le b₁ P
  have hH₂c : H₂.card ≤ C := by
    rw [hH₂, hC]; exact Finset.card_insert_le b₂ P
  have hH₃c : H₃.card ≤ C := by
    rw [hH₃, hC]; exact Finset.card_insert_le b₃ P
  set W := F \ (H₁ ∪ H₂ ∪ H₃) with hW
  have hWcard : K * D + 1 ≤ W.card := by
    have h1 := Finset.card_le_card_sdiff_add_card (s := F)
      (t := H₁ ∪ H₂ ∪ H₃)
    rw [← hW] at h1
    have h2 : (H₁ ∪ H₂ ∪ H₃).card ≤ 3 * C := by
      have h3 := Finset.card_union_le (H₁ ∪ H₂) H₃
      have h4 := Finset.card_union_le H₁ H₂
      omega
    omega
  have hWmem : ∀ a ∈ W, a ∈ A ∧ a ∉ H₁ ∧ a ∉ H₂ ∧ a ∉ H₃ ∧
      a + N₀ ≤ m₁ ∧ a + N₀ ≤ m₂ ∧ a + N₀ ≤ m₃ := by
    intro a ha
    rw [hW, Finset.mem_sdiff, Finset.mem_union,
      Finset.mem_union] at ha
    obtain ⟨haF, haH⟩ := ha
    rw [hF, Finset.mem_filter, Finset.mem_range] at haF
    push Not at haH
    exact ⟨haF.2, haH.1.1, haH.1.2, haH.2, by omega, by omega,
      by omega⟩
  obtain ⟨g₁, hg₁, g₂, hg₂, V₁, hV₁W, hcount₁, hrefl₁⟩ :=
    two_support_transversals_common_reflection h0 hcov hm₁ hm₂ hhub₁ hhub₂ W
      (fun a ha => ⟨(hWmem a ha).1, (hWmem a ha).2.1,
        (hWmem a ha).2.2.1, (hWmem a ha).2.2.2.2.1,
        (hWmem a ha).2.2.2.2.2.1⟩)
  obtain ⟨g₁', hg₁', g₃, hg₃, V₂, hV₂V₁, hcount₂, hrefl₂⟩ :=
    two_support_transversals_common_reflection h0 hcov hm₁ hm₃ hhub₁ hhub₃ V₁
      (fun a ha => ⟨(hWmem a (hV₁W ha)).1,
        (hWmem a (hV₁W ha)).2.1,
        (hWmem a (hV₁W ha)).2.2.2.1,
        (hWmem a (hV₁W ha)).2.2.2.2.1,
        (hWmem a (hV₁W ha)).2.2.2.2.2.2⟩)
  have hVK : K ≤ V₂.card := by
    have e₁ : W.card ≤ C * C * V₁.card :=
      le_trans hcount₁
        (Nat.mul_le_mul (Nat.mul_le_mul hH₁c hH₂c)
          (le_refl V₁.card))
    have e₂ : V₁.card ≤ C * C * V₂.card :=
      le_trans hcount₂
        (Nat.mul_le_mul (Nat.mul_le_mul hH₁c hH₃c)
          (le_refl V₂.card))
    have e₃ : C * C * V₁.card ≤ C * C * (C * C * V₂.card) :=
      Nat.mul_le_mul (le_refl (C * C)) e₂
    have e₄ : C * C * (C * C * V₂.card) = D * V₂.card := by
      rw [hD]; ring
    by_contra hK
    push Not at hK
    have hK' : V₂.card + 1 ≤ K := hK
    have e₅ : D * (V₂.card + 1) ≤ D * K :=
      Nat.mul_le_mul (le_refl D) hK'
    rw [Nat.mul_add, Nat.mul_one] at e₅
    have e₆ : K * D = D * K := by ring
    omega
  obtain ⟨a₀, ha₀⟩ := Finset.card_pos.1
    (lt_of_lt_of_le hK0 hVK)
  obtain ⟨⟨xw₁, hxw₁A, hxw₁⟩, ⟨xw₂, hxw₂A, hxw₂⟩⟩ :=
    hrefl₁ a₀ (hV₂V₁ ha₀)
  obtain ⟨⟨xw₁', hxw₁'A, hxw₁'⟩, ⟨xw₃, hxw₃A, hxw₃⟩⟩ :=
    hrefl₂ a₀ ha₀
  set u₁ := m₁ - g₁ with hu₁
  set u₂ := m₂ - g₂ with hu₂
  set u₁' := m₁ - g₁' with hu₁'
  set u₃ := m₃ - g₃ with hu₃
  have hpt₁ : u₁ + g₁ = m₁ := by omega
  have hpt₂ : u₂ + g₂ = m₂ := by omega
  have hpt₁' : u₁' + g₁' = m₁ := by omega
  have hpt₃ : u₃ + g₃ = m₃ := by omega
  have hrA : ∀ a ∈ V₂, a ∈ A ∧
      (∃ x ∈ A, x + a = u₁) ∧ (∃ x ∈ A, x + a = u₂) ∧
      (∃ x ∈ A, x + a = u₁') ∧ (∃ x ∈ A, x + a = u₃) := by
    intro a ha
    obtain ⟨⟨x₁, hx₁A, hx₁⟩, ⟨x₂, hx₂A, hx₂⟩⟩ :=
      hrefl₁ a (hV₂V₁ ha)
    obtain ⟨⟨x₁', hx₁'A, hx₁'⟩, ⟨x₃, hx₃A, hx₃⟩⟩ := hrefl₂ a ha
    exact ⟨(hWmem a (hV₁W (hV₂V₁ ha))).1,
      ⟨x₁, hx₁A, by omega⟩, ⟨x₂, hx₂A, by omega⟩,
      ⟨x₁', hx₁'A, by omega⟩, ⟨x₃, hx₃A, by omega⟩⟩
  have mkdiff : ∀ p q : ℕ, p < q →
      (∀ a ∈ V₂, ∃ x ∈ A, x + a = p) →
      (∀ a ∈ V₂, ∃ x ∈ A, x + a = q) →
      (∃ δ, 1 ≤ δ ∧ ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A) := by
    intro p q hpq hp hq
    refine ⟨q - p, by omega, V₂.image (fun a => p - a), ?_, ?_⟩
    · rw [Finset.card_image_of_injOn]
      · exact hVK
      · intro a ha a' ha' heq
        obtain ⟨x, hxA, hx⟩ := hp a ha
        obtain ⟨x', hx'A, hx'⟩ := hp a' ha'
        simp only at heq
        omega
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨w, hwA, hw⟩ := hp a ha
      obtain ⟨w', hw'A, hw'⟩ := hq a ha
      have hwe : w = p - a := by omega
      have hw2 : w + (q - p) = w' := by omega
      rw [← hwe, hw2]
      exact ⟨hwA, hw'A⟩
  have proj₁ : ∀ a ∈ V₂, ∃ x ∈ A, x + a = u₁ :=
    fun a ha => (hrA a ha).2.1
  have proj₂ : ∀ a ∈ V₂, ∃ x ∈ A, x + a = u₂ :=
    fun a ha => (hrA a ha).2.2.1
  have proj₁' : ∀ a ∈ V₂, ∃ x ∈ A, x + a = u₁' :=
    fun a ha => (hrA a ha).2.2.2.1
  have proj₃ : ∀ a ∈ V₂, ∃ x ∈ A, x + a = u₃ :=
    fun a ha => (hrA a ha).2.2.2.2
  by_cases h12 : u₁ = u₂
  · by_cases h11' : u₁ = u₁'
    · by_cases h13 : u₁ = u₃
      · right
        have hg₂P : g₂ = b₂ := by
          rcases Finset.mem_insert.1 hg₂ with h | h
          · exact h
          · exfalso
            have hle : g₂ ≤ P.sup id :=
              Finset.le_sup (f := id) h
            omega
        have hg₃P : g₃ = b₃ := by
          rcases Finset.mem_insert.1 hg₃ with h | h
          · exact h
          · exfalso
            have hle : g₃ ≤ P.sup id :=
              Finset.le_sup (f := id) h
            omega
        refine ⟨u₁, ⟨V₂, hVK, fun a ha =>
          ⟨(hrA a ha).1, proj₁ a ha⟩⟩,
          b₂, hb₂A, b₃, hb₃A, by omega, by omega,
          m₃ - b₂, by omega, by omega, ?_⟩
        intro x hx y hy hxy
        have hsum : b₂ + x + y = m₃ := by omega
        rcases hhub₃ b₂ hb₂A x hx y hy hsum with h | h | h
        · exfalso
          rcases Finset.mem_insert.1 h with h' | h'
          · omega
          · have hle : b₂ ≤ P.sup id :=
              Finset.le_sup (f := id) h'
            omega
        · exact Or.inl h
        · exact Or.inr h
      · left
        rcases Nat.lt_or_ge u₁ u₃ with h | h
        · exact mkdiff u₁ u₃ h proj₁ proj₃
        · exact mkdiff u₃ u₁ (by omega) proj₃ proj₁
    · left
      rcases Nat.lt_or_ge u₁ u₁' with h | h
      · exact mkdiff u₁ u₁' h proj₁ proj₁'
      · exact mkdiff u₁' u₁ (by omega) proj₁' proj₁
  · left
    rcases Nat.lt_or_ge u₁ u₂ with h | h
    · exact mkdiff u₁ u₂ h proj₁ proj₂
    · exact mkdiff u₂ u₁ (by omega) proj₂ proj₁

theorem fixed_hall_extracts_difference {A : Set ℕ} {N₀ : ℕ}
    {Q : Finset ℕ} {n : ℕ}
    (hcorner : ∀ S, ∃ b₂ ∈ A, ∃ b₃ ∈ A, S ≤ b₂ ∧ b₂ < b₃ ∧
      ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
        IsPairSupportTransversal A s (insert b₃ Q)) :
    (∃ δ, 1 ≤ δ ∧ ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A) ∨
    (∀ Δ S, ∃ b₂ ∈ A, ∃ b₃ ∈ A, S ≤ b₂ ∧ b₂ < b₃ ∧
      Δ < b₃ - b₂ ∧ ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
        IsPairSupportTransversal A s (insert b₃ Q)) := by
  classical
  set C : ℕ → ℕ → Prop := fun d S => 1 ≤ d ∧
    ∃ b₂, b₂ ∈ A ∧ S ≤ b₂ ∧ b₂ + d ∈ A ∧
    ∃ s, s + b₂ = n + (b₂ + d) ∧ N₀ ≤ s ∧
      IsPairSupportTransversal A s (insert (b₂ + d) Q) with hCdef
  have hanti : ∀ d S S', S ≤ S' → C d S' → C d S := by
    intro d S S' hSS h
    obtain ⟨hd, b₂, hb₂A, hb₂S, hb₃A, rest⟩ := h
    exact ⟨hd, b₂, hb₂A, by omega, hb₃A, rest⟩
  have hex : ∀ S, ∃ d, C d S := by
    intro S
    obtain ⟨b₂, hb₂A, b₃, hb₃A, hS, hlt, sc, hsc, hsN, hhub⟩ :=
      hcorner S
    refine ⟨b₃ - b₂, by omega, b₂, hb₂A, hS, ?_, sc, by omega,
      hsN, ?_⟩
    · have h1 : b₂ + (b₃ - b₂) = b₃ := by omega
      rw [h1]
      exact hb₃A
    · have h1 : b₂ + (b₃ - b₂) = b₃ := by omega
      rw [h1]
      exact hhub
  rcases nat_param_stabilize hanti hex with ⟨d, hd⟩ | hesc
  · left
    have hd1 : 1 ≤ d := (hd 0).1
    refine ⟨d, hd1, ?_⟩
    intro K
    induction K with
    | zero =>
      exact ⟨∅, le_refl 0, fun x hx =>
        absurd hx (Finset.notMem_empty x)⟩
    | succ K ih =>
      obtain ⟨V, hVc, hVm⟩ := ih
      obtain ⟨-, b₂, hb₂A, hb₂S, hb₃A, -⟩ :=
        hd (V.sup id + 1)
      have hb₂V : b₂ ∉ V := by
        intro hmem
        have h1 : b₂ ≤ V.sup id := Finset.le_sup (f := id) hmem
        omega
      refine ⟨insert b₂ V, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hb₂V]
        omega
      · intro x hx
        rcases Finset.mem_insert.1 hx with h | h
        · subst h
          exact ⟨hb₂A, hb₃A⟩
        · exact hVm x h
  · right
    intro Δ S
    obtain ⟨d, hΔd, hd1, b₂, hb₂A, hb₂S, hb₃A, sc, hsc, hsN,
      hhub⟩ := hesc Δ S
    refine ⟨b₂, hb₂A, b₂ + d, hb₃A, hb₂S, by omega, by omega,
      sc, by omega, hsN, hhub⟩

theorem counterexample_four_cases {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ Q : Finset ℕ, RepFree A N₀ Q ∧
    ((∃ δ, 1 ≤ δ ∧ ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A) ∨
     (∀ Δ K, ∃ δ, Δ < δ ∧ ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A) ∨
     (∃ K₀, ∀ N S, ∃ n, N < n ∧
        (∃ V : Finset ℕ, K₀ ≤ V.card ∧
          ∀ a ∈ V, a ∈ A ∧ ∃ x ∈ A, x + a = n) ∧
        ∃ b₂ ∈ A, ∃ b₃ ∈ A, S ≤ b₂ ∧ b₂ < b₃ ∧
          ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
            IsPairSupportTransversal A s (insert b₃ Q)) ∨
     (∃ n, ∀ Δ S, ∃ b₂ ∈ A, ∃ b₃ ∈ A, S ≤ b₂ ∧ b₂ < b₃ ∧
        Δ < b₃ - b₂ ∧ ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
          IsPairSupportTransversal A s (insert b₃ Q))) := by
  classical
  have hfree0 : RepFree A N₀ ∅ := by
    intro m hm
    obtain ⟨x, hx, y, hy, hxy⟩ := hcov m hm
    exact ⟨x, hx, y, hy, 0, h0, by omega, Finset.notMem_empty x,
      Finset.notMem_empty y, Finset.notMem_empty 0⟩
  obtain ⟨Q, hQfree, hdich⟩ :=
    target_sequence_dichotomy_uniform h0 hcov hfail
  by_cases hdiff : ∀ K, ∃ δ, 1 ≤ δ ∧ ∃ V : Finset ℕ,
      K ≤ V.card ∧ ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A
  · rcases fixed_offset_or_growing hdiff with h | h
    · exact ⟨∅, hfree0, Or.inl h⟩
    · exact ⟨∅, hfree0, Or.inr (Or.inl h)⟩
  · push Not at hdiff
    obtain ⟨K₀, hK₀⟩ := hdiff
    have hcorner : ∀ S, ∃ n,
        (∃ V : Finset ℕ, K₀ ≤ V.card ∧
          ∀ a ∈ V, a ∈ A ∧ ∃ x ∈ A, x + a = n) ∧
        ∃ b₂, b₂ ∈ A ∧ ∃ b₃, b₃ ∈ A ∧ S ≤ b₂ ∧ b₂ < b₃ ∧
          ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
            IsPairSupportTransversal A s (insert b₃ Q) := by
      intro S
      rcases hdich K₀ S with h | h
      · exfalso
        obtain ⟨δ, hδ, V, hV, hVmem⟩ := h
        obtain ⟨x, hxV, hximp⟩ := hK₀ δ hδ V hV
        obtain ⟨hxA, hxδ⟩ := hVmem x hxV
        exact hximp hxA hxδ
      · obtain ⟨n, hblown, b₂, hb₂A, b₃, hb₃A, rest⟩ := h
        exact ⟨n, hblown, b₂, hb₂A, b₃, hb₃A, rest⟩
    have hanti : ∀ n S S', S ≤ S' →
        ((∃ V : Finset ℕ, K₀ ≤ V.card ∧
          ∀ a ∈ V, a ∈ A ∧ ∃ x ∈ A, x + a = n) ∧
        ∃ b₂, b₂ ∈ A ∧ ∃ b₃, b₃ ∈ A ∧ S' ≤ b₂ ∧ b₂ < b₃ ∧
          ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
            IsPairSupportTransversal A s (insert b₃ Q)) →
        ((∃ V : Finset ℕ, K₀ ≤ V.card ∧
          ∀ a ∈ V, a ∈ A ∧ ∃ x ∈ A, x + a = n) ∧
        ∃ b₂, b₂ ∈ A ∧ ∃ b₃, b₃ ∈ A ∧ S ≤ b₂ ∧ b₂ < b₃ ∧
          ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
            IsPairSupportTransversal A s (insert b₃ Q)) := by
      intro n S S' hSS h
      obtain ⟨hb, b₂, hb₂A, b₃, hb₃A, hS, rest⟩ := h
      exact ⟨hb, b₂, hb₂A, b₃, hb₃A, by omega, rest⟩
    rcases nat_param_stabilize hanti hcorner with ⟨n, hn⟩ | hesc
    · -- fixed hall: extract the difference sequence
      have hhall : ∀ S, ∃ b₂ ∈ A, ∃ b₃ ∈ A, S ≤ b₂ ∧ b₂ < b₃ ∧
          ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
            IsPairSupportTransversal A s (insert b₃ Q) := by
        intro S
        obtain ⟨-, b₂, hb₂A, b₃, hb₃A, hS, rest⟩ := hn S
        exact ⟨b₂, hb₂A, b₃, hb₃A, hS, rest⟩
      rcases fixed_hall_extracts_difference hhall with h | h
      · exact ⟨Q, hQfree, Or.inl h⟩
      · exact ⟨Q, hQfree, Or.inr (Or.inr (Or.inr ⟨n, h⟩))⟩
    · refine ⟨Q, hQfree, Or.inr (Or.inr (Or.inl
        ⟨K₀, fun N S => ?_⟩))⟩
      obtain ⟨n, hNn, hblown, b₂, hb₂A, b₃, hb₃A, rest⟩ :=
        hesc N S
      exact ⟨n, hNn, hblown, b₂, hb₂A, b₃, hb₃A, rest⟩

/-! ## Mining the target sequence sequence -/

theorem target_sequence_pure {A : Set ℕ} {N₀ : ℕ}
    {Q : Finset ℕ} {n : ℕ}
    (hcov : PairCovers A N₀)
    (hladder : ∀ Δ S, ∃ b₂ ∈ A, ∃ b₃ ∈ A, S ≤ b₂ ∧ b₂ < b₃ ∧
      Δ < b₃ - b₂ ∧ ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
        IsPairSupportTransversal A s (insert b₃ Q)) :
    ∀ Δ, ∃ d, Δ < d ∧ N₀ ≤ n + d ∧
      IsPairSupportTransversal A (n + d) Q ∧
      (∃ b ∈ A, b + d ∈ A) ∧
      (∃ q ∈ Q, ∃ a ∈ A, q + a = n + d) := by
  intro Δ
  obtain ⟨b₂, hb₂A, b₃, hb₃A, hS, hlt, hΔ, s, hs, hsN, hhub⟩ :=
    hladder Δ (n + 1)
  set d := b₃ - b₂ with hd
  have hsd : s = n + d := by omega
  have hsb₃ : s < b₃ := by omega
  have hpure : IsPairSupportTransversal A (n + d) Q := by
    rw [← hsd]
    intro x hx y hy hxy
    rcases hhub x hx y hy hxy with h | h
    · rcases Finset.mem_insert.1 h with h' | h'
      · omega
      · exact Or.inl h'
    · rcases Finset.mem_insert.1 h with h' | h'
      · omega
      · exact Or.inr h'
  have hshadow : ∃ q ∈ Q, ∃ a ∈ A, q + a = n + d := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hcov (n + d) (by omega)
    rcases hpure x hx y hy hxy with h | h
    · exact ⟨x, h, y, hy, by omega⟩
    · exact ⟨y, h, x, hx, by omega⟩
  exact ⟨d, hΔ, by omega, hpure, ⟨b₂, hb₂A, by
    have h1 : b₂ + d = b₃ := by omega
    rw [h1]
    exact hb₃A⟩, hshadow⟩

theorem sequence_shadow_concentrates {A : Set ℕ} {N₀ : ℕ}
    {Q : Finset ℕ} {n : ℕ}
    (hladder : ∀ Δ, ∃ d, Δ < d ∧ N₀ ≤ n + d ∧
      IsPairSupportTransversal A (n + d) Q ∧ (∃ b ∈ A, b + d ∈ A) ∧
      (∃ q ∈ Q, ∃ a ∈ A, q + a = n + d)) :
    ∃ q ∈ Q, ∀ Δ, ∃ d, Δ < d ∧ N₀ ≤ n + d ∧
      IsPairSupportTransversal A (n + d) Q ∧ (∃ b ∈ A, b + d ∈ A) ∧
      (∃ a ∈ A, q + a = n + d) := by
  classical
  by_contra hno
  push Not at hno
  have hDf : ∀ q, ∃ Δq, q ∈ Q → ∀ d, Δq < d → N₀ ≤ n + d →
      IsPairSupportTransversal A (n + d) Q → (∃ b ∈ A, b + d ∈ A) →
      ∀ a ∈ A, q + a ≠ n + d := by
    intro q
    by_cases hq : q ∈ Q
    · obtain ⟨Δq, hΔq⟩ := hno q hq
      exact ⟨Δq, fun _ => hΔq⟩
    · exact ⟨0, fun h => absurd h hq⟩
  choose Δf hΔf using hDf
  obtain ⟨d, hd, hN, hhub, hbp, q₀, hq₀Q, a₀, ha₀A, ha₀⟩ :=
    hladder (Q.sup Δf)
  have hsup : Δf q₀ ≤ Q.sup Δf := Finset.le_sup hq₀Q
  exact hΔf q₀ hq₀Q d (by omega) hN hhub hbp a₀ ha₀A ha₀

theorem sequence_difference_exclusion_interval {A : Set ℕ} {Q : Finset ℕ}
    {q n d d' a : ℕ}
    (ha : q + a = n + d) (haA : a ∈ A) (haQ : a ∉ Q)
    (hhub' : IsPairSupportTransversal A (n + d') Q) (hdd : d ≤ d')
    (hy : q + (d' - d) ∈ A) :
    q + (d' - d) ∈ Q := by
  have hpair : a + (q + (d' - d)) = n + d' := by omega
  rcases hhub' a haA _ hy hpair with h | h
  · exact absurd h haQ
  · exact h

theorem translation_case_pair_transversals {A : Set ℕ} {N₀ δ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hR1 : ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A) :
    ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      IsRepSupportTransversal A n H ∧ (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
      2 ≤ H.card ∧ ∀ h ∈ H, h ∈ A ∧ h + δ ∈ A ∧ 0 < h := by
  classical
  set B : Set ℕ := {x | x ∈ A ∧ x + δ ∈ A ∧ 0 < x} with hB
  haveI : DecidablePred (· ∈ B) := Classical.decPred _
  have hBA : B ⊆ A := fun x hx => hx.1
  have h0B : 0 ∉ B := fun hx => by
    have := hx.2.2
    omega
  have hBinf : B.Infinite := by
    intro hfin
    obtain ⟨V, hVc, hVm⟩ := hR1 (hfin.toFinset.card + 2)
    have hsub : V ⊆ insert 0 hfin.toFinset := by
      intro x hx
      rcases Nat.eq_zero_or_pos x with h | h
      · subst h
        exact Finset.mem_insert_self 0 _
      · refine Finset.mem_insert_of_mem ?_
        rw [Set.Finite.mem_toFinset]
        exact ⟨(hVm x hx).1, (hVm x hx).2, h⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le 0 hfin.toFinset
    omega
  intro N
  obtain ⟨n, hn, H, hhub, hmin, hcard, hmem⟩ :=
    minimalSupportTransversals_from_infiniteDeletion h0 hcov hanchor hfail
      hBA hBinf h0B N
  refine ⟨n, hn, H, hhub, hmin, hcard, ?_⟩
  intro h hh
  have := hmem h hh
  exact ⟨this.1, this.2.1, this.2.2⟩

/-! ## The classical-minimality interface -/

theorem essential_private_pair_stream {A : Set ℕ} {N₀ : ℕ}
    {b : ℕ} (hcov : PairCovers A N₀)
    (hess : ¬∃ N₁, ∀ n, N₁ ≤ n → ∃ x ∈ A, ∃ y ∈ A,
      x ≠ b ∧ y ≠ b ∧ x + y = n) :
    ∀ N, ∃ m, N ≤ m ∧ ∃ c ∈ A, b + c = m ∧
      ∀ x ∈ A, ∀ y ∈ A, x + y = m →
        (x = b ∧ y = c) ∨ (x = c ∧ y = b) := by
  push Not at hess
  intro N
  obtain ⟨m, hm, hall⟩ := hess (N + N₀)
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := hcov m (by omega)
  have hb₀ : x₀ = b ∨ y₀ = b := by
    by_contra hno
    push Not at hno
    exact hall x₀ hx₀ y₀ hy₀ hno.1 hno.2 hxy₀
  have hc : ∃ c ∈ A, b + c = m := by
    rcases hb₀ with h | h
    · exact ⟨y₀, hy₀, by omega⟩
    · exact ⟨x₀, hx₀, by omega⟩
  obtain ⟨c, hcA, hbc⟩ := hc
  refine ⟨m, by omega, c, hcA, hbc, ?_⟩
  intro x hx y hy hxy
  have hbxy : x = b ∨ y = b := by
    by_contra hno
    push Not at hno
    exact hall x hx y hy hno.1 hno.2 hxy
  rcases hbxy with h | h
  · exact Or.inl ⟨h, by omega⟩
  · exact Or.inr ⟨by omega, h⟩

/-- Two distinct essential elements share a private target only
at their mutual sum: the unique pair must be {b, b'}. -/
theorem shared_private_target_is_sum {A : Set ℕ} {b b' m c c' : ℕ}
    (hne : b ≠ b') (hb'A : b' ∈ A) (hcA : c ∈ A) (hbc : b + c = m)
    (hc'A : c' ∈ A) (hbc' : b' + c' = m)
    (huniq : ∀ x ∈ A, ∀ y ∈ A, x + y = m →
      (x = b ∧ y = c) ∨ (x = c ∧ y = b)) :
    m = b + b' := by
  rcases huniq b' hb'A c' hc'A hbc' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd h1 (Ne.symm hne)
  · omega

theorem disjoint_unique_pairs_of_essential {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hess : ∀ a ∈ A, 0 < a → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ≠ a ∧ y ≠ a ∧ x + y = n) :
    ∀ K, ∃ f : Fin K → ℕ × ℕ,
      (∀ i, (f i).1 ∈ A ∧ (f i).2 ∈ A ∧
        ∀ x ∈ A, ∀ y ∈ A, x + y = (f i).1 + (f i).2 →
          (x = (f i).1 ∧ y = (f i).2) ∨
          (x = (f i).2 ∧ y = (f i).1)) ∧
      (∀ i j, i < j → (f i).1 < (f j).1 ∧ (f i).1 < (f j).2 ∧
        (f i).2 < (f j).1 ∧ (f i).2 < (f j).2) := by
  classical
  intro K
  induction K with
  | zero =>
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ K ih =>
    obtain ⟨f, hf₁, hf₂⟩ := ih
    -- height of everything used so far
    set M := (Finset.univ : Finset (Fin K)).sup
      (fun i => max (f i).1 (f i).2) with hM
    -- a fresh positive basis element above M
    obtain ⟨b, hbA, hbge⟩ := pairCovers_unbounded hcov (M + 1)
    have hbpos : 0 < b := by omega
    -- its private stream, high above everything
    obtain ⟨m, hm, c, hcA, hbc, huniq⟩ :=
      essential_private_pair_stream hcov (hess b hbA hbpos)
        (2 * b + M + N₀ + 1)
    have hcM : M < c := by omega
    refine ⟨fun i => if h : (i : ℕ) < K then
      f ⟨i, h⟩ else (b, c), ?_, ?_⟩
    · intro i
      by_cases h : (i : ℕ) < K
      · simp only [dif_pos h]
        exact hf₁ ⟨i, h⟩
      · simp only [dif_neg h]
        exact ⟨hbA, hcA, fun x hx y hy hxy =>
          huniq x hx y hy (by omega)⟩
    · intro i j hij
      have hjK : (j : ℕ) < K + 1 := j.isLt
      by_cases hi : (i : ℕ) < K
      · by_cases hj : (j : ℕ) < K
        · simp only [dif_pos hi, dif_pos hj]
          exact hf₂ ⟨i, hi⟩ ⟨j, hj⟩ (by
            rw [Fin.mk_lt_mk]
            exact hij)
        · simp only [dif_pos hi, dif_neg hj]
          have h1 : max (f ⟨i, hi⟩).1 (f ⟨i, hi⟩).2 ≤ M := by
            rw [hM]
            exact Finset.le_sup
              (f := fun k => max (f k).1 (f k).2)
              (Finset.mem_univ (⟨i, hi⟩ : Fin K))
          have h2 : (f ⟨i, hi⟩).1 ≤ M := by omega
          have h3 : (f ⟨i, hi⟩).2 ≤ M := by omega
          exact ⟨by omega, by omega, by omega, by omega⟩
      · exfalso
        have hiK : (i : ℕ) < K + 1 := i.isLt
        have : (j : ℕ) < K + 1 := j.isLt
        have hij' : (i : ℕ) < (j : ℕ) := hij
        omega

theorem unique_pair_graph_infinite_degree {A : Set ℕ} {N₀ : ℕ}
    {b : ℕ} (hcov : PairCovers A N₀)
    (hess : ¬∃ N₁, ∀ n, N₁ ≤ n → ∃ x ∈ A, ∃ y ∈ A,
      x ≠ b ∧ y ≠ b ∧ x + y = n) :
    ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ c ∈ V, c ∈ A ∧
        ∀ x ∈ A, ∀ y ∈ A, x + y = b + c →
          (x = b ∧ y = c) ∨ (x = c ∧ y = b) := by
  classical
  intro K
  induction K with
  | zero =>
    exact ⟨∅, le_refl 0, fun c hc =>
      absurd hc (Finset.notMem_empty c)⟩
  | succ K ih =>
    obtain ⟨V, hVc, hVm⟩ := ih
    obtain ⟨m, hm, c, hcA, hbc, huniq⟩ :=
      essential_private_pair_stream hcov hess
        (b + V.sup id + 1)
    have hcV : c ∉ V := by
      intro hmem
      have h1 : c ≤ V.sup id := Finset.le_sup (f := id) hmem
      omega
    refine ⟨insert c V, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hcV]
      omega
    · intro c' hc'
      rcases Finset.mem_insert.1 hc' with h | h
      · subst h
        exact ⟨hcA, fun x hx y hy hxy =>
          huniq x hx y hy (by omega)⟩
      · exact hVm c' h

theorem matched_deletion_pair_transversals {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hess : ∀ a ∈ A, 0 < a → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ≠ a ∧ y ≠ a ∧ x + y = n) :
    ∃ P : ℕ → ℕ × ℕ,
      (∀ i, (P i).1 ∈ A ∧ (P i).2 ∈ A ∧ 0 < (P i).1 ∧
        0 < (P i).2 ∧
        ∀ x ∈ A, ∀ y ∈ A, x + y = (P i).1 + (P i).2 →
          (x = (P i).1 ∧ y = (P i).2) ∨
          (x = (P i).2 ∧ y = (P i).1)) ∧
      (∀ i, max (P i).1 (P i).2 < min (P (i + 1)).1
        (P (i + 1)).2) ∧
      ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
        IsRepSupportTransversal A n H ∧ (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
        2 ≤ H.card ∧ ∀ h ∈ H, ∃ i,
          h = (P i).1 ∨ h = (P i).2 := by
  classical
  have hstep : ∀ M : ℕ, ∃ b c : ℕ, b ∈ A ∧ c ∈ A ∧ M < b ∧
      M < c ∧ ∀ x ∈ A, ∀ y ∈ A, x + y = b + c →
        (x = b ∧ y = c) ∨ (x = c ∧ y = b) := by
    intro M
    obtain ⟨b, hbA, hbge⟩ := pairCovers_unbounded hcov (M + 1)
    have hbpos : 0 < b := by omega
    obtain ⟨m, hm, c, hcA, hbc, huniq⟩ :=
      essential_private_pair_stream hcov (hess b hbA hbpos)
        (b + M + N₀ + 1)
    exact ⟨b, c, hbA, hcA, by omega, by omega,
      fun x hx y hy hxy => huniq x hx y hy (by omega)⟩
  choose fb fc hfbA hfcA hfbM hfcM hfuniq using hstep
  obtain ⟨g, hg0, hgs⟩ : ∃ g : ℕ → ℕ × ℕ,
      g 0 = (fb 0, fc 0) ∧
      ∀ i, g (i + 1) =
        (fb (max (g i).1 (g i).2), fc (max (g i).1 (g i).2)) :=
    ⟨fun i => Nat.rec (fb 0, fc 0)
      (fun _ p => (fb (max p.1 p.2), fc (max p.1 p.2))) i,
      rfl, fun _ => rfl⟩
  have hgood : ∀ i, (g i).1 ∈ A ∧ (g i).2 ∈ A ∧ 0 < (g i).1 ∧
      0 < (g i).2 ∧
      ∀ x ∈ A, ∀ y ∈ A, x + y = (g i).1 + (g i).2 →
        (x = (g i).1 ∧ y = (g i).2) ∨
        (x = (g i).2 ∧ y = (g i).1) := by
    intro i
    cases i with
    | zero =>
      rw [hg0]
      exact ⟨hfbA 0, hfcA 0, hfbM 0, hfcM 0, hfuniq 0⟩
    | succ i =>
      rw [hgs]
      refine ⟨hfbA _, hfcA _, ?_, ?_, hfuniq _⟩
      · have := hfbM (max (g i).1 (g i).2)
        omega
      · have := hfcM (max (g i).1 (g i).2)
        omega
  have hinc : ∀ i, max (g i).1 (g i).2 <
      min (g (i + 1)).1 (g (i + 1)).2 := by
    intro i
    rw [hgs]
    have h1 := hfbM (max (g i).1 (g i).2)
    have h2 := hfcM (max (g i).1 (g i).2)
    simp only [lt_min_iff]
    constructor
    · exact h1
    · exact h2
  set B : Set ℕ := {x | ∃ i, x = (g i).1 ∨ x = (g i).2} with hB
  haveI : DecidablePred (· ∈ B) := Classical.decPred _
  have hBA : B ⊆ A := by
    rintro x ⟨i, h | h⟩
    · rw [h]
      exact (hgood i).1
    · rw [h]
      exact (hgood i).2.1
  have h0B : 0 ∉ B := by
    rintro ⟨i, h | h⟩
    · have := (hgood i).2.2.1
      omega
    · have := (hgood i).2.2.2.1
      omega
  have hmono : ∀ i j, i < j → (g i).1 < (g j).1 := by
    intro i j hij
    induction j with
    | zero => omega
    | succ j ihj =>
      have h1 := hinc j
      have h3 : (g j).1 ≤ max (g j).1 (g j).2 :=
        le_max_left _ _
      have h4 : min (g (j+1)).1 (g (j+1)).2 ≤ (g (j+1)).1 :=
        min_le_left _ _
      rw [lt_min_iff] at h1
      rcases Nat.lt_or_ge i j with h | h
      · have h2 := ihj h
        omega
      · have hij' : i = j := by omega
        subst hij'
        omega
  have hBinf : B.Infinite := by
    have hinj : Function.Injective (fun i => (g i).1) := by
      intro i j hij
      by_contra hne
      simp only at hij
      rcases Nat.lt_or_ge i j with h | h
      · have := hmono i j h
        omega
      · have h' : j < i := by omega
        have := hmono j i h'
        omega
    have hsub : Set.range (fun i => (g i).1) ⊆ B := by
      rintro x ⟨i, rfl⟩
      exact ⟨i, Or.inl rfl⟩
    exact Set.Infinite.mono hsub
      (Set.infinite_range_of_injective hinj)
  refine ⟨g, hgood, hinc, ?_⟩
  intro N
  obtain ⟨n, hn, H, hhub, hminH, hcard, hmem⟩ :=
    minimalSupportTransversals_from_infiniteDeletion h0 hcov hanchor hfail
      hBA hBinf h0B N
  refine ⟨n, hn, H, hhub, hminH, hcard, ?_⟩
  intro h hh
  exact hmem h hh

theorem hmin_of_essential {A : Set ℕ}
    (hess : ∀ a ∈ A, 0 < a → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ≠ a ∧ y ≠ a ∧ x + y = n) :
    ∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n := by
  intro B hBA hBinf ⟨N₁, hN₁⟩
  obtain ⟨b, hbB, hbpos⟩ : ∃ b ∈ B, 0 < b := by
    obtain ⟨b, hb⟩ :=
      (hBinf.diff (Set.finite_singleton 0)).nonempty
    rw [Set.mem_diff, Set.mem_singleton_iff] at hb
    refine ⟨b, hb.1, ?_⟩
    have := hb.2
    omega
  refine hess b (hBA hbB) hbpos ⟨N₁, fun n hn => ?_⟩
  obtain ⟨x, hx, y, hy, hxB, hyB, hxy⟩ := hN₁ n hn
  exact ⟨x, hx, y, hy, fun h => hxB (h ▸ hbB),
    fun h => hyB (h ▸ hbB), hxy⟩

/-! ## The Ramsey iteration -/

theorem unique_sum_ramsey {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ (∀ i, g i ∈ A) ∧
      (∀ i, 0 < g i) ∧
      ((∀ i j, i < j → ∀ x ∈ A, ∀ y ∈ A, x + y = g i + g j →
          (x = g i ∧ y = g j) ∨ (x = g j ∧ y = g i)) ∨
       (∀ i j, i < j →
          ¬(∀ x ∈ A, ∀ y ∈ A, x + y = g i + g j →
            (x = g i ∧ y = g j) ∨ (x = g j ∧ y = g i)))) := by
  classical
  -- ascending enumeration inside A
  have hstep : ∀ x : ℕ, ∃ a, a ∈ A ∧ x < a := by
    intro x
    obtain ⟨a, haA, hage⟩ := pairCovers_unbounded hcov (x + 1)
    exact ⟨a, haA, by omega⟩
  choose F hFA hFgt using hstep
  obtain ⟨e, he0, hes⟩ : ∃ e : ℕ → ℕ, e 0 = F 0 ∧
      ∀ i, e (i + 1) = F (e i) :=
    ⟨fun i => Nat.rec (F 0) (fun _ p => F p) i, rfl, fun _ => rfl⟩
  have heA : ∀ i, e i ∈ A := by
    intro i
    cases i with
    | zero => rw [he0]; exact hFA 0
    | succ i => rw [hes]; exact hFA (e i)
  have hemono : StrictMono e := by
    apply strictMono_nat_of_lt_succ
    intro i
    rw [hes]
    exact hFgt (e i)
  -- colour and apply Ramsey
  set c : ℕ → ℕ → Bool := fun i j =>
    decide (∀ x ∈ A, ∀ y ∈ A, x + y = e i + e j →
      (x = e i ∧ y = e j) ∨ (x = e j ∧ y = e i)) with hc
  have hepos : ∀ i, 0 < e i := by
    intro i
    have h1 : e 0 ≤ e i := hemono.le_iff_le.2 (Nat.zero_le i)
    have h2 : 0 < e 0 := by
      rw [he0]
      exact lt_of_le_of_lt (Nat.zero_le 0) (hFgt 0)
    omega
  obtain ⟨f, hfmono, b, hfb⟩ := infinite_ramsey_pairs c
  refine ⟨fun i => e (f i), hemono.comp hfmono, fun i => heA _,
    fun i => hepos _, ?_⟩
  cases b with
  | true =>
    left
    intro i j hij
    have h1 := hfb i j hij
    rw [hc] at h1
    simpa using of_decide_eq_true h1
  | false =>
    right
    intro i j hij
    have h1 := hfb i j hij
    rw [hc] at h1
    have h2 := of_decide_eq_false h1
    simpa using h2

/-- All-unique branch, support transversal form: each pairwise sum is a
two-element pair support transversal — a 2-parameter family of maximally fragile
targets, far denser than the one-parameter target sequence sequence. -/
theorem all_unique_pair_support_transversals {A : Set ℕ} {g : ℕ → ℕ}
    (huniq : ∀ i j, i < j → ∀ x ∈ A, ∀ y ∈ A,
      x + y = g i + g j →
      (x = g i ∧ y = g j) ∨ (x = g j ∧ y = g i)) :
    ∀ i j, i < j →
      IsPairSupportTransversal A (g i + g j) ({g i, g j} : Finset ℕ) := by
  intro i j hij x hx y hy hxy
  rcases huniq i j hij x hx y hy hxy with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact Or.inl (by simp [h1])
  · exact Or.inl (by simp [h1])

/-- All-unique branch is Sidon: distinct index pairs give
distinct sums, since a coincidence would hand one sum two
decompositions and uniqueness forbids it. -/
theorem all_unique_is_sidon {A : Set ℕ} {g : ℕ → ℕ}
    (hmono : StrictMono g) (hgA : ∀ i, g i ∈ A)
    (huniq : ∀ i j, i < j → ∀ x ∈ A, ∀ y ∈ A,
      x + y = g i + g j →
      (x = g i ∧ y = g j) ∨ (x = g j ∧ y = g i)) :
    ∀ i j k l, i < j → k < l →
      g i + g j = g k + g l → i = k ∧ j = l := by
  intro i j k l hij hkl heq
  have h1 := huniq i j hij (g k) (hgA k) (g l) (hgA l) heq.symm
  rcases h1 with ⟨h2, h3⟩ | ⟨h2, h3⟩
  · exact ⟨(hmono.injective h2).symm, (hmono.injective h3).symm⟩
  · have hik : k = j := hmono.injective h2
    have hjl : l = i := hmono.injective h3
    omega

theorem clique_or_independent_pair_transversals {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ (∀ i, g i ∈ A) ∧
      ((∀ i j, i < j →
          ¬(∀ x ∈ A, ∀ y ∈ A, x + y = g i + g j →
            (x = g i ∧ y = g j) ∨ (x = g j ∧ y = g i))) ∨
       ((∀ i j, i < j →
          IsPairSupportTransversal A (g i + g j) ({g i, g j} : Finset ℕ)) ∧
        ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
          IsRepSupportTransversal A n H ∧ (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
          2 ≤ H.card ∧ ∀ h ∈ H, ∃ i, h = g i)) := by
  classical
  obtain ⟨g, hgmono, hgA, hgpos, hbranch⟩ :=
    unique_sum_ramsey hcov
  refine ⟨g, hgmono, hgA, ?_⟩
  rcases hbranch with huniq | hindep
  · right
    refine ⟨all_unique_pair_support_transversals huniq, ?_⟩
    set B : Set ℕ := Set.range g with hB
    haveI : DecidablePred (· ∈ B) := Classical.decPred _
    have hBA : B ⊆ A := by
      rintro x ⟨i, rfl⟩
      exact hgA i
    have h0B : 0 ∉ B := by
      rintro ⟨i, hi⟩
      have := hgpos i
      omega
    have hBinf : B.Infinite :=
      Set.infinite_range_of_injective hgmono.injective
    intro N
    obtain ⟨n, hn, H, hhub, hminH, hcard, hmem⟩ :=
      minimalSupportTransversals_from_infiniteDeletion h0 hcov hanchor hfail
        hBA hBinf h0B N
    refine ⟨n, hn, H, hhub, hminH, hcard, ?_⟩
    intro h hh
    obtain ⟨i, hi⟩ := hmem h hh
    exact ⟨i, hi.symm⟩
  · exact Or.inl hindep

theorem independent_alternatives_ramsey {A : Set ℕ}
    (g : ℕ → ℕ) (hgmono : StrictMono g) (hgA : ∀ i, g i ∈ A)
    (hgpos : ∀ i, 0 < g i) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ((∀ i j, i < j → ∃ x ∈ A, ∃ y ∈ A,
          x ∉ Set.range g ∧ y ∉ Set.range g ∧
          x + y = g (f i) + g (f j)) ∨
       (∀ i j, i < j → ∀ x ∈ A, ∀ y ∈ A,
          x + y = g (f i) + g (f j) →
          x ∈ Set.range g ∨ y ∈ Set.range g)) := by
  classical
  set c : ℕ → ℕ → Bool := fun i j =>
    decide (∃ x ∈ A, ∃ y ∈ A, x ∉ Set.range g ∧
      y ∉ Set.range g ∧ x + y = g i + g j) with hc
  obtain ⟨f, hfmono, b, hfb⟩ := infinite_ramsey_pairs c
  refine ⟨f, hfmono, ?_⟩
  cases b with
  | true =>
    left
    intro i j hij
    have h1 := hfb i j hij
    rw [hc] at h1
    simpa using of_decide_eq_true h1
  | false =>
    right
    intro i j hij x hx y hy hxy
    have h1 := hfb i j hij
    rw [hc] at h1
    have h2 := of_decide_eq_false h1
    by_contra hno
    push Not at hno
    exact h2 (by
      exact ⟨x, hx, y, hy, hno.1, hno.2, hxy⟩)

theorem surviving_sum_square {A : Set ℕ} {g : ℕ → ℕ}
    (h0 : 0 ∈ A) (hgpos : ∀ i, 0 < g i) {f : ℕ → ℕ}
    (halt : ∀ i j, i < j → ∃ x ∈ A, ∃ y ∈ A,
      x ∉ Set.range g ∧ y ∉ Set.range g ∧
      x + y = g (f i) + g (f j)) :
    ∀ i j, i < j → ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
      x ∉ Set.range (g ∘ f) ∧ y ∉ Set.range (g ∘ f) ∧
      z ∉ Set.range (g ∘ f) ∧
      x + y + z = g (f i) + g (f j) := by
  intro i j hij
  obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := halt i j hij
  have hsub : ∀ w, w ∉ Set.range g → w ∉ Set.range (g ∘ f) := by
    intro w hw hmem
    obtain ⟨k, hk⟩ := hmem
    exact hw ⟨f k, hk⟩
  have h0r : (0 : ℕ) ∉ Set.range (g ∘ f) := by
    rintro ⟨k, hk⟩
    have := hgpos (f k)
    simp only [Function.comp] at hk
    omega
  exact ⟨x, hx, y, hy, 0, h0, hsub x hxr, hsub y hyr, h0r,
    by omega⟩

theorem ramsey_trichotomy_of_covering {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) :
    ∃ T : ℕ → ℕ, StrictMono T ∧ (∀ i, T i ∈ A) ∧
      (∀ i, 0 < T i) ∧
      ((∀ i j, i < j →
          IsPairSupportTransversal A (T i + T j) ({T i, T j} : Finset ℕ)) ∨
       (∀ i j, i < j → ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
          x ∉ Set.range T ∧ y ∉ Set.range T ∧
          z ∉ Set.range T ∧ x + y + z = T i + T j) ∨
       (∃ R : Set ℕ, (∀ w ∈ R, w ∈ A ∧ 0 < w) ∧
          (∀ i, T i ∈ R) ∧
          ∀ i j, i < j → ∀ x ∈ A, ∀ y ∈ A,
            x + y = T i + T j → x ∈ R ∨ y ∈ R)) := by
  classical
  obtain ⟨g, hgmono, hgA, hgpos, hbranch⟩ :=
    unique_sum_ramsey hcov
  rcases hbranch with huniq | hindep
  · exact ⟨g, hgmono, hgA, hgpos,
      Or.inl (all_unique_pair_support_transversals huniq)⟩
  · obtain ⟨f, hfmono, halt⟩ :=
      independent_alternatives_ramsey g hgmono hgA hgpos
    rcases halt with hyes | hno
    · refine ⟨g ∘ f, hgmono.comp hfmono, fun i => hgA _,
        fun i => hgpos _, Or.inr (Or.inl ?_)⟩
      exact surviving_sum_square h0 hgpos hyes
    · refine ⟨g ∘ f, hgmono.comp hfmono, fun i => hgA _,
        fun i => hgpos _, Or.inr (Or.inr
          ⟨Set.range g, ?_, ?_, ?_⟩)⟩
      · rintro w ⟨k, rfl⟩
        exact ⟨hgA k, hgpos k⟩
      · intro i
        exact ⟨f i, rfl⟩
      · intro i j hij x hx y hy hxy
        exact hno i j hij x hx y hy hxy

theorem cube_avoidance_ramsey {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀) :
    ∃ T : ℕ → ℕ, StrictMono T ∧ (∀ i, T i ∈ A) ∧
      (∀ i, 0 < T i) ∧
      ∃ R : Set ℕ, (∀ w ∈ R, w ∈ A ∧ 0 < w) ∧
        (∀ i, T i ∈ R) ∧
        ((∀ i j k, i < j → j < k →
            ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
            x ∉ R ∧ y ∉ R ∧ z ∉ R ∧
            x + y + z = T i + T j + T k) ∨
         (∀ i j k, i < j → j < k →
            ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
            x + y + z = T i + T j + T k →
            x ∈ R ∨ y ∈ R ∨ z ∈ R)) := by
  classical
  have hstep : ∀ x : ℕ, ∃ a, a ∈ A ∧ x < a := by
    intro x
    obtain ⟨a, haA, hage⟩ := pairCovers_unbounded hcov (x + 1)
    exact ⟨a, haA, by omega⟩
  choose F hFA hFgt using hstep
  obtain ⟨e, he0, hes⟩ : ∃ e : ℕ → ℕ, e 0 = F 0 ∧
      ∀ i, e (i + 1) = F (e i) :=
    ⟨fun i => Nat.rec (F 0) (fun _ p => F p) i, rfl, fun _ => rfl⟩
  have heA : ∀ i, e i ∈ A := by
    intro i
    cases i with
    | zero => rw [he0]; exact hFA 0
    | succ i => rw [hes]; exact hFA (e i)
  have hemono : StrictMono e := by
    apply strictMono_nat_of_lt_succ
    intro i
    rw [hes]
    exact hFgt (e i)
  have hepos : ∀ i, 0 < e i := by
    intro i
    have h1 : e 0 ≤ e i := hemono.le_iff_le.2 (Nat.zero_le i)
    have h2 : 0 < e 0 := by
      rw [he0]
      exact lt_of_le_of_lt (Nat.zero_le 0) (hFgt 0)
    omega
  set c : ℕ → ℕ → ℕ → Bool := fun i j k =>
    decide (∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
      x ∉ Set.range e ∧ y ∉ Set.range e ∧ z ∉ Set.range e ∧
      x + y + z = e i + e j + e k) with hc
  obtain ⟨f, hfmono, b, hfb⟩ := infinite_ramsey_triples c
  refine ⟨fun i => e (f i), hemono.comp hfmono,
    fun i => heA _, fun i => hepos _,
    Set.range e, ?_, fun i => ⟨f i, rfl⟩, ?_⟩
  · rintro w ⟨k, rfl⟩
    exact ⟨heA k, hepos k⟩
  cases b with
  | true =>
    left
    intro i j k hij hjk
    have h1 := hfb i j k hij hjk
    rw [hc] at h1
    simpa using of_decide_eq_true h1
  | false =>
    right
    intro i j k hij hjk x hx y hy z hz hxyz
    have h1 := hfb i j k hij hjk
    rw [hc] at h1
    have h2 := of_decide_eq_false h1
    by_contra hno
    push Not at hno
    exact h2 ⟨x, hx, y, hy, z, hz, hno.1, hno.2.1, hno.2.2,
      hxyz⟩

theorem survival_of_complete_avoiding {A : Set ℕ} {N₂ : ℕ}
    (T : Set ℕ)
    (hcomp : ∀ n, N₂ ≤ n → ∃ S : Finset ℕ,
      (↑S : Set ℕ) ⊆ T ∧ S.sum id = n)
    (havoid : ∀ S : Finset ℕ, (↑S : Set ℕ) ⊆ T →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ T ∧ y ∉ T ∧ z ∉ T ∧ x + y + z = S.sum id) :
    ∀ n, N₂ ≤ n → ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
      x ∉ T ∧ y ∉ T ∧ z ∉ T ∧ x + y + z = n := by
  intro n hn
  obtain ⟨S, hST, hsum⟩ := hcomp n hn
  obtain ⟨x, hx, y, hy, z, hz, hxT, hyT, hzT, hxyz⟩ :=
    havoid S hST
  exact ⟨x, hx, y, hy, z, hz, hxT, hyT, hzT, by omega⟩

/-! ## The omega restriction -/

theorem omega_avoidance_dichotomy {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀) :
    ∃ T : ℕ → ℕ, StrictMono T ∧ (∀ i, T i ∈ A) ∧
      (∀ i, 0 < T i) ∧
      ∃ R : Set ℕ, (∀ w ∈ R, w ∈ A ∧ 0 < w) ∧
        (∀ i, T i ∈ R) ∧
        ((∀ r : ℕ, ∀ k : Fin (r + 1) → ℕ, StrictMono k →
            (∀ i, r + 1 ≤ k i) →
            ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
              x ∉ R ∧ y ∉ R ∧ z ∉ R ∧
              x + y + z = ∑ i, T (k i)) ∨
         (∃ r : ℕ, ∀ k : Fin (r + 1) → ℕ, StrictMono k →
            (∀ i, r + 1 ≤ k i) →
            ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
              x + y + z = ∑ i, T (k i) →
              x ∈ R ∨ y ∈ R ∨ z ∈ R)) := by
  classical
  -- base enumeration
  have hstep0 : ∀ x : ℕ, ∃ a, a ∈ A ∧ x < a := by
    intro x
    obtain ⟨a, haA, hage⟩ := pairCovers_unbounded hcov (x + 1)
    exact ⟨a, haA, by omega⟩
  choose F0 hF0A hF0gt using hstep0
  obtain ⟨e, he0, hes⟩ : ∃ e : ℕ → ℕ, e 0 = F0 0 ∧
      ∀ i, e (i + 1) = F0 (e i) :=
    ⟨fun i => Nat.rec (F0 0) (fun _ p => F0 p) i, rfl,
      fun _ => rfl⟩
  have heA : ∀ i, e i ∈ A := by
    intro i
    cases i with
    | zero => rw [he0]; exact hF0A 0
    | succ i => rw [hes]; exact hF0A (e i)
  have hemono : StrictMono e := by
    apply strictMono_nat_of_lt_succ
    intro i
    rw [hes]
    exact hF0gt (e i)
  have hepos : ∀ i, 0 < e i := by
    intro i
    have h1 : e 0 ≤ e i := hemono.le_iff_le.2 (Nat.zero_le i)
    have h2 : 0 < e 0 := by
      rw [he0]
      exact lt_of_le_of_lt (Nat.zero_le 0) (hF0gt 0)
    omega
  -- the arity-r colouring pulled back through an index map
  set col : (ℕ → ℕ) → (r : ℕ) → (Fin (r + 1) → ℕ) → Bool :=
    fun φ r t => decide (∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
      x ∉ Set.range e ∧ y ∉ Set.range e ∧ z ∉ Set.range e ∧
      x + y + z = ∑ i, e (φ (t i))) with hcol
  have hstage : ∀ (φ : ℕ → ℕ) (r : ℕ),
      ∃ fb : (ℕ → ℕ) × Bool, StrictMono fb.1 ∧
        ∀ g : Fin (r + 1) → ℕ, StrictMono g →
          col φ r (fun i => fb.1 (g i)) = fb.2 := by
    intro φ r
    obtain ⟨f, hf, b, hb⟩ := infinite_ramsey_tuples r (col φ r)
    exact ⟨(f, b), hf, hb⟩
  choose FB hFBmono hFBhom using hstage
  obtain ⟨Φ, hΦ0, hΦs⟩ : ∃ Φ : ℕ → (ℕ → ℕ), Φ 0 = id ∧
      ∀ r, Φ (r + 1) = Φ r ∘ (FB (Φ r) r).1 :=
    ⟨fun r => Nat.rec id (fun r' φ => φ ∘ (FB φ r').1) r,
      rfl, fun _ => rfl⟩
  have hΦmono : ∀ r, StrictMono (Φ r) := by
    intro r
    induction r with
    | zero => rw [hΦ0]; exact strictMono_id
    | succ r ih =>
      rw [hΦs]
      exact ih.comp (hFBmono (Φ r) r)
  -- splitting later stages over earlier ones
  have hsplit : ∀ r m, r ≤ m → ∃ Ψ : ℕ → ℕ, StrictMono Ψ ∧
      ∀ x, Φ m x = Φ r (Ψ x) := by
    intro r m hrm
    induction m, hrm using Nat.le_induction with
    | base => exact ⟨id, strictMono_id, fun x => rfl⟩
    | succ m hrm ih =>
      obtain ⟨Ψ, hΨmono, hΨ⟩ := ih
      refine ⟨Ψ ∘ (FB (Φ m) m).1,
        hΨmono.comp (hFBmono (Φ m) m), ?_⟩
      intro x
      rw [hΦs]
      exact hΨ ((FB (Φ m) m).1 x)
  -- the diagonal
  set ψ : ℕ → ℕ := fun k => Φ k k with hψ
  have hψmono : StrictMono ψ := by
    apply strictMono_nat_of_lt_succ
    intro k
    have h1 : Φ (k + 1) (k + 1) =
        Φ k ((FB (Φ k) k).1 (k + 1)) := by
      rw [hΦs]
      rfl
    have h2 : k + 1 ≤ (FB (Φ k) k).1 (k + 1) :=
      (hFBmono (Φ k) k).le_apply
    have h3 : Φ k (k) < Φ k ((FB (Φ k) k).1 (k + 1)) :=
      (hΦmono k) (by omega)
    show Φ k k < Φ (k + 1) (k + 1)
    omega
  -- homogeneity transported to the diagonal tail
  have hdiag : ∀ r, ∀ k : Fin (r + 1) → ℕ, StrictMono k →
      (∀ i, r + 1 ≤ k i) →
      col id r (fun i => ψ (k i)) = (FB (Φ r) r).2 := by
    intro r k hkmono hkge
    -- write ψ (k i) = Φ (r+1) (w i) with w strictly monotone
    have hw : ∀ i : Fin (r + 1), ∃ wv, ψ (k i) = Φ (r + 1) wv := by
      intro i
      obtain ⟨Ψ, hΨmono, hΨ⟩ := hsplit (r + 1) (k i) (hkge i)
      exact ⟨Ψ (k i), by rw [hψ]; simp only; exact hΨ (k i)⟩
    choose w hwspec using hw
    have hwmono : StrictMono w := by
      intro i j hij
      have h1 : ψ (k i) < ψ (k j) := hψmono (hkmono hij)
      rw [hwspec i, hwspec j] at h1
      exact (hΦmono (r + 1)).lt_iff_lt.1 h1
    have h2 := hFBhom (Φ r) r w hwmono
    have h3 : ∀ i : Fin (r + 1),
        Φ r ((FB (Φ r) r).1 (w i)) = ψ (k i) := by
      intro i
      have h4 : Φ r ((FB (Φ r) r).1 (w i)) = Φ (r + 1) (w i) := by
        rw [hΦs]
        rfl
      rw [h4, ← hwspec i]
    have h5 : (∑ i, e (Φ r ((FB (Φ r) r).1 (w i)))) =
        ∑ i, e (ψ (k i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [h3 i]
    have h6 : col id r (fun i => ψ (k i)) =
        col (Φ r) r (fun i => (FB (Φ r) r).1 (w i)) := by
      simp only [hcol, id_eq]
      rw [← h5]
    rw [h6]
    exact h2
  refine ⟨fun k => e (ψ k), hemono.comp hψmono,
    fun k => heA _, fun k => hepos _,
    Set.range e, ?_, fun k => ⟨ψ k, rfl⟩, ?_⟩
  · rintro wv ⟨i, rfl⟩
    exact ⟨heA i, hepos i⟩
  by_cases hex : ∃ r, (FB (Φ r) r).2 = false
  · right
    obtain ⟨r, hr⟩ := hex
    refine ⟨r, fun k hkmono hkge x hx y hy z hz hxyz => ?_⟩
    have h1 := hdiag r k hkmono hkge
    rw [hr] at h1
    simp only [hcol, id_eq] at h1
    have h2 := of_decide_eq_false h1
    by_contra hno
    push Not at hno
    exact h2 ⟨x, hx, y, hy, z, hz, hno.1, hno.2.1, hno.2.2,
      hxyz⟩
  · left
    push Not at hex
    intro r k hkmono hkge
    have h1 := hdiag r k hkmono hkge
    have h2 : (FB (Φ r) r).2 = true := by
      have := hex r
      cases hb : (FB (Φ r) r).2
      · exact absurd hb this
      · rfl
    rw [h2] at h1
    simp only [hcol, id_eq] at h1
    simpa using of_decide_eq_true h1

theorem complete_families_blocked_of_hfail {A : Set ℕ}
    {N₀ : ℕ}
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (T : Set ℕ) (hTA : T ⊆ A) (hTinf : T.Infinite) {N₂ : ℕ}
    (hcomp : ∀ n, N₂ ≤ n → ∃ S : Finset ℕ,
      (↑S : Set ℕ) ⊆ T ∧ S.sum id = n) :
    ∀ N, ∃ S : Finset ℕ, (↑S : Set ℕ) ⊆ T ∧ N ≤ S.sum id ∧
      ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = S.sum id →
        x ∈ T ∨ y ∈ T ∨ z ∈ T := by
  intro N
  have hnb := hfail T hTA hTinf
  rw [IsExactTupleAsymptoticBasis] at hnb
  push Not at hnb
  obtain ⟨n, hn, hnofail⟩ := hnb (N + N₂)
  obtain ⟨S, hST, hsum⟩ := hcomp n (by omega)
  refine ⟨S, hST, by omega, ?_⟩
  intro x hx y hy z hz hxyz
  by_contra hno
  push Not at hno
  have hmemb : ∀ i : Fin 3, (![x, y, z] : Fin 3 → ℕ) i ∈ A \ T := by
    intro i
    match i with
    | 0 => exact ⟨hx, hno.1⟩
    | 1 => exact ⟨hy, hno.2.1⟩
    | 2 => exact ⟨hz, hno.2.2⟩
  have hsum3 : (∑ i, (![x, y, z] : Fin 3 → ℕ) i) = n := by
    rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    omega
  exact hnofail ![x, y, z] hmemb hsum3

theorem subset_sum_complete_of_small_gaps (t : ℕ → ℕ)
    (h1 : t 0 = 1)
    (hgap : ∀ k, t (k + 1) ≤
      (∑ i ∈ Finset.range (k + 1), t i) + 1) :
    ∀ K n, n ≤ ∑ i ∈ Finset.range (K + 1), t i →
      ∃ S ⊆ Finset.range (K + 1), (∑ i ∈ S, t i) = n := by
  intro K
  induction K with
  | zero =>
    intro n hn
    rw [Finset.sum_range_one, h1] at hn
    rcases Nat.eq_zero_or_pos n with h | h
    · exact ⟨∅, Finset.empty_subset _, by simp [h]⟩
    · have hn1 : n = 1 := by omega
      refine ⟨{0}, ?_, ?_⟩
      · intro x hx
        rw [Finset.mem_singleton] at hx
        rw [hx]
        exact Finset.mem_range.2 (by omega)
      · rw [Finset.sum_singleton, h1, hn1]
  | succ K ih =>
    intro n hn
    rw [Finset.sum_range_succ] at hn
    by_cases hle : n ≤ ∑ i ∈ Finset.range (K + 1), t i
    · obtain ⟨S, hS, hsum⟩ := ih n hle
      refine ⟨S, ?_, hsum⟩
      intro x hx
      have := hS hx
      rw [Finset.mem_range] at this ⊢
      omega
    · push Not at hle
      have hgap' := hgap K
      have hsub : n - t (K + 1) ≤
          ∑ i ∈ Finset.range (K + 1), t i := by omega
      obtain ⟨S, hS, hsum⟩ := ih (n - t (K + 1)) hsub
      have hnotmem : K + 1 ∉ S := by
        intro hmem
        have := hS hmem
        rw [Finset.mem_range] at this
        omega
      refine ⟨insert (K + 1) S, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.1 hx with h | h
        · rw [h]
          exact Finset.mem_range.2 (by omega)
        · have := hS h
          rw [Finset.mem_range] at this ⊢
          omega
      · rw [Finset.sum_insert hnotmem, hsum]
        omega

theorem subset_sum_complete_of_bootstrap (t : ℕ → ℕ)
    {B C₀ K₀ : ℕ} (hBC : B ≤ C₀)
    (hinit : ∀ n, B ≤ n → n ≤ C₀ → ∃ S : Finset ℕ,
      S ⊆ Finset.range (K₀ + 1) ∧ (∑ i ∈ S, t i) = n)
    (hgap : ∀ k, K₀ < k → t k ≤ C₀ - B + 1 +
      (∑ i ∈ Finset.Ico (K₀ + 1) k, t i)) :
    ∀ K, K₀ ≤ K → ∀ n, B ≤ n →
      n ≤ C₀ + (∑ i ∈ Finset.Ico (K₀ + 1) (K + 1), t i) →
      ∃ S : Finset ℕ, S ⊆ Finset.range (K + 1) ∧
        (∑ i ∈ S, t i) = n := by
  intro K
  induction K with
  | zero =>
    intro hK0 n hBn hn
    have h1 : K₀ = 0 := by omega
    subst h1
    have h2 : Finset.Ico 1 1 = (∅ : Finset ℕ) := by
      simp
    rw [h2, Finset.sum_empty] at hn
    exact hinit n hBn (by omega)
  | succ K ih =>
    intro hK0 n hBn hn
    rcases Nat.lt_or_ge K₀ (K + 1) with hlt | hge
    · -- K₀ ≤ K: the interval extends by t (K + 1)
      have hK0K : K₀ ≤ K := by omega
      have hsplit : (∑ i ∈ Finset.Ico (K₀ + 1) (K + 2), t i) =
          (∑ i ∈ Finset.Ico (K₀ + 1) (K + 1), t i) +
          t (K + 1) := by
        rw [Finset.sum_Ico_succ_top (by omega)]
      rw [hsplit] at hn
      set CK := C₀ + (∑ i ∈ Finset.Ico (K₀ + 1) (K + 1), t i)
        with hCK
      by_cases hle : n ≤ CK
      · obtain ⟨S, hS, hsum⟩ := ih hK0K n hBn (by omega)
        refine ⟨S, ?_, hsum⟩
        intro x hx
        have := hS hx
        rw [Finset.mem_range] at this ⊢
        omega
      · push Not at hle
        have hgap' := hgap (K + 1) (by omega)
        have hrange : B ≤ n - t (K + 1) ∧
            n - t (K + 1) ≤ CK := by
          constructor
          · omega
          · omega
        obtain ⟨S, hS, hsum⟩ := ih hK0K (n - t (K + 1))
          hrange.1 (by omega)
        have hnotmem : K + 1 ∉ S := by
          intro hmem
          have := hS hmem
          rw [Finset.mem_range] at this
          omega
        refine ⟨insert (K + 1) S, ?_, ?_⟩
        · intro x hx
          rcases Finset.mem_insert.1 hx with h | h
          · rw [h]
            exact Finset.mem_range.2 (by omega)
          · have := hS h
            rw [Finset.mem_range] at this ⊢
            omega
        · rw [Finset.sum_insert hnotmem, hsum]
          have ht : t (K + 1) ≤ n := by omega
          omega
    · -- K + 1 ≤ K₀: still inside the bootstrap window
      have h2 : Finset.Ico (K₀ + 1) (K + 2) = (∅ : Finset ℕ) := by
        apply Finset.Ico_eq_empty
        omega
      rw [h2, Finset.sum_empty] at hn
      obtain ⟨S, hS, hsum⟩ := hinit n hBn (by omega)
      refine ⟨S, ?_, hsum⟩
      intro x hx
      have := hS hx
      rw [Finset.mem_range] at this ⊢
      omega

theorem pair_support_transversal_corep_confined {A : Set ℕ} {s : ℕ}
    {H : Finset ℕ} (hhub : IsPairSupportTransversal A s H) {a a' : ℕ}
    (ha : a ∈ A) (haH : a ∉ H) (ha' : a' ∈ A)
    (hsum : a + a' = s) : a' ∈ H := by
  rcases hhub a ha a' ha' hsum with h | h
  · exact absurd h haH
  · exact h

/-! ## Nash-Williams: chaining the rank layer antichain -/

theorem rank_layer_higman_chain {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ Q : ℕ → Finset ℕ,
      (∀ k, (Q k).Nonempty) ∧
      (∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h) ∧
      (∀ k, RepFree A N₀ (Q k)) ∧
      (∀ j k, j < k → Disjoint (Q j) (Q k)) ∧
      (∀ k, ∀ b ∈ A, 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
        ∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m (insert b (Q k))) ∧
      ∃ σ : ℕ ↪o ℕ, ∀ m n, m ≤ n →
        List.SublistForall₂ (· ≤ ·)
          ((Q (σ m)).sort (· ≤ ·)) ((Q (σ n)).sort (· ≤ ·)) := by
  classical
  obtain ⟨Q, hne, hmem, hfree, hdisj, hguard⟩ :=
    absolute_rank_layer_stratification h0 hcov hanchor hfail
  haveI hwqo : WellQuasiOrderedLE ℕ :=
    wellQuasiOrderedLE_iff_wellFoundedLT.mpr inferInstance
  have hpwo : (Set.univ : Set ℕ).PartiallyWellOrderedOn
      (· ≤ ·) :=
    Set.isPWO_of_wellQuasiOrderedLE _
  haveI hrefl :
      Std.Refl (List.SublistForall₂ ((· ≤ ·) : ℕ → ℕ → Prop)) :=
    ⟨fun l => Std.Refl.refl l⟩
  haveI hpre : IsPreorder (List ℕ)
      (List.SublistForall₂ ((· ≤ ·) : ℕ → ℕ → Prop)) := ⟨⟩
  have hlists :=
    Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂
      (· ≤ ·) hpwo
  obtain ⟨σ, hσ⟩ := hlists.exists_monotone_subseq
    (f := fun k => (Q k).sort (· ≤ ·))
    (fun k x _ => Set.mem_univ x)
  exact ⟨Q, hne, hmem, hfree, hdisj, hguard, σ, hσ⟩

/-- Forall₂-membership transfer: each left element has a related
partner on the right. -/
theorem forall₂_mem_partner {r : ℕ → ℕ → Prop}
    {l₁ l₂ : List ℕ} (h : List.Forall₂ r l₁ l₂) :
    ∀ x ∈ l₁, ∃ y ∈ l₂, r x y := by
  induction h with
  | nil => intro x hx; exact absurd hx (List.not_mem_nil)
  | cons hr _ ih =>
    intro x hx
    rcases List.mem_cons.1 hx with h' | h'
    · subst h'
      exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨y, hy, hxy⟩ := ih x h'
      exact ⟨y, List.mem_cons_of_mem _ hy, hxy⟩

theorem subsequence_lineage {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ Q : ℕ → Finset ℕ, ∃ σ : ℕ ↪o ℕ, ∃ x : ℕ → ℕ,
      (∀ k, (Q k).Nonempty) ∧
      (∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h) ∧
      (∀ k, RepFree A N₀ (Q k)) ∧
      (∀ j k, j < k → Disjoint (Q j) (Q k)) ∧
      (∀ k, ∀ b ∈ A, 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
        ∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m (insert b (Q k))) ∧
      StrictMono x ∧ (∀ t, x t ∈ Q (σ t)) := by
  classical
  obtain ⟨Q, hne, hmem, hfree, hdisj, hguard, σ, hσ⟩ :=
    rank_layer_higman_chain h0 hcov hanchor hfail
  -- step: an element of a subsequence rank layer has a strictly larger
  -- partner in the next subsequence rank layer
  have hstep : ∀ t v, v ∈ Q (σ t) → ∃ w ∈ Q (σ (t + 1)),
      v < w := by
    intro t v hv
    have hchain := hσ t (t + 1) (by omega)
    obtain ⟨l', hf₂, hsub⟩ := List.sublistForall₂_iff.1 hchain
    have hvL : v ∈ (Q (σ t)).sort (· ≤ ·) := by
      rw [Finset.mem_sort]
      exact hv
    obtain ⟨w, hwl', hvw⟩ := forall₂_mem_partner hf₂ v hvL
    have hwL : w ∈ (Q (σ (t + 1))).sort (· ≤ ·) :=
      hsub.mem hwl'
    have hwQ : w ∈ Q (σ (t + 1)) := by
      rw [← Finset.mem_sort (α := ℕ) (· ≤ ·)]
      exact hwL
    have hvne : v ≠ w := by
      intro heq
      have h1 : σ t < σ (t + 1) := σ.strictMono (by omega)
      exact (Finset.disjoint_left.1 (hdisj _ _ h1)) hv
        (heq ▸ hwQ)
    exact ⟨w, hwQ, by omega⟩
  -- thread the lineage by recursion
  obtain ⟨v₀, hv₀⟩ := hne (σ 0)
  have hpick : ∀ t v, ∃ w, v ∈ Q (σ t) → w ∈ Q (σ (t + 1)) ∧
      v < w := by
    intro t v
    by_cases hv : v ∈ Q (σ t)
    · obtain ⟨w, hw, hvw⟩ := hstep t v hv
      exact ⟨w, fun _ => ⟨hw, hvw⟩⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose W hW using hpick
  obtain ⟨x, hx0, hxs⟩ : ∃ x : ℕ → ℕ, x 0 = v₀ ∧
      ∀ t, x (t + 1) = W t (x t) :=
    ⟨fun t => Nat.rec v₀ (fun t' v => W t' v) t, rfl,
      fun _ => rfl⟩
  have hxmem : ∀ t, x t ∈ Q (σ t) := by
    intro t
    induction t with
    | zero => rw [hx0]; exact hv₀
    | succ t ih =>
      rw [hxs]
      exact (hW t (x t) ih).1
  have hxmono : StrictMono x := by
    apply strictMono_nat_of_lt_succ
    intro t
    rw [hxs]
    exact (hW t (x t) (hxmem t)).2
  exact ⟨Q, σ, x, hne, hmem, hfree, hdisj, hguard, hxmono,
    hxmem⟩

theorem subsequence_stalls_hereditarily {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ Q : ℕ → Finset ℕ, ∃ σ : ℕ ↪o ℕ, ∃ x : ℕ → ℕ,
      StrictMono x ∧ (∀ t, x t ∈ Q (σ t)) ∧
      (∀ k, RepFree A N₀ (Q k)) ∧
      (∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h) ∧
      ∀ τ : ℕ → ℕ, StrictMono τ →
        ∃ J m, N₀ ≤ m ∧
          IsRepSupportTransversal A m ((Finset.range J).image (fun t =>
            x (τ t))) := by
  classical
  obtain ⟨Q, σ, x, hne, hmem, hfree, hdisj, hguard, hxmono,
    hxmem⟩ := subsequence_lineage h0 hcov hanchor hfail
  refine ⟨Q, σ, x, hxmono, hxmem, hfree,
    hmem, ?_⟩
  intro τ hτ
  have hdie := free_prefixes_die_of_hfail h0 hcov hfail
    (fun t => x (τ t)) (hxmono.comp hτ)
    (fun t => (hmem _ _ (hxmem (τ t))).1)
    (fun t => (hmem _ _ (hxmem (τ t))).2)
  push Not at hdie
  obtain ⟨J, hJ⟩ := hdie
  rw [RepFree] at hJ
  push Not at hJ
  obtain ⟨m, hm, hall⟩ := hJ
  refine ⟨J, m, hm, ?_⟩
  intro a ha b hb c hc hsum
  by_contra hmiss
  push Not at hmiss
  obtain ⟨h1, h2, h3⟩ := hmiss
  exact h3 (hall a ha b hb c hc hsum h1 h2)

theorem subsequence_rank_or_aligned {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
      RepFree A N₀ P ∧ c ≤ P.card) ∨
    (∃ Q : ℕ → Finset ℕ, ∃ σ : ℕ ↪o ℕ, ∃ T s : ℕ,
      (∀ k, RepFree A N₀ (Q k)) ∧
      (∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h) ∧
      (∀ j k, j < k → Disjoint (Q j) (Q k)) ∧
      1 ≤ s ∧
      (∀ t, T ≤ t → (Q (σ t)).card = s) ∧
      (∀ t, T ≤ t → List.Forall₂ (· ≤ ·)
        ((Q (σ t)).sort (· ≤ ·))
        ((Q (σ (t + 1))).sort (· ≤ ·)))) := by
  classical
  obtain ⟨Q, hne, hmem, hfree, hdisj, hguard, σ, hσ⟩ :=
    rank_layer_higman_chain h0 hcov hanchor hfail
  have hmono : ∀ t t', t ≤ t' →
      (Q (σ t)).card ≤ (Q (σ t')).card := by
    intro t t' htt
    obtain ⟨l', hf₂, hsub⟩ := List.sublistForall₂_iff.1
      (hσ t t' htt)
    have h1 : ((Q (σ t)).sort (· ≤ ·)).length = l'.length :=
      hf₂.length_eq
    have h2 := hsub.length_le
    rw [Finset.length_sort] at h1
    have h3 : ((Q (σ t')).sort (· ≤ ·)).length =
        (Q (σ t')).card := Finset.length_sort _
    omega
  by_cases hunb : ∀ c, ∃ t, c ≤ (Q (σ t)).card
  · left
    intro c
    obtain ⟨t, hc⟩ := hunb c
    exact ⟨Q (σ t), hmem _, hfree _, hc⟩
  · right
    push Not at hunb
    obtain ⟨c₀, hc₀⟩ := hunb
    -- monotone bounded: eventually constant
    have hstab : ∃ T, ∀ t, T ≤ t →
        (Q (σ t)).card = (Q (σ T)).card := by
      by_contra hno
      push Not at hno
      -- build a strictly climbing value chain, contradicting c₀
      have hstep : ∀ T, ∃ t, T ≤ t ∧
          (Q (σ T)).card < (Q (σ t)).card := by
        intro T
        obtain ⟨t, hTt, hne'⟩ := hno T
        have := hmono T t hTt
        exact ⟨t, hTt, by omega⟩
      choose nxt hnxt₁ hnxt₂ using hstep
      obtain ⟨g, hg0, hgs⟩ : ∃ g : ℕ → ℕ, g 0 = 0 ∧
          ∀ k, g (k + 1) = nxt (g k) :=
        ⟨fun k => Nat.rec 0 (fun _ p => nxt p) k, rfl,
          fun _ => rfl⟩
      have hclimb : ∀ k, k ≤ (Q (σ (g k))).card := by
        intro k
        induction k with
        | zero => omega
        | succ k ih =>
          have h1 := hnxt₂ (g k)
          rw [hgs]
          omega
      have := hclimb c₀
      have := hc₀ (g c₀)
      omega
    obtain ⟨T, hT⟩ := hstab
    refine ⟨Q, σ, T, (Q (σ T)).card, hfree, hmem, hdisj, ?_,
      hT, ?_⟩
    · have := hne (σ T)
      have := Finset.card_pos.2 this
      omega
    · intro t hTt
      obtain ⟨l', hf₂, hsub⟩ := List.sublistForall₂_iff.1
        (hσ t (t + 1) (by omega))
      have h1 : ((Q (σ t)).sort (· ≤ ·)).length = l'.length :=
        hf₂.length_eq
      have h2 : ((Q (σ t)).sort (· ≤ ·)).length =
          (Q (σ t)).card := Finset.length_sort _
      have h3 : ((Q (σ (t + 1))).sort (· ≤ ·)).length =
          (Q (σ (t + 1))).card := Finset.length_sort _
      have h4 := hT t hTt
      have h5 := hT (t + 1) (by omega)
      have hleq : l' = (Q (σ (t + 1))).sort (· ≤ ·) := by
        apply hsub.eq_of_length_le
        omega
      rw [← hleq]
      exact hf₂

theorem root_rank_omega_or_aligned {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (Ordinal.omega0 ≤
      ((poolFreeStep_wf h0 hcov hfail Set.univ).apply ∅).rank) ∨
    (∃ Q : ℕ → Finset ℕ, ∃ σ : ℕ ↪o ℕ, ∃ T s : ℕ,
      (∀ k, RepFree A N₀ (Q k)) ∧
      (∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h) ∧
      (∀ j k, j < k → Disjoint (Q j) (Q k)) ∧
      1 ≤ s ∧
      (∀ t, T ≤ t → (Q (σ t)).card = s) ∧
      (∀ t, T ≤ t → List.Forall₂ (· ≤ ·)
        ((Q (σ t)).sort (· ≤ ·))
        ((Q (σ (t + 1))).sort (· ≤ ·)))) := by
  rcases subsequence_rank_or_aligned h0 hcov hanchor hfail with
    hbig | hlock
  · left
    rw [Ordinal.omega0_le]
    intro n
    obtain ⟨P, hPmem, hPfree, hPc⟩ := hbig n
    have h1 := free_set_card_le_rank h0 hcov hfail
      (P₀ := Set.univ) ⟨hPmem, hPfree⟩
      (fun h _ => Set.mem_univ h)
    calc (n : Ordinal.{0}) ≤ (P.card : Ordinal.{0}) := by
          exact_mod_cast Nat.cast_le.2 hPc
      _ ≤ _ := h1
  · exact Or.inr hlock

theorem aligned_columns {A : Set ℕ} {N₀ : ℕ}
    {Q : ℕ → Finset ℕ} {σ : ℕ ↪o ℕ} {T s : ℕ}
    (hdisj : ∀ j k, j < k → Disjoint (Q j) (Q k))
    (hcard : ∀ t, T ≤ t → (Q (σ t)).card = s)
    (hdom : ∀ t, T ≤ t → List.Forall₂ (· ≤ ·)
      ((Q (σ t)).sort (· ≤ ·))
      ((Q (σ (t + 1))).sort (· ≤ ·))) :
    ∃ y : Fin s → ℕ → ℕ,
      (∀ k, StrictMono (y k)) ∧
      (∀ k t, y k t ∈ Q (σ (T + t))) ∧
      (∀ t, ∀ h ∈ Q (σ (T + t)), ∃ k, y k t = h) := by
  classical
  have hlen : ∀ t : ℕ,
      ((Q (σ (T + t))).sort (· ≤ ·)).length = s := by
    intro t
    rw [Finset.length_sort]
    exact hcard (T + t) (by omega)
  have hkl : ∀ (k : Fin s) (t : ℕ),
      (k : ℕ) < ((Q (σ (T + t))).sort (· ≤ ·)).length := by
    intro k t
    rw [hlen]
    exact k.isLt
  have hyget : ∀ (k : Fin s) (t : ℕ),
      ((Q (σ (T + t))).sort (· ≤ ·)).getD (k : ℕ) 0 =
        ((Q (σ (T + t))).sort (· ≤ ·))[(k : ℕ)]'(hkl k t) :=
    fun k t => List.getD_eq_getElem _ _ (hkl k t)
  have hymem : ∀ (k : Fin s) (t : ℕ),
      ((Q (σ (T + t))).sort (· ≤ ·)).getD (k : ℕ) 0 ∈
        Q (σ (T + t)) := by
    intro k t
    rw [hyget k t]
    have h1 := List.getElem_mem (hkl k t)
    rw [Finset.mem_sort] at h1
    exact h1
  have hymono : ∀ k : Fin s, StrictMono (fun t =>
      ((Q (σ (T + t))).sort (· ≤ ·)).getD (k : ℕ) 0) := by
    intro k
    apply strictMono_nat_of_lt_succ
    intro t
    have hd := hdom (T + t) (by omega)
    have harith : T + t + 1 = T + (t + 1) := by omega
    rw [harith] at hd
    have hle := (List.forall₂_iff_get.1 hd).2 (k : ℕ)
      (hkl k t) (hkl k (t + 1))
    have h1 : ((Q (σ (T + t))).sort (· ≤ ·)).getD (k : ℕ) 0 ≤
        ((Q (σ (T + (t + 1)))).sort (· ≤ ·)).getD (k : ℕ) 0 := by
      rw [hyget k t, hyget k (t + 1)]
      exact hle
    have hne : ((Q (σ (T + t))).sort (· ≤ ·)).getD (k : ℕ) 0 ≠
        ((Q (σ (T + (t + 1)))).sort (· ≤ ·)).getD (k : ℕ) 0 := by
      intro heq
      have hm1 := hymem k t
      have hm2 := hymem k (t + 1)
      have hσlt : σ (T + t) < σ (T + (t + 1)) :=
        σ.strictMono (by omega)
      exact (Finset.disjoint_left.1 (hdisj _ _ hσlt)) hm1
        (heq ▸ hm2)
    show ((Q (σ (T + t))).sort (· ≤ ·)).getD (k : ℕ) 0 <
      ((Q (σ (T + (t + 1)))).sort (· ≤ ·)).getD (k : ℕ) 0
    omega
  have honto : ∀ t, ∀ h ∈ Q (σ (T + t)), ∃ k : Fin s,
      ((Q (σ (T + t))).sort (· ≤ ·)).getD (k : ℕ) 0 = h := by
    intro t h hh
    have h1 : h ∈ (Q (σ (T + t))).sort (· ≤ ·) := by
      rw [Finset.mem_sort]
      exact hh
    obtain ⟨i, hi⟩ := List.mem_iff_get.1 h1
    have his : (i : ℕ) < s := by
      have h2 := i.isLt
      have h3 := hlen t
      omega
    refine ⟨⟨(i : ℕ), his⟩, ?_⟩
    rw [hyget ⟨(i : ℕ), his⟩ t]
    rw [← hi]
    rfl
  exact ⟨fun k t =>
    ((Q (σ (T + t))).sort (· ≤ ·)).getD (k : ℕ) 0,
    hymono, hymem, honto⟩

/-- Fork with required-element condition carried through (primed form of
`subsequence_rank_or_aligned`). -/
theorem subsequence_rank_or_aligned' {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
      RepFree A N₀ P ∧ c ≤ P.card) ∨
    (∃ Q : ℕ → Finset ℕ, ∃ σ : ℕ ↪o ℕ, ∃ T s : ℕ,
      (∀ k, RepFree A N₀ (Q k)) ∧
      (∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h) ∧
      (∀ j k, j < k → Disjoint (Q j) (Q k)) ∧
      (∀ k, ∀ b ∈ A, 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
        ∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m (insert b (Q k))) ∧
      1 ≤ s ∧
      (∀ t, T ≤ t → (Q (σ t)).card = s) ∧
      (∀ t, T ≤ t → List.Forall₂ (· ≤ ·)
        ((Q (σ t)).sort (· ≤ ·))
        ((Q (σ (t + 1))).sort (· ≤ ·)))) := by
  classical
  obtain ⟨Q, hne, hmem, hfree, hdisj, hguard, σ, hσ⟩ :=
    rank_layer_higman_chain h0 hcov hanchor hfail
  have hmono : ∀ t t', t ≤ t' →
      (Q (σ t)).card ≤ (Q (σ t')).card := by
    intro t t' htt
    obtain ⟨l', hf₂, hsub⟩ := List.sublistForall₂_iff.1
      (hσ t t' htt)
    have h1 : ((Q (σ t)).sort (· ≤ ·)).length = l'.length :=
      hf₂.length_eq
    have h2 := hsub.length_le
    rw [Finset.length_sort] at h1
    have h3 : ((Q (σ t')).sort (· ≤ ·)).length =
        (Q (σ t')).card := Finset.length_sort _
    omega
  by_cases hunb : ∀ c, ∃ t, c ≤ (Q (σ t)).card
  · left
    intro c
    obtain ⟨t, hc⟩ := hunb c
    exact ⟨Q (σ t), hmem _, hfree _, hc⟩
  · right
    push Not at hunb
    obtain ⟨c₀, hc₀⟩ := hunb
    have hstab : ∃ T, ∀ t, T ≤ t →
        (Q (σ t)).card = (Q (σ T)).card := by
      by_contra hno
      push Not at hno
      have hstep : ∀ T, ∃ t, T ≤ t ∧
          (Q (σ T)).card < (Q (σ t)).card := by
        intro T
        obtain ⟨t, hTt, hne'⟩ := hno T
        have := hmono T t hTt
        exact ⟨t, hTt, by omega⟩
      choose nxt hnxt₁ hnxt₂ using hstep
      obtain ⟨g, hg0, hgs⟩ : ∃ g : ℕ → ℕ, g 0 = 0 ∧
          ∀ k, g (k + 1) = nxt (g k) :=
        ⟨fun k => Nat.rec 0 (fun _ p => nxt p) k, rfl,
          fun _ => rfl⟩
      have hclimb : ∀ k, k ≤ (Q (σ (g k))).card := by
        intro k
        induction k with
        | zero => omega
        | succ k ih =>
          have h1 := hnxt₂ (g k)
          rw [hgs]
          omega
      have := hclimb c₀
      have := hc₀ (g c₀)
      omega
    obtain ⟨T, hT⟩ := hstab
    refine ⟨Q, σ, T, (Q (σ T)).card, hfree, hmem, hdisj, hguard,
      ?_, hT, ?_⟩
    · have := hne (σ T)
      have := Finset.card_pos.2 this
      omega
    · intro t hTt
      obtain ⟨l', hf₂, hsub⟩ := List.sublistForall₂_iff.1
        (hσ t (t + 1) (by omega))
      have h1 : ((Q (σ t)).sort (· ≤ ·)).length = l'.length :=
        hf₂.length_eq
      have h2 : ((Q (σ t)).sort (· ≤ ·)).length =
          (Q (σ t)).card := Finset.length_sort _
      have h3 : ((Q (σ (t + 1))).sort (· ≤ ·)).length =
          (Q (σ (t + 1))).card := Finset.length_sort _
      have h4 := hT t hTt
      have h5 := hT (t + 1) (by omega)
      have hleq : l' = (Q (σ (t + 1))).sort (· ≤ ·) := by
        apply hsub.eq_of_length_le
        omega
      rw [← hleq]
      exact hf₂

theorem aligned_one_column_clique {A : Set ℕ} {N₀ : ℕ}
    {Q : ℕ → Finset ℕ} {σ : ℕ ↪o ℕ} {T : ℕ} {x : ℕ → ℕ}
    (hmem : ∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h)
    (hdisj : ∀ j k, j < k → Disjoint (Q j) (Q k))
    (hguard : ∀ k, ∀ b ∈ A, 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
      ∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m (insert b (Q k)))
    (hsingle : ∀ t, T ≤ t → Q (σ t) = {x t}) :
    ∀ t t', T ≤ t → t < t' →
      ∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m ({x t', x t} : Finset ℕ) := by
  intro t t' hTt htt
  have hx'mem : x t' ∈ Q (σ t') := by
    rw [hsingle t' (by omega)]
    exact Finset.mem_singleton_self _
  have hx'A := (hmem _ _ hx'mem).1
  have hx'pos := (hmem _ _ hx'mem).2
  have havoid : ∀ j, j ≤ σ t → x t' ∉ Q j := by
    intro j hj hmem'
    have hσlt : σ t < σ t' := σ.strictMono htt
    have hjlt : j < σ t' := by omega
    exact (Finset.disjoint_left.1 (hdisj j (σ t') hjlt))
      hmem' hx'mem
  obtain ⟨m, hm, hhub⟩ := hguard (σ t) (x t') hx'A hx'pos havoid
  refine ⟨m, hm, ?_⟩
  have h1 : insert (x t') (Q (σ t)) =
      ({x t', x t} : Finset ℕ) := by
    rw [hsingle t hTt]
  rw [← h1]
  exact hhub

theorem aligned_column_required_element_condition {A : Set ℕ} {N₀ : ℕ}
    {Q : ℕ → Finset ℕ} {σ : ℕ ↪o ℕ} {T s : ℕ}
    {y : Fin s → ℕ → ℕ}
    (hmem : ∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h)
    (hdisj : ∀ j k, j < k → Disjoint (Q j) (Q k))
    (hguard : ∀ k, ∀ b ∈ A, 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
      ∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m (insert b (Q k)))
    (hy : ∀ k t, y k t ∈ Q (σ (T + t))) :
    ∀ (k : Fin s) (t t' : ℕ), t < t' →
      ∃ m, N₀ ≤ m ∧
        IsRepSupportTransversal A m (insert (y k t') (Q (σ (T + t)))) := by
  intro k t t' htt
  have hymem := hy k t'
  have hyA := (hmem _ _ hymem).1
  have hypos := (hmem _ _ hymem).2
  have havoid : ∀ j, j ≤ σ (T + t) → y k t' ∉ Q j := by
    intro j hj hmem'
    have hσlt : σ (T + t) < σ (T + t') :=
      σ.strictMono (by omega)
    have hjlt : j < σ (T + t') := by omega
    exact (Finset.disjoint_left.1 (hdisj j (σ (T + t')) hjlt))
      hmem' hymem
  exact hguard (σ (T + t)) (y k t') hyA hypos havoid

theorem iteration_tax {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {Q : ℕ → Finset ℕ} {σ : ℕ ↪o ℕ} {T s : ℕ}
    {y : Fin s → ℕ → ℕ}
    (hmem : ∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h)
    (hdisj : ∀ j k, j < k → Disjoint (Q j) (Q k))
    (hguard : ∀ k, ∀ b ∈ A, 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
      ∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m (insert b (Q k)))
    (hy : ∀ k t, y k t ∈ Q (σ (T + t))) :
    ∃ X, ∀ (k : Fin s) (t : ℕ), X ≤ y k t → 1 ≤ T + t →
      ∃ j, j < σ (T + t) ∧ ∃ m, N₀ + (T + t - 1) / 3 ≤ m ∧
        N₀ ≤ m ∧ IsRepSupportTransversal A m (insert (y k t) (Q j)) := by
  obtain ⟨X, hX⟩ := depth_tax_of_hfail h0 hcov hanchor hfail
    hdisj hguard
  refine ⟨X, ?_⟩
  intro k t hXy hTt
  have hymem := hy k t
  have hyA := (hmem _ _ hymem).1
  have hypos := (hmem _ _ hymem).2
  have hσge : T + t ≤ σ (T + t) := σ.strictMono.le_apply
  have havoid : ∀ j, j ≤ σ (T + t) - 1 → y k t ∉ Q j := by
    intro j hj hmem'
    have hjlt : j < σ (T + t) := by omega
    exact (Finset.disjoint_left.1 (hdisj j (σ (T + t)) hjlt))
      hmem' hymem
  obtain ⟨j, hj, m, hm₁, hm₂, hhub⟩ :=
    hX (σ (T + t) - 1) (y k t) hyA hXy hypos havoid
  refine ⟨j, by omega, m, ?_, hm₂, hhub⟩
  have hdiv : (T + t - 1) / 3 ≤ (σ (T + t) - 1) / 3 :=
    Nat.div_le_div_right (by omega)
  omega

theorem aligned_uniform_target_sequences {A : Set ℕ} {N₀ : ℕ}
    {Q : ℕ → Finset ℕ} {σ : ℕ ↪o ℕ} {T s : ℕ}
    {y : Fin s → ℕ → ℕ}
    (hmem : ∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h)
    (hdisj : ∀ j k, j < k → Disjoint (Q j) (Q k))
    (hguard : ∀ k, ∀ b ∈ A, 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
      ∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m (insert b (Q k)))
    (hfree : ∀ k, RepFree A N₀ (Q k))
    (hy : ∀ k t, y k t ∈ Q (σ (T + t)))
    (hymono : ∀ k, StrictMono (y k)) (hs : 1 ≤ s) :
    ∀ t K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ m ∈ V, N₀ ≤ m ∧ ∃ b ∈ A, b ∉ Q (σ (T + t)) ∧
        IsRepSupportTransversal A m (insert b (Q (σ (T + t)))) := by
  classical
  intro t K
  set k₀ : Fin s := ⟨0, by omega⟩ with hk₀
  have hlane := aligned_column_required_element_condition hmem hdisj hguard hy
  have hduty : ∀ i : ℕ, ∃ m, N₀ ≤ m ∧
      IsRepSupportTransversal A m (insert (y k₀ (t + 1 + i))
        (Q (σ (T + t)))) :=
    fun i => hlane k₀ t (t + 1 + i) (by omega)
  choose mf hmf₁ hmf₂ using hduty
  have hbnotin : ∀ i : ℕ, y k₀ (t + 1 + i) ∉ Q (σ (T + t)) := by
    intro i hmem'
    have h1 := hy k₀ (t + 1 + i)
    have hσlt : σ (T + t) < σ (T + (t + 1 + i)) :=
      σ.strictMono (by omega)
    exact (Finset.disjoint_left.1 (hdisj _ _ hσlt)) hmem' h1
  have hbinj : ∀ i j : ℕ, i ≠ j →
      y k₀ (t + 1 + i) ≠ y k₀ (t + 1 + j) := by
    intro i j hij
    intro heq
    rcases Nat.lt_or_ge i j with h | h
    · exact absurd heq (ne_of_lt ((hymono k₀) (by omega)))
    · have h' : j < i := by omega
      exact absurd heq.symm
        (ne_of_lt ((hymono k₀) (by omega)))
  -- fibers of the duty map have size ≤ 3 (sharer law)
  have hfib : ∀ m ∈ (Finset.range (3 * K + 1)).image mf,
      ((Finset.range (3 * K + 1)).filter
        (fun i => mf i = m)).card ≤ 3 := by
    intro m hmV
    rw [Finset.mem_image] at hmV
    obtain ⟨i₀, hi₀r, hi₀⟩ := hmV
    have hmN : N₀ ≤ m := hi₀ ▸ hmf₁ i₀
    obtain ⟨x₀, y₀, z₀, hshare⟩ :=
      three_required_elements_per_rep_target (hfree (σ (T + t))) hmN
    have hsub : ∀ i ∈ (Finset.range (3 * K + 1)).filter
        (fun i => mf i = m),
        y k₀ (t + 1 + i) ∈ ({x₀, y₀, z₀} : Finset ℕ) := by
      intro i hi
      rw [Finset.mem_filter] at hi
      have hhub := hmf₂ i
      rw [hi.2] at hhub
      have h1 := hshare (y k₀ (t + 1 + i)) (hbnotin i) hhub
      rcases h1 with h | h | h <;> simp [h]
    have hcard := Finset.card_le_card_of_injOn
      (f := fun i => y k₀ (t + 1 + i))
      (s := (Finset.range (3 * K + 1)).filter
        (fun i => mf i = m))
      (t := ({x₀, y₀, z₀} : Finset ℕ))
      hsub
      (by
        intro i _ j _ heq
        by_contra hne
        exact hbinj i j hne heq)
    have h3 : ({x₀, y₀, z₀} : Finset ℕ).card ≤ 3 := by
      apply le_trans (Finset.card_insert_le _ _)
      have := Finset.card_insert_le y₀ ({z₀} : Finset ℕ)
      simp at this ⊢
      omega
    omega
  have hcount := Finset.card_le_mul_card_image_of_maps_to
    (f := mf) (s := Finset.range (3 * K + 1))
    (t := (Finset.range (3 * K + 1)).image mf)
    (fun i hi => Finset.mem_image_of_mem mf hi) 3 hfib
  rw [Finset.card_range] at hcount
  refine ⟨(Finset.range (3 * K + 1)).image mf, by omega, ?_⟩
  intro m hmV
  rw [Finset.mem_image] at hmV
  obtain ⟨i, hir, hi⟩ := hmV
  refine ⟨hi ▸ hmf₁ i, y k₀ (t + 1 + i),
    (hmem _ _ (hy k₀ (t + 1 + i))).1, hbnotin i, ?_⟩
  rw [← hi]
  exact hmf₂ i

theorem anchor_dichotomy {A : Set ℕ} :
    (∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g) ∨
    (∃ g₀, ∀ c ∈ A, 0 < c → c ≠ g₀ →
      IsPairSupportTransversal A (2 * c) ({c, g₀} : Finset ℕ)) := by
  classical
  by_cases h : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g
  · exact Or.inl h
  · right
    push Not at h
    obtain ⟨g₀, hg₀⟩ := h
    refine ⟨g₀, fun c hcA hcpos hcg w hw w' hw' hsum => ?_⟩
    have h1 := hg₀ c hcA hcpos hcg w hw w' hw' hsum
    by_cases hwc : w = c
    · exact Or.inl (by simp [hwc])
    · have h2 := h1 hwc
      by_cases hwg : w = g₀
      · exact Or.inl (by simp [hwg])
      · exact Or.inr (by simp [h2 hwg])

open Classical in

theorem no_anchor_doubles_thin {A : Set ℕ} {g₀ c : ℕ}
    (hhub : IsPairSupportTransversal A (2 * c) ({c, g₀} : Finset ℕ)) :
    ((Finset.range (2 * c + 1)).filter
      (fun x => x ∈ A ∧ (2 * c - x) ∈ A)).card ≤ 3 := by
  classical
  have hsub : ((Finset.range (2 * c + 1)).filter
      (fun x => x ∈ A ∧ (2 * c - x) ∈ A)) ⊆
      ({c, g₀, 2 * c - g₀} : Finset ℕ) := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_range] at hx
    obtain ⟨hxr, hxA, hxA'⟩ := hx
    have hsum : x + (2 * c - x) = 2 * c := by omega
    rcases hhub x hxA (2 * c - x) hxA' hsum with h | h
    · rcases Finset.mem_insert.1 h with h' | h'
      · simp [h']
      · rw [Finset.mem_singleton] at h'
        simp [h']
    · rcases Finset.mem_insert.1 h with h' | h'
      · have : x = c := by omega
        simp [this]
      · rw [Finset.mem_singleton] at h'
        have : x = 2 * c - g₀ := by omega
        simp [this]
  have h1 := Finset.card_le_card hsub
  have h2 : ({c, g₀, 2 * c - g₀} : Finset ℕ).card ≤ 3 := by
    apply le_trans (Finset.card_insert_le _ _)
    have h3 := Finset.card_insert_le g₀
      ({2 * c - g₀} : Finset ℕ)
    simp at h3 ⊢
    omega
  omega

theorem no_anchor_central_or_member {A : Set ℕ} {g₀ : ℕ}
    (hroute : ∀ c ∈ A, 0 < c → c ≠ g₀ →
      IsPairSupportTransversal A (2 * c) ({c, g₀} : Finset ℕ)) :
    (g₀ ∈ A) ∨
    (∀ c ∈ A, 0 < c → c ≠ g₀ → ∀ w ∈ A, ∀ w' ∈ A,
      w + w' = 2 * c → w = c ∧ w' = c) := by
  classical
  by_cases hg : g₀ ∈ A
  · exact Or.inl hg
  · right
    intro c hcA hcpos hcg w hw w' hw' hsum
    rcases hroute c hcA hcpos hcg w hw w' hw' hsum with h | h
    · rcases Finset.mem_insert.1 h with h' | h'
      · exact ⟨h', by omega⟩
      · rw [Finset.mem_singleton] at h'
        exact absurd (h' ▸ hw) hg
    · rcases Finset.mem_insert.1 h with h' | h'
      · have hwc : w = c := by omega
        exact ⟨hwc, by omega⟩
      · rw [Finset.mem_singleton] at h'
        exact absurd (h' ▸ hw') hg

theorem central_branch_singleton_support_transversals {A : Set ℕ} {g₀ : ℕ}
    (hcentral : ∀ c ∈ A, 0 < c → c ≠ g₀ → ∀ w ∈ A, ∀ w' ∈ A,
      w + w' = 2 * c → w = c ∧ w' = c) :
    ∀ c ∈ A, 0 < c → c ≠ g₀ →
      IsPairSupportTransversal A (2 * c) ({c} : Finset ℕ) := by
  intro c hcA hcpos hcg w hw w' hw' hsum
  obtain ⟨h1, _⟩ := hcentral c hcA hcpos hcg w hw w' hw' hsum
  exact Or.inl (by simp [h1])

theorem central_branch_hmin {A : Set ℕ} {g₀ : ℕ}
    (hcentral : ∀ c ∈ A, 0 < c → c ≠ g₀ → ∀ w ∈ A, ∀ w' ∈ A,
      w + w' = 2 * c → w = c ∧ w' = c) :
    ∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n := by
  rintro B hBA hBinf ⟨N₁, hN₁⟩
  obtain ⟨b, hbB, hbgt⟩ := hBinf.exists_gt (N₁ + g₀ + 1)
  have hbA := hBA hbB
  have hbpos : 0 < b := by omega
  have hbg : b ≠ g₀ := by omega
  obtain ⟨x, hx, y, hy, hxB, hyB, hxy⟩ := hN₁ (2 * b) (by omega)
  obtain ⟨hxb, hyb⟩ := hcentral b hbA hbpos hbg x hx y hy hxy
  exact hxB (hxb ▸ hbB)

theorem central_branch_no_three_AP {A : Set ℕ} {g₀ : ℕ}
    (hcentral : ∀ c ∈ A, 0 < c → c ≠ g₀ → ∀ w ∈ A, ∀ w' ∈ A,
      w + w' = 2 * c → w = c ∧ w' = c) :
    ∀ a d, 0 < d → a ∈ A → a + d ∈ A → a + 2 * d ∈ A →
      a + d = g₀ ∨ a + d = 0 := by
  intro a d hd haA hadA ha2dA
  by_contra hno
  push Not at hno
  obtain ⟨hg, h0⟩ := hno
  have hpos : 0 < a + d := by omega
  have hsum : a + (a + 2 * d) = 2 * (a + d) := by omega
  obtain ⟨h1, h2⟩ := hcentral (a + d) hadA hpos hg
    a haA (a + 2 * d) ha2dA hsum
  omega

theorem odd_deletion_obligation {A : Set ℕ} {N₀ : ℕ}
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hodd : {a ∈ A | ¬2 ∣ a}.Infinite) :
    ∀ N, ∃ n, N ≤ n ∧
      ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n →
        ¬2 ∣ x ∨ ¬2 ∣ y ∨ ¬2 ∣ z := by
  classical
  intro N
  set B : Set ℕ := {a ∈ A | ¬2 ∣ a} with hB
  have hBA : B ⊆ A := fun a ha => ha.1
  have hnb := hfail B hBA hodd
  rw [IsExactTupleAsymptoticBasis] at hnb
  push Not at hnb
  obtain ⟨n, hn, hnofail⟩ := hnb N
  refine ⟨n, hn, ?_⟩
  intro x hx y hy z hz hsum
  by_contra hno
  push Not at hno
  obtain ⟨hx2, hy2, hz2⟩ := hno
  have hxB : x ∉ B := fun h => h.2 hx2
  have hyB : y ∉ B := fun h => h.2 hy2
  have hzB : z ∉ B := fun h => h.2 hz2
  refine hnofail ![x, y, z] (fun i => ?_) ?_
  · match i with
    | 0 => exact ⟨hx, hxB⟩
    | 1 => exact ⟨hy, hyB⟩
    | 2 => exact ⟨hz, hzB⟩
  · rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    omega

theorem canonical_deletion_obligation {A : Set ℕ} {N₀ : ℕ}
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (P : ℕ → Prop) (hP : {a ∈ A | P a}.Infinite) :
    ∀ N, ∃ n, N ≤ n ∧
      ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n →
        P x ∨ P y ∨ P z := by
  classical
  intro N
  set B : Set ℕ := {a ∈ A | P a} with hB
  have hBA : B ⊆ A := fun a ha => ha.1
  have hnb := hfail B hBA hP
  rw [IsExactTupleAsymptoticBasis] at hnb
  push Not at hnb
  obtain ⟨n, hn, hnofail⟩ := hnb N
  refine ⟨n, hn, ?_⟩
  intro x hx y hy z hz hsum
  by_contra hno
  push Not at hno
  obtain ⟨hx2, hy2, hz2⟩ := hno
  have hxB : x ∉ B := fun h => hx2 h.2
  have hyB : y ∉ B := fun h => hy2 h.2
  have hzB : z ∉ B := fun h => hz2 h.2
  refine hnofail ![x, y, z] (fun i => ?_) ?_
  · match i with
    | 0 => exact ⟨hx, hxB⟩
    | 1 => exact ⟨hy, hyB⟩
    | 2 => exact ⟨hz, hzB⟩
  · rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    omega

theorem grid_cap_three_classes {A : Set ℕ} {n m : ℕ}
    {r : Fin 4 → ℕ}
    (hrne : ∀ i j : Fin 4, i ≠ j → r i % m ≠ r j % m)
    (hrep : ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = n)
    (hfire : ∀ i : Fin 4, ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
      x + y + z = n →
      x % m = r i % m ∨ y % m = r i % m ∨ z % m = r i % m) :
    False := by
  classical
  obtain ⟨x, hx, y, hy, z, hz, hsum⟩ := hrep
  have hpick : ∀ i : Fin 4, ∃ p : Fin 3,
      (if p = 0 then x else if p = 1 then y else z) % m =
        r i % m := by
    intro i
    rcases hfire i x hx y hy z hz hsum with h | h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
    · exact ⟨2, by simpa using h⟩
  choose pk hpk using hpick
  have hcard : ¬Function.Injective pk := by
    intro hinj
    have := Fintype.card_le_of_injective pk hinj
    simp at this
  rw [Function.not_injective_iff] at hcard
  obtain ⟨i, j, hpij, hij⟩ := hcard
  have h1 := hpk i
  have h2 := hpk j
  rw [hpij] at h1
  exact hrne i j hij (h1 ▸ h2 ▸ rfl)

theorem residue_width_dichotomy {A : Set ℕ} (m : ℕ)
    (hm : 1 ≤ m) :
    (∃ r : Fin 4 → ℕ, (∀ i j : Fin 4, i ≠ j →
        r i % m ≠ r j % m) ∧
      ∀ i, {a ∈ A | a % m = r i % m}.Infinite) ∨
    (∃ R : Finset ℕ, R.card ≤ 3 ∧ ∃ X, ∀ a ∈ A, X ≤ a →
      a % m ∈ R) := by
  classical
  set W := (Finset.range m).filter
    (fun r => {a ∈ A | a % m = r}.Infinite) with hW
  by_cases hcard : 4 ≤ W.card
  · left
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hcard
    let e := t.orderIsoOfFin htc
    have hmemW : ∀ i : Fin 4, (e i : ℕ) ∈ W := fun i =>
      hts (e i).2
    have hlt : ∀ i : Fin 4, (e i : ℕ) < m := by
      intro i
      have h1 := hmemW i
      rw [hW, Finset.mem_filter, Finset.mem_range] at h1
      exact h1.1
    have hmodself : ∀ i : Fin 4, (e i : ℕ) % m = (e i : ℕ) :=
      fun i => Nat.mod_eq_of_lt (hlt i)
    refine ⟨fun i => (e i : ℕ), ?_, ?_⟩
    · intro i j hij
      rw [hmodself i, hmodself j]
      intro heq
      exact hij (e.injective (Subtype.ext heq))
    · intro i
      have h1 := hmemW i
      rw [hW, Finset.mem_filter] at h1
      rw [hmodself i]
      exact h1.2
  · right
    push Not at hcard
    refine ⟨W, by omega, ?_⟩
    set F := (Finset.range m) \ W with hF
    have hFfin : ∀ r ∈ F, {a ∈ A | a % m = r}.Finite := by
      intro r hr
      rw [hF, Finset.mem_sdiff] at hr
      have h2 : ¬{a ∈ A | a % m = r}.Infinite := by
        intro hinf
        exact hr.2 (by
          rw [hW, Finset.mem_filter]
          exact ⟨hr.1, hinf⟩)
      exact Set.not_infinite.1 h2
    have hbdd : ∀ r, ∃ b, r ∈ F → ∀ a ∈ A, a % m = r →
        a ≤ b := by
      intro r
      by_cases hr : r ∈ F
      · obtain ⟨b, hb⟩ := (hFfin r hr).bddAbove
        exact ⟨b, fun _ a haA hamod =>
          hb (Set.mem_setOf.2 ⟨haA, hamod⟩)⟩
      · exact ⟨0, fun h => absurd h hr⟩
    choose Bf hBf using hbdd
    refine ⟨(F.sup Bf) + 1, ?_⟩
    intro a haA hX
    have hrlt : a % m < m := Nat.mod_lt _ (by omega)
    by_cases hin : a % m ∈ W
    · exact hin
    · exfalso
      have hinF : a % m ∈ F := by
        rw [hF, Finset.mem_sdiff]
        exact ⟨Finset.mem_range.2 hrlt, hin⟩
      have h1 := hBf (a % m) hinF a haA rfl
      have h2 : Bf (a % m) ≤ F.sup Bf := Finset.le_sup hinF
      omega

theorem grid_pressure_or_alignment {A : Set ℕ} {N₀ : ℕ}
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (m : ℕ) (hm : 1 ≤ m) :
    (∃ r : Fin 4 → ℕ,
      (∀ i j : Fin 4, i ≠ j → r i % m ≠ r j % m) ∧
      (∀ i : Fin 4, ∀ N, ∃ n, N ≤ n ∧
        ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n →
          x % m = r i % m ∨ y % m = r i % m ∨
          z % m = r i % m) ∧
      (∀ n, (∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = n) →
        ¬∀ i : Fin 4, ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
          x + y + z = n → x % m = r i % m ∨
          y % m = r i % m ∨ z % m = r i % m)) ∨
    (∃ R : Finset ℕ, R.card ≤ 3 ∧ ∃ X, ∀ a ∈ A, X ≤ a →
      a % m ∈ R) := by
  rcases residue_width_dichotomy (A := A) m hm with
    ⟨r, hrne, hrinf⟩ | hnarrow
  · left
    refine ⟨r, hrne, ?_, ?_⟩
    · intro i
      exact canonical_deletion_obligation (N₀ := N₀) hfail
        (fun a => a % m = r i % m) (hrinf i)
    · intro n hrep hall
      exact grid_cap_three_classes hrne hrep hall
  · exact Or.inr hnarrow

theorem four_disjoint_full_support_transversals_impossible {A : Set ℕ} {m : ℕ}
    {H : Fin 4 → Finset ℕ}
    (hdisj : ∀ i j, i ≠ j → Disjoint (H i) (H j))
    (hrep : ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = m)
    (hhub : ∀ i, IsRepSupportTransversal A m (H i)) : False := by
  classical
  obtain ⟨x, hx, y, hy, z, hz, hsum⟩ := hrep
  have hpick : ∀ i : Fin 4, ∃ p : Fin 3,
      (if p = 0 then x else if p = 1 then y else z) ∈ H i := by
    intro i
    rcases hhub i x hx y hy z hz hsum with h | h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
    · exact ⟨2, by simpa using h⟩
  choose pk hpk using hpick
  have hcard : ¬Function.Injective pk := by
    intro hinj
    have := Fintype.card_le_of_injective pk hinj
    simp at this
  rw [Function.not_injective_iff] at hcard
  obtain ⟨i, j, hpij, hij⟩ := hcard
  have h1 := hpk i
  have h2 := hpk j
  rw [hpij] at h1
  exact (Finset.disjoint_left.1 (hdisj i j hij)) h1 h2

/-- A free set is a full support transversal of no target: freeness hands the
target a representation avoiding the set, support transversal-ness forbids it.
The fundamental exclusion between the two sides of the game. -/
theorem free_set_never_support_transversal {A : Set ℕ} {N₀ m : ℕ}
    {P : Finset ℕ} (hfree : RepFree A N₀ P) (hm : N₀ ≤ m)
    (hhub : IsRepSupportTransversal A m P) : False := by
  obtain ⟨x, hx, y, hy, z, hz, hsum, hxP, hyP, hzP⟩ := hfree m hm
  rcases hhub x hx y hy z hz hsum with h | h | h
  · exact hxP h
  · exact hyP h
  · exact hzP h

theorem stall_window_not_in_rank_layer {A : Set ℕ} {N₀ m : ℕ}
    {Q : Finset ℕ} {W : Finset ℕ}
    (hQfree : RepFree A N₀ Q) (hWQ : W ⊆ Q) (hm : N₀ ≤ m)
    (hhub : IsRepSupportTransversal A m W) : False :=
  free_set_never_support_transversal (RepFree.mono hWQ hQfree) hm hhub

theorem subsequence_stall_stream {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
    ∃ st len : ℕ → ℕ, ∃ tgt : ℕ → ℕ,
      (∀ i, 2 ≤ len i) ∧
      (∀ i, st (i + 1) = st i + len i) ∧
      (∀ i, N₀ ≤ tgt i ∧ IsRepSupportTransversal A (tgt i)
        ((Finset.range (len i)).image (fun j => x (st i + j)))) ∧
      (∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧ ∀ v ∈ V, ∃ i, tgt i = v) := by
  classical
  obtain ⟨Q, σ, x, hxmono, hxmem, hQfree, hQmem, hstall⟩ :=
    subsequence_stalls_hereditarily h0 hcov hanchor hfail
  have hxA : ∀ t, x t ∈ A ∧ 0 < x t :=
    fun t => hQmem _ _ (hxmem t)
  -- one stall window starting at any position; the free-rank layer
  -- exclusion forces width ≥ 2
  have hwin : ∀ s : ℕ, ∃ J m, 2 ≤ J ∧ N₀ ≤ m ∧
      IsRepSupportTransversal A m ((Finset.range J).image
        (fun j => x (s + j))) := by
    intro s
    obtain ⟨J, m, hm, hhub⟩ := hstall (fun j => s + j)
      (fun a b hab => by
        show s + a < s + b
        omega)
    match hJm : J with
    | 0 =>
      exfalso
      obtain ⟨u, hu, v, hv, huv⟩ := hcov m hm
      have h3 : u + v + 0 = m := by omega
      rcases hhub u hu v hv 0 h0 h3 with h | h | h <;>
        simp at h
    | 1 =>
      exfalso
      have hW1 : ((Finset.range 1).image
          (fun j => x (s + j))) = {x s} := by
        rw [Finset.range_one, Finset.image_singleton]
        simp
      rw [hW1] at hhub
      exact stall_window_not_in_rank_layer (hQfree (σ s))
        (Finset.singleton_subset_iff.2 (by
          simpa using hxmem s)) hm hhub
    | (J' + 2) =>
      exact ⟨J' + 2, m, by omega, hm, hhub⟩
  choose Jf mf hJf hmf hhubf using hwin
  -- consecutive windows by recursion
  obtain ⟨st, hst0, hsts⟩ : ∃ st : ℕ → ℕ, st 0 = 0 ∧
      ∀ i, st (i + 1) = st i + Jf (st i) :=
    ⟨fun i => Nat.rec 0 (fun _ p => p + Jf p) i, rfl,
      fun _ => rfl⟩
  refine ⟨x, hxmono, hxA, st, fun i => Jf (st i),
    fun i => mf (st i), fun i => hJf _, hsts,
    fun i => ⟨hmf _, hhubf _⟩, ?_⟩
  -- distinct targets via the pure cap
  intro K
  set W : ℕ → Finset ℕ := fun i =>
    (Finset.range (Jf (st i))).image (fun j => x (st i + j))
    with hWdef
  have hstmono : ∀ i, st i < st (i + 1) := by
    intro i
    rw [hsts]
    have := hJf (st i)
    omega
  have hstmono' : ∀ i i', i < i' → st i < st i' := by
    intro i i' hii
    induction i' with
    | zero => omega
    | succ i' ih =>
      have h1 := hstmono i'
      rcases Nat.lt_or_ge i i' with h | h
      · have := ih h
        omega
      · have : i = i' := by omega
        subst this
        omega
  have hstJ : ∀ i i', i < i' → st i + Jf (st i) ≤ st i' := by
    intro i i' hii
    have h1 : st (i + 1) ≤ st i' := by
      rcases Nat.lt_or_ge (i + 1) i' with h | h
      · exact le_of_lt (hstmono' _ _ h)
      · have : i + 1 = i' := by omega
        subst this
        exact le_refl _
    rw [hsts] at h1
    omega
  have hWdisj : ∀ i i', i ≠ i' → Disjoint (W i) (W i') := by
    intro i i' hii
    -- wlog i < i'
    rcases Nat.lt_or_ge i i' with h | h
    · rw [Finset.disjoint_left]
      intro a hai hai'
      rw [hWdef] at hai hai'
      simp only [Finset.mem_image, Finset.mem_range] at hai hai'
      obtain ⟨j, hj, hja⟩ := hai
      obtain ⟨j', hj', hja'⟩ := hai'
      have hlt : st i + j < st i' + j' := by
        have := hstJ i i' h
        omega
      have := hxmono hlt
      omega
    · have h' : i' < i := by omega
      rw [Finset.disjoint_left]
      intro a hai hai'
      rw [hWdef] at hai hai'
      simp only [Finset.mem_image, Finset.mem_range] at hai hai'
      obtain ⟨j, hj, hja⟩ := hai
      obtain ⟨j', hj', hja'⟩ := hai'
      have hlt : st i' + j' < st i + j := by
        have := hstJ i' i h'
        omega
      have := hxmono hlt
      omega
  -- fibers of tgt over windows are ≤ 3
  have hfib : ∀ v ∈ (Finset.range (3 * K + 1)).image
      (fun i => mf (st i)),
      ((Finset.range (3 * K + 1)).filter
        (fun i => mf (st i) = v)).card ≤ 3 := by
    intro v hv
    by_contra hbig
    push Not at hbig
    have h4 : 4 ≤ ((Finset.range (3 * K + 1)).filter
        (fun i => mf (st i) = v)).card := hbig
    obtain ⟨t4, ht4s, ht4c⟩ := Finset.exists_subset_card_eq h4
    let e := t4.orderIsoOfFin ht4c
    have hemem : ∀ i : Fin 4, (e i : ℕ) ∈
        (Finset.range (3 * K + 1)).filter
          (fun i => mf (st i) = v) := fun i => ht4s (e i).2
    have hval : ∀ i : Fin 4, mf (st (e i : ℕ)) = v := by
      intro i
      have h1 := hemem i
      rw [Finset.mem_filter] at h1
      exact h1.2
    have heinj : ∀ i j : Fin 4, i ≠ j →
        (e i : ℕ) ≠ (e j : ℕ) := by
      intro i j hij heq
      exact hij (e.injective (Subtype.ext heq))
    have hvm : N₀ ≤ v := by
      have h1 := hmf (st (e 0 : ℕ))
      rw [hval 0] at h1
      exact h1
    obtain ⟨u, hu, w, hw, huw⟩ := hcov v hvm
    refine four_disjoint_full_support_transversals_impossible
      (H := fun i => W (e i : ℕ)) ?_
      ⟨u, hu, w, hw, 0, h0, by omega⟩ ?_
    · intro i j hij
      exact hWdisj _ _ (fun h => hij
        (e.injective (Subtype.ext h)))
    · intro i
      have h1 := hhubf (st (e i : ℕ))
      rw [hval i] at h1
      exact h1
  have hcount := Finset.card_le_mul_card_image_of_maps_to
    (f := fun i => mf (st i))
    (s := Finset.range (3 * K + 1))
    (t := (Finset.range (3 * K + 1)).image
      (fun i => mf (st i)))
    (fun i hi => Finset.mem_image_of_mem _ hi) 3 hfib
  rw [Finset.card_range] at hcount
  refine ⟨(Finset.range (3 * K + 1)).image
    (fun i => mf (st i)), by omega, ?_⟩
  intro v hv
  rw [Finset.mem_image] at hv
  obtain ⟨i, _, hi⟩ := hv
  exact ⟨i, hi⟩

theorem repFree_iff_forall_not_support_transversal {A : Set ℕ} {N₀ : ℕ}
    {P : Finset ℕ} :
    RepFree A N₀ P ↔ ∀ m, N₀ ≤ m → ¬IsRepSupportTransversal A m P := by
  constructor
  · intro hfree m hm hhub
    exact free_set_never_support_transversal hfree hm hhub
  · intro hnot m hm
    have h1 := hnot m hm
    rw [IsRepSupportTransversal] at h1
    push Not at h1
    obtain ⟨x, hx, y, hy, z, hz, hsum, hxP, hyP, hzP⟩ := h1
    exact ⟨x, hx, y, hy, z, hz, hsum, hxP, hyP, hzP⟩

theorem stall_width_or_rank {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
      RepFree A N₀ P ∧ c ≤ P.card) ∨
    (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
      ∃ L, ∀ s : ℕ, ∃ J m, 2 ≤ J ∧ J ≤ L ∧ N₀ ≤ m ∧
        IsRepSupportTransversal A m ((Finset.range J).image
          (fun j => x (s + j)))) := by
  classical
  obtain ⟨Q, σ, x, hxmono, hxmem, hQfree, hQmem, hstall⟩ :=
    subsequence_stalls_hereditarily h0 hcov hanchor hfail
  have hxA : ∀ t, x t ∈ A ∧ 0 < x t :=
    fun t => hQmem _ _ (hxmem t)
  set Pred : ℕ → ℕ → Prop := fun s J => ∃ m, N₀ ≤ m ∧
    IsRepSupportTransversal A m ((Finset.range J).image (fun j => x (s + j)))
    with hPred
  have hne : ∀ s, ∃ J, Pred s J := by
    intro s
    obtain ⟨J, m, hm, hhub⟩ := hstall (fun j => s + j)
      (fun a b hab => by
        show s + a < s + b
        omega)
    exact ⟨J, m, hm, hhub⟩
  have hJdef : ∀ s, Pred s (Nat.find (hne s)) :=
    fun s => Nat.find_spec (hne s)
  have hJmin : ∀ s J', J' < Nat.find (hne s) → ¬Pred s J' :=
    fun s J' h => Nat.find_min (hne s) h
  -- minimal windows have width ≥ 2
  have hJ2 : ∀ s, 2 ≤ Nat.find (hne s) := by
    intro s
    by_contra hlt
    push Not at hlt
    interval_cases h : (Nat.find (hne s))
    · obtain ⟨m, hm, hhub⟩ := hJdef s
      rw [h] at hhub
      obtain ⟨u, hu, v, hv, huv⟩ := hcov m hm
      have h3 : u + v + 0 = m := by omega
      rcases hhub u hu v hv 0 h0 h3 with hh | hh | hh <;>
        simp at hh
    · obtain ⟨m, hm, hhub⟩ := hJdef s
      rw [h] at hhub
      have hW1 : ((Finset.range 1).image
          (fun j => x (s + j))) = {x s} := by
        rw [Finset.range_one, Finset.image_singleton]
        simp
      rw [hW1] at hhub
      exact stall_window_not_in_rank_layer (hQfree (σ s))
        (Finset.singleton_subset_iff.2 (by
          simpa using hxmem s)) hm hhub
  by_cases hbnd : ∃ L, ∀ s, Nat.find (hne s) ≤ L
  · right
    obtain ⟨L, hL⟩ := hbnd
    refine ⟨x, hxmono, hxA, L, fun s => ?_⟩
    obtain ⟨m, hm, hhub⟩ := hJdef s
    exact ⟨Nat.find (hne s), m, hJ2 s, hL s, hm, hhub⟩
  · left
    push Not at hbnd
    intro c
    obtain ⟨s, hs⟩ := hbnd (c + 1)
    -- the prefix of length c + 1 is a proper prefix: free
    have hfree' : RepFree A N₀ ((Finset.range (c + 1)).image
        (fun j => x (s + j))) := by
      rw [repFree_iff_forall_not_support_transversal]
      intro m hm hhub
      exact hJmin s (c + 1) (by omega) ⟨m, hm, hhub⟩
    refine ⟨(Finset.range (c + 1)).image (fun j => x (s + j)),
      ?_, hfree', ?_⟩
    · intro h hh
      rw [Finset.mem_image] at hh
      obtain ⟨j, _, hj⟩ := hh
      rw [← hj]
      exact hxA _
    · have hcard : ((Finset.range (c + 1)).image
          (fun j => x (s + j))).card = c + 1 := by
        rw [Finset.card_image_of_injOn]
        · exact Finset.card_range _
        · intro a _ b _ hab
          by_contra hne'
          rcases Nat.lt_or_ge a b with hl | hl
          · exact absurd hab (ne_of_lt (hxmono (by omega)))
          · exact absurd hab.symm
              (ne_of_lt (hxmono (by omega)))
      omega

theorem stall_width_or_rank_along {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
    ∀ τ : ℕ → ℕ, StrictMono τ →
      ((∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
        RepFree A N₀ P ∧ c ≤ P.card) ∨
      (∃ L, ∀ s : ℕ, ∃ J m, 2 ≤ J ∧ J ≤ L ∧ N₀ ≤ m ∧
        IsRepSupportTransversal A m ((Finset.range J).image
          (fun j => x (τ (s + j)))))) := by
  classical
  obtain ⟨Q, σ, x, hxmono, hxmem, hQfree, hQmem, hstall⟩ :=
    subsequence_stalls_hereditarily h0 hcov hanchor hfail
  have hxA : ∀ t, x t ∈ A ∧ 0 < x t :=
    fun t => hQmem _ _ (hxmem t)
  refine ⟨x, hxmono, hxA, ?_⟩
  intro τ hτ
  set Pred : ℕ → ℕ → Prop := fun s J => ∃ m, N₀ ≤ m ∧
    IsRepSupportTransversal A m ((Finset.range J).image
      (fun j => x (τ (s + j)))) with hPred
  have hne : ∀ s, ∃ J, Pred s J := by
    intro s
    obtain ⟨J, m, hm, hhub⟩ := hstall (fun j => τ (s + j))
      (fun a b hab => hτ (by omega))
    exact ⟨J, m, hm, hhub⟩
  have hJdef : ∀ s, Pred s (Nat.find (hne s)) :=
    fun s => Nat.find_spec (hne s)
  have hJmin : ∀ s J', J' < Nat.find (hne s) → ¬Pred s J' :=
    fun s J' h => Nat.find_min (hne s) h
  have hJ2 : ∀ s, 2 ≤ Nat.find (hne s) := by
    intro s
    by_contra hlt
    push Not at hlt
    interval_cases h : (Nat.find (hne s))
    · obtain ⟨m, hm, hhub⟩ := hJdef s
      rw [h] at hhub
      obtain ⟨u, hu, v, hv, huv⟩ := hcov m hm
      have h3 : u + v + 0 = m := by omega
      rcases hhub u hu v hv 0 h0 h3 with hh | hh | hh <;>
        simp at hh
    · obtain ⟨m, hm, hhub⟩ := hJdef s
      rw [h] at hhub
      have hW1 : ((Finset.range 1).image
          (fun j => x (τ (s + j)))) = {x (τ s)} := by
        rw [Finset.range_one, Finset.image_singleton]
        simp
      rw [hW1] at hhub
      exact stall_window_not_in_rank_layer (hQfree (σ (τ s)))
        (Finset.singleton_subset_iff.2 (by
          simpa using hxmem (τ s))) hm hhub
  by_cases hbnd : ∃ L, ∀ s, Nat.find (hne s) ≤ L
  · right
    obtain ⟨L, hL⟩ := hbnd
    refine ⟨L, fun s => ?_⟩
    obtain ⟨m, hm, hhub⟩ := hJdef s
    exact ⟨Nat.find (hne s), m, hJ2 s, hL s, hm, hhub⟩
  · left
    push Not at hbnd
    intro c
    obtain ⟨s, hs⟩ := hbnd (c + 1)
    have hfree' : RepFree A N₀ ((Finset.range (c + 1)).image
        (fun j => x (τ (s + j)))) := by
      rw [repFree_iff_forall_not_support_transversal]
      intro m hm hhub
      exact hJmin s (c + 1) (by omega) ⟨m, hm, hhub⟩
    refine ⟨(Finset.range (c + 1)).image
      (fun j => x (τ (s + j))), ?_, hfree', ?_⟩
    · intro h hh
      rw [Finset.mem_image] at hh
      obtain ⟨j, _, hj⟩ := hh
      rw [← hj]
      exact hxA _
    · have hcard : ((Finset.range (c + 1)).image
          (fun j => x (τ (s + j)))).card = c + 1 := by
        rw [Finset.card_image_of_injOn]
        · exact Finset.card_range _
        · intro a _ b _ hab
          by_contra hne'
          rcases Nat.lt_or_ge a b with hl | hl
          · exact absurd hab
              (ne_of_lt (hxmono (hτ (by omega))))
          · exact absurd hab.symm
              (ne_of_lt (hxmono (hτ (by omega))))
      omega

theorem narrow_located_target_sequence {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    {x : ℕ → ℕ} {L : ℕ} (hxmono : StrictMono x)
    (hnarrow : ∀ s : ℕ, ∃ J m, 2 ≤ J ∧ J ≤ L ∧ N₀ ≤ m ∧
      IsRepSupportTransversal A m ((Finset.range J).image
        (fun j => x (s + j)))) :
    ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧ ∀ v ∈ V, N₀ ≤ v ∧
      ∃ s J, 2 ≤ J ∧ J ≤ L ∧
        IsRepSupportTransversal A v ((Finset.range J).image
          (fun j => x (s + j))) := by
  classical
  intro K
  choose Jf mf hJ2 hJL hmN hhub using hnarrow
  set W : ℕ → Finset ℕ := fun i =>
    (Finset.range (Jf (i * L))).image
      (fun j => x (i * L + j)) with hW
  have hL2 : 2 ≤ L := le_trans (hJ2 0) (hJL 0)
  have hWdisj : ∀ i i', i ≠ i' → Disjoint (W i) (W i') := by
    intro i i' hii
    rw [Finset.disjoint_left]
    intro a hai hai'
    rw [hW] at hai hai'
    simp only [Finset.mem_image, Finset.mem_range] at hai hai'
    obtain ⟨j, hj, hja⟩ := hai
    obtain ⟨j', hj', hja'⟩ := hai'
    have hjL : j < L := lt_of_lt_of_le hj (hJL _)
    have hj'L : j' < L := lt_of_lt_of_le hj' (hJL _)
    have hne : i * L + j ≠ i' * L + j' := by
      rcases Nat.lt_or_ge i i' with h | h
      · have h1 : i * L + j < i' * L + j' := by
          have h2 : (i + 1) * L ≤ i' * L :=
            Nat.mul_le_mul_right _ (by omega)
          have h3 : (i + 1) * L = i * L + L := by ring
          omega
        omega
      · have h' : i' < i := by omega
        have h1 : i' * L + j' < i * L + j := by
          have h2 : (i' + 1) * L ≤ i * L :=
            Nat.mul_le_mul_right _ (by omega)
          have h3 : (i' + 1) * L = i' * L + L := by ring
          omega
        omega
    exact hne (hxmono.injective (hja.trans hja'.symm))
  have hfib : ∀ v ∈ (Finset.range (3 * K + 1)).image
      (fun i => mf (i * L)),
      ((Finset.range (3 * K + 1)).filter
        (fun i => mf (i * L) = v)).card ≤ 3 := by
    intro v hv
    by_contra hbig
    push Not at hbig
    obtain ⟨t4, ht4s, ht4c⟩ := Finset.exists_subset_card_eq
      (show 4 ≤ _ from hbig)
    let e := t4.orderIsoOfFin ht4c
    have hemem : ∀ i : Fin 4, (e i : ℕ) ∈
        (Finset.range (3 * K + 1)).filter
          (fun i => mf (i * L) = v) := fun i => ht4s (e i).2
    have hval : ∀ i : Fin 4, mf ((e i : ℕ) * L) = v := by
      intro i
      have h1 := hemem i
      rw [Finset.mem_filter] at h1
      exact h1.2
    have hvm : N₀ ≤ v := by
      have h1 := hmN ((e 0 : ℕ) * L)
      rw [hval 0] at h1
      exact h1
    obtain ⟨u, hu, w, hw, huw⟩ := hcov v hvm
    refine four_disjoint_full_support_transversals_impossible
      (H := fun i => W (e i : ℕ)) ?_
      ⟨u, hu, w, hw, 0, h0, by omega⟩ ?_
    · intro i j hij
      exact hWdisj _ _ (fun h => hij
        (e.injective (Subtype.ext h)))
    · intro i
      have h1 := hhub ((e i : ℕ) * L)
      rw [hval i] at h1
      exact h1
  have hcount := Finset.card_le_mul_card_image_of_maps_to
    (f := fun i => mf (i * L))
    (s := Finset.range (3 * K + 1))
    (t := (Finset.range (3 * K + 1)).image
      (fun i => mf (i * L)))
    (fun i hi => Finset.mem_image_of_mem _ hi) 3 hfib
  rw [Finset.card_range] at hcount
  refine ⟨(Finset.range (3 * K + 1)).image
    (fun i => mf (i * L)), by omega, ?_⟩
  intro v hv
  rw [Finset.mem_image] at hv
  obtain ⟨i, _, hi⟩ := hv
  refine ⟨hi ▸ hmN (i * L), i * L, Jf (i * L), hJ2 _, hJL _, ?_⟩
  rw [← hi]
  exact hhub (i * L)

theorem final_fork {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
      RepFree A N₀ P ∧ c ≤ P.card) ∨
    (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
      ∃ L, ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ v ∈ V, N₀ ≤ v ∧ ∃ s J, 2 ≤ J ∧ J ≤ L ∧
          IsRepSupportTransversal A v ((Finset.range J).image
            (fun j => x (s + j)))) := by
  rcases stall_width_or_rank h0 hcov hanchor hfail with
    hrank | ⟨x, hxmono, hxA, L, hnarrow⟩
  · exact Or.inl hrank
  · exact Or.inr ⟨x, hxmono, hxA, L,
      narrow_located_target_sequence h0 hcov hxmono hnarrow⟩

/-! ## The welded fork: the target sequence is an order-2 object -/

theorem pairSupportTransversal_of_repSupportTransversal {A : Set ℕ} {n : ℕ} {H : Finset ℕ}
    (h0 : 0 ∈ A) (h0H : 0 ∉ H) (hhub : IsRepSupportTransversal A n H) :
    IsPairSupportTransversal A n H := by
  intro a ha b hb hab
  rcases hhub a ha b hb 0 h0 (by omega) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h h0H

open Classical in

theorem pair_support_transversal_pair_count {A : Set ℕ} {v : ℕ} {H : Finset ℕ}
    (hhub : IsPairSupportTransversal A v H) :
    ((Finset.range (v + 1)).filter
      (fun a => a ∈ A ∧ (v - a) ∈ A ∧ 2 * a ≤ v)).card ≤ H.card := by
  classical
  apply Finset.card_le_card_of_injOn
    (fun a => if a ∈ H then a else v - a)
  · intro a hafil
    simp only [Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range] at hafil
    obtain ⟨hav, haA, hvaA, h2a⟩ := hafil
    simp only [Finset.mem_coe]
    by_cases haH : a ∈ H
    · rw [if_pos haH]; exact haH
    · rw [if_neg haH]
      rcases hhub a haA (v - a) hvaA (by omega) with h | h
      · exact absurd h haH
      · exact h
  · intro a ha a' ha' heq
    simp only [Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range] at ha ha'
    obtain ⟨hav, _, _, h2a⟩ := ha
    obtain ⟨hav', _, _, h2a'⟩ := ha'
    have heq' : (if a ∈ H then a else v - a) =
        (if a' ∈ H then a' else v - a') := heq
    by_cases haH : a ∈ H
    · by_cases haH' : a' ∈ H
      · rw [if_pos haH, if_pos haH'] at heq'; exact heq'
      · rw [if_pos haH, if_neg haH'] at heq'; omega
    · by_cases haH' : a' ∈ H
      · rw [if_neg haH, if_pos haH'] at heq'; omega
      · rw [if_neg haH, if_neg haH'] at heq'; omega

theorem target_sequence_target_exclusion_interval {A : Set ℕ} {v s J : ℕ} {x : ℕ → ℕ}
    (hxmono : StrictMono x) (hJ : 1 ≤ J)
    (hhub : IsPairSupportTransversal A v ((Finset.range J).image
      (fun j => x (s + j)))) :
    ∀ a ∈ A, ∀ b ∈ A, a + b = v →
      (x s ≤ a ∧ a ≤ x (s + J - 1)) ∨
      (x s ≤ b ∧ b ≤ x (s + J - 1)) := by
  intro a ha b hb hab
  have hwin : ∀ y ∈ (Finset.range J).image (fun j => x (s + j)),
      x s ≤ y ∧ y ≤ x (s + J - 1) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨j, hj, hjy⟩ := hy
    rw [Finset.mem_range] at hj
    constructor
    · rw [← hjy]
      exact hxmono.monotone (by omega)
    · rw [← hjy]
      exact hxmono.monotone (by omega)
  rcases hhub a ha b hb hab with h | h
  · exact Or.inl (hwin a h)
  · exact Or.inr (hwin b h)

open Classical in

theorem final_fork_welded {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
      RepFree A N₀ P ∧ c ≤ P.card) ∨
    (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
      ∃ L, ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ v ∈ V, N₀ ≤ v ∧ ∃ s J, 2 ≤ J ∧ J ≤ L ∧
          IsPairSupportTransversal A v ((Finset.range J).image
            (fun j => x (s + j))) ∧
          ((Finset.range (v + 1)).filter
            (fun a => a ∈ A ∧ (v - a) ∈ A ∧ 2 * a ≤ v)).card
            ≤ L) := by
  rcases final_fork h0 hcov hanchor hfail with
    hrank | ⟨x, hxmono, hxA, L, hstreet⟩
  · exact Or.inl hrank
  · refine Or.inr ⟨x, hxmono, hxA, L, ?_⟩
    intro K
    obtain ⟨V, hVcard, hV⟩ := hstreet K
    refine ⟨V, hVcard, ?_⟩
    intro v hv
    obtain ⟨hvN, s, J, hJ2, hJL, hhub⟩ := hV v hv
    have h0win : (0 : ℕ) ∉ (Finset.range J).image
        (fun j => x (s + j)) := by
      intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨j, _, hj⟩ := hmem
      exact (hxA (s + j)).2.ne' hj
    have hpair := pairSupportTransversal_of_repSupportTransversal h0 h0win hhub
    have hcount := pair_support_transversal_pair_count (A := A) (v := v) hpair
    have hcard : ((Finset.range J).image
        (fun j => x (s + j))).card ≤ J := by
      have h1 := Finset.card_image_le (s := Finset.range J)
        (f := fun j => x (s + j))
      rw [Finset.card_range] at h1
      exact h1
    exact ⟨hvN, s, J, hJ2, hJL, hpair, by omega⟩

/-! ## The target sequence trichotomy: fixed hall or marching windows -/

theorem target_sequence_position_dichotomy {W : ℕ → ℕ → Prop}
    (hstreet : ∀ K : ℕ, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ v ∈ V, ∃ s, W v s) :
    (∃ S₀, ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ v ∈ V, ∃ s, s ≤ S₀ ∧ W v s) ∨
    (∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ v ∈ V, ∃ s, S₀ ≤ s ∧ W v s) := by
  classical
  by_cases hb : ∃ S₀, ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ v ∈ V, ∃ s, s ≤ S₀ ∧ W v s
  · exact Or.inl hb
  · right
    intro S₀ K
    have hnP : ¬∀ K', ∃ V : Finset ℕ, K' ≤ V.card ∧
        ∀ v ∈ V, ∃ s, s ≤ S₀ ∧ W v s :=
      fun hall => hb ⟨S₀, hall⟩
    obtain ⟨K₀, hK₀⟩ := not_forall.mp hnP
    obtain ⟨V, hVcard, hV⟩ := hstreet (K₀ + K)
    set Vfar := V.filter (fun v => ∃ s, S₀ ≤ s ∧ W v s) with hVfar
    by_cases hcard : K ≤ Vfar.card
    · refine ⟨Vfar, hcard, ?_⟩
      intro v hv
      rw [hVfar, Finset.mem_filter] at hv
      exact hv.2
    · exfalso
      apply hK₀
      refine ⟨V \ Vfar, ?_, ?_⟩
      · have h2 : (V \ Vfar).card =
            V.card - (Vfar ∩ V).card := Finset.card_sdiff
        have h3 : (Vfar ∩ V).card ≤ Vfar.card :=
          Finset.card_le_card Finset.inter_subset_left
        omega
      · intro v hv
        rw [Finset.mem_sdiff] at hv
        obtain ⟨hvV, hvnf⟩ := hv
        obtain ⟨s, hWs⟩ := hV v hvV
        refine ⟨s, ?_, hWs⟩
        by_contra hgt
        exact hvnf (by
          rw [hVfar, Finset.mem_filter]
          exact ⟨hvV, s, by omega, hWs⟩)

theorem target_sequence_window_below_target {A : Set ℕ} {N₀ : ℕ}
    {x : ℕ → ℕ} {v s J : ℕ} (hcov : PairCovers A N₀)
    (hxmono : StrictMono x) (hvN : N₀ ≤ v)
    (hhub : IsPairSupportTransversal A v ((Finset.range J).image
      (fun j => x (s + j)))) :
    x s ≤ v := by
  obtain ⟨a, haA, b, hbA, hab⟩ := hcov v hvN
  have hwin : ∀ y ∈ (Finset.range J).image (fun j => x (s + j)),
      x s ≤ y := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨j, _, hjy⟩ := hy
    rw [← hjy]
    exact hxmono.monotone (by omega)
  rcases hhub a haA b hbA hab with h | h
  · exact le_trans (hwin a h) (by omega)
  · exact le_trans (hwin b h) (by omega)

theorem bounded_target_sequence_fixed_hall {A : Set ℕ} {N₀ : ℕ}
    {x : ℕ → ℕ} {L S₀ : ℕ}
    (hnear : ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ v ∈ V, ∃ s, s ≤ S₀ ∧ N₀ ≤ v ∧ ∃ J, 2 ≤ J ∧ J ≤ L ∧
        IsPairSupportTransversal A v ((Finset.range J).image
          (fun j => x (s + j)))) :
    ∃ H : Finset ℕ, H.card ≤ L ∧ ∀ K, ∃ V : Finset ℕ,
      K ≤ V.card ∧ ∀ v ∈ V, N₀ ≤ v ∧ IsPairSupportTransversal A v H := by
  classical
  set box : Finset (ℕ × ℕ) :=
    (Finset.range (S₀ + 1)) ×ˢ (Finset.range (L + 1)) with hbox
  have hstep1 : ∀ K, ∃ p ∈ box, ∃ V' : Finset ℕ, K ≤ V'.card ∧
      ∀ v ∈ V', N₀ ≤ v ∧ IsPairSupportTransversal A v
        ((Finset.range p.2).image (fun j => x (p.1 + j))) := by
    intro K
    obtain ⟨V, hVcard, hV⟩ := hnear (box.card * K + 1)
    have hVtot : ∀ v, ∃ p : ℕ × ℕ, v ∈ V →
        p.1 ≤ S₀ ∧ 2 ≤ p.2 ∧ p.2 ≤ L ∧ N₀ ≤ v ∧
        IsPairSupportTransversal A v ((Finset.range p.2).image
          (fun j => x (p.1 + j))) := by
      intro v
      by_cases hvV : v ∈ V
      · obtain ⟨s, hs, hvN, J, hJ2, hJL, hhub⟩ := hV v hvV
        exact ⟨(s, J), fun _ => ⟨hs, hJ2, hJL, hvN, hhub⟩⟩
      · exact ⟨(0, 2), fun h => absurd h hvV⟩
    choose pf hpf using hVtot
    have hmaps : ∀ v ∈ V, pf v ∈ box := by
      intro v hvV
      obtain ⟨h1, h2, h3, _, _⟩ := hpf v hvV
      rw [hbox, Finset.mem_product]
      exact ⟨Finset.mem_range.2 (by omega),
        Finset.mem_range.2 (by omega)⟩
    have hlt : box.card * K < V.card := by omega
    obtain ⟨p, hpbox, hfiber⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        hmaps hlt
    refine ⟨p, hpbox, V.filter (fun v => pf v = p),
      by omega, ?_⟩
    intro v hv
    rw [Finset.mem_filter] at hv
    obtain ⟨hvV, hfv⟩ := hv
    obtain ⟨_, _, _, hvN, hhub⟩ := hpf v hvV
    rw [hfv] at hhub
    exact ⟨hvN, hhub⟩
  have hstab : ∃ p ∈ box, ∀ K, ∃ V' : Finset ℕ,
      K ≤ V'.card ∧ ∀ v ∈ V', N₀ ≤ v ∧ IsPairSupportTransversal A v
        ((Finset.range p.2).image (fun j => x (p.1 + j))) := by
    by_contra hno
    have hKp : ∀ p : ℕ × ℕ, ∃ Kp, p ∈ box →
        ¬(∃ V' : Finset ℕ, Kp ≤ V'.card ∧ ∀ v ∈ V', N₀ ≤ v ∧
          IsPairSupportTransversal A v ((Finset.range p.2).image
            (fun j => x (p.1 + j)))) := by
      intro p
      by_cases hpbox : p ∈ box
      · have h1 : ¬∀ K, ∃ V' : Finset ℕ, K ≤ V'.card ∧
            ∀ v ∈ V', N₀ ≤ v ∧ IsPairSupportTransversal A v
              ((Finset.range p.2).image (fun j => x (p.1 + j))) :=
          fun hall => hno ⟨p, hpbox, hall⟩
        obtain ⟨Kp, hKp'⟩ := not_forall.mp h1
        exact ⟨Kp, fun _ => hKp'⟩
      · exact ⟨0, fun h => absurd h hpbox⟩
    choose Kf hKf using hKp
    obtain ⟨p, hpbox, V', hV'card, hV'⟩ := hstep1 (box.sup Kf)
    exact hKf p hpbox ⟨V',
      le_trans (Finset.le_sup (f := Kf) hpbox) hV'card, hV'⟩
  obtain ⟨p, hpbox, hall⟩ := hstab
  refine ⟨(Finset.range p.2).image (fun j => x (p.1 + j)),
    ?_, hall⟩
  have h1 := Finset.card_image_le (s := Finset.range p.2)
    (f := fun j => x (p.1 + j))
  rw [Finset.card_range] at h1
  rw [hbox, Finset.mem_product] at hpbox
  have h2 := Finset.mem_range.1 hpbox.2
  omega

theorem fixed_hall_popular_shift {A : Set ℕ} {N₀ : ℕ}
    {H : Finset ℕ} (hcov : PairCovers A N₀)
    (hhall : ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ v ∈ V, N₀ ≤ v ∧ IsPairSupportTransversal A v H) :
    ∃ h ∈ H, ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ v ∈ V, N₀ ≤ v ∧ h ≤ v ∧ v - h ∈ A ∧ IsPairSupportTransversal A v H := by
  classical
  have hstep1 : ∀ K, ∃ h ∈ H, ∃ V' : Finset ℕ, K ≤ V'.card ∧
      ∀ v ∈ V', N₀ ≤ v ∧ h ≤ v ∧ v - h ∈ A ∧
        IsPairSupportTransversal A v H := by
    intro K
    obtain ⟨V, hVcard, hV⟩ := hhall (H.card * K + 1)
    have hVtot : ∀ v, ∃ h, v ∈ V →
        h ∈ H ∧ h ≤ v ∧ v - h ∈ A := by
      intro v
      by_cases hvV : v ∈ V
      · obtain ⟨hvN, hhub⟩ := hV v hvV
        obtain ⟨a, haA, b, hbA, hab⟩ := hcov v hvN
        rcases hhub a haA b hbA hab with hmem | hmem
        · refine ⟨a, fun _ => ⟨hmem, by omega, ?_⟩⟩
          have hb : v - a = b := by omega
          rw [hb]; exact hbA
        · refine ⟨b, fun _ => ⟨hmem, by omega, ?_⟩⟩
          have ha : v - b = a := by omega
          rw [ha]; exact haA
      · exact ⟨0, fun h => absurd h hvV⟩
    choose hf hhf using hVtot
    have hmaps : ∀ v ∈ V, hf v ∈ H :=
      fun v hvV => (hhf v hvV).1
    have hlt : H.card * K < V.card := by omega
    obtain ⟨h, hhH, hfiber⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        hmaps hlt
    refine ⟨h, hhH, V.filter (fun v => hf v = h), by omega, ?_⟩
    intro v hv
    rw [Finset.mem_filter] at hv
    obtain ⟨hvV, hfv⟩ := hv
    obtain ⟨_, hle, hsub⟩ := hhf v hvV
    rw [hfv] at hle hsub
    exact ⟨(hV v hvV).1, hle, hsub, (hV v hvV).2⟩
  by_contra hno
  have hKh : ∀ h : ℕ, ∃ Kh, h ∈ H → ¬(∃ V : Finset ℕ,
      Kh ≤ V.card ∧ ∀ v ∈ V, N₀ ≤ v ∧ h ≤ v ∧ v - h ∈ A ∧
        IsPairSupportTransversal A v H) := by
    intro h
    by_cases hhH : h ∈ H
    · have h1 : ¬∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
          ∀ v ∈ V, N₀ ≤ v ∧ h ≤ v ∧ v - h ∈ A ∧
            IsPairSupportTransversal A v H :=
        fun hall => hno ⟨h, hhH, hall⟩
      obtain ⟨Kh, hKh'⟩ := not_forall.mp h1
      exact ⟨Kh, fun _ => hKh'⟩
    · exact ⟨0, fun hh => absurd hh hhH⟩
  choose Kf hKf using hKh
  obtain ⟨h, hhH, V', hV'card, hV'⟩ := hstep1 (H.sup Kf)
  exact hKf h hhH ⟨V',
    le_trans (Finset.le_sup (f := Kf) hhH) hV'card, hV'⟩

theorem target_sequence_trichotomy {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
      RepFree A N₀ P ∧ c ≤ P.card) ∨
    (∃ H : Finset ℕ, ∃ h ∈ H, ∀ K, ∃ V : Finset ℕ,
      K ≤ V.card ∧ ∀ v ∈ V, N₀ ≤ v ∧ h ≤ v ∧ v - h ∈ A ∧
        IsPairSupportTransversal A v H) ∨
    (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
      ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ v ∈ V, N₀ ≤ v ∧ ∃ s, S₀ ≤ s ∧ x s ≤ v ∧
          ∃ J, 2 ≤ J ∧ J ≤ L ∧ IsPairSupportTransversal A v
            ((Finset.range J).image (fun j => x (s + j)))) := by
  rcases final_fork_welded h0 hcov hanchor hfail with
    hrank | ⟨x, hxmono, hxA, L, hstreet⟩
  · exact Or.inl hrank
  · have hstreet' : ∀ K : ℕ, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ v ∈ V, ∃ s, N₀ ≤ v ∧ ∃ J, 2 ≤ J ∧ J ≤ L ∧
          IsPairSupportTransversal A v ((Finset.range J).image
            (fun j => x (s + j))) := by
      intro K
      obtain ⟨V, hVcard, hV⟩ := hstreet K
      refine ⟨V, hVcard, ?_⟩
      intro v hv
      obtain ⟨hvN, s, J, hJ2, hJL, hhub, _⟩ := hV v hv
      exact ⟨s, hvN, J, hJ2, hJL, hhub⟩
    rcases target_sequence_position_dichotomy
      (W := fun v s => N₀ ≤ v ∧ ∃ J, 2 ≤ J ∧ J ≤ L ∧
        IsPairSupportTransversal A v ((Finset.range J).image
          (fun j => x (s + j)))) hstreet' with
      ⟨S₀, hnear⟩ | hfar
    · have hnear' : ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
          ∀ v ∈ V, ∃ s, s ≤ S₀ ∧ N₀ ≤ v ∧ ∃ J, 2 ≤ J ∧ J ≤ L ∧
            IsPairSupportTransversal A v ((Finset.range J).image
              (fun j => x (s + j))) := by
        intro K
        obtain ⟨V, hVcard, hV⟩ := hnear K
        refine ⟨V, hVcard, ?_⟩
        intro v hv
        obtain ⟨s, hs, hvN, J, hJ2, hJL, hhub⟩ := hV v hv
        exact ⟨s, hs, hvN, J, hJ2, hJL, hhub⟩
      obtain ⟨H, hHcard, hhall⟩ := bounded_target_sequence_fixed_hall hnear'
      obtain ⟨h, hhH, hpop⟩ := fixed_hall_popular_shift hcov hhall
      exact Or.inr (Or.inl ⟨H, h, hhH, hpop⟩)
    · refine Or.inr (Or.inr ⟨x, hxmono, hxA, L, ?_⟩)
      intro S₀ K
      obtain ⟨V, hVcard, hV⟩ := hfar S₀ K
      refine ⟨V, hVcard, ?_⟩
      intro v hv
      obtain ⟨s, hSs, hvN, J, hJ2, hJL, hhub⟩ := hV v hv
      exact ⟨hvN, s, hSs,
        target_sequence_window_below_target hcov hxmono hvN hhub,
        J, hJ2, hJL, hhub⟩

/-! ## The four columns: ghosts and members on the marching target sequence -/

theorem target_sequence_target_notMem_or_window {A : Set ℕ} {v : ℕ}
    {W : Finset ℕ} (h0 : 0 ∈ A) (h0W : 0 ∉ W)
    (hhub : IsPairSupportTransversal A v W) : v ∉ A ∨ v ∈ W := by
  by_cases hvA : v ∈ A
  · rcases hhub 0 h0 v hvA (by omega) with h | h
    · exact absurd h h0W
    · exact Or.inr h
  · exact Or.inl hvA

theorem target_sequence_member_small_part {A : Set ℕ} {v s J : ℕ}
    {x : ℕ → ℕ} (hxmono : StrictMono x) (hJ : 1 ≤ J)
    (hhub : IsPairSupportTransversal A v ((Finset.range J).image
      (fun j => x (s + j))))
    (hvW : v ∈ (Finset.range J).image (fun j => x (s + j))) :
    ∀ a ∈ A, ∀ b ∈ A, a + b = v →
      a ≤ x (s + J - 1) - x s ∨ b ≤ x (s + J - 1) - x s := by
  have hbounds : ∀ y ∈ (Finset.range J).image
      (fun j => x (s + j)), x s ≤ y ∧ y ≤ x (s + J - 1) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨j, hj, hjy⟩ := hy
    rw [Finset.mem_range] at hj
    exact ⟨hjy ▸ hxmono.monotone (by omega),
      hjy ▸ hxmono.monotone (by omega)⟩
  obtain ⟨hvlo, hvhi⟩ := hbounds v hvW
  intro a ha b hb hab
  rcases hhub a ha b hb hab with h | h
  · obtain ⟨halo, _⟩ := hbounds a h
    right; omega
  · obtain ⟨hblo, _⟩ := hbounds b h
    left; omega

theorem marching_member_dichotomy {A : Set ℕ} {N₀ L : ℕ}
    {x : ℕ → ℕ} (h0 : 0 ∈ A) (hxpos : ∀ t, 0 < x t)
    (hmarch : ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ v ∈ V, N₀ ≤ v ∧ ∃ s, S₀ ≤ s ∧ x s ≤ v ∧
        ∃ J, 2 ≤ J ∧ J ≤ L ∧ IsPairSupportTransversal A v
          ((Finset.range J).image (fun j => x (s + j)))) :
    (∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ v ∈ V, N₀ ≤ v ∧ v ∉ A ∧ ∃ s, S₀ ≤ s ∧ x s ≤ v ∧
        ∃ J, 2 ≤ J ∧ J ≤ L ∧ IsPairSupportTransversal A v
          ((Finset.range J).image (fun j => x (s + j)))) ∨
    (∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ v ∈ V, N₀ ≤ v ∧ v ∈ A ∧ ∃ s, S₀ ≤ s ∧
        ∃ J, 2 ≤ J ∧ J ≤ L ∧
          v ∈ (Finset.range J).image (fun j => x (s + j)) ∧
          IsPairSupportTransversal A v ((Finset.range J).image
            (fun j => x (s + j)))) := by
  classical
  by_cases hghost : ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ v ∈ V, N₀ ≤ v ∧ v ∉ A ∧ ∃ s, S₀ ≤ s ∧ x s ≤ v ∧
        ∃ J, 2 ≤ J ∧ J ≤ L ∧ IsPairSupportTransversal A v
          ((Finset.range J).image (fun j => x (s + j)))
  · exact Or.inl hghost
  · right
    obtain ⟨S₁, hS₁⟩ := not_forall.mp hghost
    obtain ⟨K₁, hK₁⟩ := not_forall.mp hS₁
    intro S₀ K
    obtain ⟨V, hVcard, hV⟩ := hmarch (S₀ + S₁) (K₁ + K)
    set Vg := V.filter (fun v => v ∉ A) with hVg
    by_cases hgcard : K₁ ≤ Vg.card
    · exfalso
      apply hK₁
      refine ⟨Vg, hgcard, ?_⟩
      intro v hv
      rw [hVg, Finset.mem_filter] at hv
      obtain ⟨hvV, hvnA⟩ := hv
      obtain ⟨hvN, s, hs, hxsv, J, hJ2, hJL, hhub⟩ := hV v hvV
      exact ⟨hvN, hvnA, s, by omega, hxsv, J, hJ2, hJL, hhub⟩
    · refine ⟨V \ Vg, ?_, ?_⟩
      · have h2 : (V \ Vg).card =
            V.card - (Vg ∩ V).card := Finset.card_sdiff
        have h3 : (Vg ∩ V).card ≤ Vg.card :=
          Finset.card_le_card Finset.inter_subset_left
        omega
      · intro v hv
        rw [Finset.mem_sdiff] at hv
        obtain ⟨hvV, hvng⟩ := hv
        have hvA : v ∈ A := by
          by_contra hvnA
          exact hvng (by
            rw [hVg, Finset.mem_filter]
            exact ⟨hvV, hvnA⟩)
        obtain ⟨hvN, s, hs, hxsv, J, hJ2, hJL, hhub⟩ := hV v hvV
        have h0W : (0 : ℕ) ∉ (Finset.range J).image
            (fun j => x (s + j)) := by
          intro hmem
          rw [Finset.mem_image] at hmem
          obtain ⟨j, _, hj⟩ := hmem
          exact (hxpos (s + j)).ne' hj
        rcases target_sequence_target_notMem_or_window h0 h0W hhub with
          hno | hyes
        · exact absurd hvA hno
        · exact ⟨hvN, hvA, s, by omega, J, hJ2, hJL, hyes, hhub⟩

theorem four_columns {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
      RepFree A N₀ P ∧ c ≤ P.card) ∨
    (∃ H : Finset ℕ, ∃ h ∈ H, ∀ K, ∃ V : Finset ℕ,
      K ≤ V.card ∧ ∀ v ∈ V, N₀ ≤ v ∧ h ≤ v ∧ v - h ∈ A ∧
        IsPairSupportTransversal A v H) ∨
    (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
      ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ v ∈ V, N₀ ≤ v ∧ v ∉ A ∧ ∃ s, S₀ ≤ s ∧ x s ≤ v ∧
          ∃ J, 2 ≤ J ∧ J ≤ L ∧ IsPairSupportTransversal A v
            ((Finset.range J).image (fun j => x (s + j)))) ∨
    (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
      ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ v ∈ V, N₀ ≤ v ∧ v ∈ A ∧ ∃ s, S₀ ≤ s ∧
          ∃ J, 2 ≤ J ∧ J ≤ L ∧
            v ∈ (Finset.range J).image (fun j => x (s + j)) ∧
            IsPairSupportTransversal A v ((Finset.range J).image
              (fun j => x (s + j))) ∧
            (∀ a ∈ A, ∀ b ∈ A, a + b = v →
              a ≤ x (s + J - 1) - x s ∨
              b ≤ x (s + J - 1) - x s)) := by
  rcases target_sequence_trichotomy h0 hcov hanchor hfail with
    h1 | h2 | ⟨x, hxmono, hxA, L, hmarch⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · have hxpos : ∀ t, 0 < x t := fun t => (hxA t).2
    rcases marching_member_dichotomy h0 hxpos hmarch with
      hg | hm
    · exact Or.inr (Or.inr (Or.inl ⟨x, hxmono, hxA, L, hg⟩))
    · refine Or.inr (Or.inr (Or.inr ⟨x, hxmono, hxA, L, ?_⟩))
      intro S₀ K
      obtain ⟨V, hVcard, hV⟩ := hm S₀ K
      refine ⟨V, hVcard, ?_⟩
      intro v hv
      obtain ⟨hvN, hvA, s, hs, J, hJ2, hJL, hvW, hhub⟩ :=
        hV v hv
      exact ⟨hvN, hvA, s, hs, J, hJ2, hJL, hvW, hhub,
        target_sequence_member_small_part hxmono (by omega) hhub hvW⟩

/-! ## The member target sequence conclusion: difference-blind stream or gap amplification -/

theorem member_difference_out {A : Set ℕ} {v' D : ℕ}
    (hsmall : ∀ a ∈ A, ∀ b ∈ A, a + b = v' → a ≤ D ∨ b ≤ D)
    {v : ℕ} (hvA : v ∈ A) (hDv : D < v) (hvv' : v + D < v') :
    v' - v ∉ A := by
  intro hdA
  rcases hsmall v hvA (v' - v) hdA (by omega) with h | h <;> omega

theorem difference_blind_stream {A : Set ℕ} {N₀ D₀ : ℕ}
    (hmem : ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ v ∈ V, N₀ ≤ v ∧ v ∈ A ∧
        ∀ a ∈ A, ∀ b ∈ A, a + b = v → a ≤ D₀ ∨ b ≤ D₀) :
    ∃ y : ℕ → ℕ, StrictMono y ∧
      (∀ t, y t ∈ A ∧ N₀ ≤ y t ∧ D₀ < y t ∧
        ∀ a ∈ A, ∀ b ∈ A, a + b = y t → a ≤ D₀ ∨ b ≤ D₀) ∧
      (∀ t t', t < t' → y t' - y t ∉ A) := by
  classical
  have hsupply : ∀ c, ∃ v, c ≤ v ∧ N₀ ≤ v ∧ v ∈ A ∧
      ∀ a ∈ A, ∀ b ∈ A, a + b = v → a ≤ D₀ ∨ b ≤ D₀ := by
    intro c
    obtain ⟨V, hVcard, hV⟩ := hmem (c + 1)
    have hbig : ∃ v ∈ V, c ≤ v := by
      by_contra hall
      have hsub : V ⊆ Finset.range c := by
        intro v hv
        rw [Finset.mem_range]
        by_contra hge
        exact hall ⟨v, hv, by omega⟩
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_range] at h1
      omega
    obtain ⟨v, hvV, hcv⟩ := hbig
    obtain ⟨h1, h2, h3⟩ := hV v hvV
    exact ⟨v, hcv, h1, h2, h3⟩
  choose nf hnf1 hnf2 hnf3 hnf4 using hsupply
  set y : ℕ → ℕ := fun t => Nat.rec (nf (D₀ + 1))
    (fun _ prev => nf (prev + D₀ + 1)) t with hy
  have hzero : y 0 = nf (D₀ + 1) := rfl
  have hstep : ∀ t, y (t + 1) = nf (y t + D₀ + 1) :=
    fun t => rfl
  have hgap : ∀ t, y t + D₀ < y (t + 1) := by
    intro t
    have h1 := hnf1 (y t + D₀ + 1)
    rw [hstep t]
    omega
  have hmono : StrictMono y :=
    strictMono_nat_of_lt_succ (fun t => by
      have := hgap t; omega)
  have hDlt : ∀ t, D₀ < y t := by
    intro t
    cases t with
    | zero =>
      have h1 := hnf1 (D₀ + 1)
      rw [hzero]
      omega
    | succ t =>
      have h1 := hnf1 (y t + D₀ + 1)
      rw [hstep t]
      omega
  have hcert : ∀ t, N₀ ≤ y t ∧ y t ∈ A ∧
      ∀ a ∈ A, ∀ b ∈ A, a + b = y t → a ≤ D₀ ∨ b ≤ D₀ := by
    intro t
    cases t with
    | zero =>
      rw [hzero]
      exact ⟨hnf2 _, hnf3 _, hnf4 _⟩
    | succ t =>
      rw [hstep t]
      exact ⟨hnf2 _, hnf3 _, hnf4 _⟩
  refine ⟨y, hmono, fun t => ⟨(hcert t).2.1, (hcert t).1,
    hDlt t, (hcert t).2.2⟩, ?_⟩
  intro t t' htt
  have h1 : y t + D₀ < y t' := by
    have h2 := hgap t
    have h3 : y (t + 1) ≤ y t' := by
      rcases Nat.lt_or_ge (t + 1) t' with h | h
      · exact le_of_lt (hmono h)
      · have h4 : t + 1 = t' := by omega
        rw [h4]
    omega
  exact member_difference_out (hcert t').2.2 (hcert t).2.1
    (hDlt t) h1

theorem member_target_sequence_conclusion {A : Set ℕ} {N₀ L : ℕ}
    {x : ℕ → ℕ} (hxmono : StrictMono x)
    (hmem : ∀ K : ℕ, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ v ∈ V, N₀ ≤ v ∧ v ∈ A ∧ ∃ s J, 2 ≤ J ∧ J ≤ L ∧
        ∀ a ∈ A, ∀ b ∈ A, a + b = v →
          a ≤ x (s + J - 1) - x s ∨ b ≤ x (s + J - 1) - x s) :
    (∃ D₀, ∃ y : ℕ → ℕ, StrictMono y ∧
      (∀ t, y t ∈ A ∧ N₀ ≤ y t ∧ D₀ < y t ∧
        ∀ a ∈ A, ∀ b ∈ A, a + b = y t → a ≤ D₀ ∨ b ≤ D₀) ∧
      (∀ t t', t < t' → y t' - y t ∉ A)) ∨
    (∀ G, ∃ i, G ≤ x (i + 1) - x i) := by
  classical
  have hstreet' : ∀ K : ℕ, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ v ∈ V, ∃ d, N₀ ≤ v ∧ v ∈ A ∧ ∃ s J, 2 ≤ J ∧ J ≤ L ∧
        d = x (s + J - 1) - x s ∧
        ∀ a ∈ A, ∀ b ∈ A, a + b = v →
          a ≤ x (s + J - 1) - x s ∨ b ≤ x (s + J - 1) - x s := by
    intro K
    obtain ⟨V, hVcard, hV⟩ := hmem K
    refine ⟨V, hVcard, ?_⟩
    intro v hv
    obtain ⟨hvN, hvA, s, J, hJ2, hJL, hlaw⟩ := hV v hv
    exact ⟨x (s + J - 1) - x s, hvN, hvA, s, J, hJ2, hJL,
      rfl, hlaw⟩
  rcases target_sequence_position_dichotomy
    (W := fun v d => N₀ ≤ v ∧ v ∈ A ∧ ∃ s J, 2 ≤ J ∧ J ≤ L ∧
      d = x (s + J - 1) - x s ∧
      ∀ a ∈ A, ∀ b ∈ A, a + b = v →
        a ≤ x (s + J - 1) - x s ∨ b ≤ x (s + J - 1) - x s)
    hstreet' with ⟨D₀, hnear⟩ | hfar
  · left
    have hmem' : ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ v ∈ V, N₀ ≤ v ∧ v ∈ A ∧
          ∀ a ∈ A, ∀ b ∈ A, a + b = v → a ≤ D₀ ∨ b ≤ D₀ := by
      intro K
      obtain ⟨V, hVcard, hV⟩ := hnear K
      refine ⟨V, hVcard, ?_⟩
      intro v hv
      obtain ⟨d, hdle, hvN, hvA, s, J, hJ2, hJL, hdspan,
        hlaw⟩ := hV v hv
      refine ⟨hvN, hvA, ?_⟩
      intro a ha b hb hab
      rcases hlaw a ha b hb hab with h | h
      · left; omega
      · right; omega
    obtain ⟨y, hymono, hyprop, hydiff⟩ :=
      difference_blind_stream hmem'
    exact ⟨D₀, y, hymono, hyprop, hydiff⟩
  · right
    intro G
    by_cases hG : G = 0
    · exact ⟨0, by omega⟩
    by_contra hno
    have hall : ∀ i, x (i + 1) - x i < G := by
      intro i
      by_contra hge
      exact hno ⟨i, by omega⟩
    obtain ⟨V, hVcard, hV⟩ := hfar (L * G + 1) 1
    have hVne : V.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨v, hvV⟩ := hVne
    obtain ⟨d, hdD, hvN, hvA, s, J, hJ2, hJL, hdspan, hlaw⟩ :=
      hV v hvV
    have hclaim : ∀ j, x (s + j) ≤ x s + j * (G - 1) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have h1 := hall (s + j)
        have h2 : x (s + j) ≤ x (s + j + 1) :=
          hxmono.monotone (by omega)
        have h3 : (j + 1) * (G - 1) = j * (G - 1) + (G - 1) :=
          by ring
        have h4 : s + (j + 1) = s + j + 1 := by omega
        rw [h4]
        omega
    have hkey := hclaim (J - 1)
    have h5 : s + (J - 1) = s + J - 1 := by omega
    rw [h5] at hkey
    have h1 : (J - 1) * (G - 1) ≤ (L - 1) * (G - 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : ((L - 1) + 1) * ((G - 1) + 1) =
        (L - 1) * (G - 1) + (L - 1) + (G - 1) + 1 := by ring
    have h3 : (L - 1) + 1 = L := by omega
    have h4 : (G - 1) + 1 = G := by omega
    rw [h3, h4] at h2
    omega

/-! ## The global trichotomy: one exported statement -/

theorem global_trichotomy {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ((∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
        w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g) ∧
      ((∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
        RepFree A N₀ P ∧ c ≤ P.card) ∨
      (∃ H : Finset ℕ, ∃ h ∈ H, ∀ K, ∃ V : Finset ℕ,
        K ≤ V.card ∧ ∀ v ∈ V, N₀ ≤ v ∧ h ≤ v ∧ v - h ∈ A ∧
          IsPairSupportTransversal A v H) ∨
      (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
        ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
          ∀ v ∈ V, N₀ ≤ v ∧ v ∉ A ∧ ∃ s, S₀ ≤ s ∧ x s ≤ v ∧
            ∃ J, 2 ≤ J ∧ J ≤ L ∧ IsPairSupportTransversal A v
              ((Finset.range J).image (fun j => x (s + j)))) ∨
      (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
        ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
          ∀ v ∈ V, N₀ ≤ v ∧ v ∈ A ∧ ∃ s, S₀ ≤ s ∧
            ∃ J, 2 ≤ J ∧ J ≤ L ∧
              v ∈ (Finset.range J).image (fun j => x (s + j)) ∧
              IsPairSupportTransversal A v ((Finset.range J).image
                (fun j => x (s + j))) ∧
              (∀ a ∈ A, ∀ b ∈ A, a + b = v →
                a ≤ x (s + J - 1) - x s ∨
                b ≤ x (s + J - 1) - x s)))) ∨
    (∃ g₀, g₀ ∈ A ∧ ∀ c ∈ A, 0 < c → c ≠ g₀ →
      IsPairSupportTransversal A (2 * c) ({c, g₀} : Finset ℕ)) ∨
    (∃ g₀, (∀ c ∈ A, 0 < c → c ≠ g₀ → ∀ w ∈ A, ∀ w' ∈ A,
        w + w' = 2 * c → w = c ∧ w' = c) ∧
      (∀ c ∈ A, 0 < c → c ≠ g₀ →
        IsPairSupportTransversal A (2 * c) ({c} : Finset ℕ)) ∧
      (∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
        ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) ∧
      (∀ a d, 0 < d → a ∈ A → a + d ∈ A → a + 2 * d ∈ A →
        a + d = g₀ ∨ a + d = 0)) := by
  rcases anchor_dichotomy (A := A) with hanchor | ⟨g₀, hroute⟩
  · exact Or.inl ⟨hanchor,
      four_columns h0 hcov
        (streamSurvives_of_anchor h0 hcov hanchor) hfail⟩
  · rcases no_anchor_central_or_member hroute with hg | hcentral
    · exact Or.inr (Or.inl ⟨g₀, hg, hroute⟩)
    · exact Or.inr (Or.inr ⟨g₀, hcentral,
        central_branch_singleton_support_transversals hcentral,
        central_branch_hmin hcentral,
        central_branch_no_three_AP hcentral⟩)

/-! ## The routed collapse: branch II has no interior -/

theorem routed_collapse {A : Set ℕ} {g₀ : ℕ} (hg : g₀ ∈ A)
    (hroute : ∀ c ∈ A, 0 < c → c ≠ g₀ →
      IsPairSupportTransversal A (2 * c) ({c, g₀} : Finset ℕ)) :
    ((∀ N, ∃ c ∈ A, N ≤ c ∧ c ≠ g₀ ∧ g₀ ≤ 2 * c ∧
        (2 * c - g₀) ∈ A ∧ 2 * c - g₀ ≠ c) ∧
      (∀ g, g ≠ g₀ → ∃ c ∈ A, 0 < c ∧ c ≠ g ∧
        ∃ w ∈ A, ∃ w' ∈ A, w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧
          w' ≠ g)) ∨
    (∃ C₀, (∀ c ∈ A, C₀ ≤ c → c ≠ g₀ → ∀ w ∈ A, ∀ w' ∈ A,
        w + w' = 2 * c → w = c ∧ w' = c) ∧
      (∀ c ∈ A, C₀ ≤ c → c ≠ g₀ →
        IsPairSupportTransversal A (2 * c) ({c} : Finset ℕ)) ∧
      (∀ B ⊆ A, B.Infinite → ¬∃ N₂, ∀ n, N₂ ≤ n →
        ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) ∧
      (∀ a d, 0 < d → a ∈ A → a + d ∈ A → a + 2 * d ∈ A →
        a + d = g₀ ∨ a + d < C₀)) := by
  classical
  by_cases hlad : ∀ N, ∃ c ∈ A, N ≤ c ∧ 0 < c ∧ c ≠ g₀ ∧
      ∃ w ∈ A, ∃ w' ∈ A, w + w' = 2 * c ∧ w ≠ c
  · left
    have hlad' : ∀ N, ∃ c ∈ A, N ≤ c ∧ c ≠ g₀ ∧ g₀ ≤ 2 * c ∧
        (2 * c - g₀) ∈ A ∧ 2 * c - g₀ ≠ c := by
      intro N
      obtain ⟨c, hcA, hN, hcpos, hcg, w, hwA, w', hw'A, hsum,
        hwc⟩ := hlad N
      have hw'c : w' ≠ c := by omega
      have hg2c : g₀ ≤ 2 * c ∧ (2 * c - g₀) ∈ A := by
        rcases hroute c hcA hcpos hcg w hwA w' hw'A hsum with
          h | h
        · rcases Finset.mem_insert.1 h with h' | h'
          · exact absurd h' hwc
          · rw [Finset.mem_singleton] at h'
            subst h'
            refine ⟨by omega, ?_⟩
            have h2 : 2 * c - w = w' := by omega
            rw [h2]
            exact hw'A
        · rcases Finset.mem_insert.1 h with h' | h'
          · exact absurd h' hw'c
          · rw [Finset.mem_singleton] at h'
            subst h'
            refine ⟨by omega, ?_⟩
            have h2 : 2 * c - w' = w := by omega
            rw [h2]
            exact hwA
      exact ⟨c, hcA, hN, hcg, hg2c.1, hg2c.2, by omega⟩
    refine ⟨hlad', ?_⟩
    intro g hgg
    obtain ⟨c, hcA, hN, hcg, hg2c, hpA, hpc⟩ :=
      hlad' (g + g₀ + 1)
    exact ⟨c, hcA, by omega, by omega, g₀, hg, 2 * c - g₀,
      hpA, by omega, by omega, by omega, by omega⟩
  · right
    obtain ⟨N₁, hN₁⟩ := not_forall.mp hlad
    refine ⟨N₁ + g₀ + 1, ?_, ?_, ?_, ?_⟩
    · intro c hcA hCc hcg w hwA w' hw'A hsum
      by_cases hwc : w = c
      · exact ⟨hwc, by omega⟩
      · exact absurd ⟨c, hcA, by omega, by omega, hcg, w, hwA,
          w', hw'A, hsum, hwc⟩ hN₁
    · intro c hcA hCc hcg w hwA w' hw'A hsum
      by_cases hwc : w = c
      · exact Or.inl (by simp [hwc])
      · exact absurd ⟨c, hcA, by omega, by omega, hcg, w, hwA,
          w', hw'A, hsum, hwc⟩ hN₁
    · rintro B hBA hBinf ⟨N₂, hN₂⟩
      obtain ⟨b, hbB, hbgt⟩ := hBinf.exists_gt
        (N₂ + N₁ + g₀ + 1)
      have hbA := hBA hbB
      obtain ⟨x, hx, y, hy, hxB, hyB, hxy⟩ :=
        hN₂ (2 * b) (by omega)
      have hxb : x = b := by
        by_cases hwc : x = b
        · exact hwc
        · exact absurd ⟨b, hbA, by omega, by omega, by omega,
            x, hx, y, hy, hxy, hwc⟩ hN₁
      exact hxB (hxb ▸ hbB)
    · intro a d hd haA hadA ha2dA
      by_contra hno
      push Not at hno
      obtain ⟨hgne, hC⟩ := hno
      have hsum : a + (a + 2 * d) = 2 * (a + d) := by omega
      have hac : a ≠ a + d := by omega
      exact absurd ⟨a + d, hadA, by omega, by omega, hgne,
        a, haA, a + 2 * d, ha2dA, hsum, hac⟩ hN₁

theorem collapsed_trichotomy {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ((∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
        w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g) ∧
      ((∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
        RepFree A N₀ P ∧ c ≤ P.card) ∨
      (∃ H : Finset ℕ, ∃ h ∈ H, ∀ K, ∃ V : Finset ℕ,
        K ≤ V.card ∧ ∀ v ∈ V, N₀ ≤ v ∧ h ≤ v ∧ v - h ∈ A ∧
          IsPairSupportTransversal A v H) ∨
      (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
        ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
          ∀ v ∈ V, N₀ ≤ v ∧ v ∉ A ∧ ∃ s, S₀ ≤ s ∧ x s ≤ v ∧
            ∃ J, 2 ≤ J ∧ J ≤ L ∧ IsPairSupportTransversal A v
              ((Finset.range J).image (fun j => x (s + j)))) ∨
      (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
        ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
          ∀ v ∈ V, N₀ ≤ v ∧ v ∈ A ∧ ∃ s, S₀ ≤ s ∧
            ∃ J, 2 ≤ J ∧ J ≤ L ∧
              v ∈ (Finset.range J).image (fun j => x (s + j)) ∧
              IsPairSupportTransversal A v ((Finset.range J).image
                (fun j => x (s + j))) ∧
              (∀ a ∈ A, ∀ b ∈ A, a + b = v →
                a ≤ x (s + J - 1) - x s ∨
                b ≤ x (s + J - 1) - x s)))) ∨
    (∃ g₀, g₀ ∈ A ∧
      (∀ N, ∃ c ∈ A, N ≤ c ∧ c ≠ g₀ ∧ g₀ ≤ 2 * c ∧
        (2 * c - g₀) ∈ A ∧ 2 * c - g₀ ≠ c) ∧
      (∀ g, g ≠ g₀ → ∃ c ∈ A, 0 < c ∧ c ≠ g ∧
        ∃ w ∈ A, ∃ w' ∈ A, w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧
          w' ≠ g)) ∨
    (∃ g₀ C₀, (∀ c ∈ A, C₀ ≤ c → c ≠ g₀ → ∀ w ∈ A, ∀ w' ∈ A,
        w + w' = 2 * c → w = c ∧ w' = c) ∧
      (∀ c ∈ A, C₀ ≤ c → c ≠ g₀ →
        IsPairSupportTransversal A (2 * c) ({c} : Finset ℕ)) ∧
      (∀ B ⊆ A, B.Infinite → ¬∃ N₂, ∀ n, N₂ ≤ n →
        ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) ∧
      (∀ a d, 0 < d → a ∈ A → a + d ∈ A → a + 2 * d ∈ A →
        a + d = g₀ ∨ a + d < C₀)) := by
  rcases global_trichotomy h0 hcov hfail with
    ⟨hanch, hlanes⟩ | ⟨g₀, hg, hroute⟩ |
    ⟨g₀, hcen, hhub, hmin, hap⟩
  · exact Or.inl ⟨hanch, hlanes⟩
  · rcases routed_collapse hg hroute with
      ⟨hl, ha⟩ | ⟨C₀, h1, h2, h3, h4⟩
    · exact Or.inr (Or.inl ⟨g₀, hg, hl, ha⟩)
    · exact Or.inr (Or.inr ⟨g₀, C₀, h1, h2, h3, h4⟩)
  · refine Or.inr (Or.inr ⟨g₀, 1, ?_, ?_, hmin, ?_⟩)
    · intro c hcA hCc hcg
      exact hcen c hcA (by omega) hcg
    · intro c hcA hCc hcg
      exact hhub c hcA (by omega) hcg
    · intro a d hd h1 h2 h3
      rcases hap a d hd h1 h2 h3 with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)

/-! ## The g₀-tower: what lives in the hole -/

theorem almost_anchored_privateStream
    {A : Set ℕ} {N₀ g₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hstream : ∀ N, ∃ a m, N ≤ m ∧ 0 < a ∧ IsPrivateTriple A a m)
    (hanchor' : ∀ g, g ≠ g₀ → ∃ c ∈ A, 0 < c ∧ c ≠ g ∧
      ∃ w ∈ A, ∃ w' ∈ A,
        w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g) :
    (∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n) ∨
    (0 < g₀ ∧ ∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A g₀ m) := by
  classical
  by_cases hro : ∀ (F : Finset ℕ) (N : ℕ), ∃ a m, N ≤ m ∧ 0 < a ∧
      a ∉ F ∧ IsPrivateTriple A a m
  · -- rotating case: every finite forbidden set is dodged
    refine Or.inl ?_
    obtain ⟨c, hc, hc0, -, w, hwA, w', hw'A, hww, hwc, -, -⟩ :=
      hanchor' (g₀ + 1) (by omega)
    choose pa pm hpm hpa0 hpaF hppriv using hro
    set F₀ : Finset ℕ := {c, w, w'} with hF₀
    set nxt : ℕ × Finset ℕ → ℕ × Finset ℕ := fun s =>
      (pm s.2 (8 * s.1 + 9 * N₀ + 21) - pa s.2 (8 * s.1 + 9 * N₀ + 21),
        insert
          (pm s.2 (8 * s.1 + 9 * N₀ + 21) -
            pa s.2 (8 * s.1 + 9 * N₀ + 21)) s.2) with hnxt
    set prev : ℕ → ℕ × Finset ℕ := fun k =>
      Nat.rec (c + N₀, F₀) (fun _ p => nxt p) k with hprev
    set L : ℕ → ℕ := fun k => (prev (k + 1)).1 with hLdef
    set d : ℕ → ℕ := fun k =>
      pa (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21) with hddef
    have hprevS : ∀ k, prev (k + 1) = nxt (prev k) := fun _ => rfl
    have hLeq : ∀ k, L k =
        pm (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21) -
          pa (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21) := by
      intro k
      simp only [hLdef, hprevS k, hnxt]
    have hFeq : ∀ k, (prev (k + 1)).2 = insert (L k) (prev k).2 := by
      intro k
      simp only [hLdef, hprevS k, hnxt]
    have hdeq : ∀ k, d k =
        pa (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21) := by
      intro k
      simp only [hddef]
    -- per-step facts
    have hstep : ∀ k, d k ∉ (prev k).2 ∧ 0 < d k ∧ L k ∈ A ∧
        (prev k).1 < L k ∧ 2 * (prev k).1 + N₀ < L k ∧
        ∀ z ∈ A, z ≠ d k → z + N₀ < L k → L k - z ∈ A := by
      intro k
      have hpriv := hppriv (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21)
      have hm := hpm (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21)
      have ha0 := hpa0 (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21)
      have hlow : ¬ (4 * (pm (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21) -
          pa (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21)) +
            4 * N₀ + 20 ≤
          pm (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21)) :=
        fun h => hpriv.corep_lower h0 hcov ha0 h
      obtain ⟨M, hMA, hMe⟩ := hpriv.corep_mem h0 hcov ha0 (by omega)
      constructor
      · rw [hdeq]
        exact hpaF _ _
      refine ⟨by rw [hdeq]; exact ha0, ?_, ?_, ?_, ?_⟩
      · rw [hLeq]
        have hMeq : M = pm (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21) -
            pa (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21) := by omega
        exact hMeq ▸ hMA
      · rw [hLeq]; omega
      · rw [hLeq]; omega
      · intro z hz hza hzM
        rw [hLeq] at hzM ⊢
        rw [hdeq] at hza
        obtain ⟨v, hvA, hvs⟩ :=
          hpriv.mirror_of_ne h0 hcov hz (by omega) (by omega) hza
        have hve : v = pm (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21) -
            pa (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21) - z := by
          omega
        exact hve ▸ hvA
    -- state invariants
    have hF₀sub : ∀ k, F₀ ⊆ (prev k).2 := by
      intro k
      induction k with
      | zero =>
          have hp0 : prev 0 = (c + N₀, F₀) := rfl
          rw [hp0]
      | succ k ih =>
          rw [hFeq k]
          exact ih.trans (Finset.subset_insert _ _)
    have hLmem : ∀ j k, j < k → L j ∈ (prev k).2 := by
      intro j k hjk
      induction k with
      | zero => omega
      | succ k ih =>
          rw [hFeq k]
          rcases Nat.lt_or_ge j k with h | h
          · exact Finset.mem_insert_of_mem (ih h)
          · have hjeq : j = k := by omega
            subst hjeq
            exact Finset.mem_insert_self _ _
    have hprev1 : ∀ k, (prev (k + 1)).1 = L k := fun _ => rfl
    have hgrow : ∀ k, 2 * L k < L (k + 1) := by
      intro k
      have h1 := (hstep (k + 1)).2.2.2.2.1
      rw [hprev1] at h1
      omega
    have hcL : c + N₀ < L 0 := by
      have h1 := (hstep 0).2.2.2.2.1
      have h2 : (prev 0).1 = c + N₀ := rfl
      omega
    have hmono : StrictMono L := by
      apply strictMono_nat_of_lt_succ
      intro k
      have h1 := hgrow k
      have h2 := (hstep k).2.2.2.1
      omega
    have hcF : ∀ k, c ∈ (prev k).2 :=
      fun k => hF₀sub k (by simp [hF₀])
    have hwF : ∀ k, w ∈ (prev k).2 :=
      fun k => hF₀sub k (by simp [hF₀])
    have hw'F : ∀ k, w' ∈ (prev k).2 :=
      fun k => hF₀sub k (by simp [hF₀])
    exact surviving_deletion_of_geometric_rotatingDefects L d h0 hcov
      hmono (fun k => (hstep k).2.2.2.2.2) (fun k => (hstep k).2.2.1)
      hgrow hc hc0 hcL hwA hw'A hww hwc
      (fun k h => (hstep k).1 (h ▸ hcF k))
      (fun k h => (hstep k).1 (h ▸ hwF k))
      (fun k h => (hstep k).1 (h ▸ hw'F k))
      (fun j k hjk h => (hstep k).1 (h ▸ hLmem j k hjk))
  · -- recurring case: all late required elements in one finite set
    push Not at hro
    obtain ⟨F, N₁, hF⟩ := hro
    by_cases hrec : ∃ g ∈ F, 0 < g ∧
        ∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A g m
    · obtain ⟨g, hgF, hg0, hgstream⟩ := hrec
      by_cases hgg₀ : g = g₀
      · subst hgg₀
        exact Or.inr ⟨hg0, hgstream⟩
      · obtain ⟨c, hc, hc0, hcg, w, hwA, w', hw'A, hww, hwc, hwg,
          hw'g⟩ := hanchor' g hgg₀
        exact Or.inl (surviving_deletion_of_cofinal_fixedRequiredElement'
          h0 hcov hg0 hgstream hc hc0 hcg
          ⟨w, hwA, w', hw'A, hww, hwc, hwg, hw'g⟩)
    · push Not at hrec
      have hbnd : ∀ g, ∃ Ng, ∀ m, Ng ≤ m → g ∈ F → 0 < g →
          ¬ IsPrivateTriple A g m := by
        intro g
        by_cases hgF : g ∈ F
        · by_cases hg0 : 0 < g
          · obtain ⟨Ng', hNg'⟩ := hrec g hgF hg0
            exact ⟨Ng', fun m hm _ _ => hNg' m hm⟩
          · exact ⟨0, fun m _ _ h0g => absurd h0g hg0⟩
        · exact ⟨0, fun m _ hgF' _ => absurd hgF' hgF⟩
      choose Ng hNg using hbnd
      obtain ⟨a, m, hm, ha0, hpriv⟩ :=
        hstream (max N₁ (F.sup Ng))
      have haF : a ∈ F := by
        by_contra haF
        exact hF a m (le_trans (le_max_left _ _) hm) ha0 haF hpriv
      have hbound : Ng a ≤ m :=
        le_trans (le_trans (Finset.le_sup haF) (le_max_right _ _)) hm
      exact absurd hpriv (hNg a m hbound haF ha0)

theorem g0_tower {A : Set ℕ} {N₀ g₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) (hg0 : 0 < g₀)
    (hstream : ∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A g₀ m) :
    ∀ K, ∃ L, K < L ∧ L ∈ A ∧ N₀ ≤ g₀ + L ∧
      IsPairSupportTransversal A (g₀ + L) ({g₀} : Finset ℕ) ∧
      ∀ z ∈ A, z ≠ g₀ → z + N₀ < L → L - z ∈ A := by
  intro K
  obtain ⟨m, hm, hpriv⟩ := hstream (4 * K + 5 * N₀ + 21)
  have hMlow : ¬ (4 * (m - g₀) + 4 * N₀ + 20 ≤ m) :=
    fun h => hpriv.corep_lower h0 hcov hg0 h
  obtain ⟨M, hMA, hMe⟩ := hpriv.corep_mem h0 hcov hg0 (by omega)
  refine ⟨M, by omega, hMA, by omega, ?_, ?_⟩
  · intro u hu v hv huv
    rcases hpriv.2 u hu v hv 0 h0 (by omega) with h | h | h
    · exact Or.inl (by simp [h])
    · exact Or.inr (by simp [h])
    · omega
  · intro z hz hzg hzM
    obtain ⟨w, hwA, hws⟩ :=
      hpriv.mirror_of_ne h0 hcov hz (by omega) (by omega) hzg
    have hwe : w = M - z := by omega
    exact hwe ▸ hwA

theorem almost_anchored_singleton_support_transversals {A : Set ℕ} {N₀ g₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor' : ∀ g, g ≠ g₀ → ∃ c ∈ A, 0 < c ∧ c ≠ g ∧
      ∃ w ∈ A, ∃ w' ∈ A,
        w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hsing : ∀ N, ∃ n, N ≤ n ∧ ∃ a, 0 < a ∧ IsRepSupportTransversal A n {a}) :
    0 < g₀ ∧ ∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A g₀ m := by
  have hstream : ∀ N, ∃ a m, N ≤ m ∧ 0 < a ∧
      IsPrivateTriple A a m := by
    intro N
    obtain ⟨n, hn, a, ha, hhub⟩ := hsing (max N N₀)
    exact ⟨a, n, le_trans (le_max_left _ _) hn, ha,
      privateTriple_of_singleton_support_transversal h0 hcov
        (le_trans (le_max_right _ _) hn) hhub⟩
  rcases almost_anchored_privateStream h0 hcov hstream hanchor'
    with ⟨B, hBsub, hBinf, hsurv⟩ | htower
  · exfalso
    refine hfail B hBsub hBinf ⟨N₀, fun n hn => ?_⟩
    obtain ⟨x, hx, y, hy, z, hz, hxB, hyB, hzB, hsum⟩ :=
      hsurv n hn
    refine ⟨![x, y, z], ?_, ?_⟩
    · intro i
      match i with
      | 0 => exact ⟨hx, hxB⟩
      | 1 => exact ⟨hy, hyB⟩
      | 2 => exact ⟨hz, hzB⟩
    · simpa [Fin.sum_univ_three] using hsum
  · exact htower

theorem g0_translate_law {A : Set ℕ} {N₀ g₀ : ℕ}
    (hg0 : 0 < g₀)
    (htower : ∀ K, ∃ L, K < L ∧ L ∈ A ∧ N₀ ≤ g₀ + L ∧
      IsPairSupportTransversal A (g₀ + L) ({g₀} : Finset ℕ) ∧
      ∀ z ∈ A, z ≠ g₀ → z + N₀ < L → L - z ∈ A) :
    ∀ z ∈ A, 0 < z → z ≠ g₀ → g₀ + z ∉ A := by
  intro z hzA hz0 hzg hmem
  obtain ⟨L, hKL, hLA, hLN, hhub, hmir⟩ :=
    htower (z + N₀ + g₀ + 1)
  have hmzA : L - z ∈ A := hmir z hzA hzg (by omega)
  rcases hhub (g₀ + z) hmem (L - z) hmzA (by omega) with h | h
  · rw [Finset.mem_singleton] at h
    omega
  · rw [Finset.mem_singleton] at h
    omega

theorem routed_tower_mirror_lock {A : Set ℕ} {N₀ g₀ c : ℕ}
    (hroute : ∀ c' ∈ A, 0 < c' → c' ≠ g₀ →
      IsPairSupportTransversal A (2 * c') ({c', g₀} : Finset ℕ))
    (hcA : c ∈ A) (hcg : c ≠ g₀) (hg2c : g₀ ≤ 2 * c)
    (hqA : (2 * c - g₀) ∈ A) (hqc : 2 * c - g₀ ≠ c)
    {L : ℕ} (hLA : L ∈ A) (hLbig : 2 * c + g₀ + N₀ + 1 < L)
    (hmir : ∀ z ∈ A, z ≠ g₀ → z + N₀ < L → L - z ∈ A) :
    L - g₀ ∉ A := by
  intro hLg
  have hmc : L - c ∈ A := hmir c hcA hcg (by omega)
  have hmq : L - (2 * c - g₀) ∈ A :=
    hmir (2 * c - g₀) hqA (by omega) (by omega)
  have hsum : (L - (2 * c - g₀)) + (L - g₀) = 2 * (L - c) := by
    omega
  have hown : 0 < L - c := by omega
  have hog : L - c ≠ g₀ := by omega
  rcases hroute (L - c) hmc hown hog
    (L - (2 * c - g₀)) hmq (L - g₀) hLg hsum with h | h
  · rcases Finset.mem_insert.1 h with h' | h'
    · omega
    · rw [Finset.mem_singleton] at h'
      omega
  · rcases Finset.mem_insert.1 h with h' | h'
    · omega
    · rw [Finset.mem_singleton] at h'
      omega

theorem g0_tower_model {A : Set ℕ} {N₀ g₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hroute : ∀ c ∈ A, 0 < c → c ≠ g₀ →
      IsPairSupportTransversal A (2 * c) ({c, g₀} : Finset ℕ))
    (hladder : ∀ N, ∃ c ∈ A, N ≤ c ∧ c ≠ g₀ ∧ g₀ ≤ 2 * c ∧
      (2 * c - g₀) ∈ A ∧ 2 * c - g₀ ≠ c)
    (hanchor' : ∀ g, g ≠ g₀ → ∃ c ∈ A, 0 < c ∧ c ≠ g ∧
      ∃ w ∈ A, ∃ w' ∈ A,
        w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hsing : ∀ N, ∃ n, N ≤ n ∧ ∃ a, 0 < a ∧ IsRepSupportTransversal A n {a}) :
    0 < g₀ ∧
    (∀ K, ∃ L, K < L ∧ L ∈ A ∧ N₀ ≤ g₀ + L ∧
      IsPairSupportTransversal A (g₀ + L) ({g₀} : Finset ℕ) ∧
      (∀ z ∈ A, z ≠ g₀ → z + N₀ < L → L - z ∈ A) ∧
      L - g₀ ∉ A) ∧
    (∀ z ∈ A, 0 < z → z ≠ g₀ → g₀ + z ∉ A) := by
  obtain ⟨hg0, hstream⟩ := almost_anchored_singleton_support_transversals
    h0 hcov hanchor' hfail hsing
  have htower := g0_tower h0 hcov hg0 hstream
  obtain ⟨c, hcA, hcN, hcg, hg2c, hqA, hqc⟩ := hladder 1
  refine ⟨hg0, ?_, g0_translate_law hg0 htower⟩
  intro K
  obtain ⟨L, hKL, hLA, hLN, hhub, hmir⟩ :=
    htower (K + 2 * c + g₀ + N₀ + 2)
  exact ⟨L, by omega, hLA, hLN, hhub, hmir,
    routed_tower_mirror_lock hroute hcA hcg hg2c hqA hqc hLA
      (by omega) hmir⟩

theorem g0_tower_engine {A : Set ℕ} {N₀ g₀ c u u' : ℕ}
    (L : ℕ → ℕ)
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hmono : StrictMono L)
    (hgrow : ∀ k, 2 * L k < L (k + 1))
    (hTLk : ∀ k, 2 * c + g₀ + N₀ + 1 < L k)
    (hmemL : ∀ k, L k ∈ A)
    (hmirL : ∀ k, ∀ z ∈ A, z ≠ g₀ → z + N₀ < L k → L k - z ∈ A)
    (hgA : g₀ ∈ A) (hcA : c ∈ A) (hcg : c ≠ g₀)
    (huA : u ∈ A) (hu'A : u' ∈ A) (huu : u + u' = 2 * c + g₀)
    (hug : u ≠ g₀) (hu'g : u' ≠ g₀) (huc : u ≠ c)
    (hu'c : u' ≠ c) :
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
  classical
  have hdiff : ∀ i j, i < j → L 0 + L i < L j :=
    fun i j h => geometric_level_separation hmono hgrow h
  set f : ℕ → ℕ := fun k => L (2 * k + 2) - c with hf
  have hfA : ∀ k, f k ∈ A := by
    intro k
    have h1 := hTLk (2 * k + 2)
    exact hmirL _ c hcA hcg (by omega)
  have hfinj : Function.Injective f := by
    intro i j hij
    simp only [hf] at hij
    have h1 := hTLk (2 * i + 2)
    have h2 := hTLk (2 * j + 2)
    have h3 : L (2 * i + 2) = L (2 * j + 2) := by omega
    have h4 := hmono.injective h3
    omega
  have hBsub : Set.range f ⊆ A := by
    rintro v ⟨k, rfl⟩
    exact hfA k
  have h0B : (0 : ℕ) ∉ Set.range f := by
    rintro ⟨r, hr⟩
    simp only [hf] at hr
    have := hTLk (2 * r + 2)
    omega
  have hg₀B : g₀ ∉ Set.range f := by
    rintro ⟨r, hr⟩
    simp only [hf] at hr
    have := hTLk (2 * r + 2)
    omega
  have hgapB : ∀ i j, j < i → L i - L j ∉ Set.range f := by
    rintro i j hji ⟨r, hr⟩
    simp only [hf] at hr
    have hLj : L j < L i := hmono hji
    have e : L (2 * r + 2) + L j = L i + c := by
      have := hTLk (2 * r + 2); omega
    rcases Nat.lt_trichotomy i (2 * r + 2) with h | h | h
    · have h6 := hdiff i (2 * r + 2) h
      have h7 := hTLk 0
      omega
    · rw [h] at e
      have h6 := hTLk j
      omega
    · have h2 : L (2 * r + 2) ≤ L (i - 1) :=
        hmono.monotone (by omega)
      have h3 : L j ≤ L (i - 1) := hmono.monotone (by omega)
      have h4 := hgrow (i - 1)
      have h5 : i - 1 + 1 = i := by omega
      rw [h5] at h4
      omega
  have hnearB : ∀ k v, v ≤ 2 * c + g₀ → v ≠ c →
      L k - v ∉ Set.range f := by
    rintro k v hvT hvc ⟨r, hr⟩
    simp only [hf] at hr
    have hvL : v < L k := by have := hTLk k; omega
    have e : L (2 * r + 2) + v = L k + c := by
      have := hTLk (2 * r + 2); omega
    rcases Nat.lt_trichotomy k (2 * r + 2) with h | h | h
    · have h6 := hdiff k (2 * r + 2) h
      have h7 := hTLk k
      have h8 := hTLk 0
      omega
    · rw [h] at e
      omega
    · have h6 := hdiff (2 * r + 2) k h
      have h7 := hTLk 0
      omega
  refine ⟨Set.range f, hBsub,
    Set.infinite_range_of_injective hfinj, ?_⟩
  intro n hn
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov n hn
  by_cases hxB : x ∈ Set.range f
  · obtain ⟨i, hix⟩ := hxB
    simp only [hf] at hix
    by_cases hyB : y ∈ Set.range f
    · obtain ⟨j, hjy⟩ := hyB
      simp only [hf] at hjy
      have hiT := hTLk (2 * i + 2)
      have hjT := hTLk (2 * j + 2)
      have hp₁A : L (2 * i + 2) - u ∈ A :=
        hmirL _ u huA hug (by omega)
      have hp₂A : L (2 * j + 2) - u' ∈ A :=
        hmirL _ u' hu'A hu'g (by omega)
      refine ⟨_, hp₁A, _, hp₂A, g₀, hgA,
        hnearB (2 * i + 2) u (by omega) huc,
        hnearB (2 * j + 2) u' (by omega) hu'c, hg₀B, ?_⟩
      omega
    · have hiT := hTLk (2 * i + 2)
      have hoT := hTLk (2 * i + 1)
      have hp₁A : L (2 * i + 1) - c ∈ A :=
        hmirL _ c hcA hcg (by omega)
      have hp₂A : L (2 * i + 2) - L (2 * i + 1) ∈ A := by
        have h1 := hgrow (2 * i + 1)
        have he : 2 * i + 1 + 1 = 2 * i + 2 := by omega
        rw [he] at h1
        exact hmirL (2 * i + 2) (L (2 * i + 1))
          (hmemL (2 * i + 1)) (by omega) (by omega)
      have hp₁B : L (2 * i + 1) - c ∉ Set.range f := by
        rintro ⟨r, hr⟩
        simp only [hf] at hr
        have h1 := hTLk (2 * r + 2)
        have h2 : L (2 * r + 2) = L (2 * i + 1) := by omega
        have h3 := hmono.injective h2
        omega
      refine ⟨_, hp₁A, _, hp₂A, y, hy, hp₁B,
        hgapB (2 * i + 2) (2 * i + 1) (by omega), hyB, ?_⟩
      have h0' : 2 * i + 1 < 2 * i + 2 := by omega
      have h1 := le_of_lt (hmono h0')
      omega
  · by_cases hyB : y ∈ Set.range f
    · obtain ⟨j, hjy⟩ := hyB
      simp only [hf] at hjy
      have hjT := hTLk (2 * j + 2)
      have hoT := hTLk (2 * j + 1)
      have hp₁A : L (2 * j + 1) - c ∈ A :=
        hmirL _ c hcA hcg (by omega)
      have hp₂A : L (2 * j + 2) - L (2 * j + 1) ∈ A := by
        have h1 := hgrow (2 * j + 1)
        have he : 2 * j + 1 + 1 = 2 * j + 2 := by omega
        rw [he] at h1
        exact hmirL (2 * j + 2) (L (2 * j + 1))
          (hmemL (2 * j + 1)) (by omega) (by omega)
      have hp₁B : L (2 * j + 1) - c ∉ Set.range f := by
        rintro ⟨r, hr⟩
        simp only [hf] at hr
        have h1 := hTLk (2 * r + 2)
        have h2 : L (2 * r + 2) = L (2 * j + 1) := by omega
        have h3 := hmono.injective h2
        omega
      refine ⟨_, hp₁A, _, hp₂A, x, hx, hp₁B,
        hgapB (2 * j + 2) (2 * j + 1) (by omega), hxB, ?_⟩
      have h0' : 2 * j + 1 < 2 * j + 2 := by omega
      have h1 := le_of_lt (hmono h0')
      omega
    · exact ⟨x, hx, y, hy, 0, h0, hxB, hyB, h0B, by omega⟩

theorem g0_tower_impossible {A : Set ℕ} {N₀ g₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) (hg0 : 0 < g₀)
    (hgA : g₀ ∈ A)
    (htower : ∀ K, ∃ L, K < L ∧ L ∈ A ∧ N₀ ≤ g₀ + L ∧
      IsPairSupportTransversal A (g₀ + L) ({g₀} : Finset ℕ) ∧
      ∀ z ∈ A, z ≠ g₀ → z + N₀ < L → L - z ∈ A)
    {c : ℕ} (hcA : c ∈ A) (hcN : N₀ + g₀ + 1 ≤ c)
    (hcg : c ≠ g₀) (hqA : (2 * c - g₀) ∈ A) :
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
  classical
  have htrans := g0_translate_law hg0 htower
  have hqpos : 0 < 2 * c - g₀ := by omega
  have hqg : 2 * c - g₀ ≠ g₀ := by omega
  have h2c : 2 * c ∉ A := by
    have h1 := htrans (2 * c - g₀) hqA hqpos hqg
    have h2 : g₀ + (2 * c - g₀) = 2 * c := by omega
    rw [h2] at h1
    exact h1
  have hcg₀ : c + g₀ ∉ A := by
    have h1 := htrans c hcA (by omega) hcg
    have h2 : g₀ + c = c + g₀ := by omega
    rw [h2] at h1
    exact h1
  obtain ⟨u, huA, u', hu'A, huu⟩ := hcov (2 * c + g₀) (by omega)
  have hug : u ≠ g₀ := by
    intro h
    have h1 : u' = 2 * c := by omega
    exact h2c (h1 ▸ hu'A)
  have hu'g : u' ≠ g₀ := by
    intro h
    have h1 : u = 2 * c := by omega
    exact h2c (h1 ▸ huA)
  have huc : u ≠ c := by
    intro h
    have h1 : u' = c + g₀ := by omega
    exact hcg₀ (h1 ▸ hu'A)
  have hu'c : u' ≠ c := by
    intro h
    have h1 : u = c + g₀ := by omega
    exact hcg₀ (h1 ▸ huA)
  have hlev : ∀ K, ∃ M, K < M ∧ M ∈ A ∧
      ∀ z ∈ A, z ≠ g₀ → z + N₀ < M → M - z ∈ A := by
    intro K
    obtain ⟨M, h1, h2, _, _, h5⟩ := htower K
    exact ⟨M, h1, h2, h5⟩
  choose next hnext hnextMem hnextMir using hlev
  let L : ℕ → ℕ := fun k =>
    Nat.rec (next (2 * c + g₀ + N₀ + 1))
      (fun _ prev => next (2 * prev)) k
  have hL0 : L 0 = next (2 * c + g₀ + N₀ + 1) := rfl
  have hLs : ∀ k, L (k + 1) = next (2 * L k) := fun _ => rfl
  have hgrow : ∀ k, 2 * L k < L (k + 1) := by
    intro k
    rw [hLs]
    exact hnext (2 * L k)
  have hTL : 2 * c + g₀ + N₀ + 1 < L 0 := by
    rw [hL0]
    exact hnext (2 * c + g₀ + N₀ + 1)
  have hmono : StrictMono L := by
    apply strictMono_nat_of_lt_succ
    intro k
    have h1 := hgrow k
    have h2 : 0 < L k := by
      induction k with
      | zero => omega
      | succ k ih => have := hgrow k; omega
    omega
  have hTLk : ∀ k, 2 * c + g₀ + N₀ + 1 < L k := by
    intro k
    have := hmono.monotone (Nat.zero_le k)
    omega
  have hmemL : ∀ k, L k ∈ A := by
    intro k
    cases k with
    | zero => exact hnextMem (2 * c + g₀ + N₀ + 1)
    | succ k => rw [hLs]; exact hnextMem (2 * L k)
  have hmirL : ∀ k, ∀ z ∈ A, z ≠ g₀ → z + N₀ < L k →
      L k - z ∈ A := by
    intro k
    cases k with
    | zero => exact hnextMir (2 * c + g₀ + N₀ + 1)
    | succ k => rw [hLs]; exact hnextMir (2 * L k)
  exact g0_tower_engine L h0 hcov hmono hgrow hTLk hmemL hmirL
    hgA hcA hcg huA hu'A huu hug hu'g huc hu'c

theorem almost_anchored_stream_impossible {A : Set ℕ} {N₀ g₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) (hgA : g₀ ∈ A)
    (hladder : ∀ N, ∃ c ∈ A, N ≤ c ∧ c ≠ g₀ ∧ g₀ ≤ 2 * c ∧
      (2 * c - g₀) ∈ A ∧ 2 * c - g₀ ≠ c)
    (hanchor' : ∀ g, g ≠ g₀ → ∃ c ∈ A, 0 < c ∧ c ≠ g ∧
      ∃ w ∈ A, ∃ w' ∈ A,
        w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hstream : ∀ N, ∃ a m, N ≤ m ∧ 0 < a ∧
      IsPrivateTriple A a m) :
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
  rcases almost_anchored_privateStream h0 hcov hstream hanchor'
    with hsurv | ⟨hg0, hg₀stream⟩
  · exact hsurv
  · have htower := g0_tower h0 hcov hg0 hg₀stream
    obtain ⟨c, hcA, hcN, hcg, hg2c, hqA, hqc⟩ :=
      hladder (N₀ + g₀ + 1)
    exact g0_tower_impossible h0 hcov hg0 hgA htower hcA hcN hcg hqA

theorem almost_anchored_singletons_refuted {A : Set ℕ}
    {N₀ g₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) (hgA : g₀ ∈ A)
    (hladder : ∀ N, ∃ c ∈ A, N ≤ c ∧ c ≠ g₀ ∧ g₀ ≤ 2 * c ∧
      (2 * c - g₀) ∈ A ∧ 2 * c - g₀ ≠ c)
    (hanchor' : ∀ g, g ≠ g₀ → ∃ c ∈ A, 0 < c ∧ c ≠ g ∧
      ∃ w ∈ A, ∃ w' ∈ A,
        w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ¬(∀ N, ∃ n, N ≤ n ∧ ∃ a, 0 < a ∧ IsRepSupportTransversal A n {a}) := by
  intro hsing
  have hstream : ∀ N, ∃ a m, N ≤ m ∧ 0 < a ∧
      IsPrivateTriple A a m := by
    intro N
    obtain ⟨n, hn, a, ha, hhub⟩ := hsing (max N N₀)
    exact ⟨a, n, le_trans (le_max_left _ _) hn, ha,
      privateTriple_of_singleton_support_transversal h0 hcov
        (le_trans (le_max_right _ _) hn) hhub⟩
  obtain ⟨B, hBsub, hBinf, hsurv⟩ :=
    almost_anchored_stream_impossible h0 hcov hgA hladder hanchor'
      hstream
  refine hfail B hBsub hBinf ⟨N₀, fun n hn => ?_⟩
  obtain ⟨x, hx, y, hy, z, hz, hxB, hyB, hzB, hsum⟩ :=
    hsurv n hn
  refine ⟨![x, y, z], ?_, ?_⟩
  · intro i
    match i with
    | 0 => exact ⟨hx, hxB⟩
    | 1 => exact ⟨hy, hyB⟩
    | 2 => exact ⟨hz, hzB⟩
  · simpa [Fin.sum_univ_three] using hsum

theorem streamSurvives_of_almost_anchored {A : Set ℕ}
    {N₀ g₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) (hgA : g₀ ∈ A)
    (hladder : ∀ N, ∃ c ∈ A, N ≤ c ∧ c ≠ g₀ ∧ g₀ ≤ 2 * c ∧
      (2 * c - g₀) ∈ A ∧ 2 * c - g₀ ≠ c)
    (hanchor' : ∀ g, g ≠ g₀ → ∃ c ∈ A, 0 < c ∧ c ≠ g ∧
      ∃ w ∈ A, ∃ w' ∈ A,
        w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g) :
    StreamSurvives A N₀ :=
  fun hstream =>
    almost_anchored_stream_impossible h0 hcov hgA hladder hanchor'
      hstream

theorem final_dichotomy {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ((∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
      RepFree A N₀ P ∧ c ≤ P.card) ∨
    (∃ H : Finset ℕ, ∃ h ∈ H, ∀ K, ∃ V : Finset ℕ,
      K ≤ V.card ∧ ∀ v ∈ V, N₀ ≤ v ∧ h ≤ v ∧ v - h ∈ A ∧
        IsPairSupportTransversal A v H) ∨
    (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
      ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ v ∈ V, N₀ ≤ v ∧ v ∉ A ∧ ∃ s, S₀ ≤ s ∧ x s ≤ v ∧
          ∃ J, 2 ≤ J ∧ J ≤ L ∧ IsPairSupportTransversal A v
            ((Finset.range J).image (fun j => x (s + j)))) ∨
    (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
      ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ v ∈ V, N₀ ≤ v ∧ v ∈ A ∧ ∃ s, S₀ ≤ s ∧
          ∃ J, 2 ≤ J ∧ J ≤ L ∧
            v ∈ (Finset.range J).image (fun j => x (s + j)) ∧
            IsPairSupportTransversal A v ((Finset.range J).image
              (fun j => x (s + j))) ∧
            (∀ a ∈ A, ∀ b ∈ A, a + b = v →
              a ≤ x (s + J - 1) - x s ∨
              b ≤ x (s + J - 1) - x s))) ∨
    (∃ g₀ C₀, (∀ c ∈ A, C₀ ≤ c → c ≠ g₀ → ∀ w ∈ A, ∀ w' ∈ A,
        w + w' = 2 * c → w = c ∧ w' = c) ∧
      (∀ c ∈ A, C₀ ≤ c → c ≠ g₀ →
        IsPairSupportTransversal A (2 * c) ({c} : Finset ℕ)) ∧
      (∀ B ⊆ A, B.Infinite → ¬∃ N₂, ∀ n, N₂ ≤ n →
        ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) ∧
      (∀ a d, 0 < d → a ∈ A → a + d ∈ A → a + 2 * d ∈ A →
        a + d = g₀ ∨ a + d < C₀)) := by
  rcases collapsed_trichotomy h0 hcov hfail with
    ⟨_, hlanes⟩ | ⟨g₀, hgA, hladder, hanchor'⟩ | htail
  · exact Or.inl hlanes
  · exact Or.inl (four_columns h0 hcov
      (streamSurvives_of_almost_anchored h0 hcov hgA hladder
        hanchor') hfail)
  · exact Or.inr htail

/-! ## The fixed transversal model: hall mirrors and the weak translate law -/

theorem hall_mirror {A : Set ℕ} {N₀ v : ℕ} {H : Finset ℕ}
    (hcov : PairCovers A N₀) (hhub : IsRepSupportTransversal A v H)
    {z : ℕ} (hz : z ∈ A) (hzH : z ∉ H) (hzv : z + N₀ ≤ v) :
    ∃ h ∈ H, h + z ≤ v ∧ v - z - h ∈ A := by
  obtain ⟨a, haA, b, hbA, hab⟩ := hcov (v - z) (by omega)
  rcases hhub z hz a haA b hbA (by omega) with h | h | h
  · exact absurd h hzH
  · refine ⟨a, h, by omega, ?_⟩
    have hb : v - z - a = b := by omega
    rw [hb]
    exact hbA
  · refine ⟨b, h, by omega, ?_⟩
    have ha : v - z - b = a := by omega
    rw [ha]
    exact haA

theorem hall_weak_translate {A : Set ℕ} {N₀ M : ℕ}
    {H : Finset ℕ}
    (hcov : PairCovers A N₀)
    (hM : ∀ h ∈ H, h ≤ M)
    (hdoor : ∀ N, ∃ v, N ≤ v ∧ N₀ ≤ v ∧ IsRepSupportTransversal A v H ∧
      IsPairSupportTransversal A v H) :
    ∀ z ∈ A, M < z → z ∉ H → ∃ h ∈ H, z + h ∉ A := by
  intro z hzA hzM hzH
  by_contra hall
  push Not at hall
  obtain ⟨v, hvN, hvN₀, hrep, hpair⟩ :=
    hdoor (z + 2 * M + N₀ + 1)
  obtain ⟨h, hhH, hhzv, hmir⟩ :=
    hall_mirror hcov hrep hzA hzH (by omega)
  have hzhA : z + h ∈ A := hall h hhH
  have hsum : (z + h) + (v - z - h) = v := by omega
  rcases hpair (z + h) hzhA (v - z - h) hmir hsum with h1 | h1
  · have h2 := hM (z + h) h1
    omega
  · have h2 := hM (v - z - h) h1
    have h3 := hM h hhH
    omega

theorem bounded_target_sequence_fixed_hall_rep {A : Set ℕ} {N₀ : ℕ}
    {x : ℕ → ℕ} {L S₀ : ℕ} (hxA : ∀ t, x t ∈ A ∧ 0 < x t)
    (hnear : ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ v ∈ V, ∃ s, s ≤ S₀ ∧ N₀ ≤ v ∧ ∃ J, 2 ≤ J ∧ J ≤ L ∧
        IsRepSupportTransversal A v ((Finset.range J).image
          (fun j => x (s + j)))) :
    ∃ H : Finset ℕ, H.card ≤ L ∧ (∀ h ∈ H, h ∈ A ∧ 0 < h) ∧
      ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ v ∈ V, N₀ ≤ v ∧ IsRepSupportTransversal A v H := by
  classical
  set box : Finset (ℕ × ℕ) :=
    (Finset.range (S₀ + 1)) ×ˢ (Finset.range (L + 1)) with hbox
  have hstep1 : ∀ K, ∃ p ∈ box, ∃ V' : Finset ℕ, K ≤ V'.card ∧
      ∀ v ∈ V', N₀ ≤ v ∧ IsRepSupportTransversal A v
        ((Finset.range p.2).image (fun j => x (p.1 + j))) := by
    intro K
    obtain ⟨V, hVcard, hV⟩ := hnear (box.card * K + 1)
    have hVtot : ∀ v, ∃ p : ℕ × ℕ, v ∈ V →
        p.1 ≤ S₀ ∧ 2 ≤ p.2 ∧ p.2 ≤ L ∧ N₀ ≤ v ∧
        IsRepSupportTransversal A v ((Finset.range p.2).image
          (fun j => x (p.1 + j))) := by
      intro v
      by_cases hvV : v ∈ V
      · obtain ⟨s, hs, hvN, J, hJ2, hJL, hhub⟩ := hV v hvV
        exact ⟨(s, J), fun _ => ⟨hs, hJ2, hJL, hvN, hhub⟩⟩
      · exact ⟨(0, 2), fun h => absurd h hvV⟩
    choose pf hpf using hVtot
    have hmaps : ∀ v ∈ V, pf v ∈ box := by
      intro v hvV
      obtain ⟨h1, h2, h3, _, _⟩ := hpf v hvV
      rw [hbox, Finset.mem_product]
      exact ⟨Finset.mem_range.2 (by omega),
        Finset.mem_range.2 (by omega)⟩
    have hlt : box.card * K < V.card := by omega
    obtain ⟨p, hpbox, hfiber⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        hmaps hlt
    refine ⟨p, hpbox, V.filter (fun v => pf v = p),
      by omega, ?_⟩
    intro v hv
    rw [Finset.mem_filter] at hv
    obtain ⟨hvV, hfv⟩ := hv
    obtain ⟨_, _, _, hvN, hhub⟩ := hpf v hvV
    rw [hfv] at hhub
    exact ⟨hvN, hhub⟩
  have hstab : ∃ p ∈ box, ∀ K, ∃ V' : Finset ℕ,
      K ≤ V'.card ∧ ∀ v ∈ V', N₀ ≤ v ∧ IsRepSupportTransversal A v
        ((Finset.range p.2).image (fun j => x (p.1 + j))) := by
    by_contra hno
    have hKp : ∀ p : ℕ × ℕ, ∃ Kp, p ∈ box →
        ¬(∃ V' : Finset ℕ, Kp ≤ V'.card ∧ ∀ v ∈ V', N₀ ≤ v ∧
          IsRepSupportTransversal A v ((Finset.range p.2).image
            (fun j => x (p.1 + j)))) := by
      intro p
      by_cases hpbox : p ∈ box
      · have h1 : ¬∀ K, ∃ V' : Finset ℕ, K ≤ V'.card ∧
            ∀ v ∈ V', N₀ ≤ v ∧ IsRepSupportTransversal A v
              ((Finset.range p.2).image (fun j => x (p.1 + j))) :=
          fun hall => hno ⟨p, hpbox, hall⟩
        obtain ⟨Kp, hKp'⟩ := not_forall.mp h1
        exact ⟨Kp, fun _ => hKp'⟩
      · exact ⟨0, fun h => absurd h hpbox⟩
    choose Kf hKf using hKp
    obtain ⟨p, hpbox, V', hV'card, hV'⟩ := hstep1 (box.sup Kf)
    exact hKf p hpbox ⟨V',
      le_trans (Finset.le_sup (f := Kf) hpbox) hV'card, hV'⟩
  obtain ⟨p, hpbox, hall⟩ := hstab
  refine ⟨(Finset.range p.2).image (fun j => x (p.1 + j)),
    ?_, ?_, hall⟩
  · have h1 := Finset.card_image_le (s := Finset.range p.2)
      (f := fun j => x (p.1 + j))
    rw [Finset.card_range] at h1
    rw [hbox, Finset.mem_product] at hpbox
    have h2 := Finset.mem_range.1 hpbox.2
    omega
  · intro h hh
    rw [Finset.mem_image] at hh
    obtain ⟨j, _, hj⟩ := hh
    rw [← hj]
    exact hxA _

theorem fixed_transversal_model {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (horacle : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {x : ℕ → ℕ} {L S₀ : ℕ} (hxA : ∀ t, x t ∈ A ∧ 0 < x t)
    (hnear : ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ v ∈ V, ∃ s, s ≤ S₀ ∧ N₀ ≤ v ∧ ∃ J, 2 ≤ J ∧ J ≤ L ∧
        IsRepSupportTransversal A v ((Finset.range J).image
          (fun j => x (s + j)))) :
    ∃ H : Finset ℕ, 2 ≤ H.card ∧ H.card ≤ L ∧
      (∀ h ∈ H, h ∈ A ∧ 0 < h) ∧
      ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ v ∈ V, N₀ ≤ v ∧ IsRepSupportTransversal A v H ∧ IsPairSupportTransversal A v H := by
  classical
  obtain ⟨H, hHL, hHmat, hall⟩ :=
    bounded_target_sequence_fixed_hall_rep hxA hnear
  have h0H : (0 : ℕ) ∉ H := by
    intro h
    exact absurd (hHmat 0 h).2 (by omega)
  have hpair : ∀ v, IsRepSupportTransversal A v H → IsPairSupportTransversal A v H :=
    fun v hrep => pairSupportTransversal_of_repSupportTransversal h0 h0H hrep
  have hH2 : 2 ≤ H.card := by
    by_contra hlt
    rcases Nat.lt_or_ge H.card 1 with h1 | h1
    · -- empty hall: covered targets have triples, support transversal empty impossible
      have hcard0 : H.card = 0 := by omega
      rw [Finset.card_eq_zero] at hcard0
      obtain ⟨V, hVcard, hV⟩ := hall 1
      have hVne : V.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨v, hvV⟩ := hVne
      obtain ⟨hvN, hrep⟩ := hV v hvV
      obtain ⟨h, hh⟩ := support_transversal_nonempty_of_covering h0 hcov hvN hrep
      rw [hcard0] at hh
      exact absurd hh (Finset.notMem_empty h)
    · -- singleton hall: refuted cofinal singleton stream
      have hcard1 : H.card = 1 := by omega
      obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hcard1
      have ha0 : 0 < a := by
        have := (hHmat a (by rw [ha]; exact
          Finset.mem_singleton_self a)).2
        omega
      refine singleton_support_transversals_refuted h0 hcov horacle hfail ?_
      intro N
      obtain ⟨V, hVcard, hV⟩ := hall (N + 1)
      have hbig : ∃ v ∈ V, N ≤ v := by
        by_contra hallv
        have hsub : V ⊆ Finset.range N := by
          intro v hv
          rw [Finset.mem_range]
          by_contra hge
          exact hallv ⟨v, hv, by omega⟩
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_range] at h1
        omega
      obtain ⟨v, hvV, hNv⟩ := hbig
      obtain ⟨hvN, hrep⟩ := hV v hvV
      rw [ha] at hrep
      exact ⟨v, hNv, a, ha0, hrep⟩
  refine ⟨H, hH2, hHL, hHmat, ?_⟩
  intro K
  obtain ⟨V, hVcard, hV⟩ := hall K
  refine ⟨V, hVcard, ?_⟩
  intro v hv
  obtain ⟨hvN, hrep⟩ := hV v hv
  exact ⟨hvN, hrep, hpair v hrep⟩

theorem hall_mirror_color_law {A : Set ℕ} {N₀ M v : ℕ}
    {H : Finset ℕ}
    (hcov : PairCovers A N₀) (hM : ∀ h ∈ H, h ≤ M)
    (hrep : IsRepSupportTransversal A v H) (hpair : IsPairSupportTransversal A v H)
    {z : ℕ} (hz : z ∈ A) (hzH : z ∉ H) (hzM : M < z)
    (hzv : z + 2 * M + N₀ + 1 ≤ v) :
    ∃ h ∈ H, h + z ≤ v ∧ v - z - h ∈ A ∧ z + h ∉ A := by
  obtain ⟨h, hhH, hhzv, hmir⟩ :=
    hall_mirror hcov hrep hz hzH (by omega)
  refine ⟨h, hhH, hhzv, hmir, ?_⟩
  intro hzhA
  have hsum : (z + h) + (v - z - h) = v := by omega
  rcases hpair (z + h) hzhA (v - z - h) hmir hsum with h1 | h1
  · have h2 := hM (z + h) h1
    omega
  · have h2 := hM (v - z - h) h1
    have h3 := hM h hhH
    omega

theorem fixed_transversal_targets_outside_basis {A : Set ℕ} {M v : ℕ}
    {H : Finset ℕ} (h0 : 0 ∈ A) (h0H : (0 : ℕ) ∉ H)
    (hM : ∀ h ∈ H, h ≤ M) (hpair : IsPairSupportTransversal A v H)
    (hvM : M < v) : v ∉ A := by
  rcases target_sequence_target_notMem_or_window h0 h0H hpair with
    h | h
  · exact h
  · have h1 := hM v h
    omega

theorem fixed_transversal_translate_dichotomy {A : Set ℕ} (H : Finset ℕ) :
    (∀ N, ∃ z, N ≤ z ∧ z ∈ A ∧ z ∉ H ∧
      ∀ h ∈ H, z + h ∉ A) ∨
    (∃ Z₀, ∀ z, Z₀ ≤ z → z ∈ A → z ∉ H →
      ∃ h ∈ H, z + h ∈ A) := by
  classical
  by_cases hs : ∀ N, ∃ z, N ≤ z ∧ z ∈ A ∧ z ∉ H ∧
      ∀ h ∈ H, z + h ∉ A
  · exact Or.inl hs
  · right
    obtain ⟨Z₀, hZ₀⟩ := not_forall.mp hs
    refine ⟨Z₀, ?_⟩
    intro z hZz hzA hzH
    by_contra hno
    push Not at hno
    exact hZ₀ ⟨z, hZz, hzA, hzH, hno⟩

theorem fixed_transversal_two_difference_law {A : Set ℕ} {N₀ M v v' : ℕ}
    {H : Finset ℕ}
    (hcov : PairCovers A N₀) (hM : ∀ h ∈ H, h ≤ M)
    (hcard : H.card = 2)
    (hrep' : IsRepSupportTransversal A v' H) (hpair' : IsPairSupportTransversal A v' H)
    (hvA : v ∉ A) {h₀ : ℕ} (hh₀ : h₀ ∈ H)
    (hpart : v - h₀ ∈ A) (hMv : 2 * M < v)
    (hgood : ∃ h ∈ H, (v - h₀) + h ∈ A)
    (hvv' : v + 2 * M + N₀ + 1 ≤ v') :
    v' - v ∈ A := by
  obtain ⟨hg, hgH, hgA⟩ := hgood
  have hgh₀ : hg ≠ h₀ := by
    intro h
    rw [h] at hgA
    have h1 : v - h₀ + h₀ = v := by
      have := hM h₀ hh₀
      omega
    rw [h1] at hgA
    exact hvA hgA
  have hLH : v - h₀ ∉ H := by
    intro h
    have h1 := hM _ h
    have h2 := hM h₀ hh₀
    omega
  obtain ⟨h, hhH, hhzv, hmir, hbad⟩ :=
    hall_mirror_color_law hcov hM hrep' hpair' hpart hLH
      (by have := hM h₀ hh₀; omega)
      (by have := hM h₀ hh₀; omega)
  have hhg : h ≠ hg := by
    intro h1
    rw [h1] at hbad
    exact hbad hgA
  have hhh₀ : h = h₀ := by
    obtain ⟨a, b, hab, hH⟩ := Finset.card_eq_two.1 hcard
    rw [hH] at hhH hgH hh₀
    simp only [Finset.mem_insert, Finset.mem_singleton]
      at hhH hgH hh₀
    rcases hhH with h1 | h1 <;> rcases hgH with h2 | h2 <;>
      rcases hh₀ with h3 | h3 <;> omega
  rw [hhh₀] at hmir
  have h1 : v' - (v - h₀) - h₀ = v' - v := by
    have := hM h₀ hh₀
    omega
  rw [h1] at hmir
  exact hmir

theorem fixed_transversal_good_deep_engine {A : Set ℕ} {N₀ h₀ h₁ : ℕ}
    (v : ℕ → ℕ)
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hmono : StrictMono v)
    (hgrow : ∀ k, 2 * v k < v (k + 1))
    (hh₁ : 0 < h₁)
    (hbase : h₀ + h₁ + N₀ + 1 < v 0)
    (hL : ∀ k, v k - h₀ ∈ A)
    (hM : ∀ k, v k - h₀ + h₁ ∈ A)
    (hDP : ∀ k, v k - h₀ - h₁ ∈ A)
    (hd : ∀ i j, i < j → v j - v i ∈ A) :
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
  classical
  have hv0 : ∀ k, v 0 ≤ v k := fun k => hmono.monotone (Nat.zero_le k)
  have hgap : ∀ k, v k + v 0 < v (k + 1) := by
    intro k
    have h1 := hgrow k
    have h2 := hv0 k
    omega
  set f : ℕ → ℕ := fun k => v (2 * k + 2) - h₀ with hf
  have hfA : ∀ k, f k ∈ A := fun k => hL (2 * k + 2)
  have hfinj : Function.Injective f := by
    intro i j hij
    simp only [hf] at hij
    have h1 := hv0 (2 * i + 2)
    have h2 := hv0 (2 * j + 2)
    have h3 : v (2 * i + 2) = v (2 * j + 2) := by omega
    have h4 := hmono.injective h3
    omega
  have hBsub : Set.range f ⊆ A := by
    rintro w ⟨k, rfl⟩
    exact hfA k
  have h0B : (0 : ℕ) ∉ Set.range f := by
    rintro ⟨r, hr⟩
    simp only [hf] at hr
    have := hv0 (2 * r + 2)
    omega
  -- scale separation: distinct indices differ by more than v 0
  have hsep : ∀ a b, a < b → v a + v 0 ≤ v b := by
    intro a b hab
    have h1 := hgap a
    have h2 : v (a + 1) ≤ v b := hmono.monotone (by omega)
    omega
  -- consecutive differences are not deleted values
  have hdiffB : ∀ i, v (i + 1) - v i ∉ Set.range f := by
    rintro i ⟨r, hr⟩
    simp only [hf] at hr
    have h1 := hv0 (2 * r + 2)
    have h2 := hv0 i
    have e : v (2 * r + 2) + v i = v (i + 1) + h₀ := by omega
    rcases Nat.lt_trichotomy (2 * r + 2) (i + 1) with h | h | h
    · have h3 : v (2 * r + 2) ≤ v i := hmono.monotone (by omega)
      have h4 := hsep i (i + 1) (by omega)
      have h5 := hgrow i
      omega
    · rw [h] at e
      omega
    · have h3 := hsep (i + 1) (2 * r + 2) h
      omega
  -- odd levels are not deleted values
  have hoddB : ∀ i, v (2 * i + 1) - h₀ ∉ Set.range f := by
    rintro i ⟨r, hr⟩
    simp only [hf] at hr
    have h1 := hv0 (2 * r + 2)
    have h2 := hv0 (2 * i + 1)
    have h3 : v (2 * r + 2) = v (2 * i + 1) := by omega
    have h4 := hmono.injective h3
    omega
  -- good-translated levels are not deleted values
  have hMB : ∀ i, v i - h₀ + h₁ ∉ Set.range f := by
    rintro i ⟨r, hr⟩
    simp only [hf] at hr
    have h1 := hv0 (2 * r + 2)
    have h2 := hv0 i
    rcases Nat.lt_trichotomy (2 * r + 2) i with h | h | h
    · have h3 := hsep (2 * r + 2) i h
      omega
    · rw [h] at hr
      omega
    · have h3 := hsep i (2 * r + 2) h
      omega
  -- deep partners are not deleted values
  have hDPB : ∀ i, v i - h₀ - h₁ ∉ Set.range f := by
    rintro i ⟨r, hr⟩
    simp only [hf] at hr
    have h1 := hv0 (2 * r + 2)
    have h2 := hv0 i
    rcases Nat.lt_trichotomy (2 * r + 2) i with h | h | h
    · have h3 := hsep (2 * r + 2) i h
      omega
    · rw [h] at hr
      omega
    · have h3 := hsep i (2 * r + 2) h
      omega
  refine ⟨Set.range f, hBsub,
    Set.infinite_range_of_injective hfinj, ?_⟩
  intro n hn
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov n hn
  by_cases hxB : x ∈ Set.range f
  · obtain ⟨i, hix⟩ := hxB
    simp only [hf] at hix
    by_cases hyB : y ∈ Set.range f
    · obtain ⟨j, hjy⟩ := hyB
      simp only [hf] at hjy
      have h1 := hv0 (2 * i + 2)
      have h2 := hv0 (2 * j + 2)
      have h3 := hsep (2 * j + 1) (2 * j + 2) (by omega)
      have h4 := hv0 (2 * j + 1)
      exact ⟨v (2 * i + 2) - h₀ + h₁, hM (2 * i + 2),
        v (2 * j + 2) - v (2 * j + 1),
        hd (2 * j + 1) (2 * j + 2) (by omega),
        v (2 * j + 1) - h₀ - h₁, hDP (2 * j + 1),
        hMB (2 * i + 2), hdiffB (2 * j + 1),
        hDPB (2 * j + 1), by omega⟩
    · have h1 := hv0 (2 * i + 2)
      have h2 := hv0 (2 * i + 1)
      have h3 := hsep (2 * i + 1) (2 * i + 2) (by omega)
      exact ⟨v (2 * i + 2) - v (2 * i + 1),
        hd (2 * i + 1) (2 * i + 2) (by omega),
        v (2 * i + 1) - h₀, hL (2 * i + 1), y, hy,
        hdiffB (2 * i + 1), hoddB i, hyB, by omega⟩
  · by_cases hyB : y ∈ Set.range f
    · obtain ⟨j, hjy⟩ := hyB
      simp only [hf] at hjy
      have h1 := hv0 (2 * j + 2)
      have h2 := hv0 (2 * j + 1)
      have h3 := hsep (2 * j + 1) (2 * j + 2) (by omega)
      exact ⟨v (2 * j + 2) - v (2 * j + 1),
        hd (2 * j + 1) (2 * j + 2) (by omega),
        v (2 * j + 1) - h₀, hL (2 * j + 1), x, hx,
        hdiffB (2 * j + 1), hoddB j, hxB, by omega⟩
    · exact ⟨x, hx, y, hy, 0, h0, hxB, hyB, h0B, by omega⟩

theorem fixed_transversal_two_good_deep_impossible {A : Set ℕ}
    {N₀ M₀ h₀ h₁ Z₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    {H : Finset ℕ} (hcard : H.card = 2)
    (hM₀ : ∀ h ∈ H, h ≤ M₀)
    (hh₀ : h₀ ∈ H) (hh₁ : h₁ ∈ H) (hne : h₀ ≠ h₁)
    (hh₀pos : 0 < h₀) (hh₁pos : 0 < h₁)
    (hgood : ∀ z, Z₀ ≤ z → z ∈ A → z ∉ H →
      ∃ h ∈ H, z + h ∈ A)
    (hsupply : ∀ N, ∃ v, N ≤ v ∧ N₀ ≤ v ∧ IsRepSupportTransversal A v H ∧
      IsPairSupportTransversal A v H ∧ v - h₀ ∈ A ∧ v - h₀ - h₁ ∈ A) :
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
  classical
  have hHeq : H = {h₀, h₁} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro a ha
      rcases Finset.mem_insert.1 ha with h | h
      · exact h ▸ hh₀
      · rw [Finset.mem_singleton] at h
        exact h ▸ hh₁
    · rw [hcard, Finset.card_insert_of_notMem
        (by rw [Finset.mem_singleton]; exact hne),
        Finset.card_singleton]
  have h0H : (0 : ℕ) ∉ H := by
    intro h
    rw [hHeq] at h
    rcases Finset.mem_insert.1 h with h | h
    · omega
    · rw [Finset.mem_singleton] at h
      omega
  -- extraction
  have hsup' : ∀ c, ∃ w, c < w ∧ N₀ ≤ w ∧ IsRepSupportTransversal A w H ∧
      IsPairSupportTransversal A w H ∧ w - h₀ ∈ A ∧ w - h₀ - h₁ ∈ A := by
    intro c
    obtain ⟨w, hw1, hw2, hw3, hw4, hw5, hw6⟩ := hsupply (c + 1)
    exact ⟨w, by omega, hw2, hw3, hw4, hw5, hw6⟩
  choose nf hnf1 hnf2 hnf3 hnf4 hnf5 hnf6 using hsup'
  set base := Z₀ + 2 * M₀ + h₀ + h₁ + N₀ + 1 with hbase
  set v : ℕ → ℕ := fun k =>
    Nat.rec (nf base) (fun _ prev => nf (2 * prev)) k with hv
  have hv0 : v 0 = nf base := rfl
  have hvs : ∀ k, v (k + 1) = nf (2 * v k) := fun _ => rfl
  have hgrow : ∀ k, 2 * v k < v (k + 1) := by
    intro k
    rw [hvs]
    exact hnf1 (2 * v k)
  have hbv : base < v 0 := by
    rw [hv0]
    exact hnf1 base
  have hmono : StrictMono v := by
    apply strictMono_nat_of_lt_succ
    intro k
    have h1 := hgrow k
    have h2 : 0 < v k := by
      induction k with
      | zero => omega
      | succ k ih => have := hgrow k; omega
    omega
  have hbvk : ∀ k, base < v k := by
    intro k
    have := hmono.monotone (Nat.zero_le k)
    omega
  have hprops : ∀ k, N₀ ≤ v k ∧ IsRepSupportTransversal A (v k) H ∧
      IsPairSupportTransversal A (v k) H ∧ v k - h₀ ∈ A ∧
      v k - h₀ - h₁ ∈ A := by
    intro k
    cases k with
    | zero =>
      rw [hv0]
      exact ⟨hnf2 _, hnf3 _, hnf4 _, hnf5 _, hnf6 _⟩
    | succ k =>
      rw [hvs]
      exact ⟨hnf2 _, hnf3 _, hnf4 _, hnf5 _, hnf6 _⟩
  have hghost : ∀ k, v k ∉ A := by
    intro k
    exact fixed_transversal_targets_outside_basis h0 h0H hM₀ (hprops k).2.2.1
      (by have := hbvk k; omega)
  have hMlaw : ∀ k, v k - h₀ + h₁ ∈ A := by
    intro k
    have hLA : v k - h₀ ∈ A := (hprops k).2.2.2.1
    have hLH : v k - h₀ ∉ H := by
      intro h
      have h1 := hM₀ _ h
      have h2 := hbvk k
      have h3 := hM₀ h₀ hh₀
      omega
    obtain ⟨g, hgH, hgA⟩ := hgood (v k - h₀)
      (by have := hbvk k; have := hM₀ h₀ hh₀; omega) hLA hLH
    have hgh₁ : g = h₁ := by
      rw [hHeq] at hgH
      rcases Finset.mem_insert.1 hgH with h | h
      · exfalso
        rw [h] at hgA
        have h1 : v k - h₀ + h₀ = v k := by
          have := hM₀ h₀ hh₀
          have := hbvk k
          omega
        rw [h1] at hgA
        exact hghost k hgA
      · rw [Finset.mem_singleton] at h
        exact h
    rw [hgh₁] at hgA
    exact hgA
  have hdlaw : ∀ i j, i < j → v j - v i ∈ A := by
    intro i j hij
    have hji : v i + 2 * M₀ + N₀ + 1 ≤ v j := by
      have h1 : v (i + 1) ≤ v j := by
        rcases Nat.lt_or_ge (i + 1) j with h | h
        · exact le_of_lt (hmono h)
        · have h4 : i + 1 = j := by omega
          rw [h4]
      have h2 := hgrow i
      have h3 := hbvk i
      omega
    exact fixed_transversal_two_difference_law hcov hM₀ hcard
      (hprops j).2.1 (hprops j).2.2.1 (hghost i) hh₀
      (hprops i).2.2.2.1
      (by have := hbvk i; omega)
      ⟨h₁, hh₁, hMlaw i⟩ hji
  exact fixed_transversal_good_deep_engine v h0 hcov hmono hgrow hh₁pos
    (by have := hbvk 0; omega)
    (fun k => (hprops k).2.2.2.1) hMlaw
    (fun k => (hprops k).2.2.2.2) hdlaw

/-! ## The walk contradicts: AP3 midpoint deletion -/

theorem ap3_deletion_engine {A : Set ℕ} {N₀ c : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hcA : c ∈ A) (hcpos : 0 < c)
    (hap : ∀ V, ∃ m, V ≤ m ∧ m - c ∈ A ∧ m ∈ A ∧
      m + c ∈ A) :
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
  classical
  have hsup : ∀ V, ∃ m, V < m ∧ m - c ∈ A ∧ m ∈ A ∧
      m + c ∈ A := by
    intro V
    obtain ⟨m, h1, h2, h3, h4⟩ := hap (V + 1)
    exact ⟨m, by omega, h2, h3, h4⟩
  choose nx hnx1 hnx2 hnx3 hnx4 using hsup
  set m : ℕ → ℕ := fun k =>
    Nat.rec (nx (c + N₀ + 1)) (fun _ p => nx (2 * p + c)) k
    with hm
  have hm0 : m 0 = nx (c + N₀ + 1) := rfl
  have hms : ∀ k, m (k + 1) = nx (2 * m k + c) := fun _ => rfl
  have hbase : c + N₀ + 1 < m 0 := by
    rw [hm0]
    exact hnx1 _
  have hgrow : ∀ k, 2 * m k + c < m (k + 1) := by
    intro k
    rw [hms]
    exact hnx1 _
  have hmono : StrictMono m := by
    apply strictMono_nat_of_lt_succ
    intro k
    have h1 := hgrow k
    omega
  have hbk : ∀ k, c + N₀ + 1 < m k := by
    intro k
    have := hmono.monotone (Nat.zero_le k)
    omega
  have hprops : ∀ k, m k - c ∈ A ∧ m k ∈ A ∧ m k + c ∈ A := by
    intro k
    cases k with
    | zero =>
      rw [hm0]
      exact ⟨hnx2 _, hnx3 _, hnx4 _⟩
    | succ k =>
      rw [hms]
      exact ⟨hnx2 _, hnx3 _, hnx4 _⟩
  have hsepk : ∀ a b, a < b → 2 * m a + c < m b := by
    intro a b hab
    have h1 := hgrow a
    have h2 : m (a + 1) ≤ m b := by
      rcases Nat.lt_or_ge (a + 1) b with h | h
      · exact le_of_lt (hmono h)
      · have h3 : a + 1 = b := by omega
        rw [h3]
    omega
  set f : ℕ → ℕ := fun k => m k with hf
  have hBsub : Set.range f ⊆ A := by
    rintro w ⟨k, rfl⟩
    exact (hprops k).2.1
  have hfinj : Function.Injective f :=
    fun i j hij => hmono.injective hij
  have h0B : (0 : ℕ) ∉ Set.range f := by
    rintro ⟨r, hr⟩
    simp only [hf] at hr
    have := hbk r
    omega
  have hcB : c ∉ Set.range f := by
    rintro ⟨r, hr⟩
    simp only [hf] at hr
    have := hbk r
    omega
  have hdownB : ∀ k, m k - c ∉ Set.range f := by
    rintro k ⟨r, hr⟩
    simp only [hf] at hr
    rcases Nat.lt_trichotomy r k with h | h | h
    · have h1 := hsepk r k h
      have h2 := hbk r
      have h3 := hbk k
      omega
    · rw [h] at hr
      have := hbk k
      omega
    · have h1 : m k < m r := hmono h
      have h2 := hbk k
      omega
  have hupB : ∀ k, m k + c ∉ Set.range f := by
    rintro k ⟨r, hr⟩
    simp only [hf] at hr
    rcases Nat.lt_trichotomy r k with h | h | h
    · have h1 : m r < m k := hmono h
      omega
    · rw [h] at hr
      omega
    · have h1 := hsepk k r h
      have h2 := hbk k
      omega
  refine ⟨Set.range f, hBsub,
    Set.infinite_range_of_injective hfinj, ?_⟩
  intro n hn
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov n hn
  by_cases hxB : x ∈ Set.range f
  · obtain ⟨i, hix⟩ := hxB
    simp only [hf] at hix
    by_cases hyB : y ∈ Set.range f
    · obtain ⟨j, hjy⟩ := hyB
      simp only [hf] at hjy
      have h1 := hbk i
      have h2 := hbk j
      exact ⟨m i - c, (hprops i).1, m j + c, (hprops j).2.2,
        0, h0, hdownB i, hupB j, h0B, by omega⟩
    · have h1 := hbk i
      exact ⟨m i - c, (hprops i).1, c, hcA, y, hy,
        hdownB i, hcB, hyB, by omega⟩
  · by_cases hyB : y ∈ Set.range f
    · obtain ⟨j, hjy⟩ := hyB
      simp only [hf] at hjy
      have h1 := hbk j
      exact ⟨m j - c, (hprops j).1, c, hcA, x, hx,
        hdownB j, hcB, hxB, by omega⟩
    · exact ⟨x, hx, y, hy, 0, h0, hxB, hyB, h0B, by omega⟩

theorem good_two_walk_impossible {A : Set ℕ} {N₀ h₀ h₁ Z₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hh₀A : h₀ ∈ A) (hh₁A : h₁ ∈ A)
    (hh₀ : 0 < h₀) (hh₁ : 0 < h₁)
    (hgood : ∀ z, Z₀ ≤ z → z ∈ A →
      z + h₀ ∈ A ∨ z + h₁ ∈ A) :
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
  classical
  -- a large starting element
  obtain ⟨p, hpA, q, hqA, hpq⟩ :=
    hcov (2 * (Z₀ + h₀ + h₁ + N₀ + 1)) (by omega)
  have hbig : ∃ a, a ∈ A ∧ Z₀ + h₀ + h₁ + N₀ + 1 ≤ a := by
    rcases le_total p q with h | h
    · exact ⟨q, hqA, by omega⟩
    · exact ⟨p, hpA, by omega⟩
  obtain ⟨a, haA, haZ⟩ := hbig
  -- the walk
  have hstepex : ∀ w, ∃ w', Z₀ ≤ w → w ∈ A →
      (w' = w + h₀ ∨ w' = w + h₁) ∧ w' ∈ A := by
    intro w
    by_cases hw : Z₀ ≤ w ∧ w ∈ A
    · rcases hgood w hw.1 hw.2 with h | h
      · exact ⟨w + h₀, fun _ _ => ⟨Or.inl rfl, h⟩⟩
      · exact ⟨w + h₁, fun _ _ => ⟨Or.inr rfl, h⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hw⟩
  choose st hst using hstepex
  set z : ℕ → ℕ := fun t =>
    Nat.rec a (fun _ p => st p) t with hzdef
  have hz0 : z 0 = a := rfl
  have hzs : ∀ t, z (t + 1) = st (z t) := fun _ => rfl
  have hzfacts : ∀ t, z t ∈ A ∧ Z₀ ≤ z t := by
    intro t
    induction t with
    | zero => exact ⟨haA, by omega⟩
    | succ t ih =>
      obtain ⟨h1, h2⟩ := hst (z t) ih.2 ih.1
      rw [hzs]
      constructor
      · exact h2
      · rcases h1 with h | h <;> omega
  have hstep : ∀ t, z (t + 1) = z t + h₀ ∨
      z (t + 1) = z t + h₁ := by
    intro t
    have := (hst (z t) (hzfacts t).2 (hzfacts t).1).1
    rw [hzs]
    exact this
  have hzmono : StrictMono z := by
    apply strictMono_nat_of_lt_succ
    intro t
    rcases hstep t with h | h <;> omega
  have hzunb : ∀ V, ∃ t, V ≤ z t := by
    intro V
    have hlin : ∀ t, z 0 + t ≤ z t := by
      intro t
      induction t with
      | zero => omega
      | succ t ih =>
        rcases hstep t with h | h <;> omega
    exact ⟨V, by have := hlin V; omega⟩
  -- the equal-adjacent dichotomy
  by_cases hEA : ∀ V, ∃ t, V ≤ z t ∧
      ((z (t + 1) = z t + h₀ ∧ z (t + 2) = z t + 2 * h₀) ∨
       (z (t + 1) = z t + h₁ ∧ z (t + 2) = z t + 2 * h₁))
  · -- cofinal doubles: pigeonhole the colour, feed the AP3 engine
    by_cases hEA0 : ∀ V, ∃ t, V ≤ z t ∧
        z (t + 1) = z t + h₀ ∧ z (t + 2) = z t + 2 * h₀
    · refine ap3_deletion_engine h0 hcov hh₀A hh₀ ?_
      intro V
      obtain ⟨t, hVt, h1, h2⟩ := hEA0 V
      refine ⟨z (t + 1), by omega, ?_, (hzfacts (t + 1)).1, ?_⟩
      · have h3 : z (t + 1) - h₀ = z t := by omega
        rw [h3]
        exact (hzfacts t).1
      · have h3 : z (t + 1) + h₀ = z (t + 2) := by omega
        rw [h3]
        exact (hzfacts (t + 2)).1
    · obtain ⟨V₀, hV₀⟩ := not_forall.mp hEA0
      refine ap3_deletion_engine h0 hcov hh₁A hh₁ ?_
      intro V
      obtain ⟨t, hVt, hdb⟩ := hEA (max V V₀)
      have hVt' : V ≤ z t := le_trans (le_max_left _ _) hVt
      have hV₀t : V₀ ≤ z t := le_trans (le_max_right _ _) hVt
      rcases hdb with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd ⟨t, hV₀t, h1, h2⟩ hV₀
      · refine ⟨z (t + 1), by omega, ?_,
          (hzfacts (t + 1)).1, ?_⟩
        · have h3 : z (t + 1) - h₁ = z t := by omega
          rw [h3]
          exact (hzfacts t).1
        · have h3 : z (t + 1) + h₁ = z (t + 2) := by omega
          rw [h3]
          exact (hzfacts (t + 2)).1
  · -- eventual perfect alternation: two-step sums are constant
    obtain ⟨V₁, hV₁⟩ := not_forall.mp hEA
    obtain ⟨T₁, hT₁⟩ := hzunb V₁
    have halt : ∀ t, T₁ ≤ t →
        z (t + 2) = z t + h₀ + h₁ := by
      intro t hTt
      have hVz : V₁ ≤ z t :=
        le_trans hT₁ (hzmono.monotone hTt)
      have hnd : ¬((z (t + 1) = z t + h₀ ∧
          z (t + 2) = z t + 2 * h₀) ∨
          (z (t + 1) = z t + h₁ ∧
          z (t + 2) = z t + 2 * h₁)) :=
        fun hdb => hV₁ ⟨t, hVz, hdb⟩
      have h2' := hstep (t + 1)
      have he : t + 1 + 1 = t + 2 := by omega
      rw [he] at h2'
      rcases hstep t with h1 | h1 <;> rcases h2' with h2 | h2
      · exact absurd (Or.inl ⟨h1, by omega⟩) hnd
      · omega
      · omega
      · exact absurd (Or.inr ⟨h1, by omega⟩) hnd
    -- delete every fifth walk element beyond T₁ + 2
    set f : ℕ → ℕ := fun k => z (T₁ + 2 + 5 * k) with hf
    have hfinj : Function.Injective f := by
      intro i j hij
      simp only [hf] at hij
      have := hzmono.injective hij
      omega
    have hBsub : Set.range f ⊆ A := by
      rintro w ⟨k, rfl⟩
      exact (hzfacts _).1
    have hidx : ∀ s r, z s ∈ Set.range f →
        s = T₁ + 2 + 5 * r → z s ∈ Set.range f := fun _ _ h _ => h
    have hnotB : ∀ s, (∀ r, s ≠ T₁ + 2 + 5 * r) →
        z s ∉ Set.range f := by
      intro s hs ⟨r, hr⟩
      simp only [hf] at hr
      exact hs r (hzmono.injective hr).symm
    have hzlow : ∀ t, a ≤ z t := by
      intro t
      have h1 : z 0 ≤ z t := hzmono.monotone (Nat.zero_le t)
      rw [hz0] at h1
      exact h1
    have h0B : (0 : ℕ) ∉ Set.range f := by
      rintro ⟨r, hr⟩
      simp only [hf] at hr
      have h1 := hzlow (T₁ + 2 + 5 * r)
      omega
    have hsmallB : ∀ w, w ≤ h₀ + h₁ → w ∉ Set.range f := by
      rintro w hw ⟨r, hr⟩
      simp only [hf] at hr
      have h1 := hzlow (T₁ + 2 + 5 * r)
      omega
    refine ⟨Set.range f, hBsub,
      Set.infinite_range_of_injective hfinj, ?_⟩
    intro n hn
    obtain ⟨x, hx, y, hy, hxy⟩ := hcov n hn
    by_cases hxB : x ∈ Set.range f
    · obtain ⟨i, hix⟩ := hxB
      simp only [hf] at hix
      by_cases hyB : y ∈ Set.range f
      · obtain ⟨j, hjy⟩ := hyB
        simp only [hf] at hjy
        have hai := halt (T₁ + 5 * i) (by omega)
        have haj := halt (T₁ + 2 + 5 * j) (by omega)
        have hei : T₁ + 5 * i + 2 = T₁ + 2 + 5 * i := by omega
        rw [hei] at hai
        have hB1 : z (T₁ + 5 * i) ∉ Set.range f := by
          apply hnotB
          intro r
          omega
        have hB2 : z (T₁ + 2 + 5 * j + 2) ∉ Set.range f :=
          hnotB (T₁ + 2 + 5 * j + 2) (by intro r; omega)
        exact ⟨z (T₁ + 5 * i), (hzfacts (T₁ + 5 * i)).1,
          z (T₁ + 2 + 5 * j + 2),
          (hzfacts (T₁ + 2 + 5 * j + 2)).1, 0, h0,
          hB1, hB2, h0B, by omega⟩
      · have hst' := hstep (T₁ + 1 + 5 * i)
        have hei : T₁ + 1 + 5 * i + 1 = T₁ + 2 + 5 * i := by
          omega
        rw [hei] at hst'
        have hB1 : z (T₁ + 1 + 5 * i) ∉ Set.range f := by
          apply hnotB
          intro r
          omega
        rcases hst' with h1 | h1
        · exact ⟨z (T₁ + 1 + 5 * i), (hzfacts _).1,
            h₀, hh₀A, y, hy, hB1,
            hsmallB h₀ (by omega), hyB, by omega⟩
        · exact ⟨z (T₁ + 1 + 5 * i), (hzfacts _).1,
            h₁, hh₁A, y, hy, hB1,
            hsmallB h₁ (by omega), hyB, by omega⟩
    · by_cases hyB : y ∈ Set.range f
      · obtain ⟨j, hjy⟩ := hyB
        simp only [hf] at hjy
        have hst' := hstep (T₁ + 1 + 5 * j)
        have hej : T₁ + 1 + 5 * j + 1 = T₁ + 2 + 5 * j := by
          omega
        rw [hej] at hst'
        have hB1 : z (T₁ + 1 + 5 * j) ∉ Set.range f := by
          apply hnotB
          intro r
          omega
        rcases hst' with h1 | h1
        · exact ⟨z (T₁ + 1 + 5 * j), (hzfacts _).1,
            h₀, hh₀A, x, hx, hB1,
            hsmallB h₀ (by omega), hxB, by omega⟩
        · exact ⟨z (T₁ + 1 + 5 * j), (hzfacts _).1,
            h₁, hh₁A, x, hx, hB1,
            hsmallB h₁ (by omega), hxB, by omega⟩
      · exact ⟨x, hx, y, hy, 0, h0, hxB, hyB, h0B, by omega⟩

theorem single_translate_law {A : Set ℕ} {N₀ c : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hcA : c ∈ A) (hcpos : 0 < c) :
    ∀ Z₀, ∃ z, Z₀ ≤ z ∧ z ∈ A ∧ z + c ∉ A := by
  by_contra hno
  push Not at hno
  obtain ⟨Z₀, hZ₀⟩ := hno
  have hgood : ∀ z, Z₀ ≤ z → z ∈ A → z + c ∈ A := by
    intro z h1 h2
    exact hZ₀ z h1 h2
  have hbig : ∀ V, ∃ a, a ∈ A ∧ V ≤ a := by
    intro V
    obtain ⟨p, hpA, q, hqA, hpq⟩ := hcov (2 * (V + N₀))
      (by omega)
    rcases le_total p q with h | h
    · exact ⟨q, hqA, by omega⟩
    · exact ⟨p, hpA, by omega⟩
  obtain ⟨B, hBsub, hBinf, hsurv⟩ :=
    ap3_deletion_engine h0 hcov hcA hcpos (by
      intro V
      obtain ⟨a, haA, haV⟩ := hbig (V + Z₀)
      have h1 : a + c ∈ A := hgood a (by omega) haA
      have h2 : a + c + c ∈ A := hgood (a + c) (by omega) h1
      refine ⟨a + c, by omega, ?_, h1, h2⟩
      have h3 : a + c - c = a := by omega
      rw [h3]
      exact haA)
  refine hfail B hBsub hBinf ⟨N₀, fun n hn => ?_⟩
  obtain ⟨x, hx, y, hy, z, hz, hxB, hyB, hzB, hsum⟩ :=
    hsurv n hn
  refine ⟨![x, y, z], ?_, ?_⟩
  · intro i
    match i with
    | 0 => exact ⟨hx, hxB⟩
    | 1 => exact ⟨hy, hyB⟩
    | 2 => exact ⟨hz, hzB⟩
  · simpa [Fin.sum_univ_three] using hsum

theorem pair_translate_law {A : Set ℕ} {N₀ h₀ h₁ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hh₀A : h₀ ∈ A) (hh₁A : h₁ ∈ A)
    (hh₀ : 0 < h₀) (hh₁ : 0 < h₁) :
    ∀ Z₀, ∃ z, Z₀ ≤ z ∧ z ∈ A ∧ z + h₀ ∉ A ∧ z + h₁ ∉ A := by
  by_contra hno
  push Not at hno
  obtain ⟨Z₀, hZ₀⟩ := hno
  have hgood : ∀ z, Z₀ ≤ z → z ∈ A →
      z + h₀ ∈ A ∨ z + h₁ ∈ A := by
    intro z h1 h2
    by_cases ha : z + h₀ ∈ A
    · exact Or.inl ha
    · exact Or.inr (hZ₀ z h1 h2 ha)
  obtain ⟨B, hBsub, hBinf, hsurv⟩ :=
    good_two_walk_impossible h0 hcov hh₀A hh₁A hh₀ hh₁ hgood
  refine hfail B hBsub hBinf ⟨N₀, fun n hn => ?_⟩
  obtain ⟨x, hx, y, hy, z, hz, hxB, hyB, hzB, hsum⟩ :=
    hsurv n hn
  refine ⟨![x, y, z], ?_, ?_⟩
  · intro i
    match i with
    | 0 => exact ⟨hx, hxB⟩
    | 1 => exact ⟨hy, hyB⟩
    | 2 => exact ⟨hz, hzB⟩
  · simpa [Fin.sum_univ_three] using hsum

theorem deletion_failure_slices {A B : Set ℕ}
    (hfail : ∀ B' ⊆ A, B'.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B') 3)
    (hBA : B ⊆ A) (hBinf : B.Infinite) :
    ∀ N, ∃ n, N ≤ n ∧ ∀ z ∈ A, z ∉ B →
      ∀ a ∈ A, ∀ b ∈ A, a + b + z = n →
        a ∈ B ∨ b ∈ B := by
  intro N
  have hnb := hfail B hBA hBinf
  rw [IsExactTupleAsymptoticBasis] at hnb
  push Not at hnb
  obtain ⟨n, hn, hnofail⟩ := hnb N
  refine ⟨n, hn, ?_⟩
  intro z hz hzB a ha b hb hab
  by_contra hno
  push Not at hno
  have hmemb : ∀ i : Fin 3, (![a, b, z] : Fin 3 → ℕ) i ∈
      A \ B := by
    intro i
    match i with
    | 0 => exact ⟨ha, hno.1⟩
    | 1 => exact ⟨hb, hno.2⟩
    | 2 => exact ⟨hz, hzB⟩
  have hsum3 : (∑ i, (![a, b, z] : Fin 3 → ℕ) i) = n := by
    rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    omega
  exact hnofail ![a, b, z] hmemb hsum3

theorem deletion_failure_double_slice {A B : Set ℕ}
    (hfail : ∀ B' ⊆ A, B'.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B') 3)
    (hBA : B ⊆ A) (hBinf : B.Infinite) :
    ∀ N, ∃ n, N ≤ n ∧ ∀ s ∈ A, s ∉ B → ∀ s' ∈ A, s' ∉ B →
      ∀ w ∈ A, s + s' + w = n → w ∈ B := by
  intro N
  obtain ⟨n, hn, hslice⟩ :=
    deletion_failure_slices hfail hBA hBinf N
  refine ⟨n, hn, ?_⟩
  intro s hs hsB s' hs' hs'B w hw hsum
  rcases hslice s hs hsB s' hs' w hw (by omega) with h | h
  · exact absurd h hs'B
  · exact h

open Classical in

theorem failure_slices_low_r2 {A B : Set ℕ}
    (hfail : ∀ B' ⊆ A, B'.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B') 3)
    (hBA : B ⊆ A) (hBinf : B.Infinite) :
    ∀ N, ∃ n, N ≤ n ∧ ∀ s ∈ A, s ∉ B → s ≤ n →
      ∀ W : Finset ℕ, (∀ b, b ∈ B → b ≤ n → b ∈ W) →
      ((Finset.range (n - s + 1)).filter
        (fun a => a ∈ A ∧ (n - s - a) ∈ A ∧
          2 * a ≤ n - s)).card ≤ W.card := by
  intro N
  obtain ⟨n, hn, hslice⟩ :=
    deletion_failure_slices hfail hBA hBinf N
  refine ⟨n, hn, ?_⟩
  intro s hs hsB hsn W hW
  have hhub : IsPairSupportTransversal A (n - s) W := by
    intro a ha b hb hab
    rcases hslice s hs hsB a ha b hb (by omega) with h | h
    · exact Or.inl (hW a h (by omega))
    · exact Or.inr (hW b h (by omega))
  exact pair_support_transversal_pair_count hhub

open Classical in

theorem covering_density {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀) :
    ∀ X, N₀ ≤ X → X - N₀ + 1 ≤
      (((Finset.range (X + 1)).filter (· ∈ A)).card) ^ 2 := by
  intro X hX
  have htot : ∀ n, ∃ x y, N₀ ≤ n →
      x ∈ A ∧ y ∈ A ∧ x + y = n := by
    intro n
    by_cases hn : N₀ ≤ n
    · obtain ⟨x, hx, y, hy, hxy⟩ := hcov n hn
      exact ⟨x, y, fun _ => ⟨hx, hy, hxy⟩⟩
    · exact ⟨0, 0, fun h => absurd h hn⟩
  choose xf yf hxy using htot
  set Af := (Finset.range (X + 1)).filter (· ∈ A) with hAf
  have hmaps : ∀ n ∈ Finset.Icc N₀ X,
      (xf n, yf n) ∈ Af ×ˢ Af := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    obtain ⟨h1, h2, h3⟩ := hxy n hn.1
    rw [Finset.mem_product, hAf, Finset.mem_filter,
      Finset.mem_filter, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨by omega, h1⟩, ⟨by omega, h2⟩⟩
  have hinj : Set.InjOn (fun n => (xf n, yf n))
      (Finset.Icc N₀ X) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_Icc] at ha hb
    obtain ⟨_, _, h3⟩ := hxy a ha.1
    obtain ⟨_, _, h3'⟩ := hxy b hb.1
    have h4 : xf a = xf b := congrArg Prod.fst hab
    have h5 : yf a = yf b := congrArg Prod.snd hab
    omega
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Nat.card_Icc, Finset.card_product] at hcard
  have h6 : Af.card * Af.card = Af.card ^ 2 := by ring
  omega

open Classical in

theorem cofinal_supply_pair_required_element {A : Set ℕ} {N₀ X : ℕ}
    {P : Finset ℕ}
    (h0 : 0 ∈ A) (h0P : (0 : ℕ) ∉ P)
    (hflood : ∀ b ∈ A, X ≤ b → ∃ m, N₀ ≤ m ∧ b ≤ m ∧
      IsRepSupportTransversal A m (insert b P)) :
    ∀ b ∈ A, X ≤ b → 0 < b → ∃ m, N₀ ≤ m ∧ b ≤ m ∧
      IsRepSupportTransversal A m (insert b P) ∧
      IsPairSupportTransversal A m (insert b P) ∧
      ((Finset.range (m + 1)).filter
        (fun a => a ∈ A ∧ (m - a) ∈ A ∧ 2 * a ≤ m)).card ≤
        P.card + 1 := by
  intro b hbA hXb hbpos
  obtain ⟨m, hmN, hbm, hhub⟩ := hflood b hbA hXb
  have h0i : (0 : ℕ) ∉ insert b P := by
    intro h
    rcases Finset.mem_insert.1 h with h | h
    · omega
    · exact h0P h
  have hpair := pairSupportTransversal_of_repSupportTransversal h0 h0i hhub
  refine ⟨m, hmN, hbm, hhub, hpair, ?_⟩
  have h1 := pair_support_transversal_pair_count hpair
  have h2 : (insert b P).card ≤ P.card + 1 :=
    Finset.card_insert_le _ _
  omega

theorem rep_cofinal_supply_pos_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P : Finset ℕ, RepFree A N₀ P ∧ (0 : ℕ) ∉ P ∧
      ∃ X, ∀ b ∈ A, X ≤ b →
      ∃ m, N₀ ≤ m ∧ b ≤ m ∧ IsRepSupportTransversal A m (insert b P) := by
  classical
  by_contra hno
  push Not at hno
  have hfree0 : RepFree A N₀ ∅ := by
    intro m hm
    obtain ⟨x, hx, y, hy, hxy⟩ := hcov m hm
    exact ⟨x, hx, y, hy, 0, h0, by omega, Finset.notMem_empty x,
      Finset.notMem_empty y, Finset.notMem_empty 0⟩
  have hpick : ∀ (P : Finset ℕ) (X : ℕ), ∃ b, b ∈ A ∧ X ≤ b ∧
      (RepFree A N₀ P → (0 : ℕ) ∉ P → ∀ m, N₀ ≤ m → b ≤ m →
        ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = m ∧
          x ∉ insert b P ∧ y ∉ insert b P ∧ z ∉ insert b P) := by
    intro P X
    by_cases hfree : RepFree A N₀ P
    · by_cases h0P : (0 : ℕ) ∉ P
      · obtain ⟨b, hbA, hXb, hbgood⟩ := hno P hfree h0P X
        refine ⟨b, hbA, hXb, fun _ _ m hm hbm => ?_⟩
        have hnh := hbgood m hm hbm
        rw [IsRepSupportTransversal] at hnh
        push Not at hnh
        obtain ⟨x, hx, y, hy, z, hz, hxyz, hxP, hyP, hzP⟩ := hnh
        exact ⟨x, hx, y, hy, z, hz, hxyz, hxP, hyP, hzP⟩
      · obtain ⟨b, hbA, hXb⟩ := pairCovers_unbounded hcov X
        exact ⟨b, hbA, hXb, fun _ h => absurd h h0P⟩
    · obtain ⟨b, hbA, hXb⟩ := pairCovers_unbounded hcov X
      exact ⟨b, hbA, hXb, fun h => absurd h hfree⟩
  choose pick hpickA hpickge hpickfree using hpick
  set st : ℕ → ℕ × Finset ℕ := fun j =>
    Nat.rec (pick ∅ 1, {pick ∅ 1})
      (fun _ prev => (pick prev.2 (prev.1 + 1),
        insert (pick prev.2 (prev.1 + 1)) prev.2)) j with hst
  have hstS : ∀ j, st (j + 1) = (pick (st j).2 ((st j).1 + 1),
      insert (pick (st j).2 ((st j).1 + 1)) (st j).2) := fun _ => rfl
  have h0S : ∀ j, (0 : ℕ) ∉ (st j).2 := by
    intro j
    induction j with
    | zero =>
      show (0 : ℕ) ∉ ({pick ∅ 1} : Finset ℕ)
      rw [Finset.mem_singleton]
      have h1 := hpickge ∅ 1
      omega
    | succ j ih =>
      rw [hstS]
      intro hmem
      rcases Finset.mem_insert.1 hmem with h | h
      · have h1 := hpickge (st j).2 ((st j).1 + 1)
        omega
      · exact ih h
  have hfreeS : ∀ j, RepFree A N₀ (st j).2 := by
    intro j
    induction j with
    | zero =>
      show RepFree A N₀ (insert (pick ∅ 1) ∅)
      exact repFree_insert hfree0
        (hpickfree ∅ 1 hfree0 (Finset.notMem_empty 0))
    | succ j ih =>
      rw [show (st (j + 1)).2 =
          insert (pick (st j).2 ((st j).1 + 1)) (st j).2 from
        by rw [hstS]]
      exact repFree_insert ih
        (hpickfree (st j).2 ((st j).1 + 1) ih (h0S j))
  have hlastge : ∀ j, j + 1 ≤ (st j).1 := by
    intro j
    induction j with
    | zero => simpa using hpickge ∅ 1
    | succ j ih =>
      have h1 : (st (j + 1)).1 = pick (st j).2 ((st j).1 + 1) := by
        rw [hstS]
      have h2 := hpickge (st j).2 ((st j).1 + 1)
      omega
  have hchain : ∀ i j, i ≤ j → (st i).2 ⊆ (st j).2 := by
    intro i j hij
    induction j with
    | zero =>
      have h0' : i = 0 := by omega
      subst h0'
      exact Finset.Subset.refl _
    | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h' | h'
      · refine Finset.Subset.trans (ih (by omega)) ?_
        rw [hstS]
        exact Finset.subset_insert _ _
      · have h1 : i = j + 1 := by omega
        subst h1
        exact Finset.Subset.refl _
  have hlastmem : ∀ j, (st j).1 ∈ (st j).2 := by
    intro j
    cases j with
    | zero => exact Finset.mem_singleton_self _
    | succ j =>
      rw [hstS]
      exact Finset.mem_insert_self _ _
  have hlaststep : ∀ j, (st j).1 < (st (j + 1)).1 := by
    intro j
    have h1 : (st (j + 1)).1 = pick (st j).2 ((st j).1 + 1) := by
      rw [hstS]
    have h2 := hpickge (st j).2 ((st j).1 + 1)
    omega
  have hlastmono : StrictMono (fun j => (st j).1) :=
    strictMono_nat_of_lt_succ hlaststep
  set B : Set ℕ := Set.range (fun j => (st j).1) with hB
  have hBA : B ⊆ A := by
    rintro x ⟨j, rfl⟩
    show (st j).1 ∈ A
    cases j with
    | zero => exact hpickA ∅ 1
    | succ j =>
      rw [show (st (j + 1)).1 = pick (st j).2 ((st j).1 + 1) from
        by rw [hstS]]
      exact hpickA _ _
  have hBinf : B.Infinite :=
    Set.infinite_range_of_injective hlastmono.injective
  refine hfail B hBA hBinf ⟨N₀, fun m hm => ?_⟩
  obtain ⟨x, hx, y, hy, z, hz, hxyz, hxP, hyP, hzP⟩ := hfreeS m m hm
  have havoid : ∀ w, w ≤ m → w ∉ (st m).2 → w ∉ B := by
    intro w hwm hwP
    rintro ⟨i, hi⟩
    have hi' : (st i).1 = w := hi
    rcases Nat.lt_or_ge m i with h' | h'
    · have := hlastge i
      omega
    · exact hwP (by
        rw [← hi']
        exact hchain i m h' (hlastmem i))
  refine ⟨![x, y, z], ?_, by simp [Fin.sum_univ_three]; omega⟩
  intro i
  match i with
  | 0 => exact ⟨hx, havoid x (by omega) hxP⟩
  | 1 => exact ⟨hy, havoid y (by omega) hyP⟩
  | 2 => exact ⟨hz, havoid z (by omega) hzP⟩

open Classical in

theorem personal_pair_required_element_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P : Finset ℕ, RepFree A N₀ P ∧ (0 : ℕ) ∉ P ∧
      ∃ X, ∀ b ∈ A, X ≤ b → 0 < b →
      ∃ m, N₀ ≤ m ∧ b ≤ m ∧ IsRepSupportTransversal A m (insert b P) ∧
      IsPairSupportTransversal A m (insert b P) ∧
      ((Finset.range (m + 1)).filter
        (fun a => a ∈ A ∧ (m - a) ∈ A ∧ 2 * a ≤ m)).card ≤
        P.card + 1 := by
  obtain ⟨P, hPfree, h0P, X, hflood⟩ :=
    rep_cofinal_supply_pos_of_hfail h0 hcov hfail
  exact ⟨P, hPfree, h0P, X,
    cofinal_supply_pair_required_element h0 h0P hflood⟩

open Classical in

theorem pair_cofinal_supply_outside_basis_or_center {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P : Finset ℕ, RepFree A N₀ P ∧ (0 : ℕ) ∉ P ∧
      ∃ X, ∀ b ∈ A, X ≤ b →
      ∃ m, N₀ ≤ m ∧ b ≤ m ∧ IsRepSupportTransversal A m (insert b P) ∧
      IsPairSupportTransversal A m (insert b P) ∧
      ((Finset.range (m + 1)).filter
        (fun a => a ∈ A ∧ (m - a) ∈ A ∧ 2 * a ≤ m)).card ≤
        P.card + 1 ∧
      (m = b ∨ m ∉ A) := by
  obtain ⟨P, hPfree, h0P, X, hguard⟩ :=
    personal_pair_required_element_of_hfail h0 hcov hfail
  refine ⟨P, hPfree, h0P, max X (P.sup id + 1), ?_⟩
  intro b hbA hXb
  have hbX : X ≤ b := le_trans (le_max_left _ _) hXb
  have hbP : P.sup id + 1 ≤ b := le_trans (le_max_right _ _) hXb
  obtain ⟨m, hmN, hbm, hrep, hpair, hcount⟩ :=
    hguard b hbA hbX (by omega)
  refine ⟨m, hmN, hbm, hrep, hpair, hcount, ?_⟩
  have h0i : (0 : ℕ) ∉ insert b P := by
    intro h
    rcases Finset.mem_insert.1 h with h | h
    · omega
    · exact h0P h
  rcases target_sequence_target_notMem_or_window h0 h0i hpair with
    h | h
  · exact Or.inr h
  · rcases Finset.mem_insert.1 h with h1 | h1
    · exact Or.inl h1
    · exfalso
      have h2 : m ≤ P.sup id := Finset.le_sup (f := id) h1
      omega

open Classical in

theorem pair_cofinal_supply_transversal_family {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P : Finset ℕ, RepFree A N₀ P ∧ (0 : ℕ) ∉ P ∧
    ((∀ N, ∃ b, N ≤ b ∧ b ∈ A ∧ ∀ x ∈ A, ∀ y ∈ A,
        0 < x → 0 < y → x + y = b → x ∈ P ∨ y ∈ P) ∨
     (∀ N, ∃ b w, N ≤ b ∧ b ∈ A ∧ w ∈ A ∧ b + w ∉ A ∧
        IsRepSupportTransversal A (b + w) (insert b P) ∧
        IsPairSupportTransversal A (b + w) (insert b P)) ∨
     (∀ N, ∃ m b, N ≤ b ∧ b ≤ m ∧ b ∈ A ∧ m ∉ A ∧
        IsRepSupportTransversal A m (insert b P) ∧ IsPairSupportTransversal A m P)) := by
  obtain ⟨P, hPfree, h0P, X, hguard⟩ :=
    pair_cofinal_supply_outside_basis_or_center h0 hcov hfail
  refine ⟨P, hPfree, h0P, ?_⟩
  by_cases hI : ∀ N, ∃ b, N ≤ b ∧ b ∈ A ∧ ∀ x ∈ A, ∀ y ∈ A,
      0 < x → 0 < y → x + y = b → x ∈ P ∨ y ∈ P
  · exact Or.inl hI
  · obtain ⟨NA, hNA⟩ := not_forall.mp hI
    by_cases hII : ∀ N, ∃ b w, N ≤ b ∧ b ∈ A ∧ w ∈ A ∧
        b + w ∉ A ∧ IsRepSupportTransversal A (b + w) (insert b P) ∧
        IsPairSupportTransversal A (b + w) (insert b P)
    · exact Or.inr (Or.inl hII)
    · obtain ⟨NB, hNB⟩ := not_forall.mp hII
      refine Or.inr (Or.inr ?_)
      intro N
      obtain ⟨b, hbA, hbig⟩ := pairCovers_unbounded hcov
        (X + NA + NB + N + 1)
      obtain ⟨m, hmN, hbm, hrep, hpair, hcount, hplace⟩ :=
        hguard b hbA (by omega)
      rcases hplace with hcen | hghost
      · exfalso
        apply hNA
        refine ⟨b, by omega, hbA, ?_⟩
        intro x hx y hy hx0 hy0 hxy
        have hxb : x ≠ b := by omega
        have hyb : y ≠ b := by omega
        rcases hpair x hx y hy (by omega) with h | h
        · rcases Finset.mem_insert.1 h with h' | h'
          · exact absurd h' hxb
          · exact Or.inl h'
        · rcases Finset.mem_insert.1 h with h' | h'
          · exact absurd h' hyb
          · exact Or.inr h'
      · by_cases hbpart : m - b ∈ A
        · exfalso
          apply hNB
          refine ⟨b, m - b, by omega, hbA, hbpart, ?_, ?_, ?_⟩
          · have h1 : b + (m - b) = m := by omega
            rw [h1]
            exact hghost
          · have h1 : b + (m - b) = m := by omega
            rw [h1]
            exact hrep
          · have h1 : b + (m - b) = m := by omega
            rw [h1]
            exact hpair
        · refine ⟨m, b, by omega, hbm, hbA, hghost,
            hrep, ?_⟩
          intro x hx y hy hxy
          have hxm : x ≠ b := by
            intro h
            subst h
            have h1 : y = m - x := by omega
            rw [h1] at hy
            exact hbpart hy
          have hym : y ≠ b := by
            intro h
            subst h
            have h1 : x = m - y := by omega
            rw [h1] at hx
            exact hbpart hx
          rcases hpair x hx y hy hxy with h | h
          · rcases Finset.mem_insert.1 h with h' | h'
            · exact absurd h' hxm
            · exact Or.inl h'
          · rcases Finset.mem_insert.1 h with h' | h'
            · exact absurd h' hym
            · exact Or.inr h'

theorem pure_hall_singleton_form {A : Set ℕ} {N₀ p : ℕ}
    (hcov : PairCovers A N₀)
    (hface : ∀ N, ∃ m, N ≤ m ∧ m ∉ A ∧
      IsPairSupportTransversal A m ({p} : Finset ℕ)) :
    ∀ N, ∃ m, N ≤ m ∧ m ∉ A ∧ p ≤ m ∧ m - p ∈ A ∧
      ∀ x ∈ A, ∀ y ∈ A, x + y = m →
        (x = p ∧ y = m - p) ∨ (x = m - p ∧ y = p) := by
  intro N
  obtain ⟨m, hmN, hmA, hhub⟩ := hface (N + N₀)
  obtain ⟨a, haA, b, hbA, hab⟩ := hcov m (by omega)
  have hpart : p ≤ m ∧ m - p ∈ A := by
    rcases hhub a haA b hbA hab with h | h
    · rw [Finset.mem_singleton] at h
      subst h
      have h1 : m - a = b := by omega
      rw [h1]
      exact ⟨by omega, hbA⟩
    · rw [Finset.mem_singleton] at h
      subst h
      have h1 : m - b = a := by omega
      rw [h1]
      exact ⟨by omega, haA⟩
  refine ⟨m, by omega, hmA, hpart.1, hpart.2, ?_⟩
  intro x hx y hy hxy
  rcases hhub x hx y hy hxy with h | h
  · rw [Finset.mem_singleton] at h
    exact Or.inl ⟨h, by omega⟩
  · rw [Finset.mem_singleton] at h
    exact Or.inr ⟨by omega, h⟩

theorem face_three_color_law {A : Set ℕ} {N₀ M₀ m b : ℕ}
    {P : Finset ℕ}
    (hcov : PairCovers A N₀) (hM : ∀ p ∈ P, p ≤ M₀)
    (hrep : IsRepSupportTransversal A m (insert b P))
    (hpair : IsPairSupportTransversal A m P)
    {z : ℕ} (hz : z ∈ A) (hzM : M₀ < z) (hzb : z ≠ b)
    (hsize : z + b + 2 * M₀ + N₀ + 1 ≤ m) :
    ∃ h ∈ insert b P, h + z ≤ m ∧ m - z - h ∈ A ∧
      z + h ∉ A := by
  have hzH : z ∉ insert b P := by
    intro h
    rcases Finset.mem_insert.1 h with h1 | h1
    · exact hzb h1
    · have := hM z h1
      omega
  obtain ⟨h, hhH, hhz, hmir⟩ :=
    hall_mirror hcov hrep hz hzH (by omega)
  refine ⟨h, hhH, hhz, hmir, ?_⟩
  intro hzhA
  have hsum : (z + h) + (m - z - h) = m := by omega
  rcases hpair (z + h) hzhA (m - z - h) hmir hsum with h1 | h1
  · have h2 := hM _ h1
    omega
  · have h2 := hM _ h1
    rcases Finset.mem_insert.1 hhH with h3 | h3
    · omega
    · have h4 := hM _ h3
      omega

theorem face_three_gap_dichotomy {A : Set ℕ} {N₀ M₀ : ℕ}
    {P : Finset ℕ}
    (hcov : PairCovers A N₀) (hM : ∀ p ∈ P, p ≤ M₀)
    (hface : ∀ N, ∃ m b, N ≤ b ∧ b ≤ m ∧ b ∈ A ∧ m ∉ A ∧
      IsRepSupportTransversal A m (insert b P) ∧ IsPairSupportTransversal A m P) :
    (∃ G, ∀ N, ∃ m b, N ≤ b ∧ b ≤ m ∧ m ≤ b + G ∧ b ∈ A ∧
      m ∉ A ∧ IsRepSupportTransversal A m (insert b P) ∧ IsPairSupportTransversal A m P) ∨
    (∀ z ∈ A, M₀ < z →
      (∃ p ∈ P, z + p ∉ A) ∨
      (∀ N, ∃ b, N ≤ b ∧ b ∈ A ∧ z + b ∉ A)) := by
  classical
  by_cases hbdd : ∃ G, ∀ N, ∃ m b, N ≤ b ∧ b ≤ m ∧
      m ≤ b + G ∧ b ∈ A ∧ m ∉ A ∧
      IsRepSupportTransversal A m (insert b P) ∧ IsPairSupportTransversal A m P
  · exact Or.inl hbdd
  · right
    intro z hzA hzM
    by_cases hzP : ∃ p ∈ P, z + p ∉ A
    · exact Or.inl hzP
    · push Not at hzP
      right
      intro N
      set G := z + 2 * M₀ + N₀ + 1 with hG
      have hnb : ¬∀ N', ∃ m b, N' ≤ b ∧ b ≤ m ∧ m ≤ b + G ∧
          b ∈ A ∧ m ∉ A ∧ IsRepSupportTransversal A m (insert b P) ∧
          IsPairSupportTransversal A m P := fun hall => hbdd ⟨G, hall⟩
      obtain ⟨NG, hNG⟩ := not_forall.mp hnb
      obtain ⟨m, b, hNb, hbm, hbA, hmA, hrep, hpair⟩ :=
        hface (N + NG + z + 1)
      have hgap : b + G < m := by
        by_contra hle
        exact hNG ⟨m, b, by omega, hbm, by omega, hbA, hmA,
          hrep, hpair⟩
      obtain ⟨h, hhH, hhz, hmir, hdead⟩ :=
        face_three_color_law hcov hM hrep hpair hzA hzM
          (by omega) (by omega)
      rcases Finset.mem_insert.1 hhH with h1 | h1
      · exact ⟨b, by omega, hbA, h1 ▸ hdead⟩
      · exact absurd (hzP h h1) hdead

theorem near_diagonal_stabilized {A : Set ℕ} {G : ℕ}
    {P : Finset ℕ}
    (hbdd : ∀ N, ∃ m b, N ≤ b ∧ b ≤ m ∧ m ≤ b + G ∧ b ∈ A ∧
      m ∉ A ∧ IsRepSupportTransversal A m (insert b P) ∧ IsPairSupportTransversal A m P) :
    ∃ g, g ≤ G ∧ ∀ N, ∃ b, N ≤ b ∧ b ∈ A ∧ b + g ∉ A ∧
      IsRepSupportTransversal A (b + g) (insert b P) ∧
      IsPairSupportTransversal A (b + g) P := by
  classical
  by_contra hno
  push Not at hno
  have hKg : ∀ g : ℕ, ∃ Kg, g ≤ G → ∀ b, Kg ≤ b → b ∈ A →
      b + g ∉ A → IsRepSupportTransversal A (b + g) (insert b P) →
      ¬IsPairSupportTransversal A (b + g) P := by
    intro g
    by_cases hgG : g ≤ G
    · obtain ⟨Kg, hKg'⟩ := hno g hgG
      exact ⟨Kg, fun _ => hKg'⟩
    · exact ⟨0, fun h => absurd h hgG⟩
  choose Kf hKf using hKg
  obtain ⟨m, b, hNb, hbm, hmG, hbA, hmA, hrep, hpair⟩ :=
    hbdd ((Finset.range (G + 1)).sup Kf + 1)
  set g := m - b with hg
  have hgG : g ≤ G := by omega
  have hKle : Kf g ≤ (Finset.range (G + 1)).sup Kf :=
    Finset.le_sup (f := Kf) (Finset.mem_range.2 (by omega))
  have hmbg : m = b + g := by omega
  rw [hmbg] at hmA hrep hpair
  exact hKf g hgG b (by omega) hbA hmA hrep hpair

theorem face_one_split {A : Set ℕ} {P : Finset ℕ}
    (hface : ∀ N, ∃ b, N ≤ b ∧ b ∈ A ∧ ∀ x ∈ A, ∀ y ∈ A,
      0 < x → 0 < y → x + y = b → x ∈ P ∨ y ∈ P) :
    (∀ N, ∃ b, N ≤ b ∧ b ∈ A ∧
      (∃ x ∈ A, ∃ y ∈ A, 0 < x ∧ 0 < y ∧ x + y = b) ∧
      (∀ x ∈ A, ∀ y ∈ A, 0 < x → 0 < y → x + y = b →
        x ∈ P ∨ y ∈ P)) ∨
    (∀ N, ∃ b, N ≤ b ∧ b ∈ A ∧
      ∀ x ∈ A, ∀ y ∈ A, 0 < x → 0 < y → x + y ≠ b) := by
  classical
  by_cases hIa : ∀ N, ∃ b, N ≤ b ∧ b ∈ A ∧
      (∃ x ∈ A, ∃ y ∈ A, 0 < x ∧ 0 < y ∧ x + y = b) ∧
      (∀ x ∈ A, ∀ y ∈ A, 0 < x → 0 < y → x + y = b →
        x ∈ P ∨ y ∈ P)
  · exact Or.inl hIa
  · right
    obtain ⟨NA, hNA⟩ := not_forall.mp hIa
    intro N
    obtain ⟨b, hNb, hbA, hcen⟩ := hface (N + NA)
    by_cases hpos : ∃ x ∈ A, ∃ y ∈ A, 0 < x ∧ 0 < y ∧
        x + y = b
    · exact absurd ⟨b, by omega, hbA, hpos, hcen⟩ hNA
    · push Not at hpos
      refine ⟨b, by omega, hbA, ?_⟩
      intro x hx y hy hx0 hy0 hxy
      exact hpos x hx y hy hx0 hy0 hxy

theorem free_tower_mirror {A : Set ℕ} {N₀ M₀ g b : ℕ}
    {P : Finset ℕ}
    (hcov : PairCovers A N₀) (hM : ∀ p ∈ P, p ≤ M₀)
    (hrep : IsRepSupportTransversal A (b + g) (insert b P))
    (hpair : IsPairSupportTransversal A (b + g) P)
    {z : ℕ} (hz : z ∈ A) (hzM : M₀ < z) (hzg : g < z)
    (hsize : z + 2 * M₀ + N₀ + 1 ≤ b) :
    ∃ p ∈ P, p + z ≤ b + g ∧ b + g - z - p ∈ A ∧
      z + p ∉ A := by
  have hzH : z ∉ insert b P := by
    intro h
    rcases Finset.mem_insert.1 h with h1 | h1
    · omega
    · have := hM z h1
      omega
  obtain ⟨h, hhH, hhz, hmir⟩ :=
    hall_mirror hcov hrep hz hzH (by omega)
  rcases Finset.mem_insert.1 hhH with h1 | h1
  · exfalso
    omega
  · refine ⟨h, h1, hhz, hmir, ?_⟩
    intro hzhA
    have hsum : (z + h) + (b + g - z - h) = b + g := by omega
    rcases hpair (z + h) hzhA (b + g - z - h) hmir hsum with
      h2 | h2
    · have := hM _ h2
      omega
    · have h3 := hM _ h2
      have h4 := hM h h1
      omega

theorem free_tower_singleton_levels {A : Set ℕ}
    {N₀ M₀ g b p : ℕ}
    (hcov : PairCovers A N₀) (hM : p ≤ M₀)
    (hrep : IsRepSupportTransversal A (b + g) (insert b {p}))
    (hpair : IsPairSupportTransversal A (b + g) ({p} : Finset ℕ)) :
    ∀ z ∈ A, M₀ < z → g < z → z + 2 * M₀ + N₀ + 1 ≤ b →
      p + z ≤ b + g ∧ (b + g - p) - z ∈ A ∧ z + p ∉ A := by
  intro z hz hzM hzg hsize
  have hM' : ∀ q ∈ ({p} : Finset ℕ), q ≤ M₀ := by
    intro q hq
    rw [Finset.mem_singleton] at hq
    omega
  obtain ⟨q, hqP, hqz, hmir, hdead⟩ :=
    free_tower_mirror hcov hM' hrep hpair hz hzM hzg hsize
  rw [Finset.mem_singleton] at hqP
  subst hqP
  have h1 : b + g - z - q = (b + g - q) - z := by omega
  rw [h1] at hmir
  exact ⟨by omega, hmir, hdead⟩

theorem pair_support_transversal_corep {A : Set ℕ} {N₀ m p : ℕ}
    (hcov : PairCovers A N₀) (hm : N₀ ≤ m)
    (hpair : IsPairSupportTransversal A m ({p} : Finset ℕ)) :
    p ≤ m ∧ m - p ∈ A := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov m hm
  rcases hpair x hx y hy hxy with h | h
  · rw [Finset.mem_singleton] at h
    subst h
    have h1 : m - x = y := by omega
    rw [h1]
    exact ⟨by omega, hy⟩
  · rw [Finset.mem_singleton] at h
    subst h
    have h1 : m - y = x := by omega
    rw [h1]
    exact ⟨by omega, hx⟩

theorem no_sequence_affine_exclusion_interval {A : Set ℕ}
    {N₀ M₀ g b p T : ℕ}
    (hcov : PairCovers A N₀) (hM : p ≤ M₀)
    (hrep : IsRepSupportTransversal A (b + g) (insert b {p}))
    (hpair : IsPairSupportTransversal A (b + g) ({p} : Finset ℕ))
    (hnl : ∀ c ∈ A, T ≤ c → p ≤ 2 * c → 2 * c - p ∉ A) :
    ∀ z ∈ A, M₀ < z → g < z → z + 2 * M₀ + N₀ + 1 ≤ b →
      z + T + p ≤ b + g →
      2 * (b + g - p) - 2 * z - p ∉ A := by
  intro z hz h1 h2 h3 h4
  obtain ⟨hle, hmir, hdead⟩ :=
    free_tower_singleton_levels hcov hM hrep hpair z hz h1 h2 h3
  have hcT : T ≤ (b + g - p) - z := by omega
  have hp2c : p ≤ 2 * ((b + g - p) - z) := by omega
  have hout := hnl _ hmir hcT hp2c
  have he : 2 * ((b + g - p) - z) - p =
      2 * (b + g - p) - 2 * z - p := by omega
  rw [he] at hout
  exact hout

open Classical in

theorem window_populated {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀) :
    ∀ Y X, N₀ ≤ X → X - N₀ + 1 ≤
      ((((Finset.range (X + 1)).filter (· ∈ A)).filter
        (fun a => Y < a)).card + Y + 1) ^ 2 := by
  intro Y X hX
  have hd := covering_density hcov X hX
  set AX := (Finset.range (X + 1)).filter (· ∈ A) with hAX
  set W := AX.filter (fun a => Y < a) with hW
  have hsplit : AX.card ≤ (Y + 1) + W.card := by
    have hsub : AX ⊆ (Finset.range (Y + 1)) ∪ W := by
      intro a ha
      rcases Nat.lt_or_ge Y a with h | h
      · exact Finset.mem_union_right _
          (by rw [hW, Finset.mem_filter]; exact ⟨ha, h⟩)
      · exact Finset.mem_union_left _
          (Finset.mem_range.2 (by omega))
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (Finset.range (Y + 1)) W
    rw [Finset.card_range] at h2
    omega
  have hpow : AX.card ^ 2 ≤ ((Y + 1) + W.card) ^ 2 :=
    Nat.pow_le_pow_left hsplit 2
  have he : (Y + 1) + W.card = W.card + Y + 1 := by omega
  rw [he] at hpow
  omega

theorem personal_fragility {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P : Finset ℕ, RepFree A N₀ P ∧ (0 : ℕ) ∉ P ∧
      ∃ X, ∀ b ∈ A, X ≤ b → 0 < b →
      ∃ m, N₀ ≤ m ∧ b ≤ m ∧
        ¬HasDisjointTripleReps A m (P.card + 2) := by
  obtain ⟨P, hPfree, h0P, X, hguard⟩ :=
    personal_pair_required_element_of_hfail h0 hcov hfail
  refine ⟨P, hPfree, h0P, X, ?_⟩
  intro b hbA hXb hbpos
  obtain ⟨m, hmN, hbm, hrep, hpair, hcount⟩ :=
    hguard b hbA hXb hbpos
  refine ⟨m, hmN, hbm, ?_⟩
  intro hK
  have h1 := disjoint_reps_le_support_transversal_card hrep hK
  have h2 : (insert b P).card ≤ P.card + 1 :=
    Finset.card_insert_le _ _
  omega

theorem parity_window_fringe {A : Set ℕ} {Y X ε : ℕ}
    (hpar : ∀ a ∈ A, Y < a → a ≤ X → a % 2 = ε) :
    ∀ n, n ≤ X → n % 2 = 1 →
      ∀ x ∈ A, ∀ y ∈ A, x + y = n → x ≤ Y ∨ y ≤ Y := by
  intro n hnX hodd x hx y hy hxy
  by_contra hno
  push Not at hno
  have h1 := hpar x hx (by omega) (by omega)
  have h2 := hpar y hy (by omega) (by omega)
  omega

theorem parity_window_partner {A : Set ℕ} {N₀ Y X ε : ℕ}
    (hcov : PairCovers A N₀)
    (hpar : ∀ a ∈ A, Y < a → a ≤ X → a % 2 = ε) :
    ∀ n, N₀ ≤ n → n ≤ X → n % 2 = 1 →
      ∃ x ∈ A, x ≤ Y ∧ n - x ∈ A := by
  intro n hnN hnX hodd
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov n hnN
  rcases parity_window_fringe hpar n hnX hodd x hx y hy hxy
    with h | h
  · refine ⟨x, hx, h, ?_⟩
    have h1 : n - x = y := by omega
    rw [h1]
    exact hy
  · refine ⟨y, hy, h, ?_⟩
    have h1 : n - y = x := by omega
    rw [h1]
    exact hx

theorem parity_window_syndetic {A : Set ℕ} {N₀ Y X ε : ℕ}
    (hcov : PairCovers A N₀)
    (hpar : ∀ a ∈ A, Y < a → a ≤ X → a % 2 = ε) :
    ∀ u, N₀ + Y ≤ u → u + 2 * Y + 2 ≤ X →
      ∃ a ∈ A, u ≤ a ∧ a ≤ u + 2 * Y + 2 := by
  intro u hu hX
  rcases Nat.mod_two_eq_zero_or_one (u + Y + 1) with h | h
  · obtain ⟨x, hx, hxY, hpart⟩ :=
      parity_window_partner hcov hpar (u + Y + 2)
        (by omega) (by omega) (by omega)
    exact ⟨u + Y + 2 - x, hpart, by omega, by omega⟩
  · obtain ⟨x, hx, hxY, hpart⟩ :=
      parity_window_partner hcov hpar (u + Y + 1)
        (by omega) (by omega) (by omega)
    exact ⟨u + Y + 1 - x, hpart, by omega, by omega⟩

open Classical in

theorem parity_window_linear_density {A : Set ℕ}
    {N₀ Y X ε : ℕ}
    (hcov : PairCovers A N₀)
    (hpar : ∀ a ∈ A, Y < a → a ≤ X → a % 2 = ε) :
    ∀ u k, N₀ + Y ≤ u → u + k * (2 * Y + 3) ≤ X →
      k ≤ ((Finset.Ioc u (u + k * (2 * Y + 3))).filter
        (· ∈ A)).card := by
  intro u k hu hX
  have hblock : ∀ j, ∃ a, j < k →
      a ∈ A ∧ u + j * (2 * Y + 3) < a ∧
      a ≤ u + (j + 1) * (2 * Y + 3) := by
    intro j
    by_cases hj : j < k
    · have h1 : (j + 1) * (2 * Y + 3) ≤ k * (2 * Y + 3) :=
        Nat.mul_le_mul_right _ (by omega)
      have h2 : j * (2 * Y + 3) + (2 * Y + 3) =
          (j + 1) * (2 * Y + 3) := by ring
      obtain ⟨a, haA, ha1, ha2⟩ :=
        parity_window_syndetic hcov hpar
          (u + j * (2 * Y + 3) + 1) (by omega) (by omega)
      exact ⟨a, fun _ => ⟨haA, by omega, by omega⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose af haf using hblock
  have hmaps : ∀ j ∈ Finset.range k, af j ∈
      (Finset.Ioc u (u + k * (2 * Y + 3))).filter (· ∈ A) := by
    intro j hj
    rw [Finset.mem_range] at hj
    obtain ⟨h1, h2, h3⟩ := haf j hj
    have h4 : (j + 1) * (2 * Y + 3) ≤ k * (2 * Y + 3) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Finset.mem_filter, Finset.mem_Ioc]
    have h5 : 0 ≤ j * (2 * Y + 3) := Nat.zero_le _
    exact ⟨⟨by omega, by omega⟩, h1⟩
  have hinj : Set.InjOn af (Finset.range k) := by
    intro i hi j hj hij
    rw [Finset.mem_coe, Finset.mem_range] at hi hj
    by_contra hne
    obtain ⟨_, hi1, hi2⟩ := haf i hi
    obtain ⟨_, hj1, hj2⟩ := haf j hj
    rcases Nat.lt_or_ge i j with h | h
    · have h1 : (i + 1) * (2 * Y + 3) ≤ j * (2 * Y + 3) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    · have h2 : i ≠ j := hne
      have h3 : j < i := by omega
      have h1 : (j + 1) * (2 * Y + 3) ≤ i * (2 * Y + 3) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
  have hcard := Finset.card_le_card_of_injOn af hmaps hinj
  rw [Finset.card_range] at hcard
  exact hcard

open Classical in

theorem dense_window_high_pairs {A : Set ℕ} {u v K : ℕ}
    (hlt : 2 * (v - u) * K <
      (((Finset.Ioc u v).filter (· ∈ A)).card) ^ 2) :
    ∃ m, 2 * u < m ∧ m ≤ 2 * v ∧
      K < ((((Finset.Ioc u v).filter (· ∈ A)) ×ˢ
        ((Finset.Ioc u v).filter (· ∈ A))).filter
          (fun q => q.1 + q.2 = m)).card := by
  set W := (Finset.Ioc u v).filter (· ∈ A) with hW
  have hmaps : ∀ q ∈ W ×ˢ W,
      q.1 + q.2 ∈ Finset.Ioc (2 * u) (2 * v) := by
    intro q hq
    rw [Finset.mem_product] at hq
    obtain ⟨h1, h2⟩ := hq
    rw [hW, Finset.mem_filter, Finset.mem_Ioc] at h1 h2
    rw [Finset.mem_Ioc]
    omega
  have hcard : (Finset.Ioc (2 * u) (2 * v)).card * K <
      (W ×ˢ W).card := by
    rw [Nat.card_Ioc]
    have h2 : 2 * v - 2 * u = 2 * (v - u) := by omega
    rw [h2, Finset.card_product]
    have h1 : W.card * W.card = W.card ^ 2 := by ring
    omega
  obtain ⟨m, hm, hfib⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      hmaps hcard
  rw [Finset.mem_Ioc] at hm
  exact ⟨m, hm.1, hm.2, hfib⟩

open Classical in

theorem pair_fiber_support_transversal_bound {A : Set ℕ} {u v m : ℕ}
    {H : Finset ℕ} (hhub : IsPairSupportTransversal A m H) :
    ((((Finset.Ioc u v).filter (· ∈ A)) ×ˢ
      ((Finset.Ioc u v).filter (· ∈ A))).filter
        (fun q => q.1 + q.2 = m)).card ≤ 2 * H.card := by
  set W := (Finset.Ioc u v).filter (· ∈ A) with hW
  set F := (W ×ˢ W).filter (fun q => q.1 + q.2 = m) with hF
  have hmaps : ∀ q ∈ F, (if q.1 ∈ H then q.1 else q.2) ∈ H := by
    intro q hq
    rw [hF, Finset.mem_filter, Finset.mem_product] at hq
    obtain ⟨⟨h1, h2⟩, h3⟩ := hq
    rw [hW, Finset.mem_filter] at h1 h2
    by_cases hq1 : q.1 ∈ H
    · rw [if_pos hq1]
      exact hq1
    · rw [if_neg hq1]
      rcases hhub q.1 h1.2 q.2 h2.2 h3 with h | h
      · exact absurd h hq1
      · exact h
  have hfib : ∀ h ∈ H, (F.filter
      (fun q => (if q.1 ∈ H then q.1 else q.2) = h)).card ≤ 2 := by
    intro h hh
    have hsub : F.filter
        (fun q => (if q.1 ∈ H then q.1 else q.2) = h) ⊆
        {(h, m - h), (m - h, h)} := by
      intro q hq
      rw [Finset.mem_filter] at hq
      obtain ⟨hqF, hqh⟩ := hq
      rw [hF, Finset.mem_filter] at hqF
      obtain ⟨_, h3⟩ := hqF
      by_cases hq1 : q.1 ∈ H
      · rw [if_pos hq1] at hqh
        have hq2 : q.2 = m - h := by omega
        rw [Finset.mem_insert]
        exact Or.inl (Prod.ext hqh hq2)
      · rw [if_neg hq1] at hqh
        have hq2 : q.1 = m - h := by omega
        rw [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr (Prod.ext hq2 hqh)
    have h1 := Finset.card_le_card hsub
    have h2 : ({(h, m - h), (m - h, h)} :
        Finset (ℕ × ℕ)).card ≤ 2 := by
      apply le_trans (Finset.card_insert_le _ _)
      rw [Finset.card_singleton]
    omega
  have hcount := Finset.card_le_mul_card_image_of_maps_to
    (f := fun q => if q.1 ∈ H then q.1 else q.2)
    (s := F) (t := H) hmaps 2 (by
      intro h hh
      exact hfib h hh)
  omega

theorem global_parity_odd_fringe {A : Set ℕ} {Y ε : ℕ}
    (hpar : ∀ a ∈ A, Y < a → a % 2 = ε) :
    ∀ n, 2 * Y < n → n % 2 = 1 →
      ∀ x ∈ A, ∀ y ∈ A, x + y = n →
        (x ≤ Y ∧ x % 2 ≠ ε) ∨ (y ≤ Y ∧ y % 2 ≠ ε) := by
  intro n hnY hodd x hx y hy hxy
  rcases Nat.lt_or_ge Y x with hxY | hxY
  · rcases Nat.lt_or_ge Y y with hyY | hyY
    · have h1 := hpar x hx hxY
      have h2 := hpar y hy hyY
      omega
    · have h1 := hpar x hx hxY
      right
      constructor
      · omega
      · omega
  · have hyY : Y < y := by omega
    have h2 := hpar y hy hyY
    left
    constructor
    · omega
    · omega

open Classical in

theorem global_parity_odd_hall {A : Set ℕ} {Y ε : ℕ}
    (hpar : ∀ a ∈ A, Y < a → a % 2 = ε) :
    ∀ n, 2 * Y < n → n % 2 = 1 →
      IsPairSupportTransversal A n ((Finset.range (Y + 1)).filter
        (fun x => x ∈ A ∧ x % 2 ≠ ε)) := by
  intro n hnY hodd x hx y hy hxy
  rcases global_parity_odd_fringe hpar n hnY hodd x hx y hy
    hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hx, h2⟩
  · right
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hy, h2⟩

theorem global_parity_dichotomy {A : Set ℕ} :
    (∃ Y ε, ε < 2 ∧ ∀ a ∈ A, Y < a → a % 2 = ε) ∨
    ((∀ N, ∃ a, N ≤ a ∧ a ∈ A ∧ a % 2 = 0) ∧
     (∀ N, ∃ a, N ≤ a ∧ a ∈ A ∧ a % 2 = 1)) := by
  classical
  by_cases he : ∀ N, ∃ a, N ≤ a ∧ a ∈ A ∧ a % 2 = 0
  · by_cases ho : ∀ N, ∃ a, N ≤ a ∧ a ∈ A ∧ a % 2 = 1
    · exact Or.inr ⟨he, ho⟩
    · left
      obtain ⟨Y, hY⟩ := not_forall.mp ho
      refine ⟨Y, 0, by omega, ?_⟩
      intro a ha hYa
      by_contra hodd
      exact hY ⟨a, by omega, ha, by omega⟩
  · left
    obtain ⟨Y, hY⟩ := not_forall.mp he
    refine ⟨Y, 1, by omega, ?_⟩
    intro a ha hYa
    by_contra heven
    exact hY ⟨a, by omega, ha, by omega⟩

open Classical in

theorem global_parity_odd_ordered_cap {A : Set ℕ} {Y ε : ℕ}
    (hpar : ∀ a ∈ A, Y < a → a % 2 = ε) :
    ∀ n, 2 * Y < n → n % 2 = 1 →
      ((Finset.range (n + 1)).filter
        (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ 2 * Y + 2 := by
  intro n h1 h2
  have hsub : (Finset.range (n + 1)).filter
      (fun x => x ∈ A ∧ (n - x) ∈ A) ⊆
      (Finset.range (Y + 1)) ∪
      (Finset.Ioc (n - Y - 1) n) := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_range] at hx
    obtain ⟨hxn, hxA, hxpA⟩ := hx
    rcases global_parity_odd_fringe hpar n h1 h2 x hxA
      (n - x) hxpA (by omega) with ⟨ha, _⟩ | ⟨ha, _⟩
    · exact Finset.mem_union_left _
        (Finset.mem_range.2 (by omega))
    · exact Finset.mem_union_right _
        (Finset.mem_Ioc.2 (by omega))
  have h3 := Finset.card_le_card hsub
  have h4 := Finset.card_union_le (Finset.range (Y + 1))
    (Finset.Ioc (n - Y - 1) n)
  rw [Finset.card_range, Nat.card_Ioc] at h4
  omega

open Classical in

theorem r2_witnesses_even {A : Set ℕ} {N₀ Y ε : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hpar : ∀ a ∈ A, Y < a → a % 2 = ε) :
    ∀ N, ∃ v, N ≤ v ∧ v % 2 = 0 ∧ 2 * Y + 3 ≤
      ((Finset.range (v + 1)).filter
        (fun x => x ∈ A ∧ (v - x) ∈ A)).card := by
  intro N
  obtain ⟨v, hvN, hvC⟩ := r2_unbounded_of_hfail h0 hcov hfail
    (2 * Y + 3) (N + 2 * Y + 1)
  refine ⟨v, by omega, ?_, hvC⟩
  by_contra hodd
  have h1 : v % 2 = 1 := by omega
  have h2 := global_parity_odd_ordered_cap hpar v
    (by omega) h1
  omega

theorem half_model_covers {A : Set ℕ} {N₀ Y ε : ℕ}
    (hε : ε < 2)
    (hcov : PairCovers A N₀)
    (hpar : ∀ a ∈ A, Y < a → a % 2 = ε) :
    PairCovers {x : ℕ | ε + 2 * x ∈ A} (N₀ + 2 * Y + 2) := by
  intro n' hn'
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    hcov (2 * n' + 2 * ε) (by omega)
  have hxpar : x % 2 = ε := by
    rcases Nat.lt_or_ge Y x with h | h
    · exact hpar x hx h
    · have hyY : Y < y := by omega
      have h2 := hpar y hy hyY
      omega
  have hypar : y % 2 = ε := by omega
  have hex : ε + 2 * ((x - ε) / 2) = x := by omega
  have hey : ε + 2 * ((y - ε) / 2) = y := by omega
  refine ⟨(x - ε) / 2, ?_, (y - ε) / 2, ?_, ?_⟩
  · show ε + 2 * ((x - ε) / 2) ∈ A
    rw [hex]
    exact hx
  · show ε + 2 * ((y - ε) / 2) ∈ A
    rw [hey]
    exact hy
  · omega

theorem half_model_lift_channel {A : Set ℕ} {ε N' : ℕ}
    (hε : ε < 2) {B' : Set ℕ}
    (hsurv' : ∀ n', N' ≤ n' →
      ∃ x' ∈ {x : ℕ | ε + 2 * x ∈ A},
      ∃ y' ∈ {x : ℕ | ε + 2 * x ∈ A},
      ∃ z' ∈ {x : ℕ | ε + 2 * x ∈ A},
        x' ∉ B' ∧ y' ∉ B' ∧ z' ∉ B' ∧ x' + y' + z' = n') :
    ∀ n, 2 * N' + 3 * ε ≤ n → n % 2 = 3 * ε % 2 →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ {a : ℕ | ∃ b' ∈ B', a = ε + 2 * b'} ∧
        y ∉ {a : ℕ | ∃ b' ∈ B', a = ε + 2 * b'} ∧
        z ∉ {a : ℕ | ∃ b' ∈ B', a = ε + 2 * b'} ∧
        x + y + z = n := by
  intro n hn hch
  obtain ⟨x', hx', y', hy', z', hz', hxB, hyB, hzB, hsum⟩ :=
    hsurv' ((n - 3 * ε) / 2) (by omega)
  have hlift : ∀ w', w' ∉ B' →
      ε + 2 * w' ∉ {a : ℕ | ∃ b' ∈ B', a = ε + 2 * b'} := by
    intro w' hw' ⟨b', hb', heq⟩
    have h1 : w' = b' := by omega
    exact hw' (h1 ▸ hb')
  refine ⟨ε + 2 * x', hx', ε + 2 * y', hy', ε + 2 * z', hz',
    hlift x' hxB, hlift y' hyB, hlift z' hzB, by omega⟩

theorem half_model_lift_offchannel {A : Set ℕ} {ε N' : ℕ}
    (hε : ε < 2) {B' : Set ℕ}
    (hsurv2 : ∀ n', N' ≤ n' →
      ∃ x' ∈ {x : ℕ | ε + 2 * x ∈ A},
      ∃ y' ∈ {x : ℕ | ε + 2 * x ∈ A},
        x' ∉ B' ∧ y' ∉ B' ∧ x' + y' = n')
    {f : ℕ} (hf : f ∈ A) (hfpar : f % 2 ≠ ε) :
    ∀ n, 2 * N' + f + 2 * ε ≤ n → n % 2 = f % 2 →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ {a : ℕ | ∃ b' ∈ B', a = ε + 2 * b'} ∧
        y ∉ {a : ℕ | ∃ b' ∈ B', a = ε + 2 * b'} ∧
        z ∉ {a : ℕ | ∃ b' ∈ B', a = ε + 2 * b'} ∧
        x + y + z = n := by
  intro n hn hch
  obtain ⟨x', hx', y', hy', hxB, hyB, hsum⟩ :=
    hsurv2 ((n - f - 2 * ε) / 2) (by omega)
  have hlift : ∀ w', w' ∉ B' →
      ε + 2 * w' ∉ {a : ℕ | ∃ b' ∈ B', a = ε + 2 * b'} := by
    intro w' hw' ⟨b', hb', heq⟩
    have h1 : w' = b' := by omega
    exact hw' (h1 ▸ hb')
  have hfB : f ∉ {a : ℕ | ∃ b' ∈ B', a = ε + 2 * b'} := by
    intro ⟨b', hb', heq⟩
    omega
  refine ⟨f, hf, ε + 2 * x', hx', ε + 2 * y', hy',
    hfB, hlift x' hxB, hlift y' hyB, by omega⟩

theorem descent_invariant {A : Set ℕ} {ε : ℕ}
    (hε : ε < 2)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {f : ℕ} (hf : f ∈ A) (hfpar : f % 2 ≠ ε) :
    ∀ B' ⊆ {x : ℕ | ε + 2 * x ∈ A}, B'.Infinite →
      ¬((∃ N2, ∀ n', N2 ≤ n' →
          ∃ x' ∈ {x : ℕ | ε + 2 * x ∈ A},
          ∃ y' ∈ {x : ℕ | ε + 2 * x ∈ A},
            x' ∉ B' ∧ y' ∉ B' ∧ x' + y' = n') ∧
        (∃ N3, ∀ n', N3 ≤ n' →
          ∃ x' ∈ {x : ℕ | ε + 2 * x ∈ A},
          ∃ y' ∈ {x : ℕ | ε + 2 * x ∈ A},
          ∃ z' ∈ {x : ℕ | ε + 2 * x ∈ A},
            x' ∉ B' ∧ y' ∉ B' ∧ z' ∉ B' ∧
            x' + y' + z' = n')) := by
  rintro B' hB'sub hB'inf ⟨⟨N2, hs2⟩, ⟨N3, hs3⟩⟩
  set LB := {a : ℕ | ∃ b' ∈ B', a = ε + 2 * b'} with hLB
  have hLBA : LB ⊆ A := by
    rintro a ⟨b', hb', rfl⟩
    exact hB'sub hb'
  have hLBinf : LB.Infinite := by
    have h1 : LB = (fun b => ε + 2 * b) '' B' := by
      ext a
      constructor
      · rintro ⟨b', hb', rfl⟩
        exact ⟨b', hb', rfl⟩
      · rintro ⟨b', hb', rfl⟩
        exact ⟨b', hb', rfl⟩
    rw [h1]
    exact hB'inf.image (fun a _ b _ h => by omega)
  refine hfail LB hLBA hLBinf ⟨2 * (N2 + N3) + f + 3, ?_⟩
  intro n hn
  by_cases hch : n % 2 = 3 * ε % 2
  · obtain ⟨x, hx, y, hy, z, hz, hxB, hyB, hzB, hsum⟩ :=
      half_model_lift_channel hε hs3 n (by omega) hch
    refine ⟨![x, y, z], ?_, ?_⟩
    · intro i
      match i with
      | 0 => exact ⟨hx, hxB⟩
      | 1 => exact ⟨hy, hyB⟩
      | 2 => exact ⟨hz, hzB⟩
    · simpa [Fin.sum_univ_three] using hsum
  · obtain ⟨x, hx, y, hy, z, hz, hxB, hyB, hzB, hsum⟩ :=
      half_model_lift_offchannel hε hs2 hf hfpar n
        (by omega) (by omega)
    refine ⟨![x, y, z], ?_, ?_⟩
    · intro i
      match i with
      | 0 => exact ⟨hx, hxB⟩
      | 1 => exact ⟨hy, hyB⟩
      | 2 => exact ⟨hz, hzB⟩
    · simpa [Fin.sum_univ_three] using hsum

open Classical in

theorem saturated_fringe_nonempty {A : Set ℕ} {N₀ Y ε : ℕ}
    (hcov : PairCovers A N₀)
    (hpar : ∀ a ∈ A, Y < a → a % 2 = ε) :
    ((Finset.range (Y + 1)).filter
      (fun x => x ∈ A ∧ x % 2 ≠ ε)).Nonempty := by
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    hcov (2 * (Y + N₀) + 1) (by omega)
  rcases global_parity_odd_fringe hpar (2 * (Y + N₀) + 1)
    (by omega) (by omega) x hx y hy hxy with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨x, by
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hx, h2⟩⟩
  · exact ⟨y, by
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hy, h2⟩⟩

open Classical in

theorem saturated_popular_fringe {A : Set ℕ} {N₀ Y ε : ℕ}
    (hcov : PairCovers A N₀)
    (hpar : ∀ a ∈ A, Y < a → a % 2 = ε) :
    ∃ f, f ∈ A ∧ f ≤ Y ∧ f % 2 ≠ ε ∧
      ∀ N, ∃ n, N ≤ n ∧ n % 2 = 1 ∧ f ≤ n ∧ n - f ∈ A := by
  classical
  by_contra hno
  push Not at hno
  have hKf : ∀ f : ℕ, ∃ Kf, f ∈ A → f ≤ Y → f % 2 ≠ ε →
      ∀ n, Kf ≤ n → n % 2 = 1 → f ≤ n → n - f ∉ A := by
    intro f
    by_cases hfA : f ∈ A
    · by_cases hfY : f ≤ Y
      · by_cases hfp : f % 2 = ε
        · exact ⟨0, fun _ _ h => absurd hfp h⟩
        · obtain ⟨Kf, hKf'⟩ := hno f hfA hfY hfp
          exact ⟨Kf, fun _ _ _ => hKf'⟩
      · exact ⟨0, fun _ h => absurd h hfY⟩
    · exact ⟨0, fun h => absurd h hfA⟩
  choose Kf hKf using hKf
  set KM := (Finset.range (Y + 1)).sup Kf with hKM
  set n := 2 * (KM + Y + N₀) + 1 with hn
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov n (by omega)
  rcases global_parity_odd_fringe hpar n (by omega) (by omega)
    x hx y hy hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hKx : Kf x ≤ KM :=
      Finset.le_sup (f := Kf) (Finset.mem_range.2 (by omega))
    have h3 := hKf x hx h1 h2 n (by omega) (by omega) (by omega)
    have h4 : n - x = y := by omega
    rw [h4] at h3
    exact h3 hy
  · have hKy : Kf y ≤ KM :=
      Finset.le_sup (f := Kf) (Finset.mem_range.2 (by omega))
    have h3 := hKf y hy h1 h2 n (by omega) (by omega) (by omega)
    have h4 : n - y = x := by omega
    rw [h4] at h3
    exact h3 hx

theorem two_level_descent {A : Set ℕ} {Y₀ Y₁ ε₀ ε₁ : ℕ}
    (hε₀ : ε₀ < 2) (hε₁ : ε₁ < 2)
    (hpar₀ : ∀ a ∈ A, Y₀ < a → a % 2 = ε₀)
    (hpar₁ : ∀ a' ∈ {x : ℕ | ε₀ + 2 * x ∈ A}, Y₁ < a' →
      a' % 2 = ε₁) :
    ∀ a ∈ A, Y₀ + ε₀ + 2 * Y₁ < a →
      a % 4 = ε₀ + 2 * ε₁ := by
  intro a ha hbig
  have h0 := hpar₀ a ha (by omega)
  have hmem : (a - ε₀) / 2 ∈ {x : ℕ | ε₀ + 2 * x ∈ A} := by
    show ε₀ + 2 * ((a - ε₀) / 2) ∈ A
    have he : ε₀ + 2 * ((a - ε₀) / 2) = a := by omega
    rw [he]
    exact ha
  have h1 := hpar₁ _ hmem (by omega)
  omega

theorem omega_descent_cylinder {A : Set ℕ} (ε Y : ℕ → ℕ)
    (hε : ∀ k, ε k < 2)
    (W : ℕ → Set ℕ) (hW0 : W 0 = A)
    (hWs : ∀ k, W (k + 1) = {x | ε k + 2 * x ∈ W k})
    (hpar : ∀ k, ∀ a ∈ W k, Y k < a → a % 2 = ε k) :
    ∀ k, ∃ c T, c < 2 ^ k ∧ ∀ a ∈ A, T < a →
      ∃ a', a = c + 2 ^ k * a' ∧ a' ∈ W k := by
  intro k
  induction k with
  | zero =>
    refine ⟨0, 0, by norm_num, ?_⟩
    intro a ha _
    refine ⟨a, by simp, ?_⟩
    rw [hW0]
    exact ha
  | succ k ih =>
    obtain ⟨c, T, hc, hT⟩ := ih
    have hpk : (0 : ℕ) < 2 ^ k := pow_pos (by omega) k
    refine ⟨c + 2 ^ k * ε k,
      max T (c + 2 ^ k * (Y k + 1)), ?_, ?_⟩
    · have h1 := hε k
      have hp : (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
      have h2 : 2 ^ k * ε k ≤ 2 ^ k * 1 :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    · intro a ha hbig
      have hT' : T < a :=
        lt_of_le_of_lt (le_max_left _ _) hbig
      have hbig' : c + 2 ^ k * (Y k + 1) < a :=
        lt_of_le_of_lt (le_max_right _ _) hbig
      obtain ⟨a', heq, hmem⟩ := hT a ha hT'
      have ha'Y : Y k < a' := by
        have h1 : 2 ^ k * (Y k + 1) < 2 ^ k * a' := by omega
        have h2 := Nat.lt_of_mul_lt_mul_left h1
        omega
      have hpar' := hpar k a' hmem ha'Y
      set a'' := (a' - ε k) / 2 with ha''
      have hε' := hε k
      have hae : a' = ε k + 2 * a'' := by omega
      have hmem' : a'' ∈ W (k + 1) := by
        rw [hWs k]
        show ε k + 2 * a'' ∈ W k
        rw [← hae]
        exact hmem
      refine ⟨a'', ?_, hmem'⟩
      have hp : (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
      rw [heq, hae, hp]
      ring

open Classical in

theorem cylinder_sparsity {A : Set ℕ} {k c T : ℕ}
    (hcyl : ∀ a ∈ A, T < a → ∃ a', a = c + 2 ^ k * a') :
    ∀ X, ((Finset.Ioc T X).filter (· ∈ A)).card ≤
      X / 2 ^ k + 1 := by
  intro X
  have hpk : (0 : ℕ) < 2 ^ k := pow_pos (by omega) k
  refine le_trans (Finset.card_le_card_of_injOn
    (fun a => (a - c) / 2 ^ k) (t := Finset.range
      (X / 2 ^ k + 1)) ?_ ?_)
    (le_of_eq (Finset.card_range _))
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter,
      Finset.mem_Ioc] at ha
    obtain ⟨⟨hTa, haX⟩, haA⟩ := ha
    obtain ⟨a', hae⟩ := hcyl a haA hTa
    have h1 : (a - c) / 2 ^ k = a' := by
      rw [hae]
      have h2 : c + 2 ^ k * a' - c = 2 ^ k * a' := by omega
      rw [h2]
      exact Nat.mul_div_cancel_left a' hpk
    simp only [Finset.mem_coe, Finset.mem_range]
    rw [h1]
    have h3 : 2 ^ k * a' ≤ X := by omega
    have h4 : a' ≤ X / 2 ^ k := by
      rw [Nat.le_div_iff_mul_le hpk]
      have h5 : a' * 2 ^ k = 2 ^ k * a' := by ring
      omega
    omega
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter,
      Finset.mem_Ioc] at ha hb
    obtain ⟨⟨hTa, _⟩, haA⟩ := ha
    obtain ⟨⟨hTb, _⟩, hbA⟩ := hb
    obtain ⟨a', hae⟩ := hcyl a haA hTa
    obtain ⟨b', hbe⟩ := hcyl b hbA hTb
    have hab' : (a - c) / 2 ^ k = (b - c) / 2 ^ k := hab
    have h1 : (a - c) / 2 ^ k = a' := by
      rw [hae]
      have h2 : c + 2 ^ k * a' - c = 2 ^ k * a' := by omega
      rw [h2]
      exact Nat.mul_div_cancel_left a' hpk
    have h2 : (b - c) / 2 ^ k = b' := by
      rw [hbe]
      have h3 : c + 2 ^ k * b' - c = 2 ^ k * b' := by omega
      rw [h3]
      exact Nat.mul_div_cancel_left b' hpk
    rw [h1, h2] at hab'
    rw [hab'] at hae
    omega

open Classical in

theorem descent_threshold_race {A : Set ℕ} {N₀ k c T : ℕ}
    (hcov : PairCovers A N₀)
    (hcyl : ∀ a ∈ A, T < a → ∃ a', a = c + 2 ^ k * a') :
    ∀ X, N₀ ≤ X →
      X - N₀ + 1 ≤ (T + X / 2 ^ k + 2) ^ 2 := by
  intro X hX
  have hd := covering_density hcov X hX
  set AX := (Finset.range (X + 1)).filter (· ∈ A) with hAX
  have hsplit : AX.card ≤ (T + 1) +
      ((Finset.Ioc T X).filter (· ∈ A)).card := by
    have hsub : AX ⊆ (Finset.range (T + 1)) ∪
        ((Finset.Ioc T X).filter (· ∈ A)) := by
      intro a ha
      rw [hAX, Finset.mem_filter, Finset.mem_range] at ha
      obtain ⟨h1, h2⟩ := ha
      rcases Nat.lt_or_ge T a with h | h
      · exact Finset.mem_union_right _ (by
          rw [Finset.mem_filter, Finset.mem_Ioc]
          exact ⟨⟨h, by omega⟩, h2⟩)
      · exact Finset.mem_union_left _
          (Finset.mem_range.2 (by omega))
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (Finset.range (T + 1))
      ((Finset.Ioc T X).filter (· ∈ A))
    rw [Finset.card_range] at h2
    omega
  have hcs := cylinder_sparsity hcyl X
  have hle : AX.card ≤ T + X / 2 ^ k + 2 := by omega
  have hpow : AX.card ^ 2 ≤ (T + X / 2 ^ k + 2) ^ 2 :=
    Nat.pow_le_pow_left hle 2
  omega

theorem descent_depth_cost {A : Set ℕ} {N₀ k c T : ℕ}
    (hcov : PairCovers A N₀)
    (hcyl : ∀ a ∈ A, T < a → ∃ a', a = c + 2 ^ k * a')
    (hk : 2 ≤ k) (hN : N₀ < 2 ^ (k - 1)) :
    2 ^ (k - 2) ≤ T + N₀ + 2 := by
  have hX : (2 : ℕ) ^ (2 * k - 2) = 2 ^ k * 2 ^ (k - 2) := by
    rw [← pow_add]
    congr 1
    omega
  have hb : (2 : ℕ) ^ (2 * k - 2) = (2 ^ (k - 1)) ^ 2 := by
    rw [← pow_mul]
    congr 1
    omega
  have hNX : N₀ ≤ 2 ^ (2 * k - 2) := by
    have h1 : (2 : ℕ) ^ (k - 1) ≤ 2 ^ (2 * k - 2) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hrace := descent_threshold_race hcov hcyl
    (2 ^ (2 * k - 2)) hNX
  have hdiv : (2 : ℕ) ^ (2 * k - 2) / 2 ^ k = 2 ^ (k - 2) := by
    rw [hX]
    exact Nat.mul_div_cancel_left _ (pow_pos (by omega) k)
  rw [hdiv] at hrace
  by_contra hlt
  push Not at hlt
  set a := T + 2 ^ (k - 2) + 2 with ha
  set b := (2 : ℕ) ^ (k - 1) with hbdef
  have hsplit : b = 2 * 2 ^ (k - 2) := by
    rw [hbdef]
    rw [show k - 1 = (k - 2) + 1 from by omega, pow_succ]
    ring
  have hab : a + N₀ < b := by omega
  set d := b - N₀ - 1 with hd
  have hbd : b = d + N₀ + 1 := by omega
  have hle : a ≤ d := by omega
  have h1 : a ^ 2 ≤ d ^ 2 := Nat.pow_le_pow_left hle 2
  have he : (d + N₀ + 1) ^ 2 =
      d ^ 2 + 2 * d * (N₀ + 1) + (N₀ + 1) ^ 2 := by ring
  have h2 : b ^ 2 = d ^ 2 + 2 * d * (N₀ + 1) +
      (N₀ + 1) ^ 2 := by
    rw [hbd]
    exact he
  have h3 : (N₀ + 1) ^ 2 = N₀ * N₀ + 2 * N₀ + 1 := by ring
  rw [← hb] at h2
  omega

theorem free_sets_avoidance {A : Set ℕ} {N₀ : ℕ}
    (hfree : ∀ c, ∃ P : Finset ℕ, RepFree A N₀ P ∧
      c ≤ P.card) :
    ∀ (F : Finset ℕ) (c : ℕ), ∃ P : Finset ℕ,
      RepFree A N₀ P ∧ c ≤ P.card ∧ Disjoint P F := by
  intro F c
  obtain ⟨P, hPfree, hPc⟩ := hfree (c + F.card)
  refine ⟨P \ F, RepFree.mono Finset.sdiff_subset hPfree,
    ?_, Finset.sdiff_disjoint⟩
  have h1 : P ⊆ (P \ F) ∪ F := by
    intro x hx
    by_cases hxF : x ∈ F
    · exact Finset.mem_union_right _ hxF
    · exact Finset.mem_union_left _
        (Finset.mem_sdiff.2 ⟨hx, hxF⟩)
  have h2 := Finset.card_le_card h1
  have h3 := Finset.card_union_le (P \ F) F
  omega

theorem free_disjoint_stream {A : Set ℕ} {N₀ : ℕ}
    (hfree : ∀ c, ∃ P : Finset ℕ, RepFree A N₀ P ∧
      c ≤ P.card) :
    ∃ Q : ℕ → Finset ℕ,
      (∀ k, RepFree A N₀ (Q k) ∧ k ≤ (Q k).card) ∧
      ∀ j k, j < k → Disjoint (Q j) (Q k) := by
  classical
  have hdodge := free_sets_avoidance hfree
  have hex : ∀ (F : Finset ℕ) (c : ℕ), ∃ P : Finset ℕ,
      RepFree A N₀ P ∧ c ≤ P.card ∧ Disjoint P F :=
    fun F c => hdodge F c
  choose Pf hPf1 hPf2 hPf3 using hex
  set st : ℕ → Finset ℕ × Finset ℕ := fun k =>
    Nat.rec (Pf ∅ 0, Pf ∅ 0)
      (fun k prev => (Pf prev.2 (k + 1),
        prev.2 ∪ Pf prev.2 (k + 1))) k with hst
  have hstS : ∀ k, st (k + 1) =
      (Pf (st k).2 (k + 1),
       (st k).2 ∪ Pf (st k).2 (k + 1)) := fun _ => rfl
  set Q : ℕ → Finset ℕ := fun k => (st k).1 with hQ
  have hQ0 : Q 0 = Pf ∅ 0 := rfl
  have hQS : ∀ k, Q (k + 1) = Pf (st k).2 (k + 1) :=
    fun _ => rfl
  have hacc : ∀ k, Q k ⊆ (st k).2 := by
    intro k
    cases k with
    | zero => exact Finset.Subset.refl _
    | succ k =>
      rw [hQS, hstS]
      exact Finset.subset_union_right
  have haccmono : ∀ j k, j ≤ k → (st j).2 ⊆ (st k).2 := by
    intro j k hjk
    induction k with
    | zero =>
      have h0 : j = 0 := by omega
      subst h0
      exact Finset.Subset.refl _
    | succ k ih =>
      rcases Nat.lt_or_ge j (k + 1) with h | h
      · refine Finset.Subset.trans (ih (by omega)) ?_
        rw [hstS]
        exact Finset.subset_union_left
      · have h1 : j = k + 1 := by omega
        subst h1
        exact Finset.Subset.refl _
  refine ⟨Q, ?_, ?_⟩
  · intro k
    cases k with
    | zero => exact ⟨(hPf1 ∅ 0), by omega⟩
    | succ k =>
      rw [hQS]
      exact ⟨hPf1 _ _, hPf2 _ _⟩
  · intro j k hjk
    have h1 : Q (k) = Pf (st (k - 1)).2 (k) := by
      have h5 := hQS (k - 1)
      have he : k - 1 + 1 = k := by omega
      rw [he] at h5
      exact h5
    have h2 : Disjoint (Pf (st (k - 1)).2 k) (st (k - 1)).2 :=
      hPf3 _ _
    have h3 : Q j ⊆ (st (k - 1)).2 := by
      have h4 : j ≤ k - 1 := by omega
      exact Finset.Subset.trans (hacc j) (haccmono j (k - 1) h4)
    rw [h1]
    exact (Finset.disjoint_of_subset_right h3 h2).symm

theorem finset_stream_higman (Q : ℕ → Finset ℕ) :
    ∃ σ : ℕ ↪o ℕ, ∀ m n, m ≤ n →
      List.SublistForall₂ (· ≤ ·)
        ((Q (σ m)).sort (· ≤ ·)) ((Q (σ n)).sort (· ≤ ·)) := by
  classical
  haveI hwqo : WellQuasiOrderedLE ℕ :=
    wellQuasiOrderedLE_iff_wellFoundedLT.mpr inferInstance
  have hpwo : (Set.univ : Set ℕ).PartiallyWellOrderedOn
      (· ≤ ·) :=
    Set.isPWO_of_wellQuasiOrderedLE _
  haveI hrefl :
      Std.Refl (List.SublistForall₂ ((· ≤ ·) : ℕ → ℕ → Prop)) :=
    ⟨fun l => Std.Refl.refl l⟩
  haveI hpre : IsPreorder (List ℕ)
      (List.SublistForall₂ ((· ≤ ·) : ℕ → ℕ → Prop)) := ⟨⟩
  have hlists :=
    Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂
      (· ≤ ·) hpwo
  obtain ⟨σ, hσ⟩ := hlists.exists_monotone_subseq
    (f := fun k => (Q k).sort (· ≤ ·))
    (fun k x _ => Set.mem_univ x)
  exact ⟨σ, hσ⟩

theorem rank_case_chain {A : Set ℕ} {N₀ : ℕ}
    (hfree : ∀ c, ∃ P : Finset ℕ,
      (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧ RepFree A N₀ P ∧
      c ≤ P.card) :
    ∃ Q : ℕ → Finset ℕ, ∃ σ : ℕ ↪o ℕ,
      (∀ k, (Q k).Nonempty) ∧
      (∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h) ∧
      (∀ k, RepFree A N₀ (Q k)) ∧
      (∀ j k, j < k → Disjoint (Q j) (Q k)) ∧
      (∀ k, k + 1 ≤ (Q k).card) ∧
      ∀ m n, m ≤ n → List.SublistForall₂ (· ≤ ·)
        ((Q (σ m)).sort (· ≤ ·))
        ((Q (σ n)).sort (· ≤ ·)) := by
  classical
  have hdodge : ∀ (F : Finset ℕ) (c : ℕ), ∃ P : Finset ℕ,
      (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧ RepFree A N₀ P ∧
      c ≤ P.card ∧ Disjoint P F := by
    intro F c
    obtain ⟨P, hmat, hPfree, hPc⟩ := hfree (c + F.card)
    refine ⟨P \ F, fun h hh => hmat h (Finset.mem_sdiff.1 hh).1,
      RepFree.mono Finset.sdiff_subset hPfree, ?_,
      Finset.sdiff_disjoint⟩
    have h1 : P ⊆ (P \ F) ∪ F := by
      intro x hx
      by_cases hxF : x ∈ F
      · exact Finset.mem_union_right _ hxF
      · exact Finset.mem_union_left _
          (Finset.mem_sdiff.2 ⟨hx, hxF⟩)
    have h2 := Finset.card_le_card h1
    have h3 := Finset.card_union_le (P \ F) F
    omega
  choose Pf hPf1 hPf2 hPf3 hPf4 using hdodge
  set st : ℕ → Finset ℕ × Finset ℕ := fun k =>
    Nat.rec (Pf ∅ 1, Pf ∅ 1)
      (fun k prev => (Pf prev.2 (k + 2),
        prev.2 ∪ Pf prev.2 (k + 2))) k with hst
  have hstS : ∀ k, st (k + 1) =
      (Pf (st k).2 (k + 2),
       (st k).2 ∪ Pf (st k).2 (k + 2)) := fun _ => rfl
  set Q : ℕ → Finset ℕ := fun k => (st k).1 with hQ
  have hQ0 : Q 0 = Pf ∅ 1 := rfl
  have hQS : ∀ k, Q (k + 1) = Pf (st k).2 (k + 2) :=
    fun _ => rfl
  have hcard : ∀ k, k + 1 ≤ (Q k).card := by
    intro k
    cases k with
    | zero => exact hPf3 ∅ 1
    | succ k =>
      rw [hQS]
      exact hPf3 _ _
  have hacc : ∀ k, Q k ⊆ (st k).2 := by
    intro k
    cases k with
    | zero => exact Finset.Subset.refl _
    | succ k =>
      rw [hQS, hstS]
      exact Finset.subset_union_right
  have haccmono : ∀ j k, j ≤ k → (st j).2 ⊆ (st k).2 := by
    intro j k hjk
    induction k with
    | zero =>
      have h0 : j = 0 := by omega
      subst h0
      exact Finset.Subset.refl _
    | succ k ih =>
      rcases Nat.lt_or_ge j (k + 1) with h | h
      · refine Finset.Subset.trans (ih (by omega)) ?_
        rw [hstS]
        exact Finset.subset_union_left
      · have h1 : j = k + 1 := by omega
        subst h1
        exact Finset.Subset.refl _
  have hdisj : ∀ j k, j < k → Disjoint (Q j) (Q k) := by
    intro j k hjk
    have h1 : Q k = Pf (st (k - 1)).2 (k + 1) := by
      have h5 := hQS (k - 1)
      have he : k - 1 + 1 = k := by omega
      have he2 : k - 1 + 2 = k + 1 := by omega
      rw [he, he2] at h5
      exact h5
    have h2 : Disjoint (Pf (st (k - 1)).2 (k + 1))
        (st (k - 1)).2 := hPf4 _ _
    have h3 : Q j ⊆ (st (k - 1)).2 := by
      have h4 : j ≤ k - 1 := by omega
      exact Finset.Subset.trans (hacc j) (haccmono j (k - 1) h4)
    rw [h1]
    exact (Finset.disjoint_of_subset_right h3 h2).symm
  have hmat : ∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h := by
    intro k
    cases k with
    | zero => exact hPf1 ∅ 1
    | succ k =>
      rw [hQS]
      exact hPf1 _ _
  have hfreeQ : ∀ k, RepFree A N₀ (Q k) := by
    intro k
    cases k with
    | zero => exact hPf2 ∅ 1
    | succ k =>
      rw [hQS]
      exact hPf2 _ _
  have hne : ∀ k, (Q k).Nonempty := by
    intro k
    have h1 := hcard k
    exact Finset.card_pos.1 (by omega)
  obtain ⟨σ, hσ⟩ := finset_stream_higman Q
  exact ⟨Q, σ, hne, hmat, hfreeQ, hdisj, hcard, hσ⟩

theorem rank_case_subsequence {A : Set ℕ} {N₀ : ℕ}
    (hfree : ∀ c, ∃ P : Finset ℕ,
      (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧ RepFree A N₀ P ∧
      c ≤ P.card) :
    ∃ Q : ℕ → Finset ℕ, ∃ σ : ℕ ↪o ℕ, ∃ x : ℕ → ℕ,
      (∀ k, RepFree A N₀ (Q k)) ∧
      (∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h) ∧
      (∀ j k, j < k → Disjoint (Q j) (Q k)) ∧
      (∀ k, k + 1 ≤ (Q k).card) ∧
      StrictMono x ∧ (∀ t, x t ∈ Q (σ t)) := by
  classical
  obtain ⟨Q, σ, hne, hmat, hfreeQ, hdisj, hcard, hσ⟩ :=
    rank_case_chain hfree
  have hstep : ∀ t v, v ∈ Q (σ t) → ∃ w ∈ Q (σ (t + 1)),
      v < w := by
    intro t v hv
    have hchain := hσ t (t + 1) (by omega)
    obtain ⟨l', hf₂, hsub⟩ := List.sublistForall₂_iff.1 hchain
    have hvL : v ∈ (Q (σ t)).sort (· ≤ ·) := by
      rw [Finset.mem_sort]
      exact hv
    obtain ⟨w, hwl', hvw⟩ := forall₂_mem_partner hf₂ v hvL
    have hwL : w ∈ (Q (σ (t + 1))).sort (· ≤ ·) :=
      hsub.mem hwl'
    have hwQ : w ∈ Q (σ (t + 1)) := by
      rw [← Finset.mem_sort (α := ℕ) (· ≤ ·)]
      exact hwL
    have hvne : v ≠ w := by
      intro heq
      have h1 : σ t < σ (t + 1) := σ.strictMono (by omega)
      exact (Finset.disjoint_left.1 (hdisj _ _ h1)) hv
        (heq ▸ hwQ)
    exact ⟨w, hwQ, by omega⟩
  obtain ⟨v₀, hv₀⟩ := hne (σ 0)
  have hpick : ∀ t v, ∃ w, v ∈ Q (σ t) →
      w ∈ Q (σ (t + 1)) ∧ v < w := by
    intro t v
    by_cases hv : v ∈ Q (σ t)
    · obtain ⟨w, hw, hvw⟩ := hstep t v hv
      exact ⟨w, fun _ => ⟨hw, hvw⟩⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose W hW using hpick
  obtain ⟨x, hx0, hxs⟩ : ∃ x : ℕ → ℕ, x 0 = v₀ ∧
      ∀ t, x (t + 1) = W t (x t) :=
    ⟨fun t => Nat.rec v₀ (fun t' v => W t' v) t, rfl,
      fun _ => rfl⟩
  have hxmem : ∀ t, x t ∈ Q (σ t) := by
    intro t
    induction t with
    | zero => rw [hx0]; exact hv₀
    | succ t ih =>
      rw [hxs]
      exact (hW t (x t) ih).1
  have hxmono : StrictMono x := by
    apply strictMono_nat_of_lt_succ
    intro t
    rw [hxs]
    exact (hW t (x t) (hxmem t)).2
  exact ⟨Q, σ, x, hfreeQ, hmat, hdisj, hcard, hxmono, hxmem⟩

theorem stall_chain_or_rank {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∀ c : ℕ, ∃ y : ℕ → ℕ, StrictMono y ∧
      (∀ t, y t ∈ A ∧ 0 < y t) ∧
      ∀ j, j ≤ c → RepFree A N₀
        ((Finset.range j).image y)) ∨
    (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
      ∃ L, ∀ s : ℕ, ∃ J m, 2 ≤ J ∧ J ≤ L ∧ N₀ ≤ m ∧
        IsRepSupportTransversal A m ((Finset.range J).image
          (fun j => x (s + j)))) := by
  classical
  obtain ⟨Q, σ, x, hxmono, hxmem, hQfree, hQmem, hstall⟩ :=
    subsequence_stalls_hereditarily h0 hcov hanchor hfail
  have hxA : ∀ t, x t ∈ A ∧ 0 < x t :=
    fun t => hQmem _ _ (hxmem t)
  set Pred : ℕ → ℕ → Prop := fun s J => ∃ m, N₀ ≤ m ∧
    IsRepSupportTransversal A m ((Finset.range J).image (fun j => x (s + j)))
    with hPred
  have hne : ∀ s, ∃ J, Pred s J := by
    intro s
    obtain ⟨J, m, hm, hhub⟩ := hstall (fun j => s + j)
      (fun a b hab => by
        show s + a < s + b
        omega)
    exact ⟨J, m, hm, hhub⟩
  have hJmin : ∀ s J', J' < Nat.find (hne s) → ¬Pred s J' :=
    fun s J' h => Nat.find_min (hne s) h
  by_cases hbnd : ∃ L, ∀ s, Nat.find (hne s) ≤ L
  · right
    obtain ⟨L, hL⟩ := hbnd
    have hJdef : ∀ s, Pred s (Nat.find (hne s)) :=
      fun s => Nat.find_spec (hne s)
    have hJ2 : ∀ s, 2 ≤ Nat.find (hne s) := by
      intro s
      by_contra hlt
      push Not at hlt
      interval_cases h : (Nat.find (hne s))
      · obtain ⟨m, hm, hhub⟩ := hJdef s
        rw [h] at hhub
        obtain ⟨u, hu, v, hv, huv⟩ := hcov m hm
        have h3 : u + v + 0 = m := by omega
        rcases hhub u hu v hv 0 h0 h3 with hh | hh | hh <;>
          simp at hh
      · obtain ⟨m, hm, hhub⟩ := hJdef s
        rw [h] at hhub
        have hW1 : ((Finset.range 1).image
            (fun j => x (s + j))) = {x s} := by
          rw [Finset.range_one, Finset.image_singleton]
          simp
        rw [hW1] at hhub
        exact stall_window_not_in_rank_layer (hQfree (σ s))
          (Finset.singleton_subset_iff.2 (by
            simpa using hxmem s)) hm hhub
    refine ⟨x, hxmono, hxA, L, fun s => ?_⟩
    obtain ⟨m, hm, hhub⟩ := hJdef s
    exact ⟨Nat.find (hne s), m, hJ2 s, hL s, hm, hhub⟩
  · left
    push Not at hbnd
    intro c
    obtain ⟨s, hs⟩ := hbnd (c + 1)
    refine ⟨fun i => x (s + i), ?_, fun t => hxA _, ?_⟩
    · intro a b hab
      exact hxmono (by omega)
    · intro j hj
      rcases Nat.eq_zero_or_pos j with h0j | h0j
      · subst h0j
        intro m hm
        obtain ⟨u, hu, v, hv, huv⟩ := hcov m hm
        exact ⟨u, hu, v, hv, 0, h0, by omega,
          by simp, by simp, by simp⟩
      · rw [repFree_iff_forall_not_support_transversal]
        intro m hm hhub
        exact hJmin s j (by omega) ⟨m, hm, hhub⟩

open Classical in

theorem r2_channel_amplification {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∀ C N, ∃ v, N ≤ v ∧ C ≤ ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A ∧ x % 2 = 0 ∧
        (v - x) % 2 = 0)).card) ∨
    (∀ C N, ∃ v, N ≤ v ∧ C ≤ ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A ∧ x % 2 = 1 ∧
        (v - x) % 2 = 1)).card) ∨
    (∀ C N, ∃ v, N ≤ v ∧ C ≤ ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A ∧
        x % 2 ≠ (v - x) % 2)).card) := by
  by_contra hno
  push Not at hno
  obtain ⟨⟨C₁, N₁, h1⟩, ⟨C₂, N₂, h2⟩, ⟨C₃, N₃, h3⟩⟩ := hno
  obtain ⟨v, hvN, hvC⟩ := r2_unbounded_of_hfail h0 hcov hfail
    (C₁ + C₂ + C₃ + 3) (N₁ + N₂ + N₃)
  have hs1 := h1 v (by omega)
  have hs2 := h2 v (by omega)
  have hs3 := h3 v (by omega)
  have hsub : (Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A) ⊆
      ((Finset.range (v + 1)).filter
        (fun x => x ∈ A ∧ (v - x) ∈ A ∧ x % 2 = 0 ∧
          (v - x) % 2 = 0)) ∪
      ((Finset.range (v + 1)).filter
        (fun x => x ∈ A ∧ (v - x) ∈ A ∧ x % 2 = 1 ∧
          (v - x) % 2 = 1)) ∪
      ((Finset.range (v + 1)).filter
        (fun x => x ∈ A ∧ (v - x) ∈ A ∧
          x % 2 ≠ (v - x) % 2)) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hxr, hxA, hxpA⟩ := hx
    rcases Nat.mod_two_eq_zero_or_one x with he | ho
    · rcases Nat.mod_two_eq_zero_or_one (v - x) with he' | ho'
      · exact Finset.mem_union_left _
          (Finset.mem_union_left _ (by
            rw [Finset.mem_filter]
            exact ⟨hxr, hxA, hxpA, he, he'⟩))
      · exact Finset.mem_union_right _ (by
          rw [Finset.mem_filter]
          exact ⟨hxr, hxA, hxpA, by omega⟩)
    · rcases Nat.mod_two_eq_zero_or_one (v - x) with he' | ho'
      · exact Finset.mem_union_right _ (by
          rw [Finset.mem_filter]
          exact ⟨hxr, hxA, hxpA, by omega⟩)
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _ (by
            rw [Finset.mem_filter]
            exact ⟨hxr, hxA, hxpA, ho, ho'⟩))
  have hc := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le
    (((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A ∧ x % 2 = 0 ∧
        (v - x) % 2 = 0)) ∪
     ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A ∧ x % 2 = 1 ∧
        (v - x) % 2 = 1)))
    ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A ∧
        x % 2 ≠ (v - x) % 2))
  have hu2 := Finset.card_union_le
    ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A ∧ x % 2 = 0 ∧
        (v - x) % 2 = 0))
    ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A ∧ x % 2 = 1 ∧
        (v - x) % 2 = 1))
  omega

open Classical in

theorem ee_channel_descends {A : Set ℕ} {v : ℕ}
    (hv : v % 2 = 0) :
    ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A ∧ x % 2 = 0 ∧
        (v - x) % 2 = 0)).card ≤
    ((Finset.range (v / 2 + 1)).filter
      (fun y => 2 * y ∈ A ∧ 2 * (v / 2 - y) ∈ A)).card := by
  apply Finset.card_le_card_of_injOn (fun x => x / 2)
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range] at hx
    obtain ⟨hxr, hxA, hxpA, hxe, hxpe⟩ := hx
    simp only [Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range]
    refine ⟨by omega, ?_, ?_⟩
    · have h1 : 2 * (x / 2) = x := by omega
      rw [h1]
      exact hxA
    · have h1 : 2 * (v / 2 - x / 2) = v - x := by omega
      rw [h1]
      exact hxpA
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range] at ha hb
    obtain ⟨_, _, _, hae, _⟩ := ha
    obtain ⟨_, _, _, hbe, _⟩ := hb
    have hab' : a / 2 = b / 2 := hab
    omega

open Classical in

theorem ee_amplification_descends {A : Set ℕ}
    (hee : ∀ C N, ∃ v, N ≤ v ∧ C ≤
      ((Finset.range (v + 1)).filter
        (fun x => x ∈ A ∧ (v - x) ∈ A ∧ x % 2 = 0 ∧
          (v - x) % 2 = 0)).card) :
    ∀ C N, ∃ w, N ≤ w ∧ C ≤
      ((Finset.range (w + 1)).filter
        (fun y => 2 * y ∈ A ∧ 2 * (w - y) ∈ A)).card := by
  intro C N
  obtain ⟨v, hvN, hvC⟩ := hee (C + 1) (2 * N)
  have hvne : ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A ∧ x % 2 = 0 ∧
        (v - x) % 2 = 0)).Nonempty :=
    Finset.card_pos.1 (by omega)
  obtain ⟨x₀, hx₀⟩ := hvne
  rw [Finset.mem_filter] at hx₀
  have hveven : v % 2 = 0 := by
    obtain ⟨hr, _, _, he, hpe⟩ := hx₀
    rw [Finset.mem_range] at hr
    omega
  have hdesc := ee_channel_descends (A := A) hveven
  exact ⟨v / 2, by omega, by omega⟩

open Classical in

theorem oo_channel_descends {A : Set ℕ} {v : ℕ}
    (hv : v % 2 = 0) :
    ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A ∧ x % 2 = 1 ∧
        (v - x) % 2 = 1)).card ≤
    ((Finset.range (v / 2)).filter
      (fun y => 2 * y + 1 ∈ A ∧
        2 * (v / 2 - 1 - y) + 1 ∈ A)).card := by
  apply Finset.card_le_card_of_injOn (fun x => x / 2)
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range] at hx
    obtain ⟨hxr, hxA, hxpA, hxo, hxpo⟩ := hx
    simp only [Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range]
    refine ⟨by omega, ?_, ?_⟩
    · have h1 : 2 * (x / 2) + 1 = x := by omega
      rw [h1]
      exact hxA
    · have h1 : 2 * (v / 2 - 1 - x / 2) + 1 = v - x := by
        omega
      rw [h1]
      exact hxpA
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range] at ha hb
    obtain ⟨_, _, _, hao, _⟩ := ha
    obtain ⟨_, _, _, hbo, _⟩ := hb
    have hab' : a / 2 = b / 2 := hab
    omega

open Classical in

theorem oo_amplification_descends {A : Set ℕ}
    (hoo : ∀ C N, ∃ v, N ≤ v ∧ C ≤
      ((Finset.range (v + 1)).filter
        (fun x => x ∈ A ∧ (v - x) ∈ A ∧ x % 2 = 1 ∧
          (v - x) % 2 = 1)).card) :
    ∀ C N, ∃ w, N ≤ w ∧ C ≤
      ((Finset.range (w + 1)).filter
        (fun y => 2 * y + 1 ∈ A ∧
          2 * (w - y) + 1 ∈ A)).card := by
  intro C N
  obtain ⟨v, hvN, hvC⟩ := hoo (C + 1) (2 * N + 2)
  have hvne : ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A ∧ x % 2 = 1 ∧
        (v - x) % 2 = 1)).Nonempty :=
    Finset.card_pos.1 (by omega)
  obtain ⟨x₀, hx₀⟩ := hvne
  rw [Finset.mem_filter] at hx₀
  have hveven : v % 2 = 0 := by
    obtain ⟨hr, _, _, ho, hpo⟩ := hx₀
    rw [Finset.mem_range] at hr
    omega
  have hdesc := oo_channel_descends (A := A) hveven
  refine ⟨v / 2 - 1, by omega, ?_⟩
  have hsub : (Finset.range (v / 2)).filter
      (fun y => 2 * y + 1 ∈ A ∧
        2 * (v / 2 - 1 - y) + 1 ∈ A) ⊆
      (Finset.range (v / 2 - 1 + 1)).filter
      (fun y => 2 * y + 1 ∈ A ∧
        2 * (v / 2 - 1 - y) + 1 ∈ A) := by
    intro y hy
    rw [Finset.mem_filter, Finset.mem_range] at hy
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hy.2⟩
  have h1 := Finset.card_le_card hsub
  omega

open Classical in

theorem mixed_channel_descends {A : Set ℕ} {v : ℕ}
    (hv : v % 2 = 1) :
    ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A ∧
        x % 2 ≠ (v - x) % 2)).card ≤
    2 * ((Finset.range ((v - 1) / 2 + 1)).filter
      (fun y => 2 * y ∈ A ∧
        2 * ((v - 1) / 2 - y) + 1 ∈ A)).card := by
  set M := (Finset.range (v + 1)).filter
    (fun x => x ∈ A ∧ (v - x) ∈ A ∧
      x % 2 ≠ (v - x) % 2) with hM
  set X := (Finset.range ((v - 1) / 2 + 1)).filter
    (fun y => 2 * y ∈ A ∧
      2 * ((v - 1) / 2 - y) + 1 ∈ A) with hX
  set Fe := M.filter (fun x => x % 2 = 0) with hFe
  set Fo := M.filter (fun x => x % 2 = 1) with hFo
  have hsplit : M.card ≤ Fe.card + Fo.card := by
    have hsub : M ⊆ Fe ∪ Fo := by
      intro x hx
      rcases Nat.mod_two_eq_zero_or_one x with h | h
      · exact Finset.mem_union_left _
          (Finset.mem_filter.2 ⟨hx, h⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.2 ⟨hx, h⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le Fe Fo
    omega
  have hFeX : Fe.card ≤ X.card := by
    apply Finset.card_le_card_of_injOn (fun x => x / 2)
    · intro x hx
      simp only [hFe, hM, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range] at hx
      obtain ⟨⟨hxr, hxA, hxpA, hxm⟩, hxe⟩ := hx
      simp only [hX, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range]
      refine ⟨by omega, ?_, ?_⟩
      · have h1 : 2 * (x / 2) = x := by omega
        rw [h1]
        exact hxA
      · have h1 : 2 * ((v - 1) / 2 - x / 2) + 1 = v - x := by
          omega
        rw [h1]
        exact hxpA
    · intro a ha b hb hab
      simp only [hFe, hM, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range] at ha hb
      obtain ⟨⟨_, _, _, _⟩, hae⟩ := ha
      obtain ⟨⟨_, _, _, _⟩, hbe⟩ := hb
      have hab' : a / 2 = b / 2 := hab
      omega
  have hFoX : Fo.card ≤ X.card := by
    apply Finset.card_le_card_of_injOn (fun x => (v - x) / 2)
    · intro x hx
      simp only [hFo, hM, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range] at hx
      obtain ⟨⟨hxr, hxA, hxpA, hxm⟩, hxo⟩ := hx
      simp only [hX, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range]
      refine ⟨by omega, ?_, ?_⟩
      · have h1 : 2 * ((v - x) / 2) = v - x := by omega
        rw [h1]
        exact hxpA
      · have h1 : 2 * ((v - 1) / 2 - (v - x) / 2) + 1 = x := by
          omega
        rw [h1]
        exact hxA
    · intro a ha b hb hab
      simp only [hFo, hM, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range] at ha hb
      obtain ⟨⟨har, _, _, _⟩, hao⟩ := ha
      obtain ⟨⟨hbr, _, _, _⟩, hbo⟩ := hb
      have hab' : (v - a) / 2 = (v - b) / 2 := hab
      omega
  omega

open Classical in

theorem total_nested_representation {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∀ C N, ∃ w, N ≤ w ∧ C ≤
      ((Finset.range (w + 1)).filter
        (fun y => 2 * y ∈ A ∧ 2 * (w - y) ∈ A)).card) ∨
    (∀ C N, ∃ w, N ≤ w ∧ C ≤
      ((Finset.range (w + 1)).filter
        (fun y => 2 * y + 1 ∈ A ∧
          2 * (w - y) + 1 ∈ A)).card) ∨
    (∀ C N, ∃ w, N ≤ w ∧ C ≤
      ((Finset.range (w + 1)).filter
        (fun y => 2 * y ∈ A ∧
          2 * (w - y) + 1 ∈ A)).card) := by
  rcases r2_channel_amplification h0 hcov hfail with hee | hoo | hmx
  · exact Or.inl (ee_amplification_descends hee)
  · exact Or.inr (Or.inl (oo_amplification_descends hoo))
  · refine Or.inr (Or.inr ?_)
    intro C N
    obtain ⟨v, hvN, hvC⟩ := hmx (2 * C + 1) (2 * N + 1)
    have hvne : ((Finset.range (v + 1)).filter
        (fun x => x ∈ A ∧ (v - x) ∈ A ∧
          x % 2 ≠ (v - x) % 2)).Nonempty :=
      Finset.card_pos.1 (by omega)
    obtain ⟨x₀, hx₀⟩ := hvne
    rw [Finset.mem_filter] at hx₀
    have hvodd : v % 2 = 1 := by
      obtain ⟨hr, _, _, hm⟩ := hx₀
      rw [Finset.mem_range] at hr
      omega
    have hdesc := mixed_channel_descends (A := A) hvodd
    exact ⟨(v - 1) / 2, by omega, by omega⟩

theorem even_target_channel_split {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀) :
    ∀ n, N₀ ≤ n → n % 2 = 0 →
      (∃ y y', 2 * y ∈ A ∧ 2 * y' ∈ A ∧ y + y' = n / 2) ∨
      (∃ y y', 2 * y + 1 ∈ A ∧ 2 * y' + 1 ∈ A ∧
        y + y' + 1 = n / 2) := by
  intro n hn hne
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov n hn
  rcases Nat.mod_two_eq_zero_or_one x with hxe | hxo
  · have hye : y % 2 = 0 := by omega
    left
    refine ⟨x / 2, y / 2, ?_, ?_, by omega⟩
    · have h1 : 2 * (x / 2) = x := by omega
      rw [h1]
      exact hx
    · have h1 : 2 * (y / 2) = y := by omega
      rw [h1]
      exact hy
  · have hyo : y % 2 = 1 := by omega
    right
    refine ⟨x / 2, y / 2, ?_, ?_, by omega⟩
    · have h1 : 2 * (x / 2) + 1 = x := by omega
      rw [h1]
      exact hx
    · have h1 : 2 * (y / 2) + 1 = y := by omega
      rw [h1]
      exact hy

theorem odd_target_cross_split {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀) :
    ∀ n, N₀ ≤ n → n % 2 = 1 →
      ∃ y y', 2 * y ∈ A ∧ 2 * y' + 1 ∈ A ∧
        y + y' = (n - 1) / 2 := by
  intro n hn hno
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov n hn
  rcases Nat.mod_two_eq_zero_or_one x with hxe | hxo
  · have hyo : y % 2 = 1 := by omega
    refine ⟨x / 2, y / 2, ?_, ?_, by omega⟩
    · have h1 : 2 * (x / 2) = x := by omega
      rw [h1]
      exact hx
    · have h1 : 2 * (y / 2) + 1 = y := by omega
      rw [h1]
      exact hy
  · have hye : y % 2 = 0 := by omega
    refine ⟨y / 2, x / 2, ?_, ?_, by omega⟩
    · have h1 : 2 * (y / 2) = y := by omega
      rw [h1]
      exact hy
    · have h1 : 2 * (x / 2) + 1 = x := by omega
      rw [h1]
      exact hx

theorem mixing_cross_slice_law {A : Set ℕ}
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {B₀ : Set ℕ} (hB₀A : ∀ b ∈ B₀, 2 * b ∈ A)
    (hB₀inf : B₀.Infinite) :
    ∀ N, ∃ n, N ≤ n ∧ ∀ z, z % 2 = 1 → z ∈ A →
      ∀ y y', 2 * y ∈ A → 2 * y' + 1 ∈ A →
        2 * y + (2 * y' + 1) + z = n → y ∈ B₀ := by
  set LB := {a : ℕ | ∃ b ∈ B₀, a = 2 * b} with hLB
  have hLBA : LB ⊆ A := by
    rintro a ⟨b, hb, rfl⟩
    exact hB₀A b hb
  have hLBinf : LB.Infinite := by
    have h1 : LB = (fun b => 2 * b) '' B₀ := by
      ext a
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨b, hb, rfl⟩
      · rintro ⟨b, hb, rfl⟩
        exact ⟨b, hb, rfl⟩
    rw [h1]
    exact hB₀inf.image (fun a _ b _ h => by omega)
  intro N
  obtain ⟨n, hn, hslice⟩ :=
    deletion_failure_slices hfail hLBA hLBinf N
  refine ⟨n, hn, ?_⟩
  intro z hzo hzA y y' hyA hy'A hsum
  have hzLB : z ∉ LB := by
    rintro ⟨b, hb, heq⟩
    omega
  have hy'LB : 2 * y' + 1 ∉ LB := by
    rintro ⟨b, hb, heq⟩
    omega
  rcases hslice z hzA hzLB (2 * y) hyA (2 * y' + 1) hy'A
    (by omega) with h | h
  · obtain ⟨b, hb, heq⟩ := h
    have h1 : y = b := by omega
    exact h1 ▸ hb
  · exact absurd h hy'LB

open Classical in

theorem mixing_cross_slice_poverty {A : Set ℕ}
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {B₀ : Set ℕ} (hB₀A : ∀ b ∈ B₀, 2 * b ∈ A)
    (hB₀inf : B₀.Infinite) :
    ∀ N, ∃ n, N ≤ n ∧ ∀ z, z % 2 = 1 → z ∈ A →
      ∀ W : Finset ℕ, (∀ b, b ∈ B₀ → b ≤ n → b ∈ W) →
      ((Finset.range (n + 1)).filter
        (fun y => 2 * y ∈ A ∧ (n - z - 2 * y) ∈ A ∧
          (n - z - 2 * y) % 2 = 1 ∧
          2 * y + z + 1 ≤ n)).card ≤ W.card := by
  intro N
  obtain ⟨n, hn, hlaw⟩ :=
    mixing_cross_slice_law hfail hB₀A hB₀inf N
  refine ⟨n, hn, ?_⟩
  intro z hzo hzA W hW
  apply Finset.card_le_card
  intro y hy
  rw [Finset.mem_filter, Finset.mem_range] at hy
  obtain ⟨hyr, hyA, hypA, hypo, hybd⟩ := hy
  have hy' : n - z - 2 * y = 2 * ((n - z - 2 * y - 1) / 2)
      + 1 := by omega
  have hyB₀ : y ∈ B₀ := by
    refine hlaw z hzo hzA y ((n - z - 2 * y - 1) / 2) hyA
      ?_ (by omega)
    rw [← hy']
    exact hypA
  exact hW y hyB₀ (by omega)

theorem half_worlds_joint_cover {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀) :
    ∀ n', N₀ ≤ 2 * n' →
      (∃ y y', 2 * y ∈ A ∧ 2 * y' ∈ A ∧ y + y' = n') ∨
      (∃ y y', 2 * y + 1 ∈ A ∧ 2 * y' + 1 ∈ A ∧
        y + y' + 1 = n') := by
  intro n' hn'
  have h := even_target_channel_split hcov (2 * n') hn'
    (by omega)
  have he : 2 * n' / 2 = n' := by omega
  rw [he] at h
  exact h

theorem half_cover_dichotomy {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀) :
    (∀ N, ∃ n', N ≤ n' ∧ ∃ y y', 2 * y ∈ A ∧ 2 * y' ∈ A ∧
      y + y' = n') ∨
    (∀ N, ∃ n', N ≤ n' ∧ ∃ y y', 2 * y + 1 ∈ A ∧
      2 * y' + 1 ∈ A ∧ y + y' + 1 = n') := by
  classical
  by_cases h0 : ∀ N, ∃ n', N ≤ n' ∧ ∃ y y', 2 * y ∈ A ∧
      2 * y' ∈ A ∧ y + y' = n'
  · exact Or.inl h0
  · right
    obtain ⟨N₁, hN₁⟩ := not_forall.mp h0
    intro N
    have hbig : N₀ ≤ 2 * (N + N₁ + N₀) := by omega
    rcases half_worlds_joint_cover hcov (N + N₁ + N₀) hbig
      with ⟨y, y', h1, h2, h3⟩ | ⟨y, y', h1, h2, h3⟩
    · exact absurd ⟨N + N₁ + N₀, by omega, y, y', h1, h2, h3⟩
        hN₁
    · exact ⟨N + N₁ + N₀, by omega, y, y', h1, h2, h3⟩

open Classical in

theorem cross_channel_split {S T : Set ℕ}
    (hST : ∀ C N, ∃ v, N ≤ v ∧ C ≤
      ((Finset.range (v + 1)).filter
        (fun x => x ∈ S ∧ (v - x) ∈ T)).card) :
    (∀ C N, ∃ v, N ≤ v ∧ C ≤ ((Finset.range (v + 1)).filter
      (fun x => x ∈ S ∧ (v - x) ∈ T ∧ x % 2 = 0 ∧
        (v - x) % 2 = 0)).card) ∨
    (∀ C N, ∃ v, N ≤ v ∧ C ≤ ((Finset.range (v + 1)).filter
      (fun x => x ∈ S ∧ (v - x) ∈ T ∧ x % 2 = 0 ∧
        (v - x) % 2 = 1)).card) ∨
    (∀ C N, ∃ v, N ≤ v ∧ C ≤ ((Finset.range (v + 1)).filter
      (fun x => x ∈ S ∧ (v - x) ∈ T ∧ x % 2 = 1 ∧
        (v - x) % 2 = 0)).card) ∨
    (∀ C N, ∃ v, N ≤ v ∧ C ≤ ((Finset.range (v + 1)).filter
      (fun x => x ∈ S ∧ (v - x) ∈ T ∧ x % 2 = 1 ∧
        (v - x) % 2 = 1)).card) := by
  classical
  by_contra hno
  push Not at hno
  obtain ⟨⟨C₁, N₁, h1⟩, ⟨C₂, N₂, h2⟩, ⟨C₃, N₃, h3⟩,
    ⟨C₄, N₄, h4⟩⟩ := hno
  obtain ⟨v, hvN, hvC⟩ := hST (C₁ + C₂ + C₃ + C₄ + 4)
    (N₁ + N₂ + N₃ + N₄)
  have hs1 := h1 v (by omega)
  have hs2 := h2 v (by omega)
  have hs3 := h3 v (by omega)
  have hs4 := h4 v (by omega)
  have hsub : (Finset.range (v + 1)).filter
      (fun x => x ∈ S ∧ (v - x) ∈ T) ⊆
      (((Finset.range (v + 1)).filter
        (fun x => x ∈ S ∧ (v - x) ∈ T ∧ x % 2 = 0 ∧
          (v - x) % 2 = 0)) ∪
       ((Finset.range (v + 1)).filter
        (fun x => x ∈ S ∧ (v - x) ∈ T ∧ x % 2 = 0 ∧
          (v - x) % 2 = 1))) ∪
      (((Finset.range (v + 1)).filter
        (fun x => x ∈ S ∧ (v - x) ∈ T ∧ x % 2 = 1 ∧
          (v - x) % 2 = 0)) ∪
       ((Finset.range (v + 1)).filter
        (fun x => x ∈ S ∧ (v - x) ∈ T ∧ x % 2 = 1 ∧
          (v - x) % 2 = 1))) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hxr, hxS, hxT⟩ := hx
    rcases Nat.mod_two_eq_zero_or_one x with he | ho <;>
      rcases Nat.mod_two_eq_zero_or_one (v - x) with he' | ho'
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.2 ⟨hxr, hxS, hxT, he, he'⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.2 ⟨hxr, hxS, hxT, he, ho'⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_filter.2 ⟨hxr, hxS, hxT, ho, he'⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_filter.2 ⟨hxr, hxS, hxT, ho, ho'⟩))
  have hc := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le
    (((Finset.range (v + 1)).filter
      (fun x => x ∈ S ∧ (v - x) ∈ T ∧ x % 2 = 0 ∧
        (v - x) % 2 = 0)) ∪
     ((Finset.range (v + 1)).filter
      (fun x => x ∈ S ∧ (v - x) ∈ T ∧ x % 2 = 0 ∧
        (v - x) % 2 = 1)))
    (((Finset.range (v + 1)).filter
      (fun x => x ∈ S ∧ (v - x) ∈ T ∧ x % 2 = 1 ∧
        (v - x) % 2 = 0)) ∪
     ((Finset.range (v + 1)).filter
      (fun x => x ∈ S ∧ (v - x) ∈ T ∧ x % 2 = 1 ∧
        (v - x) % 2 = 1)))
  have hu2 := Finset.card_union_le
    ((Finset.range (v + 1)).filter
      (fun x => x ∈ S ∧ (v - x) ∈ T ∧ x % 2 = 0 ∧
        (v - x) % 2 = 0))
    ((Finset.range (v + 1)).filter
      (fun x => x ∈ S ∧ (v - x) ∈ T ∧ x % 2 = 0 ∧
        (v - x) % 2 = 1))
  have hu3 := Finset.card_union_le
    ((Finset.range (v + 1)).filter
      (fun x => x ∈ S ∧ (v - x) ∈ T ∧ x % 2 = 1 ∧
        (v - x) % 2 = 0))
    ((Finset.range (v + 1)).filter
      (fun x => x ∈ S ∧ (v - x) ∈ T ∧ x % 2 = 1 ∧
        (v - x) % 2 = 1))
  omega
open Classical in

theorem cross_channel_descends {S T : Set ℕ} {p q : ℕ}
    (hp : p < 2) (hq : q < 2) {v : ℕ}
    (hv : v % 2 = (p + q) % 2) :
    ((Finset.range (v + 1)).filter
      (fun x => x ∈ S ∧ (v - x) ∈ T ∧ x % 2 = p ∧
        (v - x) % 2 = q)).card ≤
    ((Finset.range ((v - p - q) / 2 + 1)).filter
      (fun y => 2 * y + p ∈ S ∧
        2 * ((v - p - q) / 2 - y) + q ∈ T)).card := by
  apply Finset.card_le_card_of_injOn (fun x => x / 2)
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range] at hx
    obtain ⟨hxr, hxS, hxT, hxp, hxq⟩ := hx
    simp only [Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range]
    refine ⟨by omega, ?_, ?_⟩
    · have h1 : 2 * (x / 2) + p = x := by omega
      rw [h1]
      exact hxS
    · have h1 : 2 * ((v - p - q) / 2 - x / 2) + q = v - x := by
        omega
      rw [h1]
      exact hxT
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range] at ha hb
    obtain ⟨_, _, _, hap, _⟩ := ha
    obtain ⟨_, _, _, hbp, _⟩ := hb
    have hab' : a / 2 = b / 2 := hab
    omega

open Classical in

theorem cross_amplification_descends {S T : Set ℕ} {p q : ℕ}
    (hp : p < 2) (hq : q < 2)
    (hch : ∀ C N, ∃ v, N ≤ v ∧ C ≤
      ((Finset.range (v + 1)).filter
        (fun x => x ∈ S ∧ (v - x) ∈ T ∧ x % 2 = p ∧
          (v - x) % 2 = q)).card) :
    ∀ C N, ∃ w, N ≤ w ∧ C ≤
      ((Finset.range (w + 1)).filter
        (fun y => 2 * y + p ∈ S ∧
          2 * (w - y) + q ∈ T)).card := by
  intro C N
  obtain ⟨v, hvN, hvC⟩ := hch (C + 1) (2 * N + 2)
  have hvne : ((Finset.range (v + 1)).filter
      (fun x => x ∈ S ∧ (v - x) ∈ T ∧ x % 2 = p ∧
        (v - x) % 2 = q)).Nonempty :=
    Finset.card_pos.1 (by omega)
  obtain ⟨x₀, hx₀⟩ := hvne
  rw [Finset.mem_filter] at hx₀
  have hvpar : v % 2 = (p + q) % 2 := by
    obtain ⟨hr, _, _, hxp, hxq⟩ := hx₀
    rw [Finset.mem_range] at hr
    omega
  have hdesc := cross_channel_descends (S := S) (T := T)
    hp hq hvpar
  exact ⟨(v - p - q) / 2, by omega, by omega⟩

open Classical in

theorem omega_nested_representation {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ S T : ℕ → Set ℕ, S 0 = A ∧ T 0 = A ∧
      (∀ k, ∃ p q, p < 2 ∧ q < 2 ∧
        S (k + 1) = {y | 2 * y + p ∈ S k} ∧
        T (k + 1) = {y | 2 * y + q ∈ T k}) ∧
      ∀ k C N, ∃ v, N ≤ v ∧ C ≤
        ((Finset.range (v + 1)).filter
          (fun x => x ∈ S k ∧ (v - x) ∈ T k)).card := by
  have hstep : ∀ S T : Set ℕ,
      (∀ C N, ∃ v, N ≤ v ∧ C ≤ ((Finset.range (v + 1)).filter
        (fun x => x ∈ S ∧ (v - x) ∈ T)).card) →
      ∃ p q, p < 2 ∧ q < 2 ∧
        ∀ C N, ∃ v, N ≤ v ∧ C ≤
          ((Finset.range (v + 1)).filter
            (fun x => x ∈ {y | 2 * y + p ∈ S} ∧
              (v - x) ∈ {y | 2 * y + q ∈ T})).card := by
    intro S T h
    have hconv : ∀ (p q : ℕ),
        (∀ C N, ∃ w, N ≤ w ∧ C ≤
          ((Finset.range (w + 1)).filter
            (fun y => 2 * y + p ∈ S ∧
              2 * (w - y) + q ∈ T)).card) →
        (∀ C N, ∃ v, N ≤ v ∧ C ≤
          ((Finset.range (v + 1)).filter
            (fun x => x ∈ {y | 2 * y + p ∈ S} ∧
              (v - x) ∈ {y | 2 * y + q ∈ T})).card) := by
      intro p q hh C N
      obtain ⟨w, hw, hc⟩ := hh C N
      refine ⟨w, hw, ?_⟩
      have he : (Finset.range (w + 1)).filter
          (fun y => 2 * y + p ∈ S ∧ 2 * (w - y) + q ∈ T) =
          (Finset.range (w + 1)).filter
          (fun x => x ∈ {y | 2 * y + p ∈ S} ∧
            (w - x) ∈ {y | 2 * y + q ∈ T}) := by
        apply Finset.filter_congr
        intro x _
        simp [Set.mem_setOf_eq]
      rw [← he]
      exact hc
    rcases cross_channel_split h with h1 | h1 | h1 | h1
    · exact ⟨0, 0, by omega, by omega, hconv 0 0
        (cross_amplification_descends (by omega) (by omega) h1)⟩
    · exact ⟨0, 1, by omega, by omega, hconv 0 1
        (cross_amplification_descends (by omega) (by omega) h1)⟩
    · exact ⟨1, 0, by omega, by omega, hconv 1 0
        (cross_amplification_descends (by omega) (by omega) h1)⟩
    · exact ⟨1, 1, by omega, by omega, hconv 1 1
        (cross_amplification_descends (by omega) (by omega) h1)⟩
  have hroot : ∀ C N, ∃ v, N ≤ v ∧ C ≤
      ((Finset.range (v + 1)).filter
        (fun x => x ∈ A ∧ (v - x) ∈ A)).card :=
    fun C N => r2_unbounded_of_hfail h0 hcov hfail C N
  set Blow : Set ℕ × Set ℕ → Prop := fun ST =>
    ∀ C N, ∃ v, N ≤ v ∧ C ≤
      ((Finset.range (v + 1)).filter
        (fun x => x ∈ ST.1 ∧ (v - x) ∈ ST.2)).card with hBlow
  have hstep' : ∀ ST : Set ℕ × Set ℕ, Blow ST →
      ∃ ST' : Set ℕ × Set ℕ, (∃ p q, p < 2 ∧ q < 2 ∧
        ST'.1 = {y | 2 * y + p ∈ ST.1} ∧
        ST'.2 = {y | 2 * y + q ∈ ST.2}) ∧ Blow ST' := by
    rintro ⟨S, T⟩ hB
    obtain ⟨p, q, hp, hq, hB'⟩ := hstep S T hB
    exact ⟨({y | 2 * y + p ∈ S}, {y | 2 * y + q ∈ T}),
      ⟨p, q, hp, hq, rfl, rfl⟩, hB'⟩
  have hnext : ∀ ST : Set ℕ × Set ℕ, ∃ ST' : Set ℕ × Set ℕ,
      Blow ST → ((∃ p q, p < 2 ∧ q < 2 ∧
        ST'.1 = {y | 2 * y + p ∈ ST.1} ∧
        ST'.2 = {y | 2 * y + q ∈ ST.2}) ∧ Blow ST') := by
    intro ST
    by_cases hB : Blow ST
    · obtain ⟨ST', h1, h2⟩ := hstep' ST hB
      exact ⟨ST', fun _ => ⟨h1, h2⟩⟩
    · exact ⟨ST, fun h => absurd h hB⟩
  choose nx hnx using hnext
  set st : ℕ → Set ℕ × Set ℕ := fun k =>
    Nat.rec (A, A) (fun _ prev => nx prev) k with hst
  have hstS : ∀ k, st (k + 1) = nx (st k) := fun _ => rfl
  have hB : ∀ k, Blow (st k) := by
    intro k
    induction k with
    | zero => exact hroot
    | succ k ih =>
      rw [hstS]
      exact (hnx (st k) ih).2
  refine ⟨fun k => (st k).1, fun k => (st k).2, rfl, rfl,
    ?_, ?_⟩
  · intro k
    have h1 := (hnx (st k) (hB k)).1
    obtain ⟨p, q, hp, hq, h2, h3⟩ := h1
    refine ⟨p, q, hp, hq, ?_, ?_⟩
    · show (st (k + 1)).1 = _
      rw [hstS]
      exact h2
    · show (st (k + 1)).2 = _
      rw [hstS]
      exact h3
  · intro k
    exact hB k

open Classical in

theorem cross_amplification_infinite {S T : Set ℕ}
    (h : ∀ C N, ∃ v, N ≤ v ∧ C ≤
      ((Finset.range (v + 1)).filter
        (fun x => x ∈ S ∧ (v - x) ∈ T)).card) :
    S.Infinite ∧ T.Infinite := by
  constructor
  · by_contra hS
    rw [Set.not_infinite] at hS
    obtain ⟨v, hv, hc⟩ := h (hS.toFinset.card + 1) 0
    have hsub : (Finset.range (v + 1)).filter
        (fun x => x ∈ S ∧ (v - x) ∈ T) ⊆ hS.toFinset := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Set.Finite.mem_toFinset]
      exact hx.2.1
    have := Finset.card_le_card hsub
    omega
  · by_contra hT
    rw [Set.not_infinite] at hT
    obtain ⟨v, hv, hc⟩ := h (hT.toFinset.card + 1) 0
    have hinj : ((Finset.range (v + 1)).filter
        (fun x => x ∈ S ∧ (v - x) ∈ T)).card ≤
        hT.toFinset.card := by
      apply Finset.card_le_card_of_injOn (fun x => v - x)
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_filter,
          Finset.mem_range] at hx
        simp only [Finset.mem_coe, Set.Finite.mem_toFinset]
        exact hx.2.2
      · intro a ha b hb hab
        simp only [Finset.mem_coe, Finset.mem_filter,
          Finset.mem_range] at ha hb
        have hab' : v - a = v - b := hab
        omega
    omega

open Classical in

theorem nested_representation_address_cluster {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ c : ℕ → ℕ, c 0 = 0 ∧
      (∀ k, ∃ p, p < 2 ∧ c (k + 1) = c k + 2 ^ k * p) ∧
      ∀ k N, ∃ a, N ≤ a ∧ a ∈ A ∧
        ∃ y, a = c k + 2 ^ k * y := by
  obtain ⟨S, T, hS0, hT0, hstep, hblow⟩ :=
    omega_nested_representation h0 hcov hfail
  choose pf qf hpf hqf hSe hTe using hstep
  set c : ℕ → ℕ := fun k =>
    Nat.rec 0 (fun k' acc => acc + 2 ^ k' * pf k') k with hc
  have hc0 : c 0 = 0 := rfl
  have hcS : ∀ k, c (k + 1) = c k + 2 ^ k * pf k :=
    fun _ => rfl
  have hlift : ∀ k y, y ∈ S k ↔ c k + 2 ^ k * y ∈ A := by
    intro k
    induction k with
    | zero =>
      intro y
      have he : c 0 + 2 ^ 0 * y = y := by
        rw [hc0]
        simp
      rw [he, hS0]
    | succ k ih =>
      intro y
      rw [hSe k, Set.mem_setOf_eq, ih (2 * y + pf k)]
      have he : c k + 2 ^ k * (2 * y + pf k) =
          c (k + 1) + 2 ^ (k + 1) * y := by
        rw [hcS k, pow_succ]
        ring
      rw [he]
  have hinf : ∀ k, (S k).Infinite :=
    fun k => (cross_amplification_infinite (hblow k)).1
  refine ⟨c, hc0, fun k => ⟨pf k, hpf k, hcS k⟩, ?_⟩
  intro k N
  obtain ⟨y, hyS, hyN⟩ := (hinf k).exists_gt N
  have hple : y ≤ 2 ^ k * y :=
    Nat.le_mul_of_pos_left y (pow_pos (by omega) k)
  exact ⟨c k + 2 ^ k * y, by omega, (hlift k y).1 hyS,
    y, rfl⟩

open Classical in

theorem nested_representation_repair_family {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ k C, ∃ a b δ : ℕ, 0 < δ ∧ 2 ^ k ∣ δ ∧ C ≤ a ∧ δ ≤ b ∧
      a ∈ A ∧ a + δ ∈ A ∧ b ∈ A ∧ b - δ ∈ A := by
  obtain ⟨S, T, hS0, hT0, hstep, hblow⟩ :=
    omega_nested_representation h0 hcov hfail
  choose pf qf hpf hqf hSe hTe using hstep
  set c : ℕ → ℕ := fun k =>
    Nat.rec 0 (fun k' acc => acc + 2 ^ k' * pf k') k with hc
  set d : ℕ → ℕ := fun k =>
    Nat.rec 0 (fun k' acc => acc + 2 ^ k' * qf k') k with hd
  have hc0 : c 0 = 0 := rfl
  have hd0 : d 0 = 0 := rfl
  have hcS : ∀ k, c (k + 1) = c k + 2 ^ k * pf k :=
    fun _ => rfl
  have hdS : ∀ k, d (k + 1) = d k + 2 ^ k * qf k :=
    fun _ => rfl
  have hliftS : ∀ k y, y ∈ S k ↔ c k + 2 ^ k * y ∈ A := by
    intro k
    induction k with
    | zero =>
      intro y
      have he : c 0 + 2 ^ 0 * y = y := by
        rw [hc0]
        simp
      rw [he, hS0]
    | succ k ih =>
      intro y
      rw [hSe k, Set.mem_setOf_eq, ih (2 * y + pf k)]
      have he : c k + 2 ^ k * (2 * y + pf k) =
          c (k + 1) + 2 ^ (k + 1) * y := by
        rw [hcS k, pow_succ]
        ring
      rw [he]
  have hliftT : ∀ k y, y ∈ T k ↔ d k + 2 ^ k * y ∈ A := by
    intro k
    induction k with
    | zero =>
      intro y
      have he : d 0 + 2 ^ 0 * y = y := by
        rw [hd0]
        simp
      rw [he, hT0]
    | succ k ih =>
      intro y
      rw [hTe k, Set.mem_setOf_eq, ih (2 * y + qf k)]
      have he : d k + 2 ^ k * (2 * y + qf k) =
          d (k + 1) + 2 ^ (k + 1) * y := by
        rw [hdS k, pow_succ]
        ring
      rw [he]
  intro k C
  obtain ⟨v, hvN, hvc⟩ := hblow k (C + 2) 0
  set F := (Finset.range (v + 1)).filter
    (fun x => x ∈ S k ∧ (v - x) ∈ T k) with hF
  have hcov2 : F ⊆ F.filter (fun x => C ≤ x) ∪
      Finset.range C := by
    intro x hxF
    by_cases hxc : C ≤ x
    · exact Finset.mem_union_left _
        (Finset.mem_filter.2 ⟨hxF, hxc⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_range.2 (by omega))
  have hcard2 : 2 ≤ (F.filter (fun x => C ≤ x)).card := by
    have h2 := Finset.card_le_card hcov2
    have h3 := Finset.card_union_le
      (F.filter (fun x => C ≤ x)) (Finset.range C)
    have h4 : (Finset.range C).card = C := Finset.card_range C
    omega
  have h1lt : 1 < (F.filter (fun x => C ≤ x)).card := by omega
  obtain ⟨x₁, hx₁, x₂, hx₂, hne⟩ := Finset.one_lt_card.1 h1lt
  have key : ∀ x y : ℕ, x ∈ F.filter (fun x => C ≤ x) →
      y ∈ F.filter (fun x => C ≤ x) → x < y →
      ∃ a b δ : ℕ, 0 < δ ∧ 2 ^ k ∣ δ ∧ C ≤ a ∧ δ ≤ b ∧
        a ∈ A ∧ a + δ ∈ A ∧ b ∈ A ∧ b - δ ∈ A := by
    intro x y hx hy hxy
    rw [Finset.mem_filter] at hx hy
    obtain ⟨hxF, hxC⟩ := hx
    obtain ⟨hyF, hyC⟩ := hy
    rw [hF, Finset.mem_filter, Finset.mem_range] at hxF hyF
    obtain ⟨hxv, hxS, hxT⟩ := hxF
    obtain ⟨hyv, hyS, hyT⟩ := hyF
    have hpow : 0 < 2 ^ k := pow_pos (by omega) k
    refine ⟨c k + 2 ^ k * x, d k + 2 ^ k * (v - x),
      2 ^ k * (y - x), Nat.mul_pos hpow (by omega),
      ⟨y - x, rfl⟩, ?_, ?_, (hliftS k x).1 hxS, ?_,
      (hliftT k (v - x)).1 hxT, ?_⟩
    · have hle : x ≤ 2 ^ k * x :=
        Nat.le_mul_of_pos_left x hpow
      omega
    · have h5 : y - x ≤ v - x := by omega
      have h6 := Nat.mul_le_mul_left (2 ^ k) h5
      omega
    · have h7 : x + (y - x) = y := by omega
      have h6 : 2 ^ k * y = 2 ^ k * x + 2 ^ k * (y - x) := by
        rw [← Nat.mul_add, h7]
      have hsum : c k + 2 ^ k * x + 2 ^ k * (y - x) =
          c k + 2 ^ k * y := by omega
      rw [hsum]
      exact (hliftS k y).1 hyS
    · have h9 : v - y + (y - x) = v - x := by omega
      have h8 : 2 ^ k * (v - x) =
          2 ^ k * (v - y) + 2 ^ k * (y - x) := by
        rw [← Nat.mul_add, h9]
      have h10 : d k + 2 ^ k * (v - x) - 2 ^ k * (y - x) =
          d k + 2 ^ k * (v - y) := by omega
      rw [h10]
      exact (hliftT k (v - y)).1 hyT
  have hne' : x₁ ≠ x₂ := hne
  rcases lt_or_gt_of_ne hne' with hlt | hlt
  · exact key x₁ x₂ hx₁ hx₂ hlt
  · exact key x₂ x₁ hx₂ hx₁ hlt

open Classical in

theorem nested_representation_wealth_addresses {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ e : ℕ → ℕ, e 0 = 0 ∧
      (∀ k, ∃ r, r ≤ 2 ∧ e (k + 1) = e k + 2 ^ k * r) ∧
      ∀ k C N, ∃ w y, N ≤ w ∧ w = e k + 2 ^ k * y ∧
        C ≤ ((Finset.range (w + 1)).filter
          (fun x => x ∈ A ∧ (w - x) ∈ A)).card := by
  obtain ⟨S, T, hS0, hT0, hstep, hblow⟩ :=
    omega_nested_representation h0 hcov hfail
  choose pf qf hpf hqf hSe hTe using hstep
  set c : ℕ → ℕ := fun k =>
    Nat.rec 0 (fun k' acc => acc + 2 ^ k' * pf k') k with hc
  set d : ℕ → ℕ := fun k =>
    Nat.rec 0 (fun k' acc => acc + 2 ^ k' * qf k') k with hd
  have hc0 : c 0 = 0 := rfl
  have hd0 : d 0 = 0 := rfl
  have hcS : ∀ k, c (k + 1) = c k + 2 ^ k * pf k :=
    fun _ => rfl
  have hdS : ∀ k, d (k + 1) = d k + 2 ^ k * qf k :=
    fun _ => rfl
  have hliftS : ∀ k y, y ∈ S k ↔ c k + 2 ^ k * y ∈ A := by
    intro k
    induction k with
    | zero =>
      intro y
      have he : c 0 + 2 ^ 0 * y = y := by
        rw [hc0]
        simp
      rw [he, hS0]
    | succ k ih =>
      intro y
      rw [hSe k, Set.mem_setOf_eq, ih (2 * y + pf k)]
      have he : c k + 2 ^ k * (2 * y + pf k) =
          c (k + 1) + 2 ^ (k + 1) * y := by
        rw [hcS k, pow_succ]
        ring
      rw [he]
  have hliftT : ∀ k y, y ∈ T k ↔ d k + 2 ^ k * y ∈ A := by
    intro k
    induction k with
    | zero =>
      intro y
      have he : d 0 + 2 ^ 0 * y = y := by
        rw [hd0]
        simp
      rw [he, hT0]
    | succ k ih =>
      intro y
      rw [hTe k, Set.mem_setOf_eq, ih (2 * y + qf k)]
      have he : d k + 2 ^ k * (2 * y + qf k) =
          d (k + 1) + 2 ^ (k + 1) * y := by
        rw [hdS k, pow_succ]
        ring
      rw [he]
  refine ⟨fun k => c k + d k, ?_, ?_, ?_⟩
  · show c 0 + d 0 = 0
    rw [hc0, hd0]
  · intro k
    refine ⟨pf k + qf k, by have := hpf k; have := hqf k; omega,
      ?_⟩
    show c (k + 1) + d (k + 1) =
      c k + d k + 2 ^ k * (pf k + qf k)
    rw [hcS k, hdS k, Nat.mul_add]
    ring
  · intro k C N
    obtain ⟨v, hvN, hvc⟩ := hblow k C N
    have hpow : 0 < 2 ^ k := pow_pos (by omega) k
    have hvle : v ≤ 2 ^ k * v := Nat.le_mul_of_pos_left v hpow
    refine ⟨c k + d k + 2 ^ k * v, v, by omega, rfl, ?_⟩
    refine le_trans hvc ?_
    apply Finset.card_le_card_of_injOn
      (fun x => c k + 2 ^ k * x)
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range] at hx
      obtain ⟨hxv, hxS, hxT⟩ := hx
      have hxle : 2 ^ k * x ≤ 2 ^ k * v :=
        Nat.mul_le_mul_left _ (by omega)
      simp only [Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range]
      refine ⟨by omega, (hliftS k x).1 hxS, ?_⟩
      have h7 : v - x + x = v := by omega
      have h8 : 2 ^ k * v = 2 ^ k * (v - x) + 2 ^ k * x := by
        rw [← Nat.mul_add, h7]
      have h9 : c k + d k + 2 ^ k * v - (c k + 2 ^ k * x) =
          d k + 2 ^ k * (v - x) := by omega
      rw [h9]
      exact (hliftT k (v - x)).1 hxT
    · intro a ha b hb hab
      have hab' : c k + 2 ^ k * a = c k + 2 ^ k * b := hab
      have h10 : 2 ^ k * a = 2 ^ k * b := by omega
      exact Nat.eq_of_mul_eq_mul_left hpow h10

open Classical in

theorem repSupportTransversal_caps_pair_wealth {A : Set ℕ} {w : ℕ}
    {H : Finset ℕ}
    (h0 : 0 ∈ A) (h0H : 0 ∉ H) (hhub : IsRepSupportTransversal A w H) :
    ((Finset.range (w + 1)).filter
      (fun x => x ∈ A ∧ (w - x) ∈ A)).card ≤ 2 * H.card := by
  have hpair := pairSupportTransversal_of_repSupportTransversal h0 h0H hhub
  have hlow := pair_support_transversal_pair_count hpair
  set Low := (Finset.range (w + 1)).filter
    (fun a => a ∈ A ∧ (w - a) ∈ A ∧ 2 * a ≤ w) with hLow
  set High := (Finset.range (w + 1)).filter
    (fun a => a ∈ A ∧ (w - a) ∈ A ∧ w < 2 * a) with hHigh
  have hsub : (Finset.range (w + 1)).filter
      (fun x => x ∈ A ∧ (w - x) ∈ A) ⊆ Low ∪ High := by
    intro a ha
    rw [Finset.mem_filter, Finset.mem_range] at ha
    obtain ⟨hav, haA, hwaA⟩ := ha
    rcases Nat.lt_or_ge w (2 * a) with hc | hc
    · exact Finset.mem_union_right _ (Finset.mem_filter.2
        ⟨Finset.mem_range.2 hav, haA, hwaA, hc⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.2
        ⟨Finset.mem_range.2 hav, haA, hwaA, hc⟩)
  have hHL : High.card ≤ Low.card := by
    apply Finset.card_le_card_of_injOn (fun a => w - a)
    · intro a ha
      simp only [hHigh, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range] at ha
      obtain ⟨hav, haA, hwaA, hc⟩ := ha
      simp only [hLow, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range]
      have he : w - (w - a) = a := by omega
      rw [he]
      exact ⟨by omega, hwaA, haA, by omega⟩
    · intro a ha b hb hab
      simp only [hHigh, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range] at ha hb
      have hab' : w - a = w - b := hab
      omega
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le Low High
  omega

open Classical in

theorem target_sequence_is_sidon_poor {A : Set ℕ} {L m s J : ℕ}
    {x : ℕ → ℕ}
    (h0 : 0 ∈ A) (hx : ∀ t, 0 < x t) (hJL : J ≤ L)
    (hhub : IsRepSupportTransversal A m
      ((Finset.range J).image (fun j => x (s + j)))) :
    ((Finset.range (m + 1)).filter
      (fun z => z ∈ A ∧ (m - z) ∈ A)).card ≤ 2 * L := by
  have h0H : 0 ∉ (Finset.range J).image
      (fun j => x (s + j)) := by
    rw [Finset.mem_image]
    rintro ⟨j, hj, hxj⟩
    have := hx (s + j)
    omega
  have hcap := repSupportTransversal_caps_pair_wealth h0 h0H hhub
  have hcard : ((Finset.range J).image
      (fun j => x (s + j))).card ≤ L := by
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_range]
    exact hJL
  omega

open Classical in

theorem saturated_contradicts_antidiagonal {A : Set ℕ} {Y ε : ℕ}
    (hpar : ∀ a ∈ A, Y < a → a % 2 = ε)
    {S1 T1 : Set ℕ} {p q : ℕ} (hp : p < 2) (hq : q < 2)
    (hS1 : S1 = {y | 2 * y + p ∈ A})
    (hT1 : T1 = {y | 2 * y + q ∈ A})
    (hblow : ∀ C N, ∃ v, N ≤ v ∧ C ≤
      ((Finset.range (v + 1)).filter
        (fun x => x ∈ S1 ∧ (v - x) ∈ T1)).card) :
    p = q := by
  by_contra hne
  have hpq : p + q = 1 := by omega
  obtain ⟨v, hvN, hvc⟩ := hblow (2 * Y + 3) (Y + 1)
  set w := 2 * v + p + q with hw
  have hcap := global_parity_odd_ordered_cap hpar w
    (by omega) (by omega)
  have hinj : ((Finset.range (v + 1)).filter
      (fun x => x ∈ S1 ∧ (v - x) ∈ T1)).card ≤
      ((Finset.range (w + 1)).filter
        (fun z => z ∈ A ∧ (w - z) ∈ A)).card := by
    apply Finset.card_le_card_of_injOn (fun x => 2 * x + p)
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range] at hx
      obtain ⟨hxv, hxS, hxT⟩ := hx
      rw [hS1, Set.mem_setOf_eq] at hxS
      rw [hT1, Set.mem_setOf_eq] at hxT
      simp only [Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range]
      refine ⟨by omega, hxS, ?_⟩
      have he : w - (2 * x + p) = 2 * (v - x) + q := by omega
      rw [he]
      exact hxT
    · intro a ha b hb hab
      have hab' : 2 * a + p = 2 * b + p := hab
      omega
  omega

open Classical in

theorem saturated_nested_representation_diagonal {A : Set ℕ} {N₀ Y ε : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hpar : ∀ a ∈ A, Y < a → a % 2 = ε) :
    ∃ S T : ℕ → Set ℕ, S 0 = A ∧ T 0 = A ∧
      (∀ k, ∃ p q, p < 2 ∧ q < 2 ∧
        S (k + 1) = {y | 2 * y + p ∈ S k} ∧
        T (k + 1) = {y | 2 * y + q ∈ T k}) ∧
      (∀ k, ∀ C N, ∃ v, N ≤ v ∧ C ≤
        ((Finset.range (v + 1)).filter
          (fun x => x ∈ S k ∧ (v - x) ∈ T k)).card) ∧
      ∀ p q, p < 2 → q < 2 →
        S 1 = {y | 2 * y + p ∈ S 0} →
        T 1 = {y | 2 * y + q ∈ T 0} → p = q := by
  obtain ⟨S, T, hS0, hT0, hstep, hblow⟩ :=
    omega_nested_representation h0 hcov hfail
  refine ⟨S, T, hS0, hT0, hstep, hblow, ?_⟩
  intro p q hp hq hS1 hT1
  rw [hS0] at hS1
  rw [hT0] at hT1
  exact saturated_contradicts_antidiagonal hpar hp hq hS1 hT1
    (hblow 1)

open Classical in

theorem saturated_nested_representation_pinned {A : Set ℕ} {N₀ Y ε : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hpar : ∀ a ∈ A, Y < a → a % 2 = ε) :
    ∃ S T : ℕ → Set ℕ, S 0 = A ∧ T 0 = A ∧
      (∀ k, ∃ p q, p < 2 ∧ q < 2 ∧
        S (k + 1) = {y | 2 * y + p ∈ S k} ∧
        T (k + 1) = {y | 2 * y + q ∈ T k}) ∧
      (∀ k, ∀ C N, ∃ v, N ≤ v ∧ C ≤
        ((Finset.range (v + 1)).filter
          (fun x => x ∈ S k ∧ (v - x) ∈ T k)).card) ∧
      ∀ p q, p < 2 → q < 2 →
        S 1 = {y | 2 * y + p ∈ S 0} →
        T 1 = {y | 2 * y + q ∈ T 0} →
        p = ε ∧ q = ε ∧ S 1 = {x : ℕ | ε + 2 * x ∈ A} ∧
          T 1 = {x : ℕ | ε + 2 * x ∈ A} := by
  obtain ⟨S, T, hS0, hT0, hstep, hblow⟩ :=
    omega_nested_representation h0 hcov hfail
  refine ⟨S, T, hS0, hT0, hstep, hblow, ?_⟩
  intro p q hp hq hS1 hT1
  rw [hS0] at hS1
  rw [hT0] at hT1
  have hpq := saturated_contradicts_antidiagonal hpar hp hq hS1 hT1
    (hblow 1)
  have hSinf : (S 1).Infinite :=
    (cross_amplification_infinite (hblow 1)).1
  obtain ⟨y, hyS, hyY⟩ := hSinf.exists_gt Y
  have hyA : 2 * y + p ∈ A := by
    rw [hS1] at hyS
    exact hyS
  have hppar : p = ε := by
    have h2 := hpar (2 * y + p) hyA (by omega)
    omega
  have hqpar : q = ε := by omega
  refine ⟨hppar, hqpar, ?_, ?_⟩
  · rw [hS1, hppar]
    ext z
    simp only [Set.mem_setOf_eq]
    have he : 2 * z + ε = ε + 2 * z := by ring
    rw [he]
  · rw [hT1, hqpar]
    ext z
    simp only [Set.mem_setOf_eq]
    have he : 2 * z + ε = ε + 2 * z := by ring
    rw [he]

open Classical in

theorem saturated_iteration_step {W : Set ℕ} {Y ε : ℕ}
    (hpar : ∀ a ∈ W, Y < a → a % 2 = ε)
    {S1 T1 : Set ℕ} {p q : ℕ} (hp : p < 2) (hq : q < 2)
    (hS1 : S1 = {y | 2 * y + p ∈ W})
    (hT1 : T1 = {y | 2 * y + q ∈ W})
    (hblow : ∀ C N, ∃ v, N ≤ v ∧ C ≤
      ((Finset.range (v + 1)).filter
        (fun x => x ∈ S1 ∧ (v - x) ∈ T1)).card) :
    p = ε ∧ q = ε ∧ S1 = {x : ℕ | ε + 2 * x ∈ W} ∧
      T1 = {x : ℕ | ε + 2 * x ∈ W} := by
  have hpq := saturated_contradicts_antidiagonal hpar hp hq hS1 hT1
    hblow
  have hSinf : S1.Infinite := (cross_amplification_infinite hblow).1
  obtain ⟨y, hyS, hyY⟩ := hSinf.exists_gt Y
  have hyW : 2 * y + p ∈ W := by
    rw [hS1] at hyS
    exact hyS
  have hppar : p = ε := by
    have h2 := hpar (2 * y + p) hyW (by omega)
    omega
  have hqpar : q = ε := by omega
  refine ⟨hppar, hqpar, ?_, ?_⟩
  · rw [hS1, hppar]
    ext z
    simp only [Set.mem_setOf_eq]
    have he : 2 * z + ε = ε + 2 * z := by ring
    rw [he]
  · rw [hT1, hqpar]
    ext z
    simp only [Set.mem_setOf_eq]
    have he : 2 * z + ε = ε + 2 * z := by ring
    rw [he]

open Classical in

theorem saturated_iteration_determined {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ S T : ℕ → Set ℕ, S 0 = A ∧ T 0 = A ∧
      (∀ k, ∃ p q, p < 2 ∧ q < 2 ∧
        S (k + 1) = {y | 2 * y + p ∈ S k} ∧
        T (k + 1) = {y | 2 * y + q ∈ T k}) ∧
      (∀ k, ∀ C N, ∃ v, N ≤ v ∧ C ≤
        ((Finset.range (v + 1)).filter
          (fun x => x ∈ S k ∧ (v - x) ∈ T k)).card) ∧
      ((∀ k, ∃ Y ε, ∀ a ∈ S k, Y < a → a % 2 = ε) →
        ∃ ε' α : ℕ → ℕ, α 0 = 0 ∧
          (∀ k, ε' k < 2 ∧ α (k + 1) = α k + 2 ^ k * ε' k) ∧
          (∀ k, S k = T k) ∧
          (∀ k, S k = {x : ℕ | α k + 2 ^ k * x ∈ A})) := by
  obtain ⟨S, T, hS0, hT0, hstep, hblow⟩ :=
    omega_nested_representation h0 hcov hfail
  refine ⟨S, T, hS0, hT0, hstep, hblow, ?_⟩
  intro hsat
  choose Yf εf hparf using hsat
  have hmain : ∀ k, S k = T k ∧ εf k < 2 ∧
      S (k + 1) = {x : ℕ | εf k + 2 * x ∈ S k} ∧
      T (k + 1) = {x : ℕ | εf k + 2 * x ∈ S k} := by
    intro k
    induction k with
    | zero =>
      have heq : S 0 = T 0 := by rw [hS0, hT0]
      obtain ⟨p, q, hp, hq, hS1, hT1⟩ := hstep 0
      rw [← heq] at hT1
      have hres := saturated_iteration_step (hparf 0) hp hq
        hS1 hT1 (hblow 1)
      exact ⟨heq, by omega, hres.2.2.1, hres.2.2.2⟩
    | succ k ih =>
      obtain ⟨ihEq, ihε, ihS, ihT⟩ := ih
      have heq1 : S (k + 1) = T (k + 1) := by rw [ihS, ihT]
      obtain ⟨p, q, hp, hq, hS2, hT2⟩ := hstep (k + 1)
      rw [← heq1] at hT2
      have hres := saturated_iteration_step (hparf (k + 1)) hp hq
        hS2 hT2 (hblow (k + 2))
      exact ⟨heq1, by omega, hres.2.2.1, hres.2.2.2⟩
  set α : ℕ → ℕ := fun k =>
    Nat.rec 0 (fun k' acc => acc + 2 ^ k' * εf k') k with hα
  have hα0 : α 0 = 0 := rfl
  have hαS : ∀ k, α (k + 1) = α k + 2 ^ k * εf k :=
    fun _ => rfl
  have hlift : ∀ k x, x ∈ S k ↔ α k + 2 ^ k * x ∈ A := by
    intro k
    induction k with
    | zero =>
      intro x
      have he : α 0 + 2 ^ 0 * x = x := by
        rw [hα0]
        simp
      rw [he, hS0]
    | succ k ih =>
      intro x
      rw [(hmain k).2.2.1, Set.mem_setOf_eq,
        ih (εf k + 2 * x)]
      have he : α k + 2 ^ k * (εf k + 2 * x) =
          α (k + 1) + 2 ^ (k + 1) * x := by
        rw [hαS k, pow_succ]
        ring
      rw [he]
  refine ⟨εf, α, hα0,
    fun k => ⟨(hmain k).2.1, hαS k⟩,
    fun k => (hmain k).1, fun k => ?_⟩
  ext x
  simp only [Set.mem_setOf_eq]
  exact hlift k x

open Classical in

theorem iteration_mixing_fork {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ S T : ℕ → Set ℕ, S 0 = A ∧ T 0 = A ∧
      (∀ k, ∃ p q, p < 2 ∧ q < 2 ∧
        S (k + 1) = {y | 2 * y + p ∈ S k} ∧
        T (k + 1) = {y | 2 * y + q ∈ T k}) ∧
      (∀ k, ∀ C N, ∃ v, N ≤ v ∧ C ≤
        ((Finset.range (v + 1)).filter
          (fun x => x ∈ S k ∧ (v - x) ∈ T k)).card) ∧
      ((∃ ε' α : ℕ → ℕ, α 0 = 0 ∧
          (∀ k, ε' k < 2 ∧ α (k + 1) = α k + 2 ^ k * ε' k) ∧
          (∀ k, S k = T k) ∧
          (∀ k, S k = {x : ℕ | α k + 2 ^ k * x ∈ A})) ∨
        (∃ m c, S m = T m ∧
          S m = {x : ℕ | c + 2 ^ m * x ∈ A} ∧
          (∀ N, ∃ a, N ≤ a ∧ a ∈ S m ∧ a % 2 = 0) ∧
          (∀ N, ∃ a, N ≤ a ∧ a ∈ S m ∧ a % 2 = 1))) := by
  obtain ⟨S, T, hS0, hT0, hstep, hblow, hdet⟩ :=
    saturated_iteration_determined h0 hcov hfail
  refine ⟨S, T, hS0, hT0, hstep, hblow, ?_⟩
  by_cases hsat : ∀ k, ∃ Y ε, ∀ a ∈ S k, Y < a → a % 2 = ε
  · exact Or.inl (hdet hsat)
  · right
    have hP : ∃ k, ¬∃ Y ε, ∀ a ∈ S k, Y < a → a % 2 = ε :=
      not_forall.mp hsat
    set m := Nat.find hP with hm
    have hPm : ¬∃ Y ε, ∀ a ∈ S m, Y < a → a % 2 = ε :=
      Nat.find_spec hP
    have htot : ∀ j, ∃ Y ε, j < m →
        ∀ a ∈ S j, Y < a → a % 2 = ε := by
      intro j
      by_cases hj : j < m
      · obtain ⟨Y, ε, h⟩ := not_not.mp (Nat.find_min hP hj)
        exact ⟨Y, ε, fun _ => h⟩
      · exact ⟨0, 0, fun h => absurd h hj⟩
    choose Yf εf hf using htot
    set α : ℕ → ℕ := fun k =>
      Nat.rec 0 (fun k' acc => acc + 2 ^ k' * εf k') k with hα
    have hα0 : α 0 = 0 := rfl
    have hαS : ∀ k, α (k + 1) = α k + 2 ^ k * εf k :=
      fun _ => rfl
    have hchain : ∀ j, j ≤ m → S j = T j ∧
        S j = {x : ℕ | α j + 2 ^ j * x ∈ A} := by
      intro j
      induction j with
      | zero =>
        intro _
        refine ⟨by rw [hS0, hT0], ?_⟩
        rw [hS0]
        ext z
        simp only [Set.mem_setOf_eq]
        have he : α 0 + 2 ^ 0 * z = z := by
          rw [hα0]
          simp
        rw [he]
      | succ j ih =>
        intro hjm
        obtain ⟨heqj, hcylj⟩ := ih (by omega)
        obtain ⟨p, q, hp, hq, hS1, hT1⟩ := hstep j
        rw [← heqj] at hT1
        have hres := saturated_iteration_step
          (hf j (by omega)) hp hq hS1 hT1 (hblow (j + 1))
        refine ⟨by rw [hres.2.2.1, hres.2.2.2], ?_⟩
        rw [hres.2.2.1]
        ext z
        simp only [Set.mem_setOf_eq]
        rw [hcylj]
        simp only [Set.mem_setOf_eq]
        have he : α j + 2 ^ j * (εf j + 2 * z) =
            α (j + 1) + 2 ^ (j + 1) * z := by
          rw [hαS j, pow_succ]
          ring
        rw [he]
    obtain ⟨heqm, hcylm⟩ := hchain m le_rfl
    refine ⟨m, α m, heqm, hcylm, ?_, ?_⟩
    · intro N
      by_contra hcon
      apply hPm
      refine ⟨N, 1, fun a ha hNa => ?_⟩
      by_contra hne
      exact hcon ⟨a, by omega, ha, by omega⟩
    · intro N
      by_contra hcon
      apply hPm
      refine ⟨N, 0, fun a ha hNa => ?_⟩
      by_contra hne
      exact hcon ⟨a, by omega, ha, by omega⟩

open Classical in

theorem two_adic_convergence_contradicts_covering {A : Set ℕ}
    {N₀ : ℕ} (hcov : PairCovers A N₀)
    (hconv : ∀ k, ∃ Y ρ, ρ < 2 ^ k ∧ ∀ a ∈ A, Y < a →
      ∃ z, a = ρ + 2 ^ k * z) : False := by
  obtain ⟨Y1, ρ1, hρ1, hpar⟩ := hconv 1
  set K := Y1 + 3 with hK
  obtain ⟨YK, ρK, hρK, hcK⟩ := hconv K
  set H := (Finset.range (Y1 + 1)).filter (fun a => a ∈ A)
    with hH
  set F := H.image (fun a => (a + ρK) % 2 ^ K) with hF
  set bpar := (ρ1 + ρK + 1) % 2 with hbpar
  set Cand := (Finset.range (Y1 + 2)).image
    (fun t => 2 * t + bpar) with hCand
  have hCandCard : Cand.card = Y1 + 2 := by
    rw [hCand, Finset.card_image_of_injOn
      (fun x _ y _ hxy => by omega)]
    exact Finset.card_range _
  have hFcard : F.card ≤ Y1 + 1 := by
    refine le_trans Finset.card_image_le ?_
    rw [hH]
    refine le_trans (Finset.card_filter_le _ _) ?_
    rw [Finset.card_range]
  have hex : (Cand \ F).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : Cand ⊆ F := by
      intro x hx
      by_contra hxF
      have hmem : x ∈ Cand \ F := Finset.mem_sdiff.2 ⟨hx, hxF⟩
      rw [hemp] at hmem
      exact absurd hmem (Finset.notMem_empty x)
    have := Finset.card_le_card hsub
    omega
  obtain ⟨r, hr⟩ := hex
  rw [Finset.mem_sdiff] at hr
  obtain ⟨hrC, hrF⟩ := hr
  rw [hCand, Finset.mem_image] at hrC
  obtain ⟨t, htr, hrt⟩ := hrC
  rw [Finset.mem_range] at htr
  have hpow2 : Y1 + 2 < 2 ^ (Y1 + 2) :=
    Nat.lt_pow_self (by omega)
  have hKsplit : 2 ^ K = 2 * 2 ^ (Y1 + 2) := by
    rw [hK, pow_succ]
    ring
  have hbp2 : bpar < 2 := by
    rw [hbpar]
    omega
  have hrK : r < 2 ^ K := by omega
  set M := N₀ + Y1 + YK + ρK + 5 with hM
  set n := r + 2 ^ K * M with hn
  have hPK : 0 < 2 ^ K := pow_pos (by omega) K
  have hMle : M ≤ 2 ^ K * M := Nat.le_mul_of_pos_left M hPK
  have h2K : 2 ≤ 2 ^ K := by omega
  have h2M : 2 * M ≤ 2 ^ K * M := Nat.mul_le_mul_right M h2K
  obtain ⟨u, huA, v, hvA, huv⟩ := hcov n (by omega)
  have key : ∀ u v, u ∈ A → v ∈ A → u + v = n → u ≤ v →
      False := by
    intro u v huA hvA huv hule
    have hvM : M ≤ v := by omega
    obtain ⟨zv, hzv⟩ := hcK v hvA (by omega)
    rcases Nat.lt_or_ge Y1 u with hu1 | hu1
    · obtain ⟨zu, hzu⟩ := hpar u huA hu1
      have h21 : (2:ℕ) ^ 1 = 2 := by norm_num
      rw [h21] at hzu
      have hzv2 : 2 ^ K * zv = 2 * (2 ^ (Y1 + 2) * zv) := by
        rw [hKsplit]
        ring
      have hnM2 : 2 ^ K * M = 2 * (2 ^ (Y1 + 2) * M) := by
        rw [hKsplit]
        ring
      omega
    · have hru : (u + ρK) % 2 ^ K = r := by
        have h1 : u + v = (u + ρK) + 2 ^ K * zv := by omega
        have h2 : (u + ρK + 2 ^ K * zv) % 2 ^ K =
            (u + ρK) % 2 ^ K := Nat.add_mul_mod_self_left _ _ _
        have h3 : (r + 2 ^ K * M) % 2 ^ K = r % 2 ^ K :=
          Nat.add_mul_mod_self_left _ _ _
        have h4 : r % 2 ^ K = r := Nat.mod_eq_of_lt hrK
        rw [hn] at huv
        rw [← huv] at h3
        rw [h1] at h3
        rw [h2] at h3
        rw [h4] at h3
        exact h3
      apply hrF
      rw [hF, Finset.mem_image]
      refine ⟨u, ?_, hru⟩
      rw [hH, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, huA⟩
  rcases Nat.le_total u v with h | h
  · exact key u v huA hvA huv h
  · exact key v u hvA huA (by omega) h

open Classical in

theorem iteration_forces_mixing {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ S T : ℕ → Set ℕ, S 0 = A ∧ T 0 = A ∧
      (∀ k, ∃ p q, p < 2 ∧ q < 2 ∧
        S (k + 1) = {y | 2 * y + p ∈ S k} ∧
        T (k + 1) = {y | 2 * y + q ∈ T k}) ∧
      (∀ k, ∀ C N, ∃ v, N ≤ v ∧ C ≤
        ((Finset.range (v + 1)).filter
          (fun x => x ∈ S k ∧ (v - x) ∈ T k)).card) ∧
      ∃ m c, S m = T m ∧
        S m = {x : ℕ | c + 2 ^ m * x ∈ A} ∧
        (∀ N, ∃ a, N ≤ a ∧ a ∈ S m ∧ a % 2 = 0) ∧
        (∀ N, ∃ a, N ≤ a ∧ a ∈ S m ∧ a % 2 = 1) := by
  obtain ⟨S, T, hS0, hT0, hstep, hblow, hdet⟩ :=
    saturated_iteration_determined h0 hcov hfail
  refine ⟨S, T, hS0, hT0, hstep, hblow, ?_⟩
  by_cases hsat : ∀ k, ∃ Y ε, ∀ a ∈ S k, Y < a → a % 2 = ε
  · exfalso
    obtain ⟨ε', α, hα0, hdig, heq, hcyl⟩ := hdet hsat
    choose Ys εs hs using hsat
    have hαlt : ∀ k, α k < 2 ^ k := by
      intro k
      induction k with
      | zero =>
        rw [hα0]
        norm_num
      | succ k ih =>
        have hd1 := (hdig k).1
        have hd2 := (hdig k).2
        have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by
          rw [pow_succ]
          ring
        have hle : 2 ^ k * ε' k ≤ 2 ^ k * 1 :=
          Nat.mul_le_mul_left _ (by omega)
        omega
    have hdigpar : ∀ k, ε' k = εs k := by
      intro k
      have hinf : (S (k + 1)).Infinite :=
        (cross_amplification_infinite (hblow (k + 1))).1
      obtain ⟨x, hxS, hxgt⟩ := hinf.exists_gt (Ys k)
      have hxA : α (k + 1) + 2 ^ (k + 1) * x ∈ A := by
        rw [hcyl (k + 1)] at hxS
        exact hxS
      have halg : α k + 2 ^ k * (ε' k + 2 * x) =
          α (k + 1) + 2 ^ (k + 1) * x := by
        rw [(hdig k).2, pow_succ]
        ring
      have hz'S : (ε' k + 2 * x) ∈ S k := by
        rw [hcyl k]
        show α k + 2 ^ k * (ε' k + 2 * x) ∈ A
        rw [halg]
        exact hxA
      have hpar' := hs k (ε' k + 2 * x) hz'S (by omega)
      have hd1 := (hdig k).1
      omega
    have hconc : ∀ k, ∃ Y, ∀ a ∈ A, Y < a →
        ∃ z, a = α k + 2 ^ k * z ∧ z ∈ S k := by
      intro k
      induction k with
      | zero =>
        refine ⟨0, fun a haA _ => ⟨a, ?_, ?_⟩⟩
        · rw [hα0]
          simp
        · rw [hS0]
          exact haA
      | succ k ih =>
        obtain ⟨Yk', hYk'⟩ := ih
        refine ⟨max Yk' (α k + 2 ^ k * (Ys k + 1)),
          fun a haA ha => ?_⟩
        have ha1 : Yk' < a :=
          lt_of_le_of_lt (le_max_left _ _) ha
        have ha2 : α k + 2 ^ k * (Ys k + 1) < a :=
          lt_of_le_of_lt (le_max_right _ _) ha
        obtain ⟨z, hzeq, hzS⟩ := hYk' a haA ha1
        have hzY : Ys k < z := by
          rcases Nat.lt_or_ge (Ys k) z with h | h
          · exact h
          · exfalso
            have h3 : 2 ^ k * z ≤ 2 ^ k * (Ys k + 1) :=
              Nat.mul_le_mul_left _ (by omega)
            omega
        have hzp := hs k z hzS hzY
        obtain ⟨w, hw⟩ : ∃ w, z = εs k + 2 * w :=
          ⟨z / 2, by omega⟩
        have h4 : 2 ^ k * z = 2 ^ k * (εs k + 2 * w) := by
          rw [hw]
        have halg2 : α (k + 1) + 2 ^ (k + 1) * w =
            α k + 2 ^ k * (εs k + 2 * w) := by
          rw [(hdig k).2, hdigpar k, pow_succ]
          ring
        have h5 : α (k + 1) + 2 ^ (k + 1) * w = a := by
          omega
        refine ⟨w, by omega, ?_⟩
        rw [hcyl (k + 1)]
        show α (k + 1) + 2 ^ (k + 1) * w ∈ A
        rw [h5]
        exact haA
    apply two_adic_convergence_contradicts_covering hcov
    intro k
    obtain ⟨Y, hY⟩ := hconc k
    refine ⟨Y, α k, hαlt k, fun a ha hYa => ?_⟩
    obtain ⟨z, h1, _⟩ := hY a ha hYa
    exact ⟨z, h1⟩
  · have hP : ∃ k, ¬∃ Y ε, ∀ a ∈ S k, Y < a → a % 2 = ε :=
      not_forall.mp hsat
    set m := Nat.find hP with hm
    have hPm : ¬∃ Y ε, ∀ a ∈ S m, Y < a → a % 2 = ε :=
      Nat.find_spec hP
    have htot : ∀ j, ∃ Y ε, j < m →
        ∀ a ∈ S j, Y < a → a % 2 = ε := by
      intro j
      by_cases hj : j < m
      · obtain ⟨Y, ε, h⟩ := not_not.mp (Nat.find_min hP hj)
        exact ⟨Y, ε, fun _ => h⟩
      · exact ⟨0, 0, fun h => absurd h hj⟩
    choose Yf εf hf using htot
    set α : ℕ → ℕ := fun k =>
      Nat.rec 0 (fun k' acc => acc + 2 ^ k' * εf k') k with hα
    have hα0 : α 0 = 0 := rfl
    have hαS : ∀ k, α (k + 1) = α k + 2 ^ k * εf k :=
      fun _ => rfl
    have hchain : ∀ j, j ≤ m → S j = T j ∧
        S j = {x : ℕ | α j + 2 ^ j * x ∈ A} := by
      intro j
      induction j with
      | zero =>
        intro _
        refine ⟨by rw [hS0, hT0], ?_⟩
        rw [hS0]
        ext z
        simp only [Set.mem_setOf_eq]
        have he : α 0 + 2 ^ 0 * z = z := by
          rw [hα0]
          simp
        rw [he]
      | succ j ih =>
        intro hjm
        obtain ⟨heqj, hcylj⟩ := ih (by omega)
        obtain ⟨p, q, hp, hq, hS1, hT1⟩ := hstep j
        rw [← heqj] at hT1
        have hres := saturated_iteration_step
          (hf j (by omega)) hp hq hS1 hT1 (hblow (j + 1))
        refine ⟨by rw [hres.2.2.1, hres.2.2.2], ?_⟩
        rw [hres.2.2.1]
        ext z
        simp only [Set.mem_setOf_eq]
        rw [hcylj]
        simp only [Set.mem_setOf_eq]
        have he : α j + 2 ^ j * (εf j + 2 * z) =
            α (j + 1) + 2 ^ (j + 1) * z := by
          rw [hαS j, pow_succ]
          ring
        rw [he]
    obtain ⟨heqm, hcylm⟩ := hchain m le_rfl
    refine ⟨m, α m, heqm, hcylm, ?_, ?_⟩
    · intro N
      by_contra hcon
      apply hPm
      refine ⟨N, 1, fun a ha hNa => ?_⟩
      by_contra hne
      exact hcon ⟨a, by omega, ha, by omega⟩
    · intro N
      by_contra hcon
      apply hPm
      refine ⟨N, 0, fun a ha hNa => ?_⟩
      by_contra hne
      exact hcon ⟨a, by omega, ha, by omega⟩

open Classical in

theorem mixing_model_complete {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ S T : ℕ → Set ℕ, S 0 = A ∧ T 0 = A ∧
      (∀ k, ∃ p q, p < 2 ∧ q < 2 ∧
        S (k + 1) = {y | 2 * y + p ∈ S k} ∧
        T (k + 1) = {y | 2 * y + q ∈ T k}) ∧
      (∀ k, ∀ C N, ∃ v, N ≤ v ∧ C ≤
        ((Finset.range (v + 1)).filter
          (fun x => x ∈ S k ∧ (v - x) ∈ T k)).card) ∧
      ∃ m c, S m = T m ∧
        S m = {x : ℕ | c + 2 ^ m * x ∈ A} ∧
        (∀ N, ∃ a, N ≤ a ∧ a ∈ S m ∧ a % 2 = 0) ∧
        (∀ N, ∃ a, N ≤ a ∧ a ∈ S m ∧ a % 2 = 1) ∧
        (∃ N', PairCovers (S m) N') ∧
        (S m).Infinite := by
  obtain ⟨S, T, hS0, hT0, hstep, hblow, hdet⟩ :=
    saturated_iteration_determined h0 hcov hfail
  refine ⟨S, T, hS0, hT0, hstep, hblow, ?_⟩
  by_cases hsat : ∀ k, ∃ Y ε, ∀ a ∈ S k, Y < a → a % 2 = ε
  · exfalso
    obtain ⟨ε', α, hα0, hdig, heq, hcyl⟩ := hdet hsat
    choose Ys εs hs using hsat
    have hαlt : ∀ k, α k < 2 ^ k := by
      intro k
      induction k with
      | zero =>
        rw [hα0]
        norm_num
      | succ k ih =>
        have hd1 := (hdig k).1
        have hd2 := (hdig k).2
        have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by
          rw [pow_succ]
          ring
        have hle : 2 ^ k * ε' k ≤ 2 ^ k * 1 :=
          Nat.mul_le_mul_left _ (by omega)
        omega
    have hdigpar : ∀ k, ε' k = εs k := by
      intro k
      have hinf : (S (k + 1)).Infinite :=
        (cross_amplification_infinite (hblow (k + 1))).1
      obtain ⟨x, hxS, hxgt⟩ := hinf.exists_gt (Ys k)
      have hxA : α (k + 1) + 2 ^ (k + 1) * x ∈ A := by
        rw [hcyl (k + 1)] at hxS
        exact hxS
      have halg : α k + 2 ^ k * (ε' k + 2 * x) =
          α (k + 1) + 2 ^ (k + 1) * x := by
        rw [(hdig k).2, pow_succ]
        ring
      have hz'S : (ε' k + 2 * x) ∈ S k := by
        rw [hcyl k]
        show α k + 2 ^ k * (ε' k + 2 * x) ∈ A
        rw [halg]
        exact hxA
      have hpar' := hs k (ε' k + 2 * x) hz'S (by omega)
      have hd1 := (hdig k).1
      omega
    have hconc : ∀ k, ∃ Y, ∀ a ∈ A, Y < a →
        ∃ z, a = α k + 2 ^ k * z ∧ z ∈ S k := by
      intro k
      induction k with
      | zero =>
        refine ⟨0, fun a haA _ => ⟨a, ?_, ?_⟩⟩
        · rw [hα0]
          simp
        · rw [hS0]
          exact haA
      | succ k ih =>
        obtain ⟨Yk', hYk'⟩ := ih
        refine ⟨max Yk' (α k + 2 ^ k * (Ys k + 1)),
          fun a haA ha => ?_⟩
        have ha1 : Yk' < a :=
          lt_of_le_of_lt (le_max_left _ _) ha
        have ha2 : α k + 2 ^ k * (Ys k + 1) < a :=
          lt_of_le_of_lt (le_max_right _ _) ha
        obtain ⟨z, hzeq, hzS⟩ := hYk' a haA ha1
        have hzY : Ys k < z := by
          rcases Nat.lt_or_ge (Ys k) z with h | h
          · exact h
          · exfalso
            have h3 : 2 ^ k * z ≤ 2 ^ k * (Ys k + 1) :=
              Nat.mul_le_mul_left _ (by omega)
            omega
        have hzp := hs k z hzS hzY
        obtain ⟨w, hw⟩ : ∃ w, z = εs k + 2 * w :=
          ⟨z / 2, by omega⟩
        have h4 : 2 ^ k * z = 2 ^ k * (εs k + 2 * w) := by
          rw [hw]
        have halg2 : α (k + 1) + 2 ^ (k + 1) * w =
            α k + 2 ^ k * (εs k + 2 * w) := by
          rw [(hdig k).2, hdigpar k, pow_succ]
          ring
        have h5 : α (k + 1) + 2 ^ (k + 1) * w = a := by
          omega
        refine ⟨w, by omega, ?_⟩
        rw [hcyl (k + 1)]
        show α (k + 1) + 2 ^ (k + 1) * w ∈ A
        rw [h5]
        exact haA
    apply two_adic_convergence_contradicts_covering hcov
    intro k
    obtain ⟨Y, hY⟩ := hconc k
    refine ⟨Y, α k, hαlt k, fun a ha hYa => ?_⟩
    obtain ⟨z, h1, _⟩ := hY a ha hYa
    exact ⟨z, h1⟩
  · have hP : ∃ k, ¬∃ Y ε, ∀ a ∈ S k, Y < a → a % 2 = ε :=
      not_forall.mp hsat
    set m := Nat.find hP with hm
    have hPm : ¬∃ Y ε, ∀ a ∈ S m, Y < a → a % 2 = ε :=
      Nat.find_spec hP
    have htot : ∀ j, ∃ Y ε, j < m →
        ∀ a ∈ S j, Y < a → a % 2 = ε := by
      intro j
      by_cases hj : j < m
      · obtain ⟨Y, ε, h⟩ := not_not.mp (Nat.find_min hP hj)
        exact ⟨Y, ε, fun _ => h⟩
      · exact ⟨0, 0, fun h => absurd h hj⟩
    choose Yf εf hf using htot
    set α : ℕ → ℕ := fun k =>
      Nat.rec 0 (fun k' acc => acc + 2 ^ k' * εf k') k with hα
    have hα0 : α 0 = 0 := rfl
    have hαS : ∀ k, α (k + 1) = α k + 2 ^ k * εf k :=
      fun _ => rfl
    have hchain : ∀ j, j ≤ m → S j = T j ∧
        S j = {x : ℕ | α j + 2 ^ j * x ∈ A} := by
      intro j
      induction j with
      | zero =>
        intro _
        refine ⟨by rw [hS0, hT0], ?_⟩
        rw [hS0]
        ext z
        simp only [Set.mem_setOf_eq]
        have he : α 0 + 2 ^ 0 * z = z := by
          rw [hα0]
          simp
        rw [he]
      | succ j ih =>
        intro hjm
        obtain ⟨heqj, hcylj⟩ := ih (by omega)
        obtain ⟨p, q, hp, hq, hS1, hT1⟩ := hstep j
        rw [← heqj] at hT1
        have hres := saturated_iteration_step
          (hf j (by omega)) hp hq hS1 hT1 (hblow (j + 1))
        refine ⟨by rw [hres.2.2.1, hres.2.2.2], ?_⟩
        rw [hres.2.2.1]
        ext z
        simp only [Set.mem_setOf_eq]
        rw [hcylj]
        simp only [Set.mem_setOf_eq]
        have he : α j + 2 ^ j * (εf j + 2 * z) =
            α (j + 1) + 2 ^ (j + 1) * z := by
          rw [hαS j, pow_succ]
          ring
        rw [he]
    have hcovchain : ∀ j, j ≤ m →
        ∃ N', PairCovers (S j) N' := by
      intro j
      induction j with
      | zero =>
        intro _
        refine ⟨N₀, ?_⟩
        rw [hS0]
        exact hcov
      | succ j ih =>
        intro hjm
        obtain ⟨Nj, hNj⟩ := ih (by omega)
        obtain ⟨heqj, _⟩ := hchain j (by omega)
        obtain ⟨p, q, hp, hq, hS1, hT1⟩ := hstep j
        rw [← heqj] at hT1
        have hres := saturated_iteration_step
          (hf j (by omega)) hp hq hS1 hT1 (hblow (j + 1))
        have hεlt : εf j < 2 := by
          have h1 := hres.1
          omega
        have hcovj1 := half_model_covers hεlt hNj
          (hf j (by omega))
        rw [hres.2.2.1]
        exact ⟨Nj + 2 * Yf j + 2, hcovj1⟩
    obtain ⟨heqm, hcylm⟩ := hchain m le_rfl
    refine ⟨m, α m, heqm, hcylm, ?_, ?_,
      hcovchain m le_rfl,
      (cross_amplification_infinite (hblow m)).1⟩
    · intro N
      by_contra hcon
      apply hPm
      refine ⟨N, 1, fun a ha hNa => ?_⟩
      by_contra hne
      exact hcon ⟨a, by omega, ha, by omega⟩
    · intro N
      by_contra hcon
      apply hPm
      refine ⟨N, 0, fun a ha hNa => ?_⟩
      by_contra hne
      exact hcon ⟨a, by omega, ha, by omega⟩

theorem mixing_deletion_destructions_root {A : Set ℕ}
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {W : Set ℕ} {m c : ℕ}
    (hW : W = {x : ℕ | c + 2 ^ m * x ∈ A}) :
    ∀ B' ⊆ W, B'.Infinite →
      ¬IsExactTupleAsymptoticBasis
        (A \ ((fun x => c + 2 ^ m * x) '' B')) 3 := by
  intro B' hB'W hB'inf
  refine hfail _ ?_ ?_
  · rintro a ⟨x, hxB', hxa⟩
    have hxW := hB'W hxB'
    rw [hW] at hxW
    rw [← hxa]
    exact hxW
  · refine hB'inf.image ?_
    intro a _ b _ hab
    have h : c + 2 ^ m * a = c + 2 ^ m * b := hab
    have hp : 0 < 2 ^ m := pow_pos (by omega) m
    exact Nat.eq_of_mul_eq_mul_left hp (by omega)

open Classical in

theorem mixing_model_interface {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ S T : ℕ → Set ℕ, S 0 = A ∧ T 0 = A ∧
      (∀ k, ∃ p q, p < 2 ∧ q < 2 ∧
        S (k + 1) = {y | 2 * y + p ∈ S k} ∧
        T (k + 1) = {y | 2 * y + q ∈ T k}) ∧
      (∀ k, ∀ C N, ∃ v, N ≤ v ∧ C ≤
        ((Finset.range (v + 1)).filter
          (fun x => x ∈ S k ∧ (v - x) ∈ T k)).card) ∧
      ∃ m c, S m = T m ∧
        S m = {x : ℕ | c + 2 ^ m * x ∈ A} ∧
        (∀ N, ∃ a, N ≤ a ∧ a ∈ S m ∧ a % 2 = 0) ∧
        (∀ N, ∃ a, N ≤ a ∧ a ∈ S m ∧ a % 2 = 1) ∧
        (∃ N', PairCovers (S m) N') ∧
        (S m).Infinite ∧
        (∀ B' ⊆ S m, B'.Infinite →
          ¬IsExactTupleAsymptoticBasis
            (A \ ((fun x => c + 2 ^ m * x) '' B')) 3) := by
  obtain ⟨S, T, hS0, hT0, hstep, hblow, m, c, heqm, hcylm,
    hmix0, hmix1, hcovm, hinfm⟩ :=
    mixing_model_complete h0 hcov hfail
  exact ⟨S, T, hS0, hT0, hstep, hblow, m, c, heqm, hcylm,
    hmix0, hmix1, hcovm, hinfm,
    mixing_deletion_destructions_root hfail hcylm⟩

open Classical in

theorem wealthy_target_survives {A D : Set ℕ} {v : ℕ}
    (h0A : 0 ∈ A) (h0D : 0 ∉ D)
    (hwealth : 2 * ((Finset.range (v + 1)).filter
        (fun x => x ∈ D)).card + 2 <
      ((Finset.range (v + 1)).filter
        (fun x => x ∈ A ∧ (v - x) ∈ A)).card) :
    ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x ∉ D ∧ y ∉ D ∧ z ∉ D ∧
      x + y + z = v := by
  set Full := (Finset.range (v + 1)).filter
    (fun x => x ∈ A ∧ (v - x) ∈ A) with hFull
  set DF := (Finset.range (v + 1)).filter
    (fun x => x ∈ D) with hDF
  set Bad := Full.filter
    (fun x => x ∈ D ∨ (v - x) ∈ D) with hBad
  have hBadsub : Bad ⊆ DF ∪ (Finset.range (v + 1)).filter
      (fun x => (v - x) ∈ D) := by
    intro x hx
    rw [hBad, Finset.mem_filter] at hx
    obtain ⟨hxF, hxor⟩ := hx
    rw [hFull, Finset.mem_filter] at hxF
    rcases hxor with h | h
    · exact Finset.mem_union_left _
        (Finset.mem_filter.2 ⟨hxF.1, h⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.2 ⟨hxF.1, h⟩)
  have hrefl : ((Finset.range (v + 1)).filter
      (fun x => (v - x) ∈ D)).card ≤ DF.card := by
    apply Finset.card_le_card_of_injOn (fun x => v - x)
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range] at hx
      simp only [hDF, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range]
      exact ⟨by omega, hx.2⟩
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range] at ha hb
      have hab' : v - a = v - b := hab
      omega
  have hBadcard : Bad.card ≤ 2 * DF.card := by
    have h1 := Finset.card_le_card hBadsub
    have h2 := Finset.card_union_le DF
      ((Finset.range (v + 1)).filter (fun x => (v - x) ∈ D))
    omega
  have hex : (Full \ Bad).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : Full ⊆ Bad := by
      intro x hx
      by_contra hxB
      have hmem : x ∈ Full \ Bad :=
        Finset.mem_sdiff.2 ⟨hx, hxB⟩
      rw [hemp] at hmem
      exact absurd hmem (Finset.notMem_empty x)
    have := Finset.card_le_card hsub
    omega
  obtain ⟨x, hx⟩ := hex
  rw [Finset.mem_sdiff] at hx
  obtain ⟨hxF, hxB⟩ := hx
  have hxF' := hxF
  rw [hFull, Finset.mem_filter, Finset.mem_range] at hxF'
  obtain ⟨hxv, hxA, hvxA⟩ := hxF'
  have hxnotor : ¬(x ∈ D ∨ (v - x) ∈ D) := by
    intro h
    exact hxB (Finset.mem_filter.2 ⟨hxF, h⟩)
  refine ⟨x, hxA, v - x, hvxA, 0, h0A, ?_, ?_, h0D,
    by omega⟩
  · intro h
    exact hxnotor (Or.inl h)
  · intro h
    exact hxnotor (Or.inr h)

open Classical in

theorem cylinder_failure_residue_law {A D : Set ℕ}
    {m c n : ℕ}
    (h0A : 0 ∈ A) (h0D : 0 ∉ D)
    (hDcyl : ∀ d ∈ D, d % 2 ^ m = c % 2 ^ m)
    (hfailn : ∀ v : Fin 3 → ℕ, (∀ i, v i ∈ A \ D) →
      ∑ i, v i ≠ n) :
    ∀ x ∈ A, ∀ y ∈ A, x + y = n →
      x % 2 ^ m = c % 2 ^ m ∨ y % 2 ^ m = c % 2 ^ m := by
  intro x hx y hy hxy
  by_contra hcon
  have hxc : x % 2 ^ m ≠ c % 2 ^ m :=
    fun h => hcon (Or.inl h)
  have hyc : y % 2 ^ m ≠ c % 2 ^ m :=
    fun h => hcon (Or.inr h)
  have hxD : x ∉ D := fun h => hxc (hDcyl x h)
  have hyD : y ∉ D := fun h => hyc (hDcyl y h)
  have hmem : ∀ i, (![x, y, 0] : Fin 3 → ℕ) i ∈ A \ D := by
    intro i
    match i with
    | 0 => exact ⟨hx, hxD⟩
    | 1 => exact ⟨hy, hyD⟩
    | 2 => exact ⟨h0A, h0D⟩
  have hsum0 : x + y + 0 = n := by omega
  exact hfailn ![x, y, 0] hmem
    (by simpa [Fin.sum_univ_three] using hsum0)

open Classical in

theorem failing_target_poor {A D : Set ℕ} {n : ℕ}
    (h0A : 0 ∈ A) (h0D : 0 ∉ D)
    (hfailn : ∀ v : Fin 3 → ℕ, (∀ i, v i ∈ A \ D) →
      ∑ i, v i ≠ n) :
    ((Finset.range (n + 1)).filter
      (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤
    2 * ((Finset.range (n + 1)).filter
      (fun x => x ∈ D)).card + 2 := by
  by_contra hrich
  push Not at hrich
  obtain ⟨x, hx, y, hy, z, hz, hxD, hyD, hzD, hsum⟩ :=
    wealthy_target_survives h0A h0D hrich
  have hmem : ∀ i, (![x, y, z] : Fin 3 → ℕ) i ∈ A \ D := by
    intro i
    match i with
    | 0 => exact ⟨hx, hxD⟩
    | 1 => exact ⟨hy, hyD⟩
    | 2 => exact ⟨hz, hzD⟩
  exact hfailn ![x, y, z] hmem
    (by simpa [Fin.sum_univ_three] using hsum)

open Classical in

theorem mixing_failure_addresses {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ S T : ℕ → Set ℕ, S 0 = A ∧ T 0 = A ∧
      (∀ k, ∃ p q, p < 2 ∧ q < 2 ∧
        S (k + 1) = {y | 2 * y + p ∈ S k} ∧
        T (k + 1) = {y | 2 * y + q ∈ T k}) ∧
      (∀ k, ∀ C N, ∃ v, N ≤ v ∧ C ≤
        ((Finset.range (v + 1)).filter
          (fun x => x ∈ S k ∧ (v - x) ∈ T k)).card) ∧
      ∃ m c, S m = T m ∧
        S m = {x : ℕ | c + 2 ^ m * x ∈ A} ∧
        (∀ N, ∃ a, N ≤ a ∧ a ∈ S m ∧ a % 2 = 0) ∧
        (∀ N, ∃ a, N ≤ a ∧ a ∈ S m ∧ a % 2 = 1) ∧
        (∃ N', PairCovers (S m) N') ∧
        (S m).Infinite ∧
        ∀ B' ⊆ S m, 0 ∉ B' → B'.Infinite → ∀ N, ∃ n, N ≤ n ∧
          (∀ x ∈ A, ∀ y ∈ A, x + y = n →
            x % 2 ^ m = c % 2 ^ m ∨
            y % 2 ^ m = c % 2 ^ m) ∧
          ((Finset.range (n + 1)).filter
            (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤
          2 * ((Finset.range (n + 1)).filter
            (fun x => x ∈ ((fun x => c + 2 ^ m * x) ''
              B'))).card + 2 := by
  obtain ⟨S, T, hS0, hT0, hstep, hblow, m, c, heqm, hcylm,
    hmix0, hmix1, hcovm, hinfm, hwound⟩ :=
    mixing_model_interface h0 hcov hfail
  refine ⟨S, T, hS0, hT0, hstep, hblow, m, c, heqm, hcylm,
    hmix0, hmix1, hcovm, hinfm, ?_⟩
  intro B' hB'sub h0B' hB'inf N
  have hnot := hwound B' hB'sub hB'inf
  set D : Set ℕ := (fun x => c + 2 ^ m * x) '' B' with hD
  have h0D : 0 ∉ D := by
    rintro ⟨x, hxB', hx0⟩
    have hx0' : c + 2 ^ m * x = 0 := hx0
    have hp : 0 < 2 ^ m := pow_pos (by omega) m
    have hx : x = 0 := by
      rcases Nat.eq_zero_or_pos x with h | h
      · exact h
      · exfalso
        have h1 : 2 ^ m * 1 ≤ 2 ^ m * x :=
          Nat.mul_le_mul_left _ (by omega)
        omega
    rw [hx] at hxB'
    exact h0B' hxB'
  have hDcyl : ∀ d ∈ D, d % 2 ^ m = c % 2 ^ m := by
    rintro d ⟨x, _, hxd⟩
    rw [← hxd]
    exact Nat.add_mul_mod_self_left c (2 ^ m) x
  simp only [IsExactTupleAsymptoticBasis, not_exists,
    not_forall] at hnot
  obtain ⟨n, hn, hnrep⟩ := hnot N
  have hfailn : ∀ v : Fin 3 → ℕ, (∀ i, v i ∈ A \ D) →
      ∑ i, v i ≠ n := by
    intro v hv hs
    exact hnrep v ⟨hv, hs⟩
  exact ⟨n, hn,
    cylinder_failure_residue_law h0 h0D hDcyl hfailn,
    failing_target_poor h0 h0D hfailn⟩

open Classical in

theorem failing_target_in_sumset {A D : Set ℕ} {N₀ n : ℕ}
    (h0A : 0 ∈ A) (h0D : 0 ∉ D)
    (hcov : PairCovers A N₀) (hn : N₀ ≤ n)
    (hfailn : ∀ v : Fin 3 → ℕ, (∀ i, v i ∈ A \ D) →
      ∑ i, v i ≠ n) :
    ∃ d ∈ D, ∃ a ∈ A, d ∈ A ∧ d + a = n := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov n hn
  by_cases hxD : x ∈ D
  · exact ⟨x, hxD, y, hy, hx, hxy⟩
  · by_cases hyD : y ∈ D
    · exact ⟨y, hyD, x, hx, hy, by omega⟩
    · exfalso
      have hmem : ∀ i, (![x, y, 0] : Fin 3 → ℕ) i ∈ A \ D := by
        intro i
        match i with
        | 0 => exact ⟨hx, hxD⟩
        | 1 => exact ⟨hy, hyD⟩
        | 2 => exact ⟨h0A, h0D⟩
      have hsum0 : x + y + 0 = n := by omega
      exact hfailn ![x, y, 0] hmem
        (by simpa [Fin.sum_univ_three] using hsum0)

open Classical in

theorem three_deletion_exclusion {A D₁ D₂ D₃ : Set ℕ}
    {N₀ n : ℕ}
    (h0A : 0 ∈ A) (h01 : 0 ∉ D₁) (h02 : 0 ∉ D₂) (h03 : 0 ∉ D₃)
    (hd12 : ∀ x, x ∈ D₁ → x ∉ D₂)
    (hd13 : ∀ x, x ∈ D₁ → x ∉ D₃)
    (hd23 : ∀ x, x ∈ D₂ → x ∉ D₃)
    (hcov : PairCovers A N₀) (hn : N₀ ≤ n)
    (hf1 : ∀ v : Fin 3 → ℕ, (∀ i, v i ∈ A \ D₁) →
      ∑ i, v i ≠ n)
    (hf2 : ∀ v : Fin 3 → ℕ, (∀ i, v i ∈ A \ D₂) →
      ∑ i, v i ≠ n)
    (hf3 : ∀ v : Fin 3 → ℕ, (∀ i, v i ∈ A \ D₃) →
      ∑ i, v i ≠ n) :
    False := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov n hn
  have key : ∀ (D : Set ℕ), 0 ∉ D →
      (∀ v : Fin 3 → ℕ, (∀ i, v i ∈ A \ D) → ∑ i, v i ≠ n) →
      x ∈ D ∨ y ∈ D := by
    intro D h0D hfD
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · by_cases hyD : y ∈ D
      · exact Or.inr hyD
      · exfalso
        have hmem : ∀ i, (![x, y, 0] : Fin 3 → ℕ) i ∈
            A \ D := by
          intro i
          match i with
          | 0 => exact ⟨hx, hxD⟩
          | 1 => exact ⟨hy, hyD⟩
          | 2 => exact ⟨h0A, h0D⟩
        have hsum0 : x + y + 0 = n := by omega
        exact hfD ![x, y, 0] hmem
          (by simpa [Fin.sum_univ_three] using hsum0)
  rcases key D₁ h01 hf1 with h1 | h1 <;>
    rcases key D₂ h02 hf2 with h2 | h2 <;>
    rcases key D₃ h03 hf3 with h3 | h3
  · exact hd12 x h1 h2
  · exact hd12 x h1 h2
  · exact hd13 x h1 h3
  · exact hd23 y h2 h3
  · exact hd23 x h2 h3
  · exact hd13 y h1 h3
  · exact hd12 y h1 h2
  · exact hd12 y h1 h2

open Classical in

theorem overlap_bilinear_law {A D₁ D₂ : Set ℕ} {N₀ n : ℕ}
    (h0A : 0 ∈ A) (h01 : 0 ∉ D₁) (h02 : 0 ∉ D₂)
    (hd12 : ∀ x, x ∈ D₁ → x ∉ D₂)
    (hcov : PairCovers A N₀) (hn : N₀ ≤ n)
    (hf1 : ∀ v : Fin 3 → ℕ, (∀ i, v i ∈ A \ D₁) →
      ∑ i, v i ≠ n)
    (hf2 : ∀ v : Fin 3 → ℕ, (∀ i, v i ∈ A \ D₂) →
      ∑ i, v i ≠ n) :
    (∀ x ∈ A, ∀ y ∈ A, x + y = n →
      (x ∈ D₁ ∧ y ∈ D₂) ∨ (x ∈ D₂ ∧ y ∈ D₁)) ∧
    ∃ d₁ ∈ D₁, ∃ d₂ ∈ D₂, d₁ + d₂ = n := by
  have key : ∀ x ∈ A, ∀ y ∈ A, x + y = n →
      (x ∈ D₁ ∧ y ∈ D₂) ∨ (x ∈ D₂ ∧ y ∈ D₁) := by
    intro x hx y hy hxy
    have touch : ∀ (D : Set ℕ), 0 ∉ D →
        (∀ v : Fin 3 → ℕ, (∀ i, v i ∈ A \ D) →
          ∑ i, v i ≠ n) →
        x ∈ D ∨ y ∈ D := by
      intro D h0D hfD
      by_cases hxD : x ∈ D
      · exact Or.inl hxD
      · by_cases hyD : y ∈ D
        · exact Or.inr hyD
        · exfalso
          have hmem : ∀ i, (![x, y, 0] : Fin 3 → ℕ) i ∈
              A \ D := by
            intro i
            match i with
            | 0 => exact ⟨hx, hxD⟩
            | 1 => exact ⟨hy, hyD⟩
            | 2 => exact ⟨h0A, h0D⟩
          have hsum0 : x + y + 0 = n := by omega
          exact hfD ![x, y, 0] hmem
            (by simpa [Fin.sum_univ_three] using hsum0)
    rcases touch D₁ h01 hf1 with h1 | h1 <;>
      rcases touch D₂ h02 hf2 with h2 | h2
    · exact absurd h2 (hd12 x h1)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exact absurd h2 (hd12 y h1)
  refine ⟨key, ?_⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov n hn
  rcases key x hx y hy hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨x, h1, y, h2, hxy⟩
  · exact ⟨y, h2, x, h1, by omega⟩

open Classical in

theorem two_adic_width_law {A : Set ℕ} {N₀ j Y : ℕ}
    (hcov : PairCovers A N₀)
    (hY : ∀ a ∈ A, Y < a →
      {b | b ∈ A ∧ b % 2 ^ j = a % 2 ^ j}.Infinite) :
    2 ^ j ≤
      (((Finset.range (Y + 1)).filter (fun a => a ∈ A)).image
        (fun a => a % 2 ^ j)).card *
      ((Finset.range (2 ^ j)).filter (fun r =>
        {b | b ∈ A ∧ b % 2 ^ j = r}.Infinite)).card +
      ((Finset.range (2 ^ j)).filter (fun r =>
        {b | b ∈ A ∧ b % 2 ^ j = r}.Infinite)).card *
      ((Finset.range (2 ^ j)).filter (fun r =>
        {b | b ∈ A ∧ b % 2 ^ j = r}.Infinite)).card := by
  set HC := ((Finset.range (Y + 1)).filter
    (fun a => a ∈ A)).image (fun a => a % 2 ^ j) with hHC
  set WC := (Finset.range (2 ^ j)).filter (fun r =>
    {b | b ∈ A ∧ b % 2 ^ j = r}.Infinite) with hWC
  have hpj : 0 < 2 ^ j := pow_pos (by omega) j
  set f : ℕ × ℕ → ℕ := fun p => (p.1 + p.2) % 2 ^ j with hf
  have hsub : Finset.range (2 ^ j) ⊆
      ((HC ×ˢ WC).image f) ∪ ((WC ×ˢ WC).image f) := by
    intro r hr
    rw [Finset.mem_range] at hr
    set M := N₀ + 2 * Y + 4 with hM
    set n := r + 2 ^ j * M with hn
    have hMle : M ≤ 2 ^ j * M := Nat.le_mul_of_pos_left M hpj
    obtain ⟨u, hu, v, hv, huv⟩ := hcov n (by omega)
    have hkey : ∀ a b : ℕ, a ∈ A → b ∈ A → a + b = n →
        a ≤ b → r ∈ ((HC ×ˢ WC).image f) ∪
          ((WC ×ˢ WC).image f) := by
      intro a b haA hbA hab hle
      have hbY : Y < b := by omega
      have hbW : b % 2 ^ j ∈ WC := by
        rw [hWC, Finset.mem_filter, Finset.mem_range]
        exact ⟨Nat.mod_lt _ hpj, hY b hbA hbY⟩
      have hrmod : (a % 2 ^ j + b % 2 ^ j) % 2 ^ j = r := by
        rw [← Nat.add_mod, hab, hn]
        rw [Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt hr
      rcases Nat.lt_or_ge Y a with haY | haY
      · refine Finset.mem_union_right _ ?_
        rw [Finset.mem_image]
        refine ⟨(a % 2 ^ j, b % 2 ^ j), ?_, hrmod⟩
        rw [Finset.mem_product]
        refine ⟨?_, hbW⟩
        rw [hWC, Finset.mem_filter, Finset.mem_range]
        exact ⟨Nat.mod_lt _ hpj, hY a haA haY⟩
      · refine Finset.mem_union_left _ ?_
        rw [Finset.mem_image]
        refine ⟨(a % 2 ^ j, b % 2 ^ j), ?_, hrmod⟩
        rw [Finset.mem_product]
        refine ⟨?_, hbW⟩
        rw [hHC, Finset.mem_image]
        refine ⟨a, ?_, rfl⟩
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, haA⟩
    rcases Nat.le_total u v with h | h
    · exact hkey u v hu hv huv h
    · exact hkey v u hv hu (by omega) h
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_range] at h1
  have h2 := Finset.card_union_le ((HC ×ˢ WC).image f)
    ((WC ×ˢ WC).image f)
  have h3 : ((HC ×ˢ WC).image f).card ≤ HC.card * WC.card := by
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_product]
  have h4 : ((WC ×ˢ WC).image f).card ≤ WC.card * WC.card := by
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_product]
  omega

open Classical in

theorem same_class_overlap_pinned {A D₁ D₂ : Set ℕ}
    {N₀ j c n : ℕ}
    (h0A : 0 ∈ A) (h01 : 0 ∉ D₁) (h02 : 0 ∉ D₂)
    (hd12 : ∀ x, x ∈ D₁ → x ∉ D₂)
    (hc1 : ∀ d ∈ D₁, d % 2 ^ j = c % 2 ^ j)
    (hc2 : ∀ d ∈ D₂, d % 2 ^ j = c % 2 ^ j)
    (hcov : PairCovers A N₀) (hn : N₀ ≤ n)
    (hf1 : ∀ v : Fin 3 → ℕ, (∀ i, v i ∈ A \ D₁) →
      ∑ i, v i ≠ n)
    (hf2 : ∀ v : Fin 3 → ℕ, (∀ i, v i ∈ A \ D₂) →
      ∑ i, v i ≠ n) :
    n % 2 ^ j = (2 * c) % 2 ^ j ∧
    ∃ d₁ ∈ D₁, ∃ d₂ ∈ D₂, d₁ + d₂ = n := by
  obtain ⟨-, d₁, hd₁, d₂, hd₂, hsum⟩ :=
    overlap_bilinear_law h0A h01 h02 hd12 hcov hn hf1 hf2
  refine ⟨?_, d₁, hd₁, d₂, hd₂, hsum⟩
  have h1 := hc1 d₁ hd₁
  have h2 := hc2 d₂ hd₂
  calc n % 2 ^ j = (d₁ + d₂) % 2 ^ j := by rw [hsum]
    _ = (d₁ % 2 ^ j + d₂ % 2 ^ j) % 2 ^ j := by
        rw [Nat.add_mod]
    _ = (c % 2 ^ j + c % 2 ^ j) % 2 ^ j := by rw [h1, h2]
    _ = (c + c) % 2 ^ j := by rw [← Nat.add_mod]
    _ = (2 * c) % 2 ^ j := by ring_nf

open Classical in

theorem pairSupportTransversal_caps_wealth {A : Set ℕ} {w : ℕ}
    {H : Finset ℕ} (hhub : IsPairSupportTransversal A w H) :
    ((Finset.range (w + 1)).filter
      (fun x => x ∈ A ∧ (w - x) ∈ A)).card ≤ 2 * H.card := by
  have hlow := pair_support_transversal_pair_count hhub
  set Low := (Finset.range (w + 1)).filter
    (fun a => a ∈ A ∧ (w - a) ∈ A ∧ 2 * a ≤ w) with hLow
  set High := (Finset.range (w + 1)).filter
    (fun a => a ∈ A ∧ (w - a) ∈ A ∧ w < 2 * a) with hHigh
  have hsub : (Finset.range (w + 1)).filter
      (fun x => x ∈ A ∧ (w - x) ∈ A) ⊆ Low ∪ High := by
    intro a ha
    rw [Finset.mem_filter, Finset.mem_range] at ha
    obtain ⟨hav, haA, hwaA⟩ := ha
    rcases Nat.lt_or_ge w (2 * a) with hc | hc
    · exact Finset.mem_union_right _ (Finset.mem_filter.2
        ⟨Finset.mem_range.2 hav, haA, hwaA, hc⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.2
        ⟨Finset.mem_range.2 hav, haA, hwaA, hc⟩)
  have hHL : High.card ≤ Low.card := by
    apply Finset.card_le_card_of_injOn (fun a => w - a)
    · intro a ha
      simp only [hHigh, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range] at ha
      obtain ⟨hav, haA, hwaA, hc⟩ := ha
      simp only [hLow, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range]
      have he : w - (w - a) = a := by omega
      rw [he]
      exact ⟨by omega, hwaA, haA, by omega⟩
    · intro a ha b hb hab
      simp only [hHigh, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range] at ha hb
      have hab' : w - a = w - b := hab
      omega
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le Low High
  omega

open Classical in

theorem universal_prefix_support_transversal_law {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ B ⊆ A, 0 ∉ B → B.Infinite → ∀ N, ∃ n, N ≤ n ∧
      IsPairSupportTransversal A n ((Finset.range (n + 1)).filter
        (fun x => x ∈ B)) ∧
      ((Finset.range (n + 1)).filter
        (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤
      2 * ((Finset.range (n + 1)).filter
        (fun x => x ∈ B)).card := by
  intro B hBA h0B hBinf N
  have hnot := hfail B hBA hBinf
  simp only [IsExactTupleAsymptoticBasis, not_exists,
    not_forall] at hnot
  obtain ⟨n, hn, hnrep⟩ := hnot N
  have hfailn : ∀ v : Fin 3 → ℕ, (∀ i, v i ∈ A \ B) →
      ∑ i, v i ≠ n := by
    intro v hv hs
    exact hnrep v ⟨hv, hs⟩
  have hhub : IsPairSupportTransversal A n ((Finset.range (n + 1)).filter
      (fun x => x ∈ B)) := by
    intro x hx y hy hxy
    by_cases hxB : x ∈ B
    · exact Or.inl (Finset.mem_filter.2
        ⟨Finset.mem_range.2 (by omega), hxB⟩)
    · by_cases hyB : y ∈ B
      · exact Or.inr (Finset.mem_filter.2
          ⟨Finset.mem_range.2 (by omega), hyB⟩)
      · exfalso
        have hmem : ∀ i, (![x, y, 0] : Fin 3 → ℕ) i ∈
            A \ B := by
          intro i
          match i with
          | 0 => exact ⟨hx, hxB⟩
          | 1 => exact ⟨hy, hyB⟩
          | 2 => exact ⟨h0, h0B⟩
        have hsum0 : x + y + 0 = n := by omega
        exact hfailn ![x, y, 0] hmem
          (by simpa [Fin.sum_univ_three] using hsum0)
  exact ⟨n, hn, hhub, pairSupportTransversal_caps_wealth hhub⟩

open Classical in

theorem universal_deletion_transversal_law {A : Set ℕ}
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ B ⊆ A, B.Infinite → ∀ N, ∃ n, N ≤ n ∧
      ∃ H ⊆ (Finset.range (n + 1)).filter (fun x => x ∈ B),
        IsRepSupportTransversal A n H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
        ∀ h ∈ H, ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = n ∧
          (x = h ∨ y = h ∨ z = h) ∧
          ∀ g ∈ H, g ≠ h → x ≠ g ∧ y ≠ g ∧ z ≠ g := by
  intro B hBA hBinf N
  have hnot := hfail B hBA hBinf
  simp only [IsExactTupleAsymptoticBasis, not_exists,
    not_forall] at hnot
  obtain ⟨n, hn, hnrep⟩ := hnot N
  have hprefix : IsRepSupportTransversal A n ((Finset.range (n + 1)).filter
      (fun x => x ∈ B)) := by
    intro x hx y hy z hz hsum
    by_cases hxB : x ∈ B
    · exact Or.inl (Finset.mem_filter.2
        ⟨Finset.mem_range.2 (by omega), hxB⟩)
    · by_cases hyB : y ∈ B
      · exact Or.inr (Or.inl (Finset.mem_filter.2
          ⟨Finset.mem_range.2 (by omega), hyB⟩))
      · by_cases hzB : z ∈ B
        · exact Or.inr (Or.inr (Finset.mem_filter.2
            ⟨Finset.mem_range.2 (by omega), hzB⟩))
        · exfalso
          have hmem : ∀ i, (![x, y, z] : Fin 3 → ℕ) i ∈
              A \ B := by
            intro i
            match i with
            | 0 => exact ⟨hx, hxB⟩
            | 1 => exact ⟨hy, hyB⟩
            | 2 => exact ⟨hz, hzB⟩
          exact hnrep ![x, y, z] ⟨hmem,
            by simpa [Fin.sum_univ_three] using hsum⟩
  obtain ⟨H, hHsub, hHhub, hHmin⟩ := exists_minimal_support_transversal hprefix
  exact ⟨n, hn, H, hHsub, hHhub, hHmin,
    minimal_support_transversal_necessity hHhub hHmin⟩

open Classical in

theorem deletion_transversal_size_floor {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ B ⊆ A, (∀ b ∈ B, 0 < b) → B.Infinite →
      ∀ N, ∃ n, N ≤ n ∧
      ∃ H ⊆ (Finset.range (n + 1)).filter (fun x => x ∈ B),
        2 ≤ H.card ∧ IsRepSupportTransversal A n H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
        ∀ h ∈ H, ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = n ∧
          (x = h ∨ y = h ∨ z = h) ∧
          ∀ g ∈ H, g ≠ h → x ≠ g ∧ y ≠ g ∧ z ≠ g := by
  intro B hBA hBpos hBinf N
  have hnosing := singleton_support_transversals_refuted h0 hcov hanchor hfail
  push Not at hnosing
  obtain ⟨N₁, hN₁⟩ := hnosing
  obtain ⟨n, hn, H, hHsub, hHhub, hHmin, hHwit⟩ :=
    universal_deletion_transversal_law hfail B hBA hBinf
      (max N (max N₁ N₀))
  refine ⟨n, by omega, H, hHsub, ?_, hHhub, hHmin, hHwit⟩
  rcases Nat.lt_or_ge H.card 2 with hc | hc
  · exfalso
    interval_cases h : H.card
    · have hemp : H = ∅ := Finset.card_eq_zero.1 h
      obtain ⟨x, hx, y, hy, hxy⟩ := hcov n (by omega)
      rcases hHhub x hx y hy 0 h0 (by omega) with hm | hm | hm
        <;> rw [hemp] at hm <;>
        exact absurd hm (Finset.notMem_empty _)
    · obtain ⟨b, hb⟩ := Finset.card_eq_one.1 h
      have hbB : b ∈ B := by
        have := hHsub (hb ▸ Finset.mem_singleton_self b)
        rw [Finset.mem_filter] at this
        exact this.2
      exact hN₁ n (by omega) b (hBpos b hbB) (hb ▸ hHhub)
  · exact hc

open Classical in

theorem routing_case_doubles_poor {A : Set ℕ} {g₀ : ℕ}
    (hroute : ∀ c ∈ A, 0 < c → c ≠ g₀ →
      IsPairSupportTransversal A (2 * c) ({c, g₀} : Finset ℕ)) :
    ∀ c ∈ A, 0 < c → c ≠ g₀ →
      ((Finset.range (2 * c + 1)).filter
        (fun x => x ∈ A ∧ (2 * c - x) ∈ A)).card ≤ 4 := by
  intro c hc hpos hne
  have hcap := pairSupportTransversal_caps_wealth (hroute c hc hpos hne)
  have hcard : ({c, g₀} : Finset ℕ).card ≤ 2 := by
    refine le_trans (Finset.card_insert_le c {g₀}) ?_
    rw [Finset.card_singleton]
  omega

open Classical in

theorem routing_case_wealth_avoids_doubles {A : Set ℕ}
    {N₀ g₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hroute : ∀ c ∈ A, 0 < c → c ≠ g₀ →
      IsPairSupportTransversal A (2 * c) ({c, g₀} : Finset ℕ)) :
    ∀ N, ∃ w, N ≤ w ∧ 5 ≤
      ((Finset.range (w + 1)).filter
        (fun x => x ∈ A ∧ (w - x) ∈ A)).card ∧
      ∀ c ∈ A, 0 < c → c ≠ g₀ → w ≠ 2 * c := by
  intro N
  obtain ⟨w, hwN, hwC⟩ :=
    r2_unbounded_of_hfail h0 hcov hfail 5 N
  refine ⟨w, hwN, hwC, ?_⟩
  intro c hc hpos hne heq
  have hpoor := routing_case_doubles_poor hroute c hc hpos hne
  rw [heq] at hwC
  omega

open Classical in

theorem deletion_transversal_band_tax {A B : Set ℕ} {C : ℕ}
    (h0 : 0 ∈ A) (hBpos : ∀ b ∈ B, 0 < b)
    (hfam : ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧
      (∀ x ∈ H, x ∈ B) ∧ IsRepSupportTransversal A n H) :
    ∀ N, ∃ n, N ≤ n ∧
      ((Finset.range (n + 1)).filter
        (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ 2 * C := by
  intro N
  obtain ⟨n, hn, H, hc, hHB, hhub⟩ := hfam N
  have h0H : 0 ∉ H := by
    intro h
    have := hBpos 0 (hHB 0 h)
    omega
  have hcap := repSupportTransversal_caps_pair_wealth h0 h0H hhub
  exact ⟨n, hn, by omega⟩

open Classical in

theorem deletion_transversal_translate_freeness {A : Set ℕ} {n : ℕ}
    {H : Finset ℕ}
    (hhub : IsRepSupportTransversal A n H)
    (hmin : ∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) :
    ∀ h ∈ H, ¬IsPairSupportTransversal A (n - h) (H \ {h}) := by
  intro h hhH hpair
  obtain ⟨x, hx, y, hy, z, hz, hsum, hmem, havoid⟩ :=
    minimal_support_transversal_necessity hhub hmin h hhH
  have key : ∀ u v : ℕ, u ∈ A → v ∈ A → h + u + v = n →
      u ∉ H \ {h} → v ∉ H \ {h} → False := by
    intro u v hu hv hsum' hunot hvnot
    rcases hpair u hu v hv (by omega) with hm | hm
    · exact hunot hm
    · exact hvnot hm
  have hnot : ∀ g, g ∈ H → g ≠ h → x ≠ g ∧ y ≠ g ∧ z ≠ g :=
    havoid
  have hxn : x ∉ H \ {h} ∨ x = h := by
    by_cases hxh : x = h
    · exact Or.inr hxh
    · left
      intro hxH
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hxH
      exact (hnot x hxH.1 hxH.2).1 rfl
  have hyn : y ∉ H \ {h} ∨ y = h := by
    by_cases hyh : y = h
    · exact Or.inr hyh
    · left
      intro hyH
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hyH
      exact (hnot y hyH.1 hyH.2).2.1 rfl
  have hzn : z ∉ H \ {h} ∨ z = h := by
    by_cases hzh : z = h
    · exact Or.inr hzh
    · left
      intro hzH
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hzH
      exact (hnot z hzH.1 hzH.2).2.2 rfl
  have hhnot : (h : ℕ) ∉ H \ {h} := by
    rw [Finset.mem_sdiff, Finset.mem_singleton]
    intro hc
    exact hc.2 rfl
  rcases hmem with hxh | hyh | hzh
  · rcases hyn with hyn' | hyh'
    · rcases hzn with hzn' | hzh'
      · exact key y z hy hz (by omega) hyn' hzn'
      · exact key y z hy hz (by omega) hyn' (hzh' ▸ hhnot)
    · rcases hzn with hzn' | hzh'
      · exact key y z hy hz (by omega) (hyh' ▸ hhnot) hzn'
      · exact key y z hy hz (by omega) (hyh' ▸ hhnot)
          (hzh' ▸ hhnot)
  · rcases hxn with hxn' | hxh'
    · rcases hzn with hzn' | hzh'
      · exact key x z hx hz (by omega) hxn' hzn'
      · exact key x z hx hz (by omega) hxn' (hzh' ▸ hhnot)
    · rcases hzn with hzn' | hzh'
      · exact key x z hx hz (by omega) (hxh' ▸ hhnot) hzn'
      · exact key x z hx hz (by omega) (hxh' ▸ hhnot)
          (hzh' ▸ hhnot)
  · rcases hxn with hxn' | hxh'
    · rcases hyn with hyn' | hyh'
      · exact key x y hx hy (by omega) hxn' hyn'
      · exact key x y hx hy (by omega) hxn' (hyh' ▸ hhnot)
    · rcases hyn with hyn' | hyh'
      · exact key x y hx hy (by omega) (hxh' ▸ hhnot) hyn'
      · exact key x y hx hy (by omega) (hxh' ▸ hhnot)
          (hyh' ▸ hhnot)

open Classical in

theorem counterexample_structure_width_band_local {A B : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B' ⊆ A, B'.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B') 3)
    (hBA : B ⊆ A) (hBpos : ∀ b ∈ B, 0 < b)
    (hBinf : B.Infinite) :
    (∃ C, ∀ N, ∃ n, N ≤ n ∧
      (∃ H ⊆ (Finset.range (n + 1)).filter (fun x => x ∈ B),
        H.card ≤ C ∧ 2 ≤ H.card ∧ IsRepSupportTransversal A n H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h}))) ∧
      ((Finset.range (n + 1)).filter
        (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ 2 * C) ∨
    (∀ C N, ∃ n, N ≤ n ∧
      ∃ H ⊆ (Finset.range (n + 1)).filter (fun x => x ∈ B),
        C < H.card ∧ IsRepSupportTransversal A n H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
        (∀ h ∈ H, ¬IsPairSupportTransversal A (n - h) (H \ {h})) ∧
        ∀ h ∈ H, ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = n ∧
          (x = h ∨ y = h ∨ z = h) ∧
          ∀ g ∈ H, g ≠ h → x ≠ g ∧ y ≠ g ∧ z ≠ g) := by
  by_cases hb : ∃ C, ∀ N, ∃ n, N ≤ n ∧
      ∃ H ⊆ (Finset.range (n + 1)).filter (fun x => x ∈ B),
        H.card ≤ C ∧ 2 ≤ H.card ∧ IsRepSupportTransversal A n H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h}))
  · left
    obtain ⟨C, hC⟩ := hb
    refine ⟨C, fun N => ?_⟩
    obtain ⟨n, hn, H, hHsub, hHc, hH2, hHhub, hHmin⟩ := hC N
    have h0H : 0 ∉ H := by
      intro hmem
      have := hHsub hmem
      rw [Finset.mem_filter] at this
      have := hBpos 0 this.2
      omega
    have hcap := repSupportTransversal_caps_pair_wealth h0 h0H hHhub
    exact ⟨n, hn, ⟨H, hHsub, hHc, hH2, hHhub, hHmin⟩,
      by omega⟩
  · right
    push Not at hb
    intro C N
    obtain ⟨N₁, hN₁⟩ := hb C
    obtain ⟨n, hn, H, hHsub, hH2, hHhub, hHmin, hHwit⟩ :=
      deletion_transversal_size_floor h0 hcov hanchor hfail B hBA hBpos
        hBinf (max N N₁)
    have hwide : C < H.card := by
      rcases Nat.lt_or_ge C H.card with h | h
      · exact h
      · exfalso
        obtain ⟨h', hh'H, hh'hub⟩ :=
          hN₁ n (by omega) H hHsub h hH2 hHhub
        exact hHmin h' hh'H hh'hub
    exact ⟨n, by omega, H, hHsub, hwide, hHhub, hHmin,
      deletion_transversal_translate_freeness hHhub hHmin, hHwit⟩

open Classical in

theorem cylinder_deletion_transversal_chains {A : Set ℕ}
    {m c n : ℕ} {H : Finset ℕ}
    (h0 : 0 ∈ A)
    (hHcyl : ∀ x ∈ H, x % 2 ^ m = c % 2 ^ m ∧ 0 < x)
    (hhub : IsRepSupportTransversal A n H) :
    (∀ x ∈ A, ∀ y ∈ A, x + y = n →
      x % 2 ^ m = c % 2 ^ m ∨ y % 2 ^ m = c % 2 ^ m) ∧
    ((Finset.range (n + 1)).filter
      (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ 2 * H.card := by
  have h0H : 0 ∉ H := by
    intro h
    have := (hHcyl 0 h).2
    omega
  have hpair := pairSupportTransversal_of_repSupportTransversal h0 h0H hhub
  constructor
  · intro x hx y hy hxy
    rcases hpair x hx y hy hxy with h | h
    · exact Or.inl (hHcyl x h).1
    · exact Or.inr (hHcyl y h).1
  · exact repSupportTransversal_caps_pair_wealth h0 h0H hhub

open Classical in

theorem poor_stream_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ L, ∀ N, ∃ n, N ≤ n ∧
      ((Finset.range (n + 1)).filter
        (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ L := by
  by_contra hno
  push Not at hno
  choose G hG using hno
  have hsupply : ∀ X, ∃ a, a ∈ A ∧ X ≤ a := by
    intro X
    obtain ⟨a, ha, hX⟩ := pairCovers_unbounded hcov X
    exact ⟨a, ha, hX⟩
  choose f hfA hfge using hsupply
  set d : ℕ → ℕ := fun i => Nat.rec (f (G 4 + 1))
    (fun i prev => f (max prev (G (2 * (i + 1) + 4)) + 1)) i
    with hd
  have hd0 : d 0 = f (G 4 + 1) := rfl
  have hdS : ∀ i, d (i + 1) =
      f (max (d i) (G (2 * (i + 1) + 4)) + 1) := fun _ => rfl
  have hdA : ∀ i, d i ∈ A := by
    intro i
    cases i with
    | zero =>
      rw [hd0]
      exact hfA _
    | succ i =>
      rw [hdS]
      exact hfA _
  have hdgap : ∀ i, G (2 * i + 4) < d i := by
    intro i
    cases i with
    | zero =>
      have he : 2 * 0 + 4 = 4 := by norm_num
      rw [he, hd0]
      have := hfge (G 4 + 1)
      omega
    | succ i =>
      rw [hdS]
      have h1 := hfge (max (d i) (G (2 * (i + 1) + 4)) + 1)
      have h2 := le_max_right (d i) (G (2 * (i + 1) + 4))
      omega
  have hdmono : StrictMono d := by
    apply strictMono_nat_of_lt_succ
    intro i
    rw [hdS]
    have h1 := hfge (max (d i) (G (2 * (i + 1) + 4)) + 1)
    have h2 := le_max_left (d i) (G (2 * (i + 1) + 4))
    omega
  have hdpos : ∀ i, 0 < d i := by
    intro i
    cases i with
    | zero =>
      rw [hd0]
      have := hfge (G 4 + 1)
      omega
    | succ i =>
      rw [hdS]
      have := hfge (max (d i) (G (2 * (i + 1) + 4)) + 1)
      omega
  have hlin : ∀ i, i ≤ d i := by
    intro i
    induction i with
    | zero => omega
    | succ i ih =>
      have := hdmono (by omega : i < i + 1)
      omega
  set D : Set ℕ := Set.range d with hD
  have hDA : D ⊆ A := by
    intro x hx
    rw [hD, Set.mem_range] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hdA i
  have h0D : 0 ∉ D := by
    intro hx
    rw [hD, Set.mem_range] at hx
    obtain ⟨i, hi⟩ := hx
    have := hdpos i
    omega
  have hDinf : D.Infinite := by
    rw [hD]
    exact Set.infinite_range_of_injective hdmono.injective
  have hnot := hfail D hDA hDinf
  simp only [IsExactTupleAsymptoticBasis, not_exists,
    not_forall] at hnot
  obtain ⟨n, hn, hnrep⟩ := hnot (max N₀ (d 0))
  have hfailn : ∀ v : Fin 3 → ℕ, (∀ i, v i ∈ A \ D) →
      ∑ i, v i ≠ n := fun v hv hs => hnrep v ⟨hv, hs⟩
  have hpoor := failing_target_poor h0 h0D hfailn
  have hnd0 : d 0 ≤ n := le_trans (le_max_right _ _) hn
  have hexJ : ∃ i, n < d i := by
    obtain ⟨i, hi⟩ : ∃ i, n + 1 ≤ i := ⟨n + 1, le_refl _⟩
    exact ⟨n + 1, by have := hlin (n + 1); omega⟩
  set J := Nat.find hexJ with hJ
  have hJspec : n < d J := Nat.find_spec hexJ
  have hJmin : ∀ i, i < J → d i ≤ n := by
    intro i hi
    have := Nat.find_min hexJ hi
    omega
  have hJ1 : 1 ≤ J := by
    rcases Nat.eq_zero_or_pos J with h | h
    · exfalso
      rw [h] at hJspec
      omega
    · exact h
  have hFeq : (Finset.range (n + 1)).filter (fun x => x ∈ D) =
      (Finset.range J).image d := by
    ext x
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hxn, hxD⟩
      rw [hD, Set.mem_range] at hxD
      obtain ⟨i, rfl⟩ := hxD
      refine ⟨i, Finset.mem_range.2 ?_, rfl⟩
      by_contra hiJ
      have h1 : J ≤ i := by omega
      have h2 : d J ≤ d i := hdmono.monotone h1
      omega
    · rintro ⟨i, hiJ, rfl⟩
      rw [Finset.mem_range] at hiJ
      have := hJmin i hiJ
      refine ⟨by omega, ?_⟩
      rw [hD, Set.mem_range]
      exact ⟨i, rfl⟩
  have hFcard : ((Finset.range (n + 1)).filter
      (fun x => x ∈ D)).card = J := by
    rw [hFeq, Finset.card_image_of_injOn
      (fun a _ b _ hab => hdmono.injective hab),
      Finset.card_range]
  have hd1 : G (2 * (J - 1) + 4) < d (J - 1) := hdgap (J - 1)
  have heq2 : 2 * (J - 1) + 4 = 2 * J + 2 := by omega
  rw [heq2] at hd1
  have hdn : d (J - 1) ≤ n := hJmin (J - 1) (by omega)
  have hbig := hG (2 * J + 2) n (by omega)
  rw [hFcard] at hpoor
  omega

open Classical in

theorem poor_stream_canonical_support_transversals {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ L, ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      H.card ≤ L ∧ IsPairSupportTransversal A n H ∧
      (∀ h ∈ H, h ∈ A ∧ (n - h) ∈ A ∧ 2 * h ≤ n) ∧
      (∀ x, 2 * x ≤ n → x ∈ A → (n - x) ∈ A → x ∈ H) := by
  obtain ⟨L, hL⟩ := poor_stream_of_hfail h0 hcov hfail
  refine ⟨L, fun N => ?_⟩
  obtain ⟨n, hn, hpoor⟩ := hL N
  set H := (Finset.range (n + 1)).filter
    (fun x => x ∈ A ∧ (n - x) ∈ A ∧ 2 * x ≤ n) with hH
  refine ⟨n, hn, H, ?_, ?_, ?_, ?_⟩
  · refine le_trans (Finset.card_le_card ?_) hpoor
    intro x hx
    rw [hH, Finset.mem_filter] at hx
    rw [Finset.mem_filter]
    exact ⟨hx.1, hx.2.1, hx.2.2.1⟩
  · intro x hx y hy hxy
    rcases Nat.le_total x y with hc | hc
    · left
      rw [hH, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, hx, ?_, by omega⟩
      have he : n - x = y := by omega
      rw [he]
      exact hy
    · right
      rw [hH, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, hy, ?_, by omega⟩
      have he : n - y = x := by omega
      rw [he]
      exact hx
  · intro h hh
    rw [hH, Finset.mem_filter] at hh
    exact hh.2
  · intro x hxle hxA hxpA
    rw [hH, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hxA, hxpA, hxle⟩

open Classical in

theorem pair_support_transversal_window_split {A : Set ℕ} {C : ℕ} (W : ℕ)
    (R : ℕ → Finset ℕ → Prop)
    (hfam : ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧
      IsPairSupportTransversal A n H ∧ R n H) :
    ∃ S : Finset ℕ, S ⊆ Finset.range (W + 1) ∧
      ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧
        IsPairSupportTransversal A n H ∧ R n H ∧ S ⊆ H ∧
        ∀ h ∈ H, h ∉ S → W < h := by
  have hvac : ∀ (n : ℕ) (H : Finset ℕ),
      IsRepSupportTransversal (∅ : Set ℕ) n H := by
    intro n H x hx
    exact absurd hx (Set.notMem_empty x)
  obtain ⟨S, hSW, hS⟩ := support_transversal_window_split_aux'
    (A := (∅ : Set ℕ)) (C := C)
    (R := fun n H => IsPairSupportTransversal A n H ∧ R n H) W C ∅
    (by simp)
    (fun N => by
      obtain ⟨n, hn, H, hcard, hpair, hR⟩ := hfam N
      exact ⟨n, hn, H, hcard, hvac n H, ⟨hpair, hR⟩,
        Finset.empty_subset _, by simpa using hcard⟩)
  refine ⟨S, hSW, fun N => ?_⟩
  obtain ⟨n, hn, H, hcard, -, ⟨hpair, hR⟩, hSH, htail⟩ := hS N
  exact ⟨n, hn, H, hcard, hpair, hR, hSH, htail⟩

open Classical in

theorem canonical_core_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ L, ∀ W, ∃ S : Finset ℕ, S ⊆ Finset.range (W + 1) ∧
      ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ L ∧
        IsPairSupportTransversal A n H ∧
        (∀ h ∈ H, h ∈ A ∧ (n - h) ∈ A ∧ 2 * h ≤ n) ∧
        (∀ x, 2 * x ≤ n → x ∈ A → (n - x) ∈ A → x ∈ H) ∧
        S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h := by
  obtain ⟨L, hL⟩ := poor_stream_canonical_support_transversals h0 hcov hfail
  refine ⟨L, fun W => ?_⟩
  obtain ⟨S, hSW, hS⟩ := pair_support_transversal_window_split W
    (R := fun n H =>
      (∀ h ∈ H, h ∈ A ∧ (n - h) ∈ A ∧ 2 * h ≤ n) ∧
      (∀ x, 2 * x ≤ n → x ∈ A → (n - x) ∈ A → x ∈ H))
    (fun N => by
      obtain ⟨n, hn, H, hcard, hpair, hmem, hcomp⟩ := hL N
      exact ⟨n, hn, H, hcard, hpair, hmem, hcomp⟩)
  refine ⟨S, hSW, fun N => ?_⟩
  obtain ⟨n, hn, H, hcard, hpair, ⟨hmem, hcomp⟩, hSH, htail⟩ :=
    hS N
  exact ⟨n, hn, H, hcard, hpair, hmem, hcomp, hSH, htail⟩

open Classical in

theorem poor_drift_fork {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ L,
    (∃ u, ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ L ∧
      IsPairSupportTransversal A n H ∧
      (∀ h ∈ H, h ∈ A ∧ (n - h) ∈ A ∧ 2 * h ≤ n) ∧
      (∀ x, 2 * x ≤ n → x ∈ A → (n - x) ∈ A → x ∈ H) ∧
      u ∈ H) ∨
    (∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ L ∧
      IsPairSupportTransversal A n H ∧
      (∀ h ∈ H, h ∈ A ∧ (n - h) ∈ A ∧ 2 * h ≤ n) ∧
      (∀ x, 2 * x ≤ n → x ∈ A → (n - x) ∈ A → x ∈ H) ∧
      ∀ h ∈ H, W < h) := by
  obtain ⟨L, hL⟩ := canonical_core_of_hfail h0 hcov hfail
  refine ⟨L, ?_⟩
  by_cases hu : ∃ u, ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      H.card ≤ L ∧ IsPairSupportTransversal A n H ∧
      (∀ h ∈ H, h ∈ A ∧ (n - h) ∈ A ∧ 2 * h ≤ n) ∧
      (∀ x, 2 * x ≤ n → x ∈ A → (n - x) ∈ A → x ∈ H) ∧
      u ∈ H
  · exact Or.inl hu
  · right
    intro W N
    obtain ⟨S, hSW, hS⟩ := hL W
    rcases Finset.eq_empty_or_nonempty S with hemp | ⟨u, huS⟩
    · obtain ⟨n, hn, H, hcard, hpair, hmem, hcomp, hSH,
        htail⟩ := hS N
      refine ⟨n, hn, H, hcard, hpair, hmem, hcomp,
        fun h hh => ?_⟩
      refine htail h hh ?_
      rw [hemp]
      exact Finset.notMem_empty h
    · exfalso
      apply hu
      refine ⟨u, fun N' => ?_⟩
      obtain ⟨n, hn, H, hcard, hpair, hmem, hcomp, hSH,
        htail⟩ := hS N'
      exact ⟨n, hn, H, hcard, hpair, hmem, hcomp, hSH huS⟩

open Classical in

theorem drift_case_exclusion_intervals {A : Set ℕ} {L : ℕ}
    (hdrift : ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      H.card ≤ L ∧ IsPairSupportTransversal A n H ∧
      (∀ h ∈ H, h ∈ A ∧ (n - h) ∈ A ∧ 2 * h ≤ n) ∧
      (∀ x, 2 * x ≤ n → x ∈ A → (n - x) ∈ A → x ∈ H) ∧
      ∀ h ∈ H, W < h) :
    ∀ W N, ∃ n, N ≤ n ∧
      ((Finset.range (n + 1)).filter
        (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ 2 * L ∧
      ∀ x, x ∈ A → 1 ≤ x → x ≤ W → 2 * x ≤ n →
        (n - x) ∉ A := by
  intro W N
  obtain ⟨n, hn, H, hcard, hpair, hmem, hcomp, htail⟩ :=
    hdrift W N
  refine ⟨n, hn, ?_, ?_⟩
  · have hcap := pairSupportTransversal_caps_wealth hpair
    omega
  · intro x hxA hx1 hxW hxle hnxA
    have hxH : x ∈ H := hcomp x hxle hxA hnxA
    have := htail x hxH
    omega

open Classical in

theorem small_lowpart_rigidity {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ L, ∀ W, ∃ S : Finset ℕ, S ⊆ Finset.range (W + 1) ∧
      ∀ N, ∃ n, N ≤ n ∧
        ((Finset.range (n + 1)).filter
          (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ 2 * L ∧
        ∀ x, x ≤ W →
          ((x ∈ A ∧ (n - x) ∈ A ∧ 2 * x ≤ n) ↔ x ∈ S) := by
  obtain ⟨L, hL⟩ := canonical_core_of_hfail h0 hcov hfail
  refine ⟨L, fun W => ?_⟩
  obtain ⟨S, hSW, hS⟩ := hL W
  refine ⟨S, hSW, fun N => ?_⟩
  obtain ⟨n, hn, H, hcard, hpair, hmem, hcomp, hSH, htail⟩ :=
    hS N
  have hcap := pairSupportTransversal_caps_wealth hpair
  refine ⟨n, hn, by omega, fun x hxW => ?_⟩
  constructor
  · rintro ⟨hxA, hnxA, hxle⟩
    have hxH : x ∈ H := hcomp x hxle hxA hnxA
    rcases Nat.lt_or_ge W x with hgt | hle'
    · omega
    · by_contra hxS
      have := htail x hxH hxS
      omega
  · intro hxS
    have hxH : x ∈ H := hSH hxS
    exact hmem x hxH

open Classical in

theorem rigidity_trichotomy {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∃ d, 1 ≤ d ∧ ∀ N, ∃ a, N ≤ a ∧ a ∈ A ∧ a + d ∈ A) ∨
    (∃ L u W, u ≤ W ∧ ∀ N, ∃ n, N ≤ n ∧
      ((Finset.range (n + 1)).filter
        (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ 2 * L ∧
      (u ∈ A ∧ (n - u) ∈ A ∧ 2 * u ≤ n) ∧
      ∀ x, x ≤ W → x ≠ u →
        ¬(x ∈ A ∧ (n - x) ∈ A ∧ 2 * x ≤ n)) ∨
    (∃ L, ∀ W N, ∃ n, N ≤ n ∧
      ((Finset.range (n + 1)).filter
        (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ 2 * L ∧
      ∀ x, x ≤ W → ¬(x ∈ A ∧ (n - x) ∈ A ∧ 2 * x ≤ n)) := by
  obtain ⟨L, hL⟩ := small_lowpart_rigidity h0 hcov hfail
  choose Sf hSfW hSf using hL
  by_cases h2 : ∃ W, 2 ≤ (Sf W).card
  · left
    obtain ⟨W, hW2⟩ := h2
    have h1lt : 1 < (Sf W).card := by omega
    obtain ⟨x, hxS, x', hx'S, hne⟩ := Finset.one_lt_card.1 h1lt
    have hne' : x ≠ x' := hne
    have key : ∀ y y' : ℕ, y ∈ Sf W → y' ∈ Sf W → y < y' →
        ∃ d, 1 ≤ d ∧ ∀ N, ∃ a, N ≤ a ∧ a ∈ A ∧ a + d ∈ A := by
      intro y y' hyS hy'S hyy'
      refine ⟨y' - y, by omega, fun N => ?_⟩
      obtain ⟨n, hn, hpoor, hiff⟩ := hSf W (N + y' + 1)
      have hyW : y ≤ W := by
        have := hSfW W hyS
        rw [Finset.mem_range] at this
        omega
      have hy'W : y' ≤ W := by
        have := hSfW W hy'S
        rw [Finset.mem_range] at this
        omega
      have hy := (hiff y hyW).2 hyS
      have hy' := (hiff y' hy'W).2 hy'S
      refine ⟨n - y', by omega, hy'.2.1, ?_⟩
      have he : n - y' + (y' - y) = n - y := by omega
      rw [he]
      exact hy.2.1
    rcases lt_or_gt_of_ne hne' with hlt | hlt
    · exact key x x' hxS hx'S hlt
    · exact key x' x hx'S hxS hlt
  · by_cases h1 : ∃ W, (Sf W).card = 1
    · right
      left
      obtain ⟨W, hW1⟩ := h1
      obtain ⟨u, hu⟩ := Finset.card_eq_one.1 hW1
      have huW : u ≤ W := by
        have : u ∈ Sf W := by
          rw [hu]
          exact Finset.mem_singleton_self u
        have := hSfW W this
        rw [Finset.mem_range] at this
        omega
      refine ⟨L, u, W, huW, fun N => ?_⟩
      obtain ⟨n, hn, hpoor, hiff⟩ := hSf W N
      refine ⟨n, hn, hpoor, ?_, ?_⟩
      · refine (hiff u huW).2 ?_
        rw [hu]
        exact Finset.mem_singleton_self u
      · intro x hxW hxu hpkg
        have := (hiff x hxW).1 hpkg
        rw [hu, Finset.mem_singleton] at this
        exact hxu this
    · right
      right
      refine ⟨L, fun W N => ?_⟩
      obtain ⟨n, hn, hpoor, hiff⟩ := hSf W N
      refine ⟨n, hn, hpoor, fun x hxW hpkg => ?_⟩
      have hxS := (hiff x hxW).1 hpkg
      have hcard : (Sf W).card = 0 ∨ (Sf W).card = 1 ∨
          2 ≤ (Sf W).card := by omega
      rcases hcard with h | h | h
      · rw [Finset.card_eq_zero.1 h] at hxS
        exact absurd hxS (Finset.notMem_empty x)
      · exact h1 ⟨W, h⟩
      · exact h2 ⟨W, h⟩

/-- Cofinal δ-paired supply yields finite δ-paired families of every size. -/
theorem fixed_difference_families {d : ℕ} {A : Set ℕ}
    (hsup : ∀ N, ∃ a, N ≤ a ∧ a ∈ A ∧ a + d ∈ A) :
    ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ x ∈ V, x ∈ A ∧ x + d ∈ A := by
  intro K
  induction K with
  | zero => exact ⟨∅, by simp, by simp⟩
  | succ K ih =>
    obtain ⟨V, hVc, hVm⟩ := ih
    obtain ⟨a, ha, haA, hadA⟩ := hsup (V.sup id + 1)
    have haV : a ∉ V := by
      intro hmem
      have := Finset.le_sup (f := id) hmem
      simp only [id] at this
      omega
    refine ⟨insert a V, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem haV]
      omega
    · intro x hx
      rcases Finset.mem_insert.1 hx with hxa | hxV
      · rw [hxa]
        exact ⟨haA, hadA⟩
      · exact hVm x hxV

open Classical in

theorem rigidity_trichotomy_pair_transversals {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∃ d, 1 ≤ d ∧ ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      IsRepSupportTransversal A n H ∧ (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
      2 ≤ H.card ∧ ∀ h ∈ H, h ∈ A ∧ h + d ∈ A ∧ 0 < h) ∨
    (∃ L u W, u ≤ W ∧ ∀ N, ∃ n, N ≤ n ∧
      ((Finset.range (n + 1)).filter
        (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ 2 * L ∧
      (u ∈ A ∧ (n - u) ∈ A ∧ 2 * u ≤ n) ∧
      ∀ x, x ≤ W → x ≠ u →
        ¬(x ∈ A ∧ (n - x) ∈ A ∧ 2 * x ≤ n)) ∨
    (∃ L, ∀ W N, ∃ n, N ≤ n ∧
      ((Finset.range (n + 1)).filter
        (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ 2 * L ∧
      ∀ x, x ≤ W → ¬(x ∈ A ∧ (n - x) ∈ A ∧ 2 * x ≤ n)) := by
  rcases rigidity_trichotomy h0 hcov hfail with
    ⟨d, hd, hsup⟩ | h | h
  · left
    refine ⟨d, hd, ?_⟩
    have hteams := translation_case_pair_transversals h0 hcov hanchor
      hfail (fixed_difference_families hsup)
    intro N
    obtain ⟨n, hn, H, hhub, hmin, hcard, hmem⟩ := hteams N
    exact ⟨n, hn, H, hhub, hmin, hcard, hmem⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

open Classical in

theorem disjoint_matching_avoidance {A : Set ℕ} {nseq x₁ x₂ : ℕ → ℕ}
    (hx₁A : ∀ k, x₁ k ∈ A) (hx₁pA : ∀ k, nseq k - x₁ k ∈ A)
    (hx₂A : ∀ k, x₂ k ∈ A) (hx₂pA : ∀ k, nseq k - x₂ k ∈ A)
    (hx₁le : ∀ k, x₁ k ≤ nseq k) (hx₂le : ∀ k, x₂ k ≤ nseq k)
    (hpos : ∀ k, 0 < x₁ k)
    (hne : ∀ k, x₂ k ≠ x₁ k ∧ nseq k - x₂ k ≠ x₁ k)
    (hVdisj : ∀ j k, j ≠ k →
      ∀ v, v ∈ ({x₁ j, nseq j - x₁ j, x₂ j, nseq j - x₂ j} :
        Finset ℕ) →
      v ∉ ({x₁ k, nseq k - x₁ k, x₂ k, nseq k - x₂ k} :
        Finset ℕ)) :
    ∃ D ⊆ A, D.Infinite ∧ 0 ∉ D ∧
      ∀ k, ∃ y, y ∈ A ∧ (nseq k - y) ∈ A ∧ y ≤ nseq k ∧
        y ∉ D ∧ (nseq k - y) ∉ D := by
  set D : Set ℕ := Set.range (fun k => x₁ (2 * k)) with hD
  have hDmem : ∀ v, v ∈ D → ∃ j, v = x₁ (2 * j) := by
    intro v hv
    rw [hD, Set.mem_range] at hv
    obtain ⟨j, hj⟩ := hv
    exact ⟨j, hj.symm⟩
  have hDA : D ⊆ A := by
    intro v hv
    obtain ⟨j, hj⟩ := hDmem v hv
    rw [hj]
    exact hx₁A _
  have hDinf : D.Infinite := by
    rw [hD]
    apply Set.infinite_range_of_injective
    intro a b hab
    by_contra hne'
    have hab' : x₁ (2 * a) = x₁ (2 * b) := hab
    have h2 : 2 * a ≠ 2 * b := by omega
    have hnotin := hVdisj (2 * a) (2 * b) h2 (x₁ (2 * a))
      (by simp)
    refine hnotin ?_
    rw [hab']
    simp
  have h0D : 0 ∉ D := by
    intro hv
    obtain ⟨j, hj⟩ := hDmem 0 hv
    have := hpos (2 * j)
    omega
  have hDV : ∀ k, ∀ v, v ∈ D →
      v ∈ ({x₁ k, nseq k - x₁ k, x₂ k, nseq k - x₂ k} :
        Finset ℕ) → v = x₁ k := by
    intro k v hvD hvV
    obtain ⟨j, hj⟩ := hDmem v hvD
    by_cases hjk : 2 * j = k
    · rw [hj, hjk]
    · exfalso
      have := hVdisj (2 * j) k hjk v (by rw [hj]; simp)
      exact this hvV
  refine ⟨D, hDA, hDinf, h0D, fun k => ?_⟩
  refine ⟨x₂ k, hx₂A k, hx₂pA k, hx₂le k, ?_, ?_⟩
  · intro hmem
    have := hDV k (x₂ k) hmem (by simp)
    exact (hne k).1 this
  · intro hmem
    have := hDV k (nseq k - x₂ k) hmem (by simp)
    exact (hne k).2 this

open Classical in

theorem wealthy_pair_survives {A D : Set ℕ} {v : ℕ}
    (hwealth : 2 * ((Finset.range (v + 1)).filter
        (fun x => x ∈ D)).card + 2 <
      ((Finset.range (v + 1)).filter
        (fun x => x ∈ A ∧ (v - x) ∈ A)).card) :
    ∃ x, x ∈ A ∧ (v - x) ∈ A ∧ x ≤ v ∧ x ∉ D ∧
      (v - x) ∉ D := by
  set Full := (Finset.range (v + 1)).filter
    (fun x => x ∈ A ∧ (v - x) ∈ A) with hFull
  set DF := (Finset.range (v + 1)).filter
    (fun x => x ∈ D) with hDF
  set Bad := Full.filter
    (fun x => x ∈ D ∨ (v - x) ∈ D) with hBad
  have hBadsub : Bad ⊆ DF ∪ (Finset.range (v + 1)).filter
      (fun x => (v - x) ∈ D) := by
    intro x hx
    rw [hBad, Finset.mem_filter] at hx
    obtain ⟨hxF, hxor⟩ := hx
    rw [hFull, Finset.mem_filter] at hxF
    rcases hxor with h | h
    · exact Finset.mem_union_left _
        (Finset.mem_filter.2 ⟨hxF.1, h⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.2 ⟨hxF.1, h⟩)
  have hrefl : ((Finset.range (v + 1)).filter
      (fun x => (v - x) ∈ D)).card ≤ DF.card := by
    apply Finset.card_le_card_of_injOn (fun x => v - x)
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range] at hx
      simp only [hDF, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range]
      exact ⟨by omega, hx.2⟩
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range] at ha hb
      have hab' : v - a = v - b := hab
      omega
  have hBadcard : Bad.card ≤ 2 * DF.card := by
    have h1 := Finset.card_le_card hBadsub
    have h2 := Finset.card_union_le DF
      ((Finset.range (v + 1)).filter (fun x => (v - x) ∈ D))
    omega
  have hex : (Full \ Bad).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : Full ⊆ Bad := by
      intro x hx
      by_contra hxB
      have hmem : x ∈ Full \ Bad :=
        Finset.mem_sdiff.2 ⟨hx, hxB⟩
      rw [hemp] at hmem
      exact absurd hmem (Finset.notMem_empty x)
    have := Finset.card_le_card hsub
    omega
  obtain ⟨x, hx⟩ := hex
  rw [Finset.mem_sdiff] at hx
  obtain ⟨hxF, hxB⟩ := hx
  have hxF' := hxF
  rw [hFull, Finset.mem_filter, Finset.mem_range] at hxF'
  obtain ⟨hxv, hxA, hvxA⟩ := hxF'
  have hxnotor : ¬(x ∈ D ∨ (v - x) ∈ D) := by
    intro h
    exact hxB (Finset.mem_filter.2 ⟨hxF, h⟩)
  exact ⟨x, hxA, hvxA, by omega,
    fun h => hxnotor (Or.inl h),
    fun h => hxnotor (Or.inr h)⟩

open Classical in

theorem fan_poverty_of_failing {A D : Set ℕ} {n : ℕ}
    (hfailn : ∀ v : Fin 3 → ℕ, (∀ i, v i ∈ A \ D) →
      ∑ i, v i ≠ n) :
    ∀ x, x ∈ A → x ∉ D → x ≤ n →
      ((Finset.range (n - x + 1)).filter
        (fun y => y ∈ A ∧ (n - x - y) ∈ A)).card ≤
      2 * ((Finset.range (n + 1)).filter
        (fun d => d ∈ D)).card + 2 := by
  intro x hxA hxD hxn
  by_contra hrich
  push Not at hrich
  have hmono : ((Finset.range (n - x + 1)).filter
      (fun d => d ∈ D)).card ≤
      ((Finset.range (n + 1)).filter
        (fun d => d ∈ D)).card := by
    apply Finset.card_le_card
    intro d hd
    rw [Finset.mem_filter, Finset.mem_range] at hd
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hd.2⟩
  have hwealth : 2 * ((Finset.range (n - x + 1)).filter
      (fun d => d ∈ D)).card + 2 <
      ((Finset.range (n - x + 1)).filter
        (fun y => y ∈ A ∧ (n - x - y) ∈ A)).card := by
    omega
  obtain ⟨y, hyA, hyxA, hyle, hyD, hyxD⟩ :=
    wealthy_pair_survives hwealth
  have hmem : ∀ i, (![x, y, n - x - y] : Fin 3 → ℕ) i ∈
      A \ D := by
    intro i
    match i with
    | 0 => exact ⟨hxA, hxD⟩
    | 1 => exact ⟨hyA, hyD⟩
    | 2 => exact ⟨hyxA, hyxD⟩
  have hsum0 : x + y + (n - x - y) = n := by omega
  exact hfailn ![x, y, n - x - y] hmem
    (by simpa [Fin.sum_univ_three] using hsum0)

open Classical in

theorem poor_count_of_failing {A D : Set ℕ} {n : ℕ}
    (hfailn : ∀ v : Fin 3 → ℕ, (∀ i, v i ∈ A \ D) →
      ∑ i, v i ≠ n) :
    ((Finset.range (n + 1)).filter
      (fun x => x ∈ A ∧ x ∉ D)).card ≤
    ((Finset.range (n + 1)).filter (fun m =>
      ((Finset.range (m + 1)).filter
        (fun y => y ∈ A ∧ (m - y) ∈ A)).card ≤
      2 * ((Finset.range (n + 1)).filter
        (fun d => d ∈ D)).card + 2)).card := by
  apply Finset.card_le_card_of_injOn (fun x => n - x)
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range] at hx
    obtain ⟨hxn, hxA, hxD⟩ := hx
    simp only [Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range]
    exact ⟨by omega,
      fan_poverty_of_failing hfailn x hxA hxD (by omega)⟩
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range] at ha hb
    have hab' : n - a = n - b := hab
    omega

open Classical in

theorem density_law_of_failing {A D : Set ℕ} {n : ℕ}
    (hfailn : ∀ v : Fin 3 → ℕ, (∀ i, v i ∈ A \ D) →
      ∑ i, v i ≠ n) :
    ((Finset.range (n + 1)).filter (fun x => x ∈ A)).card -
      ((Finset.range (n + 1)).filter (fun d => d ∈ D)).card ≤
    ((Finset.range (n + 1)).filter (fun m =>
      ((Finset.range (m + 1)).filter
        (fun y => y ∈ A ∧ (m - y) ∈ A)).card ≤
      2 * ((Finset.range (n + 1)).filter
        (fun d => d ∈ D)).card + 2)).card ∧
    ((Finset.range (n / 2 + 1)).filter
        (fun x => x ∈ A)).card *
      ((Finset.range (n / 2 + 1)).filter
        (fun x => x ∈ A)).card +
    ((Finset.range (n + 1)).filter (fun m =>
      ((Finset.range (m + 1)).filter
        (fun y => y ∈ A ∧ (m - y) ∈ A)).card ≤
      2 * ((Finset.range (n + 1)).filter
        (fun d => d ∈ D)).card + 2)).card *
      (((Finset.range (n + 1)).filter
        (fun x => x ∈ A)).card -
       (2 * ((Finset.range (n + 1)).filter
        (fun d => d ∈ D)).card + 2)) ≤
    (n + 1) * ((Finset.range (n + 1)).filter
      (fun x => x ∈ A)).card := by
  constructor
  · have hemb := poor_count_of_failing hfailn
    have hsplit : ((Finset.range (n + 1)).filter
        (fun x => x ∈ A)).card ≤
        ((Finset.range (n + 1)).filter
          (fun x => x ∈ A ∧ x ∉ D)).card +
        ((Finset.range (n + 1)).filter
          (fun d => d ∈ D)).card := by
      have hsub : (Finset.range (n + 1)).filter
          (fun x => x ∈ A) ⊆
          ((Finset.range (n + 1)).filter
            (fun x => x ∈ A ∧ x ∉ D)) ∪
          ((Finset.range (n + 1)).filter (fun d => d ∈ D)) := by
        intro x hx
        rw [Finset.mem_filter] at hx
        by_cases hxD : x ∈ D
        · exact Finset.mem_union_right _
            (Finset.mem_filter.2 ⟨hx.1, hxD⟩)
        · exact Finset.mem_union_left _
            (Finset.mem_filter.2 ⟨hx.1, hx.2, hxD⟩)
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le
        ((Finset.range (n + 1)).filter
          (fun x => x ∈ A ∧ x ∉ D))
        ((Finset.range (n + 1)).filter (fun d => d ∈ D))
      omega
    omega
  · set Af := (Finset.range (n + 1)).filter (fun x => x ∈ A)
      with hAf
    set A2f := (Finset.range (n / 2 + 1)).filter
      (fun x => x ∈ A) with hA2f
    set DFf := (Finset.range (n + 1)).filter (fun d => d ∈ D)
      with hDFf
    set r2f : ℕ → ℕ := fun m => ((Finset.range (m + 1)).filter
      (fun y => y ∈ A ∧ (m - y) ∈ A)).card with hr2f
    set C := 2 * DFf.card + 2 with hC
    set Poor := (Finset.range (n + 1)).filter
      (fun m => r2f m ≤ C) with hPoor
    have hsumlow : A2f.card * A2f.card ≤
        (Finset.range (n + 1)).sum r2f := by
      have hkey : (A2f ×ˢ A2f).card ≤
          ((Finset.range (n + 1)).sigma (fun m =>
            (Finset.range (m + 1)).filter
              (fun y => y ∈ A ∧ (m - y) ∈ A))).card := by
        apply Finset.card_le_card_of_injOn
          (fun p => (⟨p.1 + p.2, p.1⟩ : Σ _ : ℕ, ℕ))
        · intro p hp
          rw [Finset.mem_coe, Finset.mem_product] at hp
          obtain ⟨hp1, hp2⟩ := hp
          rw [hA2f, Finset.mem_filter, Finset.mem_range] at hp1
          rw [hA2f, Finset.mem_filter, Finset.mem_range] at hp2
          rw [Finset.mem_coe, Finset.mem_sigma]
          constructor
          · show p.1 + p.2 ∈ Finset.range (n + 1)
            rw [Finset.mem_range]
            omega
          · show p.1 ∈ (Finset.range (p.1 + p.2 + 1)).filter
              (fun y => y ∈ A ∧ (p.1 + p.2 - y) ∈ A)
            rw [Finset.mem_filter, Finset.mem_range]
            refine ⟨by omega, hp1.2, ?_⟩
            have he : p.1 + p.2 - p.1 = p.2 := by omega
            rw [he]
            exact hp2.2
        · intro p hp q hq hpq
          have h1 : p.1 + p.2 = q.1 + q.2 :=
            congrArg Sigma.fst hpq
          have h2 : p.1 = q.1 := congrArg Sigma.snd hpq
          exact Prod.ext h2 (by omega)
      rw [Finset.card_product, Finset.card_sigma] at hkey
      exact hkey
    have hsumsplit := Finset.sum_filter_add_sum_filter_not
      (Finset.range (n + 1)) (fun m => r2f m ≤ C) r2f
    have hpoorsum : Poor.sum r2f ≤ Poor.card * C := by
      rw [← smul_eq_mul]
      apply Finset.sum_le_card_nsmul
      intro m hm
      rw [hPoor, Finset.mem_filter] at hm
      exact hm.2
    have hrestsum : ((Finset.range (n + 1)).filter
        (fun m => ¬r2f m ≤ C)).sum r2f ≤
        ((Finset.range (n + 1)).filter
          (fun m => ¬r2f m ≤ C)).card * Af.card := by
      rw [← smul_eq_mul]
      apply Finset.sum_le_card_nsmul
      intro m hm
      rw [Finset.mem_filter, Finset.mem_range] at hm
      show r2f m ≤ Af.card
      rw [hr2f]
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_filter, Finset.mem_range] at hx
      rw [hAf, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hx.2.1⟩
    have hcards := Finset.card_filter_add_card_filter_not
      (s := Finset.range (n + 1)) (p := fun m => r2f m ≤ C)
    rw [Finset.card_range] at hcards
    have hcards2 : Poor.card + ((Finset.range (n + 1)).filter
        (fun m => ¬r2f m ≤ C)).card = n + 1 := hcards
    have hsumsplit2 : Poor.sum r2f +
        ((Finset.range (n + 1)).filter
          (fun m => ¬r2f m ≤ C)).sum r2f =
        (Finset.range (n + 1)).sum r2f := hsumsplit
    have hA2sub : A2f.card ≤ Af.card := by
      apply Finset.card_le_card
      intro x hx
      rw [hA2f, Finset.mem_filter, Finset.mem_range] at hx
      rw [hAf, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hx.2⟩
    have hA2n : A2f.card ≤ n + 1 := by
      rw [hA2f]
      have h := Finset.card_filter_le (Finset.range (n / 2 + 1))
        (fun x => x ∈ A)
      rw [Finset.card_range] at h
      omega
    show A2f.card * A2f.card + Poor.card * (Af.card - C) ≤
      (n + 1) * Af.card
    rcases Nat.le_total C Af.card with hCα | hCα
    · have hmul1 : Poor.card * (Af.card - C) + Poor.card * C =
          Poor.card * Af.card := by
        have h7 : Af.card - C + C = Af.card := by omega
        rw [← Nat.mul_add, h7]
      have hPn : Poor.card ≤ n + 1 := by omega
      have hmul2 : Poor.card * Af.card +
          ((n + 1) - Poor.card) * Af.card =
          (n + 1) * Af.card := by
        have h8 : Poor.card + ((n + 1) - Poor.card) = n + 1 :=
          by omega
        rw [← Nat.add_mul, h8]
      have hrestcard : ((Finset.range (n + 1)).filter
          (fun m => ¬r2f m ≤ C)).card =
          (n + 1) - Poor.card := by omega
      rw [hrestcard] at hrestsum
      omega
    · have hzero : Af.card - C = 0 := by omega
      rw [hzero, Nat.mul_zero, Nat.add_zero]
      calc A2f.card * A2f.card ≤ (n + 1) * A2f.card :=
            Nat.mul_le_mul_right _ hA2n
        _ ≤ (n + 1) * Af.card :=
            Nat.mul_le_mul_left _ hA2sub

open Classical in

theorem combined_law {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ((∃ L, ∀ N, ∃ n, N ≤ n ∧
      ((Finset.range (n + 1)).filter
        (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ L) ∧
     (∀ C N, ∃ v, N ≤ v ∧ C ≤
      ((Finset.range (v + 1)).filter
        (fun x => x ∈ A ∧ (v - x) ∈ A)).card)) ∧
    ((∃ d, 1 ≤ d ∧ ∀ N, ∃ a, N ≤ a ∧ a ∈ A ∧ a + d ∈ A) ∨
     (∃ L u W, u ≤ W ∧ ∀ N, ∃ n, N ≤ n ∧
       ((Finset.range (n + 1)).filter
         (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ 2 * L ∧
       (u ∈ A ∧ (n - u) ∈ A ∧ 2 * u ≤ n) ∧
       ∀ x, x ≤ W → x ≠ u →
         ¬(x ∈ A ∧ (n - x) ∈ A ∧ 2 * x ≤ n)) ∨
     (∃ L, ∀ W N, ∃ n, N ≤ n ∧
       ((Finset.range (n + 1)).filter
         (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ 2 * L ∧
       ∀ x, x ≤ W → ¬(x ∈ A ∧ (n - x) ∈ A ∧ 2 * x ≤ n))) ∧
    (∀ B ⊆ A, B.Infinite → ∀ N, ∃ n, N ≤ n ∧
      (((Finset.range (n + 1)).filter
          (fun x => x ∈ A)).card -
        ((Finset.range (n + 1)).filter
          (fun d => d ∈ B)).card ≤
       ((Finset.range (n + 1)).filter (fun m =>
         ((Finset.range (m + 1)).filter
           (fun y => y ∈ A ∧ (m - y) ∈ A)).card ≤
         2 * ((Finset.range (n + 1)).filter
           (fun d => d ∈ B)).card + 2)).card) ∧
      ((Finset.range (n / 2 + 1)).filter
          (fun x => x ∈ A)).card *
        ((Finset.range (n / 2 + 1)).filter
          (fun x => x ∈ A)).card +
      ((Finset.range (n + 1)).filter (fun m =>
        ((Finset.range (m + 1)).filter
          (fun y => y ∈ A ∧ (m - y) ∈ A)).card ≤
        2 * ((Finset.range (n + 1)).filter
          (fun d => d ∈ B)).card + 2)).card *
        (((Finset.range (n + 1)).filter
          (fun x => x ∈ A)).card -
         (2 * ((Finset.range (n + 1)).filter
          (fun d => d ∈ B)).card + 2)) ≤
      (n + 1) * ((Finset.range (n + 1)).filter
        (fun x => x ∈ A)).card) := by
  refine ⟨⟨poor_stream_of_hfail h0 hcov hfail,
    fun C N => r2_unbounded_of_hfail h0 hcov hfail C N⟩,
    rigidity_trichotomy h0 hcov hfail, ?_⟩
  intro B hBA hBinf N
  have hnot := hfail B hBA hBinf
  simp only [IsExactTupleAsymptoticBasis, not_exists,
    not_forall] at hnot
  obtain ⟨n, hn, hnrep⟩ := hnot N
  have hfailn : ∀ v : Fin 3 → ℕ, (∀ i, v i ∈ A \ B) →
      ∑ i, v i ≠ n := fun v hv hs => hnrep v ⟨hv, hs⟩
  exact ⟨n, hn, density_law_of_failing hfailn⟩

open Classical in

theorem failing_avoids_wealthy_translates {A D : Set ℕ}
    {n w : ℕ}
    (hfailn : ∀ v : Fin 3 → ℕ, (∀ i, v i ∈ A \ D) →
      ∑ i, v i ≠ n)
    (hwn : w ≤ n)
    (hwealthy : 2 * ((Finset.range (n + 1)).filter
        (fun d => d ∈ D)).card + 2 <
      ((Finset.range (w + 1)).filter
        (fun y => y ∈ A ∧ (w - y) ∈ A)).card) :
    n - w ∉ A ∨ n - w ∈ D := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hxA, hxD⟩ := hcon
  have hcap := fan_poverty_of_failing hfailn (n - w) hxA hxD
    (by omega)
  have he : n - (n - w) = w := by omega
  rw [he] at hcap
  omega

open Classical in

theorem served_targets_never_fail {A D : Set ℕ} {n : ℕ}
    (hserve : ∃ w, w ≤ n ∧ (n - w) ∈ A ∧ (n - w) ∉ D ∧
      2 * ((Finset.range (n + 1)).filter
        (fun d => d ∈ D)).card + 2 <
      ((Finset.range (w + 1)).filter
        (fun y => y ∈ A ∧ (w - y) ∈ A)).card) :
    ¬(∀ v : Fin 3 → ℕ, (∀ i, v i ∈ A \ D) →
      ∑ i, v i ≠ n) := by
  intro hfailn
  obtain ⟨w, hwn, hxA, hxD, hwealthy⟩ := hserve
  rcases failing_avoids_wealthy_translates hfailn hwn
    hwealthy with h | h
  · exact h hxA
  · exact hxD h

open Classical in

theorem coverage_breakdown_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ B ⊆ A, B.Infinite → ∀ N, ∃ n, N ≤ n ∧
      ∀ w, w ≤ n →
        2 * ((Finset.range (n + 1)).filter
          (fun d => d ∈ B)).card + 2 <
        ((Finset.range (w + 1)).filter
          (fun y => y ∈ A ∧ (w - y) ∈ A)).card →
        (n - w) ∉ A ∨ (n - w) ∈ B := by
  intro B hBA hBinf N
  have hnot := hfail B hBA hBinf
  simp only [IsExactTupleAsymptoticBasis, not_exists,
    not_forall] at hnot
  obtain ⟨n, hn, hnrep⟩ := hnot N
  have hfailn : ∀ v : Fin 3 → ℕ, (∀ i, v i ∈ A \ B) →
      ∑ i, v i ≠ n := fun v hv hs => hnrep v ⟨hv, hs⟩
  exact ⟨n, hn, fun w hwn hwealthy =>
    failing_avoids_wealthy_translates hfailn hwn hwealthy⟩

open Classical in

theorem pair_energy_lower_bound {A : Set ℕ} (n : ℕ) :
    (((Finset.range (n / 2 + 1)).filter
      (fun x => x ∈ A)).card) ^ 4 ≤
    (n + 1) * (Finset.range (n + 1)).sum (fun m =>
      ((Finset.range (m + 1)).filter
        (fun y => y ∈ A ∧ (m - y) ∈ A)).card ^ 2) := by
  set A2f := (Finset.range (n / 2 + 1)).filter
    (fun x => x ∈ A) with hA2f
  set r2f : ℕ → ℕ := fun m => ((Finset.range (m + 1)).filter
    (fun y => y ∈ A ∧ (m - y) ∈ A)).card with hr2f
  have hsumlow : A2f.card * A2f.card ≤
      (Finset.range (n + 1)).sum r2f := by
    have hkey : (A2f ×ˢ A2f).card ≤
        ((Finset.range (n + 1)).sigma (fun m =>
          (Finset.range (m + 1)).filter
            (fun y => y ∈ A ∧ (m - y) ∈ A))).card := by
      apply Finset.card_le_card_of_injOn
        (fun p => (⟨p.1 + p.2, p.1⟩ : Σ _ : ℕ, ℕ))
      · intro p hp
        rw [Finset.mem_coe, Finset.mem_product] at hp
        obtain ⟨hp1, hp2⟩ := hp
        rw [hA2f, Finset.mem_filter, Finset.mem_range] at hp1
        rw [hA2f, Finset.mem_filter, Finset.mem_range] at hp2
        rw [Finset.mem_coe, Finset.mem_sigma]
        constructor
        · show p.1 + p.2 ∈ Finset.range (n + 1)
          rw [Finset.mem_range]
          omega
        · show p.1 ∈ (Finset.range (p.1 + p.2 + 1)).filter
            (fun y => y ∈ A ∧ (p.1 + p.2 - y) ∈ A)
          rw [Finset.mem_filter, Finset.mem_range]
          refine ⟨by omega, hp1.2, ?_⟩
          have he : p.1 + p.2 - p.1 = p.2 := by omega
          rw [he]
          exact hp2.2
      · intro p hp q hq hpq
        have h1 : p.1 + p.2 = q.1 + q.2 :=
          congrArg Sigma.fst hpq
        have h2 : p.1 = q.1 := congrArg Sigma.snd hpq
        exact Prod.ext h2 (by omega)
    rw [Finset.card_product, Finset.card_sigma] at hkey
    exact hkey
  have hCS : ((Finset.range (n + 1)).sum r2f) ^ 2 ≤
      (n + 1) * (Finset.range (n + 1)).sum
        (fun m => r2f m ^ 2) := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := Finset.range (n + 1)) (f := r2f)
    rw [Finset.card_range] at h
    exact h
  have hfour : A2f.card ^ 4 = (A2f.card * A2f.card) ^ 2 := by
    ring
  calc A2f.card ^ 4 = (A2f.card * A2f.card) ^ 2 := hfour
    _ ≤ ((Finset.range (n + 1)).sum r2f) ^ 2 :=
        Nat.pow_le_pow_left hsumlow 2
    _ ≤ (n + 1) * (Finset.range (n + 1)).sum
        (fun m => r2f m ^ 2) := hCS

open Classical in

theorem wealthy_count_bound {A : Set ℕ} (n C : ℕ) :
    (((Finset.range (n / 2 + 1)).filter
      (fun x => x ∈ A)).card) ^ 4 ≤
    (n + 1) * ((n + 1) * C ^ 2 +
      ((Finset.range (n + 1)).filter (fun m =>
        C < ((Finset.range (m + 1)).filter
          (fun y => y ∈ A ∧ (m - y) ∈ A)).card)).card *
      (((Finset.range (n + 1)).filter
        (fun x => x ∈ A)).card) ^ 2) := by
  set Af := (Finset.range (n + 1)).filter (fun x => x ∈ A)
    with hAf
  set r2f : ℕ → ℕ := fun m => ((Finset.range (m + 1)).filter
    (fun y => y ∈ A ∧ (m - y) ∈ A)).card with hr2f
  set Wf := (Finset.range (n + 1)).filter
    (fun m => C < r2f m) with hWf
  have henergy := pair_energy_lower_bound (A := A) n
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.range (n + 1)) (fun m => C < r2f m)
    (fun m => r2f m ^ 2)
  have hsplit2 : Wf.sum (fun m => r2f m ^ 2) +
      ((Finset.range (n + 1)).filter
        (fun m => ¬C < r2f m)).sum (fun m => r2f m ^ 2) =
      (Finset.range (n + 1)).sum (fun m => r2f m ^ 2) :=
    hsplit
  have hr2le : ∀ m, m ≤ n → r2f m ≤ Af.card := by
    intro m hm
    rw [hr2f]
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_filter, Finset.mem_range] at hx
    rw [hAf, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hx.2.1⟩
  have hwealthy_sum : Wf.sum (fun m => r2f m ^ 2) ≤
      Wf.card * Af.card ^ 2 := by
    rw [← smul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro m hm
    rw [hWf, Finset.mem_filter, Finset.mem_range] at hm
    exact Nat.pow_le_pow_left (hr2le m (by omega)) 2
  have hpoor_sum : ((Finset.range (n + 1)).filter
      (fun m => ¬C < r2f m)).sum (fun m => r2f m ^ 2) ≤
      ((Finset.range (n + 1)).filter
        (fun m => ¬C < r2f m)).card * C ^ 2 := by
    rw [← smul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro m hm
    rw [Finset.mem_filter] at hm
    exact Nat.pow_le_pow_left (by omega) 2
  have hpoor_card : ((Finset.range (n + 1)).filter
      (fun m => ¬C < r2f m)).card ≤ n + 1 := by
    have := Finset.card_filter_le (Finset.range (n + 1))
      (fun m => ¬C < r2f m)
    rw [Finset.card_range] at this
    exact this
  have htotal : (Finset.range (n + 1)).sum
      (fun m => r2f m ^ 2) ≤
      (n + 1) * C ^ 2 + Wf.card * Af.card ^ 2 := by
    have h1 : ((Finset.range (n + 1)).filter
        (fun m => ¬C < r2f m)).card * C ^ 2 ≤
        (n + 1) * C ^ 2 :=
      Nat.mul_le_mul_right _ hpoor_card
    omega
  calc (((Finset.range (n / 2 + 1)).filter
      (fun x => x ∈ A)).card) ^ 4 ≤
      (n + 1) * (Finset.range (n + 1)).sum
        (fun m => r2f m ^ 2) := henergy
    _ ≤ (n + 1) * ((n + 1) * C ^ 2 +
        Wf.card * Af.card ^ 2) :=
      Nat.mul_le_mul_left _ htotal

open Classical in

theorem covering_sqrt_growth {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀) :
    ∀ X, X ≤ ((Finset.range (X + 1)).filter
      (fun x => x ∈ A)).card ^ 2 + N₀ := by
  intro X
  rcases Nat.lt_or_ge X N₀ with hXN | hXN
  · omega
  set Af := (Finset.range (X + 1)).filter (fun x => x ∈ A)
    with hAf
  have hpair : ∀ m, ∃ p : ℕ × ℕ, N₀ ≤ m →
      p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = m := by
    intro m
    by_cases hm : N₀ ≤ m
    · obtain ⟨x, hx, y, hy, hxy⟩ := hcov m hm
      exact ⟨(x, y), fun _ => ⟨hx, hy, hxy⟩⟩
    · exact ⟨(0, 0), fun h => absurd h hm⟩
  choose f hf using hpair
  have hinj : (Finset.Icc N₀ X).card ≤ (Af ×ˢ Af).card := by
    apply Finset.card_le_card_of_injOn f
    · intro m hm
      have hm' := hm
      rw [Finset.mem_coe, Finset.mem_Icc] at hm'
      rw [Finset.mem_coe, Finset.mem_product]
      obtain ⟨h1, h2, h3⟩ := hf m hm'.1
      constructor
      · rw [hAf, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, h1⟩
      · rw [hAf, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, h2⟩
    · intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_Icc] at ha hb
      obtain ⟨-, -, h3a⟩ := hf a ha.1
      obtain ⟨-, -, h3b⟩ := hf b hb.1
      rw [hab] at h3a
      omega
  rw [Finset.card_product, Nat.card_Icc] at hinj
  have hsq : Af.card * Af.card = Af.card ^ 2 := by ring
  omega
open Classical Pointwise in

theorem window_energy_le_addEnergy {A : Set ℕ} (n : ℕ) :
    (Finset.range (n + 1)).sum (fun m =>
      ((Finset.range (m + 1)).filter
        (fun y => y ∈ A ∧ (m - y) ∈ A)).card ^ 2) ≤
    Finset.addEnergy ((Finset.range (n + 1)).filter
      (fun x => x ∈ A))
      ((Finset.range (n + 1)).filter (fun x => x ∈ A)) := by
  set Af := (Finset.range (n + 1)).filter (fun x => x ∈ A)
    with hAf
  rw [Finset.addEnergy_eq_sum_sq']
  have hfiber : ∀ m, m ≤ n →
      ((Finset.range (m + 1)).filter
        (fun y => y ∈ A ∧ (m - y) ∈ A)).card =
      ((Af ×ˢ Af).filter
        (fun xy => xy.1 + xy.2 = m)).card := by
    intro m hm
    apply Finset.card_bij' (fun x _ => (x, m - x))
      (fun xy _ => xy.1)
    · intro x hx
      rw [Finset.mem_filter, Finset.mem_range] at hx
      rw [Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨?_, ?_⟩, by omega⟩
      · rw [hAf, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hx.2.1⟩
      · rw [hAf, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hx.2.2⟩
    · intro xy hxy
      rw [Finset.mem_filter, Finset.mem_product] at hxy
      obtain ⟨⟨h1, h2⟩, h3⟩ := hxy
      rw [hAf, Finset.mem_filter, Finset.mem_range] at h1
      rw [hAf, Finset.mem_filter, Finset.mem_range] at h2
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, h1.2, ?_⟩
      have he : m - xy.1 = xy.2 := by omega
      rw [he]
      exact h2.2
    · intro x hx
      rfl
    · intro xy hxy
      rw [Finset.mem_filter, Finset.mem_product] at hxy
      obtain ⟨⟨h1, h2⟩, h3⟩ := hxy
      have he : m - xy.1 = xy.2 := by omega
      exact Prod.ext rfl he
  have hrw : (Finset.range (n + 1)).sum (fun m =>
      ((Finset.range (m + 1)).filter
        (fun y => y ∈ A ∧ (m - y) ∈ A)).card ^ 2) =
      (Finset.range (n + 1)).sum (fun m =>
        ((Af ×ˢ Af).filter
          (fun xy => xy.1 + xy.2 = m)).card ^ 2) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_range] at hm
    rw [hfiber m (by omega)]
  rw [hrw]
  apply Finset.sum_le_sum_of_ne_zero
  intro m hm hne
  have hpos : 0 < ((Af ×ˢ Af).filter
      (fun xy => xy.1 + xy.2 = m)).card := by
    rcases Nat.eq_zero_or_pos ((Af ×ˢ Af).filter
        (fun xy => xy.1 + xy.2 = m)).card with h | h
    · rw [h] at hne
      simp at hne
    · exact h
  rw [Finset.card_pos] at hpos
  obtain ⟨xy, hxy⟩ := hpos
  rw [Finset.mem_filter, Finset.mem_product] at hxy
  obtain ⟨⟨h1, h2⟩, h3⟩ := hxy
  rw [← h3]
  exact Finset.add_mem_add h1 h2

open Classical Pointwise in

theorem mathlib_energy_floor {A : Set ℕ} (n : ℕ) :
    (((Finset.range (n + 1)).filter
      (fun x => x ∈ A)).card) ^ 2 *
    (((Finset.range (n + 1)).filter
      (fun x => x ∈ A)).card) ^ 2 ≤
    (2 * n + 1) * Finset.addEnergy
      ((Finset.range (n + 1)).filter (fun x => x ∈ A))
      ((Finset.range (n + 1)).filter (fun x => x ∈ A)) := by
  set Af := (Finset.range (n + 1)).filter (fun x => x ∈ A)
    with hAf
  have hle := Finset.le_card_add_mul_addEnergy Af Af
  have hsub : Af + Af ⊆ Finset.range (2 * n + 1) := by
    intro z hz
    rw [Finset.mem_add] at hz
    obtain ⟨a, ha, b, hb, hab⟩ := hz
    rw [hAf, Finset.mem_filter, Finset.mem_range] at ha
    rw [hAf, Finset.mem_filter, Finset.mem_range] at hb
    rw [Finset.mem_range]
    omega
  have hcard : (Af + Af).card ≤ 2 * n + 1 := by
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    exact this
  calc Af.card ^ 2 * Af.card ^ 2 ≤
      (Af + Af).card * Finset.addEnergy Af Af := hle
    _ ≤ (2 * n + 1) * Finset.addEnergy Af Af :=
      Nat.mul_le_mul_right _ hcard

open Classical Pointwise in

theorem energy_upper_half_floor {A : Set ℕ} (n : ℕ) :
    (((Finset.range (n + 1)).filter
      (fun x => x ∈ A)).card) ^ 2 *
    (((Finset.range (n + 1)).filter
      (fun x => x ∈ A)).card) ^ 2 ≤
    (2 * n + 1) *
      ((Finset.range (n + 1)).sum (fun m =>
        ((Finset.range (m + 1)).filter
          (fun y => y ∈ A ∧ (m - y) ∈ A)).card ^ 2) +
      ((((Finset.range (n + 1)).filter (fun x => x ∈ A)) +
        ((Finset.range (n + 1)).filter (fun x => x ∈ A))).filter
          (fun a => n < a)).sum (fun a =>
        (((((Finset.range (n + 1)).filter (fun x => x ∈ A)) ×ˢ
           ((Finset.range (n + 1)).filter (fun x => x ∈ A))).filter
          (fun xy => xy.1 + xy.2 = a)).card) ^ 2)) := by
  set Af := (Finset.range (n + 1)).filter (fun x => x ∈ A)
    with hAf
  have hfloor := mathlib_energy_floor (A := A) n
  have hE : Finset.addEnergy Af Af =
      (Af + Af).sum (fun a =>
        ((Af ×ˢ Af).filter
          (fun xy => xy.1 + xy.2 = a)).card ^ 2) := by
    rw [Finset.addEnergy_eq_sum_sq']
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Af + Af) (fun a => a ≤ n)
    (fun a => ((Af ×ˢ Af).filter
      (fun xy => xy.1 + xy.2 = a)).card ^ 2)
  have hfiber : ∀ m, m ≤ n →
      ((Af ×ˢ Af).filter
        (fun xy => xy.1 + xy.2 = m)).card =
      ((Finset.range (m + 1)).filter
        (fun y => y ∈ A ∧ (m - y) ∈ A)).card := by
    intro m hm
    apply Finset.card_bij' (fun xy _ => xy.1)
      (fun x _ => (x, m - x))
    · intro xy hxy
      rw [Finset.mem_filter, Finset.mem_product] at hxy
      obtain ⟨⟨h1, h2⟩, h3⟩ := hxy
      rw [hAf, Finset.mem_filter, Finset.mem_range] at h1
      rw [hAf, Finset.mem_filter, Finset.mem_range] at h2
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, h1.2, ?_⟩
      have he : m - xy.1 = xy.2 := by omega
      rw [he]
      exact h2.2
    · intro x hx
      rw [Finset.mem_filter, Finset.mem_range] at hx
      rw [Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨?_, ?_⟩, by omega⟩
      · rw [hAf, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hx.2.1⟩
      · rw [hAf, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hx.2.2⟩
    · intro xy hxy
      rw [Finset.mem_filter, Finset.mem_product] at hxy
      obtain ⟨⟨h1, h2⟩, h3⟩ := hxy
      have he : m - xy.1 = xy.2 := by omega
      exact Prod.ext rfl he
    · intro x hx
      rfl
  have hlow : ((Af + Af).filter (fun a => a ≤ n)).sum
      (fun a => ((Af ×ˢ Af).filter
        (fun xy => xy.1 + xy.2 = a)).card ^ 2) ≤
      (Finset.range (n + 1)).sum (fun m =>
        ((Finset.range (m + 1)).filter
          (fun y => y ∈ A ∧ (m - y) ∈ A)).card ^ 2) := by
    have hcongr : ((Af + Af).filter (fun a => a ≤ n)).sum
        (fun a => ((Af ×ˢ Af).filter
          (fun xy => xy.1 + xy.2 = a)).card ^ 2) =
        ((Af + Af).filter (fun a => a ≤ n)).sum
        (fun a => ((Finset.range (a + 1)).filter
          (fun y => y ∈ A ∧ (a - y) ∈ A)).card ^ 2) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mem_filter] at ha
      rw [hfiber a ha.2]
    rw [hcongr]
    apply Finset.sum_le_sum_of_subset
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_range]
    omega
  have hupper_eq : ((Af + Af).filter (fun a => ¬a ≤ n)).sum
      (fun a => ((Af ×ˢ Af).filter
        (fun xy => xy.1 + xy.2 = a)).card ^ 2) =
      ((Af + Af).filter (fun a => n < a)).sum
      (fun a => ((Af ×ˢ Af).filter
        (fun xy => xy.1 + xy.2 = a)).card ^ 2) := by
    apply Finset.sum_congr
    · apply Finset.filter_congr
      intro a ha
      constructor
      · intro h
        omega
      · intro h
        omega
    · intro a ha
      rfl
  have hEle : Finset.addEnergy Af Af ≤
      (Finset.range (n + 1)).sum (fun m =>
        ((Finset.range (m + 1)).filter
          (fun y => y ∈ A ∧ (m - y) ∈ A)).card ^ 2) +
      ((Af + Af).filter (fun a => n < a)).sum
        (fun a => ((Af ×ˢ Af).filter
          (fun xy => xy.1 + xy.2 = a)).card ^ 2) := by
    rw [hE, ← hsplit, hupper_eq]
    omega
  calc Af.card ^ 2 * Af.card ^ 2 ≤
      (2 * n + 1) * Finset.addEnergy Af Af := hfloor
    _ ≤ (2 * n + 1) * _ := Nat.mul_le_mul_left _ hEle

open Classical Pointwise in

theorem iteration_law {A : Set ℕ} (n C : ℕ) :
    (((Finset.range (n + 1)).filter
      (fun x => x ∈ A)).card) ^ 2 *
    (((Finset.range (n + 1)).filter
      (fun x => x ∈ A)).card) ^ 2 ≤
    (2 * n + 1) * ((n + 1) * C ^ 2 +
      ((Finset.range (n + 1)).filter (fun m =>
        C < ((Finset.range (m + 1)).filter
          (fun y => y ∈ A ∧ (m - y) ∈ A)).card)).card *
      (((Finset.range (n + 1)).filter
        (fun x => x ∈ A)).card) ^ 2 +
      ((((Finset.range (n + 1)).filter (fun x => x ∈ A)) +
        ((Finset.range (n + 1)).filter (fun x => x ∈ A))).filter
          (fun a => n < a)).sum (fun a =>
        (((((Finset.range (n + 1)).filter (fun x => x ∈ A)) ×ˢ
           ((Finset.range (n + 1)).filter (fun x => x ∈ A))).filter
          (fun xy => xy.1 + xy.2 = a)).card) ^ 2)) := by
  set Af := (Finset.range (n + 1)).filter (fun x => x ∈ A)
    with hAf
  set r2f : ℕ → ℕ := fun m => ((Finset.range (m + 1)).filter
    (fun y => y ∈ A ∧ (m - y) ∈ A)).card with hr2f
  set Wf := (Finset.range (n + 1)).filter
    (fun m => C < r2f m) with hWf
  have hfloor := energy_upper_half_floor (A := A) n
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.range (n + 1)) (fun m => C < r2f m)
    (fun m => r2f m ^ 2)
  have hsplit2 : Wf.sum (fun m => r2f m ^ 2) +
      ((Finset.range (n + 1)).filter
        (fun m => ¬C < r2f m)).sum (fun m => r2f m ^ 2) =
      (Finset.range (n + 1)).sum (fun m => r2f m ^ 2) :=
    hsplit
  have hr2le : ∀ m, m ≤ n → r2f m ≤ Af.card := by
    intro m hm
    rw [hr2f]
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_filter, Finset.mem_range] at hx
    rw [hAf, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hx.2.1⟩
  have hwealthy_sum : Wf.sum (fun m => r2f m ^ 2) ≤
      Wf.card * Af.card ^ 2 := by
    rw [← smul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro m hm
    rw [hWf, Finset.mem_filter, Finset.mem_range] at hm
    exact Nat.pow_le_pow_left (hr2le m (by omega)) 2
  have hpoor_sum : ((Finset.range (n + 1)).filter
      (fun m => ¬C < r2f m)).sum (fun m => r2f m ^ 2) ≤
      (n + 1) * C ^ 2 := by
    have h1 : ((Finset.range (n + 1)).filter
        (fun m => ¬C < r2f m)).sum (fun m => r2f m ^ 2) ≤
        ((Finset.range (n + 1)).filter
          (fun m => ¬C < r2f m)).card * C ^ 2 := by
      rw [← smul_eq_mul]
      apply Finset.sum_le_card_nsmul
      intro m hm
      rw [Finset.mem_filter] at hm
      exact Nat.pow_le_pow_left (by omega) 2
    have h2 : ((Finset.range (n + 1)).filter
        (fun m => ¬C < r2f m)).card ≤ n + 1 := by
      have := Finset.card_filter_le (Finset.range (n + 1))
        (fun m => ¬C < r2f m)
      rw [Finset.card_range] at this
      exact this
    have h3 : ((Finset.range (n + 1)).filter
        (fun m => ¬C < r2f m)).card * C ^ 2 ≤
        (n + 1) * C ^ 2 := Nat.mul_le_mul_right _ h2
    omega
  have hwindow : (Finset.range (n + 1)).sum
      (fun m => r2f m ^ 2) ≤
      (n + 1) * C ^ 2 + Wf.card * Af.card ^ 2 := by
    omega
  have hfloor2 : Af.card ^ 2 * Af.card ^ 2 ≤
      (2 * n + 1) * ((Finset.range (n + 1)).sum
        (fun m => r2f m ^ 2) +
      ((Af + Af).filter (fun a => n < a)).sum (fun a =>
        (((Af ×ˢ Af).filter
          (fun xy => xy.1 + xy.2 = a)).card) ^ 2)) := hfloor
  refine le_trans hfloor2 ?_
  apply Nat.mul_le_mul_left
  omega

open Classical Pointwise in

theorem upper_le_next_window {A : Set ℕ} (n : ℕ) :
    ((((Finset.range (n + 1)).filter (fun x => x ∈ A)) +
      ((Finset.range (n + 1)).filter (fun x => x ∈ A))).filter
        (fun a => n < a)).sum (fun a =>
      (((((Finset.range (n + 1)).filter (fun x => x ∈ A)) ×ˢ
         ((Finset.range (n + 1)).filter (fun x => x ∈ A))).filter
        (fun xy => xy.1 + xy.2 = a)).card) ^ 2) ≤
    (Finset.range (2 * n + 1)).sum (fun m =>
      ((Finset.range (m + 1)).filter
        (fun y => y ∈ A ∧ (m - y) ∈ A)).card ^ 2) := by
  set Af := (Finset.range (n + 1)).filter (fun x => x ∈ A)
    with hAf
  have hfib : ∀ a, ((Af ×ˢ Af).filter
      (fun xy => xy.1 + xy.2 = a)).card ≤
      ((Finset.range (a + 1)).filter
        (fun y => y ∈ A ∧ (a - y) ∈ A)).card := by
    intro a
    apply Finset.card_le_card_of_injOn (fun xy => xy.1)
    · intro xy hxy
      rw [Finset.mem_coe, Finset.mem_filter,
        Finset.mem_product] at hxy
      obtain ⟨⟨h1, h2⟩, h3⟩ := hxy
      have h3' : xy.1 + xy.2 = a := h3
      rw [hAf, Finset.mem_filter, Finset.mem_range] at h1
      rw [hAf, Finset.mem_filter, Finset.mem_range] at h2
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, h1.2, ?_⟩
      · show xy.1 < a + 1
        omega
      · show (a - xy.1) ∈ A
        have he : a - xy.1 = xy.2 := by omega
        rw [he]
        exact h2.2
    · intro p hp q hq hpq
      rw [Finset.mem_coe, Finset.mem_filter,
        Finset.mem_product] at hp hq
      have h3p : p.1 + p.2 = a := hp.2
      have h3q : q.1 + q.2 = a := hq.2
      have hpq' : p.1 = q.1 := hpq
      refine Prod.ext hpq' ?_
      omega
  calc ((Af + Af).filter (fun a => n < a)).sum (fun a =>
      (((Af ×ˢ Af).filter
        (fun xy => xy.1 + xy.2 = a)).card) ^ 2) ≤
      ((Af + Af).filter (fun a => n < a)).sum (fun a =>
        ((Finset.range (a + 1)).filter
          (fun y => y ∈ A ∧ (a - y) ∈ A)).card ^ 2) := by
        apply Finset.sum_le_sum
        intro a ha
        exact Nat.pow_le_pow_left (hfib a) 2
    _ ≤ (Finset.range (2 * n + 1)).sum (fun m =>
        ((Finset.range (m + 1)).filter
          (fun y => y ∈ A ∧ (m - y) ∈ A)).card ^ 2) := by
        apply Finset.sum_le_sum_of_subset
        intro a ha
        rw [Finset.mem_filter] at ha
        obtain ⟨haS, -⟩ := ha
        rw [Finset.mem_add] at haS
        obtain ⟨u, hu, v, hv, huv⟩ := haS
        rw [hAf, Finset.mem_filter, Finset.mem_range] at hu
        rw [hAf, Finset.mem_filter, Finset.mem_range] at hv
        rw [Finset.mem_range]
        omega

open Classical Pointwise in

theorem two_scale_law {A : Set ℕ} (n C : ℕ) :
    (((Finset.range (n + 1)).filter
      (fun x => x ∈ A)).card) ^ 2 *
    (((Finset.range (n + 1)).filter
      (fun x => x ∈ A)).card) ^ 2 ≤
    (2 * n + 1) * ((n + 1) * C ^ 2 +
      ((Finset.range (n + 1)).filter (fun m =>
        C < ((Finset.range (m + 1)).filter
          (fun y => y ∈ A ∧ (m - y) ∈ A)).card)).card *
      (((Finset.range (n + 1)).filter
        (fun x => x ∈ A)).card) ^ 2 +
      (Finset.range (2 * n + 1)).sum (fun m =>
        ((Finset.range (m + 1)).filter
          (fun y => y ∈ A ∧ (m - y) ∈ A)).card ^ 2)) := by
  have hc := iteration_law (A := A) n C
  have hu := upper_le_next_window (A := A) n
  refine le_trans hc ?_
  apply Nat.mul_le_mul_left
  omega

open Classical in

theorem window_partition {A : Set ℕ} (n C : ℕ) :
    (Finset.range (n + 1)).sum (fun m =>
      ((Finset.range (m + 1)).filter
        (fun y => y ∈ A ∧ (m - y) ∈ A)).card ^ 2) ≤
    (n + 1) * C ^ 2 +
    ((Finset.range (n + 1)).filter (fun m =>
      C < ((Finset.range (m + 1)).filter
        (fun y => y ∈ A ∧ (m - y) ∈ A)).card)).card *
    (((Finset.range (n + 1)).filter
      (fun x => x ∈ A)).card) ^ 2 := by
  set Af := (Finset.range (n + 1)).filter (fun x => x ∈ A)
    with hAf
  set r2f : ℕ → ℕ := fun m => ((Finset.range (m + 1)).filter
    (fun y => y ∈ A ∧ (m - y) ∈ A)).card with hr2f
  set Wf := (Finset.range (n + 1)).filter
    (fun m => C < r2f m) with hWf
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.range (n + 1)) (fun m => C < r2f m)
    (fun m => r2f m ^ 2)
  have hsplit2 : Wf.sum (fun m => r2f m ^ 2) +
      ((Finset.range (n + 1)).filter
        (fun m => ¬C < r2f m)).sum (fun m => r2f m ^ 2) =
      (Finset.range (n + 1)).sum (fun m => r2f m ^ 2) :=
    hsplit
  have hr2le : ∀ m, m ≤ n → r2f m ≤ Af.card := by
    intro m hm
    rw [hr2f]
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_filter, Finset.mem_range] at hx
    rw [hAf, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hx.2.1⟩
  have hwealthy_sum : Wf.sum (fun m => r2f m ^ 2) ≤
      Wf.card * Af.card ^ 2 := by
    rw [← smul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro m hm
    rw [hWf, Finset.mem_filter, Finset.mem_range] at hm
    exact Nat.pow_le_pow_left (hr2le m (by omega)) 2
  have hpoor_sum : ((Finset.range (n + 1)).filter
      (fun m => ¬C < r2f m)).sum (fun m => r2f m ^ 2) ≤
      (n + 1) * C ^ 2 := by
    have h1 : ((Finset.range (n + 1)).filter
        (fun m => ¬C < r2f m)).sum (fun m => r2f m ^ 2) ≤
        ((Finset.range (n + 1)).filter
          (fun m => ¬C < r2f m)).card * C ^ 2 := by
      rw [← smul_eq_mul]
      apply Finset.sum_le_card_nsmul
      intro m hm
      rw [Finset.mem_filter] at hm
      exact Nat.pow_le_pow_left (by omega) 2
    have h2 : ((Finset.range (n + 1)).filter
        (fun m => ¬C < r2f m)).card ≤ n + 1 := by
      have := Finset.card_filter_le (Finset.range (n + 1))
        (fun m => ¬C < r2f m)
      rw [Finset.card_range] at this
      exact this
    have h3 : ((Finset.range (n + 1)).filter
        (fun m => ¬C < r2f m)).card * C ^ 2 ≤
        (n + 1) * C ^ 2 := Nat.mul_le_mul_right _ h2
    omega
  show (Finset.range (n + 1)).sum (fun m => r2f m ^ 2) ≤
    (n + 1) * C ^ 2 + Wf.card * Af.card ^ 2
  omega

open Classical in

theorem two_scale_closed {A : Set ℕ} (n C C' : ℕ) :
    (((Finset.range (n + 1)).filter
      (fun x => x ∈ A)).card) ^ 2 *
    (((Finset.range (n + 1)).filter
      (fun x => x ∈ A)).card) ^ 2 ≤
    (2 * n + 1) * ((n + 1) * C ^ 2 +
      ((Finset.range (n + 1)).filter (fun m =>
        C < ((Finset.range (m + 1)).filter
          (fun y => y ∈ A ∧ (m - y) ∈ A)).card)).card *
      (((Finset.range (n + 1)).filter
        (fun x => x ∈ A)).card) ^ 2 +
      ((2 * n + 1) * C' ^ 2 +
      ((Finset.range (2 * n + 1)).filter (fun m =>
        C' < ((Finset.range (m + 1)).filter
          (fun y => y ∈ A ∧ (m - y) ∈ A)).card)).card *
      (((Finset.range (2 * n + 1)).filter
        (fun x => x ∈ A)).card) ^ 2)) := by
  have h2s := two_scale_law (A := A) n C
  have hw := window_partition (A := A) (2 * n) C'
  refine le_trans h2s ?_
  apply Nat.mul_le_mul_left
  have hrw : (2 * n + 1) = 2 * n + 1 := rfl
  omega

open Classical in

theorem breakdown_pigeonhole {A D : Set ℕ} {n : ℕ}
    (hbd : ∀ w, w ≤ n →
      2 * ((Finset.range (n + 1)).filter
        (fun d => d ∈ D)).card + 2 <
      ((Finset.range (w + 1)).filter
        (fun y => y ∈ A ∧ (w - y) ∈ A)).card →
      (n - w) ∉ A ∨ (n - w) ∈ D) :
    ((Finset.range (n + 1)).filter
      (fun x => x ∈ A)).card +
    ((Finset.range (n + 1)).filter (fun w =>
      2 * ((Finset.range (n + 1)).filter
        (fun d => d ∈ D)).card + 2 <
      ((Finset.range (w + 1)).filter
        (fun y => y ∈ A ∧ (w - y) ∈ A)).card)).card ≤
    n + 1 + 2 * ((Finset.range (n + 1)).filter
      (fun d => d ∈ D)).card := by
  set DF := (Finset.range (n + 1)).filter (fun d => d ∈ D)
    with hDF
  set Sf := (Finset.range (n + 1)).filter (fun w =>
    2 * DF.card + 2 <
    ((Finset.range (w + 1)).filter
      (fun y => y ∈ A ∧ (w - y) ∈ A)).card) with hSf
  set ADf := (Finset.range (n + 1)).filter
    (fun x => x ∈ A ∧ x ∉ D) with hADf
  set Rf := Sf.image (fun w => n - w) with hRf
  have hRcard : Rf.card = Sf.card := by
    rw [hRf]
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    rw [Finset.mem_coe, hSf, Finset.mem_filter,
      Finset.mem_range] at ha hb
    have hab' : n - a = n - b := hab
    omega
  have hdisj : Disjoint ADf Rf := by
    rw [Finset.disjoint_left]
    intro x hxAD hxR
    rw [hADf, Finset.mem_filter, Finset.mem_range] at hxAD
    rw [hRf, Finset.mem_image] at hxR
    obtain ⟨w, hwS, hwx⟩ := hxR
    rw [hSf, Finset.mem_filter, Finset.mem_range] at hwS
    have hbd' := hbd w (by omega) hwS.2
    rw [hwx] at hbd'
    rcases hbd' with h | h
    · exact h hxAD.2.1
    · exact hxAD.2.2 h
  have hsub : ADf ∪ Rf ⊆ Finset.range (n + 1) := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · rw [hADf, Finset.mem_filter] at h
      exact h.1
    · rw [hRf, Finset.mem_image] at h
      obtain ⟨w, hwS, hwx⟩ := h
      rw [hSf, Finset.mem_filter, Finset.mem_range] at hwS
      rw [Finset.mem_range]
      omega
  have hcard_union : ADf.card + Rf.card ≤ n + 1 := by
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_range] at h1
    exact h1
  have hAD_lower : ((Finset.range (n + 1)).filter
      (fun x => x ∈ A)).card ≤ ADf.card + DF.card := by
    have hsub2 : (Finset.range (n + 1)).filter
        (fun x => x ∈ A) ⊆ ADf ∪ DF := by
      intro x hx
      rw [Finset.mem_filter] at hx
      by_cases hxD : x ∈ D
      · exact Finset.mem_union_right _
          (Finset.mem_filter.2 ⟨hx.1, hxD⟩)
      · exact Finset.mem_union_left _
          (Finset.mem_filter.2 ⟨hx.1, hx.2, hxD⟩)
    have h1 := Finset.card_le_card hsub2
    have h2 := Finset.card_union_le ADf DF
    omega
  show ((Finset.range (n + 1)).filter
    (fun x => x ∈ A)).card + Sf.card ≤ n + 1 + 2 * DF.card
  omega

open Classical in

theorem spike_census_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ B ⊆ A, B.Infinite → ∀ N, ∃ n, N ≤ n ∧
      ((Finset.range (n + 1)).filter
        (fun x => x ∈ A)).card +
      ((Finset.range (n + 1)).filter (fun w =>
        2 * ((Finset.range (n + 1)).filter
          (fun d => d ∈ B)).card + 2 <
        ((Finset.range (w + 1)).filter
          (fun y => y ∈ A ∧ (w - y) ∈ A)).card)).card ≤
      n + 1 + 2 * ((Finset.range (n + 1)).filter
        (fun d => d ∈ B)).card := by
  intro B hBA hBinf N
  obtain ⟨n, hn, hbd⟩ :=
    coverage_breakdown_of_hfail h0 hcov hfail B hBA hBinf N
  exact ⟨n, hn, breakdown_pigeonhole hbd⟩

open Classical in

theorem deletion_criterion {A B : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (h0B : 0 ∉ B) (hcov : PairCovers A N₀)
    (hsplit : ∀ b ∈ B, ∃ u ∈ A, ∃ v ∈ A,
      u ∉ B ∧ v ∉ B ∧ u + v = b)
    (hboth : ∀ x ∈ B, ∀ y ∈ B, N₀ ≤ x + y →
      ∃ p ∈ A, ∃ q ∈ A, ∃ r ∈ A,
        p ∉ B ∧ q ∉ B ∧ r ∉ B ∧ p + q + r = x + y) :
    IsExactTupleAsymptoticBasis (A \ B) 3 := by
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨x, hxA, y, hyA, hxy⟩ := hcov n hn
  by_cases hxB : x ∈ B
  · by_cases hyB : y ∈ B
    · -- both parts deleted: the served triple
      obtain ⟨p, hpA, q, hqA, r, hrA, hpB, hqB, hrB, hsum⟩ :=
        hboth x hxB y hyB (by omega)
      refine ⟨![p, q, r], ?_, ?_⟩
      · intro i
        match i with
        | 0 => exact ⟨hpA, hpB⟩
        | 1 => exact ⟨hqA, hqB⟩
        | 2 => exact ⟨hrA, hrB⟩
      · have he : p + q + r = n := by omega
        simpa [Fin.sum_univ_three] using he
    · -- x deleted, y survives: split x
      obtain ⟨u, huA, v, hvA, huB, hvB, huv⟩ := hsplit x hxB
      refine ⟨![u, v, y], ?_, ?_⟩
      · intro i
        match i with
        | 0 => exact ⟨huA, huB⟩
        | 1 => exact ⟨hvA, hvB⟩
        | 2 => exact ⟨hyA, hyB⟩
      · have he : u + v + y = n := by omega
        simpa [Fin.sum_univ_three] using he
  · by_cases hyB : y ∈ B
    · -- y deleted, x survives: split y
      obtain ⟨u, huA, v, hvA, huB, hvB, huv⟩ := hsplit y hyB
      refine ⟨![x, u, v], ?_, ?_⟩
      · intro i
        match i with
        | 0 => exact ⟨hxA, hxB⟩
        | 1 => exact ⟨huA, huB⟩
        | 2 => exact ⟨hvA, hvB⟩
      · have he : x + u + v = n := by omega
        simpa [Fin.sum_univ_three] using he
    · -- both survive: pad with zero
      refine ⟨![x, y, 0], ?_, ?_⟩
      · intro i
        match i with
        | 0 => exact ⟨hxA, hxB⟩
        | 1 => exact ⟨hyA, hyB⟩
        | 2 => exact ⟨h0, h0B⟩
      · have he : x + y + 0 = n := by omega
        simpa [Fin.sum_univ_three] using he

open Classical in

theorem deletion_exists_of_construction {A : Set ℕ} {N₀ : ℕ}
    {b : ℕ → ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hbA : ∀ k, b k ∈ A) (hbpos : ∀ k, 0 < b k)
    (hbmono : StrictMono b)
    (hsplit : ∀ k, ∃ u ∈ A, ∃ v ∈ A,
      (∀ j, u ≠ b j) ∧ (∀ j, v ≠ b j) ∧ u + v = b k)
    (hboth : ∀ i j, N₀ ≤ b i + b j →
      ∃ p ∈ A, ∃ q ∈ A, ∃ r ∈ A,
        (∀ k, p ≠ b k) ∧ (∀ k, q ≠ b k) ∧ (∀ k, r ≠ b k) ∧
        p + q + r = b i + b j) :
    ∃ B ⊆ A, B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) 3 := by
  refine ⟨Set.range b, ?_, Set.infinite_range_of_injective
    hbmono.injective, ?_⟩
  · rintro x ⟨k, rfl⟩
    exact hbA k
  · have h0B : (0 : ℕ) ∉ Set.range b := by
      rintro ⟨k, hk⟩
      have := hbpos k
      omega
    refine deletion_criterion h0 h0B hcov ?_ ?_
    · rintro x ⟨k, rfl⟩
      obtain ⟨u, huA, v, hvA, hu, hv, huv⟩ := hsplit k
      refine ⟨u, huA, v, hvA, ?_, ?_, huv⟩
      · rintro ⟨j, hj⟩
        exact hu j hj.symm
      · rintro ⟨j, hj⟩
        exact hv j hj.symm
    · rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩ hN
      obtain ⟨p, hpA, q, hqA, r, hrA, hp, hq, hr, hsum⟩ :=
        hboth i j hN
      refine ⟨p, hpA, q, hqA, r, hrA, ?_, ?_, ?_, hsum⟩
      · rintro ⟨k, hk⟩
        exact hp k hk.symm
      · rintro ⟨k, hk⟩
        exact hq k hk.symm
      · rintro ⟨k, hk⟩
        exact hr k hk.symm

open Classical in

theorem sumfree_triple {A : Set ℕ} {N₀ X : ℕ}
    (hcov : PairCovers A N₀)
    (hsf : ∀ a ∈ A, X < a → ∀ u ∈ A, ∀ v ∈ A,
      0 < u → 0 < v → u + v ≠ a)
    {a x : ℕ} (haA : a ∈ A) (hax : X < a)
    (hxA : x ∈ A) (hx0 : 0 < x) (hxa : x < a)
    (hbig : N₀ ≤ a - x) :
    ∃ u ∈ A, ∃ v ∈ A, 0 < u ∧ 0 < v ∧ x + u + v = a := by
  obtain ⟨u, huA, v, hvA, huv⟩ := hcov (a - x) hbig
  have hu0 : 0 < u := by
    rcases Nat.eq_zero_or_pos u with h | h
    · exfalso
      have hvA' : v ∈ A := hvA
      have hveq : v = a - x := by omega
      rw [hveq] at hvA'
      exact hsf a haA hax x hxA (a - x) hvA' hx0 (by omega)
        (by omega)
    · exact h
  have hv0 : 0 < v := by
    rcases Nat.eq_zero_or_pos v with h | h
    · exfalso
      have huA' : u ∈ A := huA
      have hueq : u = a - x := by omega
      rw [hueq] at huA'
      exact hsf a haA hax x hxA (a - x) huA' hx0 (by omega)
        (by omega)
    · exact h
  exact ⟨u, huA, v, hvA, hu0, hv0, by omega⟩

open Classical in

theorem deletion_criterion_sumfree {A B : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (h0B : 0 ∉ B)
    (hserved : ∀ b ∈ B, ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
      x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = b)
    (hcover : ∀ n, N₀ ≤ n → n ∉ A →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) :
    IsExactTupleAsymptoticBasis (A \ B) 3 := by
  refine ⟨N₀, fun n hn => ?_⟩
  by_cases hnA : n ∈ A
  · by_cases hnB : n ∈ B
    · obtain ⟨x, hxA, y, hyA, z, hzA, hxB, hyB, hzB, hsum⟩ :=
        hserved n hnB
      refine ⟨![x, y, z], ?_, ?_⟩
      · intro i
        match i with
        | 0 => exact ⟨hxA, hxB⟩
        | 1 => exact ⟨hyA, hyB⟩
        | 2 => exact ⟨hzA, hzB⟩
      · simpa [Fin.sum_univ_three] using hsum
    · refine ⟨![n, 0, 0], ?_, ?_⟩
      · intro i
        match i with
        | 0 => exact ⟨hnA, hnB⟩
        | 1 => exact ⟨h0, h0B⟩
        | 2 => exact ⟨h0, h0B⟩
      · have he : n + 0 + 0 = n := by omega
        simpa [Fin.sum_univ_three] using he
  · obtain ⟨x, hxA, y, hyA, hxB, hyB, hsum⟩ := hcover n hn hnA
    refine ⟨![x, y, 0], ?_, ?_⟩
    · intro i
      match i with
      | 0 => exact ⟨hxA, hxB⟩
      | 1 => exact ⟨hyA, hyB⟩
      | 2 => exact ⟨h0, h0B⟩
    · have he : x + y + 0 = n := by omega
      simpa [Fin.sum_univ_three] using he

open Classical in

theorem deletion_criterion_local {A B : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (h0B : 0 ∉ B) (hcov : PairCovers A N₀)
    (hrisk : ∀ n, N₀ ≤ n → (∃ b ∈ B, ∃ a ∈ A, b + a = n) →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n) :
    IsExactTupleAsymptoticBasis (A \ B) 3 := by
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨x, hxA, y, hyA, hxy⟩ := hcov n hn
  by_cases hxB : x ∈ B
  · obtain ⟨p, hpA, q, hqA, r, hrA, hpB, hqB, hrB, hsum⟩ :=
      hrisk n hn ⟨x, hxB, y, hyA, hxy⟩
    refine ⟨![p, q, r], ?_, ?_⟩
    · intro i
      match i with
      | 0 => exact ⟨hpA, hpB⟩
      | 1 => exact ⟨hqA, hqB⟩
      | 2 => exact ⟨hrA, hrB⟩
    · simpa [Fin.sum_univ_three] using hsum
  · by_cases hyB : y ∈ B
    · obtain ⟨p, hpA, q, hqA, r, hrA, hpB, hqB, hrB, hsum⟩ :=
        hrisk n hn ⟨y, hyB, x, hxA, by omega⟩
      refine ⟨![p, q, r], ?_, ?_⟩
      · intro i
        match i with
        | 0 => exact ⟨hpA, hpB⟩
        | 1 => exact ⟨hqA, hqB⟩
        | 2 => exact ⟨hrA, hrB⟩
      · simpa [Fin.sum_univ_three] using hsum
    · refine ⟨![x, y, 0], ?_, ?_⟩
      · intro i
        match i with
        | 0 => exact ⟨hxA, hxB⟩
        | 1 => exact ⟨hyA, hyB⟩
        | 2 => exact ⟨h0, h0B⟩
      · have he : x + y + 0 = n := by omega
        simpa [Fin.sum_univ_three] using he

open Classical in

def FinitePrefixServesRisks
    (A : Set ℕ) (N₀ : ℕ) (B : Finset ℕ) : Prop :=
  ∀ n, N₀ ≤ n → (∃ b ∈ B, ∃ a ∈ A, b + a = n) →
    ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
      x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n

open Classical in

theorem moving_stall_iff_relative_singleton_support_transversal
    {A : Set ℕ} {B : Finset ℕ} {b n : ℕ} :
    (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
      x ∉ insert b B → y ∉ insert b B → z ∉ insert b B →
        x + y + z ≠ n) ↔
    IsRepSupportTransversal (A \ (B : Set ℕ)) n {b} := by
  constructor
  · intro hstall x hx y hy z hz hsum
    by_contra hnone
    push Not at hnone
    have hxInsert : x ∉ insert b B := by
      intro h
      rcases Finset.mem_insert.1 h with hxb | hxB
      · exact hnone.1 (Finset.mem_singleton.2 hxb)
      · exact hx.2 hxB
    have hyInsert : y ∉ insert b B := by
      intro h
      rcases Finset.mem_insert.1 h with hyb | hyB
      · exact hnone.2.1 (Finset.mem_singleton.2 hyb)
      · exact hy.2 hyB
    have hzInsert : z ∉ insert b B := by
      intro h
      rcases Finset.mem_insert.1 h with hzb | hzB
      · exact hnone.2.2 (Finset.mem_singleton.2 hzb)
      · exact hz.2 hzB
    exact hstall x hx.1 y hy.1 z hz.1
      hxInsert hyInsert hzInsert hsum
  · intro hhub x hxA y hyA z hzA hxInsert hyInsert hzInsert hsum
    have hx : x ∈ A \ (B : Set ℕ) := by
      refine ⟨hxA, ?_⟩
      exact fun hxB => hxInsert (Finset.mem_insert_of_mem hxB)
    have hy : y ∈ A \ (B : Set ℕ) := by
      refine ⟨hyA, ?_⟩
      exact fun hyB => hyInsert (Finset.mem_insert_of_mem hyB)
    have hz : z ∈ A \ (B : Set ℕ) := by
      refine ⟨hzA, ?_⟩
      exact fun hzB => hzInsert (Finset.mem_insert_of_mem hzB)
    rcases hhub x hx y hy z hz hsum with hxB | hyB | hzB
    · rw [Finset.mem_singleton] at hxB
      subst x
      exact hxInsert (Finset.mem_insert_self b B)
    · rw [Finset.mem_singleton] at hyB
      subst y
      exact hyInsert (Finset.mem_insert_self b B)
    · rw [Finset.mem_singleton] at hzB
      subst z
      exact hzInsert (Finset.mem_insert_self b B)

open Classical in

theorem unsafe_extension_self_risk_or_collateral_private
    {A : Set ℕ} {N₀ b : ℕ} {B : Finset ℕ}
    (hserved : FinitePrefixServesRisks A N₀ B)
    (hunsafe : ¬ FinitePrefixServesRisks A N₀ (insert b B)) :
    (∃ n, N₀ ≤ n ∧ (∃ a ∈ A, b + a = n) ∧
      ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
        x ∉ insert b B → y ∉ insert b B → z ∉ insert b B →
          x + y + z ≠ n) ∨
    (∃ n, N₀ ≤ n ∧ (∃ d ∈ B, ∃ a ∈ A, d + a = n) ∧
      IsPrivateTriple (A \ (B : Set ℕ)) b n) := by
  unfold FinitePrefixServesRisks at hunsafe
  push Not at hunsafe
  obtain ⟨n, hn, ⟨d, hdPrefix, a, haA, hda⟩, hstall⟩ := hunsafe
  rcases Finset.mem_insert.1 hdPrefix with hdb | hdB
  · left
    subst d
    exact ⟨n, hn, ⟨a, haA, hda⟩, hstall⟩
  · right
    have holdRisk : ∃ d ∈ B, ∃ a ∈ A, d + a = n :=
      ⟨d, hdB, a, haA, hda⟩
    obtain ⟨x, hxA, y, hyA, z, hzA, hxB, hyB, hzB, hsum⟩ :=
      hserved n hn holdRisk
    have hprivate : IsPrivateTriple (A \ (B : Set ℕ)) b n := by
      constructor
      · exact ⟨x, ⟨hxA, hxB⟩, y, ⟨hyA, hyB⟩,
          z, ⟨hzA, hzB⟩, hsum⟩
      · intro x' hx' y' hy' z' hz' hsum'
        have hhub :=
          moving_stall_iff_relative_singleton_support_transversal.mp hstall
        rcases hhub x' hx' y' hy' z' hz' hsum' with h | h | h
        · exact Or.inl (Finset.mem_singleton.1 h)
        · exact Or.inr (Or.inl (Finset.mem_singleton.1 h))
        · exact Or.inr (Or.inr (Finset.mem_singleton.1 h))
    exact ⟨n, hn, holdRisk, hprivate⟩

open Classical in

theorem IsPrivateTriple.required_element_mem_le_and_complement_split
    {S : Set ℕ} {b n : ℕ} (hprivate : IsPrivateTriple S b n) :
    b ∈ S ∧ b ≤ n ∧
      ∃ u ∈ S, ∃ v ∈ S, u + v = n - b := by
  obtain ⟨⟨x, hxS, y, hyS, z, hzS, hsum⟩, hall⟩ := hprivate
  rcases hall x hxS y hyS z hzS hsum with hxb | hyb | hzb
  · subst x
    exact ⟨hxS, by omega, y, hyS, z, hzS, by omega⟩
  · subst y
    exact ⟨hyS, by omega, x, hxS, z, hzS, by omega⟩
  · subst z
    exact ⟨hzS, by omega, x, hxS, y, hyS, by omega⟩

open Classical in

theorem candidate_batch_safe_or_self_stalls_or_collateral_private
    {A : Set ℕ} {N₀ K : ℕ} {B C : Finset ℕ}
    (hserved : FinitePrefixServesRisks A N₀ B)
    (hmany : 2 * K < C.card) :
    (∃ b ∈ C, FinitePrefixServesRisks A N₀ (insert b B)) ∨
    (∃ S : Finset ℕ, S ⊆ C ∧ K < S.card ∧
      ∀ b ∈ S, ∃ n, N₀ ≤ n ∧ (∃ a ∈ A, b + a = n) ∧
        ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
          x ∉ insert b B → y ∉ insert b B → z ∉ insert b B →
            x + y + z ≠ n) ∨
    (∃ P : Finset ℕ, P ⊆ C ∧ K < P.card ∧
      ∀ b ∈ P, ∃ n, N₀ ≤ n ∧
        (∃ d ∈ B, ∃ a ∈ A, d + a = n) ∧
        IsPrivateTriple (A \ (B : Set ℕ)) b n) := by
  by_cases hsafe :
      ∃ b ∈ C, FinitePrefixServesRisks A N₀ (insert b B)
  · exact Or.inl hsafe
  · right
    have hclass : ∀ b ∈ C,
        (∃ n, N₀ ≤ n ∧ (∃ a ∈ A, b + a = n) ∧
          ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
            x ∉ insert b B → y ∉ insert b B →
              z ∉ insert b B → x + y + z ≠ n) ∨
        (∃ n, N₀ ≤ n ∧
          (∃ d ∈ B, ∃ a ∈ A, d + a = n) ∧
          IsPrivateTriple (A \ (B : Set ℕ)) b n) := by
      intro b hbC
      apply unsafe_extension_self_risk_or_collateral_private hserved
      exact fun h => hsafe ⟨b, hbC, h⟩
    set S := C.filter (fun b =>
      ∃ n, N₀ ≤ n ∧ (∃ a ∈ A, b + a = n) ∧
        ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
          x ∉ insert b B → y ∉ insert b B →
            z ∉ insert b B → x + y + z ≠ n) with hS
    set P := C.filter (fun b =>
      ∃ n, N₀ ≤ n ∧
        (∃ d ∈ B, ∃ a ∈ A, d + a = n) ∧
        IsPrivateTriple (A \ (B : Set ℕ)) b n) with hP
    have hcover : C ⊆ S ∪ P := by
      intro b hbC
      rcases hclass b hbC with hself | hprivate
      · exact Finset.mem_union_left _
          (by rw [hS, Finset.mem_filter]; exact ⟨hbC, hself⟩)
      · exact Finset.mem_union_right _
          (by rw [hP, Finset.mem_filter]; exact ⟨hbC, hprivate⟩)
    have hcard : C.card ≤ S.card + P.card := by
      exact (Finset.card_le_card hcover).trans
        (Finset.card_union_le S P)
    by_cases hSlarge : K < S.card
    · left
      refine ⟨S, ?_, hSlarge, ?_⟩
      · intro b hb
        rw [hS, Finset.mem_filter] at hb
        exact hb.1
      · intro b hb
        rw [hS, Finset.mem_filter] at hb
        exact hb.2
    · right
      have hSsmall : S.card ≤ K := Nat.le_of_not_gt hSlarge
      have hPlarge : K < P.card := by omega
      refine ⟨P, ?_, hPlarge, ?_⟩
      · intro b hb
        rw [hP, Finset.mem_filter] at hb
        exact hb.1
      · intro b hb
        rw [hP, Finset.mem_filter] at hb
        exact hb.2

open Classical in

theorem stall_forces_wealth {A : Set ℕ} {N₀ n : ℕ} {B : Finset ℕ}
    (hcov : PairCovers A N₀) (hB : B.Nonempty) (hn : N₀ ≤ n)
    (hunserved : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
      x ∉ B → y ∉ B → z ∉ B → x + y + z ≠ n) :
    ∃ w ∈ B,
      ((Finset.range (n - N₀ + 1)).filter
        (fun z => z ∈ A ∧ z ∉ B)).card ≤
      B.card * ((Finset.range (n - w + 1)).filter
        (fun x => x ∈ A ∧ (n - w - x) ∈ A)).card := by
  set s := (Finset.range (n - N₀ + 1)).filter
    (fun z => z ∈ A ∧ z ∉ B) with hs
  have key : ∀ z, ∃ w, z ∈ s →
      (w ∈ B ∧ w ≤ n - z ∧ (n - z - w) ∈ A) := by
    intro z
    by_cases hz : z ∈ s
    · rw [hs, Finset.mem_filter, Finset.mem_range] at hz
      obtain ⟨hzn, hzA, hzB⟩ := hz
      obtain ⟨p, hpA, q, hqA, hpq⟩ := hcov (n - z) (by omega)
      by_cases hpB : p ∈ B
      · refine ⟨p, fun _ => ⟨hpB, by omega, ?_⟩⟩
        have he : n - z - p = q := by omega
        rw [he]
        exact hqA
      · by_cases hqB : q ∈ B
        · refine ⟨q, fun _ => ⟨hqB, by omega, ?_⟩⟩
          have he : n - z - q = p := by omega
          rw [he]
          exact hpA
        · exfalso
          exact hunserved z hzA p hpA q hqA hzB hpB hqB
            (by omega)
    · exact ⟨0, fun h => absurd h hz⟩
  choose g hg using key
  set fib : ℕ → Finset ℕ := fun w =>
    s.filter (fun z => g z = w) with hfib
  have hcover : s ⊆ B.biUnion fib := by
    intro z hz
    rw [Finset.mem_biUnion]
    exact ⟨g z, (hg z hz).1, Finset.mem_filter.2 ⟨hz, rfl⟩⟩
  obtain ⟨w, hwB, hwmax⟩ := Finset.exists_max_image B
    (fun w => (fib w).card) hB
  refine ⟨w, hwB, ?_⟩
  have h1 : s.card ≤ ∑ v ∈ B, (fib v).card :=
    le_trans (Finset.card_le_card hcover)
      (Finset.card_biUnion_le)
  have h2 : ∑ v ∈ B, (fib v).card ≤ B.card * (fib w).card := by
    rw [← smul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ (fun v hv => hwmax v hv)
  have h3 : (fib w).card ≤ ((Finset.range (n - w + 1)).filter
      (fun x => x ∈ A ∧ (n - w - x) ∈ A)).card := by
    apply Finset.card_le_card
    intro z hz
    rw [hfib, Finset.mem_filter] at hz
    obtain ⟨hzs, hzg⟩ := hz
    obtain ⟨hgB, hgle, hgA⟩ := hg z hzs
    rw [hzg] at hgle hgA
    have hzs' := hzs
    rw [hs, Finset.mem_filter, Finset.mem_range] at hzs'
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, hzs'.2.1, ?_⟩
    have he : n - w - z = n - z - w := by omega
    rw [he]
    exact hgA
  have h4 : B.card * (fib w).card ≤
      B.card * ((Finset.range (n - w + 1)).filter
        (fun x => x ∈ A ∧ (n - w - x) ∈ A)).card :=
    Nat.mul_le_mul_left _ h3
  omega

open Classical in

theorem large_finset_image_or_large_fiber
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (K R : ℕ)
    (hlarge : K * R < S.card) :
    R < (S.image f).card ∨
      ∃ y ∈ S.image f, K < (S.filter (fun x => f x = y)).card := by
  by_cases hImage : R < (S.image f).card
  · exact Or.inl hImage
  · right
    have hImageSmall : (S.image f).card ≤ R :=
      Nat.le_of_not_gt hImage
    by_contra hFiber
    have hFiberSmall : ∀ y ∈ S.image f,
        (S.filter (fun x => f x = y)).card ≤ K := by
      intro y hy
      exact Nat.le_of_not_gt
        (fun hyLarge => hFiber ⟨y, hy, hyLarge⟩)
    have hcount : S.card ≤ K * (S.image f).card :=
      Finset.card_le_mul_card_image (f := f) S K hFiberSmall
    have hmul : K * (S.image f).card ≤ K * R :=
      Nat.mul_le_mul_left K hImageSmall
    exact (Nat.not_lt_of_ge (hcount.trans hmul)) hlarge

open Classical in

theorem moving_prefix_stalls_core_or_mobile
    {A : Set ℕ} {N₀ K L : ℕ} {B C : Finset ℕ} {n : ℕ → ℕ}
    (hcov : PairCovers A N₀)
    (hscale : ∀ b ∈ C, N₀ ≤ n b)
    (hstall : ∀ b ∈ C, ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
      x ∉ insert b B → y ∉ insert b B → z ∉ insert b B →
        x + y + z ≠ n b)
    (hlow : ∀ b ∈ C,
      (insert b B).card * L ≤
        ((Finset.range (n b - N₀ + 1)).filter
          (fun z => z ∈ A ∧ z ∉ insert b B)).card)
    (hmany : (B.card + 1) * K < C.card) :
    (∃ M : Finset ℕ, M ⊆ C ∧ K < M.card ∧
      ∀ b ∈ M,
        L ≤ ((Finset.range (n b - b + 1)).filter
          (fun x => x ∈ A ∧ (n b - b - x) ∈ A)).card) ∨
    (∃ w ∈ B, ∃ M : Finset ℕ, M ⊆ C ∧ K < M.card ∧
      ∀ b ∈ M,
        L ≤ ((Finset.range (n b - w + 1)).filter
          (fun x => x ∈ A ∧ (n b - w - x) ∈ A)).card) := by
  have hpick : ∀ b, ∃ w, b ∈ C →
      w ∈ insert b B ∧
        L ≤ ((Finset.range (n b - w + 1)).filter
          (fun x => x ∈ A ∧ (n b - w - x) ∈ A)).card := by
    intro b
    by_cases hbC : b ∈ C
    · have hprefix : (insert b B).Nonempty :=
        ⟨b, Finset.mem_insert_self b B⟩
      obtain ⟨w, hw, hwealth⟩ :=
        stall_forces_wealth hcov hprefix (hscale b hbC)
          (hstall b hbC)
      refine ⟨w, fun _ => ⟨hw, ?_⟩⟩
      apply le_of_mul_le_mul_left
        (le_trans (hlow b hbC) hwealth)
        (Finset.card_pos.mpr hprefix)
    · exact ⟨b, fun hb => absurd hb hbC⟩
  choose g hg using hpick
  set Mobile := C.filter (fun b => g b = b) with hMobile
  set Core := C.filter (fun b => g b ≠ b) with hCore
  have hpartition : Mobile.card + Core.card = C.card := by
    rw [hMobile, hCore]
    exact Finset.card_filter_add_card_filter_not (fun b => g b = b)
  by_cases hMobileLarge : K < Mobile.card
  · left
    refine ⟨Mobile, ?_, hMobileLarge, ?_⟩
    · intro b hb
      exact (Finset.mem_filter.1 hb).1
    · intro b hb
      have hb' := Finset.mem_filter.1 hb
      have hwealth := (hg b hb'.1).2
      rw [hb'.2] at hwealth
      exact hwealth
  · right
    have hMobileSmall : Mobile.card ≤ K :=
      Nat.le_of_not_gt hMobileLarge
    have hCoreLarge : B.card * K < Core.card := by
      have hmany' := hmany
      rw [← hpartition] at hmany'
      simp only [Nat.add_mul, one_mul] at hmany'
      omega
    have hmaps : ∀ b ∈ Core, g b ∈ B := by
      intro b hb
      have hb' := Finset.mem_filter.1 hb
      have hginsert := (hg b hb'.1).1
      rw [Finset.mem_insert] at hginsert
      exact hginsert.resolve_left hb'.2
    obtain ⟨w, hwB, hwfiber⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        hmaps hCoreLarge
    refine ⟨w, hwB, Core.filter (fun b => g b = w), ?_,
      hwfiber, ?_⟩
    · intro b hb
      have hbCore := (Finset.mem_filter.1 hb).1
      exact (Finset.mem_filter.1 hbCore).1
    · intro b hb
      have hb' := Finset.mem_filter.1 hb
      have hbCore := Finset.mem_filter.1 hb'.1
      have hwealth := (hg b hbCore.1).2
      rw [hb'.2] at hwealth
      exact hwealth

open Classical in

theorem moving_prefix_stalls_distinct_or_recurrent
    {A : Set ℕ} {N₀ K R L : ℕ} {B C : Finset ℕ} {n : ℕ → ℕ}
    (hcov : PairCovers A N₀)
    (hscale : ∀ b ∈ C, N₀ ≤ n b)
    (hstall : ∀ b ∈ C, ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
      x ∉ insert b B → y ∉ insert b B → z ∉ insert b B →
        x + y + z ≠ n b)
    (hlow : ∀ b ∈ C,
      (insert b B).card * L ≤
        ((Finset.range (n b - N₀ + 1)).filter
          (fun z => z ∈ A ∧ z ∉ insert b B)).card)
    (hmany : (B.card + 1) * (K * R) < C.card) :
    (∃ T : Finset ℕ, R < T.card ∧ T.card ≤ C.card ∧
      ∀ M ∈ T,
        (∃ b ∈ C, M ≤ n b) ∧
          L ≤ ((Finset.range (M + 1)).filter
            (fun x => x ∈ A ∧ (M - x) ∈ A)).card) ∨
    (∃ M : ℕ, ∃ F : Finset ℕ, F ⊆ C ∧ K < F.card ∧
      (∀ b ∈ F, n b - b = M) ∧
      L ≤ ((Finset.range (M + 1)).filter
        (fun x => x ∈ A ∧ (M - x) ∈ A)).card) ∨
    (∃ w ∈ B, ∃ M : ℕ, ∃ F : Finset ℕ,
      F ⊆ C ∧ K < F.card ∧
      (∀ b ∈ F, n b - w = M) ∧
      L ≤ ((Finset.range (M + 1)).filter
        (fun x => x ∈ A ∧ (M - x) ∈ A)).card) := by
  rcases moving_prefix_stalls_core_or_mobile
      (K := K * R) hcov hscale hstall hlow hmany with
    ⟨M, hMC, hMlarge, hwealth⟩ |
      ⟨w, hwB, M, hMC, hMlarge, hwealth⟩
  · rcases large_finset_image_or_large_fiber M
      (fun b => n b - b) K R hMlarge with hDistinct | hRecurrent
    · left
      refine ⟨M.image (fun b => n b - b), hDistinct,
        Finset.card_image_le.trans (Finset.card_le_card hMC), ?_⟩
      intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨b, hbM, rfl⟩ := hq
      exact ⟨⟨b, hMC hbM, Nat.sub_le _ _⟩, hwealth b hbM⟩
    · right
      left
      obtain ⟨q, hqImage, hqFiber⟩ := hRecurrent
      rw [Finset.mem_image] at hqImage
      obtain ⟨b₀, hb₀M, hb₀q⟩ := hqImage
      refine ⟨q, M.filter (fun b => n b - b = q), ?_,
        hqFiber, ?_, ?_⟩
      · intro b hb
        exact hMC (Finset.mem_filter.1 hb).1
      · intro b hb
        exact (Finset.mem_filter.1 hb).2
      · rw [← hb₀q]
        exact hwealth b₀ hb₀M
  · rcases large_finset_image_or_large_fiber M
      (fun b => n b - w) K R hMlarge with hDistinct | hRecurrent
    · left
      refine ⟨M.image (fun b => n b - w), hDistinct,
        Finset.card_image_le.trans (Finset.card_le_card hMC), ?_⟩
      intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨b, hbM, rfl⟩ := hq
      exact ⟨⟨b, hMC hbM, Nat.sub_le _ _⟩, hwealth b hbM⟩
    · right
      right
      obtain ⟨q, hqImage, hqFiber⟩ := hRecurrent
      rw [Finset.mem_image] at hqImage
      obtain ⟨b₀, hb₀M, hb₀q⟩ := hqImage
      refine ⟨w, hwB, q, M.filter (fun b => n b - w = q), ?_,
        hqFiber, ?_, ?_⟩
      · intro b hb
        exact hMC (Finset.mem_filter.1 hb).1
      · intro b hb
        exact (Finset.mem_filter.1 hb).2
      · rw [← hb₀q]
        exact hwealth b₀ hb₀M

open Classical in

theorem four_moving_stalls_same_target_force_fixed_stall
    {A : Set ℕ} {B F : Finset ℕ} {m : ℕ}
    (hF : 3 < F.card)
    (hstall : ∀ b ∈ F, ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
      x ∉ insert b B → y ∉ insert b B → z ∉ insert b B →
        x + y + z ≠ m) :
    ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
      x ∉ B → y ∉ B → z ∉ B → x + y + z ≠ m := by
  intro x hxA y hyA z hzA hxB hyB hzB hsum
  have hfresh : ∃ b ∈ F, b ∉ ({x, y, z} : Finset ℕ) := by
    by_contra hnone
    push Not at hnone
    have hsub : F ⊆ ({x, y, z} : Finset ℕ) :=
      fun b hb => hnone b hb
    have hcard := Finset.card_le_card hsub
    have hthree : ({x, y, z} : Finset ℕ).card ≤ 3 := by
      apply le_trans (Finset.card_insert_le _ _)
      have htwo := Finset.card_insert_le y ({z} : Finset ℕ)
      simp at htwo ⊢
      omega
    omega
  obtain ⟨b, hbF, hbFresh⟩ := hfresh
  have hbxyz : b ≠ x ∧ b ≠ y ∧ b ≠ z := by
    simpa using hbFresh
  have hxInsert : x ∉ insert b B := by
    intro hx
    rcases Finset.mem_insert.1 hx with hxb | hxB'
    · exact hbxyz.1 hxb.symm
    · exact hxB hxB'
  have hyInsert : y ∉ insert b B := by
    intro hy
    rcases Finset.mem_insert.1 hy with hyb | hyB'
    · exact hbxyz.2.1 hyb.symm
    · exact hyB hyB'
  have hzInsert : z ∉ insert b B := by
    intro hz
    rcases Finset.mem_insert.1 hz with hzb | hzB'
    · exact hbxyz.2.2 hzb.symm
    · exact hzB hzB'
  exact hstall b hbF x hxA y hyA z hzA
    hxInsert hyInsert hzInsert hsum

open Classical in

theorem affine_stall_forces_pair_support_transversal
    {A : Set ℕ} {B : Finset ℕ} {a b : ℕ}
    (haA : a ∈ A) (haFresh : a ∉ insert b B)
    (hstall : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
      x ∉ insert b B → y ∉ insert b B → z ∉ insert b B →
        x + y + z ≠ b + a) :
    IsPairSupportTransversal A b (insert b B) := by
  intro x hxA y hyA hxy
  by_contra havoid
  push Not at havoid
  exact hstall x hxA y hyA a haA havoid.1 havoid.2 haFresh (by omega)

open Classical in

theorem moving_prefix_risks_distinct_or_affine_or_fixed_stall
    {A : Set ℕ} {N₀ R L : ℕ} {B C : Finset ℕ} {n : ℕ → ℕ}
    (hcov : PairCovers A N₀)
    (hscale : ∀ b ∈ C, N₀ ≤ n b)
    (hcandidate : ∀ b ∈ C, b ∈ A)
    (hrisk : ∀ b ∈ C, ∃ a ∈ A, b + a = n b)
    (hordered : ∀ b ∈ C, ∀ w ∈ B, w ≤ b)
    (hstall : ∀ b ∈ C, ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
      x ∉ insert b B → y ∉ insert b B → z ∉ insert b B →
        x + y + z ≠ n b)
    (hlow : ∀ b ∈ C,
      (insert b B).card * L ≤
        ((Finset.range (n b - N₀ + 1)).filter
          (fun z => z ∈ A ∧ z ∉ insert b B)).card)
    (hmany : (B.card + 1) * (3 * R) < C.card) :
    (∃ T : Finset ℕ, R < T.card ∧ T.card ≤ C.card ∧
      ∀ M ∈ T,
        (∃ b ∈ C, M ≤ n b) ∧
          L ≤ ((Finset.range (M + 1)).filter
            (fun x => x ∈ A ∧ (M - x) ∈ A)).card) ∨
    (∃ a ∈ A, ∃ F : Finset ℕ, F ⊆ C ∧ 3 < F.card ∧
      (∀ b ∈ F, b ∈ A ∧ n b = b + a) ∧
      L ≤ ((Finset.range (a + 1)).filter
        (fun x => x ∈ A ∧ (a - x) ∈ A)).card ∧
      (a ∈ B ∨ ∃ G : Finset ℕ, G ⊆ F ∧ 2 < G.card ∧
        ∀ b ∈ G, IsPairSupportTransversal A b (insert b B))) ∨
    (∃ m, N₀ ≤ m ∧ (∀ w ∈ B, w ≤ m) ∧
      (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
        x ∉ B → y ∉ B → z ∉ B → x + y + z ≠ m) ∧
      B.card * L ≤
        ((Finset.range (m - N₀ + 1)).filter
          (fun z => z ∈ A ∧ z ∉ B)).card) := by
  rcases moving_prefix_stalls_distinct_or_recurrent
      (K := 3) hcov hscale hstall hlow hmany with
    hDistinct | hAffine | hCore
  · exact Or.inl hDistinct
  · right
    left
    obtain ⟨a, F, hFC, hFlarge, hoffset, hwealth⟩ := hAffine
    obtain ⟨b₀, hb₀F⟩ := Finset.card_pos.mp (by omega : 0 < F.card)
    obtain ⟨a₀, ha₀A, ha₀eq⟩ := hrisk b₀ (hFC hb₀F)
    have haA : a ∈ A := by
      have haeq : n b₀ - b₀ = a₀ := by omega
      rw [hoffset b₀ hb₀F] at haeq
      rw [haeq]
      exact ha₀A
    have hwall : ∀ b ∈ F, n b = b + a := by
      intro b hbF
      obtain ⟨a', ha'A, ha'eq⟩ := hrisk b (hFC hbF)
      have hsub : n b - b = a' := by omega
      rw [hoffset b hbF] at hsub
      omega
    have hwallA : ∀ b ∈ F, b ∈ A ∧ n b = b + a :=
      fun b hbF => ⟨hcandidate b (hFC hbF), hwall b hbF⟩
    have hstructure :
        a ∈ B ∨ ∃ G : Finset ℕ, G ⊆ F ∧ 2 < G.card ∧
          ∀ b ∈ G, IsPairSupportTransversal A b (insert b B) := by
      by_cases haB : a ∈ B
      · exact Or.inl haB
      · right
        refine ⟨F.erase a, Finset.erase_subset a F, ?_, ?_⟩
        · by_cases haF : a ∈ F
          · rw [Finset.card_erase_of_mem haF]
            omega
          · rw [Finset.erase_eq_self.mpr haF]
            omega
        · intro b hb
          rw [Finset.mem_erase] at hb
          have haFresh : a ∉ insert b B := by
            intro ha
            rcases Finset.mem_insert.1 ha with hab | haB'
            · exact hb.1 hab.symm
            · exact haB haB'
          apply affine_stall_forces_pair_support_transversal haA haFresh
          intro x hxA y hyA z hzA hxI hyI hzI
          rw [← hwall b hb.2]
          exact hstall b (hFC hb.2) x hxA y hyA z hzA hxI hyI hzI
    exact ⟨a, haA, F, hFC, hFlarge, hwallA, hwealth, hstructure⟩
  · right
    right
    obtain ⟨w, hwB, q, F, hFC, hFlarge, hoffset, hwealth⟩ := hCore
    have htarget : ∀ b ∈ F, n b = q + w := by
      intro b hbF
      obtain ⟨a, haA, haeq⟩ := hrisk b (hFC hbF)
      have hbLe : b ≤ n b := by omega
      have hwLe : w ≤ n b :=
        le_trans (hordered b (hFC hbF) w hwB) hbLe
      have hoff := hoffset b hbF
      omega
    have hfixedStall :
        ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
          x ∉ B → y ∉ B → z ∉ B → x + y + z ≠ q + w := by
      apply four_moving_stalls_same_target_force_fixed_stall hFlarge
      intro b hbF x hxA y hyA z hzA hxI hyI hzI
      rw [← htarget b hbF]
      exact hstall b (hFC hbF) x hxA y hyA z hzA hxI hyI hzI
    obtain ⟨b₀, hb₀F⟩ := Finset.card_pos.mp (by omega : 0 < F.card)
    have hb₀C := hFC hb₀F
    have hmScale : N₀ ≤ q + w := by
      rw [← htarget b₀ hb₀F]
      exact hscale b₀ hb₀C
    have hBbelow : ∀ u ∈ B, u ≤ q + w := by
      intro u huB
      obtain ⟨a, haA, haeq⟩ := hrisk b₀ hb₀C
      have hb₀Le : b₀ ≤ n b₀ := by omega
      rw [← htarget b₀ hb₀F]
      exact le_trans (hordered b₀ hb₀C u huB) hb₀Le
    have hcardPrefix : B.card ≤ (insert b₀ B).card :=
      Finset.card_le_card (Finset.subset_insert b₀ B)
    have hsurvivorSubset :
        ((Finset.range (n b₀ - N₀ + 1)).filter
          (fun z => z ∈ A ∧ z ∉ insert b₀ B)) ⊆
        ((Finset.range (n b₀ - N₀ + 1)).filter
          (fun z => z ∈ A ∧ z ∉ B)) := by
      intro z hz
      rw [Finset.mem_filter] at hz ⊢
      refine ⟨hz.1, hz.2.1, ?_⟩
      exact fun hzB => hz.2.2 (Finset.mem_insert_of_mem hzB)
    have hlowFixed :
        B.card * L ≤
          ((Finset.range (q + w - N₀ + 1)).filter
            (fun z => z ∈ A ∧ z ∉ B)).card := by
      have hmul :
          B.card * L ≤ (insert b₀ B).card * L :=
        Nat.mul_le_mul_right L hcardPrefix
      have hcardSurvivors := Finset.card_le_card hsurvivorSubset
      rw [htarget b₀ hb₀F] at hcardSurvivors
      have hlow₀ := hlow b₀ hb₀C
      rw [htarget b₀ hb₀F] at hlow₀
      exact hmul.trans (hlow₀.trans hcardSurvivors)
    exact ⟨q + w, hmScale, hBbelow, hfixedStall, hlowFixed⟩

open Classical in

theorem moving_prefix_private_distinct_or_cosum_or_fixed_stall
    {A : Set ℕ} {N₀ R L : ℕ} {B C : Finset ℕ} {n : ℕ → ℕ}
    (hcov : PairCovers A N₀)
    (hscale : ∀ b ∈ C, N₀ ≤ n b)
    (hprivate : ∀ b ∈ C,
      IsPrivateTriple (A \ (B : Set ℕ)) b (n b))
    (hordered : ∀ b ∈ C, ∀ w ∈ B, w ≤ b)
    (hlow : ∀ b ∈ C,
      (insert b B).card * L ≤
        ((Finset.range (n b - N₀ + 1)).filter
          (fun z => z ∈ A ∧ z ∉ insert b B)).card)
    (hmany : (B.card + 1) * (3 * R) < C.card) :
    (∃ T : Finset ℕ, R < T.card ∧ T.card ≤ C.card ∧
      ∀ M ∈ T,
        (∃ b ∈ C, M ≤ n b) ∧
          L ≤ ((Finset.range (M + 1)).filter
            (fun x => x ∈ A ∧ (M - x) ∈ A)).card) ∨
    (∃ q, (∃ u ∈ A \ (B : Set ℕ), ∃ v ∈ A \ (B : Set ℕ),
        u + v = q) ∧
      ∃ F : Finset ℕ, F ⊆ C ∧ 3 < F.card ∧
        (∀ b ∈ F, b ∈ A \ (B : Set ℕ) ∧ n b = b + q ∧
          IsRepSupportTransversal A (b + q) (insert b B)) ∧
        L ≤ ((Finset.range (q + 1)).filter
          (fun x => x ∈ A ∧ (q - x) ∈ A)).card) ∨
    (∃ m, N₀ ≤ m ∧ (∀ w ∈ B, w ≤ m) ∧
      (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
        x ∉ B → y ∉ B → z ∉ B → x + y + z ≠ m) ∧
      B.card * L ≤
        ((Finset.range (m - N₀ + 1)).filter
          (fun z => z ∈ A ∧ z ∉ B)).card) := by
  have hstall : ∀ b ∈ C, ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
      x ∉ insert b B → y ∉ insert b B → z ∉ insert b B →
        x + y + z ≠ n b := by
    intro b hbC
    apply moving_stall_iff_relative_singleton_support_transversal.mpr
    intro x hx y hy z hz hsum
    rcases (hprivate b hbC).2 x hx y hy z hz hsum with h | h | h
    · exact Or.inl (Finset.mem_singleton.2 h)
    · exact Or.inr (Or.inl (Finset.mem_singleton.2 h))
    · exact Or.inr (Or.inr (Finset.mem_singleton.2 h))
  rcases moving_prefix_stalls_distinct_or_recurrent
      (K := 3) hcov hscale hstall hlow hmany with
    hDistinct | hAffine | hCore
  · exact Or.inl hDistinct
  · right
    left
    obtain ⟨q, F, hFC, hFlarge, hoffset, hwealth⟩ := hAffine
    obtain ⟨b₀, hb₀F⟩ := Finset.card_pos.mp (by omega : 0 < F.card)
    obtain ⟨hb₀S, hb₀Le, u, huS, v, hvS, huv⟩ :=
      (hprivate b₀ (hFC hb₀F)).required_element_mem_le_and_complement_split
    have hqsplit :
        ∃ u ∈ A \ (B : Set ℕ), ∃ v ∈ A \ (B : Set ℕ),
          u + v = q := by
      rw [hoffset b₀ hb₀F] at huv
      exact ⟨u, huS, v, hvS, huv⟩
    have hwall : ∀ b ∈ F, n b = b + q := by
      intro b hbF
      have hbLe :=
        (hprivate b (hFC hbF)).required_element_mem_le_and_complement_split.2.1
      have hoff := hoffset b hbF
      omega
    refine ⟨q, hqsplit, F, hFC, hFlarge, ?_, hwealth⟩
    intro b hbF
    have hbS :=
      (hprivate b (hFC hbF)).required_element_mem_le_and_complement_split.1
    refine ⟨hbS, hwall b hbF, ?_⟩
    intro x hxA y hyA z hzA hsum
    by_contra havoid
    push Not at havoid
    have hne := hstall b (hFC hbF) x hxA y hyA z hzA
      havoid.1 havoid.2.1 havoid.2.2
    rw [hwall b hbF] at hne
    exact hne hsum
  · right
    right
    obtain ⟨w, hwB, q, F, hFC, hFlarge, hoffset, hwealth⟩ := hCore
    have htarget : ∀ b ∈ F, n b = q + w := by
      intro b hbF
      have hbLe :=
        (hprivate b (hFC hbF)).required_element_mem_le_and_complement_split.2.1
      have hwLe : w ≤ n b :=
        le_trans (hordered b (hFC hbF) w hwB) hbLe
      have hoff := hoffset b hbF
      omega
    have hfixedStall :
        ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
          x ∉ B → y ∉ B → z ∉ B → x + y + z ≠ q + w := by
      apply four_moving_stalls_same_target_force_fixed_stall hFlarge
      intro b hbF x hxA y hyA z hzA hxI hyI hzI
      rw [← htarget b hbF]
      exact hstall b (hFC hbF) x hxA y hyA z hzA hxI hyI hzI
    obtain ⟨b₀, hb₀F⟩ := Finset.card_pos.mp (by omega : 0 < F.card)
    have hb₀C := hFC hb₀F
    have hmScale : N₀ ≤ q + w := by
      rw [← htarget b₀ hb₀F]
      exact hscale b₀ hb₀C
    have hBbelow : ∀ u ∈ B, u ≤ q + w := by
      intro u huB
      have hb₀Le :=
        (hprivate b₀ hb₀C).required_element_mem_le_and_complement_split.2.1
      rw [← htarget b₀ hb₀F]
      exact le_trans (hordered b₀ hb₀C u huB) hb₀Le
    have hcardPrefix : B.card ≤ (insert b₀ B).card :=
      Finset.card_le_card (Finset.subset_insert b₀ B)
    have hsurvivorSubset :
        ((Finset.range (n b₀ - N₀ + 1)).filter
          (fun z => z ∈ A ∧ z ∉ insert b₀ B)) ⊆
        ((Finset.range (n b₀ - N₀ + 1)).filter
          (fun z => z ∈ A ∧ z ∉ B)) := by
      intro z hz
      rw [Finset.mem_filter] at hz ⊢
      refine ⟨hz.1, hz.2.1, ?_⟩
      exact fun hzB => hz.2.2 (Finset.mem_insert_of_mem hzB)
    have hlowFixed :
        B.card * L ≤
          ((Finset.range (q + w - N₀ + 1)).filter
            (fun z => z ∈ A ∧ z ∉ B)).card := by
      have hmul :
          B.card * L ≤ (insert b₀ B).card * L :=
        Nat.mul_le_mul_right L hcardPrefix
      have hcardSurvivors := Finset.card_le_card hsurvivorSubset
      rw [htarget b₀ hb₀F] at hcardSurvivors
      have hlow₀ := hlow b₀ hb₀C
      rw [htarget b₀ hb₀F] at hlow₀
      exact hmul.trans (hlow₀.trans hcardSurvivors)
    exact ⟨q + w, hmScale, hBbelow, hfixedStall, hlowFixed⟩

open Classical in

theorem greedy_batch_safe_or_wealth_or_affine_or_fixed_or_collateral
    {A : Set ℕ} {N₀ R L : ℕ} {B C : Finset ℕ}
    (hcov : PairCovers A N₀)
    (hserved : FinitePrefixServesRisks A N₀ B)
    (hcandidate : ∀ b ∈ C, b ∈ A)
    (hordered : ∀ b ∈ C, ∀ w ∈ B, w ≤ b)
    (hlow : ∀ b ∈ C,
      (insert b B).card * L ≤
        ((Finset.range (b - N₀ + 1)).filter
          (fun z => z ∈ A ∧ z ∉ insert b B)).card)
    (hmany : 2 * ((B.card + 1) * (3 * R)) < C.card) :
    (∃ b ∈ C, FinitePrefixServesRisks A N₀ (insert b B)) ∨
    (∃ T : Finset ℕ, R < T.card ∧ T.card ≤ C.card ∧
      ∀ M ∈ T,
        L ≤ ((Finset.range (M + 1)).filter
          (fun x => x ∈ A ∧ (M - x) ∈ A)).card) ∨
    (∃ a ∈ A, ∃ F : Finset ℕ, F ⊆ C ∧ 3 < F.card ∧
      (∀ b ∈ F, b ∈ A ∧
        IsRepSupportTransversal A (b + a) (insert b B)) ∧
      L ≤ ((Finset.range (a + 1)).filter
        (fun x => x ∈ A ∧ (a - x) ∈ A)).card ∧
      (a ∈ B ∨ ∃ G : Finset ℕ, G ⊆ F ∧ 2 < G.card ∧
        ∀ b ∈ G, IsPairSupportTransversal A b (insert b B))) ∨
    (∃ m, N₀ ≤ m ∧ (∀ w ∈ B, w ≤ m) ∧
      (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
        x ∉ B → y ∉ B → z ∉ B → x + y + z ≠ m) ∧
      B.card * L ≤
        ((Finset.range (m - N₀ + 1)).filter
          (fun z => z ∈ A ∧ z ∉ B)).card) ∨
    (∃ P : Finset ℕ, P ⊆ C ∧
      (B.card + 1) * (3 * R) < P.card ∧
      ∀ b ∈ P, ∃ n, N₀ ≤ n ∧
        (∃ d ∈ B, ∃ a ∈ A, d + a = n) ∧
        IsPrivateTriple (A \ (B : Set ℕ)) b n) := by
  rcases candidate_batch_safe_or_self_stalls_or_collateral_private
      hserved hmany with hsafe | hself | hcollateral
  · exact Or.inl hsafe
  · obtain ⟨S, hSC, hSlarge, hself⟩ := hself
    have hpick : ∀ b, ∃ n, b ∈ S →
        N₀ ≤ n ∧ (∃ a ∈ A, b + a = n) ∧
        ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
          x ∉ insert b B → y ∉ insert b B →
            z ∉ insert b B → x + y + z ≠ n := by
      intro b
      by_cases hbS : b ∈ S
      · obtain ⟨n, hn⟩ := hself b hbS
        exact ⟨n, fun _ => hn⟩
      · exact ⟨0, fun hb => absurd hb hbS⟩
    choose n hn using hpick
    have hscale : ∀ b ∈ S, N₀ ≤ n b :=
      fun b hb => (hn b hb).1
    have hrisk : ∀ b ∈ S, ∃ a ∈ A, b + a = n b :=
      fun b hb => (hn b hb).2.1
    have hstall : ∀ b ∈ S, ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
        x ∉ insert b B → y ∉ insert b B → z ∉ insert b B →
          x + y + z ≠ n b :=
      fun b hb => (hn b hb).2.2
    have hlowS : ∀ b ∈ S,
        (insert b B).card * L ≤
          ((Finset.range (n b - N₀ + 1)).filter
            (fun z => z ∈ A ∧ z ∉ insert b B)).card := by
      intro b hbS
      obtain ⟨a, haA, haeq⟩ := hrisk b hbS
      have hbLe : b ≤ n b := by omega
      apply (hlow b (hSC hbS)).trans
      apply Finset.card_le_card
      intro z hz
      rw [Finset.mem_filter, Finset.mem_range] at hz ⊢
      exact ⟨by omega, hz.2⟩
    rcases moving_prefix_risks_distinct_or_affine_or_fixed_stall
        (B := B) (C := S) hcov hscale
          (fun b hb => hcandidate b (hSC hb))
          hrisk (fun b hb => hordered b (hSC hb))
          hstall hlowS hSlarge with
      hDistinct | hAffine | hFixed
    · right
      left
      obtain ⟨T, hTR, hTS, hwealth⟩ := hDistinct
      refine ⟨T, hTR, hTS.trans (Finset.card_le_card hSC), ?_⟩
      intro M hMT
      exact (hwealth M hMT).2
    · right
      right
      left
      obtain ⟨a, haA, F, hFS, hFlarge, hwall,
        hwealth, hstructure⟩ := hAffine
      refine ⟨a, haA, F, hFS.trans hSC, hFlarge, ?_,
        hwealth, hstructure⟩
      intro b hbF
      refine ⟨(hwall b hbF).1, ?_⟩
      intro x hxA y hyA z hzA hsum
      by_contra havoid
      push Not at havoid
      have hne := hstall b (hFS hbF) x hxA y hyA z hzA
        havoid.1 havoid.2.1 havoid.2.2
      rw [(hwall b hbF).2] at hne
      exact hne hsum
    · exact Or.inr (Or.inr (Or.inr (Or.inl hFixed)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hcollateral)))

open Classical in

theorem greedy_batch_complete_structural_fork
    {A : Set ℕ} {N₀ R L : ℕ} {B C : Finset ℕ}
    (hcov : PairCovers A N₀)
    (hserved : FinitePrefixServesRisks A N₀ B)
    (hcandidate : ∀ b ∈ C, b ∈ A)
    (hordered : ∀ b ∈ C, ∀ w ∈ B, w ≤ b)
    (hlow : ∀ b ∈ C,
      (insert b B).card * L ≤
        ((Finset.range (b - N₀ + 1)).filter
          (fun z => z ∈ A ∧ z ∉ insert b B)).card)
    (hmany : 2 * ((B.card + 1) * (3 * R)) < C.card) :
    (∃ b ∈ C, FinitePrefixServesRisks A N₀ (insert b B)) ∨
    (∃ T : Finset ℕ, R < T.card ∧ T.card ≤ C.card ∧
      ∀ M ∈ T,
        L ≤ ((Finset.range (M + 1)).filter
          (fun x => x ∈ A ∧ (M - x) ∈ A)).card) ∨
    (∃ a ∈ A, ∃ F : Finset ℕ, F ⊆ C ∧ 3 < F.card ∧
      (∀ b ∈ F, b ∈ A ∧ IsRepSupportTransversal A (b + a) (insert b B)) ∧
      L ≤ ((Finset.range (a + 1)).filter
        (fun x => x ∈ A ∧ (a - x) ∈ A)).card ∧
      (a ∈ B ∨ ∃ G : Finset ℕ, G ⊆ F ∧ 2 < G.card ∧
        ∀ b ∈ G, IsPairSupportTransversal A b (insert b B))) ∨
    (∃ q, (∃ u ∈ A \ (B : Set ℕ), ∃ v ∈ A \ (B : Set ℕ),
        u + v = q) ∧
      ∃ F : Finset ℕ, F ⊆ C ∧ 3 < F.card ∧
        (∀ b ∈ F, b ∈ A \ (B : Set ℕ) ∧
          IsRepSupportTransversal A (b + q) (insert b B)) ∧
        L ≤ ((Finset.range (q + 1)).filter
          (fun x => x ∈ A ∧ (q - x) ∈ A)).card) ∨
    (∃ m, N₀ ≤ m ∧ (∀ w ∈ B, w ≤ m) ∧
      (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
        x ∉ B → y ∉ B → z ∉ B → x + y + z ≠ m) ∧
      B.card * L ≤
        ((Finset.range (m - N₀ + 1)).filter
          (fun z => z ∈ A ∧ z ∉ B)).card) := by
  rcases greedy_batch_safe_or_wealth_or_affine_or_fixed_or_collateral
      hcov hserved hcandidate hordered hlow hmany with
    hsafe | hDistinct | hAffine | hFixed | hCollateral
  · exact Or.inl hsafe
  · exact Or.inr (Or.inl hDistinct)
  · exact Or.inr (Or.inr (Or.inl hAffine))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hFixed)))
  · obtain ⟨P, hPC, hPlarge, hprivateWitness⟩ := hCollateral
    have hpick : ∀ b, ∃ n, b ∈ P →
        N₀ ≤ n ∧
        (∃ d ∈ B, ∃ a ∈ A, d + a = n) ∧
        IsPrivateTriple (A \ (B : Set ℕ)) b n := by
      intro b
      by_cases hbP : b ∈ P
      · obtain ⟨n, hn⟩ := hprivateWitness b hbP
        exact ⟨n, fun _ => hn⟩
      · exact ⟨0, fun hb => absurd hb hbP⟩
    choose n hn using hpick
    have hscaleP : ∀ b ∈ P, N₀ ≤ n b :=
      fun b hb => (hn b hb).1
    have hprivateP : ∀ b ∈ P,
        IsPrivateTriple (A \ (B : Set ℕ)) b (n b) :=
      fun b hb => (hn b hb).2.2
    have hlowP : ∀ b ∈ P,
        (insert b B).card * L ≤
          ((Finset.range (n b - N₀ + 1)).filter
            (fun z => z ∈ A ∧ z ∉ insert b B)).card := by
      intro b hbP
      have hbLe :=
        (hprivateP b hbP).required_element_mem_le_and_complement_split.2.1
      apply (hlow b (hPC hbP)).trans
      apply Finset.card_le_card
      intro z hz
      rw [Finset.mem_filter, Finset.mem_range] at hz ⊢
      exact ⟨by omega, hz.2⟩
    rcases moving_prefix_private_distinct_or_cosum_or_fixed_stall
        (B := B) (C := P) hcov hscaleP hprivateP
          (fun b hb => hordered b (hPC hb)) hlowP hPlarge with
      hDistinct | hCosum | hFixed
    · right
      left
      obtain ⟨T, hTR, hTP, hwealth⟩ := hDistinct
      refine ⟨T, hTR, hTP.trans (Finset.card_le_card hPC), ?_⟩
      intro M hMT
      exact (hwealth M hMT).2
    · right
      right
      right
      left
      obtain ⟨q, hqsplit, F, hFP, hFlarge, hwall, hwealth⟩ := hCosum
      refine ⟨q, hqsplit, F, hFP.trans hPC, hFlarge, ?_, hwealth⟩
      intro b hbF
      exact ⟨(hwall b hbF).1, (hwall b hbF).2.2⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr hFixed)))

open Classical in

theorem exists_large_ordered_candidate_batch_with_low_supply
    {A : Set ℕ} {N₀ R L : ℕ} (hcov : PairCovers A N₀)
    (B : Finset ℕ) :
    ∃ C : Finset ℕ,
      2 * ((B.card + 1) * (3 * R)) < C.card ∧
      (∀ b ∈ C, b ∈ A) ∧
      (∀ b ∈ C, 0 < b) ∧
      (∀ b ∈ C, ∀ w ∈ B, w < b) ∧
      ∀ b ∈ C,
        (insert b B).card * L ≤
          ((Finset.range (b - N₀ + 1)).filter
            (fun z => z ∈ A ∧ z ∉ insert b B)).card := by
  have hstep : ∀ x : ℕ, ∃ a, a ∈ A ∧ x + N₀ < a := by
    intro x
    obtain ⟨a, haA, ha⟩ :=
      pairCovers_unbounded hcov (x + N₀ + 1)
    exact ⟨a, haA, by omega⟩
  choose f hfA hfgap using hstep
  let e : ℕ → ℕ :=
    fun i => Nat.rec (f (B.sup id)) (fun _ prev => f prev) i
  have he0 : e 0 = f (B.sup id) := rfl
  have heSucc : ∀ i, e (i + 1) = f (e i) := fun _ => rfl
  have heA : ∀ i, e i ∈ A := by
    intro i
    cases i with
    | zero =>
        rw [he0]
        exact hfA _
    | succ i =>
        rw [heSucc]
        exact hfA _
  have hegap : ∀ i, e i + N₀ < e (i + 1) := by
    intro i
    rw [heSucc]
    exact hfgap _
  have hemono : StrictMono e :=
    strictMono_nat_of_lt_succ (fun i => by
      have := hegap i
      omega)
  have heAbove : ∀ i, B.sup id < e i := by
    intro i
    have hbase : B.sup id < e 0 := by
      rw [he0]
      have := hfgap (B.sup id)
      omega
    exact hbase.trans_le (hemono.monotone (Nat.zero_le i))
  let Q := (B.card + 1) * L
  let H := 2 * ((B.card + 1) * (3 * R)) + 1
  let W := (Finset.range Q).image e
  let C := (Finset.range H).image (fun j => e (Q + j))
  have hWcard : W.card = Q := by
    rw [show W = (Finset.range Q).image e from rfl,
      Finset.card_image_of_injective _ hemono.injective,
      Finset.card_range]
  have hCcard : C.card = H := by
    rw [show C = (Finset.range H).image (fun j => e (Q + j)) from rfl,
      Finset.card_image_of_injective, Finset.card_range]
    intro i j hij
    have hidx : Q + i = Q + j := hemono.injective hij
    omega
  refine ⟨C, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hCcard]
    simp only [H]
    omega
  · intro b hbC
    rw [show C = (Finset.range H).image (fun j => e (Q + j)) from rfl,
      Finset.mem_image] at hbC
    obtain ⟨j, hj, rfl⟩ := hbC
    exact heA _
  · intro b hbC
    rw [show C = (Finset.range H).image (fun j => e (Q + j)) from rfl,
      Finset.mem_image] at hbC
    obtain ⟨j, hj, rfl⟩ := hbC
    have := heAbove (Q + j)
    omega
  · intro b hbC w hwB
    rw [show C = (Finset.range H).image (fun j => e (Q + j)) from rfl,
      Finset.mem_image] at hbC
    obtain ⟨j, hj, rfl⟩ := hbC
    have hwSup : w ≤ B.sup id := Finset.le_sup (f := id) hwB
    exact hwSup.trans_lt (heAbove _)
  · intro b hbC
    rw [show C = (Finset.range H).image (fun j => e (Q + j)) from rfl,
      Finset.mem_image] at hbC
    obtain ⟨j, hj, rfl⟩ := hbC
    have hWsub :
        W ⊆ ((Finset.range (e (Q + j) - N₀ + 1)).filter
          (fun z => z ∈ A ∧ z ∉ insert (e (Q + j)) B)) := by
      intro z hzW
      rw [show W = (Finset.range Q).image e from rfl,
        Finset.mem_image] at hzW
      obtain ⟨i, hi, rfl⟩ := hzW
      have hiQ : i < Q := Finset.mem_range.1 hi
      have hindex : i + 1 ≤ Q + j := by omega
      have hsep : e i + N₀ < e (Q + j) :=
        (hegap i).trans_le (hemono.monotone hindex)
      have hiB : e i ∉ B := by
        intro heiB
        have hle : e i ≤ B.sup id := Finset.le_sup (f := id) heiB
        exact (not_lt_of_ge hle) (heAbove i)
      have hneq : e i ≠ e (Q + j) := by omega
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, heA i, ?_⟩
      intro hmem
      rcases Finset.mem_insert.1 hmem with heq | hmemB
      · exact hneq heq
      · exact hiB hmemB
    have hreserved :
        Q ≤ ((Finset.range (e (Q + j) - N₀ + 1)).filter
          (fun z => z ∈ A ∧ z ∉ insert (e (Q + j)) B)).card := by
      calc
        Q = W.card := hWcard.symm
        _ ≤ ((Finset.range (e (Q + j) - N₀ + 1)).filter
          (fun z => z ∈ A ∧ z ∉ insert (e (Q + j)) B)).card :=
            Finset.card_le_card hWsub
    have hprefix : (insert (e (Q + j)) B).card ≤ B.card + 1 :=
      Finset.card_insert_le _ _
    have hpay :
        (insert (e (Q + j)) B).card * L ≤ Q := by
      simp only [Q]
      exact Nat.mul_le_mul_right L hprefix
    exact hpay.trans hreserved

open Classical in

theorem finite_prefix_extension_or_complete_structure
    {A : Set ℕ} {N₀ R L : ℕ} {B : Finset ℕ}
    (hcov : PairCovers A N₀)
    (hserved : FinitePrefixServesRisks A N₀ B) :
    (∃ b ∈ A, 0 < b ∧ (∀ w ∈ B, w < b) ∧
      FinitePrefixServesRisks A N₀ (insert b B)) ∨
    (∃ T : Finset ℕ, R < T.card ∧
      ∀ M ∈ T,
        L ≤ ((Finset.range (M + 1)).filter
          (fun x => x ∈ A ∧ (M - x) ∈ A)).card) ∨
    (∃ a ∈ A, ∃ F : Finset ℕ, 3 < F.card ∧
      (∀ b ∈ F, b ∈ A ∧ IsRepSupportTransversal A (b + a) (insert b B)) ∧
      L ≤ ((Finset.range (a + 1)).filter
        (fun x => x ∈ A ∧ (a - x) ∈ A)).card ∧
      (a ∈ B ∨ ∃ G : Finset ℕ, G ⊆ F ∧ 2 < G.card ∧
        ∀ b ∈ G, IsPairSupportTransversal A b (insert b B))) ∨
    (∃ q, (∃ u ∈ A \ (B : Set ℕ), ∃ v ∈ A \ (B : Set ℕ),
        u + v = q) ∧
      ∃ F : Finset ℕ, 3 < F.card ∧
        (∀ b ∈ F, b ∈ A \ (B : Set ℕ) ∧
          IsRepSupportTransversal A (b + q) (insert b B)) ∧
        L ≤ ((Finset.range (q + 1)).filter
          (fun x => x ∈ A ∧ (q - x) ∈ A)).card) ∨
    (∃ m, N₀ ≤ m ∧ (∀ w ∈ B, w ≤ m) ∧
      (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
        x ∉ B → y ∉ B → z ∉ B → x + y + z ≠ m) ∧
      B.card * L ≤
        ((Finset.range (m - N₀ + 1)).filter
          (fun z => z ∈ A ∧ z ∉ B)).card) := by
  obtain ⟨C, hmany, hcandidate, hpositive, hordered, hlow⟩ :=
    exists_large_ordered_candidate_batch_with_low_supply
      (R := R) (L := L) hcov B
  rcases greedy_batch_complete_structural_fork
      hcov hserved hcandidate
        (fun b hb w hw => (hordered b hb w hw).le)
        hlow hmany with
    hsafe | hDistinct | hAffine | hCosum | hFixed
  · left
    obtain ⟨b, hbC, hsafe⟩ := hsafe
    exact ⟨b, hcandidate b hbC, hpositive b hbC,
      hordered b hbC, hsafe⟩
  · obtain ⟨T, hTR, hTC, hwealth⟩ := hDistinct
    exact Or.inr (Or.inl ⟨T, hTR, hwealth⟩)
  · right
    right
    left
    obtain ⟨a, haA, F, hFC, hFlarge, hwall,
      hwealth, hstructure⟩ := hAffine
    exact ⟨a, haA, F, hFlarge, hwall, hwealth, hstructure⟩
  · right
    right
    right
    left
    obtain ⟨q, hqsplit, F, hFC, hFlarge, hwall, hwealth⟩ := hCosum
    exact ⟨q, hqsplit, F, hFlarge, hwall, hwealth⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr hFixed)))

open Classical in

theorem infinite_deletion_of_safe_prefix_extensions
    {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hext : ∀ B : Finset ℕ, FinitePrefixServesRisks A N₀ B →
      0 ∉ B →
      ∃ b ∈ A, 0 < b ∧ (∀ w ∈ B, w < b) ∧
        FinitePrefixServesRisks A N₀ (insert b B)) :
    ∃ B : Set ℕ, B ⊆ A ∧ B.Infinite ∧ 0 ∉ B ∧
      IsExactTupleAsymptoticBasis (A \ B) 3 := by
  have hempty : FinitePrefixServesRisks A N₀ ∅ := by
    intro n hn hrisk
    obtain ⟨b, hb, a, ha, hba⟩ := hrisk
    exact absurd hb (Finset.notMem_empty b)
  let SafePrefix :=
    {B : Finset ℕ //
      FinitePrefixServesRisks A N₀ B ∧ 0 ∉ B}
  let pick : SafePrefix → ℕ :=
    fun S => Classical.choose (hext S.1 S.2.1 S.2.2)
  have hpick : ∀ S : SafePrefix,
      pick S ∈ A ∧ 0 < pick S ∧
        (∀ w ∈ S.1, w < pick S) ∧
        FinitePrefixServesRisks A N₀ (insert (pick S) S.1) := by
    intro S
    exact Classical.choose_spec (hext S.1 S.2.1 S.2.2)
  let step : SafePrefix → SafePrefix :=
    fun S => ⟨insert (pick S) S.1, (hpick S).2.2.2, by
      rw [Finset.mem_insert]
      push Not
      exact ⟨(ne_of_gt (hpick S).2.1).symm, S.2.2⟩⟩
  let state : ℕ → SafePrefix :=
    fun k => Nat.rec ⟨∅, hempty, Finset.notMem_empty 0⟩
      (fun _ S => step S) k
  let b : ℕ → ℕ := fun k => pick (state k)
  have hstateSucc : ∀ k,
      (state (k + 1)).1 = insert (b k) (state k).1 := by
    intro k
    rfl
  have hbA : ∀ k, b k ∈ A := by
    intro k
    exact (hpick (state k)).1
  have hbpos : ∀ k, 0 < b k := by
    intro k
    exact (hpick (state k)).2.1
  have hbAbove : ∀ k, ∀ w ∈ (state k).1, w < b k := by
    intro k
    exact (hpick (state k)).2.2.1
  have hbmem : ∀ k, b k ∈ (state (k + 1)).1 := by
    intro k
    rw [hstateSucc]
    exact Finset.mem_insert_self _ _
  have hbstep : ∀ k, b k < b (k + 1) := by
    intro k
    exact hbAbove (k + 1) (b k) (hbmem k)
  have hbmono : StrictMono b := strictMono_nat_of_lt_succ hbstep
  have hprefix : ∀ k,
      (Finset.range k).image b = (state k).1 := by
    intro k
    induction k with
    | zero =>
        simp [state]
    | succ k ih =>
        rw [Finset.range_add_one, Finset.image_insert, ih,
          hstateSucc]
  have hkltb : ∀ k, k < b k := by
    intro k
    induction k with
    | zero => exact hbpos 0
    | succ k ih =>
        have := hbstep k
        omega
  let B : Set ℕ := Set.range b
  have hBA : B ⊆ A := by
    rintro _ ⟨k, rfl⟩
    exact hbA k
  have hBinf : B.Infinite :=
    Set.infinite_range_of_injective hbmono.injective
  have h0B : 0 ∉ B := by
    rintro ⟨k, hk⟩
    have := hbpos k
    omega
  refine ⟨B, hBA, hBinf, h0B, ?_⟩
  apply deletion_criterion_local h0 h0B hcov
  intro n hn
  rintro ⟨d, ⟨i, rfl⟩, a, haA, hba⟩
  let k := n + i + 2
  have hik : i < k := by
    simp only [k]
    omega
  have hnk : n < k := by
    simp only [k]
    omega
  have hnbk : n < b k := hnk.trans (hkltb k)
  have hbiPrefix : b i ∈ (state k).1 := by
    rw [← hprefix k]
    exact Finset.mem_image.2
      ⟨i, Finset.mem_range.2 hik, rfl⟩
  obtain ⟨x, hxA, y, hyA, z, hzA, hxPrefix, hyPrefix, hzPrefix,
      hxyz⟩ :=
    (state k).2.1 n hn ⟨b i, hbiPrefix, a, haA, hba⟩
  have havoid : ∀ t, t ∉ (state k).1 → t ≤ n → t ∉ B := by
    intro t htPrefix htn
    rintro ⟨j, rfl⟩
    by_cases hjk : j < k
    · apply htPrefix
      rw [← hprefix k]
      exact Finset.mem_image.2
        ⟨j, Finset.mem_range.2 hjk, rfl⟩
    · have hkj : k ≤ j := Nat.le_of_not_gt hjk
      have hbkj : b k ≤ b j := hbmono.monotone hkj
      omega
  exact ⟨x, hxA, y, hyA, z, hzA,
    havoid x hxPrefix (by omega),
    havoid y hyPrefix (by omega),
    havoid z hzPrefix (by omega), hxyz⟩

open Classical in
/-- The four non-extension outputs of
`finite_prefix_extension_or_complete_structure`, packaged so that they can
be quantified at one fixed terminal prefix. -/
def FinitePrefixStructuralObstruction
    (A : Set ℕ) (N₀ : ℕ) (B : Finset ℕ) (R L : ℕ) : Prop :=
  (∃ T : Finset ℕ, R < T.card ∧
      ∀ M ∈ T,
        L ≤ ((Finset.range (M + 1)).filter
          (fun x => x ∈ A ∧ (M - x) ∈ A)).card) ∨
  (∃ a ∈ A, ∃ F : Finset ℕ, 3 < F.card ∧
      (∀ b ∈ F, b ∈ A ∧ IsRepSupportTransversal A (b + a) (insert b B)) ∧
      L ≤ ((Finset.range (a + 1)).filter
        (fun x => x ∈ A ∧ (a - x) ∈ A)).card ∧
      (a ∈ B ∨ ∃ G : Finset ℕ, G ⊆ F ∧ 2 < G.card ∧
        ∀ b ∈ G, IsPairSupportTransversal A b (insert b B))) ∨
  (∃ q, (∃ u ∈ A \ (B : Set ℕ), ∃ v ∈ A \ (B : Set ℕ),
        u + v = q) ∧
      ∃ F : Finset ℕ, 3 < F.card ∧
        (∀ b ∈ F, b ∈ A \ (B : Set ℕ) ∧
          IsRepSupportTransversal A (b + q) (insert b B)) ∧
        L ≤ ((Finset.range (q + 1)).filter
          (fun x => x ∈ A ∧ (q - x) ∈ A)).card) ∨
  (∃ m, N₀ ≤ m ∧ (∀ w ∈ B, w ≤ m) ∧
      (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
        x ∉ B → y ∉ B → z ∉ B → x + y + z ≠ m) ∧
      B.card * L ≤
        ((Finset.range (m - N₀ + 1)).filter
          (fun z => z ∈ A ∧ z ∉ B)).card)

open Classical in
/-- The unconditional finite fork in its compact interface. -/
theorem finite_prefix_extension_or_structural_obstruction
    {A : Set ℕ} {N₀ R L : ℕ} {B : Finset ℕ}
    (hcov : PairCovers A N₀)
    (hserved : FinitePrefixServesRisks A N₀ B) :
    (∃ b ∈ A, 0 < b ∧ (∀ w ∈ B, w < b) ∧
      FinitePrefixServesRisks A N₀ (insert b B)) ∨
    FinitePrefixStructuralObstruction A N₀ B R L := by
  simpa [FinitePrefixStructuralObstruction] using
    (finite_prefix_extension_or_complete_structure
      (R := R) (L := L) hcov hserved)

open Classical in

theorem counterexample_has_terminal_safe_prefix
    {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ B : Finset ℕ, FinitePrefixServesRisks A N₀ B ∧
      0 ∉ B ∧
      ∀ b ∈ A, 0 < b → (∀ w ∈ B, w < b) →
        ¬FinitePrefixServesRisks A N₀ (insert b B) := by
  by_contra hterminal
  have hext : ∀ B : Finset ℕ, FinitePrefixServesRisks A N₀ B →
      0 ∉ B →
      ∃ b ∈ A, 0 < b ∧ (∀ w ∈ B, w < b) ∧
        FinitePrefixServesRisks A N₀ (insert b B) := by
    intro B hserved h0B
    by_contra hnone
    apply hterminal
    refine ⟨B, hserved, h0B, ?_⟩
    intro b hbA hbpos hbAbove hsafe
    exact hnone ⟨b, hbA, hbpos, hbAbove, hsafe⟩
  obtain ⟨B, hBA, hBinf, h0B, hbasis⟩ :=
    infinite_deletion_of_safe_prefix_extensions h0 hcov hext
  exact (hfail B hBA hBinf) hbasis

open Classical in

theorem counterexample_terminal_prefix_has_complete_structure
    {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ B : Finset ℕ,
      FinitePrefixServesRisks A N₀ B ∧
      0 ∉ B ∧
      (∀ b ∈ A, 0 < b → (∀ w ∈ B, w < b) →
        ¬FinitePrefixServesRisks A N₀ (insert b B)) ∧
      ∀ R L, FinitePrefixStructuralObstruction A N₀ B R L := by
  obtain ⟨B, hserved, h0B, hterminal⟩ :=
    counterexample_has_terminal_safe_prefix h0 hcov hfail
  refine ⟨B, hserved, h0B, hterminal, ?_⟩
  intro R L
  rcases finite_prefix_extension_or_structural_obstruction
      (R := R) (L := L) hcov hserved with hsafe | hstructure
  · obtain ⟨b, hbA, hbpos, hbAbove, hsafe⟩ := hsafe
    exact absurd hsafe (hterminal b hbA hbpos hbAbove)
  · exact hstructure

open Classical in
/-- A safe prefix which leaves `0` undeleted cannot have a genuine fixed
stall above the covering threshold.  A covering pair either avoids the
prefix, in which case it can be padded by `0`, or contains a deleted
endpoint, in which case the target is a risk and `hserved` supplies the
required surviving triple. -/
theorem safe_zero_surviving_prefix_has_no_fixed_stall
    {A : Set ℕ} {N₀ m : ℕ} {B : Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hserved : FinitePrefixServesRisks A N₀ B)
    (h0B : 0 ∉ B) (hm : N₀ ≤ m) :
    ¬(∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
      x ∉ B → y ∉ B → z ∉ B → x + y + z ≠ m) := by
  intro hstall
  obtain ⟨x, hxA, y, hyA, hxy⟩ := hcov m hm
  by_cases hxB : x ∈ B
  · obtain ⟨p, hpA, q, hqA, r, hrA, hpB, hqB, hrB, hpqr⟩ :=
      hserved m hm ⟨x, hxB, y, hyA, hxy⟩
    exact hstall p hpA q hqA r hrA hpB hqB hrB hpqr
  · by_cases hyB : y ∈ B
    · obtain ⟨p, hpA, q, hqA, r, hrA, hpB, hqB, hrB, hpqr⟩ :=
        hserved m hm ⟨y, hyB, x, hxA, by omega⟩
      exact hstall p hpA q hqA r hrA hpB hqB hrB hpqr
    · exact hstall x hxA y hyA 0 h0 hxB hyB h0B (by omega)

open Classical in
/-- More than `R` distinct targets, each with pair wealth at least `L`. -/
def ManyWealthyOffsets (A : Set ℕ) (R L : ℕ) : Prop :=
  ∃ T : Finset ℕ, R < T.card ∧
    ∀ M ∈ T,
      L ≤ ((Finset.range (M + 1)).filter
        (fun x => x ∈ A ∧ (M - x) ∈ A)).card

open Classical in
/-- The wealthy basis-translate affine wall at a finite prefix. -/
def BasisAffineWall
    (A : Set ℕ) (B : Finset ℕ) (L : ℕ) : Prop :=
  ∃ a ∈ A, ∃ F : Finset ℕ, 3 < F.card ∧
    (∀ b ∈ F, b ∈ A ∧ IsRepSupportTransversal A (b + a) (insert b B)) ∧
    L ≤ ((Finset.range (a + 1)).filter
      (fun x => x ∈ A ∧ (a - x) ∈ A)).card ∧
    (a ∈ B ∨ ∃ G : Finset ℕ, G ⊆ F ∧ 2 < G.card ∧
      ∀ b ∈ G, IsPairSupportTransversal A b (insert b B))

open Classical in
/-- The wealthy survivor-co-sum affine wall at a finite prefix. -/
def SurvivorCosumAffineWall
    (A : Set ℕ) (B : Finset ℕ) (L : ℕ) : Prop :=
  ∃ q, (∃ u ∈ A \ (B : Set ℕ), ∃ v ∈ A \ (B : Set ℕ),
      u + v = q) ∧
    ∃ F : Finset ℕ, 3 < F.card ∧
      (∀ b ∈ F, b ∈ A \ (B : Set ℕ) ∧
        IsRepSupportTransversal A (b + q) (insert b B)) ∧
      L ≤ ((Finset.range (q + 1)).filter
        (fun x => x ∈ A ∧ (q - x) ∈ A)).card

/-- The three genuinely mobile outputs left after the fixed-stall case is
eliminated at a safe prefix which preserves zero. -/
def FinitePrefixMobileObstruction
    (A : Set ℕ) (B : Finset ℕ) (R L : ℕ) : Prop :=
  ManyWealthyOffsets A R L ∨
  BasisAffineWall A B L ∨
  SurvivorCosumAffineWall A B L

open Classical in
/-- At a safe prefix preserving zero, the complete four-way structural
obstruction automatically reduces to the three mobile cases. -/
theorem finitePrefixStructuralObstruction_is_mobile
    {A : Set ℕ} {N₀ R L : ℕ} {B : Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hserved : FinitePrefixServesRisks A N₀ B) (h0B : 0 ∉ B)
    (hstructure : FinitePrefixStructuralObstruction A N₀ B R L) :
    FinitePrefixMobileObstruction A B R L := by
  rcases hstructure with hDistinct | hAffine | hCosum | hFixed
  · exact Or.inl hDistinct
  · exact Or.inr (Or.inl hAffine)
  · exact Or.inr (Or.inr hCosum)
  · obtain ⟨m, hm, hmB, hstall, hlow⟩ := hFixed
    exact absurd hstall
      (safe_zero_surviving_prefix_has_no_fixed_stall
        h0 hcov hserved h0B hm)

open Classical in

theorem counterexample_terminal_prefix_has_mobile_structure
    {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ B : Finset ℕ,
      FinitePrefixServesRisks A N₀ B ∧
      0 ∉ B ∧
      (∀ b ∈ A, 0 < b → (∀ w ∈ B, w < b) →
        ¬FinitePrefixServesRisks A N₀ (insert b B)) ∧
      ∀ R L, FinitePrefixMobileObstruction A B R L := by
  obtain ⟨B, hserved, h0B, hterminal, hstructure⟩ :=
    counterexample_terminal_prefix_has_complete_structure h0 hcov hfail
  refine ⟨B, hserved, h0B, hterminal, ?_⟩
  intro R L
  exact finitePrefixStructuralObstruction_is_mobile
    h0 hcov hserved h0B (hstructure R L)

open Classical in
/-- Distinct wealthy families are downward monotone in both requested
scales. -/
theorem manyWealthyOffsets_mono
    {A : Set ℕ} {R L R' L' : ℕ}
    (hR : R ≤ R') (hL : L ≤ L')
    (h : ManyWealthyOffsets A R' L') :
    ManyWealthyOffsets A R L := by
  obtain ⟨T, hlarge, hwealth⟩ := h
  exact ⟨T, hR.trans_lt hlarge,
    fun M hMT => hL.trans (hwealth M hMT)⟩

open Classical in
/-- Basis-affine walls are downward monotone in wealth. -/
theorem basisAffineWall_mono
    {A : Set ℕ} {B : Finset ℕ} {L L' : ℕ}
    (hL : L ≤ L') (h : BasisAffineWall A B L') :
    BasisAffineWall A B L := by
  obtain ⟨a, haA, F, hF, hwall, hwealth, hstructure⟩ := h
  exact ⟨a, haA, F, hF, hwall, hL.trans hwealth, hstructure⟩

open Classical in
/-- Survivor-co-sum affine walls are downward monotone in wealth. -/
theorem survivorCosumAffineWall_mono
    {A : Set ℕ} {B : Finset ℕ} {L L' : ℕ}
    (hL : L ≤ L') (h : SurvivorCosumAffineWall A B L') :
    SurvivorCosumAffineWall A B L := by
  obtain ⟨q, hqsplit, F, hF, hwall, hwealth⟩ := h
  exact ⟨q, hqsplit, F, hF, hwall, hL.trans hwealth⟩

open Classical in

theorem mobile_obstruction_cofinal_trichotomy
    {A : Set ℕ} {B : Finset ℕ}
    (hmobile : ∀ R L, FinitePrefixMobileObstruction A B R L) :
    (∀ R L, ManyWealthyOffsets A R L) ∨
    (∀ L, BasisAffineWall A B L) ∨
    (∀ L, SurvivorCosumAffineWall A B L) := by
  by_cases hAffine : ∀ L, BasisAffineWall A B L
  · exact Or.inr (Or.inl hAffine)
  · by_cases hCosum : ∀ L, SurvivorCosumAffineWall A B L
    · exact Or.inr (Or.inr hCosum)
    · left
      simp only [not_forall] at hAffine hCosum
      obtain ⟨L₁, hL₁⟩ := hAffine
      obtain ⟨L₂, hL₂⟩ := hCosum
      intro R L
      let L' := max L (max L₁ L₂)
      rcases hmobile R L' with hDistinct | hAffine' | hCosum'
      · exact manyWealthyOffsets_mono (le_refl R)
          (le_max_left L (max L₁ L₂)) hDistinct
      · exfalso
        apply hL₁
        exact basisAffineWall_mono
          (le_trans (le_max_left L₁ L₂)
            (le_max_right L (max L₁ L₂))) hAffine'
      · exfalso
        apply hL₂
        exact survivorCosumAffineWall_mono
          (le_trans (le_max_right L₁ L₂)
            (le_max_right L (max L₁ L₂))) hCosum'

open Classical in

theorem counterexample_terminal_prefix_cofinal_trichotomy
    {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ B : Finset ℕ,
      FinitePrefixServesRisks A N₀ B ∧
      0 ∉ B ∧
      (∀ b ∈ A, 0 < b → (∀ w ∈ B, w < b) →
        ¬FinitePrefixServesRisks A N₀ (insert b B)) ∧
      ((∀ R L, ManyWealthyOffsets A R L) ∨
       (∀ L, BasisAffineWall A B L) ∨
       (∀ L, SurvivorCosumAffineWall A B L)) := by
  obtain ⟨B, hserved, h0B, hterminal, hmobile⟩ :=
    counterexample_terminal_prefix_has_mobile_structure h0 hcov hfail
  exact ⟨B, hserved, h0B, hterminal,
    mobile_obstruction_cofinal_trichotomy hmobile⟩

open Classical in
/-- A safe finite prefix which preserves zero in fact has a surviving
triple for every late target, not only for the targets it threatens.
For a covering pair, either an endpoint lies in the prefix and `hserved`
applies, or both endpoints survive and the pair is padded by zero. -/
theorem safe_zero_surviving_prefix_serves_every_late_target
    {A : Set ℕ} {N₀ : ℕ} {B : Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hserved : FinitePrefixServesRisks A N₀ B)
    (h0B : 0 ∉ B) :
    ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
  intro n hn
  obtain ⟨x, hxA, y, hyA, hxy⟩ := hcov n hn
  by_cases hxB : x ∈ B
  · exact hserved n hn ⟨x, hxB, y, hyA, hxy⟩
  · by_cases hyB : y ∈ B
    · exact hserved n hn ⟨y, hyB, x, hxA, by omega⟩
    · exact ⟨x, hxA, y, hyA, 0, h0, hxB, hyB, h0B, by omega⟩

open Classical in

theorem unsafe_extension_has_relative_private_destruction
    {A : Set ℕ} {N₀ b : ℕ} {B : Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hserved : FinitePrefixServesRisks A N₀ B)
    (h0B : 0 ∉ B)
    (hunsafe : ¬FinitePrefixServesRisks A N₀ (insert b B)) :
    ∃ n, N₀ ≤ n ∧
      (∃ d ∈ insert b B, ∃ a ∈ A, d + a = n) ∧
      IsPrivateTriple (A \ (B : Set ℕ)) b n := by
  unfold FinitePrefixServesRisks at hunsafe
  push Not at hunsafe
  obtain ⟨n, hn, hrisk, hstall⟩ := hunsafe
  obtain ⟨x, hxA, y, hyA, z, hzA, hxB, hyB, hzB, hxyz⟩ :=
    safe_zero_surviving_prefix_serves_every_late_target
      h0 hcov hserved h0B n hn
  refine ⟨n, hn, hrisk, ?_⟩
  constructor
  · exact ⟨x, ⟨hxA, hxB⟩, y, ⟨hyA, hyB⟩,
      z, ⟨hzA, hzB⟩, hxyz⟩
  · intro p hp q hq r hr hpqr
    have hhub := moving_stall_iff_relative_singleton_support_transversal.mp hstall
    rcases hhub p hp q hq r hr hpqr with h | h | h
    · exact Or.inl (Finset.mem_singleton.1 h)
    · exact Or.inr (Or.inl (Finset.mem_singleton.1 h))
    · exact Or.inr (Or.inr (Finset.mem_singleton.1 h))

open Classical in
/-- A repair of the private destruction at `(b,n)` which avoids `b` but
necessarily uses at least one element of the retained finite prefix. -/
def HasPrefixRepairTriple
    (A : Set ℕ) (B : Finset ℕ) (b n : ℕ) : Prop :=
  ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
    x + y + z = n ∧ x ≠ b ∧ y ≠ b ∧ z ≠ b ∧
      (x ∈ B ∨ y ∈ B ∨ z ∈ B)

open Classical in

theorem relative_private_absolute_or_prefix_repair
    {A : Set ℕ} {B : Finset ℕ} {b n : ℕ}
    (hprivate : IsPrivateTriple (A \ (B : Set ℕ)) b n) :
    IsPrivateTriple A b n ∨ HasPrefixRepairTriple A B b n := by
  by_cases habsolute :
      ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
        x + y + z = n → x = b ∨ y = b ∨ z = b
  · left
    obtain ⟨x, hx, y, hy, z, hz, hxyz⟩ := hprivate.1
    exact ⟨⟨x, hx.1, y, hy.1, z, hz.1, hxyz⟩, habsolute⟩
  · right
    push Not at habsolute
    obtain ⟨x, hxA, y, hyA, z, hzA, hxyz,
      hxb, hyb, hzb⟩ := habsolute
    have hhit : x ∈ B ∨ y ∈ B ∨ z ∈ B := by
      by_contra havoid
      push Not at havoid
      rcases hprivate.2 x ⟨hxA, havoid.1⟩
          y ⟨hyA, havoid.2.1⟩ z ⟨hzA, havoid.2.2⟩ hxyz with
        h | h | h
      · exact hxb h
      · exact hyb h
      · exact hzb h
    exact ⟨x, hxA, y, hyA, z, hzA, hxyz,
      hxb, hyb, hzb, hhit⟩

open Classical in

theorem counterexample_terminal_prefix_private_destruction_fork
    {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ B : Finset ℕ,
      FinitePrefixServesRisks A N₀ B ∧ 0 ∉ B ∧
      ∀ b ∈ A, 0 < b → (∀ w ∈ B, w < b) →
        ∃ n, N₀ ≤ n ∧ b ≤ n ∧
          (∃ d ∈ insert b B, ∃ a ∈ A, d + a = n) ∧
          IsPrivateTriple (A \ (B : Set ℕ)) b n ∧
          (IsPrivateTriple A b n ∨
            HasPrefixRepairTriple A B b n) := by
  obtain ⟨B, hserved, h0B, hterminal⟩ :=
    counterexample_has_terminal_safe_prefix h0 hcov hfail
  refine ⟨B, hserved, h0B, ?_⟩
  intro b hbA hbpos hbAbove
  obtain ⟨n, hn, hrisk, hprivate⟩ :=
    unsafe_extension_has_relative_private_destruction
      h0 hcov hserved h0B (hterminal b hbA hbpos hbAbove)
  have hbn :=
    (IsPrivateTriple.required_element_mem_le_and_complement_split hprivate).2.1
  exact ⟨n, hn, hbn, hrisk, hprivate,
    relative_private_absolute_or_prefix_repair hprivate⟩

open Classical in
/-- A repair triple avoiding `b` and passing through one specified old
prefix element `w`. -/
def HasRepairThrough
    (A : Set ℕ) (w b n : ℕ) : Prop :=
  ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
    x + y + z = n ∧ x ≠ b ∧ y ≠ b ∧ z ≠ b ∧
      (x = w ∨ y = w ∨ z = w)

open Classical in
/-- A repair through `w` is exactly a shifted surviving pair:
`w + u + v = n`, with both pair entries different from the current
required element `b`. -/
theorem repairThrough_gives_shifted_pair
    {A : Set ℕ} {w b n : ℕ}
    (hrepair : HasRepairThrough A w b n) :
    ∃ u ∈ A, ∃ v ∈ A,
      u ≠ b ∧ v ≠ b ∧ w + u + v = n := by
  obtain ⟨x, hxA, y, hyA, z, hzA, hxyz,
    hxb, hyb, hzb, hxw | hyw | hzw⟩ := hrepair
  · subst x
    exact ⟨y, hyA, z, hzA, hyb, hzb, by omega⟩
  · subst y
    exact ⟨x, hxA, z, hzA, hxb, hzb, by omega⟩
  · subst z
    exact ⟨x, hxA, y, hyA, hxb, hyb, by omega⟩

open Classical in
/-- The fixed channel element in a repair-through witness is itself a
basis element. -/
theorem HasRepairThrough.channel_mem
    {A : Set ℕ} {w b n : ℕ}
    (hrepair : HasRepairThrough A w b n) : w ∈ A := by
  obtain ⟨x, hxA, y, hyA, z, hzA, hxyz,
    hxb, hyb, hzb, hxw | hyw | hzw⟩ := hrepair
  · exact hxw ▸ hxA
  · exact hyw ▸ hyA
  · exact hzw ▸ hzA

open Classical in
/-- A prefix repair passes through at least one specified member of the
finite prefix. -/
theorem prefixRepairTriple_has_repairThrough
    {A : Set ℕ} {B : Finset ℕ} {b n : ℕ}
    (hrepair : HasPrefixRepairTriple A B b n) :
    ∃ w ∈ B, HasRepairThrough A w b n := by
  obtain ⟨x, hxA, y, hyA, z, hzA, hxyz,
    hxb, hyb, hzb, hhit⟩ := hrepair
  rcases hhit with hxB | hyB | hzB
  · exact ⟨x, hxB, x, hxA, y, hyA, z, hzA,
      hxyz, hxb, hyb, hzb, Or.inl rfl⟩
  · exact ⟨y, hyB, x, hxA, y, hyA, z, hzA,
      hxyz, hxb, hyb, hzb, Or.inr (Or.inl rfl)⟩
  · exact ⟨z, hzB, x, hxA, y, hyA, z, hzA,
      hxyz, hxb, hyb, hzb, Or.inr (Or.inr rfl)⟩

open Classical in
/-- Finite cofinal pigeonhole: if arbitrarily large objects carry a label
from a fixed finite set, one fixed label occurs arbitrarily far out. -/
theorem finite_cofinal_pigeonhole
    {B : Finset ℕ} {P : ℕ → ℕ → Prop}
    (hcofinal : ∀ X, ∃ b, X < b ∧ ∃ w ∈ B, P w b) :
    ∃ w ∈ B, ∀ X, ∃ b, X < b ∧ P w b := by
  by_contra hfixed
  push Not at hfixed
  let f : ℕ → ℕ := fun w =>
    if hw : w ∈ B then Classical.choose (hfixed w hw) else 0
  have hf : ∀ w ∈ B, ∀ b, f w < b → ¬P w b := by
    intro w hw
    have hspec := Classical.choose_spec (hfixed w hw)
    simpa [f, hw] using hspec
  obtain ⟨b, hb, w, hwB, hP⟩ := hcofinal (B.sup f)
  have hfw : f w ≤ B.sup f := Finset.le_sup (f := f) hwB
  exact hf w hwB b (hfw.trans_lt hb) hP

open Classical in
/-- An absolute terminal destruction carried by the candidate `b`. -/
def HasAbsoluteTerminalDestruction
    (A : Set ℕ) (N₀ : ℕ) (B : Finset ℕ) (b : ℕ) : Prop :=
  ∃ n, N₀ ≤ n ∧ b ≤ n ∧
    (∃ d ∈ insert b B, ∃ a ∈ A, d + a = n) ∧
    IsPrivateTriple (A \ (B : Set ℕ)) b n ∧
    IsPrivateTriple A b n

open Classical in
/-- A relative terminal destruction at `b` with a repair routed through the
specified old prefix element `w`. -/
def HasTerminalRepairDestructionThrough
    (A : Set ℕ) (N₀ : ℕ) (B : Finset ℕ) (w b : ℕ) : Prop :=
  ∃ n, N₀ ≤ n ∧ b ≤ n ∧
    (∃ d ∈ insert b B, ∃ a ∈ A, d + a = n) ∧
    IsPrivateTriple (A \ (B : Set ℕ)) b n ∧
    HasRepairThrough A w b n

open Classical in

theorem cofinal_fixedRepairChannel_has_conflictFree_thinning
    {A : Set ℕ} {N₀ w : ℕ} {B : Finset ℕ}
    (hcofinal : ∀ X, ∃ b ∈ A, X < b ∧
      HasTerminalRepairDestructionThrough A N₀ B w b) :
    ∃ C : Set ℕ, C ⊆ A ∧ C.Infinite ∧
      (∀ b ∈ C, w < b) ∧ w ∉ C ∧ w ∈ A ∧
      ∀ b ∈ C, ∃ n, N₀ ≤ n ∧ b ≤ n ∧
        (∃ d ∈ insert b B, ∃ a ∈ A, d + a = n) ∧
        IsPrivateTriple (A \ (B : Set ℕ)) b n ∧
        ∃ u ∈ A \ C, ∃ v ∈ A \ C, w + u + v = n := by
  let K : Set ℕ :=
    {b | b ∈ A ∧ w < b ∧
      HasTerminalRepairDestructionThrough A N₀ B w b}
  have hK : K.Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro X
    obtain ⟨b, hbA, hbLarge, hbRepair⟩ :=
      hcofinal (max X w)
    exact ⟨b, ⟨hbA, by omega, hbRepair⟩, by omega⟩
  have hchoice : ∀ b, ∃ n, ∃ u, ∃ v, b ∈ K →
      N₀ ≤ n ∧ b ≤ n ∧
      (∃ d ∈ insert b B, ∃ a ∈ A, d + a = n) ∧
      IsPrivateTriple (A \ (B : Set ℕ)) b n ∧
      u ∈ A ∧ v ∈ A ∧ u ≠ b ∧ v ≠ b ∧ w + u + v = n := by
    intro b
    by_cases hbK : b ∈ K
    · obtain ⟨n, hn, hbn, hrisk, hprivate, hrepair⟩ := hbK.2.2
      obtain ⟨u, huA, v, hvA, support_transversal, hvb, huv⟩ :=
        repairThrough_gives_shifted_pair hrepair
      exact ⟨n, u, v, fun _ =>
        ⟨hn, hbn, hrisk, hprivate, huA, hvA, support_transversal, hvb, huv⟩⟩
    · exact ⟨0, 0, 0, fun h => absurd h hbK⟩
  choose n u v hdata using hchoice
  let f : ℕ → Finset ℕ := fun b => {u b, v b}
  have hfcard : ∀ b ∈ K, (f b).card ≤ 2 := by
    intro b hbK
    exact le_trans (Finset.card_insert_le _ _) (by simp)
  have hfavoid : ∀ b ∈ K, b ∉ f b := by
    intro b hbK hb
    have h := hdata b hbK
    simp only [f, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with hbu | hbv
    · exact h.2.2.2.2.2.2.1 hbu.symm
    · exact h.2.2.2.2.2.2.2.1 hbv.symm
  obtain ⟨C, hCK, hCinf, hfree⟩ :=
    exists_infinite_freeSet_of_bounded_pointMap
      hK f 2 hfcard hfavoid
  have hwC : w ∉ C := by
    intro hw
    have := (hCK hw).2.1
    omega
  have hwA : w ∈ A := by
    obtain ⟨b, hbC⟩ := hCinf.nonempty
    obtain ⟨n, hn, hbn, hrisk, hprivate, hrepair⟩ :=
      (hCK hbC).2.2
    exact hrepair.channel_mem
  refine ⟨C, fun b hb => (hCK hb).1, hCinf,
    (fun b hb => (hCK hb).2.1), hwC, hwA, ?_⟩
  intro b hbC
  have hbK := hCK hbC
  have hd := hdata b hbK
  have hdisj := hfree b hbC
  have huC : u b ∉ C := by
    intro hu
    exact Set.disjoint_left.mp hdisj (by simp [f]) hu
  have hvC : v b ∉ C := by
    intro hv
    exact Set.disjoint_left.mp hdisj (by simp [f]) hv
  exact ⟨n b, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1,
    u b, ⟨hd.2.2.2.2.1, huC⟩,
    v b, ⟨hd.2.2.2.2.2.1, hvC⟩,
    hd.2.2.2.2.2.2.2.2⟩

open Classical in
/-- Selector form of conflict-free thinning.  One function `τ` records the
single repaired destruction chosen for each member of the infinite thinning. -/
theorem cofinal_fixedRepairChannel_has_conflictFree_selector
    {A : Set ℕ} {N₀ w : ℕ} {B : Finset ℕ}
    (hcofinal : ∀ X, ∃ b ∈ A, X < b ∧
      HasTerminalRepairDestructionThrough A N₀ B w b) :
    ∃ C : Set ℕ, ∃ τ : ℕ → ℕ,
      C ⊆ A ∧ C.Infinite ∧ 0 ∉ C ∧ w ∉ C ∧ w ∈ A ∧
      ∀ b ∈ C, N₀ ≤ τ b ∧ b ≤ τ b ∧
        (∃ d ∈ insert b B, ∃ a ∈ A, d + a = τ b) ∧
        IsPrivateTriple (A \ (B : Set ℕ)) b (τ b) ∧
        ∃ u ∈ A \ C, ∃ v ∈ A \ C, w + u + v = τ b := by
  obtain ⟨C, hCA, hCinf, hwBelow, hwC, hwA, hdata⟩ :=
    cofinal_fixedRepairChannel_has_conflictFree_thinning hcofinal
  have hpick : ∀ b, ∃ n, b ∈ C →
      N₀ ≤ n ∧ b ≤ n ∧
      (∃ d ∈ insert b B, ∃ a ∈ A, d + a = n) ∧
      IsPrivateTriple (A \ (B : Set ℕ)) b n ∧
      ∃ u ∈ A \ C, ∃ v ∈ A \ C, w + u + v = n := by
    intro b
    by_cases hbC : b ∈ C
    · obtain ⟨n, hn, hbn, hrisk, hprivate, hrepair⟩ :=
        hdata b hbC
      exact ⟨n, fun _ => ⟨hn, hbn, hrisk, hprivate, hrepair⟩⟩
    · exact ⟨0, fun h => absurd h hbC⟩
  choose τ hτ using hpick
  have h0C : 0 ∉ C := by
    intro hzero
    have := hwBelow 0 hzero
    omega
  refine ⟨C, τ, hCA, hCinf, h0C, hwC, hwA, ?_⟩
  intro b hbC
  exact hτ b hbC

open Classical in

theorem deletion_of_selectedRepairs_and_offSelectorRisks
    {A C : Set ℕ} {N₀ : ℕ} (τ : ℕ → ℕ)
    (h0 : 0 ∈ A) (h0C : 0 ∉ C) (hcov : PairCovers A N₀)
    (hselected : ∀ b ∈ C,
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ C ∧ y ∉ C ∧ z ∉ C ∧ x + y + z = τ b)
    (hoff : ∀ n, N₀ ≤ n →
      (∃ b ∈ C, ∃ a ∈ A, b + a = n) →
      (∀ b ∈ C, τ b ≠ n) →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ C ∧ y ∉ C ∧ z ∉ C ∧ x + y + z = n) :
    IsExactTupleAsymptoticBasis (A \ C) 3 := by
  apply deletion_criterion_local h0 h0C hcov
  intro n hn hrisk
  by_cases hhit : ∃ b ∈ C, τ b = n
  · obtain ⟨b, hbC, hbn⟩ := hhit
    obtain ⟨x, hxA, y, hyA, z, hzA, hxC, hyC, hzC, hxyz⟩ :=
      hselected b hbC
    exact ⟨x, hxA, y, hyA, z, hzA,
      hxC, hyC, hzC, by omega⟩
  · apply hoff n hn hrisk
    intro b hbC hbn
    exact hhit ⟨b, hbC, hbn⟩

open Classical in

theorem selectedRepairs_basis_iff_eventual_offSelectorRisks
    {A C : Set ℕ} {N₀ : ℕ} (τ : ℕ → ℕ)
    (h0 : 0 ∈ A) (h0C : 0 ∉ C) (hcov : PairCovers A N₀)
    (hselected : ∀ b ∈ C,
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ C ∧ y ∉ C ∧ z ∉ C ∧ x + y + z = τ b) :
    IsExactTupleAsymptoticBasis (A \ C) 3 ↔
      ∃ M, ∀ n, M ≤ n →
        (∃ b ∈ C, ∃ a ∈ A, b + a = n) →
        (∀ b ∈ C, τ b ≠ n) →
        ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
          x ∉ C ∧ y ∉ C ∧ z ∉ C ∧ x + y + z = n := by
  constructor
  · rintro ⟨M, hbasis⟩
    refine ⟨M, ?_⟩
    intro n hn hrisk hoff
    obtain ⟨v, hv, hvsum⟩ := hbasis n hn
    exact ⟨v 0, (hv 0).1, v 1, (hv 1).1, v 2, (hv 2).1,
      (hv 0).2, (hv 1).2, (hv 2).2,
      by simpa [Fin.sum_univ_three] using hvsum⟩
  · rintro ⟨M, hoff⟩
    have hcov' : PairCovers A (max N₀ M) := by
      intro n hn
      exact hcov n ((le_max_left N₀ M).trans hn)
    apply deletion_criterion_local h0 h0C hcov'
    intro n hn hrisk
    by_cases hhit : ∃ b ∈ C, τ b = n
    · obtain ⟨b, hbC, hbn⟩ := hhit
      obtain ⟨x, hxA, y, hyA, z, hzA, hxC, hyC, hzC, hxyz⟩ :=
        hselected b hbC
      exact ⟨x, hxA, y, hyA, z, hzA,
        hxC, hyC, hzC, by omega⟩
    · apply hoff n ((le_max_right N₀ M).trans hn) hrisk
      intro b hbC hbn
      exact hhit ⟨b, hbC, hbn⟩

open Classical in

theorem failure_with_selectedRepairs_forces_cofinal_offSelectorStalls
    {A C : Set ℕ} {N₀ : ℕ} (τ : ℕ → ℕ)
    (h0 : 0 ∈ A) (h0C : 0 ∉ C) (hcov : PairCovers A N₀)
    (hselected : ∀ b ∈ C,
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ C ∧ y ∉ C ∧ z ∉ C ∧ x + y + z = τ b)
    (hfail : ¬IsExactTupleAsymptoticBasis (A \ C) 3) :
    ∀ T, ∃ n, T ≤ n ∧ N₀ ≤ n ∧
      (∃ b ∈ C, ∃ a ∈ A, b + a = n) ∧
      (∀ b ∈ C, τ b ≠ n) ∧
      ¬∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ C ∧ y ∉ C ∧ z ∉ C ∧ x + y + z = n := by
  simp only [IsExactTupleAsymptoticBasis,
    not_exists, not_forall] at hfail
  intro T
  obtain ⟨n, hn, hnorep⟩ := hfail (max T N₀)
  have hnT : T ≤ n := (le_max_left T N₀).trans hn
  have hn₀ : N₀ ≤ n := (le_max_right T N₀).trans hn
  obtain ⟨x, hxA, y, hyA, hxy⟩ := hcov n hn₀
  have hrisk : ∃ b ∈ C, ∃ a ∈ A, b + a = n := by
    by_cases hxC : x ∈ C
    · exact ⟨x, hxC, y, hyA, hxy⟩
    · by_cases hyC : y ∈ C
      · exact ⟨y, hyC, x, hxA, by omega⟩
      · exfalso
        apply hnorep ![x, y, 0]
        constructor
        · intro i
          match i with
          | 0 => exact ⟨hxA, hxC⟩
          | 1 => exact ⟨hyA, hyC⟩
          | 2 => exact ⟨h0, h0C⟩
        · simpa [Fin.sum_univ_three] using hxy
  have hoff : ∀ b ∈ C, τ b ≠ n := by
    intro b hbC hbn
    obtain ⟨p, hpA, q, hqA, r, hrA, hpC, hqC, hrC, hpqr⟩ :=
      hselected b hbC
    apply hnorep ![p, q, r]
    constructor
    · intro i
      match i with
      | 0 => exact ⟨hpA, hpC⟩
      | 1 => exact ⟨hqA, hqC⟩
      | 2 => exact ⟨hrA, hrC⟩
    · simpa [Fin.sum_univ_three, hbn] using hpqr
  refine ⟨n, hnT, hn₀, hrisk, hoff, ?_⟩
  rintro ⟨p, hpA, q, hqA, r, hrA, hpC, hqC, hrC, hpqr⟩
  apply hnorep ![p, q, r]
  constructor
  · intro i
    match i with
    | 0 => exact ⟨hpA, hpC⟩
    | 1 => exact ⟨hqA, hqC⟩
    | 2 => exact ⟨hrA, hrC⟩
  · simpa [Fin.sum_univ_three] using hpqr

open Classical in

theorem failure_with_selectedRepairs_forces_offSelector_minimalDeletionTransversals
    {A C : Set ℕ} {N₀ : ℕ} (τ : ℕ → ℕ)
    (h0 : 0 ∈ A) (h0C : 0 ∉ C) (hcov : PairCovers A N₀)
    (hselected : ∀ b ∈ C,
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ C ∧ y ∉ C ∧ z ∉ C ∧ x + y + z = τ b)
    (hfail : ¬IsExactTupleAsymptoticBasis (A \ C) 3) :
    ∀ T, ∃ n, T ≤ n ∧ N₀ ≤ n ∧
      (∀ b ∈ C, τ b ≠ n) ∧
      ∃ H : Finset ℕ,
        H.Nonempty ∧
        H ⊆ (Finset.range (n + 1)).filter (· ∈ C) ∧
        IsRepSupportTransversal A n H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
        ∀ h ∈ H,
          ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
            x + y + z = n ∧
            (x = h ∨ y = h ∨ z = h) ∧
            ∀ g ∈ H, g ≠ h →
              x ≠ g ∧ y ≠ g ∧ z ≠ g := by
  intro T
  obtain ⟨n, hnT, hn₀, hrisk, hoff, hno⟩ :=
    failure_with_selectedRepairs_forces_cofinal_offSelectorStalls
      τ h0 h0C hcov hselected hfail T
  have hdead : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
      x + y + z = n → x ∈ C ∨ y ∈ C ∨ z ∈ C := by
    intro x hxA y hyA z hzA hxyz
    by_cases hxC : x ∈ C
    · exact Or.inl hxC
    · by_cases hyC : y ∈ C
      · exact Or.inr (Or.inl hyC)
      · by_cases hzC : z ∈ C
        · exact Or.inr (Or.inr hzC)
        · exact (hno
            ⟨x, hxA, y, hyA, z, hzA, hxC, hyC, hzC, hxyz⟩).elim
  have hhub :=
    failing_support_transversal_subset_deletion (A := A) (B := C) hdead
  obtain ⟨H, hHsub, hHhub, hHmin⟩ := exists_minimal_support_transversal hhub
  have hHne : H.Nonempty :=
    support_transversal_nonempty_of_covering h0 hcov hn₀ hHhub
  exact ⟨n, hnT, hn₀, hoff, H, hHne, hHsub, hHhub, hHmin,
    minimal_support_transversal_necessity hHhub hHmin⟩

open Classical in
/-- A nonempty minimal representation deletion transversal for an off-selector
target, contained in the deleted set below that target. -/
def IsOffSelectorMinimalDeletionTransversal
    (A C : Set ℕ) (N₀ : ℕ) (τ : ℕ → ℕ)
    (n : ℕ) (H : Finset ℕ) : Prop :=
  N₀ ≤ n ∧
  (∀ b ∈ C, τ b ≠ n) ∧
  H.Nonempty ∧
  IsRepSupportTransversal A n H ∧
  (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
  H ⊆ (Finset.range (n + 1)).filter (· ∈ C)

open Classical in
/-- A member of a minimal representation support transversal owns a pair co-witness:
the target is `h+u+v`, and the two co-witness entries avoid every other
member of the support transversal.  They need not avoid deleted points outside the support transversal. -/
theorem minimalRepSupportTransversal_member_has_pairCowitness
    {A : Set ℕ} {n h : ℕ} {H : Finset ℕ}
    (hhub : IsRepSupportTransversal A n H)
    (hmin : ∀ g ∈ H, ¬IsRepSupportTransversal A n (H \ {g}))
    (hhH : h ∈ H) :
    ∃ u ∈ A, ∃ v ∈ A, h + u + v = n ∧
      ∀ g ∈ H, g ≠ h → u ≠ g ∧ v ≠ g := by
  obtain ⟨x, hxA, y, hyA, z, hzA, hxyz, howner, havoid⟩ :=
    minimal_support_transversal_necessity hhub hmin h hhH
  rcases howner with hxh | hyh | hzh
  · subst x
    exact ⟨y, hyA, z, hzA, hxyz, fun g hgH hgh =>
      ⟨(havoid g hgH hgh).2.1, (havoid g hgH hgh).2.2⟩⟩
  · subst y
    exact ⟨x, hxA, z, hzA, by omega, fun g hgH hgh =>
      ⟨(havoid g hgH hgh).1, (havoid g hgH hgh).2.2⟩⟩
  · subst z
    exact ⟨x, hxA, y, hyA, by omega, fun g hgH hgh =>
      ⟨(havoid g hgH hgh).1, (havoid g hgH hgh).2.1⟩⟩

open Classical in

theorem finite_minimalSupportTransversal_has_external_deleted_interference :
    let A : Set ℕ := {0, 1, 2, 3}
    let H : Finset ℕ := {1, 2}
    IsRepSupportTransversal A 4 H ∧
    (∀ h ∈ H, ¬IsRepSupportTransversal A 4 (H \ {h})) ∧
    ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = 4 →
      (x = 1 ∨ y = 1 ∨ z = 1) →
      x ≠ 2 → y ≠ 2 → z ≠ 2 →
      x = 3 ∨ y = 3 ∨ z = 3 := by
  dsimp
  constructor
  · intro x hx y hy z hz hsum
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy hz
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  constructor
  · intro h hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl
    · intro hhub
      have hhit := hhub 0 (by simp) 1 (by simp) 3 (by simp) (by omega)
      simp at hhit
    · intro hhub
      have hhit := hhub 0 (by simp) 2 (by simp) 2 (by simp) (by omega)
      simp at hhit
  · intro x hx y hy z hz hsum howner hx2 hy2 hz2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy hz
    omega

open Classical in

theorem selectedRepairs_offSelector_window_core
    {A C : Set ℕ} {N₀ : ℕ} (τ : ℕ → ℕ)
    (h0 : 0 ∈ A) (h0C : 0 ∉ C) (hcov : PairCovers A N₀)
    (hselected : ∀ b ∈ C,
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ C ∧ y ∉ C ∧ z ∉ C ∧ x + y + z = τ b)
    (hfail : ¬IsExactTupleAsymptoticBasis (A \ C) 3)
    (W : ℕ) :
    ∃ S ⊆ (Finset.range (W + 1)).filter (· ∈ C),
      ∀ T, ∃ n, T ≤ n ∧
        (∀ b ∈ C, τ b ≠ n) ∧
        ∃ H : Finset ℕ,
          H.Nonempty ∧ IsRepSupportTransversal A n H ∧
          (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
          H ⊆ (Finset.range (n + 1)).filter (· ∈ C) ∧
          H ∩ Finset.range (W + 1) =
            S ∩ Finset.range (W + 1) := by
  have hQ : ∀ T, ∃ n, T ≤ n ∧ ∃ S,
      S ⊆ (Finset.range (W + 1)).filter (· ∈ C) ∧
      ((∀ b ∈ C, τ b ≠ n) ∧
        ∃ H : Finset ℕ,
          H.Nonempty ∧ IsRepSupportTransversal A n H ∧
          (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
          H ⊆ (Finset.range (n + 1)).filter (· ∈ C) ∧
          H ∩ Finset.range (W + 1) =
            S ∩ Finset.range (W + 1)) := by
    intro T
    obtain ⟨n, hnT, hn₀, hoff, H, hHne, hHsub, hHhub, hHmin,
      hnecessity⟩ :=
      failure_with_selectedRepairs_forces_offSelector_minimalDeletionTransversals
        τ h0 h0C hcov hselected hfail T
    refine ⟨n, hnT, H ∩ Finset.range (W + 1), ?_, hoff,
      H, hHne, hHhub, hHmin, hHsub, ?_⟩
    · intro x hx
      obtain ⟨hxH, hxW⟩ := Finset.mem_inter.1 hx
      have hxHC := hHsub hxH
      obtain ⟨hxn, hxC⟩ := Finset.mem_filter.1 hxHC
      exact Finset.mem_filter.2 ⟨hxW, hxC⟩
    · rw [Finset.inter_assoc, Finset.inter_self]
  obtain ⟨S, hSsub, hrec⟩ :=
    cofinal_subset_pigeonhole
      (Q := fun n S =>
        (∀ b ∈ C, τ b ≠ n) ∧
        ∃ H : Finset ℕ,
          H.Nonempty ∧ IsRepSupportTransversal A n H ∧
          (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
          H ⊆ (Finset.range (n + 1)).filter (· ∈ C) ∧
          H ∩ Finset.range (W + 1) =
            S ∩ Finset.range (W + 1))
      (F := (Finset.range (W + 1)).filter (· ∈ C)) hQ
  exact ⟨S, hSsub, hrec⟩

open Classical in

theorem selectedRepairs_recurrentRequiredElement_or_escapingDeletionTransversals
    {A C : Set ℕ} {N₀ : ℕ} (τ : ℕ → ℕ)
    (h0 : 0 ∈ A) (h0C : 0 ∉ C) (hcov : PairCovers A N₀)
    (hselected : ∀ b ∈ C,
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ C ∧ y ∉ C ∧ z ∉ C ∧ x + y + z = τ b)
    (hfail : ¬IsExactTupleAsymptoticBasis (A \ C) 3) :
    (∃ h ∈ C, ∀ T, ∃ n, T ≤ n ∧
      ∃ H : Finset ℕ,
        IsOffSelectorMinimalDeletionTransversal A C N₀ τ n H ∧ h ∈ H) ∨
    (∀ W T, ∃ n, T ≤ n ∧
      ∃ H : Finset ℕ,
        IsOffSelectorMinimalDeletionTransversal A C N₀ τ n H ∧
        ∀ h ∈ H, W < h) := by
  by_cases hrec : ∃ h ∈ C, ∀ T, ∃ n, T ≤ n ∧
      ∃ H : Finset ℕ,
        IsOffSelectorMinimalDeletionTransversal A C N₀ τ n H ∧ h ∈ H
  · exact Or.inl hrec
  · right
    have hboundedC : ∀ h ∈ C, ∃ T, ∀ n, T ≤ n →
        ∀ H : Finset ℕ,
          IsOffSelectorMinimalDeletionTransversal A C N₀ τ n H → h ∉ H := by
      intro h hhC
      by_contra hnoT
      push Not at hnoT
      exact hrec ⟨h, hhC, hnoT⟩
    have hthreshold : ∀ h, ∃ T, h ∈ C → ∀ n, T ≤ n →
        ∀ H : Finset ℕ,
          IsOffSelectorMinimalDeletionTransversal A C N₀ τ n H → h ∉ H := by
      intro h
      by_cases hhC : h ∈ C
      · obtain ⟨T, hT⟩ := hboundedC h hhC
        exact ⟨T, fun _ => hT⟩
      · exact ⟨0, fun hmem => absurd hmem hhC⟩
    choose g hg using hthreshold
    intro W T
    let F : Finset ℕ :=
      (Finset.range (W + 1)).filter (· ∈ C)
    let T' := max T (F.sup g)
    obtain ⟨n, hnT', hn₀, hoff, H, hHne, hHsub, hHhub, hHmin,
      hnecessity⟩ :=
      failure_with_selectedRepairs_forces_offSelector_minimalDeletionTransversals
        τ h0 h0C hcov hselected hfail T'
    have hcomm : IsOffSelectorMinimalDeletionTransversal A C N₀ τ n H :=
      ⟨hn₀, hoff, hHne, hHhub, hHmin, hHsub⟩
    refine ⟨n, ?_, H, hcomm, ?_⟩
    · dsimp [T'] at hnT'
      omega
    · intro h hhH
      by_contra hnotAbove
      have hhW : h ≤ W := Nat.le_of_not_gt hnotAbove
      have hhC : h ∈ C := by
        have hhFilter := hHsub hhH
        exact (Finset.mem_filter.1 hhFilter).2
      have hhF : h ∈ F := by
        exact Finset.mem_filter.2
          ⟨Finset.mem_range.2 (by omega), hhC⟩
      have hgSup : g h ≤ F.sup g :=
        Finset.le_sup (f := g) hhF
      have hgn : g h ≤ n := by
        dsimp [T'] at hnT'
        omega
      exact (hg h hhC n hgn H hcomm) hhH

open Classical in
/-- In the recurrent-core branch, the fixed required element owns cofinally many
pair co-witnesses at off-selector targets.  The pair avoids every other
member of the current minimal deletion transversal.  No conclusion about points of
`C \ H` is asserted. -/
theorem recurrentOffSelectorRequiredElement_has_pairCowitnessStream
    {A C : Set ℕ} {N₀ : ℕ} {τ : ℕ → ℕ}
    (hrec : ∃ h ∈ C, ∀ T, ∃ n, T ≤ n ∧
      ∃ H : Finset ℕ,
        IsOffSelectorMinimalDeletionTransversal A C N₀ τ n H ∧ h ∈ H) :
    ∃ h ∈ C, ∀ T, ∃ n, T ≤ n ∧
      ∃ H : Finset ℕ,
        IsOffSelectorMinimalDeletionTransversal A C N₀ τ n H ∧ h ∈ H ∧
        ∃ u ∈ A, ∃ v ∈ A, h + u + v = n ∧
          ∀ g ∈ H, g ≠ h → u ≠ g ∧ v ≠ g := by
  obtain ⟨h, hhC, hcofinal⟩ := hrec
  refine ⟨h, hhC, ?_⟩
  intro T
  obtain ⟨n, hnT, H, hcomm, hhH⟩ := hcofinal T
  obtain ⟨u, huA, v, hvA, huv, havoid⟩ :=
    minimalRepSupportTransversal_member_has_pairCowitness
      hcomm.2.2.2.1 hcomm.2.2.2.2.1 hhH
  exact ⟨n, hnT, H, hcomm, hhH,
    u, huA, v, hvA, huv, havoid⟩

open Classical in

theorem escapingDeletionTransversals_singletonPrivate_or_uniformlyMultiple
    {A C : Set ℕ} {N₀ : ℕ} {τ : ℕ → ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hesc : ∀ W T, ∃ n, T ≤ n ∧
      ∃ H : Finset ℕ,
        IsOffSelectorMinimalDeletionTransversal A C N₀ τ n H ∧
        ∀ h ∈ H, W < h) :
    (∀ W T, ∃ n, T ≤ n ∧ ∃ h ∈ C,
      W < h ∧ h ≤ n ∧ N₀ ≤ n ∧
      τ h ≠ n ∧ IsPrivateTriple A h n) ∨
    (∃ W₀ T₀,
      (∀ n, T₀ ≤ n → ∀ H : Finset ℕ,
        IsOffSelectorMinimalDeletionTransversal A C N₀ τ n H →
        (∀ h ∈ H, W₀ < h) → 2 ≤ H.card) ∧
      ∀ W T, ∃ n, T ≤ n ∧ ∃ H : Finset ℕ,
        IsOffSelectorMinimalDeletionTransversal A C N₀ τ n H ∧
        (∀ h ∈ H, W < h) ∧ 2 ≤ H.card) := by
  by_cases hsingle : ∀ W T, ∃ n, T ≤ n ∧
      ∃ H : Finset ℕ,
        IsOffSelectorMinimalDeletionTransversal A C N₀ τ n H ∧
        (∀ h ∈ H, W < h) ∧ H.card = 1
  · left
    intro W T
    obtain ⟨n, hnT, H, hcomm, habove, hHcard⟩ :=
      hsingle W T
    obtain ⟨h, rfl⟩ := Finset.card_eq_one.mp hHcard
    have hhC : h ∈ C := by
      have hhFilter :=
        hcomm.2.2.2.2.2 (Finset.mem_singleton_self h)
      exact (Finset.mem_filter.1 hhFilter).2
    have hhle : h ≤ n := by
      have hhFilter :=
        hcomm.2.2.2.2.2 (Finset.mem_singleton_self h)
      have := Finset.mem_range.1 (Finset.mem_filter.1 hhFilter).1
      omega
    have hprivate : IsPrivateTriple A h n :=
      privateTriple_of_singleton_support_transversal h0 hcov hcomm.1
        hcomm.2.2.2.1
    exact ⟨n, hnT, h, hhC,
      habove h (Finset.mem_singleton_self h), hhle,
      hcomm.1, hcomm.2.1 h hhC, hprivate⟩
  · right
    push Not at hsingle
    obtain ⟨W₀, T₀, hnotSingle⟩ := hsingle
    have hmultiple : ∀ n, T₀ ≤ n → ∀ H : Finset ℕ,
        IsOffSelectorMinimalDeletionTransversal A C N₀ τ n H →
        (∀ h ∈ H, W₀ < h) → 2 ≤ H.card := by
      intro n hn H hcomm habove
      have hpos : 0 < H.card :=
        Finset.card_pos.mpr hcomm.2.2.1
      have hneOne : H.card ≠ 1 :=
        hnotSingle n hn H hcomm habove
      omega
    refine ⟨W₀, T₀, hmultiple, ?_⟩
    intro W T
    obtain ⟨n, hn, H, hcomm, habove⟩ :=
      hesc (max W W₀) (max T T₀)
    have hnT : T ≤ n := by omega
    have hnT₀ : T₀ ≤ n := by omega
    have haboveW₀ : ∀ h ∈ H, W₀ < h := by
      intro h hh
      have := habove h hh
      omega
    have hcard : 2 ≤ H.card :=
      hmultiple n hnT₀ H hcomm haboveW₀
    refine ⟨n, hnT, H, hcomm, ?_, hcard⟩
    intro h hh
    have := habove h hh
    omega

open Classical in
/-- Escaping deletion transversals can be diagonalized into a block-separated
sequence: targets increase strictly, and every required element in the next
deletion transversal lies above the preceding target.  Since each deletion transversal lies
below its own target, distinct deletion transversals in the sequence are disjoint. -/
theorem escapingOffSelectorDeletionTransversals_has_blockSequence
    {A C : Set ℕ} {N₀ : ℕ} {τ : ℕ → ℕ}
    (hesc : ∀ W T, ∃ n, T ≤ n ∧
      ∃ H : Finset ℕ,
        IsOffSelectorMinimalDeletionTransversal A C N₀ τ n H ∧
        ∀ h ∈ H, W < h) :
    ∃ n : ℕ → ℕ, ∃ H : ℕ → Finset ℕ,
      StrictMono n ∧
      (∀ i, IsOffSelectorMinimalDeletionTransversal A C N₀ τ (n i) (H i)) ∧
      (∀ i, ∀ h ∈ H (i + 1), n i < h) ∧
      ∀ i j, i < j → Disjoint (H i) (H j) := by
  have hpick : ∀ W, ∃ p : ℕ × Finset ℕ,
      W < p.1 ∧
      IsOffSelectorMinimalDeletionTransversal A C N₀ τ p.1 p.2 ∧
      ∀ h ∈ p.2, W < h := by
    intro W
    obtain ⟨n, hn, H, hcomm, habove⟩ := hesc W (W + 1)
    exact ⟨(n, H), by omega, hcomm, habove⟩
  choose p hp using hpick
  let s : ℕ → ℕ × Finset ℕ :=
    Nat.rec (p 0) (fun _ q => p q.1)
  let n : ℕ → ℕ := fun i => (s i).1
  let H : ℕ → Finset ℕ := fun i => (s i).2
  have hs_zero : s 0 = p 0 := rfl
  have hs_succ : ∀ i, s (i + 1) = p (s i).1 := by
    intro i
    rfl
  have hn_step : ∀ i, n i < n (i + 1) := by
    intro i
    rw [show n i = (s i).1 from rfl,
      show n (i + 1) = (s (i + 1)).1 from rfl,
      hs_succ]
    exact (hp (s i).1).1
  have hn_mono : StrictMono n :=
    strictMono_nat_of_lt_succ hn_step
  have hcomm : ∀ i,
      IsOffSelectorMinimalDeletionTransversal A C N₀ τ (n i) (H i) := by
    intro i
    cases i with
    | zero =>
        rw [show n 0 = (s 0).1 from rfl,
          show H 0 = (s 0).2 from rfl, hs_zero]
        exact (hp 0).2.1
    | succ i =>
        rw [show n (i + 1) = (s (i + 1)).1 from rfl,
          show H (i + 1) = (s (i + 1)).2 from rfl, hs_succ]
        exact (hp (s i).1).2.1
  have habove : ∀ i, ∀ h ∈ H (i + 1), n i < h := by
    intro i h hh
    have hh' : h ∈ (p (s i).1).2 := by
      dsimp [H] at hh
      rw [hs_succ] at hh
      exact hh
    exact (hp (s i).1).2.2 h hh'
  refine ⟨n, H, hn_mono, hcomm, habove, ?_⟩
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hik : i ≤ k := by omega
  have hxle : x ≤ n i := by
    have hxFilter := (hcomm i).2.2.2.2.2 hxi
    have hxRange := (Finset.mem_filter.1 hxFilter).1
    have := Finset.mem_range.1 hxRange
    omega
  have hnik : n i ≤ n k := hn_mono.monotone hik
  have hkx : n k < x := habove k x hxj
  omega

open Classical in
/-- Once escaping deletion transversals are uniformly non-singleton, the
block-separated diagonal may be taken entirely in the multi-required element
regime. -/
theorem escapingUniformlyMultipleDeletionTransversals_has_blockSequence
    {A C : Set ℕ} {N₀ : ℕ} {τ : ℕ → ℕ} {W₀ T₀ : ℕ}
    (hmultiple : ∀ n, T₀ ≤ n → ∀ H : Finset ℕ,
      IsOffSelectorMinimalDeletionTransversal A C N₀ τ n H →
      (∀ h ∈ H, W₀ < h) → 2 ≤ H.card)
    (hesc : ∀ W T, ∃ n, T ≤ n ∧
      ∃ H : Finset ℕ,
        IsOffSelectorMinimalDeletionTransversal A C N₀ τ n H ∧
        ∀ h ∈ H, W < h) :
    ∃ n : ℕ → ℕ, ∃ H : ℕ → Finset ℕ,
      StrictMono n ∧
      (∀ i, IsOffSelectorMinimalDeletionTransversal A C N₀ τ (n i) (H i)) ∧
      (∀ i, 2 ≤ (H i).card) ∧
      (∀ i, ∀ h ∈ H (i + 1), n i < h) ∧
      ∀ i j, i < j → Disjoint (H i) (H j) := by
  obtain ⟨n, H, hnmono, hcomm, habove, hdisjoint⟩ :=
    escapingOffSelectorDeletionTransversals_has_blockSequence hesc
  let I := max W₀ T₀ + 1
  let n' : ℕ → ℕ := fun i => n (I + i)
  let H' : ℕ → Finset ℕ := fun i => H (I + i)
  have hn'mono : StrictMono n' := by
    intro i j hij
    exact hnmono (by omega)
  have hcomm' : ∀ i,
      IsOffSelectorMinimalDeletionTransversal A C N₀ τ (n' i) (H' i) := by
    intro i
    exact hcomm (I + i)
  have hcard' : ∀ i, 2 ≤ (H' i).card := by
    intro i
    have hindexPos : 0 < I + i := by
      dsimp [I]
      omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt hindexPos)
    have hnT₀ : T₀ ≤ n' i := by
      have hself : I + i ≤ n (I + i) := hnmono.id_le (I + i)
      have hTindex : T₀ ≤ I + i := by
        dsimp [I]
        omega
      exact hTindex.trans hself
    have hHW₀ : ∀ h ∈ H' i, W₀ < h := by
      intro h hh
      have hprev : n k < h := by
        apply habove k h
        simpa [H', hk] using hh
      have hkself : k ≤ n k := hnmono.id_le k
      dsimp [I] at hk
      omega
    exact hmultiple (n' i) hnT₀ (H' i) (hcomm' i) hHW₀
  have habove' : ∀ i, ∀ h ∈ H' (i + 1), n' i < h := by
    intro i h hh
    apply habove (I + i) h
    simpa [H', Nat.add_assoc] using hh
  have hdisjoint' : ∀ i j, i < j → Disjoint (H' i) (H' j) := by
    intro i j hij
    exact hdisjoint (I + i) (I + j) (by omega)
  exact ⟨n', H', hn'mono, hcomm', hcard',
    habove', hdisjoint'⟩

open Classical in

theorem counterexample_fixedRepairChannel_has_offSelectorStalls
    {A : Set ℕ} {N₀ w : ℕ} {B : Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ C ⊆ A, C.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ C) 3)
    (hcofinal : ∀ X, ∃ b ∈ A, X < b ∧
      HasTerminalRepairDestructionThrough A N₀ B w b) :
    ∃ C : Set ℕ, ∃ τ : ℕ → ℕ,
      C ⊆ A ∧ C.Infinite ∧ 0 ∉ C ∧ w ∉ C ∧ w ∈ A ∧
      (∀ b ∈ C, N₀ ≤ τ b ∧ b ≤ τ b ∧
        (∃ d ∈ insert b B, ∃ a ∈ A, d + a = τ b) ∧
        IsPrivateTriple (A \ (B : Set ℕ)) b (τ b) ∧
        ∃ u ∈ A \ C, ∃ v ∈ A \ C, w + u + v = τ b) ∧
      ∀ T, ∃ n, T ≤ n ∧ N₀ ≤ n ∧
        (∃ b ∈ C, ∃ a ∈ A, b + a = n) ∧
        (∀ b ∈ C, τ b ≠ n) ∧
        ¬∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
          x ∉ C ∧ y ∉ C ∧ z ∉ C ∧ x + y + z = n := by
  obtain ⟨C, τ, hCA, hCinf, h0C, hwC, hwA, hdata⟩ :=
    cofinal_fixedRepairChannel_has_conflictFree_selector hcofinal
  have hselected : ∀ b ∈ C,
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ C ∧ y ∉ C ∧ z ∉ C ∧ x + y + z = τ b := by
    intro b hbC
    obtain ⟨-, -, -, -, u, hu, v, hv, huv⟩ := hdata b hbC
    exact ⟨w, hwA, u, hu.1, v, hv.1, hwC, hu.2, hv.2, huv⟩
  have hstalls :=
    failure_with_selectedRepairs_forces_cofinal_offSelectorStalls
      τ h0 h0C hcov hselected (hfail C hCA hCinf)
  exact ⟨C, τ, hCA, hCinf, h0C, hwC, hwA, hdata, hstalls⟩

open Classical in
/-- A fixed-channel destruction whose failed target is a genuine new risk
`b+a`. -/
def HasSelfRepairDestructionThrough
    (A : Set ℕ) (N₀ : ℕ) (B : Finset ℕ) (w b : ℕ) : Prop :=
  ∃ n, N₀ ≤ n ∧ b ≤ n ∧
    (∃ a ∈ A, b + a = n) ∧
    IsPrivateTriple (A \ (B : Set ℕ)) b n ∧
    HasRepairThrough A w b n

open Classical in
/-- A fixed-channel destruction whose failed target comes from one specified old
prefix element `d`. -/
def HasCollateralRepairDestructionThrough
    (A : Set ℕ) (N₀ : ℕ) (B : Finset ℕ)
    (w d b : ℕ) : Prop :=
  ∃ n, N₀ ≤ n ∧ b ≤ n ∧
    (∃ a ∈ A, d + a = n) ∧
    IsPrivateTriple (A \ (B : Set ℕ)) b n ∧
    HasRepairThrough A w b n

open Classical in
/-- Retaining the source of the risk gives an exact pointwise split:
the new required element `b` caused the destruction, or one old `d∈B` did. -/
theorem terminalRepairDestruction_self_or_collateral
    {A : Set ℕ} {N₀ w b : ℕ} {B : Finset ℕ}
    (h : HasTerminalRepairDestructionThrough A N₀ B w b) :
    HasSelfRepairDestructionThrough A N₀ B w b ∨
      ∃ d ∈ B, HasCollateralRepairDestructionThrough A N₀ B w d b := by
  obtain ⟨n, hn, hbn, hrisk, hprivate, hrepair⟩ := h
  obtain ⟨d, hdInsert, a, haA, hda⟩ := hrisk
  rcases Finset.mem_insert.1 hdInsert with hdb | hdB
  · subst d
    exact Or.inl
      ⟨n, hn, hbn, ⟨a, haA, hda⟩, hprivate, hrepair⟩
  · exact Or.inr
      ⟨d, hdB, n, hn, hbn, ⟨a, haA, hda⟩,
        hprivate, hrepair⟩

open Classical in

theorem cofinal_fixedRepairChannel_self_or_fixedCollateral
    {A : Set ℕ} {N₀ w : ℕ} {B : Finset ℕ}
    (hcofinal : ∀ X, ∃ b ∈ A, X < b ∧
      HasTerminalRepairDestructionThrough A N₀ B w b) :
    (∀ X, ∃ b ∈ A, X < b ∧
      HasSelfRepairDestructionThrough A N₀ B w b) ∨
    (∃ d ∈ B, ∀ X, ∃ b ∈ A, X < b ∧
      HasCollateralRepairDestructionThrough A N₀ B w d b) := by
  by_cases hself : ∀ X, ∃ b ∈ A, X < b ∧
      HasSelfRepairDestructionThrough A N₀ B w b
  · exact Or.inl hself
  · right
    push Not at hself
    obtain ⟨X₀, hX₀⟩ := hself
    have hcollateral : ∀ X, ∃ b, X < b ∧
        ∃ d ∈ B, b ∈ A ∧
          HasCollateralRepairDestructionThrough A N₀ B w d b := by
      intro X
      obtain ⟨b, hbA, hbLarge, hrepair⟩ :=
        hcofinal (max X X₀)
      rcases terminalRepairDestruction_self_or_collateral hrepair with
        hnew | hold
      · exact absurd hnew (hX₀ b hbA (by omega))
      · obtain ⟨d, hdB, hold⟩ := hold
        exact ⟨b, by omega, d, hdB, hbA, hold⟩
    obtain ⟨d, hdB, hdCofinal⟩ :=
      finite_cofinal_pigeonhole hcollateral
    refine ⟨d, hdB, ?_⟩
    intro X
    obtain ⟨b, hbX, hbA, hrepair⟩ := hdCofinal X
    exact ⟨b, hbA, hbX, hrepair⟩

open Classical in
/-- A collateral repair through fixed `w,d` is an exact fixed-shift
identity.  If `w≤d`, it gives a surviving pair for `a+(d-w)`; if `d≤w`,
it expresses `a` as the fixed shift `w-d` plus that pair. -/
theorem collateralRepairDestruction_fixedShift_identity
    {A : Set ℕ} {N₀ w d b : ℕ} {B : Finset ℕ}
    (h : HasCollateralRepairDestructionThrough A N₀ B w d b) :
    ∃ a ∈ A, ∃ u ∈ A, ∃ v ∈ A,
      u ≠ b ∧ v ≠ b ∧ d + a = w + u + v ∧
      ((w ≤ d ∧ (d - w) + a = u + v) ∨
       (d ≤ w ∧ a = (w - d) + u + v)) := by
  obtain ⟨n, hn, hbn, hrisk, hprivate, hrepair⟩ := h
  obtain ⟨a, haA, hda⟩ := hrisk
  obtain ⟨u, huA, v, hvA, support_transversal, hvb, huv⟩ :=
    repairThrough_gives_shifted_pair hrepair
  refine ⟨a, haA, u, huA, v, hvA, support_transversal, hvb, by omega, ?_⟩
  rcases le_total w d with hwd | hdw
  · exact Or.inl ⟨hwd, by omega⟩
  · exact Or.inr ⟨hdw, by omega⟩

open Classical in

theorem counterexample_cofinal_absolute_or_fixed_prefix_repairs
    {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ B : Finset ℕ,
      FinitePrefixServesRisks A N₀ B ∧ 0 ∉ B ∧
      ((∀ X, ∃ b ∈ A, X < b ∧
          HasAbsoluteTerminalDestruction A N₀ B b) ∨
       ∃ w ∈ B, ∀ X, ∃ b ∈ A, X < b ∧
          HasTerminalRepairDestructionThrough A N₀ B w b) := by
  obtain ⟨B, hserved, h0B, hwound⟩ :=
    counterexample_terminal_prefix_private_destruction_fork h0 hcov hfail
  have hcandidate : ∀ X, ∃ b ∈ A, X < b ∧
      (HasAbsoluteTerminalDestruction A N₀ B b ∨
       ∃ w ∈ B, HasTerminalRepairDestructionThrough A N₀ B w b) := by
    intro X
    obtain ⟨b, hbA, hbLarge⟩ :=
      pairCovers_unbounded hcov (max (X + 1) (B.sup id + 1))
    have hbX : X < b := by omega
    have hbpos : 0 < b := by omega
    have hbAbove : ∀ w ∈ B, w < b := by
      intro w hwB
      have hwSup : w ≤ B.sup id := Finset.le_sup (f := id) hwB
      omega
    obtain ⟨n, hn, hbn, hrisk, hprivate, habs | hrepair⟩ :=
      hwound b hbA hbpos hbAbove
    · exact ⟨b, hbA, hbX, Or.inl
        ⟨n, hn, hbn, hrisk, hprivate, habs⟩⟩
    · obtain ⟨w, hwB, hthrough⟩ :=
        prefixRepairTriple_has_repairThrough hrepair
      exact ⟨b, hbA, hbX, Or.inr
        ⟨w, hwB, n, hn, hbn, hrisk, hprivate, hthrough⟩⟩
  by_cases habsolute :
      ∀ X, ∃ b ∈ A, X < b ∧
        HasAbsoluteTerminalDestruction A N₀ B b
  · exact ⟨B, hserved, h0B, Or.inl habsolute⟩
  · push Not at habsolute
    obtain ⟨X₀, hX₀⟩ := habsolute
    have hrepairs : ∀ X, ∃ b, X < b ∧
        ∃ w ∈ B,
          b ∈ A ∧ HasTerminalRepairDestructionThrough A N₀ B w b := by
      intro X
      obtain ⟨b, hbA, hbLarge, habs | hrepair⟩ :=
        hcandidate (max X X₀)
      · exact absurd habs (hX₀ b hbA (by omega))
      · obtain ⟨w, hwB, hrepair⟩ := hrepair
        exact ⟨b, by omega, w, hwB, hbA, hrepair⟩
    obtain ⟨w, hwB, hwCofinal⟩ :=
      finite_cofinal_pigeonhole hrepairs
    refine ⟨B, hserved, h0B, Or.inr ⟨w, hwB, ?_⟩⟩
    intro X
    obtain ⟨b, hbX, hbA, hrepair⟩ := hwCofinal X
    exact ⟨b, hbA, hbX, hrepair⟩

open Classical in
/-- The data of an absolute private destruction whose required element is larger than its
co-offset. -/
def IsBigAbsolutePrivateDestruction
    (A : Set ℕ) (N₀ b n : ℕ) : Prop :=
  N₀ ≤ n ∧ b ≤ n ∧ n < 2 * b ∧ IsPrivateTriple A b n

open Classical in

theorem no_cofinal_big_absolute_private_required_elements
    {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) :
    ¬(∀ X, ∃ b ∈ A, X < b ∧
      ∃ n, IsBigAbsolutePrivateDestruction A N₀ b n) := by
  intro hcofinal
  have hbound : ∃ Q X₀, ∀ b ∈ A, X₀ < b → ∀ n,
      IsBigAbsolutePrivateDestruction A N₀ b n → n - b < Q := by
    by_cases hlargeOffset : ∀ X, ∃ b ∈ A, X < b ∧
        ∃ n, IsBigAbsolutePrivateDestruction A N₀ b n ∧ N₀ ≤ n - b
    · obtain ⟨b₁, hb₁A, hb₁large, n₁, hbig₁, hq₁N⟩ :=
        hlargeOffset (N₀ + 3)
      refine ⟨max N₀ n₁, 0, ?_⟩
      intro b hbA hbpos n hbig
      by_cases hqN : N₀ ≤ n - b
      · by_contra hqBound
        have hn₁q : n₁ ≤ n - b := by
          have := Nat.le_of_not_gt hqBound
          omega
        have hN₁ : N₀ + b₁ ≤ n₁ := by
          have := hbig₁.2.1
          omega
        have hN : N₀ + b ≤ n := by
          have := hbig.2.1
          omega
        have hsep : n₁ + b ≤ n := by omega
        exact no_big_required_element_stacking h0 hcov
          hbig₁.2.2.2 hbig.2.2.2
          hbig₁.2.2.1 hN₁ hbig.2.2.1 hN
          (by omega) hsep
      · have := Nat.lt_of_not_ge hqN
        exact this.trans_le (le_max_left N₀ n₁)
    · simp only [not_forall] at hlargeOffset
      obtain ⟨X₀, hX₀⟩ := hlargeOffset
      refine ⟨N₀, X₀, ?_⟩
      intro b hbA hbX n hbig
      by_contra hq
      have hqN : N₀ ≤ n - b := Nat.le_of_not_gt hq
      exact hX₀ ⟨b, hbA, hbX, n, hbig, hqN⟩
  obtain ⟨Q, X₀, hbound⟩ := hbound
  have hfixedInput : ∀ X, ∃ b, X < b ∧
      ∃ q ∈ Finset.range Q,
        b ∈ A ∧ ∃ n, IsBigAbsolutePrivateDestruction A N₀ b n ∧
          n - b = q := by
    intro X
    obtain ⟨b, hbA, hbLarge, n, hbig⟩ :=
      hcofinal (max X X₀)
    have hbX₀ : X₀ < b := by omega
    have hqQ := hbound b hbA hbX₀ n hbig
    exact ⟨b, by omega, n - b, Finset.mem_range.2 hqQ,
      hbA, n, hbig, rfl⟩
  have hfixedInput' : ∀ X, ∃ b, X < b ∧
      ∃ q ∈ Finset.range Q,
        (b ∈ A ∧ ∃ n, IsBigAbsolutePrivateDestruction A N₀ b n ∧
          n - b = q) := hfixedInput
  obtain ⟨q, hqQ, hqCofinal⟩ :=
    finite_cofinal_pigeonhole hfixedInput'
  obtain ⟨b₁, hb₁q, hb₁A, n₁, hbig₁, hn₁q⟩ :=
    hqCofinal q
  obtain ⟨b₂, hb₂large, hb₂A, n₂, hbig₂, hn₂q⟩ :=
    hqCofinal (b₁ + N₀ + 1)
  have hqb₁ : q < b₁ := by
    have := hbig₁.2.2.1
    have := hbig₁.2.1
    omega
  have hb₂pos : 0 < b₂ := by omega
  have hn₂sum : n₂ = b₂ + q := by
    calc
      n₂ = (n₂ - b₂) + b₂ :=
        (Nat.sub_add_cancel hbig₂.2.1).symm
      _ = q + b₂ := by rw [hn₂q]
      _ = b₂ + q := Nat.add_comm _ _
  have hlow : n₂ < b₂ + b₁ := by
    rw [hn₂sum]
    omega
  have hhigh : b₁ + N₀ ≤ n₂ := by omega
  have hdesert :=
    hbig₂.2.2.2.exclusion_interval h0 hcov hb₂pos hb₁A
      hlow hhigh
  omega

open Classical in
/-- An unbounded singleton-deletion transversal stream cannot remain in the big
required element regime.  After thinning, its absolute private off-selector
destructions all satisfy `2h≤n`. -/
theorem cofinal_offSelector_absolutePrivate_destructions_are_nonbig
    {A C : Set ℕ} {N₀ : ℕ} {τ : ℕ → ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) (hCA : C ⊆ A)
    (hstream : ∀ W T, ∃ n, T ≤ n ∧ ∃ h ∈ C,
      W < h ∧ h ≤ n ∧ N₀ ≤ n ∧
      τ h ≠ n ∧ IsPrivateTriple A h n) :
    ∀ W T, ∃ n, T ≤ n ∧ ∃ h ∈ C,
      W < h ∧ h ≤ n ∧ N₀ ≤ n ∧ 2 * h ≤ n ∧
      τ h ≠ n ∧ IsPrivateTriple A h n := by
  by_contra hnonbig
  push Not at hnonbig
  obtain ⟨W₀, T₀, hbad⟩ := hnonbig
  have hbigCofinal : ∀ X, ∃ h ∈ A, X < h ∧
      ∃ n, IsBigAbsolutePrivateDestruction A N₀ h n := by
    intro X
    obtain ⟨n, hnT₀, h, hhC, hhLarge, hhn, hn₀, hoff, hprivate⟩ :=
      hstream (max X W₀) T₀
    have hnotNonbig : ¬2 * h ≤ n := by
      intro hnonbig
      exact hbad n hnT₀ h hhC (by omega) hhn hn₀
        hnonbig hoff hprivate
    exact ⟨h, hCA hhC, by omega, n,
      hn₀, hhn, Nat.lt_of_not_ge hnotNonbig, hprivate⟩
  exact no_cofinal_big_absolute_private_required_elements h0 hcov hbigCofinal

open Classical in
/-- A fixed deleted point occurs in off-selector minimal deletion transversals
cofinally. -/
def HasRecurrentOffSelectorRequiredElement
    (A C : Set ℕ) (N₀ : ℕ) (τ : ℕ → ℕ) : Prop :=
  ∃ h ∈ C, ∀ T, ∃ n, T ≤ n ∧
    ∃ H : Finset ℕ,
      IsOffSelectorMinimalDeletionTransversal A C N₀ τ n H ∧ h ∈ H

open Classical in
/-- Cofinal non-big absolute private destructions arising from singleton
off-selector deletion transversals. -/
def HasCofinalNonbigOffSelectorPrivateStream
    (A C : Set ℕ) (N₀ : ℕ) (τ : ℕ → ℕ) : Prop :=
  ∀ W T, ∃ n, T ≤ n ∧ ∃ h ∈ C,
    W < h ∧ h ≤ n ∧ N₀ ≤ n ∧ 2 * h ≤ n ∧
    τ h ≠ n ∧ IsPrivateTriple A h n

open Classical in
/-- A block-separated sequence of non-singleton off-selector minimal
deletion transversals. -/
def HasBlockSeparatedMultipleOffSelectorDeletionTransversals
    (A C : Set ℕ) (N₀ : ℕ) (τ : ℕ → ℕ) : Prop :=
  ∃ n : ℕ → ℕ, ∃ H : ℕ → Finset ℕ,
    StrictMono n ∧
    (∀ i, IsOffSelectorMinimalDeletionTransversal A C N₀ τ (n i) (H i)) ∧
    (∀ i, 2 ≤ (H i).card) ∧
    (∀ i, ∀ h ∈ H (i + 1), n i < h) ∧
    ∀ i j, i < j → Disjoint (H i) (H j)

open Classical in
/-- Every target in the finite schedule attached to a deleted point has
a representation surviving the whole deletion. -/
def HasSurvivingFiniteCoverageSchedule
    (A C : Set ℕ) (σ : ℕ → Finset ℕ) : Prop :=
  ∀ b ∈ C, ∀ m ∈ σ b,
    ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
      x ∉ C ∧ y ∉ C ∧ z ∉ C ∧ x + y + z = m

open Classical in
/-- A surviving finite coverage schedule with exactly `k` distinct targets
attached to every deleted point. -/
def HasUniformSurvivingCoverageSchedule
    (A C : Set ℕ) (k : ℕ) : Prop :=
  ∃ σ : ℕ → Finset ℕ,
    HasSurvivingFiniteCoverageSchedule A C σ ∧
    ∀ b ∈ C, (σ b).card = k

open Classical in
/-- A finite coverage schedule whose labels are genuine: every target
attached to `b` is actually threatened by deleting `b`. -/
def HasSurvivingFiniteRiskSchedule
    (A C : Set ℕ) (σ : ℕ → Finset ℕ) : Prop :=
  ∀ b ∈ C, ∀ m ∈ σ b,
    (∃ a ∈ A, b + a = m) ∧
    ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
      x ∉ C ∧ y ∉ C ∧ z ∉ C ∧ x + y + z = m

open Classical in
/-- Forgetting the genuine-risk labels leaves an ordinary surviving
finite coverage schedule. -/
theorem HasSurvivingFiniteRiskSchedule.toCoverage
    {A C : Set ℕ} {σ : ℕ → Finset ℕ}
    (h : HasSurvivingFiniteRiskSchedule A C σ) :
    HasSurvivingFiniteCoverageSchedule A C σ := by
  intro b hbC m hm
  exact (h b hbC m hm).2

open Classical in

theorem finiteCoverageSchedule_basis_iff_eventual_offScheduleRisks
    {A C : Set ℕ} {N₀ : ℕ} (σ : ℕ → Finset ℕ)
    (h0 : 0 ∈ A) (h0C : 0 ∉ C) (hcov : PairCovers A N₀)
    (hschedule : HasSurvivingFiniteCoverageSchedule A C σ) :
    IsExactTupleAsymptoticBasis (A \ C) 3 ↔
      ∃ M, ∀ n, M ≤ n →
        (∃ b ∈ C, ∃ a ∈ A, b + a = n) →
        (∀ b ∈ C, n ∉ σ b) →
        ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
          x ∉ C ∧ y ∉ C ∧ z ∉ C ∧ x + y + z = n := by
  constructor
  · rintro ⟨M, hbasis⟩
    refine ⟨M, ?_⟩
    intro n hn hrisk hoff
    obtain ⟨v, hv, hvsum⟩ := hbasis n hn
    exact ⟨v 0, (hv 0).1, v 1, (hv 1).1, v 2, (hv 2).1,
      (hv 0).2, (hv 1).2, (hv 2).2,
      by simpa [Fin.sum_univ_three] using hvsum⟩
  · rintro ⟨M, hoff⟩
    have hcov' : PairCovers A (max N₀ M) := by
      intro n hn
      exact hcov n ((le_max_left N₀ M).trans hn)
    apply deletion_criterion_local h0 h0C hcov'
    intro n hn hrisk
    by_cases hhit : ∃ b ∈ C, n ∈ σ b
    · obtain ⟨b, hbC, hnσ⟩ := hhit
      exact hschedule b hbC n hnσ
    · apply hoff n ((le_max_right N₀ M).trans hn) hrisk
      intro b hbC hnσ
      exact hhit ⟨b, hbC, hnσ⟩

open Classical in

theorem failure_with_finiteCoverageSchedule_forces_cofinal_offScheduleStalls
    {A C : Set ℕ} {N₀ : ℕ} (σ : ℕ → Finset ℕ)
    (h0 : 0 ∈ A) (h0C : 0 ∉ C) (hcov : PairCovers A N₀)
    (hschedule : HasSurvivingFiniteCoverageSchedule A C σ)
    (hfail : ¬IsExactTupleAsymptoticBasis (A \ C) 3) :
    ∀ T, ∃ n, T ≤ n ∧ N₀ ≤ n ∧
      (∃ b ∈ C, ∃ a ∈ A, b + a = n) ∧
      (∀ b ∈ C, n ∉ σ b) ∧
      ¬∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ C ∧ y ∉ C ∧ z ∉ C ∧ x + y + z = n := by
  simp only [IsExactTupleAsymptoticBasis,
    not_exists, not_forall] at hfail
  intro T
  obtain ⟨n, hn, hnorep⟩ := hfail (max T N₀)
  have hnT : T ≤ n := (le_max_left T N₀).trans hn
  have hn₀ : N₀ ≤ n := (le_max_right T N₀).trans hn
  obtain ⟨x, hxA, y, hyA, hxy⟩ := hcov n hn₀
  have hrisk : ∃ b ∈ C, ∃ a ∈ A, b + a = n := by
    by_cases hxC : x ∈ C
    · exact ⟨x, hxC, y, hyA, hxy⟩
    · by_cases hyC : y ∈ C
      · exact ⟨y, hyC, x, hxA, by omega⟩
      · exfalso
        apply hnorep ![x, y, 0]
        constructor
        · intro i
          match i with
          | 0 => exact ⟨hxA, hxC⟩
          | 1 => exact ⟨hyA, hyC⟩
          | 2 => exact ⟨h0, h0C⟩
        · simpa [Fin.sum_univ_three] using hxy
  have hoff : ∀ b ∈ C, n ∉ σ b := by
    intro b hbC hnσ
    obtain ⟨p, hpA, q, hqA, r, hrA, hpC, hqC, hrC, hpqr⟩ :=
      hschedule b hbC n hnσ
    apply hnorep ![p, q, r]
    constructor
    · intro i
      match i with
      | 0 => exact ⟨hpA, hpC⟩
      | 1 => exact ⟨hqA, hqC⟩
      | 2 => exact ⟨hrA, hrC⟩
    · simpa [Fin.sum_univ_three] using hpqr
  refine ⟨n, hnT, hn₀, hrisk, hoff, ?_⟩
  rintro ⟨p, hpA, q, hqA, r, hrA, hpC, hqC, hrC, hpqr⟩
  apply hnorep ![p, q, r]
  constructor
  · intro i
    match i with
    | 0 => exact ⟨hpA, hpC⟩
    | 1 => exact ⟨hqA, hqC⟩
    | 2 => exact ⟨hrA, hrC⟩
  · simpa [Fin.sum_univ_three] using hpqr

open Classical in
/-- A nonempty minimal representation deletion transversal for a target lying outside
every currently scheduled finite coverage list. -/
def IsOffScheduleMinimalDeletionTransversal
    (A C : Set ℕ) (N₀ : ℕ) (σ : ℕ → Finset ℕ)
    (n : ℕ) (H : Finset ℕ) : Prop :=
  N₀ ≤ n ∧
  (∀ b ∈ C, n ∉ σ b) ∧
  H.Nonempty ∧
  IsRepSupportTransversal A n H ∧
  (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
  H ⊆ (Finset.range (n + 1)).filter (· ∈ C)

open Classical in
/-- Every stall outside a finite coverage schedule has a finite nonempty
minimal deletion transversal contained in the deleted points below the target. -/
theorem failure_with_finiteCoverageSchedule_forces_offSchedule_minimalDeletionTransversals
    {A C : Set ℕ} {N₀ : ℕ} (σ : ℕ → Finset ℕ)
    (h0 : 0 ∈ A) (h0C : 0 ∉ C) (hcov : PairCovers A N₀)
    (hschedule : HasSurvivingFiniteCoverageSchedule A C σ)
    (hfail : ¬IsExactTupleAsymptoticBasis (A \ C) 3) :
    ∀ T, ∃ n, T ≤ n ∧
      ∃ H : Finset ℕ,
        IsOffScheduleMinimalDeletionTransversal A C N₀ σ n H := by
  intro T
  obtain ⟨n, hnT, hn₀, hrisk, hoff, hno⟩ :=
    failure_with_finiteCoverageSchedule_forces_cofinal_offScheduleStalls
      σ h0 h0C hcov hschedule hfail T
  have hdead : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
      x + y + z = n → x ∈ C ∨ y ∈ C ∨ z ∈ C := by
    intro x hxA y hyA z hzA hxyz
    by_cases hxC : x ∈ C
    · exact Or.inl hxC
    · by_cases hyC : y ∈ C
      · exact Or.inr (Or.inl hyC)
      · by_cases hzC : z ∈ C
        · exact Or.inr (Or.inr hzC)
        · exact (hno
            ⟨x, hxA, y, hyA, z, hzA, hxC, hyC, hzC, hxyz⟩).elim
  have hhub :=
    failing_support_transversal_subset_deletion (A := A) (B := C) hdead
  obtain ⟨H, hHsub, hHhub, hHmin⟩ := exists_minimal_support_transversal hhub
  have hHne : H.Nonempty :=
    support_transversal_nonempty_of_covering h0 hcov hn₀ hHhub
  exact ⟨n, hnT, H,
    hn₀, hoff, hHne, hHhub, hHmin, hHsub⟩

open Classical in
/-- A block-separated sequence of non-singleton minimal deletion transversals outside
an arbitrary finite coverage schedule. -/
def HasBlockSeparatedMultipleOffScheduleDeletionTransversals
    (A C : Set ℕ) (N₀ : ℕ) (σ : ℕ → Finset ℕ) : Prop :=
  ∃ n : ℕ → ℕ, ∃ H : ℕ → Finset ℕ,
    StrictMono n ∧
    (∀ i, IsOffScheduleMinimalDeletionTransversal A C N₀ σ (n i) (H i)) ∧
    (∀ i, 2 ≤ (H i).card) ∧
    (∀ i, ∀ h ∈ H (i + 1), n i < h) ∧
    ∀ i j, i < j → Disjoint (H i) (H j)

open Classical in

theorem finiteCoverageSchedule_recurrentRequiredElement_or_escapingDeletionTransversals
    {A C : Set ℕ} {N₀ : ℕ} (σ : ℕ → Finset ℕ)
    (h0 : 0 ∈ A) (h0C : 0 ∉ C) (hcov : PairCovers A N₀)
    (hschedule : HasSurvivingFiniteCoverageSchedule A C σ)
    (hfail : ¬IsExactTupleAsymptoticBasis (A \ C) 3) :
    (∃ h ∈ C, ∀ T, ∃ n, T ≤ n ∧
      ∃ H : Finset ℕ,
        IsOffScheduleMinimalDeletionTransversal A C N₀ σ n H ∧ h ∈ H) ∨
    (∀ W T, ∃ n, T ≤ n ∧
      ∃ H : Finset ℕ,
        IsOffScheduleMinimalDeletionTransversal A C N₀ σ n H ∧
        ∀ h ∈ H, W < h) := by
  by_cases hrec : ∃ h ∈ C, ∀ T, ∃ n, T ≤ n ∧
      ∃ H : Finset ℕ,
        IsOffScheduleMinimalDeletionTransversal A C N₀ σ n H ∧ h ∈ H
  · exact Or.inl hrec
  · right
    have hboundedC : ∀ h ∈ C, ∃ T, ∀ n, T ≤ n →
        ∀ H : Finset ℕ,
          IsOffScheduleMinimalDeletionTransversal A C N₀ σ n H → h ∉ H := by
      intro h hhC
      by_contra hnoT
      push Not at hnoT
      exact hrec ⟨h, hhC, hnoT⟩
    have hthreshold : ∀ h, ∃ T, h ∈ C → ∀ n, T ≤ n →
        ∀ H : Finset ℕ,
          IsOffScheduleMinimalDeletionTransversal A C N₀ σ n H → h ∉ H := by
      intro h
      by_cases hhC : h ∈ C
      · obtain ⟨T, hT⟩ := hboundedC h hhC
        exact ⟨T, fun _ => hT⟩
      · exact ⟨0, fun hmem => absurd hmem hhC⟩
    choose g hg using hthreshold
    intro W T
    let F : Finset ℕ :=
      (Finset.range (W + 1)).filter (· ∈ C)
    let T' := max T (F.sup g)
    obtain ⟨n, hnT', H, hcomm⟩ :=
      failure_with_finiteCoverageSchedule_forces_offSchedule_minimalDeletionTransversals
        σ h0 h0C hcov hschedule hfail T'
    refine ⟨n, ?_, H, hcomm, ?_⟩
    · dsimp [T'] at hnT'
      omega
    · intro h hhH
      by_contra hnotAbove
      have hhW : h ≤ W := Nat.le_of_not_gt hnotAbove
      have hhC : h ∈ C := by
        have hhFilter := hcomm.2.2.2.2.2 hhH
        exact (Finset.mem_filter.1 hhFilter).2
      have hhF : h ∈ F := by
        exact Finset.mem_filter.2
          ⟨Finset.mem_range.2 (by omega), hhC⟩
      have hgSup : g h ≤ F.sup g :=
        Finset.le_sup (f := g) hhF
      have hgn : g h ≤ n := by
        dsimp [T'] at hnT'
        omega
      exact (hg h hhC n hgn H hcomm) hhH

open Classical in

theorem escapingOffScheduleDeletionTransversals_singletonPrivate_or_multiple
    {A C : Set ℕ} {N₀ : ℕ} {σ : ℕ → Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hesc : ∀ W T, ∃ n, T ≤ n ∧
      ∃ H : Finset ℕ,
        IsOffScheduleMinimalDeletionTransversal A C N₀ σ n H ∧
        ∀ h ∈ H, W < h) :
    (∀ W T, ∃ n, T ≤ n ∧ ∃ h ∈ C,
      W < h ∧ h ≤ n ∧ N₀ ≤ n ∧
      (∀ b ∈ C, n ∉ σ b) ∧ IsPrivateTriple A h n) ∨
    (∀ W T, ∃ n, T ≤ n ∧ ∃ H : Finset ℕ,
      IsOffScheduleMinimalDeletionTransversal A C N₀ σ n H ∧
      (∀ h ∈ H, W < h) ∧ 2 ≤ H.card) := by
  by_cases hsingle : ∀ W T, ∃ n, T ≤ n ∧
      ∃ H : Finset ℕ,
        IsOffScheduleMinimalDeletionTransversal A C N₀ σ n H ∧
        (∀ h ∈ H, W < h) ∧ H.card = 1
  · left
    intro W T
    obtain ⟨n, hnT, H, hcomm, habove, hHcard⟩ :=
      hsingle W T
    obtain ⟨h, rfl⟩ := Finset.card_eq_one.mp hHcard
    have hhC : h ∈ C := by
      have hhFilter :=
        hcomm.2.2.2.2.2 (Finset.mem_singleton_self h)
      exact (Finset.mem_filter.1 hhFilter).2
    have hhle : h ≤ n := by
      have hhFilter :=
        hcomm.2.2.2.2.2 (Finset.mem_singleton_self h)
      have := Finset.mem_range.1 (Finset.mem_filter.1 hhFilter).1
      omega
    have hprivate : IsPrivateTriple A h n :=
      privateTriple_of_singleton_support_transversal h0 hcov hcomm.1
        hcomm.2.2.2.1
    exact ⟨n, hnT, h, hhC,
      habove h (Finset.mem_singleton_self h), hhle,
      hcomm.1, hcomm.2.1, hprivate⟩
  · right
    push Not at hsingle
    obtain ⟨W₀, T₀, hnotSingle⟩ := hsingle
    have hmultiple : ∀ n, T₀ ≤ n → ∀ H : Finset ℕ,
        IsOffScheduleMinimalDeletionTransversal A C N₀ σ n H →
        (∀ h ∈ H, W₀ < h) → 2 ≤ H.card := by
      intro n hn H hcomm habove
      have hpos : 0 < H.card :=
        Finset.card_pos.mpr hcomm.2.2.1
      have hneOne : H.card ≠ 1 :=
        hnotSingle n hn H hcomm habove
      omega
    intro W T
    obtain ⟨n, hn, H, hcomm, habove⟩ :=
      hesc (max W W₀) (max T T₀)
    have hnT : T ≤ n := by omega
    have hnT₀ : T₀ ≤ n := by omega
    have haboveW₀ : ∀ h ∈ H, W₀ < h := by
      intro h hh
      have := habove h hh
      omega
    have hHcard : 2 ≤ H.card :=
      hmultiple n hnT₀ H hcomm haboveW₀
    refine ⟨n, hnT, H, hcomm, ?_, hHcard⟩
    intro h hh
    have := habove h hh
    omega

open Classical in
/-- Escaping multi-required element off-schedule deletion transversals admit a
block-separated diagonal. -/
theorem escapingMultipleOffScheduleDeletionTransversals_has_blockSequence
    {A C : Set ℕ} {N₀ : ℕ} {σ : ℕ → Finset ℕ}
    (hmulti : ∀ W T, ∃ n, T ≤ n ∧
      ∃ H : Finset ℕ,
        IsOffScheduleMinimalDeletionTransversal A C N₀ σ n H ∧
        (∀ h ∈ H, W < h) ∧ 2 ≤ H.card) :
    HasBlockSeparatedMultipleOffScheduleDeletionTransversals A C N₀ σ := by
  have hpick : ∀ W, ∃ p : ℕ × Finset ℕ,
      W < p.1 ∧
      IsOffScheduleMinimalDeletionTransversal A C N₀ σ p.1 p.2 ∧
      (∀ h ∈ p.2, W < h) ∧ 2 ≤ p.2.card := by
    intro W
    obtain ⟨n, hn, H, hcomm, habove, hcard⟩ :=
      hmulti W (W + 1)
    exact ⟨(n, H), by omega, hcomm, habove, hcard⟩
  choose p hp using hpick
  let s : ℕ → ℕ × Finset ℕ :=
    Nat.rec (p 0) (fun _ q => p q.1)
  let n : ℕ → ℕ := fun i => (s i).1
  let H : ℕ → Finset ℕ := fun i => (s i).2
  have hs_zero : s 0 = p 0 := rfl
  have hs_succ : ∀ i, s (i + 1) = p (s i).1 := by
    intro i
    rfl
  have hn_step : ∀ i, n i < n (i + 1) := by
    intro i
    rw [show n i = (s i).1 from rfl,
      show n (i + 1) = (s (i + 1)).1 from rfl,
      hs_succ]
    exact (hp (s i).1).1
  have hnmono : StrictMono n :=
    strictMono_nat_of_lt_succ hn_step
  have hcomm : ∀ i,
      IsOffScheduleMinimalDeletionTransversal A C N₀ σ (n i) (H i) := by
    intro i
    cases i with
    | zero =>
        rw [show n 0 = (s 0).1 from rfl,
          show H 0 = (s 0).2 from rfl, hs_zero]
        exact (hp 0).2.1
    | succ i =>
        rw [show n (i + 1) = (s (i + 1)).1 from rfl,
          show H (i + 1) = (s (i + 1)).2 from rfl, hs_succ]
        exact (hp (s i).1).2.1
  have hcard : ∀ i, 2 ≤ (H i).card := by
    intro i
    cases i with
    | zero =>
        rw [show H 0 = (s 0).2 from rfl, hs_zero]
        exact (hp 0).2.2.2
    | succ i =>
        rw [show H (i + 1) = (s (i + 1)).2 from rfl, hs_succ]
        exact (hp (s i).1).2.2.2
  have habove : ∀ i, ∀ h ∈ H (i + 1), n i < h := by
    intro i h hh
    have hh' : h ∈ (p (s i).1).2 := by
      dsimp [H] at hh
      rw [hs_succ] at hh
      exact hh
    exact (hp (s i).1).2.2.1 h hh'
  refine ⟨n, H, hnmono, hcomm, hcard, habove, ?_⟩
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  obtain ⟨r, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hir : i ≤ r := by omega
  have hxle : x ≤ n i := by
    have hxFilter := (hcomm i).2.2.2.2.2 hxi
    have hxRange := (Finset.mem_filter.1 hxFilter).1
    have := Finset.mem_range.1 hxRange
    omega
  have hnir : n i ≤ n r := hnmono.monotone hir
  have hrx : n r < x := habove r x hxj
  omega

open Classical in

theorem blockSeparatedMultipleOffScheduleDeletionTransversals_scheduleIncrement
    {A C : Set ℕ} {N₀ k : ℕ} {σ : ℕ → Finset ℕ}
    (hCA : C ⊆ A)
    (hschedule : HasSurvivingFiniteCoverageSchedule A C σ)
    (hcard : ∀ b ∈ C, (σ b).card = k)
    (hblocks :
      HasBlockSeparatedMultipleOffScheduleDeletionTransversals A C N₀ σ) :
    ∃ D ⊆ C, D.Infinite ∧
      HasUniformSurvivingCoverageSchedule A D (k + 1) := by
  obtain ⟨n, H, hnmono, hcomm, hcommitteeCard, habove, hdisjoint⟩ :=
    hblocks
  have htwo : ∀ i, ∃ d ∈ H i, ∃ e ∈ H i, d ≠ e := by
    intro i
    apply Finset.one_lt_card.mp
    have := hcommitteeCard i
    omega
  choose d hdH e heH hde using htwo
  have hcowitness : ∀ i, ∃ u ∈ A, ∃ v ∈ A,
      e i + u + v = n i ∧
      ∀ g ∈ H i, g ≠ e i → u ≠ g ∧ v ≠ g := by
    intro i
    exact minimalRepSupportTransversal_member_has_pairCowitness
      (hcomm i).2.2.2.1 (hcomm i).2.2.2.2.1 (heH i)
  choose u huA v hvA huv havoid using hcowitness
  have hdInjective : Function.Injective d := by
    intro i j hdij
    by_contra hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hdis := Finset.disjoint_left.mp (hdisjoint i j hij)
      have hdiHj : d i ∈ H j := by
        rw [hdij]
        exact hdH j
      exact hdis (hdH i) hdiHj
    · have hdis := Finset.disjoint_left.mp (hdisjoint j i hji)
      have hdjHi : d j ∈ H i := by
        rw [← hdij]
        exact hdH i
      exact hdis (hdH j) hdjHi
  let K : Set ℕ := Set.range d
  have hKinf : K.Infinite :=
    Set.infinite_range_of_injective hdInjective
  let idx : ℕ → ℕ := fun x =>
    if hx : x ∈ K then Classical.choose hx else 0
  have hidx : ∀ x ∈ K, d (idx x) = x := by
    intro x hx
    simpa [idx, hx] using Classical.choose_spec hx
  let f : ℕ → Finset ℕ := fun x =>
    {e (idx x), u (idx x), v (idx x)}
  have hfcard : ∀ x ∈ K, (f x).card ≤ 3 := by
    intro x hx
    calc
      (f x).card ≤
          ({u (idx x), v (idx x)} : Finset ℕ).card + 1 := by
        simpa [f] using
          Finset.card_insert_le (e (idx x))
            ({u (idx x), v (idx x)} : Finset ℕ)
      _ ≤ ({v (idx x)} : Finset ℕ).card + 1 + 1 := by
        exact Nat.add_le_add_right
          (Finset.card_insert_le (u (idx x)) {v (idx x)}) 1
      _ ≤ 3 := by simp
  have hfavoid : ∀ x ∈ K, x ∉ f x := by
    intro x hx
    have hav :=
      havoid (idx x) (d (idx x)) (hdH (idx x)) (hde (idx x))
    simp only [f, Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_⟩
    · intro hxe
      exact hde (idx x) ((hidx x hx).trans hxe)
    · intro hxu
      exact hav.1 ((hidx x hx).trans hxu).symm
    · intro hxv
      exact hav.2 ((hidx x hx).trans hxv).symm
  obtain ⟨D, hDK, hDinf, hfree⟩ :=
    exists_infinite_freeSet_of_bounded_pointMap
      hKinf f 3 hfcard hfavoid
  have hDC : D ⊆ C := by
    intro x hxD
    have hxK := hDK hxD
    have hdFilter :=
      (hcomm (idx x)).2.2.2.2.2 (hdH (idx x))
    have hdC := (Finset.mem_filter.1 hdFilter).2
    rw [hidx x hxK] at hdC
    exact hdC
  let σ' : ℕ → Finset ℕ := fun x => insert (n (idx x)) (σ x)
  have hschedule' : HasSurvivingFiniteCoverageSchedule A D σ' := by
    intro x hxD m hm
    have hxK := hDK hxD
    have hcoordAvoid :
        e (idx x) ∉ D ∧ u (idx x) ∉ D ∧ v (idx x) ∉ D := by
      have hdis := Set.disjoint_left.mp (hfree x hxD)
      refine ⟨?_, ?_, ?_⟩
      · intro heD
        exact hdis (by simp [f]) heD
      · intro huD
        exact hdis (by simp [f]) huD
      · intro hvD
        exact hdis (by simp [f]) hvD
    simp only [σ', Finset.mem_insert] at hm
    rcases hm with hnew | hold
    · subst m
      have heFilter :=
        (hcomm (idx x)).2.2.2.2.2 (heH (idx x))
      exact ⟨e (idx x), hCA (Finset.mem_filter.1 heFilter).2,
        u (idx x), huA (idx x), v (idx x), hvA (idx x),
        hcoordAvoid.1, hcoordAvoid.2.1, hcoordAvoid.2.2,
        huv (idx x)⟩
    · obtain ⟨p, hpA, q, hqA, r, hrA, hpC, hqC, hrC, hpqr⟩ :=
        hschedule x (hDC hxD) m hold
      exact ⟨p, hpA, q, hqA, r, hrA,
        fun hpD => hpC (hDC hpD),
        fun hqD => hqC (hDC hqD),
        fun hrD => hrC (hDC hrD), hpqr⟩
  have hcard' : ∀ x ∈ D, (σ' x).card = k + 1 := by
    intro x hxD
    have hnew :
        n (idx x) ∉ σ x :=
      (hcomm (idx x)).2.1 x (hDC hxD)
    simp [σ', hnew, hcard x (hDC hxD)]
  exact ⟨D, hDC, hDinf, σ', hschedule', hcard'⟩

open Classical in

theorem infiniteCoRequiredElementFixedTransversals_scheduleIncrement
    {A C U : Set ℕ} {N₀ k h : ℕ} {σ : ℕ → Finset ℕ}
    (hCA : C ⊆ A)
    (hhC : h ∈ C)
    (hUC : U ⊆ C)
    (hUinf : U.Infinite)
    (hschedule : HasSurvivingFiniteCoverageSchedule A C σ)
    (hcard : ∀ b ∈ C, (σ b).card = k)
    (hdoors : ∀ d ∈ U, d ≠ h ∧
      ∃ n, ∃ H : Finset ℕ,
        IsOffScheduleMinimalDeletionTransversal A C N₀ σ n H ∧
        h ∈ H ∧ d ∈ H) :
    ∃ D ⊆ C, D.Infinite ∧
      HasUniformSurvivingCoverageSchedule A D (k + 1) := by
  have hpick : ∀ d, ∃ n, ∃ H : Finset ℕ, d ∈ U →
      IsOffScheduleMinimalDeletionTransversal A C N₀ σ n H ∧
      h ∈ H ∧ d ∈ H := by
    intro d
    by_cases hdU : d ∈ U
    · obtain ⟨hdh, n, H, hcomm, hhH, hdH⟩ := hdoors d hdU
      exact ⟨n, H, fun _ => ⟨hcomm, hhH, hdH⟩⟩
    · exact ⟨0, ∅, fun h => absurd h hdU⟩
  choose n H hdata using hpick
  have hcowitness : ∀ d, ∃ u, ∃ v, d ∈ U →
      u ∈ A ∧ v ∈ A ∧ h + u + v = n d ∧
      u ≠ d ∧ v ≠ d := by
    intro d
    by_cases hdU : d ∈ U
    · have hd := hdata d hdU
      obtain ⟨u, huA, v, hvA, huv, havoid⟩ :=
        minimalRepSupportTransversal_member_has_pairCowitness
          hd.1.2.2.2.1 hd.1.2.2.2.2.1 hd.2.1
      have havd := havoid d hd.2.2 (hdoors d hdU).1
      exact ⟨u, v, fun _ =>
        ⟨huA, hvA, huv, havd.1, havd.2⟩⟩
    · exact ⟨0, 0, fun h => absurd h hdU⟩
  choose u v hcow using hcowitness
  let f : ℕ → Finset ℕ := fun d => {h, u d, v d}
  have hfcard : ∀ d ∈ U, (f d).card ≤ 3 := by
    intro d hdU
    calc
      (f d).card ≤ ({u d, v d} : Finset ℕ).card + 1 := by
        simpa [f] using
          Finset.card_insert_le h ({u d, v d} : Finset ℕ)
      _ ≤ ({v d} : Finset ℕ).card + 1 + 1 := by
        exact Nat.add_le_add_right
          (Finset.card_insert_le (u d) {v d}) 1
      _ ≤ 3 := by simp
  have hfavoid : ∀ d ∈ U, d ∉ f d := by
    intro d hdU
    have hdne := (hdoors d hdU).1
    have hco := hcow d hdU
    simp only [f, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hdne, hco.2.2.2.1.symm, hco.2.2.2.2.symm⟩
  obtain ⟨D, hDU, hDinf, hfree⟩ :=
    exists_infinite_freeSet_of_bounded_pointMap
      hUinf f 3 hfcard hfavoid
  have hDC : D ⊆ C := hDU.trans hUC
  let σ' : ℕ → Finset ℕ := fun d => insert (n d) (σ d)
  have hschedule' : HasSurvivingFiniteCoverageSchedule A D σ' := by
    intro d hdD m hm
    have hdU := hDU hdD
    have hco := hcow d hdU
    have hcoordAvoid :
        h ∉ D ∧ u d ∉ D ∧ v d ∉ D := by
      have hdis := Set.disjoint_left.mp (hfree d hdD)
      refine ⟨?_, ?_, ?_⟩
      · intro hhD
        exact hdis (by simp [f]) hhD
      · intro huD
        exact hdis (by simp [f]) huD
      · intro hvD
        exact hdis (by simp [f]) hvD
    simp only [σ', Finset.mem_insert] at hm
    rcases hm with hnew | hold
    · subst m
      exact ⟨h, hCA hhC, u d, hco.1, v d, hco.2.1,
        hcoordAvoid.1, hcoordAvoid.2.1, hcoordAvoid.2.2,
        hco.2.2.1⟩
    · obtain ⟨p, hpA, q, hqA, r, hrA, hpC, hqC, hrC, hpqr⟩ :=
        hschedule d (hDC hdD) m hold
      exact ⟨p, hpA, q, hqA, r, hrA,
        fun hpD => hpC (hDC hpD),
        fun hqD => hqC (hDC hqD),
        fun hrD => hrC (hDC hrD), hpqr⟩
  have hcard' : ∀ d ∈ D, (σ' d).card = k + 1 := by
    intro d hdD
    have hdU := hDU hdD
    have hnew : n d ∉ σ d :=
      (hdata d hdU).1.2.1 d (hDC hdD)
    simp [σ', hnew, hcard d (hDC hdD)]
  exact ⟨D, hDC, hDinf, σ', hschedule', hcard'⟩

open Classical in

theorem recurrentOffScheduleRequiredElement_fixedDeletionTransversal_or_increment
    {A C : Set ℕ} {N₀ k : ℕ} {σ : ℕ → Finset ℕ}
    (hCA : C ⊆ A)
    (hschedule : HasSurvivingFiniteCoverageSchedule A C σ)
    (hcard : ∀ b ∈ C, (σ b).card = k)
    (hrec : ∃ h ∈ C, ∀ T, ∃ n, T ≤ n ∧
      ∃ H : Finset ℕ,
        IsOffScheduleMinimalDeletionTransversal A C N₀ σ n H ∧ h ∈ H) :
    (∃ h ∈ C, ∃ R : Finset ℕ, h ∈ R ∧
      ∀ T, ∃ n, T ≤ n ∧
        IsOffScheduleMinimalDeletionTransversal A C N₀ σ n R) ∨
    (∃ D ⊆ C, D.Infinite ∧
      HasUniformSurvivingCoverageSchedule A D (k + 1)) := by
  obtain ⟨h, hhC, hcofinal⟩ := hrec
  let U : Set ℕ := {d | d ≠ h ∧
    ∃ n, ∃ H : Finset ℕ,
      IsOffScheduleMinimalDeletionTransversal A C N₀ σ n H ∧
      h ∈ H ∧ d ∈ H}
  have hUC : U ⊆ C := by
    intro d hdU
    obtain ⟨hdh, n, H, hcomm, hhH, hdH⟩ := hdU
    have hdFilter := hcomm.2.2.2.2.2 hdH
    exact (Finset.mem_filter.1 hdFilter).2
  by_cases hUinf : U.Infinite
  · right
    apply infiniteCoRequiredElementFixedTransversals_scheduleIncrement
      hCA hhC hUC hUinf hschedule hcard
    intro d hdU
    exact hdU
  · left
    have hUfin : U.Finite := Set.not_infinite.mp hUinf
    let F : Finset ℕ := insert h hUfin.toFinset
    have hQ : ∀ T, ∃ n, T ≤ n ∧ ∃ H : Finset ℕ,
        H ⊆ F ∧
        (IsOffScheduleMinimalDeletionTransversal A C N₀ σ n H ∧ h ∈ H) := by
      intro T
      obtain ⟨n, hnT, H, hcomm, hhH⟩ := hcofinal T
      refine ⟨n, hnT, H, ?_, hcomm, hhH⟩
      intro d hdH
      by_cases hdh : d = h
      · subst d
        exact Finset.mem_insert_self h _
      · apply Finset.mem_insert_of_mem
        apply hUfin.mem_toFinset.mpr
        exact ⟨hdh, n, H, hcomm, hhH, hdH⟩
    obtain ⟨R, hRF, hRcofinal⟩ :=
      cofinal_subset_pigeonhole
        (Q := fun n H =>
          IsOffScheduleMinimalDeletionTransversal A C N₀ σ n H ∧ h ∈ H)
        hQ
    refine ⟨h, hhC, R, ?_, ?_⟩
    · obtain ⟨n, hn, hcomm, hhR⟩ := hRcofinal 0
      exact hhR
    · intro T
      obtain ⟨n, hnT, hcomm, hhR⟩ := hRcofinal T
      exact ⟨n, hnT, hcomm⟩

open Classical in
/-- An escaping singleton-deletion transversal stream outside a finite schedule may
be thinned so that every required element is non-big (`2h ≤ n`). -/
theorem cofinal_offSchedule_singletonPrivate_are_nonbig
    {A C : Set ℕ} {N₀ : ℕ} {σ : ℕ → Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) (hCA : C ⊆ A)
    (hstream : ∀ W T, ∃ n, T ≤ n ∧ ∃ h ∈ C,
      W < h ∧ h ≤ n ∧ N₀ ≤ n ∧
      (∀ b ∈ C, n ∉ σ b) ∧ IsPrivateTriple A h n) :
    ∀ W T, ∃ n, T ≤ n ∧ ∃ h ∈ C,
      W < h ∧ h ≤ n ∧ N₀ ≤ n ∧ 2 * h ≤ n ∧
      (∀ b ∈ C, n ∉ σ b) ∧ IsPrivateTriple A h n := by
  by_contra hnonbig
  push Not at hnonbig
  obtain ⟨W₀, T₀, hbad⟩ := hnonbig
  have hbigCofinal : ∀ X, ∃ h ∈ A, X < h ∧
      ∃ n, IsBigAbsolutePrivateDestruction A N₀ h n := by
    intro X
    obtain ⟨n, hnT₀, h, hhC, hhLarge, hhn, hn₀, hoff, hprivate⟩ :=
      hstream (max X W₀) T₀
    have hnotNonbig : ¬2 * h ≤ n := by
      intro hnonbig
      exact hbad n hnT₀ h hhC (by omega) hhn hn₀
        hnonbig hoff hprivate
    exact ⟨h, hCA hhC, by omega, n,
      hn₀, hhn, Nat.lt_of_not_ge hnotNonbig, hprivate⟩
  exact no_cofinal_big_absolute_private_required_elements h0 hcov hbigCofinal

open Classical in

theorem finiteCoverageSchedule_recurrent_or_nonbigPrivate_or_increment
    {A C : Set ℕ} {N₀ k : ℕ} {σ : ℕ → Finset ℕ}
    (h0 : 0 ∈ A) (h0C : 0 ∉ C) (hcov : PairCovers A N₀)
    (hCA : C ⊆ A)
    (hschedule : HasSurvivingFiniteCoverageSchedule A C σ)
    (hcard : ∀ b ∈ C, (σ b).card = k)
    (hfail : ¬IsExactTupleAsymptoticBasis (A \ C) 3) :
    (∃ h ∈ C, ∀ T, ∃ n, T ≤ n ∧
      ∃ H : Finset ℕ,
        IsOffScheduleMinimalDeletionTransversal A C N₀ σ n H ∧ h ∈ H) ∨
    (∀ W T, ∃ n, T ≤ n ∧ ∃ h ∈ C,
      W < h ∧ h ≤ n ∧ N₀ ≤ n ∧ 2 * h ≤ n ∧
      (∀ b ∈ C, n ∉ σ b) ∧ IsPrivateTriple A h n) ∨
    (∃ D ⊆ C, D.Infinite ∧
      HasUniformSurvivingCoverageSchedule A D (k + 1)) := by
  rcases finiteCoverageSchedule_recurrentRequiredElement_or_escapingDeletionTransversals
      σ h0 h0C hcov hschedule hfail with hrec | hesc
  · exact Or.inl hrec
  rcases escapingOffScheduleDeletionTransversals_singletonPrivate_or_multiple
      h0 hcov hesc with hsingle | hmulti
  · exact Or.inr (Or.inl
      (cofinal_offSchedule_singletonPrivate_are_nonbig
        h0 hcov hCA hsingle))
  · exact Or.inr (Or.inr
      (blockSeparatedMultipleOffScheduleDeletionTransversals_scheduleIncrement
        hCA hschedule hcard
        (escapingMultipleOffScheduleDeletionTransversals_has_blockSequence hmulti)))

open Classical in

theorem finiteCoverageSchedule_fixedDeletionTransversal_or_nonbigPrivate_or_increment
    {A C : Set ℕ} {N₀ k : ℕ} {σ : ℕ → Finset ℕ}
    (h0 : 0 ∈ A) (h0C : 0 ∉ C) (hcov : PairCovers A N₀)
    (hCA : C ⊆ A)
    (hschedule : HasSurvivingFiniteCoverageSchedule A C σ)
    (hcard : ∀ b ∈ C, (σ b).card = k)
    (hfail : ¬IsExactTupleAsymptoticBasis (A \ C) 3) :
    (∃ h ∈ C, ∃ R : Finset ℕ, h ∈ R ∧
      ∀ T, ∃ n, T ≤ n ∧
        IsOffScheduleMinimalDeletionTransversal A C N₀ σ n R) ∨
    (∀ W T, ∃ n, T ≤ n ∧ ∃ h ∈ C,
      W < h ∧ h ≤ n ∧ N₀ ≤ n ∧ 2 * h ≤ n ∧
      (∀ b ∈ C, n ∉ σ b) ∧ IsPrivateTriple A h n) ∨
    (∃ D ⊆ C, D.Infinite ∧
      HasUniformSurvivingCoverageSchedule A D (k + 1)) := by
  rcases finiteCoverageSchedule_recurrent_or_nonbigPrivate_or_increment
      h0 h0C hcov hCA hschedule hcard hfail with
    hrec | hprivate | hincrement
  · rcases recurrentOffScheduleRequiredElement_fixedDeletionTransversal_or_increment
      hCA hschedule hcard hrec with hfixed | hincrement
    · exact Or.inl hfixed
    · exact Or.inr (Or.inr hincrement)
  · exact Or.inr (Or.inl hprivate)
  · exact Or.inr (Or.inr hincrement)

open Classical in

theorem failed_uniformFiniteCoverageSchedule_has_increment
    {A C : Set ℕ} {N₀ k : ℕ} {σ : ℕ → Finset ℕ}
    (h0 : 0 ∈ A) (h0C : 0 ∉ C) (hcov : PairCovers A N₀)
    (hCinf : C.Infinite)
    (hschedule : HasSurvivingFiniteCoverageSchedule A C σ)
    (hcard : ∀ b ∈ C, (σ b).card = k)
    (hfail : ¬IsExactTupleAsymptoticBasis (A \ C) 3) :
    ∃ D ⊆ C, D.Infinite ∧
      HasUniformSurvivingCoverageSchedule A D (k + 1) := by
  have hstalls :=
    failure_with_finiteCoverageSchedule_forces_cofinal_offScheduleStalls
      σ h0 h0C hcov hschedule hfail
  have hpick : ∀ W, ∃ p : ℕ × ℕ,
      W < p.1 ∧ p.1 < p.2 ∧ p.2 ∈ C ∧
      N₀ ≤ p.1 ∧ ∀ b ∈ C, p.1 ∉ σ b := by
    intro W
    obtain ⟨m, hmW, hmN, hrisk, hoff, hno⟩ :=
      hstalls (W + 1)
    obtain ⟨d, hdC, hmd⟩ := hCinf.exists_gt m
    exact ⟨(m, d), by omega, hmd, hdC, hmN, hoff⟩
  choose p hp using hpick
  let s : ℕ → ℕ × ℕ :=
    Nat.rec (p 0) (fun _ q => p q.2)
  let m : ℕ → ℕ := fun i => (s i).1
  let d : ℕ → ℕ := fun i => (s i).2
  have hs_zero : s 0 = p 0 := rfl
  have hs_succ : ∀ i, s (i + 1) = p (s i).2 := by
    intro i
    rfl
  have hdata : ∀ i, m i < d i ∧ d i ∈ C ∧
      N₀ ≤ m i ∧ ∀ b ∈ C, m i ∉ σ b := by
    intro i
    cases i with
    | zero =>
        rw [show m 0 = (s 0).1 from rfl,
          show d 0 = (s 0).2 from rfl, hs_zero]
        exact ⟨(hp 0).2.1, (hp 0).2.2.1,
          (hp 0).2.2.2.1, (hp 0).2.2.2.2⟩
    | succ i =>
        rw [show m (i + 1) = (s (i + 1)).1 from rfl,
          show d (i + 1) = (s (i + 1)).2 from rfl, hs_succ]
        exact ⟨(hp (s i).2).2.1, (hp (s i).2).2.2.1,
          (hp (s i).2).2.2.2.1, (hp (s i).2).2.2.2.2⟩
  have hdstep : ∀ i, d i < d (i + 1) := by
    intro i
    have hbetween := (hp (s i).2).1
    have hmnext := (hp (s i).2).2.1
    rw [show d i = (s i).2 from rfl,
      show d (i + 1) = (s (i + 1)).2 from rfl,
      hs_succ]
    omega
  have hdmono : StrictMono d :=
    strictMono_nat_of_lt_succ hdstep
  have hrep : ∀ i, ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
      x + y + z = m i := by
    intro i
    obtain ⟨x, hxA, y, hyA, hxy⟩ :=
      hcov (m i) (hdata i).2.2.1
    exact ⟨x, hxA, y, hyA, 0, h0, by omega⟩
  choose x hxA y hyA z hzA hxyz using hrep
  let K : Set ℕ := Set.range d
  have hKinf : K.Infinite :=
    Set.infinite_range_of_injective hdmono.injective
  let idx : ℕ → ℕ := fun q =>
    if hq : q ∈ K then Classical.choose hq else 0
  have hidx : ∀ q ∈ K, d (idx q) = q := by
    intro q hq
    simpa [idx, hq] using Classical.choose_spec hq
  let f : ℕ → Finset ℕ := fun q =>
    {x (idx q), y (idx q), z (idx q)}
  have hfcard : ∀ q ∈ K, (f q).card ≤ 3 := by
    intro q hq
    calc
      (f q).card ≤
          ({y (idx q), z (idx q)} : Finset ℕ).card + 1 := by
        simpa [f] using
          Finset.card_insert_le (x (idx q))
            ({y (idx q), z (idx q)} : Finset ℕ)
      _ ≤ ({z (idx q)} : Finset ℕ).card + 1 + 1 := by
        exact Nat.add_le_add_right
          (Finset.card_insert_le (y (idx q)) {z (idx q)}) 1
      _ ≤ 3 := by simp
  have hfavoid : ∀ q ∈ K, q ∉ f q := by
    intro q hq
    have hsum := hxyz (idx q)
    have hbelow := (hdata (idx q)).1
    have hdoor := hidx q hq
    have hmQ : m (idx q) < q := by
      calc
        m (idx q) < d (idx q) := hbelow
        _ = q := hdoor
    simp only [f, Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro hqx
      omega
    constructor
    · intro hqy
      omega
    · intro hqz
      omega
  obtain ⟨D, hDK, hDinf, hfree⟩ :=
    exists_infinite_freeSet_of_bounded_pointMap
      hKinf f 3 hfcard hfavoid
  have hDC : D ⊆ C := by
    intro q hqD
    have hqK := hDK hqD
    rw [← hidx q hqK]
    exact (hdata (idx q)).2.1
  let σ' : ℕ → Finset ℕ := fun q =>
    insert (m (idx q)) (σ q)
  have hschedule' : HasSurvivingFiniteCoverageSchedule A D σ' := by
    intro q hqD t ht
    have hqK := hDK hqD
    have hcoordAvoid :
        x (idx q) ∉ D ∧ y (idx q) ∉ D ∧ z (idx q) ∉ D := by
      have hdis := Set.disjoint_left.mp (hfree q hqD)
      refine ⟨?_, ?_, ?_⟩
      · intro hxD
        exact hdis (by simp [f]) hxD
      · intro hyD
        exact hdis (by simp [f]) hyD
      · intro hzD
        exact hdis (by simp [f]) hzD
    simp only [σ', Finset.mem_insert] at ht
    rcases ht with hnew | hold
    · subst t
      exact ⟨x (idx q), hxA (idx q),
        y (idx q), hyA (idx q), z (idx q), hzA (idx q),
        hcoordAvoid.1, hcoordAvoid.2.1, hcoordAvoid.2.2,
        hxyz (idx q)⟩
    · obtain ⟨a, haA, b, hbA, c, hcA, haC, hbC, hcC, habc⟩ :=
        hschedule q (hDC hqD) t hold
      exact ⟨a, haA, b, hbA, c, hcA,
        fun haD => haC (hDC haD),
        fun hbD => hbC (hDC hbD),
        fun hcD => hcC (hDC hcD), habc⟩
  have hcard' : ∀ q ∈ D, (σ' q).card = k + 1 := by
    intro q hqD
    have hnew : m (idx q) ∉ σ q :=
      (hdata (idx q)).2.2.2 q (hDC hqD)
    simp [σ', hnew, hcard q (hDC hqD)]
  exact ⟨D, hDC, hDinf, σ', hschedule', hcard'⟩

open Classical in

theorem counterexample_has_uniformCoverageSchedules_of_every_finite_size
    {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ C ⊆ A, C.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ C) 3) :
    ∀ k, ∃ C : Set ℕ,
      C ⊆ A ∧ C.Infinite ∧ 0 ∉ C ∧
      HasUniformSurvivingCoverageSchedule A C k := by
  intro k
  induction k with
  | zero =>
      let C : Set ℕ := {a | a ∈ A ∧ 0 < a}
      have hCA : C ⊆ A := by
        intro a ha
        exact ha.1
      have hCinf : C.Infinite := by
        apply Set.infinite_of_forall_exists_gt
        intro X
        obtain ⟨a, haA, hXa⟩ :=
          pairCovers_unbounded hcov (X + 1)
        exact ⟨a, ⟨haA, by omega⟩, by omega⟩
      have h0C : 0 ∉ C := by
        intro hz
        exact (Nat.lt_irrefl 0) hz.2
      let σ : ℕ → Finset ℕ := fun _ => ∅
      have hschedule :
          HasSurvivingFiniteCoverageSchedule A C σ := by
        intro b hbC m hm
        simp [σ] at hm
      have hcard : ∀ b ∈ C, (σ b).card = 0 := by
        intro b hbC
        simp [σ]
      exact ⟨C, hCA, hCinf, h0C, σ, hschedule, hcard⟩
  | succ k ih =>
      obtain ⟨C, hCA, hCinf, h0C, σ, hschedule, hcard⟩ := ih
      obtain ⟨D, hDC, hDinf, hDuniform⟩ :=
        failed_uniformFiniteCoverageSchedule_has_increment
          h0 h0C hcov hCinf hschedule hcard
            (hfail C hCA hCinf)
      exact ⟨D, hDC.trans hCA, hDinf,
        fun h0D => h0C (hDC h0D), hDuniform⟩

open Classical in

theorem uniformFiniteCoverageSchedules_all_sizes_not_force_basis :
    let A : Set ℕ := Set.univ
    let C : Set ℕ := {n | n % 2 = 1}
    (∀ k, HasUniformSurvivingCoverageSchedule A C k) ∧
      ¬IsExactTupleAsymptoticBasis (A \ C) 3 := by
  dsimp
  constructor
  · intro k
    let σ : ℕ → Finset ℕ := fun _ =>
      (Finset.range k).image (fun i => 2 * i)
    have hschedule :
        HasSurvivingFiniteCoverageSchedule Set.univ
          {n | n % 2 = 1} σ := by
      intro b hbC m hm
      simp only [σ, Finset.mem_image] at hm
      obtain ⟨i, hi, rfl⟩ := hm
      exact ⟨0, Set.mem_univ 0, 0, Set.mem_univ 0,
        2 * i, Set.mem_univ (2 * i),
        by simp, by simp, by simp, by omega⟩
    have hcard : ∀ b ∈ ({n | n % 2 = 1} : Set ℕ),
        (σ b).card = k := by
      intro b hbC
      change ((Finset.range k).image (fun i => 2 * i)).card = k
      rw [Finset.card_image_of_injective _
        (fun i j hij => by omega), Finset.card_range]
    exact ⟨σ, hschedule, hcard⟩
  · rintro ⟨M, hbasis⟩
    obtain ⟨v, hv, hvsum⟩ := hbasis (2 * M + 1) (by omega)
    have hmod : ∀ i, v i % 2 = 0 := by
      intro i
      have hnot : v i % 2 ≠ 1 := by
        simpa using (hv i).2
      have hlt := Nat.mod_lt (v i) (by omega : 0 < 2)
      omega
    have hd0 : 2 ∣ v 0 := Nat.dvd_of_mod_eq_zero (hmod 0)
    have hd1 : 2 ∣ v 1 := Nat.dvd_of_mod_eq_zero (hmod 1)
    have hd2 : 2 ∣ v 2 := Nat.dvd_of_mod_eq_zero (hmod 2)
    obtain ⟨q0, hq0⟩ := hd0
    obtain ⟨q1, hq1⟩ := hd1
    obtain ⟨q2, hq2⟩ := hd2
    have hsum : v 0 + v 1 + v 2 = 2 * M + 1 := by
      simpa [Fin.sum_univ_three] using hvsum
    omega

open Classical in

theorem fair_finiteCoverageSchedule_fusion
    {A C : Set ℕ} {N₀ : ℕ} (sched : ℕ → ℕ → Finset ℕ)
    (h0 : 0 ∈ A) (h0C : 0 ∉ C) (hcov : PairCovers A N₀)
    (hschedule : ∀ k,
      HasSurvivingFiniteCoverageSchedule A C (sched k))
    (hfair : ∃ M, ∀ n, M ≤ n →
      (∃ b ∈ C, ∃ a ∈ A, b + a = n) →
      ∃ k, ∃ b ∈ C, n ∈ sched k b) :
    IsExactTupleAsymptoticBasis (A \ C) 3 := by
  obtain ⟨M, hfair⟩ := hfair
  have hcov' : PairCovers A (max N₀ M) := by
    intro n hn
    exact hcov n ((le_max_left N₀ M).trans hn)
  apply deletion_criterion_local h0 h0C hcov'
  intro n hn hrisk
  obtain ⟨k, b, hbC, hnSched⟩ :=
    hfair n ((le_max_right N₀ M).trans hn) hrisk
  exact hschedule k b hbC n hnSched

open Classical in

theorem infiniteAlternativeRiskSources_scheduleIncrement
    {A C K : Set ℕ} {k : ℕ} {σ : ℕ → Finset ℕ}
    (hKC : K ⊆ C) (hKinf : K.Infinite)
    (hschedule : HasSurvivingFiniteRiskSchedule A C σ)
    (hcard : ∀ b ∈ C, (σ b).card = k)
    (hdata : ∀ b ∈ K, ∃ n,
      n ∉ σ b ∧
      (∃ a ∈ A, b + a = n) ∧
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x + y + z = n ∧ x ≠ b ∧ y ≠ b ∧ z ≠ b) :
    ∃ D ⊆ C, D.Infinite ∧
      ∃ σ' : ℕ → Finset ℕ,
        HasSurvivingFiniteRiskSchedule A D σ' ∧
        ∀ b ∈ D, (σ' b).card = k + 1 := by
  have hnchoice : ∀ b, ∃ n, b ∈ K →
      n ∉ σ b ∧
      (∃ a ∈ A, b + a = n) ∧
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x + y + z = n ∧ x ≠ b ∧ y ≠ b ∧ z ≠ b := by
    intro b
    by_cases hbK : b ∈ K
    · obtain ⟨n, hn⟩ := hdata b hbK
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h => absurd h hbK⟩
  choose n hn using hnchoice
  have hrepchoice : ∀ b, ∃ x, ∃ y, ∃ z, b ∈ K →
      x ∈ A ∧ y ∈ A ∧ z ∈ A ∧
      x + y + z = n b ∧ x ≠ b ∧ y ≠ b ∧ z ≠ b := by
    intro b
    by_cases hbK : b ∈ K
    · obtain ⟨x, hxA, y, hyA, z, hzA, hxyz, hxb, hyb, hzb⟩ :=
        (hn b hbK).2.2
      exact ⟨x, y, z, fun _ =>
        ⟨hxA, hyA, hzA, hxyz, hxb, hyb, hzb⟩⟩
    · exact ⟨0, 0, 0, fun h => absurd h hbK⟩
  choose x y z hrep using hrepchoice
  let f : ℕ → Finset ℕ := fun b => {x b, y b, z b}
  have hfcard : ∀ b ∈ K, (f b).card ≤ 3 := by
    intro b hbK
    calc
      (f b).card ≤ ({y b, z b} : Finset ℕ).card + 1 := by
        simpa [f] using
          Finset.card_insert_le (x b) ({y b, z b} : Finset ℕ)
      _ ≤ ({z b} : Finset ℕ).card + 1 + 1 := by
        exact Nat.add_le_add_right
          (Finset.card_insert_le (y b) {z b}) 1
      _ ≤ 3 := by simp
  have hfavoid : ∀ b ∈ K, b ∉ f b := by
    intro b hbK
    have hr := hrep b hbK
    simp only [f, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hr.2.2.2.2.1.symm, hr.2.2.2.2.2.1.symm,
      hr.2.2.2.2.2.2.symm⟩
  obtain ⟨D, hDK, hDinf, hfree⟩ :=
    exists_infinite_freeSet_of_bounded_pointMap
      hKinf f 3 hfcard hfavoid
  have hDC : D ⊆ C := hDK.trans hKC
  let σ' : ℕ → Finset ℕ := fun b => insert (n b) (σ b)
  have hschedule' : HasSurvivingFiniteRiskSchedule A D σ' := by
    intro b hbD m hm
    have hbK := hDK hbD
    simp only [σ', Finset.mem_insert] at hm
    rcases hm with hnew | hold
    · subst m
      have hr := hrep b hbK
      have hdis := Set.disjoint_left.mp (hfree b hbD)
      refine ⟨(hn b hbK).2.1,
        x b, hr.1, y b, hr.2.1, z b, hr.2.2.1,
        ?_, ?_, ?_, hr.2.2.2.1⟩
      · intro hxD
        exact hdis (by simp [f]) hxD
      · intro hyD
        exact hdis (by simp [f]) hyD
      · intro hzD
        exact hdis (by simp [f]) hzD
    · obtain ⟨hrisk, p, hpA, q, hqA, r, hrA,
        hpC, hqC, hrC, hpqr⟩ :=
        hschedule b (hDC hbD) m hold
      exact ⟨hrisk, p, hpA, q, hqA, r, hrA,
        fun hpD => hpC (hDC hpD),
        fun hqD => hqC (hDC hqD),
        fun hrD => hrC (hDC hrD), hpqr⟩
  have hcard' : ∀ b ∈ D, (σ' b).card = k + 1 := by
    intro b hbD
    have hbK := hDK hbD
    have hnew : n b ∉ σ b :=
      (hn b hbK).1
    simp [σ', hnew, hcard b (hDC hbD)]
  exact ⟨D, hDC, hDinf, σ', hschedule', hcard'⟩

open Classical in
/-- A target has a three-term representation avoiding one specified
source point. -/
def HasAlternativeTriple (A : Set ℕ) (b n : ℕ) : Prop :=
  ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
    x + y + z = n ∧ x ≠ b ∧ y ≠ b ∧ z ≠ b

open Classical in
/-- A failed target outside a finite schedule, together with one genuine
deleted source `b` which threatens it. -/
def IsOffScheduleFailedRiskSource
    (A C : Set ℕ) (N₀ : ℕ) (σ : ℕ → Finset ℕ)
    (b n : ℕ) : Prop :=
  b ∈ C ∧ N₀ ≤ n ∧
  (∃ a ∈ A, b + a = n) ∧
  (∀ c ∈ C, n ∉ σ c) ∧
  ¬∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
    x ∉ C ∧ y ∉ C ∧ z ∉ C ∧ x + y + z = n

open Classical in
/-- Above the pair-cover threshold, failure of an alternative triple
means exactly that `b` is an absolute private required element. -/
theorem alternativeTriple_or_private
    {A : Set ℕ} {N₀ b n : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) (hn : N₀ ≤ n) :
    HasAlternativeTriple A b n ∨ IsPrivateTriple A b n := by
  by_cases halt : HasAlternativeTriple A b n
  · exact Or.inl halt
  · right
    obtain ⟨x, hxA, y, hyA, hxy⟩ := hcov n hn
    constructor
    · exact ⟨x, hxA, y, hyA, 0, h0, by omega⟩
    · intro p hpA q hqA r hrA hpqr
      by_contra hnone
      push Not at hnone
      exact halt ⟨p, hpA, q, hqA, r, hrA, hpqr,
        hnone.1, hnone.2.1, hnone.2.2⟩

open Classical in

theorem failed_riskSchedule_source_boundary
    {A C : Set ℕ} {N₀ k : ℕ} {σ : ℕ → Finset ℕ}
    (h0 : 0 ∈ A) (h0C : 0 ∉ C) (hcov : PairCovers A N₀)
    (hschedule : HasSurvivingFiniteRiskSchedule A C σ)
    (hcard : ∀ b ∈ C, (σ b).card = k)
    (hfail : ¬IsExactTupleAsymptoticBasis (A \ C) 3) :
    (∃ D ⊆ C, D.Infinite ∧
      ∃ σ' : ℕ → Finset ℕ,
        HasSurvivingFiniteRiskSchedule A D σ' ∧
        ∀ b ∈ D, (σ' b).card = k + 1) ∨
    (∀ W, ∃ b ∈ C, W < b ∧ ∃ n,
      IsOffScheduleFailedRiskSource A C N₀ σ b n ∧
      IsPrivateTriple A b n) ∨
    (∃ b ∈ C,
      (∀ T, ∃ n, T < n ∧
        IsOffScheduleFailedRiskSource A C N₀ σ b n ∧
        HasAlternativeTriple A b n) ∨
      (∀ T, ∃ n, T < n ∧
        IsOffScheduleFailedRiskSource A C N₀ σ b n ∧
        IsPrivateTriple A b n)) := by
  have hstalls :=
    failure_with_finiteCoverageSchedule_forces_cofinal_offScheduleStalls
      σ h0 h0C hcov hschedule.toCoverage hfail
  have hQ : ∀ T, ∃ n, T < n ∧ ∃ b,
      IsOffScheduleFailedRiskSource A C N₀ σ b n := by
    intro T
    obtain ⟨n, hnT, hnN, hrisk, hoff, hno⟩ :=
      hstalls (T + 1)
    obtain ⟨b, hbC, a, haA, hba⟩ := hrisk
    exact ⟨n, by omega, b, hbC, hnN, ⟨a, haA, hba⟩,
      hoff, hno⟩
  let Kalt : Set ℕ := {b | ∃ n,
    IsOffScheduleFailedRiskSource A C N₀ σ b n ∧
    HasAlternativeTriple A b n}
  let Kprivate : Set ℕ := {b | ∃ n,
    IsOffScheduleFailedRiskSource A C N₀ σ b n ∧
    IsPrivateTriple A b n}
  have hKaltC : Kalt ⊆ C := by
    intro b hb
    obtain ⟨n, hq, halt⟩ := hb
    exact hq.1
  have hKprivateC : Kprivate ⊆ C := by
    intro b hb
    obtain ⟨n, hq, hprivate⟩ := hb
    exact hq.1
  have hclass : ∀ b n,
      IsOffScheduleFailedRiskSource A C N₀ σ b n →
      b ∈ Kalt ∨ b ∈ Kprivate := by
    intro b n hq
    rcases alternativeTriple_or_private h0 hcov hq.2.1 with
      halt | hprivate
    · exact Or.inl ⟨n, hq, halt⟩
    · exact Or.inr ⟨n, hq, hprivate⟩
  by_cases hKaltInf : Kalt.Infinite
  · left
    apply infiniteAlternativeRiskSources_scheduleIncrement
      hKaltC hKaltInf hschedule hcard
    intro b hbK
    obtain ⟨n, hq, halt⟩ := hbK
    exact ⟨n, hq.2.2.2.1 b hq.1, hq.2.2.1, halt⟩
  have hKaltFin : Kalt.Finite := Set.not_infinite.mp hKaltInf
  by_cases hKprivateInf : Kprivate.Infinite
  · right
    left
    intro W
    obtain ⟨b, hbK, hbW⟩ := hKprivateInf.exists_gt W
    have hbC := hKprivateC hbK
    obtain ⟨n, hq, hprivate⟩ := hbK
    exact ⟨b, hbC, hbW, n, hq, hprivate⟩
  have hKprivateFin : Kprivate.Finite :=
    Set.not_infinite.mp hKprivateInf
  right
  right
  have hUnionFin : (Kalt ∪ Kprivate).Finite :=
    hKaltFin.union hKprivateFin
  let F : Finset ℕ := hUnionFin.toFinset
  have hlabels : ∀ T, ∃ n, T < n ∧ ∃ b ∈ F,
      IsOffScheduleFailedRiskSource A C N₀ σ b n := by
    intro T
    obtain ⟨n, hnT, b, hq⟩ := hQ T
    have hbUnion : b ∈ Kalt ∪ Kprivate := hclass b n hq
    exact ⟨n, hnT, b, hUnionFin.mem_toFinset.mpr hbUnion, hq⟩
  obtain ⟨b, hbF, hbcofinal⟩ :=
    finite_cofinal_pigeonhole
      (B := F)
      (P := fun b n =>
        IsOffScheduleFailedRiskSource A C N₀ σ b n)
      hlabels
  obtain ⟨n₀, hn₀, hq₀⟩ := hbcofinal 0
  refine ⟨b, hq₀.1, ?_⟩
  by_cases haltCofinal : ∀ T, ∃ n, T < n ∧
      IsOffScheduleFailedRiskSource A C N₀ σ b n ∧
      HasAlternativeTriple A b n
  · exact Or.inl haltCofinal
  · right
    push Not at haltCofinal
    obtain ⟨T₀, hT₀⟩ := haltCofinal
    intro T
    obtain ⟨n, hnLarge, hq⟩ :=
      hbcofinal (max T T₀)
    have hnotAlt : ¬HasAlternativeTriple A b n := by
      intro halt
      exact hT₀ n (by omega) hq halt
    have hprivate : IsPrivateTriple A b n :=
      (alternativeTriple_or_private h0 hcov hq.2.1).resolve_left
        hnotAlt
    exact ⟨n, by omega, hq, hprivate⟩

open Classical in

theorem anchored_counterexample_riskSchedule_increment_or_fixedCollateral
    {A C : Set ℕ} {N₀ k : ℕ} {σ : ℕ → Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hCA : C ⊆ A) (hCinf : C.Infinite) (h0C : 0 ∉ C)
    (hglobal : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧
      ∃ w ∈ A, ∃ w' ∈ A,
        w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hschedule : HasSurvivingFiniteRiskSchedule A C σ)
    (hcard : ∀ b ∈ C, (σ b).card = k) :
    (∃ D ⊆ C, D.Infinite ∧
      ∃ σ' : ℕ → Finset ℕ,
        HasSurvivingFiniteRiskSchedule A D σ' ∧
        ∀ b ∈ D, (σ' b).card = k + 1) ∨
    (∃ b ∈ C, ∀ T, ∃ n, T < n ∧
      IsOffScheduleFailedRiskSource A C N₀ σ b n ∧
      HasAlternativeTriple A b n) := by
  rcases failed_riskSchedule_source_boundary
      h0 h0C hcov hschedule hcard (hglobal C hCA hCinf) with
    hincrement | hunboundedPrivate |
      ⟨b, hbC, hfixedAlt | hfixedPrivate⟩
  · exact Or.inl hincrement
  · exfalso
    have hstream : ∀ N, ∃ a m, N ≤ m ∧
        0 < a ∧ IsPrivateTriple A a m := by
      intro N
      obtain ⟨b, hbC, hbN, n, hq, hprivate⟩ :=
        hunboundedPrivate N
      obtain ⟨a, haA, hba⟩ := hq.2.2.1
      have hbpos : 0 < b := by
        by_contra hb0
        have : b = 0 := Nat.eq_zero_of_not_pos hb0
        exact h0C (this ▸ hbC)
      exact ⟨b, n, by omega, hbpos, hprivate⟩
    obtain ⟨B, hBA, hBinf, hsurvive⟩ :=
      surviving_deletion_of_cofinal_privateStream
        h0 hcov hstream hanchor
    exact hglobal B hBA hBinf
      (exactTupleBasis_diff_of_survival hsurvive)
  · exact Or.inr ⟨b, hbC, hfixedAlt⟩
  · exfalso
    have hbpos : 0 < b := by
      by_contra hb0
      have : b = 0 := Nat.eq_zero_of_not_pos hb0
      exact h0C (this ▸ hbC)
    have hstream : ∀ N, ∃ a m, N ≤ m ∧
        0 < a ∧ IsPrivateTriple A a m := by
      intro N
      obtain ⟨n, hnN, hq, hprivate⟩ := hfixedPrivate N
      exact ⟨b, n, by omega, hbpos, hprivate⟩
    obtain ⟨B, hBA, hBinf, hsurvive⟩ :=
      surviving_deletion_of_cofinal_privateStream
        h0 hcov hstream hanchor
    exact hglobal B hBA hBinf
      (exactTupleBasis_diff_of_survival hsurvive)

open Classical in

theorem fixedAlternativeRiskSource_has_collateralSunflower
    {A C : Set ℕ} {N₀ : ℕ} {σ : ℕ → Finset ℕ}
    (hfixed : ∃ b ∈ C, ∀ T, ∃ n, T < n ∧
      IsOffScheduleFailedRiskSource A C N₀ σ b n ∧
      HasAlternativeTriple A b n) :
    ∃ b ∈ C, ∃ n : ℕ → ℕ, ∃ P : ℕ → Finset ℕ,
      ∃ L : Set ℕ,
      StrictMono n ∧ L.Infinite ∧
      (∀ i ∈ L,
        IsOffScheduleFailedRiskSource A C N₀ σ b (n i) ∧
        (P i).card ≤ 3 ∧ b ∉ P i ∧
        ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
          P i = {x, y, z} ∧ x + y + z = n i) ∧
      ((∃ c ∈ C, c ≠ b ∧ ∀ i ∈ L, c ∈ P i) ∨
       ∃ d : ℕ → ℕ, Set.InjOn d L ∧
         ∀ i ∈ L, d i ∈ C ∧ d i ∈ P i) := by
  obtain ⟨b, hbC, hcofinal⟩ := hfixed
  have hpick : ∀ T, ∃ m, T < m ∧
      IsOffScheduleFailedRiskSource A C N₀ σ b m ∧
      HasAlternativeTriple A b m := hcofinal
  choose nxt hnxt hQnext hAltnext using hpick
  let n : ℕ → ℕ :=
    Nat.rec (nxt 0) (fun _ prev => nxt prev)
  have hnzero : n 0 = nxt 0 := rfl
  have hnsucc : ∀ i, n (i + 1) = nxt (n i) := by
    intro i
    rfl
  have hnstep : ∀ i, n i < n (i + 1) := by
    intro i
    rw [hnsucc]
    exact hnxt (n i)
  have hnmono : StrictMono n :=
    strictMono_nat_of_lt_succ hnstep
  have hndata : ∀ i,
      IsOffScheduleFailedRiskSource A C N₀ σ b (n i) ∧
      HasAlternativeTriple A b (n i) := by
    intro i
    cases i with
    | zero =>
        rw [hnzero]
        exact ⟨hQnext 0, hAltnext 0⟩
    | succ i =>
        rw [hnsucc]
        exact ⟨hQnext (n i), hAltnext (n i)⟩
  have hrepchoice : ∀ i, ∃ x, ∃ y, ∃ z,
      x ∈ A ∧ y ∈ A ∧ z ∈ A ∧
      x + y + z = n i ∧ x ≠ b ∧ y ≠ b ∧ z ≠ b := by
    intro i
    simpa [HasAlternativeTriple] using (hndata i).2
  choose x y z hrep using hrepchoice
  let P : ℕ → Finset ℕ := fun i => {x i, y i, z i}
  have hPcard : ∀ i, (P i).card ≤ 3 := by
    intro i
    calc
      (P i).card ≤ ({y i, z i} : Finset ℕ).card + 1 := by
        simpa [P] using
          Finset.card_insert_le (x i) ({y i, z i} : Finset ℕ)
      _ ≤ ({z i} : Finset ℕ).card + 1 + 1 := by
        exact Nat.add_le_add_right
          (Finset.card_insert_le (y i) {z i}) 1
      _ ≤ 3 := by simp
  obtain ⟨L, hLuniv, hLinf, R, hdelta⟩ :=
    exists_infinite_deltaSystem_of_bounded_pointMap
      (K := Set.univ) Set.infinite_univ P 3
        (fun i hi => hPcard i)
  have hPavoid : ∀ i, b ∉ P i := by
    intro i
    have hr := hrep i
    simp only [P, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hr.2.2.2.2.1.symm, hr.2.2.2.2.2.1.symm,
      hr.2.2.2.2.2.2.symm⟩
  have hPhit : ∀ i, ∃ c, c ∈ C ∧ c ∈ P i := by
    intro i
    have hq := (hndata i).1
    have hr := hrep i
    have hhit : x i ∈ C ∨ y i ∈ C ∨ z i ∈ C := by
      by_contra hnone
      push Not at hnone
      exact hq.2.2.2.2
        ⟨x i, hr.1, y i, hr.2.1, z i, hr.2.2.1,
          hnone.1, hnone.2.1, hnone.2.2, hr.2.2.2.1⟩
    rcases hhit with hxC | hyC | hzC
    · exact ⟨x i, hxC, by simp [P]⟩
    · exact ⟨y i, hyC, by simp [P]⟩
    · exact ⟨z i, hzC, by simp [P]⟩
  refine ⟨b, hbC, n, P, L, hnmono, hLinf, ?_, ?_⟩
  · intro i hiL
    have hr := hrep i
    exact ⟨(hndata i).1, hPcard i, hPavoid i,
      x i, hr.1, y i, hr.2.1, z i, hr.2.2.1,
      rfl, hr.2.2.2.1⟩
  · by_cases hrootHit : ∃ c, c ∈ R ∧ c ∈ C
    · left
      obtain ⟨c, hcR, hcC⟩ := hrootHit
      have hcAll : ∀ i ∈ L, c ∈ P i := by
        intro i hiL
        have hother : (L \ ({i} : Set ℕ)).Infinite :=
          hLinf.diff (Set.finite_singleton i)
        obtain ⟨j, hjL, hji⟩ := hother.nonempty
        have hij : i ≠ j := by
          exact fun hij => hji (by simpa using hij.symm)
        have hd := hdelta i hiL j hjL hij
        rw [← hd] at hcR
        exact (Finset.mem_inter.1 hcR).1
      have hcb : c ≠ b := by
        obtain ⟨i, hiL⟩ := hLinf.nonempty
        intro hcb
        subst c
        exact hPavoid i (hcAll i hiL)
      exact ⟨c, hcC, hcb, hcAll⟩
    · right
      have hchoice : ∀ i, ∃ c, i ∈ L →
          c ∈ C ∧ c ∈ P i := by
        intro i
        by_cases hiL : i ∈ L
        · obtain ⟨c, hcC, hcP⟩ := hPhit i
          exact ⟨c, fun _ => ⟨hcC, hcP⟩⟩
        · exact ⟨0, fun h => absurd h hiL⟩
      choose d hd using hchoice
      have hdInj : Set.InjOn d L := by
        intro i hiL j hjL hij
        by_contra hne
        have hdI := hd i hiL
        have hdJ := hd j hjL
        have hdInter : d i ∈ P i ∩ P j := by
          exact Finset.mem_inter.2
            ⟨hdI.2, hij ▸ hdJ.2⟩
        have hdRoot : d i ∈ R := by
          rw [← hdelta i hiL j hjL hne]
          exact hdInter
        exact hrootHit ⟨d i, hdRoot, hdI.1⟩
      exact ⟨d, hdInj, fun i hiL => hd i hiL⟩

open Classical in
/-- Removing a named member from a three-point support leaves two
`A`-entries and the corresponding additive identity. -/
theorem tripleSupport_member_has_pairDecomposition
    {A : Set ℕ} {P : Finset ℕ} {c n x y z : ℕ}
    (hxA : x ∈ A) (hyA : y ∈ A) (hzA : z ∈ A)
    (hP : P = {x, y, z}) (hcP : c ∈ P)
    (hxyz : x + y + z = n) :
    ∃ u ∈ A, ∃ v ∈ A, c + u + v = n := by
  rw [hP] at hcP
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcP
  rcases hcP with hcx | hcy | hcz
  · subst c
    exact ⟨y, hyA, z, hzA, hxyz⟩
  · subst c
    exact ⟨x, hxA, z, hzA, by omega⟩
  · subst c
    exact ⟨x, hxA, y, hyA, by omega⟩

open Classical in

theorem fixedAlternativeRiskSource_fixed_or_mobileCollateralEquations
    {A C : Set ℕ} {N₀ : ℕ} {σ : ℕ → Finset ℕ}
    (hfixed : ∃ b ∈ C, ∀ T, ∃ n, T < n ∧
      IsOffScheduleFailedRiskSource A C N₀ σ b n ∧
      HasAlternativeTriple A b n) :
    ∃ b ∈ C, ∃ n : ℕ → ℕ, ∃ L : Set ℕ,
      StrictMono n ∧ L.Infinite ∧
      (∀ i ∈ L,
        IsOffScheduleFailedRiskSource A C N₀ σ b (n i)) ∧
      ((∃ c ∈ C, c ≠ b ∧ ∀ i ∈ L,
        ∃ a ∈ A, ∃ u ∈ A, ∃ v ∈ A,
          b + a = n i ∧ c + u + v = n i) ∨
       ∃ d : ℕ → ℕ, Set.InjOn d L ∧
        ∀ i ∈ L, d i ∈ C ∧ d i ≠ b ∧
          ∃ a ∈ A, ∃ u ∈ A, ∃ v ∈ A,
            b + a = n i ∧ d i + u + v = n i) := by
  obtain ⟨b, hbC, n, P, L, hnmono, hLinf, hrows,
      hfixedCollateral | hmobileCollateral⟩ :=
    fixedAlternativeRiskSource_has_collateralSunflower hfixed
  · refine ⟨b, hbC, n, L, hnmono, hLinf,
      fun i hiL => (hrows i hiL).1, Or.inl ?_⟩
    obtain ⟨c, hcC, hcb, hcAll⟩ := hfixedCollateral
    refine ⟨c, hcC, hcb, ?_⟩
    intro i hiL
    have hrow := hrows i hiL
    obtain ⟨a, haA, hba⟩ := hrow.1.2.2.1
    obtain ⟨x, hxA, y, hyA, z, hzA, hP, hxyz⟩ :=
      hrow.2.2.2
    obtain ⟨u, huA, v, hvA, hcuv⟩ :=
      tripleSupport_member_has_pairDecomposition
        hxA hyA hzA hP (hcAll i hiL) hxyz
    exact ⟨a, haA, u, huA, v, hvA, hba, hcuv⟩
  · refine ⟨b, hbC, n, L, hnmono, hLinf,
      fun i hiL => (hrows i hiL).1, Or.inr ?_⟩
    obtain ⟨d, hdInj, hdAll⟩ := hmobileCollateral
    refine ⟨d, hdInj, ?_⟩
    intro i hiL
    have hrow := hrows i hiL
    obtain ⟨a, haA, hba⟩ := hrow.1.2.2.1
    obtain ⟨x, hxA, y, hyA, z, hzA, hP, hxyz⟩ :=
      hrow.2.2.2
    obtain ⟨hdiC, hdiP⟩ := hdAll i hiL
    obtain ⟨u, huA, v, hvA, hduv⟩ :=
      tripleSupport_member_has_pairDecomposition
        hxA hyA hzA hP hdiP hxyz
    exact ⟨hdiC, fun hdib => (hrow.2.2.1) (hdib ▸ hdiP),
      a, haA, u, huA, v, hvA, hba, hduv⟩

open Classical in
/-- A cofinal mobile-collateral stream in which the collateral point is
the original pair partner.  The two equations then cancel to
`b = uᵢ+vᵢ`; thus every row is the same two-required element conflict
`b+dᵢ = dᵢ+uᵢ+vᵢ`, with pairwise distinct `dᵢ`. -/
def HasCofinalSourceConflictRows
    (A C : Set ℕ) (N₀ : ℕ) (σ : ℕ → Finset ℕ) (b : ℕ) : Prop :=
  ∃ n : ℕ → ℕ, ∃ L : Set ℕ,
    ∃ d a u v : ℕ → ℕ,
      StrictMono n ∧ L.Infinite ∧ Set.InjOn d L ∧
      ∀ i ∈ L,
        IsOffScheduleFailedRiskSource A C N₀ σ b (n i) ∧
        d i ∈ C ∧ d i ≠ b ∧
        a i ∈ A ∧ u i ∈ A ∧ v i ∈ A ∧
        d i = a i ∧ b = u i + v i ∧
        b + a i = n i ∧ d i + u i + v i = n i

open Classical in
/-- A cofinal mobile-collateral stream whose collateral co-pair cannot
be normalized to an element of `A`.  This records the exact failure of
the tempting compression
`dᵢ+uᵢ+vᵢ = nᵢ  ↦  dᵢ+(uᵢ+vᵢ) = nᵢ`
as a genuine pair-risk label. -/
def HasCofinalNonNormalizableCollateralRows
    (A C : Set ℕ) (N₀ : ℕ) (σ : ℕ → Finset ℕ) (b : ℕ) : Prop :=
  ∃ n : ℕ → ℕ, ∃ L : Set ℕ,
    ∃ d a u v : ℕ → ℕ,
      StrictMono n ∧ L.Infinite ∧ Set.InjOn d L ∧
      ∀ i ∈ L,
        IsOffScheduleFailedRiskSource A C N₀ σ b (n i) ∧
        d i ∈ C ∧ d i ≠ b ∧
        a i ∈ A ∧ u i ∈ A ∧ v i ∈ A ∧
        u i + v i ∉ A ∧
        b + a i = n i ∧ d i + u i + v i = n i

open Classical in

theorem mobileCollateralEquations_increment_or_conflict_or_nonNormalizable
    {A C : Set ℕ} {N₀ k b : ℕ} {σ : ℕ → Finset ℕ}
    {n d : ℕ → ℕ} {L : Set ℕ}
    (h0 : 0 ∈ A) (h0C : 0 ∉ C) (hCA : C ⊆ A)
    (hbC : b ∈ C)
    (hschedule : HasSurvivingFiniteRiskSchedule A C σ)
    (hcard : ∀ c ∈ C, (σ c).card = k)
    (hnmono : StrictMono n) (hLinf : L.Infinite)
    (hfailed : ∀ i ∈ L,
      IsOffScheduleFailedRiskSource A C N₀ σ b (n i))
    (hdInj : Set.InjOn d L)
    (hmobile : ∀ i ∈ L, d i ∈ C ∧ d i ≠ b ∧
      ∃ a ∈ A, ∃ u ∈ A, ∃ v ∈ A,
        b + a = n i ∧ d i + u + v = n i) :
    (∃ D ⊆ C, D.Infinite ∧
      ∃ σ' : ℕ → Finset ℕ,
        HasSurvivingFiniteRiskSchedule A D σ' ∧
        ∀ c ∈ D, (σ' c).card = k + 1) ∨
    HasCofinalSourceConflictRows A C N₀ σ b ∨
    HasCofinalNonNormalizableCollateralRows A C N₀ σ b := by
  have hpick : ∀ i, ∃ a, ∃ u, ∃ v, i ∈ L →
      a ∈ A ∧ u ∈ A ∧ v ∈ A ∧
      b + a = n i ∧ d i + u + v = n i := by
    intro i
    by_cases hiL : i ∈ L
    · obtain ⟨a, haA, u, huA, v, hvA, hba, hduv⟩ :=
        (hmobile i hiL).2.2
      exact ⟨a, u, v, fun _ =>
        ⟨haA, huA, hvA, hba, hduv⟩⟩
    · exact ⟨0, 0, 0, fun hi => absurd hi hiL⟩
  choose a u v hrow using hpick
  let P : Set ℕ := {i | u i + v i ∈ A}
  have hfirstSplit :
      (L ∩ P).Infinite ∨ (L \ P).Infinite := by
    by_cases hLP : (L ∩ P).Infinite
    · exact Or.inl hLP
    · right
      have hdiff :=
        hLinf.diff (Set.not_infinite.mp hLP)
      simpa [P, Set.ext_iff] using hdiff
  rcases hfirstSplit with hnormal | hnonNormal
  · let Q : Set ℕ := {i | d i ≠ a i}
    have hsecondSplit :
        ((L ∩ P) ∩ Q).Infinite ∨
          ((L ∩ P) \ Q).Infinite := by
      by_cases hLPQ : ((L ∩ P) ∩ Q).Infinite
      · exact Or.inl hLPQ
      · right
        have hdiff :=
          hnormal.diff (Set.not_infinite.mp hLPQ)
        simpa [Q, Set.ext_iff] using hdiff
    rcases hsecondSplit with hcomposable | hcollision
    · left
      let K : Set ℕ := (L ∩ P) ∩ Q
      have hKinf : K.Infinite := hcomposable
      have hKL : K ⊆ L := by
        intro i hi
        exact hi.1.1
      have hdInjK : Set.InjOn d K :=
        hdInj.mono hKL
      have hsourceInf : (d '' K).Infinite :=
        hKinf.image hdInjK
      have hsourceC : d '' K ⊆ C := by
        rintro c ⟨i, hiK, rfl⟩
        exact (hmobile i (hKL hiK)).1
      apply infiniteAlternativeRiskSources_scheduleIncrement
        hsourceC hsourceInf hschedule hcard
      intro c hc
      obtain ⟨i, hiK, rfl⟩ := hc
      have hiL : i ∈ L := hKL hiK
      have hri := hrow i hiL
      have hdi := hmobile i hiL
      have hsumA : u i + v i ∈ A := hiK.1.2
      have hdneA : d i ≠ a i := hiK.2
      have hd0 : d i ≠ 0 := by
        intro hdi0
        exact h0C (hdi0 ▸ hdi.1)
      refine ⟨n i,
        (hfailed i hiL).2.2.2.1 (d i) hdi.1,
        ⟨u i + v i, hsumA, by omega⟩, ?_⟩
      exact ⟨b, hCA hbC, a i, hri.1, 0, h0,
        by omega, hdi.2.1.symm, hdneA.symm, hd0.symm⟩
    · right
      left
      let K : Set ℕ := (L ∩ P) \ Q
      have hKL : K ⊆ L := by
        intro i hi
        exact hi.1.1
      refine ⟨n, K, d, a, u, v, hnmono, hcollision,
        hdInj.mono hKL, ?_⟩
      intro i hiK
      have hiL : i ∈ L := hKL hiK
      have hri := hrow i hiL
      have hdi := hmobile i hiL
      have hdia : d i = a i := by
        simpa [Q] using hiK.2
      have hbuv : b = u i + v i := by
        omega
      exact ⟨hfailed i hiL, hdi.1, hdi.2.1,
        hri.1, hri.2.1, hri.2.2.1, hdia, hbuv,
        hri.2.2.2.1, hri.2.2.2.2⟩
  · right
    right
    let K : Set ℕ := L \ P
    have hKL : K ⊆ L := by
      intro i hi
      exact hi.1
    refine ⟨n, K, d, a, u, v, hnmono, hnonNormal,
      hdInj.mono hKL, ?_⟩
    intro i hiK
    have hiL : i ∈ L := hKL hiK
    have hri := hrow i hiL
    have hdi := hmobile i hiL
    have hsumNot : u i + v i ∉ A := by
      simpa [P] using hiK.2
    exact ⟨hfailed i hiL, hdi.1, hdi.2.1,
      hri.1, hri.2.1, hri.2.2.1, hsumNot,
      hri.2.2.2.1, hri.2.2.2.2⟩

open Classical in
/-- One fixed collateral point occurs in an alternative equation for a
cofinal stream of failed risks of the fixed source `b`. -/
def HasCofinalFixedCollateralRows
    (A C : Set ℕ) (N₀ : ℕ) (σ : ℕ → Finset ℕ) (b : ℕ) : Prop :=
  ∃ c ∈ C, c ≠ b ∧
    ∃ n : ℕ → ℕ, ∃ L : Set ℕ,
      StrictMono n ∧ L.Infinite ∧
      ∀ i ∈ L,
        IsOffScheduleFailedRiskSource A C N₀ σ b (n i) ∧
        ∃ a ∈ A, ∃ u ∈ A, ∃ v ∈ A,
          b + a = n i ∧ c + u + v = n i

open Classical in

theorem anchored_counterexample_riskSchedule_increment_or_terminalRows
    {A C : Set ℕ} {N₀ k : ℕ} {σ : ℕ → Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hCA : C ⊆ A) (hCinf : C.Infinite) (h0C : 0 ∉ C)
    (hglobal : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧
      ∃ w ∈ A, ∃ w' ∈ A,
        w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hschedule : HasSurvivingFiniteRiskSchedule A C σ)
    (hcard : ∀ b ∈ C, (σ b).card = k) :
    (∃ D ⊆ C, D.Infinite ∧
      ∃ σ' : ℕ → Finset ℕ,
        HasSurvivingFiniteRiskSchedule A D σ' ∧
        ∀ b ∈ D, (σ' b).card = k + 1) ∨
    (∃ b ∈ C, HasCofinalFixedCollateralRows A C N₀ σ b) ∨
    (∃ b ∈ C, HasCofinalSourceConflictRows A C N₀ σ b) ∨
    ∃ b ∈ C,
      HasCofinalNonNormalizableCollateralRows A C N₀ σ b := by
  rcases anchored_counterexample_riskSchedule_increment_or_fixedCollateral
      h0 hcov hCA hCinf h0C hglobal hanchor hschedule hcard with
    hincrement | hfixedSource
  · exact Or.inl hincrement
  obtain ⟨b, hbC, n, L, hnmono, hLinf, hfailed,
      hfixed | hmobile⟩ :=
    fixedAlternativeRiskSource_fixed_or_mobileCollateralEquations
      hfixedSource
  · right
    left
    obtain ⟨c, hcC, hcb, hrows⟩ := hfixed
    exact ⟨b, hbC, c, hcC, hcb, n, L, hnmono, hLinf,
      fun i hiL => ⟨hfailed i hiL, hrows i hiL⟩⟩
  · obtain ⟨d, hdInj, hrows⟩ := hmobile
    rcases
        mobileCollateralEquations_increment_or_conflict_or_nonNormalizable
          h0 h0C hCA hbC hschedule hcard hnmono hLinf
            hfailed hdInj hrows with
      hincrement | hcollision | hnonNormal
    · exact Or.inl hincrement
    · exact Or.inr (Or.inr (Or.inl ⟨b, hbC, hcollision⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨b, hbC, hnonNormal⟩))

open Classical in

theorem anchored_sourceConflictRows_force_increment
    {A C : Set ℕ} {N₀ k b : ℕ} {σ : ℕ → Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hCA : C ⊆ A) (h0C : 0 ∉ C) (hbC : b ∈ C)
    (hglobal : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧
      ∃ w ∈ A, ∃ w' ∈ A,
        w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hschedule : HasSurvivingFiniteRiskSchedule A C σ)
    (hcard : ∀ c ∈ C, (σ c).card = k)
    (hcollision :
      HasCofinalSourceConflictRows A C N₀ σ b) :
    ∃ D ⊆ C, D.Infinite ∧
      ∃ σ' : ℕ → Finset ℕ,
        HasSurvivingFiniteRiskSchedule A D σ' ∧
        ∀ c ∈ D, (σ' c).card = k + 1 := by
  obtain ⟨n, L, d, a, u, v, hnmono, hLinf, hdInj, hrows⟩ :=
    hcollision
  let P : Set ℕ := {i | HasAlternativeTriple A (d i) (n i)}
  have hsplit :
      (L ∩ P).Infinite ∨ (L \ P).Infinite := by
    by_cases hLP : (L ∩ P).Infinite
    · exact Or.inl hLP
    · right
      have hdiff :=
        hLinf.diff (Set.not_infinite.mp hLP)
      simpa [P, Set.ext_iff] using hdiff
  rcases hsplit with hAltInf | hPrivateInf
  · let K : Set ℕ := L ∩ P
    have hKL : K ⊆ L := by
      intro i hi
      exact hi.1
    have hsourceInf : (d '' K).Infinite :=
      hAltInf.image (hdInj.mono hKL)
    have hsourceC : d '' K ⊆ C := by
      rintro c ⟨i, hiK, rfl⟩
      exact (hrows i (hKL hiK)).2.1
    apply infiniteAlternativeRiskSources_scheduleIncrement
      hsourceC hsourceInf hschedule hcard
    intro c hc
    obtain ⟨i, hiK, rfl⟩ := hc
    have hiL : i ∈ L := hKL hiK
    obtain ⟨hfailed, hdiC, hdib, haiA, huiA, hviA,
        hdia, hbuv, hba, hduv⟩ :=
      hrows i hiL
    exact ⟨n i, hfailed.2.2.2.1 (d i) hdiC,
      ⟨b, hCA hbC, by omega⟩, hiK.2⟩
  · exfalso
    let K : Set ℕ := L \ P
    have hKL : K ⊆ L := by
      intro i hi
      exact hi.1
    have hsourceInf : (d '' K).Infinite :=
      hPrivateInf.image (hdInj.mono hKL)
    have hstream : ∀ N, ∃ g m, N ≤ m ∧
        0 < g ∧ IsPrivateTriple A g m := by
      intro N
      obtain ⟨g, hgSource, hgN⟩ :=
        hsourceInf.exists_gt N
      obtain ⟨i, hiK, rfl⟩ := hgSource
      have hiL : i ∈ L := hKL hiK
      obtain ⟨hfailed, hdiC, hdib, haiA, huiA, hviA,
          hdia, hbuv, hba, hduv⟩ :=
        hrows i hiL
      have hnotAlt :
          ¬HasAlternativeTriple A (d i) (n i) := by
        simpa [P] using hiK.2
      have hprivate : IsPrivateTriple A (d i) (n i) :=
        (alternativeTriple_or_private h0 hcov hfailed.2.1).resolve_left
          hnotAlt
      have hdpos : 0 < d i := by
        by_contra hd0
        have : d i = 0 := Nat.eq_zero_of_not_pos hd0
        exact h0C (this ▸ hdiC)
      exact ⟨d i, n i, by omega, hdpos, hprivate⟩
    obtain ⟨B, hBA, hBinf, hsurvive⟩ :=
      surviving_deletion_of_cofinal_privateStream
        h0 hcov hstream hanchor
    exact hglobal B hBA hBinf
      (exactTupleBasis_diff_of_survival hsurvive)

open Classical in
/-- After eliminating the conflict case, an anchored counterexample
with a genuine finite schedule has only two non-increment outputs:
fixed collateral composition, or an explicit cofinal failure of
co-sum normalization. -/
theorem anchored_counterexample_riskSchedule_increment_or_fixed_or_nonNormalizable
    {A C : Set ℕ} {N₀ k : ℕ} {σ : ℕ → Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hCA : C ⊆ A) (hCinf : C.Infinite) (h0C : 0 ∉ C)
    (hglobal : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧
      ∃ w ∈ A, ∃ w' ∈ A,
        w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hschedule : HasSurvivingFiniteRiskSchedule A C σ)
    (hcard : ∀ b ∈ C, (σ b).card = k) :
    (∃ D ⊆ C, D.Infinite ∧
      ∃ σ' : ℕ → Finset ℕ,
        HasSurvivingFiniteRiskSchedule A D σ' ∧
        ∀ b ∈ D, (σ' b).card = k + 1) ∨
    (∃ b ∈ C, HasCofinalFixedCollateralRows A C N₀ σ b) ∨
    ∃ b ∈ C,
      HasCofinalNonNormalizableCollateralRows A C N₀ σ b := by
  rcases anchored_counterexample_riskSchedule_increment_or_terminalRows
      h0 hcov hCA hCinf h0C hglobal hanchor hschedule hcard with
    hincrement | hfixed | hcollision | hnonNormal
  · exact Or.inl hincrement
  · exact Or.inr (Or.inl hfixed)
  · obtain ⟨b, hbC, hcollision⟩ := hcollision
    exact Or.inl
      (anchored_sourceConflictRows_force_increment
        h0 hcov hCA h0C hbC hglobal hanchor
          hschedule hcard hcollision)
  · exact Or.inr (Or.inr hnonNormal)

open Classical in

theorem anchored_counterexample_freshAlternativeRiskSource
    {A C : Set ℕ} {N₀ k : ℕ} {σ : ℕ → Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hCA : C ⊆ A) (hCinf : C.Infinite) (h0C : 0 ∉ C)
    (hglobal : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧
      ∃ w ∈ A, ∃ w' ∈ A,
        w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hschedule : HasSurvivingFiniteRiskSchedule A C σ)
    (hcard : ∀ b ∈ C, (σ b).card = k)
    (hnoIncrement : ¬∃ D ⊆ C, D.Infinite ∧
      ∃ σ' : ℕ → Finset ℕ,
        HasSurvivingFiniteRiskSchedule A D σ' ∧
        ∀ b ∈ D, (σ' b).card = k + 1)
    (F : Finset ℕ) :
    ∃ b ∈ C, b ∉ F ∧ ∃ n,
      (∀ c ∈ C, n ∉ σ c) ∧
      (∃ a ∈ A, b + a = n) ∧
      HasAlternativeTriple A b n := by
  let D : Set ℕ := C \ (F : Set ℕ)
  have hDC : D ⊆ C := by
    intro x hx
    exact hx.1
  have hDinf : D.Infinite := by
    exact hCinf.diff F.finite_toSet
  have hDA : D ⊆ A :=
    hDC.trans hCA
  have h0D : 0 ∉ D := by
    intro hzero
    exact h0C (hDC hzero)
  have hscheduleD :
      HasSurvivingFiniteRiskSchedule A D σ := by
    intro b hbD m hm
    obtain ⟨hrisk, x, hxA, y, hyA, z, hzA,
        hxC, hyC, hzC, hxyz⟩ :=
      hschedule b (hDC hbD) m hm
    exact ⟨hrisk, x, hxA, y, hyA, z, hzA,
      fun hxD => hxC (hDC hxD),
      fun hyD => hyC (hDC hyD),
      fun hzD => hzC (hDC hzD), hxyz⟩
  have hcardD : ∀ b ∈ D, (σ b).card = k := by
    intro b hbD
    exact hcard b (hDC hbD)
  rcases
      anchored_counterexample_riskSchedule_increment_or_fixedCollateral
        (A := A) (C := D) (N₀ := N₀) (k := k) (σ := σ)
        h0 hcov hDA hDinf h0D hglobal hanchor
          hscheduleD hcardD with
    hincrement | ⟨b, hbD, hcofinal⟩
  · exfalso
    obtain ⟨E, hED, hEinf, σ', hschedule', hcard'⟩ :=
      hincrement
    exact hnoIncrement
      ⟨E, hED.trans hDC, hEinf, σ', hschedule', hcard'⟩
  · let U : Finset ℕ := F.biUnion σ
    obtain ⟨n, hnU, hfailed, halt⟩ :=
      hcofinal (U.sum id)
    refine ⟨b, hDC hbD, hbD.2, n, ?_,
      hfailed.2.2.1, halt⟩
    intro c hcC hnσ
    by_cases hcF : c ∈ F
    · have hnMemU : n ∈ U := by
        exact Finset.mem_biUnion.mpr ⟨c, hcF, hnσ⟩
      have hnLe : n ≤ U.sum id :=
        Finset.single_le_sum
          (fun x _hx => Nat.zero_le x) hnMemU
      omega
    · exact hfailed.2.2.2.1 c ⟨hcC, hcF⟩ hnσ

open Classical in

theorem anchored_counterexample_riskSchedule_increment
    {A C : Set ℕ} {N₀ k : ℕ} {σ : ℕ → Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hCA : C ⊆ A) (hCinf : C.Infinite) (h0C : 0 ∉ C)
    (hglobal : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧
      ∃ w ∈ A, ∃ w' ∈ A,
        w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hschedule : HasSurvivingFiniteRiskSchedule A C σ)
    (hcard : ∀ b ∈ C, (σ b).card = k) :
    ∃ D ⊆ C, D.Infinite ∧
      ∃ σ' : ℕ → Finset ℕ,
        HasSurvivingFiniteRiskSchedule A D σ' ∧
        ∀ b ∈ D, (σ' b).card = k + 1 := by
  by_contra hnoIncrement
  have hchoice : ∀ F : Finset ℕ, ∃ b, ∃ n,
      b ∈ C ∧ b ∉ F ∧
      (∀ c ∈ C, n ∉ σ c) ∧
      (∃ a ∈ A, b + a = n) ∧
      HasAlternativeTriple A b n := by
    intro F
    obtain ⟨b, hbC, hbF, n, hoff, hrisk, halt⟩ :=
      anchored_counterexample_freshAlternativeRiskSource
        h0 hcov hCA hCinf h0C hglobal hanchor
          hschedule hcard hnoIncrement F
    exact ⟨b, n, hbC, hbF, hoff, hrisk, halt⟩
  choose source target hdata using hchoice
  let used : ℕ → Finset ℕ :=
    fun i => Nat.rec (∅ : Finset ℕ)
      (fun _ (F : Finset ℕ) => insert (source F) F) i
  let b : ℕ → ℕ := fun i => source (used i)
  let n : ℕ → ℕ := fun i => target (used i)
  have husedSucc : ∀ i,
      used (i + 1) = insert (b i) (used i) := by
    intro i
    simp only [used, b]
  have husedStep : ∀ i, used i ⊆ used (i + 1) := by
    intro i
    rw [husedSucc]
    exact Finset.subset_insert _ _
  have husedMono : Monotone used :=
    monotone_nat_of_le_succ husedStep
  have hbUsedNext : ∀ i, b i ∈ used (i + 1) := by
    intro i
    rw [husedSucc]
    exact Finset.mem_insert_self _ _
  have hbC : ∀ i, b i ∈ C := by
    intro i
    exact (hdata (used i)).1
  have hbFresh : ∀ i, b i ∉ used i := by
    intro i
    exact (hdata (used i)).2.1
  have hbInjective : Function.Injective b := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hijlt | hjilt
    · have hbiUsed : b i ∈ used j :=
        husedMono (Nat.succ_le_of_lt hijlt) (hbUsedNext i)
      exact hbFresh j (hij ▸ hbiUsed)
    · have hbjUsed : b j ∈ used i :=
        husedMono (Nat.succ_le_of_lt hjilt) (hbUsedNext j)
      exact hbFresh i (hij.symm ▸ hbjUsed)
  have hKinf : (Set.range b).Infinite :=
    Set.infinite_range_of_injective hbInjective
  have hKC : Set.range b ⊆ C := by
    rintro c ⟨i, rfl⟩
    exact hbC i
  have hincrement :=
    infiniteAlternativeRiskSources_scheduleIncrement
      hKC hKinf hschedule hcard
      (fun c hc => by
        obtain ⟨i, rfl⟩ := hc
        have hi := hdata (used i)
        exact ⟨n i, hi.2.2.1 (b i) (hbC i),
          hi.2.2.2.1,
          hi.2.2.2.2⟩)
  exact hnoIncrement hincrement

open Classical in

theorem anchored_counterexample_serves_finite_translationSlices
    {A C : Set ℕ} {N₀ : ℕ} (Q : Finset ℕ)
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hCinf : C.Infinite)
    (hCAbove : ∀ b ∈ C, N₀ ≤ b)
    (hglobal : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧
      ∃ w ∈ A, ∃ w' ∈ A,
        w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g) :
    ∃ D ⊆ C, D.Infinite ∧
      ∀ b ∈ D, ∀ q ∈ Q,
        ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
          x ∉ D ∧ y ∉ D ∧ z ∉ D ∧
          x + y + z = b + q := by
  let BadAt : ℕ → Set ℕ := fun q =>
    {b | b ∈ C ∧ IsPrivateTriple A b (b + q)}
  have hBadAtFinite : ∀ q ∈ (Q : Set ℕ),
      (BadAt q).Finite := by
    intro q hqQ
    apply Set.not_infinite.mp
    intro hBadInf
    have hstream : ∀ N, ∃ g m, N ≤ m ∧
        0 < g ∧ IsPrivateTriple A g m := by
      intro N
      obtain ⟨b, hbBad, hbN⟩ :=
        hBadInf.exists_gt N
      have hbpos : 0 < b := by omega
      exact ⟨b, b + q, by omega, hbpos, hbBad.2⟩
    obtain ⟨B, hBA, hBinf, hsurvive⟩ :=
      surviving_deletion_of_cofinal_privateStream
        h0 hcov hstream hanchor
    exact hglobal B hBA hBinf
      (exactTupleBasis_diff_of_survival hsurvive)
  let Bad : Set ℕ :=
    ⋃ q ∈ (Q : Set ℕ), BadAt q
  have hBadFinite : Bad.Finite := by
    exact Q.finite_toSet.biUnion hBadAtFinite
  let K : Set ℕ := C \ Bad
  have hKinf : K.Infinite :=
    hCinf.diff hBadFinite
  have hKC : K ⊆ C := by
    intro b hb
    exact hb.1
  have hrepchoice : ∀ b q, ∃ x, ∃ y, ∃ z,
      b ∈ K → q ∈ Q →
      x ∈ A ∧ y ∈ A ∧ z ∈ A ∧
      x + y + z = b + q ∧
      x ≠ b ∧ y ≠ b ∧ z ≠ b := by
    intro b q
    by_cases hbK : b ∈ K
    · by_cases hqQ : q ∈ Q
      · have hnotPrivate :
            ¬IsPrivateTriple A b (b + q) := by
          intro hprivate
          apply hbK.2
          simp only [Bad, Set.mem_iUnion]
          exact ⟨q, hqQ, hbK.1, hprivate⟩
        have halt : HasAlternativeTriple A b (b + q) :=
          (alternativeTriple_or_private h0 hcov
            (by have := hCAbove b hbK.1; omega)).resolve_right
              hnotPrivate
        obtain ⟨x, hxA, y, hyA, z, hzA,
            hxyz, hxb, hyb, hzb⟩ := halt
        exact ⟨x, y, z, fun _ _ =>
          ⟨hxA, hyA, hzA, hxyz, hxb, hyb, hzb⟩⟩
      · exact ⟨0, 0, 0, fun _ h => absurd h hqQ⟩
    · exact ⟨0, 0, 0, fun h => absurd h hbK⟩
  choose x y z hrep using hrepchoice
  let f : ℕ → Finset ℕ := fun b =>
    Q.biUnion fun q => {x b q, y b q, z b q}
  have hfcard : ∀ b ∈ K, (f b).card ≤ 3 * Q.card := by
    intro b hbK
    calc
      (f b).card ≤
          ∑ q ∈ Q, ({x b q, y b q, z b q} : Finset ℕ).card := by
        exact Finset.card_biUnion_le
      _ ≤ ∑ _q ∈ Q, 3 := by
        apply Finset.sum_le_sum
        intro q hqQ
        calc
          ({x b q, y b q, z b q} : Finset ℕ).card ≤
              ({y b q, z b q} : Finset ℕ).card + 1 := by
            exact Finset.card_insert_le _ _
          _ ≤ ({z b q} : Finset ℕ).card + 1 + 1 := by
            exact Nat.add_le_add_right
              (Finset.card_insert_le _ _) 1
          _ ≤ 3 := by simp
      _ = 3 * Q.card := by simp [Nat.mul_comm]
  have hfavoid : ∀ b ∈ K, b ∉ f b := by
    intro b hbK hb
    obtain ⟨q, hqQ, hbSupport⟩ :=
      Finset.mem_biUnion.mp hb
    obtain ⟨hxA, hyA, hzA, hxyz, hxb, hyb, hzb⟩ :=
      hrep b q hbK hqQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbSupport
    rcases hbSupport with h | h | h
    · exact hxb h.symm
    · exact hyb h.symm
    · exact hzb h.symm
  obtain ⟨D, hDK, hDinf, hfree⟩ :=
    exists_infinite_freeSet_of_bounded_pointMap
      hKinf f (3 * Q.card) hfcard hfavoid
  refine ⟨D, hDK.trans hKC, hDinf, ?_⟩
  intro b hbD q hqQ
  have hbK := hDK hbD
  obtain ⟨hxA, hyA, hzA, hxyz, hxb, hyb, hzb⟩ :=
    hrep b q hbK hqQ
  have hdis := Set.disjoint_left.mp (hfree b hbD)
  refine ⟨x b q, hxA, y b q, hyA, z b q, hzA,
    ?_, ?_, ?_, hxyz⟩
  · intro hxD
    exact hdis
      (Finset.mem_biUnion.mpr
        ⟨q, hqQ, by simp⟩) hxD
  · intro hyD
    exact hdis
      (Finset.mem_biUnion.mpr
        ⟨q, hqQ, by simp⟩) hyD
  · intro hzD
    exact hdis
      (Finset.mem_biUnion.mpr
        ⟨q, hqQ, by simp⟩) hzD

open Classical in
/-- Tail form of finite translation-slice fairness.  The lower-bound
hypothesis is automatic after discarding the finite initial interval
`[0,N₀)`. -/
theorem anchored_counterexample_serves_finite_translationSlices_on_tail
    {A C : Set ℕ} {N₀ : ℕ} (Q : Finset ℕ)
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hCinf : C.Infinite)
    (hglobal : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧
      ∃ w ∈ A, ∃ w' ∈ A,
        w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g) :
    ∃ D ⊆ C, D.Infinite ∧
      ∀ b ∈ D, ∀ q ∈ Q,
        ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
          x ∉ D ∧ y ∉ D ∧ z ∉ D ∧
          x + y + z = b + q := by
  let K : Set ℕ := C \ Set.Iio N₀
  have hKinf : K.Infinite :=
    hCinf.diff (Set.finite_Iio N₀)
  have hKAbove : ∀ b ∈ K, N₀ ≤ b := by
    intro b hbK
    exact Nat.le_of_not_gt hbK.2
  obtain ⟨D, hDK, hDinf, hserve⟩ :=
    anchored_counterexample_serves_finite_translationSlices
      (C := K) Q h0 hcov hKinf hKAbove hglobal hanchor
  exact ⟨D, hDK.trans Set.diff_subset, hDinf, hserve⟩

open Classical in
/-- Finite-slice fairness in genuine schedule form.  Any prescribed finite
set `Q⊆A` can be installed as the exact risk schedule
`σ(b)={b+q | q∈Q}` on an infinite thinning. -/
theorem anchored_counterexample_has_prescribedFiniteRiskSchedule
    {A C : Set ℕ} {N₀ : ℕ} (Q : Finset ℕ)
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hQA : ∀ q ∈ Q, q ∈ A)
    (hCinf : C.Infinite)
    (hglobal : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧
      ∃ w ∈ A, ∃ w' ∈ A,
        w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g) :
    ∃ D ⊆ C, D.Infinite ∧
      ∃ σ : ℕ → Finset ℕ,
        HasSurvivingFiniteRiskSchedule A D σ ∧
        (∀ b, σ b = Q.image (fun q => b + q)) ∧
        ∀ b ∈ D, (σ b).card = Q.card := by
  obtain ⟨D, hDC, hDinf, hserve⟩ :=
    anchored_counterexample_serves_finite_translationSlices_on_tail
      (A := A) Q h0 hcov hCinf hglobal hanchor
  let σ : ℕ → Finset ℕ :=
    fun b => Q.image (fun q => b + q)
  have hschedule : HasSurvivingFiniteRiskSchedule A D σ := by
    intro b hbD m hm
    simp only [σ, Finset.mem_image] at hm
    obtain ⟨q, hqQ, rfl⟩ := hm
    obtain ⟨x, hxA, y, hyA, z, hzA,
        hxD, hyD, hzD, hxyz⟩ :=
      hserve b hbD q hqQ
    exact ⟨⟨q, hQA q hqQ, rfl⟩,
      x, hxA, y, hyA, z, hzA,
      hxD, hyD, hzD, hxyz⟩
  refine ⟨D, hDC, hDinf, σ, hschedule, fun b => rfl, ?_⟩
  intro b hbD
  change (Q.image (fun q => b + q)).card = Q.card
  exact Finset.card_image_of_injective Q
    (fun q r hqr => by omega)

open Classical in
/-- Every finite offset window can be made fair on some infinite
deletion: all risks `b+q` with `q∈A∩[0,M]` occur in the schedule.
Only the dependence of the deletion on `M` remains. -/
theorem anchored_counterexample_has_every_finite_fairWindow
    {A C : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hCinf : C.Infinite)
    (hglobal : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧
      ∃ w ∈ A, ∃ w' ∈ A,
        w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g) :
    ∀ M, ∃ D ⊆ C, D.Infinite ∧
      ∃ σ : ℕ → Finset ℕ,
        HasSurvivingFiniteRiskSchedule A D σ ∧
        ∀ b ∈ D, ∀ q ∈ A, q ≤ M → b + q ∈ σ b := by
  intro M
  let Q : Finset ℕ :=
    (Finset.range (M + 1)).filter fun q => q ∈ A
  have hQA : ∀ q ∈ Q, q ∈ A := by
    intro q hqQ
    exact (Finset.mem_filter.mp hqQ).2
  obtain ⟨D, hDC, hDinf, σ, hschedule, hσ, hcard⟩ :=
    anchored_counterexample_has_prescribedFiniteRiskSchedule
      (A := A) Q h0 hcov hQA hCinf hglobal hanchor
  refine ⟨D, hDC, hDinf, σ, hschedule, ?_⟩
  intro b hbD q hqA hqM
  rw [hσ b]
  apply Finset.mem_image.mpr
  refine ⟨q, ?_, rfl⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega), hqA⟩

open Classical in

theorem fixedDeletion_allFiniteFairWindows_implies_basis
    {A D : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (h0D : 0 ∉ D) (hcov : PairCovers A N₀)
    (hfair : ∀ M, ∃ σ : ℕ → Finset ℕ,
      HasSurvivingFiniteRiskSchedule A D σ ∧
      ∀ b ∈ D, ∀ q ∈ A, q ≤ M → b + q ∈ σ b) :
    IsExactTupleAsymptoticBasis (A \ D) 3 := by
  apply deletion_criterion_local h0 h0D hcov
  intro n hn
  rintro ⟨b, hbD, a, haA, hba⟩
  obtain ⟨σ, hschedule, hwindow⟩ := hfair a
  have hmem : b + a ∈ σ b :=
    hwindow b hbD a haA le_rfl
  obtain ⟨hrisk, x, hxA, y, hyA, z, hzA,
      hxD, hyD, hzD, hxyz⟩ :=
    hschedule b hbD (b + a) hmem
  exact ⟨x, hxA, y, hyA, z, hzA,
    hxD, hyD, hzD, by omega⟩

open Classical in

theorem finite_free_pointMaps_not_countably_fusible :
    let f : ℕ → ℕ → Finset ℕ :=
      fun q b => if q < b then {q} else ∅
    (∀ C : Set ℕ, C.Infinite → ∀ Q : Finset ℕ,
      ∃ D ⊆ C, D.Infinite ∧
      ∀ q ∈ Q, ∀ b ∈ D,
        Disjoint ((f q b : Finset ℕ) : Set ℕ) D) ∧
    ¬∃ D : Set ℕ, D.Infinite ∧
      ∀ q, ∀ b ∈ D,
        Disjoint ((f q b : Finset ℕ) : Set ℕ) D := by
  dsimp
  constructor
  · intro C hCinf Q
    let D : Set ℕ := C \ Set.Iic (Q.sum id)
    have hDinf : D.Infinite :=
      hCinf.diff (Set.finite_Iic (Q.sum id))
    refine ⟨D, Set.diff_subset, hDinf, ?_⟩
    intro q hqQ b hbD
    rw [Set.disjoint_left]
    intro x hxf hxD
    have hqLe : q ≤ Q.sum id :=
      Finset.single_le_sum
        (fun y _hy => Nat.zero_le y) hqQ
    have hqb : q < b := by
      have hbLarge : b ∉ Set.Iic (Q.sum id) := hbD.2
      simp only [Set.mem_Iic] at hbLarge
      omega
    have hxq : x = q := by
      simpa [hqb] using hxf
    subst x
    exact hxD.2 (by simpa only [Set.mem_Iic] using hqLe)
  · rintro ⟨D, hDinf, hfree⟩
    obtain ⟨q, hqD⟩ := hDinf.nonempty
    obtain ⟨b, hbD, hqb⟩ := hDinf.exists_gt q
    have hdis := Set.disjoint_left.mp (hfree q b hbD)
    exact hdis (by simp [hqb]) hqD

open Classical in
/-- An infinite deletion for which every deleted point has both its
selected target and one distinct off-selector target already served. -/
def HasTwoTargetFixedTransversalThinning
    (A C : Set ℕ) (N₀ : ℕ) (τ : ℕ → ℕ) : Prop :=
  ∃ D : Set ℕ, D ⊆ C ∧ D.Infinite ∧
    ∀ x ∈ D,
      (∃ p ∈ A, ∃ q ∈ A, ∃ r ∈ A,
        p ∉ D ∧ q ∉ D ∧ r ∉ D ∧ p + q + r = τ x) ∧
      ∃ m, N₀ ≤ m ∧ x ≤ m ∧ τ x ≠ m ∧
        (∀ b ∈ C, τ b ≠ m) ∧
        ∃ p ∈ A, ∃ q ∈ A, ∃ r ∈ A,
          p ∉ D ∧ q ∉ D ∧ r ∉ D ∧ p + q + r = m

open Classical in

theorem blockSeparatedMultipleDeletionTransversals_has_twoTargetFixedTransversalThinning
    {A C : Set ℕ} {N₀ : ℕ} {τ : ℕ → ℕ}
    (hCA : C ⊆ A)
    (hselected : ∀ b ∈ C,
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ C ∧ y ∉ C ∧ z ∉ C ∧ x + y + z = τ b)
    (hblocks :
      HasBlockSeparatedMultipleOffSelectorDeletionTransversals A C N₀ τ) :
    HasTwoTargetFixedTransversalThinning A C N₀ τ := by
  unfold HasTwoTargetFixedTransversalThinning
  obtain ⟨n, H, hnmono, hcomm, hcard, habove, hdisjoint⟩ :=
    hblocks
  have htwo : ∀ i, ∃ d ∈ H i, ∃ e ∈ H i, d ≠ e := by
    intro i
    apply Finset.one_lt_card.mp
    have := hcard i
    omega
  choose d hdH e heH hde using htwo
  have hcowitness : ∀ i, ∃ u ∈ A, ∃ v ∈ A,
      e i + u + v = n i ∧
      ∀ g ∈ H i, g ≠ e i → u ≠ g ∧ v ≠ g := by
    intro i
    exact minimalRepSupportTransversal_member_has_pairCowitness
      (hcomm i).2.2.2.1 (hcomm i).2.2.2.2.1 (heH i)
  choose u huA v hvA huv havoid using hcowitness
  have hdInjective : Function.Injective d := by
    intro i j hdij
    by_contra hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hdis := Finset.disjoint_left.mp (hdisjoint i j hij)
      have hdiHj : d i ∈ H j := by
        rw [hdij]
        exact hdH j
      exact hdis (hdH i) hdiHj
    · have hdis := Finset.disjoint_left.mp (hdisjoint j i hji)
      have hdjHi : d j ∈ H i := by
        rw [← hdij]
        exact hdH i
      exact hdis (hdH j) hdjHi
  let K : Set ℕ := Set.range d
  have hKinf : K.Infinite :=
    Set.infinite_range_of_injective hdInjective
  let idx : ℕ → ℕ := fun x =>
    if hx : x ∈ K then Classical.choose hx else 0
  have hidx : ∀ x ∈ K, d (idx x) = x := by
    intro x hx
    simpa [idx, hx] using Classical.choose_spec hx
  let f : ℕ → Finset ℕ := fun x =>
    {e (idx x), u (idx x), v (idx x)}
  have hfcard : ∀ x ∈ K, (f x).card ≤ 3 := by
    intro x hx
    calc
      (f x).card ≤
          ({u (idx x), v (idx x)} : Finset ℕ).card + 1 := by
        simpa [f] using
          Finset.card_insert_le (e (idx x))
            ({u (idx x), v (idx x)} : Finset ℕ)
      _ ≤ ({v (idx x)} : Finset ℕ).card + 1 + 1 := by
        exact Nat.add_le_add_right
          (Finset.card_insert_le (u (idx x)) {v (idx x)}) 1
      _ ≤ 3 := by simp
  have hfavoid : ∀ x ∈ K, x ∉ f x := by
    intro x hx
    have hav :=
      havoid (idx x) (d (idx x)) (hdH (idx x)) (hde (idx x))
    simp only [f, Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_⟩
    · intro hxe
      exact hde (idx x) ((hidx x hx).trans hxe)
    · intro hxu
      exact hav.1 ((hidx x hx).trans hxu).symm
    · intro hxv
      exact hav.2 ((hidx x hx).trans hxv).symm
  obtain ⟨D, hDK, hDinf, hfree⟩ :=
    exists_infinite_freeSet_of_bounded_pointMap
      hKinf f 3 hfcard hfavoid
  have hDC : D ⊆ C := by
    intro x hxD
    obtain ⟨i, rfl⟩ := hDK hxD
    have hdFilter := (hcomm i).2.2.2.2.2 (hdH i)
    exact (Finset.mem_filter.1 hdFilter).2
  refine ⟨D, hDC, hDinf, ?_⟩
  intro x hxD
  have hxK := hDK hxD
  obtain ⟨i, hix⟩ := hxK
  have hidxi : idx x = i := by
    apply hdInjective
    rw [hidx x (hDK hxD), hix]
  have hcoordAvoid : e i ∉ D ∧ u i ∉ D ∧ v i ∉ D := by
    have hdis := Set.disjoint_left.mp (hfree x hxD)
    refine ⟨?_, ?_, ?_⟩
    · intro heD
      exact hdis (by simp [f, hidxi]) heD
    · intro huD
      exact hdis (by simp [f, hidxi]) huD
    · intro hvD
      exact hdis (by simp [f, hidxi]) hvD
  obtain ⟨p, hpA, q, hqA, r, hrA, hpC, hqC, hrC, hpqr⟩ :=
    hselected x (hDC hxD)
  have hselectedD :
      ∃ p ∈ A, ∃ q ∈ A, ∃ r ∈ A,
        p ∉ D ∧ q ∉ D ∧ r ∉ D ∧ p + q + r = τ x :=
    ⟨p, hpA, q, hqA, r, hrA,
      fun hpD => hpC (hDC hpD),
      fun hqD => hqC (hDC hqD),
      fun hrD => hrC (hDC hrD), hpqr⟩
  have hxm : x ≤ n i := by
    have hdFilter := (hcomm i).2.2.2.2.2 (hdH i)
    have hdiRange := Finset.mem_range.1 (Finset.mem_filter.1 hdFilter).1
    omega
  refine ⟨hselectedD, n i, (hcomm i).1, hxm,
    (hcomm i).2.1 x (hDC hxD), (hcomm i).2.1, ?_⟩
  refine ⟨e i, ?_, u i, huA i, v i, hvA i,
    hcoordAvoid.1, hcoordAvoid.2.1, hcoordAvoid.2.2, huv i⟩
  have heFilter := (hcomm i).2.2.2.2.2 (heH i)
  exact hCA (Finset.mem_filter.1 heFilter).2

open Classical in
/-- A two-target fixed transversal thinning is equivalently an infinite subdeletion
carrying a surviving coverage schedule of uniform cardinality two. -/
theorem twoTargetFixedTransversalThinning_has_uniform_twoCoverageSchedule
    {A C : Set ℕ} {N₀ : ℕ} {τ : ℕ → ℕ}
    (hdoors : HasTwoTargetFixedTransversalThinning A C N₀ τ) :
    ∃ D ⊆ C, D.Infinite ∧
      HasUniformSurvivingCoverageSchedule A D 2 := by
  obtain ⟨D, hDC, hDinf, hserve⟩ := hdoors
  have hchoice : ∀ x, ∃ m, x ∈ D →
      τ x ≠ m ∧
      ∃ p ∈ A, ∃ q ∈ A, ∃ r ∈ A,
        p ∉ D ∧ q ∉ D ∧ r ∉ D ∧ p + q + r = m := by
    intro x
    by_cases hxD : x ∈ D
    · obtain ⟨m, hm₀, hxm, hne, hoff, hrep⟩ :=
        (hserve x hxD).2
      exact ⟨m, fun _ => ⟨hne, hrep⟩⟩
    · exact ⟨0, fun hx => absurd hx hxD⟩
  choose μ hμ using hchoice
  let σ : ℕ → Finset ℕ := fun x => {τ x, μ x}
  have hschedule : HasSurvivingFiniteCoverageSchedule A D σ := by
    intro x hxD m hm
    simp only [σ, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hmt | hmt
    · subst m
      exact (hserve x hxD).1
    · subst m
      exact (hμ x hxD).2
  have hcard : ∀ x ∈ D, (σ x).card = 2 := by
    intro x hxD
    have hne := (hμ x hxD).1
    simp [σ, hne]
  exact ⟨D, hDC, hDinf, σ, hschedule, hcard⟩

open Classical in

theorem counterexample_fixedRepairChannel_deletion_transversal_boundary
    {A : Set ℕ} {N₀ w : ℕ} {B : Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ C ⊆ A, C.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ C) 3)
    (hcofinal : ∀ X, ∃ b ∈ A, X < b ∧
      HasTerminalRepairDestructionThrough A N₀ B w b) :
    ∃ C : Set ℕ, ∃ τ : ℕ → ℕ,
      C ⊆ A ∧ C.Infinite ∧ 0 ∉ C ∧ w ∉ C ∧ w ∈ A ∧
      (∀ b ∈ C, N₀ ≤ τ b ∧ b ≤ τ b ∧
        (∃ d ∈ insert b B, ∃ a ∈ A, d + a = τ b) ∧
        IsPrivateTriple (A \ (B : Set ℕ)) b (τ b) ∧
        ∃ u ∈ A \ C, ∃ v ∈ A \ C, w + u + v = τ b) ∧
      (HasRecurrentOffSelectorRequiredElement A C N₀ τ ∨
       HasCofinalNonbigOffSelectorPrivateStream A C N₀ τ ∨
       HasBlockSeparatedMultipleOffSelectorDeletionTransversals A C N₀ τ) := by
  obtain ⟨C, τ, hCA, hCinf, h0C, hwC, hwA, hdata⟩ :=
    cofinal_fixedRepairChannel_has_conflictFree_selector hcofinal
  have hselected : ∀ b ∈ C,
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ C ∧ y ∉ C ∧ z ∉ C ∧ x + y + z = τ b := by
    intro b hbC
    obtain ⟨-, -, -, -, u, hu, v, hv, huv⟩ := hdata b hbC
    exact ⟨w, hwA, u, hu.1, v, hv.1,
      hwC, hu.2, hv.2, huv⟩
  have hfailC := hfail C hCA hCinf
  rcases selectedRepairs_recurrentRequiredElement_or_escapingDeletionTransversals
      τ h0 h0C hcov hselected hfailC with hrec | hesc
  · exact ⟨C, τ, hCA, hCinf, h0C, hwC, hwA, hdata,
      Or.inl hrec⟩
  · rcases escapingDeletionTransversals_singletonPrivate_or_uniformlyMultiple
      h0 hcov hesc with hsingle | hmultiple
    · have hnonbig :=
        cofinal_offSelector_absolutePrivate_destructions_are_nonbig
          h0 hcov hCA hsingle
      exact ⟨C, τ, hCA, hCinf, h0C, hwC, hwA, hdata,
        Or.inr (Or.inl hnonbig)⟩
    · obtain ⟨W₀, T₀, hlarge, hsupply⟩ := hmultiple
      have hblocks :=
        escapingUniformlyMultipleDeletionTransversals_has_blockSequence
          hlarge hesc
      exact ⟨C, τ, hCA, hCinf, h0C, hwC, hwA, hdata,
        Or.inr (Or.inr hblocks)⟩

open Classical in

theorem counterexample_fixedRepairChannel_twoTarget_boundary
    {A : Set ℕ} {N₀ w : ℕ} {B : Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ C ⊆ A, C.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ C) 3)
    (hcofinal : ∀ X, ∃ b ∈ A, X < b ∧
      HasTerminalRepairDestructionThrough A N₀ B w b) :
    ∃ C : Set ℕ, ∃ τ : ℕ → ℕ,
      C ⊆ A ∧ C.Infinite ∧ 0 ∉ C ∧ w ∉ C ∧ w ∈ A ∧
      (∀ b ∈ C, N₀ ≤ τ b ∧ b ≤ τ b ∧
        (∃ d ∈ insert b B, ∃ a ∈ A, d + a = τ b) ∧
        IsPrivateTriple (A \ (B : Set ℕ)) b (τ b) ∧
        ∃ u ∈ A \ C, ∃ v ∈ A \ C, w + u + v = τ b) ∧
      (HasRecurrentOffSelectorRequiredElement A C N₀ τ ∨
       HasCofinalNonbigOffSelectorPrivateStream A C N₀ τ ∨
       HasTwoTargetFixedTransversalThinning A C N₀ τ) := by
  obtain ⟨C, τ, hCA, hCinf, h0C, hwC, hwA, hdata,
    hrec | hprivate | hblocks⟩ :=
    counterexample_fixedRepairChannel_deletion_transversal_boundary
      h0 hcov hfail hcofinal
  · exact ⟨C, τ, hCA, hCinf, h0C, hwC, hwA, hdata,
      Or.inl hrec⟩
  · exact ⟨C, τ, hCA, hCinf, h0C, hwC, hwA, hdata,
      Or.inr (Or.inl hprivate)⟩
  · have hselected : ∀ b ∈ C,
        ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
          x ∉ C ∧ y ∉ C ∧ z ∉ C ∧ x + y + z = τ b := by
      intro b hbC
      obtain ⟨-, -, -, -, u, hu, v, hv, huv⟩ := hdata b hbC
      exact ⟨w, hwA, u, hu.1, v, hv.1,
        hwC, hu.2, hv.2, huv⟩
    have hdoors :=
      blockSeparatedMultipleDeletionTransversals_has_twoTargetFixedTransversalThinning
        hCA hselected hblocks
    exact ⟨C, τ, hCA, hCinf, h0C, hwC, hwA, hdata,
      Or.inr (Or.inr hdoors)⟩

open Classical in
/-- An absolute terminal destruction in the non-big regime: the co-offset is at
least the required element. -/
def HasNonBigAbsoluteTerminalDestruction
    (A : Set ℕ) (N₀ : ℕ) (B : Finset ℕ) (b : ℕ) : Prop :=
  ∃ n, N₀ ≤ n ∧ b ≤ n ∧ 2 * b ≤ n ∧
    (∃ d ∈ insert b B, ∃ a ∈ A, d + a = n) ∧
    IsPrivateTriple (A \ (B : Set ℕ)) b n ∧
    IsPrivateTriple A b n

open Classical in
/-- A cofinal stream of absolute terminal destructions can be thinned to the
non-big regime `2b≤n`; otherwise its cofinal big substream contradicts
`no_cofinal_big_absolute_private_required_elements`. -/
theorem cofinal_absolute_terminal_destructions_are_nonbig
    {A : Set ℕ} {N₀ : ℕ} {B : Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hcofinal : ∀ X, ∃ b ∈ A, X < b ∧
      HasAbsoluteTerminalDestruction A N₀ B b) :
    ∀ X, ∃ b ∈ A, X < b ∧
      HasNonBigAbsoluteTerminalDestruction A N₀ B b := by
  by_contra hnonbig
  push Not at hnonbig
  obtain ⟨X₀, hX₀⟩ := hnonbig
  have hbigCofinal : ∀ X, ∃ b ∈ A, X < b ∧
      ∃ n, IsBigAbsolutePrivateDestruction A N₀ b n := by
    intro X
    obtain ⟨b, hbA, hbLarge, n, hn, hbn, hrisk,
      hrelative, habsolute⟩ := hcofinal (max X X₀)
    have hbX₀ : X₀ < b := by omega
    have hbig : n < 2 * b := by
      by_contra hnotBig
      have hnonBig : 2 * b ≤ n := Nat.le_of_not_gt hnotBig
      exact hX₀ b hbA hbX₀
        ⟨n, hn, hbn, hnonBig, hrisk, hrelative, habsolute⟩
    exact ⟨b, hbA, by omega, n,
      hn, hbn, hbig, habsolute⟩
  exact no_cofinal_big_absolute_private_required_elements h0 hcov hbigCofinal

open Classical in

theorem counterexample_nonbig_absolute_or_fixed_prefix_repairs
    {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ B : Finset ℕ,
      FinitePrefixServesRisks A N₀ B ∧ 0 ∉ B ∧
      ((∀ X, ∃ b ∈ A, X < b ∧
          HasNonBigAbsoluteTerminalDestruction A N₀ B b) ∨
       ∃ w ∈ B, ∀ X, ∃ b ∈ A, X < b ∧
          HasTerminalRepairDestructionThrough A N₀ B w b) := by
  obtain ⟨B, hserved, h0B, habsolute | hrepair⟩ :=
    counterexample_cofinal_absolute_or_fixed_prefix_repairs h0 hcov hfail
  · exact ⟨B, hserved, h0B, Or.inl
      (cofinal_absolute_terminal_destructions_are_nonbig
        h0 hcov habsolute)⟩
  · exact ⟨B, hserved, h0B, Or.inr hrepair⟩

open Classical in
/-- A terminal absolute destruction at twice the required element. -/
def HasDoubleAbsoluteTerminalDestruction
    (A : Set ℕ) (N₀ : ℕ) (B : Finset ℕ) (b : ℕ) : Prop :=
  N₀ ≤ 2 * b ∧
    (∃ d ∈ insert b B, ∃ a ∈ A, d + a = 2 * b) ∧
    IsPrivateTriple (A \ (B : Set ℕ)) b (2 * b) ∧
    IsPrivateTriple A b (2 * b)

open Classical in
/-- Absolute privacy at `2b` pins its covering pair uniquely to `b+b`.
This is the pointwise central geometry. -/
theorem absolute_private_double_forces_unique_pair
    {A : Set ℕ} {b : ℕ}
    (h0 : 0 ∈ A) (hbpos : 0 < b)
    (hprivate : IsPrivateTriple A b (2 * b)) :
    ∀ x ∈ A, ∀ y ∈ A, x + y = 2 * b → x = b ∧ y = b := by
  intro x hxA y hyA hxy
  rcases hprivate.2 x hxA y hyA 0 h0 (by omega) with
    hxb | hyb | h0b
  · exact ⟨hxb, by omega⟩
  · exact ⟨by omega, hyb⟩
  · exact absurd h0b (Nat.ne_of_lt hbpos)

open Classical in

theorem strict_small_absolute_private_structure
    {A : Set ℕ} {N₀ b n : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hbpos : 0 < b) (hn : N₀ ≤ n)
    (hprivate : IsPrivateTriple A b n) (hstrict : 2 * b < n) :
    ∃ q ∈ A, b < q ∧ b + q = n ∧
      IsPairSupportTransversal A b {b} ∧
      ∀ z ∈ A, q < z → z + N₀ ≤ n → False := by
  obtain ⟨q, hqA, hbq⟩ :=
    hprivate.corep_mem h0 hcov hbpos hn
  have hbq' : b < q := by omega
  have hpairSupportTransversal : IsPairSupportTransversal A b {b} := by
    intro x hxA y hyA hxy
    rcases hprivate.2 q hqA x hxA y hyA (by omega) with
      hqb | hxb | hyb
    · exact absurd hqb (Nat.ne_of_lt hbq').symm
    · exact Or.inl (by simp [hxb])
    · exact Or.inr (by simp [hyb])
  refine ⟨q, hqA, hbq', hbq, hpairSupportTransversal, ?_⟩
  intro z hzA hqz hzHigh
  exact hprivate.small_exclusion_interval h0 hcov hbpos hstrict hzA
    (by omega) hzHigh

open Classical in
/-- The singleton-deletion transversal branch has the same exact central/atomic
split as the original absolute-private branch: cofinally private doubles
with a unique covering pair, or cofinally strict-small singleton pair
support transversals with a post-corepresentative exclusion interval. -/
theorem cofinal_nonbig_offSelector_privateStream_split
    {A C : Set ℕ} {N₀ : ℕ} {τ : ℕ → ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hstream : HasCofinalNonbigOffSelectorPrivateStream
      A C N₀ τ) :
    (∀ W T, ∃ h ∈ C, W < h ∧ T ≤ 2 * h ∧ N₀ ≤ 2 * h ∧
      τ h ≠ 2 * h ∧ IsPrivateTriple A h (2 * h) ∧
      ∀ x ∈ A, ∀ y ∈ A, x + y = 2 * h → x = h ∧ y = h) ∨
    (∀ W T, ∃ n, T ≤ n ∧ ∃ h ∈ C,
      W < h ∧ N₀ ≤ n ∧ 2 * h < n ∧ τ h ≠ n ∧
      IsPrivateTriple A h n ∧
      ∃ q ∈ A, h < q ∧ h + q = n ∧
        IsPairSupportTransversal A h {h} ∧
        ∀ z ∈ A, q < z → z + N₀ ≤ n → False) := by
  by_cases hdouble : ∀ W T, ∃ h ∈ C,
      W < h ∧ T ≤ 2 * h ∧ N₀ ≤ 2 * h ∧
      τ h ≠ 2 * h ∧ IsPrivateTriple A h (2 * h) ∧
      ∀ x ∈ A, ∀ y ∈ A, x + y = 2 * h → x = h ∧ y = h
  · exact Or.inl hdouble
  · right
    push Not at hdouble
    obtain ⟨W₀, T₀, hnoDouble⟩ := hdouble
    intro W T
    obtain ⟨n, hnT, h, hhC, hhLarge, hhn, hn₀, hnonbig,
      hoff, hprivate⟩ :=
      hstream (max W (max W₀ 0)) (max T T₀)
    have hhpos : 0 < h := by omega
    have hstrict : 2 * h < n := by
      rcases lt_or_eq_of_le hnonbig with hlt | heq
      · exact hlt
      · exfalso
        have hunique :=
          absolute_private_double_forces_unique_pair h0 hhpos
            (by simpa [heq] using hprivate)
        obtain ⟨x, hxA, y, hyA, hxy, hbadPair⟩ :=
          hnoDouble h hhC (by omega) (by omega) (by omega)
            (by simpa [heq] using hoff)
            (by simpa [heq] using hprivate)
        have hxyUnique := hunique x hxA y hyA hxy
        exact hbadPair hxyUnique.1 hxyUnique.2
    obtain ⟨q, hqA, hhq, hhqsum, hpairSupportTransversal, hdesert⟩ :=
      strict_small_absolute_private_structure
        h0 hcov hhpos hn₀ hprivate hstrict
    exact ⟨n, by omega, h, hhC, by omega, hn₀, hstrict,
      hoff, hprivate, q, hqA, hhq, hhqsum, hpairSupportTransversal, hdesert⟩

open Classical in
/-- A strict-small terminal destruction, including its forced co-representative,
singleton pair support transversal, and exclusion interval. -/
def HasStrictSmallAbsoluteTerminalDestruction
    (A : Set ℕ) (N₀ : ℕ) (B : Finset ℕ) (b : ℕ) : Prop :=
  ∃ n, N₀ ≤ n ∧ b ≤ n ∧ 2 * b < n ∧
    (∃ d ∈ insert b B, ∃ a ∈ A, d + a = n) ∧
    IsPrivateTriple (A \ (B : Set ℕ)) b n ∧
    IsPrivateTriple A b n ∧
    ∃ q ∈ A, b < q ∧ b + q = n ∧
      IsPairSupportTransversal A b {b} ∧
      ∀ z ∈ A, q < z → z + N₀ ≤ n → False

open Classical in
/-- Cofinal non-big absolute destructions stabilize to one of their two exact
size regimes: private doubles, or strict-small zero-atomic exclusion intervals. -/
theorem cofinal_nonbig_absolute_terminal_destructions_split
    {A : Set ℕ} {N₀ : ℕ} {B : Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hcofinal : ∀ X, ∃ b ∈ A, X < b ∧
      HasNonBigAbsoluteTerminalDestruction A N₀ B b) :
    (∀ X, ∃ b ∈ A, X < b ∧
      HasDoubleAbsoluteTerminalDestruction A N₀ B b) ∨
    (∀ X, ∃ b ∈ A, X < b ∧
      HasStrictSmallAbsoluteTerminalDestruction A N₀ B b) := by
  by_cases hdouble : ∀ X, ∃ b ∈ A, X < b ∧
      HasDoubleAbsoluteTerminalDestruction A N₀ B b
  · exact Or.inl hdouble
  · right
    push Not at hdouble
    obtain ⟨X₀, hX₀⟩ := hdouble
    intro X
    obtain ⟨b, hbA, hbLarge, n, hn, hbn, hnonbig,
      hrisk, hrelative, habsolute⟩ :=
      hcofinal (max X X₀)
    have hbX₀ : X₀ < b := by omega
    have hstrict : 2 * b < n := by
      rcases lt_or_eq_of_le hnonbig with hlt | heq
      · exact hlt
      · exfalso
        apply hX₀ b hbA hbX₀
        exact ⟨by omega,
          by simpa [heq] using hrisk,
          by simpa [heq] using hrelative,
          by simpa [heq] using habsolute⟩
    obtain ⟨q, hqA, hbq, hbqsum, hpairSupportTransversal, hdesert⟩ :=
      strict_small_absolute_private_structure
        h0 hcov (by omega) hn habsolute hstrict
    exact ⟨b, hbA, by omega, n, hn, hbn, hstrict,
      hrisk, hrelative, habsolute,
      q, hqA, hbq, hbqsum, hpairSupportTransversal, hdesert⟩

open Classical in

theorem counterexample_double_or_strictSmall_or_fixedPrefixRepairs
    {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ B : Finset ℕ,
      FinitePrefixServesRisks A N₀ B ∧ 0 ∉ B ∧
      ((∀ X, ∃ b ∈ A, X < b ∧
          HasDoubleAbsoluteTerminalDestruction A N₀ B b) ∨
       (∀ X, ∃ b ∈ A, X < b ∧
          HasStrictSmallAbsoluteTerminalDestruction A N₀ B b) ∨
       ∃ w ∈ B, ∀ X, ∃ b ∈ A, X < b ∧
          HasTerminalRepairDestructionThrough A N₀ B w b) := by
  obtain ⟨B, hserved, h0B, hnonbig | hrepair⟩ :=
    counterexample_nonbig_absolute_or_fixed_prefix_repairs h0 hcov hfail
  · rcases cofinal_nonbig_absolute_terminal_destructions_split
      h0 hcov hnonbig with hdouble | hstrict
    · exact ⟨B, hserved, h0B, Or.inl hdouble⟩
    · exact ⟨B, hserved, h0B, Or.inr (Or.inl hstrict)⟩
  · exact ⟨B, hserved, h0B, Or.inr (Or.inr hrepair)⟩

/-- A finite quantitative certificate saying that many targets stall against
one fixed deletion prefix and carry enough surviving low mass to violate the
popular-difference bound at multiplicity threshold `D`. -/
def FixedPrefixStallMassCertificate
    (A : Set ℕ) (N₀ D : ℕ) : Prop := by
  classical
  exact ∃ X L : ℕ, ∃ B S : Finset ℕ,
    B.Nonempty ∧
    (∀ n ∈ S, N₀ ≤ n ∧ n ≤ X ∧ ∀ w ∈ B, w ≤ n) ∧
    (∀ n ∈ S, ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
      x ∉ B → y ∉ B → z ∉ B → x + y + z ≠ n) ∧
    (∀ n ∈ S,
      B.card * L ≤
        ((Finset.range (n - N₀ + 1)).filter
          (fun z => z ∈ A ∧ z ∉ B)).card) ∧
    ∀ t, S.card ≤ B.card * t → t ≤ S.card →
      ((Finset.range (X + 1)).filter (fun x => x ∈ A)).card *
          (t * ((Finset.range (X + 1)).filter
              (fun x => x ∈ A)).card +
            t * t * D) <
        (t * L) ^ 2

theorem stall_mass_quantitative_of_single_inequality
    {s k α L D : ℕ} (hk : 0 < k)
    (hsingle :
      α * (s * α + s * s * D) <
        (((s + k - 1) / k) * L) ^ 2) :
    ∀ t, s ≤ k * t → t ≤ s →
      α * (t * α + t * t * D) < (t * L) ^ 2 := by
  intro t hst hts
  have hceil : (s + k - 1) / k ≤ t := by
    rw [Nat.div_le_iff_le_mul hk]
    have hadd : s + k ≤ k * t + k :=
      Nat.add_le_add_right hst k
    have hsub := Nat.sub_le_sub_right hadd 1
    simpa [Nat.mul_comm] using hsub
  have hlinear : t * α ≤ s * α :=
    Nat.mul_le_mul_right α hts
  have hquadratic : t * t * D ≤ s * s * D :=
    Nat.mul_le_mul_right D (Nat.mul_le_mul hts hts)
  have hinside :
      t * α + t * t * D ≤ s * α + s * s * D :=
    Nat.add_le_add hlinear hquadratic
  have hleft :
      α * (t * α + t * t * D) ≤
        α * (s * α + s * s * D) :=
    Nat.mul_le_mul_left α hinside
  have hbase :
      ((s + k - 1) / k) * L ≤ t * L :=
    Nat.mul_le_mul_right L hceil
  have hright :
      (((s + k - 1) / k) * L) ^ 2 ≤ (t * L) ^ 2 :=
    Nat.pow_le_pow_left hbase 2
  exact hleft.trans_lt (hsingle.trans_le hright)

open Classical in
/-- Build a fixed-prefix stall-mass certificate from one checkable endpoint
inequality rather than a universally quantified condition on the unknown
pigeonhole fiber size. -/
theorem fixedPrefixStallMassCertificate_of_single_inequality
    {A : Set ℕ} {N₀ X L D : ℕ} {B S : Finset ℕ}
    (hB : B.Nonempty)
    (hscale : ∀ n ∈ S, N₀ ≤ n ∧ n ≤ X ∧
      ∀ w ∈ B, w ≤ n)
    (hstall : ∀ n ∈ S, ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
      x ∉ B → y ∉ B → z ∉ B → x + y + z ≠ n)
    (hlow : ∀ n ∈ S,
      B.card * L ≤
        ((Finset.range (n - N₀ + 1)).filter
          (fun z => z ∈ A ∧ z ∉ B)).card)
    (hsingle :
      ((Finset.range (X + 1)).filter (fun x => x ∈ A)).card *
          (S.card * ((Finset.range (X + 1)).filter
              (fun x => x ∈ A)).card +
            S.card * S.card * D) <
        (((S.card + B.card - 1) / B.card) * L) ^ 2) :
    FixedPrefixStallMassCertificate A N₀ D := by
  refine ⟨X, L, B, S, hB, hscale, hstall, hlow, ?_⟩
  exact stall_mass_quantitative_of_single_inequality
    (Finset.card_pos.mpr hB) hsingle

open Classical in

theorem stall_family_mass_amplifier
    {A : Set ℕ} {N₀ X L : ℕ} {B S : Finset ℕ}
    (hcov : PairCovers A N₀) (hB : B.Nonempty)
    (hscale : ∀ n ∈ S, N₀ ≤ n ∧ n ≤ X ∧
      ∀ w ∈ B, w ≤ n)
    (hstall : ∀ n ∈ S, ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
      x ∉ B → y ∉ B → z ∉ B → x + y + z ≠ n)
    (hlow : ∀ n ∈ S,
      B.card * L ≤
        ((Finset.range (n - N₀ + 1)).filter
          (fun z => z ∈ A ∧ z ∉ B)).card) :
    ∃ w ∈ B, ∃ T : Finset ℕ,
      S.card ≤ B.card * T.card ∧ T.card ≤ S.card ∧
      (∀ M ∈ T, M ≤ X) ∧
      T.card * L ≤
        ∑ M ∈ T, ((Finset.range (M + 1)).filter
          (fun z => z ∈ A ∧ (M - z) ∈ A)).card ∧
      (∑ M ∈ T, ((Finset.range (M + 1)).filter
          (fun z => z ∈ A ∧ (M - z) ∈ A)).card) ≤
        T.card *
          ((Finset.range (X + 1)).filter (fun x => x ∈ A)).card := by
  have hBpos : 0 < B.card := Finset.card_pos.mpr hB
  have hpick : ∀ n, ∃ w, n ∈ S →
      w ∈ B ∧
        L ≤ ((Finset.range (n - w + 1)).filter
          (fun x => x ∈ A ∧ (n - w - x) ∈ A)).card := by
    intro n
    by_cases hnS : n ∈ S
    · obtain ⟨w, hwB, hwealth⟩ :=
        stall_forces_wealth hcov hB (hscale n hnS).1
          (hstall n hnS)
      refine ⟨w, fun _ => ⟨hwB, ?_⟩⟩
      apply le_of_mul_le_mul_left
        (le_trans (hlow n hnS) hwealth) hBpos
    · exact ⟨hB.choose, fun h => absurd h hnS⟩
  choose g hg using hpick
  set fib : ℕ → Finset ℕ := fun w =>
    S.filter (fun n => g n = w) with hfib
  have hcover : S ⊆ B.biUnion fib := by
    intro n hnS
    rw [Finset.mem_biUnion]
    exact ⟨g n, (hg n hnS).1,
      Finset.mem_filter.2 ⟨hnS, rfl⟩⟩
  obtain ⟨w, hwB, hwmax⟩ :=
    Finset.exists_max_image B (fun w => (fib w).card) hB
  set R := fib w with hR
  have hScard : S.card ≤ B.card * R.card := by
    have hsum :
        S.card ≤ ∑ v ∈ B, (fib v).card :=
      le_trans (Finset.card_le_card hcover) Finset.card_biUnion_le
    have hmaxsum :
        ∑ v ∈ B, (fib v).card ≤ B.card * (fib w).card := by
      rw [← smul_eq_mul]
      exact Finset.sum_le_card_nsmul _ _ _
        (fun v hv => hwmax v hv)
    rw [hR]
    exact le_trans hsum hmaxsum
  have hRS : R ⊆ S := by
    intro n hnR
    rw [hR, hfib, Finset.mem_filter] at hnR
    exact hnR.1
  have hsubinj :
      (R : Set ℕ).InjOn (fun n => n - w) := by
    intro n hnR m hmR hnm
    have hnS := hRS hnR
    have hmS := hRS hmR
    have hwn := (hscale n hnS).2.2 w hwB
    have hwm := (hscale m hmS).2.2 w hwB
    calc
      n = (n - w) + w := (Nat.sub_add_cancel hwn).symm
      _ = (m - w) + w := congrArg (fun t => t + w) hnm
      _ = m := Nat.sub_add_cancel hwm
  set T := R.image (fun n => n - w) with hT
  have hTcard : T.card = R.card := by
    rw [hT, Finset.card_image_iff.mpr hsubinj]
  have hTle : T.card ≤ S.card := by
    rw [hTcard]
    exact Finset.card_le_card hRS
  have hTX : ∀ M ∈ T, M ≤ X := by
    intro M hMT
    rw [hT, Finset.mem_image] at hMT
    obtain ⟨n, hnR, rfl⟩ := hMT
    exact le_trans (Nat.sub_le n w) (hscale n (hRS hnR)).2.1
  have hwealth : ∀ M ∈ T,
      L ≤ ((Finset.range (M + 1)).filter
        (fun z => z ∈ A ∧ (M - z) ∈ A)).card := by
    intro M hMT
    rw [hT, Finset.mem_image] at hMT
    obtain ⟨n, hnR, rfl⟩ := hMT
    have hnRf := hnR
    rw [hR, hfib, Finset.mem_filter] at hnRf
    have hp := (hg n hnRf.1).2
    rw [hnRf.2] at hp
    exact hp
  have hlower :
      T.card * L ≤
        ∑ M ∈ T, ((Finset.range (M + 1)).filter
          (fun z => z ∈ A ∧ (M - z) ∈ A)).card := by
    calc
      T.card * L = ∑ _M ∈ T, L := by
        simp
      _ ≤ ∑ M ∈ T, ((Finset.range (M + 1)).filter
          (fun z => z ∈ A ∧ (M - z) ∈ A)).card :=
        Finset.sum_le_sum hwealth
  have heachUpper : ∀ M ∈ T,
      ((Finset.range (M + 1)).filter
        (fun z => z ∈ A ∧ (M - z) ∈ A)).card ≤
      ((Finset.range (X + 1)).filter (fun x => x ∈ A)).card := by
    intro M hMT
    apply Finset.card_le_card
    intro z hz
    rw [Finset.mem_filter, Finset.mem_range] at hz
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := hTX M hMT; omega, hz.2.1⟩
  have hupper :
      (∑ M ∈ T, ((Finset.range (M + 1)).filter
          (fun z => z ∈ A ∧ (M - z) ∈ A)).card) ≤
        T.card *
          ((Finset.range (X + 1)).filter (fun x => x ∈ A)).card := by
    rw [← smul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ heachUpper
  refine ⟨w, hwB, T, ?_, hTle, hTX, hlower, hupper⟩
  rw [hTcard]
  exact hScard

open Classical in

theorem wealthy_set_symm {A : Set ℕ} {M x : ℕ}
    (hx : x ∈ (Finset.range (M + 1)).filter
      (fun z => z ∈ A ∧ (M - z) ∈ A)) :
    (M - x) ∈ (Finset.range (M + 1)).filter
      (fun z => z ∈ A ∧ (M - z) ∈ A) := by
  rw [Finset.mem_filter, Finset.mem_range] at hx
  obtain ⟨hxM, hxA, hMxA⟩ := hx
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨by omega, hMxA, ?_⟩
  have he : M - (M - x) = x := by omega
  rw [he]
  exact hxA

open Classical in

theorem two_symmetries_translate {A : Set ℕ} {M₁ M₂ : ℕ}
    (h12 : M₁ ≤ M₂) :
    (((Finset.range (M₁ + 1)).filter
        (fun z => z ∈ A ∧ (M₁ - z) ∈ A)) ∩
      ((Finset.range (M₂ + 1)).filter
        (fun z => z ∈ A ∧ (M₂ - z) ∈ A))).card ≤
    ((Finset.range (M₁ + 1)).filter
      (fun y => y ∈ A ∧ (y + (M₂ - M₁)) ∈ A)).card := by
  apply Finset.card_le_card_of_injOn (fun x => M₁ - x)
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_inter, Finset.mem_filter,
      Finset.mem_range] at hx
    obtain ⟨⟨hx1, hxA, hM1x⟩, ⟨hx2, -, hM2x⟩⟩ := hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, hM1x, ?_⟩
    have he : M₁ - x + (M₂ - M₁) = M₂ - x := by omega
    rw [he]
    exact hM2x
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_inter, Finset.mem_filter,
      Finset.mem_range] at ha hb
    have hab' : M₁ - a = M₁ - b := hab
    omega

open Classical in

theorem sum_pairwise_inter_lower {U T : Finset ℕ}
    {S : ℕ → Finset ℕ} (hsub : ∀ M ∈ T, S M ⊆ U) :
    (∑ M ∈ T, (S M).card) ^ 2 ≤
    U.card * ∑ M₁ ∈ T, ∑ M₂ ∈ T, ((S M₁) ∩ (S M₂)).card := by
  have hrestrict : ∀ M ∈ T, S M = U.filter (fun x => x ∈ S M) := by
    intro M hM
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨hsub M hM h, h⟩, fun h => h.2⟩
  have h1 : ∑ M ∈ T, (S M).card =
      ∑ x ∈ U, (T.filter (fun M => x ∈ S M)).card := by
    calc ∑ M ∈ T, (S M).card
        = ∑ M ∈ T, ∑ x ∈ U, (if x ∈ S M then 1 else 0) := by
          refine Finset.sum_congr rfl (fun M hM => ?_)
          conv_lhs => rw [hrestrict M hM]
          rw [Finset.card_filter]
      _ = ∑ x ∈ U, ∑ M ∈ T, (if x ∈ S M then 1 else 0) :=
          Finset.sum_comm
      _ = ∑ x ∈ U, (T.filter (fun M => x ∈ S M)).card := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [Finset.card_filter]
  have hinter : ∀ M₁ ∈ T, ∀ M₂ ∈ T,
      ((S M₁) ∩ (S M₂)).card =
      ∑ x ∈ U, (if x ∈ S M₁ then 1 else 0) *
        (if x ∈ S M₂ then 1 else 0) := by
    intro M₁ h₁ M₂ _
    have he : (S M₁) ∩ (S M₂) =
        U.filter (fun x => x ∈ S M₁ ∧ x ∈ S M₂) := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_filter]
      exact ⟨fun h => ⟨hsub M₁ h₁ h.1, h⟩, fun h => h.2⟩
    rw [he, Finset.card_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx1 : x ∈ S M₁ <;> by_cases hx2 : x ∈ S M₂ <;>
      simp [hx1, hx2]
  have h2 : ∑ M₁ ∈ T, ∑ M₂ ∈ T, ((S M₁) ∩ (S M₂)).card =
      ∑ x ∈ U, ((T.filter (fun M => x ∈ S M)).card) ^ 2 := by
    calc ∑ M₁ ∈ T, ∑ M₂ ∈ T, ((S M₁) ∩ (S M₂)).card
        = ∑ M₁ ∈ T, ∑ M₂ ∈ T, ∑ x ∈ U,
            (if x ∈ S M₁ then 1 else 0) *
            (if x ∈ S M₂ then 1 else 0) := by
          refine Finset.sum_congr rfl (fun M₁ h₁ => ?_)
          exact Finset.sum_congr rfl (fun M₂ h₂ => hinter M₁ h₁ M₂ h₂)
      _ = ∑ M₁ ∈ T, ∑ x ∈ U, ∑ M₂ ∈ T,
            (if x ∈ S M₁ then 1 else 0) *
            (if x ∈ S M₂ then 1 else 0) := by
          refine Finset.sum_congr rfl (fun M₁ _ => ?_)
          exact Finset.sum_comm
      _ = ∑ x ∈ U, ∑ M₁ ∈ T, ∑ M₂ ∈ T,
            (if x ∈ S M₁ then 1 else 0) *
            (if x ∈ S M₂ then 1 else 0) := Finset.sum_comm
      _ = ∑ x ∈ U, ((T.filter (fun M => x ∈ S M)).card) ^ 2 := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [← Finset.sum_mul_sum, Finset.card_filter, sq]
  rw [h1, h2]
  exact sq_sum_le_card_mul_sum_sq

open Classical in

theorem popular_difference_bound {A : Set ℕ} {X D : ℕ}
    {T : Finset ℕ} (hTX : ∀ M ∈ T, M ≤ X)
    (hD : ∀ d, 0 < d → d ≤ X →
      ((Finset.range (X + 1)).filter
        (fun y => y ∈ A ∧ (y + d) ∈ A)).card ≤ D) :
    (∑ M ∈ T, ((Finset.range (M + 1)).filter
        (fun z => z ∈ A ∧ (M - z) ∈ A)).card) ^ 2 ≤
    ((Finset.range (X + 1)).filter (fun x => x ∈ A)).card *
      ((∑ M ∈ T, ((Finset.range (M + 1)).filter
        (fun z => z ∈ A ∧ (M - z) ∈ A)).card) +
        T.card * T.card * D) := by
  set U := (Finset.range (X + 1)).filter (fun x => x ∈ A) with hU
  set S : ℕ → Finset ℕ := fun M => (Finset.range (M + 1)).filter
    (fun z => z ∈ A ∧ (M - z) ∈ A) with hS
  have hsub : ∀ M ∈ T, S M ⊆ U := by
    intro M hM z hz
    rw [hS, Finset.mem_filter, Finset.mem_range] at hz
    rw [hU, Finset.mem_filter, Finset.mem_range]
    have := hTX M hM
    exact ⟨by omega, hz.2.1⟩
  have hoff : ∀ M₁ ∈ T, ∀ M₂ ∈ T, M₁ ≠ M₂ →
      ((S M₁) ∩ (S M₂)).card ≤ D := by
    intro M₁ h₁ M₂ h₂ hne
    have key : ∀ N₁ N₂, N₁ ∈ T → N₂ ∈ T → N₁ < N₂ →
        ((S N₁) ∩ (S N₂)).card ≤ D := by
      intro N₁ N₂ hN₁ hN₂ hlt
      refine le_trans (two_symmetries_translate (A := A) hlt.le) ?_
      refine le_trans (Finset.card_le_card ?_)
        (hD (N₂ - N₁) (by omega) (by
          have := hTX N₂ hN₂
          omega))
      intro y hy
      rw [Finset.mem_filter, Finset.mem_range] at hy
      rw [Finset.mem_filter, Finset.mem_range]
      have := hTX N₁ hN₁
      exact ⟨by omega, hy.2⟩
    rcases Nat.lt_or_ge M₁ M₂ with h | h
    · exact key M₁ M₂ h₁ h₂ (by omega)
    · rw [Finset.inter_comm]
      exact key M₂ M₁ h₂ h₁ (by omega)
  have hrow : ∀ M₁ ∈ T, ∑ M₂ ∈ T, ((S M₁) ∩ (S M₂)).card ≤
      (S M₁).card + T.card * D := by
    intro M₁ h₁
    rw [← Finset.add_sum_erase T _ h₁, Finset.inter_self]
    have hsum : ∑ M₂ ∈ T.erase M₁, ((S M₁) ∩ (S M₂)).card ≤
        (T.erase M₁).card * D := by
      rw [← smul_eq_mul]
      refine Finset.sum_le_card_nsmul _ _ _ (fun M₂ hM₂ => ?_)
      exact hoff M₁ h₁ M₂ (Finset.mem_of_mem_erase hM₂)
        (Ne.symm (Finset.ne_of_mem_erase hM₂))
    have hcard : (T.erase M₁).card ≤ T.card :=
      Finset.card_le_card (Finset.erase_subset _ _)
    have : (T.erase M₁).card * D ≤ T.card * D :=
      Nat.mul_le_mul_right _ hcard
    omega
  have htot : ∑ M₁ ∈ T, ∑ M₂ ∈ T, ((S M₁) ∩ (S M₂)).card ≤
      (∑ M ∈ T, (S M).card) + T.card * T.card * D := by
    have h1 : ∑ M₁ ∈ T, ∑ M₂ ∈ T, ((S M₁) ∩ (S M₂)).card ≤
        ∑ M₁ ∈ T, ((S M₁).card + T.card * D) :=
      Finset.sum_le_sum (fun M₁ h₁ => hrow M₁ h₁)
    have h2 : ∑ M₁ ∈ T, ((S M₁).card + T.card * D) =
        (∑ M ∈ T, (S M).card) + T.card * (T.card * D) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
    have h3 : T.card * (T.card * D) = T.card * T.card * D := by
      ring
    omega
  have hcs := sum_pairwise_inter_lower (U := U) (T := T) (S := S) hsub
  have hmul : U.card * ∑ M₁ ∈ T, ∑ M₂ ∈ T,
      ((S M₁) ∩ (S M₂)).card ≤
      U.card * ((∑ M ∈ T, (S M).card) + T.card * T.card * D) :=
    Nat.mul_le_mul_left _ htot
  show (∑ M ∈ T, (S M).card) ^ 2 ≤
    U.card * ((∑ M ∈ T, (S M).card) + T.card * T.card * D)
  exact le_trans hcs hmul

open Classical in

theorem exists_popular_positive_difference {A : Set ℕ} {X D : ℕ}
    {T : Finset ℕ} (hTX : ∀ M ∈ T, M ≤ X)
    (hmass :
      ((Finset.range (X + 1)).filter (fun x => x ∈ A)).card *
        ((∑ M ∈ T, ((Finset.range (M + 1)).filter
          (fun z => z ∈ A ∧ (M - z) ∈ A)).card) +
          T.card * T.card * D) <
      (∑ M ∈ T, ((Finset.range (M + 1)).filter
        (fun z => z ∈ A ∧ (M - z) ∈ A)).card) ^ 2) :
    ∃ d, 0 < d ∧ d ≤ X ∧ D <
      ((Finset.range (X + 1)).filter
        (fun y => y ∈ A ∧ (y + d) ∈ A)).card := by
  by_contra hno
  push Not at hno
  have hD : ∀ d, 0 < d → d ≤ X →
      ((Finset.range (X + 1)).filter
        (fun y => y ∈ A ∧ (y + d) ∈ A)).card ≤ D := by
    intro d hd hdX
    exact hno d hd hdX
  exact (not_le_of_gt hmass) (popular_difference_bound hTX hD)

open Classical in

theorem wealthy_targets_force_popular_difference_of_endpoint
    {A : Set ℕ} {X D L R S : ℕ} {T : Finset ℕ}
    (hTX : ∀ M ∈ T, M ≤ X)
    (hlarge : R < T.card) (hupperCard : T.card ≤ S)
    (hwealth : ∀ M ∈ T,
      L ≤ ((Finset.range (M + 1)).filter
        (fun z => z ∈ A ∧ (M - z) ∈ A)).card)
    (hendpoint :
      ((Finset.range (X + 1)).filter (fun x => x ∈ A)).card *
        (S * ((Finset.range (X + 1)).filter
            (fun x => x ∈ A)).card +
          S * S * D) <
      ((R + 1) * L) ^ 2) :
    ∃ d, 0 < d ∧ d ≤ X ∧ D <
      ((Finset.range (X + 1)).filter
        (fun y => y ∈ A ∧ (y + d) ∈ A)).card := by
  let α := ((Finset.range (X + 1)).filter
    (fun x => x ∈ A)).card
  let mass := ∑ M ∈ T, ((Finset.range (M + 1)).filter
    (fun z => z ∈ A ∧ (M - z) ∈ A)).card
  have hmassLower : T.card * L ≤ mass := by
    calc
      T.card * L = ∑ _M ∈ T, L := by simp
      _ ≤ mass := Finset.sum_le_sum hwealth
  have heachUpper : ∀ M ∈ T,
      ((Finset.range (M + 1)).filter
        (fun z => z ∈ A ∧ (M - z) ∈ A)).card ≤ α := by
    intro M hMT
    apply Finset.card_le_card
    intro z hz
    rw [Finset.mem_filter, Finset.mem_range] at hz
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by
      have := hTX M hMT
      omega, hz.2.1⟩
  have hmassUpper : mass ≤ T.card * α := by
    calc
      mass ≤ ∑ _M ∈ T, α := Finset.sum_le_sum heachUpper
      _ = T.card * α := by simp
  have hlinear : T.card * α ≤ S * α :=
    Nat.mul_le_mul_right α hupperCard
  have hquadratic : T.card * T.card * D ≤ S * S * D :=
    Nat.mul_le_mul_right D
      (Nat.mul_le_mul hupperCard hupperCard)
  have hinside :
      mass + T.card * T.card * D ≤ S * α + S * S * D :=
    Nat.add_le_add (hmassUpper.trans hlinear) hquadratic
  have hleft :
      α * (mass + T.card * T.card * D) ≤
        α * (S * α + S * S * D) :=
    Nat.mul_le_mul_left α hinside
  have hbase : (R + 1) * L ≤ T.card * L :=
    Nat.mul_le_mul_right L hlarge
  have hright :
      ((R + 1) * L) ^ 2 ≤ mass ^ 2 :=
    (Nat.pow_le_pow_left hbase 2).trans
      (Nat.pow_le_pow_left hmassLower 2)
  have hmass :
      α * (mass + T.card * T.card * D) < mass ^ 2 :=
    hleft.trans_lt (hendpoint.trans_le hright)
  exact exists_popular_positive_difference hTX hmass

open Classical in

theorem moving_prefix_risks_popular_or_affine_or_fixed_stall
    {A : Set ℕ} {N₀ X D R L : ℕ}
    {B C : Finset ℕ} {n : ℕ → ℕ}
    (hcov : PairCovers A N₀)
    (hscale : ∀ b ∈ C, N₀ ≤ n b)
    (hcap : ∀ b ∈ C, n b ≤ X)
    (hcandidate : ∀ b ∈ C, b ∈ A)
    (hrisk : ∀ b ∈ C, ∃ a ∈ A, b + a = n b)
    (hordered : ∀ b ∈ C, ∀ w ∈ B, w ≤ b)
    (hstall : ∀ b ∈ C, ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
      x ∉ insert b B → y ∉ insert b B → z ∉ insert b B →
        x + y + z ≠ n b)
    (hlow : ∀ b ∈ C,
      (insert b B).card * L ≤
        ((Finset.range (n b - N₀ + 1)).filter
          (fun z => z ∈ A ∧ z ∉ insert b B)).card)
    (hmany : (B.card + 1) * (3 * R) < C.card)
    (hendpoint :
      ((Finset.range (X + 1)).filter (fun x => x ∈ A)).card *
        (C.card * ((Finset.range (X + 1)).filter
            (fun x => x ∈ A)).card +
          C.card * C.card * D) <
      ((R + 1) * L) ^ 2) :
    (∃ d, 0 < d ∧ d ≤ X ∧ D <
      ((Finset.range (X + 1)).filter
        (fun y => y ∈ A ∧ (y + d) ∈ A)).card) ∨
    (∃ a ∈ A, ∃ F : Finset ℕ, F ⊆ C ∧ 3 < F.card ∧
      (∀ b ∈ F, b ∈ A ∧ n b = b + a) ∧
      L ≤ ((Finset.range (a + 1)).filter
        (fun x => x ∈ A ∧ (a - x) ∈ A)).card ∧
      (a ∈ B ∨ ∃ G : Finset ℕ, G ⊆ F ∧ 2 < G.card ∧
        ∀ b ∈ G, IsPairSupportTransversal A b (insert b B))) ∨
    (∃ m, N₀ ≤ m ∧ (∀ w ∈ B, w ≤ m) ∧
      (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
        x ∉ B → y ∉ B → z ∉ B → x + y + z ≠ m) ∧
      B.card * L ≤
        ((Finset.range (m - N₀ + 1)).filter
          (fun z => z ∈ A ∧ z ∉ B)).card) := by
  rcases moving_prefix_risks_distinct_or_affine_or_fixed_stall
      hcov hscale hcandidate hrisk hordered hstall hlow hmany with
    ⟨T, hTlarge, hTcard, hTwealth⟩ | hAffine | hFixed
  · left
    have hTX : ∀ M ∈ T, M ≤ X := by
      intro M hMT
      obtain ⟨⟨b, hbC, hMnb⟩, hwealth⟩ := hTwealth M hMT
      exact hMnb.trans (hcap b hbC)
    exact wealthy_targets_force_popular_difference_of_endpoint
      hTX hTlarge hTcard (fun M hMT => (hTwealth M hMT).2)
        hendpoint
  · exact Or.inr (Or.inl hAffine)
  · exact Or.inr (Or.inr hFixed)

open Classical in

theorem stall_family_forces_popular_difference
    {A : Set ℕ} {N₀ X L D : ℕ} {B S : Finset ℕ}
    (hcov : PairCovers A N₀) (hB : B.Nonempty)
    (hscale : ∀ n ∈ S, N₀ ≤ n ∧ n ≤ X ∧
      ∀ w ∈ B, w ≤ n)
    (hstall : ∀ n ∈ S, ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
      x ∉ B → y ∉ B → z ∉ B → x + y + z ≠ n)
    (hlow : ∀ n ∈ S,
      B.card * L ≤
        ((Finset.range (n - N₀ + 1)).filter
          (fun z => z ∈ A ∧ z ∉ B)).card)
    (hquant : ∀ t, S.card ≤ B.card * t → t ≤ S.card →
      ((Finset.range (X + 1)).filter (fun x => x ∈ A)).card *
          (t * ((Finset.range (X + 1)).filter
              (fun x => x ∈ A)).card +
            t * t * D) <
        (t * L) ^ 2) :
    ∃ d, 0 < d ∧ d ≤ X ∧ D <
      ((Finset.range (X + 1)).filter
        (fun y => y ∈ A ∧ y + d ∈ A)).card := by
  obtain ⟨w, hwB, T, hST, hTS, hTX, hlower, hupper⟩ :=
    stall_family_mass_amplifier hcov hB hscale hstall hlow
  let α := ((Finset.range (X + 1)).filter
    (fun x => x ∈ A)).card
  let mass := ∑ M ∈ T, ((Finset.range (M + 1)).filter
    (fun z => z ∈ A ∧ (M - z) ∈ A)).card
  have hnum :
      α * (T.card * α + T.card * T.card * D) <
        (T.card * L) ^ 2 := by
    exact hquant T.card hST hTS
  have hinside :
      mass + T.card * T.card * D ≤
        T.card * α + T.card * T.card * D := by
    exact Nat.add_le_add_right hupper _
  have hleft :
      α * (mass + T.card * T.card * D) ≤
        α * (T.card * α + T.card * T.card * D) :=
    Nat.mul_le_mul_left _ hinside
  have hright : (T.card * L) ^ 2 ≤ mass ^ 2 :=
    Nat.pow_le_pow_left hlower 2
  have hmass :
      α * (mass + T.card * T.card * D) < mass ^ 2 :=
    lt_of_le_of_lt hleft (lt_of_lt_of_le hnum hright)
  exact exists_popular_positive_difference hTX hmass

open Classical in
/-- A fixed-prefix stall-mass certificate produces the advertised positive
popular difference. -/
theorem FixedPrefixStallMassCertificate.exists_popular_difference
    {A : Set ℕ} {N₀ D : ℕ}
    (hcov : PairCovers A N₀)
    (hcert : FixedPrefixStallMassCertificate A N₀ D) :
    ∃ X d, 0 < d ∧ d ≤ X ∧ D <
      ((Finset.range (X + 1)).filter
        (fun y => y ∈ A ∧ y + d ∈ A)).card := by
  obtain ⟨X, L, B, S, hB, hscale, hstall, hlow, hquant⟩ := hcert
  obtain ⟨d, hd, hdX, hmany⟩ :=
    stall_family_forces_popular_difference
      hcov hB hscale hstall hlow hquant
  exact ⟨X, d, hd, hdX, hmany⟩

open Classical in

theorem stall_mass_certificates_fixed_offset_or_growing
    {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hsupply : ∀ K, FixedPrefixStallMassCertificate A N₀ K) :
    (∃ δ, 1 ≤ δ ∧ ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A) ∨
    (∀ Δ K, ∃ δ, Δ < δ ∧ ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A) := by
  apply fixed_offset_or_growing
  intro K
  obtain ⟨X, δ, hδ, hδX, hcard⟩ :=
    (hsupply K).exists_popular_difference hcov
  let V := (Finset.range (X + 1)).filter
    (fun x => x ∈ A ∧ x + δ ∈ A)
  refine ⟨δ, hδ, V, by dsimp [V]; omega, ?_⟩
  intro x hx
  exact (Finset.mem_filter.1 hx).2

open Classical in
/-- More than `K + 2|F|` starts from one equal-difference family leave more
than `K` starts whose two endpoints avoid `F`.  This is the quantitative
finite-obstruction form of `many_difference_pairs_avoid_finset`, stated for an
arbitrary supplied family rather than an initial interval. -/
theorem difference_pair_family_many_fresh
    {A : Set ℕ} {d K : ℕ} {V : Finset ℕ} (F : Finset ℕ)
    (hV : ∀ x ∈ V, x ∈ A ∧ x + d ∈ A)
    (hmany : K + 2 * F.card < V.card) :
    ∃ W : Finset ℕ, W ⊆ V ∧ K < W.card ∧
      ∀ x ∈ W, x ∈ A ∧ x + d ∈ A ∧ x ∉ F ∧ x + d ∉ F := by
  let fresh : ℕ → Prop := fun x => x ∉ F ∧ x + d ∉ F
  set W := V.filter fresh with hW
  set Bad := V.filter (fun x => ¬fresh x) with hBad
  let f : ℕ → Sum ℕ ℕ := fun x =>
    if x ∈ F then Sum.inl x else Sum.inr (x + d)
  have hmaps : Set.MapsTo f (Bad : Set ℕ)
      (F.disjSum F : Set (Sum ℕ ℕ)) := by
    intro x hxBad
    have hxBadFin : x ∈ Bad := hxBad
    rw [hBad, Finset.mem_filter] at hxBadFin
    by_cases hxF : x ∈ F
    · simp [f, hxF]
    · have hxdF : x + d ∈ F := by
        by_contra hxdF
        exact hxBadFin.2 ⟨hxF, hxdF⟩
      simp [f, hxF, hxdF]
  have hinj : (Bad : Set ℕ).InjOn f := by
    intro x hx y hy hxy
    by_cases hxF : x ∈ F
    · by_cases hyF : y ∈ F
      · simpa [f, hxF, hyF] using hxy
      · simp [f, hxF, hyF] at hxy
    · by_cases hyF : y ∈ F
      · simp [f, hxF, hyF] at hxy
      · have hadd : x + d = y + d := by
          simpa [f, hxF, hyF] using hxy
        exact Nat.add_right_cancel hadd
  have hBadcard : Bad.card ≤ 2 * F.card := by
    have hcard :
        Bad.card ≤ (F.disjSum F).card :=
      Finset.card_le_card_of_injOn f hmaps hinj
    rw [Finset.card_disjSum] at hcard
    omega
  have hpartition : W.card + Bad.card = V.card := by
    rw [hW, hBad]
    exact Finset.card_filter_add_card_filter_not fresh
  refine ⟨W, ?_, by omega, ?_⟩
  · intro x hx
    exact (Finset.mem_filter.1 hx).1
  · intro x hx
    have hx' := Finset.mem_filter.1 hx
    exact ⟨(hV x hx'.1).1, (hV x hx'.1).2,
      hx'.2.1, hx'.2.2⟩

open Classical in

theorem many_difference_pairs_avoid_finset
    {A : Set ℕ} {X d : ℕ} (F : Finset ℕ)
    (hmany : 2 * F.card <
      ((Finset.range (X + 1)).filter
        (fun y => y ∈ A ∧ y + d ∈ A)).card) :
    ∃ y, y ≤ X ∧ y ∈ A ∧ y + d ∈ A ∧ y ∉ F ∧ y + d ∉ F := by
  set P := (Finset.range (X + 1)).filter
    (fun y => y ∈ A ∧ y + d ∈ A) with hP
  by_contra hno
  push Not at hno
  have hbad : ∀ y ∈ P, y ∈ F ∨ y + d ∈ F := by
    intro y hy
    rw [hP, Finset.mem_filter, Finset.mem_range] at hy
    by_cases hyF : y ∈ F
    · exact Or.inl hyF
    · exact Or.inr (hno y (by omega) hy.2.1 hy.2.2 hyF)
  let f : ℕ → Sum ℕ ℕ := fun y =>
    if y ∈ F then Sum.inl y else Sum.inr (y + d)
  have hmaps : Set.MapsTo f (P : Set ℕ)
      (F.disjSum F : Set (Sum ℕ ℕ)) := by
    intro y hy
    by_cases hyF : y ∈ F
    · simp [f, hyF]
    · have hydF : y + d ∈ F := (hbad y hy).resolve_left hyF
      simp [f, hyF, hydF]
  have hinj : (P : Set ℕ).InjOn f := by
    intro x hx y hy hxy
    by_cases hxF : x ∈ F
    · by_cases hyF : y ∈ F
      · simpa [f, hxF, hyF] using hxy
      · simp [f, hxF, hyF] at hxy
    · by_cases hyF : y ∈ F
      · simp [f, hxF, hyF] at hxy
      · have hadd : x + d = y + d := by
          simpa [f, hxF, hyF] using hxy
        exact Nat.add_right_cancel hadd
  have hcard :
      P.card ≤ (F.disjSum F).card :=
    Finset.card_le_card_of_injOn f hmaps hinj
  rw [Finset.card_disjSum] at hcard
  omega

open Classical in

theorem large_mem_or_splits {A : Set ℕ} {N₀ d : ℕ}
    (hcov : PairCovers A N₀) (hd : N₀ ≤ d) :
    d ∈ A ∨ ∃ u ∈ A, ∃ v ∈ A, 0 < u ∧ 0 < v ∧ u + v = d := by
  obtain ⟨u, huA, v, hvA, huv⟩ := hcov d hd
  rcases Nat.eq_zero_or_pos u with hu0 | hu0
  · left
    have he : v = d := by omega
    rw [← he]
    exact hvA
  · rcases Nat.eq_zero_or_pos v with hv0 | hv0
    · left
      have he : u = d := by omega
      rw [← he]
      exact huA
    · exact Or.inr ⟨u, huA, v, hvA, hu0, hv0, huv⟩

open Classical in

theorem difference_reaches_element {A : Set ℕ} {N₀ d y : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hd : N₀ ≤ d) (hd0 : 0 < d) (hy0 : 0 < y)
    (hyA : y ∈ A) (_hydA : y + d ∈ A) :
    ∃ p ∈ A, ∃ q ∈ A, ∃ r ∈ A,
      p + q + r = y + d ∧ p < y + d ∧ q < y + d ∧ r < y + d := by
  rcases large_mem_or_splits hcov hd with hdA | ⟨u, huA, v, hvA,
    hu0, hv0, huv⟩
  · exact ⟨y, hyA, d, hdA, 0, h0, by omega, by omega, by omega,
      by omega⟩
  · exact ⟨y, hyA, u, huA, v, hvA, by omega, by omega, by omega,
      by omega⟩

open Classical in

theorem growing_differences_composable_or_missing_rectangles
    {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hgrowing : ∀ Δ K, ∃ d, Δ < d ∧ ∃ V : Finset ℕ,
      K ≤ V.card ∧ ∀ x ∈ V, x ∈ A ∧ x + d ∈ A) :
    ∀ (F : Finset ℕ) (Δ K : ℕ), ∃ d, Δ < d ∧
      ((d ∈ A ∧ ∃ V : Finset ℕ, K < V.card ∧
          ∀ x ∈ V, x ∈ A ∧ x + d ∈ A ∧
            x ∉ F ∧ x + d ∉ F) ∨
       ∃ u ∈ A, ∃ v ∈ A,
          0 < u ∧ 0 < v ∧ u + v = d ∧
          ((∃ x, x ∈ A ∧ x + d ∈ A ∧
              x ∉ F ∧ x + d ∉ F ∧
              (x + u ∈ A ∨ x + v ∈ A)) ∨
           ∃ V : Finset ℕ, K < V.card ∧
              ∀ x ∈ V, x ∈ A ∧ x + d ∈ A ∧
                x ∉ F ∧ x + d ∉ F ∧
                x + u ∉ A ∧ x + v ∉ A)) := by
  intro F Δ K
  obtain ⟨d, hdlarge, V, hVcard, hV⟩ :=
    hgrowing (max Δ N₀) (K + 2 * F.card + 1)
  have hdΔ : Δ < d := lt_of_le_of_lt (le_max_left _ _) hdlarge
  have hdN : N₀ ≤ d :=
    le_trans (le_max_right Δ N₀) (le_of_lt hdlarge)
  have hmany : K + 2 * F.card < V.card := by omega
  obtain ⟨W, hWV, hWK, hW⟩ :=
    difference_pair_family_many_fresh F hV hmany
  refine ⟨d, hdΔ, ?_⟩
  rcases large_mem_or_splits hcov hdN with hdA |
      ⟨u, huA, v, hvA, hu0, hv0, huv⟩
  · left
    exact ⟨hdA, W, hWK, hW⟩
  · right
    refine ⟨u, huA, v, hvA, hu0, hv0, huv, ?_⟩
    by_cases hcomp : ∃ x ∈ W, x + u ∈ A ∨ x + v ∈ A
    · left
      obtain ⟨x, hxW, hxcomp⟩ := hcomp
      obtain ⟨hxA, hxdA, hxF, hxdF⟩ := hW x hxW
      exact ⟨x, hxA, hxdA, hxF, hxdF, hxcomp⟩
    · right
      push Not at hcomp
      refine ⟨W, hWK, fun x hxW => ?_⟩
      obtain ⟨hxA, hxdA, hxF, hxdF⟩ := hW x hxW
      have hxmid := hcomp x hxW
      exact ⟨hxA, hxdA, hxF, hxdF, hxmid.1, hxmid.2⟩

/-! ## Fixed-difference composition through a shifted slice -/

/-- Every translate `a + δ`, for `a ∈ A`, has a surviving pair after
deleting `B`.  This is the precise order-two slice needed to compose a
`δ`-edge with every target threatened by its upper endpoint. -/
def ShiftedPairSurvives
    (A B : Set ℕ) (δ : ℕ) : Prop :=
  ∀ a ∈ A, ∃ p ∈ A, ∃ q ∈ A,
    p ∉ B ∧ q ∉ B ∧ p + q = a + δ

theorem fixed_difference_deletion_of_shiftedPairSurvival
    {A B : Set ℕ} {N₀ δ : ℕ}
    (h0 : 0 ∈ A) (h0B : 0 ∉ B) (hcov : PairCovers A N₀)
    (hpred : ∀ b ∈ B, ∃ x ∈ A, x ∉ B ∧ x + δ = b)
    (hshift : ShiftedPairSurvives A B δ) :
    IsExactTupleAsymptoticBasis (A \ B) 3 := by
  apply deletion_criterion_local h0 h0B hcov
  intro n _hn
  rintro ⟨b, hbB, a, haA, hba⟩
  obtain ⟨x, hxA, hxB, hxδ⟩ := hpred b hbB
  obtain ⟨p, hpA, q, hqA, hpB, hqB, hpq⟩ := hshift a haA
  exact ⟨x, hxA, p, hpA, q, hqA, hxB, hpB, hqB, by omega⟩

open Classical in
/-- Cofinal `δ`-pairs contain an infinite separated matching.  Deleting the
upper endpoints leaves every selected lower endpoint outside the deletion,
so each deleted element has a surviving `δ`-predecessor. -/
theorem fixed_difference_predecessor_deletion
    {A : Set ℕ} {δ : ℕ} (hδ : 0 < δ)
    (hsupply : ∀ N, ∃ x, N ≤ x ∧ x ∈ A ∧ x + δ ∈ A) :
    ∃ B : Set ℕ, B ⊆ A ∧ B.Infinite ∧ 0 ∉ B ∧
      ∀ b ∈ B, ∃ x ∈ A, x ∉ B ∧ x + δ = b := by
  have hnext : ∀ N, ∃ x, N < x ∧ x ∈ A ∧ x + δ ∈ A := by
    intro N
    obtain ⟨x, hxN, hxA, hxδA⟩ := hsupply (N + 1)
    exact ⟨x, by omega, hxA, hxδA⟩
  choose nx hnx hnxA hnxδA using hnext
  set x : ℕ → ℕ :=
    fun k => Nat.rec (nx 0) (fun _ prev => nx (prev + δ)) k
    with hx
  have hx0 : x 0 = nx 0 := rfl
  have hxs : ∀ k, x (k + 1) = nx (x k + δ) := fun _ => rfl
  have hsep : ∀ k, x k + δ < x (k + 1) := by
    intro k
    rw [hxs]
    exact hnx _
  have hxmono : StrictMono x := by
    apply strictMono_nat_of_lt_succ
    intro k
    have := hsep k
    omega
  have hxA : ∀ k, x k ∈ A := by
    intro k
    cases k with
    | zero =>
        rw [hx0]
        exact hnxA _
    | succ k =>
        rw [hxs]
        exact hnxA _
  have hxδA : ∀ k, x k + δ ∈ A := by
    intro k
    cases k with
    | zero =>
        rw [hx0]
        exact hnxδA _
    | succ k =>
        rw [hxs]
        exact hnxδA _
  let b : ℕ → ℕ := fun k => x k + δ
  have hbmono : StrictMono b := by
    intro i j hij
    dsimp [b]
    exact Nat.add_lt_add_right (hxmono hij) δ
  have hlower_notMem : ∀ k, x k ∉ Set.range b := by
    intro k
    rintro ⟨j, hj⟩
    dsimp [b] at hj
    rcases Nat.lt_trichotomy j k with hjk | hjk | hjk
    · have hj1k : j + 1 ≤ k := by omega
      have hle : x (j + 1) ≤ x k := hxmono.monotone hj1k
      have := hsep j
      omega
    · subst j
      omega
    · have := hxmono hjk
      omega
  refine ⟨Set.range b, ?_, Set.infinite_range_of_injective
    hbmono.injective, ?_, ?_⟩
  · rintro _ ⟨k, rfl⟩
    exact hxδA k
  · rintro ⟨k, hk⟩
    dsimp [b] at hk
    have := hδ
    omega
  · rintro _ ⟨k, rfl⟩
    exact ⟨x k, hxA k, hlower_notMem k, rfl⟩

theorem fixed_difference_forces_shifted_slice_obstruction
    {A : Set ℕ} {N₀ δ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hδ : 0 < δ)
    (hsupply : ∀ N, ∃ x, N ≤ x ∧ x ∈ A ∧ x + δ ∈ A) :
    ∃ B : Set ℕ, B ⊆ A ∧ B.Infinite ∧ 0 ∉ B ∧
      (∀ b ∈ B, ∃ x ∈ A, x ∉ B ∧ x + δ = b) ∧
      ∃ a ∈ A, ∀ p ∈ A, ∀ q ∈ A, p + q = a + δ →
        p ∈ B ∨ q ∈ B := by
  obtain ⟨B, hBA, hBinf, h0B, hpred⟩ :=
    fixed_difference_predecessor_deletion hδ hsupply
  refine ⟨B, hBA, hBinf, h0B, hpred, ?_⟩
  by_contra hno
  push Not at hno
  have hshift : ShiftedPairSurvives A B δ := by
    intro a haA
    obtain ⟨p, hpA, q, hqA, hpq, hpB, hqB⟩ := hno a haA
    exact ⟨p, hpA, q, hqA, hpB, hqB, hpq⟩
  exact hfail B hBA hBinf
    (fixed_difference_deletion_of_shiftedPairSurvival
      h0 h0B hcov hpred hshift)

open Classical in

theorem counterexample_pairSplittable_reservoir_finite
    {A K : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hKA : K ⊆ A) (h0K : 0 ∉ K)
    (hsplittable : ∀ b ∈ K, PairSplittableAwayFromSelf A b) :
    K.Finite := by
  apply Set.not_infinite.mp
  intro hKinf
  obtain ⟨B₀, hB₀K, hB₀inf, hsplit⟩ :=
    exists_infiniteDeletion_splittingDeletedPoints
      hKinf hsplittable
  have hB₀A : B₀ ⊆ A := hB₀K.trans hKA
  have h0B₀ : 0 ∉ B₀ := fun hzero => h0K (hB₀K hzero)
  have hbasisTwo : IsExactTupleAsymptoticBasis A 2 := by
    refine ⟨N₀, ?_⟩
    intro n hn
    obtain ⟨x, hxA, y, hyA, hxy⟩ := hcov n hn
    refine ⟨![x, y], ?_, ?_⟩
    · intro i
      fin_cases i
      · exact hxA
      · exact hyA
    · simpa [Fin.sum_univ_two] using hxy
  obtain ⟨B, hBB₀, hBinf, hbasisThree⟩ :=
    exists_infiniteDeletion_threeBasis_of_zero_splittingReservoir
      hbasisTwo h0 h0B₀ hB₀A hB₀inf hsplit
  exact hfail B (hBB₀.trans hB₀A) hBinf hbasisThree

open Classical in

theorem counterexample_positive_pairSplittable_points_finite
    {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    {a | a ∈ A ∧ 0 < a ∧ PairSplittableAwayFromSelf A a}.Finite := by
  let K : Set ℕ :=
    {a | a ∈ A ∧ 0 < a ∧ PairSplittableAwayFromSelf A a}
  apply counterexample_pairSplittable_reservoir_finite
      h0 hcov hfail
  · intro a ha
    exact ha.1
  · intro ha
    change 0 ∈ A ∧ 0 < 0 ∧
      PairSplittableAwayFromSelf A 0 at ha
    omega
  · intro a ha
    exact ha.2.2

open Classical in

theorem counterexample_eventually_all_basisPoints_zeroAtomic
    {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ T, ∀ a ∈ A, T ≤ a →
      ∀ E ∈ additiveSupportFamily A 2 a, E = {a, 0} := by
  let K : Set ℕ :=
    {a | a ∈ A ∧ 0 < a ∧ PairSplittableAwayFromSelf A a}
  have hKfinite : K.Finite :=
    counterexample_positive_pairSplittable_points_finite
      h0 hcov hfail
  obtain ⟨U, hU⟩ := hKfinite.bddAbove
  refine ⟨U + 1, ?_⟩
  intro a haA haU E hER
  have hatomic : ¬PairSplittableAwayFromSelf A a := by
    intro hsplit
    have haK : a ∈ K := ⟨haA, by omega, hsplit⟩
    have haBound := hU haK
    omega
  exact pairSupport_eq_self_zero_of_not_pairSplittableAwayFromSelf
    hatomic hER

open Classical in

theorem counterexample_eventually_positive_sumFree
    {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ T, ∀ a ∈ A, T ≤ a →
      ∀ u ∈ A, ∀ v ∈ A, 0 < u → 0 < v → u + v ≠ a := by
  obtain ⟨T, hatomic⟩ :=
    counterexample_eventually_all_basisPoints_zeroAtomic
      h0 hcov hfail
  refine ⟨T, ?_⟩
  intro a haA haT u huA v hvA huPos hvPos huv
  have hua : u < a := by omega
  have hsub : a - u = v := by omega
  exact
    (zeroAtom_forbids_positiveBackwardTranslate
      (hatomic a haA haT) huA huPos hua)
      (hsub.symm ▸ hvA)

open Classical in

theorem counterexample_eventually_completeSumFreePartition
    {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ T, ∀ n, T ≤ n →
      (n ∈ A ↔ ¬∃ u ∈ A, ∃ v ∈ A,
        0 < u ∧ 0 < v ∧ u + v = n) := by
  obtain ⟨S, hsumfree⟩ :=
    counterexample_eventually_positive_sumFree h0 hcov hfail
  refine ⟨max S N₀, ?_⟩
  intro n hn
  have hnS : S ≤ n := (le_max_left S N₀).trans hn
  have hnN : N₀ ≤ n := (le_max_right S N₀).trans hn
  constructor
  · intro hnA
    rintro ⟨u, huA, v, hvA, huPos, hvPos, huv⟩
    exact hsumfree n hnA hnS u huA v hvA huPos hvPos huv
  · intro hnoPositive
    by_contra hnA
    obtain ⟨u, huA, v, hvA, huv⟩ := hcov n hnN
    have huPos : 0 < u := by
      rcases Nat.eq_zero_or_pos u with rfl | huPos
      · have hvn : v = n := by omega
        exact (hnA (hvn ▸ hvA)).elim
      · exact huPos
    have hvPos : 0 < v := by
      rcases Nat.eq_zero_or_pos v with rfl | hvPos
      · have hun : u = n := by omega
        exact (hnA (hun ▸ huA)).elim
      · exact hvPos
    exact hnoPositive ⟨u, huA, v, hvA, huPos, hvPos, huv⟩

open Classical in

theorem counterexample_basisDifference_edges_finite
    {A : Set ℕ} {N₀ δ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hδpos : 0 < δ) (hδA : δ ∈ A) :
    {x | x ∈ A ∧ x + δ ∈ A}.Finite := by
  apply Set.not_infinite.mp
  intro hstart
  let Start : Set ℕ := {x | x ∈ A ∧ x + δ ∈ A}
  let StartPos : Set ℕ := Start \ ({0} : Set ℕ)
  have hStartPos : StartPos.Infinite :=
    hstart.diff (Set.finite_singleton 0)
  let K : Set ℕ := (fun x => x + δ) '' StartPos
  have hKinf : K.Infinite := by
    apply hStartPos.image
    intro x hx y hy hxy
    exact Nat.add_right_cancel hxy
  have hKA : K ⊆ A := by
    rintro b ⟨x, hx, rfl⟩
    exact hx.1.2
  have h0K : 0 ∉ K := by
    rintro ⟨x, hx, hzero⟩
    change x + δ = 0 at hzero
    omega
  have hsplittable : ∀ b ∈ K,
      PairSplittableAwayFromSelf A b := by
    rintro b ⟨x, hx, rfl⟩
    have hxStart : x ∈ A ∧ x + δ ∈ A := hx.1
    have hxpos : 0 < x := by
      by_contra hx0
      have : x = 0 := Nat.eq_zero_of_not_pos hx0
      exact hx.2 (by simpa [this])
    have hcomp : x + δ - x = δ := by omega
    have hsupport :
        pairSupport (x + δ) x ∈
          additiveSupportFamily A 2 (x + δ) := by
      apply pairSupport_mem_additiveSupportFamily
        (by omega) hxStart.1
      simpa [hcomp] using hδA
    refine ⟨pairSupport (x + δ) x, hsupport, ?_⟩
    intro hupper
    simp only [pairSupport, Finset.mem_insert,
      Finset.mem_singleton] at hupper
    rcases hupper with h | h <;> omega
  obtain ⟨B₀, hB₀K, hB₀inf, hsplit⟩ :=
    exists_infiniteDeletion_splittingDeletedPoints
      hKinf hsplittable
  have hB₀A : B₀ ⊆ A := hB₀K.trans hKA
  have h0B₀ : 0 ∉ B₀ := fun hzero => h0K (hB₀K hzero)
  have hbasisTwo : IsExactTupleAsymptoticBasis A 2 := by
    refine ⟨N₀, ?_⟩
    intro n hn
    obtain ⟨x, hxA, y, hyA, hxy⟩ := hcov n hn
    refine ⟨![x, y], ?_, ?_⟩
    · intro i
      fin_cases i
      · exact hxA
      · exact hyA
    · simpa [Fin.sum_univ_two] using hxy
  obtain ⟨B, hBB₀, hBinf, hbasisThree⟩ :=
    exists_infiniteDeletion_threeBasis_of_zero_splittingReservoir
      hbasisTwo h0 h0B₀ hB₀A hB₀inf hsplit
  exact hfail B (hBB₀.trans hB₀A) hBinf hbasisThree

open Classical in

theorem counterexample_fixedDifference_split_filled_finite
    {A : Set ℕ} {N₀ δ s t : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hδpos : 0 < δ) (htA : t ∈ A)
    (hst : s + t = δ) (hsδ : s ≠ δ) :
    {x | x ∈ A ∧ x + δ ∈ A ∧ x + s ∈ A}.Finite := by
  apply Set.not_infinite.mp
  intro hstarts
  let Starts : Set ℕ :=
    {x | x ∈ A ∧ x + δ ∈ A ∧ x + s ∈ A}
  let Upper : Set ℕ := (fun x => x + δ) '' Starts
  have hUpperInf : Upper.Infinite := by
    apply hstarts.image
    intro x hx y hy hxy
    exact Nat.add_right_cancel hxy
  let K : Set ℕ := Upper \ ({t} : Set ℕ)
  have hKinf : K.Infinite :=
    hUpperInf.diff (Set.finite_singleton t)
  have hKUpper : K ⊆ Upper := Set.diff_subset
  have hKA : K ⊆ A := by
    intro b hbK
    obtain ⟨x, hx, rfl⟩ := hKUpper hbK
    exact hx.2.1
  have h0K : 0 ∉ K := by
    intro hzero
    obtain ⟨x, hx, hsum⟩ := hKUpper hzero
    change x + δ = 0 at hsum
    omega
  have hsplittable : ∀ b ∈ K,
      PairSplittableAwayFromSelf A b := by
    intro b hbK
    obtain ⟨x, hx, hxb⟩ := hKUpper hbK
    change x ∈ A ∧ x + δ ∈ A ∧ x + s ∈ A at hx
    have hslt : s < δ := by omega
    have hcomponent : x + δ - (x + s) = t := by omega
    have hsupport :
        pairSupport (x + δ) (x + s) ∈
          additiveSupportFamily A 2 (x + δ) := by
      apply pairSupport_mem_additiveSupportFamily
        (by omega) hx.2.2
      simpa [hcomponent] using htA
    refine ⟨pairSupport (x + δ) (x + s), hxb ▸ hsupport, ?_⟩
    intro hbmem
    simp only [pairSupport, Finset.mem_insert,
      Finset.mem_singleton] at hbmem
    rcases hbmem with hfirst | hsecond
    · exact hsδ
        (Nat.add_left_cancel (hxb.trans hfirst)).symm
    · have hbt : b = t := hsecond.trans hcomponent
      exact hbK.2 (by simpa using hbt)
  exact hKinf
    (counterexample_pairSplittable_reservoir_finite
      h0 hcov hfail hKA h0K hsplittable)

open Classical in

theorem twoScale_fixedDifference_composition
    {A : Set ℕ} {N₀ δ s t u v : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hδpos : 0 < δ)
    (htA : t ∈ A) (hvA : v ∈ A)
    (hst : s + t = δ) (huv : u + v = 2 * δ)
    (hsδ : s ≠ δ) (huδ : u ≠ δ)
    (hstarts :
      {x | x ∈ A ∧ x + δ ∈ A ∧ x + s ∈ A ∧ x + u ∈ A}.Infinite) :
    ∃ B : Set ℕ, B ⊆ A ∧ B.Infinite ∧ 0 ∉ B ∧
      IsExactTupleAsymptoticBasis (A \ B) 3 := by
  let Starts : Set ℕ :=
    {x | x ∈ A ∧ x + δ ∈ A ∧ x + s ∈ A ∧ x + u ∈ A}
  let Upper : Set ℕ := (fun x => x + δ) '' Starts
  have hUpperInf : Upper.Infinite := by
    apply hstarts.image
    intro x hx y hy hxy
    exact Nat.add_right_cancel hxy
  let K : Set ℕ := Upper \ ({t, v} : Set ℕ)
  have hKinf : K.Infinite :=
    hUpperInf.diff (Set.toFinite {t, v})
  have hKUpper : K ⊆ Upper := Set.diff_subset
  have hdata : ∀ b ∈ K,
      δ ≤ b ∧ b - δ ∈ A ∧ b - δ + δ = b ∧
      (b - δ) + s ∈ A ∧ (b - δ) + u ∈ A := by
    intro b hbK
    obtain ⟨x, hxStarts, rfl⟩ := hKUpper hbK
    change x ∈ A ∧ x + δ ∈ A ∧
      x + s ∈ A ∧ x + u ∈ A at hxStarts
    change δ ≤ x + δ ∧
      x + δ - δ ∈ A ∧
      x + δ - δ + δ = x + δ ∧
      (x + δ - δ) + s ∈ A ∧
      (x + δ - δ) + u ∈ A
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · simpa using hxStarts.1
    · simp
    · simpa using hxStarts.2.2.1
    · simpa using hxStarts.2.2.2
  let f : ℕ → Finset ℕ := fun b =>
    {(b - δ) + s, t, (b - δ) + u, b - δ, v}
  have hfcard : ∀ b ∈ K, (f b).card ≤ 5 := by
    intro b hbK
    calc
      (f b).card ≤
          ({t, (b - δ) + u, b - δ, v} : Finset ℕ).card + 1 := by
        exact Finset.card_insert_le _ _
      _ ≤ ({(b - δ) + u, b - δ, v} : Finset ℕ).card + 1 + 1 := by
        exact Nat.add_le_add_right (Finset.card_insert_le _ _) 1
      _ ≤ ({b - δ, v} : Finset ℕ).card + 1 + 1 + 1 := by
        exact Nat.add_le_add_right (Finset.card_insert_le _ _) 2
      _ ≤ ({v} : Finset ℕ).card + 1 + 1 + 1 + 1 := by
        exact Nat.add_le_add_right (Finset.card_insert_le _ _) 3
      _ ≤ 5 := by simp
  have hfavoid : ∀ b ∈ K, b ∉ f b := by
    intro b hbK hb
    have hd := hdata b hbK
    simp only [f, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with hbs | hbt | hbu | hbx | hbv
    · have hbeq : (b - δ) + δ = (b - δ) + s := by
        exact hd.2.2.1.trans hbs
      exact hsδ (Nat.add_left_cancel hbeq).symm
    · exact hbK.2 (by simp [hbt])
    · have hbeq : (b - δ) + δ = (b - δ) + u := by
        exact hd.2.2.1.trans hbu
      exact huδ (Nat.add_left_cancel hbeq).symm
    · omega
    · exact hbK.2 (by simp [hbv])
  obtain ⟨B, hBK, hBinf, hfree⟩ :=
    exists_infinite_freeSet_of_bounded_pointMap
      hKinf f 5 hfcard hfavoid
  have hBA : B ⊆ A := by
    intro b hbB
    obtain ⟨x, hxStarts, rfl⟩ := hKUpper (hBK hbB)
    exact hxStarts.2.1
  have h0B : 0 ∉ B := by
    intro hzero
    have hd := hdata 0 (hBK hzero)
    omega
  refine ⟨B, hBA, hBinf, h0B, ?_⟩
  apply deletion_criterion_local h0 h0B hcov
  intro n hn
  rintro ⟨b, hbB, a, haA, hba⟩
  have hbK := hBK hbB
  have hbd := hdata b hbK
  have hbdis := Set.disjoint_left.mp (hfree b hbB)
  by_cases haB : a ∈ B
  · have haK := hBK haB
    have had := hdata a haK
    have hadis := Set.disjoint_left.mp (hfree a haB)
    refine ⟨(b - δ) + u, hbd.2.2.2.2,
      a - δ, had.2.1,
      v, hvA, ?_, ?_, ?_, ?_⟩
    · intro hmem
      exact hbdis (by simp [f]) hmem
    · intro hmem
      exact hadis (by simp [f]) hmem
    · intro hmem
      exact hbdis (by simp [f]) hmem
    · omega
  · refine ⟨(b - δ) + s, hbd.2.2.2.1,
      t, htA, a, haA, ?_, ?_, haB, ?_⟩
    · intro hmem
      exact hbdis (by simp [f]) hmem
    · intro hmem
      exact hbdis (by simp [f]) hmem
    · omega

open Classical in

theorem counterexample_twoScale_missingRectangles
    {A : Set ℕ} {N₀ δ s t u v : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hδpos : 0 < δ)
    (htA : t ∈ A) (hvA : v ∈ A)
    (hst : s + t = δ) (huv : u + v = 2 * δ)
    (hsδ : s ≠ δ) (huδ : u ≠ δ) :
    {x | x ∈ A ∧ x + δ ∈ A ∧
      x + s ∈ A ∧ x + u ∈ A}.Finite := by
  apply Set.not_infinite.mp
  intro hinfinite
  obtain ⟨B, hBA, hBinf, h0B, hbasis⟩ :=
    twoScale_fixedDifference_composition
      h0 hcov hδpos htA hvA hst huv hsδ huδ hinfinite
  exact hfail B hBA hBinf hbasis

open Classical in

theorem counterexample_anchorCenter_missingParallelograms
    {A : Set ℕ} {N₀ δ u v : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hδpos : 0 < δ) (hδA : δ ∈ A) (hvA : v ∈ A)
    (huv : u + v = 2 * δ) (huδ : u ≠ δ) :
    {x | x ∈ A ∧ x + δ ∈ A ∧ x + u ∈ A}.Finite := by
  have hfinite :=
    counterexample_twoScale_missingRectangles
      h0 hcov hfail hδpos hδA hvA
        (by omega : 0 + δ = δ) huv (by omega) huδ
  apply hfinite.subset
  intro x hx
  exact ⟨hx.1, hx.2.1, by simpa using hx.1, hx.2.2⟩

open Classical in

theorem counterexample_popularAnchorCenter_has_emptyParallelograms
    {A : Set ℕ} {N₀ δ u v : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hδpos : 0 < δ) (hδA : δ ∈ A)
    (huA : u ∈ A) (hvA : v ∈ A)
    (huv : u + v = 2 * δ) (huδ : u ≠ δ)
    (hedges : {x | x ∈ A ∧ x + δ ∈ A}.Infinite) :
    {x | x ∈ A ∧ x + δ ∈ A ∧
      x + u ∉ A ∧ x + v ∉ A}.Infinite := by
  have hvδ : v ≠ δ := by
    intro hvδ
    omega
  let Edge : Set ℕ := {x | x ∈ A ∧ x + δ ∈ A}
  let FillU : Set ℕ :=
    {x | x ∈ A ∧ x + δ ∈ A ∧ x + u ∈ A}
  let FillV : Set ℕ :=
    {x | x ∈ A ∧ x + δ ∈ A ∧ x + v ∈ A}
  have hFillU : FillU.Finite :=
    counterexample_anchorCenter_missingParallelograms
      h0 hcov hfail hδpos hδA hvA huv huδ
  have hFillV : FillV.Finite :=
    counterexample_anchorCenter_missingParallelograms
      h0 hcov hfail hδpos hδA huA (by omega) hvδ
  have hremaining : (Edge \ (FillU ∪ FillV)).Infinite :=
    hedges.diff (hFillU.union hFillV)
  apply hremaining.mono
  intro x hx
  have hxEdge : x ∈ A ∧ x + δ ∈ A := hx.1
  have hxNotU : x + u ∉ A := by
    intro hxu
    exact hx.2 (Or.inl ⟨hxEdge.1, hxEdge.2, hxu⟩)
  have hxNotV : x + v ∉ A := by
    intro hxv
    exact hx.2 (Or.inr ⟨hxEdge.1, hxEdge.2, hxv⟩)
  exact ⟨hxEdge.1, hxEdge.2, hxNotU, hxNotV⟩

open Classical in

theorem counterexample_popularDifference_missingIntermediate_fork
    {A : Set ℕ} {N₀ δ s t u v : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hδpos : 0 < δ)
    (htA : t ∈ A) (hvA : v ∈ A)
    (hst : s + t = δ) (huv : u + v = 2 * δ)
    (hsδ : s ≠ δ) (huδ : u ≠ δ)
    (hedges : {x | x ∈ A ∧ x + δ ∈ A}.Infinite) :
    {x | x ∈ A ∧ x + δ ∈ A ∧ x + s ∉ A}.Infinite ∨
    {x | x ∈ A ∧ x + δ ∈ A ∧ x + u ∉ A}.Infinite := by
  let Edge : Set ℕ := {x | x ∈ A ∧ x + δ ∈ A}
  let Both : Set ℕ :=
    {x | x ∈ A ∧ x + δ ∈ A ∧ x + s ∈ A ∧ x + u ∈ A}
  let MissingS : Set ℕ :=
    {x | x ∈ A ∧ x + δ ∈ A ∧ x + s ∉ A}
  let MissingU : Set ℕ :=
    {x | x ∈ A ∧ x + δ ∈ A ∧ x + u ∉ A}
  have hBoth : Both.Finite :=
    counterexample_twoScale_missingRectangles
      h0 hcov hfail hδpos htA hvA hst huv hsδ huδ
  by_cases hS : MissingS.Infinite
  · exact Or.inl hS
  · right
    by_contra hU
    have hcover : Edge ⊆ Both ∪ MissingS ∪ MissingU := by
      intro x hx
      by_cases hxs : x + s ∈ A
      · by_cases hxu : x + u ∈ A
        · exact Or.inl (Or.inl ⟨hx.1, hx.2, hxs, hxu⟩)
        · exact Or.inr ⟨hx.1, hx.2, hxu⟩
      · exact Or.inl (Or.inr ⟨hx.1, hx.2, hxs⟩)
    have hfinite : Edge.Finite :=
      (hBoth.union (Set.not_infinite.mp hS) |>.union
        (Set.not_infinite.mp hU)).subset hcover
    exact hedges hfinite

open Classical in

theorem counterexample_popularDifference_central_or_twoScaleMissing
    {A : Set ℕ} {N₀ δ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hδpos : 0 < δ) (hδN : N₀ ≤ δ)
    (hedges : {x | x ∈ A ∧ x + δ ∈ A}.Infinite) :
    (δ ∈ A ∧
      ∀ x ∈ A, ∀ y ∈ A, x + y = 2 * δ → x = δ ∧ y = δ) ∨
    ∃ s ∈ A, ∃ t ∈ A, ∃ u ∈ A, ∃ v ∈ A,
      s + t = δ ∧ u + v = 2 * δ ∧ s ≠ δ ∧ u ≠ δ ∧
      ({x | x ∈ A ∧ x + δ ∈ A ∧ x + s ∉ A}.Infinite ∨
       {x | x ∈ A ∧ x + δ ∈ A ∧ x + u ∉ A}.Infinite) := by
  by_cases hoffcenter :
      ∃ u ∈ A, ∃ v ∈ A, u + v = 2 * δ ∧ u ≠ δ
  · right
    obtain ⟨u, huA, v, hvA, huv, huδ⟩ := hoffcenter
    obtain ⟨p, hpA, q, hqA, hpq⟩ := hcov δ hδN
    by_cases hpδ : p = δ
    · have hq0 : q = 0 := by omega
      have hsplit :=
        counterexample_popularDifference_missingIntermediate_fork
          h0 hcov hfail hδpos hpA hvA
            (by omega : q + p = δ) huv (by omega) huδ hedges
      exact ⟨q, hqA, p, hpA, u, huA, v, hvA,
        by omega, huv, by omega, huδ, hsplit⟩
    · have hsplit :=
        counterexample_popularDifference_missingIntermediate_fork
          h0 hcov hfail hδpos hqA hvA
            hpq huv hpδ huδ hedges
      exact ⟨p, hpA, q, hqA, u, huA, v, hvA,
        hpq, huv, hpδ, huδ, hsplit⟩
  · left
    push Not at hoffcenter
    obtain ⟨p, hpA, q, hqA, hpq⟩ :=
      hcov (2 * δ) (by omega)
    have hpδ : p = δ :=
      hoffcenter p hpA q hqA hpq
    have hqδ : q = δ := by omega
    refine ⟨hpδ ▸ hpA, ?_⟩
    intro x hxA y hyA hxy
    have hxδ : x = δ :=
      hoffcenter x hxA y hyA hxy
    exact ⟨hxδ, by omega⟩

open Classical in

theorem counterexample_popularDifference_not_mem
    {A : Set ℕ} {N₀ δ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hδpos : 0 < δ)
    (hedges : {x | x ∈ A ∧ x + δ ∈ A}.Infinite) :
    δ ∉ A := by
  intro hδA
  exact hedges
    (counterexample_basisDifference_edges_finite
      h0 hcov hfail hδpos hδA)

open Classical in

theorem counterexample_popularDifference_has_emptySplitDiamonds
    {A : Set ℕ} {N₀ δ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hδpos : 0 < δ) (hδN : N₀ ≤ δ)
    (hedges : {x | x ∈ A ∧ x + δ ∈ A}.Infinite) :
    ∃ s ∈ A, ∃ t ∈ A, s + t = δ ∧
      {x | x ∈ A ∧ x + δ ∈ A ∧
        x + s ∉ A ∧ x + t ∉ A}.Infinite := by
  have hδnot : δ ∉ A :=
    counterexample_popularDifference_not_mem
      h0 hcov hfail hδpos hedges
  obtain ⟨s, hsA, t, htA, hst⟩ := hcov δ hδN
  have hsδ : s ≠ δ := by
    intro hs
    exact hδnot (hs ▸ hsA)
  have htδ : t ≠ δ := by
    intro ht
    exact hδnot (ht ▸ htA)
  let Edge : Set ℕ := {x | x ∈ A ∧ x + δ ∈ A}
  let FillS : Set ℕ :=
    {x | x ∈ A ∧ x + δ ∈ A ∧ x + s ∈ A}
  let FillT : Set ℕ :=
    {x | x ∈ A ∧ x + δ ∈ A ∧ x + t ∈ A}
  have hFillS : FillS.Finite :=
    counterexample_fixedDifference_split_filled_finite
      h0 hcov hfail hδpos htA hst hsδ
  have hFillT : FillT.Finite :=
    counterexample_fixedDifference_split_filled_finite
      h0 hcov hfail hδpos hsA (by omega) htδ
  have hremaining : (Edge \ (FillS ∪ FillT)).Infinite :=
    hedges.diff (hFillS.union hFillT)
  refine ⟨s, hsA, t, htA, hst, ?_⟩
  apply hremaining.mono
  intro x hx
  have hxEdge : x ∈ A ∧ x + δ ∈ A := hx.1
  have hxs : x + s ∉ A := by
    intro hxsA
    exact hx.2 (Or.inl ⟨hxEdge.1, hxEdge.2, hxsA⟩)
  have hxt : x + t ∉ A := by
    intro hxtA
    exact hx.2 (Or.inr ⟨hxEdge.1, hxEdge.2, hxtA⟩)
  exact ⟨hxEdge.1, hxEdge.2, hxs, hxt⟩

open Classical in

theorem counterexample_popularDifference_has_twoScaleMissing
    {A : Set ℕ} {N₀ δ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hδpos : 0 < δ) (hδN : N₀ ≤ δ)
    (hedges : {x | x ∈ A ∧ x + δ ∈ A}.Infinite) :
    ∃ s ∈ A, ∃ t ∈ A, ∃ u ∈ A, ∃ v ∈ A,
      s + t = δ ∧ u + v = 2 * δ ∧ s ≠ δ ∧ u ≠ δ ∧
      ({x | x ∈ A ∧ x + δ ∈ A ∧ x + s ∉ A}.Infinite ∨
       {x | x ∈ A ∧ x + δ ∈ A ∧ x + u ∉ A}.Infinite) := by
  rcases counterexample_popularDifference_central_or_twoScaleMissing
      h0 hcov hfail hδpos hδN hedges with hcentral | hmissing
  · exact (counterexample_popularDifference_not_mem
      h0 hcov hfail hδpos hedges hcentral.1).elim
  · exact hmissing

open Classical in

theorem counterexample_growingDifferences_have_large_emptySplitRectangles
    {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hgrowing : ∀ Δ K, ∃ d, Δ < d ∧ ∃ V : Finset ℕ,
      K ≤ V.card ∧ ∀ x ∈ V, x ∈ A ∧ x + d ∈ A) :
    ∀ Δ K, ∃ d, Δ < d ∧ d ∉ A ∧
      ∃ u ∈ A, ∃ v ∈ A,
        0 < u ∧ 0 < v ∧ u + v = d ∧
        ∃ V : Finset ℕ, K ≤ V.card ∧
          ∀ x ∈ V, x ∈ A ∧ x + d ∈ A ∧
            x + u ∉ A ∧ x + v ∉ A := by
  obtain ⟨T, hsumfree⟩ :=
    counterexample_eventually_positive_sumFree h0 hcov hfail
  intro Δ K
  obtain ⟨d, hdlarge, V, hVcard, hV⟩ :=
    hgrowing (max Δ (max T N₀)) (max K 2)
  have hdΔ : Δ < d := lt_of_le_of_lt
    (le_max_left Δ (max T N₀)) hdlarge
  have hdT : T < d := lt_of_le_of_lt
    (le_trans (le_max_left T N₀)
      (le_max_right Δ (max T N₀))) hdlarge
  have hdN : N₀ ≤ d := le_trans
    (le_trans (le_max_right T N₀)
      (le_max_right Δ (max T N₀)))
    (le_of_lt hdlarge)
  have hVtwo : 1 < V.card := by omega
  obtain ⟨x, hxV, y, hyV, hxy⟩ :=
    Finset.one_lt_card.mp hVtwo
  have hdnot : d ∉ A := by
    intro hdA
    have hpositive : 0 < x ∨ 0 < y := by omega
    rcases hpositive with hxpos | hypos
    · have hxdata := hV x hxV
      exact
        (hsumfree (x + d) hxdata.2 (by omega)
          x hxdata.1 d hdA hxpos (by omega)) rfl
    · have hydata := hV y hyV
      exact
        (hsumfree (y + d) hydata.2 (by omega)
          y hydata.1 d hdA hypos (by omega)) rfl
  obtain ⟨u, huA, v, hvA, huPos, hvPos, huv⟩ :=
    (large_mem_or_splits hcov hdN).resolve_left hdnot
  refine ⟨d, hdΔ, hdnot, u, huA, v, hvA,
    huPos, hvPos, huv, V, by omega, ?_⟩
  intro z hzV
  have hzdata := hV z hzV
  have hzu : z + u ∉ A := by
    intro hzuA
    apply hsumfree (z + d) hzdata.2 (by omega)
      (z + u) hzuA v hvA (by omega) hvPos
    omega
  have hzv : z + v ∉ A := by
    intro hzvA
    apply hsumfree (z + d) hzdata.2 (by omega)
      (z + v) hzvA u huA (by omega) huPos
    omega
  exact ⟨hzdata.1, hzdata.2, hzu, hzv⟩

open Classical in

theorem infiniteDeletionThreeBasis_or_boundedMovingPairTransversalsAlongExternal
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzero : 0 ∈ A) :
    (∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) 3) ∨
      HasBoundedMovingOutsideTransversalsAlong
        (additiveSupportFamily A 2) A {n | n ∉ A} := by
  obtain ⟨F, hFA, hgrowth⟩ | hmoving :=
    exists_finiteCore_outsideMatchingAlong_or_boundedMovingAlong
      (A := A) (S := {n | n ∉ A})
      (R := additiveSupportFamily A 2) (r := 2)
      (additiveSupportFamily_supportsIn A 2)
      (additiveSupportFamily_cardAtMost A 2)
  · left
    have hmatches : MatchingTendsToInfinityOutsideAlong
        (additiveSupportFamily A 2) F {n | n ∉ A} :=
      matchingTendsToInfinityOutsideAlong_of_outsideMatchingAlong hgrowth
    obtain ⟨B₀, hB₀A, hB₀, _hB₀F, hsurvive⟩ :=
      sparseDeletion_of_matchingTendsToInfinityOutsideAlong
        (C := A) (S := {n | n ∉ A})
        (R := additiveSupportFamily A 2) (F := F)
        (additiveSupportFamily_supportsBounded A 2)
        hmatches (hbasis.unboundedOutside F)
    have hexternal :
        IsExactTupleAsymptoticBasisAlong
          (A \ B₀) 2 {n | n ∉ A} :=
      hasEventuallySurvivingSupportAlong_additive_iff.mp hsurvive
    obtain ⟨N, hN⟩ := hexternal
    obtain ⟨T, hself⟩ :=
      eventually_selfAvoidingTripleSupport_of_orderTwoBasis hbasis
    let K : Set ℕ := B₀ \ Set.Iio (max T 1)
    have hK : K.Infinite :=
      hB₀.diff (Set.finite_Iio (max T 1))
    have hlocal : ∀ x ∈ K, HasSelfAvoidingTripleSupport A x := by
      intro x hxK
      apply hself x
      exact le_trans (le_max_left T 1) (Nat.le_of_not_gt hxK.2)
    obtain ⟨B, hBK, hB, hrepairs⟩ :=
      exists_infinite_selfTripleRepairs hK hlocal
    have hBB₀ : B ⊆ B₀ :=
      hBK.trans Set.diff_subset
    have hBA : B ⊆ A :=
      hBB₀.trans hB₀A
    have hzeroB : 0 ∉ B := by
      intro h0B
      have h0K := hBK h0B
      apply h0K.2
      exact lt_of_lt_of_le Nat.zero_lt_one (le_max_right T 1)
    have hserved : ∀ b ∈ B, ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = b := by
      intro b hbB
      obtain ⟨G, hGR, hGB⟩ := hrepairs b hbB
      obtain ⟨v, hvA, hvsum, hvSupport⟩ :=
        mem_additiveSupportFamily_iff.mp hGR
      have hnotB : ∀ i, (v i).1 ∉ B := by
        intro i hviB
        apply Set.disjoint_left.mp hGB
          (show (v i).1 ∈ G from by
            rw [← hvSupport]
            exact mem_tupleSupport_iff.mpr ⟨i, rfl⟩)
          hviB
      refine ⟨(v 0).1, hvA 0, (v 1).1, hvA 1,
        (v 2).1, hvA 2, hnotB 0, hnotB 1, hnotB 2, ?_⟩
      simpa [Fin.sum_univ_three] using hvsum
    have hcover : ∀ n, N ≤ n → n ∉ A →
        ∃ x ∈ A, ∃ y ∈ A,
          x ∉ B ∧ y ∉ B ∧ x + y = n := by
      intro n hn hnA
      obtain ⟨v, hvAB₀, hvsum⟩ := hN n hn hnA
      refine ⟨v 0, (hvAB₀ 0).1, v 1, (hvAB₀ 1).1,
        ?_, ?_, ?_⟩
      · intro hvB
        exact (hvAB₀ 0).2 (hBB₀ hvB)
      · intro hvB
        exact (hvAB₀ 1).2 (hBB₀ hvB)
      · simpa [Fin.sum_univ_two] using hvsum
    exact ⟨B, hBA, hB,
      deletion_criterion_sumfree hzero hzeroB hserved hcover⟩
  · exact Or.inr hmoving

open Classical in
/-- A genuine counterexample must lie in the external bounded-moving
branch of the preceding dichotomy. -/
theorem counterexample_forces_boundedMovingPairTransversalsAlongExternal
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzero : 0 ∈ A)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    HasBoundedMovingOutsideTransversalsAlong
      (additiveSupportFamily A 2) A {n | n ∉ A} := by
  rcases
      infiniteDeletionThreeBasis_or_boundedMovingPairTransversalsAlongExternal
        hbasis hzero with hdelete | hmoving
  · obtain ⟨B, hBA, hB, hthree⟩ := hdelete
    exact (hfail B hBA hB hthree).elim
  · exact hmoving

open Classical in
/-- Bounded moving transversals along external targets give a fixed
cardinality bound for the complete pair-support family at arbitrarily large
external targets.  With empty protected core, pair supports are nonempty and
form a matching, so any transversal has at least as many vertices as there
are supports. -/
theorem recurrently_bounded_pairSupports_on_external_of_boundedMoving
    {A : Set ℕ}
    (hmoving : HasBoundedMovingOutsideTransversalsAlong
      (additiveSupportFamily A 2) A {n | n ∉ A}) :
    ∃ m, ∀ N, ∃ n, N ≤ n ∧ n ∉ A ∧
      (additiveSupportFamily A 2 n).card ≤ m := by
  obtain ⟨m, hm⟩ := hmoving ∅ (by simp)
  refine ⟨m, ?_⟩
  intro N
  obtain ⟨n, T, hn, hnA, _hTA, _hTempty, hTcard, htrans⟩ := hm N
  have hdestroy : DestroysAt
      (additiveSupportFamily A 2) (T : Set ℕ) n := by
    intro E hER
    have hEnonempty :=
      additiveSupportFamily_supportsNonempty A (by omega) n E hER
    have hEout : E ∈ outsideSupportHypergraph
        (additiveSupportFamily A 2) ∅ n := by
      apply Finset.mem_erase.mpr
      refine ⟨Finset.nonempty_iff_ne_empty.mp hEnonempty, ?_⟩
      exact Finset.mem_image.mpr ⟨E, hER, by simp⟩
    obtain ⟨x, hx⟩ := htrans E hEout
    have hx' := Finset.mem_inter.mp hx
    exact Set.not_disjoint_iff.mpr
      ⟨x, hx'.1, Finset.mem_coe.mpr hx'.2⟩
  have hsupportCard : (additiveSupportFamily A 2 n).card ≤ T.card :=
    card_supports_le_card_of_matching_of_destroysAt
      (fun E hER =>
        additiveSupportFamily_supportsNonempty A (by omega) n E hER)
      (additiveSupportFamily_two_isMatching A n) hdestroy
  exact ⟨n, hn, hnA, hsupportCard.trans hTcard⟩

open Classical in
/-- Numerical external-target normal form for a counterexample: one fixed
bound controls the number of unordered pair supports on an unbounded
sequence of targets outside `A`. -/
theorem counterexample_forces_recurrentlyBoundedPairSupportsOnExternal
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzero : 0 ∈ A)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ m, ∀ N, ∃ n, N ≤ n ∧ n ∉ A ∧
      (additiveSupportFamily A 2 n).card ≤ m :=
  recurrently_bounded_pairSupports_on_external_of_boundedMoving
    (counterexample_forces_boundedMovingPairTransversalsAlongExternal
      hbasis hzero hfail)

open Classical in
/-- At a complete sum-free tail, subtracting a positive basis source from
an external target has only two outcomes.  Either the remainder is itself
in the basis, so the source is an endpoint of a pair representation of the
original target, or the remainder splits into two positive basis elements
and the source extends that split to a positive triple representation. -/
theorem completeSumFree_external_source_pair_or_positiveTriple
    {A : Set ℕ} {T n a : ℕ}
    (hcomplete : ∀ q, T ≤ q →
      (q ∈ A ↔ ¬∃ u ∈ A, ∃ v ∈ A,
        0 < u ∧ 0 < v ∧ u + v = q))
    (hnA : n ∉ A) (haA : a ∈ A) (haPos : 0 < a)
    (hTa : T + a ≤ n) :
    n - a ∈ A ∨
      ∃ u ∈ A, ∃ v ∈ A,
        0 < u ∧ 0 < v ∧ a + u + v = n := by
  by_cases hremA : n - a ∈ A
  · exact Or.inl hremA
  · right
    have hTrem : T ≤ n - a := by omega
    have hsplit : ∃ u ∈ A, ∃ v ∈ A,
        0 < u ∧ 0 < v ∧ u + v = n - a := by
      by_contra hno
      exact hremA ((hcomplete (n - a) hTrem).mpr hno)
    obtain ⟨u, huA, v, hvA, huPos, hvPos, huv⟩ := hsplit
    exact ⟨u, huA, v, hvA, huPos, hvPos, by omega⟩

open Classical in

theorem counterexample_externalPairBottlenecks_have_manyPositiveTripleSources
    {A : Set ℕ} {N₀ : ℕ}
    (hzero : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ m, ∀ K N, ∃ n, ∃ S : Finset ℕ,
      N ≤ n ∧ n ∉ A ∧
      (additiveSupportFamily A 2 n).card ≤ m ∧
      K < S.card ∧
      ∀ a ∈ S, a ∈ A ∧ 0 < a ∧
        ∃ u ∈ A, ∃ v ∈ A,
          0 < u ∧ 0 < v ∧ a + u + v = n := by
  have hbasis : IsExactTupleAsymptoticBasis A 2 := by
    refine ⟨N₀, ?_⟩
    intro n hn
    obtain ⟨x, hxA, y, hyA, hxy⟩ := hcov n hn
    refine ⟨![x, y], ?_, ?_⟩
    · intro i
      fin_cases i
      · exact hxA
      · exact hyA
    · simpa [Fin.sum_univ_two] using hxy
  obtain ⟨T, hcomplete⟩ :=
    counterexample_eventually_completeSumFreePartition
      hzero hcov hfail
  obtain ⟨m, hbounded⟩ :=
    counterexample_forces_recurrentlyBoundedPairSupportsOnExternal
      hbasis hzero hfail
  refine ⟨m, ?_⟩
  intro K N
  let Apos : Set ℕ := A \ ({0} : Set ℕ)
  have hApos : Apos.Infinite :=
    hbasis.infinite.diff (Set.finite_singleton 0)
  obtain ⟨S₀, hS₀Apos, hS₀card⟩ :=
    hApos.exists_subset_card_eq (K + 2 * m + 1)
  have hS₀nonempty : S₀.Nonempty := by
    apply Finset.card_pos.mp
    rw [hS₀card]
    omega
  obtain ⟨n, hnLate, hnA, hnPairCard⟩ :=
    hbounded (max N (T + S₀.max' hS₀nonempty))
  let U : Finset ℕ :=
    (additiveSupportFamily A 2 n).biUnion id
  let S : Finset ℕ := S₀ \ U
  have hUcard : U.card ≤ 2 * m := by
    calc
      U.card ≤
          ∑ E ∈ additiveSupportFamily A 2 n, E.card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _E ∈ additiveSupportFamily A 2 n, 2 := by
        gcongr with E hER
        exact additiveSupportFamily_cardAtMost A 2 n E hER
      _ = 2 * (additiveSupportFamily A 2 n).card := by
        simp [Nat.mul_comm]
      _ ≤ 2 * m := Nat.mul_le_mul_left 2 hnPairCard
  have hinterCard : (S₀ ∩ U).card ≤ U.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hScardSum : S.card + (S₀ ∩ U).card = S₀.card := by
    exact Finset.card_sdiff_add_card_inter S₀ U
  have hScard : K < S.card := by
    rw [hS₀card] at hScardSum
    omega
  refine ⟨n, S,
    (le_max_left N (T + S₀.max' hS₀nonempty)).trans hnLate,
    hnA, hnPairCard, hScard, ?_⟩
  intro a haS
  have haS₀ : a ∈ S₀ := (Finset.mem_sdiff.mp haS).1
  have haU : a ∉ U := (Finset.mem_sdiff.mp haS).2
  have haApos := hS₀Apos haS₀
  have haA : a ∈ A := haApos.1
  have haPos : 0 < a := by
    have ha0 : a ≠ 0 := by simpa using haApos.2
    omega
  have haMax : a ≤ S₀.max' hS₀nonempty :=
    Finset.le_max' S₀ a haS₀
  have hTa : T + a ≤ n := by
    exact (Nat.add_le_add_left haMax T).trans
      ((le_max_right N (T + S₀.max' hS₀nonempty)).trans hnLate)
  rcases
      completeSumFree_external_source_pair_or_positiveTriple
        hcomplete hnA haA haPos hTa with hremA | htriple
  · exfalso
    have han : a ≤ n := by omega
    have hpair :
        pairSupport n a ∈ additiveSupportFamily A 2 n := by
      apply pairSupport_mem_additiveSupportFamily han haA
      have hsub : n - a = n - a := rfl
      simpa [hsub] using hremA
    apply haU
    exact Finset.mem_biUnion.mpr
      ⟨pairSupport n a, hpair, by simp [pairSupport]⟩
  · exact ⟨haA, haPos, htriple⟩

open Classical in
/-- A fixed-difference cross target has a triple repair avoiding both upper
endpoints.  Subtract a fixed positive source `d` and cover the remainder by
two basis elements.  If either one were `x+δ`, the other would express the
late basis point `y` as a sum of two positive basis elements; the other
endpoint is symmetric. -/
theorem fixedDifference_crossTarget_has_endpointAvoidingTriple
    {A : Set ℕ} {N₀ T δ d x y : ℕ}
    (hcov : PairCovers A N₀)
    (hsumfree : ∀ a ∈ A, T ≤ a →
      ∀ u ∈ A, ∀ v ∈ A, 0 < u → 0 < v → u + v ≠ a)
    (hdA : d ∈ A) (hdPos : 0 < d)
    (hxA : x ∈ A) (hyA : y ∈ A)
    (hxT : T ≤ x) (hyT : T ≤ y)
    (hxd : d < x) (hyd : d < y)
    (hxlarge : N₀ + d ≤ x) :
    ∃ G ∈ additiveSupportFamily A 3 (x + y + δ),
      Disjoint (G : Set ℕ)
        ((({x + δ, y + δ} : Finset ℕ) : Set ℕ)) := by
  have hdTarget : d ≤ x + y + δ := by omega
  obtain ⟨p, hpA, q, hqA, hpq⟩ :=
    hcov (x + y + δ - d) (by omega)
  have hsum : d + p + q = x + y + δ := by omega
  have hpx : p ≠ x + δ := by
    intro hp
    have hqPos : 0 < q := by omega
    exact hsumfree y hyA hyT d hdA q hqA hdPos hqPos (by omega)
  have hpy : p ≠ y + δ := by
    intro hp
    have hqPos : 0 < q := by omega
    exact hsumfree x hxA hxT d hdA q hqA hdPos hqPos (by omega)
  have hqx : q ≠ x + δ := by
    intro hq
    have hpPos : 0 < p := by omega
    exact hsumfree y hyA hyT d hdA p hpA hdPos hpPos (by omega)
  have hqy : q ≠ y + δ := by
    intro hq
    have hpPos : 0 < p := by omega
    exact hsumfree x hxA hxT d hdA p hpA hdPos hpPos (by omega)
  apply exists_surviving_additiveSupport_iff.mpr
  refine ⟨![d, p, q], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp_all <;> omega
  · simpa [Fin.sum_univ_three] using hsum

open Classical in
/-- A bounded exceptional shift `a<d` has a triple repair avoiding the
upper endpoint `x+δ`.  If the pair obtained after subtracting `d` used that
endpoint, its complementary summand would force `d≤a`. -/
theorem fixedDifference_smallShift_has_endpointAvoidingTriple
    {A : Set ℕ} {N₀ δ d x a : ℕ}
    (hcov : PairCovers A N₀)
    (hdA : d ∈ A) (hxA : x ∈ A)
    (haA : a ∈ A) (haSmall : a < d)
    (hdx : d < x)
    (hxlarge : N₀ + d ≤ x) :
    ∃ G ∈ additiveSupportFamily A 3 (x + δ + a),
      Disjoint (G : Set ℕ) ({x + δ} : Set ℕ) := by
  obtain ⟨p, hpA, q, hqA, hpq⟩ :=
    hcov (x + δ + a - d) (by omega)
  have hsum : d + p + q = x + δ + a := by omega
  have hdp : d ≠ x + δ := by omega
  have hpp : p ≠ x + δ := by
    intro hp
    omega
  have hqp : q ≠ x + δ := by
    intro hq
    omega
  apply exists_surviving_additiveSupport_iff.mpr
  refine ⟨![d, p, q], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp_all
  · simpa [Fin.sum_univ_three] using hsum

open Classical in
/-- Finitely many pointwise endpoint-avoiding repairs can be made
simultaneously disjoint from one infinite thinning of the endpoint
reservoir. -/
theorem exists_infinite_freeSet_for_finitelyMany_pointwiseSupports
    {A K : Set ℕ} {I : Finset ℕ} {target : ℕ → ℕ → ℕ}
    (hK : K.Infinite)
    (hlocal : ∀ b ∈ K, ∀ i ∈ I,
      ∃ G ∈ additiveSupportFamily A 3 (target b i),
        Disjoint (G : Set ℕ) ({b} : Set ℕ)) :
    ∃ L, L ⊆ K ∧ L.Infinite ∧
      ∀ b ∈ L, ∀ i ∈ I,
        ∃ G ∈ additiveSupportFamily A 3 (target b i),
          Disjoint (G : Set ℕ) L := by
  let HasRepair (b i : ℕ) : Prop :=
    ∃ G ∈ additiveSupportFamily A 3 (target b i),
      Disjoint (G : Set ℕ) ({b} : Set ℕ)
  let chooseSupport (b i : ℕ) : Finset ℕ :=
    if h : HasRepair b i then Classical.choose h else ∅
  let f : ℕ → Finset ℕ := fun b => I.biUnion (chooseSupport b)
  have hchoose : ∀ b ∈ K, ∀ i ∈ I,
      chooseSupport b i ∈ additiveSupportFamily A 3 (target b i) ∧
        Disjoint (chooseSupport b i : Set ℕ) ({b} : Set ℕ) := by
    intro b hbK i hiI
    have hHas : HasRepair b i := hlocal b hbK i hiI
    simp only [chooseSupport, dif_pos hHas]
    exact Classical.choose_spec hHas
  have hfcard : ∀ b ∈ K, (f b).card ≤ 3 * I.card := by
    intro b hbK
    calc
      (f b).card ≤ ∑ i ∈ I, (chooseSupport b i).card := by
        exact Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ I, 3 := by
        apply Finset.sum_le_sum
        intro i hiI
        exact additiveSupportFamily_cardAtMost A 3 (target b i)
          (chooseSupport b i) (hchoose b hbK i hiI).1
      _ = 3 * I.card := by simp [Nat.mul_comm]
  have hfavoid : ∀ b ∈ K, b ∉ f b := by
    intro b hbK hbf
    obtain ⟨i, hiI, hbi⟩ := Finset.mem_biUnion.mp hbf
    exact Set.disjoint_left.mp (hchoose b hbK i hiI).2 hbi (by simp)
  obtain ⟨L, hLK, hL, hfree⟩ :=
    exists_infinite_freeSet_of_bounded_pointMap
      hK f (3 * I.card) hfcard hfavoid
  refine ⟨L, hLK, hL, ?_⟩
  intro b hbL i hiI
  refine ⟨chooseSupport b i, (hchoose b (hLK hbL) i hiI).1, ?_⟩
  rw [Set.disjoint_left]
  intro x hxi hxL
  exact Set.disjoint_left.mp (hfree b hbL)
    (Finset.mem_biUnion.mpr ⟨i, hiI, hxi⟩) hxL

open Classical in
/-- Pairwise endpoint-avoiding repairs of the shifted targets
`b+c-δ` can be made simultaneously disjoint from one infinite thinning. -/
theorem exists_infinite_freeSet_for_shiftedPairSupports
    {A K : Set ℕ} {δ : ℕ}
    (hK : K.Infinite)
    (hlocal : ∀ b ∈ K, ∀ c ∈ K, b ≠ c →
      ∃ G ∈ additiveSupportFamily A 3 (b + c - δ),
        Disjoint (G : Set ℕ)
          ((({b, c} : Finset ℕ) : Set ℕ))) :
    ∃ L, L ⊆ K ∧ L.Infinite ∧
      ∀ b ∈ L, ∀ c ∈ L, b ≠ c →
        ∃ G ∈ additiveSupportFamily A 3 (b + c - δ),
          Disjoint (G : Set ℕ) L := by
  let HasRepair (P : Finset ℕ) : Prop :=
    ∃ G ∈ additiveSupportFamily A 3 (P.sum id - δ),
      Disjoint (G : Set ℕ) (P : Set ℕ)
  let chooseSupport (P : Finset ℕ) : Finset ℕ :=
    if h : HasRepair P then Classical.choose h else ∅
  let f : ℕ → ℕ → Finset ℕ := fun b c => chooseSupport {b, c}
  have hfsymm : ∀ b c, f b c = f c b := by
    intro b c
    have hp : ({b, c} : Finset ℕ) = {c, b} := by
      ext z
      simp [or_comm]
    simp only [f, hp]
  have hfRepair : ∀ b ∈ K, ∀ c ∈ K, b ≠ c →
      f b c ∈ additiveSupportFamily A 3 (b + c - δ) ∧
        Disjoint (f b c : Set ℕ)
          ((({b, c} : Finset ℕ) : Set ℕ)) := by
    intro b hbK c hcK hbc
    obtain ⟨G, hGR, hGbc⟩ := hlocal b hbK c hcK hbc
    have hHas : HasRepair {b, c} := by
      refine ⟨G, ?_, hGbc⟩
      simpa [hbc] using hGR
    have hspec : chooseSupport {b, c} ∈
          additiveSupportFamily A 3
            (({b, c} : Finset ℕ).sum id - δ) ∧
        Disjoint (chooseSupport {b, c} : Set ℕ)
          ((({b, c} : Finset ℕ) : Set ℕ)) := by
      simp only [chooseSupport, dif_pos hHas]
      exact Classical.choose_spec hHas
    change chooseSupport {b, c} ∈
          additiveSupportFamily A 3 (b + c - δ) ∧
        Disjoint (chooseSupport {b, c} : Set ℕ)
          ((({b, c} : Finset ℕ) : Set ℕ))
    simpa [hbc] using hspec
  have hfcard : ∀ b ∈ K, ∀ c ∈ K, b ≠ c →
      (f b c).card ≤ 3 := by
    intro b hbK c hcK hbc
    exact additiveSupportFamily_cardAtMost A 3 (b + c - δ)
      (f b c) (hfRepair b hbK c hcK hbc).1
  have hfavoid : ∀ b ∈ K, ∀ c ∈ K, b ≠ c →
      b ∉ f b c ∧ c ∉ f b c := by
    intro b hbK c hcK hbc
    have hdisj := (hfRepair b hbK c hcK hbc).2
    constructor
    · intro hb
      exact Set.disjoint_left.mp hdisj hb (by simp)
    · intro hc
      exact Set.disjoint_left.mp hdisj hc (by simp)
  obtain ⟨L, hLK, hL, hfree⟩ :=
    exists_infinite_freeSet_of_symmetric_bounded_pairMap
      hK f 3 hfsymm hfcard hfavoid
  refine ⟨L, hLK, hL, ?_⟩
  intro b hbL c hcL hbc
  exact ⟨f b c, (hfRepair b (hLK hbL) c (hLK hcL) hbc).1,
    hfree b hbL c hcL hbc⟩

open Classical in

theorem exists_infiniteDeletion_threeBasis_of_fixedPopularDifference
    {A : Set ℕ} {N₀ T δ : ℕ}
    (h0 : 0 ∈ A)
    (hcov : PairCovers A N₀)
    (hsumfree : ∀ a ∈ A, T ≤ a →
      ∀ u ∈ A, ∀ v ∈ A, 0 < u → 0 < v → u + v ≠ a)
    (hδ : 0 < δ)
    (hsupply : ∀ N, ∃ x, N ≤ x ∧ x ∈ A ∧ x + δ ∈ A) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) 3 := by
  have hbasis : IsExactTupleAsymptoticBasis A 2 := by
    refine ⟨N₀, ?_⟩
    intro n hn
    obtain ⟨x, hxA, y, hyA, hxy⟩ := hcov n hn
    refine ⟨![x, y], ?_, ?_⟩
    · intro i
      fin_cases i
      · exact hxA
      · exact hyA
    · simpa [Fin.sum_univ_two] using hxy
  obtain ⟨d, hdA, hdLarge⟩ :=
    hbasis.infinite.exists_gt (max T N₀)
  have hdPos : 0 < d := by omega
  let H : ℕ := max T (max (d + 1) (N₀ + d))
  obtain ⟨Braw, hBrawA, hBraw, h0Braw, hpredRaw⟩ :=
    fixed_difference_predecessor_deletion hδ hsupply
  let B₀ : Set ℕ := Braw \ Set.Iio (H + δ)
  have hB₀A : B₀ ⊆ A := fun b hb => hBrawA hb.1
  have hB₀ : B₀.Infinite :=
    hBraw.diff (Set.finite_Iio (H + δ))
  have h0B₀ : 0 ∉ B₀ := fun h => h0Braw h.1
  have hpredData : ∀ b ∈ B₀,
      b - δ ∈ A ∧ b - δ ∉ B₀ ∧ b - δ + δ = b ∧
        T ≤ b - δ ∧ d < b - δ ∧ N₀ + d ≤ b - δ := by
    intro b hbB₀
    obtain ⟨x, hxA, hxBraw, hxδ⟩ := hpredRaw b hbB₀.1
    have hxH : H ≤ x := by
      have hbLarge : H + δ ≤ b := Nat.le_of_not_gt hbB₀.2
      omega
    have hsub : b - δ = x := by omega
    rw [hsub]
    refine ⟨hxA, fun hxB₀ => hxBraw hxB₀.1, hxδ, ?_, ?_, ?_⟩
    · exact (le_max_left T (max (d + 1) (N₀ + d))).trans hxH
    · have := (le_max_left (d + 1) (N₀ + d)).trans
        ((le_max_right T (max (d + 1) (N₀ + d))).trans hxH)
      omega
    · exact (le_max_right (d + 1) (N₀ + d)).trans
        ((le_max_right T (max (d + 1) (N₀ + d))).trans hxH)
  let I : Finset ℕ := insert d ((Finset.range d).filter (· ∈ A))
  let target : ℕ → ℕ → ℕ := fun b a =>
    if a = d then b + (b - δ) else b + a
  have hlocalPoint : ∀ b ∈ B₀, ∀ a ∈ I,
      ∃ G ∈ additiveSupportFamily A 3 (target b a),
        Disjoint (G : Set ℕ) ({b} : Set ℕ) := by
    intro b hbB₀ a haI
    obtain ⟨hxA, hxB₀, hxδ, hxT, hxd, hxlarge⟩ :=
      hpredData b hbB₀
    by_cases had : a = d
    · subst a
      obtain ⟨G, hGR, hGb⟩ :=
        fixedDifference_crossTarget_has_endpointAvoidingTriple
          (A := A) (N₀ := N₀) (T := T) (δ := δ) (d := d)
          (x := b - δ) (y := b - δ)
          hcov hsumfree hdA hdPos hxA hxA hxT hxT hxd hxd hxlarge
      refine ⟨G, ?_, ?_⟩
      · have heq : (b - δ) + (b - δ) + δ =
            b + (b - δ) := by omega
        rw [show target b d = b + (b - δ) by simp [target]]
        rw [← heq]
        exact hGR
      · simpa [hxδ] using hGb
    · have haFilter :
          a ∈ (Finset.range d).filter (· ∈ A) := by
        simpa [I, had] using haI
      have haSmall : a < d := Finset.mem_range.mp
        (Finset.mem_filter.mp haFilter).1
      have haA : a ∈ A := (Finset.mem_filter.mp haFilter).2
      obtain ⟨G, hGR, hGb⟩ :=
        fixedDifference_smallShift_has_endpointAvoidingTriple
          (A := A) (N₀ := N₀) (δ := δ) (d := d)
          (x := b - δ) (a := a)
          hcov hdA hxA haA haSmall hxd hxlarge
      refine ⟨G, ?_, ?_⟩
      · have heq : (b - δ) + δ + a = b + a := by omega
        rw [show target b a = b + a by simp [target, had]]
        rw [← heq]
        exact hGR
      · simpa [hxδ] using hGb
  obtain ⟨K, hKB₀, hK, hpoint⟩ :=
    exists_infinite_freeSet_for_finitelyMany_pointwiseSupports
      (A := A) (I := I) (target := target) hB₀ hlocalPoint
  have hlocalPair : ∀ b ∈ K, ∀ c ∈ K, b ≠ c →
      ∃ G ∈ additiveSupportFamily A 3 (b + c - δ),
        Disjoint (G : Set ℕ)
          ((({b, c} : Finset ℕ) : Set ℕ)) := by
    intro b hbK c hcK hbc
    obtain ⟨hxbA, hxbB₀, hxbδ, hxbT, hxbd, hxblarge⟩ :=
      hpredData b (hKB₀ hbK)
    obtain ⟨hxcA, hxcB₀, hxcδ, hxcT, hxcd, hxclarge⟩ :=
      hpredData c (hKB₀ hcK)
    obtain ⟨G, hGR, hGbc⟩ :=
      fixedDifference_crossTarget_has_endpointAvoidingTriple
        (A := A) (N₀ := N₀) (T := T) (δ := δ) (d := d)
        (x := b - δ) (y := c - δ)
        hcov hsumfree hdA hdPos hxbA hxcA hxbT hxcT
        hxbd hxcd hxblarge
    refine ⟨G, ?_, ?_⟩
    · have htarget :
          (b - δ) + (c - δ) + δ = b + c - δ := by
        omega
      simpa [htarget] using hGR
    · simpa [hxbδ, hxcδ] using hGbc
  obtain ⟨B, hBK, hB, hpair⟩ :=
    exists_infinite_freeSet_for_shiftedPairSupports
      (A := A) (δ := δ) hK hlocalPair
  have hBA : B ⊆ A := hBK.trans (hKB₀.trans hB₀A)
  have hBB₀ : B ⊆ B₀ := hBK.trans hKB₀
  have h0B : 0 ∉ B := fun h => h0B₀ (hBB₀ h)
  have hunpack : ∀ n,
      (∃ G ∈ additiveSupportFamily A 3 n,
          Disjoint (G : Set ℕ) B) →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
    intro n hrep
    obtain ⟨v, hvAB, hvsum⟩ :=
      exists_surviving_additiveSupport_iff.mp hrep
    refine ⟨v 0, (hvAB 0).1, v 1, (hvAB 1).1,
      v 2, (hvAB 2).1, (hvAB 0).2, (hvAB 1).2,
      (hvAB 2).2, ?_⟩
    simpa [Fin.sum_univ_three] using hvsum
  refine ⟨B, hBA, hB, deletion_criterion_local h0 h0B hcov ?_⟩
  intro n hn
  rintro ⟨b, hbB, a, haA, hba⟩
  have hbK := hBK hbB
  obtain ⟨hxbA, hxbB₀, hxbδ, hxbT, hxbd, hxblarge⟩ :=
    hpredData b (hKB₀ hbK)
  let x := b - δ
  have hxA : x ∈ A := hxbA
  have hxB₀ : x ∉ B₀ := hxbB₀
  have hxB : x ∉ B := fun hx => hxB₀ (hBB₀ hx)
  have hxδ : x + δ = b := hxbδ
  by_cases haSmall : a < d
  · have haI : a ∈ I := by
      simp [I, haSmall, haA]
    have had : a ≠ d := by omega
    obtain ⟨G, hGR, hGK⟩ := hpoint b hbK a haI
    apply hunpack n
    refine ⟨G, ?_, hGK.mono_right hBK⟩
    rw [show target b a = b + a by simp [target, had], hba] at hGR
    exact hGR
  · have hda : d ≤ a := Nat.le_of_not_gt haSmall
    by_cases hselected : ∃ c ∈ B, c - δ = a
    · obtain ⟨c, hcB, hca⟩ := hselected
      by_cases hbc : b = c
      · subst c
        have hdI : d ∈ I := by simp [I]
        obtain ⟨G, hGR, hGK⟩ := hpoint b hbK d hdI
        apply hunpack n
        refine ⟨G, ?_, hGK.mono_right hBK⟩
        rw [show target b d = b + (b - δ) by simp [target],
          hca, hba] at hGR
        exact hGR
      · obtain ⟨G, hGR, hGB⟩ := hpair b hbB c hcB hbc
        apply hunpack n
        refine ⟨G, ?_, hGB⟩
        obtain ⟨hxcA, hxcB₀, hxcδ, hxcT, hxcd, hxclarge⟩ :=
          hpredData c (hBB₀ hcB)
        have hδc : δ ≤ c := by omega
        have htarget : b + c - δ = n := by
          calc
            b + c - δ = b + (c - δ) := Nat.add_sub_assoc hδc b
            _ = b + a := by rw [hca]
            _ = n := hba
        rw [htarget] at hGR
        exact hGR
    · obtain ⟨p, hpA, q, hqA, hpq⟩ :=
        hcov (a + δ) (by omega)
      have hpB : p ∉ B := by
        intro hp
        obtain ⟨hzA, hzB₀, hzδ, hzT, hzd, hzlarge⟩ :=
          hpredData p (hBB₀ hp)
        by_cases hq0 : q = 0
        · apply hselected
          exact ⟨p, hp, by omega⟩
        · have hqPos : 0 < q := Nat.pos_of_ne_zero hq0
          have hzPos : 0 < p - δ := by
            omega
          exact hsumfree a haA (by omega) (p - δ) hzA q hqA
            hzPos hqPos (by omega)
      have hqB : q ∉ B := by
        intro hq
        obtain ⟨hzA, hzB₀, hzδ, hzT, hzd, hzlarge⟩ :=
          hpredData q (hBB₀ hq)
        by_cases hp0 : p = 0
        · apply hselected
          exact ⟨q, hq, by omega⟩
        · have hpPos : 0 < p := Nat.pos_of_ne_zero hp0
          have hzPos : 0 < q - δ := by
            omega
          exact hsumfree a haA (by omega) p hpA (q - δ) hzA
            hpPos hzPos (by omega)
      exact ⟨x, hxA, p, hpA, q, hqA, hxB, hpB, hqB, by omega⟩

open Classical in
/-- In a genuine counterexample, every fixed positive difference occurs
only finitely often.  Unlike
`counterexample_basisDifference_edges_finite`, the difference need not
itself belong to `A`. -/
theorem counterexample_all_positiveDifference_edges_finite
    {A : Set ℕ} {N₀ δ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hδ : 0 < δ) :
    {x | x ∈ A ∧ x + δ ∈ A}.Finite := by
  apply Set.not_infinite.mp
  intro hedges
  obtain ⟨T, hsumfree⟩ :=
    counterexample_eventually_positive_sumFree h0 hcov hfail
  have hsupply : ∀ N, ∃ x, N ≤ x ∧ x ∈ A ∧ x + δ ∈ A := by
    intro N
    obtain ⟨x, hxEdges, hxN⟩ := hedges.exists_gt N
    exact ⟨x, hxN.le, hxEdges.1, hxEdges.2⟩
  obtain ⟨B, hBA, hB, hthree⟩ :=
    exists_infiniteDeletion_threeBasis_of_fixedPopularDifference
      h0 hcov hsumfree hδ hsupply
  exact hfail B hBA hB hthree

open Classical in

theorem crossGap_conflictingOffsets_finite
    {A : Set ℕ} {δ c : ℕ}
    (hδc : δ ≠ c)
    (hedges : ∀ r, 0 < r →
      {x | x ∈ A ∧ x + r ∈ A}.Finite) :
    {a | a ∈ A ∧ ∃ q ∈ A, a + δ = c + q}.Finite := by
  rcases lt_or_gt_of_ne hδc with hδltc | hcltδ
  · let r := c - δ
    have hrpos : 0 < r := by
      simp only [r]
      omega
    have hfinite : {q | q ∈ A ∧ q + r ∈ A}.Finite :=
      hedges r hrpos
    apply (hfinite.image (fun q => q + r)).subset
    intro a ha
    obtain ⟨haA, q, hqA, haq⟩ := ha
    have hqa : q + r = a := by
      simp only [r]
      omega
    exact ⟨q, ⟨hqA, hqa ▸ haA⟩, hqa⟩
  · let r := δ - c
    have hrpos : 0 < r := by
      simp only [r]
      omega
    have hfinite : {a | a ∈ A ∧ a + r ∈ A}.Finite :=
      hedges r hrpos
    apply hfinite.subset
    intro a ha
    obtain ⟨haA, q, hqA, haq⟩ := ha
    refine ⟨haA, ?_⟩
    have haq' : a + r = q := by
      simp only [r]
      omega
    exact haq' ▸ hqA

open Classical in
/-- A finite set of old endpoints creates only finitely many exceptional
offsets for a new gap `δ`, provided no old endpoint is literally equal to
`δ`.  This is the finite-union form needed in a block-by-block
construction. -/
theorem crossGap_conflictingOffsets_finite_prefix
    {A : Set ℕ} {δ : ℕ} {D : Finset ℕ}
    (hδD : ∀ c ∈ D, δ ≠ c)
    (hedges : ∀ r, 0 < r →
      {x | x ∈ A ∧ x + r ∈ A}.Finite) :
    {a | a ∈ A ∧ ∃ c ∈ D, ∃ q ∈ A, a + δ = c + q}.Finite := by
  induction D using Finset.induction_on with
  | empty =>
      simp
  | @insert c D hc ih =>
      have hcne : δ ≠ c := hδD c (Finset.mem_insert_self c D)
      have hDne : ∀ d ∈ D, δ ≠ d := by
        intro d hd
        exact hδD d (Finset.mem_insert_of_mem hd)
      have hcfinite :
          {a | a ∈ A ∧ ∃ q ∈ A, a + δ = c + q}.Finite :=
        crossGap_conflictingOffsets_finite hcne hedges
      have hDfinite :
          {a | a ∈ A ∧ ∃ d ∈ D, ∃ q ∈ A,
            a + δ = d + q}.Finite :=
        ih hDne
      apply (hcfinite.union hDfinite).subset
      intro a ha
      obtain ⟨haA, d, hd, q, hqA, haq⟩ := ha
      rcases Finset.mem_insert.mp hd with hdc | hdD
      · subst d
        exact Or.inl ⟨haA, q, hqA, haq⟩
      · exact Or.inr ⟨haA, d, hdD, q, hqA, haq⟩

open Classical in

theorem equalGap_genericRisk_has_prefixAvoidingTriple
    {A : Set ℕ} {N₀ T δ x a : ℕ} {D : Finset ℕ}
    (hcov : PairCovers A N₀)
    (hsumfree : ∀ n ∈ A, T ≤ n →
      ∀ u ∈ A, ∀ v ∈ A, 0 < u → 0 < v → u + v ≠ n)
    (hδpos : 0 < δ) (hcover : N₀ ≤ a + δ)
    (hxA : x ∈ A) (hxpos : 0 < x)
    (haA : a ∈ A) (haT : T ≤ a) (hax : a ≠ x)
    (hxD : x ∉ D)
    (hgeneric : ¬∃ c ∈ D, ∃ q ∈ A, a + δ = c + q) :
    ∃ p ∈ A, ∃ q ∈ A,
      x ∉ insert (x + δ) D ∧
      p ∉ insert (x + δ) D ∧
      q ∉ insert (x + δ) D ∧
      x + p + q = (x + δ) + a := by
  obtain ⟨p, hpA, q, hqA, hpq⟩ := hcov (a + δ) hcover
  have hpb : p ≠ x + δ := by
    intro hpb
    have hxq : x + q = a := by omega
    have hqpos : 0 < q := by
      by_contra hq0
      have hqzero : q = 0 := Nat.eq_zero_of_not_pos hq0
      exact hax (by omega)
    exact hsumfree a haA haT x hxA q hqA hxpos hqpos hxq
  have hqb : q ≠ x + δ := by
    intro hqb
    have hxp : x + p = a := by omega
    have hppos : 0 < p := by
      by_contra hp0
      have hpzero : p = 0 := Nat.eq_zero_of_not_pos hp0
      exact hax (by omega)
    exact hsumfree a haA haT x hxA p hpA hxpos hppos hxp
  have hpD : p ∉ D := by
    intro hpD
    exact hgeneric ⟨p, hpD, q, hqA, by omega⟩
  have hqD : q ∉ D := by
    intro hqD
    exact hgeneric ⟨q, hqD, p, hpA, by omega⟩
  refine ⟨p, hpA, q, hqA, ?_, ?_, ?_, by omega⟩
  · simp only [Finset.mem_insert, not_or]
    exact ⟨by omega, hxD⟩
  · simp [hpb, hpD]
  · simp [hqb, hqD]

open Classical in

theorem equalGap_pairSurvival_has_prefixAvoidingTriple
    {A : Set ℕ} {T δ x a : ℕ} {D : Finset ℕ}
    (hsumfree : ∀ n ∈ A, T ≤ n →
      ∀ u ∈ A, ∀ v ∈ A, 0 < u → 0 < v → u + v ≠ n)
    (hδpos : 0 < δ)
    (hxA : x ∈ A) (hxpos : 0 < x)
    (haA : a ∈ A) (haT : T ≤ a) (hax : a ≠ x)
    (hxD : x ∉ D)
    (hsurvive : ¬ DestroysAt (additiveSupportFamily A 2)
      (D : Set ℕ) (a + δ)) :
    ∃ p ∈ A, ∃ q ∈ A,
      x ∉ insert (x + δ) D ∧
      p ∉ insert (x + δ) D ∧
      q ∉ insert (x + δ) D ∧
      x + p + q = (x + δ) + a := by
  obtain ⟨E, hER, hED⟩ := not_destroysAt_iff.mp hsurvive
  obtain ⟨v, hvAD, hvsum⟩ :=
    exists_surviving_additiveSupport_iff.mp ⟨E, hER, hED⟩
  let p := v 0
  let q := v 1
  have hpA : p ∈ A := (hvAD 0).1
  have hqA : q ∈ A := (hvAD 1).1
  have hpD : p ∉ D := (hvAD 0).2
  have hqD : q ∉ D := (hvAD 1).2
  have hpq : p + q = a + δ := by
    simpa [p, q, Fin.sum_univ_two] using hvsum
  have hpb : p ≠ x + δ := by
    intro hpb
    have hxq : x + q = a := by omega
    have hqpos : 0 < q := by
      by_contra hq0
      have hqzero : q = 0 := Nat.eq_zero_of_not_pos hq0
      exact hax (by omega)
    exact hsumfree a haA haT x hxA q hqA hxpos hqpos hxq
  have hqb : q ≠ x + δ := by
    intro hqb
    have hxp : x + p = a := by omega
    have hppos : 0 < p := by
      by_contra hp0
      have hpzero : p = 0 := Nat.eq_zero_of_not_pos hp0
      exact hax (by omega)
    exact hsumfree a haA haT x hxA p hpA hxpos hppos hxp
  refine ⟨p, hpA, q, hqA, ?_, ?_, ?_, by omega⟩
  · simp only [Finset.mem_insert, not_or]
    exact ⟨by omega, hxD⟩
  · simp [hpb, hpD]
  · simp [hqb, hqD]

open Classical in

theorem pairDestroyed_shiftOffsets_finite
    {A : Set ℕ} {N₀ δ : ℕ} {D : Finset ℕ}
    (hcov : PairCovers A N₀) (hδN : N₀ ≤ δ)
    (hδD : ∀ c ∈ D, δ ≠ c)
    (hedges : ∀ r, 0 < r →
      {x | x ∈ A ∧ x + r ∈ A}.Finite) :
    {a | a ∈ A ∧
      DestroysAt (additiveSupportFamily A 2)
        (D : Set ℕ) (a + δ)}.Finite := by
  have hcollision :
      {a | a ∈ A ∧ ∃ c ∈ D, ∃ q ∈ A,
        a + δ = c + q}.Finite :=
    crossGap_conflictingOffsets_finite_prefix hδD hedges
  apply hcollision.subset
  intro a ha
  obtain ⟨p, hpA, q, hqA, hpq⟩ :=
    hcov (a + δ) (by omega)
  have hpLe : p ≤ a + δ := by omega
  have hpair :
      pairSupport (a + δ) p ∈
        additiveSupportFamily A 2 (a + δ) := by
    apply pairSupport_mem_additiveSupportFamily hpLe hpA
    have hsub : a + δ - p = q := by omega
    simpa [hsub] using hqA
  obtain ⟨z, hzPair, hzD⟩ :=
    Set.not_disjoint_iff.mp (ha.2 (pairSupport (a + δ) p) hpair)
  have hzCases : z = p ∨ z = a + δ - p := by
    simpa [pairSupport] using hzPair
  rcases hzCases with hzp | hzq
  · subst z
    exact ⟨ha.1, p, hzD, q, hqA, hpq.symm⟩
  · rw [hzq] at hzD
    exact ⟨ha.1, a + δ - p, hzD, p, hpA, by omega⟩

open Classical in
/-- In a global counterexample the preceding finite cross-gap conclusion is
automatic, because every fixed positive difference has already been proved
to occur only finitely often. -/
theorem counterexample_crossGap_conflictingOffsets_finite_prefix
    {A : Set ℕ} {N₀ δ : ℕ} {D : Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hδD : ∀ c ∈ D, δ ≠ c) :
    {a | a ∈ A ∧ ∃ c ∈ D, ∃ q ∈ A,
      a + δ = c + q}.Finite := by
  apply crossGap_conflictingOffsets_finite_prefix hδD
  intro r hr
  exact counterexample_all_positiveDifference_edges_finite
    h0 hcov hfail hr

open Classical in

theorem crossGap_finiteException_can_genuinely_stall :
    let S : Finset ℕ := {0, 1, 5, 8, 11, 15}
    (∀ n ∈ S, 0 < n →
      ∀ u ∈ S, ∀ v ∈ S, 0 < u → 0 < v → u + v ≠ n) ∧
    (5 ∈ S ∧ 1 ∈ ({1} : Finset ℕ) ∧ 8 ∈ S ∧ 5 + 4 = 1 + 8) ∧
    ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S,
      p ∉ insert 15 ({1} : Finset ℕ) →
      q ∉ insert 15 ({1} : Finset ℕ) →
      r ∉ insert 15 ({1} : Finset ℕ) →
      p + q + r ≠ 20 := by
  decide

open Classical in
/-- The fixed-offset case of `fixed_offset_or_growing` is impossible in a
counterexample.  Thus any unbounded multiplicity of difference edges must
escape through arbitrarily large differences. -/
theorem counterexample_differenceMultiplicity_mustGrow
    {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hdiff : ∀ K, ∃ δ, 1 ≤ δ ∧ ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A) :
    ∀ Δ K, ∃ δ, Δ < δ ∧ ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A := by
  rcases fixed_offset_or_growing hdiff with hfixed | hgrowing
  · obtain ⟨δ, hδ, hpopular⟩ := hfixed
    have hfinite :
        {x | x ∈ A ∧ x + δ ∈ A}.Finite :=
      counterexample_all_positiveDifference_edges_finite
        h0 hcov hfail hδ
    obtain ⟨V, hVcard, hV⟩ :=
      hpopular (hfinite.toFinset.card + 1)
    have hsub : V ⊆ hfinite.toFinset := by
      intro x hxV
      simpa using hV x hxV
    have := Finset.card_le_card hsub
    omega
  · exact hgrowing

/-- Cancelling two routes through the same moving required element turns the gap
between their anchors into a fixed difference between their co-parts. -/
theorem equalRequiredElementRoutes_force_coPartDifference
    {r s b u v n : ℕ}
    (hrs : r ≤ s) (hr : r + b + u = n) (hs : s + b + v = n) :
    v + (s - r) = u := by
  omega

/-- If the later anchor was chosen beyond every possible co-part of the
earlier route, the two routes cannot hit the same moving required element. -/
theorem separatedRequiredElementRoutes_impossible
    {r s b u v n U : ℕ}
    (hsep : r + U + 1 ≤ s) (hu : u ≤ U)
    (hr : r + b + u = n) (hs : s + b + v = n) :
    False := by
  omega

open Classical in

theorem threeAnchor_forbids_terminalPrivateDestructions
    {A : Set ℕ} {N₀ T : ℕ}
    (hcov : PairCovers A N₀)
    (hsumfree : ∀ a ∈ A, T ≤ a →
      ∀ u ∈ A, ∀ v ∈ A, 0 < u → 0 < v → u + v ≠ a)
    (hedges : ∀ g, 0 < g →
      {x | x ∈ A ∧ x + g ∈ A}.Finite)
    (D : Finset ℕ)
    (hwounds : ∀ b ∈ A, 0 < b → (∀ d ∈ D, d < b) →
      ∃ n, N₀ ≤ n ∧ b ≤ n ∧
        (∃ d ∈ insert b D, ∃ a ∈ A, d + a = n) ∧
        IsPrivateTriple (A \ (D : Set ℕ)) b n) :
    False := by
  let Dmax := D.sup id
  have hDle : ∀ d ∈ D, d ≤ Dmax := by
    intro d hdD
    exact Finset.le_sup (f := id) hdD
  have hedgeBounded : ∀ g, ∃ U, 0 < g →
      ∀ x ∈ A, x + g ∈ A → x ≤ U := by
    intro g
    by_cases hg : 0 < g
    · obtain ⟨U, hU⟩ := (hedges g hg).bddAbove
      exact ⟨U, fun _ x hxA hxgA => hU ⟨hxA, hxgA⟩⟩
    · exact ⟨0, fun h => absurd h hg⟩
  choose edgeBound hedgeBound using hedgeBounded
  obtain ⟨r₀, hr₀A, hr₀large⟩ :=
    pairCovers_unbounded hcov (max T Dmax + 1)
  obtain ⟨r₁, hr₁A, hr₁large⟩ :=
    pairCovers_unbounded hcov (r₀ + Dmax + 1)
  have hr₀pos : 0 < r₀ := by omega
  have hr₁pos : 0 < r₁ := by omega
  have hr₀T : T ≤ r₀ := by omega
  have hr₁T : T ≤ r₁ := by omega
  have hr₀D : r₀ ∉ D := by
    intro hr₀mem
    have := hDle r₀ hr₀mem
    omega
  have hr₁D : r₁ ∉ D := by
    intro hr₁mem
    have := hDle r₁ hr₁mem
    omega
  have hg₀₁pos : 0 < r₁ - r₀ := by omega
  obtain ⟨U₀₁, hU₀₁⟩ :=
    (hedges (r₁ - r₀) hg₀₁pos).bddAbove
  obtain ⟨r₂, hr₂A, hr₂large⟩ :=
    pairCovers_unbounded hcov
      (max (r₁ + Dmax + 1) (r₁ + U₀₁ + 1))
  have hr₂pos : 0 < r₂ := by omega
  have hr₂T : T ≤ r₂ := by omega
  have hr₂D : r₂ ∉ D := by
    intro hr₂mem
    have := hDle r₂ hr₂mem
    omega
  have hDmaxr₀ : Dmax < r₀ := by omega
  have hDmaxr₁ : Dmax < r₁ := by omega
  have hDmaxr₂ : Dmax < r₂ := by omega
  have hr₀le₂ : r₀ ≤ r₂ := by omega
  have hr₁le₂ : r₁ ≤ r₂ := by omega
  let H := r₂ + Dmax
  let U := (Finset.range (H + 1)).sup edgeBound
  have hboundedEdge :
      ∀ g, 0 < g → g ≤ H →
        ∀ x ∈ A, x + g ∈ A → x ≤ U := by
    intro g hgpos hgH x hxA hxgA
    have hxBound := hedgeBound g hgpos x hxA hxgA
    have hgRange : g ∈ Finset.range (H + 1) :=
      Finset.mem_range.2 (by omega)
    have htoSup : edgeBound g ≤ U := by
      dsimp only [U]
      exact Finset.le_sup (f := edgeBound) hgRange
    exact hxBound.trans htoSup
  obtain ⟨b, hbA, hbLarge⟩ :=
    pairCovers_unbounded hcov
      (max (N₀ + r₂) (U + r₂ + 2 * Dmax + 1))
  have hbpos : 0 < b := by omega
  have hbAboveD : ∀ d ∈ D, d < b := by
    intro d hdD
    have := hDle d hdD
    omega
  have hr₀b : r₀ < b := by omega
  have hr₁b : r₁ < b := by omega
  have hr₂b : r₂ < b := by omega
  obtain ⟨n, hnN, hbn, hrisk, hprivate⟩ :=
    hwounds b hbA hbpos hbAboveD
  have hroute : ∀ r, r ∈ A → r ∉ D → r < b → r ≤ r₂ →
      (∃ u ∈ A, r + b + u = n) ∨
      ∃ c ∈ D, ∃ u ∈ A, r + c + u = n := by
    intro r hrA hrD hrb hr₂
    obtain ⟨p, hpA, q, hqA, hpq⟩ :=
      hcov (n - r) (by omega)
    have hrpq : r + p + q = n := by omega
    by_cases hpD : p ∈ D
    · exact Or.inr ⟨p, hpD, q, hqA, hrpq⟩
    · by_cases hqD : q ∈ D
      · exact Or.inr ⟨q, hqD, p, hpA, by omega⟩
      · have hrS : r ∈ A \ (D : Set ℕ) :=
          ⟨hrA, by simpa using hrD⟩
        have hpS : p ∈ A \ (D : Set ℕ) :=
          ⟨hpA, by simpa using hpD⟩
        have hqS : q ∈ A \ (D : Set ℕ) :=
          ⟨hqA, by simpa using hqD⟩
        rcases hprivate.2 r hrS p hpS q hqS hrpq with
          hrEq | hpEq | hqEq
        · exact absurd hrEq (ne_of_lt hrb)
        · subst p
          exact Or.inl ⟨q, hqA, by omega⟩
        · subst q
          exact Or.inl ⟨p, hpA, by omega⟩
  have hroute₀ := hroute r₀ hr₀A hr₀D hr₀b (by omega)
  have hroute₁ := hroute r₁ hr₁A hr₁D hr₁b (by omega)
  have hroute₂ := hroute r₂ hr₂A hr₂D hr₂b le_rfl
  have holdRoutesContradict :
      ∀ r s, r + Dmax < s → s ≤ r₂ →
        (∃ c ∈ D, ∃ u ∈ A, r + c + u = n) →
        (∃ c ∈ D, ∃ u ∈ A, s + c + u = n) →
        False := by
    intro r s hrs hs₂ hrOld hsOld
    obtain ⟨c, hcD, u, huA, hrcu⟩ := hrOld
    obtain ⟨c', hc'D, v, hvA, hscv⟩ := hsOld
    have hcLe := hDle c hcD
    have hc'Le := hDle c' hc'D
    let g := (s + c') - (r + c)
    have hgpos : 0 < g := by
      dsimp only [g]
      omega
    have hgH : g ≤ H := by
      dsimp only [g, H]
      omega
    have hvLarge : U < v := by
      have hbThreshold :
          U + r₂ + 2 * Dmax + 1 ≤ b := by
        exact (le_max_right (N₀ + r₂)
          (U + r₂ + 2 * Dmax + 1)).trans hbLarge
      omega
    have hvg : v + g = u := by
      dsimp only [g]
      omega
    have hvBound : v ≤ U :=
      hboundedEdge g hgpos hgH v hvA (by
        rw [hvg]
        exact huA)
    omega
  obtain ⟨d, hdInsert, a, haA, hda⟩ := hrisk
  rcases Finset.mem_insert.1 hdInsert with hdb | hdD
  · subst d
    have hselfRoute :
        ∀ r u, r ∈ A → T ≤ r → 0 < r → u ∈ A →
          r + b + u = n → b + a = n → a = r := by
      intro r u hrA hrT hrpos huA hrbu hba
      have haru : r + u = a := by omega
      rcases Nat.eq_zero_or_pos u with hu0 | hupos
      · omega
      · exact absurd haru
          (hsumfree a haA (by omega)
            r hrA u huA hrpos hupos)
    rcases hroute₀ with hr₀Self | hr₀Old
    · obtain ⟨u₀, hu₀A, hr₀bu⟩ := hr₀Self
      have ha₀ := hselfRoute r₀ u₀ hr₀A hr₀T hr₀pos
        hu₀A hr₀bu hda
      rcases hroute₁ with hr₁Self | hr₁Old
      · obtain ⟨u₁, hu₁A, hr₁bu⟩ := hr₁Self
        have ha₁ := hselfRoute r₁ u₁ hr₁A hr₁T hr₁pos
          hu₁A hr₁bu hda
        omega
      · rcases hroute₂ with hr₂Self | hr₂Old
        · obtain ⟨u₂, hu₂A, hr₂bu⟩ := hr₂Self
          have ha₂ := hselfRoute r₂ u₂ hr₂A hr₂T hr₂pos
            hu₂A hr₂bu hda
          omega
        · exact holdRoutesContradict r₁ r₂ (by omega) le_rfl
            hr₁Old hr₂Old
    · rcases hroute₁ with hr₁Self | hr₁Old
      · obtain ⟨u₁, hu₁A, hr₁bu⟩ := hr₁Self
        have ha₁ := hselfRoute r₁ u₁ hr₁A hr₁T hr₁pos
          hu₁A hr₁bu hda
        rcases hroute₂ with hr₂Self | hr₂Old
        · obtain ⟨u₂, hu₂A, hr₂bu⟩ := hr₂Self
          have ha₂ := hselfRoute r₂ u₂ hr₂A hr₂T hr₂pos
            hu₂A hr₂bu hda
          omega
        · exact holdRoutesContradict r₀ r₂ (by omega) le_rfl
            hr₀Old hr₂Old
      · exact holdRoutesContradict r₀ r₁ (by omega) (by omega)
          hr₀Old hr₁Old
  · have hdLe := hDle d hdD
    have hcollateralOldImpossible :
        ∀ r, Dmax < r → r ≤ r₂ →
          (∃ c ∈ D, ∃ u ∈ A, r + c + u = n) → False := by
      intro r hrDmax hr₂ oldRoute
      obtain ⟨c, hcD, u, huA, hrcu⟩ := oldRoute
      have hcLe := hDle c hcD
      let g := r + c - d
      have hgpos : 0 < g := by
        dsimp only [g]
        omega
      have hgH : g ≤ H := by
        dsimp only [g, H]
        omega
      have huLarge : U < u := by
        have hbThreshold :
            U + r₂ + 2 * Dmax + 1 ≤ b := by
          exact (le_max_right (N₀ + r₂)
            (U + r₂ + 2 * Dmax + 1)).trans hbLarge
        omega
      have hug : u + g = a := by
        dsimp only [g]
        omega
      have huBound : u ≤ U :=
        hboundedEdge g hgpos hgH u huA (by
          rw [hug]
          exact haA)
      omega
    have hr₀Self : ∃ u ∈ A, r₀ + b + u = n := by
      rcases hroute₀ with h | h
      · exact h
      · exact
          (hcollateralOldImpossible r₀ hDmaxr₀ hr₀le₂ h).elim
    have hr₁Self : ∃ u ∈ A, r₁ + b + u = n := by
      rcases hroute₁ with h | h
      · exact h
      · exact
          (hcollateralOldImpossible r₁ hDmaxr₁ hr₁le₂ h).elim
    have hr₂Self : ∃ u ∈ A, r₂ + b + u = n := by
      rcases hroute₂ with h | h
      · exact h
      · exact
          (hcollateralOldImpossible r₂ hDmaxr₂ le_rfl h).elim
    obtain ⟨u₀, hu₀A, hr₀bu⟩ := hr₀Self
    obtain ⟨u₁, hu₁A, hr₁bu⟩ := hr₁Self
    obtain ⟨u₂, hu₂A, hr₂bu⟩ := hr₂Self
    have hu₁edge : u₁ + (r₁ - r₀) = u₀ :=
      equalRequiredElementRoutes_force_coPartDifference
        (by omega) hr₀bu hr₁bu
    have hu₁Bound : u₁ ≤ U₀₁ :=
      hU₀₁ ⟨hu₁A, by
        rw [hu₁edge]
        exact hu₀A⟩
    exact separatedRequiredElementRoutes_impossible
      (le_max_right (r₁ + Dmax + 1) (r₁ + U₀₁ + 1) |>.trans
        hr₂large)
      hu₁Bound hr₁bu hr₂bu

open Classical in

theorem exists_infiniteDeletion_threeBasis_of_pairCovers
    {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) 3 := by
  by_contra hno
  push Not at hno
  have hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3 := by
    intro B hBA hBinf
    exact hno B hBA hBinf
  obtain ⟨D, _hserved, _h0D, hwounds⟩ :=
    counterexample_terminal_prefix_private_destruction_fork h0 hcov hfail
  obtain ⟨T, hsumfree⟩ :=
    counterexample_eventually_positive_sumFree h0 hcov hfail
  have hedges : ∀ g, 0 < g →
      {x | x ∈ A ∧ x + g ∈ A}.Finite := by
    intro g hg
    exact counterexample_all_positiveDifference_edges_finite
      h0 hcov hfail hg
  exact threeAnchor_forbids_terminalPrivateDestructions
    hcov hsumfree hedges D (by
      intro b hbA hbpos hbAbove
      obtain ⟨n, hnN, hbn, hrisk, hprivate, _hfork⟩ :=
        hwounds b hbA hbpos hbAbove
      exact ⟨n, hnN, hbn, hrisk, hprivate⟩)

/-- The zero-normalized order-two instance of Erdős 881. -/
theorem erdos881_zero_normalized :
    ∀ A : Set ℕ, 0 ∈ A →
      IsStronglyMinimalExactBasis A 2 →
      ∃ B, B ⊆ A ∧ B.Infinite ∧
        IsExactTupleAsymptoticBasis (A \ B) 3 := by
  intro A h0 hminimal
  obtain ⟨N₀, hcov⟩ :=
    pairCovers_of_exactTupleBasis hminimal.1
  exact exists_infiniteDeletion_threeBasis_of_pairCovers h0 hcov

theorem erdos881 :
    ∀ A : Set ℕ, IsStronglyMinimalExactBasis A 2 →
      ∃ B, B ⊆ A ∧ B.Infinite ∧
        IsExactTupleAsymptoticBasis (A \ B) 3 :=
  erdos881_of_zero_normalized erdos881_zero_normalized

end Erdos881
