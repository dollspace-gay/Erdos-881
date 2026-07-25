/-
# The ordinal rank of the freeness tree

The rep-free finite subsets of a counterexample's basis form a tree
under extension-by-a-larger-element.  `free_prefixes_die_of_hfail`
says every branch dies; here that becomes a well-founded relation
(`freeStep_wf`) carrying an ordinal rank that every extension
strictly decreases (`exists_strict_rank`).

This is the formal centerpiece of the rank program
(docs/rank-program.md): the floods are the stalled nodes of this
tree, and a proof that some verified operation drives the rank down
past every ordinal would refute the counterexample outright.
-/

import Erdos881.DisjointRepEngine

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

/-- **The freeness tree is well-founded.**  An infinite ascending
chain of free extensions would glue (initial node, then the picks)
into one strictly monotone positive sequence all of whose finite
prefixes are free — exactly what `free_prefixes_die_of_hfail`
forbids in a counterexample. -/
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

/-- **THE RANK EXISTS.**  In a counterexample there is an
ordinal-valued rank on finite sets that every free extension
strictly decreases: the formal centerpiece of the rank program.
Any verified operation shown to drive this rank below every bound
refutes the counterexample. -/
theorem exists_strict_rank {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ ρ : Finset ℕ → Ordinal.{0},
      ∀ P Q, FreeStep A N₀ Q P → ρ Q < ρ P := by
  have hwf := freeStep_wf h0 hcov hfail
  exact ⟨fun P => (hwf.apply P).rank,
    fun P Q h => Acc.rank_lt_of_rel (hwf.apply P) h⟩

/-- **The leaf law.**  For a free node `P` and an admissible new
element `b`, the extension `P ∪ {b}` leaves the tree EXACTLY when
`b` completes a rep hub over `P` at some late target: the boundary
of the freeness tree consists precisely of the flood's hubs.  Rank
measures distance to the hub boundary. -/
theorem freeNode_extension_iff {A : Set ℕ} {N₀ : ℕ} {P : Finset ℕ}
    {b : ℕ} (hP : FreeNode A N₀ P) (hbA : b ∈ A) (hbpos : 0 < b) :
    ¬FreeNode A N₀ (insert b P) ↔
      ∃ m, N₀ ≤ m ∧ IsRepHub A m (insert b P) := by
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
    push_neg at hnotfree
    obtain ⟨m, hm, hall⟩ := hnotfree
    refine ⟨m, hm, ?_⟩
    intro x hx y hy z hz hsum
    by_contra hmiss
    push_neg at hmiss
    obtain ⟨hxm, hym, hzm⟩ := hmiss
    exact hzm (hall x hx y hy z hz hsum hxm hym)
  · rintro ⟨m, hm, hhub⟩ ⟨-, hfree⟩
    obtain ⟨x, hx, y, hy, z, hz, hsum, hxP, hyP, hzP⟩ := hfree m hm
    rcases hhub x hx y hy z hz hsum with h | h | h
    · exact hxP h
    · exact hyP h
    · exact hzP h

/-- A stalled node: free, but no extension by a large positive
basis element stays free.  The rep flood asserts such nodes exist;
the leaf law identifies their boundary with hubs. -/
def Stalled (A : Set ℕ) (N₀ X : ℕ) (P : Finset ℕ) : Prop :=
  FreeNode A N₀ P ∧
  ∀ b, b ∈ A → 0 < b → X ≤ b → ¬RepFree A N₀ (insert b P)

/-- **Stalledness is hereditary.**  Not-free is upward closed, so
every tree child of a stalled node is stalled at the same
threshold: once the dodge is trapped, it stays trapped. -/
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

/-- **The stalled zone is shallow.**  Every ascending free chain
from a stalled node has length at most `|A ∩ [0, X)|`: all its
picks are distinct positive basis elements below the stall
threshold.  Stalled nodes sit at finite depth above the tree's hub
boundary — the flood's envelopes are the finite-rank zone. -/
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
    push_neg at hbX
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

/-- **The flood is a stalled node.**  The positive-pool rep flood
hands the freeness tree an explicit stalled node: its envelope is
free with positive basis elements, and every large positive element
completes a hub over it, killing the extension.  Together with
`stalled_chain_bound` and `exists_strict_rank`: a counterexample's
freeness tree contains a hereditarily-trapped, finite-depth zone,
and the flood's guardians patrol its boundary. -/
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
    rep_flood_pool (P₀ := {a | a ∈ A ∧ 0 < a}) h0 hcov
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

/-- **The root-rank dichotomy.**  Either free sets have unbounded
cardinality — every free set is reachable by a chain from the empty
node (freeness is downward closed), so the tree has arbitrarily
long chains and the root's ordinal rank is at least `ω` — or there
is a uniform bound `D` and EVERY set of `D + 1` positive basis
elements is a rep hub of some late target: universal hubbing at one
fixed size.  (The second branch collides with the Ramsey ladder's
hub-free subsequences arity by arity.) -/
theorem root_rank_dichotomy (A : Set ℕ) (N₀ : ℕ) :
    (∀ n, ∃ P : Finset ℕ, FreeNode A N₀ P ∧ n ≤ P.card) ∨
    (∃ D, ∀ S : Finset ℕ, (∀ h ∈ S, h ∈ A ∧ 0 < h) →
      S.card = D + 1 → ∃ m, N₀ ≤ m ∧ IsRepHub A m S) := by
  classical
  by_cases hub : ∀ n, ∃ P : Finset ℕ, FreeNode A N₀ P ∧ n ≤ P.card
  · exact Or.inl hub
  · right
    push_neg at hub
    obtain ⟨D, hD⟩ := hub
    refine ⟨D, fun S hSpos hScard => ?_⟩
    have hnotfree : ¬RepFree A N₀ S := by
      intro hfree
      have := hD S ⟨hSpos, hfree⟩
      omega
    rw [RepFree] at hnotfree
    push_neg at hnotfree
    obtain ⟨m, hm, hall⟩ := hnotfree
    refine ⟨m, hm, ?_⟩
    intro x hx y hy z hz hsum
    by_contra hmiss
    push_neg at hmiss
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

/-- **Every ℵ₀-minimal basis carries a well-founded pair-freeness
tree** — no counterexample hypothesis anywhere.  Its ordinal rank
is a new invariant of minimal bases. -/
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

/-- **The order-2 rank of a minimal basis.**  Every ℵ₀-minimal
order-2 covering set carries an ordinal-valued invariant: the rank
of its pair-freeness tree, strictly decreasing along free
extensions.  A structural invariant of ALL minimal bases, born from
the Erdős 881 campaign. -/
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

/-- **THE REDUCTION.**  No sequence of pools can have strictly
descending root ranks: ordinal descent terminates.  Consequently,
if any verified pool operation (removing an envelope, passing to
guardians, passing to coreps, …) is ever shown to STRICTLY drop the
pool tree's root rank along its own iterates, the counterexample is
refuted outright and Erdős 881 (k = 2) is solved positively.  The
entire remaining problem is compressed into finding one
rank-dropping operation. -/
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

/-- **Pool ranks are monotone.**  A sub-pool's tree is a subtree,
so its root rank never exceeds the larger pool's.  The reduction's
open question is exactly: which verified pool operation makes this
inequality STRICT along its own iterates? -/
theorem pool_rank_mono {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {P₀ P₀' : Set ℕ} (hsub : P₀' ⊆ P₀) :
    ((poolFreeStep_wf h0 hcov hfail P₀').apply ∅).rank ≤
    ((poolFreeStep_wf h0 hcov hfail P₀).apply ∅).rank :=
  rank_le_of_subrel
    (fun _ _ h => ⟨h.1, fun a ha => hsub (h.2 a ha)⟩) _ _

/-- **Pool ranks are strictly positive.**  Root rank zero would
mean no pool element extends the empty node — every large pool
element a positive singleton hub — which the private-stream kill
forbids.  With anchors, every unbounded 0-free pool's tree has
rank at least one: the rank interval `(0, root]` is where the
descent must happen. -/
theorem pool_rank_pos {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
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
    push_neg at hno
    refine singleton_hubs_refuted h0 hcov hanchor hfail ?_
    intro N
    obtain ⟨b, hbP, hNb⟩ := hunb (max N 1)
    have hbpos : 0 < b := by
      rcases Nat.eq_zero_or_pos b with h | h
      · exact absurd (h ▸ hbP) h0P
      · exact h
    have hnotfree := hno b hbP hbpos
    rw [RepFree] at hnotfree
    push_neg at hnotfree
    obtain ⟨m, hm, hall⟩ := hnotfree
    have hhub : IsRepHub A m {b} := by
      intro x hx y hy z hz hsum
      by_contra hmiss
      push_neg at hmiss
      obtain ⟨hxm, hym, hzm⟩ := hmiss
      exact hzm (hall x hx y hy z hz hsum hxm hym)
    -- the target dominates the guardian, so targets are cofinal
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

/-- **Size-to-rank.**  A free pool set of cardinality `n` puts `n`
below the pool tree's root rank: its sorted prefixes form a free
chain of length `n` from the empty node.  Hub-free sets from the
Ramsey ladder are rank certificates, and unbounded free
cardinalities force root rank `≥ ω`. -/
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
        rw [Nat.cast_succ, Ordinal.add_one_eq_succ]
      rw [h2]
      exact Order.succ_le_of_lt h1
  have h0pre : pre 0 = ∅ := by
    show (Finset.range 0).image e = ∅
    simp
  have := hrank n 0 (by omega)
  rw [h0pre] at this
  exact this

/-- **Rank-to-size.**  Conversely, rank at least `n` above a node
yields a free pool superset with `n` more elements: below `ω`, the
pool tree's root rank IS the supremum of free-set cardinalities.
The ordinal invariant is arithmetic in its finite regime. -/
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

/-- Hub-freeness of a set is exactly rep-freeness: `S` is rep-free
iff no late target has `S` as a full hub. -/
theorem repFree_iff_no_hub {A : Set ℕ} {N₀ : ℕ} {S : Finset ℕ} :
    RepFree A N₀ S ↔ ¬∃ m, N₀ ≤ m ∧ IsRepHub A m S := by
  constructor
  · rintro hfree ⟨m, hm, hhub⟩
    obtain ⟨x, hx, y, hy, z, hz, hs, hxS, hyS, hzS⟩ := hfree m hm
    rcases hhub x hx y hy z hz hs with h | h | h
    · exact hxS h
    · exact hyS h
    · exact hzS h
  · intro hno m hm
    by_contra hall
    push_neg at hall
    refine hno ⟨m, hm, ?_⟩
    intro x hx y hy z hz hs
    by_contra hmiss
    push_neg at hmiss
    obtain ⟨h1, h2, h3⟩ := hmiss
    exact h3 (hall x hx y hy z hz hs h1 h2)

/-- **The ladder certifies rank.**  Along any ground stream inside
a pool, the escalation either produces a clique (arity two or
three) or hands the pool tree a rank certificate: a hub-free triple
is a free 3-set, so the root rank is at least 3.  Every further
Ramsey rung raises the certificate by one; low-rank pools force
cliques at low arity. -/
theorem escalation_rank_certificate {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {P₀ : Set ℕ}
    (b : ℕ → ℕ) (hmono : StrictMono b)
    (hbA : ∀ j, b j ∈ A) (hbpos : ∀ j, 0 < b j)
    (hbpool : ∀ j, b j ∈ P₀) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ((∀ i j, i < j → ∃ n, N₀ ≤ n ∧
        IsRepHub A n {b (f i), b (f j)}) ∨
      (∀ i j k, i < j → j < k → ∃ n, N₀ ≤ n ∧
        IsRepHub A n {b (f i), b (f j), b (f k)}) ∨
      (3 : Ordinal.{0}) ≤
        ((poolFreeStep_wf h0 hcov hfail P₀).apply ∅).rank) := by
  classical
  obtain ⟨f, hf, hout⟩ := team_card_escalation_two' h0 hcov hanchor
    hfail b hmono hbA hbpos
  rcases hout with hcl | ⟨-, hcl⟩ | ⟨-, htf, -⟩
  · exact ⟨f, hf, Or.inl hcl⟩
  · exact ⟨f, hf, Or.inr (Or.inl hcl)⟩
  · refine ⟨f, hf, Or.inr (Or.inr ?_)⟩
    set S : Finset ℕ := {b (f 0), b (f 1), b (f 2)} with hS
    have h01 : b (f 0) < b (f 1) := hmono (hf (by omega))
    have h12 : b (f 1) < b (f 2) := hmono (hf (by omega))
    have hSfree : RepFree A N₀ S :=
      repFree_iff_no_hub.2 (htf 0 1 2 (by omega) (by omega))
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
          push_neg
          omega),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_singleton]
          omega),
        Finset.card_singleton]
    have := free_set_card_le_rank h0 hcov hfail hSnode hSpool
    rw [hScard] at this
    exact_mod_cast this

/-- **The clique descent.**  Along any stream whose `(d+1)`-subsets
are all non-free, Ramsey at arity `d` either yields a subsequence
with ALL `d`-subsets free — a perfect clique world at level `d` —
or pushes the freeness level down and recurses; the level-1 floor
is barred by the private-stream kill.  Some perfect level
`1 ≤ d' ≤ d` always exists. -/
theorem clique_descent {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
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
      · -- r = 0: every refined singleton is non-free: stream kill
        exfalso
        have hr0' : r = 0 := by omega
        subst hr0'
        refine singleton_hubs_refuted h0 hcov hanchor hfail ?_
        intro N
        set v := e (f₁ N) with hv
        have hvpos : 0 < v := hepos _
        have hnf : ¬RepFree A N₀ {v} := by
          refine hallnonfree {v} ?_ (Finset.card_singleton v)
          intro h hh
          exact ⟨N, by rw [Finset.mem_singleton.1 hh]⟩
        rw [repFree_iff_no_hub, not_not] at hnf
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

/-- **LOW RANK FORCES A PERFECT CLIQUE WORLD.**  If a stream's pool
tree has finite root rank, some subsequence and level `d ≥ 1`
realize the perfect configuration: every `d`-subset is free and
every `(d+1)`-subset is a full hub of some late target.  With the
reduction (`no_pool_rank_descent`) this completes the block's
trichotomy: a counterexample's pools are either infinite-rank or
perfect clique worlds — and the descent to the perfect world is
itself the rank analysis the program called for. -/
theorem rank_lt_omega_perfect_clique {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
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
        S.card = d + 1 → ∃ m, N₀ ≤ m ∧ IsRepHub A m S) := by
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
  rw [repFree_iff_no_hub, not_not] at h1
  exact h1

/-- In a perfect clique world every stream-subset of size at most
`d` is free (extend it with high stream values to size exactly
`d`), so minimal hubs inside the world have FULL cardinality
`d + 1`: the hub hypergraph is exactly `(d+1)`-uniform — complete
at `d + 1`, empty below. -/
theorem perfect_world_small_sets_free {A : Set ℕ} {N₀ : ℕ}
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

/-- **Perfect worlds have root rank exactly `d`.**  The free
`d`-subsets certify rank `≥ d`; a free `(d+1)`-set would contradict
completeness of the hub hypergraph, capping the rank at `d`.  The
first exact rank computation in the framework — and since every
infinite subsequence of a perfect world is a perfect world at the
same level, perfect worlds are rank-stable: no intra-world pool
operation can drop the rank.  The descent must engage the outside. -/
theorem perfect_world_rank {A : Set ℕ} {N₀ : ℕ}
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
    push_neg at hgt
    have hge : ((d + 1 : ℕ) : Ordinal.{0}) ≤
        ((poolFreeStep_wf h0 hcov hfail (Set.range e)).apply
          ∅).rank := by
      have h1 : ((d : ℕ) : Ordinal.{0}) <
          ((poolFreeStep_wf h0 hcov hfail (Set.range e)).apply
            ∅).rank := hgt
      have h2 : ((d + 1 : ℕ) : Ordinal.{0}) =
          Order.succ ((d : ℕ) : Ordinal.{0}) := by
        rw [Nat.cast_succ, Ordinal.add_one_eq_succ]
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

/-- **Every member of a perfect-world hub is below its target.**
Removing any one member leaves a free `d`-set, whose avoiding
representation must hit the removed member alone: each member
personally participates, so the target dominates them all. -/
theorem perfect_world_target_dominates_all {A : Set ℕ} {N₀ : ℕ}
    {e : ℕ → ℕ} {d : ℕ} (hemono : StrictMono e)
    (hfree : ∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, e i = h) → S.card = d →
      RepFree A N₀ S)
    {S : Finset ℕ} (hSmem : ∀ h ∈ S, ∃ i, e i = h)
    (hScard : S.card = d + 1)
    {m : ℕ} (hm : N₀ ≤ m) (hhub : IsRepHub A m S) :
    ∀ s ∈ S, s ≤ m := by
  intro s hs
  have herase : (S.erase s).card ≤ d := by
    have := Finset.card_erase_of_mem hs
    omega
  have heraseF : RepFree A N₀ (S.erase s) :=
    perfect_world_small_sets_free hemono hfree
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

/-- **Perfect-world targets are uniformly Sidon.**  Hubs are 0-free
(their members are positive stream values), so the pair shadow
bounds every hub target's order-2 count by `2(d + 2)`. -/
theorem perfect_world_sidon_targets {A : Set ℕ} {N₀ : ℕ}
    [DecidablePred (· ∈ A)]
    (h0 : 0 ∈ A) {e : ℕ → ℕ} {d : ℕ} (hepos : ∀ j, 0 < e j)
    {S : Finset ℕ} (hSmem : ∀ h ∈ S, ∃ i, e i = h)
    (hScard : S.card = d + 1)
    {m : ℕ} (hhub : IsRepHub A m S) :
    ((Finset.range (m + 1)).filter
      (fun x => x ∈ A ∧ (m - x) ∈ A)).card ≤ 2 * (d + 1) := by
  have h0S : 0 ∉ S := by
    intro h
    obtain ⟨i, hi⟩ := hSmem 0 h
    have := hepos i
    omega
  have := pair_count_of_hub h0 hhub h0S
  omega

/-- **Deletions inside a perfect world are answered at full
uniformity.**  Any infinite deletion drawn from a level-`d` perfect
world has cofinal failing targets whose minimal hubs — made of
deleted elements — have cardinality at least `d + 1`: subsets of
size `≤ d` are free and cannot hub.  The crystal's team supply
runs exactly at its uniformity level. -/
theorem perfect_world_deletion_hubs_card {A B : Set ℕ} {N₀ : ℕ}
    [DecidablePred (· ∈ B)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B' ⊆ A, B'.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B') 3)
    {e : ℕ → ℕ} {d : ℕ} (hemono : StrictMono e)
    (heA : ∀ j, e j ∈ A) (hepos : ∀ j, 0 < e j)
    (hfree : ∀ S : Finset ℕ, (∀ h ∈ S, ∃ i, e i = h) → S.card = d →
      RepFree A N₀ S)
    (hBsub : B ⊆ Set.range e) (hBinf : B.Infinite) :
    ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      IsRepHub A n H ∧ (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
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
  have hteams := guardian_team_hubs_of_deletion h0 hcov hanchor
    hfail hBA hBinf h0B
  intro N
  obtain ⟨n, hn, H, hhub, hmin, hcard2, hHB⟩ := hteams (max N N₀)
  refine ⟨n, le_trans (le_max_left _ _) hn, H, hhub, hmin, ?_, hHB⟩
  by_contra hlt
  push_neg at hlt
  have hHmem : ∀ h ∈ H, ∃ i, e i = h := by
    intro h hh
    obtain ⟨j, hj⟩ := hBsub (hHB h hh)
    exact ⟨j, hj⟩
  have hHfree : RepFree A N₀ H :=
    perfect_world_small_sets_free hemono hfree hHmem (by omega)
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

/-- **Cross-order rank comparison.**  In a counterexample the
order-2 rank (an invariant of the minimal basis alone) never
exceeds the order-3 rank: the pair tree is a subtree of the rep
tree.  Two ordinal invariants, one inequality. -/
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

/-- Pair-hub-freeness of a set is exactly pair-freeness. -/
theorem pairFree_iff_no_pairHub {A : Set ℕ} {N₀ : ℕ}
    {S : Finset ℕ} :
    PairFree A N₀ S ↔ ¬∃ m, N₀ ≤ m ∧ IsPairHub A m S := by
  constructor
  · rintro hfree ⟨m, hm, hhub⟩
    obtain ⟨x, hx, y, hy, hs, hxS, hyS⟩ := hfree m hm
    rcases hhub x hx y hy hs with h | h
    · exact hxS h
    · exact hyS h
  · intro hno m hm
    by_contra hall
    push_neg at hall
    refine hno ⟨m, hm, ?_⟩
    intro x hx y hy hs
    by_contra hmiss
    push_neg at hmiss
    obtain ⟨h1, h2⟩ := hmiss
    exact h2 (hall x hx y hy hs h1)

/-- **The pair clique descent, for every minimal basis.**  Along
any stream whose `(d+1)`-subsets are all non-pair-free, Ramsey at
each arity yields one of: a subsequence every element of which
2-guards a target of its own (the order-2 floor is a legal world,
not a contradiction), or a PERFECT PAIR-CRYSTAL — all `d'`-subsets
pair-free, all `(d'+1)`-subsets pair-hubs — at some level
`1 ≤ d' ≤ d`. -/
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
    · -- perfect pair-crystal at level r + 1
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
      · -- r = 0: every refined singleton 2-guards — the legal floor
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

/-- **The stream classification, hypothesis-free.**  Any strictly
monotone stream, over any set whatsoever, refines into one of three
order-2 worlds: WIDE FREEDOM (pair-free subsets of every size),
TOTAL GUARDIANSHIP (an infinite subsequence each of whose elements
pair-guards a target of its own), or a PERFECT PAIR-CRYSTAL (a
level `d ≥ 1` with all `d`-subsets pair-free and all
`(d+1)`-subsets pair-hubs).  Pure combinatorics of the pair-freeness
lattice; every minimal basis and every counterexample stream falls
under it. -/
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
    push_neg at hwide
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

end Erdos881
