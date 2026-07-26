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

/-- **The order-3 stream classification, hypothesis-free.**  Any
monotone stream over any set refines into wide rep-freedom, total
private guardianship (each element a singleton rep-hub owner), or a
perfect rep-crystal.  Under the counterexample interfaces the
middle branch dies by the stream kill, recovering the conditional
descent. -/
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
    push_neg at hwide
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

/-- Rank-to-size with the superset recorded: rank `n` above a node
yields a free pool SUPERSET with `n` more elements. -/
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

/-- **Stalled nodes have finite rank, quantitatively.**  Any free
superset of a stalled node lives inside the stall window: a fresh
element `≥ X` would make `P ∪ {q}` free by downward closure,
contradicting the stall.  Hence the node's rank in ANY pool tree is
at most `|A ∩ [0, X)|`.  The flood's envelopes are finitely ranked
in every pool at once. -/
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
  push_neg at hgt
  have hge : ((W + 1 : ℕ) : Ordinal.{0}) ≤
      ((poolFreeStep_wf h0 hcov hfail P₀).apply P).rank := by
    have h2 : ((W + 1 : ℕ) : Ordinal.{0}) =
        Order.succ ((W : ℕ) : Ordinal.{0}) := by
      rw [Nat.cast_succ, Ordinal.add_one_eq_succ]
    rw [h2]
    exact Order.succ_le_of_lt hgt
  obtain ⟨Q, hQnode, hQpool, hPQ, hQcard⟩ :=
    rank_ge_imp_free_superset h0 hcov hfail (W + 1) P hst.1
      hPpool hge
  -- every fresh element sits below the stall threshold
  have hfresh : ∀ q ∈ Q, q ∉ P → q < X := by
    intro q hq hqP
    by_contra hqX
    push_neg at hqX
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

/-- **The crossing edge: narrowing elements exist.**  In a pool
whose tree has infinite root rank but which contains a stalled node
(every pool does, by the flood), the path from the root to the
stalled node crosses from infinite to finite rank at one step:
some free node `R` of infinite rank has an extension `insert b R`
of finite rank.  One element annihilates wideness.  The
infinite-rank room's interior structure, first theorem. -/
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
      _ < Ordinal.omega0 := Ordinal.nat_lt_omega0 _
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
        push_neg
        exact this)
    · exact h
  have hprev : ¬((hwf.apply (pre (i₀ - 1))).rank <
      Ordinal.omega0) := by
    intro hfin
    have := Nat.find_min hex (m := i₀ - 1) (by omega)
    exact this ⟨by omega, hfin⟩
  push_neg at hprev
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, i₀ = j₀ + 1 := ⟨i₀ - 1, by omega⟩
  have hj₀prev : ¬((hwf.apply (pre j₀)).rank <
      Ordinal.omega0) := by
    have h1 : j₀ = i₀ - 1 := by omega
    rw [h1]
    exact fun h => absurd h (by
      push_neg
      exact hprev)
  push_neg at hj₀prev
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

/-- **Cofinitely many singletons are free.**  Beyond one threshold,
no positive basis element is a private guardian: an infinite supply
of non-free singletons would give cofinal positive singleton hubs
(hub targets dominate their guardians), which the private-stream
kill forbids.  Every element of the enemy's tail opens the freeness
tree. -/
theorem cofinite_free_singletons {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ X, ∀ b ∈ A, X ≤ b → 0 < b → RepFree A N₀ {b} := by
  classical
  by_contra hno
  push_neg at hno
  refine singleton_hubs_refuted h0 hcov hanchor hfail ?_
  intro N
  obtain ⟨b, hbA, hNb, hbpos, hnotfree⟩ := hno N
  rw [repFree_iff_no_hub, not_not] at hnotfree
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

/-- **The ω-room dichotomy.**  An infinite-rank pool either has an
infinite-rank CHILD (a wide element: one singleton already carries
infinite freedom above it) or its root rank is exactly `ω` — the
singleton ranks are finite but unbounded, and the elements are
graded by a finite rank function.  Infinite rank never hides: it
is witnessed one element down, or the pool sits exactly at the
first limit. -/
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
    push_neg at hwide
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
    push_neg at hwide
    apply le_antisymm _ hR
    rw [Acc.rank_eq]
    apply Ordinal.iSup_le
    rintro ⟨C, hC⟩
    exact Order.succ_le_of_lt (hwide C hC)

/-- **THE ω-NODE EXISTS.**  Every infinite-rank pool tree contains
a node of rank EXACTLY `ω`: descend along wide children (each step
strictly decreases the rank, so the descent halts), and where it
halts the node dichotomy pins the rank at the first limit.  The
ω-node is the boundary where the infinite-rank room meets the
finite-rank (crystal) regime: all its extensions have finite,
unbounded freedom. -/
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

/-- **The ω-node's grade filtration.**  At a node of rank exactly
`ω`, extensions of every finite rank exist beyond every bound: if
large extensions were capped at rank `k`, the finitely many small
ones would cap the supremum below `ω`.  The grades
`ρ(b) = rank(R ∪ {b})` are finite, unbounded, with infinite nested
fibers of empty intersection — the boundary node is graded. -/
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
  push_neg at hno
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
            rw [h1, Nat.cast_succ, Ordinal.add_one_eq_succ]
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
    push_neg
    exact Ordinal.nat_lt_omega0 K)

/-- **The diagonal through the grades.**  From a rank-`ω` node,
extract a strictly monotone sequence of admissible extensions whose
grades climb without bound: `rank(R ∪ {b j}) ≥ j`.  The first
deletion candidate whose members carry unbounded relative freedom —
the staged object for the boundary attack. -/
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
prefixes never trap any target. -/
def HereditarilyFree (A : Set ℕ) (N₀ : ℕ) (B : Set ℕ) : Prop :=
  B.Infinite ∧ (∀ b ∈ B, b ∈ A ∧ 0 < b) ∧
  ∀ P : Finset ℕ, (∀ h ∈ P, h ∈ B) → RepFree A N₀ P

/-- **THE CHARACTERIZATION.**  For a covering set with `0`, the
counterexample condition is EQUIVALENT to the absence of an
infinite hereditarily rep-free subset.  Erdős 881 (k = 2) is
exactly: does every ℵ₀-minimal exact order-2 basis contain an
infinite hereditarily rep-free set? -/
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
    push_neg at hnother
    obtain ⟨Q, hQB', hQnotfree⟩ := hnother hB'inf
      (fun b hb => ⟨hBA hb.1, hb.2.1⟩)
    rw [RepFree] at hQnotfree
    push_neg at hQnotfree
    obtain ⟨n, hn, halln⟩ := hQnotfree
    have hhub : IsRepHub A n Q := by
      intro x hx y hy z hz hsum
      by_contra hmiss
      push_neg at hmiss
      obtain ⟨h1, h2, h3⟩ := hmiss
      exact h3 (halln x hx y hy z hz hsum h1 h2)
    -- the hub is high, so the dead target is late
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

/-- **The tree and the witness are one.**  Purely combinatorially
(no covering, no failure hypothesis): the freeness tree is
well-founded exactly when no infinite hereditarily free set
exists.  A descending chain's union is hereditarily free
(downward closure); a hereditarily free set's sorted prefixes are
a descending chain. -/
theorem freeStep_wf_iff_no_hereditarilyFree {A : Set ℕ} {N₀ : ℕ} :
    WellFounded (FreeStep A N₀) ↔
    ¬∃ B : Set ℕ, HereditarilyFree A N₀ B := by
  classical
  constructor
  · -- WF kills hereditarily free sets: their prefixes descend
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
      -- P is finite, so it sits inside one stage
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

/-- **The triangle.**  Counterexample-hood IS tree
well-foundedness: with covering and `0 ∈ A`, order-3 failure under
every infinite deletion, absence of hereditarily free sets, and
well-foundedness of the freeness tree are one property. -/
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

/-- **The pair characterization.**  Elementwise ℵ₀-minimality is
equivalent to the absence of an infinite hereditarily pair-free
subset. -/
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
    push_neg at hnother
    obtain ⟨Q, hQB', hQnotfree⟩ := hnother hB'inf
      (fun b hb => ⟨hBA hb.1, hb.2.1⟩)
    rw [PairFree] at hQnotfree
    push_neg at hQnotfree
    obtain ⟨n, hn, halln⟩ := hQnotfree
    have hhub : IsPairHub A n Q := by
      intro x hx y hy hsum
      by_contra hmiss
      push_neg at hmiss
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

/-- **The pair tree and its witness are one** (combinatorial). -/
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

/-- **THE TWO-TREE FORMULATION.**  A counterexample to Erdős 881
(k = 2) is exactly a covering set with `0` whose pair tree AND rep
tree are BOTH well-founded.  The problem: can two nested freeness
trees over one basis both be well-founded? -/
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

/-- **THE COLLAPSE: one tree decides everything.**  For a covering
set with `0`, the full counterexample condition — minimality AND
universal order-3 failure — is equivalent to well-foundedness of
the rep tree ALONE: the pair tree is a subtree, so minimality
comes free.  Erdős 881 (k = 2), final form: IS THERE a covering
set with `0` whose rep-freeness tree is well-founded?  (If no such
set exists, the answer to the problem is yes.) -/
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

/-- **THE BRANCH TEMPLATE: Sidon covering sets carry explicit
infinite branches.**  Under a global pair-count bound `C`, a
geometrically spaced subset is hereditarily rep-free: at every
target the candidate third parts outnumber the window fibers (each
of size `≤ C + N₀`), so a stream-avoiding triple survives.  The
constructive companion of `r2_unbounded_of_hfail`, and the counting
shape every general branch construction must beat. -/
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
  -- THE CORE: at every target, a triple avoiding the whole window
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
        push_neg at hgood
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
  -- WRAPPER: hereditary freeness from window avoidance
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

/-- **Order-2 survival implies order-3 survival**: translate every
late target through one fixed remaining element.  Hence universal
order-3 failure implies minimality outright — in the original
tuple vocabulary, with no zero hypothesis. -/
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

/-- **The collapse in the original vocabulary**: universal order-3
failure implies ℵ₀-minimality (tuple form), because an order-2
surviving deletion would survive at order 3 by translation. -/
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

/-- **Branches are uniform.**  Hereditary freeness (all finite
subsets rep-free) is equivalent to uniform avoidance: every late
target has a representation avoiding the WHOLE set (parts below
the target only ever meet the finite shadow).  Both verified
branch mechanisms — Sidon counting and Cantor carry repair —
produce exactly this object. -/
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

/-- **The Sidon door, full circle.**  A globally pair-bounded
covering set is never a counterexample: the branch template
supplies a hereditarily free set, and the characterization
converts it into a surviving deletion.  The constructive
counterpart of `r2_unbounded_of_hfail`, composed end to end. -/
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

/-- **Maximal free nodes exist above every node.**  Well-founded
induction: extend until no step remains.  Every leaf is totally
stalled — every larger positive basis element completes a hub over
it at once (threshold `max P + 1`, sharper than the flood's
abstract threshold).  Under `hfail` the tree is a forest of stalls
all the way up. -/
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
    · push_neg at hmax
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

/-- **No infinite ascending inclusion-chains of free sets**: their
union would be an infinite hereditarily free set.  Stronger than
tree well-foundedness — insertions anywhere, not just at the top. -/
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

/-- **THE ABSOLUTE FLOOD.**  Every free node extends to an
inclusion-maximal free set — a fixed finite free envelope over
which EVERY positive basis element outside it, small or large, is
a guardian: adding any one of them creates a hub.  The strongest
stall form: one canonical envelope, total guardianship. -/
theorem exists_absolute_leaf {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (P : Finset ℕ) (hP : FreeNode A N₀ P) :
    ∃ Q : Finset ℕ, FreeNode A N₀ Q ∧ P ⊆ Q ∧
      ∀ b ∈ A, 0 < b → b ∉ Q →
        ∃ m, N₀ ≤ m ∧ IsRepHub A m (insert b Q) := by
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
      push_neg at hnotfree
      obtain ⟨m, hm, hall⟩ := hnotfree
      refine ⟨m, hm, ?_⟩
      intro x hx y hy z hz hsum
      by_contra hmiss
      push_neg at hmiss
      obtain ⟨h1, h2, h3⟩ := hmiss
      exact h3 (hall x hx y hy z hz hsum h1 h2)
    · push_neg at hmax
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

/-- **The order-2 absolute flood** — a structure theorem for EVERY
elementwise-minimal order-2 covering set, no counterexample
hypothesis: each pair-free node extends to an inclusion-maximal
pair-free envelope over which every outside positive basis element
is a pair-guardian. -/
theorem exists_absolute_pair_leaf {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hmin : ∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n)
    (P : Finset ℕ) (hP : PairFreeNode A N₀ P) :
    ∃ Q : Finset ℕ, PairFreeNode A N₀ Q ∧ P ⊆ Q ∧
      ∀ b ∈ A, 0 < b → b ∉ Q →
        ∃ m, N₀ ≤ m ∧ IsPairHub A m (insert b Q) := by
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
      push_neg at hnotfree
      obtain ⟨m, hm, hall⟩ := hnotfree
      refine ⟨m, hm, ?_⟩
      intro x hx y hy hsum
      by_cases hxin : x ∈ insert b P
      · exact Or.inl hxin
      · exact Or.inr (hall x hx y hy hsum hxin)
    · push_neg at hmax
      obtain ⟨b, hbA, hbpos, hbP, hbfree⟩ := hmax
      have hstep : PairSup A N₀ (insert b P) P :=
        ⟨hP, hbfree, Finset.ssubset_insert hbP⟩
      obtain ⟨Q, hQnode, hQsub, hQmax⟩ := ih _ hstep hbfree
      exact ⟨Q, hQnode, Finset.Subset.trans
        (Finset.subset_insert _ _) hQsub, hQmax⟩

/-- Personal-target geometry at an absolute leaf: the envelope is
free, so any envelope-avoiding representation of the hub target
must use the new element itself — hence the target sits at or
above its guardian, which appears as a part. -/
theorem absolute_leaf_personal_target {A : Set ℕ} {N₀ : ℕ}
    {Q : Finset ℕ} {b m : ℕ}
    (hQ : FreeNode A N₀ Q) (hm : N₀ ≤ m)
    (hhub : IsRepHub A m (insert b Q)) :
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

/-- **Three-never-four for rotating envelope-hubs.**  A rep has
three parts, so a b-avoiding rep meets at most three pairwise
disjoint envelopes.  If one target carries hubs `insert b Qᵢ`
through FOUR pairwise disjoint b-free envelopes, no rep can avoid
b: the shared guardian owns the target outright ({b} is a full
singleton hub).  Pure combinatorics — no freeness, no hfail. -/
theorem four_disjoint_hubs_singleton {A : Set ℕ} {m b : ℕ}
    {Q : Fin 4 → Finset ℕ}
    (hdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j))
    (hb : ∀ i, b ∉ Q i)
    (hhub : ∀ i, IsRepHub A m (insert b (Q i))) :
    IsRepHub A m {b} := by
  classical
  intro x hx y hy z hz hsum
  by_contra hmiss
  push_neg at hmiss
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

/-- Pool form of the absolute flood: within any pool of positive
basis elements, every free set of pool elements extends to a
pool-inclusion-maximal one, over which every remaining pool
element is a guardian. -/
theorem exists_absolute_leaf_pool {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (C : Set ℕ) (hC : ∀ c ∈ C, c ∈ A ∧ 0 < c)
    (P : Finset ℕ) (hPC : ∀ h ∈ P, h ∈ C)
    (hPfree : RepFree A N₀ P) :
    ∃ Q : Finset ℕ, (∀ h ∈ Q, h ∈ C) ∧ RepFree A N₀ Q ∧ P ⊆ Q ∧
      ∀ b ∈ C, b ∉ Q → ∃ m, N₀ ≤ m ∧ IsRepHub A m (insert b Q) := by
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
      push_neg at hnotfree
      obtain ⟨m, hm, hall⟩ := hnotfree
      refine ⟨m, hm, ?_⟩
      intro x hx y hy z hz hsum
      by_contra hmiss
      push_neg at hmiss
      obtain ⟨h1, h2, h3⟩ := hmiss
      exact h3 (hall x hx y hy z hz hsum h1 h2)
    · push_neg at hmax
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

/-- **THE SHELL STRATIFICATION.**  Under hfail the positive basis
elements organize into infinitely many pairwise disjoint NONEMPTY
free shells Q₀, Q₁, Q₂, …: each shell is inclusion-maximal free
inside the pool left over by its predecessors, so every positive
element outside the first k+1 shells is a guardian of shell k.
An element joining shell k+1 guards shells 0..k; an element
avoiding all shells guards every level. -/
theorem absolute_shell_stratification {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ Q : ℕ → Finset ℕ,
      (∀ k, (Q k).Nonempty) ∧
      (∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h) ∧
      (∀ k, RepFree A N₀ (Q k)) ∧
      (∀ j k, j < k → Disjoint (Q j) (Q k)) ∧
      (∀ k, ∀ b ∈ A, 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
        ∃ m, N₀ ≤ m ∧ IsRepHub A m (insert b (Q k))) := by
  classical
  -- one shell over the pool avoiding a given finite past
  have hstep : ∀ U : Finset ℕ, ∃ Q : Finset ℕ, Q.Nonempty ∧
      (∀ h ∈ Q, h ∈ A ∧ 0 < h ∧ h ∉ U) ∧ RepFree A N₀ Q ∧
      ∀ b ∈ A, 0 < b → b ∉ U → b ∉ Q →
        ∃ m, N₀ ≤ m ∧ IsRepHub A m (insert b Q) := by
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
  -- the cumulative union is exactly the union of shells so far
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
      show ∃ m, N₀ ≤ m ∧ IsRepHub A m (insert b (g 0).1)
      rw [hQ0] at hb0 ⊢
      exact hFmax ∅ b hbA hbpos (Finset.notMem_empty b) hb0
    | succ k =>
      have hbU : b ∉ (g k).2 := by
        intro hmem
        obtain ⟨j, hj, hx⟩ := (hUmem k b).1 hmem
        exact hbQ j (by omega) hx
      have hb1 : b ∉ (g (k + 1)).1 := hbQ (k + 1) (le_refl _)
      show ∃ m, N₀ ≤ m ∧ IsRepHub A m (insert b (g (k + 1)).1)
      rw [hQs] at hb1 ⊢
      exact hFmax _ b hbA hbpos hbU hb1

/-- **The eternal-survivor dichotomy.**  An element guarding every
level of a disjoint shell family either sees its personal targets
grow without bound, or — if they stay bounded — pigeonholes four
disjoint shells onto ONE target and owns it outright
(`four_disjoint_hubs_singleton`): every representation of that
target uses the survivor. -/
theorem eternal_survivor_dichotomy {A : Set ℕ} {N₀ : ℕ}
    {Q : ℕ → Finset ℕ} {b : ℕ}
    (hdisj : ∀ j k, j < k → Disjoint (Q j) (Q k))
    (hb : ∀ j, b ∉ Q j)
    (hguard : ∀ k, ∃ m, N₀ ≤ m ∧ IsRepHub A m (insert b (Q k))) :
    (∀ Y, ∃ k, ∃ m, Y ≤ m ∧ N₀ ≤ m ∧
      IsRepHub A m (insert b (Q k))) ∨
    ∃ m, N₀ ≤ m ∧ IsRepHub A m {b} := by
  classical
  choose m hm₁ hm₂ using hguard
  by_cases hunb : ∀ Y, ∃ k, Y ≤ m k
  · left
    intro Y
    obtain ⟨k, hk⟩ := hunb Y
    exact ⟨k, m k, hk, hm₁ k, hm₂ k⟩
  · right
    push_neg at hunb
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
    refine four_disjoint_hubs_singleton
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

/-- **The singleton-owner corner dies.**  Survivors of a disjoint
shell family cannot take the bounded-target branch of
`eternal_survivor_dichotomy` at unbounded sizes: an owner sits
inside every representation of its target, so its target is at or
above its own scale, and infinitely many owners would form a
cofinal private-triple stream — which the rotating-guardian kill
converts into a surviving deletion, refuting hfail.  Hence beyond
one threshold EVERY eternal survivor has unbounded personal
targets across the shells. -/
theorem shell_survivors_unbounded_targets {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {Q : ℕ → Finset ℕ}
    (hdisj : ∀ j k, j < k → Disjoint (Q j) (Q k))
    (hguard : ∀ k, ∀ b ∈ A, 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
      ∃ m, N₀ ≤ m ∧ IsRepHub A m (insert b (Q k))) :
    ∃ X, ∀ b ∈ A, X ≤ b → 0 < b → (∀ j, b ∉ Q j) →
      ∀ Y, ∃ k, ∃ m, Y ≤ m ∧ N₀ ≤ m ∧
        IsRepHub A m (insert b (Q k)) := by
  classical
  by_contra hno
  push_neg at hno
  have hstream : ∀ N, ∃ a m, N ≤ m ∧ 0 < a ∧
      IsPrivateTriple A a m := by
    intro N
    obtain ⟨b, hbA, hbX, hbpos, hbQ, Y, hY⟩ := hno N
    have hg : ∀ k, ∃ m, N₀ ≤ m ∧
        IsRepHub A m (insert b (Q k)) := by
      intro k
      exact hguard k b hbA hbpos (fun j _ => hbQ j)
    have hnotleft : ¬(∀ Y', ∃ k, ∃ m, Y' ≤ m ∧ N₀ ≤ m ∧
        IsRepHub A m (insert b (Q k))) := by
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
  obtain ⟨B, hBA, hBinf, hsurv⟩ :=
    surviving_deletion_of_cofinal_privateStream h0 hcov hstream
      hanchor
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

/-- **THE SHELL ENDGAME.**  Composition of the stratification and
the singleton-owner kill: a counterexample's positive elements
split into infinitely many disjoint nonempty free shells with
hierarchical total guardianship, and every sufficiently large
element avoiding all shells guards at UNBOUNDED scales.  So the
enemy is either a perfect stratification (finitely many eternal
survivors) or carries an infinite crowd of infinitely-employed
survivors — no third shape exists. -/
theorem shell_endgame {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ Q : ℕ → Finset ℕ, ∃ X,
      (∀ k, (Q k).Nonempty) ∧
      (∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h) ∧
      (∀ k, RepFree A N₀ (Q k)) ∧
      (∀ j k, j < k → Disjoint (Q j) (Q k)) ∧
      (∀ k, ∀ b ∈ A, 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
        ∃ m, N₀ ≤ m ∧ IsRepHub A m (insert b (Q k))) ∧
      (∀ b ∈ A, X ≤ b → 0 < b → (∀ j, b ∉ Q j) →
        ∀ Y, ∃ k, ∃ m, Y ≤ m ∧ N₀ ≤ m ∧
          IsRepHub A m (insert b (Q k))) := by
  obtain ⟨Q, hne, hmem, hfree, hdisj, hguard⟩ :=
    absolute_shell_stratification h0 hcov hanchor hfail
  obtain ⟨X, hX⟩ :=
    shell_survivors_unbounded_targets h0 hcov hanchor hfail
      hdisj hguard
  exact ⟨Q, X, hne, hmem, hfree, hdisj, hguard, hX⟩

/-- **Depth forces scale** (hypothesis-free pigeonhole).  An
element with guardian duties at k+1 pairwise disjoint shells
either owns some target outright, or one of its duty targets
already sits at height N₀ + k/3: at most three duties can share a
target value without triggering `four_disjoint_hubs_singleton`,
so k+1 duties cannot all hide below the tax line. -/
theorem shell_depth_forces_scale {A : Set ℕ} {N₀ : ℕ}
    {Q : ℕ → Finset ℕ} {k b : ℕ}
    (hdisj : ∀ j k', j < k' → Disjoint (Q j) (Q k'))
    (hguard : ∀ j, j ≤ k → ∃ m, N₀ ≤ m ∧
      IsRepHub A m (insert b (Q j)))
    (hb : ∀ j, j ≤ k → b ∉ Q j) :
    (∃ m, N₀ ≤ m ∧ IsRepHub A m {b}) ∨
    (∃ j, j ≤ k ∧ ∃ m, N₀ + k / 3 ≤ m ∧ N₀ ≤ m ∧
      IsRepHub A m (insert b (Q j))) := by
  classical
  have hg : ∀ j, ∃ m, N₀ ≤ m ∧
      (j ≤ k → IsRepHub A m (insert b (Q j))) := by
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
    push_neg at hbig
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
    refine four_disjoint_hubs_singleton
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

/-- **THE DEPTH TAX.**  Under hfail and anchors, beyond one
threshold every element clear of shells 0..k — a depth-(k+1)
shell member or an eternal survivor — carries a guardian duty at
height at least N₀ + k/3.  Ownership cannot pay the tax at
unbounded sizes (owners at their own scale form a cofinal private
stream, and the rotating-guardian kill fires).  Depth in the
stratification forces employment at linear scale; this
quantitatively strengthens `shell_survivors_unbounded_targets`. -/
theorem depth_tax_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {Q : ℕ → Finset ℕ}
    (hdisj : ∀ j k, j < k → Disjoint (Q j) (Q k))
    (hguard : ∀ k, ∀ b ∈ A, 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
      ∃ m, N₀ ≤ m ∧ IsRepHub A m (insert b (Q k))) :
    ∃ X, ∀ k, ∀ b ∈ A, X ≤ b → 0 < b →
      (∀ j, j ≤ k → b ∉ Q j) →
      ∃ j, j ≤ k ∧ ∃ m, N₀ + k / 3 ≤ m ∧ N₀ ≤ m ∧
        IsRepHub A m (insert b (Q j)) := by
  classical
  by_contra hno
  push_neg at hno
  have hstream : ∀ N, ∃ a m', N ≤ m' ∧ 0 < a ∧
      IsPrivateTriple A a m' := by
    intro N
    obtain ⟨k, b, hbA, hbX, hbpos, hbQ, hbdd⟩ := hno N
    have hg : ∀ j, j ≤ k → ∃ m, N₀ ≤ m ∧
        IsRepHub A m (insert b (Q j)) := by
      intro j hj
      exact hguard j b hbA hbpos (fun j' hj' => hbQ j' (by omega))
    rcases shell_depth_forces_scale hdisj hg
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
  obtain ⟨B, hBA, hBinf, hsurv⟩ :=
    surviving_deletion_of_cofinal_privateStream h0 hcov hstream
      hanchor
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
disjoint b-free envelope-hubs at one target already force
singleton ownership at order 2.  Hypothesis-free. -/
theorem three_disjoint_pair_hubs_singleton {A : Set ℕ} {m b : ℕ}
    {Q : Fin 3 → Finset ℕ}
    (hdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j))
    (hb : ∀ i, b ∉ Q i)
    (hhub : ∀ i, IsPairHub A m (insert b (Q i))) :
    IsPairHub A m {b} := by
  classical
  intro x hx y hy hsum
  by_contra hmiss
  push_neg at hmiss
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

/-- **THE STRATIFIED TAX PORTRAIT.**  Everything the shell arc
proves, in one object: disjoint nonempty free shells with
hierarchical total guardianship, and a single threshold beyond
which every element clear of shells 0..k — shell-(k+1) members
and eternal survivors alike — pays a guardian duty at height at
least N₀ + k/3 over one of those shells.  Since each shell is
free, `absolute_leaf_personal_target` applies to every such duty:
the payer appears in every shell-avoiding representation of its
duty target, which therefore also sits at or above the payer. -/
theorem stratified_tax_portrait {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ Q : ℕ → Finset ℕ, ∃ X,
      (∀ k, (Q k).Nonempty) ∧
      (∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h) ∧
      (∀ k, RepFree A N₀ (Q k)) ∧
      (∀ j k, j < k → Disjoint (Q j) (Q k)) ∧
      (∀ k, ∀ b ∈ A, 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
        ∃ m, N₀ ≤ m ∧ IsRepHub A m (insert b (Q k))) ∧
      (∀ k, ∀ b ∈ A, X ≤ b → 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
        ∃ j, j ≤ k ∧ ∃ m, N₀ + k / 3 ≤ m ∧ N₀ ≤ m ∧
          IsRepHub A m (insert b (Q j))) := by
  obtain ⟨Q, hne, hmem, hfree, hdisj, hguard⟩ :=
    absolute_shell_stratification h0 hcov hanchor hfail
  obtain ⟨X, hX⟩ :=
    depth_tax_of_hfail h0 hcov hanchor hfail hdisj hguard
  exact ⟨Q, X, hne, hmem, hfree, hdisj, hguard, hX⟩

/-- **THE SIX-LEVEL CAP.**  Seven pairwise disjoint envelopes with
seven DISTINCT guardians can never hub one common target: a
representation has three parts, each lying in at most one envelope
(disjointness) and equal to at most one guardian (injectivity), so
a rep covers at most six of the seven demands.  Unlike the
rotation cap there is no ownership escape — distinct guardians
kill it.  One target therefore serves at most six shell-levels of
distinct-guardian duty.  Hypothesis-free pigeonhole. -/
theorem seven_level_hub_impossible {A : Set ℕ} {m : ℕ}
    {Q : Fin 7 → Finset ℕ} {b : Fin 7 → ℕ}
    (hdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j))
    (hbinj : Function.Injective b)
    (hrep : ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = m)
    (hhub : ∀ i, IsRepHub A m (insert (b i) (Q i))) :
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

/-- **THE 18-LEVEL ABSOLUTE CAP.**  Nineteen shell-duties at one
target force singleton ownership: if any guardian value serves
four of the levels, the rotation cap hands it the target; if all
fibers have size at most three, at least seven distinct guardian
values appear and `seven_level_hub_impossible` rules the
configuration out entirely.  So one target carries at most 18
envelope-hubs over pairwise disjoint envelopes, unless some
guardian owns it outright.  Hypothesis-free. -/
theorem eighteen_level_cap {A : Set ℕ} {m : ℕ}
    {Q : Fin 19 → Finset ℕ} {b : Fin 19 → ℕ}
    (hdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j))
    (hb : ∀ i j, b i ∉ Q j)
    (hrep : ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = m)
    (hhub : ∀ i, IsRepHub A m (insert (b i) (Q i))) :
    ∃ i, IsRepHub A m {b i} := by
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
    have hown : IsRepHub A m {v} := by
      refine four_disjoint_hubs_singleton
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
    push_neg at hfib
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
    refine seven_level_hub_impossible (A := A) (m := m)
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

/-- **The shell-conflict degree cap.**  Shells pairwise conflict:
by inclusion-maximality any two shells union to a non-free set,
so each pair owns a conflict target whose representations all
meet the union.  But conflicts are 3-bounded per (shell, target):
a free shell admits a rep of the target avoiding it, and that rep
must then meet every conflict partner — three parts, so at most
three pairwise disjoint partners.  A fifth is impossible. -/
theorem five_shell_conflict_impossible {A : Set ℕ} {N₀ m : ℕ}
    {Q : Fin 5 → Finset ℕ}
    (hdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j))
    (hfree : RepFree A N₀ (Q 0))
    (hm : N₀ ≤ m)
    (hhub : ∀ i : Fin 4, IsRepHub A m (Q 0 ∪ Q i.succ)) :
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

/-- Hub-ness is up-monotone in the envelope. -/
theorem IsRepHub.mono {A : Set ℕ} {m : ℕ} {H H' : Finset ℕ}
    (hsub : H ⊆ H') (h : IsRepHub A m H) : IsRepHub A m H' := by
  intro x hx y hy z hz hsum
  rcases h x hx y hy z hz hsum with h' | h' | h'
  · exact Or.inl (hsub h')
  · exact Or.inr (Or.inl (hsub h'))
  · exact Or.inr (Or.inr (hsub h'))

/-- **Shells pairwise conflict.**  Any member of a later shell is
a guardian of any earlier one, so every pair of shells owns a
conflict target whose representations all meet the union of the
two.  With `five_shell_conflict_impossible` this pins the conflict
graph at every target: max degree ≤ 3 (hence ≤ 9 shell-pairs per
target, cover number ≤ 3). -/
theorem shell_pairs_conflict {A : Set ℕ} {N₀ : ℕ}
    {Q : ℕ → Finset ℕ}
    (hne : ∀ k, (Q k).Nonempty)
    (hmem : ∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h)
    (hdisj : ∀ j k, j < k → Disjoint (Q j) (Q k))
    (hguard : ∀ k, ∀ b ∈ A, 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
      ∃ m, N₀ ≤ m ∧ IsRepHub A m (insert b (Q k))) :
    ∀ j k, j < k → ∃ m, N₀ ≤ m ∧
      IsRepHub A m (Q j ∪ Q k) := by
  intro j k hjk
  obtain ⟨b, hb⟩ := hne k
  have hbA := (hmem k b hb).1
  have hbpos := (hmem k b hb).2
  have hbavoid : ∀ j', j' ≤ j → b ∉ Q j' := by
    intro j' hj' hmem'
    exact (Finset.disjoint_left.1 (hdisj j' k (by omega)))
      hmem' hb
  obtain ⟨m, hm, hhub⟩ := hguard j b hbA hbpos hbavoid
  refine ⟨m, hm, IsRepHub.mono ?_ hhub⟩
  intro w hw
  rcases Finset.mem_insert.1 hw with h' | h'
  · rw [h']
    exact Finset.mem_union_right _ hb
  · exact Finset.mem_union_left _ h'

/-- Order-2 conflict cap: a pair-free shell's escape pair must
meet every conflict partner, and a pair has two parts — so at
order 2 the per-target conflict degree is at most 2; a fourth
disjoint partner is impossible. -/
theorem four_shell_pair_conflict_impossible {A : Set ℕ}
    {N₀ m : ℕ} {Q : Fin 4 → Finset ℕ}
    (hdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j))
    (hfree : PairFree A N₀ (Q 0))
    (hm : N₀ ≤ m)
    (hhub : ∀ i : Fin 3, IsPairHub A m (Q 0 ∪ Q i.succ)) :
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
    (hhub : IsRepHub A m (insert b (Q k)))
    (hrob : HasDisjointTripleReps A m K) :
    K ≤ (Q k).card + 1 := by
  have h1 := disjoint_reps_le_hub_card hhub hrob
  have h2 := Finset.card_insert_le b (Q k)
  omega

/-- Conflict targets are fragile: a conflict target of the shell
pair (j,k) admits at most |Q j| + |Q k| pairwise disjoint
representations.  Robust windows repel shell conflicts too. -/
theorem conflict_targets_fragile {A : Set ℕ} {N₀ : ℕ}
    {Q : ℕ → Finset ℕ} {j k m K : ℕ}
    (hhub : IsRepHub A m (Q j ∪ Q k))
    (hrob : HasDisjointTripleReps A m K) :
    K ≤ (Q j).card + (Q k).card := by
  have h1 := disjoint_reps_le_hub_card hhub hrob
  have h2 := Finset.card_union_le (Q j) (Q k)
  omega

/-- **THE ROBUSTNESS BRANCH.**  If disjoint-representation counts
grow uniformly (for every C, all large targets carry C pairwise
disjoint representations), then a hereditarily free infinite set
exists: pick the sequence diagonally above the monotone
robustness thresholds.  Any finite subset P then loses to every
target — targets below the relevant threshold see nothing of P,
and a target above it has more disjoint representations than P
has members at or below the target, so some representation
escapes whole.  A third branch mechanism, alongside counting
(Sidon) and structure (Cantor). -/
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
      push_neg at hall
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

/-- **THE FRAGILE SUPPLY** (contrapositive).  Under hfail some
fixed fragility level C recurs cofinally: infinitely many targets
carry fewer than C pairwise disjoint representations.  Otherwise
the robustness branch would survive, refuting hfail.  A
self-contained rederivation of the card-bounded supply from pure
robustness logic. -/
theorem fragile_supply_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ C, ∀ H, ∃ m, H ≤ m ∧ ¬HasDisjointTripleReps A m C := by
  by_contra hno
  push_neg at hno
  exact (hfail_iff_no_hereditarily_free h0 hcov).1 hfail
    (robustness_gives_hereditarily_free h0 hcov hno)

/-- **The seal-cost inequality** (ledger line (i) of the
mass-accounting program).  To seal an envelope S at a target m by
deleting D — making every surviving representation meet S — costs
at least one deleted element per pairwise disjoint S-avoiding
representation: each such rep must lose a part to D, and
disjointness makes those parts distinct.  Deletion-form of
`disjoint_reps_le_hub_card`. -/
theorem seal_cost_of_disjoint_avoiding {A : Set ℕ} {m K : ℕ}
    {S D : Finset ℕ} (P : Fin K → Fin 3 → ℕ)
    (hPA : ∀ i k, P i k ∈ A)
    (hPsum : ∀ i, P i 0 + P i 1 + P i 2 = m)
    (hPdis : ∀ i j k l, i ≠ j → P i k ≠ P j l)
    (hPavoid : ∀ i k, P i k ∉ S)
    (hseal : IsRepHub (A \ ↑D) m S) :
    K ≤ D.card := by
  classical
  have hpick : ∀ i : Fin K, ∃ k : Fin 3, P i k ∈ D := by
    intro i
    by_contra hnone
    push_neg at hnone
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

/-- **The common-reflection supply.**  Two hub targets route every
window element through their envelopes (fan routing), and
pigeonholing the envelope pair hands one (h, h') a proportional
sub-window V reflecting through BOTH points m − h and m' − h':
for a ∈ V, both (m − h) − a and (m' − h') − a lie in A.  The
caller splits on m − h = m' − h' (sum multiplicity at one point)
versus ≠ (difference multiplicity at the fixed offset) — the
engine of the difference-blowup program. -/
theorem two_hubs_common_reflection {A : Set ℕ} {N₀ m m' : ℕ}
    {H H' : Finset ℕ} (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hm : N₀ ≤ m) (hm' : N₀ ≤ m')
    (hhub : IsRepHub A m H) (hhub' : IsRepHub A m' H')
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
  -- fan routing at each street
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

/-- **THE DOUBLE-REFLECTION SUPPLY.**  A counterexample carries,
at every size K, two reflection points u, u' and K window
elements reflecting through BOTH: a ∈ A with u − a ∈ A and
u' − a ∈ A.  (Flood streets supply the hubs, the covering √-bound
supplies the window, `two_hubs_common_reflection` pigeonholes.)
If u ≠ u' this is K-fold difference multiplicity at the fixed
offset u' − u; if u = u' it is K-fold sum concentration — but
unlike bare r₂-blowup the SAME window works for both points,
which is strictly more than two separate blowups. -/
theorem double_reflection_supply_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ K, ∃ u u' : ℕ, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ a ∈ V, a ∈ A ∧ (∃ x ∈ A, x + a = u) ∧
        (∃ x' ∈ A, x' + a = u') := by
  classical
  obtain ⟨P, hPfree, X, hflood⟩ := rep_flood_of_hfail h0 hcov hfail
  intro K
  set C := P.card + 1 with hC
  set T := K * C * C + 2 * C + 1 with hT
  -- street 1: a large guardian with its personal hub
  obtain ⟨b, hbA, hbge⟩ :=
    pairCovers_unbounded hcov (X + T * T + 2 * N₀ + 1)
  obtain ⟨m, hm, hbm, hhub⟩ := hflood b hbA (by omega)
  -- street 2: strictly beyond street 1
  obtain ⟨b', hb'A, hb'ge⟩ := pairCovers_unbounded hcov (X + m + 1)
  obtain ⟨m', hm', hb'm', hhub'⟩ := hflood b' hb'A (by omega)
  -- the window: A-elements below street 1's horizon
  haveI : DecidablePred (· ∈ A) := Classical.decPred _
  set F := ((Finset.range (b - N₀ + 1)).filter (· ∈ A)) with hF
  have hFcard : T ≤ F.card := by
    have h1 := covering_sqrt_lower (A := A) (N₀ := N₀) hcov
      (n := b - N₀) (by omega)
    by_contra hlt
    push_neg at hlt
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
    push_neg at haHH
    refine ⟨haF.2, haHH.1, haHH.2, ?_, ?_⟩
    · omega
    · omega
  obtain ⟨h₀, hh₀, h₀', hh₀', V, hVW, hcount, hVrefl⟩ :=
    two_hubs_common_reflection h0 hcov hm hm' hhub hhub' W hWmem
  refine ⟨m - h₀, m' - h₀', V, ?_, ?_⟩
  · -- K ≤ V.card from the pigeonhole count
    have h1 : H.card * H'.card ≤ C * C :=
      Nat.mul_le_mul hHc hH'c
    have h2 : H.card * H'.card * V.card ≤ C * C * V.card :=
      Nat.mul_le_mul h1 (le_refl V.card)
    by_contra hVK
    push_neg at hVK
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

/-- **THE STREET DICHOTOMY.**  Three flood streets, one shared
window, the reflection engine applied twice: either two of the
four reflection points differ — K-fold DIFFERENCE multiplicity at
a fixed positive offset — or all coincide at one point n, and
size-forcing turns the flood affine (m₂ = n + b₂, m₃ = n + b₃):
n is a K-fold blown point AND the difference translate
n + b₃ − b₂ is a pair street through the third rotator.  The
enemy must blow up differences or go affine. -/
theorem street_dichotomy_of_hfail {A : Set ℕ} {N₀ : ℕ}
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
          IsPairHub A s (insert b₃ Q)) := by
  classical
  obtain ⟨P, hPfree, X, hflood⟩ := rep_flood_of_hfail h0 hcov hfail
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
    push_neg at hlt
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
    push_neg at haH
    exact ⟨haF.2, haH.1.1, haH.1.2, haH.2, by omega, by omega,
      by omega⟩
  obtain ⟨g₁, hg₁, g₂, hg₂, V₁, hV₁W, hcount₁, hrefl₁⟩ :=
    two_hubs_common_reflection h0 hcov hm₁ hm₂ hhub₁ hhub₂ W
      (fun a ha => ⟨(hWmem a ha).1, (hWmem a ha).2.1,
        (hWmem a ha).2.2.1, (hWmem a ha).2.2.2.2.1,
        (hWmem a ha).2.2.2.2.2.1⟩)
  obtain ⟨g₁', hg₁', g₃, hg₃, V₂, hV₂V₁, hcount₂, hrefl₂⟩ :=
    two_hubs_common_reflection h0 hcov hm₁ hm₃ hhub₁ hhub₃ V₁
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
    push_neg at hK
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

/-- **Difference blowup or infinite affine corners.**  Splitting
the street dichotomy over all K: a counterexample either has
UNBOUNDED difference multiplicity (for every K some positive
offset δ carries K pairs x, x + δ ∈ A), or beyond every size
threshold it produces affine corners — a K₀-fold blown point n
with a pair street at the difference translate n + b₃ − b₂
through arbitrarily large rotators.  Erdős–Turán closed the sum
door; this closes the difference door except into affinity. -/
theorem difference_blowup_or_affine_corners {A : Set ℕ}
    {N₀ : ℕ} (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∀ K, ∃ δ, 1 ≤ δ ∧ ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A) ∨
    (∃ K₀, ∀ S, ∃ n, (∃ V : Finset ℕ, K₀ ≤ V.card ∧
        ∀ a ∈ V, a ∈ A ∧ ∃ x ∈ A, x + a = n) ∧
      ∃ Q : Finset ℕ, RepFree A N₀ Q ∧ ∃ b₂ ∈ A, ∃ b₃ ∈ A,
        S ≤ b₂ ∧ b₂ < b₃ ∧ ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
          IsPairHub A s (insert b₃ Q)) := by
  by_cases hdiff : ∀ K, ∃ δ, 1 ≤ δ ∧ ∃ V : Finset ℕ,
      K ≤ V.card ∧ ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A
  · exact Or.inl hdiff
  · push_neg at hdiff
    obtain ⟨K₀, hK₀⟩ := hdiff
    refine Or.inr ⟨K₀, fun S => ?_⟩
    rcases street_dichotomy_of_hfail h0 hcov hfail K₀ S with
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
  · push_neg at hfix
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
    · push_neg at hle
      exact ⟨δ₀, hle, V₀, by omega, hV₀m⟩

/-- An affine corner at blown point n and size S: a K₀-fold
reflected point coupled to two basis elements beyond S and a pair
street at the difference translate (s + b₂ = n + b₃). -/
def AffineCorner (A : Set ℕ) (N₀ K₀ n S : ℕ) : Prop :=
  (∃ V : Finset ℕ, K₀ ≤ V.card ∧
    ∀ a ∈ V, a ∈ A ∧ ∃ x ∈ A, x + a = n) ∧
  ∃ Q : Finset ℕ, RepFree A N₀ Q ∧ ∃ b₂ ∈ A, ∃ b₃ ∈ A,
    S ≤ b₂ ∧ b₂ < b₃ ∧ ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
      IsPairHub A s (insert b₃ Q)

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
  · push_neg at hstab
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
    · push_neg at hle
      exact ⟨n₀, hle, hanti n₀ S Ssup (le_max_left _ _) hn₀⟩

/-- **The mirror hall splits.**  In the affine-corner branch the
blown reflection point either STABILIZES — one fixed n serves
corners beyond every size: an infinite affine family clustered at
a single mirror point — or SCATTERS: arbitrarily large blown
points, each with its own affine corner, at every size. -/
theorem affine_corner_fixed_or_scattered {A : Set ℕ}
    {N₀ K₀ : ℕ}
    (hcorner : ∀ S, ∃ n, AffineCorner A N₀ K₀ n S) :
    (∃ n, ∀ S, AffineCorner A N₀ K₀ n S) ∨
    (∀ N S, ∃ n, N < n ∧ AffineCorner A N₀ K₀ n S) :=
  nat_param_stabilize
    (fun _ _ _ hSS h => AffineCorner.anti hSS h) hcorner

/-- Uniform-envelope form of the street dichotomy: ONE free
envelope Q (the flood envelope) serves every K and S.  This is
what the proof always produced; recording it makes the affine
corners comparable across sizes. -/
theorem street_dichotomy_uniform {A : Set ℕ} {N₀ : ℕ}
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
          IsPairHub A s (insert b₃ Q)) := by
  classical
  obtain ⟨P, hPfree, X, hflood⟩ := rep_flood_of_hfail h0 hcov hfail
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
    push_neg at hlt
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
    push_neg at haH
    exact ⟨haF.2, haH.1.1, haH.1.2, haH.2, by omega, by omega,
      by omega⟩
  obtain ⟨g₁, hg₁, g₂, hg₂, V₁, hV₁W, hcount₁, hrefl₁⟩ :=
    two_hubs_common_reflection h0 hcov hm₁ hm₂ hhub₁ hhub₂ W
      (fun a ha => ⟨(hWmem a ha).1, (hWmem a ha).2.1,
        (hWmem a ha).2.2.1, (hWmem a ha).2.2.2.2.1,
        (hWmem a ha).2.2.2.2.2.1⟩)
  obtain ⟨g₁', hg₁', g₃, hg₃, V₂, hV₂V₁, hcount₂, hrefl₂⟩ :=
    two_hubs_common_reflection h0 hcov hm₁ hm₃ hhub₁ hhub₃ V₁
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
    push_neg at hK
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

/-- **The fixed hall extracts a difference.**  If one mirror
point n serves affine corners beyond every size (with a uniform
envelope Q), then stabilizing the basis-pair difference d = b₃ −
b₂ gives: either ONE offset δ carries unbounded difference
multiplicity — corners at all sizes with the same d hand over
infinitely many pairs b, b + δ ∈ A — or the realized differences
grow without bound, producing infinitely many DISTINCT streets
n + d with basis pairs at difference d.  The mirror hall cannot
avoid difference structure. -/
theorem fixed_hall_extracts_difference {A : Set ℕ} {N₀ : ℕ}
    {Q : Finset ℕ} {n : ℕ}
    (hcorner : ∀ S, ∃ b₂ ∈ A, ∃ b₃ ∈ A, S ≤ b₂ ∧ b₂ < b₃ ∧
      ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
        IsPairHub A s (insert b₃ Q)) :
    (∃ δ, 1 ≤ δ ∧ ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A) ∨
    (∀ Δ S, ∃ b₂ ∈ A, ∃ b₃ ∈ A, S ≤ b₂ ∧ b₂ < b₃ ∧
      Δ < b₃ - b₂ ∧ ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
        IsPairHub A s (insert b₃ Q)) := by
  classical
  set C : ℕ → ℕ → Prop := fun d S => 1 ≤ d ∧
    ∃ b₂, b₂ ∈ A ∧ S ≤ b₂ ∧ b₂ + d ∈ A ∧
    ∃ s, s + b₂ = n + (b₂ + d) ∧ N₀ ≤ s ∧
      IsPairHub A s (insert (b₂ + d) Q) with hCdef
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

/-- **THE FOUR ROOMS.**  Composing the street dichotomy, the
corner stabilizations, and the hall extraction, every
counterexample lives in one of four terminal rooms:

  R1  one fixed offset δ with UNBOUNDED difference multiplicity
      (A ∩ (A − δ) infinite: near-translation-invariance);
  R2  difference pairs at arbitrarily large offsets, at every
      multiplicity;
  R3  scattered mirror halls: arbitrarily large blown points n,
      each an affine corner beyond every size;
  R4  a street ladder: ONE mirror point n whose difference
      translates n + d are pair streets for unboundedly large
      realized d — street POSITIONS pinned to a one-parameter
      family, the first crack in target liberty.

Rooms 3 and 4 share one flood envelope Q. -/
theorem counterexample_four_rooms {A : Set ℕ} {N₀ : ℕ}
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
            IsPairHub A s (insert b₃ Q)) ∨
     (∃ n, ∀ Δ S, ∃ b₂ ∈ A, ∃ b₃ ∈ A, S ≤ b₂ ∧ b₂ < b₃ ∧
        Δ < b₃ - b₂ ∧ ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
          IsPairHub A s (insert b₃ Q))) := by
  classical
  have hfree0 : RepFree A N₀ ∅ := by
    intro m hm
    obtain ⟨x, hx, y, hy, hxy⟩ := hcov m hm
    exact ⟨x, hx, y, hy, 0, h0, by omega, Finset.notMem_empty x,
      Finset.notMem_empty y, Finset.notMem_empty 0⟩
  obtain ⟨Q, hQfree, hdich⟩ :=
    street_dichotomy_uniform h0 hcov hfail
  by_cases hdiff : ∀ K, ∃ δ, 1 ≤ δ ∧ ∃ V : Finset ℕ,
      K ≤ V.card ∧ ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A
  · rcases fixed_offset_or_growing hdiff with h | h
    · exact ⟨∅, hfree0, Or.inl h⟩
    · exact ⟨∅, hfree0, Or.inr (Or.inl h)⟩
  · push_neg at hdiff
    obtain ⟨K₀, hK₀⟩ := hdiff
    have hcorner : ∀ S, ∃ n,
        (∃ V : Finset ℕ, K₀ ≤ V.card ∧
          ∀ a ∈ V, a ∈ A ∧ ∃ x ∈ A, x + a = n) ∧
        ∃ b₂, b₂ ∈ A ∧ ∃ b₃, b₃ ∈ A ∧ S ≤ b₂ ∧ b₂ < b₃ ∧
          ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
            IsPairHub A s (insert b₃ Q) := by
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
            IsPairHub A s (insert b₃ Q)) →
        ((∃ V : Finset ℕ, K₀ ≤ V.card ∧
          ∀ a ∈ V, a ∈ A ∧ ∃ x ∈ A, x + a = n) ∧
        ∃ b₂, b₂ ∈ A ∧ ∃ b₃, b₃ ∈ A ∧ S ≤ b₂ ∧ b₂ < b₃ ∧
          ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
            IsPairHub A s (insert b₃ Q)) := by
      intro n S S' hSS h
      obtain ⟨hb, b₂, hb₂A, b₃, hb₃A, hS, rest⟩ := h
      exact ⟨hb, b₂, hb₂A, b₃, hb₃A, by omega, rest⟩
    rcases nat_param_stabilize hanti hcorner with ⟨n, hn⟩ | hesc
    · -- fixed hall: extract the difference ladder
      have hhall : ∀ S, ∃ b₂ ∈ A, ∃ b₃ ∈ A, S ≤ b₂ ∧ b₂ < b₃ ∧
          ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
            IsPairHub A s (insert b₃ Q) := by
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

/-- **The rotator drops out of the ladder.**  In the street
ladder (room R4), taking the basis pair beyond the mirror point
puts the street strictly below the rotator: s = n + b₃ − b₂ < b₃
whenever b₂ > n.  No pair of s can use b₃, so the street is a
PURE-Q street: a fixed finite set pair-hubs infinitely many
explicitly-located targets n + d, each in the shadow Q + A, with
a basis pair at difference d alongside.  Target liberty is broken
on the ladder: positions, envelope, and shadow are all pinned. -/
theorem street_ladder_pure {A : Set ℕ} {N₀ : ℕ}
    {Q : Finset ℕ} {n : ℕ}
    (hcov : PairCovers A N₀)
    (hladder : ∀ Δ S, ∃ b₂ ∈ A, ∃ b₃ ∈ A, S ≤ b₂ ∧ b₂ < b₃ ∧
      Δ < b₃ - b₂ ∧ ∃ s, s + b₂ = n + b₃ ∧ N₀ ≤ s ∧
        IsPairHub A s (insert b₃ Q)) :
    ∀ Δ, ∃ d, Δ < d ∧ N₀ ≤ n + d ∧
      IsPairHub A (n + d) Q ∧
      (∃ b ∈ A, b + d ∈ A) ∧
      (∃ q ∈ Q, ∃ a ∈ A, q + a = n + d) := by
  intro Δ
  obtain ⟨b₂, hb₂A, b₃, hb₃A, hS, hlt, hΔ, s, hs, hsN, hhub⟩ :=
    hladder Δ (n + 1)
  set d := b₃ - b₂ with hd
  have hsd : s = n + d := by omega
  have hsb₃ : s < b₃ := by omega
  have hpure : IsPairHub A (n + d) Q := by
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

/-- **The ladder shadow concentrates.**  The pure ladder's shadow
elements q ∈ Q are finitely many, so ONE q* serves unboundedly
many rungs: the set {n + d − q*} is an infinite subset of A that
is a translate of the realized-difference family — an arithmetic
copy of the ladder inside the basis itself, alongside a basis
pair at each difference d. -/
theorem ladder_shadow_concentrates {A : Set ℕ} {N₀ : ℕ}
    {Q : Finset ℕ} {n : ℕ}
    (hladder : ∀ Δ, ∃ d, Δ < d ∧ N₀ ≤ n + d ∧
      IsPairHub A (n + d) Q ∧ (∃ b ∈ A, b + d ∈ A) ∧
      (∃ q ∈ Q, ∃ a ∈ A, q + a = n + d)) :
    ∃ q ∈ Q, ∀ Δ, ∃ d, Δ < d ∧ N₀ ≤ n + d ∧
      IsPairHub A (n + d) Q ∧ (∃ b ∈ A, b + d ∈ A) ∧
      (∃ a ∈ A, q + a = n + d) := by
  classical
  by_contra hno
  push_neg at hno
  have hDf : ∀ q, ∃ Δq, q ∈ Q → ∀ d, Δq < d → N₀ ≤ n + d →
      IsPairHub A (n + d) Q → (∃ b ∈ A, b + d ∈ A) →
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

/-- **The ladder difference desert.**  A rung reflection
a = n + d − q* (large, hence outside Q) crossed with a higher
rung's pure street forces the translated difference out of the
basis: if q* + (d' − d) ∈ A it must lie in the finite Q.  So for
every large rung, the translated rung-differences avoid A with at
most |Q| exceptions — the ladder digs deserts at its own
difference set. -/
theorem ladder_difference_desert {A : Set ℕ} {Q : Finset ℕ}
    {q n d d' a : ℕ}
    (ha : q + a = n + d) (haA : a ∈ A) (haQ : a ∉ Q)
    (hhub' : IsPairHub A (n + d') Q) (hdd : d ≤ d')
    (hy : q + (d' - d) ∈ A) :
    q + (d' - d) ∈ Q := by
  have hpair : a + (q + (d' - d)) = n + d' := by omega
  rcases hhub' a haA _ hy hpair with h | h
  · exact absurd h haQ
  · exact h

/-- **Room R1 gets teams.**  In the translation room the δ-paired
family {x : x, x + δ ∈ A} is infinite, so the team supply applies
to it: beyond every bound some failing target carries a minimal
hub of size ≥ 2 whose EVERY member has a δ-partner in the basis.
The enemy's teams there are translation-coherent — each team
shifts by δ into a family of fresh representations. -/
theorem translation_room_teams {A : Set ℕ} {N₀ δ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hR1 : ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ x ∈ V, x ∈ A ∧ x + δ ∈ A) :
    ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      IsRepHub A n H ∧ (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
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
    guardian_team_hubs_of_deletion h0 hcov hanchor hfail
      hBA hBinf h0B N
  refine ⟨n, hn, H, hhub, hmin, hcard, ?_⟩
  intro h hh
  have := hmem h hh
  exact ⟨this.1, this.2.1, this.2.2⟩

/-- **The essential element's private stream.**  Erdős 881's own
hypothesis — A is a MINIMAL basis, every element essential — has
been under-used: essentiality of b at order 2 means deleting b
breaks coverage cofinally, i.e. b owns a cofinal stream of
targets whose EVERY pair decomposition uses b.  At each such
target the decomposition is unique: m = b + c with c ∈ A, and no
other pair exists.  Every element of the true 881 configuration
owns infinitely many unique-representation targets. -/
theorem essential_private_pair_stream {A : Set ℕ} {N₀ : ℕ}
    {b : ℕ} (hcov : PairCovers A N₀)
    (hess : ¬∃ N₁, ∀ n, N₁ ≤ n → ∃ x ∈ A, ∃ y ∈ A,
      x ≠ b ∧ y ≠ b ∧ x + y = n) :
    ∀ N, ∃ m, N ≤ m ∧ ∃ c ∈ A, b + c = m ∧
      ∀ x ∈ A, ∀ y ∈ A, x + y = m →
        (x = b ∧ y = c) ∨ (x = c ∧ y = b) := by
  push_neg at hess
  intro N
  obtain ⟨m, hm, hall⟩ := hess (N + N₀)
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := hcov m (by omega)
  have hb₀ : x₀ = b ∨ y₀ = b := by
    by_contra hno
    push_neg at hno
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
    push_neg at hno
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

/-- **The disjoint unique-pair supply.**  In a classically minimal
basis (every positive element essential at order 2), every K
admits K pairwise disjoint pairs (bᵢ, cᵢ) of basis elements whose
sums are unique-decomposition targets.  Fresh choice by height:
each new private target is taken above everything used, so its
companion is automatically fresh. -/
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

/-- **Infinite degree in the unique-sum graph.**  Every essential
element has unboundedly many companions: distinct private targets
give distinct companions c = m − b, so the graph whose edges are
unique-decomposition sums has all degrees infinite.  With
`shared_private_target_is_sum` (edges meet only at forced sums)
and `disjoint_unique_pairs_of_essential` (infinite matchings),
the classical-minimality hypothesis carries a complete graph
theory. -/
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

/-- **Matched deletions field matched teams.**  Classical
minimality supplies an INFINITE matching of unique-sum pairs
(components strictly ascending); deleting all its vertices forces
— by the team supply — cofinal failing targets carrying minimal
hubs of size ≥ 2 made entirely of matched vertices.  Every team
member is half of a unique-decomposition pair: the enemy must
defend with elements that each carry a private target of their
own.  First contact between the classical-minimality graph and
the order-3 machinery. -/
theorem matched_deletion_teams {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
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
        IsRepHub A n H ∧ (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
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
    guardian_team_hubs_of_deletion h0 hcov hanchor hfail
      hBA hBinf h0B N
  refine ⟨n, hn, H, hhub, hminH, hcard, ?_⟩
  intro h hh
  exact hmem h hh

/-- **Classical minimality implies elementwise ℵ₀-minimality.**
Deleting more can only break coverage harder: an infinite
deletion contains a positive element, and the survivors are a
subset of that element's own deletion, whose coverage already
fails cofinally.  Every hmin-theorem in the repository is
therefore available under Erdős 881's true hypothesis. -/
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

end Erdos881
