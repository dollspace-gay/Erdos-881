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

end Erdos881
