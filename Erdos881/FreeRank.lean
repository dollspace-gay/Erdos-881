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
    (hanchor : StreamSurvives A N₀)
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
    (hanchor : StreamSurvives A N₀)
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
    (hanchor : StreamSurvives A N₀)
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


/-! ## Night block 2026-07-25: the absolute floods -/

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


/-! ## The cap suite (hypothesis-free pigeonholes) -/

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


/-! ## Shells: pool leaves and the stratification -/

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
    (hanchor : StreamSurvives A N₀)
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
    (hanchor : StreamSurvives A N₀)
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
    (hanchor : StreamSurvives A N₀)
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


/-! ## The depth tax -/

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
    (hanchor : StreamSurvives A N₀)
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
    (hanchor : StreamSurvives A N₀)
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


/-! ## Higher caps and the conflict law -/

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


/-! ## The robustness branch mechanism -/

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


/-! ## The reflection ledger -/

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


/-! ## The street dichotomy and the four rooms -/

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


/-! ## Mining the street ladder -/

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
    (hanchor : StreamSurvives A N₀)
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


/-! ## The classical-minimality interface -/

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


/-! ## The Ramsey cascade -/

/-- **The unique-sum Ramsey dichotomy.**  Any covering set
contains an infinite ascending subsequence whose pairwise sums
are ALL unique-decomposition targets, or NONE are: colour index
pairs by unique-sum-ness and apply infinite Ramsey.  The
all-unique side is an infinite strong-Sidon configuration inside
A; the none-unique side has every pairwise sum robust.  Both
sides are deletion fodder for the classical-minimality program. -/
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

/-- All-unique branch, hub form: each pairwise sum is a
two-element pair hub — a 2-parameter family of maximally fragile
targets, far denser than the one-parameter street ladder. -/
theorem all_unique_pair_hubs {A : Set ℕ} {g : ℕ → ℕ}
    (huniq : ∀ i j, i < j → ∀ x ∈ A, ∀ y ∈ A,
      x + y = g i + g j →
      (x = g i ∧ y = g j) ∨ (x = g j ∧ y = g i)) :
    ∀ i j, i < j →
      IsPairHub A (g i + g j) ({g i, g j} : Finset ℕ) := by
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

/-- **Clique teams or an independent set.**  Composing the
unique-sum Ramsey dichotomy with the team supply: a
counterexample either contains an infinite ascending sequence
with NO unique pairwise sums (the independent set), or an
infinite Sidon clique whose deletion forces cofinal minimal teams
drawn from the clique — teams whose members' own pairwise sums
are unique-decomposition targets.  The enemy defends the clique's
2-parameter fragile family with defenders married inside it. -/
theorem clique_or_independent_teams {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ (∀ i, g i ∈ A) ∧
      ((∀ i j, i < j →
          ¬(∀ x ∈ A, ∀ y ∈ A, x + y = g i + g j →
            (x = g i ∧ y = g j) ∨ (x = g j ∧ y = g i))) ∨
       ((∀ i j, i < j →
          IsPairHub A (g i + g j) ({g i, g j} : Finset ℕ)) ∧
        ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
          IsRepHub A n H ∧ (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
          2 ≤ H.card ∧ ∀ h ∈ H, ∃ i, h = g i)) := by
  classical
  obtain ⟨g, hgmono, hgA, hgpos, hbranch⟩ :=
    unique_sum_ramsey hcov
  refine ⟨g, hgmono, hgA, ?_⟩
  rcases hbranch with huniq | hindep
  · right
    refine ⟨all_unique_pair_hubs huniq, ?_⟩
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
      guardian_team_hubs_of_deletion h0 hcov hanchor hfail
        hBA hBinf h0B N
    refine ⟨n, hn, H, hhub, hminH, hcard, ?_⟩
    intro h hh
    obtain ⟨i, hi⟩ := hmem h hh
    exact ⟨i, hi.symm⟩
  · exact Or.inl hindep

/-- **Second-order Ramsey on the independent branch.**  Given an
ascending sequence in A, colour index pairs by whether the sum
g i + g j has a decomposition avoiding the whole range of g.
Homogenizing yields a subsequence g' = g ∘ f with: every pairwise
sum has a range-avoiding alternative (so the sum square SURVIVES
deleting the subsequence — its targets cannot be failing targets
of that deletion), or no pairwise sum has one (every
decomposition of the sum square routes through the range). -/
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
    push_neg at hno
    exact h2 (by
      exact ⟨x, hx, y, hy, hno.1, hno.2, hxy⟩)

/-- **The surviving sum square.**  In the avoiding-alternatives
branch, the pairwise sums of the subsequence retain 0-padded
representations avoiding the subsequence itself: no sum-square
target can be a failing target of the subsequence's deletion.
The first verified NEGATIVE placement law for failures — an
infinite 2-parameter region failures must avoid. -/
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

/-- **THE RAMSEY TRICHOTOMY.**  Every covering set contains an
infinite ascending positive sequence T of one of three kinds:

  (C1) a Sidon CLIQUE — every pairwise sum is a two-element pair
       hub {T i, T j} (unique decomposition);
  (C2) a SELF-AVOIDING sequence — every pairwise sum retains a
       representation avoiding all of T, so no sum-square target
       can fail under the T-deletion (negative placement law);
  (C3) an R-ROUTED sequence — some positive basis family R ⊇ T
       carries every decomposition of every pairwise sum.

Pure combinatorics over covering + 0 ∈ A; two nested infinite
Ramsey passes. -/
theorem ramsey_trichotomy_of_covering {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) :
    ∃ T : ℕ → ℕ, StrictMono T ∧ (∀ i, T i ∈ A) ∧
      (∀ i, 0 < T i) ∧
      ((∀ i j, i < j →
          IsPairHub A (T i + T j) ({T i, T j} : Finset ℕ)) ∨
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
      Or.inl (all_unique_pair_hubs huniq)⟩
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

/-- **THE CUBE DICHOTOMY** (order-3 Ramsey, the problem in
miniature).  Every covering set contains an infinite ascending
positive sequence T inside a positive family R with: every
triple sum T i + T j + T k has a representation avoiding R
entirely — so the T-deletion leaves its own sum CUBE alive at
order 3, and failing targets of that deletion must dodge an
infinite 3-parameter region — or every representation of every
triple sum routes through R, the enemy's dream configuration
realized on one sequence.  The gap between the surviving-cube
branch and full survival (all late targets, not just the cube)
is exactly Erdős 881. -/
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
    push_neg at hno
    exact h2 ⟨x, hx, y, hy, z, hz, hno.1, hno.2.1, hno.2.2,
      hxyz⟩

/-- **THE COMPLETENESS REDUCTION.**  If some infinite family
T ⊆ A is COMPLETE (every late target is a finite subset-sum of
it) and SELF-AVOIDING at all subset arities (every such subset
sum has an order-3 representation avoiding T), then A∖T is an
order-3 basis: T is a surviving deletion and the counterexample
dies.  The Ramsey cascade produces self-avoidance branch-wise
(`cube_avoidance_ramsey`, tuples version pending); completeness
is what Ramsey thinning destroys.  Erdős 881 (k = 2), sufficient
form: every minimal basis contains a complete self-avoiding
family. -/
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


/-! ## The omega pinch -/

/-- **THE ω-AVOIDANCE DICHOTOMY.**  Homogenizing the
self-avoidance colouring at EVERY arity (nested subsequences,
one fixed base range R, diagonal extraction): every covering set
contains an ascending positive sequence T inside a positive
family R such that either every tail subset-sum of T (any arity)
has a representation avoiding R — the deletion of T leaves its
ENTIRE tail subset-sum semigroup alive, so failing targets dodge
it at every arity — or some fixed arity r is fully routed
through R.  Combined with `survival_of_complete_avoiding`, the
only gap to a full solution is the density the diagonal loses. -/
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
    push_neg at hno
    exact h2 ⟨x, hx, y, hy, z, hz, hno.1, hno.2.1, hno.2.2,
      hxyz⟩
  · left
    push_neg at hex
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

/-- **Complete families are blocked** (enemy-side interface,
contrapositive of the completeness reduction).  Under hfail,
every infinite complete family T ⊆ A has, beyond every bound, a
finite subset whose sum admits no representation avoiding T: the
enemy must post a blocked subset-sum against every complete
family, cofinally.  Its defence budget is measured in blocked
subset-sums per family per window. -/
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
  push_neg at hnb
  obtain ⟨n, hn, hnofail⟩ := hnb (N + N₂)
  obtain ⟨S, hST, hsum⟩ := hcomp n (by omega)
  refine ⟨S, hST, by omega, ?_⟩
  intro x hx y hy z hz hxyz
  by_contra hno
  push_neg at hno
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

/-- **The completeness criterion.**  A sequence starting at 1
whose each term is at most one more than the sum of its
predecessors has subset sums covering every value up to the
total: greedy from the top.  This is the bridge between the
greedy probe's high density and `survival_of_complete_avoiding`:
a self-avoiding family with small gaps is complete, hence a
surviving deletion. -/
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
    · push_neg at hle
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

/-- **Bootstrap completeness.**  The offset form of the
completeness criterion for real bases (which need not contain 1):
if the first K₀+1 terms' subset sums cover an initial window
[B, C₀], and each later term is at most one more than the
interval already reachable, then subset sums cover [B, C₀ + tail
sum] at every stage.  Interval-extension induction. -/
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
      · push_neg at hle
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
/-- Corep confinement at a pair street: any basis element outside
the hub pairs with the street only through hub elements — its
corep lands INSIDE the finite hub. -/
theorem pair_hub_corep_confined {A : Set ℕ} {s : ℕ}
    {H : Finset ℕ} (hhub : IsPairHub A s H) {a a' : ℕ}
    (ha : a ∈ A) (haH : a ∉ H) (ha' : a' ∈ A)
    (hsum : a + a' = s) : a' ∈ H := by
  rcases hhub a ha a' ha' hsum with h | h
  · exact absurd h haH
  · exact h

/-! ## Nash-Williams: chaining the shell antichain -/

/-- **The shell Higman chain.**  The first Nash-Williams step of
the chaining program: the enemy's shells, read as sorted lists,
form a sequence in the Higman well-quasi-order (lists over ℕ
under pointwise-≤ sublist embedding), so an infinite subsequence
of shells is a CHAIN — each shell embeds, dominated pointwise,
into every later one.  The enemy's antichain of freedoms carries
a canonical infinite ascending spine; converting this
embedding-chain into a freeness chain is the remaining distance
to a branch. -/
theorem shell_higman_chain {A : Set ℕ} {N₀ : ℕ}
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
        ∃ m, N₀ ≤ m ∧ IsRepHub A m (insert b (Q k))) ∧
      ∃ σ : ℕ ↪o ℕ, ∀ m n, m ≤ n →
        List.SublistForall₂ (· ≤ ·)
          ((Q (σ m)).sort (· ≤ ·)) ((Q (σ n)).sort (· ≤ ·)) := by
  classical
  obtain ⟨Q, hne, hmem, hfree, hdisj, hguard⟩ :=
    absolute_shell_stratification h0 hcov hanchor hfail
  haveI hwqo : WellQuasiOrderedLE ℕ :=
    wellQuasiOrderedLE_iff_wellFoundedLT.mpr inferInstance
  have hpwo : (Set.univ : Set ℕ).PartiallyWellOrderedOn
      (· ≤ ·) :=
    Set.isPWO_of_wellQuasiOrderedLE _
  haveI hrefl : IsRefl (List ℕ)
      (List.SublistForall₂ ((· ≤ ·) : ℕ → ℕ → Prop)) :=
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

/-- **THE SPINE LINEAGE.**  Walking through the Nash-Williams
door: consecutive Higman embeddings along the shell chain
compose into element lineages, and shell disjointness makes
every step STRICT.  The enemy's stratification threads a
canonical strictly increasing sequence meeting one spine shell
after another — an infinite ascending skeleton assembled from
the enemy's own free material.  The branch program's raw
spine. -/
theorem spine_lineage {A : Set ℕ} {N₀ : ℕ}
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
        ∃ m, N₀ ≤ m ∧ IsRepHub A m (insert b (Q k))) ∧
      StrictMono x ∧ (∀ t, x t ∈ Q (σ t)) := by
  classical
  obtain ⟨Q, hne, hmem, hfree, hdisj, hguard, σ, hσ⟩ :=
    shell_higman_chain h0 hcov hanchor hfail
  -- step: an element of a spine shell has a strictly larger
  -- partner in the next spine shell
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

/-- **The board is set.**  Against EVERY subsequence of the
canonical spine, the enemy must post a stall: some finite prefix
of lineage elements becomes a full hub at some target.  The
adaptive endgame is now a game on canonical material — the
constructor plays subsequences of the spine, the enemy must
answer each with a hub made of spine elements, and every hub it
posts is subject to the cap suite, the depth tax, and the sharer
laws.  This theorem is the game board; the winning strategy is
the remaining work. -/
theorem spine_stalls_hereditarily {A : Set ℕ} {N₀ : ℕ}
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
          IsRepHub A m ((Finset.range J).image (fun t =>
            x (τ t))) := by
  classical
  obtain ⟨Q, σ, x, hne, hmem, hfree, hdisj, hguard, hxmono,
    hxmem⟩ := spine_lineage h0 hcov hanchor hfail
  refine ⟨Q, σ, x, hxmono, hxmem, hfree,
    hmem, ?_⟩
  intro τ hτ
  have hdie := free_prefixes_die_of_hfail h0 hcov hfail
    (fun t => x (τ t)) (hxmono.comp hτ)
    (fun t => (hmem _ _ (hxmem (τ t))).1)
    (fun t => (hmem _ _ (hxmem (τ t))).2)
  push_neg at hdie
  obtain ⟨J, hJ⟩ := hdie
  rw [RepFree] at hJ
  push_neg at hJ
  obtain ⟨m, hm, hall⟩ := hJ
  refine ⟨J, m, hm, ?_⟩
  intro a ha b hb c hc hsum
  by_contra hmiss
  push_neg at hmiss
  obtain ⟨h1, h2, h3⟩ := hmiss
  exact h3 (hall a ha b hb c hc hsum h1 h2)

/-- **RANK OR LOCKSTEP.**  Spine shell sizes are non-decreasing
(sublist embeddings), so they are unbounded — the counterexample
contains FREE SETS OF EVERY SIZE, forcing infinite root rank and
closing the finite-rank room at the root — or eventually
constant, and then equal-length sublist embeddings are FULL
pointwise dominations: beyond some point the spine shells march
in lockstep, the t-th shell's sorted list dominated coordinate
by coordinate inside the (t+1)-st.  Either the rank door closes
or the enemy's shells are s parallel strictly increasing
columns. -/
theorem spine_rank_or_lockstep {A : Set ℕ} {N₀ : ℕ}
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
    shell_higman_chain h0 hcov hanchor hfail
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
    push_neg at hunb
    obtain ⟨c₀, hc₀⟩ := hunb
    -- monotone bounded: eventually constant
    have hstab : ∃ T, ∀ t, T ≤ t →
        (Q (σ t)).card = (Q (σ T)).card := by
      by_contra hno
      push_neg at hno
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

/-- **The fork, in rank form.**  Either the root rank of the full
freeness tree is at least ω — free sets of every size exist, and
the finite-rank room is closed at the root — or the spine goes
lockstep.  Mechanical combination of `spine_rank_or_lockstep`
with `free_set_card_le_rank`. -/
theorem root_rank_omega_or_lockstep {A : Set ℕ} {N₀ : ℕ}
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
  rcases spine_rank_or_lockstep h0 hcov hanchor hfail with
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

/-- **The lockstep columns.**  In the lockstep branch the spine
shells are literally s parallel strictly increasing columns: the
k-th smallest elements across the spine form a strictly monotone
sequence, and every shell is exactly the set of current column
values.  The enemy's entire late freedom supply is an s-lane
highway. -/
theorem lockstep_columns {A : Set ℕ} {N₀ : ℕ}
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

/-- Fork with guardianship carried through (primed form of
`spine_rank_or_lockstep`). -/
theorem spine_rank_or_lockstep' {A : Set ℕ} {N₀ : ℕ}
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
        ∃ m, N₀ ≤ m ∧ IsRepHub A m (insert b (Q k))) ∧
      1 ≤ s ∧
      (∀ t, T ≤ t → (Q (σ t)).card = s) ∧
      (∀ t, T ≤ t → List.Forall₂ (· ≤ ·)
        ((Q (σ t)).sort (· ≤ ·))
        ((Q (σ (t + 1))).sort (· ≤ ·)))) := by
  classical
  obtain ⟨Q, hne, hmem, hfree, hdisj, hguard, σ, hσ⟩ :=
    shell_higman_chain h0 hcov hanchor hfail
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
    push_neg at hunb
    obtain ⟨c₀, hc₀⟩ := hunb
    have hstab : ∃ T, ∀ t, T ≤ t →
        (Q (σ t)).card = (Q (σ T)).card := by
      by_contra hno
      push_neg at hno
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

/-- **The one-lane clique.**  If the lockstep width is s = 1 the
spine shells are singletons {x t}, and hierarchical guardianship
makes every LATER spine value a guardian of every EARLIER
singleton shell: each pair of one-lane spine values is a full
two-element hub somewhere.  A single-lane enemy carries an
infinite d = 1 crystal clique on canonical material. -/
theorem lockstep_one_lane_clique {A : Set ℕ} {N₀ : ℕ}
    {Q : ℕ → Finset ℕ} {σ : ℕ ↪o ℕ} {T : ℕ} {x : ℕ → ℕ}
    (hmem : ∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h)
    (hdisj : ∀ j k, j < k → Disjoint (Q j) (Q k))
    (hguard : ∀ k, ∀ b ∈ A, 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
      ∃ m, N₀ ≤ m ∧ IsRepHub A m (insert b (Q k)))
    (hsingle : ∀ t, T ≤ t → Q (σ t) = {x t}) :
    ∀ t t', T ≤ t → t < t' →
      ∃ m, N₀ ≤ m ∧ IsRepHub A m ({x t', x t} : Finset ℕ) := by
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

/-- **Lane guardianship.**  On the lockstep highway every later
column value guards every earlier spine shell: the duty ledger
of the s-lane enemy is indexed by (lane, later time, earlier
time), every entry a hub of uniform size s + 1.  General-s form
of the one-lane clique. -/
theorem lockstep_lane_guardianship {A : Set ℕ} {N₀ : ℕ}
    {Q : ℕ → Finset ℕ} {σ : ℕ ↪o ℕ} {T s : ℕ}
    {y : Fin s → ℕ → ℕ}
    (hmem : ∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h)
    (hdisj : ∀ j k, j < k → Disjoint (Q j) (Q k))
    (hguard : ∀ k, ∀ b ∈ A, 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
      ∃ m, N₀ ≤ m ∧ IsRepHub A m (insert b (Q k)))
    (hy : ∀ k t, y k t ∈ Q (σ (T + t))) :
    ∀ (k : Fin s) (t t' : ℕ), t < t' →
      ∃ m, N₀ ≤ m ∧
        IsRepHub A m (insert (y k t') (Q (σ (T + t)))) := by
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

/-- **The highway tax.**  Composing the depth tax with lockstep
membership: every sufficiently large column value at spine time
t pays a guardian duty at height at least N₀ + (T + t − 1)/3.
The s-lane highway carries linearly growing duty heights on a
fixed-width structure — the quantitative burden of the lockstep
branch. -/
theorem highway_tax {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {Q : ℕ → Finset ℕ} {σ : ℕ ↪o ℕ} {T s : ℕ}
    {y : Fin s → ℕ → ℕ}
    (hmem : ∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h)
    (hdisj : ∀ j k, j < k → Disjoint (Q j) (Q k))
    (hguard : ∀ k, ∀ b ∈ A, 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
      ∃ m, N₀ ≤ m ∧ IsRepHub A m (insert b (Q k)))
    (hy : ∀ k t, y k t ∈ Q (σ (T + t))) :
    ∃ X, ∀ (k : Fin s) (t : ℕ), X ≤ y k t → 1 ≤ T + t →
      ∃ j, j < σ (T + t) ∧ ∃ m, N₀ + (T + t - 1) / 3 ≤ m ∧
        N₀ ≤ m ∧ IsRepHub A m (insert (y k t) (Q j)) := by
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

/-- **Uniform streets over every shell.**  One lane supplies
infinitely many guardians for each spine shell, and the sharer
law caps three guardians per target: every shell owns
unboundedly many DISTINCT duty targets, all hubbed by
(s+1)-sized envelopes.  On the lockstep highway every shell
carries an infinite street of uniformly fragile targets. -/
theorem lockstep_uniform_streets {A : Set ℕ} {N₀ : ℕ}
    {Q : ℕ → Finset ℕ} {σ : ℕ ↪o ℕ} {T s : ℕ}
    {y : Fin s → ℕ → ℕ}
    (hmem : ∀ k, ∀ h ∈ Q k, h ∈ A ∧ 0 < h)
    (hdisj : ∀ j k, j < k → Disjoint (Q j) (Q k))
    (hguard : ∀ k, ∀ b ∈ A, 0 < b → (∀ j, j ≤ k → b ∉ Q j) →
      ∃ m, N₀ ≤ m ∧ IsRepHub A m (insert b (Q k)))
    (hfree : ∀ k, RepFree A N₀ (Q k))
    (hy : ∀ k t, y k t ∈ Q (σ (T + t)))
    (hymono : ∀ k, StrictMono (y k)) (hs : 1 ≤ s) :
    ∀ t K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ m ∈ V, N₀ ≤ m ∧ ∃ b ∈ A, b ∉ Q (σ (T + t)) ∧
        IsRepHub A m (insert b (Q (σ (T + t)))) := by
  classical
  intro t K
  set k₀ : Fin s := ⟨0, by omega⟩ with hk₀
  have hlane := lockstep_lane_guardianship hmem hdisj hguard hy
  have hduty : ∀ i : ℕ, ∃ m, N₀ ≤ m ∧
      IsRepHub A m (insert (y k₀ (t + 1 + i))
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
      three_guardians_per_rep_target (hfree (σ (T + t))) hmN
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

/-- **The anchor dichotomy** (integrity rescue for the
anchor-conditioned arcs).  Lab audit shows carry-free worlds
(Cantor) have NO anchors: every double 2c decomposes centrally
only.  This theorem makes the failure mode itself a weapon:
either anchors exist — and the entire shell/spine/encirclement
machinery applies — or some single element g₀ routes every
noncentral decomposition of every double: EVERY double 2c is a
two-element pair hub {c, g₀}, a universal crystal-like family at
the explicit positions 2·A.  No counterexample escapes both. -/
theorem anchor_dichotomy {A : Set ℕ} :
    (∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g) ∨
    (∃ g₀, ∀ c ∈ A, 0 < c → c ≠ g₀ →
      IsPairHub A (2 * c) ({c, g₀} : Finset ℕ)) := by
  classical
  by_cases h : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g
  · exact Or.inl h
  · right
    push_neg at h
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
/-- **Anchor-free doubles are thin.**  In the no-anchor branch
every double 2c has its entire pair life inside three explicit
values {c, g₀, 2c − g₀}: r₂(2c) ≤ 3 uniformly, at the explicit
one-parameter family of positions 2·A.  Combined with unbounded
r₂ (anchor-free theorem), blown targets avoid the doubled basis
entirely — the anchor-free enemy's blowups live off 2·A. -/
theorem no_anchor_doubles_thin {A : Set ℕ} {g₀ c : ℕ}
    (hhub : IsPairHub A (2 * c) ({c, g₀} : Finset ℕ)) :
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

/-- Sharpening the no-anchor branch: the router g₀ is a basis
element, or every double is PURELY CENTRAL — 2c decomposes only
as c + c, and the whole basis is self-married: each element owns
the unique-decomposition target 2c at the explicit position
family 2·A.  Carry-free worlds (Cantor) realize the central
branch exactly. -/
theorem no_anchor_central_or_member {A : Set ℕ} {g₀ : ℕ}
    (hroute : ∀ c ∈ A, 0 < c → c ≠ g₀ →
      IsPairHub A (2 * c) ({c, g₀} : Finset ℕ)) :
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

/-- **Total pinning in the central branch.**  Purely central
doubles mean every element pair-OWNS its double: {c} is a full
singleton pair hub at 2c.  Consequently any deletion B fails at
order 2 exactly on the explicit set 2·B — the first TOTAL
placement law of the campaign: in the central branch there is no
order-2 target liberty at all.  (Order 3 keeps its freedom
through nonzero triples; that residue is where the carry-free
enemy would have to live.) -/
theorem central_branch_singleton_hubs {A : Set ℕ} {g₀ : ℕ}
    (hcentral : ∀ c ∈ A, 0 < c → c ≠ g₀ → ∀ w ∈ A, ∀ w' ∈ A,
      w + w' = 2 * c → w = c ∧ w' = c) :
    ∀ c ∈ A, 0 < c → c ≠ g₀ →
      IsPairHub A (2 * c) ({c} : Finset ℕ) := by
  intro c hcA hcpos hcg w hw w' hw' hsum
  obtain ⟨h1, _⟩ := hcentral c hcA hcpos hcg w hw w' hw' hsum
  exact Or.inl (by simp [h1])

/-- **Central minimality for free.**  In the purely central
branch every infinite deletion automatically breaks order-2
coverage at its own doubles: ℵ₀-minimality is not a hypothesis
there but a consequence — consistent with the verified Cantor
instance, which is carry-free, central, and ℵ₀-minimal. -/
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

/-- **The central branch is progression-free.**  Centrality of
doubles is exactly midpoint-freeness: no two distinct basis
elements average to a positive basis element other than the
router.  Hence the central enemy carries no nontrivial 3-term
arithmetic progression whose middle is a positive non-router
element — it is a Salem–Spencer-type object, living where
Behrend density (≫ √n) still permits covering.  Cantor is
midpoint-free, confirming the classification. -/
theorem central_branch_no_three_AP {A : Set ℕ} {g₀ : ℕ}
    (hcentral : ∀ c ∈ A, 0 < c → c ≠ g₀ → ∀ w ∈ A, ∀ w' ∈ A,
      w + w' = 2 * c → w = c ∧ w' = c) :
    ∀ a d, 0 < d → a ∈ A → a + d ∈ A → a + 2 * d ∈ A →
      a + d = g₀ ∨ a + d = 0 := by
  intro a d hd haA hadA ha2dA
  by_contra hno
  push_neg at hno
  obtain ⟨hg, h0⟩ := hno
  have hpos : 0 < a + d := by omega
  have hsum : a + (a + 2 * d) = 2 * (a + d) := by omega
  obtain ⟨h1, h2⟩ := hcentral (a + d) hadA hpos hg
    a haA (a + 2 * d) ha2dA hsum
  omega

/-- **The first canonical obligation.**  The odd elements form
an enemy-independent deletion: if they are infinite, hfail owes
cofinal targets whose EVERY representation uses an odd basis
element — the all-even sector must die cofinally.  Opening move
of the canonical (residue-grid) deletion program. -/
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
  push_neg at hnb
  obtain ⟨n, hn, hnofail⟩ := hnb N
  refine ⟨n, hn, ?_⟩
  intro x hx y hy z hz hsum
  by_contra hno
  push_neg at hno
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

/-- **The canonical obligation, fully general.**  For ANY
property P cutting an infinite slice of the basis, hfail owes
cofinal targets whose every representation uses a P-element.
The residue grid, the odd deletion, digit classes, column
families — every enemy-independent slice generates its own
obligation schedule.  The adaptive game's full opening book. -/
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
  push_neg at hnb
  obtain ⟨n, hn, hnofail⟩ := hnb N
  refine ⟨n, hn, ?_⟩
  intro x hx y hy z hz hsum
  by_contra hno
  push_neg at hno
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

/-- **The grid cap.**  A representation has three parts and each
part has one residue: at most three residue-class obligations
per modulus can fire at a single target.  Four distinct classes
mod m whose obligations all fire at n are impossible — the
enemy's obligation schedule against the residue grid must spread
across at least ⌈(width of A's residue support)/3⌉ distinct
targets per modulus, cofinally.  Hypothesis-free pigeonhole. -/
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

/-- **The per-modulus width dichotomy** (the corrected grid
law).  At every modulus m ≥ 1 a set either has four infinite
residue classes — feeding four canonical obligations that the
grid cap forces apart — or its tail concentrates in at most
three classes: a two-scale-style alignment at that modulus.
Pure classical combinatorics. -/
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
    push_neg at hcard
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

/-- **Grid pressure or alignment** (the grid capstone).  Under
hfail, at every modulus: four infinite classes yield four
cofinal obligation streams that no represented target can serve
simultaneously — the enemy's schedule must permanently split —
or the tail concentrates in at most three classes, a two-scale
alignment at that modulus.  Every modulus interrogates the
enemy: spread or align. -/
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

/-- **The pure four-hub cap.**  Four pairwise disjoint envelopes
cannot all be full hubs at one represented target: a
representation has three parts and each part lies in at most one
envelope.  The simplest cap of the suite — no guardians, no
freeness, no escape.  Feeds the spine stall stream: pairwise
disjoint stall windows share targets at most three-fold, so
cofinal stall streams carry cofinally many DISTINCT targets. -/
theorem four_disjoint_full_hubs_impossible {A : Set ℕ} {m : ℕ}
    {H : Fin 4 → Finset ℕ}
    (hdisj : ∀ i j, i ≠ j → Disjoint (H i) (H j))
    (hrep : ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = m)
    (hhub : ∀ i, IsRepHub A m (H i)) : False := by
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

/-- A free set is a full hub of no target: freeness hands the
target a representation avoiding the set, hub-ness forbids it.
The fundamental exclusion between the two sides of the game. -/
theorem free_set_never_hub {A : Set ℕ} {N₀ m : ℕ}
    {P : Finset ℕ} (hfree : RepFree A N₀ P) (hm : N₀ ≤ m)
    (hhub : IsRepHub A m P) : False := by
  obtain ⟨x, hx, y, hy, z, hz, hsum, hxP, hyP, hzP⟩ := hfree m hm
  rcases hhub x hx y hy z hz hsum with h | h | h
  · exact hxP h
  · exact hyP h
  · exact hzP h

/-- **Stall windows are wide, and stall defence is cross-shell.**
Any stall window contained in a single (free) shell would be a
free full hub — impossible.  Since consecutive spine values lie
in distinct shells, every stall window of the spine stream has
length at least two, and more generally every sub-hub of every
stall window must straddle at least two shells: the enemy's
defence against its own spine is intrinsically a cross-shell
phenomenon, exactly where the conflict law and the caps live. -/
theorem stall_window_not_in_shell {A : Set ℕ} {N₀ m : ℕ}
    {Q : Finset ℕ} {W : Finset ℕ}
    (hQfree : RepFree A N₀ Q) (hWQ : W ⊆ Q) (hm : N₀ ≤ m)
    (hhub : IsRepHub A m W) : False :=
  free_set_never_hub (RepFree.mono hWQ hQfree) hm hhub

/-- **The spine stall stream.**  Playing consecutive shifts of
the spine yields pairwise disjoint stall WINDOWS — finite blocks
of consecutive lineage values, each a full hub at its own
target.  By the pure four-hub cap a target serves at most three
disjoint windows, so the stream carries unboundedly many
DISTINCT stall targets: the enemy's defence against its own
spine is an infinite ledger of window-hubs with an infinite
target street.  The racing-proof battlefield, fully
formalized. -/
theorem spine_stall_stream {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
    ∃ st len : ℕ → ℕ, ∃ tgt : ℕ → ℕ,
      (∀ i, 2 ≤ len i) ∧
      (∀ i, st (i + 1) = st i + len i) ∧
      (∀ i, N₀ ≤ tgt i ∧ IsRepHub A (tgt i)
        ((Finset.range (len i)).image (fun j => x (st i + j)))) ∧
      (∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧ ∀ v ∈ V, ∃ i, tgt i = v) := by
  classical
  obtain ⟨Q, σ, x, hxmono, hxmem, hQfree, hQmem, hstall⟩ :=
    spine_stalls_hereditarily h0 hcov hanchor hfail
  have hxA : ∀ t, x t ∈ A ∧ 0 < x t :=
    fun t => hQmem _ _ (hxmem t)
  -- one stall window starting at any position; the free-shell
  -- exclusion forces width ≥ 2
  have hwin : ∀ s : ℕ, ∃ J m, 2 ≤ J ∧ N₀ ≤ m ∧
      IsRepHub A m ((Finset.range J).image
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
      exact stall_window_not_in_shell (hQfree (σ s))
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
    push_neg at hbig
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
    refine four_disjoint_full_hubs_impossible
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

/-- **The exact duality.**  Freeness is precisely never being a
full hub: the two sides of the whole campaign — free sets (the
constructor's material) and hubs (the enemy's defence) — are
logical complements at every target.  With this, minimal stall
windows have FREE proper prefixes: window length measures
exactly how much freeness the shifted spine accumulates before
the enemy strikes, so bounded window lengths mean bounded free
prefixes and unbounded lengths hand the constructor unbounded
cross-shell free sets (root rank ≥ ω — the fork again, on the
game board). -/
theorem repFree_iff_forall_not_hub {A : Set ℕ} {N₀ : ℕ}
    {P : Finset ℕ} :
    RepFree A N₀ P ↔ ∀ m, N₀ ≤ m → ¬IsRepHub A m P := by
  constructor
  · intro hfree m hm hhub
    exact free_set_never_hub hfree hm hhub
  · intro hnot m hm
    have h1 := hnot m hm
    rw [IsRepHub] at h1
    push_neg at h1
    obtain ⟨x, hx, y, hy, z, hz, hsum, hxP, hyP, hzP⟩ := h1
    exact ⟨x, hx, y, hy, z, hz, hsum, hxP, hyP, hzP⟩

/-- **WIDTH OR RANK** (the fork on the game board).  Take the
MINIMAL stall window at every shift of the spine; by the exact
duality its proper prefixes are free.  Either the minimal
widths are unbounded — handing the constructor cross-shell free
sets of every size, hence root rank ≥ ω — or one width bound L
serves every shift: at every position of the spine a window of
between 2 and L consecutive lineage values is a full hub.  The
enemy must fund infinite rank or defend with uniformly narrow,
uniformly fragile, cofinally distinct window-hubs against its
own canonical material.  The night's closing theorem. -/
theorem stall_width_or_rank {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
      RepFree A N₀ P ∧ c ≤ P.card) ∨
    (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
      ∃ L, ∀ s : ℕ, ∃ J m, 2 ≤ J ∧ J ≤ L ∧ N₀ ≤ m ∧
        IsRepHub A m ((Finset.range J).image
          (fun j => x (s + j)))) := by
  classical
  obtain ⟨Q, σ, x, hxmono, hxmem, hQfree, hQmem, hstall⟩ :=
    spine_stalls_hereditarily h0 hcov hanchor hfail
  have hxA : ∀ t, x t ∈ A ∧ 0 < x t :=
    fun t => hQmem _ _ (hxmem t)
  set Pred : ℕ → ℕ → Prop := fun s J => ∃ m, N₀ ≤ m ∧
    IsRepHub A m ((Finset.range J).image (fun j => x (s + j)))
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
    push_neg at hlt
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
      exact stall_window_not_in_shell (hQfree (σ s))
        (Finset.singleton_subset_iff.2 (by
          simpa using hxmem s)) hm hhub
  by_cases hbnd : ∃ L, ∀ s, Nat.find (hne s) ≤ L
  · right
    obtain ⟨L, hL⟩ := hbnd
    refine ⟨x, hxmono, hxA, L, fun s => ?_⟩
    obtain ⟨m, hm, hhub⟩ := hJdef s
    exact ⟨Nat.find (hne s), m, hJ2 s, hL s, hm, hhub⟩
  · left
    push_neg at hbnd
    intro c
    obtain ⟨s, hs⟩ := hbnd (c + 1)
    -- the prefix of length c + 1 is a proper prefix: free
    have hfree' : RepFree A N₀ ((Finset.range (c + 1)).image
        (fun j => x (s + j))) := by
      rw [repFree_iff_forall_not_hub]
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

/-- **Width or rank, along every subsequence.**  The fork holds
on every strictly monotone reindexing of the spine: unbounded
free sets (root rank ≥ ω), or a uniform width bound for the
minimal stall windows of THAT subsequence.  Since hub-windows
are up-monotone, the narrow branch makes every L-block of the
subsequence a full hub — and the constructor may then recurse on
sparser subsequences: the narrow branch is self-similar, and the
recursion is now formally available at every level. -/
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
        IsRepHub A m ((Finset.range J).image
          (fun j => x (τ (s + j)))))) := by
  classical
  obtain ⟨Q, σ, x, hxmono, hxmem, hQfree, hQmem, hstall⟩ :=
    spine_stalls_hereditarily h0 hcov hanchor hfail
  have hxA : ∀ t, x t ∈ A ∧ 0 < x t :=
    fun t => hQmem _ _ (hxmem t)
  refine ⟨x, hxmono, hxA, ?_⟩
  intro τ hτ
  set Pred : ℕ → ℕ → Prop := fun s J => ∃ m, N₀ ≤ m ∧
    IsRepHub A m ((Finset.range J).image
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
    push_neg at hlt
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
      exact stall_window_not_in_shell (hQfree (σ (τ s)))
        (Finset.singleton_subset_iff.2 (by
          simpa using hxmem (τ s))) hm hhub
  by_cases hbnd : ∃ L, ∀ s, Nat.find (hne s) ≤ L
  · right
    obtain ⟨L, hL⟩ := hbnd
    refine ⟨L, fun s => ?_⟩
    obtain ⟨m, hm, hhub⟩ := hJdef s
    exact ⟨Nat.find (hne s), m, hJ2 s, hL s, hm, hhub⟩
  · left
    push_neg at hbnd
    intro c
    obtain ⟨s, hs⟩ := hbnd (c + 1)
    have hfree' : RepFree A N₀ ((Finset.range (c + 1)).image
        (fun j => x (τ (s + j)))) := by
      rw [repFree_iff_forall_not_hub]
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

/-- **The narrow branch's located street.**  Uniform width L
gives disjoint windows at L-spaced shifts; the pure cap bounds
target-sharing at three, so the narrow branch carries
unboundedly many DISTINCT targets, each hubbed by a located
window of 2..L consecutive spine values.  Unlike the V10
supply, the hubs here are made of KNOWN material at KNOWN
positions: the fork's narrow side is a fully located
uniform-width street. -/
theorem narrow_located_street {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    {x : ℕ → ℕ} {L : ℕ} (hxmono : StrictMono x)
    (hnarrow : ∀ s : ℕ, ∃ J m, 2 ≤ J ∧ J ≤ L ∧ N₀ ≤ m ∧
      IsRepHub A m ((Finset.range J).image
        (fun j => x (s + j)))) :
    ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧ ∀ v ∈ V, N₀ ≤ v ∧
      ∃ s J, 2 ≤ J ∧ J ≤ L ∧
        IsRepHub A v ((Finset.range J).image
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
    push_neg at hbig
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
    refine four_disjoint_full_hubs_impossible
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

/-- **THE FINAL FORK.**  Every counterexample funds free sets of
every size — root rank ≥ ω, the finite-rank room closed at the
root — or runs a LOCATED uniform-width hub street on its own
canonical spine: unboundedly many distinct targets, each fully
hubbed by a window of 2..L consecutive lineage values at a known
position.  The night's whole machinery — shells, spine, duality,
caps — compressed into one two-branch sentence about known
material.  Erdős 881's remaining content is the defeat of these
two explicit configurations. -/
theorem the_final_fork {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
      RepFree A N₀ P ∧ c ≤ P.card) ∨
    (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
      ∃ L, ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ v ∈ V, N₀ ≤ v ∧ ∃ s J, 2 ≤ J ∧ J ≤ L ∧
          IsRepHub A v ((Finset.range J).image
            (fun j => x (s + j)))) := by
  rcases stall_width_or_rank h0 hcov hanchor hfail with
    hrank | ⟨x, hxmono, hxA, L, hnarrow⟩
  · exact Or.inl hrank
  · exact Or.inr ⟨x, hxmono, hxA, L,
      narrow_located_street h0 hcov hxmono hnarrow⟩

/-! ## The welded fork: the street is an order-2 object -/

/-- **The 0-weld.**  Over a basis containing 0, any order-3 hub
avoiding 0 is already an order-2 hub: pad each pair with the zero
part.  Every hub made of positive material answers to the entire
order-2 reflection engine. -/
theorem pairHub_of_repHub {A : Set ℕ} {n : ℕ} {H : Finset ℕ}
    (h0 : 0 ∈ A) (h0H : 0 ∉ H) (hhub : IsRepHub A n H) :
    IsPairHub A n H := by
  intro a ha b hb hab
  rcases hhub a ha b hb 0 h0 (by omega) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h h0H

open Classical in
/-- **Pair-hub counting.**  An order-2 hub for v bounds the
UNORDERED pair count of v by |H|: every pair donates a member to
H, and distinct pairs donate distinct members (two low parts
sharing a donated value forces both pairs to be the central one). -/
theorem pair_hub_pair_count {A : Set ℕ} {v : ℕ} {H : Finset ℕ}
    (hhub : IsPairHub A v H) :
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

/-- **The street desert.**  A located pair-hub window confines
every pair of its target: one part lies inside the window's
closed spine interval.  Outside [x s, x (s+J−1)] and its mirror
[v − x (s+J−1), v − x s] the target's pair life is empty. -/
theorem street_target_desert {A : Set ℕ} {v s J : ℕ} {x : ℕ → ℕ}
    (hxmono : StrictMono x) (hJ : 1 ≤ J)
    (hhub : IsPairHub A v ((Finset.range J).image
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
/-- **THE WELDED FORK.**  The final fork's street branch is an
ORDER-2 object: the spine is positive material, so the 0-weld
turns every street window into a pair hub, and each street
target's ENTIRE pair life is caught by 2..L consecutive spine
values — at most L unordered pair representations.  A
counterexample funds root rank ≥ ω or runs a located
uniform-width ORDER-2 street: unboundedly many targets with
r₂ ≤ L and pair supply pinned to known spine windows.  The
order-3 problem's remaining enemy lives at order 2. -/
theorem the_final_fork_welded {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
      RepFree A N₀ P ∧ c ≤ P.card) ∨
    (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
      ∃ L, ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ v ∈ V, N₀ ≤ v ∧ ∃ s J, 2 ≤ J ∧ J ≤ L ∧
          IsPairHub A v ((Finset.range J).image
            (fun j => x (s + j))) ∧
          ((Finset.range (v + 1)).filter
            (fun a => a ∈ A ∧ (v - a) ∈ A ∧ 2 * a ≤ v)).card
            ≤ L) := by
  rcases the_final_fork h0 hcov hanchor hfail with
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
    have hpair := pairHub_of_repHub h0 h0win hhub
    have hcount := pair_hub_pair_count (A := A) (v := v) hpair
    have hcard : ((Finset.range J).image
        (fun j => x (s + j))).card ≤ J := by
      have h1 := Finset.card_image_le (s := Finset.range J)
        (f := fun j => x (s + j))
      rw [Finset.card_range] at h1
      exact h1
    exact ⟨hvN, s, J, hJ2, hJL, hpair, by omega⟩

/-! ## The street trichotomy: fixed hall or marching windows -/

/-- **Street position dichotomy.**  A street whose targets each
carry a positioned certificate either re-forms with all positions
under one fixed bound (the bounded hall) or re-forms beyond every
position bound (the marching street).  Generic in the certificate:
the splitting argument only counts near- and far-certified
targets. -/
theorem street_position_dichotomy {W : ℕ → ℕ → Prop}
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

/-- **The window sits below its target.**  A covered target's
pair-hub window cannot start above the target: the guaranteed
pair donates a part inside the window, and parts are at most the
sum.  Marching windows drag their targets up with them. -/
theorem street_window_below_target {A : Set ℕ} {N₀ : ℕ}
    {x : ℕ → ℕ} {v s J : ℕ} (hcov : PairCovers A N₀)
    (hxmono : StrictMono x) (hvN : N₀ ≤ v)
    (hhub : IsPairHub A v ((Finset.range J).image
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

/-- **The bounded street has a fixed hall.**  Windows drawn from a
bounded position range with widths at most L form a finite pool;
double pigeonhole (fibers per size, then stabilization over the
pool) hands one SINGLE window that pair-hubs unboundedly many
targets: a fixed finite hall through which infinitely many
targets route their entire pair life. -/
theorem bounded_street_fixed_hall {A : Set ℕ} {N₀ : ℕ}
    {x : ℕ → ℕ} {L S₀ : ℕ}
    (hnear : ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ v ∈ V, ∃ s, s ≤ S₀ ∧ N₀ ≤ v ∧ ∃ J, 2 ≤ J ∧ J ≤ L ∧
        IsPairHub A v ((Finset.range J).image
          (fun j => x (s + j)))) :
    ∃ H : Finset ℕ, H.card ≤ L ∧ ∀ K, ∃ V : Finset ℕ,
      K ≤ V.card ∧ ∀ v ∈ V, N₀ ≤ v ∧ IsPairHub A v H := by
  classical
  set box : Finset (ℕ × ℕ) :=
    (Finset.range (S₀ + 1)) ×ˢ (Finset.range (L + 1)) with hbox
  have hstep1 : ∀ K, ∃ p ∈ box, ∃ V' : Finset ℕ, K ≤ V'.card ∧
      ∀ v ∈ V', N₀ ≤ v ∧ IsPairHub A v
        ((Finset.range p.2).image (fun j => x (p.1 + j))) := by
    intro K
    obtain ⟨V, hVcard, hV⟩ := hnear (box.card * K + 1)
    have hVtot : ∀ v, ∃ p : ℕ × ℕ, v ∈ V →
        p.1 ≤ S₀ ∧ 2 ≤ p.2 ∧ p.2 ≤ L ∧ N₀ ≤ v ∧
        IsPairHub A v ((Finset.range p.2).image
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
      K ≤ V'.card ∧ ∀ v ∈ V', N₀ ≤ v ∧ IsPairHub A v
        ((Finset.range p.2).image (fun j => x (p.1 + j))) := by
    by_contra hno
    have hKp : ∀ p : ℕ × ℕ, ∃ Kp, p ∈ box →
        ¬(∃ V' : Finset ℕ, Kp ≤ V'.card ∧ ∀ v ∈ V', N₀ ≤ v ∧
          IsPairHub A v ((Finset.range p.2).image
            (fun j => x (p.1 + j)))) := by
      intro p
      by_cases hpbox : p ∈ box
      · have h1 : ¬∀ K, ∃ V' : Finset ℕ, K ≤ V'.card ∧
            ∀ v ∈ V', N₀ ≤ v ∧ IsPairHub A v
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

/-- **The fixed hall's popular shift.**  A single finite hall
pair-hubbing unboundedly many covered targets concentrates them
further: pigeonhole over the hall's members hands ONE element h
such that unboundedly many targets v sit on the translate h + A —
the hall's traffic runs through one door. -/
theorem fixed_hall_popular_shift {A : Set ℕ} {N₀ : ℕ}
    {H : Finset ℕ} (hcov : PairCovers A N₀)
    (hhall : ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ v ∈ V, N₀ ≤ v ∧ IsPairHub A v H) :
    ∃ h ∈ H, ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ v ∈ V, N₀ ≤ v ∧ h ≤ v ∧ v - h ∈ A ∧ IsPairHub A v H := by
  classical
  have hstep1 : ∀ K, ∃ h ∈ H, ∃ V' : Finset ℕ, K ≤ V'.card ∧
      ∀ v ∈ V', N₀ ≤ v ∧ h ≤ v ∧ v - h ∈ A ∧
        IsPairHub A v H := by
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
        IsPairHub A v H) := by
    intro h
    by_cases hhH : h ∈ H
    · have h1 : ¬∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
          ∀ v ∈ V, N₀ ≤ v ∧ h ≤ v ∧ v - h ∈ A ∧
            IsPairHub A v H :=
        fun hall => hno ⟨h, hhH, hall⟩
      obtain ⟨Kh, hKh'⟩ := not_forall.mp h1
      exact ⟨Kh, fun _ => hKh'⟩
    · exact ⟨0, fun hh => absurd hh hhH⟩
  choose Kf hKf using hKh
  obtain ⟨h, hhH, V', hV'card, hV'⟩ := hstep1 (H.sup Kf)
  exact hKf h hhH ⟨V',
    le_trans (Finset.le_sup (f := Kf) hhH) hV'card, hV'⟩

/-- **THE STREET TRICHOTOMY.**  The welded fork's street branch
splits by window position: every anchored counterexample funds
root rank ≥ ω, or routes unboundedly many targets' ENTIRE pair
life through one FIXED finite hall — with one hall element h
serving as the door: unboundedly many targets on the translate
h + A — or runs a MARCHING street: pair-hub windows of width
2..L beyond every spine position, each window below its own
target.  Three explicit configurations; nothing else survives. -/
theorem the_street_trichotomy {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
      RepFree A N₀ P ∧ c ≤ P.card) ∨
    (∃ H : Finset ℕ, ∃ h ∈ H, ∀ K, ∃ V : Finset ℕ,
      K ≤ V.card ∧ ∀ v ∈ V, N₀ ≤ v ∧ h ≤ v ∧ v - h ∈ A ∧
        IsPairHub A v H) ∨
    (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
      ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ v ∈ V, N₀ ≤ v ∧ ∃ s, S₀ ≤ s ∧ x s ≤ v ∧
          ∃ J, 2 ≤ J ∧ J ≤ L ∧ IsPairHub A v
            ((Finset.range J).image (fun j => x (s + j)))) := by
  rcases the_final_fork_welded h0 hcov hanchor hfail with
    hrank | ⟨x, hxmono, hxA, L, hstreet⟩
  · exact Or.inl hrank
  · have hstreet' : ∀ K : ℕ, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ v ∈ V, ∃ s, N₀ ≤ v ∧ ∃ J, 2 ≤ J ∧ J ≤ L ∧
          IsPairHub A v ((Finset.range J).image
            (fun j => x (s + j))) := by
      intro K
      obtain ⟨V, hVcard, hV⟩ := hstreet K
      refine ⟨V, hVcard, ?_⟩
      intro v hv
      obtain ⟨hvN, s, J, hJ2, hJL, hhub, _⟩ := hV v hv
      exact ⟨s, hvN, J, hJ2, hJL, hhub⟩
    rcases street_position_dichotomy
      (W := fun v s => N₀ ≤ v ∧ ∃ J, 2 ≤ J ∧ J ≤ L ∧
        IsPairHub A v ((Finset.range J).image
          (fun j => x (s + j)))) hstreet' with
      ⟨S₀, hnear⟩ | hfar
    · have hnear' : ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
          ∀ v ∈ V, ∃ s, s ≤ S₀ ∧ N₀ ≤ v ∧ ∃ J, 2 ≤ J ∧ J ≤ L ∧
            IsPairHub A v ((Finset.range J).image
              (fun j => x (s + j))) := by
        intro K
        obtain ⟨V, hVcard, hV⟩ := hnear K
        refine ⟨V, hVcard, ?_⟩
        intro v hv
        obtain ⟨s, hs, hvN, J, hJ2, hJL, hhub⟩ := hV v hv
        exact ⟨s, hs, hvN, J, hJ2, hJL, hhub⟩
      obtain ⟨H, hHcard, hhall⟩ := bounded_street_fixed_hall hnear'
      obtain ⟨h, hhH, hpop⟩ := fixed_hall_popular_shift hcov hhall
      exact Or.inr (Or.inl ⟨H, h, hhH, hpop⟩)
    · refine Or.inr (Or.inr ⟨x, hxmono, hxA, L, ?_⟩)
      intro S₀ K
      obtain ⟨V, hVcard, hV⟩ := hfar S₀ K
      refine ⟨V, hVcard, ?_⟩
      intro v hv
      obtain ⟨s, hSs, hvN, J, hJ2, hJL, hhub⟩ := hV v hv
      exact ⟨hvN, s, hSs,
        street_window_below_target hcov hxmono hvN hhub,
        J, hJ2, hJL, hhub⟩

/-! ## The four lanes: ghosts and members on the marching street -/

/-- **The 0-pair forces membership placement.**  A pair-hubbed
target over a basis containing 0 either lies outside A entirely
or lies INSIDE its own hub: the pair (0, v) must meet the hub,
and 0 is not hub material.  Forced non-membership — the shape
that carries information. -/
theorem street_target_notMem_or_window {A : Set ℕ} {v : ℕ}
    {W : Finset ℕ} (h0 : 0 ∈ A) (h0W : 0 ∉ W)
    (hhub : IsPairHub A v W) : v ∉ A ∨ v ∈ W := by
  by_cases hvA : v ∈ A
  · rcases hhub 0 h0 v hvA (by omega) with h | h
    · exact absurd h h0W
    · exact Or.inr h
  · exact Or.inl hvA

/-- **Member targets have only small-part pairs.**  A street
target sitting inside its own window has every pair split
unevenly: one part inside the window, hence the other at most
the window's span.  Middle pairs are banned — the member street
is difference-desert material. -/
theorem street_member_small_part {A : Set ℕ} {v s J : ℕ}
    {x : ℕ → ℕ} (hxmono : StrictMono x) (hJ : 1 ≤ J)
    (hhub : IsPairHub A v ((Finset.range J).image
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

/-- **Ghost-or-member dichotomy on the marching street.**  The
marching street's targets split: either unboundedly many are
GHOSTS — forced OUT of A, at every window horizon — or, from
some horizon on, unboundedly many are MEMBERS, each sitting
inside its own hub window. -/
theorem marching_member_dichotomy {A : Set ℕ} {N₀ L : ℕ}
    {x : ℕ → ℕ} (h0 : 0 ∈ A) (hxpos : ∀ t, 0 < x t)
    (hmarch : ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ v ∈ V, N₀ ≤ v ∧ ∃ s, S₀ ≤ s ∧ x s ≤ v ∧
        ∃ J, 2 ≤ J ∧ J ≤ L ∧ IsPairHub A v
          ((Finset.range J).image (fun j => x (s + j)))) :
    (∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ v ∈ V, N₀ ≤ v ∧ v ∉ A ∧ ∃ s, S₀ ≤ s ∧ x s ≤ v ∧
        ∃ J, 2 ≤ J ∧ J ≤ L ∧ IsPairHub A v
          ((Finset.range J).image (fun j => x (s + j)))) ∨
    (∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ v ∈ V, N₀ ≤ v ∧ v ∈ A ∧ ∃ s, S₀ ≤ s ∧
        ∃ J, 2 ≤ J ∧ J ≤ L ∧
          v ∈ (Finset.range J).image (fun j => x (s + j)) ∧
          IsPairHub A v ((Finset.range J).image
            (fun j => x (s + j)))) := by
  classical
  by_cases hghost : ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ v ∈ V, N₀ ≤ v ∧ v ∉ A ∧ ∃ s, S₀ ≤ s ∧ x s ≤ v ∧
        ∃ J, 2 ≤ J ∧ J ≤ L ∧ IsPairHub A v
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
        rcases street_target_notMem_or_window h0 h0W hhub with
          hno | hyes
        · exact absurd hvA hno
        · exact ⟨hvN, hvA, s, by omega, J, hJ2, hJL, hyes, hhub⟩

/-- **THE FOUR LANES.**  Every anchored counterexample drives in
one of four explicit lanes.  LANE 1 (rank): free sets of every
size — root rank ≥ ω.  LANE 2 (the door): one FIXED finite hall
pair-hubs unboundedly many targets, one hall element h carrying
unboundedly many of them onto the translate h + A.  LANE 3 (the
ghost street): unboundedly many targets FORCED OUT of A, each
with its whole pair life caught by a marching spine window.
LANE 4 (the member street): unboundedly many targets INSIDE
their own marching windows — spine material whose every pair
has a part at most the window span: middle pairs banned.  The
night's taxonomies compress into rank, door, ghosts, members. -/
theorem the_four_lanes {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
      RepFree A N₀ P ∧ c ≤ P.card) ∨
    (∃ H : Finset ℕ, ∃ h ∈ H, ∀ K, ∃ V : Finset ℕ,
      K ≤ V.card ∧ ∀ v ∈ V, N₀ ≤ v ∧ h ≤ v ∧ v - h ∈ A ∧
        IsPairHub A v H) ∨
    (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
      ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ v ∈ V, N₀ ≤ v ∧ v ∉ A ∧ ∃ s, S₀ ≤ s ∧ x s ≤ v ∧
          ∃ J, 2 ≤ J ∧ J ≤ L ∧ IsPairHub A v
            ((Finset.range J).image (fun j => x (s + j)))) ∨
    (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
      ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ v ∈ V, N₀ ≤ v ∧ v ∈ A ∧ ∃ s, S₀ ≤ s ∧
          ∃ J, 2 ≤ J ∧ J ≤ L ∧
            v ∈ (Finset.range J).image (fun j => x (s + j)) ∧
            IsPairHub A v ((Finset.range J).image
              (fun j => x (s + j))) ∧
            (∀ a ∈ A, ∀ b ∈ A, a + b = v →
              a ≤ x (s + J - 1) - x s ∨
              b ≤ x (s + J - 1) - x s)) := by
  rcases the_street_trichotomy h0 hcov hanchor hfail with
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
        street_member_small_part hxmono (by omega) hhub hvW⟩

/-! ## The member street verdict: difference-blind stream or gap blowup -/

/-- **Members expel differences.**  If every pair of v' has a
part at most D, then any basis element v strictly between D and
v' − D forces v' − v OUT of A: otherwise (v, v' − v) would be a
banned middle pair.  Forced non-membership from pure counting
geometry. -/
theorem member_difference_out {A : Set ℕ} {v' D : ℕ}
    (hsmall : ∀ a ∈ A, ∀ b ∈ A, a + b = v' → a ≤ D ∨ b ≤ D)
    {v : ℕ} (hvA : v ∈ A) (hDv : D < v) (hvv' : v + D < v') :
    v' - v ∉ A := by
  intro hdA
  rcases hsmall v hvA (v' - v) hdA (by omega) with h | h <;> omega

/-- **The difference-blind stream.**  A uniformly-bounded-span
member street condenses into a strictly increasing stream inside
A, every element above the span bound, with EVERY pairwise
difference forced out of A: an infinite subset of the basis
whose difference set the basis refuses. -/
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

/-- **THE MEMBER STREET VERDICT.**  The member street's window
spans either stay bounded — and the street condenses into a
difference-blind stream: an infinite ascending subset of A all
of whose pairwise differences are forced OUT of A — or the spans
blow up, and with width capped at L the CANONICAL SPINE develops
unbounded consecutive gaps.  Lane 4 ends in a Sidon-flavoured
stream or a torn spine; there is no third exit. -/
theorem member_street_verdict {A : Set ℕ} {N₀ L : ℕ}
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
  rcases street_position_dichotomy
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

/-- **THE GLOBAL TRICHOTOMY.**  One statement, hypotheses only
(0 ∈ A, covering, order-3 failure of every infinite deletion) —
no anchor condition anywhere.  Every counterexample world is:

I. ANCHORED — full anchor supply holds, and the four-lane
   endgame runs: rank ≥ ω, or the fixed hall with its door, or
   the ghost street, or the member street.

II. ROUTED — some basis MEMBER g₀ routes every noncentral
   decomposition of every double: each 2c is pair-hubbed by the
   two explicit values {c, g₀}.

III. CENTRAL — doubles decompose ONLY centrally: every element
   pair-owns its double ({c} is a full pair hub at 2c), every
   infinite deletion breaks order-2 coverage at its own doubles
   (minimality is automatic), and the basis is midpoint-free off
   the router: Salem–Spencer geometry.

The anchored fork, the g₀-routed branch, and the central branch,
formally fused.  Erdős 881's negative answer would have to live
in one of these three rooms; each carries explicit, located,
verified structure. -/
theorem the_global_trichotomy {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ((∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
        w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g) ∧
      ((∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
        RepFree A N₀ P ∧ c ≤ P.card) ∨
      (∃ H : Finset ℕ, ∃ h ∈ H, ∀ K, ∃ V : Finset ℕ,
        K ≤ V.card ∧ ∀ v ∈ V, N₀ ≤ v ∧ h ≤ v ∧ v - h ∈ A ∧
          IsPairHub A v H) ∨
      (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
        ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
          ∀ v ∈ V, N₀ ≤ v ∧ v ∉ A ∧ ∃ s, S₀ ≤ s ∧ x s ≤ v ∧
            ∃ J, 2 ≤ J ∧ J ≤ L ∧ IsPairHub A v
              ((Finset.range J).image (fun j => x (s + j)))) ∨
      (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
        ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
          ∀ v ∈ V, N₀ ≤ v ∧ v ∈ A ∧ ∃ s, S₀ ≤ s ∧
            ∃ J, 2 ≤ J ∧ J ≤ L ∧
              v ∈ (Finset.range J).image (fun j => x (s + j)) ∧
              IsPairHub A v ((Finset.range J).image
                (fun j => x (s + j))) ∧
              (∀ a ∈ A, ∀ b ∈ A, a + b = v →
                a ≤ x (s + J - 1) - x s ∨
                b ≤ x (s + J - 1) - x s)))) ∨
    (∃ g₀, g₀ ∈ A ∧ ∀ c ∈ A, 0 < c → c ≠ g₀ →
      IsPairHub A (2 * c) ({c, g₀} : Finset ℕ)) ∨
    (∃ g₀, (∀ c ∈ A, 0 < c → c ≠ g₀ → ∀ w ∈ A, ∀ w' ∈ A,
        w + w' = 2 * c → w = c ∧ w' = c) ∧
      (∀ c ∈ A, 0 < c → c ≠ g₀ →
        IsPairHub A (2 * c) ({c} : Finset ℕ)) ∧
      (∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
        ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) ∧
      (∀ a d, 0 < d → a ∈ A → a + d ∈ A → a + 2 * d ∈ A →
        a + d = g₀ ∨ a + d = 0)) := by
  rcases anchor_dichotomy (A := A) with hanchor | ⟨g₀, hroute⟩
  · exact Or.inl ⟨hanchor,
      the_four_lanes h0 hcov
        (streamSurvives_of_anchor h0 hcov hanchor) hfail⟩
  · rcases no_anchor_central_or_member hroute with hg | hcentral
    · exact Or.inr (Or.inl ⟨g₀, hg, hroute⟩)
    · exact Or.inr (Or.inr ⟨g₀, hcentral,
        central_branch_singleton_hubs hcentral,
        central_branch_hmin hcentral,
        central_branch_no_three_AP hcentral⟩)

/-! ## The routed collapse: branch II has no interior -/

/-- **THE ROUTED COLLAPSE.**  The g₀-routed branch is not an
independent room.  If the genuine g₀-routes persist cofinally,
the world is ALMOST-ANCHORED: the explicit ladder 2c − g₀ ∈ A
runs forever and full anchor supply holds at every value except
g₀ itself.  If the routes die out, every sufficiently large
double is purely central and the ENTIRE central suite applies
beyond a threshold: total pinning, automatic minimality,
midpoint-freeness.  Routed worlds are absorbed into the anchored
frontier or the central branch; the trichotomy's middle room is
defeated as a separate case. -/
theorem the_routed_collapse {A : Set ℕ} {g₀ : ℕ} (hg : g₀ ∈ A)
    (hroute : ∀ c ∈ A, 0 < c → c ≠ g₀ →
      IsPairHub A (2 * c) ({c, g₀} : Finset ℕ)) :
    ((∀ N, ∃ c ∈ A, N ≤ c ∧ c ≠ g₀ ∧ g₀ ≤ 2 * c ∧
        (2 * c - g₀) ∈ A ∧ 2 * c - g₀ ≠ c) ∧
      (∀ g, g ≠ g₀ → ∃ c ∈ A, 0 < c ∧ c ≠ g ∧
        ∃ w ∈ A, ∃ w' ∈ A, w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧
          w' ≠ g)) ∨
    (∃ C₀, (∀ c ∈ A, C₀ ≤ c → c ≠ g₀ → ∀ w ∈ A, ∀ w' ∈ A,
        w + w' = 2 * c → w = c ∧ w' = c) ∧
      (∀ c ∈ A, C₀ ≤ c → c ≠ g₀ →
        IsPairHub A (2 * c) ({c} : Finset ℕ)) ∧
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
      push_neg at hno
      obtain ⟨hgne, hC⟩ := hno
      have hsum : a + (a + 2 * d) = 2 * (a + d) := by omega
      have hac : a ≠ a + d := by omega
      exact absurd ⟨a + d, hadA, by omega, by omega, hgne,
        a, haA, a + 2 * d, ha2dA, hsum, hac⟩ hN₁

/-- **THE COLLAPSED TRICHOTOMY.**  The global trichotomy after
the routed collapse: the middle room is gone.  Every
counterexample world (0 ∈ A, covering, hfail — nothing else) is

I. ANCHORED: full anchor supply and the four lanes;

II. ALMOST-ANCHORED: a basis member g₀ with the explicit
   infinite ladder 2c − g₀ ∈ A and full anchor supply at every
   value EXCEPT g₀ — one single hole in the anchor wall, at a
   known member, with known ladder structure through it;

III. CENTRAL-TAIL: beyond an explicit threshold every double is
   purely central — total pinning, automatic minimality,
   midpoint-freeness — subsuming the pure central branch at
   threshold 1.

Two live geometries remain: the anchored/almost-anchored fork
frontier and the Salem–Spencer central tail. -/
theorem the_collapsed_trichotomy {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ((∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
        w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g) ∧
      ((∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
        RepFree A N₀ P ∧ c ≤ P.card) ∨
      (∃ H : Finset ℕ, ∃ h ∈ H, ∀ K, ∃ V : Finset ℕ,
        K ≤ V.card ∧ ∀ v ∈ V, N₀ ≤ v ∧ h ≤ v ∧ v - h ∈ A ∧
          IsPairHub A v H) ∨
      (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
        ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
          ∀ v ∈ V, N₀ ≤ v ∧ v ∉ A ∧ ∃ s, S₀ ≤ s ∧ x s ≤ v ∧
            ∃ J, 2 ≤ J ∧ J ≤ L ∧ IsPairHub A v
              ((Finset.range J).image (fun j => x (s + j)))) ∨
      (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
        ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
          ∀ v ∈ V, N₀ ≤ v ∧ v ∈ A ∧ ∃ s, S₀ ≤ s ∧
            ∃ J, 2 ≤ J ∧ J ≤ L ∧
              v ∈ (Finset.range J).image (fun j => x (s + j)) ∧
              IsPairHub A v ((Finset.range J).image
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
        IsPairHub A (2 * c) ({c} : Finset ℕ)) ∧
      (∀ B ⊆ A, B.Infinite → ¬∃ N₂, ∀ n, N₂ ≤ n →
        ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) ∧
      (∀ a d, 0 < d → a ∈ A → a + d ∈ A → a + 2 * d ∈ A →
        a + d = g₀ ∨ a + d < C₀)) := by
  rcases the_global_trichotomy h0 hcov hfail with
    ⟨hanch, hlanes⟩ | ⟨g₀, hg, hroute⟩ |
    ⟨g₀, hcen, hhub, hmin, hap⟩
  · exact Or.inl ⟨hanch, hlanes⟩
  · rcases the_routed_collapse hg hroute with
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

/-- **The almost-anchored stream dichotomy.**  With anchor
supply at every value EXCEPT g₀ — the almost-anchored branch of
the collapsed trichotomy — the private-stream kill still runs:
the rotating extraction needs only one anchor package, and every
recurring guardian other than g₀ dies by the fixed kill.  What
survives is ONE explicit configuration: the guardian g₀ itself
recurring cofinally.  The g₀-hole in the anchor wall admits
exactly the g₀-tower. -/
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
  · -- recurring case: all late guardians in one finite set
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
        exact Or.inl (surviving_deletion_of_cofinal_fixedGuardian'
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

/-- **The g₀-tower structure.**  A cofinal g₀-private stream
condenses into explicit material: cofinal levels L ∈ A with the
target g₀ + L pair-hubbed by the SINGLETON {g₀} (one door for
every pair) and the full mirror law at L — every non-g₀ element
below the level reflects back into A.  The hole in the anchor
wall contains a fully symmetric tower, all of it centred on the
single member g₀. -/
theorem g0_tower {A : Set ℕ} {N₀ g₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) (hg0 : 0 < g₀)
    (hstream : ∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A g₀ m) :
    ∀ K, ∃ L, K < L ∧ L ∈ A ∧ N₀ ≤ g₀ + L ∧
      IsPairHub A (g₀ + L) ({g₀} : Finset ℕ) ∧
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

/-- **Almost-anchored singleton hubs feed the tower.**  Under
hfail, an almost-anchored world with cofinal positive singleton
rep-hubs is forced into the g₀-tower: the stream dichotomy's
surviving branch contradicts hfail, so the guardian g₀ recurs
cofinally and the tower stands.  The last unkilled singleton
configuration of the almost-anchored branch is completely
explicit. -/
theorem almost_anchored_singleton_hubs {A : Set ℕ} {N₀ g₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor' : ∀ g, g ≠ g₀ → ∃ c ∈ A, 0 < c ∧ c ≠ g ∧
      ∃ w ∈ A, ∃ w' ∈ A,
        w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hsing : ∀ N, ∃ n, N ≤ n ∧ ∃ a, 0 < a ∧ IsRepHub A n {a}) :
    0 < g₀ ∧ ∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A g₀ m := by
  have hstream : ∀ N, ∃ a m, N ≤ m ∧ 0 < a ∧
      IsPrivateTriple A a m := by
    intro N
    obtain ⟨n, hn, a, ha, hhub⟩ := hsing (max N N₀)
    exact ⟨a, n, le_trans (le_max_left _ _) hn, ha,
      privateTriple_of_singleton_hub h0 hcov
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

/-- **The g₀-translate law.**  The tower alone — no routing
needed — forces A off its own g₀-translate: for any positive
z ∈ A other than g₀, the value g₀ + z is OUT of A.  Otherwise
some high tower level L would pair g₀ + z with the mirror L − z
and hand its private target a second pair, breaking the
singleton hub.  A ∩ (A + g₀) ⊆ {g₀, 2g₀}: the door element's
translate is a desert. -/
theorem g0_translate_law {A : Set ℕ} {N₀ g₀ : ℕ}
    (hg0 : 0 < g₀)
    (htower : ∀ K, ∃ L, K < L ∧ L ∈ A ∧ N₀ ≤ g₀ + L ∧
      IsPairHub A (g₀ + L) ({g₀} : Finset ℕ) ∧
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

/-- **The g₀-mirror lock.**  In a ROUTED world the tower's one
missing reflection is forced missing: at every sufficiently
high tower level L the slot L − g₀ is OUT of A.  Otherwise the
mirrors of a fixed ladder anchor c and its route partner
q = 2c − g₀ would give the double 2(L − c) the noncentral
g₀-free decomposition (L − q) + (L − g₀), which routing forbids.
The tower is near-symmetric with exactly one empty slot — at
the router's own mirror. -/
theorem routed_tower_mirror_lock {A : Set ℕ} {N₀ g₀ c : ℕ}
    (hroute : ∀ c' ∈ A, 0 < c' → c' ≠ g₀ →
      IsPairHub A (2 * c') ({c', g₀} : Finset ℕ))
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

/-- **THE g₀-TOWER WORLD.**  The complete portrait of the
anchor-hole.  In a routed world (member g₀, routing law, ladder)
under hfail, cofinal positive singleton hubs force: g₀ is
positive; cofinal tower levels L ∈ A each carrying the singleton
pair hub {g₀} at g₀ + L, the full mirror law, AND the forced
empty slot L − g₀ ∉ A (the mirror lock); and the global
translate desert g₀ + z ∉ A for every positive z ∈ A ∖ {g₀}.
The last singleton refuge of the almost-anchored branch is a
near-symmetric tower, centred on one member, disjoint from its
own translate, with exactly one reflection missing — at the
router's own image. -/
theorem the_g0_tower_world {A : Set ℕ} {N₀ g₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hroute : ∀ c ∈ A, 0 < c → c ≠ g₀ →
      IsPairHub A (2 * c) ({c, g₀} : Finset ℕ))
    (hladder : ∀ N, ∃ c ∈ A, N ≤ c ∧ c ≠ g₀ ∧ g₀ ≤ 2 * c ∧
      (2 * c - g₀) ∈ A ∧ 2 * c - g₀ ≠ c)
    (hanchor' : ∀ g, g ≠ g₀ → ∃ c ∈ A, 0 < c ∧ c ≠ g ∧
      ∃ w ∈ A, ∃ w' ∈ A,
        w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hsing : ∀ N, ∃ n, N ≤ n ∧ ∃ a, 0 < a ∧ IsRepHub A n {a}) :
    0 < g₀ ∧
    (∀ K, ∃ L, K < L ∧ L ∈ A ∧ N₀ ≤ g₀ + L ∧
      IsPairHub A (g₀ + L) ({g₀} : Finset ℕ) ∧
      (∀ z ∈ A, z ≠ g₀ → z + N₀ < L → L - z ∈ A) ∧
      L - g₀ ∉ A) ∧
    (∀ z ∈ A, 0 < z → z ≠ g₀ → g₀ + z ∉ A) := by
  obtain ⟨hg0, hstream⟩ := almost_anchored_singleton_hubs
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

/-- **The tower engine.**  Geometric levels carrying the
g₀-defective mirror, a small anchor c with c-free g₀-free repair
pair (u, u') of 2c + g₀, and the door g₀ itself as a member:
the deletion {L(2k+2) − c} survives.  Double hits are repaired
by (L − u) + (L' − u') + g₀, single hits by the c-mirror at the
odd level, clean pairs by 0-padding. -/
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

/-- **THE TOWER KILLS ITSELF.**  The g₀-tower plus one ladder
anchor forces a surviving deletion — no anchor dodging g₀
needed.  The translate law (a consequence of the tower alone)
forbids 2c ∈ A and c + g₀ ∈ A at a ladder anchor c, so EVERY
pair of the covered target 2c + g₀ is automatically g₀-free and
c-free — exactly the repair material the geometric extraction
was missing.  The last refuge of the almost-anchored branch is
self-contradictory. -/
theorem g0_tower_killed {A : Set ℕ} {N₀ g₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) (hg0 : 0 < g₀)
    (hgA : g₀ ∈ A)
    (htower : ∀ K, ∃ L, K < L ∧ L ∈ A ∧ N₀ ≤ g₀ + L ∧
      IsPairHub A (g₀ + L) ({g₀} : Finset ℕ) ∧
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

/-- **The almost-anchored stream is killed outright.**  With the
ladder supplying the anchor c and the tower supplying its own
repair pair, the private-stream dichotomy's residual branch
(the g₀-tower) is self-contradictory: EVERY cofinal positive
private stream in an almost-anchored world yields a surviving
deletion.  The g₀-hole is plugged at the stream level. -/
theorem almost_anchored_stream_killed {A : Set ℕ} {N₀ g₀ : ℕ}
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
    exact g0_tower_killed h0 hcov hg0 hgA htower hcA hcN hcg hqA

/-- **Almost-anchored singleton hubs are refuted.**  The routed
branch with cofinal routes now matches the anchored branch
exactly: no counterexample world of either kind carries cofinal
positive singleton rep-hubs.  The anchor wall's one hole admits
nothing. -/
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
    ¬(∀ N, ∃ n, N ≤ n ∧ ∃ a, 0 < a ∧ IsRepHub A n {a}) := by
  intro hsing
  have hstream : ∀ N, ∃ a m, N ≤ m ∧ 0 < a ∧
      IsPrivateTriple A a m := by
    intro N
    obtain ⟨n, hn, a, ha, hhub⟩ := hsing (max N N₀)
    exact ⟨a, n, le_trans (le_max_left _ _) hn, ha,
      privateTriple_of_singleton_hub h0 hcov
        (le_trans (le_max_right _ _) hn) hhub⟩
  obtain ⟨B, hBsub, hBinf, hsurv⟩ :=
    almost_anchored_stream_killed h0 hcov hgA hladder hanchor'
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

/-- **Almost-anchored worlds implement the stream-kill oracle.**
The g₀-tower self-kill in interface form: with a member router,
the ladder, and anchors at every value except g₀, every cofinal
positive private stream yields a surviving deletion.  The
almost-anchored world can be fed to EVERY theorem of the engine
that formerly demanded full anchor supply. -/
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
    almost_anchored_stream_killed h0 hcov hgA hladder hanchor'
      hstream

/-- **THE FINAL DICHOTOMY.**  Two rooms.  Every counterexample
world (0 ∈ A, covering, hfail — nothing else) either drives in
one of the FOUR LANES — root rank ≥ ω, the fixed hall with its
door, the ghost street, or the member street — or lives in the
CENTRAL TAIL: beyond an explicit threshold every double is
purely central, minimality is automatic, and the basis is
midpoint-free off one value.  The anchored and almost-anchored
branches are MERGED: the stream-kill oracle is implemented on
both sides, so the four-lane endgame runs regardless of the
anchor wall's hole.  Erdős 881's negative answer would have to
live in one of five explicit configurations: rank, door,
ghosts, members, or Salem–Spencer tail. -/
theorem the_final_dichotomy {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ((∀ c : ℕ, ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ A ∧ 0 < h) ∧
      RepFree A N₀ P ∧ c ≤ P.card) ∨
    (∃ H : Finset ℕ, ∃ h ∈ H, ∀ K, ∃ V : Finset ℕ,
      K ≤ V.card ∧ ∀ v ∈ V, N₀ ≤ v ∧ h ≤ v ∧ v - h ∈ A ∧
        IsPairHub A v H) ∨
    (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
      ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ v ∈ V, N₀ ≤ v ∧ v ∉ A ∧ ∃ s, S₀ ≤ s ∧ x s ≤ v ∧
          ∃ J, 2 ≤ J ∧ J ≤ L ∧ IsPairHub A v
            ((Finset.range J).image (fun j => x (s + j)))) ∨
    (∃ x : ℕ → ℕ, StrictMono x ∧ (∀ t, x t ∈ A ∧ 0 < x t) ∧
      ∃ L, ∀ S₀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ v ∈ V, N₀ ≤ v ∧ v ∈ A ∧ ∃ s, S₀ ≤ s ∧
          ∃ J, 2 ≤ J ∧ J ≤ L ∧
            v ∈ (Finset.range J).image (fun j => x (s + j)) ∧
            IsPairHub A v ((Finset.range J).image
              (fun j => x (s + j))) ∧
            (∀ a ∈ A, ∀ b ∈ A, a + b = v →
              a ≤ x (s + J - 1) - x s ∨
              b ≤ x (s + J - 1) - x s))) ∨
    (∃ g₀ C₀, (∀ c ∈ A, C₀ ≤ c → c ≠ g₀ → ∀ w ∈ A, ∀ w' ∈ A,
        w + w' = 2 * c → w = c ∧ w' = c) ∧
      (∀ c ∈ A, C₀ ≤ c → c ≠ g₀ →
        IsPairHub A (2 * c) ({c} : Finset ℕ)) ∧
      (∀ B ⊆ A, B.Infinite → ¬∃ N₂, ∀ n, N₂ ≤ n →
        ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) ∧
      (∀ a d, 0 < d → a ∈ A → a + d ∈ A → a + 2 * d ∈ A →
        a + d = g₀ ∨ a + d < C₀)) := by
  rcases the_collapsed_trichotomy h0 hcov hfail with
    ⟨_, hlanes⟩ | ⟨g₀, hgA, hladder, hanchor'⟩ | htail
  · exact Or.inl hlanes
  · exact Or.inl (the_four_lanes h0 hcov
      (streamSurvives_of_almost_anchored h0 hcov hgA hladder
        hanchor') hfail)
  · exact Or.inr htail

/-! ## The door world: hall mirrors and the weak translate law -/

/-- **The hall mirror.**  An order-3 hall target reflects every
non-hall element into one of |H| translated copies: covering
v − z and routing the triple through the hall produces
v − z − h ∈ A for SOME hall member h.  The defective mirror of
the door world — multivalued where the tower's was exact. -/
theorem hall_mirror {A : Set ℕ} {N₀ v : ℕ} {H : Finset ℕ}
    (hcov : PairCovers A N₀) (hhub : IsRepHub A v H)
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

/-- **The weak hall translate law.**  In a door world — one
fixed hall H both rep- and pair-hubbing unboundedly many
targets — every basis element beyond the hall's range escapes
at least one hall translate: SOME h ∈ H has z + h ∉ A.
Otherwise a huge door target's defective mirror would recombine
with the translate into a hall-free pair.  For a singleton hall
this is exactly the g₀-translate law. -/
theorem hall_weak_translate {A : Set ℕ} {N₀ M : ℕ}
    {H : Finset ℕ}
    (hcov : PairCovers A N₀)
    (hM : ∀ h ∈ H, h ≤ M)
    (hdoor : ∀ N, ∃ v, N ≤ v ∧ N₀ ≤ v ∧ IsRepHub A v H ∧
      IsPairHub A v H) :
    ∀ z ∈ A, M < z → z ∉ H → ∃ h ∈ H, z + h ∉ A := by
  intro z hzA hzM hzH
  by_contra hall
  push_neg at hall
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

/-- **The bounded street's fixed hall, order-3 form.**  The
double pigeonhole re-run WITHOUT the weld: one single window
REP-hubs unboundedly many targets, and the hall material is
known positive basis elements. -/
theorem bounded_street_fixed_hall_rep {A : Set ℕ} {N₀ : ℕ}
    {x : ℕ → ℕ} {L S₀ : ℕ} (hxA : ∀ t, x t ∈ A ∧ 0 < x t)
    (hnear : ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ v ∈ V, ∃ s, s ≤ S₀ ∧ N₀ ≤ v ∧ ∃ J, 2 ≤ J ∧ J ≤ L ∧
        IsRepHub A v ((Finset.range J).image
          (fun j => x (s + j)))) :
    ∃ H : Finset ℕ, H.card ≤ L ∧ (∀ h ∈ H, h ∈ A ∧ 0 < h) ∧
      ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ v ∈ V, N₀ ≤ v ∧ IsRepHub A v H := by
  classical
  set box : Finset (ℕ × ℕ) :=
    (Finset.range (S₀ + 1)) ×ˢ (Finset.range (L + 1)) with hbox
  have hstep1 : ∀ K, ∃ p ∈ box, ∃ V' : Finset ℕ, K ≤ V'.card ∧
      ∀ v ∈ V', N₀ ≤ v ∧ IsRepHub A v
        ((Finset.range p.2).image (fun j => x (p.1 + j))) := by
    intro K
    obtain ⟨V, hVcard, hV⟩ := hnear (box.card * K + 1)
    have hVtot : ∀ v, ∃ p : ℕ × ℕ, v ∈ V →
        p.1 ≤ S₀ ∧ 2 ≤ p.2 ∧ p.2 ≤ L ∧ N₀ ≤ v ∧
        IsRepHub A v ((Finset.range p.2).image
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
      K ≤ V'.card ∧ ∀ v ∈ V', N₀ ≤ v ∧ IsRepHub A v
        ((Finset.range p.2).image (fun j => x (p.1 + j))) := by
    by_contra hno
    have hKp : ∀ p : ℕ × ℕ, ∃ Kp, p ∈ box →
        ¬(∃ V' : Finset ℕ, Kp ≤ V'.card ∧ ∀ v ∈ V', N₀ ≤ v ∧
          IsRepHub A v ((Finset.range p.2).image
            (fun j => x (p.1 + j)))) := by
      intro p
      by_cases hpbox : p ∈ box
      · have h1 : ¬∀ K, ∃ V' : Finset ℕ, K ≤ V'.card ∧
            ∀ v ∈ V', N₀ ≤ v ∧ IsRepHub A v
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

/-- **THE DOOR WORLD.**  The final fork's street branch, in the
bounded-window case, upgraded to full strength: a fixed hall H
of 2..L known positive basis elements REP-hubbing and
PAIR-hubbing unboundedly many targets, with a door h₀ ∈ H
carrying unboundedly many of them onto h₀ + A.  Teamness
(2 ≤ |H|) comes from the stream-kill oracle: a singleton hall
would be a refuted cofinal singleton stream. -/
theorem the_door_world {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (horacle : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    {x : ℕ → ℕ} {L S₀ : ℕ} (hxA : ∀ t, x t ∈ A ∧ 0 < x t)
    (hnear : ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
      ∀ v ∈ V, ∃ s, s ≤ S₀ ∧ N₀ ≤ v ∧ ∃ J, 2 ≤ J ∧ J ≤ L ∧
        IsRepHub A v ((Finset.range J).image
          (fun j => x (s + j)))) :
    ∃ H : Finset ℕ, 2 ≤ H.card ∧ H.card ≤ L ∧
      (∀ h ∈ H, h ∈ A ∧ 0 < h) ∧
      ∀ K, ∃ V : Finset ℕ, K ≤ V.card ∧
        ∀ v ∈ V, N₀ ≤ v ∧ IsRepHub A v H ∧ IsPairHub A v H := by
  classical
  obtain ⟨H, hHL, hHmat, hall⟩ :=
    bounded_street_fixed_hall_rep hxA hnear
  have h0H : (0 : ℕ) ∉ H := by
    intro h
    exact absurd (hHmat 0 h).2 (by omega)
  have hpair : ∀ v, IsRepHub A v H → IsPairHub A v H :=
    fun v hrep => pairHub_of_repHub h0 h0H hrep
  have hH2 : 2 ≤ H.card := by
    by_contra hlt
    rcases Nat.lt_or_ge H.card 1 with h1 | h1
    · -- empty hall: covered targets have triples, hub empty impossible
      have hcard0 : H.card = 0 := by omega
      rw [Finset.card_eq_zero] at hcard0
      obtain ⟨V, hVcard, hV⟩ := hall 1
      have hVne : V.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨v, hvV⟩ := hVne
      obtain ⟨hvN, hrep⟩ := hV v hvV
      obtain ⟨h, hh⟩ := hub_nonempty_of_covering h0 hcov hvN hrep
      rw [hcard0] at hh
      exact absurd hh (Finset.notMem_empty h)
    · -- singleton hall: refuted cofinal singleton stream
      have hcard1 : H.card = 1 := by omega
      obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hcard1
      have ha0 : 0 < a := by
        have := (hHmat a (by rw [ha]; exact
          Finset.mem_singleton_self a)).2
        omega
      refine singleton_hubs_refuted h0 hcov horacle hfail ?_
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

/-- **The mirror-color law.**  At a door target the defective
mirror's choice is never a good translate: it produces
v − z − h ∈ A only for h with z + h ∉ A.  (A good translate
z + h ∈ A would recombine with the mirror image into a
hall-free pair of v, breaking the pair hub.)  The door world's
mirrors and translates are locked together: the mirror colour
set of z is exactly the complement of its translate set. -/
theorem hall_mirror_color_law {A : Set ℕ} {N₀ M v : ℕ}
    {H : Finset ℕ}
    (hcov : PairCovers A N₀) (hM : ∀ h ∈ H, h ≤ M)
    (hrep : IsRepHub A v H) (hpair : IsPairHub A v H)
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

/-- **Door targets are ghosts.**  Every door target beyond the
hall's range is forced OUT of A: a member target would be hall
material by the 0-pair law, but the hall is bounded.  Lane 2's
targets share lane 3's defining mark. -/
theorem door_targets_ghost {A : Set ℕ} {M v : ℕ}
    {H : Finset ℕ} (h0 : 0 ∈ A) (h0H : (0 : ℕ) ∉ H)
    (hM : ∀ h ∈ H, h ≤ M) (hpair : IsPairHub A v H)
    (hvM : M < v) : v ∉ A := by
  rcases street_target_notMem_or_window h0 h0H hpair with
    h | h
  · exact h
  · have h1 := hM v h
    omega

/-- **The translate dichotomy.**  Either arbitrarily large basis
elements have ALL their hall translates out of A (cofinal strong
translate — the tower law verbatim), or beyond some point every
basis element keeps at least one good translate.  The door
world's first fork. -/
theorem door_translate_dichotomy {A : Set ℕ} (H : Finset ℕ) :
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
    push_neg at hno
    exact hZ₀ ⟨z, hZz, hzA, hzH, hno⟩

/-- **The two-member difference law.**  In a door world with
|H| = 2, in the good horn, door-target differences are FORCED
INTO A: the partner L = v − h₀ has h₀ bad (v is a ghost), so
goodness pins its bad set to exactly {h₀}; the mirror colour at
any higher door target v' must be h₀, and the mirror image is
the pure difference v' − v.  The door world's targets carry
their own difference ladder. -/
theorem door_two_difference_law {A : Set ℕ} {N₀ M v v' : ℕ}
    {H : Finset ℕ}
    (hcov : PairCovers A N₀) (hM : ∀ h ∈ H, h ≤ M)
    (hcard : H.card = 2)
    (hrep' : IsRepHub A v' H) (hpair' : IsPairHub A v' H)
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

/-- **The good-deep door engine.**  In the two-member good horn
with cofinal deep partners, deleting the even levels
{v(2k+2) − h₀} survives.  Single hits are repaired by a
difference plus an odd level; double hits by the
good-translated level M = v − h₀ + h₁, a consecutive
difference, and a deep partner v − h₀ − h₁ — the h₁'s cancel
and the sum closes with NO constraint between the two hit
indices.  All parts are separated from the deletion by parity
and scale. -/
theorem door_good_deep_engine {A : Set ℕ} {N₀ h₀ h₁ : ℕ}
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

/-- **THE TWO-MEMBER GOOD-DEEP DOOR IS DEAD.**  Assembly: in a
door world with |H| = 2, the eventually-good horn, and cofinal
deep partners, a surviving deletion exists.  The stream
extraction threads four laws — ghostliness, the pinned good
translate of every level (bad(L) = {h₀} since L + h₀ is the
ghost target, so L + h₁ ∈ A), deep partners, and the pairwise
difference law — into the good-deep engine. -/
theorem door_two_good_deep_killed {A : Set ℕ}
    {N₀ M₀ h₀ h₁ Z₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    {H : Finset ℕ} (hcard : H.card = 2)
    (hM₀ : ∀ h ∈ H, h ≤ M₀)
    (hh₀ : h₀ ∈ H) (hh₁ : h₁ ∈ H) (hne : h₀ ≠ h₁)
    (hh₀pos : 0 < h₀) (hh₁pos : 0 < h₁)
    (hgood : ∀ z, Z₀ ≤ z → z ∈ A → z ∉ H →
      ∃ h ∈ H, z + h ∈ A)
    (hsupply : ∀ N, ∃ v, N ≤ v ∧ N₀ ≤ v ∧ IsRepHub A v H ∧
      IsPairHub A v H ∧ v - h₀ ∈ A ∧ v - h₀ - h₁ ∈ A) :
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
  have hsup' : ∀ c, ∃ w, c < w ∧ N₀ ≤ w ∧ IsRepHub A w H ∧
      IsPairHub A w H ∧ w - h₀ ∈ A ∧ w - h₀ - h₁ ∈ A := by
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
  have hprops : ∀ k, N₀ ≤ v k ∧ IsRepHub A (v k) H ∧
      IsPairHub A (v k) H ∧ v k - h₀ ∈ A ∧
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
    exact door_targets_ghost h0 h0H hM₀ (hprops k).2.2.1
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
    exact door_two_difference_law hcov hM₀ hcard
      (hprops j).2.1 (hprops j).2.2.1 (hghost i) hh₀
      (hprops i).2.2.2.1
      (by have := hbvk i; omega)
      ⟨h₁, hh₁, hMlaw i⟩ hji
  exact door_good_deep_engine v h0 hcov hmono hgrow hh₁pos
    (by have := hbvk 0; omega)
    (fun k => (hprops k).2.2.2.1) hMlaw
    (fun k => (hprops k).2.2.2.2) hdlaw

/-! ## The walk kills: AP3 midpoint deletion -/

/-- **The AP3 midpoint engine.**  Cofinally many three-term
arithmetic progressions with one fixed common difference c ∈ A
force a surviving deletion: delete the midpoints along a
geometric subsequence; a deleted part in a pair is replaced by
stepping down (m − c) + c, a doubly-deleted pair by stepping
one midpoint down and the other up, (m − c) + (m' + c).  No
counterexample carries a cofinal fixed-difference AP3 family
through its own basis — the first unconditional AP kill,
consistent with the central branch's forced AP3-freeness. -/
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

/-- **THE GOOD HORN DIES BY WALKING.**  If every large basis
element keeps at least one good translate among two fixed
positive basis elements h₀ ≠ h₁, a surviving deletion exists —
full stop.  The good-translate walk climbs forever in
{h₀, h₁}-steps; either some colour repeats consecutively at
cofinally many heights — giving cofinal fixed-difference AP3s
and the midpoint engine — or the walk eventually alternates
perfectly, every two steps sum to h₀ + h₁, and deleting every
fifth walk element survives by two-step shifting.  The door
world's entire good horn (|H| = 2) is contradictory with hfail,
with no reference to mirrors, ghosts, or partners. -/
theorem good_two_walk_killed {A : Set ℕ} {N₀ h₀ h₁ Z₀ : ℕ}
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

/-- **THE SINGLE TRANSLATE LAW.**  Unconditional counterexample
law: for every positive basis element c, arbitrarily large
basis elements z have z + c OUT of A.  Otherwise the c-chain
z, z + c, z + 2c, … supplies cofinal fixed-difference AP3s and
the midpoint engine hands hfail a surviving deletion.  No
element's upward translate eventually captures the basis. -/
theorem single_translate_law {A : Set ℕ} {N₀ c : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hcA : c ∈ A) (hcpos : 0 < c) :
    ∀ Z₀, ∃ z, Z₀ ≤ z ∧ z ∈ A ∧ z + c ∉ A := by
  by_contra hno
  push_neg at hno
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

/-- **THE PAIR TRANSLATE LAW.**  Unconditional counterexample
law: for every two positive basis elements h₀, h₁, arbitrarily
large basis elements z have BOTH z + h₀ and z + h₁ out of A.
Otherwise the good-translate walk runs and dies by the walk
kill.  Every counterexample is cofinally two-sided
translate-free at every pair — the door world's strong horn is
not a case, it is the LAW, and the good horn is empty. -/
theorem pair_translate_law {A : Set ℕ} {N₀ h₀ h₁ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hh₀A : h₀ ∈ A) (hh₁A : h₁ ∈ A)
    (hh₀ : 0 < h₀) (hh₁ : 0 < h₁) :
    ∀ Z₀, ∃ z, Z₀ ≤ z ∧ z ∈ A ∧ z + h₀ ∉ A ∧ z + h₁ ∉ A := by
  by_contra hno
  push_neg at hno
  obtain ⟨Z₀, hZ₀⟩ := hno
  have hgood : ∀ z, Z₀ ≤ z → z ∈ A →
      z + h₀ ∈ A ∨ z + h₁ ∈ A := by
    intro z h1 h2
    by_cases ha : z + h₀ ∈ A
    · exact Or.inl ha
    · exact Or.inr (hZ₀ z h1 h2 ha)
  obtain ⟨B, hBsub, hBinf, hsurv⟩ :=
    good_two_walk_killed h0 hcov hh₀A hh₁A hh₀ hh₁ hgood
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

/-- **The slice law.**  A deletion's failure, in hub
vocabulary: cofinally many targets n have EVERY slice n − z
(z a survivor) pair-hubbed by the deleted set — every two-part
completion of every survivor is caught by B.  The lab shows
this demand is unmeetable in hall worlds; formally it is the
door to counting pressure: one deleted set must simultaneously
hub every slice family of every failure target. -/
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
  push_neg at hnb
  obtain ⟨n, hn, hnofail⟩ := hnb N
  refine ⟨n, hn, ?_⟩
  intro z hz hzB a ha b hb hab
  by_contra hno
  push_neg at hno
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

/-- **The double-slice law.**  The cascade's second axiom: at a
failure target, the survivor set S = A ∖ B is SUM-FREE against
every slice — no survivor pair completes any survivor to n.
Every element of A landing in n − s − S is deleted; the
survivors' three-fold sumset misses every failure target by
exactly this mechanism, slice by slice. -/
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
/-- **The quantitative cascade law.**  At any deletion's failure
targets, the ENTIRE survivor-slice spectrum is pair-poor: for
every survivor s, the slice n − s has at most |W| unordered
pairs, where W is any finite window catching the deleted
elements below n.  A sparse deletion forces every slice of
every failure target into uniform pair-poverty — the formal
counterpart of the lab's finding, and the counting blade
against the canonical core's unbounded r₂. -/
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
  have hhub : IsPairHub A (n - s) W := by
    intro a ha b hb hab
    rcases hslice s hs hsB a ha b hb (by omega) with h | h
    · exact Or.inl (hW a h (by omega))
    · exact Or.inr (hW b h (by omega))
  exact pair_hub_pair_count hhub

open Classical in
/-- **Covering density.**  An order-2 covering set has at least
√X elements below X: the chosen pair of each covered target is
an injection of [N₀, X] into the window's pair square.  The
mass side of every cascade count. -/
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
/-- **The pair flood.**  Welding the rep flood: when the flood
envelope avoids 0, every large positive basis element b
personally guards a target m ≥ b whose ENTIRE pair life routes
through the constant-size set P ∪ {b} — so r₂(m) ≤ |P| + 1.
A personal pair-poor guarded target for every basis element:
the density-free supply the cascade counting was missing. -/
theorem flood_pair_guard {A : Set ℕ} {N₀ X : ℕ}
    {P : Finset ℕ}
    (h0 : 0 ∈ A) (h0P : (0 : ℕ) ∉ P)
    (hflood : ∀ b ∈ A, X ≤ b → ∃ m, N₀ ≤ m ∧ b ≤ m ∧
      IsRepHub A m (insert b P)) :
    ∀ b ∈ A, X ≤ b → 0 < b → ∃ m, N₀ ≤ m ∧ b ≤ m ∧
      IsRepHub A m (insert b P) ∧
      IsPairHub A m (insert b P) ∧
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
  have hpair := pairHub_of_repHub h0 h0i hhub
  refine ⟨m, hmN, hbm, hhub, hpair, ?_⟩
  have h1 := pair_hub_pair_count hpair
  have h2 : (insert b P).card ≤ P.card + 1 :=
    Finset.card_insert_le _ _
  omega

/-- **THE REP FLOOD, POSITIVE ENVELOPE.**  The rep flood with
the envelope guaranteed to avoid 0: the dodge chain only ever
inserts picks at thresholds ≥ 1, so the classical envelope can
be taken 0-free.  This is what the 0-weld needs.  The theorem the campaign''s
assumed configurations were reaching for, with no interface beyond
covering and `0 ∈ A`: a counterexample yields ONE finite rep-free
envelope `P` and a threshold beyond which EVERY basis element `b`
personally guards a target `m ≥ b` at ORDER 3 — every
3-representation of `m` routes through `P ∪ {b}`.  Constant
cardinality; the freeness of `P` is the recorded non-vacuity (junk
envelopes are never free).  Proof: the rep dodge; if it never
stalls, all parts of a late target''s surviving representation lie
below the target and hence inside the stalled prefix''s shadow, so
the built deletion leaves every late target represented, refuting
`hfail` directly. -/
theorem rep_flood_pos_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P : Finset ℕ, RepFree A N₀ P ∧ (0 : ℕ) ∉ P ∧
      ∃ X, ∀ b ∈ A, X ≤ b →
      ∃ m, N₀ ≤ m ∧ b ≤ m ∧ IsRepHub A m (insert b P) := by
  classical
  by_contra hno
  push_neg at hno
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
        rw [IsRepHub] at hnh
        push_neg at hnh
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
/-- **THE PAIR FLOOD, UNCONDITIONAL.**  Every counterexample
world carries a constant C and a free 0-less envelope P such
that EVERY sufficiently large basis element b personally guards
a target m ≥ b whose ENTIRE pair life routes through P ∪ {b}
and whose unordered pair count is at most C.  Pair-poverty is
not scattered — it is pinned to every basis element personally,
with one constant, density-free.  The canonical core's
unbounded r₂ and this law now share one world: the enemy's
r₂-blowups live only on targets guarded by NO large element. -/
theorem personal_pair_guard_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P : Finset ℕ, RepFree A N₀ P ∧ (0 : ℕ) ∉ P ∧
      ∃ X, ∀ b ∈ A, X ≤ b → 0 < b →
      ∃ m, N₀ ≤ m ∧ b ≤ m ∧ IsRepHub A m (insert b P) ∧
      IsPairHub A m (insert b P) ∧
      ((Finset.range (m + 1)).filter
        (fun a => a ∈ A ∧ (m - a) ∈ A ∧ 2 * a ≤ m)).card ≤
        P.card + 1 := by
  obtain ⟨P, hPfree, h0P, X, hflood⟩ :=
    rep_flood_pos_of_hfail h0 hcov hfail
  exact ⟨P, hPfree, h0P, X,
    flood_pair_guard h0 h0P hflood⟩

open Classical in
/-- **Ghost or centre.**  The pair flood's placement law: each
large basis element's personal target either IS the element
itself — its every nontrivial pair routed through the fixed
envelope — or is a GHOST, forced out of A with its whole pair
life through P ∪ {b}.  Unconditional: every counterexample is
saturated with personal door-configurations. -/
theorem pair_flood_ghost_or_center {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P : Finset ℕ, RepFree A N₀ P ∧ (0 : ℕ) ∉ P ∧
      ∃ X, ∀ b ∈ A, X ≤ b →
      ∃ m, N₀ ≤ m ∧ b ≤ m ∧ IsRepHub A m (insert b P) ∧
      IsPairHub A m (insert b P) ∧
      ((Finset.range (m + 1)).filter
        (fun a => a ∈ A ∧ (m - a) ∈ A ∧ 2 * a ≤ m)).card ≤
        P.card + 1 ∧
      (m = b ∨ m ∉ A) := by
  obtain ⟨P, hPfree, h0P, X, hguard⟩ :=
    personal_pair_guard_of_hfail h0 hcov hfail
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
  rcases street_target_notMem_or_window h0 h0i hpair with
    h | h
  · exact Or.inr h
  · rcases Finset.mem_insert.1 h with h1 | h1
    · exact Or.inl h1
    · exfalso
      have h2 : m ≤ P.sup id := Finset.le_sup (f := id) h1
      omega

open Classical in
/-- **THE PAIR-FLOOD FUNNEL.**  The block's closing summit:
every counterexample world funnels, through its own pair flood,
into one of three cofinal configurations over ONE fixed free
0-less envelope P:

I. P-CENTRED MEMBERS — cofinally many basis elements whose
   every positive pair routes through P;
II. ROTATOR GHOSTS — cofinally many b ∈ A with a partner
   w ∈ A whose sum b + w is OUT of A and pair-hubbed by
   P ∪ {b} — the canonical core-and-rotator configuration;
III. THE PURE HALL — cofinally many ghosts pair-hubbed by the
   FIXED P alone: the door configuration, unconditional.

The door is not a lane; it is one of three faces of the flood.
The remaining core of Erdős 881 is the defeat of these three
faces and the rank-ω room. -/
theorem the_pair_flood_funnel {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P : Finset ℕ, RepFree A N₀ P ∧ (0 : ℕ) ∉ P ∧
    ((∀ N, ∃ b, N ≤ b ∧ b ∈ A ∧ ∀ x ∈ A, ∀ y ∈ A,
        0 < x → 0 < y → x + y = b → x ∈ P ∨ y ∈ P) ∨
     (∀ N, ∃ b w, N ≤ b ∧ b ∈ A ∧ w ∈ A ∧ b + w ∉ A ∧
        IsRepHub A (b + w) (insert b P) ∧
        IsPairHub A (b + w) (insert b P)) ∨
     (∀ N, ∃ m b, N ≤ b ∧ b ≤ m ∧ b ∈ A ∧ m ∉ A ∧
        IsRepHub A m (insert b P) ∧ IsPairHub A m P)) := by
  obtain ⟨P, hPfree, h0P, X, hguard⟩ :=
    pair_flood_ghost_or_center h0 hcov hfail
  refine ⟨P, hPfree, h0P, ?_⟩
  by_cases hI : ∀ N, ∃ b, N ≤ b ∧ b ∈ A ∧ ∀ x ∈ A, ∀ y ∈ A,
      0 < x → 0 < y → x + y = b → x ∈ P ∨ y ∈ P
  · exact Or.inl hI
  · obtain ⟨NA, hNA⟩ := not_forall.mp hI
    by_cases hII : ∀ N, ∃ b w, N ≤ b ∧ b ∈ A ∧ w ∈ A ∧
        b + w ∉ A ∧ IsRepHub A (b + w) (insert b P) ∧
        IsPairHub A (b + w) (insert b P)
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

/-- **The singleton hall is a marriage stream.**  Face III of
the funnel with a one-element envelope is exactly the
unique-pair configuration: cofinal ghosts m whose ONLY pair is
(p, m − p) — the fixed element p order-2-owns cofinally many
targets at explicit positions p + A.  The funnel's third face,
handed to the marriage network in its native vocabulary. -/
theorem pure_hall_singleton_form {A : Set ℕ} {N₀ p : ℕ}
    (hcov : PairCovers A N₀)
    (hface : ∀ N, ∃ m, N ≤ m ∧ m ∉ A ∧
      IsPairHub A m ({p} : Finset ℕ)) :
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

/-- **The two-level colour law.**  At a face-III target — rep
hub P ∪ {b}, pair hub P alone — the defective mirror's colour
ALWAYS has a dead translate, including when the colour is the
rotator b itself: a live translate would recombine with the
mirror image into a pair of m forced through the small envelope,
which the size window forbids.  The rotator obeys the same
translate discipline as the hall. -/
theorem face_three_color_law {A : Set ℕ} {N₀ M₀ m b : ℕ}
    {P : Finset ℕ}
    (hcov : PairCovers A N₀) (hM : ∀ p ∈ P, p ≤ M₀)
    (hrep : IsRepHub A m (insert b P))
    (hpair : IsPairHub A m P)
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

/-- **The rotator-gap dichotomy.**  Face III splits on the gap
between targets and their rotators.  Either the gaps stay
bounded — cofinal instances with m ≤ b + G, the near-diagonal
regime — or the two-level colour law's window opens for every
basis element and the DEAD SPECTRUM pigeonhole fires: every
large basis element has a dead translate into the fixed
envelope, or its translates die along the rotator stream
itself.  Every element of the basis is translate-poor against
face III's own material. -/
theorem face_three_gap_dichotomy {A : Set ℕ} {N₀ M₀ : ℕ}
    {P : Finset ℕ}
    (hcov : PairCovers A N₀) (hM : ∀ p ∈ P, p ≤ M₀)
    (hface : ∀ N, ∃ m b, N ≤ b ∧ b ≤ m ∧ b ∈ A ∧ m ∉ A ∧
      IsRepHub A m (insert b P) ∧ IsPairHub A m P) :
    (∃ G, ∀ N, ∃ m b, N ≤ b ∧ b ≤ m ∧ m ≤ b + G ∧ b ∈ A ∧
      m ∉ A ∧ IsRepHub A m (insert b P) ∧ IsPairHub A m P) ∨
    (∀ z ∈ A, M₀ < z →
      (∃ p ∈ P, z + p ∉ A) ∨
      (∀ N, ∃ b, N ≤ b ∧ b ∈ A ∧ z + b ∉ A)) := by
  classical
  by_cases hbdd : ∃ G, ∀ N, ∃ m b, N ≤ b ∧ b ≤ m ∧
      m ≤ b + G ∧ b ∈ A ∧ m ∉ A ∧
      IsRepHub A m (insert b P) ∧ IsPairHub A m P
  · exact Or.inl hbdd
  · right
    intro z hzA hzM
    by_cases hzP : ∃ p ∈ P, z + p ∉ A
    · exact Or.inl hzP
    · push_neg at hzP
      right
      intro N
      set G := z + 2 * M₀ + N₀ + 1 with hG
      have hnb : ¬∀ N', ∃ m b, N' ≤ b ∧ b ≤ m ∧ m ≤ b + G ∧
          b ∈ A ∧ m ∉ A ∧ IsRepHub A m (insert b P) ∧
          IsPairHub A m P := fun hall => hbdd ⟨G, hall⟩
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

/-- **Near-diagonal stabilization.**  In the bounded-gap regime
one single offset g ≤ G serves cofinally: infinitely many basis
elements b whose g-translate b + g is a GHOST pair-hubbed by
the fixed envelope, with the rotator b guarding it at order 3.
Face III's near-diagonal horn is a fixed-offset ghost family —
the single translate law's witnesses, upgraded with full hub
structure at one explicit offset. -/
theorem near_diagonal_stabilized {A : Set ℕ} {G : ℕ}
    {P : Finset ℕ}
    (hbdd : ∀ N, ∃ m b, N ≤ b ∧ b ≤ m ∧ m ≤ b + G ∧ b ∈ A ∧
      m ∉ A ∧ IsRepHub A m (insert b P) ∧ IsPairHub A m P) :
    ∃ g, g ≤ G ∧ ∀ N, ∃ b, N ≤ b ∧ b ∈ A ∧ b + g ∉ A ∧
      IsRepHub A (b + g) (insert b P) ∧
      IsPairHub A (b + g) P := by
  classical
  by_contra hno
  push_neg at hno
  have hKg : ∀ g : ℕ, ∃ Kg, g ≤ G → ∀ b, Kg ≤ b → b ∈ A →
      b + g ∉ A → IsRepHub A (b + g) (insert b P) →
      ¬IsPairHub A (b + g) P := by
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

/-- **Face I, honestly split** (junk-test repair).  P-centred
membership is vacuous for basis elements with NO positive pair
at all, so face I splits: either cofinally many members carry a
genuine positive pair with ALL positive pairs through the
envelope, or the basis has cofinally many PRIMITIVE elements —
members that are not sums of two positive members.  Both horns
carry real information; neither is allowed to hide behind the
other. -/
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
    · push_neg at hpos
      refine ⟨b, by omega, hbA, ?_⟩
      intro x hx y hy hx0 hy0 hxy
      exact hpos x hx y hy hx0 hy0 hxy

/-- **The free-tower mirror.**  At a near-diagonal face-III
target b + g, every basis element in the huge window
(g, b − 2M₀ − N₀ − 1] mirrors PURELY through the envelope — the
rotator colour is size-excluded — and the mirror colour's
translate is dead: b + g − z − p ∈ A and z + p ∉ A for some
p ∈ P.  The g₀-tower's mirror-and-translate structure,
recovered for a general envelope without any routing
hypothesis. -/
theorem free_tower_mirror {A : Set ℕ} {N₀ M₀ g b : ℕ}
    {P : Finset ℕ}
    (hcov : PairCovers A N₀) (hM : ∀ p ∈ P, p ≤ M₀)
    (hrep : IsRepHub A (b + g) (insert b P))
    (hpair : IsPairHub A (b + g) P)
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

/-- **The free tower's level structure.**  Singleton envelope:
at a near-diagonal face-III target b + g with envelope {p}, the
whole window reflects through the constant level L' = b + g − p
— every window element z has L' − z ∈ A — and the STRONG
translate law holds across the window: z + p ∉ A for every
window z.  The g₀-tower's exact structure (levels, mirror,
translate desert), recovered with no routing and no anchor
hypothesis.  The tower kill lacks only its ladder: one c ∈ A
with 2c − p ∈ A in range would close this room. -/
theorem free_tower_singleton_levels {A : Set ℕ}
    {N₀ M₀ g b p : ℕ}
    (hcov : PairCovers A N₀) (hM : p ≤ M₀)
    (hrep : IsRepHub A (b + g) (insert b {p}))
    (hpair : IsPairHub A (b + g) ({p} : Finset ℕ)) :
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

/-- **Pair-hub corep.**  A singleton pair hub's target donates
its level: the covering pair of m must route through p, so
L' = m − p is a basis member.  The free tower's levels are
genuine material, exactly as the g₀-tower's coreps were. -/
theorem pair_hub_corep {A : Set ℕ} {N₀ m p : ℕ}
    (hcov : PairCovers A N₀) (hm : N₀ ≤ m)
    (hpair : IsPairHub A m ({p} : Finset ℕ)) :
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

/-- **The no-ladder affine desert.**  If the enemy defends the
free tower by total AP3-freeness at p (no ladder), the defence
costs a new desert: every window element's mirror image is a
large basis element c whose double-shift 2c − p must die, so
the affine family 2L' − p − 2z is FORCED OUT of A across the
window.  Midpoint-freeness at one point propagates, through the
tower's own mirror, into a two-parameter exclusion zone. -/
theorem no_ladder_affine_desert {A : Set ℕ}
    {N₀ M₀ g b p T : ℕ}
    (hcov : PairCovers A N₀) (hM : p ≤ M₀)
    (hrep : IsRepHub A (b + g) (insert b {p}))
    (hpair : IsPairHub A (b + g) ({p} : Finset ℕ))
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
/-- **Windows are populated.**  Coverage forces mass into every
window: the count of basis elements in (Y, X] plus the trivial
bound below Y squares to at least the covered range.  Keeps the
free tower's mirror, translate, and desert laws non-vacuous on
windows of width ≫ √X. -/
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

/-- **Personal fragility.**  The located form of the fragile
supply: every large basis element personally guards a target
with at most |P| + 1 disjoint triple representations.  The
mixed regime's fragile half is not merely cofinal — it is
pinned above every basis element, with one constant. -/
theorem personal_fragility {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P : Finset ℕ, RepFree A N₀ P ∧ (0 : ℕ) ∉ P ∧
      ∃ X, ∀ b ∈ A, X ≤ b → 0 < b →
      ∃ m, N₀ ≤ m ∧ b ≤ m ∧
        ¬HasDisjointTripleReps A m (P.card + 2) := by
  obtain ⟨P, hPfree, h0P, X, hguard⟩ :=
    personal_pair_guard_of_hfail h0 hcov hfail
  refine ⟨P, hPfree, h0P, X, ?_⟩
  intro b hbA hXb hbpos
  obtain ⟨m, hmN, hbm, hrep, hpair, hcount⟩ :=
    hguard b hbA hXb hbpos
  refine ⟨m, hmN, hbm, ?_⟩
  intro hK
  have h1 := disjoint_reps_le_hub_card hrep hK
  have h2 : (insert b P).card ≤ P.card + 1 :=
    Finset.card_insert_le _ _
  omega

/-- **The parity fringe law.**  A single-parity window cannot
pair-cover odd-parity targets internally: window-window sums
are even.  Every pair of an odd target in range has its minor
part in the low fringe [0, Y].  The parity defence buys the
enemy the affine desert but chains its odd targets to a finite
fringe. -/
theorem parity_window_fringe {A : Set ℕ} {Y X ε : ℕ}
    (hpar : ∀ a ∈ A, Y < a → a ≤ X → a % 2 = ε) :
    ∀ n, n ≤ X → n % 2 = 1 →
      ∀ x ∈ A, ∀ y ∈ A, x + y = n → x ≤ Y ∨ y ≤ Y := by
  intro n hnX hodd x hx y hy hxy
  by_contra hno
  push_neg at hno
  have h1 := hpar x hx (by omega) (by omega)
  have h2 := hpar y hy (by omega) (by omega)
  omega

/-- **The fringe partner law.**  With covering, every odd
target in a single-parity window's range has a pair through the
fringe: some x ≤ Y in A with n − x ∈ A.  The basis is trapped
within Y + 1 of every odd target — near-syndetic structure, the
opening of the completeness road (`subset_sum_complete_of_
small_gaps` → the completeness pinch). -/
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

/-- **Parity windows force syndeticity.**  Under a single-parity
window, the basis meets EVERY interval of length 2Y + 2 in the
range: an odd target inside the interval donates its fringe
partner.  The enemy's parity defence converts √-sparseness into
bounded gaps — the exact input of the small-gaps completeness
criterion. -/
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
/-- **The parity defence costs linear density.**  A
single-parity window contains at least one basis element per
2Y + 3 integers: k disjoint blocks donate k distinct elements.
Sidon-sparseness and the parity defence are incompatible on the
same window — the enemy pays for every parity escape in
density, and density is what all the counting engines eat. -/
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
/-- **Dense windows concentrate pairs.**  If a window carries
enough basis elements, some target in the doubled range
collects more than K window-pairs: the pair square outnumbers
the available sums.  Dense regions manufacture pair-rich
targets. -/
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
/-- **Pair-rich targets are hub-immune.**  A target with more
than 2|H| ordered window-pairs cannot be pair-hubbed by H:
every ordered pair donates its hub part, and each hub element
serves at most two ordered pairs.  Dense windows therefore
defeat every small hall on their doubled range — the halls'
targets are forced OUT of the sums of every dense window. -/
theorem pair_fiber_hub_bound {A : Set ℕ} {u v m : ℕ}
    {H : Finset ℕ} (hhub : IsPairHub A m H) :
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

/-- **The odd channel's parity law.**  If the basis is single-
parity beyond Y, every pair of every odd target beyond 2Y has
its minor part in the OPPOSITE-parity fringe: two large parts
sum evenly, and the large partner fixes the fringe part's
parity.  Not a cofinal family — every odd target at once. -/
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
/-- **THE ODD CHANNEL IS A HALL.**  Globally single-parity
worlds hand their ENTIRE odd channel to one finite hall: the
opposite-parity fringe F* pair-hubs every odd target beyond 2Y.
This is the door configuration at total saturation — no
placement liberty, no dodging, every odd target at once — and
it caps r₂ on the whole odd channel at |F*| ≤ Y + 1, forcing
all of the canonical core's r₂-blowups onto the even channel,
one 2-adic level down. -/
theorem global_parity_odd_hall {A : Set ℕ} {Y ε : ℕ}
    (hpar : ∀ a ∈ A, Y < a → a % 2 = ε) :
    ∀ n, 2 * Y < n → n % 2 = 1 →
      IsPairHub A n ((Finset.range (Y + 1)).filter
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

/-- **The global parity dichotomy** — the last splitter.
Either the basis is eventually single-parity (the saturated
odd-hall world) or both parity classes persist cofinally. -/
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
/-- **The odd channel's ordered pair cap.**  In single-parity
worlds every odd target beyond 2Y has at most 2Y + 2 ordered
pair representations: every pair part is in the fringe or
mirrors into it. -/
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
/-- **The blowups are forced even.**  In single-parity worlds
under hfail, the canonical core's unbounded-r₂ witnesses are
eventually all EVEN: the saturated odd hall caps the odd
channel, so the enemy's pair riches must live one 2-adic level
down.  The descent has teeth. -/
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

/-- **The half-world covers.**  In a single-parity world the
even channel descends: every pair of an even target has both
parts ≡ ε (the large partner forces the fringe part's parity
too), so the half-world A' = {x : ε + 2x ∈ A} inherits order-2
covering at half scale.  The 2-adic descent's first rung,
formal: each defended level hands the game to its half-world
intact. -/
theorem half_world_covers {A : Set ℕ} {N₀ Y ε : ℕ}
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

/-- **The ε-channel lift.**  Order-3 survival in the half-world
lifts to the ε-channel upstairs: a surviving half-triple
x' + y' + z' = n' lifts part-by-part to
(ε + 2x') + (ε + 2y') + (ε + 2z') = 3ε + 2n', avoiding the
lifted deletion.  The other channel needs fringe assistance —
the descent's (2,3)-mixed structure, honestly split. -/
theorem half_world_lift_channel {A : Set ℕ} {ε N' : ℕ}
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

/-- **The off-channel lift.**  Opposite-parity targets ascend
by fringe assistance: one off-parity fringe element plus a
surviving half-world PAIR covers the other channel.  The
descent's survival transfer is (2,3)-mixed: order-3 on the
ε-channel, order-2 plus a fringe key on the rest. -/
theorem half_world_lift_offchannel {A : Set ℕ} {ε N' : ℕ}
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

/-- **THE DESCENT INVARIANT.**  In a single-parity world with
one off-parity fringe key, hfail DESCENDS: every infinite
half-world deletion fails at order 2 or at order 3.  The
half-world inherits the (2,3)-mixed counterexample interface —
the 2-adic recursion is formally armed. -/
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
      half_world_lift_channel hε hs3 n (by omega) hch
    refine ⟨![x, y, z], ?_, ?_⟩
    · intro i
      match i with
      | 0 => exact ⟨hx, hxB⟩
      | 1 => exact ⟨hy, hyB⟩
      | 2 => exact ⟨hz, hzB⟩
    · simpa [Fin.sum_univ_three] using hsum
  · obtain ⟨x, hx, y, hy, z, hz, hxB, hyB, hzB, hsum⟩ :=
      half_world_lift_offchannel hε hs2 hf hfpar n
        (by omega) (by omega)
    refine ⟨![x, y, z], ?_, ?_⟩
    · intro i
      match i with
      | 0 => exact ⟨hx, hxB⟩
      | 1 => exact ⟨hy, hyB⟩
      | 2 => exact ⟨hz, hzB⟩
    · simpa [Fin.sum_univ_three] using hsum

open Classical in
/-- **The saturated fringe is nonempty.**  Single-parity worlds
must keep at least one opposite-parity key in the fringe — odd
targets have no other door. -/
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
/-- **The popular fringe key.**  One opposite-parity fringe
element partners cofinally many odd targets: the saturated
hall has a door, and the door's partner stream is the whole
odd channel's backbone. -/
theorem saturated_popular_fringe {A : Set ℕ} {N₀ Y ε : ℕ}
    (hcov : PairCovers A N₀)
    (hpar : ∀ a ∈ A, Y < a → a % 2 = ε) :
    ∃ f, f ∈ A ∧ f ≤ Y ∧ f % 2 ≠ ε ∧
      ∀ N, ∃ n, N ≤ n ∧ n % 2 = 1 ∧ f ≤ n ∧ n - f ∈ A := by
  classical
  by_contra hno
  push_neg at hno
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

/-- **Two-level descent: the mod-4 cylinder.**  If the world is
single-parity and its half-world is single-parity again, the
large basis elements live in ONE residue class mod 4.  Each
descent level halves the enemy's residue freedom; k levels pin
a 2^k-cylinder, forcing gaps ≥ 2^k beyond growing thresholds —
the quantitative Cantor calibration of infinitely descending
worlds. -/
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

/-- **The ω-descent cylinder law.**  An iterated single-parity
tower of half-worlds pins the basis, beyond level thresholds,
into ONE 2-adic cylinder per depth: every large element
decomposes as (address) + 2^k · (level-k survivor).  Infinitely
descending worlds are asymptotically 2-adic — Cantor-caliber —
with residue freedom zero at every depth. -/
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
/-- **Cylinder sparsity.**  A single 2-adic lane holds at most
one element per 2^k integers: the level-k decomposition injects
the tail into its survivor indices. -/
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
/-- **The threshold race.**  Cylinder containment against
covering: the level threshold plus the lane's own capacity must
square to the covered range.  Deep lanes force √-scale
thresholds — the racing cost of every descent level, made
quantitative. -/
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

/-- **The depth cost.**  Descent thresholds grow geometrically:
a level-k cylinder needs its threshold within N₀ + 2 of
2^(k−2).  Instantiating the race at X = 4^(k−1): the enemy pays
an exponential threshold for every level of parity defence —
the racing lane's speed limit, in closed form. -/
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
  push_neg at hlt
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

/-- **Free sets dodge.**  The rank-ω room's supply is agile:
free sets of every size exist AVOIDING any prescribed finite
obstruction — take a larger one and discard the collisions.
Whatever diagonal the rank kill runs, the enemy cannot block it
with finitely much material. -/
theorem free_sets_dodge {A : Set ℕ} {N₀ : ℕ}
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

/-- **The free disjoint stream.**  From the rank branch's bare
supply — free sets of every size — dodging builds an infinite
PAIRWISE DISJOINT stream of growing free sets: the rank room
carries its own shell stratification with no oracle and no
covering hypothesis. -/
theorem free_disjoint_stream {A : Set ℕ} {N₀ : ℕ}
    (hfree : ∀ c, ∃ P : Finset ℕ, RepFree A N₀ P ∧
      c ≤ P.card) :
    ∃ Q : ℕ → Finset ℕ,
      (∀ k, RepFree A N₀ (Q k) ∧ k ≤ (Q k).card) ∧
      ∀ j k, j < k → Disjoint (Q j) (Q k) := by
  classical
  have hdodge := free_sets_dodge hfree
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

/-- **Generic Higman chaining.**  ANY sequence of finsets has an
infinite subsequence forming a sorted-list Higman chain — no
hypotheses at all.  The Nash-Williams door, detached from the
stratification: the rank room's own disjoint stream can now
walk through it. -/
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
  haveI hrefl : IsRefl (List ℕ)
      (List.SublistForall₂ ((· ≤ ·) : ℕ → ℕ → Prop)) :=
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

/-- **THE RANK ROOM'S OWN CHAIN.**  From the four lanes' rank
branch alone — free positive envelopes of every size — the rank
room builds its own nonempty disjoint growing shell stream and
walks it through the detached Nash-Williams door: a sorted-list
Higman chain of the room's own free material, no oracle, no
stratification.  The spine program's entry interface,
reproduced inside the rank refuge: the third core is a corridor
toward the street machinery, not a separate room. -/
theorem rank_room_chain {A : Set ℕ} {N₀ : ℕ}
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

/-- **THE RANK ROOM'S SPINE.**  The corridor walked: the rank
branch's own chain threads a strictly increasing canonical
lineage through its own disjoint free shells — the spine,
reproduced from bare rank supply with no oracle.  The rank
refuge now contains the street program's starting object built
from its own material. -/
theorem rank_room_spine {A : Set ℕ} {N₀ : ℕ}
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
    rank_room_chain hfree
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

/-- **Chain or width.**  The final fork's rank branch,
strengthened at its source: the stall windows' minimality kills
every shorter width at the same base, so the rank supply is
CHAIN-REACHABLE — ascending windows all of whose initial
segments are free.  The rank room's supply is not loose free
sets but genuine FreeStep chains of every length: the prefix-
freeness gap of the corridor closes at the fork itself. -/
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
        IsRepHub A m ((Finset.range J).image
          (fun j => x (s + j)))) := by
  classical
  obtain ⟨Q, σ, x, hxmono, hxmem, hQfree, hQmem, hstall⟩ :=
    spine_stalls_hereditarily h0 hcov hanchor hfail
  have hxA : ∀ t, x t ∈ A ∧ 0 < x t :=
    fun t => hQmem _ _ (hxmem t)
  set Pred : ℕ → ℕ → Prop := fun s J => ∃ m, N₀ ≤ m ∧
    IsRepHub A m ((Finset.range J).image (fun j => x (s + j)))
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
      push_neg at hlt
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
        exact stall_window_not_in_shell (hQfree (σ s))
          (Finset.singleton_subset_iff.2 (by
            simpa using hxmem s)) hm hhub
    refine ⟨x, hxmono, hxA, L, fun s => ?_⟩
    obtain ⟨m, hm, hhub⟩ := hJdef s
    exact ⟨Nat.find (hne s), m, hJ2 s, hL s, hm, hhub⟩
  · left
    push_neg at hbnd
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
      · rw [repFree_iff_forall_not_hub]
        intro m hm hhub
        exact hJmin s j (by omega) ⟨m, hm, hhub⟩

open Classical in
/-- **The channel blowup.**  The canonical core's unbounded
pair counts concentrate in one parity channel: even-even,
odd-odd, or mixed.  Each channel is a door one level down the
2-adic tree — ee and oo descend to half-world pair blowups,
mixed to cross-pairs of the two half-sets.  The tree descent's
opening pigeonhole. -/
theorem r2_channel_blowup {A : Set ℕ} {N₀ : ℕ}
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
  push_neg at hno
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
/-- **The ee-channel descends.**  Even-even pairs of an even
target halve into genuine pairs of the half-world
H₀ = {y : 2y ∈ A} at the half target: the channel count injects
downstairs.  The tree descent's counting edge, concrete. -/
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
/-- **The ee-blowup descends.**  If the even-even channel
carries the unbounded pair counts, the HALF-WORLD inherits
unbounded pair counts cofinally: the enemy's riches provably
move one level down the 2-adic tree. -/
theorem ee_blowup_descends {A : Set ℕ}
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
/-- **The oo-channel descends.**  Odd-odd pairs of an even
target halve into pairs of the shifted half-world
H₁ = {y : 2y + 1 ∈ A} at the target v/2 − 1: the second
counting edge of the tree. -/
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
/-- **The oo-blowup descends.**  If the odd-odd channel carries
the unbounded pair counts, the SHIFTED half-world inherits
them: the tree's second drain, formal. -/
theorem oo_blowup_descends {A : Set ℕ}
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
/-- **The mixed channel descends.**  Mixed-parity pairs of an
odd target drain into CROSS-pairs between the two half-worlds
at the half target (v−1)/2: each mixed pair, from either side,
lands on a cross-pair, at most two-to-one.  The tree's third
and last counting edge. -/
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
/-- **THE TOTAL DRAIN.**  Every counterexample's pair riches
provably reappear one 2-adic level down: in the half-world H₀,
the shifted half-world H₁, or the cross-structure between them.
The channel pigeonhole picks the direction; the three counting
edges carry the wealth.  No 2-adic level can hold the canonical
core's blowups — the tree drains forever. -/
theorem the_total_drain {A : Set ℕ} {N₀ : ℕ}
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
  rcases r2_channel_blowup h0 hcov hfail with hee | hoo | hmx
  · exact Or.inl (ee_blowup_descends hee)
  · exact Or.inr (Or.inl (oo_blowup_descends hoo))
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

/-- **The covering channel split.**  Every even target's pair
has equal parities, so it descends whole: the half target is
H₀-pair-covered or the shifted half target is H₁-pair-covered.
Coverage, like wealth, cannot stay at one 2-adic level. -/
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

/-- **The odd channel crosses.**  Every odd target's pair is
mixed, descending to a CROSS pair of the two half-worlds:
2y + (2y' + 1) = n.  The tree's covering laws are total:
every target's coverage lives one level down, in a channel. -/
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

/-- **The mixing cross-slice law.**  hfail speaks downstairs in
mixing worlds too: deleting any infinite H₀-part forces cofinal
failure targets whose every odd-survivor slice has ALL its
cross-pairs captured on the H₀ side — the even part of every
mixed triple routes through the lifted deletion, because odd
material can never be deleted by an even lift.  The slice law's
image in the tree's cross-channel. -/
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
/-- **Cross-slice poverty.**  The quantitative form: at the
mixing failure targets, every odd-survivor slice's cross-pair
count is bounded by any window catching the deleted H₀-part —
sparse deletions force uniform cross-pair poverty across the
whole slice family, one level down.  The cascade's counting
blade, now cutting in the tree's cross-channel. -/
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

/-- **Joint half-covering.**  The two half-worlds jointly cover
at half scale: every half target is an H₀-pair sum or, shifted
by one, an H₁-pair sum.  The tree node's children form a
covering system — the interface the ω-iteration consumes. -/
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

/-- **The half-cover dichotomy.**  One child channel serves
cofinally: the even half-world pair-covers arbitrarily large
half targets, or the odd one does.  Every tree node passes
covering duty to at least one child — the descent always has a
live branch. -/
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
/-- **The generic cross-channel split.**  Any pair of sets
whose cross-pair counts blow up cofinally has the blowup in one
of the four parity channels.  Cross-systems are closed under
this split, so the drain ITERATES: this is the induction step's
pigeonhole, hypothesis-free beyond the supply itself. -/
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
  push_neg at hno
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
/-- **The generic cross-descent.**  All four edges at once: the
(p, q)-parity channel of a cross-system (S, T) injects into the
cross-system of the (p, q)-children at the reduced target.
With the split, the drain machinery is closed under iteration:
cross-systems all the way down. -/
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
/-- **The generic cross-blowup descends.**  If the
(p, q)-channel of a cross-system carries unbounded counts, the
(p, q)-child cross-system inherits them: the drain's induction
step, complete for all four edges. -/
theorem cross_blowup_descends {S T : Set ℕ} {p q : ℕ}
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
/-- **THE ω-DRAIN.**  Every counterexample owns an infinite
path through the 2-adic tree of cross-systems along which pair
wealth persists at EVERY level: starting from (A, A), each
level's split picks a parity square and the generic descent
carries the blowup down, forever.  The enemy's riches trace an
infinite 2-adic address — the formal shadow of the Cantor
cascade, extracted from hfail alone. -/
theorem the_omega_drain {A : Set ℕ} {N₀ : ℕ}
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
        (cross_blowup_descends (by omega) (by omega) h1)⟩
    · exact ⟨0, 1, by omega, by omega, hconv 0 1
        (cross_blowup_descends (by omega) (by omega) h1)⟩
    · exact ⟨1, 0, by omega, by omega, hconv 1 0
        (cross_blowup_descends (by omega) (by omega) h1)⟩
    · exact ⟨1, 1, by omega, by omega, hconv 1 1
        (cross_blowup_descends (by omega) (by omega) h1)⟩
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
/-- **Blowup worlds are infinite.**  Cross-pair wealth forces
both carriers infinite: the filter's members live in S and
their reflections in T.  Every world on the ω-drain's path is
infinite on both sides. -/
theorem cross_blowup_infinite {S T : Set ℕ}
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
/-- **THE 2-ADIC CLUSTER.**  The drain's path lifts to the root:
every counterexample contains an infinite nested address tower —
one residue class mod 2^k at every depth, consistently nested,
each carrying infinitely many basis elements.  A profinite
accumulation point of the basis, extracted from hfail alone:
the Cantor cascade is no longer a shadow but literal nested
material inside A. -/
theorem drain_address_cluster {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ c : ℕ → ℕ, c 0 = 0 ∧
      (∀ k, ∃ p, p < 2 ∧ c (k + 1) = c k + 2 ^ k * p) ∧
      ∀ k N, ∃ a, N ≤ a ∧ a ∈ A ∧
        ∃ y, a = c k + 2 ^ k * y := by
  obtain ⟨S, T, hS0, hT0, hstep, hblow⟩ :=
    the_omega_drain h0 hcov hfail
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
    fun k => (cross_blowup_infinite (hblow k)).1
  refine ⟨c, hc0, fun k => ⟨pf k, hpf k, hcS k⟩, ?_⟩
  intro k N
  obtain ⟨y, hyS, hyN⟩ := (hinf k).exists_gt N
  have hple : y ≤ 2 ^ k * y :=
    Nat.le_mul_of_pos_left y (pow_pos (by omega) k)
  exact ⟨c k + 2 ^ k * y, by omega, (hlift k y).1 hyS,
    y, rfl⟩

open Classical in
/-- **THE REPAIR MINE.**  Root-coordinate export of the drain's
wealth at count two: every counterexample contains, at every
2-adic depth k and beyond every bound, a repair quadruple —
a, a+δ, b, b−δ all in A with the SAME difference δ, 2^k ∣ δ,
and matched sums a + b = (a+δ) + (b−δ).  A Sidon set has no
repeated difference at all: this is counting content, not
covering junk.  The raw material the translate-law and
carry-repair engines consume, guaranteed at every depth of the
2-adic tree. -/
theorem drain_repair_mine {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ k C, ∃ a b δ : ℕ, 0 < δ ∧ 2 ^ k ∣ δ ∧ C ≤ a ∧ δ ≤ b ∧
      a ∈ A ∧ a + δ ∈ A ∧ b ∈ A ∧ b - δ ∈ A := by
  obtain ⟨S, T, hS0, hT0, hstep, hblow⟩ :=
    the_omega_drain h0 hcov hfail
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
/-- **DRAIN TARGETS ARE 2-ADICALLY PINNED.**  The wealthy
targets manufactured by the ω-drain carry addresses: there is a
nested residue tower e (steps of size ≤ 2·2^k) such that at
every depth k, beyond every bound, some target congruent to
e k mod 2^k carries arbitrarily large root-coordinate pair
wealth.  Sharpens `r2_unbounded_of_hfail`: the Sidon door is
closed CYLINDER BY CYLINDER along one 2-adic point — the
collision battleground with the street branch's width-capped
hub targets. -/
theorem drain_wealth_addresses {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ e : ℕ → ℕ, e 0 = 0 ∧
      (∀ k, ∃ r, r ≤ 2 ∧ e (k + 1) = e k + 2 ^ k * r) ∧
      ∀ k C N, ∃ w y, N ≤ w ∧ w = e k + 2 ^ k * y ∧
        C ≤ ((Finset.range (w + 1)).filter
          (fun x => x ∈ A ∧ (w - x) ∈ A)).card := by
  obtain ⟨S, T, hS0, hT0, hstep, hblow⟩ :=
    the_omega_drain h0 hcov hfail
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
/-- **THE WEALTH CAP.**  A 0-free order-3 hub caps its target's
ENTIRE pair wealth: through the 0-weld the hub is an order-2 hub,
the low-half pair count injects into it, and the high half
reflects onto the low half.  r₂(w) ≤ 2·|H| for any rep hub H of
positive material at w.  Contrapositive: a target with pair
wealth above 2·|H| refutes every candidate hub of that width —
wealth and hubs cannot share an address. -/
theorem repHub_caps_pair_wealth {A : Set ℕ} {w : ℕ}
    {H : Finset ℕ}
    (h0 : 0 ∈ A) (h0H : 0 ∉ H) (hhub : IsRepHub A w H) :
    ((Finset.range (w + 1)).filter
      (fun x => x ∈ A ∧ (w - x) ∈ A)).card ≤ 2 * H.card := by
  have hpair := pairHub_of_repHub h0 h0H hhub
  have hlow := pair_hub_pair_count hpair
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
/-- **STREETS ARE SIDON-POOR.**  Every street target — hubbed by
a window of ≤ L positive spine elements — has pair wealth at
most 2L.  The street branch of the final fork is a uniformly
poor lane: while `r2_unbounded_of_hfail` blows wealth up
cofinally and `drain_wealth_addresses` pins it 2-adically, the
enemy's street must dodge every wealthy address forever. -/
theorem street_is_sidon_poor {A : Set ℕ} {L m s J : ℕ}
    {x : ℕ → ℕ}
    (h0 : 0 ∈ A) (hx : ∀ t, 0 < x t) (hJL : J ≤ L)
    (hhub : IsRepHub A m
      ((Finset.range J).image (fun j => x (s + j)))) :
    ((Finset.range (m + 1)).filter
      (fun z => z ∈ A ∧ (m - z) ∈ A)).card ≤ 2 * L := by
  have h0H : 0 ∉ (Finset.range J).image
      (fun j => x (s + j)) := by
    rw [Finset.mem_image]
    rintro ⟨j, hj, hxj⟩
    have := hx (s + j)
    omega
  have hcap := repHub_caps_pair_wealth h0 h0H hhub
  have hcard : ((Finset.range J).image
      (fun j => x (s + j))).card ≤ L := by
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_range]
    exact hJL
  omega

open Classical in
/-- **SATURATION KILLS THE ANTIDIAGONAL.**  In a single-parity
world, a cross-system one level down with blowing-up cross-pair
wealth cannot mix its parities: antidiagonal channels (p ≠ q)
manufacture ODD wealthy targets w = 2v + 1 in root coordinates,
and the saturated odd hall caps every odd target at 2Y + 2
ordered pair representations.  A pure counting law — no hfail
hypothesis at all. -/
theorem saturated_kills_antidiagonal {A : Set ℕ} {Y ε : ℕ}
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
/-- **THE DRAIN'S FIRST MOVE IS FORCED.**  In a saturated
(single-parity) counterexample, the ω-drain cannot open with an
antidiagonal step: every valid parity pair for its first
cross-system is DIAGONAL (p = q).  The enemy's wealth must
descend along the doubled channel — the first confirmed forced
move of the descent dynamics, and the entry step of the
saturated cascade toward Cantor-like worlds. -/
theorem saturated_drain_diagonal {A : Set ℕ} {N₀ Y ε : ℕ}
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
    the_omega_drain h0 hcov hfail
  refine ⟨S, T, hS0, hT0, hstep, hblow, ?_⟩
  intro p q hp hq hS1 hT1
  rw [hS0] at hS1
  rw [hT0] at hT1
  exact saturated_kills_antidiagonal hpar hp hq hS1 hT1
    (hblow 1)

open Classical in
/-- **THE DRAIN LANDS ON THE CANONICAL HALF-WORLD.**  In a
saturated counterexample the drain's first step is not merely
diagonal: both channels are PINNED to the saturation parity ε,
so the level-1 cross-system is the single set
{x | ε + 2x ∈ A} — exactly the half-world onto which the parity
fork descends covering and mixed failure.  Wealth, covering,
and the descended interface now live on ONE set: the cascade's
three descent tracks converge at level one. -/
theorem saturated_drain_pinned {A : Set ℕ} {N₀ Y ε : ℕ}
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
    the_omega_drain h0 hcov hfail
  refine ⟨S, T, hS0, hT0, hstep, hblow, ?_⟩
  intro p q hp hq hS1 hT1
  rw [hS0] at hS1
  rw [hT0] at hT1
  have hpq := saturated_kills_antidiagonal hpar hp hq hS1 hT1
    (hblow 1)
  have hSinf : (S 1).Infinite :=
    (cross_blowup_infinite (hblow 1)).1
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
/-- **THE SATURATED CASCADE STEP** (generic, hfail-free).  At
ANY level of a cross-system descent: if the current world W is
single-parity beyond Y with parity ε and the child system's
cross-pair wealth blows up, then the child's parities are both
PINNED to ε and both channels collapse onto the canonical
half-world {x | ε + 2x ∈ W}.  Saturation determines the descent
completely, level by level — the enemy's only escape from total
determination is mixing (both parities cofinal) at some level.
Subsumes `saturated_drain_pinned`'s level-1 case. -/
theorem saturated_cascade_step {W : Set ℕ} {Y ε : ℕ}
    (hpar : ∀ a ∈ W, Y < a → a % 2 = ε)
    {S1 T1 : Set ℕ} {p q : ℕ} (hp : p < 2) (hq : q < 2)
    (hS1 : S1 = {y | 2 * y + p ∈ W})
    (hT1 : T1 = {y | 2 * y + q ∈ W})
    (hblow : ∀ C N, ∃ v, N ≤ v ∧ C ≤
      ((Finset.range (v + 1)).filter
        (fun x => x ∈ S1 ∧ (v - x) ∈ T1)).card) :
    p = ε ∧ q = ε ∧ S1 = {x : ℕ | ε + 2 * x ∈ W} ∧
      T1 = {x : ℕ | ε + 2 * x ∈ W} := by
  have hpq := saturated_kills_antidiagonal hpar hp hq hS1 hT1
    hblow
  have hSinf : S1.Infinite := (cross_blowup_infinite hblow).1
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
/-- **THE DETERMINED CASCADE.**  If saturation persists at every
level of the drain, the counterexample's wealth stream is
COMPLETELY DETERMINED: there are explicit binary digits ε' and
addresses α (partial sums of ε'ₖ2^k) such that both channels
coincide at every level and every level's world is literally the
α-cylinder slice of the root basis — S k = {x | α k + 2^k x ∈ A}.
The enemy under permanent saturation IS a 2-adic point: the
Cantor-like endpoint of the descent, formalized.  Its only
alternative is mixing at some finite level. -/
theorem saturated_cascade_determined {A : Set ℕ} {N₀ : ℕ}
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
    the_omega_drain h0 hcov hfail
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
      have hres := saturated_cascade_step (hparf 0) hp hq
        hS1 hT1 (hblow 1)
      exact ⟨heq, by omega, hres.2.2.1, hres.2.2.2⟩
    | succ k ih =>
      obtain ⟨ihEq, ihε, ihS, ihT⟩ := ih
      have heq1 : S (k + 1) = T (k + 1) := by rw [ihS, ihT]
      obtain ⟨p, q, hp, hq, hS2, hT2⟩ := hstep (k + 1)
      rw [← heq1] at hT2
      have hres := saturated_cascade_step (hparf (k + 1)) hp hq
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
/-- **THE CASCADE FORK.**  Every counterexample's drain either
stays saturated forever — and is then a fully DETERMINED 2-adic
point (explicit digits, every level a cylinder slice of A) — or
hits a FIRST MIXING LEVEL m: a world S m that is itself an
explicit cylinder slice {x | c + 2^m x ∈ A}, equal to its twin
channel, carrying blowup wealth (ambient conjunct), with BOTH
parities cofinal.  The mixed-regime entry point now has exact
coordinates: depth m, address c, and a wealth stream flowing
through it. -/
theorem cascade_mixing_fork {A : Set ℕ} {N₀ : ℕ}
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
    saturated_cascade_determined h0 hcov hfail
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
        have hres := saturated_cascade_step
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
/-- **2-ADIC CONVERGENCE KILLS COVERING.**  A set whose tail
concentrates into a single residue class mod 2^k FOR EVERY k
cannot pair-cover: pick K with 2^(K−1) beyond the mod-2 head
size; large-large sums have pinned parity, small-large sums
land in at most |head| residue classes mod 2^K, so some
wrong-parity class mod 2^K contains cofinally many uncovered
targets.  Pure counting — no hfail, no basis theory.  This is
the blade that empties the determined cascade horn. -/
theorem two_adic_convergence_kills_covering {A : Set ℕ}
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
  have h2M : 2 * M ≤ 2 ^ K * M := mul_le_mul_right' h2K M
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
/-- **THE CASCADE FORCES MIXING** (the determined horn is
EMPTY).  Permanent saturation would make the drain a fully
determined 2-adic point; then the root basis's tail would
concentrate into one residue class mod 2^k for every k, and
`two_adic_convergence_kills_covering` contradicts pair covering.
So EVERY counterexample's drain hits a first mixing level: a
twin-channel world at explicit cylinder coordinates
{x | c + 2^m x ∈ A} with BOTH parities cofinal and blowup
wealth flowing through it.  The Cantor-like endpoint is dead;
mixing is not one branch but THE regime. -/
theorem cascade_forces_mixing {A : Set ℕ} {N₀ : ℕ}
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
    saturated_cascade_determined h0 hcov hfail
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
        (cross_blowup_infinite (hblow (k + 1))).1
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
    apply two_adic_convergence_kills_covering hcov
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
        have hres := saturated_cascade_step
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
/-- **THE MIXING WORLD IS A COMPLETE SUB-INSTANCE.**  Sharpens
`cascade_forces_mixing`: the first mixing level's world not only
mixes with wealth — it PAIR-COVERS beyond a threshold (covering
descends the saturated prefix through `half_world_covers`, one
half-world at a time) and is infinite.  So every counterexample
owns a located cylinder world {x | c + 2^m x ∈ A} that is
simultaneously covering, wealthy, parity-mixing, and infinite:
a self-similar sub-instance of the whole problem, in explicit
coordinates. -/
theorem mixing_world_complete {A : Set ℕ} {N₀ : ℕ}
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
    saturated_cascade_determined h0 hcov hfail
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
        (cross_blowup_infinite (hblow (k + 1))).1
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
    apply two_adic_convergence_kills_covering hcov
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
        have hres := saturated_cascade_step
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
        have hres := saturated_cascade_step
          (hf j (by omega)) hp hq hS1 hT1 (hblow (j + 1))
        have hεlt : εf j < 2 := by
          have h1 := hres.1
          omega
        have hcovj1 := half_world_covers hεlt hNj
          (hf j (by omega))
        rw [hres.2.2.1]
        exact ⟨Nj + 2 * Yf j + 2, hcovj1⟩
    obtain ⟨heqm, hcylm⟩ := hchain m le_rfl
    refine ⟨m, α m, heqm, hcylm, ?_, ?_,
      hcovchain m le_rfl,
      (cross_blowup_infinite (hblow m)).1⟩
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

/-- **Cylinder deletions wound the root.**  Any infinite
deletion drawn from a cylinder world W = {x | c + 2^m x ∈ A}
lifts to an infinite subset of A, so the root failure interface
strikes it: the root basis minus the lifted copy fails at order
3.  The failure interface touches every mixing world through
its own address map — the entry point of the mixed-interface
descent. -/
theorem mixing_deletion_wounds_root {A : Set ℕ}
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
/-- **THE MIXING WORLD CARRIES THE INTERFACE.**  The complete
located mixing sub-instance, now with the failure interface
attached: every infinite deletion drawn from the mixing world
S m wounds the root basis at order 3 through the address map
x ↦ c + 2^m x.  Covering, wealth, mixing, infinitude, AND the
lifted failure law — the full hypothesis package of the
original problem, reproduced inside explicit cylinder
coordinates. -/
theorem mixing_world_interface {A : Set ℕ} {N₀ : ℕ}
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
    mixing_world_complete h0 hcov hfail
  exact ⟨S, T, hS0, hT0, hstep, hblow, m, c, heqm, hcylm,
    hmix0, hmix1, hcovm, hinfm,
    mixing_deletion_wounds_root hfail hcylm⟩

open Classical in
/-- **WEALTHY TARGETS SURVIVE SPARSE DELETIONS.**  If a
target's pair wealth exceeds twice the deletion's mass below it
(plus two), some pair avoids the deletion entirely and the
0-weld finishes the triple: v = x + (v−x) + 0 with all three
parts outside D.  Contrapositive — every failing target of a
deletion is PAIR-POOR relative to the deletion's local mass.
Combined with `drain_wealth_addresses`, the enemy's failure
must live strictly off its own wealth stream: the 2-adically
pinned wealthy targets can never be failing targets of any
locally-sparse deletion.  This is the lab's 268/268 survival
mechanism (probe_mixing_survival.py), formalized locally. -/
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
/-- **THE FAILURE RESIDUE LAW.**  Against a deletion confined to
one residue class mod 2^m, a failing target's EVERY pair
representation must touch that class: the 0-pad turns any
class-avoiding pair into a surviving triple.  Failure is
residue-chained to the deletion's own address. -/
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
/-- **Failing targets are poor** (tuple-form composition of
`wealthy_target_survives`).  A target failing against a
deletion avoiding 0 has pair wealth at most twice the
deletion's local mass plus two. -/
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
/-- **THE FAILURE STREAM HAS ADDRESSES.**  In the located
mixing world of any counterexample: every infinite deletion
B' ⊆ S m ∖ {0}, lifted through the address map, generates
cofinally many failing targets n, and EACH obeys two laws —
(i) the residue law: every pair representation of n touches
the class c mod 2^m, and (ii) the poverty law: n's pair wealth
is at most twice the lifted deletion's mass below n plus two.
Failure is now formally address-chained and wealth-capped,
while `drain_wealth_addresses` pins the wealth stream to its
own nested tower: the enemy must run two disjoint cofinal
streams — poor c-chained failures and rich pinned wealth —
inside one covering world, forever. -/
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
    mixing_world_interface h0 hcov hfail
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
/-- **Failing targets live in the deletion's sumset.**  A
covered target failing against a deletion avoiding 0 must have
its guaranteed pair touch the deletion itself: n ∈ D + A.  With
D chosen arbitrarily sparse, the entire failure stream is
confined to an arbitrarily thin sumset — the quantitative
companion of the residue law. -/
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
/-- **THE THREE-DELETION EXCLUSION.**  A covered target cannot
fail against three pairwise disjoint 0-free deletions at once:
its guaranteed pair (x, y, 0-pad) offers only TWO slots, and
three disjoint sets cannot all be hit by two elements.  So the
enemy's failure streams for disjoint deletions are 3-wise
disjoint beyond the covering threshold — every new disjoint
sparse deletion demands its own fresh cofinal failure stream,
pairwise-overlap at most.  The simultaneous bounded-hub demand
is load-balanced across infinitely many essentially disjoint
streams: the quantitative form of the enemy's last liberty. -/
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
/-- **THE OVERLAP BILINEAR LAW.**  A covered target failing
against TWO disjoint 0-free deletions has every pair
representation split across them — one part in each — and in
particular lies in the doubly-thin sumset D₁ + D₂.  With both
deletions log-sparse, stream overlaps are confined to a set of
(log log)²-type growth: pairwise stream overlap is nearly as
expensive as the forbidden triple overlap. -/
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
/-- **THE 2-ADIC WIDTH LAW.**  A pair-covering set's support
tree must branch: at every depth j, if all elements beyond Y
lie in infinitely-populated residue classes mod 2^j, then the
head classes HC (residues of A ∩ [0,Y]) and the wide classes
WC (infinitely-populated residues) must satisfy
2^j ≤ |HC|·|WC| + |WC|², because every residue needs cofinal
targets and every such target splits as head+wide or
wide+wide.  Generalizes `two_adic_convergence_kills_covering`
(the case |WC| = 1): a counterexample's 2-adic support width
must grow like 2^(j/2) forever, up to head mass.  No finite
union of 2-adic branches can pair-cover. -/
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
/-- **Same-class overlaps are address-pinned.**  Two disjoint
deletions drawn from ONE residue class c mod 2^j: any covered
target failing both has its address pinned to 2c mod 2^j and
lies in the doubly-sparse sumset D₁ + D₂.  Splitting one deep
class hence splits its failure duty into 3-wise-disjoint
streams whose overlaps are pinned to a single known residue —
the load ledger's first entry. -/
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
/-- **Pair hubs cap full wealth** (pair-hub form of
`repHub_caps_pair_wealth`).  An order-2 hub caps the target's
ENTIRE ordered pair count at twice its size: low half injects,
high half reflects. -/
theorem pairHub_caps_wealth {A : Set ℕ} {w : ℕ}
    {H : Finset ℕ} (hhub : IsPairHub A w H) :
    ((Finset.range (w + 1)).filter
      (fun x => x ∈ A ∧ (w - x) ∈ A)).card ≤ 2 * H.card := by
  have hlow := pair_hub_pair_count hhub
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
/-- **THE UNIVERSAL PREFIX-HUB LAW.**  In a counterexample,
EVERY infinite positive subset B of the basis manufactures its
own cofinal stream of targets at which B's prefix B ∩ [0,n] is
an order-2 hub: the 0-pad turns any B-avoiding pair into a
B-avoiding triple.  Corollary at each such target:
r₂(n) ≤ 2·|B ∩ [0,n]|.  This is the root of the exclusion
suite and the entry lemma of the load ledger — the enemy owes
every infinite positive subset of itself a cofinal
prefix-hubbed poverty stream. -/
theorem universal_prefix_hub_law {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ B ⊆ A, 0 ∉ B → B.Infinite → ∀ N, ∃ n, N ≤ n ∧
      IsPairHub A n ((Finset.range (n + 1)).filter
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
  have hhub : IsPairHub A n ((Finset.range (n + 1)).filter
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
  exact ⟨n, hn, hhub, pairHub_caps_wealth hhub⟩

open Classical in
/-- **THE UNIVERSAL COMMITTEE LAW.**  Strengthens the universal
prefix-hub law to full guardian structure, from the failure
interface ALONE (no 0-weld, no covering): every infinite subset
B of the basis owns a cofinal stream of targets each carrying a
MINIMAL order-3 guardian committee drawn from B itself — and by
minimality, every committee member holds a private witness
representation meeting the committee only at that member.  The
entire guardian/team machinery, originally mined on A, now
fires inside every infinite subset of A: the enemy's defense
obligations are hereditary. -/
theorem universal_committee_law {A : Set ℕ}
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ B ⊆ A, B.Infinite → ∀ N, ∃ n, N ≤ n ∧
      ∃ H ⊆ (Finset.range (n + 1)).filter (fun x => x ∈ B),
        IsRepHub A n H ∧
        (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
        ∀ h ∈ H, ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = n ∧
          (x = h ∨ y = h ∨ z = h) ∧
          ∀ g ∈ H, g ≠ h → x ≠ g ∧ y ≠ g ∧ z ≠ g := by
  intro B hBA hBinf N
  have hnot := hfail B hBA hBinf
  simp only [IsExactTupleAsymptoticBasis, not_exists,
    not_forall] at hnot
  obtain ⟨n, hn, hnrep⟩ := hnot N
  have hprefix : IsRepHub A n ((Finset.range (n + 1)).filter
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
  obtain ⟨H, hHsub, hHhub, hHmin⟩ := exists_minimal_hub hprefix
  exact ⟨n, hn, H, hHsub, hHhub, hHmin,
    minimal_hub_necessity hHhub hHmin⟩

open Classical in
/-- **THE COMMITTEE SIZE FLOOR.**  In anchored counterexample
worlds, the hereditary committees are never lone guardians:
for every infinite positive subset B, cofinally many targets
carry minimal committees from B of size AT LEAST TWO — empty
committees die on covering, singleton committees feed the
private-triple stream and the rotating-guardian engine kills
through the oracle.  Every subset the deleter proposes is
defended by genuine TEAMS, with every member holding a private
witness: the team machinery is hereditary with its floor
intact. -/
theorem committee_size_floor {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ B ⊆ A, (∀ b ∈ B, 0 < b) → B.Infinite →
      ∀ N, ∃ n, N ≤ n ∧
      ∃ H ⊆ (Finset.range (n + 1)).filter (fun x => x ∈ B),
        2 ≤ H.card ∧ IsRepHub A n H ∧
        (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
        ∀ h ∈ H, ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = n ∧
          (x = h ∨ y = h ∨ z = h) ∧
          ∀ g ∈ H, g ≠ h → x ≠ g ∧ y ≠ g ∧ z ≠ g := by
  intro B hBA hBpos hBinf N
  have hnosing := singleton_hubs_refuted h0 hcov hanchor hfail
  push Not at hnosing
  obtain ⟨N₁, hN₁⟩ := hnosing
  obtain ⟨n, hn, H, hHsub, hHhub, hHmin, hHwit⟩ :=
    universal_committee_law hfail B hBA hBinf
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
/-- **THE ROUTER ROOM'S DOUBLES ARE UNIFORMLY POOR.**  In the
g₀-routed geometry every noncentral double 2c is pair-hubbed by
the two-element set {c, g₀}, so its ENTIRE pair count is capped
at four.  Meanwhile `r2_unbounded_of_hfail` blows pair wealth
up cofinally: in room II the wealthy targets must dodge every
noncentral double of the basis forever — wealth lives only on
odd targets, central doubles 2g₀, and non-doubles.  The router
buys total routing at the price of total double-poverty. -/
theorem router_room_doubles_poor {A : Set ℕ} {g₀ : ℕ}
    (hroute : ∀ c ∈ A, 0 < c → c ≠ g₀ →
      IsPairHub A (2 * c) ({c, g₀} : Finset ℕ)) :
    ∀ c ∈ A, 0 < c → c ≠ g₀ →
      ((Finset.range (2 * c + 1)).filter
        (fun x => x ∈ A ∧ (2 * c - x) ∈ A)).card ≤ 4 := by
  intro c hc hpos hne
  have hcap := pairHub_caps_wealth (hroute c hc hpos hne)
  have hcard : ({c, g₀} : Finset ℕ).card ≤ 2 := by
    refine le_trans (Finset.card_insert_le c {g₀}) ?_
    rw [Finset.card_singleton]
  omega

open Classical in
/-- **ROOM II'S WEALTH DODGES ITS OWN DOUBLES.**  In the
g₀-routed geometry, unbounded pair wealth
(`r2_unbounded_of_hfail`) collides with uniform double-poverty
(`router_room_doubles_poor`): beyond every bound there are
targets of pair count ≥ 5, and none of them can be a
noncentral double of the basis.  The router room's riches are
permanently confined to odd targets, the central double, and
non-doubles — while every noncentral double sits at pair count
≤ 4 forever. -/
theorem router_room_wealth_dodges_doubles {A : Set ℕ}
    {N₀ g₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hroute : ∀ c ∈ A, 0 < c → c ≠ g₀ →
      IsPairHub A (2 * c) ({c, g₀} : Finset ℕ)) :
    ∀ N, ∃ w, N ≤ w ∧ 5 ≤
      ((Finset.range (w + 1)).filter
        (fun x => x ∈ A ∧ (w - x) ∈ A)).card ∧
      ∀ c ∈ A, 0 < c → c ≠ g₀ → w ≠ 2 * c := by
  intro N
  obtain ⟨w, hwN, hwC⟩ :=
    r2_unbounded_of_hfail h0 hcov hfail 5 N
  refine ⟨w, hwN, hwC, ?_⟩
  intro c hc hpos hne heq
  have hpoor := router_room_doubles_poor hroute c hc hpos hne
  rw [heq] at hwC
  omega

open Classical in
/-- **THE BAND TAX.**  If some subset B (positive material)
supplies bounded-width committees cofinally — width ≤ C — then
those committee targets form a cofinal family of UNIFORMLY POOR
targets: r₂ ≤ 2C on the whole stream, by the 0-weld and the
pair-hub wealth cap.  Holding the committee width in a bounded
band anywhere in the subset lattice forces a poor street there;
the band and the wealth stream can never share targets.  The
width-band question's bounded horn pays this tax against
`r2_unbounded_of_hfail` and `drain_wealth_addresses` at every
single subset. -/
theorem committee_band_tax {A B : Set ℕ} {C : ℕ}
    (h0 : 0 ∈ A) (hBpos : ∀ b ∈ B, 0 < b)
    (hfam : ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧
      (∀ x ∈ H, x ∈ B) ∧ IsRepHub A n H) :
    ∀ N, ∃ n, N ≤ n ∧
      ((Finset.range (n + 1)).filter
        (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ 2 * C := by
  intro N
  obtain ⟨n, hn, H, hc, hHB, hhub⟩ := hfam N
  have h0H : 0 ∉ H := by
    intro h
    have := hBpos 0 (hHB 0 h)
    omega
  have hcap := repHub_caps_pair_wealth h0 h0H hhub
  exact ⟨n, hn, by omega⟩

open Classical in
/-- **COMMITTEE TRANSLATE FREENESS.**  A minimal committee's
sub-committees are powerless on the translate fan: for every
member h, the committee minus h does NOT pair-hub the translate
n − h — h's private witness donates a pair of n − h avoiding
all other members.  Minimal committees thus carry
pair-freeness certificates for every one of their
cardinality-(K−1) sub-committees: the escalating horn of the
width band manufactures FREENESS material at scale, feeding
the rank room rather than escaping it. -/
theorem committee_translate_freeness {A : Set ℕ} {n : ℕ}
    {H : Finset ℕ}
    (hhub : IsRepHub A n H)
    (hmin : ∀ h ∈ H, ¬IsRepHub A n (H \ {h})) :
    ∀ h ∈ H, ¬IsPairHub A (n - h) (H \ {h}) := by
  intro h hhH hpair
  obtain ⟨x, hx, y, hy, z, hz, hsum, hmem, havoid⟩ :=
    minimal_hub_necessity hhub hmin h hhH
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
/-- **THE WIDTH BAND** (capstone of the committee program).
In anchored counterexample worlds, every infinite positive
subset B runs one of exactly two regimes:

BOUNDED BAND — some width C works cofinally, and then every
such committee target is simultaneously POOR (r₂ ≤ 2C,
pointwise, by the 0-weld cap): a hereditary poor street,
segregated forever from the unbounded pinned wealth stream; or

ESCALATION — beyond every width C, cofinal targets carry
minimal committees from B WIDER than C, every member privately
witnessed, and every sub-committee formally unable to pair-hub
its member's translate: freeness-certificate towers of
unbounded width.

Erdős 881's residue, stated as one verified fork. -/
theorem endgame_width_band_local {A B : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B' ⊆ A, B'.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B') 3)
    (hBA : B ⊆ A) (hBpos : ∀ b ∈ B, 0 < b)
    (hBinf : B.Infinite) :
    (∃ C, ∀ N, ∃ n, N ≤ n ∧
      (∃ H ⊆ (Finset.range (n + 1)).filter (fun x => x ∈ B),
        H.card ≤ C ∧ 2 ≤ H.card ∧ IsRepHub A n H ∧
        (∀ h ∈ H, ¬IsRepHub A n (H \ {h}))) ∧
      ((Finset.range (n + 1)).filter
        (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ 2 * C) ∨
    (∀ C N, ∃ n, N ≤ n ∧
      ∃ H ⊆ (Finset.range (n + 1)).filter (fun x => x ∈ B),
        C < H.card ∧ IsRepHub A n H ∧
        (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
        (∀ h ∈ H, ¬IsPairHub A (n - h) (H \ {h})) ∧
        ∀ h ∈ H, ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = n ∧
          (x = h ∨ y = h ∨ z = h) ∧
          ∀ g ∈ H, g ≠ h → x ≠ g ∧ y ≠ g ∧ z ≠ g) := by
  by_cases hb : ∃ C, ∀ N, ∃ n, N ≤ n ∧
      ∃ H ⊆ (Finset.range (n + 1)).filter (fun x => x ∈ B),
        H.card ≤ C ∧ 2 ≤ H.card ∧ IsRepHub A n H ∧
        (∀ h ∈ H, ¬IsRepHub A n (H \ {h}))
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
    have hcap := repHub_caps_pair_wealth h0 h0H hHhub
    exact ⟨n, hn, ⟨H, hHsub, hHc, hH2, hHhub, hHmin⟩,
      by omega⟩
  · right
    push Not at hb
    intro C N
    obtain ⟨N₁, hN₁⟩ := hb C
    obtain ⟨n, hn, H, hHsub, hH2, hHhub, hHmin, hHwit⟩ :=
      committee_size_floor h0 hcov hanchor hfail B hBA hBpos
        hBinf (max N N₁)
    have hwide : C < H.card := by
      rcases Nat.lt_or_ge C H.card with h | h
      · exact h
      · exfalso
        obtain ⟨h', hh'H, hh'hub⟩ :=
          hN₁ n (by omega) H hHsub h hH2 hHhub
        exact hHmin h' hh'H hh'hub
    exact ⟨n, by omega, H, hHsub, hwide, hHhub, hHmin,
      committee_translate_freeness hHhub hHmin, hHwit⟩

open Classical in
/-- **Cylinder committees chain and cap.**  A committee of
positive material from one residue class mod 2^m does both
things to its target at once: every pair representation of n
must touch the class (0-weld + hub), and n's entire pair
wealth is capped at twice the committee size.  The workhorse
for the same-set collision: when the width band's bounded horn
runs inside the drain's own cylinder material, its poor street
is simultaneously residue-chained to the tower's address. -/
theorem cylinder_committee_chains {A : Set ℕ}
    {m c n : ℕ} {H : Finset ℕ}
    (h0 : 0 ∈ A)
    (hHcyl : ∀ x ∈ H, x % 2 ^ m = c % 2 ^ m ∧ 0 < x)
    (hhub : IsRepHub A n H) :
    (∀ x ∈ A, ∀ y ∈ A, x + y = n →
      x % 2 ^ m = c % 2 ^ m ∨ y % 2 ^ m = c % 2 ^ m) ∧
    ((Finset.range (n + 1)).filter
      (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ 2 * H.card := by
  have h0H : 0 ∉ H := by
    intro h
    have := (hHcyl 0 h).2
    omega
  have hpair := pairHub_of_repHub h0 h0H hhub
  constructor
  · intro x hx y hy hxy
    rcases hpair x hx y hy hxy with h | h
    · exact Or.inl (hHcyl x h).1
    · exact Or.inr (hHcyl y h).1
  · exact repHub_caps_pair_wealth h0 h0H hhub

open Classical in
/-- **THE POOR STREAM IS UNCONDITIONAL.**  Every counterexample
keeps a cofinal stream of targets with BOUNDED pair wealth:
liminf r₂ < ∞.  Proof by diagonal against the growth rate — if
r₂ → ∞, build a deletion D sparser than the growth (spacing its
i-th element beyond the threshold where r₂ exceeds 2i + 4);
its failing targets would need r₂ ≤ 2·|D∩[0,n]| + 2, which the
running minimum forbids, so D would survive.  Fat sets fail
this conclusion (their r₂ → ∞): genuine counting content, from
h0 + covering + hfail alone. -/
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
/-- **The poor stream's canonical hubs.**  Each bounded-wealth
target carries its COMPLETE low-part set as a canonical pair
hub: card ≤ L, every member a genuine low part, and — unlike
the flood's envelope hubs — COMPLETE: every low part of n
belongs to it.  Cofinal complete bounded pair hubs, from the
oscillation theorem alone.  Completeness is the extra the
envelope supply never had: rigidity and uniqueness arguments
downstream consume exactly this. -/
theorem poor_stream_canonical_hubs {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ L, ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      H.card ≤ L ∧ IsPairHub A n H ∧
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
/-- **Pair-hub window split** (free via the vacuous-world
trick: `hub_window_split_aux'` never unfolds rep-hubness, so
instantiating its world at ∅ makes that slot trivial and the
side-predicate slot carries pair-hubness).  Any cofinal
bounded-card pair-hub family splits at every window into a
persistent core plus tails beyond the window. -/
theorem pair_hub_window_split {A : Set ℕ} {C : ℕ} (W : ℕ)
    (R : ℕ → Finset ℕ → Prop)
    (hfam : ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧
      IsPairHub A n H ∧ R n H) :
    ∃ S : Finset ℕ, S ⊆ Finset.range (W + 1) ∧
      ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧
        IsPairHub A n H ∧ R n H ∧ S ⊆ H ∧
        ∀ h ∈ H, h ∉ S → W < h := by
  have hvac : ∀ (n : ℕ) (H : Finset ℕ),
      IsRepHub (∅ : Set ℕ) n H := by
    intro n H x hx
    exact absurd hx (Set.notMem_empty x)
  obtain ⟨S, hSW, hS⟩ := hub_window_split_aux'
    (A := (∅ : Set ℕ)) (C := C)
    (R := fun n H => IsPairHub A n H ∧ R n H) W C ∅
    (by simp)
    (fun N => by
      obtain ⟨n, hn, H, hcard, hpair, hR⟩ := hfam N
      exact ⟨n, hn, H, hcard, hvac n H, ⟨hpair, hR⟩,
        Finset.empty_subset _, by simpa using hcard⟩)
  refine ⟨S, hSW, fun N => ?_⟩
  obtain ⟨n, hn, H, hcard, -, ⟨hpair, hR⟩, hSH, htail⟩ := hS N
  exact ⟨n, hn, H, hcard, hpair, hR, hSH, htail⟩

open Classical in
/-- **THE CANONICAL CORE.**  Composing the oscillation
theorem's canonical hubs with the pair-hub window split: every
counterexample has a bound L such that at EVERY window W there
is a persistent core S of low-part material — recurring inside
the COMPLETE canonical hubs of cofinally many poor targets,
with every non-core member beyond the window.  The poor
stream's low material organizes into stable cores plus
marching tails, unconditionally. -/
theorem canonical_core_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ L, ∀ W, ∃ S : Finset ℕ, S ⊆ Finset.range (W + 1) ∧
      ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ L ∧
        IsPairHub A n H ∧
        (∀ h ∈ H, h ∈ A ∧ (n - h) ∈ A ∧ 2 * h ≤ n) ∧
        (∀ x, 2 * x ≤ n → x ∈ A → (n - x) ∈ A → x ∈ H) ∧
        S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h := by
  obtain ⟨L, hL⟩ := poor_stream_canonical_hubs h0 hcov hfail
  refine ⟨L, fun W => ?_⟩
  obtain ⟨S, hSW, hS⟩ := pair_hub_window_split W
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
/-- **THE DRIFT FORK.**  The canonical core organizes into a
clean dichotomy: either some FIXED u is a universal low part —
belonging to the complete canonical hubs of cofinally many
poor targets (the door configuration at a known member) — or
the poor stream's ENTIRE low material drifts: beyond every
window, cofinally many poor targets have every single low part
larger than the window.  Unconditional, from the oscillation
layer alone. -/
theorem poor_drift_fork {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ L,
    (∃ u, ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ L ∧
      IsPairHub A n H ∧
      (∀ h ∈ H, h ∈ A ∧ (n - h) ∈ A ∧ 2 * h ≤ n) ∧
      (∀ x, 2 * x ≤ n → x ∈ A → (n - x) ∈ A → x ∈ H) ∧
      u ∈ H) ∨
    (∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ L ∧
      IsPairHub A n H ∧
      (∀ h ∈ H, h ∈ A ∧ (n - h) ∈ A ∧ 2 * h ≤ n) ∧
      (∀ x, 2 * x ≤ n → x ∈ A → (n - x) ∈ A → x ∈ H) ∧
      ∀ h ∈ H, W < h) := by
  obtain ⟨L, hL⟩ := canonical_core_of_hfail h0 hcov hfail
  refine ⟨L, ?_⟩
  by_cases hu : ∃ u, ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      H.card ≤ L ∧ IsPairHub A n H ∧
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
/-- **THE DRIFT HORN DIGS DESERTS.**  On the total-drift horn
of the drift fork, the poor stream's targets sit in translate
deserts: for every window W, cofinally many poor targets n
have n − x ∉ A for EVERY basis element x ∈ [1, W] (with
2x ≤ n) — because the complete canonical hub contains all low
parts and all its members exceed W.  The R4 street ladder's
difference-desert geometry, now derived UNCONDITIONALLY on the
drift horn: the enemy's small elements are simultaneously
useless for an entire cofinal target family. -/
theorem drift_horn_deserts {A : Set ℕ} {L : ℕ}
    (hdrift : ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      H.card ≤ L ∧ IsPairHub A n H ∧
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
  · have hcap := pairHub_caps_wealth hpair
    omega
  · intro x hxA hx1 hxW hxle hnxA
    have hxH : x ∈ H := hcomp x hxle hxA hnxA
    have := htail x hxH
    omega

open Classical in
/-- **SMALL-LOW-PART RIGIDITY.**  At every scale W there is ONE
fixed set S ⊆ [0, W] such that cofinally many poor targets have
EXACTLY S as their small low parts: x ≤ W is a low part of n if
and only if x ∈ S.  The enemy's small pair-service pattern is
frozen on a cofinal stream at every window — completeness turns
the canonical core's containment into an equality.  Forced
membership in both directions, unconditionally. -/
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
  have hcap := pairHub_caps_wealth hpair
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
/-- **THE RIGIDITY TRICHOTOMY.**  The frozen small-low-part
pattern admits exactly three shapes, so every counterexample
unconditionally runs one of three explicit geometries:
(1) FIXED DIFFERENCE — some d ≥ 1 with a, a + d ∈ A beyond
every bound (the translation room's team supply, unlocked);
(2) DOORED DESERT — one u serving a cofinal poor stream as its
ONLY small low part up to some window: a pure door with a
desert moat;
(3) TOTAL DESERT — beyond every window, cofinal poor targets
with no small low parts at all.
R1, the door, and R4: the campaign's oldest room names, now
forced from the bare interface by the oscillation layer. -/
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

/-- Cofinal δ-paired supply yields δ-paired finite families of
every size — the bridge from the rigidity trichotomy's fixed-
difference horn to the translation room's team machinery. -/
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
/-- **THE RIGIDITY TRICHOTOMY WITH TEAMS.**  In anchored
worlds the fixed-difference horn upgrades from bare supply to
TRANSLATION-COHERENT TEAMS: cofinally many targets carry
minimal committees of size ≥ 2 whose EVERY member is δ-paired
in the basis (h, h + d ∈ A).  Every counterexample runs
δ-coherent teams, a doored desert, or a total desert. -/
theorem rigidity_trichotomy_teams {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∃ d, 1 ≤ d ∧ ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      IsRepHub A n H ∧ (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
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
    have hteams := translation_room_teams h0 hcov hanchor
      hfail (fixed_difference_families hsup)
    intro N
    obtain ⟨n, hn, H, hhub, hmin, hcard, hmem⟩ := hteams N
    exact ⟨n, hn, H, hhub, hmin, hcard, hmem⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

open Classical in
/-- **THE DISJOINT-MATCHING DODGE** (step two of the steering
kill plan).  A target stream carrying two pair representations
each, with pairwise-disjoint vertex sets across the stream, can
always be dodged: choose one vertex from every second target's
matching as the deletion — it is infinite basis material, yet
every stream target keeps a representation pair completely
outside it.  Pairwise-disjoint matchings are non-steering:
no such stream can serve as a failing family.  The enemy's
failing streams are FORCED to share matching vertices — and a
fixed shared vertex is eventually a LOW part of later targets,
returning all distant sharing to the rigidity trichotomy's
jurisdiction. -/
theorem disjoint_matching_dodge {A : Set ℕ} {nseq x₁ x₂ : ℕ → ℕ}
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
/-- **Wealthy targets keep a clean pair** (pair-form of
`wealthy_target_survives`; no zero hypotheses needed).  If a
target's pair wealth exceeds twice the deletion's local mass
plus two, some pair avoids the deletion entirely. -/
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
/-- **THE FAN POVERTY LAW.**  A target failing at order 3
against a deletion has its ENTIRE non-deleted translate fan
uniformly poor: for every x ∈ A ∖ D below n, the translate
n − x has pair wealth at most twice the deletion's mass below
n plus two — else a clean pair of n − x completes a surviving
triple through x.  One failing target taxes the wealth of
|A ∖ D| ∩ [0,n] many translates at once: failure is no longer
a local event but a blanket poverty requirement across the
fan, and the fan must avoid the entire wealth stream. -/
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
/-- **THE REFLECTED EMBEDDING COUNT.**  A failing target's fan
injects into the poor set: below any target failing at order 3
against D, the number of (2·|D∩[0,n]|+2)-poor targets is at
least the number of non-deleted basis elements — the map
x ↦ n − x embeds A ∖ D into the poor population.  A
counterexample's poor targets must be AS NUMEROUS AS ITS OWN
ELEMENTS below every failing target: in fat worlds (positive-
density bases) failure forces positive-density near-Sidon
target populations; in thin worlds this is the √n-scale
bookkeeping.  The fat-regime program's counting core. -/
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
/-- **THE DENSITY LAW.**  At every order-3 failing target the
counting closes into one global inequality: with α = |A∩[0,n]|,
α₂ = |A∩[0,n/2]|, DF = |D∩[0,n]|, C = 2·DF+2, and P the number
of C-poor targets below n,

    α − DF ≤ P   and   α₂² + P·(α − C) ≤ (n+1)·α.

Lower bound: the reflected embedding.  Upper: the energy
Σ r₂ ≥ α₂² (pairs of low halves) against the poor/rich
partition (poor contribute ≤ C, the rest ≤ α each).  First
consequence: a set containing [0,n] can never have a failing
target (α₂² + α² ≈ 1.25·n² > n² ≈ (n+1)·α) — dense bases fail
nothing, quantitatively.  The campaign's first global
inequality binding density profiles at every failing
target of every deletion. -/
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
/-- **THE MASTER LAW.**  One statement carrying the
unconditional layer: every counterexample simultaneously
(I) OSCILLATES — bounded-wealth targets cofinally, unbounded
wealth cofinally; (II) runs one of the three RIGIDITY
geometries — fixed difference, doored desert, or total
desert; and (III) pays the DENSITY LAW at cofinally many
failing targets of EVERY infinite positive deletion: the poor
population exceeds the surviving basis count, and the energy
inequality α₂² + P·(α−C) ≤ (n+1)·α binds.  From 0 ∈ A,
covering, and the failure interface alone. -/
theorem the_master_law {A : Set ℕ} {N₀ : ℕ}
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
/-- **Failing targets avoid wealthy translates.**  If w is
wealthy beyond the deletion cap and w ≤ n, then a failing
target n cannot reach w through surviving basis material:
n − w is outside A or inside D.  The failing stream must
thread the complement of w + (A ∖ D) for EVERY sufficiently
wealthy w simultaneously — each wealthy target erects one more
corridor wall. -/
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
/-- **Served targets never fail.**  One wealthy server —
w ≤ n wealthy beyond the deletion cap with n − w surviving in
the basis — is enough to save n: the server's own clean pair
plus the surviving translate part make a surviving triple.
Contrapositive of the wealthy-translate wall, stated as the
survival criterion of the completeness reduction. -/
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
/-- **THE SERVICE BREAKDOWN LAW.**  Every counterexample must
break sumset completeness against every deletion: for each
infinite B ⊆ A there are cofinally many targets n at which
EVERY wealthy target w ≤ n (wealth above the deletion cap) has
a dead translate — n − w outside the basis or deleted.  The
completeness reduction in theorem form: Erdős 881 (k = 2) is
exactly the impossibility of running this total breakdown
forever against all deletions at once, and every lab world
ever built fails to run it against a single one. -/
theorem service_breakdown_of_hfail {A : Set ℕ} {N₀ : ℕ}
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
/-- **The pair-energy lower bound** (pure counting, no failure
hypothesis).  For any set: α₂⁴ ≤ (n+1)·Σ r₂(m)², by the
low-half pair injection and Cauchy–Schwarz.  In corridor
worlds this forces wealthy square-mass: with the poor
partition, a world whose α₂ beats √n must carry polynomially
many wealthy targets — each of which erects a translate wall
against every failing stream.  The corridor program's counting
engine. -/
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
/-- **The wealthy count bound** (pure counting).  Splitting the
energy between C-poor targets (≤ C² each) and wealthy ones
(≤ α² each): α₂⁴ ≤ (n+1)·((n+1)·C² + W·α²), where W counts the
wealthy targets below n.  In any world whose low half beats
√n·C-scale, wealth is forced in QUANTITY, not merely
cofinally — and every wealthy target is a wall against every
failing stream.  The corridor profile inequality, formal. -/
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
/-- **Covering √-growth** (standalone).  A pair-covering set
has |A ∩ [0,X]|² ≥ X − N₀ at every scale: each covered target
donates a pair of elements below it, and the sum recovers the
target, so the map is injective.  The floor that every profile
analysis of the corridor stands on. -/
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
/-- **THE ENERGY BRIDGE.**  The campaign's windowed second
moment embeds into Mathlib's additive energy: the window sum
Σ_{m ≤ n} r₂(m)² is at most E[Af, Af] for Af = A ∩ [0,n] —
each window fiber is exactly a sumset fiber, and the sumset
carries more.  This connects the entire bespoke counting suite
to `Mathlib.Combinatorics.Additive` (energy, Plünnecke–Ruzsa,
Ruzsa covering, doubling): the classical arsenal now points at
the corridor. -/
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
/-- **The Mathlib energy floor.**  α⁴ ≤ (2n+1)·E[Af, Af] —
directly from `le_card_add_mul_addEnergy` and the sumset
living inside [0, 2n].  Sharper than the hand-built engine
(α, not α₂), and stated in the classical library's own
vocabulary: covering worlds have near-maximal additive energy
demands at every scale. -/
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
/-- **The upper-half energy floor** (cascade entry).  The
Mathlib energy floor with the energy split at the window
boundary: α⁴ ≤ (2n+1)·(windowΣ + upperΣ), where windowΣ is the
campaign's windowed second moment on [0,n] and upperΣ is the
sumset energy above n.  Whenever the window's second moment is
capped (poor-dense regimes), the demand transfers to the upper
half — which is the next scale's window: the energy cascade's
first rung, formal. -/
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

end Erdos881
