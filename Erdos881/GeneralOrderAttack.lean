import Erdos881.InternalAnchorOrderTwo
import Erdos881.GeneralOrder
import Erdos881.CertificateAmplification

/-!
# General-order moving-transversal attack

This module retains the cardinal information in the bounded
successor-transversal branch and develops the first order-uniform incidence
step.

For order two, swapping an external anchor with a hit in a predecessor pair
produces a large pair star.  The same swap works at every positive order:
remove one occurrence of the hit from the predecessor tuple and insert the
external anchor.  The resulting support has the same order and represents the
common translated target.

Consequently, a bounded order-`k+1` successor destroyer which is tested
against sufficiently many external basis elements forces arbitrarily many
order-`k` supports at one target.  No matching property is used here; the
next step is to apply bounded-rank matching/sunflower descent to the large
support family.
-/

open scoped BigOperators

namespace Erdos881

/-- Failure of exact order `h` is exactly cofinal emptiness of its finite
support families. -/
theorem not_exactTupleAsymptoticBasis_iff_cofinal_emptySupport
    {A : Set ℕ} {h : ℕ} :
    ¬ IsExactTupleAsymptoticBasis A h ↔
      ∀ N, ∃ n, N ≤ n ∧ additiveSupportFamily A h n = ∅ := by
  constructor
  · intro hnot N
    by_contra hnone
    push Not at hnone
    apply hnot
    apply hasEventuallySurvivingSupport_empty_additive_iff.mp
    refine ⟨N, ?_⟩
    intro n hn
    have hnonempty :
        (additiveSupportFamily A h n).Nonempty := by
      simpa [Finset.nonempty_iff_ne_empty] using hnone n hn
    obtain ⟨E, hER⟩ := hnonempty
    exact ⟨E, hER, by simp⟩
  · intro hgap hbasis
    obtain ⟨N, hN⟩ :=
      hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
    obtain ⟨n, hn, hempty⟩ := hgap N
    obtain ⟨E, hER, _⟩ := hN n hn
    rw [hempty] at hER
    simp at hER

/-- If every infinite subset of `A` fails as a deletion at exact order `h`,
then the order-`h` additive support family satisfies strong infinite
deletion.  This is the order-uniform version of the order-three
counterexample bridge. -/
theorem strongExactDeletion_of_counterexample
    {A : Set ℕ} {h : ℕ}
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) h) :
    StrongInfiniteDeletion (additiveSupportFamily A h) A := by
  rw [strongInfiniteDeletion_additiveSupportFamily_iff]
  intro B hBA hB N
  have hnot := hcounter B hBA hB
  simp only [IsExactTupleAsymptoticBasis, not_exists, not_forall] at hnot
  obtain ⟨n, hn, hnrep⟩ := hnot N
  refine ⟨n, hn, ?_⟩
  rintro ⟨v, hv⟩
  exact hnrep v hv

/-- Above any fixed basis element, the predecessor gaps of a primitive
order-`k+1` basis have cofinally many represented one-summand extensions.
These are exactly the targets to which the gap descent can be applied. -/
theorem cofinal_representedExtensions_of_lowerOrderGaps
    {A : Set ℕ} {k b : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hnotLower : ¬ IsExactTupleAsymptoticBasis A k)
    (_hbA : b ∈ A) :
    ∀ L, ∃ d q,
      L ≤ d ∧ q = d + b ∧
      (additiveSupportFamily A (k + 1) q).Nonempty ∧
      additiveSupportFamily A k d = ∅ := by
  obtain ⟨N, hN⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  have hgap :=
    not_exactTupleAsymptoticBasis_iff_cofinal_emptySupport.mp hnotLower
  intro L
  obtain ⟨d, hdLower, hdGap⟩ := hgap (max L N)
  have hLd : L ≤ d :=
    le_trans (le_max_left L N) hdLower
  have hNd : N ≤ d :=
    le_trans (le_max_right L N) hdLower
  obtain ⟨E, hER, _⟩ :=
    hN (d + b) (hNd.trans (Nat.le_add_right d b))
  exact ⟨d, d + b, hLd, rfl, ⟨E, hER⟩, hdGap⟩

/-- Strong minimality descends to every lower order at which the same set is
already an exact basis.  Indeed, if an infinite deletion were still a basis
at the lower order, order monotonicity would make it a basis at the original
order as well. -/
theorem IsStronglyMinimalExactBasis.descend_to_exactOrder
    {A : Set ℕ} {h k : ℕ}
    (hminimal : IsStronglyMinimalExactBasis A k)
    (hle : h ≤ k)
    (hbasis : IsExactTupleAsymptoticBasis A h) :
    IsStronglyMinimalExactBasis A h := by
  refine ⟨hbasis, ?_⟩
  rw [strongInfiniteDeletion_additiveSupportFamily_iff]
  intro B hBA hBinf N
  by_contra hnone
  push Not at hnone
  have hlowerDeletion :
      IsExactTupleAsymptoticBasis (A \ B) h :=
    ⟨N, fun n hn => hnone n hn⟩
  have hupperDeletion :
      IsExactTupleAsymptoticBasis (A \ B) k :=
    hlowerDeletion.of_le hle
  obtain ⟨K, hK⟩ := hupperDeletion
  obtain ⟨n, hn, hdestroy⟩ :=
    hminimal.2 B hBA hBinf (max N K)
  obtain ⟨v, hvAB, hvsum⟩ :=
    hK n (le_trans (le_max_right N K) hn)
  exact (destroysAt_additiveSupportFamily_iff.mp hdestroy)
    ⟨v, hvAB, hvsum⟩

/-- Every exact basis has a least positive exact order, and strong minimality
at any larger order descends to that least order.  The predecessor order is
then genuinely non-basis, supplying arbitrarily late lower-rank gaps. -/
theorem IsStronglyMinimalExactBasis.exists_leastStrongOrder
    {A : Set ℕ} {k : ℕ}
    (hminimal : IsStronglyMinimalExactBasis A k) :
    ∃ h, 1 ≤ h ∧ h ≤ k ∧
      IsStronglyMinimalExactBasis A h ∧
      ¬ IsExactTupleAsymptoticBasis A (h - 1) := by
  classical
  let ExistsOrder : ∃ h, IsExactTupleAsymptoticBasis A h :=
    ⟨k, hminimal.1⟩
  let h := Nat.find ExistsOrder
  have hhBasis : IsExactTupleAsymptoticBasis A h :=
    Nat.find_spec ExistsOrder
  have hhPos : 1 ≤ h := by
    by_contra hh
    have hhzero : h = 0 := by omega
    have hzeroBasis : IsExactTupleAsymptoticBasis A 0 := by
      simpa [hhzero] using hhBasis
    obtain ⟨N, hN⟩ := hzeroBasis
    obtain ⟨v, _hvA, hvsum⟩ := hN (N + 1) (by omega)
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hvsum
    omega
  have hhLe : h ≤ k :=
    Nat.find_min' ExistsOrder hminimal.1
  have hpredLt : h - 1 < h := by omega
  have hpredNot :
      ¬ IsExactTupleAsymptoticBasis A (h - 1) :=
    Nat.find_min ExistsOrder hpredLt
  exact ⟨h, hhPos, hhLe,
    hminimal.descend_to_exactOrder hhLe hhBasis, hpredNot⟩

/-- In the genuine hard case, the least exact order is at least three.
Consequently it is enough to attack strongly minimal bases whose exact order
is primitive: order `h` works but order `h-1` does not. -/
theorem IsStronglyMinimalExactBasis.exists_primitiveHardOrder
    {A : Set ℕ} {k : ℕ}
    (hminimal : IsStronglyMinimalExactBasis A k)
    (hnotTwo : ¬ IsExactTupleAsymptoticBasis A 2) :
    ∃ h, 3 ≤ h ∧ h ≤ k ∧
      IsStronglyMinimalExactBasis A h ∧
      ¬ IsExactTupleAsymptoticBasis A (h - 1) := by
  obtain ⟨h, hhPos, hhLe, hhMinimal, hpredNot⟩ :=
    hminimal.exists_leastStrongOrder
  have hhThree : 3 ≤ h := by
    by_contra hh
    have hhTwo : h ≤ 2 := by omega
    exact hnotTwo (hhMinimal.1.of_le hhTwo)
  exact ⟨h, hhThree, hhLe, hhMinimal, hpredNot⟩

/-- It is enough to solve the primitive hard orders.  If a strongly minimal
order-`k` basis is not already an order-two basis, descend to its least exact
order `h`.  A deletion which survives at order `h+1` also survives at the
originally requested order `k+1` by order monotonicity. -/
theorem erdos881_general_of_primitiveHardCase
    (hprimitive :
      ∀ h, 3 ≤ h → ∀ A : Set ℕ,
        IsStronglyMinimalExactBasis A h →
        ¬ IsExactTupleAsymptoticBasis A (h - 1) →
        ∃ B, B ⊆ A ∧ B.Infinite ∧
          IsExactTupleAsymptoticBasis (A \ B) (h + 1)) :
    ∀ k, Erdos881At k := by
  apply erdos881_general_of_hardCase
  intro k hk A hminimal hnotTwo
  obtain ⟨h, hhThree, hhLe, hhMinimal, hpredNot⟩ :=
    hminimal.exists_primitiveHardOrder hnotTwo
  obtain ⟨B, hBA, hBinf, hsurvive⟩ :=
    hprimitive h hhThree A hhMinimal hpredNot
  refine ⟨B, hBA, hBinf, hsurvive.of_le ?_⟩
  omega

/-- Cross-anchor descent.  Suppose `T` destroys every order-`k+1`
representation of `q+a`.  Replacing the anchor `a` by a smaller external
basis element `b` turns every order-`k` representation of `q+a-b` into an
order-`k+1` representation of `q+a`.  Since `b ∉ T`, the hit lies in the
predecessor support; and since `q < b`, that support is bounded strictly
below `a`.  Hence `T.erase a` destroys the translated predecessor.

This is the arithmetic interaction between distinct internal-anchor cells:
an earlier anchor forces the later cell's erased core to destroy a new
order-`k` target. -/
theorem crossAnchor_erasedCore_destroys_predecessor
    {A : Set ℕ} {k q a b : ℕ} {T : Finset ℕ}
    (hdestroy : DestroysAt
      (additiveSupportFamily A (k + 1))
      (T : Set ℕ) (q + a))
    (hbA : b ∈ A) (hbT : b ∉ T)
    (hba : b ≤ a) (hqb : q < b) :
    DestroysAt
      (additiveSupportFamily A k)
      ((T.erase a : Finset ℕ) : Set ℕ) (q + a - b) := by
  intro E hER
  have hlift :
      insert b E ∈
        additiveSupportFamily A (k + 1) (q + a) := by
    have h := insert_mem_additiveSupportFamily_succ hbA hER
    have hsum : b + (q + a - b) = q + a := by omega
    simpa [hsum] using h
  obtain ⟨x, hxLift, hxT⟩ :=
    Set.not_disjoint_iff.mp (hdestroy (insert b E) hlift)
  have hxb : x ≠ b := by
    intro hxb
    subst x
    exact hbT (Finset.mem_coe.mp hxT)
  have hxE : x ∈ E := by
    rcases Finset.mem_insert.mp hxLift with hxb' | hxE
    · exact (hxb hxb').elim
    · exact hxE
  have hxa : x ≠ a := by
    intro hxa
    subst x
    have hale : a ≤ q + a - b :=
      additiveSupportFamily_supportsBounded
        A k (q + a - b) E hER a hxE
    omega
  apply Set.not_disjoint_iff.mpr
  exact ⟨x, Finset.mem_coe.mpr hxE,
    Finset.mem_coe.mpr
      (Finset.mem_erase.mpr ⟨hxa, Finset.mem_coe.mp hxT⟩)⟩

/-- Swap an external summand `b` with one chosen occurrence of `x` in an
order-`k+1` representation of `n - b`.  The remaining `k` summands are
unchanged, so inserting `b` gives an order-`k+1` representation of `n - x`.

The conclusion retains both the new support and the fact that it contains
`b`; the latter is what makes the incidence encoding injective. -/
theorem additiveSupport_swap_external_succ
    {A : Set ℕ} {k n b x : ℕ} {E : Finset ℕ}
    (hbA : b ∈ A)
    (hbn : b ≤ n)
    (hER : E ∈ additiveSupportFamily A (k + 1) (n - b))
    (hxE : x ∈ E) :
    ∃ G ∈ additiveSupportFamily A (k + 1) (n - x), b ∈ G := by
  classical
  have hxle : x ≤ n - b :=
    additiveSupportFamily_supportsBounded
      A (k + 1) (n - b) E hER x hxE
  obtain ⟨v, hvA, hvsum, rfl⟩ :=
    mem_additiveSupportFamily_iff.mp hER
  obtain ⟨i, hi⟩ := mem_tupleSupport_iff.mp hxE
  let u : Fin k → ℕ := fun j => (v (i.succAbove j)).1
  have husum : ∑ j, u j = n - b - x := by
    have hsplit := Fin.sum_univ_succAbove (fun t => (v t).1) i
    rw [hvsum, hi] at hsplit
    dsimp only [u]
    omega
  have hule : ∀ j, u j ≤ n - b - x := by
    intro j
    rw [← husum]
    exact Finset.single_le_sum
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  let w : Fin k → Fin (n - b - x + 1) := fun j =>
    ⟨u j, Nat.lt_succ_of_le (hule j)⟩
  have hwR :
      tupleSupport w ∈
        additiveSupportFamily A k (n - b - x) := by
    apply mem_additiveSupportFamily_iff.mpr
    refine ⟨w, ?_, ?_, rfl⟩
    · intro j
      exact hvA (i.succAbove j)
    · simpa [w] using husum
  let G : Finset ℕ := insert b (tupleSupport w)
  have hGR :
      G ∈ additiveSupportFamily A (k + 1) (n - x) := by
    have hlift := insert_mem_additiveSupportFamily_succ hbA hwR
    have hsum : b + (n - b - x) = n - x := by omega
    simpa [G, hsum] using hlift
  exact ⟨G, hGR, Finset.mem_insert_self b (tupleSupport w)⟩

/-- Exact-target richness versus a lower-order gap.  If many basis elements
`b ≤ n` all have an order-`k` predecessor support at `n-b`, adjoining `b`
places every such `b` in the union of the order-`k+1` supports of `n`.
Since each support has at most `k+1` vertices, either that exact support
family is large or one of the predecessors is a genuine gap.

This is the target-covering complement to the gap descent: every target with
few exact supports lies in a translate of the lower-order gap set. -/
theorem many_belowBasisElements_force_exactSupportGrowth_or_gap
    {A : Set ℕ} {k n r : ℕ} {B : Finset ℕ}
    (hBA : ∀ b ∈ B, b ∈ A)
    (hBn : ∀ b ∈ B, b ≤ n)
    (hlarge : (k + 1) * r < B.card) :
    r < (additiveSupportFamily A (k + 1) n).card ∨
      ∃ b ∈ B, additiveSupportFamily A k (n - b) = ∅ := by
  classical
  by_contra hnone
  push Not at hnone
  have hsupport : ∀ b : {b // b ∈ B},
      ∃ E ∈ additiveSupportFamily A k (n - b.1), True := by
    intro b
    obtain ⟨E, hER⟩ := hnone.2 b.1 b.2
    exact ⟨E, hER, trivial⟩
  choose predecessor hpredecessorR _ using hsupport
  let lifted : {b // b ∈ B} → Finset ℕ := fun b =>
    insert b.1 (predecessor b)
  have hliftedR : ∀ b,
      lifted b ∈ additiveSupportFamily A (k + 1) n := by
    intro b
    have h :=
      insert_mem_additiveSupportFamily_succ
        (hBA b.1 b.2) (hpredecessorR b)
    have hsum : b.1 + (n - b.1) = n := by
      exact Nat.add_sub_of_le (hBn b.1 b.2)
    simpa [lifted, hsum] using h
  have hbLifted : ∀ b, b.1 ∈ lifted b := by
    intro b
    exact Finset.mem_insert_self _ _
  let U :=
    (additiveSupportFamily A (k + 1) n).biUnion id
  have hBU : B ⊆ U := by
    intro b hbB
    let b' : {b // b ∈ B} := ⟨b, hbB⟩
    exact Finset.mem_biUnion.mpr
      ⟨lifted b', hliftedR b', hbLifted b'⟩
  have hUcard :
      U.card ≤
        (k + 1) * (additiveSupportFamily A (k + 1) n).card := by
    calc
      U.card ≤
          ∑ E ∈ additiveSupportFamily A (k + 1) n,
            E.card := Finset.card_biUnion_le
      _ ≤
          ∑ _E ∈ additiveSupportFamily A (k + 1) n,
            (k + 1) := by
        gcongr with E hER
        exact additiveSupportFamily_cardAtMost
          A (k + 1) n E hER
      _ =
          (k + 1) *
            (additiveSupportFamily A (k + 1) n).card := by
        simp [Nat.mul_comm]
  have hupper : B.card ≤ (k + 1) * r := by
    exact (Finset.card_le_card hBU).trans <|
      hUcard.trans <|
        Nat.mul_le_mul_left (k + 1) hnone.1
  omega

/-- A bounded successor destroyer hit by many usable external anchors forces
growth of the predecessor support family at one common translated target.

For every external `b`, choose a predecessor support of `n-b`; destruction
chooses a hit `x ∈ T`, and `additiveSupport_swap_external_succ` turns it into
an order-`k+1` support of `n-x` containing `b`.  A support contains at most
`k+1` external anchors, so if every translated support family had at most
`r` members, the number of anchors would be at most
`|T| * ((k+1) * r)`. -/
theorem large_externalAnchorSet_forces_supportGrowth_succ
    {A : Set ℕ} {k n r : ℕ} {T B : Finset ℕ}
    (hdestroy : DestroysAt
      (additiveSupportFamily A (k + 2)) (T : Set ℕ) n)
    (hBA : ∀ b ∈ B, b ∈ A)
    (hBT : Disjoint B T)
    (hble : ∀ b ∈ B, b ≤ n)
    (hrep : ∀ b ∈ B,
      (additiveSupportFamily A (k + 1) (n - b)).Nonempty)
    (hlarge : T.card * ((k + 1) * r) < B.card) :
    ∃ x ∈ T, x ≤ n ∧
      r < (additiveSupportFamily A (k + 1) (n - x)).card := by
  classical
  let chosenSupport : ∀ b : {b // b ∈ B}, Finset ℕ := fun b =>
    (hrep b.1 b.2).choose
  have hchosenSupport : ∀ b : {b // b ∈ B},
      chosenSupport b ∈
        additiveSupportFamily A (k + 1) (n - b.1) := by
    intro b
    exact (hrep b.1 b.2).choose_spec
  have hdescend : ∀ b : {b // b ∈ B},
      DestroysAt
        (additiveSupportFamily A (k + 1))
        (T : Set ℕ) (n - b.1) := by
    intro b
    exact additiveSuccessorTransversalsDescend A (k + 1)
      T n hdestroy b.1 (hBA b.1 b.2)
      (fun hbT => Finset.disjoint_left.mp hBT b.2
        (Finset.mem_coe.mp hbT))
      (hble b.1 b.2)
  let hit : ∀ b : {b // b ∈ B}, {x // x ∈ T} := fun b =>
    let witness := Set.not_disjoint_iff.mp
      (hdescend b (chosenSupport b) (hchosenSupport b))
    ⟨witness.choose, Finset.mem_coe.mp witness.choose_spec.2⟩
  have hhitSupport : ∀ b : {b // b ∈ B},
      (hit b).1 ∈ chosenSupport b := by
    intro b
    exact Finset.mem_coe.mp
      (Set.not_disjoint_iff.mp
        (hdescend b (chosenSupport b) (hchosenSupport b))).choose_spec.1
  have hhitBounded : ∀ b : {b // b ∈ B}, (hit b).1 ≤ n := by
    intro b
    exact le_trans
      (additiveSupportFamily_supportsBounded
        A (k + 1) (n - b.1)
        (chosenSupport b) (hchosenSupport b)
        (hit b).1 (hhitSupport b))
      (Nat.sub_le n b.1)
  let boundedT : Finset ℕ := T.filter fun x => x ≤ n
  let boundedHit : ∀ b : {b // b ∈ B}, {x // x ∈ boundedT} := fun b =>
    ⟨(hit b).1,
      Finset.mem_filter.mpr ⟨(hit b).2, hhitBounded b⟩⟩
  have hswap : ∀ b : {b // b ∈ B},
      ∃ G ∈ additiveSupportFamily A (k + 1) (n - (hit b).1),
        b.1 ∈ G := by
    intro b
    exact additiveSupport_swap_external_succ
      (hBA b.1 b.2) (hble b.1 b.2)
      (hchosenSupport b) (hhitSupport b)
  let swappedSupport (b : {b // b ∈ B}) : Finset ℕ :=
    (hswap b).choose
  have hswappedSupport : ∀ b : {b // b ∈ B},
      swappedSupport b ∈
        additiveSupportFamily A (k + 1) (n - (hit b).1) := by
    intro b
    exact (hswap b).choose_spec.1
  have hbSwapped : ∀ b : {b // b ∈ B},
      b.1 ∈ swappedSupport b := by
    intro b
    exact (hswap b).choose_spec.2
  let Target := Σ x : {x // x ∈ boundedT},
    {y // y ∈
      (additiveSupportFamily A (k + 1) (n - x.1)).biUnion id}
  let encode : {b // b ∈ B} → Target := fun b =>
    ⟨boundedHit b, ⟨b.1, Finset.mem_biUnion.mpr
      ⟨swappedSupport b, hswappedSupport b, hbSwapped b⟩⟩⟩
  have hencode : Function.Injective encode := by
    intro b c hbc
    apply Subtype.ext
    exact congrArg (fun z : Target => z.2.1) hbc
  have hdomainTarget : B.card ≤ Fintype.card Target := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective encode hencode
  by_contra hnone
  push Not at hnone
  have hunionBound : ∀ x : {x // x ∈ boundedT},
      ((additiveSupportFamily A (k + 1) (n - x.1)).biUnion id).card ≤
        (k + 1) * r := by
    intro x
    calc
      ((additiveSupportFamily A (k + 1) (n - x.1)).biUnion id).card ≤
          ∑ E ∈ additiveSupportFamily A (k + 1) (n - x.1),
            E.card := Finset.card_biUnion_le
      _ ≤ ∑ _E ∈ additiveSupportFamily A (k + 1) (n - x.1),
            (k + 1) := by
        gcongr with E hER
        exact additiveSupportFamily_cardAtMost
          A (k + 1) (n - x.1) E hER
      _ = (k + 1) *
          (additiveSupportFamily A (k + 1) (n - x.1)).card := by
        simp [Nat.mul_comm]
      _ ≤ (k + 1) * r := Nat.mul_le_mul_left (k + 1) <|
        hnone x.1 (Finset.mem_filter.mp x.2).1
          (Finset.mem_filter.mp x.2).2
  have htargetBound :
      Fintype.card Target ≤ T.card * ((k + 1) * r) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe]
    calc
      (∑ x : {x // x ∈ boundedT},
          ((additiveSupportFamily A (k + 1)
            (n - x.1)).biUnion id).card) ≤
          ∑ _x : {x // x ∈ boundedT}, ((k + 1) * r) := by
        gcongr with x
        exact hunionBound x
      _ = boundedT.card * ((k + 1) * r) := by simp
      _ ≤ T.card * ((k + 1) * r) := by
        exact Nat.mul_le_mul_right ((k + 1) * r) <|
          Finset.card_le_card (Finset.filter_subset _ _)
  have hupper : B.card ≤ T.card * ((k + 1) * r) :=
    hdomainTarget.trans htargetBound
  omega

/-- Distinguished-anchor form of the incidence lemma.  When the successor
target is written as `n = q + a`, the hit selected by the incidence count
has a useful exact split.  If the hit is the distinguished anchor `a`, the
large predecessor family lies at the original target `q` itself.  Otherwise
the hit belongs to the strictly smaller erased core `T.erase a`.

This retains precisely the target label which was lost in the unlabelled
rank descent: every failure to land back on `q` is localized to a point of
the successor destroyer other than its anchor.  A further argument is still
needed before that localization can be iterated as an actual core descent. -/
theorem large_externalAnchorSet_forces_supportGrowth_anchorFork
    {A : Set ℕ} {k n q a r : ℕ} {T B : Finset ℕ}
    (hnqa : n = q + a)
    (hdestroy : DestroysAt
      (additiveSupportFamily A (k + 2)) (T : Set ℕ) n)
    (hBA : ∀ b ∈ B, b ∈ A)
    (hBT : Disjoint B T)
    (hble : ∀ b ∈ B, b ≤ n)
    (hrep : ∀ b ∈ B,
      (additiveSupportFamily A (k + 1) (n - b)).Nonempty)
    (hlarge : T.card * ((k + 1) * r) < B.card) :
    r < (additiveSupportFamily A (k + 1) q).card ∨
      ∃ x ∈ T.erase a, x ≤ n ∧
        r < (additiveSupportFamily A (k + 1) (n - x)).card := by
  obtain ⟨x, hxT, hxn, hxlarge⟩ :=
    large_externalAnchorSet_forces_supportGrowth_succ
      hdestroy hBA hBT hble hrep hlarge
  by_cases hxa : x = a
  · left
    subst x
    have htarget : n - a = q := by omega
    rw [htarget] at hxlarge
    exact hxlarge
  · right
    exact ⟨x, Finset.mem_erase.mpr ⟨hxa, hxT⟩, hxn, hxlarge⟩

/-- If every non-anchor channel has bounded support count, the distinguished
anchor channel must carry the growth, so the target is exactly `q`. -/
theorem large_externalAnchorSet_forces_exactTargetSupportGrowth
    {A : Set ℕ} {k n q a r : ℕ} {T B : Finset ℕ}
    (hnqa : n = q + a)
    (hdestroy : DestroysAt
      (additiveSupportFamily A (k + 2)) (T : Set ℕ) n)
    (hBA : ∀ b ∈ B, b ∈ A)
    (hBT : Disjoint B T)
    (hble : ∀ b ∈ B, b ≤ n)
    (hrep : ∀ b ∈ B,
      (additiveSupportFamily A (k + 1) (n - b)).Nonempty)
    (hoff : ∀ x ∈ T.erase a, x ≤ n →
      (additiveSupportFamily A (k + 1) (n - x)).card ≤ r)
    (hlarge : T.card * ((k + 1) * r) < B.card) :
    r < (additiveSupportFamily A (k + 1) q).card := by
  obtain hexact | ⟨x, hxcore, hxn, hxlarge⟩ :=
    large_externalAnchorSet_forces_supportGrowth_anchorFork
      hnqa hdestroy hBA hBT hble hrep hlarge
  · exact hexact
  · exact (not_lt_of_ge (hoff x hxcore hxn) hxlarge).elim

/-- Basis-specialized form of the incidence lemma.  Once every predecessor
`n-b` lies beyond the exact order-`k+1` basis threshold, the predecessor
support required for each external anchor exists automatically. -/
theorem IsExactTupleAsymptoticBasis.large_externalAnchorSet_forces_supportGrowth_succ
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1)) :
    ∃ N, ∀ {n r : ℕ} {T B : Finset ℕ},
      DestroysAt
          (additiveSupportFamily A (k + 2)) (T : Set ℕ) n →
      (∀ b ∈ B, b ∈ A) →
      Disjoint B T →
      (∀ b ∈ B, N + b ≤ n) →
      T.card * ((k + 1) * r) < B.card →
      ∃ x ∈ T, x ≤ n ∧
        r < (additiveSupportFamily A (k + 1) (n - x)).card := by
  obtain ⟨N, hN⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  refine ⟨N, ?_⟩
  intro n r T B hdestroy hBA hBT hlate hlarge
  apply Erdos881.large_externalAnchorSet_forces_supportGrowth_succ
    hdestroy hBA hBT
  · intro b hbB
    have := hlate b hbB
    omega
  · intro b hbB
    obtain ⟨E, hER, _⟩ :=
      hN (n - b) (by
        have := hlate b hbB
        omega)
    exact ⟨E, hER⟩
  · exact hlarge

/-- Basis-specialized distinguished-anchor fork.  It is enough to choose
the external test anchors below `q` and to put the translate anchor `a`
beyond the basis threshold: then every predecessor `q+a-b` is represented.

Thus a large bounded successor transversal over `q+a` either creates support
growth at exactly `q`, or attributes the growth to a hit in `T.erase a`. -/
theorem IsExactTupleAsymptoticBasis.large_belowTargetAnchorSet_forces_supportGrowth_anchorFork
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1)) :
    ∃ N, ∀ {q a r : ℕ} {T B : Finset ℕ},
      DestroysAt
          (additiveSupportFamily A (k + 2)) (T : Set ℕ) (q + a) →
      (∀ b ∈ B, b ∈ A) →
      Disjoint B T →
      (∀ b ∈ B, b ≤ q) →
      N ≤ a →
      T.card * ((k + 1) * r) < B.card →
      r < (additiveSupportFamily A (k + 1) q).card ∨
        ∃ x ∈ T.erase a, x ≤ q + a ∧
          r <
            (additiveSupportFamily A (k + 1) (q + a - x)).card := by
  obtain ⟨N, hN⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  refine ⟨N, ?_⟩
  intro q a r T B hdestroy hBA hBT hbq hNa hlarge
  apply large_externalAnchorSet_forces_supportGrowth_anchorFork
    (n := q + a) (q := q) (a := a) rfl
    hdestroy hBA hBT
  · intro b hbB
    exact (hbq b hbB).trans (Nat.le_add_right q a)
  · intro b hbB
    obtain ⟨E, hER, _⟩ :=
      hN (q + a - b) (by
        have hb := hbq b hbB
        omega)
    exact ⟨E, hER⟩
  · exact hlarge

/-- At a fixed predecessor target `q`, its moving translate anchor cannot
remain a singleton successor destroyer arbitrarily far out.

If `{a}` destroyed `q+a`, test that destruction against more external basis
elements than there are order-`k+1` supports of `q`.  The incidence lemma
has only the hit `a` available, so it would inject all those tests back into
distinct supports of the fixed target `q`, a cardinality contradiction. -/
theorem IsExactTupleAsymptoticBasis.eventually_not_anchorSingletonDestroyer
    {A : Set ℕ} {k q : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1)) :
    ∃ L, ∀ a ∈ A, L ≤ a →
      ¬ DestroysAt
        (additiveSupportFamily A (k + 2)) ({a} : Set ℕ) (q + a) := by
  classical
  obtain ⟨N, hforce⟩ :=
    hbasis.large_externalAnchorSet_forces_supportGrowth_succ
  let r := (additiveSupportFamily A (k + 1) q).card
  let s := (k + 1) * r + 1
  obtain ⟨B, hBA, hBcard⟩ :=
    hbasis.infinite.exists_subset_card_eq s
  have hBnonempty : B.Nonempty := by
    apply Finset.card_pos.mp
    rw [hBcard]
    simp [s]
  refine ⟨N + B.max' hBnonempty + 1, ?_⟩
  intro a haA hLa hdestroy
  have hBa : Disjoint B ({a} : Finset ℕ) := by
    rw [Finset.disjoint_left]
    intro b hbB hba
    have hbmax : b ≤ B.max' hBnonempty :=
      Finset.le_max' B b hbB
    have hbaEq : b = a := by simpa using hba
    omega
  have hlate : ∀ b ∈ B, N + b ≤ q + a := by
    intro b hbB
    have hbmax : b ≤ B.max' hBnonempty :=
      Finset.le_max' B b hbB
    omega
  have hlarge :
      ({a} : Finset ℕ).card * ((k + 1) * r) < B.card := by
    rw [hBcard]
    simp [s]
  have hdestroy' :
      DestroysAt
        (additiveSupportFamily A (k + 2))
        (({a} : Finset ℕ) : Set ℕ) (q + a) := by
    simpa using hdestroy
  obtain ⟨x, hxSingleton, _hxn, hxlarge⟩ :=
    hforce hdestroy' hBA hBa hlate hlarge
  have hxa : x = a := by simpa using hxSingleton
  subst x
  have htarget : q + a - a = q := by omega
  rw [htarget] at hxlarge
  exact (Nat.lt_irrefl r hxlarge)

/-- Once singleton destruction by the moving anchor has been excluded, any
protected successor destroyer contains a genuine binary repair cell at the
same target.

Minimize the destroyer.  The protected padded support forces the anchor to
remain in the minimal core.  Since the singleton anchor is not itself a
destroyer, the core has a second point.  Minimality supplies private supports
at these two points, and they meet the resulting binary cell at opposite
endpoints. -/
theorem representedTranslate_destroyer_has_binaryRepairCell
    {A : Set ℕ} {k q a : ℕ} {T E : Finset ℕ}
    (haA : a ∈ A)
    (hER : E ∈ additiveSupportFamily A (k + 1) q)
    (hET : Disjoint (E : Set ℕ) (T : Set ℕ))
    (hdestroy :
      DestroysAt
        (additiveSupportFamily A (k + 2))
        (T : Set ℕ) (q + a))
    (hnoSingleton :
      ¬ DestroysAt
        (additiveSupportFamily A (k + 2))
        ({a} : Set ℕ) (q + a)) :
    ∃ x Hanchor Hcore,
      a ∈ T ∧ x ∈ T.erase a ∧ x ≠ a ∧
      Hanchor ∈ additiveSupportFamily A (k + 2) (q + a) ∧
      Hcore ∈ additiveSupportFamily A (k + 2) (q + a) ∧
      Hanchor ∩ {a, x} = {a} ∧
      Hcore ∩ {a, x} = {x} := by
  classical
  have hanchorR :
      insert a E ∈ additiveSupportFamily A (k + 2) (q + a) := by
    have h := insert_mem_additiveSupportFamily_succ haA hER
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have haT : a ∈ T := by
    obtain ⟨y, hyAE, hyT⟩ :=
      Set.not_disjoint_iff.mp (hdestroy (insert a E) hanchorR)
    rcases Finset.mem_insert.mp hyAE with hya | hyE
    · exact hya ▸ Finset.mem_coe.mp hyT
    · exact (Set.disjoint_left.mp hET
        (Finset.mem_coe.mpr hyE) hyT).elim
  obtain ⟨D, hDT, hDminimal⟩ :=
    exists_inclusionMinimalDestroyer_subset hdestroy
  have haD : a ∈ D := by
    obtain ⟨y, hyAE, hyD⟩ :=
      Set.not_disjoint_iff.mp (hDminimal.1 (insert a E) hanchorR)
    have hyT : y ∈ T := hDT (Finset.mem_coe.mp hyD)
    rcases Finset.mem_insert.mp hyAE with hya | hyE
    · exact hya ▸ Finset.mem_coe.mp hyD
    · exact (Set.disjoint_left.mp hET
        (Finset.mem_coe.mpr hyE) (Finset.mem_coe.mpr hyT)).elim
  have hDnotSingleton : D ≠ {a} := by
    intro hDa
    apply hnoSingleton
    simpa [hDa] using hDminimal.1
  have hsecond : ∃ x ∈ D, x ≠ a := by
    by_contra hnone
    push Not at hnone
    apply hDnotSingleton
    ext y
    simp only [Finset.mem_singleton]
    constructor
    · exact fun hyD => hnone y hyD
    · rintro rfl
      exact haD
  obtain ⟨x, hxD, hxa⟩ := hsecond
  obtain ⟨Hanchor, hHanchorR, hHanchorUnique⟩ :=
    hDminimal.exists_uniqueHitSupport haD
  obtain ⟨Hcore, hHcoreR, hHcoreUnique⟩ :=
    hDminimal.exists_uniqueHitSupport hxD
  have hpairD : {a, x} ⊆ D := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact haD
    · exact hxD
  have hanchorPair : Hanchor ∩ {a, x} = {a} := by
    ext y
    constructor
    · intro hy
      have hyLarge : y ∈ Hanchor ∩ D :=
        Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hy).1,
            hpairD (Finset.mem_inter.mp hy).2⟩
      simpa [hHanchorUnique] using hyLarge
    · intro hy
      have hya : y = a := by simpa using hy
      subst y
      have haLarge : a ∈ Hanchor ∩ D := by
        simp [hHanchorUnique]
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp haLarge).1, by simp⟩
  have hcorePair : Hcore ∩ {a, x} = {x} := by
    ext y
    constructor
    · intro hy
      have hyLarge : y ∈ Hcore ∩ D :=
        Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hy).1,
            hpairD (Finset.mem_inter.mp hy).2⟩
      simpa [hHcoreUnique] using hyLarge
    · intro hy
      have hyx : y = x := by simpa using hy
      subst y
      have hxLarge : x ∈ Hcore ∩ D := by
        simp [hHcoreUnique]
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hxLarge).1, by simp⟩
  exact ⟨x, Hanchor, Hcore, haT,
    Finset.mem_erase.mpr ⟨hxa, hDT hxD⟩, hxa,
    hHanchorR, hHcoreR, hanchorPair, hcorePair⟩

/-- Retaining the uniform cardinal bound in a recurrent successor
transversal forces arbitrarily large predecessor support stars at general
order.  This is the order-uniform analogue of
`recurrentLargePairStars_of_boundedFullTranslateDestroyers`.

The next combinatorial step is rank descent: a sufficiently large bounded
family either has a large matching, or a high-degree hit can be removed to
produce a large support family one order lower. -/
theorem recurrentLargeSupportStars_of_boundedFullTranslateDestroyers
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hfull : HasBoundedFullTranslateDestroyersByAnchor A (k + 1) Q) :
    ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A → ∀ r L,
      ∃ n T q a x,
        L ≤ a ∧ q ∈ Q ∧ a ∈ A ∧ n = q + a ∧
        (∀ y ∈ T, y ∈ A) ∧ Disjoint T F ∧ T.Nonempty ∧
        DestroysAt
          (additiveSupportFamily A (k + 2)) (T : Set ℕ) n ∧
        x ∈ T ∧ x ≤ n ∧
        r < (additiveSupportFamily A (k + 1) (n - x)).card := by
  classical
  obtain ⟨N, hforce⟩ :=
    hbasis.large_externalAnchorSet_forces_supportGrowth_succ
  intro F hFA r L
  obtain ⟨m, hm⟩ := hfull F hFA
  let s := m * ((k + 1) * r) + m + 1
  obtain ⟨B₀, hB₀A, hB₀card⟩ :=
    hbasis.infinite.exists_subset_card_eq s
  have hB₀nonempty : B₀.Nonempty := by
    apply Finset.card_pos.mp
    rw [hB₀card]
    simp [s]
  obtain ⟨n, T, q, a, haLower, hqQ, haA, hnqa,
      hTA, hTF, hTnonempty, hTcard, hdestroy⟩ :=
    hm (max L (N + B₀.max' hB₀nonempty))
  let B := B₀ \ T
  have hBA : ∀ b ∈ B, b ∈ A := by
    intro b hbB
    exact hB₀A (Finset.mem_sdiff.mp hbB).1
  have hBT : Disjoint B T := Finset.sdiff_disjoint
  have hlate : ∀ b ∈ B, N + b ≤ n := by
    intro b hbB
    have hbB₀ : b ∈ B₀ := (Finset.mem_sdiff.mp hbB).1
    have hbmax : b ≤ B₀.max' hB₀nonempty :=
      Finset.le_max' B₀ b hbB₀
    have hNa : N + B₀.max' hB₀nonempty ≤ a :=
      le_trans
        (le_max_right L (N + B₀.max' hB₀nonempty)) haLower
    omega
  have hinterCard : (B₀ ∩ T).card ≤ T.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hBcardSum : B.card + (B₀ ∩ T).card = B₀.card :=
    Finset.card_sdiff_add_card_inter B₀ T
  have hBlarge : T.card * ((k + 1) * r) < B.card := by
    rw [hB₀card] at hBcardSum
    dsimp only [s] at hBcardSum
    have hbase : m * ((k + 1) * r) < B.card := by omega
    exact lt_of_le_of_lt
      (Nat.mul_le_mul_right ((k + 1) * r) hTcard) hbase
  obtain ⟨x, hxT, hxn, hxlarge⟩ :=
    hforce hdestroy hBA hBT hlate hBlarge
  refine ⟨n, T, q, a, x,
    le_trans (le_max_left L (N + B₀.max' hB₀nonempty)) haLower,
    hqQ, haA, hnqa, hTA, hTF, hTnonempty, hdestroy,
    hxT, hxn, hxlarge⟩

/-! ## One-step rank descent -/

/-- A large finite hypergraph of rank at most `d` either has a matching
larger than `r`, or some vertex belongs to more than `s` edges.

This is the finite matching/star dichotomy used at each order of the descent.
If the matching number is at most `r`, a maximum matching supplies a
transversal of size at most `d*r`, and pigeonhole supplies the large star. -/
theorem large_boundedHypergraph_matching_or_star
    {α : Type*} [DecidableEq α]
    {H : Finset (Finset α)} {d r s : ℕ}
    (hedges : ∀ E ∈ H, E.Nonempty)
    (hsize : ∀ E ∈ H, E.card ≤ d)
    (hlarge : (d * r) * s < H.card) :
    (∃ M : Finset (Finset α),
        M ⊆ H ∧ IsMatching M ∧ r < M.card) ∨
      ∃ x, s < (H.filter fun E => x ∈ E).card := by
  classical
  by_cases hmatch : r < matchingNumber H
  · obtain ⟨M, hMH, hMmatching, hMcard, _hmaximal⟩ :=
      exists_maximumMatching hedges
    exact Or.inl ⟨M, hMH, hMmatching, by omega⟩
  · have hmatchle : matchingNumber H ≤ r := Nat.le_of_not_gt hmatch
    obtain ⟨T, htrans, hTcard⟩ :=
      exists_small_transversal_of_matchingNumber_le
        hedges hsize hmatchle
    have hHnonempty : H.Nonempty := by
      rw [← Finset.card_pos]
      exact lt_of_le_of_lt (Nat.zero_le ((d * r) * s)) hlarge
    let default : α :=
      (hedges hHnonempty.choose hHnonempty.choose_spec).choose
    let hit : Finset α → α := fun E =>
      if hE : E ∈ H then (htrans E hE).choose
      else default
    have hhitT : ∀ E ∈ H, hit E ∈ T := by
      intro E hEH
      simp only [hit, dif_pos hEH]
      exact (Finset.mem_inter.mp (htrans E hEH).choose_spec).2
    have hhitE : ∀ E ∈ H, hit E ∈ E := by
      intro E hEH
      simp only [hit, dif_pos hEH]
      exact (Finset.mem_inter.mp (htrans E hEH).choose_spec).1
    have hfiberLarge : T.card * s < H.card := by
      exact lt_of_le_of_lt (Nat.mul_le_mul_right s hTcard) hlarge
    obtain ⟨x, hxT, hxfiber⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        hhitT hfiberLarge
    have hsub :
        H.filter (fun E => hit E = x) ⊆
          H.filter (fun E => x ∈ E) := by
      intro E hE
      obtain ⟨hEH, hhit⟩ := Finset.mem_filter.mp hE
      apply Finset.mem_filter.mpr
      exact ⟨hEH, hhit ▸ hhitE E hEH⟩
    exact Or.inr ⟨x, lt_of_lt_of_le hxfiber
      (Finset.card_le_card hsub)⟩

/-- Removing one chosen occurrence of `x` from an order-`k+1` tuple lowers
both the order and target by one summand.  At support level the original
support is exactly `insert x H`; this exact reconstruction makes the descent
injective on a star of distinct supports. -/
theorem additiveSupport_remove_hit_succ
    {A : Set ℕ} {k m x : ℕ} {E : Finset ℕ}
    (hER : E ∈ additiveSupportFamily A (k + 1) m)
    (hxE : x ∈ E) :
    ∃ H ∈ additiveSupportFamily A k (m - x),
      E = insert x H := by
  classical
  have hxle : x ≤ m :=
    additiveSupportFamily_supportsBounded
      A (k + 1) m E hER x hxE
  obtain ⟨v, hvA, hvsum, hEv⟩ :=
    mem_additiveSupportFamily_iff.mp hER
  obtain ⟨i, hi⟩ :=
    mem_tupleSupport_iff.mp (hEv ▸ hxE)
  let u : Fin k → ℕ := fun j => (v (i.succAbove j)).1
  have husum : ∑ j, u j = m - x := by
    have hsplit := Fin.sum_univ_succAbove (fun t => (v t).1) i
    rw [hvsum, hi] at hsplit
    dsimp only [u]
    omega
  have hule : ∀ j, u j ≤ m - x := by
    intro j
    rw [← husum]
    exact Finset.single_le_sum
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  let w : Fin k → Fin (m - x + 1) := fun j =>
    ⟨u j, Nat.lt_succ_of_le (hule j)⟩
  have hwR :
      tupleSupport w ∈ additiveSupportFamily A k (m - x) := by
    apply mem_additiveSupportFamily_iff.mpr
    refine ⟨w, ?_, ?_, rfl⟩
    · intro j
      exact hvA (i.succAbove j)
    · simpa [w] using husum
  refine ⟨tupleSupport w, hwR, ?_⟩
  rw [← hEv]
  ext y
  simp only [Finset.mem_insert, mem_tupleSupport_iff]
  constructor
  · intro hy
    by_cases hyx : y = x
    · exact Or.inl hyx
    · right
      obtain ⟨j, hj⟩ := hy
      have hji : j ≠ i := by
        intro hji
        subst j
        exact hyx (hj.symm.trans hi)
      obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hji
      refine ⟨t, ?_⟩
      simpa [w, u, ht] using hj
  · rintro (rfl | ⟨j, hj⟩)
    · exact ⟨i, hi⟩
    · exact ⟨i.succAbove j, by simpa [w, u] using hj⟩

/-- Gap-driven internal-anchor descent.  Suppose `T` destroys every
order-`k+2` representation of `q+a`, and `b ∈ A \ T` lies below `q`.
If `q-b` has no order-`k` representation, then `T.erase a` destroys every
order-`k+1` representation of `q+a-b`.

The key point is exact: a hit at `a` would allow that occurrence of `a` to
be removed, producing the forbidden order-`k` representation of `q-b`.
Thus every hit belongs to the strict erased core. -/
theorem gapAnchor_erasedCore_destroys_predecessor
    {A : Set ℕ} {k q a b : ℕ} {T : Finset ℕ}
    (hdestroy : DestroysAt
      (additiveSupportFamily A (k + 2))
      (T : Set ℕ) (q + a))
    (hbA : b ∈ A) (hbT : b ∉ T)
    (hbq : b ≤ q)
    (hgap : additiveSupportFamily A k (q - b) = ∅) :
    DestroysAt
      (additiveSupportFamily A (k + 1))
      ((T.erase a : Finset ℕ) : Set ℕ) (q + a - b) := by
  intro E hER
  have hlift :
      insert b E ∈
        additiveSupportFamily A (k + 2) (q + a) := by
    have h := insert_mem_additiveSupportFamily_succ hbA hER
    have hsum : b + (q + a - b) = q + a := by omega
    simpa [hsum] using h
  obtain ⟨x, hxLift, hxT⟩ :=
    Set.not_disjoint_iff.mp (hdestroy (insert b E) hlift)
  have hxb : x ≠ b := by
    intro hxb
    subst x
    exact hbT (Finset.mem_coe.mp hxT)
  have hxE : x ∈ E := by
    rcases Finset.mem_insert.mp hxLift with hxb' | hxE
    · exact (hxb hxb').elim
    · exact hxE
  have hxa : x ≠ a := by
    intro hxa
    subst x
    obtain ⟨H, hHR, _hEH⟩ :=
      additiveSupport_remove_hit_succ hER hxE
    have htarget : q + a - b - a = q - b := by omega
    rw [htarget, hgap] at hHR
    simp at hHR
  apply Set.not_disjoint_iff.mpr
  exact ⟨x, Finset.mem_coe.mpr hxE,
    Finset.mem_coe.mpr
      (Finset.mem_erase.mpr
        ⟨hxa, Finset.mem_coe.mp hxT⟩)⟩

/-- A represented gap translate forces a strict, nonempty core inside every
protected successor destroyer.

The protected support `E` of `q` first forces the moving anchor `a` to lie
in `T`: otherwise successor descent would make `T` destroy `E`.  Erasing
that anchor then gives a destroyer of `d+a` by the gap lemma.  Because
`d+a` is represented, this erased core is nonempty, and its cardinality is
exactly one smaller than that of `T`.

Unlike the order-descended obstruction alone, this statement retains the
original successor target `q+a`; that provenance is needed to control
destroyer migration. -/
theorem representedGap_successorDestroyer_has_strictCore
    {A : Set ℕ} {k q d b a : ℕ} {T E : Finset ℕ}
    (haA : a ∈ A) (hbA : b ∈ A)
    (hqdb : q = d + b)
    (hER : E ∈ additiveSupportFamily A (k + 1) q)
    (hET : Disjoint (E : Set ℕ) (T : Set ℕ))
    (hbT : b ∉ T)
    (hdestroy :
      DestroysAt
        (additiveSupportFamily A (k + 2))
        (T : Set ℕ) (q + a))
    (htarget :
      (additiveSupportFamily A (k + 1) (d + a)).Nonempty)
    (hgap : additiveSupportFamily A k d = ∅) :
    ∃ D : Finset ℕ,
      D = T.erase a ∧ a ∈ T ∧ D.Nonempty ∧
      D.card + 1 = T.card ∧
      DestroysAt
        (additiveSupportFamily A (k + 1))
        (D : Set ℕ) (d + a) := by
  classical
  have haT : a ∈ T := by
    by_contra haT
    have hdescend :
        DestroysAt
          (additiveSupportFamily A (k + 1))
          (T : Set ℕ) q := by
      have hraw :=
        additiveSuccessorTransversalsDescend
          A (k + 1) T (q + a) hdestroy a haA
            (by simpa using haT) (by omega)
      have hsub : q + a - a = q := by omega
      simpa [hsub] using hraw
    exact (hdescend E hER) hET
  let D := T.erase a
  have hbq : b ≤ q := by omega
  have hgap' : additiveSupportFamily A k (q - b) = ∅ := by
    have hsub : q - b = d := by omega
    simpa [hsub] using hgap
  have hdestroyD :
      DestroysAt
        (additiveSupportFamily A (k + 1))
        (D : Set ℕ) (d + a) := by
    have hraw :=
      gapAnchor_erasedCore_destroys_predecessor
        (A := A) (k := k) (q := q) (a := a) (b := b) (T := T)
        hdestroy hbA hbT hbq hgap'
    have htargetEq : q + a - b = d + a := by omega
    simpa [D, htargetEq] using hraw
  have hDnonempty : D.Nonempty := by
    obtain ⟨G, hGR⟩ := htarget
    by_contra hDempty
    have hDeq : D = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hDempty
    exact (hdestroyD G hGR) (by simp [hDeq])
  refine ⟨D, rfl, haT, hDnonempty, ?_, hdestroyD⟩
  simpa [D] using Finset.card_erase_add_one haT

/-- The provenance-rich form of bounded gap descent.

For arbitrarily large anchors, `T` is still recorded as a destroyer of the
successor target `q+a`, while `D = T.erase a` destroys the gap translate
`d+a`.  The exact one-point size drop is retained.  This is strictly
stronger data than a bare bounded-destroyer statement at the lower order. -/
def HasBoundedLiftedGapDestroyersByAnchor
    (A : Set ℕ) (k q d : ℕ) : Prop :=
  ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A →
    ∃ m, ∀ L, ∃ a T D,
      L ≤ a ∧ a ∈ A ∧
      (∀ x ∈ T, x ∈ A) ∧ Disjoint T F ∧
      T.Nonempty ∧ T.card ≤ m ∧
      D = T.erase a ∧ a ∈ T ∧ D.Nonempty ∧
      D.card + 1 = T.card ∧ D.card ≤ m - 1 ∧
      DestroysAt
        (additiveSupportFamily A (k + 2))
        (T : Set ℕ) (q + a) ∧
      DestroysAt
        (additiveSupportFamily A (k + 1))
        (D : Set ℕ) (d + a)

/-- Bounded full successor destroyers above a represented lower-order gap
produce bounded lifted gap destroyers with a strict one-point core.

The proof protects the gap anchor `b` and one complete support of `q`.
Eventual exact representability ensures that the descended target `d+a`
has a support, so the erased core cannot be empty. -/
theorem boundedFullTranslateDestroyers_lifted_over_gap
    {A : Set ℕ} {k q d b : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hfull :
      HasBoundedFullTranslateDestroyersByAnchor A (k + 1) {q})
    (hbA : b ∈ A)
    (hqdb : q = d + b)
    (hqrep : (additiveSupportFamily A (k + 1) q).Nonempty)
    (hgap : additiveSupportFamily A k d = ∅) :
    HasBoundedLiftedGapDestroyersByAnchor A k q d := by
  classical
  obtain ⟨N, hN⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  obtain ⟨E, hER⟩ := hqrep
  intro F hFA
  let F' := insert b (F ∪ E)
  have hF'A : (F' : Set ℕ) ⊆ A := by
    intro x hxF'
    rcases Finset.mem_insert.mp hxF' with rfl | hxUnion
    · exact hbA
    · rcases Finset.mem_union.mp hxUnion with hxF | hxE
      · exact hFA hxF
      · exact additiveSupportFamily_supportsIn
          A (k + 1) q E hER x hxE
  obtain ⟨m, hm⟩ := hfull F' hF'A
  refine ⟨m, ?_⟩
  intro L
  obtain ⟨n, T, q', a, haLower, hq'singleton, haA, hnq'a,
      hTA, hTF', hTnonempty, hTcard, hdestroy⟩ :=
    hm (max L N)
  have hq'eq : q' = q := by
    simpa using hq'singleton
  subst q'
  have hLa : L ≤ a :=
    le_trans (le_max_left L N) haLower
  have hNa : N ≤ a :=
    le_trans (le_max_right L N) haLower
  have hbT : b ∉ T := by
    intro hbT
    apply Finset.disjoint_left.mp hTF' hbT
    exact Finset.mem_insert_self b (F ∪ E)
  have hET : Disjoint (E : Set ℕ) (T : Set ℕ) := by
    rw [Set.disjoint_left]
    intro x hxE hxT
    apply Finset.disjoint_left.mp hTF' hxT
    exact Finset.mem_insert_of_mem
      (Finset.mem_union_right F hxE)
  have hdestroy' :
      DestroysAt
        (additiveSupportFamily A (k + 2))
        (T : Set ℕ) (q + a) := by
    simpa [hnq'a, Nat.add_assoc] using hdestroy
  have htarget :
      (additiveSupportFamily A (k + 1) (d + a)).Nonempty := by
    obtain ⟨G, hGR, _⟩ :=
      hN (d + a) (le_trans hNa (Nat.le_add_left a d))
    exact ⟨G, hGR⟩
  obtain ⟨D, hDerase, haT, hDnonempty, hDcardEq, hdestroyD⟩ :=
    representedGap_successorDestroyer_has_strictCore
      (A := A) (k := k) (q := q) (d := d) (b := b)
      (a := a) (T := T) (E := E)
      haA hbA hqdb hER hET hbT hdestroy' htarget hgap
  have hDcard : D.card ≤ m - 1 := by omega
  have hTF : Disjoint T F := by
    rw [Finset.disjoint_left]
    intro x hxT hxF
    apply Finset.disjoint_left.mp hTF' hxT
    exact Finset.mem_insert_of_mem
      (Finset.mem_union_left E hxF)
  exact ⟨a, T, D, hLa, haA, hTA, hTF, hTnonempty, hTcard,
    hDerase, haT, hDnonempty, hDcardEq, hDcard,
    hdestroy', hdestroyD⟩

/-- Minimalizing the strict gap core produces a private repair for every
option of the anchored cell.

The anchor option has the protected support `insert a E`.  Every point
`x` of a minimal current-order core has a private support `G` of `d+a`.
Such a `G` cannot contain `a`, since removing that occurrence would
represent the forbidden lower-order target `d`.  Therefore `insert b G` is
a successor support meeting the reduced anchored cell `insert a D₀`
exactly at `x`.

This is the local selector configuration needed after gap descent: choosing
any one cell point leaves a successor support attached to every other
option, while all arithmetic labels and the gap obstruction are retained. -/
theorem representedGap_successorDestroyer_has_minimalPrivateCore
    {A : Set ℕ} {k q d b a : ℕ} {T E : Finset ℕ}
    (haA : a ∈ A) (hbA : b ∈ A)
    (hqdb : q = d + b)
    (hER : E ∈ additiveSupportFamily A (k + 1) q)
    (hET : Disjoint (E : Set ℕ) (T : Set ℕ))
    (hbT : b ∉ T)
    (hdestroy :
      DestroysAt
        (additiveSupportFamily A (k + 2))
        (T : Set ℕ) (q + a))
    (htarget :
      (additiveSupportFamily A (k + 1) (d + a)).Nonempty)
    (hgap : additiveSupportFamily A k d = ∅) :
    ∃ D₀ : Finset ℕ,
      D₀ ⊆ T.erase a ∧ D₀.Nonempty ∧
      IsInclusionMinimalDestroyer
        (additiveSupportFamily A (k + 1)) D₀ (d + a) ∧
      insert a E ∈ additiveSupportFamily A (k + 2) (q + a) ∧
      insert a E ∩ insert a D₀ = {a} ∧
      ∀ x ∈ D₀, ∃ G ∈ additiveSupportFamily A (k + 1) (d + a),
        G ∩ D₀ = {x} ∧ a ∉ G ∧
        insert b G ∈ additiveSupportFamily A (k + 2) (q + a) ∧
        insert b G ∩ insert a D₀ = {x} := by
  classical
  obtain ⟨D, hDerase, haT, _hDnonempty, _hDcard, hdestroyD⟩ :=
    representedGap_successorDestroyer_has_strictCore
      (A := A) (k := k) (q := q) (d := d) (b := b)
      (a := a) (T := T) (E := E)
      haA hbA hqdb hER hET hbT hdestroy htarget hgap
  obtain ⟨D₀, hD₀D, hD₀minimal⟩ :=
    exists_inclusionMinimalDestroyer_subset hdestroyD
  have hD₀erase : D₀ ⊆ T.erase a := by
    simpa [hDerase] using hD₀D
  have hD₀nonempty : D₀.Nonempty := by
    obtain ⟨G, hGR⟩ := htarget
    by_contra hD₀empty
    have hD₀eq : D₀ = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hD₀empty
    exact (hD₀minimal.1 G hGR) (by simp [hD₀eq])
  have hanchorR :
      insert a E ∈ additiveSupportFamily A (k + 2) (q + a) := by
    have h :=
      insert_mem_additiveSupportFamily_succ haA hER
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hanchorUnique : insert a E ∩ insert a D₀ = {a} := by
    ext y
    constructor
    · intro hy
      obtain ⟨hyAE, hyAD⟩ := Finset.mem_inter.mp hy
      rcases Finset.mem_insert.mp hyAE with hya | hyE
      · simpa [hya]
      · rcases Finset.mem_insert.mp hyAD with hya | hyD₀
        · simpa [hya]
        · exact (Set.disjoint_left.mp hET
            (Finset.mem_coe.mpr hyE)
            (Finset.mem_coe.mpr
              (Finset.mem_of_mem_erase (hD₀erase hyD₀)))).elim
    · intro hy
      have hya : y = a := by simpa using hy
      subst y
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩
  refine ⟨D₀, hD₀erase, hD₀nonempty, hD₀minimal,
    hanchorR, hanchorUnique, ?_⟩
  intro x hxD₀
  obtain ⟨G, hGR, hGunique⟩ :=
    hD₀minimal.exists_uniqueHitSupport hxD₀
  have haG : a ∉ G := by
    intro haG
    obtain ⟨H, hHR, _hGH⟩ :=
      additiveSupport_remove_hit_succ hGR haG
    have htargetEq : d + a - a = d := by omega
    rw [htargetEq, hgap] at hHR
    simp at hHR
  have hlift :
      insert b G ∈ additiveSupportFamily A (k + 2) (q + a) := by
    have h :=
      insert_mem_additiveSupportFamily_succ hbA hGR
    have hsum : b + (d + a) = q + a := by omega
    simpa [hsum] using h
  have hliftUnique : insert b G ∩ insert a D₀ = {x} := by
    ext y
    constructor
    · intro hy
      obtain ⟨hyBG, hyAD⟩ := Finset.mem_inter.mp hy
      rcases Finset.mem_insert.mp hyBG with hyb | hyG
      · subst y
        rcases Finset.mem_insert.mp hyAD with hba | hbD₀
        · apply (hbT ?_).elim
          simpa [hba] using haT
        · exact (hbT (Finset.mem_of_mem_erase
            (hD₀erase hbD₀))).elim
      · rcases Finset.mem_insert.mp hyAD with hya | hyD₀
        · exact (haG (hya ▸ hyG)).elim
        · have hyInter : y ∈ G ∩ D₀ :=
            Finset.mem_inter.mpr ⟨hyG, hyD₀⟩
          simpa [hGunique] using hyInter
    · intro hy
      have hyx : y = x := by simpa using hy
      subst y
      have hxG : x ∈ G := by
        have hxInter : x ∈ G ∩ D₀ := by simp [hGunique]
        exact (Finset.mem_inter.mp hxInter).1
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_insert_of_mem hxG,
          Finset.mem_insert_of_mem hxD₀⟩
  exact ⟨G, hGR, hGunique, haG, hlift, hliftUnique⟩

/-- Every represented-gap successor destroyer contains a binary repair cell.

Choose one point `x` of the nonempty minimal erased core.  The two supports
provided by `representedGap_successorDestroyer_has_minimalPrivateCore`
meet the two-point cell `{a,x}` at opposite endpoints.  Thus either possible
selector choice in this cell leaves one of the two successor supports
untouched inside the cell. -/
theorem representedGap_successorDestroyer_has_binaryRepairCell
    {A : Set ℕ} {k q d b a : ℕ} {T E : Finset ℕ}
    (haA : a ∈ A) (hbA : b ∈ A)
    (hqdb : q = d + b)
    (hER : E ∈ additiveSupportFamily A (k + 1) q)
    (hET : Disjoint (E : Set ℕ) (T : Set ℕ))
    (hbT : b ∉ T)
    (hdestroy :
      DestroysAt
        (additiveSupportFamily A (k + 2))
        (T : Set ℕ) (q + a))
    (htarget :
      (additiveSupportFamily A (k + 1) (d + a)).Nonempty)
    (hgap : additiveSupportFamily A k d = ∅) :
    ∃ x Hanchor Hcore,
      x ∈ T.erase a ∧ x ≠ a ∧
      Hanchor ∈ additiveSupportFamily A (k + 2) (q + a) ∧
      Hcore ∈ additiveSupportFamily A (k + 2) (q + a) ∧
      Hanchor ∩ {a, x} = {a} ∧
      Hcore ∩ {a, x} = {x} := by
  classical
  obtain ⟨D₀, hD₀erase, hD₀nonempty, _hD₀minimal,
      hanchorR, hanchorUnique, hcore⟩ :=
    representedGap_successorDestroyer_has_minimalPrivateCore
      (A := A) (k := k) (q := q) (d := d) (b := b)
      (a := a) (T := T) (E := E)
      haA hbA hqdb hER hET hbT hdestroy htarget hgap
  obtain ⟨x, hxD₀⟩ := hD₀nonempty
  obtain ⟨G, _hGR, _hGunique, _haG, hlift, hliftUnique⟩ :=
    hcore x hxD₀
  have hxa : x ≠ a :=
    (Finset.mem_erase.mp (hD₀erase hxD₀)).1
  have hanchorPair : insert a E ∩ {a, x} = {a} := by
    have hpairSubset : {a, x} ⊆ insert a D₀ := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
      rcases hy with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr hxD₀
    ext y
    constructor
    · intro hy
      have hyLarge : y ∈ insert a E ∩ insert a D₀ :=
        Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hy).1,
            hpairSubset (Finset.mem_inter.mp hy).2⟩
      simpa [hanchorUnique] using hyLarge
    · intro hy
      have hya : y = a := by simpa using hy
      subst y
      simp
  have hcorePair : insert b G ∩ {a, x} = {x} := by
    have hpairSubset : {a, x} ⊆ insert a D₀ := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
      rcases hy with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr hxD₀
    ext y
    constructor
    · intro hy
      have hyLarge : y ∈ insert b G ∩ insert a D₀ :=
        Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hy).1,
            hpairSubset (Finset.mem_inter.mp hy).2⟩
      simpa [hliftUnique] using hyLarge
    · intro hy
      have hyx : y = x := by simpa using hy
      subst y
      have hxLarge : x ∈ insert b G ∩ insert a D₀ := by
        simp [hliftUnique]
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hxLarge).1, by simp⟩
  exact ⟨x, insert a E, insert b G, hD₀erase hxD₀, hxa,
    hanchorR, hlift, hanchorPair, hcorePair⟩

/-- The bounded moving branch over a represented primitive gap supplies
arbitrarily late fresh binary repair cells.

Both endpoints lie in `A`, the cell avoids any prescribed finite protected
set, and its two opposite private supports represent the same successor
target `q+a`.  In a recursive use, adding both supports to the next
protected set makes every future cell avoid all earlier repairs; hence this
is the exact one-step input for a lower-triangular binary repair sequence. -/
theorem boundedFullTranslateDestroyers_recurrentBinaryRepairCells_over_gap
    {A : Set ℕ} {k q d b : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hfull :
      HasBoundedFullTranslateDestroyersByAnchor A (k + 1) {q})
    (hbA : b ∈ A)
    (hqdb : q = d + b)
    (hqrep : (additiveSupportFamily A (k + 1) q).Nonempty)
    (hgap : additiveSupportFamily A k d = ∅) :
    ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A → ∀ L,
      ∃ a x Hanchor Hcore,
        L ≤ a ∧ a ∈ A ∧ x ∈ A ∧ x ≠ a ∧
        Disjoint ({a, x} : Finset ℕ) F ∧
        Hanchor ∈ additiveSupportFamily A (k + 2) (q + a) ∧
        Hcore ∈ additiveSupportFamily A (k + 2) (q + a) ∧
        (∀ y ∈ Hanchor, y ∈ A) ∧
        (∀ y ∈ Hcore, y ∈ A) ∧
        Hanchor ∩ {a, x} = {a} ∧
        Hcore ∩ {a, x} = {x} := by
  classical
  obtain ⟨N, hN⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  obtain ⟨E, hER⟩ := hqrep
  intro F hFA L
  let F' := insert b (F ∪ E)
  have hF'A : (F' : Set ℕ) ⊆ A := by
    intro y hyF'
    rcases Finset.mem_insert.mp hyF' with rfl | hyUnion
    · exact hbA
    · rcases Finset.mem_union.mp hyUnion with hyF | hyE
      · exact hFA hyF
      · exact additiveSupportFamily_supportsIn
          A (k + 1) q E hER y hyE
  obtain ⟨_m, hm⟩ := hfull F' hF'A
  obtain ⟨n, T, q', a, haLower, hq'singleton, haA, hnq'a,
      hTA, hTF', _hTnonempty, _hTcard, hdestroy⟩ :=
    hm (max L N)
  have hq'eq : q' = q := by
    simpa using hq'singleton
  subst q'
  have hLa : L ≤ a :=
    le_trans (le_max_left L N) haLower
  have hNa : N ≤ a :=
    le_trans (le_max_right L N) haLower
  have hbT : b ∉ T := by
    intro hbT
    apply Finset.disjoint_left.mp hTF' hbT
    exact Finset.mem_insert_self b (F ∪ E)
  have hET : Disjoint (E : Set ℕ) (T : Set ℕ) := by
    rw [Set.disjoint_left]
    intro y hyE hyT
    apply Finset.disjoint_left.mp hTF' hyT
    exact Finset.mem_insert_of_mem
      (Finset.mem_union_right F hyE)
  have hdestroy' :
      DestroysAt
        (additiveSupportFamily A (k + 2))
        (T : Set ℕ) (q + a) := by
    simpa [hnq'a, Nat.add_assoc] using hdestroy
  have htarget :
      (additiveSupportFamily A (k + 1) (d + a)).Nonempty := by
    obtain ⟨G, hGR, _⟩ :=
      hN (d + a) (le_trans hNa (Nat.le_add_left a d))
    exact ⟨G, hGR⟩
  obtain ⟨x, Hanchor, Hcore, hxErase, hxa,
      hanchorR, hcoreR, hanchorUnique, hcoreUnique⟩ :=
    representedGap_successorDestroyer_has_binaryRepairCell
      (A := A) (k := k) (q := q) (d := d) (b := b)
      (a := a) (T := T) (E := E)
      haA hbA hqdb hER hET hbT hdestroy' htarget hgap
  have haT : a ∈ T := by
    by_contra haT
    have hdescend :
        DestroysAt
          (additiveSupportFamily A (k + 1))
          (T : Set ℕ) q := by
      have hraw :=
        additiveSuccessorTransversalsDescend
          A (k + 1) T (q + a) hdestroy' a haA
            (by simpa using haT) (by omega)
      have hsub : q + a - a = q := by omega
      simpa [hsub] using hraw
    exact (hdescend E hER) hET
  have hxA : x ∈ A :=
    hTA x (Finset.mem_of_mem_erase hxErase)
  have hpairF : Disjoint ({a, x} : Finset ℕ) F := by
    rw [Finset.disjoint_left]
    intro y hyPair hyF
    have hyT : y ∈ T := by
      rcases Finset.mem_insert.mp hyPair with hya | hyx
      · subst y
        exact haT
      · have hyx' : y = x := by simpa using hyx
        subst y
        exact Finset.mem_of_mem_erase hxErase
    have hyF' : y ∈ F' :=
      Finset.mem_insert_of_mem
        (Finset.mem_union_left E hyF)
    exact Finset.disjoint_left.mp hTF' hyT hyF'
  exact ⟨a, x, Hanchor, Hcore, hLa, haA, hxA, hxa, hpairF,
    hanchorR, hcoreR,
    additiveSupportFamily_supportsIn A (k + 2) (q + a)
      Hanchor hanchorR,
    additiveSupportFamily_supportsIn A (k + 2) (q + a)
      Hcore hcoreR,
    hanchorUnique, hcoreUnique⟩

/-- One fresh binary repair cell, packaged for recursive choice. -/
structure FreshBinaryRepairWitness
    (A : Set ℕ) (k q : ℕ) (F : Finset ℕ) (L : ℕ) where
  anchor : ℕ
  core : ℕ
  leftRepair : Finset ℕ
  rightRepair : Finset ℕ
  lower : L ≤ anchor
  anchor_mem : anchor ∈ A
  core_mem : core ∈ A
  distinct : core ≠ anchor
  cell_disjoint : Disjoint ({anchor, core} : Finset ℕ) F
  left_mem :
    leftRepair ∈ additiveSupportFamily A (k + 2) (q + anchor)
  right_mem :
    rightRepair ∈ additiveSupportFamily A (k + 2) (q + anchor)
  left_subset : ∀ y ∈ leftRepair, y ∈ A
  right_subset : ∀ y ∈ rightRepair, y ∈ A
  left_private : leftRepair ∩ {anchor, core} = {anchor}
  right_private : rightRepair ∩ {anchor, core} = {core}

/-- Gap-free recurrent binary cells.  A represented predecessor target and
bounded full successor transversals already suffice: protect one predecessor
support so that every destroyer contains the moving anchor, then move beyond
the singleton-anchor cutoff and minimize. -/
theorem boundedFullTranslateDestroyers_recurrentBinaryRepairCells
    {A : Set ℕ} {k q : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hfull :
      HasBoundedFullTranslateDestroyersByAnchor A (k + 1) {q})
    (hqrep : (additiveSupportFamily A (k + 1) q).Nonempty) :
    ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A → ∀ L,
      ∃ a x Hanchor Hcore,
        L ≤ a ∧ a ∈ A ∧ x ∈ A ∧ x ≠ a ∧
        Disjoint ({a, x} : Finset ℕ) F ∧
        Hanchor ∈ additiveSupportFamily A (k + 2) (q + a) ∧
        Hcore ∈ additiveSupportFamily A (k + 2) (q + a) ∧
        (∀ y ∈ Hanchor, y ∈ A) ∧
        (∀ y ∈ Hcore, y ∈ A) ∧
        Hanchor ∩ {a, x} = {a} ∧
        Hcore ∩ {a, x} = {x} := by
  classical
  obtain ⟨E, hER⟩ := hqrep
  obtain ⟨Lsingle, hsingle⟩ :=
    hbasis.eventually_not_anchorSingletonDestroyer (q := q)
  intro F hFA L
  let F' := F ∪ E
  have hF'A : (F' : Set ℕ) ⊆ A := by
    intro y hyF'
    rcases Finset.mem_union.mp hyF' with hyF | hyE
    · exact hFA hyF
    · exact additiveSupportFamily_supportsIn
        A (k + 1) q E hER y hyE
  obtain ⟨_m, hm⟩ := hfull F' hF'A
  obtain ⟨n, T, q', a, haLower, hq'singleton, haA, hnq'a,
      hTA, hTF', _hTnonempty, _hTcard, hdestroy⟩ :=
    hm (max L Lsingle)
  have hq'eq : q' = q := by
    simpa using hq'singleton
  subst q'
  have hLa : L ≤ a :=
    le_trans (le_max_left L Lsingle) haLower
  have hLsingleA : Lsingle ≤ a :=
    le_trans (le_max_right L Lsingle) haLower
  have hET : Disjoint (E : Set ℕ) (T : Set ℕ) := by
    rw [Set.disjoint_left]
    intro y hyE hyT
    apply Finset.disjoint_left.mp hTF' hyT
    exact Finset.mem_union_right F hyE
  have hdestroy' :
      DestroysAt
        (additiveSupportFamily A (k + 2))
        (T : Set ℕ) (q + a) := by
    simpa [hnq'a, Nat.add_assoc] using hdestroy
  have hnoSingleton :
      ¬ DestroysAt
        (additiveSupportFamily A (k + 2))
        ({a} : Set ℕ) (q + a) :=
    hsingle a haA hLsingleA
  obtain ⟨x, Hanchor, Hcore, haT, hxErase, hxa,
      hanchorR, hcoreR, hanchorPrivate, hcorePrivate⟩ :=
    representedTranslate_destroyer_has_binaryRepairCell
      (A := A) (k := k) (q := q) (a := a) (T := T) (E := E)
      haA hER hET hdestroy' hnoSingleton
  have hxT : x ∈ T := Finset.mem_of_mem_erase hxErase
  have hxA : x ∈ A := hTA x hxT
  have hpairF : Disjoint ({a, x} : Finset ℕ) F := by
    rw [Finset.disjoint_left]
    intro y hyPair hyF
    have hyT : y ∈ T := by
      rcases Finset.mem_insert.mp hyPair with hya | hyx
      · exact hya ▸ haT
      · have hyx' : y = x := by simpa using hyx
        exact hyx' ▸ hxT
    exact Finset.disjoint_left.mp hTF' hyT
      (Finset.mem_union_left E hyF)
  exact ⟨a, x, Hanchor, Hcore, hLa, haA, hxA, hxa,
    hpairF, hanchorR, hcoreR,
    additiveSupportFamily_supportsIn A (k + 2) (q + a)
      Hanchor hanchorR,
    additiveSupportFamily_supportsIn A (k + 2) (q + a)
      Hcore hcoreR,
    hanchorPrivate, hcorePrivate⟩

/-- The gap-free recurrent cell theorem in the packaged form used by the
recursive construction. -/
theorem nonempty_freshBinaryRepairWitness
    {A : Set ℕ} {k q : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hfull :
      HasBoundedFullTranslateDestroyersByAnchor A (k + 1) {q})
    (hqrep : (additiveSupportFamily A (k + 1) q).Nonempty)
    (F : Finset ℕ) (hFA : (F : Set ℕ) ⊆ A) (L : ℕ) :
    Nonempty (FreshBinaryRepairWitness A k q F L) := by
  obtain ⟨a, x, Hleft, Hright, hLa, haA, hxA, hxa, hcellF,
      hleftR, hrightR, hleftA, hrightA, hleftPrivate,
      hrightPrivate⟩ :=
    boundedFullTranslateDestroyers_recurrentBinaryRepairCells
      hbasis hfull hqrep F hFA L
  exact ⟨{
    anchor := a
    core := x
    leftRepair := Hleft
    rightRepair := Hright
    lower := hLa
    anchor_mem := haA
    core_mem := hxA
    distinct := hxa
    cell_disjoint := hcellF
    left_mem := hleftR
    right_mem := hrightR
    left_subset := hleftA
    right_subset := hrightA
    left_private := hleftPrivate
    right_private := hrightPrivate
  }⟩

theorem nonempty_freshBinaryRepairWitness_over_gap
    {A : Set ℕ} {k q d b : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hfull :
      HasBoundedFullTranslateDestroyersByAnchor A (k + 1) {q})
    (hbA : b ∈ A)
    (hqdb : q = d + b)
    (hqrep : (additiveSupportFamily A (k + 1) q).Nonempty)
    (hgap : additiveSupportFamily A k d = ∅)
    (F : Finset ℕ) (hFA : (F : Set ℕ) ⊆ A) (L : ℕ) :
    Nonempty (FreshBinaryRepairWitness A k q F L) := by
  obtain ⟨a, x, Hleft, Hright, hLa, haA, hxA, hxa, hcellF,
      hleftR, hrightR, hleftA, hrightA, hleftPrivate,
      hrightPrivate⟩ :=
    boundedFullTranslateDestroyers_recurrentBinaryRepairCells_over_gap
      hbasis hfull hbA hqdb hqrep hgap F hFA L
  exact ⟨{
    anchor := a
    core := x
    leftRepair := Hleft
    rightRepair := Hright
    lower := hLa
    anchor_mem := haA
    core_mem := hxA
    distinct := hxa
    cell_disjoint := hcellF
    left_mem := hleftR
    right_mem := hrightR
    left_subset := hleftA
    right_subset := hrightA
    left_private := hleftPrivate
    right_private := hrightPrivate
  }⟩

/-- An infinite lower-triangular binary repair sequence.  Every repair of an
earlier cell avoids every later cell. -/
structure LowerTriangularBinaryRepairSequence
    (A : Set ℕ) (k q : ℕ) where
  anchor : ℕ → ℕ
  core : ℕ → ℕ
  leftRepair : ℕ → Finset ℕ
  rightRepair : ℕ → Finset ℕ
  anchor_strictMono : StrictMono anchor
  anchor_mem : ∀ i, anchor i ∈ A
  core_mem : ∀ i, core i ∈ A
  distinct : ∀ i, core i ≠ anchor i
  cells_disjoint :
    Pairwise fun i j =>
      Disjoint ({anchor i, core i} : Finset ℕ)
        ({anchor j, core j} : Finset ℕ)
  left_mem : ∀ i,
    leftRepair i ∈
      additiveSupportFamily A (k + 2) (q + anchor i)
  right_mem : ∀ i,
    rightRepair i ∈
      additiveSupportFamily A (k + 2) (q + anchor i)
  left_private : ∀ i,
    leftRepair i ∩ {anchor i, core i} = {anchor i}
  right_private : ∀ i,
    rightRepair i ∩ {anchor i, core i} = {core i}
  forward_disjoint : ∀ i j, i < j →
    Disjoint (leftRepair i) ({anchor j, core j} : Finset ℕ) ∧
    Disjoint (rightRepair i) ({anchor j, core j} : Finset ℕ)

/-- Recursively protect every earlier cell and both of its repairs, given a
fresh binary repair cell beyond every finite protected state. -/
theorem exists_lowerTriangularBinaryRepairSequence_of_freshWitnesses
    {A : Set ℕ} {k q : ℕ}
    (hfresh : ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A → ∀ L,
      Nonempty (FreshBinaryRepairWitness A k q F L)) :
    Nonempty (LowerTriangularBinaryRepairSequence A k q) := by
  classical
  let State := {p : ℕ × Finset ℕ // (p.2 : Set ℕ) ⊆ A}
  let initial : State := ⟨(0, ∅), by simp⟩
  let chooseWitness : (s : State) →
      FreshBinaryRepairWitness A k q s.1.2 (s.1.1 + 1) :=
    fun s => Classical.choice <|
      hfresh s.1.2 s.2 (s.1.1 + 1)
  let cell (s : State) : Finset ℕ :=
    {(chooseWitness s).anchor, (chooseWitness s).core}
  let advance : State → State := fun s =>
    ⟨((chooseWitness s).anchor,
      s.1.2 ∪ cell s ∪
        (chooseWitness s).leftRepair ∪
        (chooseWitness s).rightRepair), by
      intro y hy
      rcases Finset.mem_union.mp hy with hy | hyRight
      · rcases Finset.mem_union.mp hy with hy | hyLeft
        · rcases Finset.mem_union.mp hy with hyOld | hyCell
          · exact s.2 hyOld
          · rcases Finset.mem_insert.mp hyCell with hya | hyx
            · subst y
              exact (chooseWitness s).anchor_mem
            · have hyx' : y = (chooseWitness s).core := by
                simpa using hyx
              subst y
              exact (chooseWitness s).core_mem
        · exact (chooseWitness s).left_subset y hyLeft
      · exact (chooseWitness s).right_subset y hyRight⟩
  let state : ℕ → State := fun i =>
    Nat.rec initial (fun _ s => advance s) i
  let witness (i : ℕ) := chooseWitness (state i)
  let U (i : ℕ) : Finset ℕ := (state i).1.2
  let a (i : ℕ) : ℕ := (witness i).anchor
  let x (i : ℕ) : ℕ := (witness i).core
  let Hleft (i : ℕ) : Finset ℕ := (witness i).leftRepair
  let Hright (i : ℕ) : Finset ℕ := (witness i).rightRepair
  let C (i : ℕ) : Finset ℕ := {a i, x i}
  have hstate_succ : ∀ i, state (i + 1) = advance (state i) := by
    intro i
    simp [state]
  have hU_succ : ∀ i,
      U (i + 1) =
        U i ∪ C i ∪ Hleft i ∪ Hright i := by
    intro i
    change (state (i + 1)).1.2 =
      (state i).1.2 ∪ cell (state i) ∪
        (witness i).leftRepair ∪ (witness i).rightRepair
    rw [hstate_succ]
  have hlast_succ : ∀ i, (state (i + 1)).1.1 = a i := by
    intro i
    rw [hstate_succ]
  have hU_step : ∀ i, U i ⊆ U (i + 1) := by
    intro i y hy
    rw [hU_succ]
    exact Finset.mem_union_left _ <|
      Finset.mem_union_left _ <|
        Finset.mem_union_left _ hy
  have hU_mono : Monotone U :=
    monotone_nat_of_le_succ hU_step
  have hC_into_next : ∀ i, C i ⊆ U (i + 1) := by
    intro i
    rw [hU_succ]
    exact fun y hy => Finset.mem_union_left _ <|
      Finset.mem_union_left _ <|
        Finset.mem_union_right _ hy
  have hleft_into_next : ∀ i, Hleft i ⊆ U (i + 1) := by
    intro i
    rw [hU_succ]
    exact fun y hy => Finset.mem_union_left _ <|
      Finset.mem_union_right _ hy
  have hright_into_next : ∀ i, Hright i ⊆ U (i + 1) := by
    intro i
    rw [hU_succ]
    exact Finset.subset_union_right
  have haStrict : StrictMono a := by
    apply strictMono_nat_of_lt_succ
    intro i
    have hlower := (witness (i + 1)).lower
    change (state (i + 1)).1.1 + 1 ≤ a (i + 1) at hlower
    rw [hlast_succ] at hlower
    omega
  have hcells : Pairwise fun i j => Disjoint (C i) (C j) := by
    intro i j hij
    by_cases hijlt : i < j
    · have hCiUj : C i ⊆ U j :=
        fun y hy => hU_mono (Nat.succ_le_of_lt hijlt)
          (hC_into_next i hy)
      exact (witness j).cell_disjoint.symm.mono_left hCiUj
    · have hjilt : j < i := by omega
      have hCjUi : C j ⊆ U i :=
        fun y hy => hU_mono (Nat.succ_le_of_lt hjilt)
          (hC_into_next j hy)
      exact (witness i).cell_disjoint.mono_right hCjUi
  have hforward : ∀ i j, i < j →
      Disjoint (Hleft i) (C j) ∧
      Disjoint (Hright i) (C j) := by
    intro i j hij
    have hLeftUj : Hleft i ⊆ U j :=
      fun y hy => hU_mono (Nat.succ_le_of_lt hij)
        (hleft_into_next i hy)
    have hRightUj : Hright i ⊆ U j :=
      fun y hy => hU_mono (Nat.succ_le_of_lt hij)
        (hright_into_next i hy)
    exact ⟨(witness j).cell_disjoint.symm.mono_left hLeftUj,
      (witness j).cell_disjoint.symm.mono_left hRightUj⟩
  exact ⟨{
    anchor := a
    core := x
    leftRepair := Hleft
    rightRepair := Hright
    anchor_strictMono := haStrict
    anchor_mem := fun i => (witness i).anchor_mem
    core_mem := fun i => (witness i).core_mem
    distinct := fun i => (witness i).distinct
    cells_disjoint := hcells
    left_mem := fun i => (witness i).left_mem
    right_mem := fun i => (witness i).right_mem
    left_private := fun i => (witness i).left_private
    right_private := fun i => (witness i).right_private
    forward_disjoint := hforward
  }⟩

/-- Start the lower-triangular recursion beyond a prescribed finite protected
set.  Every cell in the resulting sequence avoids that set, while the usual
forward repair protection is retained.

This is the finite-service interface needed for a shared reservoir: first
choose finitely many repairs, put all their vertices into `F₀`, and then grow
the infinite deletion blocks entirely outside `F₀`. -/
theorem exists_lowerTriangularBinaryRepairSequence_avoiding_of_freshWitnesses
    {A : Set ℕ} {k q : ℕ}
    (F₀ : Finset ℕ) (hF₀A : (F₀ : Set ℕ) ⊆ A)
    (hfresh : ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A → ∀ L,
      Nonempty (FreshBinaryRepairWitness A k q F L)) :
    ∃ S : LowerTriangularBinaryRepairSequence A k q,
      ∀ i, Disjoint ({S.anchor i, S.core i} : Finset ℕ) F₀ := by
  classical
  let State := {p : ℕ × Finset ℕ // (p.2 : Set ℕ) ⊆ A}
  let initial : State := ⟨(0, F₀), hF₀A⟩
  let chooseWitness : (s : State) →
      FreshBinaryRepairWitness A k q s.1.2 (s.1.1 + 1) :=
    fun s => Classical.choice <|
      hfresh s.1.2 s.2 (s.1.1 + 1)
  let cell (s : State) : Finset ℕ :=
    {(chooseWitness s).anchor, (chooseWitness s).core}
  let advance : State → State := fun s =>
    ⟨((chooseWitness s).anchor,
      s.1.2 ∪ cell s ∪
        (chooseWitness s).leftRepair ∪
        (chooseWitness s).rightRepair), by
      intro y hy
      rcases Finset.mem_union.mp hy with hy | hyRight
      · rcases Finset.mem_union.mp hy with hy | hyLeft
        · rcases Finset.mem_union.mp hy with hyOld | hyCell
          · exact s.2 hyOld
          · rcases Finset.mem_insert.mp hyCell with hya | hyx
            · subst y
              exact (chooseWitness s).anchor_mem
            · have hyx' : y = (chooseWitness s).core := by
                simpa using hyx
              subst y
              exact (chooseWitness s).core_mem
        · exact (chooseWitness s).left_subset y hyLeft
      · exact (chooseWitness s).right_subset y hyRight⟩
  let state : ℕ → State := fun i =>
    Nat.rec initial (fun _ s => advance s) i
  let witness (i : ℕ) := chooseWitness (state i)
  let U (i : ℕ) : Finset ℕ := (state i).1.2
  let a (i : ℕ) : ℕ := (witness i).anchor
  let x (i : ℕ) : ℕ := (witness i).core
  let Hleft (i : ℕ) : Finset ℕ := (witness i).leftRepair
  let Hright (i : ℕ) : Finset ℕ := (witness i).rightRepair
  let C (i : ℕ) : Finset ℕ := {a i, x i}
  have hstate_succ : ∀ i, state (i + 1) = advance (state i) := by
    intro i
    simp [state]
  have hU_succ : ∀ i,
      U (i + 1) =
        U i ∪ C i ∪ Hleft i ∪ Hright i := by
    intro i
    change (state (i + 1)).1.2 =
      (state i).1.2 ∪ cell (state i) ∪
        (witness i).leftRepair ∪ (witness i).rightRepair
    rw [hstate_succ]
  have hlast_succ : ∀ i, (state (i + 1)).1.1 = a i := by
    intro i
    rw [hstate_succ]
  have hU_step : ∀ i, U i ⊆ U (i + 1) := by
    intro i y hy
    rw [hU_succ]
    exact Finset.mem_union_left _ <|
      Finset.mem_union_left _ <|
        Finset.mem_union_left _ hy
  have hU_mono : Monotone U :=
    monotone_nat_of_le_succ hU_step
  have hF₀U : ∀ i, F₀ ⊆ U i := by
    intro i
    exact hU_mono (Nat.zero_le i)
  have hC_into_next : ∀ i, C i ⊆ U (i + 1) := by
    intro i
    rw [hU_succ]
    exact fun y hy => Finset.mem_union_left _ <|
      Finset.mem_union_left _ <|
        Finset.mem_union_right _ hy
  have hleft_into_next : ∀ i, Hleft i ⊆ U (i + 1) := by
    intro i
    rw [hU_succ]
    exact fun y hy => Finset.mem_union_left _ <|
      Finset.mem_union_right _ hy
  have hright_into_next : ∀ i, Hright i ⊆ U (i + 1) := by
    intro i
    rw [hU_succ]
    exact Finset.subset_union_right
  have haStrict : StrictMono a := by
    apply strictMono_nat_of_lt_succ
    intro i
    have hlower := (witness (i + 1)).lower
    change (state (i + 1)).1.1 + 1 ≤ a (i + 1) at hlower
    rw [hlast_succ] at hlower
    omega
  have hcells : Pairwise fun i j => Disjoint (C i) (C j) := by
    intro i j hij
    by_cases hijlt : i < j
    · have hCiUj : C i ⊆ U j :=
        fun y hy => hU_mono (Nat.succ_le_of_lt hijlt)
          (hC_into_next i hy)
      exact (witness j).cell_disjoint.symm.mono_left hCiUj
    · have hjilt : j < i := by omega
      have hCjUi : C j ⊆ U i :=
        fun y hy => hU_mono (Nat.succ_le_of_lt hjilt)
          (hC_into_next j hy)
      exact (witness i).cell_disjoint.mono_right hCjUi
  have hforward : ∀ i j, i < j →
      Disjoint (Hleft i) (C j) ∧
      Disjoint (Hright i) (C j) := by
    intro i j hij
    have hLeftUj : Hleft i ⊆ U j :=
      fun y hy => hU_mono (Nat.succ_le_of_lt hij)
        (hleft_into_next i hy)
    have hRightUj : Hright i ⊆ U j :=
      fun y hy => hU_mono (Nat.succ_le_of_lt hij)
        (hright_into_next i hy)
    exact ⟨(witness j).cell_disjoint.symm.mono_left hLeftUj,
      (witness j).cell_disjoint.symm.mono_left hRightUj⟩
  let S : LowerTriangularBinaryRepairSequence A k q := {
    anchor := a
    core := x
    leftRepair := Hleft
    rightRepair := Hright
    anchor_strictMono := haStrict
    anchor_mem := fun i => (witness i).anchor_mem
    core_mem := fun i => (witness i).core_mem
    distinct := fun i => (witness i).distinct
    cells_disjoint := hcells
    left_mem := fun i => (witness i).left_mem
    right_mem := fun i => (witness i).right_mem
    left_private := fun i => (witness i).left_private
    right_private := fun i => (witness i).right_private
    forward_disjoint := hforward
  }
  refine ⟨S, ?_⟩
  intro i
  exact (witness i).cell_disjoint.mono_right (hF₀U i)

/-- The recursive binary repair sequence no longer needs a lower-order gap:
any represented fixed predecessor target with recurrent bounded successor
transversals supplies the fresh cells. -/
theorem exists_lowerTriangularBinaryRepairSequence
    {A : Set ℕ} {k q : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hfull :
      HasBoundedFullTranslateDestroyersByAnchor A (k + 1) {q})
    (hqrep : (additiveSupportFamily A (k + 1) q).Nonempty) :
    Nonempty (LowerTriangularBinaryRepairSequence A k q) :=
  exists_lowerTriangularBinaryRepairSequence_of_freshWitnesses
    (nonempty_freshBinaryRepairWitness hbasis hfull hqrep)

/-- Compatibility form retaining the primitive-gap hypotheses.  The
gap-free theorem above shows that only representedness of `q` is needed. -/
theorem exists_lowerTriangularBinaryRepairSequence_over_gap
    {A : Set ℕ} {k q d b : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hfull :
      HasBoundedFullTranslateDestroyersByAnchor A (k + 1) {q})
    (_hbA : b ∈ A)
    (_hqdb : q = d + b)
    (hqrep : (additiveSupportFamily A (k + 1) q).Nonempty)
    (_hgap : additiveSupportFamily A k d = ∅) :
    Nonempty (LowerTriangularBinaryRepairSequence A k q) :=
  exists_lowerTriangularBinaryRepairSequence hbasis hfull hqrep

/-- Finite-label shared-reservoir fusion.

Choose one binary service repair for every `q ∈ Q` and collect all service
cells and anchor-private repairs into one finite set `V`.  A final guard cell
is chosen outside `V`; its core is the selector value in the first block.
An infinite lower-triangular tail is then started beyond the whole first
block, and the selector chooses the core of every tail cell.

Every service repair avoids this one selector.  Removing its translate anchor
therefore gives an order-`k+1` support of the *original label* `q`, not merely
of a moving translate.  Thus all labels in the finite set survive on one
shared infinite reservoir, with no Ramsey thinning and no discarded target
class. -/
theorem finiteTargets_have_sharedBinaryRepairReservoir
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hQ : Q.Nonempty)
    (hfull : ∀ q ∈ Q,
      HasBoundedFullTranslateDestroyersByAnchor A (k + 1) {q})
    (hrep : ∀ q ∈ Q,
      (additiveSupportFamily A (k + 1) q).Nonempty) :
    ∃ K : Set ℕ, ∃ cell : ℕ → Finset ℕ,
      ∃ s : BlockSelector cell,
        K ⊆ A ∧ K.Infinite ∧
        IsFiniteBlockPartition K cell ∧
        ∀ q ∈ Q,
          ∃ E ∈ additiveSupportFamily A (k + 1) q,
            Disjoint (E : Set ℕ) (selectedSet s) := by
  classical
  let q₀ : {q // q ∈ Q} := ⟨hQ.choose, hQ.choose_spec⟩
  let service :
      ∀ q : {q // q ∈ Q},
        FreshBinaryRepairWitness A k q.1 ∅ 0 :=
    fun q => Classical.choice <|
      nonempty_freshBinaryRepairWitness
        hbasis (hfull q.1 q.2) (hrep q.1 q.2) ∅ (by simp) 0
  let serviceCell (q : {q // q ∈ Q}) : Finset ℕ :=
    {(service q).anchor, (service q).core}
  let V : Finset ℕ :=
    Q.attach.biUnion fun q =>
      serviceCell q ∪ (service q).leftRepair
  have hVA : (V : Set ℕ) ⊆ A := by
    intro y hyV
    obtain ⟨q, _hqAttach, hy⟩ := Finset.mem_biUnion.mp hyV
    rcases Finset.mem_union.mp hy with hyCell | hyRepair
    · rcases Finset.mem_insert.mp hyCell with hya | hyc
      · subst y
        exact (service q).anchor_mem
      · have hyc' : y = (service q).core := by simpa using hyc
        subst y
        exact (service q).core_mem
    · exact (service q).left_subset y hyRepair
  let guard : FreshBinaryRepairWitness A k q₀.1 V 0 :=
    Classical.choice <|
      nonempty_freshBinaryRepairWitness
        hbasis (hfull q₀.1 q₀.2) (hrep q₀.1 q₀.2) V hVA 0
  let block₀ : Finset ℕ :=
    V ∪ ({guard.anchor, guard.core} : Finset ℕ)
  have hblock₀A : (block₀ : Set ℕ) ⊆ A := by
    intro y hy
    rcases Finset.mem_union.mp hy with hyV | hyGuard
    · exact hVA hyV
    · rcases Finset.mem_insert.mp hyGuard with hya | hyc
      · subst y
        exact guard.anchor_mem
      · have hyc' : y = guard.core := by simpa using hyc
        subst y
        exact guard.core_mem
  obtain ⟨S, hSblock₀⟩ :=
    exists_lowerTriangularBinaryRepairSequence_avoiding_of_freshWitnesses
      (A := A) (k := k) (q := q₀.1) block₀ hblock₀A
      (nonempty_freshBinaryRepairWitness
        hbasis (hfull q₀.1 q₀.2) (hrep q₀.1 q₀.2))
  let cell : ℕ → Finset ℕ
    | 0 => block₀
    | i + 1 => {S.anchor i, S.core i}
  let K : Set ℕ := {y | ∃ i, y ∈ cell i}
  have hcellNonempty : ∀ i, (cell i).Nonempty := by
    intro i
    cases i with
    | zero =>
        exact ⟨guard.core, by simp [cell, block₀]⟩
    | succ i =>
        exact ⟨S.core i, by simp [cell]⟩
  have hcellDisjoint :
      Pairwise fun i j => Disjoint (cell i) (cell j) := by
    intro i j hij
    cases i with
    | zero =>
        cases j with
        | zero => exact (hij rfl).elim
        | succ j =>
            simpa only [cell] using (hSblock₀ j).symm
    | succ i =>
        cases j with
        | zero =>
            simpa only [cell] using hSblock₀ i
        | succ j =>
            have hij' : i ≠ j := by
              intro heq
              apply hij
              rw [heq]
            simpa only [cell] using S.cells_disjoint hij'
  have hKA : K ⊆ A := by
    rintro y ⟨i, hy⟩
    cases i with
    | zero =>
        exact hblock₀A (by simpa only [cell] using hy)
    | succ i =>
        have hy' :
            y = S.anchor i ∨ y = S.core i := by
          simpa only [cell, Finset.mem_insert, Finset.mem_singleton] using hy
        rcases hy' with rfl | rfl
        · exact S.anchor_mem i
        · exact S.core_mem i
  have hKInfinite : K.Infinite := by
    have hrange :
        Set.range S.anchor ⊆ K := by
      rintro y ⟨i, rfl⟩
      exact ⟨i + 1, by simp [cell]⟩
    exact
      (Set.infinite_range_of_injective
        S.anchor_strictMono.injective).mono hrange
  have P : IsFiniteBlockPartition K cell := by
    refine ⟨hcellNonempty, hcellDisjoint, ?_⟩
    intro y
    rfl
  let s : BlockSelector cell
    | 0 => ⟨guard.core, by simp [cell, block₀]⟩
    | i + 1 => ⟨S.core i, by simp [cell]⟩
  refine ⟨K, cell, s, hKA, hKInfinite, P, ?_⟩
  intro q hqQ
  let q' : {u // u ∈ Q} := ⟨q, hqQ⟩
  have hanchorIn :
      (service q').anchor ∈ (service q').leftRepair := by
    have hinter :
        (service q').anchor ∈
          (service q').leftRepair ∩ serviceCell q' := by
      rw [(service q').left_private]
      simp
    exact (Finset.mem_inter.mp hinter).1
  obtain ⟨E, hERaw, hrepairEq⟩ :=
    additiveSupport_remove_hit_succ
      (A := A) (k := k + 1)
      (m := q + (service q').anchor)
      (x := (service q').anchor)
      (service q').left_mem hanchorIn
  have hER :
      E ∈ additiveSupportFamily A (k + 1) q := by
    have htarget :
        q + (service q').anchor - (service q').anchor = q := by
      omega
    simpa [htarget] using hERaw
  have hrepairV :
      (service q').leftRepair ⊆ V := by
    intro y hy
    apply Finset.mem_biUnion.mpr
    exact ⟨q', by simp, Finset.mem_union_right _ hy⟩
  have hrepairBlock :
      (service q').leftRepair ⊆ block₀ :=
    hrepairV.trans Finset.subset_union_left
  have hrepairDisjoint :
      Disjoint ((service q').leftRepair : Set ℕ)
        (selectedSet s) := by
    rw [Set.disjoint_left]
    intro y hyRepair hySelected
    obtain ⟨i, rfl⟩ := hySelected
    cases i with
    | zero =>
        change guard.core ∈
          (service q').leftRepair at hyRepair
        exact Finset.disjoint_left.mp guard.cell_disjoint
          (by simp) (hrepairV hyRepair)
    | succ i =>
        change S.core i ∈
          (service q').leftRepair at hyRepair
        exact Finset.disjoint_left.mp (hSblock₀ i)
          (by simp) (hrepairBlock hyRepair)
  refine ⟨E, hER, ?_⟩
  rw [Set.disjoint_left]
  intro y hyE hySelected
  apply Set.disjoint_left.mp hrepairDisjoint
    (Finset.mem_coe.mpr ?_) hySelected
  rw [hrepairEq]
  exact Finset.mem_insert_of_mem (Finset.mem_coe.mp hyE)

/-- Concrete quantifier-order counterconfiguration.

At additive order one on `ℕ`, strong infinite deletion holds.  Nevertheless,
after *any particular* finite target set `Q` is revealed, one can build a
`Q`-dependent finite-block partition and a selector preserving every target
in `Q`: put all numbers through `sum Q + 1` in block zero, select its largest
point, and make the remaining tail singleton blocks.

Thus a construction whose partition is allowed to depend on the destruction
certificate cannot by itself contradict strong deletion.  The successful
finite-label reservoir theorem above must still be fused into one partition
chosen before the certificate is returned. -/
theorem strongDeletion_coexists_with_targetDependentFiniteSurvival_univ_one :
    StrongInfiniteDeletion
        (additiveSupportFamily (Set.univ : Set ℕ) 1) Set.univ ∧
      ∀ Q : Finset ℕ,
        ∃ F : ℕ → Finset ℕ, ∃ _P : IsFiniteBlockPartition Set.univ F,
          ∃ s : BlockSelector F,
            ∀ q ∈ Q,
              ∃ E ∈ additiveSupportFamily (Set.univ : Set ℕ) 1 q,
                Disjoint (E : Set ℕ) (selectedSet s) := by
  classical
  refine ⟨strongInfiniteDeletion_additive_univ_one, ?_⟩
  intro Q
  let M := Q.sum id + 1
  let F : ℕ → Finset ℕ
    | 0 => Finset.range (M + 1)
    | i + 1 => {M + i + 1}
  have hFnonempty : ∀ i, (F i).Nonempty := by
    intro i
    cases i with
    | zero =>
        exact ⟨M, by simp [F]⟩
    | succ i =>
        exact ⟨M + i + 1, by simp [F]⟩
  have hFdisjoint : Pairwise fun i j => Disjoint (F i) (F j) := by
    intro i j hij
    cases i with
    | zero =>
        cases j with
        | zero => exact (hij rfl).elim
        | succ j =>
            rw [Finset.disjoint_left]
            intro y hy0 hyj
            have hylt : y < M + 1 := by
              simpa only [F, Finset.mem_range] using hy0
            have hyeq : y = M + j + 1 := by
              simpa only [F, Finset.mem_singleton] using hyj
            omega
    | succ i =>
        cases j with
        | zero =>
            rw [Finset.disjoint_left]
            intro y hyi hy0
            have hyeq : y = M + i + 1 := by
              simpa only [F, Finset.mem_singleton] using hyi
            have hylt : y < M + 1 := by
              simpa only [F, Finset.mem_range] using hy0
            omega
        | succ j =>
            rw [Finset.disjoint_left]
            intro y hyi hyj
            have hyiEq : y = M + i + 1 := by
              simpa only [F, Finset.mem_singleton] using hyi
            have hyjEq : y = M + j + 1 := by
              simpa only [F, Finset.mem_singleton] using hyj
            apply hij
            congr
            omega
  have P : IsFiniteBlockPartition (Set.univ : Set ℕ) F := by
    refine ⟨hFnonempty, hFdisjoint, ?_⟩
    intro y
    simp only [Set.mem_univ, true_iff]
    by_cases hyM : y ≤ M
    · exact ⟨0, by simp [F, hyM]⟩
    · refine ⟨y - M, ?_⟩
      have hpos : 0 < y - M := Nat.sub_pos_of_lt (lt_of_not_ge hyM)
      obtain ⟨i, hi⟩ : ∃ i, y - M = i + 1 :=
        ⟨y - M - 1, by omega⟩
      have hyEq : y = M + i + 1 := by omega
      rw [hi]
      simpa [F, hyEq]
  let s : BlockSelector F
    | 0 => ⟨M, by simp [F]⟩
    | i + 1 => ⟨M + i + 1, by simp [F]⟩
  refine ⟨F, P, s, ?_⟩
  intro q hqQ
  have hqsum : q ≤ Q.sum id :=
    Finset.single_le_sum
      (s := Q) (f := id) (fun _ _ => Nat.zero_le _) hqQ
  let v : Fin 1 → Fin (q + 1) :=
    fun _ => ⟨q, Nat.lt_succ_self q⟩
  let E := tupleSupport v
  have hER :
      E ∈ additiveSupportFamily (Set.univ : Set ℕ) 1 q := by
    apply mem_additiveSupportFamily_iff.mpr
    refine ⟨v, by simp, ?_, rfl⟩
    simp [v]
  refine ⟨E, hER, ?_⟩
  rw [Set.disjoint_left]
  intro y hyE hySelected
  have hyq : y ≤ q :=
    additiveSupportFamily_supportsBounded
      (Set.univ : Set ℕ) 1 q E hER y (Finset.mem_coe.mp hyE)
  obtain ⟨i, rfl⟩ := hySelected
  cases i with
  | zero =>
      change M ≤ q at hyq
      dsimp only [M] at hyq
      omega
  | succ i =>
      change M + i + 1 ≤ q at hyq
      dsimp only [M] at hyq
      omega

/-- Any finite deletion which destroys a represented successor-order target
contains a summand whose removal leaves a represented target one order lower.

This is the additive content of finite-prefix destruction: a destructive
prefix cannot remain an opaque transversal.  It exposes a concrete difference
`q - d` represented at the preceding order. -/
theorem finiteDestroyer_has_lowerOrderDifference
    {A : Set ℕ} {k q : ℕ} {D : Finset ℕ}
    (hrepresented :
      (additiveSupportFamily A (k + 1) q).Nonempty)
    (hdestroy :
      DestroysAt
        (additiveSupportFamily A (k + 1)) (D : Set ℕ) q) :
    ∃ d ∈ D, d ≤ q ∧
      (additiveSupportFamily A k (q - d)).Nonempty := by
  obtain ⟨E, hER⟩ := hrepresented
  obtain ⟨d, hdE, hdD⟩ :=
    Set.not_disjoint_iff.mp (hdestroy E hER)
  have hdq : d ≤ q :=
    additiveSupportFamily_supportsBounded
      A (k + 1) q E hER d hdE
  obtain ⟨H, hHR, _hEeq⟩ :=
    additiveSupport_remove_hit_succ hER hdE
  exact ⟨d, Finset.mem_coe.mp hdD, hdq, H, hHR⟩

/-- Destruction by an infinite block selector is always witnessed by a
finite subset of that same selector: retain only the selected coordinates of
blocks which contain a support vertex at the target. -/
theorem exists_finiteSelectedDestroyer_of_destroysAt
    {A : Set ℕ} {R : SupportFamily}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {q : ℕ}
    (hdestroy : DestroysAt R (selectedSet s) q) :
    ∃ D : Finset ℕ,
      (D : Set ℕ) ⊆ selectedSet s ∧
      D.card ≤ (supportVertices R q).card ∧
      DestroysAt R (D : Set ℕ) q := by
  classical
  let I : Finset ℕ :=
    (supportVertices R q).image (blockIndex P)
  let D : Finset ℕ :=
    I.image fun i => (s i).1
  have hDselected : (D : Set ℕ) ⊆ selectedSet s := by
    intro x hxD
    obtain ⟨i, _hiI, hix⟩ := Finset.mem_image.mp hxD
    exact ⟨i, hix⟩
  have hDcard : D.card ≤ (supportVertices R q).card := by
    calc
      D.card ≤ I.card := Finset.card_image_le
      _ ≤ (supportVertices R q).card := Finset.card_image_le
  refine ⟨D, hDselected, hDcard, ?_⟩
  intro E hER
  obtain ⟨x, hxE, hxSelected⟩ :=
    Set.not_disjoint_iff.mp (hdestroy E hER)
  have hxVertex : x ∈ supportVertices R q :=
    Finset.mem_biUnion.mpr ⟨E, hER, hxE⟩
  have hxIndex : blockIndex P x ∈ I :=
    Finset.mem_image.mpr ⟨x, hxVertex, rfl⟩
  have hxEq : (s (blockIndex P x)).1 = x :=
    (P.mem_selectedSet_iff s).mp hxSelected
  apply Set.not_disjoint_iff.mpr
  refine ⟨x, hxE, Finset.mem_coe.mpr ?_⟩
  exact Finset.mem_image.mpr
    ⟨blockIndex P x, hxIndex, hxEq⟩

/-- The canonical finite part of a selector relevant to one target uses one
point for each block which occurs in the support hypergraph at that target.

This sharpens `exists_finiteSelectedDestroyer_of_destroysAt`: the cardinal
bound is the number of active block coordinates, rather than the number of
support vertices. -/
theorem exists_activeBlockSelectedDestroyer_of_destroysAt
    {A : Set ℕ} {R : SupportFamily}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {q : ℕ}
    (hdestroy : DestroysAt R (selectedSet s) q) :
    ∃ D : Finset ℕ,
      (D : Set ℕ) ⊆ selectedSet s ∧
      D.card ≤
        ((supportVertices R q).image (blockIndex P)).card ∧
      DestroysAt R (D : Set ℕ) q := by
  classical
  let I : Finset ℕ :=
    (supportVertices R q).image (blockIndex P)
  let D : Finset ℕ :=
    I.image fun i => (s i).1
  have hDselected : (D : Set ℕ) ⊆ selectedSet s := by
    intro x hxD
    obtain ⟨i, _hiI, hix⟩ := Finset.mem_image.mp hxD
    exact ⟨i, hix⟩
  have hDcard : D.card ≤ I.card := Finset.card_image_le
  refine ⟨D, hDselected, by simpa only [I] using hDcard, ?_⟩
  intro E hER
  obtain ⟨x, hxE, hxSelected⟩ :=
    Set.not_disjoint_iff.mp (hdestroy E hER)
  have hxVertex : x ∈ supportVertices R q :=
    Finset.mem_biUnion.mpr ⟨E, hER, hxE⟩
  have hxIndex : blockIndex P x ∈ I :=
    Finset.mem_image.mpr ⟨x, hxVertex, rfl⟩
  have hxEq : (s (blockIndex P x)).1 = x :=
    (P.mem_selectedSet_iff s).mp hxSelected
  apply Set.not_disjoint_iff.mpr
  refine ⟨x, hxE, Finset.mem_coe.mpr ?_⟩
  exact Finset.mem_image.mpr
    ⟨blockIndex P x, hxIndex, hxEq⟩

/-- A lower-order gap point is completely absent from every successor-order
support at the translated target.  If `b` occurred, removing that occurrence
would represent `q-b` one order lower. -/
theorem lowerOrderGap_point_avoids_successorSupports
    {A : Set ℕ} {k q b : ℕ}
    (hgap : additiveSupportFamily A k (q - b) = ∅) :
    ∀ E ∈ additiveSupportFamily A (k + 1) q, b ∉ E := by
  intro E hER hbE
  obtain ⟨H, hHR, _hEeq⟩ :=
    additiveSupport_remove_hit_succ hER hbE
  rw [hgap] at hHR
  simpa using hHR

/-- Hypergraph form of a safe block replacement.  If `b` belongs to no
support at the target, it may replace any private hit of an
inclusion-minimal destroyer. -/
theorem IsInclusionMinimalDestroyer.swap_hit_for_avoidedPoint_repairs
    {R : SupportFamily} {D : Finset ℕ} {q d b : ℕ}
    (hminimal : IsInclusionMinimalDestroyer R D q)
    (hdD : d ∈ D)
    (havoid : ∀ E ∈ R q, b ∉ E) :
    ¬ DestroysAt R
      (((D.erase d ∪ {b} : Finset ℕ) : Set ℕ)) q := by
  apply hminimal.exists_swapRepair hdD
  intro E hER _hEunique
  apply Finset.disjoint_left.mpr
  intro x hxE hxb
  have hxbEq : x = b := by simpa using hxb
  subst x
  exact havoid E hER hxE

/-- An inclusion-minimal destroyer has at most as many vertices as there are
supports at its target.  Its private support at each deleted vertex gives an
injection from destroyer vertices to supports. -/
theorem IsInclusionMinimalDestroyer.card_le_supportFamily
    {R : SupportFamily} {D : Finset ℕ} {q : ℕ}
    (hminimal : IsInclusionMinimalDestroyer R D q) :
    D.card ≤ (R q).card := by
  classical
  let privateSupport :
      ∀ d : {x // x ∈ D}, {E // E ∈ R q} := fun d =>
    ⟨(hminimal.exists_uniqueHitSupport d.2).choose,
      (hminimal.exists_uniqueHitSupport d.2).choose_spec.1⟩
  have hprivate :
      ∀ d : {x // x ∈ D},
        (privateSupport d).1 ∩ D = {d.1} := by
    intro d
    exact (hminimal.exists_uniqueHitSupport d.2).choose_spec.2
  have hinjective : Function.Injective privateSupport := by
    intro d e hde
    apply Subtype.ext
    have hsupport :
        (privateSupport d).1 = (privateSupport e).1 :=
      congrArg Subtype.val hde
    have hsingle : ({d.1} : Finset ℕ) = {e.1} := by
      rw [← hprivate d, ← hprivate e, hsupport]
    simpa using hsingle
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective privateSupport hinjective

/-- Exact local repair supplied by the lower-gap horn.

For an inclusion-minimal finite destroyer, erase any private hit `d` and
delete a lower-gap point `b` instead.  The private repair support avoids the
rest of the destroyer by minimality and avoids `b` because `q-b` is a gap, so
the swapped deletion no longer destroys `q`. -/
theorem IsInclusionMinimalDestroyer.swap_hit_for_lowerGap_repairs
    {A : Set ℕ} {k q b d : ℕ} {D : Finset ℕ}
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hdD : d ∈ D)
    (hgap : additiveSupportFamily A k (q - b) = ∅) :
    ¬ DestroysAt
      (additiveSupportFamily A (k + 1))
      (((D.erase d ∪ {b} : Finset ℕ) : Set ℕ)) q := by
  exact hminimal.swap_hit_for_avoidedPoint_repairs hdD
    (lowerOrderGap_point_avoids_successorSupports hgap)

/-- Block-aligned safe-swap versus coherent-difference growth.

Let `D` be an inclusion-minimal order-`k+1` destroyer contained in one
selector, and let `d` be its active value in block `i`.  Use every other
point of that same block as an external test anchor.

If one alternative is larger than `q`, or if `q-b` is an order-`k` gap,
then `b` is absent from every support of `q` and swapping `d` for `b`
repairs the target.  Otherwise every block alternative represents `q-b`.
When the active block is large enough, the external-anchor incidence bound
forces more than `r` order-`k` supports at `q-x` for some `x ∈ D`.

Thus the gap witness is now genuinely block-aligned; failure of alignment
has a quantitative matching-growth cost. -/
theorem positiveOrder_minimalDestroyer_activeBlock_safeSwap_or_differenceGrowth
    {A : Set ℕ} {k q r : ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D : Finset ℕ} {i : ℕ}
    (hk : 0 < k)
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hDselected : (D : Set ℕ) ⊆ selectedSet s)
    (hactive : (s i).1 ∈ D)
    (hlarge :
      D.card * (k * r) <
        ((F i).erase (s i).1).card) :
    (∃ b ∈ (F i).erase (s i).1,
        ¬ DestroysAt
          (additiveSupportFamily A (k + 1))
          (((D.erase (s i).1 ∪ {b} : Finset ℕ) : Set ℕ)) q) ∨
      ∃ x ∈ D, x ≤ q ∧
        r < (additiveSupportFamily A k (q - x)).card := by
  classical
  let B : Finset ℕ := (F i).erase (s i).1
  have hBA : ∀ b ∈ B, b ∈ A := by
    intro b hbB
    exact (P.mem_iff b).2
      ⟨i, (Finset.mem_erase.mp hbB).2⟩
  have hBD : Disjoint B D := by
    rw [Finset.disjoint_left]
    intro b hbB hbD
    obtain ⟨j, hbj⟩ :=
      hDselected (Finset.mem_coe.mpr hbD)
    have hbFi : b ∈ F i := (Finset.mem_erase.mp hbB).2
    have hbne : b ≠ (s i).1 := (Finset.mem_erase.mp hbB).1
    by_cases hji : j = i
    · subst j
      exact hbne hbj.symm
    · have hbFj : b ∈ F j := by
        rw [← hbj]
        exact (s j).2
      exact Finset.disjoint_left.mp (P.disjoint hji)
        hbFj hbFi
  by_cases hlargePoint : ∃ b ∈ B, q < b
  · left
    obtain ⟨b, hbB, hqb⟩ := hlargePoint
    refine ⟨b, hbB,
      hminimal.swap_hit_for_avoidedPoint_repairs hactive ?_⟩
    intro E hER hbE
    have hbq :=
      additiveSupportFamily_supportsBounded
        A (k + 1) q E hER b hbE
    omega
  by_cases hgap :
      ∃ b ∈ B, additiveSupportFamily A k (q - b) = ∅
  · left
    obtain ⟨b, hbB, hbGap⟩ := hgap
    exact ⟨b, hbB,
      hminimal.swap_hit_for_lowerGap_repairs hactive hbGap⟩
  · right
    have hble : ∀ b ∈ B, b ≤ q := by
      intro b hbB
      by_contra hbq
      exact hlargePoint ⟨b, hbB, Nat.lt_of_not_ge hbq⟩
    have hrep :
        ∀ b ∈ B,
          (additiveSupportFamily A k (q - b)).Nonempty := by
      intro b hbB
      rw [Finset.nonempty_iff_ne_empty]
      intro hbEmpty
      exact hgap ⟨b, hbB, hbEmpty⟩
    cases k with
    | zero => omega
    | succ j =>
      obtain ⟨x, hxD, hxq, hxlarge⟩ :=
        large_externalAnchorSet_forces_supportGrowth_succ
          (k := j) hminimal.1 hBA hBD hble hrep (by
            simpa [B, Nat.mul_assoc] using hlarge)
      exact ⟨x, hxD, hxq, hxlarge⟩

/-- Protected-union form of the block-aligned fork.

Only same-block alternatives outside `U` are used as test anchors.  Thus the
safe horn already avoids every support stored in `U`; if there are too many
such alternatives for the destroyer-incidence budget, failure of a safe
swap again forces coherent lower-order support growth. -/
theorem positiveOrder_minimalDestroyer_activeBlock_safeSwap_avoiding_or_differenceGrowth
    {A : Set ℕ} {k q r : ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D U : Finset ℕ} {i : ℕ}
    (hk : 0 < k)
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hDselected : (D : Set ℕ) ⊆ selectedSet s)
    (hactive : (s i).1 ∈ D)
    (hlarge :
      D.card * (k * r) <
        (((F i).erase (s i).1) \ U).card) :
    (∃ b ∈ (F i).erase (s i).1, b ∉ U ∧
        ¬ DestroysAt
          (additiveSupportFamily A (k + 1))
          (((D.erase (s i).1 ∪ {b} : Finset ℕ) : Set ℕ)) q) ∨
      ∃ x ∈ D, x ≤ q ∧
        r < (additiveSupportFamily A k (q - x)).card := by
  classical
  let B : Finset ℕ := ((F i).erase (s i).1) \ U
  have hBA : ∀ b ∈ B, b ∈ A := by
    intro b hbB
    exact (P.mem_iff b).2
      ⟨i, (Finset.mem_erase.mp
        (Finset.mem_sdiff.mp hbB).1).2⟩
  have hBD : Disjoint B D := by
    rw [Finset.disjoint_left]
    intro b hbB hbD
    obtain ⟨j, hbj⟩ :=
      hDselected (Finset.mem_coe.mpr hbD)
    have hbErase := (Finset.mem_sdiff.mp hbB).1
    have hbFi : b ∈ F i := (Finset.mem_erase.mp hbErase).2
    have hbne : b ≠ (s i).1 := (Finset.mem_erase.mp hbErase).1
    by_cases hji : j = i
    · subst j
      exact hbne hbj.symm
    · have hbFj : b ∈ F j := by
        rw [← hbj]
        exact (s j).2
      exact Finset.disjoint_left.mp (P.disjoint hji)
        hbFj hbFi
  by_cases hlargePoint : ∃ b ∈ B, q < b
  · left
    obtain ⟨b, hbB, hqb⟩ := hlargePoint
    have hbParts := Finset.mem_sdiff.mp hbB
    refine ⟨b, hbParts.1, hbParts.2,
      hminimal.swap_hit_for_avoidedPoint_repairs hactive ?_⟩
    intro E hER hbE
    have hbq :=
      additiveSupportFamily_supportsBounded
        A (k + 1) q E hER b hbE
    omega
  by_cases hgap :
      ∃ b ∈ B, additiveSupportFamily A k (q - b) = ∅
  · left
    obtain ⟨b, hbB, hbGap⟩ := hgap
    have hbParts := Finset.mem_sdiff.mp hbB
    exact ⟨b, hbParts.1, hbParts.2,
      hminimal.swap_hit_for_lowerGap_repairs hactive hbGap⟩
  · right
    have hble : ∀ b ∈ B, b ≤ q := by
      intro b hbB
      by_contra hbq
      exact hlargePoint ⟨b, hbB, Nat.lt_of_not_ge hbq⟩
    have hrep :
        ∀ b ∈ B,
          (additiveSupportFamily A k (q - b)).Nonempty := by
      intro b hbB
      rw [Finset.nonempty_iff_ne_empty]
      intro hbEmpty
      exact hgap ⟨b, hbB, hbEmpty⟩
    cases k with
    | zero => omega
    | succ j =>
      obtain ⟨x, hxD, hxq, hxlarge⟩ :=
        large_externalAnchorSet_forces_supportGrowth_succ
          (k := j) hminimal.1 hBA hBD hble hrep (by
            simpa [B, Nat.mul_assoc] using hlarge)
      exact ⟨x, hxD, hxq, hxlarge⟩

/-- Reservoir-relative version of the protected active-block fork.  The
block partition may cover only `C ⊆ A`; this is the form needed by a
constructed infinite deletion reservoir. -/
theorem positiveOrder_minimalDestroyer_activeBlock_safeSwap_avoiding_or_differenceGrowth_onReservoir
    {A C : Set ℕ} {k q r : ℕ}
    {F : ℕ → Finset ℕ} (hCA : C ⊆ A)
    (P : IsFiniteBlockPartition C F)
    (s : BlockSelector F) {D U : Finset ℕ} {i : ℕ}
    (hk : 0 < k)
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hDselected : (D : Set ℕ) ⊆ selectedSet s)
    (hactive : (s i).1 ∈ D)
    (hlarge :
      D.card * (k * r) <
        (((F i).erase (s i).1) \ U).card) :
    (∃ b ∈ (F i).erase (s i).1, b ∉ U ∧
        ¬ DestroysAt
          (additiveSupportFamily A (k + 1))
          (((D.erase (s i).1 ∪ {b} : Finset ℕ) : Set ℕ)) q) ∨
      ∃ x ∈ D, x ≤ q ∧
        r < (additiveSupportFamily A k (q - x)).card := by
  classical
  let B : Finset ℕ := ((F i).erase (s i).1) \ U
  have hBA : ∀ b ∈ B, b ∈ A := by
    intro b hbB
    apply hCA
    exact (P.mem_iff b).2
      ⟨i, (Finset.mem_erase.mp
        (Finset.mem_sdiff.mp hbB).1).2⟩
  have hBD : Disjoint B D := by
    rw [Finset.disjoint_left]
    intro b hbB hbD
    obtain ⟨j, hbj⟩ :=
      hDselected (Finset.mem_coe.mpr hbD)
    have hbErase := (Finset.mem_sdiff.mp hbB).1
    have hbFi : b ∈ F i := (Finset.mem_erase.mp hbErase).2
    have hbne : b ≠ (s i).1 := (Finset.mem_erase.mp hbErase).1
    by_cases hji : j = i
    · subst j
      exact hbne hbj.symm
    · have hbFj : b ∈ F j := by
        rw [← hbj]
        exact (s j).2
      exact Finset.disjoint_left.mp (P.disjoint hji)
        hbFj hbFi
  by_cases hlargePoint : ∃ b ∈ B, q < b
  · left
    obtain ⟨b, hbB, hqb⟩ := hlargePoint
    have hbParts := Finset.mem_sdiff.mp hbB
    refine ⟨b, hbParts.1, hbParts.2,
      hminimal.swap_hit_for_avoidedPoint_repairs hactive ?_⟩
    intro E hER hbE
    have hbq :=
      additiveSupportFamily_supportsBounded
        A (k + 1) q E hER b hbE
    omega
  by_cases hgap :
      ∃ b ∈ B, additiveSupportFamily A k (q - b) = ∅
  · left
    obtain ⟨b, hbB, hbGap⟩ := hgap
    have hbParts := Finset.mem_sdiff.mp hbB
    exact ⟨b, hbParts.1, hbParts.2,
      hminimal.swap_hit_for_lowerGap_repairs hactive hbGap⟩
  · right
    have hble : ∀ b ∈ B, b ≤ q := by
      intro b hbB
      by_contra hbq
      exact hlargePoint ⟨b, hbB, Nat.lt_of_not_ge hbq⟩
    have hrep :
        ∀ b ∈ B,
          (additiveSupportFamily A k (q - b)).Nonempty := by
      intro b hbB
      rw [Finset.nonempty_iff_ne_empty]
      intro hbEmpty
      exact hgap ⟨b, hbB, hbEmpty⟩
    cases k with
    | zero => omega
    | succ j =>
      obtain ⟨x, hxD, hxq, hxlarge⟩ :=
        large_externalAnchorSet_forces_supportGrowth_succ
          (k := j) hminimal.1 hBA hBD hble hrep (by
            simpa [B, Nat.mul_assoc] using hlarge)
      exact ⟨x, hxD, hxq, hxlarge⟩

/-- A finite same-block safe swap extends to a genuine selector repair.

Take a support `E` surviving the swapped minimal destroyer.  Every block has
more than `k+1` points while `E` has at most `k+1`, so every remaining block
has a choice outside `E`.  Keep the still-active old choices, put `b` in the
repaired block, and choose outside `E` everywhere else.

The resulting full selector preserves `q`, and it records the repaired
coordinate exactly. -/
theorem blockAlignedSafeSwap_extends_to_selectorSurvival
    {A : Set ℕ} {k q : ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D : Finset ℕ} {i b : ℕ}
    (hbBlock : b ∈ (F i).erase (s i).1)
    (hrepair :
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1))
        (((D.erase (s i).1 ∪ {b} : Finset ℕ) : Set ℕ)) q)
    (hblocks : ∀ j, k + 1 < (F j).card) :
    ∃ t : BlockSelector F,
      (t i).1 = b ∧
      (∀ j, j ≠ i → (s j).1 ∈ D.erase (s i).1 →
        (t j).1 = (s j).1) ∧
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1))
        (selectedSet t) q := by
  classical
  obtain ⟨E, hER, hEswap⟩ :=
    not_destroysAt_iff.mp hrepair
  have hEcard : E.card ≤ k + 1 :=
    additiveSupportFamily_cardAtMost A (k + 1) q E hER
  have houtside : ∀ j, (F j \ E).Nonempty := by
    intro j
    by_contra hempty
    have hsubset : F j ⊆ E := by
      intro x hxF
      by_contra hxE
      exact hempty ⟨x, Finset.mem_sdiff.mpr ⟨hxF, hxE⟩⟩
    have hcard := Finset.card_le_card hsubset
    have hlarge := hblocks j
    omega
  choose outside houtsideSpec using houtside
  let t : BlockSelector F := fun j =>
    if hji : j = i then
      ⟨b, by
        subst j
        exact (Finset.mem_erase.mp hbBlock).2⟩
    else if hjD : (s j).1 ∈ D.erase (s i).1 then
      s j
    else
      ⟨outside j, (Finset.mem_sdiff.mp (houtsideSpec j)).1⟩
  have hti : (t i).1 = b := by
    dsimp [t]
    rw [dif_pos rfl]
  have hkeep :
      ∀ j, j ≠ i → (s j).1 ∈ D.erase (s i).1 →
        (t j).1 = (s j).1 := by
    intro j hji hjD
    dsimp [t]
    rw [dif_neg hji, if_pos hjD]
  refine ⟨t, hti, hkeep, ?_⟩
  apply not_destroysAt_iff.mpr
  refine ⟨E, hER, ?_⟩
  rw [Set.disjoint_left]
  intro x hxE hxSelected
  obtain ⟨j, hjx⟩ := hxSelected
  by_cases hji : j = i
  · have htx : (t j).1 = b := by
      subst j
      exact hti
    have hxb : x = b := hjx.symm.trans htx
    apply Set.disjoint_left.mp hEswap hxE
    exact Finset.mem_coe.mpr (by
      rw [hxb]
      exact Finset.mem_union_right _
        (Finset.mem_singleton_self b))
  by_cases hjD : (s j).1 ∈ D.erase (s i).1
  · have htx : (t j).1 = (s j).1 := hkeep j hji hjD
    have hxs : x = (s j).1 := hjx.symm.trans htx
    apply Set.disjoint_left.mp hEswap hxE
    exact Finset.mem_coe.mpr (by
      rw [hxs]
      exact Finset.mem_union_left _ hjD)
  · have htOutside :
        (t j).1 = outside j := by
      dsimp [t]
      rw [dif_neg hji, if_neg hjD]
    have hxOutside : x = outside j := hjx.symm.trans htOutside
    apply (Finset.mem_sdiff.mp (houtsideSpec j)).2
    rw [← hxOutside]
    exact hxE

/-- A lower-order gap gives a genuine two-block selector repair even when
the gap point is not in the damaged summand's block.

Choose a support `E` witnessing the finite swap
`D.erase d ∪ {b}`.  In the block containing `b`, select `b`.  Keep every
old selected value in `D.erase d`; in all remaining blocks choose outside
`E`.  In particular, unless `b` already lies in the block containing `d`,
that damaged block is rerouted outside `E`.  Since `E` has at most `k+1`
vertices, blocks of size greater than `k+1` suffice. -/
theorem lowerGapRepair_extends_to_twoBlockSelectorSurvival
    {A : Set ℕ} {k q b d : ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D : Finset ℕ}
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hdD : d ∈ D)
    (hbA : b ∈ A)
    (hgap : additiveSupportFamily A k (q - b) = ∅)
    (hblocks : ∀ j, k + 1 < (F j).card) :
    ∃ t : BlockSelector F,
      (t (blockIndex P b)).1 = b ∧
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1))
        (selectedSet t) q := by
  classical
  have hrepair :
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1))
        (((D.erase d ∪ {b} : Finset ℕ) : Set ℕ)) q :=
    hminimal.swap_hit_for_lowerGap_repairs hdD hgap
  obtain ⟨E, hER, hEswap⟩ :=
    not_destroysAt_iff.mp hrepair
  have hEcard : E.card ≤ k + 1 :=
    additiveSupportFamily_cardAtMost A (k + 1) q E hER
  have houtside : ∀ j, (F j \ E).Nonempty := by
    intro j
    by_contra hempty
    have hsubset : F j ⊆ E := by
      intro x hxF
      by_contra hxE
      exact hempty ⟨x, Finset.mem_sdiff.mpr ⟨hxF, hxE⟩⟩
    have hcard := Finset.card_le_card hsubset
    have hlarge := hblocks j
    omega
  choose outside houtsideSpec using houtside
  let j := blockIndex P b
  have hbBlock : b ∈ F j :=
    P.mem_blockIndex hbA
  let t : BlockSelector F := fun ℓ =>
    if hℓj : ℓ = j then
      ⟨b, by
        subst ℓ
        exact hbBlock⟩
    else if hℓD : (s ℓ).1 ∈ D.erase d then
      s ℓ
    else
      ⟨outside ℓ, (Finset.mem_sdiff.mp (houtsideSpec ℓ)).1⟩
  have htj : (t j).1 = b := by
    dsimp [t]
    rw [dif_pos rfl]
  refine ⟨t, htj, ?_⟩
  apply not_destroysAt_iff.mpr
  refine ⟨E, hER, ?_⟩
  rw [Set.disjoint_left]
  intro x hxE hxSelected
  obtain ⟨ℓ, hℓx⟩ := hxSelected
  by_cases hℓj : ℓ = j
  · have htx : (t ℓ).1 = b := by
      subst ℓ
      exact htj
    have hxb : x = b := hℓx.symm.trans htx
    apply Set.disjoint_left.mp hEswap hxE
    exact Finset.mem_coe.mpr (by
      rw [hxb]
      exact Finset.mem_union_right _
        (Finset.mem_singleton_self b))
  by_cases hℓD : (s ℓ).1 ∈ D.erase d
  · have htx : (t ℓ).1 = (s ℓ).1 := by
      dsimp [t]
      rw [dif_neg hℓj, if_pos hℓD]
    have hxs : x = (s ℓ).1 := hℓx.symm.trans htx
    apply Set.disjoint_left.mp hEswap hxE
    exact Finset.mem_coe.mpr (by
      rw [hxs]
      exact Finset.mem_union_left _ hℓD)
  · have htx : (t ℓ).1 = outside ℓ := by
      dsimp [t]
      rw [dif_neg hℓj, if_neg hℓD]
    have hxOutside : x = outside ℓ := hℓx.symm.trans htx
    apply (Finset.mem_sdiff.mp (houtsideSpec ℓ)).2
    rw [← hxOutside]
    exact hxE

/-- Protected completion of a lower-gap repair, with finite old-block
exceptions.

The gap point `b` is selected in its actual block and is assumed outside the
protected union `U`.  Every other selected coordinate which meets the repair
support is rerouted outside `U ∪ E` when its block is contemporary.  An old
hit outside the block already replaced by `b` is the only obstruction and is
returned together with the unchanged repair support. -/
theorem lowerGapRepairWitness_extends_protected_or_oldCollision
    {A : Set ℕ} {k q b : ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D U J E : Finset ℕ}
    (hbA : b ∈ A)
    (hbU : b ∉ U)
    (hUselected : Disjoint (U : Set ℕ) (selectedSet s))
    (hER : E ∈ additiveSupportFamily A (k + 1) q)
    (hEswap : Disjoint (E : Set ℕ)
      (((D ∪ {b} : Finset ℕ) : Set ℕ)))
    (hcontemporary :
      ∀ j, j ∉ J → U.card + (k + 1) < (F j).card) :
    (∃ t : BlockSelector F,
        Disjoint (U : Set ℕ) (selectedSet t) ∧
        ¬ DestroysAt
          (additiveSupportFamily A (k + 1))
          (selectedSet t) q) ∨
      ∃ j ∈ J, (s j).1 ∈ E := by
  classical
  let jb := blockIndex P b
  have hbBlock : b ∈ F jb :=
    P.mem_blockIndex hbA
  have hEcard : E.card ≤ k + 1 :=
    additiveSupportFamily_cardAtMost A (k + 1) q E hER
  by_cases holdHit :
      ∃ j ∈ J, j ≠ jb ∧ (s j).1 ∈ E
  · right
    obtain ⟨j, hjJ, _hjjb, hsjE⟩ := holdHit
    exact ⟨j, hjJ, hsjE⟩
  · left
    let W : Finset ℕ := U ∪ E
    have hWcard : W.card ≤ U.card + (k + 1) := by
      calc
        W.card ≤ U.card + E.card := by
          simpa only [W] using Finset.card_union_le U E
        _ ≤ U.card + (k + 1) :=
          Nat.add_le_add_left hEcard U.card
    have houtside :
        ∀ j, j ∉ J → (F j \ W).Nonempty := by
      intro j hjJ
      by_contra hempty
      have hsubset : F j ⊆ W := by
        intro x hxF
        by_contra hxW
        exact hempty
          ⟨x, Finset.mem_sdiff.mpr ⟨hxF, hxW⟩⟩
      have hcard := Finset.card_le_card hsubset
      have hlarge := hcontemporary j hjJ
      omega
    choose outside houtsideSpec using houtside
    let alt : BlockSelector F := fun j =>
      if hjJ : j ∈ J then
        s j
      else
        ⟨outside j hjJ,
          (Finset.mem_sdiff.mp (houtsideSpec j hjJ)).1⟩
    let t : BlockSelector F := fun j =>
      if hjb : j = jb then
        ⟨b, by
          subst j
          exact hbBlock⟩
      else if hsjE : (s j).1 ∈ E then
        alt j
      else
        s j
    have htjb : (t jb).1 = b := by
      dsimp [t]
      rw [dif_pos rfl]
    have hmissKeep :
        ∀ j, j ≠ jb → (s j).1 ∉ E →
          (t j).1 = (s j).1 := by
      intro j hjjb hsjE
      dsimp [t]
      rw [dif_neg hjjb, if_neg hsjE]
    have hUavoid : Disjoint (U : Set ℕ) (selectedSet t) := by
      rw [Set.disjoint_left]
      intro x hxU hxSelected
      obtain ⟨j, hjx⟩ := hxSelected
      by_cases hjjb : j = jb
      · have htx : (t j).1 = b := by
          subst j
          exact htjb
        have hxb : x = b := hjx.symm.trans htx
        exact hbU (hxb ▸ Finset.mem_coe.mp hxU)
      by_cases hsjE : (s j).1 ∈ E
      · have hjNew : j ∉ J := by
          intro hjJ
          exact holdHit ⟨j, hjJ, hjjb, hsjE⟩
        have htx :
            (t j).1 = outside j hjNew := by
          dsimp [t]
          rw [dif_neg hjjb, if_pos hsjE]
          dsimp [alt]
          rw [dif_neg hjNew]
        have hxOutside : x = outside j hjNew :=
          hjx.symm.trans htx
        have hxW : outside j hjNew ∈ W := by
          apply Finset.mem_union_left E
          rw [← hxOutside]
          exact Finset.mem_coe.mp hxU
        exact (Finset.mem_sdiff.mp
          (houtsideSpec j hjNew)).2 hxW
      · have htx : (t j).1 = (s j).1 :=
          hmissKeep j hjjb hsjE
        apply Set.disjoint_left.mp hUselected hxU
        exact ⟨j, htx.symm.trans hjx⟩
    refine ⟨t, hUavoid, ?_⟩
    apply not_destroysAt_iff.mpr
    refine ⟨E, hER, ?_⟩
    rw [Set.disjoint_left]
    intro x hxE hxSelected
    obtain ⟨j, hjx⟩ := hxSelected
    by_cases hjjb : j = jb
    · have htx : (t j).1 = b := by
        subst j
        exact htjb
      have hxb : x = b := hjx.symm.trans htx
      apply Set.disjoint_left.mp hEswap hxE
      apply Finset.mem_coe.mpr
      exact Finset.mem_union_right D
        (hxb ▸ Finset.mem_singleton_self b)
    by_cases hsjE : (s j).1 ∈ E
    · have hjNew : j ∉ J := by
        intro hjJ
        exact holdHit ⟨j, hjJ, hjjb, hsjE⟩
      have htx :
          (t j).1 = outside j hjNew := by
        dsimp [t]
        rw [dif_neg hjjb, if_pos hsjE]
        dsimp [alt]
        rw [dif_neg hjNew]
      have hxOutside : x = outside j hjNew :=
        hjx.symm.trans htx
      apply (Finset.mem_sdiff.mp
        (houtsideSpec j hjNew)).2
      apply Finset.mem_union_right U
      rw [← hxOutside]
      exact Finset.mem_coe.mp hxE
    · have htx : (t j).1 = (s j).1 :=
        hmissKeep j hjjb hsjE
      have hxs : x = (s j).1 := hjx.symm.trans htx
      exact hsjE (hxs ▸ Finset.mem_coe.mp hxE)

/-- A protected lower-gap repair either completes or retains a private old
collision.

Minimality supplies a support surviving `D.erase d ∪ {b}`.  If protected
completion fails on an old block, that same support intersects the original
destroyer exactly in `d`.  Thus failures obtained from distinct choices of
`d` remain injectively distinguishable. -/
theorem lowerGapRepair_extends_protected_or_oldCollision
    {A : Set ℕ} {k q b d : ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D U J : Finset ℕ}
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hdD : d ∈ D)
    (hbA : b ∈ A)
    (hbU : b ∉ U)
    (hgap : additiveSupportFamily A k (q - b) = ∅)
    (hUselected : Disjoint (U : Set ℕ) (selectedSet s))
    (hcontemporary :
      ∀ j, j ∉ J → U.card + (k + 1) < (F j).card) :
    (∃ t : BlockSelector F,
        Disjoint (U : Set ℕ) (selectedSet t) ∧
        ¬ DestroysAt
          (additiveSupportFamily A (k + 1))
          (selectedSet t) q) ∨
      ∃ j ∈ J, ∃ E ∈ additiveSupportFamily A (k + 1) q,
        (s j).1 ∈ E ∧ E ∩ D = {d} := by
  classical
  have hrepair :
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1))
        (((D.erase d ∪ {b} : Finset ℕ) : Set ℕ)) q :=
    hminimal.swap_hit_for_lowerGap_repairs hdD hgap
  obtain ⟨E, hER, hEswap⟩ :=
    not_destroysAt_iff.mp hrepair
  obtain hcompletion | ⟨j, hjJ, hsjE⟩ :=
    lowerGapRepairWitness_extends_protected_or_oldCollision
      P s hbA hbU hUselected hER hEswap hcontemporary
  · exact Or.inl hcompletion
  · right
    have hdE : d ∈ E := by
      by_contra hdE
      apply hminimal.1 E hER
      rw [Set.disjoint_left]
      intro x hxE hxD
      by_cases hxd : x = d
      · subst x
        exact hdE (Finset.mem_coe.mp hxE)
      · apply Set.disjoint_left.mp hEswap hxE
        apply Finset.mem_coe.mpr
        exact Finset.mem_union_left _
          (Finset.mem_erase.mpr
            ⟨hxd, Finset.mem_coe.mp hxD⟩)
    have hprivate : E ∩ D = {d} := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxE, hxD⟩ := Finset.mem_inter.mp hx
        have hxd : x = d := by
          by_contra hne
          apply Set.disjoint_left.mp hEswap
            (Finset.mem_coe.mpr hxE)
          apply Finset.mem_coe.mpr
          exact Finset.mem_union_left _
            (Finset.mem_erase.mpr ⟨hne, hxD⟩)
        simpa [hxd]
      · intro hx
        have hxd : x = d := by simpa using hx
        subst x
        exact Finset.mem_inter.mpr ⟨hdE, hdD⟩
    exact ⟨j, hjJ, E, hER, hsjE, hprivate⟩

/-- Protected completion of a lower-gap repair when every block has the
required second-choice capacity.

This is the empty-exception specialization of
`lowerGapRepair_extends_protected_or_oldCollision`: with no old blocks, the
collision horn is impossible.  It is the direct bridge from uniform
finite-prefix composition to a certificate-safe selector repair for
bounded destroyers. -/
theorem lowerGapRepair_extends_avoiding_protectedUnion
    {A : Set ℕ} {k q b d : ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D U : Finset ℕ}
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hdD : d ∈ D)
    (hbA : b ∈ A)
    (hbU : b ∉ U)
    (hgap : additiveSupportFamily A k (q - b) = ∅)
    (hUselected : Disjoint (U : Set ℕ) (selectedSet s))
    (hblocks :
      ∀ j, U.card + (k + 1) < (F j).card) :
    ∃ t : BlockSelector F,
      Disjoint (U : Set ℕ) (selectedSet t) ∧
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1))
        (selectedSet t) q := by
  obtain hrepair | ⟨j, hjEmpty, _E, _hER, _hsjE, _hprivate⟩ :=
    lowerGapRepair_extends_protected_or_oldCollision
      P s (J := ∅) hminimal hdD hbA hbU hgap hUselected
        (by
          intro j _hj
          exact hblocks j)
  · exact hrepair
  · simpa using hjEmpty

/-- Amplification of protected lower-gap repair failures.

Try the same protected gap point against every private hit `d ∈ D`.  If no
choice completes, each `d` produces an upper support meeting `D` exactly at
`d` and containing an old selected summand.  Removing that old summand gives
an injective encoding of `D` into the disjoint union of the old lower-order
support families. -/
theorem lowerGapRepair_manyPrivateHits_complete_or_oldGrowth
    {A : Set ℕ} {k q b r : ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D U J : Finset ℕ}
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hbA : b ∈ A)
    (hbU : b ∉ U)
    (hgap : additiveSupportFamily A k (q - b) = ∅)
    (hUselected : Disjoint (U : Set ℕ) (selectedSet s))
    (hcontemporary :
      ∀ j, j ∉ J → U.card + (k + 1) < (F j).card)
    (hmany : J.card * r < D.card) :
    (∃ t : BlockSelector F,
        Disjoint (U : Set ℕ) (selectedSet t) ∧
        ¬ DestroysAt
          (additiveSupportFamily A (k + 1))
          (selectedSet t) q) ∨
      ∃ j ∈ J,
        r < (additiveSupportFamily A k
          (q - (s j).1)).card := by
  classical
  by_cases hcompletion :
      ∃ d : {d // d ∈ D}, ∃ t : BlockSelector F,
        Disjoint (U : Set ℕ) (selectedSet t) ∧
        ¬ DestroysAt
          (additiveSupportFamily A (k + 1))
          (selectedSet t) q
  · left
    obtain ⟨_d, t, htU, htq⟩ := hcompletion
    exact ⟨t, htU, htq⟩
  · right
    have hcollision :
        ∀ d : {d // d ∈ D},
          ∃ j ∈ J, ∃ E ∈ additiveSupportFamily A (k + 1) q,
            (s j).1 ∈ E ∧ E ∩ D = {d.1} := by
      intro d
      obtain hcomplete | hcollision :=
        lowerGapRepair_extends_protected_or_oldCollision
          P s hminimal d.2 hbA hbU hgap hUselected
            hcontemporary
      · exact (hcompletion ⟨d, hcomplete⟩).elim
      · exact hcollision
    choose oldIndex holdIndex upper hupperR holdUpper hprivate
      using hcollision
    have hlower :
        ∀ d : {d // d ∈ D},
          ∃ H ∈ additiveSupportFamily A k
              (q - (s (oldIndex d)).1),
            upper d = insert (s (oldIndex d)).1 H := by
      intro d
      exact additiveSupport_remove_hit_succ
        (hupperR d) (holdUpper d)
    choose lower hlowerR hreconstruct using hlower
    let Target :=
      Σ j : {j // j ∈ J},
        {H // H ∈ additiveSupportFamily A k
          (q - (s j.1).1)}
    let encode : {d // d ∈ D} → Target := fun d =>
      ⟨⟨oldIndex d, holdIndex d⟩,
        ⟨lower d, hlowerR d⟩⟩
    have hencode : Function.Injective encode := by
      intro d e hde
      have hj :
          oldIndex d = oldIndex e :=
        congrArg (fun z : Target => z.1.1) hde
      have hH :
          lower d = lower e :=
        congrArg (fun z : Target => z.2.1) hde
      apply Subtype.ext
      have hupperEq : upper d = upper e := by
        rw [hreconstruct d, hreconstruct e, hj, hH]
      have hsingle :
          ({d.1} : Finset ℕ) = {e.1} := by
        rw [← hprivate d, ← hprivate e, hupperEq]
      simpa using hsingle
    have hdomainTarget :
        D.card ≤ Fintype.card Target := by
      simpa only [Fintype.card_coe] using
        Fintype.card_le_of_injective encode hencode
    by_contra hnone
    push Not at hnone
    have htargetBound :
        Fintype.card Target ≤ J.card * r := by
      rw [Fintype.card_sigma]
      simp only [Fintype.card_coe]
      calc
        (∑ j : {j // j ∈ J},
            (additiveSupportFamily A k
              (q - (s j.1).1)).card) ≤
            ∑ _j : {j // j ∈ J}, r := by
          gcongr with j
          exact hnone j.1 j.2
        _ = J.card * r := by simp
    exact (not_lt_of_ge (hdomainTarget.trans htargetBound)) hmany

/-- Supports at `q` which contain a fixed summand inject into the
lower-order support family at the corresponding difference.

Choose one tuple-level removal of `a` from every upper support containing
`a`.  The removal is injective because the upper support is reconstructed
as `insert a H`.  This is the counting fact needed to bound *all* possible
collision witnesses at one old selector coordinate, rather than only the
witnesses already returned by a particular repair attempt. -/
theorem additiveSupportFamily_hitFilter_card_le_lowerDifference
    {A : Set ℕ} {k q a : ℕ} :
    ((additiveSupportFamily A (k + 1) q).filter
        fun E => a ∈ E).card ≤
      (additiveSupportFamily A k (q - a)).card := by
  classical
  let Hit : Finset (Finset ℕ) :=
    (additiveSupportFamily A (k + 1) q).filter
      fun E => a ∈ E
  let witness :
      ∀ E : {E // E ∈ Hit},
        ∃ H ∈ additiveSupportFamily A k (q - a),
          E.1 = insert a H := fun E => by
    have hparts := Finset.mem_filter.mp E.2
    exact additiveSupport_remove_hit_succ hparts.1 hparts.2
  let lower :
      {E // E ∈ Hit} →
        {H // H ∈ additiveSupportFamily A k (q - a)} := fun E =>
    ⟨(witness E).choose, (witness E).choose_spec.1⟩
  have hreconstruct :
      ∀ E : {E // E ∈ Hit},
        E.1 = insert a (lower E).1 := by
    intro E
    exact (witness E).choose_spec.2
  have hlowerInjective : Function.Injective lower := by
    intro E G hEG
    apply Subtype.ext
    rw [hreconstruct E, hreconstruct G]
    exact congrArg (fun H : Finset ℕ => insert a H)
      (congrArg Subtype.val hEG)
  have hcard :
      Hit.card ≤
        (additiveSupportFamily A k (q - a)).card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective lower hlowerInjective
  simpa only [Hit] using hcard

/-- A represented lower difference lifts back to the exact upper target with
loss at most a factor of two in support cardinality.

Split the order-`k` supports at `q-d` according to whether they already
contain `d`.  On the containing half, insertion of `d` changes no support;
on the avoiding half, insertion is injective (erase `d` recovers the
source).  Both halves therefore inject into the order-`k+1` support family
at the exact label `q`.  This is the cardinal bridge that prevents
finite-prefix growth from drifting to an unrelated lower target. -/
theorem lowerDifferenceSupportFamily_card_le_twice_exact
    {A : Set ℕ} {k q d : ℕ}
    (hdA : d ∈ A) (hdq : d ≤ q) :
    (additiveSupportFamily A k (q - d)).card ≤
      2 * (additiveSupportFamily A (k + 1) q).card := by
  classical
  let Lower := additiveSupportFamily A k (q - d)
  let With : Finset (Finset ℕ) :=
    Lower.filter fun H => d ∈ H
  let Without : Finset (Finset ℕ) :=
    Lower.filter fun H => d ∉ H
  let lift : Finset ℕ → Finset ℕ := fun H => insert d H
  let Lifted : Finset (Finset ℕ) := Without.image lift
  have hWithSub :
      With ⊆ additiveSupportFamily A (k + 1) q := by
    intro H hHWith
    have hparts := Finset.mem_filter.mp hHWith
    have hlift :=
      insert_mem_additiveSupportFamily_succ hdA hparts.1
    simpa only [Finset.insert_eq_of_mem hparts.2,
      Nat.add_sub_of_le hdq] using hlift
  have hliftInjective : Set.InjOn lift (Without : Set (Finset ℕ)) := by
    intro H hH G hG hHG
    have hdH : d ∉ H := (Finset.mem_filter.mp hH).2
    have hdG : d ∉ G := (Finset.mem_filter.mp hG).2
    change insert d H = insert d G at hHG
    have herase :=
      congrArg (fun E : Finset ℕ => E.erase d) hHG
    simpa [hdH, hdG] using herase
  have hLiftedCard : Lifted.card = Without.card := by
    exact Finset.card_image_iff.mpr hliftInjective
  have hLiftedSub :
      Lifted ⊆ additiveSupportFamily A (k + 1) q := by
    intro E hELifted
    obtain ⟨H, hHWithout, rfl⟩ :=
      Finset.mem_image.mp hELifted
    have hHR := (Finset.mem_filter.mp hHWithout).1
    have hlift :=
      insert_mem_additiveSupportFamily_succ hdA hHR
    simpa only [lift, Nat.add_sub_of_le hdq] using hlift
  have hWithCard :
      With.card ≤
        (additiveSupportFamily A (k + 1) q).card :=
    Finset.card_le_card hWithSub
  have hWithoutCard :
      Without.card ≤
        (additiveSupportFamily A (k + 1) q).card := by
    rw [← hLiftedCard]
    exact Finset.card_le_card hLiftedSub
  have hsplit : With.card + Without.card = Lower.card := by
    simpa only [With, Without] using
      (Finset.card_filter_add_card_filter_not
        (s := Lower) (p := fun H => d ∈ H))
  dsimp only [Lower] at hsplit ⊢
  omega

/-- A block larger than a protected set and a bounded finite family has a
point avoiding both.

The family union occupies at most `h * M.card` vertices.  This elementary
finite-union estimate is the reusable second-choice principle for old
coordinates. -/
theorem exists_point_avoiding_protected_and_boundedFamily
    {V U : Finset ℕ} {M : Finset (Finset ℕ)} {h : ℕ}
    (hcard : ∀ E ∈ M, E.card ≤ h)
    (hlarge : U.card + h * M.card < V.card) :
    ∃ y ∈ V, y ∉ U ∧ ∀ E ∈ M, y ∉ E := by
  classical
  let W : Finset ℕ := U ∪ M.biUnion id
  have hfamilyUnion :
      (M.biUnion id).card ≤ h * M.card :=
    biUnion_card_le_of_edge_card_le
      (H := M) (M := M) (by simp) hcard
  have hWcard : W.card < V.card := by
    have hunion :
        W.card ≤ U.card + (M.biUnion id).card := by
      simpa only [W] using Finset.card_union_le U (M.biUnion id)
    omega
  have hnotSubset : ¬ V ⊆ W := by
    intro hsubset
    exact (not_lt_of_ge (Finset.card_le_card hsubset)) hWcard
  obtain ⟨y, hyV, hyW⟩ :=
    Finset.not_subset.mp hnotSubset
  refine ⟨y, hyV, ?_, ?_⟩
  · intro hyU
    exact hyW (Finset.mem_union_left _ hyU)
  · intro E hEM hyE
    apply hyW
    apply Finset.mem_union_right U
    exact Finset.mem_biUnion.mpr ⟨E, hEM, hyE⟩

/-- Universal second choice at one old block.

If the lower-order difference family at `q-a` has at most `r` supports,
then there are at most `r` upper supports at `q` containing `a`.  A block
larger than the protected union plus `(k+1)r` therefore contains one point
which avoids the protected set and every possible collision support
containing `a`. -/
theorem exists_blockChoice_avoiding_protected_and_allHitSupports
    {A : Set ℕ} {k q a r : ℕ} {V U : Finset ℕ}
    (hlower :
      (additiveSupportFamily A k (q - a)).card ≤ r)
    (hlarge : U.card + (k + 1) * r < V.card) :
    ∃ y ∈ V, y ∉ U ∧
      ∀ E ∈ additiveSupportFamily A (k + 1) q,
        a ∈ E → y ∉ E := by
  classical
  let Hit : Finset (Finset ℕ) :=
    (additiveSupportFamily A (k + 1) q).filter
      fun E => a ∈ E
  have hHitCard : Hit.card ≤ r := by
    exact
      (additiveSupportFamily_hitFilter_card_le_lowerDifference
        (A := A) (k := k) (q := q) (a := a)).trans hlower
  have hHitRank :
      ∀ E ∈ Hit, E.card ≤ k + 1 := by
    intro E hEHit
    exact additiveSupportFamily_cardAtMost
      A (k + 1) q E (Finset.mem_filter.mp hEHit).1
  have hlargeHit :
      U.card + (k + 1) * Hit.card < V.card := by
    have hmul :
        (k + 1) * Hit.card ≤ (k + 1) * r :=
      Nat.mul_le_mul_left (k + 1) hHitCard
    omega
  obtain ⟨y, hyV, hyU, hyHit⟩ :=
    exists_point_avoiding_protected_and_boundedFamily
      hHitRank hlargeHit
  refine ⟨y, hyV, hyU, ?_⟩
  intro E hER haE
  exact hyHit E (Finset.mem_filter.mpr ⟨hER, haE⟩)

/-- Local dependency form of the old-coordinate attack.

Fix an old selected coordinate `a` at the current target `q`, and store one
protected order-`k+1` support for every target in `Q`.  If the lower
difference family at `q-a` already has more than `r` members, we have genuine
support growth.  Otherwise one of two things happens in a proposed old
block `V`:

* there is a universal second choice avoiding every protected support and
  every possible collision support through `a`; or
* a subcollection `P` of at most `V.card` protected targets, all strictly
  larger than `q`, covers the whole block together with those collision
  supports.

The final cardinal inequality is independent of `Q.card`.  In particular, a
large saturated old block forces many strictly larger local dependencies,
rather than merely reporting that the global certificate is large. -/
theorem oldCoordinate_growth_or_secondChoice_or_localLargerDependency
    {A : Set ℕ} {k q a r : ℕ} {Q V : Finset ℕ}
    (c :
      FiniteSupportChoice
        (additiveSupportFamily A (k + 1)) Q)
    (hQlarger : ∀ u ∈ Q, q < u) :
    r < (additiveSupportFamily A k (q - a)).card ∨
      (∃ y ∈ V,
        y ∉ finiteSupportChoiceUnion c ∧
        ∀ G ∈ additiveSupportFamily A (k + 1) q,
          a ∈ G → y ∉ G) ∨
      ∃ P : Finset ℕ, ∃ hPQ : P ⊆ Q,
        P.card ≤ V.card ∧
        (∀ u ∈ P, q < u) ∧
        V ⊆
          ((additiveSupportFamily A (k + 1) q).filter
              fun G => a ∈ G).biUnion id ∪
            finiteSupportChoiceUnion
              (restrictFiniteSupportChoice hPQ c) ∧
        V.card ≤ (k + 1) * (r + P.card) := by
  classical
  let Hit : Finset (Finset ℕ) :=
    (additiveSupportFamily A (k + 1) q).filter
      fun G => a ∈ G
  by_cases hgrowth :
      r < (additiveSupportFamily A k (q - a)).card
  · exact Or.inl hgrowth
  · right
    have hlower :
        (additiveSupportFamily A k (q - a)).card ≤ r :=
      Nat.le_of_not_gt hgrowth
    have hHitCard : Hit.card ≤ r :=
      (additiveSupportFamily_hitFilter_card_le_lowerDifference
        (A := A) (k := k) (q := q) (a := a)).trans hlower
    have hHitRank :
        ∀ G ∈ Hit, G.card ≤ k + 1 := by
      intro G hGHit
      exact additiveSupportFamily_cardAtMost
        A (k + 1) q G (Finset.mem_filter.mp hGHit).1
    obtain ⟨y, hyV, hyHit, hyProtected⟩ |
        ⟨P, hPQ, hPcard, hcover, hcard⟩ :=
      exists_point_avoiding_families_or_localSupportChoiceSubcover
        c Hit hHitRank
          (additiveSupportFamily_cardAtMost A (k + 1))
    · left
      refine ⟨y, hyV, hyProtected, ?_⟩
      intro G hGR haG
      exact hyHit G (Finset.mem_filter.mpr ⟨hGR, haG⟩)
    · right
      have hPlarger : ∀ u ∈ P, q < u := by
        intro u huP
        exact hQlarger u (hPQ huP)
      have hcard' :
          V.card ≤ (k + 1) * r + (k + 1) * P.card := by
        exact hcard.trans
          (Nat.add_le_add_right
            (Nat.mul_le_mul_left (k + 1) hHitCard)
            ((k + 1) * P.card))
      refine ⟨P, hPQ, hPcard, hPlarger, ?_, ?_⟩
      · simpa only [Hit] using hcover
      · simpa only [Nat.mul_add] using hcard'

/-- Whole-block version of the local dependency attack.

Instead of fixing one old coordinate, put the entire exact support family at
`q` into the immediate collision family.  If that family has at most `r`
members, a point outside its union is a completely safe replacement for
*any* active hit of a minimal destroyer at `q`.  Thus an old block yields
exact support growth, a protected safe second choice, or a locally bounded
set of strictly larger certificate dependencies. -/
theorem oldBlock_exactGrowth_or_safeSecondChoice_or_localLargerDependency
    {A : Set ℕ} {k q r : ℕ} {Q V : Finset ℕ}
    (c :
      FiniteSupportChoice
        (additiveSupportFamily A (k + 1)) Q)
    (hQlarger : ∀ u ∈ Q, q < u) :
    r < (additiveSupportFamily A (k + 1) q).card ∨
      (∃ y ∈ V,
        y ∉ finiteSupportChoiceUnion c ∧
        ∀ G ∈ additiveSupportFamily A (k + 1) q, y ∉ G) ∨
      ∃ P : Finset ℕ, ∃ hPQ : P ⊆ Q,
        P.card ≤ V.card ∧
        (∀ u ∈ P, q < u) ∧
        V ⊆
          (additiveSupportFamily A (k + 1) q).biUnion id ∪
            finiteSupportChoiceUnion
              (restrictFiniteSupportChoice hPQ c) ∧
        V.card ≤ (k + 1) * (r + P.card) := by
  classical
  by_cases hgrowth :
      r < (additiveSupportFamily A (k + 1) q).card
  · exact Or.inl hgrowth
  · right
    have hfamilyCard :
        (additiveSupportFamily A (k + 1) q).card ≤ r :=
      Nat.le_of_not_gt hgrowth
    obtain ⟨y, hyV, hyFamily, hyProtected⟩ |
        ⟨P, hPQ, hPcard, hcover, hcard⟩ :=
      exists_point_avoiding_families_or_localSupportChoiceSubcover
        c (additiveSupportFamily A (k + 1) q)
          (fun G hG =>
            additiveSupportFamily_cardAtMost A (k + 1) q G hG)
          (additiveSupportFamily_cardAtMost A (k + 1))
    · exact Or.inl ⟨y, hyV, hyProtected, hyFamily⟩
    · right
      have hPlarger : ∀ u ∈ P, q < u := by
        intro u huP
        exact hQlarger u (hPQ huP)
      have hcard' :
          V.card ≤ (k + 1) * r + (k + 1) * P.card := by
        exact hcard.trans
          (Nat.add_le_add_right
            (Nat.mul_le_mul_left (k + 1) hfamilyCard)
            ((k + 1) * P.card))
      refine ⟨P, hPQ, hPcard, hPlarger, hcover, ?_⟩
      simpa only [Nat.mul_add] using hcard'

/-- Block-aligned consequence for a minimal destroyer.

Apply the whole-block dichotomy to the alternatives in the active block.
The second horn is immediately converted into a verified safe swap.  The
remaining obstruction is no longer the cardinality of the full certificate:
it is an explicit bounded family of strictly larger targets whose chosen
supports, together with the exact supports at `q`, cover this one block. -/
theorem blockAligned_exactGrowth_or_protectedSafeSwap_or_localLargerDependency
    {A : Set ℕ} {k q r : ℕ} {Q : Finset ℕ}
    {F : ℕ → Finset ℕ} (s : BlockSelector F)
    {D : Finset ℕ} {i : ℕ}
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hactive : (s i).1 ∈ D)
    (c :
      FiniteSupportChoice
        (additiveSupportFamily A (k + 1)) Q)
    (hQlarger : ∀ u ∈ Q, q < u) :
    r < (additiveSupportFamily A (k + 1) q).card ∨
      (∃ b ∈ (F i).erase (s i).1,
        b ∉ finiteSupportChoiceUnion c ∧
        ¬ DestroysAt
          (additiveSupportFamily A (k + 1))
          (((D.erase (s i).1 ∪ {b} : Finset ℕ) : Set ℕ)) q) ∨
      ∃ P : Finset ℕ, ∃ hPQ : P ⊆ Q,
        P.card ≤ ((F i).erase (s i).1).card ∧
        (∀ u ∈ P, q < u) ∧
        (F i).erase (s i).1 ⊆
          (additiveSupportFamily A (k + 1) q).biUnion id ∪
            finiteSupportChoiceUnion
              (restrictFiniteSupportChoice hPQ c) ∧
        ((F i).erase (s i).1).card ≤
          (k + 1) * (r + P.card) := by
  obtain hgrowth | ⟨b, hbBlock, hbProtected, hbAvoid⟩ |
      hdependency :=
    oldBlock_exactGrowth_or_safeSecondChoice_or_localLargerDependency
      (V := (F i).erase (s i).1) c hQlarger
  · exact Or.inl hgrowth
  · exact Or.inr (Or.inl
      ⟨b, hbBlock, hbProtected,
        hminimal.swap_hit_for_avoidedPoint_repairs hactive hbAvoid⟩)
  · exact Or.inr (Or.inr hdependency)

/-- A block-aligned repair may be completed while avoiding an additional
finite protected set.

The old selector already avoids `U`.  The replacement `b` is also outside
`U`, and the still-active old choices lie in that selector.  Choose every
other coordinate outside `U ∪ E`, where `E` is a support surviving the
finite swap.  The resulting selector simultaneously avoids `U` and
preserves the repaired target. -/
theorem blockAlignedSafeSwap_extends_avoiding_protectedUnion
    {A : Set ℕ} {k q : ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D U : Finset ℕ} {i b : ℕ}
    (hbBlock : b ∈ (F i).erase (s i).1)
    (hbU : b ∉ U)
    (hUselected : Disjoint (U : Set ℕ) (selectedSet s))
    (hrepair :
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1))
        (((D.erase (s i).1 ∪ {b} : Finset ℕ) : Set ℕ)) q)
    (hblocks : ∀ j, U.card + (k + 1) < (F j).card) :
    ∃ t : BlockSelector F,
      (t i).1 = b ∧
      Disjoint (U : Set ℕ) (selectedSet t) ∧
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1))
        (selectedSet t) q := by
  classical
  obtain ⟨E, hER, hEswap⟩ :=
    not_destroysAt_iff.mp hrepair
  have hEcard : E.card ≤ k + 1 :=
    additiveSupportFamily_cardAtMost A (k + 1) q E hER
  let W : Finset ℕ := U ∪ E
  have hWcard : W.card ≤ U.card + (k + 1) := by
    calc
      W.card ≤ U.card + E.card := by
        simpa only [W] using Finset.card_union_le U E
      _ ≤ U.card + (k + 1) := Nat.add_le_add_left hEcard U.card
  have houtside : ∀ j, (F j \ W).Nonempty := by
    intro j
    by_contra hempty
    have hsubset : F j ⊆ W := by
      intro x hxF
      by_contra hxW
      exact hempty ⟨x, Finset.mem_sdiff.mpr ⟨hxF, hxW⟩⟩
    have hcard := Finset.card_le_card hsubset
    have hlarge := hblocks j
    omega
  choose outside houtsideSpec using houtside
  let t : BlockSelector F := fun j =>
    if hji : j = i then
      ⟨b, by
        subst j
        exact (Finset.mem_erase.mp hbBlock).2⟩
    else if hjD : (s j).1 ∈ D.erase (s i).1 then
      s j
    else
      ⟨outside j, (Finset.mem_sdiff.mp (houtsideSpec j)).1⟩
  have hti : (t i).1 = b := by
    dsimp [t]
    rw [dif_pos rfl]
  have hkeep :
      ∀ j, j ≠ i → (s j).1 ∈ D.erase (s i).1 →
        (t j).1 = (s j).1 := by
    intro j hji hjD
    dsimp [t]
    rw [dif_neg hji, if_pos hjD]
  have houtside :
      ∀ j, j ≠ i → (s j).1 ∉ D.erase (s i).1 →
        (t j).1 = outside j := by
    intro j hji hjD
    dsimp [t]
    rw [dif_neg hji, if_neg hjD]
  have hUavoid : Disjoint (U : Set ℕ) (selectedSet t) := by
    rw [Set.disjoint_left]
    intro x hxU hxSelected
    obtain ⟨j, hjx⟩ := hxSelected
    by_cases hji : j = i
    · have htx : (t j).1 = b := by
        subst j
        exact hti
      have hxb : x = b := hjx.symm.trans htx
      exact hbU (hxb ▸ Finset.mem_coe.mp hxU)
    by_cases hjD : (s j).1 ∈ D.erase (s i).1
    · have htx : (t j).1 = (s j).1 := hkeep j hji hjD
      apply Set.disjoint_left.mp hUselected hxU
      exact ⟨j, htx.symm.trans hjx⟩
    · have htx : (t j).1 = outside j :=
        houtside j hji hjD
      have hxOutside : x = outside j := hjx.symm.trans htx
      have hxW : outside j ∈ W := by
        apply Finset.mem_union_left E
        rw [← hxOutside]
        exact Finset.mem_coe.mp hxU
      exact (Finset.mem_sdiff.mp (houtsideSpec j)).2 hxW
  refine ⟨t, hti, hUavoid, ?_⟩
  apply not_destroysAt_iff.mpr
  refine ⟨E, hER, ?_⟩
  rw [Set.disjoint_left]
  intro x hxE hxSelected
  obtain ⟨j, hjx⟩ := hxSelected
  by_cases hji : j = i
  · have htx : (t j).1 = b := by
      subst j
      exact hti
    have hxb : x = b := hjx.symm.trans htx
    apply Set.disjoint_left.mp hEswap hxE
    exact Finset.mem_coe.mpr (by
      rw [hxb]
      exact Finset.mem_union_right _
        (Finset.mem_singleton_self b))
  by_cases hjD : (s j).1 ∈ D.erase (s i).1
  · have htx : (t j).1 = (s j).1 := hkeep j hji hjD
    have hxs : x = (s j).1 := hjx.symm.trans htx
    apply Set.disjoint_left.mp hEswap hxE
    exact Finset.mem_coe.mpr (by
      rw [hxs]
      exact Finset.mem_union_left _ hjD)
  · have htx : (t j).1 = outside j :=
      houtside j hji hjD
    have hxOutside : x = outside j := hjx.symm.trans htx
    have hxW : outside j ∈ W := by
      apply Finset.mem_union_right U
      rw [← hxOutside]
      exact Finset.mem_coe.mp hxE
    exact (Finset.mem_sdiff.mp (houtsideSpec j)).2 hxW

/-- Complete a fixed block-aligned repair when every colliding old
coordinate has a second choice avoiding both the protected set and the
repair support.

Contemporary hit-coordinates obtain such a choice from their cardinal
reserve.  Old hit-coordinates use the supplied second-choice hypothesis.
All non-hit coordinates are kept unchanged.  This separates the genuine
old-block issue from the rest of the infinite selector completion. -/
theorem blockAlignedRepairWitness_extends_protected_of_oldSecondChoices
    {A : Set ℕ} {k q : ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D U J E : Finset ℕ} {i b : ℕ}
    (hbBlock : b ∈ (F i).erase (s i).1)
    (hbU : b ∉ U)
    (hUselected : Disjoint (U : Set ℕ) (selectedSet s))
    (hER : E ∈ additiveSupportFamily A (k + 1) q)
    (hEswap : Disjoint (E : Set ℕ)
      (((D.erase (s i).1 ∪ {b} : Finset ℕ) : Set ℕ)))
    (hsecond :
      ∀ j, j ∈ J → (s j).1 ∈ E →
        ∃ y ∈ F j, y ∉ U ∧ y ∉ E)
    (hcontemporary :
      ∀ j, j ∉ J → (s j).1 ∈ E →
        U.card + (k + 1) < (F j).card) :
    ∃ t : BlockSelector F,
      Disjoint (U : Set ℕ) (selectedSet t) ∧
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1))
        (selectedSet t) q := by
  classical
  have hEcard : E.card ≤ k + 1 :=
    additiveSupportFamily_cardAtMost A (k + 1) q E hER
  have hchoice :
      ∀ j, (s j).1 ∈ E →
        ∃ y ∈ F j, y ∉ U ∧ y ∉ E := by
    intro j hsjE
    by_cases hjJ : j ∈ J
    · exact hsecond j hjJ hsjE
    · have hsingletonRank :
          ∀ G ∈ ({E} : Finset (Finset ℕ)),
            G.card ≤ k + 1 := by
        intro G hGE
        have hGEq : G = E := by simpa using hGE
        simpa only [hGEq] using hEcard
      have hlarge :
          U.card + (k + 1) * ({E} : Finset (Finset ℕ)).card <
            (F j).card := by
        simpa using hcontemporary j hjJ hsjE
      obtain ⟨y, hyF, hyU, hyAll⟩ :=
        exists_point_avoiding_protected_and_boundedFamily
          hsingletonRank hlarge
      exact ⟨y, hyF, hyU,
        hyAll E (Finset.mem_singleton_self E)⟩
  choose outside houtBlock houtU houtE using hchoice
  let t : BlockSelector F := fun j =>
    if hji : j = i then
      ⟨b, by
        subst j
        exact (Finset.mem_erase.mp hbBlock).2⟩
    else if hsjE : (s j).1 ∈ E then
      ⟨outside j hsjE, houtBlock j hsjE⟩
    else
      s j
  have hti : (t i).1 = b := by
    dsimp [t]
    rw [dif_pos rfl]
  have hUavoid : Disjoint (U : Set ℕ) (selectedSet t) := by
    rw [Set.disjoint_left]
    intro x hxU hxSelected
    obtain ⟨j, hjx⟩ := hxSelected
    by_cases hji : j = i
    · have htx : (t j).1 = b := by
        subst j
        exact hti
      have hxb : x = b := hjx.symm.trans htx
      exact hbU (hxb ▸ Finset.mem_coe.mp hxU)
    by_cases hsjE : (s j).1 ∈ E
    · have htx : (t j).1 = outside j hsjE := by
        dsimp [t]
        rw [dif_neg hji, dif_pos hsjE]
      have hxOutside : x = outside j hsjE :=
        hjx.symm.trans htx
      exact houtU j hsjE
        (hxOutside ▸ Finset.mem_coe.mp hxU)
    · have htx : (t j).1 = (s j).1 := by
        dsimp [t]
        rw [dif_neg hji, dif_neg hsjE]
      apply Set.disjoint_left.mp hUselected hxU
      exact ⟨j, htx.symm.trans hjx⟩
  refine ⟨t, hUavoid, ?_⟩
  apply not_destroysAt_iff.mpr
  refine ⟨E, hER, ?_⟩
  rw [Set.disjoint_left]
  intro x hxE hxSelected
  obtain ⟨j, hjx⟩ := hxSelected
  by_cases hji : j = i
  · have htx : (t j).1 = b := by
      subst j
      exact hti
    have hxb : x = b := hjx.symm.trans htx
    apply Set.disjoint_left.mp hEswap hxE
    apply Finset.mem_coe.mpr
    exact Finset.mem_union_right _
      (hxb ▸ Finset.mem_singleton_self b)
  by_cases hsjE : (s j).1 ∈ E
  · have htx : (t j).1 = outside j hsjE := by
      dsimp [t]
      rw [dif_neg hji, dif_pos hsjE]
    have hxOutside : x = outside j hsjE :=
      hjx.symm.trans htx
    exact houtE j hsjE
      (hxOutside ▸ Finset.mem_coe.mp hxE)
  · have htx : (t j).1 = (s j).1 := by
      dsimp [t]
      rw [dif_neg hji, dif_neg hsjE]
    have hxs : x = (s j).1 := hjx.symm.trans htx
    exact hsjE (hxs ▸ Finset.mem_coe.mp hxE)

/-- Protected completion only needs capacity in blocks actually hit by the
chosen repair support.

All unhit coordinates are left unchanged, so the former all-block capacity
assumption was stronger than necessary.  This support-local form is the one
compatible with scheduled unequal blocks: at most `k+1` block indices need
fresh room during one repair. -/
theorem blockAlignedRepairWitness_extends_protected_of_hitBlockCapacity
    {A : Set ℕ} {k q : ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D U E : Finset ℕ} {i b : ℕ}
    (hbBlock : b ∈ (F i).erase (s i).1)
    (hbU : b ∉ U)
    (hUselected : Disjoint (U : Set ℕ) (selectedSet s))
    (hER : E ∈ additiveSupportFamily A (k + 1) q)
    (hEswap : Disjoint (E : Set ℕ)
      (((D.erase (s i).1 ∪ {b} : Finset ℕ) : Set ℕ)))
    (hhitCapacity :
      ∀ j, (s j).1 ∈ E →
        U.card + (k + 1) < (F j).card) :
    ∃ t : BlockSelector F,
      Disjoint (U : Set ℕ) (selectedSet t) ∧
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1))
        (selectedSet t) q := by
  apply blockAlignedRepairWitness_extends_protected_of_oldSecondChoices
    P s (J := ∅) hbBlock hbU hUselected hER hEswap
  · intro j hj
    simp at hj
  · intro j _hj hsjE
    exact hhitCapacity j hsjE

/-- Support-local protected completion with an exceptional finite set.

If the repair support hits no selected coordinate from `J`, capacity is
needed only at its remaining hit coordinates and the repair completes.
Otherwise the actual exceptional hit is returned.  This avoids imposing
any size condition on blocks which the repair support never visits. -/
theorem blockAlignedRepairWitness_extends_protected_or_hitBlockCollision
    {A : Set ℕ} {k q : ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D U J E : Finset ℕ} {i b : ℕ}
    (hbBlock : b ∈ (F i).erase (s i).1)
    (hbU : b ∉ U)
    (hUselected : Disjoint (U : Set ℕ) (selectedSet s))
    (hER : E ∈ additiveSupportFamily A (k + 1) q)
    (hEswap : Disjoint (E : Set ℕ)
      (((D.erase (s i).1 ∪ {b} : Finset ℕ) : Set ℕ)))
    (hhitCapacity :
      ∀ j, j ∉ J → (s j).1 ∈ E →
        U.card + (k + 1) < (F j).card) :
    (∃ t : BlockSelector F,
        Disjoint (U : Set ℕ) (selectedSet t) ∧
        ¬ DestroysAt
          (additiveSupportFamily A (k + 1))
          (selectedSet t) q) ∨
      ∃ j ∈ J, (s j).1 ∈ E := by
  classical
  by_cases hhit : ∃ j ∈ J, (s j).1 ∈ E
  · exact Or.inr hhit
  · left
    apply blockAlignedRepairWitness_extends_protected_of_hitBlockCapacity
      P s hbBlock hbU hUselected hER hEswap
    intro j hsjE
    have hjJ : j ∉ J := by
      intro hjJ
      exact hhit ⟨j, hjJ, hsjE⟩
    exact hhitCapacity j hjJ hsjE

/-- A fixed repair either completes or collides at a genuinely undersized
old block.

Assume every old coherent difference has at most `r` lower supports.  At an
old block larger than `U.card + (k+1)r`, the universal second-choice lemma
finds a point avoiding `U` and every possible upper collision support
through that coordinate.  Therefore a failed completion can only occur at
an old block below this explicit size threshold. -/
theorem blockAlignedRepairWitness_extends_protected_or_smallOldCollision
    {A : Set ℕ} {k q r : ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D U J E : Finset ℕ} {i b : ℕ}
    (hbBlock : b ∈ (F i).erase (s i).1)
    (hbU : b ∉ U)
    (hUselected : Disjoint (U : Set ℕ) (selectedSet s))
    (hER : E ∈ additiveSupportFamily A (k + 1) q)
    (hEswap : Disjoint (E : Set ℕ)
      (((D.erase (s i).1 ∪ {b} : Finset ℕ) : Set ℕ)))
    (holdBound :
      ∀ j ∈ J,
        (additiveSupportFamily A k
          (q - (s j).1)).card ≤ r)
    (hcontemporary :
      ∀ j, j ∉ J → U.card + (k + 1) < (F j).card) :
    (∃ t : BlockSelector F,
        Disjoint (U : Set ℕ) (selectedSet t) ∧
        ¬ DestroysAt
          (additiveSupportFamily A (k + 1))
          (selectedSet t) q) ∨
      ∃ j ∈ J, (s j).1 ∈ E ∧
        (F j).card ≤ U.card + (k + 1) * r := by
  classical
  by_cases hsmall :
      ∃ j ∈ J, (s j).1 ∈ E ∧
        (F j).card ≤ U.card + (k + 1) * r
  · exact Or.inr hsmall
  · left
    apply blockAlignedRepairWitness_extends_protected_of_oldSecondChoices
      P s hbBlock hbU hUselected hER hEswap
    · intro j hjJ hsjE
      have hnotSmall :
          ¬ (F j).card ≤ U.card + (k + 1) * r := by
        intro hjCard
        exact hsmall ⟨j, hjJ, hsjE, hjCard⟩
      have hlarge :
          U.card + (k + 1) * r < (F j).card :=
        Nat.lt_of_not_ge hnotSmall
      obtain ⟨y, hyF, hyU, hyAvoid⟩ :=
        exists_blockChoice_avoiding_protected_and_allHitSupports
          (holdBound j hjJ) hlarge
      exact ⟨y, hyF, hyU, hyAvoid E hER hsjE⟩
    · intro j hjJ _hsjE
      exact hcontemporary j hjJ

/-- Protected completion of one fixed repair witness with a finite old-block
exception.

Only contemporary blocks (`j ∉ J`) are assumed large enough to avoid the
protected union.  If the supplied repair support meets an old selected
coordinate, that collision is returned without discarding the support.
Otherwise every old selected coordinate already avoids the repair support,
and only contemporary hit-coordinates need to be rerouted; the full
protected selector completion goes through.

Retaining the actual support is essential for amplifying collisions from
distinct active points of one minimal destroyer. -/
theorem blockAlignedRepairWitness_extends_protected_or_oldCollision
    {A C : Set ℕ} {k q : ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition C F)
    (s : BlockSelector F) {D U J E : Finset ℕ} {i b : ℕ}
    (hbBlock : b ∈ (F i).erase (s i).1)
    (hbU : b ∉ U)
    (hUselected : Disjoint (U : Set ℕ) (selectedSet s))
    (hER : E ∈ additiveSupportFamily A (k + 1) q)
    (hEswap : Disjoint (E : Set ℕ)
      (((D.erase (s i).1 ∪ {b} : Finset ℕ) : Set ℕ)))
    (hcontemporary :
      ∀ j, j ∉ J → U.card + (k + 1) < (F j).card) :
    (∃ t : BlockSelector F,
        Disjoint (U : Set ℕ) (selectedSet t) ∧
        ¬ DestroysAt
          (additiveSupportFamily A (k + 1))
          (selectedSet t) q) ∨
      ∃ j ∈ J, (s j).1 ∈ E := by
  classical
  have hEcard : E.card ≤ k + 1 :=
    additiveSupportFamily_cardAtMost A (k + 1) q E hER
  by_cases holdHit : ∃ j ∈ J, (s j).1 ∈ E
  · right
    exact holdHit
  · left
    let W : Finset ℕ := U ∪ E
    have hWcard : W.card ≤ U.card + (k + 1) := by
      calc
        W.card ≤ U.card + E.card := by
          simpa only [W] using Finset.card_union_le U E
        _ ≤ U.card + (k + 1) :=
          Nat.add_le_add_left hEcard U.card
    have houtside :
        ∀ j, j ∉ J → (F j \ W).Nonempty := by
      intro j hjJ
      by_contra hempty
      have hsubset : F j ⊆ W := by
        intro x hxF
        by_contra hxW
        exact hempty ⟨x, Finset.mem_sdiff.mpr ⟨hxF, hxW⟩⟩
      have hcard := Finset.card_le_card hsubset
      have hlarge := hcontemporary j hjJ
      omega
    choose outside houtsideSpec using houtside
    let alt : BlockSelector F := fun j =>
      if hjJ : j ∈ J then
        s j
      else
        ⟨outside j hjJ,
          (Finset.mem_sdiff.mp (houtsideSpec j hjJ)).1⟩
    let t : BlockSelector F := fun j =>
      if hji : j = i then
        ⟨b, by
          subst j
          exact (Finset.mem_erase.mp hbBlock).2⟩
      else if hsjE : (s j).1 ∈ E then
        alt j
      else
        s j
    have hti : (t i).1 = b := by
      dsimp [t]
      rw [dif_pos rfl]
    have hmissKeep :
        ∀ j, j ≠ i → (s j).1 ∉ E →
          (t j).1 = (s j).1 := by
      intro j hji hsjE
      dsimp [t]
      rw [dif_neg hji, if_neg hsjE]
    have hUavoid : Disjoint (U : Set ℕ) (selectedSet t) := by
      rw [Set.disjoint_left]
      intro x hxU hxSelected
      obtain ⟨j, hjx⟩ := hxSelected
      by_cases hji : j = i
      · have htx : (t j).1 = b := by
          subst j
          exact hti
        have hxb : x = b := hjx.symm.trans htx
        exact hbU (hxb ▸ Finset.mem_coe.mp hxU)
      by_cases hsjE : (s j).1 ∈ E
      · have hjOld : j ∉ J := by
          intro hjJ
          exact holdHit ⟨j, hjJ, hsjE⟩
        have htx :
            (t j).1 = outside j hjOld := by
          dsimp [t]
          rw [dif_neg hji, if_pos hsjE]
          dsimp [alt]
          rw [dif_neg hjOld]
        have hxOutside : x = outside j hjOld :=
          hjx.symm.trans htx
        have hxW : outside j hjOld ∈ W := by
          apply Finset.mem_union_left E
          rw [← hxOutside]
          exact Finset.mem_coe.mp hxU
        exact (Finset.mem_sdiff.mp
          (houtsideSpec j hjOld)).2 hxW
      · have htx : (t j).1 = (s j).1 :=
          hmissKeep j hji hsjE
        apply Set.disjoint_left.mp hUselected hxU
        exact ⟨j, htx.symm.trans hjx⟩
    refine ⟨t, hUavoid, ?_⟩
    apply not_destroysAt_iff.mpr
    refine ⟨E, hER, ?_⟩
    rw [Set.disjoint_left]
    intro x hxE hxSelected
    obtain ⟨j, hjx⟩ := hxSelected
    by_cases hji : j = i
    · have htx : (t j).1 = b := by
        subst j
        exact hti
      have hxb : x = b := hjx.symm.trans htx
      apply Set.disjoint_left.mp hEswap hxE
      exact Finset.mem_coe.mpr (by
        rw [hxb]
        exact Finset.mem_union_right _
          (Finset.mem_singleton_self b))
    by_cases hsjE : (s j).1 ∈ E
    · have hjOld : j ∉ J := by
        intro hjJ
        exact holdHit ⟨j, hjJ, hsjE⟩
      have htx :
          (t j).1 = outside j hjOld := by
        dsimp [t]
        rw [dif_neg hji, if_pos hsjE]
        dsimp [alt]
        rw [dif_neg hjOld]
      have hxOutside : x = outside j hjOld :=
        hjx.symm.trans htx
      apply (Finset.mem_sdiff.mp
        (houtsideSpec j hjOld)).2
      apply Finset.mem_union_right U
      rw [← hxOutside]
      exact Finset.mem_coe.mp hxE
    · have htx : (t j).1 = (s j).1 :=
        hmissKeep j hji hsjE
      have hxs : x = (s j).1 := hjx.symm.trans htx
      exact hsjE (hxs ▸ Finset.mem_coe.mp hxE)

/-- Protected completion with a finite old-block exception.

This existential-witness wrapper is the public difference form: a failed
completion exposes an old selected summand and removes it from the retained
repair support to obtain a represented coherent difference. -/
theorem blockAlignedSafeSwap_extends_protected_or_oldDifference
    {A : Set ℕ} {k q : ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D U J : Finset ℕ} {i b : ℕ}
    (hbBlock : b ∈ (F i).erase (s i).1)
    (hbU : b ∉ U)
    (hUselected : Disjoint (U : Set ℕ) (selectedSet s))
    (hrepair :
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1))
        (((D.erase (s i).1 ∪ {b} : Finset ℕ) : Set ℕ)) q)
    (hcontemporary :
      ∀ j, j ∉ J → U.card + (k + 1) < (F j).card) :
    (∃ t : BlockSelector F,
        Disjoint (U : Set ℕ) (selectedSet t) ∧
        ¬ DestroysAt
          (additiveSupportFamily A (k + 1))
          (selectedSet t) q) ∨
      ∃ j ∈ J, (s j).1 ≤ q ∧
        (additiveSupportFamily A k (q - (s j).1)).Nonempty := by
  obtain ⟨E, hER, hEswap⟩ :=
    not_destroysAt_iff.mp hrepair
  obtain hcompletion | ⟨j, hjJ, hsjE⟩ :=
    blockAlignedRepairWitness_extends_protected_or_oldCollision
      P s hbBlock hbU hUselected hER hEswap hcontemporary
  · exact Or.inl hcompletion
  · right
    have hsjLe : (s j).1 ≤ q :=
      additiveSupportFamily_supportsBounded
        A (k + 1) q E hER (s j).1 hsjE
    obtain ⟨H, hHR, _hEeq⟩ :=
      additiveSupport_remove_hit_succ hER hsjE
    exact ⟨j, hjJ, hsjLe, H, hHR⟩

/-- Certificate migration forced by an aligned safe repair.  If `Q` is a
finite selector certificate and a full selector repair makes `q ∈ Q`
survive, the repaired selector must destroy a different member of `Q`. -/
theorem blockAlignedSafeSwap_forces_certificateMigration
    {A : Set ℕ} {k q : ℕ} {Q : Finset ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D : Finset ℕ} {i b : ℕ}
    (hcert : ∀ t : BlockSelector F, ∃ u ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u)
    (hbBlock : b ∈ (F i).erase (s i).1)
    (hrepair :
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1))
        (((D.erase (s i).1 ∪ {b} : Finset ℕ) : Set ℕ)) q)
    (hblocks : ∀ j, k + 1 < (F j).card) :
    ∃ t : BlockSelector F, ∃ u ∈ Q, u ≠ q ∧
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u := by
  obtain ⟨t, _hti, _hkeep, hqSurvives⟩ :=
    blockAlignedSafeSwap_extends_to_selectorSurvival
      P s hbBlock hrepair hblocks
  obtain ⟨u, huQ, huDestroy⟩ := hcert t
  refine ⟨t, u, huQ, ?_, huDestroy⟩
  intro huq
  subst u
  exact hqSurvives huDestroy

/-- A protected support for every other certificate target turns a
block-aligned safe swap into an outright contradiction.

The protected-union completion preserves `q` and avoids `U`.  Every other
target has a support inside `U`, so it survives as well.  No member of the
certificate can then be destroyed. -/
theorem blockAlignedSafeSwap_impossible_of_protectedCertificateSupports
    {A : Set ℕ} {k q : ℕ} {Q U : Finset ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D : Finset ℕ} {i b : ℕ}
    (hcert : ∀ t : BlockSelector F, ∃ u ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u)
    (hprotected : ∀ u ∈ Q, u ≠ q →
      ∃ E ∈ additiveSupportFamily A (k + 1) u,
        (E : Set ℕ) ⊆ (U : Set ℕ))
    (hbBlock : b ∈ (F i).erase (s i).1)
    (hbU : b ∉ U)
    (hUselected : Disjoint (U : Set ℕ) (selectedSet s))
    (hblocks : ∀ j, U.card + (k + 1) < (F j).card) :
    DestroysAt
      (additiveSupportFamily A (k + 1))
      (((D.erase (s i).1 ∪ {b} : Finset ℕ) : Set ℕ)) q := by
  by_contra hrepair
  obtain ⟨t, _hti, hUavoid, hqSurvives⟩ :=
    blockAlignedSafeSwap_extends_avoiding_protectedUnion
      P s hbBlock hbU hUselected hrepair hblocks
  obtain ⟨u, huQ, huDestroy⟩ := hcert t
  by_cases huq : u = q
  · subst u
    exact hqSurvives huDestroy
  · obtain ⟨E, hER, hEU⟩ := hprotected u huQ huq
    exact (huDestroy E hER)
      (Set.disjoint_of_subset_left hEU hUavoid)

/-- A failed protected completion retains a private collision witness.

Besides locating an old selected summand in the repair support, this version
records that the support meets the minimal destroyer at exactly the active
contemporary value.  Consequently collision witnesses obtained from
different active destroyer points are distinct, even if they choose the same
old block. -/
theorem blockAlignedSafeSwap_certificate_forces_oldCollision
    {A C : Set ℕ} {k q : ℕ} {Q U J : Finset ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition C F)
    (s : BlockSelector F) {D : Finset ℕ} {i b : ℕ}
    (hcert : ∀ t : BlockSelector F, ∃ u ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u)
    (hprotected : ∀ u ∈ Q, u ≠ q →
      ∃ E ∈ additiveSupportFamily A (k + 1) u,
        (E : Set ℕ) ⊆ (U : Set ℕ))
    (hDdestroy :
      DestroysAt
        (additiveSupportFamily A (k + 1)) (D : Set ℕ) q)
    (hactive : (s i).1 ∈ D)
    (hbBlock : b ∈ (F i).erase (s i).1)
    (hbU : b ∉ U)
    (hUselected : Disjoint (U : Set ℕ) (selectedSet s))
    (hrepair :
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1))
        (((D.erase (s i).1 ∪ {b} : Finset ℕ) : Set ℕ)) q)
    (hcontemporary :
      ∀ j, j ∉ J → U.card + (k + 1) < (F j).card) :
    ∃ j ∈ J, ∃ E ∈ additiveSupportFamily A (k + 1) q,
      (s j).1 ∈ E ∧ E ∩ D = {(s i).1} := by
  classical
  obtain ⟨E, hER, hEswap⟩ :=
    not_destroysAt_iff.mp hrepair
  obtain ⟨t, hUavoid, hqSurvives⟩ | ⟨j, hjJ, hsjE⟩ :=
    blockAlignedRepairWitness_extends_protected_or_oldCollision
      P s hbBlock hbU hUselected hER hEswap hcontemporary
  · obtain ⟨u, huQ, huDestroy⟩ := hcert t
    by_cases huq : u = q
    · subst u
      exact (hqSurvives huDestroy).elim
    · obtain ⟨G, hGR, hGU⟩ := hprotected u huQ huq
      exact ((huDestroy G hGR)
        (Set.disjoint_of_subset_left hGU hUavoid)).elim
  · have hactiveE : (s i).1 ∈ E := by
      by_contra hsiE
      apply hDdestroy E hER
      rw [Set.disjoint_left]
      intro x hxE hxD
      by_cases hxi : x = (s i).1
      · subst x
        exact hsiE (Finset.mem_coe.mp hxE)
      · apply Set.disjoint_left.mp hEswap hxE
        apply Finset.mem_coe.mpr
        exact Finset.mem_union_left _
          (Finset.mem_erase.mpr
            ⟨hxi, Finset.mem_coe.mp hxD⟩)
    have hprivate : E ∩ D = {(s i).1} := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxE, hxD⟩ := Finset.mem_inter.mp hx
        have hxi : x = (s i).1 := by
          by_contra hne
          apply Set.disjoint_left.mp hEswap
            (Finset.mem_coe.mpr hxE)
          apply Finset.mem_coe.mpr
          exact Finset.mem_union_left _
            (Finset.mem_erase.mpr ⟨hne, hxD⟩)
        simpa [hxi]
      · intro hx
        have hxi : x = (s i).1 := by simpa using hx
        subst x
        exact Finset.mem_inter.mpr ⟨hactiveE, hactive⟩
    exact ⟨j, hjJ, E, hER, hsjE, hprivate⟩

/-- Bounded old differences sharpen a certificate collision to an
undersized old block.

The collision support and its private-hit identity are retained exactly as
in `blockAlignedSafeSwap_certificate_forces_oldCollision`.  The additional
counting input says that every sufficiently large old block has a universal
second choice avoiding the protected set and all of its possible collision
supports.  Hence the certificate can force a collision only at a block
whose capacity is at most `U.card + (k+1)r`. -/
theorem blockAlignedSafeSwap_certificate_forces_smallOldCollision
    {A : Set ℕ} {k q r : ℕ} {Q U J : Finset ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D : Finset ℕ} {i b : ℕ}
    (hcert : ∀ t : BlockSelector F, ∃ u ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u)
    (hprotected : ∀ u ∈ Q, u ≠ q →
      ∃ E ∈ additiveSupportFamily A (k + 1) u,
        (E : Set ℕ) ⊆ (U : Set ℕ))
    (hDdestroy :
      DestroysAt
        (additiveSupportFamily A (k + 1)) (D : Set ℕ) q)
    (hactive : (s i).1 ∈ D)
    (hbBlock : b ∈ (F i).erase (s i).1)
    (hbU : b ∉ U)
    (hUselected : Disjoint (U : Set ℕ) (selectedSet s))
    (hrepair :
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1))
        (((D.erase (s i).1 ∪ {b} : Finset ℕ) : Set ℕ)) q)
    (holdBound :
      ∀ j ∈ J,
        (additiveSupportFamily A k
          (q - (s j).1)).card ≤ r)
    (hcontemporary :
      ∀ j, j ∉ J → U.card + (k + 1) < (F j).card) :
    ∃ j ∈ J, ∃ E ∈ additiveSupportFamily A (k + 1) q,
      (s j).1 ∈ E ∧
      E ∩ D = {(s i).1} ∧
      (F j).card ≤ U.card + (k + 1) * r := by
  classical
  obtain ⟨E, hER, hEswap⟩ :=
    not_destroysAt_iff.mp hrepair
  obtain ⟨t, hUavoid, hqSurvives⟩ |
      ⟨j, hjJ, hsjE, hjSmall⟩ :=
    blockAlignedRepairWitness_extends_protected_or_smallOldCollision
      P s hbBlock hbU hUselected hER hEswap
        holdBound hcontemporary
  · obtain ⟨u, huQ, huDestroy⟩ := hcert t
    by_cases huq : u = q
    · subst u
      exact (hqSurvives huDestroy).elim
    · obtain ⟨G, hGR, hGU⟩ := hprotected u huQ huq
      exact ((huDestroy G hGR)
        (Set.disjoint_of_subset_left hGU hUavoid)).elim
  · have hactiveE : (s i).1 ∈ E := by
      by_contra hsiE
      apply hDdestroy E hER
      rw [Set.disjoint_left]
      intro x hxE hxD
      by_cases hxi : x = (s i).1
      · subst x
        exact hsiE (Finset.mem_coe.mp hxE)
      · apply Set.disjoint_left.mp hEswap hxE
        apply Finset.mem_coe.mpr
        exact Finset.mem_union_left _
          (Finset.mem_erase.mpr
            ⟨hxi, Finset.mem_coe.mp hxD⟩)
    have hprivate : E ∩ D = {(s i).1} := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxE, hxD⟩ := Finset.mem_inter.mp hx
        have hxi : x = (s i).1 := by
          by_contra hne
          apply Set.disjoint_left.mp hEswap
            (Finset.mem_coe.mpr hxE)
          apply Finset.mem_coe.mpr
          exact Finset.mem_union_left _
            (Finset.mem_erase.mpr ⟨hne, hxD⟩)
        simpa [hxi]
      · intro hx
        have hxi : x = (s i).1 := by simpa using hx
        subst x
        exact Finset.mem_inter.mpr ⟨hactiveE, hactive⟩
    exact ⟨j, hjJ, E, hER, hsjE, hprivate, hjSmall⟩

/-- With only contemporary blocks large, a safe aligned swap in a selector
certificate cannot disappear: it must expose an old selected summand whose
coherent lower-order difference is represented.

The protected-completion horn would preserve every certificate target and
is therefore impossible. -/
theorem blockAlignedSafeSwap_certificate_forces_oldDifference
    {A : Set ℕ} {k q : ℕ} {Q U J : Finset ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D : Finset ℕ} {i b : ℕ}
    (hcert : ∀ t : BlockSelector F, ∃ u ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u)
    (hprotected : ∀ u ∈ Q, u ≠ q →
      ∃ E ∈ additiveSupportFamily A (k + 1) u,
        (E : Set ℕ) ⊆ (U : Set ℕ))
    (hbBlock : b ∈ (F i).erase (s i).1)
    (hbU : b ∉ U)
    (hUselected : Disjoint (U : Set ℕ) (selectedSet s))
    (hrepair :
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1))
        (((D.erase (s i).1 ∪ {b} : Finset ℕ) : Set ℕ)) q)
    (hcontemporary :
      ∀ j, j ∉ J → U.card + (k + 1) < (F j).card) :
    ∃ j ∈ J, (s j).1 ≤ q ∧
      (additiveSupportFamily A k (q - (s j).1)).Nonempty := by
  obtain ⟨t, hUavoid, hqSurvives⟩ | holdDifference :=
    blockAlignedSafeSwap_extends_protected_or_oldDifference
      P s hbBlock hbU hUselected hrepair hcontemporary
  · obtain ⟨u, huQ, huDestroy⟩ := hcert t
    by_cases huq : u = q
    · subst u
      exact (hqSurvives huDestroy).elim
    · obtain ⟨E, hER, hEU⟩ := hprotected u huQ huq
      exact ((huDestroy E hER)
        (Set.disjoint_of_subset_left hEU hUavoid)).elim
  · exact holdDifference

/-- When the repaired target is the largest member of a finite certificate,
certificate migration is strictly downward. -/
theorem blockAlignedSafeSwap_at_max_forces_strictDescent
    {A : Set ℕ} {k q : ℕ} {Q : Finset ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D : Finset ℕ} {i b : ℕ}
    (hqMax : ∀ u ∈ Q, u ≤ q)
    (hcert : ∀ t : BlockSelector F, ∃ u ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u)
    (hbBlock : b ∈ (F i).erase (s i).1)
    (hrepair :
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1))
        (((D.erase (s i).1 ∪ {b} : Finset ℕ) : Set ℕ)) q)
    (hblocks : ∀ j, k + 1 < (F j).card) :
    ∃ t : BlockSelector F, ∃ u ∈ Q, u < q ∧
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u := by
  obtain ⟨t, u, huQ, hune, huDestroy⟩ :=
    blockAlignedSafeSwap_forces_certificateMigration
      P s (Q := Q) (q := q) hcert hbBlock hrepair hblocks
  exact ⟨t, u, huQ, lt_of_le_of_ne (hqMax u huQ) hune, huDestroy⟩

/-- Package one support surviving the localized selector for every
certificate target other than `q`.

Their union avoids the selector and has the sharp rank-times-target-count
cardinality bound.  This is the protected set used to prevent a repair of
`q` from creating collateral destruction elsewhere in the certificate. -/
theorem exists_protectedSupportUnion_of_targetLocalization
    {A : Set ℕ} {k q : ℕ} {Q : Finset ℕ}
    {F : ℕ → Finset ℕ} (s : BlockSelector F)
    (hother : ∀ u ∈ Q, u ≠ q →
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet s) u) :
    ∃ U : Finset ℕ,
      U.card ≤ (k + 1) * Q.card ∧
      Disjoint (U : Set ℕ) (selectedSet s) ∧
      ∀ u ∈ Q, u ≠ q →
        ∃ E ∈ additiveSupportFamily A (k + 1) u,
          (E : Set ℕ) ⊆ (U : Set ℕ) := by
  classical
  let witness :
      ∀ u : {n // n ∈ Q.erase q},
        ∃ E ∈ additiveSupportFamily A (k + 1) u.1,
          Disjoint (E : Set ℕ) (selectedSet s) := fun u =>
    not_destroysAt_iff.mp
      (hother u.1 (Finset.mem_erase.mp u.2).2
        (Finset.mem_erase.mp u.2).1)
  let c :
      FiniteSupportChoice
        (additiveSupportFamily A (k + 1)) (Q.erase q) := fun u =>
    ⟨(witness u).choose, (witness u).choose_spec.1⟩
  let U : Finset ℕ := finiteSupportChoiceUnion c
  have hcdisjoint :
      ∀ u : {n // n ∈ Q.erase q},
        Disjoint ((c u).1 : Set ℕ) (selectedSet s) := by
    intro u
    exact (witness u).choose_spec.2
  have hUdisjoint :
      Disjoint (U : Set ℕ) (selectedSet s) := by
    rw [Set.disjoint_left]
    intro x hxU hxSelected
    obtain ⟨u, _huAttach, hxSupport⟩ :=
      Finset.mem_biUnion.mp (Finset.mem_coe.mp hxU)
    exact Set.disjoint_left.mp (hcdisjoint u)
      (Finset.mem_coe.mpr hxSupport) hxSelected
  have hUcardErase :
      U.card ≤ (k + 1) * (Q.erase q).card := by
    exact finiteSupportChoiceUnion_card_le
      (additiveSupportFamily_cardAtMost A (k + 1)) c
  have hUcard : U.card ≤ (k + 1) * Q.card := by
    exact hUcardErase.trans
      (Nat.mul_le_mul_left (k + 1)
        (Finset.card_erase_le (s := Q) (a := q)))
  refine ⟨U, hUcard, hUdisjoint, ?_⟩
  intro u huQ huq
  let u' : {n // n ∈ Q.erase q} :=
    ⟨u, Finset.mem_erase.mpr ⟨huq, huQ⟩⟩
  refine ⟨(c u').1, (c u').2, ?_⟩
  intro x hx
  exact Finset.mem_coe.mpr
    (finiteSupportChoice_subset_union c u'
      (Finset.mem_coe.mp hx))

/-- Choose one support surviving the current selector for every certificate
target strictly larger than `q`.

Unlike the union-only packaging below, this retains the target-to-support
incidence map.  That extra data is what lets an obstruction inside one old
block be compressed to the strictly larger targets which actually meet the
block. -/
theorem exists_survivingLargerSupportChoice
    {A : Set ℕ} {k q : ℕ} {Q : Finset ℕ}
    {F : ℕ → Finset ℕ} (s : BlockSelector F)
    (hlarger : ∀ u ∈ Q, q < u →
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet s) u) :
    ∃ c :
        FiniteSupportChoice
          (additiveSupportFamily A (k + 1))
          (Q.filter fun u => q < u),
      Disjoint (finiteSupportChoiceUnion c : Set ℕ) (selectedSet s) := by
  classical
  let Larger : Finset ℕ := Q.filter fun u => q < u
  let witness :
      ∀ u : {n // n ∈ Larger},
        ∃ E ∈ additiveSupportFamily A (k + 1) u.1,
          Disjoint (E : Set ℕ) (selectedSet s) := fun u =>
    not_destroysAt_iff.mp
      (hlarger u.1
        (Finset.mem_filter.mp u.2).1
        (Finset.mem_filter.mp u.2).2)
  let c :
      FiniteSupportChoice
        (additiveSupportFamily A (k + 1)) Larger := fun u =>
    ⟨(witness u).choose, (witness u).choose_spec.1⟩
  refine ⟨c, ?_⟩
  rw [Set.disjoint_left]
  intro x hxU hxSelected
  obtain ⟨u, _huAttach, hxSupport⟩ :=
    Finset.mem_biUnion.mp (Finset.mem_coe.mp hxU)
  exact Set.disjoint_left.mp (witness u).choose_spec.2
    (Finset.mem_coe.mpr hxSupport) hxSelected

/-- Store one surviving support for every certificate target strictly larger
than `q`.

The union is disjoint from the current selector and has the same uniform
rank-times-certificate cardinality bound as full target localization. -/
theorem exists_protectedSupportUnion_of_survivingLargerTargets
    {A : Set ℕ} {k q : ℕ} {Q : Finset ℕ}
    {F : ℕ → Finset ℕ} (s : BlockSelector F)
    (hlarger : ∀ u ∈ Q, q < u →
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet s) u) :
    ∃ U : Finset ℕ,
      U.card ≤ (k + 1) * Q.card ∧
      Disjoint (U : Set ℕ) (selectedSet s) ∧
      ∀ u ∈ Q, q < u →
        ∃ E ∈ additiveSupportFamily A (k + 1) u,
          (E : Set ℕ) ⊆ (U : Set ℕ) := by
  classical
  let larger : Finset ℕ := Q.filter fun u => q < u
  let witness :
      ∀ u : {n // n ∈ larger},
        ∃ E ∈ additiveSupportFamily A (k + 1) u.1,
          Disjoint (E : Set ℕ) (selectedSet s) := fun u =>
    not_destroysAt_iff.mp
      (hlarger u.1
        (Finset.mem_filter.mp u.2).1
        (Finset.mem_filter.mp u.2).2)
  let c :
      FiniteSupportChoice
        (additiveSupportFamily A (k + 1)) larger := fun u =>
    ⟨(witness u).choose, (witness u).choose_spec.1⟩
  let U : Finset ℕ := finiteSupportChoiceUnion c
  have hUdisjoint :
      Disjoint (U : Set ℕ) (selectedSet s) := by
    rw [Set.disjoint_left]
    intro x hxU hxSelected
    obtain ⟨u, _huAttach, hxSupport⟩ :=
      Finset.mem_biUnion.mp (Finset.mem_coe.mp hxU)
    exact Set.disjoint_left.mp (witness u).choose_spec.2
      (Finset.mem_coe.mpr hxSupport) hxSelected
  have hUcardLarger :
      U.card ≤ (k + 1) * larger.card := by
    exact finiteSupportChoiceUnion_card_le
      (additiveSupportFamily_cardAtMost A (k + 1)) c
  have hUcard : U.card ≤ (k + 1) * Q.card := by
    exact hUcardLarger.trans
      (Nat.mul_le_mul_left (k + 1)
        (Finset.card_le_card (Finset.filter_subset _ _)))
  refine ⟨U, hUcard, hUdisjoint, ?_⟩
  intro u huQ hqu
  let u' : {n // n ∈ larger} :=
    ⟨u, Finset.mem_filter.mpr ⟨huQ, hqu⟩⟩
  refine ⟨(c u').1, (c u').2, ?_⟩
  intro x hx
  exact Finset.mem_coe.mpr
    (finiteSupportChoice_subset_union c u'
      (Finset.mem_coe.mp hx))

/-- Store one surviving support for every *other* target of a
target-localized certificate selector.

This is stronger than the ordered version above: avoiding the returned union
preserves all certificate targets except `q`.  It is the finite augmenting
path interface for a lower-gap repair—if the repaired selector also
preserves `q`, it contradicts the certificate outright rather than merely
migrating its destroyed target. -/
theorem exists_protectedSupportUnion_of_targetLocalizedSelector
    {A : Set ℕ} {k q : ℕ} {Q : Finset ℕ}
    {F : ℕ → Finset ℕ} (s : BlockSelector F)
    (hother : ∀ u ∈ Q, u ≠ q →
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet s) u) :
    ∃ U : Finset ℕ,
      U.card ≤ (k + 1) * Q.card ∧
      Disjoint (U : Set ℕ) (selectedSet s) ∧
      ∀ u ∈ Q, u ≠ q →
        ∃ E ∈ additiveSupportFamily A (k + 1) u,
          (E : Set ℕ) ⊆ (U : Set ℕ) := by
  classical
  let other : Finset ℕ := Q.filter fun u => u ≠ q
  let witness :
      ∀ u : {n // n ∈ other},
        ∃ E ∈ additiveSupportFamily A (k + 1) u.1,
          Disjoint (E : Set ℕ) (selectedSet s) := fun u =>
    not_destroysAt_iff.mp
      (hother u.1
        (Finset.mem_filter.mp u.2).1
        (Finset.mem_filter.mp u.2).2)
  let c :
      FiniteSupportChoice
        (additiveSupportFamily A (k + 1)) other := fun u =>
    ⟨(witness u).choose, (witness u).choose_spec.1⟩
  let U : Finset ℕ := finiteSupportChoiceUnion c
  have hUdisjoint :
      Disjoint (U : Set ℕ) (selectedSet s) := by
    rw [Set.disjoint_left]
    intro x hxU hxSelected
    obtain ⟨u, _huAttach, hxSupport⟩ :=
      Finset.mem_biUnion.mp (Finset.mem_coe.mp hxU)
    exact Set.disjoint_left.mp (witness u).choose_spec.2
      (Finset.mem_coe.mpr hxSupport) hxSelected
  have hUcardOther :
      U.card ≤ (k + 1) * other.card := by
    exact finiteSupportChoiceUnion_card_le
      (additiveSupportFamily_cardAtMost A (k + 1)) c
  have hUcard : U.card ≤ (k + 1) * Q.card := by
    exact hUcardOther.trans
      (Nat.mul_le_mul_left (k + 1)
        (Finset.card_le_card (Finset.filter_subset _ _)))
  refine ⟨U, hUcard, hUdisjoint, ?_⟩
  intro u huQ huq
  let u' : {n // n ∈ other} :=
    ⟨u, Finset.mem_filter.mpr ⟨huQ, huq⟩⟩
  refine ⟨(c u').1, (c u').2, ?_⟩
  intro x hx
  exact Finset.mem_coe.mpr
    (finiteSupportChoice_subset_union c u'
      (Finset.mem_coe.mp hx))

/-- A lower-gap repair of a target-localized certificate either augments all
the way to a selector preserving the whole certificate, or collides in an
exceptional old block.

The first alternative is impossible because `Q` is a selector certificate:
the repair support preserves `q`, while avoidance of the all-other protected
union preserves every `u ≠ q`.  Hence every private hit of the minimal
destroyer supplies an actual old-block collision support, still carrying
the identity `E ∩ D = {d}` needed for amplification. -/
theorem targetLocalized_lowerGapRepair_forces_oldCollision
    {A : Set ℕ} {k q b : ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D Q U J : Finset ℕ}
    (hcert : ∀ t : BlockSelector F, ∃ u ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u)
    (hprotected : ∀ u ∈ Q, u ≠ q →
      ∃ E ∈ additiveSupportFamily A (k + 1) u,
        (E : Set ℕ) ⊆ (U : Set ℕ))
    (hUselected : Disjoint (U : Set ℕ) (selectedSet s))
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hbA : b ∈ A)
    (hbU : b ∉ U)
    (hgap : additiveSupportFamily A k (q - b) = ∅)
    (hblocks : ∀ j, j ∉ J →
      U.card + (k + 1) < (F j).card) :
    ∀ d ∈ D, ∃ j ∈ J,
      ∃ E ∈ additiveSupportFamily A (k + 1) q,
        (s j).1 ∈ E ∧ E ∩ D = {d} := by
  intro d hdD
  obtain ⟨t, htU, htq⟩ | hcollision :=
    lowerGapRepair_extends_protected_or_oldCollision
      P s hminimal hdD hbA hbU hgap hUselected hblocks
  · obtain ⟨u, huQ, huDestroy⟩ := hcert t
    by_cases huq : u = q
    · subst u
      exact (htq huDestroy).elim
    · obtain ⟨E, hER, hEU⟩ := hprotected u huQ huq
      exact ((huDestroy E hER)
        (Set.disjoint_of_subset_left hEU htU)).elim
  · exact hcollision

/-- A protected repair makes certificate migration strictly descend.

The repaired selector preserves `q` and avoids one stored support for every
larger certificate target.  Hence the target destroyed by the certificate
is neither `q` nor larger than `q`; it is strictly smaller. -/
theorem protectedSelectorRepair_forces_strictCertificateDescent
    {A : Set ℕ} {k q : ℕ} {Q U : Finset ℕ}
    {F : ℕ → Finset ℕ}
    (hcert : ∀ t : BlockSelector F, ∃ u ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u)
    (hprotected : ∀ u ∈ Q, q < u →
      ∃ E ∈ additiveSupportFamily A (k + 1) u,
        (E : Set ℕ) ⊆ (U : Set ℕ))
    {t : BlockSelector F}
    (hUavoid : Disjoint (U : Set ℕ) (selectedSet t))
    (hqSurvives :
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1))
        (selectedSet t) q) :
    ∃ u ∈ Q, u < q ∧
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u := by
  obtain ⟨u, huQ, huDestroy⟩ := hcert t
  have hune : u ≠ q := by
    intro huq
    subst u
    exact hqSurvives huDestroy
  have hnotLarger : ¬ q < u := by
    intro hqu
    obtain ⟨E, hER, hEU⟩ := hprotected u huQ hqu
    exact (huDestroy E hER)
      (Set.disjoint_of_subset_left hEU hUavoid)
  exact ⟨u, huQ, by omega, huDestroy⟩

/-- Strict protected repair at the maximal currently destroyed target cannot
persist on a finite certificate.

For each selector, take the maximum member of `Q` that it destroys.  A step
which preserves that target and every larger target produces a selector with
a strictly smaller maximum.  Strong induction on that natural-valued
measure rules out the certificate entirely. -/
theorem finiteSelectorCertificate_impossible_of_strictRepairStep
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    {F : ℕ → Finset ℕ}
    (s₀ : BlockSelector F)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet s) q)
    (hstep : ∀ s : BlockSelector F, ∀ q ∈ Q,
      DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet s) q →
      (∀ u ∈ Q, q < u →
        ¬ DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet s) u) →
      ∃ t : BlockSelector F,
        ¬ DestroysAt
            (additiveSupportFamily A (k + 1)) (selectedSet t) q ∧
        ∀ u ∈ Q, q < u →
          ¬ DestroysAt
            (additiveSupportFamily A (k + 1)) (selectedSet t) u) :
    False := by
  classical
  let bad (s : BlockSelector F) : Finset ℕ :=
    Q.filter fun q =>
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet s) q
  have hbad : ∀ s : BlockSelector F, (bad s).Nonempty := by
    intro s
    obtain ⟨q, hqQ, hqDestroy⟩ := hcert s
    exact ⟨q, Finset.mem_filter.mpr ⟨hqQ, hqDestroy⟩⟩
  let top (s : BlockSelector F) : ℕ :=
    (bad s).max' (hbad s)
  have htopMem : ∀ s : BlockSelector F, top s ∈ bad s := by
    intro s
    exact Finset.max'_mem (bad s) (hbad s)
  have htopQ : ∀ s : BlockSelector F, top s ∈ Q := by
    intro s
    exact (Finset.mem_filter.mp (htopMem s)).1
  have htopDestroy : ∀ s : BlockSelector F,
      DestroysAt
        (additiveSupportFamily A (k + 1))
        (selectedSet s) (top s) := by
    intro s
    exact (Finset.mem_filter.mp (htopMem s)).2
  have htopLargest : ∀ s : BlockSelector F, ∀ u ∈ Q,
      top s < u →
        ¬ DestroysAt
          (additiveSupportFamily A (k + 1))
          (selectedSet s) u := by
    intro s u huQ htopu huDestroy
    have huBad : u ∈ bad s :=
      Finset.mem_filter.mpr ⟨huQ, huDestroy⟩
    have hule : u ≤ top s :=
      Finset.le_max' (bad s) u huBad
    omega
  have hdescend : ∀ s : BlockSelector F,
      ∃ t : BlockSelector F, top t < top s := by
    intro s
    obtain ⟨t, htopSurvives, hlargerSurvives⟩ :=
      hstep s (top s) (htopQ s) (htopDestroy s)
        (htopLargest s)
    refine ⟨t, ?_⟩
    by_contra hnot
    have hle : top s ≤ top t := Nat.le_of_not_gt hnot
    rcases eq_or_lt_of_le hle with heq | hlt
    · rw [heq] at htopSurvives
      exact htopSurvives (htopDestroy t)
    · exact (hlargerSurvives (top t) (htopQ t) hlt)
        (htopDestroy t)
  have himpossible :
      ∀ n, ∀ s : BlockSelector F, top s = n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro s hsn
        obtain ⟨t, hts⟩ := hdescend s
        exact ih (top t) (by simpa only [hsn] using hts) t rfl
  exact himpossible (top s₀) s₀ rfl

/-- Target localization eliminates the safe horn once the active block has
room both for the incidence test and for all protected certificate supports.

Choose one support surviving the localized selector for every target other
than `q`, and let `U` be their union.  Test only same-block replacements
outside `U`.  A safe replacement would preserve all targets in the
certificate by
`blockAlignedSafeSwap_impossible_of_protectedCertificateSupports`;
therefore the incidence fork must produce coherent lower-order support
growth (unless the support family at `q` already exceeds `m`). -/
theorem positiveOrder_targetLocalizedCertificate_largeBlocks_forces_supportGrowth
    {A : Set ℕ} {k q r m : ℕ} {Q : Finset ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D : Finset ℕ}
    (hk : 0 < k)
    (hrepresented :
      (additiveSupportFamily A (k + 1) q).Nonempty)
    (hcert : ∀ t : BlockSelector F, ∃ u ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u)
    (hother : ∀ u ∈ Q, u ≠ q →
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet s) u)
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hDselected : (D : Set ℕ) ⊆ selectedSet s)
    (hblocks : ∀ i,
      m * (k * r) + (k + 1) * Q.card + k + 3 ≤
        (F i).card) :
    m < (additiveSupportFamily A (k + 1) q).card ∨
      ∃ x ∈ D, x ≤ q ∧
        r < (additiveSupportFamily A k (q - x)).card := by
  classical
  by_cases hsupport :
      m < (additiveSupportFamily A (k + 1) q).card
  · exact Or.inl hsupport
  · right
    obtain ⟨U, hUcard, hUselected, hprotected⟩ :=
      exists_protectedSupportUnion_of_targetLocalization
        s hother
    have hDcard : D.card ≤ m :=
      hminimal.card_le_supportFamily.trans
        (Nat.le_of_not_gt hsupport)
    have hDnonempty : D.Nonempty := by
      by_contra hDempty
      rw [Finset.not_nonempty_iff_eq_empty.mp hDempty] at hminimal
      obtain ⟨E, hER⟩ := hrepresented
      exact hminimal.1 E hER (by simp)
    obtain ⟨d, hdD⟩ := hDnonempty
    obtain ⟨i, hdi⟩ :=
      hDselected (Finset.mem_coe.mpr hdD)
    have hactive : (s i).1 ∈ D := by
      change (fun j => (s j).1) i ∈ D
      rw [hdi]
      exact hdD
    have heraseCard :
        ((F i).erase (s i).1).card + 1 = (F i).card :=
      Finset.card_erase_add_one (s i).2
    have hinterCard :
        (((F i).erase (s i).1) ∩ U).card ≤ U.card :=
      Finset.card_le_card Finset.inter_subset_right
    have hsplit :=
      Finset.card_sdiff_add_card_inter
        ((F i).erase (s i).1) U
    have hDmul :
        D.card * (k * r) ≤ m * (k * r) :=
      Nat.mul_le_mul_right (k * r) hDcard
    have hlarge :
        D.card * (k * r) <
          (((F i).erase (s i).1) \ U).card := by
      have hblock := hblocks i
      omega
    obtain hsafe | hgrowth :=
      positiveOrder_minimalDestroyer_activeBlock_safeSwap_avoiding_or_differenceGrowth
        P s hk hminimal hDselected hactive hlarge
    · obtain ⟨b, hbBlock, hbU, hrepair⟩ := hsafe
      have hcompletionBlocks :
          ∀ j, U.card + (k + 1) < (F j).card := by
        intro j
        have hblock := hblocks j
        omega
      have himpossible :=
        blockAlignedSafeSwap_impossible_of_protectedCertificateSupports
          P s (D := D) hcert hprotected hbBlock hbU hUselected
            hcompletionBlocks
      exact (hrepair himpossible).elim
    · exact hgrowth

/-- One active-coordinate old/contemporary split retaining the collision
support.

If the active private hit is already in an old block, return its private
support.  Otherwise the contemporary block has enough alternatives for the
protected incidence test.  Difference growth is then forced unless a safe
swap exposes some (possibly different) old selected summand in a support
whose unique destroyer hit is the active value.

Unlike the uniform large-block theorem, only blocks outside the finite old
index set `J` carry the large capacity hypothesis. -/
theorem positiveOrder_targetLocalized_activeBlock_growth_or_oldCollision
    {A : Set ℕ} {k q r : ℕ} {Q J : Finset ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D : Finset ℕ} {i : ℕ}
    (hk : 0 < k)
    (hcert : ∀ t : BlockSelector F, ∃ u ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u)
    (hother : ∀ u ∈ Q, u ≠ q →
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet s) u)
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hDselected : (D : Set ℕ) ⊆ selectedSet s)
    (hactive : (s i).1 ∈ D)
    (hcontemporary : ∀ j, j ∉ J →
      D.card * (k * r) + (k + 1) * Q.card + k + 3 ≤
        (F j).card) :
    (∃ x ∈ D, x ≤ q ∧
        r < (additiveSupportFamily A k (q - x)).card) ∨
      ∃ j ∈ J, ∃ E ∈ additiveSupportFamily A (k + 1) q,
        (s j).1 ∈ E ∧ E ∩ D = {(s i).1} := by
  classical
  by_cases hiOld : i ∈ J
  · right
    obtain ⟨E, hER, hEprivate⟩ :=
      hminimal.exists_uniqueHitSupport hactive
    have hsiE : (s i).1 ∈ E := by
      have hmem : (s i).1 ∈ E ∩ D := by
        rw [hEprivate]
        simp
      exact (Finset.mem_inter.mp hmem).1
    exact ⟨i, hiOld, E, hER, hsiE, hEprivate⟩
  · obtain ⟨U, hUcard, hUselected, hprotected⟩ :=
      exists_protectedSupportUnion_of_targetLocalization
        s hother
    have heraseCard :
        ((F i).erase (s i).1).card + 1 = (F i).card :=
      Finset.card_erase_add_one (s i).2
    have hinterCard :
        (((F i).erase (s i).1) ∩ U).card ≤ U.card :=
      Finset.card_le_card Finset.inter_subset_right
    have hsplit :=
      Finset.card_sdiff_add_card_inter
        ((F i).erase (s i).1) U
    have hlarge :
        D.card * (k * r) <
          (((F i).erase (s i).1) \ U).card := by
      have hblock := hcontemporary i hiOld
      omega
    obtain hsafe | hgrowth :=
      positiveOrder_minimalDestroyer_activeBlock_safeSwap_avoiding_or_differenceGrowth
        P s hk hminimal hDselected hactive hlarge
    · right
      obtain ⟨b, hbBlock, hbU, hrepair⟩ := hsafe
      have hcompletion :
          ∀ j, j ∉ J →
            U.card + (k + 1) < (F j).card := by
        intro j hjOld
        have hblock := hcontemporary j hjOld
        omega
      exact blockAlignedSafeSwap_certificate_forces_oldCollision
        P s hcert hprotected hminimal.1 hactive hbBlock hbU
          hUselected hrepair hcompletion
    · exact Or.inl hgrowth

/-- Reservoir-relative active-coordinate old/contemporary split.

This is the form used by the coherent infinite deletion: the blocks
partition a reservoir `C ⊆ A`, while all additive supports are still taken
in the original basis `A`. -/
theorem positiveOrder_targetLocalized_activeBlock_growth_or_oldCollision_onReservoir
    {A C : Set ℕ} {k q r : ℕ} {Q J : Finset ℕ}
    {F : ℕ → Finset ℕ} (hCA : C ⊆ A)
    (P : IsFiniteBlockPartition C F)
    (s : BlockSelector F) {D : Finset ℕ} {i : ℕ}
    (hk : 0 < k)
    (hcert : ∀ t : BlockSelector F, ∃ u ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u)
    (hother : ∀ u ∈ Q, u ≠ q →
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet s) u)
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hDselected : (D : Set ℕ) ⊆ selectedSet s)
    (hactive : (s i).1 ∈ D)
    (hcontemporary : ∀ j, j ∉ J →
      D.card * (k * r) + (k + 1) * Q.card + k + 3 ≤
        (F j).card) :
    (∃ x ∈ D, x ≤ q ∧
        r < (additiveSupportFamily A k (q - x)).card) ∨
      ∃ j ∈ J, ∃ E ∈ additiveSupportFamily A (k + 1) q,
        (s j).1 ∈ E ∧ E ∩ D = {(s i).1} := by
  classical
  by_cases hiOld : i ∈ J
  · right
    obtain ⟨E, hER, hEprivate⟩ :=
      hminimal.exists_uniqueHitSupport hactive
    have hsiE : (s i).1 ∈ E := by
      have hmem : (s i).1 ∈ E ∩ D := by
        rw [hEprivate]
        simp
      exact (Finset.mem_inter.mp hmem).1
    exact ⟨i, hiOld, E, hER, hsiE, hEprivate⟩
  · obtain ⟨U, hUcard, hUselected, hprotected⟩ :=
      exists_protectedSupportUnion_of_targetLocalization
        s hother
    have heraseCard :
        ((F i).erase (s i).1).card + 1 = (F i).card :=
      Finset.card_erase_add_one (s i).2
    have hinterCard :
        (((F i).erase (s i).1) ∩ U).card ≤ U.card :=
      Finset.card_le_card Finset.inter_subset_right
    have hsplit :=
      Finset.card_sdiff_add_card_inter
        ((F i).erase (s i).1) U
    have hlarge :
        D.card * (k * r) <
          (((F i).erase (s i).1) \ U).card := by
      have hblock := hcontemporary i hiOld
      omega
    obtain hsafe | hgrowth :=
      positiveOrder_minimalDestroyer_activeBlock_safeSwap_avoiding_or_differenceGrowth_onReservoir
        hCA P s hk hminimal hDselected hactive hlarge
    · right
      obtain ⟨b, hbBlock, hbU, hrepair⟩ := hsafe
      have hcompletion :
          ∀ j, j ∉ J →
            U.card + (k + 1) < (F j).card := by
        intro j hjOld
        have hblock := hcontemporary j hjOld
        omega
      exact blockAlignedSafeSwap_certificate_forces_oldCollision
        P s hcert hprotected hminimal.1 hactive hbBlock hbU
          hUselected hrepair hcompletion
    · exact Or.inl hgrowth

/-- Contemporary active-coordinate fork with universal old second choices.

Assume the lower support family at every old coherent difference has size at
most `r`.  The active contemporary block supplies either direct
difference-growth or a safe aligned swap.  In the safe branch, every old
block larger than the protected budget plus `(k+1)r` has a universal second
choice avoiding all collision supports.  Thus a certificate-forced private
collision can occur only at an explicitly undersized old block. -/
theorem positiveOrder_targetLocalized_contemporaryBlock_growth_or_smallOldCollision
    {A : Set ℕ} {k q r : ℕ} {Q J : Finset ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D : Finset ℕ} {i : ℕ}
    (hk : 0 < k)
    (hcert : ∀ t : BlockSelector F, ∃ u ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u)
    (hother : ∀ u ∈ Q, u ≠ q →
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet s) u)
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hDselected : (D : Set ℕ) ⊆ selectedSet s)
    (hactive : (s i).1 ∈ D)
    (hiNew : i ∉ J)
    (holdBound :
      ∀ j ∈ J,
        (additiveSupportFamily A k
          (q - (s j).1)).card ≤ r)
    (hcontemporary : ∀ j, j ∉ J →
      D.card * (k * r) + (k + 1) * Q.card + k + 3 ≤
        (F j).card) :
    (∃ x ∈ D, x ≤ q ∧
        r < (additiveSupportFamily A k (q - x)).card) ∨
      ∃ j ∈ J,
        (F j).card ≤
          (k + 1) * Q.card + (k + 1) * r ∧
        ∃ E ∈ additiveSupportFamily A (k + 1) q,
          (s j).1 ∈ E ∧ E ∩ D = {(s i).1} := by
  classical
  obtain ⟨U, hUcard, hUselected, hprotected⟩ :=
    exists_protectedSupportUnion_of_targetLocalization
      s hother
  have heraseCard :
      ((F i).erase (s i).1).card + 1 = (F i).card :=
    Finset.card_erase_add_one (s i).2
  have hinterCard :
      (((F i).erase (s i).1) ∩ U).card ≤ U.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hsplit :=
    Finset.card_sdiff_add_card_inter
      ((F i).erase (s i).1) U
  have hlarge :
      D.card * (k * r) <
        (((F i).erase (s i).1) \ U).card := by
    have hblock := hcontemporary i hiNew
    omega
  obtain hsafe | hgrowth :=
    positiveOrder_minimalDestroyer_activeBlock_safeSwap_avoiding_or_differenceGrowth
      P s hk hminimal hDselected hactive hlarge
  · right
    obtain ⟨b, hbBlock, hbU, hrepair⟩ := hsafe
    have hcompletion :
        ∀ j, j ∉ J →
          U.card + (k + 1) < (F j).card := by
      intro j hjOld
      have hblock := hcontemporary j hjOld
      omega
    obtain ⟨j, hjJ, E, hER, hsjE, hprivate, hjSmall⟩ :=
      blockAlignedSafeSwap_certificate_forces_smallOldCollision
        P s hcert hprotected hminimal.1 hactive hbBlock hbU
          hUselected hrepair holdBound hcompletion
    refine ⟨j, hjJ, ?_, E, hER, hsjE, hprivate⟩
    exact hjSmall.trans
      (Nat.add_le_add_right hUcard ((k + 1) * r))
  · exact Or.inl hgrowth

/-- Difference-only projection of the retained-collision active-block fork.
Removing the old collision point from its support gives the represented
coherent difference used by the earlier old/contemporary interface. -/
theorem positiveOrder_targetLocalized_activeBlock_growth_or_oldDifference
    {A : Set ℕ} {k q r : ℕ} {Q J : Finset ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D : Finset ℕ} {i : ℕ}
    (hk : 0 < k)
    (hcert : ∀ t : BlockSelector F, ∃ u ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u)
    (hother : ∀ u ∈ Q, u ≠ q →
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet s) u)
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hDselected : (D : Set ℕ) ⊆ selectedSet s)
    (hactive : (s i).1 ∈ D)
    (hcontemporary : ∀ j, j ∉ J →
      D.card * (k * r) + (k + 1) * Q.card + k + 3 ≤
        (F j).card) :
    (∃ x ∈ D, x ≤ q ∧
        r < (additiveSupportFamily A k (q - x)).card) ∨
      ∃ j ∈ J, (s j).1 ≤ q ∧
        (additiveSupportFamily A k (q - (s j).1)).Nonempty := by
  obtain hgrowth | ⟨j, hjJ, E, hER, hsjE, _hprivate⟩ :=
    positiveOrder_targetLocalized_activeBlock_growth_or_oldCollision
      P s hk hcert hother hminimal hDselected hactive hcontemporary
  · exact Or.inl hgrowth
  · right
    have hsjLe : (s j).1 ≤ q :=
      additiveSupportFamily_supportsBounded
        A (k + 1) q E hER (s j).1 hsjE
    obtain ⟨H, hHR, _hEeq⟩ :=
      additiveSupport_remove_hit_succ hER hsjE
    exact ⟨j, hjJ, hsjLe, H, hHR⟩

/-- Repeated old collisions from many contemporary destroyer points amplify
to genuine support growth.

Run the protected active-block fork at every destroyer point whose block is
outside `J`.  If none of those runs gives the direct incidence-growth horn,
each point `d` supplies a support `E_d` at `q`, an old index `j_d ∈ J`, and
the private-hit identity `E_d ∩ D = {d}`.  Removing the old selected summand
from `E_d` gives a lower-order support at `q - s(j_d)`.

The map `d ↦ (j_d, E_d \ {s(j_d)})` is injective: equality of both
coordinates reconstructs equal upper supports, whose intersections with
`D` recover `d`.  Thus more than `|J| * r` contemporary destroyer points
force more than `r` distinct lower-order supports at one old difference. -/
theorem positiveOrder_targetLocalized_manyContemporaryPoints_force_growth
    {A : Set ℕ} {k q r : ℕ} {Q J : Finset ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D : Finset ℕ}
    (hk : 0 < k)
    (hcert : ∀ t : BlockSelector F, ∃ u ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u)
    (hother : ∀ u ∈ Q, u ≠ q →
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet s) u)
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hDselected : (D : Set ℕ) ⊆ selectedSet s)
    (hcontemporary : ∀ j, j ∉ J →
      D.card * (k * r) + (k + 1) * Q.card + k + 3 ≤
        (F j).card)
    (hmany :
      J.card * r <
        (D.filter fun d => blockIndex P d ∉ J).card) :
    (∃ x ∈ D, x ≤ q ∧
        r < (additiveSupportFamily A k (q - x)).card) ∨
      ∃ j ∈ J,
        r < (additiveSupportFamily A k (q - (s j).1)).card := by
  classical
  let C : Finset ℕ :=
    D.filter fun d => blockIndex P d ∉ J
  by_cases hgrowth :
      ∃ x ∈ D, x ≤ q ∧
        r < (additiveSupportFamily A k (q - x)).card
  · exact Or.inl hgrowth
  · right
    have hcollision :
        ∀ d : {d // d ∈ C},
          ∃ j ∈ J, ∃ E ∈ additiveSupportFamily A (k + 1) q,
            (s j).1 ∈ E ∧ E ∩ D = {d.1} := by
      intro d
      have hdParts :
          d.1 ∈ D ∧ blockIndex P d.1 ∉ J := by
        exact Finset.mem_filter.mp d.2
      have hdSelected :
          d.1 ∈ selectedSet s :=
        hDselected (Finset.mem_coe.mpr hdParts.1)
      have hselectedAt :
          (s (blockIndex P d.1)).1 = d.1 :=
        (P.mem_selectedSet_iff s).mp hdSelected
      have hactive :
          (s (blockIndex P d.1)).1 ∈ D := by
        rw [hselectedAt]
        exact hdParts.1
      obtain hdirect | ⟨j, hjJ, E, hER, hsjE, hprivate⟩ :=
        positiveOrder_targetLocalized_activeBlock_growth_or_oldCollision
          P s hk hcert hother hminimal hDselected hactive
            hcontemporary
      · exact (hgrowth hdirect).elim
      · refine ⟨j, hjJ, E, hER, hsjE, ?_⟩
        simpa only [hselectedAt] using hprivate
    choose oldIndex holdIndex upper hupperR holdUpper hprivate
      using hcollision
    have hlower :
        ∀ d : {d // d ∈ C},
          ∃ H ∈ additiveSupportFamily A k
              (q - (s (oldIndex d)).1),
            upper d = insert (s (oldIndex d)).1 H := by
      intro d
      exact additiveSupport_remove_hit_succ
        (hupperR d) (holdUpper d)
    choose lower hlowerR hreconstruct using hlower
    let Target :=
      Σ j : {j // j ∈ J},
        {H // H ∈ additiveSupportFamily A k
          (q - (s j.1).1)}
    let encode : {d // d ∈ C} → Target := fun d =>
      ⟨⟨oldIndex d, holdIndex d⟩,
        ⟨lower d, hlowerR d⟩⟩
    have hencode : Function.Injective encode := by
      intro d e hde
      have hj :
          oldIndex d = oldIndex e :=
        congrArg (fun z : Target => z.1.1) hde
      have hH :
          lower d = lower e :=
        congrArg (fun z : Target => z.2.1) hde
      apply Subtype.ext
      have hupperEq : upper d = upper e := by
        rw [hreconstruct d, hreconstruct e, hj, hH]
      have hsingle :
          ({d.1} : Finset ℕ) = {e.1} := by
        rw [← hprivate d, ← hprivate e, hupperEq]
      simpa using hsingle
    have hdomainTarget :
        C.card ≤ Fintype.card Target := by
      simpa only [Fintype.card_coe] using
        Fintype.card_le_of_injective encode hencode
    by_contra hnone
    push Not at hnone
    have htargetBound :
        Fintype.card Target ≤ J.card * r := by
      rw [Fintype.card_sigma]
      simp only [Fintype.card_coe]
      calc
        (∑ j : {j // j ∈ J},
            (additiveSupportFamily A k
              (q - (s j.1).1)).card) ≤
            ∑ _j : {j // j ∈ J}, r := by
          gcongr with j
          exact hnone j.1 j.2
        _ = J.card * r := by simp
    have hCbound : C.card ≤ J.card * r :=
      hdomainTarget.trans htargetBound
    exact (not_lt_of_ge hCbound) (by simpa only [C] using hmany)

/-- Reservoir-relative repeated-collision amplification.

The selected destroyer lives in a block reservoir `C ⊆ A`; private
collision supports and their lower-order remainders continue to live in
the full additive basis `A`. -/
theorem positiveOrder_targetLocalized_manyContemporaryPoints_force_growth_onReservoir
    {A C : Set ℕ} {k q r : ℕ} {Q J : Finset ℕ}
    {F : ℕ → Finset ℕ} (hCA : C ⊆ A)
    (P : IsFiniteBlockPartition C F)
    (s : BlockSelector F) {D : Finset ℕ}
    (hk : 0 < k)
    (hcert : ∀ t : BlockSelector F, ∃ u ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u)
    (hother : ∀ u ∈ Q, u ≠ q →
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet s) u)
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hDselected : (D : Set ℕ) ⊆ selectedSet s)
    (hcontemporary : ∀ j, j ∉ J →
      D.card * (k * r) + (k + 1) * Q.card + k + 3 ≤
        (F j).card)
    (hmany :
      J.card * r <
        (D.filter fun d => blockIndex P d ∉ J).card) :
    (∃ x ∈ D, x ≤ q ∧
        r < (additiveSupportFamily A k (q - x)).card) ∨
      ∃ j ∈ J,
        r < (additiveSupportFamily A k (q - (s j).1)).card := by
  classical
  let contemporaryPoints : Finset ℕ :=
    D.filter fun d => blockIndex P d ∉ J
  by_cases hgrowth :
      ∃ x ∈ D, x ≤ q ∧
        r < (additiveSupportFamily A k (q - x)).card
  · exact Or.inl hgrowth
  · right
    have hcollision :
        ∀ d : {d // d ∈ contemporaryPoints},
          ∃ j ∈ J, ∃ E ∈ additiveSupportFamily A (k + 1) q,
            (s j).1 ∈ E ∧ E ∩ D = {d.1} := by
      intro d
      have hdParts :
          d.1 ∈ D ∧ blockIndex P d.1 ∉ J := by
        exact Finset.mem_filter.mp d.2
      have hdSelected :
          d.1 ∈ selectedSet s :=
        hDselected (Finset.mem_coe.mpr hdParts.1)
      have hselectedAt :
          (s (blockIndex P d.1)).1 = d.1 :=
        (P.mem_selectedSet_iff s).mp hdSelected
      have hactive :
          (s (blockIndex P d.1)).1 ∈ D := by
        rw [hselectedAt]
        exact hdParts.1
      obtain hdirect | ⟨j, hjJ, E, hER, hsjE, hprivate⟩ :=
        positiveOrder_targetLocalized_activeBlock_growth_or_oldCollision_onReservoir
          hCA P s hk hcert hother hminimal hDselected hactive
            hcontemporary
      · exact (hgrowth hdirect).elim
      · refine ⟨j, hjJ, E, hER, hsjE, ?_⟩
        simpa only [hselectedAt] using hprivate
    choose oldIndex holdIndex upper hupperR holdUpper hprivate
      using hcollision
    have hlower :
        ∀ d : {d // d ∈ contemporaryPoints},
          ∃ H ∈ additiveSupportFamily A k
              (q - (s (oldIndex d)).1),
            upper d = insert (s (oldIndex d)).1 H := by
      intro d
      exact additiveSupport_remove_hit_succ
        (hupperR d) (holdUpper d)
    choose lower hlowerR hreconstruct using hlower
    let Target :=
      Σ j : {j // j ∈ J},
        {H // H ∈ additiveSupportFamily A k
          (q - (s j.1).1)}
    let encode : {d // d ∈ contemporaryPoints} → Target := fun d =>
      ⟨⟨oldIndex d, holdIndex d⟩,
        ⟨lower d, hlowerR d⟩⟩
    have hencode : Function.Injective encode := by
      intro d e hde
      have hj :
          oldIndex d = oldIndex e :=
        congrArg (fun z : Target => z.1.1) hde
      have hH :
          lower d = lower e :=
        congrArg (fun z : Target => z.2.1) hde
      apply Subtype.ext
      have hupperEq : upper d = upper e := by
        rw [hreconstruct d, hreconstruct e, hj, hH]
      have hsingle :
          ({d.1} : Finset ℕ) = {e.1} := by
        rw [← hprivate d, ← hprivate e, hupperEq]
      simpa using hsingle
    have hdomainTarget :
        contemporaryPoints.card ≤ Fintype.card Target := by
      simpa only [Fintype.card_coe] using
        Fintype.card_le_of_injective encode hencode
    by_contra hnone
    push Not at hnone
    have htargetBound :
        Fintype.card Target ≤ J.card * r := by
      rw [Fintype.card_sigma]
      simp only [Fintype.card_coe]
      calc
        (∑ j : {j // j ∈ J},
            (additiveSupportFamily A k
              (q - (s j.1).1)).card) ≤
            ∑ _j : {j // j ∈ J}, r := by
          gcongr with j
          exact hnone j.1 j.2
        _ = J.card * r := by simp
    have hCbound : contemporaryPoints.card ≤ J.card * r :=
      hdomainTarget.trans htargetBound
    exact (not_lt_of_ge hCbound)
      (by simpa only [contemporaryPoints] using hmany)

/-- Second-choice refinement of repeated old-collision amplification.

Only old blocks too small for the universal second choice can receive a
failed repair witness.  Let

`Small = {j ∈ J | |F j| ≤ (k+1)|Q| + (k+1)r}`.

If more than `|Small| * r` contemporary destroyer points collide, their
private supports inject into the lower support families indexed by `Small`,
so one such family has more than `r` members.  Compared with the preceding
amplification theorem, every adequately large old block has disappeared
from the pigeonhole denominator. -/
theorem positiveOrder_targetLocalized_manyContemporaryPoints_force_growth_usingSecondChoices
    {A : Set ℕ} {k q r : ℕ} {Q J : Finset ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D : Finset ℕ}
    (hk : 0 < k)
    (hcert : ∀ t : BlockSelector F, ∃ u ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u)
    (hother : ∀ u ∈ Q, u ≠ q →
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet s) u)
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hDselected : (D : Set ℕ) ⊆ selectedSet s)
    (hcontemporary : ∀ j, j ∉ J →
      D.card * (k * r) + (k + 1) * Q.card + k + 3 ≤
        (F j).card)
    (hmany :
      (J.filter fun j =>
          (F j).card ≤
            (k + 1) * Q.card + (k + 1) * r).card * r <
        (D.filter fun d => blockIndex P d ∉ J).card) :
    (∃ x ∈ D, x ≤ q ∧
        r < (additiveSupportFamily A k (q - x)).card) ∨
      ∃ j ∈ J,
        r < (additiveSupportFamily A k (q - (s j).1)).card := by
  classical
  let C : Finset ℕ :=
    D.filter fun d => blockIndex P d ∉ J
  let Small : Finset ℕ :=
    J.filter fun j =>
      (F j).card ≤
        (k + 1) * Q.card + (k + 1) * r
  by_cases hgrowth :
      ∃ x ∈ D, x ≤ q ∧
        r < (additiveSupportFamily A k (q - x)).card
  · exact Or.inl hgrowth
  by_cases holdGrowth :
      ∃ j ∈ J,
        r < (additiveSupportFamily A k
          (q - (s j).1)).card
  · exact Or.inr holdGrowth
  have holdBound :
      ∀ j ∈ J,
        (additiveSupportFamily A k
          (q - (s j).1)).card ≤ r := by
    intro j hjJ
    apply Nat.le_of_not_gt
    intro hjLarge
    exact holdGrowth ⟨j, hjJ, hjLarge⟩
  have hcollision :
      ∀ d : {d // d ∈ C},
        ∃ j ∈ Small,
          ∃ E ∈ additiveSupportFamily A (k + 1) q,
            (s j).1 ∈ E ∧ E ∩ D = {d.1} := by
    intro d
    have hdParts :
        d.1 ∈ D ∧ blockIndex P d.1 ∉ J := by
      exact Finset.mem_filter.mp d.2
    have hdSelected :
        d.1 ∈ selectedSet s :=
      hDselected (Finset.mem_coe.mpr hdParts.1)
    have hselectedAt :
        (s (blockIndex P d.1)).1 = d.1 :=
      (P.mem_selectedSet_iff s).mp hdSelected
    have hactive :
        (s (blockIndex P d.1)).1 ∈ D := by
      rw [hselectedAt]
      exact hdParts.1
    obtain hdirect |
        ⟨j, hjJ, hjSmall, E, hER, hsjE, hprivate⟩ :=
      positiveOrder_targetLocalized_contemporaryBlock_growth_or_smallOldCollision
        P s hk hcert hother hminimal hDselected hactive
          hdParts.2 holdBound hcontemporary
    · exact (hgrowth hdirect).elim
    · refine ⟨j, ?_, E, hER, hsjE, ?_⟩
      · exact Finset.mem_filter.mpr ⟨hjJ, hjSmall⟩
      · simpa only [hselectedAt] using hprivate
  choose oldIndex holdIndex upper hupperR holdUpper hprivate
    using hcollision
  have hlower :
      ∀ d : {d // d ∈ C},
        ∃ H ∈ additiveSupportFamily A k
            (q - (s (oldIndex d)).1),
          upper d = insert (s (oldIndex d)).1 H := by
    intro d
    exact additiveSupport_remove_hit_succ
      (hupperR d) (holdUpper d)
  choose lower hlowerR hreconstruct using hlower
  let Target :=
    Σ j : {j // j ∈ Small},
      {H // H ∈ additiveSupportFamily A k
        (q - (s j.1).1)}
  let encode : {d // d ∈ C} → Target := fun d =>
    ⟨⟨oldIndex d, holdIndex d⟩,
      ⟨lower d, hlowerR d⟩⟩
  have hencode : Function.Injective encode := by
    intro d e hde
    have hj :
        oldIndex d = oldIndex e :=
      congrArg (fun z : Target => z.1.1) hde
    have hH :
        lower d = lower e :=
      congrArg (fun z : Target => z.2.1) hde
    apply Subtype.ext
    have hupperEq : upper d = upper e := by
      rw [hreconstruct d, hreconstruct e, hj, hH]
    have hsingle :
        ({d.1} : Finset ℕ) = {e.1} := by
      rw [← hprivate d, ← hprivate e, hupperEq]
    simpa using hsingle
  have hdomainTarget :
      C.card ≤ Fintype.card Target := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective encode hencode
  have htargetBound :
      Fintype.card Target ≤ Small.card * r := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe]
    calc
      (∑ j : {j // j ∈ Small},
          (additiveSupportFamily A k
            (q - (s j.1).1)).card) ≤
          ∑ _j : {j // j ∈ Small}, r := by
        gcongr with j
        exact holdBound j.1
          (Finset.mem_filter.mp j.2).1
      _ = Small.card * r := by simp
  have hCbound : C.card ≤ Small.card * r :=
    hdomainTarget.trans htargetBound
  exact ((not_lt_of_ge hCbound) (by
    simpa only [C, Small] using hmany)).elim

/-- Large-block form of the aligned fork.

If every block has two more points than the incidence budget
`|D| * k * r`, choose any active point of the minimal destroyer.  Its block
automatically satisfies the local large-block hypothesis, so either a
same-block swap repairs the target or a coherent difference has more than
`r` lower-order supports.

The representedness hypothesis only rules out the vacuous empty destroyer. -/
theorem positiveOrder_minimalDestroyer_largeBlocks_safeSwap_or_differenceGrowth
    {A : Set ℕ} {k q r : ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D : Finset ℕ}
    (hk : 0 < k)
    (hrepresented :
      (additiveSupportFamily A (k + 1) q).Nonempty)
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hDselected : (D : Set ℕ) ⊆ selectedSet s)
    (hblocks :
      ∀ i, D.card * (k * r) + 2 ≤ (F i).card) :
    (∃ i, ∃ b ∈ (F i).erase (s i).1,
        (s i).1 ∈ D ∧
        ¬ DestroysAt
          (additiveSupportFamily A (k + 1))
          (((D.erase (s i).1 ∪ {b} : Finset ℕ) : Set ℕ)) q) ∨
      ∃ x ∈ D, x ≤ q ∧
        r < (additiveSupportFamily A k (q - x)).card := by
  classical
  have hDnonempty : D.Nonempty := by
    by_contra hDempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hDempty] at hminimal
    obtain ⟨E, hER⟩ := hrepresented
    exact hminimal.1 E hER (by simp)
  obtain ⟨d, hdD⟩ := hDnonempty
  obtain ⟨i, hdi⟩ :=
    hDselected (Finset.mem_coe.mpr hdD)
  have hactive : (s i).1 ∈ D := by
    change (fun j => (s j).1) i ∈ D
    rw [hdi]
    exact hdD
  have heraseCard :
      ((F i).erase (s i).1).card + 1 = (F i).card :=
    Finset.card_erase_add_one (s i).2
  have hlarge :
      D.card * (k * r) <
        ((F i).erase (s i).1).card := by
    have hblock := hblocks i
    omega
  obtain hsafe | hgrowth :=
    positiveOrder_minimalDestroyer_activeBlock_safeSwap_or_differenceGrowth
      P s hk hminimal hDselected hactive hlarge
  · left
    obtain ⟨b, hbBlock, hrepair⟩ := hsafe
    exact ⟨i, b, hbBlock, hactive, hrepair⟩
  · exact Or.inr hgrowth

/-- Uniform-budget version.  Block sizes are chosen from a proposed support
bound `m`, before the minimal destroyer is known.  If the target already has
more than `m` supports there is immediate growth.  Otherwise
`card_le_supportFamily` bounds the unknown destroyer size by `m`, and the
large-block aligned fork applies.

This removes the last circular dependence of block size on the subsequently
revealed minimal destroyer. -/
theorem positiveOrder_minimalDestroyer_uniformLargeBlocks_trichotomy
    {A : Set ℕ} {k q r m : ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D : Finset ℕ}
    (hk : 0 < k)
    (hrepresented :
      (additiveSupportFamily A (k + 1) q).Nonempty)
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hDselected : (D : Set ℕ) ⊆ selectedSet s)
    (hblocks :
      ∀ i, m * (k * r) + 2 ≤ (F i).card) :
    m < (additiveSupportFamily A (k + 1) q).card ∨
      (∃ i, ∃ b ∈ (F i).erase (s i).1,
          (s i).1 ∈ D ∧
          ¬ DestroysAt
            (additiveSupportFamily A (k + 1))
            (((D.erase (s i).1 ∪ {b} : Finset ℕ) : Set ℕ)) q) ∨
      ∃ x ∈ D, x ≤ q ∧
        r < (additiveSupportFamily A k (q - x)).card := by
  by_cases hsupport :
      m < (additiveSupportFamily A (k + 1) q).card
  · exact Or.inl hsupport
  · right
    have hDcard : D.card ≤ m :=
      hminimal.card_le_supportFamily.trans
        (Nat.le_of_not_gt hsupport)
    apply
      positiveOrder_minimalDestroyer_largeBlocks_safeSwap_or_differenceGrowth
        P s hk hrepresented hminimal hDselected
    intro i
    have hi := hblocks i
    have hmul :
        D.card * (k * r) ≤ m * (k * r) :=
      Nat.mul_le_mul_right (k * r) hDcard
    omega

/-- Arbitrarily late global block-alignment trichotomy.

Choose, before the strong-deletion certificate is revealed, an exact-cardinal
block partition with

`m * (k * r) + 2`

points in every block.  Any selector destruction has a finite selected
subdestroyer; minimize it.  The unknown minimal core cannot be larger than
the target's support family.  Therefore:

* the exact target already has more than `m` supports; or
* a private deleted point has a verified safe replacement in its own block;
  or
* some coherent difference `q-x` has more than `r` order-`k` supports.

This is the first certificate-level theorem in which the safe gap replacement
and the damaged summand are forced into the same finite block. -/
theorem IsStronglyMinimalExactBasis.arbitrarilyLate_blockAlignedRepair_or_supportGrowth
    {A : Set ℕ} {k : ℕ}
    (hminimal : IsStronglyMinimalExactBasis A (k + 1))
    (hk : 0 < k) :
    ∀ m r L,
      ∃ F : ℕ → Finset ℕ, ∃ P : IsFiniteBlockPartition A F,
        ∃ s : BlockSelector F, ∃ q D,
          (∀ i, (F i).card = m * (k * r) + 2) ∧
          L ≤ q ∧
          IsInclusionMinimalDestroyer
            (additiveSupportFamily A (k + 1)) D q ∧
          (D : Set ℕ) ⊆ selectedSet s ∧
          (m < (additiveSupportFamily A (k + 1) q).card ∨
            (∃ i, ∃ b ∈ (F i).erase (s i).1,
                (s i).1 ∈ D ∧
                ¬ DestroysAt
                  (additiveSupportFamily A (k + 1))
                  (((D.erase (s i).1 ∪ {b} : Finset ℕ) : Set ℕ)) q) ∨
            ∃ x ∈ D, x ≤ q ∧
              r < (additiveSupportFamily A k (q - x)).card) := by
  classical
  obtain ⟨N₀, hN₀⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hminimal.1
  intro m r L
  let blockSize := m * (k * r) + 2
  have hblockSizePos : 0 < blockSize := by
    simp [blockSize]
  obtain ⟨F, P, hFcard⟩ :=
    exists_finiteBlockPartition_exactCard
      hminimal.1.infinite hblockSizePos
  obtain ⟨Q, hQLower, hcert⟩ :=
    (finiteBlockCertificates_of_strongInfiniteDeletion hminimal.2)
      F P (max L N₀)
  let s : BlockSelector F := fun i =>
    ⟨(P.nonempty i).choose, (P.nonempty i).choose_spec⟩
  obtain ⟨q, hqQ, hdestroySelected⟩ := hcert s
  have hLq : L ≤ q :=
    le_trans (le_max_left L N₀) (hQLower q hqQ)
  have hqRepresented :
      (additiveSupportFamily A (k + 1) q).Nonempty := by
    obtain ⟨E, hER, _hEnonempty⟩ :=
      hN₀ q (le_trans (le_max_right L N₀) (hQLower q hqQ))
    exact ⟨E, hER⟩
  obtain ⟨D, hDselected, _hDcard, hDdestroy⟩ :=
    exists_finiteSelectedDestroyer_of_destroysAt
      P s hdestroySelected
  obtain ⟨D₀, hD₀D, hD₀minimal⟩ :=
    exists_inclusionMinimalDestroyer_subset hDdestroy
  have hD₀selected : (D₀ : Set ℕ) ⊆ selectedSet s := by
    intro x hxD₀
    exact hDselected (Finset.mem_coe.mpr
      (hD₀D (Finset.mem_coe.mp hxD₀)))
  have hblocks :
      ∀ i, m * (k * r) + 2 ≤ (F i).card := by
    intro i
    rw [hFcard i]
  have htri :=
    positiveOrder_minimalDestroyer_uniformLargeBlocks_trichotomy
      P s hk hqRepresented hD₀minimal hD₀selected hblocks
  exact ⟨F, P, s, q, D₀, hFcard, hLq,
    hD₀minimal, hD₀selected, htri⟩

/-- Global target-localized consequence of protected block alignment.

Fix in advance a proposed certificate-cardinality bound `C` and make every
block large enough for:

* the destroyer-incidence budget;
* one protected order-`k+1` support for each of at most `C` targets; and
* completion of the repaired selector outside their union.

After strong deletion returns a certificate, shrink it to a cardinal-minimal
target-localized certificate `Q`.  If `Q.card > C`, certificate cardinality
has genuinely grown.  Otherwise localization eliminates the safe-repair
horn completely, leaving support growth at the largest target or at one of
its coherent differences. -/
theorem IsStronglyMinimalExactBasis.arbitrarilyLate_largeMinimalCertificate_or_supportGrowth
    {A : Set ℕ} {k : ℕ}
    (hminimal : IsStronglyMinimalExactBasis A (k + 1))
    (hk : 0 < k) :
    ∀ C m r L,
      ∃ F : ℕ → Finset ℕ, ∃ P : IsFiniteBlockPartition A F,
        ∃ Q : Finset ℕ,
          (∀ u ∈ Q, L ≤ u) ∧
          (∀ s : BlockSelector F, ∃ u ∈ Q,
            DestroysAt
              (additiveSupportFamily A (k + 1))
              (selectedSet s) u) ∧
          (∀ u ∈ Q, ∃ s : BlockSelector F,
            DestroysAt
                (additiveSupportFamily A (k + 1))
                (selectedSet s) u ∧
              ∀ v ∈ Q, v ≠ u →
                ¬ DestroysAt
                  (additiveSupportFamily A (k + 1))
                  (selectedSet s) v) ∧
          (C < Q.card ∨
            ∃ q ∈ Q,
              m < (additiveSupportFamily A (k + 1) q).card ∨
                ∃ x, x ≤ q ∧
                  r <
                    (additiveSupportFamily A k (q - x)).card) := by
  classical
  obtain ⟨N₀, hN₀⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hminimal.1
  intro C m r L
  let blockSize :=
    m * (k * r) + (k + 1) * C + k + 3
  have hblockSizePos : 0 < blockSize := by
    dsimp only [blockSize]
    omega
  obtain ⟨F, P, hFcard⟩ :=
    exists_finiteBlockPartition_exactCard
      hminimal.1.infinite hblockSizePos
  obtain ⟨Qraw, hQrawLower, hcertRaw⟩ :=
    (finiteBlockCertificates_of_strongInfiniteDeletion hminimal.2)
      F P (max L N₀)
  obtain ⟨Q, hQQraw, hcert, hlocalized⟩ :=
    exists_minimal_targetLocalized_subcertificate hcertRaw
  let arbitrary : BlockSelector F := fun i =>
    ⟨(P.nonempty i).choose, (P.nonempty i).choose_spec⟩
  obtain ⟨q₀, hq₀Q, _hq₀destroy⟩ := hcert arbitrary
  have hQnonempty : Q.Nonempty := ⟨q₀, hq₀Q⟩
  let q := Q.max' hQnonempty
  have hqQ : q ∈ Q := Finset.max'_mem Q hQnonempty
  obtain ⟨s, hsdestroy, hsother⟩ := hlocalized q hqQ
  have hlate : ∀ u ∈ Q, L ≤ u := by
    intro u huQ
    exact (le_max_left L N₀).trans
      (hQrawLower u (hQQraw huQ))
  refine ⟨F, P, Q, hlate, hcert, hlocalized, ?_⟩
  by_cases hQlarge : C < Q.card
  · exact Or.inl hQlarge
  · right
    have hQcard : Q.card ≤ C := Nat.le_of_not_gt hQlarge
    have hqRepresented :
        (additiveSupportFamily A (k + 1) q).Nonempty := by
      obtain ⟨E, hER, _hEnonempty⟩ :=
        hN₀ q ((le_max_right L N₀).trans
          (hQrawLower q (hQQraw hqQ)))
      exact ⟨E, hER⟩
    obtain ⟨D, hDselected, _hDcard, hDdestroy⟩ :=
      exists_finiteSelectedDestroyer_of_destroysAt
        P s hsdestroy
    obtain ⟨D₀, hD₀D, hD₀minimal⟩ :=
      exists_inclusionMinimalDestroyer_subset hDdestroy
    have hD₀selected : (D₀ : Set ℕ) ⊆ selectedSet s := by
      intro x hxD₀
      exact hDselected (Finset.mem_coe.mpr
        (hD₀D (Finset.mem_coe.mp hxD₀)))
    have hQmul :
        (k + 1) * Q.card ≤ (k + 1) * C :=
      Nat.mul_le_mul_left (k + 1) hQcard
    have hblocks :
        ∀ i,
          m * (k * r) + (k + 1) * Q.card + k + 3 ≤
            (F i).card := by
      intro i
      rw [hFcard i]
      dsimp only [blockSize]
      omega
    have hgrowth :=
      positiveOrder_targetLocalizedCertificate_largeBlocks_forces_supportGrowth
        P s hk hqRepresented hcert hsother hD₀minimal
          hD₀selected hblocks
    refine ⟨q, hqQ, ?_⟩
    rcases hgrowth with hexact | ⟨x, _hxD₀, hxq, hxdifference⟩
    · exact Or.inl hexact
    · exact Or.inr ⟨x, hxq, hxdifference⟩

/-- Universal pre-certificate anchored partition.

Thin an arbitrary certificate-aligned diagonal to the nested labels
`range (j+1)`.  The corresponding row cells still form a countable,
pairwise-disjoint family, and the bijective row locator places exactly one
such cell in every completed partition block.

After an arbitrary finite target set `Q` is revealed, let
`M = sum Q + 1`.  In every block whose row index is at least `M`, choose the
row anchor.  That anchor is at least `M`, while every vertex of every support
at a target `q ∈ Q` is at most `q ≤ sum Q`.  Consequently the entire infinite
tail of the selector is invisible to all targets in `Q`: any destruction of
one of them is already caused by the finitely many selected points in rows
below `M`.

This constructs one partition before the certificate is known and removes
the former global collision problem.  The remaining obstruction is now
literally finite-prefix destruction. -/
theorem HasDiagonalAnchoredAlignedTranslateCellRows.exists_universalPartition_localizingFiniteTargets
    {A : Set ℕ} {k : ℕ}
    (hdiag : HasDiagonalAnchoredAlignedTranslateCellRows A k) :
    ∃ F : ℕ → Finset ℕ, ∃ _P : IsFiniteBlockPartition A F,
      ∃ base : BlockSelector F, ∃ damagePrefix : ℕ → Finset ℕ,
        Monotone damagePrefix ∧
        (∀ M, (damagePrefix M).card = M) ∧
        (∀ M, (damagePrefix M : Set ℕ) ⊆ selectedSet base) ∧
        (∀ x ∈ selectedSet base, ∃ M, x ∈ damagePrefix M) ∧
        ∀ Q : Finset ℕ, ∃ s : BlockSelector F,
          (damagePrefix (Q.sum id + 1) : Set ℕ) ⊆ selectedSet s ∧
          (∀ x ∈ selectedSet s,
            x ∈ damagePrefix (Q.sum id + 1) ∨ Q.sum id < x) ∧
          ∀ q ∈ Q,
            DestroysAt
                (additiveSupportFamily A k) (selectedSet s) q →
              DestroysAt
                (additiveSupportFamily A k)
                  (damagePrefix (Q.sum id + 1) : Set ℕ) q := by
  classical
  obtain ⟨enumerate, henumerate, rows, hrows, hcross⟩ := hdiag
  let label (j : ℕ) : {Q : Finset ℕ // Q.Nonempty} :=
    ⟨Finset.range (j + 1), by simp⟩
  let rowIndex (j : ℕ) : ℕ :=
    Classical.choose (henumerate (label j))
  have hrowIndexSpec : ∀ j, enumerate (rowIndex j) = label j := by
    intro j
    exact Classical.choose_spec (henumerate (label j))
  have hrowIndexInjective : Function.Injective rowIndex := by
    intro i j hij
    have hlabels : label i = label j := by
      rw [← hrowIndexSpec i, ← hrowIndexSpec j, hij]
    have hcard := congrArg (fun Q => Q.1.card) hlabels
    simpa [label] using hcard
  let nestedRows (j : ℕ) : Finset (Finset ℕ) :=
    rows (rowIndex j)
  have hnestedFamily : ∀ j,
      IsAnchoredAlignedTranslateCellFamily
        A k (Finset.range (j + 1)) (j + 1) (nestedRows j) := by
    intro j
    have hrow := (hrows (rowIndex j)).1
    have hmax :
        (Finset.range (j + 1)).max' (by simp) = j := by
      apply
        (Finset.max'_eq_iff
          (s := Finset.range (j + 1)) (H := by simp) j).2
      constructor
      · simp
      · intro b hb
        simp only [Finset.mem_range] at hb
        omega
    simpa only [nestedRows, hrowIndexSpec, label, hmax] using hrow
  have hnestedNonempty : ∀ j, (nestedRows j).Nonempty := by
    intro j
    rw [← Finset.card_pos]
    change 0 < (rows (rowIndex j)).card
    rw [(hrows (rowIndex j)).2]
    omega
  have hnestedCross :
      ArePairwiseDisjointDestroyerRows nestedRows := by
    intro i j hij C hCi D hDj
    exact hcross (rowIndex i) (rowIndex j)
      (hrowIndexInjective.ne hij) C hCi D hDj
  let chosenCell :
      ∀ j, {C : Finset ℕ // C ∈ nestedRows j} := fun j =>
    ⟨(hnestedNonempty j).choose, (hnestedNonempty j).choose_spec⟩
  let thinRows (j : ℕ) : Finset (Finset ℕ) :=
    {(chosenCell j).1}
  have hthinNonempty : ∀ j, (thinRows j).Nonempty := by
    intro j
    simp [thinRows]
  have hthinMatching : ∀ j, IsMatching (thinRows j) := by
    intro j
    simp [thinRows, IsMatching]
  have hthinCellNonempty :
      ∀ j, ∀ C ∈ thinRows j, C.Nonempty := by
    intro j C hC
    have hCeq : C = (chosenCell j).1 := by
      simpa [thinRows] using hC
    rw [hCeq]
    exact (hnestedFamily j).2.1
      (chosenCell j).1 (chosenCell j).2
  have hthinCellA :
      ∀ j, ∀ C ∈ thinRows j, ∀ x ∈ C, x ∈ A := by
    intro j C hC x hxC
    have hCeq : C = (chosenCell j).1 := by
      simpa [thinRows] using hC
    rw [hCeq] at hxC
    exact (hnestedFamily j).2.2.1
      (chosenCell j).1 (chosenCell j).2 x hxC
  have hthinCross :
      ArePairwiseDisjointDestroyerRows thinRows := by
    intro i j hij C hCi D hDj
    have hCeq : C = (chosenCell i).1 := by
      simpa [thinRows] using hCi
    have hDeq : D = (chosenCell j).1 := by
      simpa [thinRows] using hDj
    rw [hCeq, hDeq]
    exact hnestedCross i j hij
      (chosenCell i).1 (chosenCell i).2
      (chosenCell j).1 (chosenCell j).2
  obtain ⟨F, P, locate, hlocate, hcell⟩ :=
    exists_finiteBlockPartition_for_disjointRows
      hthinNonempty hthinMatching hthinCellNonempty hthinCellA hthinCross
  let CellIndex :=
    Σ j, {C : Finset ℕ // C ∈ thinRows j}
  have hwitness : ∀ c : CellIndex,
      ∃ T : Finset ℕ, ∃ q : {m // m ∈ Finset.range (c.1 + 1)},
        ∃ n a,
          c.2.1 = insert a T ∧ c.1 + 1 ≤ a ∧ a ∈ A ∧
            n = q.1 + a ∧
          DestroysAt
            (additiveSupportFamily A (k + 1)) (T : Set ℕ) n := by
    intro c
    have hcNested : c.2.1 ∈ nestedRows c.1 := by
      have hceq : c.2.1 = (chosenCell c.1).1 := by
        exact Finset.mem_singleton.mp
          (show c.2.1 ∈ {(chosenCell c.1).1} from c.2.2)
      rw [hceq]
      exact (chosenCell c.1).2
    exact (hnestedFamily c.1).2.2.2 c.2.1 hcNested
  choose core target successor anchor hcellEq hanchorLower
    hanchorA hsuccessor hdestroy using hwitness
  have hanchorMem : ∀ c : CellIndex, anchor c ∈ c.2.1 := by
    intro c
    rw [hcellEq c]
    exact Finset.mem_insert_self _ _
  let blockCell : ℕ → CellIndex := fun i =>
    Classical.choose (hlocate.2 i)
  have hlocateBlockCell : ∀ i, locate (blockCell i) = i := by
    intro i
    exact Classical.choose_spec (hlocate.2 i)
  let thinCell (j : ℕ) : {C : Finset ℕ // C ∈ thinRows j} :=
    ⟨(chosenCell j).1, by simp [thinRows]⟩
  have hcellCanonical : ∀ c : CellIndex,
      (⟨c.1, thinCell c.1⟩ : CellIndex) = c := by
    intro c
    have hval : c.2.1 = (chosenCell c.1).1 :=
      Finset.mem_singleton.mp
        (show c.2.1 ∈ {(chosenCell c.1).1} from c.2.2)
    exact Sigma.ext rfl
      (heq_of_eq (Subtype.ext hval.symm))
  let rowBlock (j : ℕ) : ℕ :=
    locate ⟨j, thinCell j⟩
  have hblockCellRowBlock : ∀ j,
      blockCell (rowBlock j) = (⟨j, thinCell j⟩ : CellIndex) := by
    intro j
    apply hlocate.1
    rw [hlocateBlockCell]
  have hrowBlockBlockCell : ∀ i,
      rowBlock (blockCell i).1 = i := by
    intro i
    change locate ⟨(blockCell i).1, thinCell (blockCell i).1⟩ = i
    rw [hcellCanonical (blockCell i)]
    exact hlocateBlockCell i
  have hrowBlockInjective : Function.Injective rowBlock := by
    intro i j hij
    have hcells := congrArg blockCell hij
    rw [hblockCellRowBlock i, hblockCellRowBlock j] at hcells
    exact congrArg Sigma.fst hcells
  let base : BlockSelector F := fun i =>
    ⟨(P.nonempty i).choose, (P.nonempty i).choose_spec⟩
  let selectedRow (j : ℕ) : ℕ :=
    (base (rowBlock j)).1
  have hselectedRowInjective : Function.Injective selectedRow :=
    (P.selector_injective base).comp hrowBlockInjective
  let damagePrefix (M : ℕ) : Finset ℕ :=
    (Finset.range M).image selectedRow
  have hprefixMono : Monotone damagePrefix := by
    intro M L hML x hx
    obtain ⟨j, hjM, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_range.mpr ?_, rfl⟩
    exact lt_of_lt_of_le (Finset.mem_range.mp hjM) hML
  have hprefixCard : ∀ M, (damagePrefix M).card = M := by
    intro M
    rw [Finset.card_image_iff.mpr hselectedRowInjective.injOn]
    simp
  have hprefixBase :
      ∀ M, (damagePrefix M : Set ℕ) ⊆ selectedSet base := by
    intro M x hx
    obtain ⟨j, _hjM, hjx⟩ := Finset.mem_image.mp hx
    exact ⟨rowBlock j, hjx⟩
  have hprefixExhausts :
      ∀ x ∈ selectedSet base, ∃ M, x ∈ damagePrefix M := by
    intro x hx
    obtain ⟨i, rfl⟩ := hx
    refine ⟨(blockCell i).1 + 1, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨(blockCell i).1, by simp, ?_⟩
    simp only [selectedRow]
    rw [hrowBlockBlockCell]
  refine ⟨F, P, base, damagePrefix, hprefixMono, hprefixCard, hprefixBase,
    hprefixExhausts, ?_⟩
  intro Q
  let M := Q.sum id + 1
  let s : BlockSelector F := fun i =>
    if hi : M ≤ (blockCell i).1 then
      ⟨anchor (blockCell i), by
        have hc :=
          hcell (blockCell i) (hanchorMem (blockCell i))
        rw [hlocateBlockCell i] at hc
        exact hc⟩
    else base i
  have hDselected : (damagePrefix M : Set ℕ) ⊆ selectedSet s := by
    intro x hxD
    obtain ⟨j, hjM, hix⟩ := Finset.mem_image.mp hxD
    have hjlt : j < M := Finset.mem_range.mp hjM
    refine ⟨rowBlock j, ?_⟩
    rw [← hix]
    simp [s, selectedRow, hblockCellRowBlock,
      not_le.mpr hjlt]
  have hselectedTail :
      ∀ x ∈ selectedSet s, x ∈ damagePrefix M ∨ Q.sum id < x := by
    intro x hxSelected
    obtain ⟨i, rfl⟩ := hxSelected
    by_cases hi : M ≤ (blockCell i).1
    · right
      have hchoice :
          (s i).1 = anchor (blockCell i) := by
        simp [s, hi]
      have hlower := hanchorLower (blockCell i)
      change Q.sum id < (s i).1
      rw [hchoice]
      dsimp only [M] at hi
      omega
    · left
      apply Finset.mem_image.mpr
      refine ⟨(blockCell i).1, Finset.mem_range.mpr ?_, ?_⟩
      · omega
      · simp only [selectedRow]
        rw [hrowBlockBlockCell]
        simp [s, hi]
  refine ⟨s, ?_, ?_, ?_⟩
  · simpa only [M] using hDselected
  · simpa only [M] using hselectedTail
  intro q hqQ hdestroySelected E hER
  obtain ⟨x, hxE, hxSelected⟩ :=
    Set.not_disjoint_iff.mp (hdestroySelected E hER)
  have hxBound : x ≤ q :=
    additiveSupportFamily_supportsBounded
      A k q E hER x hxE
  have hqSum : q ≤ Q.sum id :=
    Finset.single_le_sum
      (s := Q) (f := id) (fun _ _ => Nat.zero_le _) hqQ
  obtain hxD | hxLarge := hselectedTail x hxSelected
  · apply Set.not_disjoint_iff.mpr
    exact ⟨x, hxE, Finset.mem_coe.mpr hxD⟩
  · omega

/-- Compose the universal partition with strong deletion.

The partition `F` is fixed once and for all, before the late threshold and
before the finite certificate `Q`.  For every threshold, strong deletion
returns a certificate, while the universal selector neutralizes the infinite
tail.  Hence some certified target is destroyed by a genuinely finite prefix
`D`.  Exact-basis representability then turns one point `d ∈ D` into a
represented lower-order difference `q-d`.

Thus the universal pre-certificate attack eliminates infinite cross-block
collisions completely; its remaining mathematical obligation is the
finite-prefix/difference composition. -/
theorem HasDiagonalAnchoredAlignedTranslateCellRows.strongDeletion_forces_universalFinitePrefixDifferences
    {A : Set ℕ} {k : ℕ}
    (hdiag : HasDiagonalAnchoredAlignedTranslateCellRows A (k + 1))
    (hminimal : IsStronglyMinimalExactBasis A (k + 1)) :
    ∃ F : ℕ → Finset ℕ, ∃ _P : IsFiniteBlockPartition A F,
      ∃ base : BlockSelector F, ∃ damagePrefix : ℕ → Finset ℕ,
        Monotone damagePrefix ∧
        (∀ M, (damagePrefix M).card = M) ∧
        (∀ M, (damagePrefix M : Set ℕ) ⊆ selectedSet base) ∧
        (∀ x ∈ selectedSet base, ∃ M, x ∈ damagePrefix M) ∧
        ∀ N, ∃ Q : Finset ℕ,
          ∃ s : BlockSelector F, ∃ q ∈ Q,
            ∃ d ∈ damagePrefix (Q.sum id + 1),
            (∀ u ∈ Q, N ≤ u) ∧
            (damagePrefix (Q.sum id + 1) : Set ℕ) ⊆ selectedSet s ∧
            (∀ x ∈ selectedSet s,
              x ∈ damagePrefix (Q.sum id + 1) ∨ Q.sum id < x) ∧
            DestroysAt
              (additiveSupportFamily A (k + 1))
                (damagePrefix (Q.sum id + 1) : Set ℕ) q ∧
            d ∈ A ∧ d ≤ q ∧
            (additiveSupportFamily A k (q - d)).Nonempty := by
  obtain ⟨F, P, base, damagePrefix, hprefixMono, hprefixCard, hprefixBase,
      hprefixExhausts, huniversal⟩ :=
    hdiag.exists_universalPartition_localizingFiniteTargets
  obtain ⟨N₀, hN₀⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hminimal.1
  refine ⟨F, P, base, damagePrefix, hprefixMono, hprefixCard, hprefixBase,
    hprefixExhausts, ?_⟩
  intro N
  obtain ⟨Q, hQlower, hcertificate⟩ :=
    (finiteBlockCertificates_of_strongInfiniteDeletion hminimal.2)
      F P (max N N₀)
  obtain ⟨s, hDselected, htail, hlocalize⟩ :=
    huniversal Q
  obtain ⟨q, hqQ, hdestroySelected⟩ :=
    hcertificate s
  have hqRepresented :
      (additiveSupportFamily A (k + 1) q).Nonempty := by
    obtain ⟨E, hER, _hEnonempty⟩ :=
      hN₀ q
        (le_trans (le_max_right N N₀) (hQlower q hqQ))
    exact ⟨E, hER⟩
  have hdestroyD :
      DestroysAt
        (additiveSupportFamily A (k + 1))
          (damagePrefix (Q.sum id + 1) : Set ℕ) q :=
    hlocalize q hqQ hdestroySelected
  obtain ⟨d, hdD, hdq, hdifference⟩ :=
    finiteDestroyer_has_lowerOrderDifference
      hqRepresented hdestroyD
  have hQA : ∀ u ∈ Q, N ≤ u := by
    intro u huQ
    exact le_trans (le_max_left N N₀) (hQlower u huQ)
  have hdA : d ∈ A :=
    P.selectedSet_subset s (hDselected (Finset.mem_coe.mpr hdD))
  exact ⟨Q, s, q, hqQ, d, hdD, hQA,
    hDselected, htail, hdestroyD, hdA, hdq, hdifference⟩

/-- Exhaustive universal pre-certificate reduction for a hypothetical strongly
minimal exact basis of positive order.  Either finite-translate matching growth
already occurs, or one fixed partition produces arbitrarily late finite-prefix
destroyers and represented one-order-lower differences. -/
theorem IsStronglyMinimalExactBasis.finiteTranslateGrowth_or_universalFinitePrefixDifferences
    {A : Set ℕ} {k : ℕ}
    (hminimal : IsStronglyMinimalExactBasis A (k + 1)) :
    HasSomeFiniteTranslateMatchingGrowth A (k + 1) ∨
      ∃ F : ℕ → Finset ℕ, ∃ _P : IsFiniteBlockPartition A F,
        ∃ base : BlockSelector F, ∃ damagePrefix : ℕ → Finset ℕ,
          Monotone damagePrefix ∧
          (∀ M, (damagePrefix M).card = M) ∧
          (∀ M, (damagePrefix M : Set ℕ) ⊆ selectedSet base) ∧
          (∀ x ∈ selectedSet base, ∃ M, x ∈ damagePrefix M) ∧
          ∀ N, ∃ Q : Finset ℕ,
            ∃ s : BlockSelector F, ∃ q ∈ Q,
              ∃ d ∈ damagePrefix (Q.sum id + 1),
              (∀ u ∈ Q, N ≤ u) ∧
              (damagePrefix (Q.sum id + 1) : Set ℕ) ⊆ selectedSet s ∧
              (∀ x ∈ selectedSet s,
                x ∈ damagePrefix (Q.sum id + 1) ∨ Q.sum id < x) ∧
              DestroysAt
                (additiveSupportFamily A (k + 1))
                  (damagePrefix (Q.sum id + 1) : Set ℕ) q ∧
              d ∈ A ∧ d ≤ q ∧
              (additiveSupportFamily A k (q - d)).Nonempty := by
  obtain hgrowth | hdiag :=
    finiteTranslateMatchingGrowth_or_diagonalAnchoredCellRows hminimal.1
  · exact Or.inl hgrowth
  · exact Or.inr
      (hdiag.strongDeletion_forces_universalFinitePrefixDifferences hminimal)

/-- A lower-triangular family of bounded binary repairs has an infinite
cross-disjoint subfamily.

Earlier repairs are assumed to avoid later cells.  Ramsey-thin the symmetric
cross-collision relation.  An infinite collision clique is impossible:
for a sufficiently late member, its two bounded repairs would have to meet
more pairwise-disjoint earlier cells than their union has vertices.  Hence
the infinite homogeneous set is collision-free.

This is the combinatorial mechanism which controls representations crossing
between different gap blocks. -/
theorem exists_infinite_crossDisjoint_binaryRepairs
    {cell Hleft Hright : ℕ → Finset ℕ} {r : ℕ}
    (hcell : Pairwise fun i j => Disjoint (cell i) (cell j))
    (hleftCard : ∀ i, (Hleft i).card ≤ r)
    (hrightCard : ∀ i, (Hright i).card ≤ r)
    (hforward : ∀ i j, i < j →
      Disjoint (Hleft i) (cell j) ∧
      Disjoint (Hright i) (cell j)) :
    ∃ I : Set ℕ, I.Infinite ∧
      ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        Disjoint (Hleft i) (cell j) ∧
        Disjoint (Hright i) (cell j) := by
  classical
  let Collides : ℕ → ℕ → Prop := fun i j =>
    ¬ Disjoint (Hleft i) (cell j) ∨
    ¬ Disjoint (Hright i) (cell j) ∨
    ¬ Disjoint (Hleft j) (cell i) ∨
    ¬ Disjoint (Hright j) (cell i)
  have hsymm : Symmetric Collides := by
    intro i j hij
    rcases hij with hij | hij | hji | hji
    · exact Or.inr (Or.inr (Or.inl hij))
    · exact Or.inr (Or.inr (Or.inr hij))
    · exact Or.inl hji
    · exact Or.inr (Or.inl hji)
  obtain ⟨L, _hLuniv, hLinf, hLclique⟩ |
      ⟨L, _hLuniv, hLinf, hLindependent⟩ :=
    infinite_pairRamsey_nat Set.infinite_univ Collides hsymm
  · exfalso
    let s := 2 * r + 2
    obtain ⟨J, hJL, hJcard⟩ :=
      hLinf.exists_subset_card_eq s
    have hJnonempty : J.Nonempty := by
      apply Finset.card_pos.mp
      rw [hJcard]
      simp [s]
    let j := J.max' hJnonempty
    let K := J.erase j
    have hjJ : j ∈ J := Finset.max'_mem J hJnonempty
    have hjL : j ∈ L := hJL hjJ
    have hKcard : K.card = 2 * r + 1 := by
      have hcardErase := Finset.card_erase_add_one hjJ
      rw [hJcard] at hcardErase
      dsimp only [s, K] at hcardErase ⊢
      omega
    have hKlt : ∀ i ∈ K, i < j := by
      intro i hiK
      have hiJ : i ∈ J := Finset.mem_of_mem_erase hiK
      have hile : i ≤ j := Finset.le_max' J i hiJ
      have hij : i ≠ j := (Finset.mem_erase.mp hiK).1
      omega
    have hhit : ∀ i : {i // i ∈ K},
        ∃ x, x ∈ Hleft j ∪ Hright j ∧ x ∈ cell i.1 := by
      intro i
      have hiJ : i.1 ∈ J := Finset.mem_of_mem_erase i.2
      have hiL : i.1 ∈ L := hJL hiJ
      have hij : i.1 ≠ j := by
        exact (Finset.mem_erase.mp i.2).1
      have hcollision := hLclique hiL hjL hij
      have hforward' := hforward i.1 j (hKlt i.1 i.2)
      rcases hcollision with hbad | hbad | hbad | hbad
      · exact (hbad hforward'.1).elim
      · exact (hbad hforward'.2).elim
      · obtain ⟨x, hxH, hxC⟩ :=
          Finset.not_disjoint_iff.mp hbad
        exact ⟨x, Finset.mem_union_left _ hxH, hxC⟩
      · obtain ⟨x, hxH, hxC⟩ :=
          Finset.not_disjoint_iff.mp hbad
        exact ⟨x, Finset.mem_union_right _ hxH, hxC⟩
    choose hit hhitUnion hhitCell using hhit
    let hitU : {i // i ∈ K} →
        {x // x ∈ Hleft j ∪ Hright j} := fun i =>
      ⟨hit i, hhitUnion i⟩
    have hhitInjective : Function.Injective hitU := by
      intro i t hitEq
      apply Subtype.ext
      by_contra hitNe
      have hdisj : Disjoint (cell i.1) (cell t.1) :=
        hcell hitNe
      have hvalue : hit i = hit t :=
        congrArg Subtype.val hitEq
      exact Finset.disjoint_left.mp hdisj
        (hhitCell i) (hvalue ▸ hhitCell t)
    have hKle :
        K.card ≤ (Hleft j ∪ Hright j).card := by
      simpa only [Fintype.card_coe] using
        Fintype.card_le_of_injective hitU hhitInjective
    have hunionCard :
        (Hleft j ∪ Hright j).card ≤ 2 * r := by
      calc
        (Hleft j ∪ Hright j).card ≤
            (Hleft j).card + (Hright j).card :=
          Finset.card_union_le (Hleft j) (Hright j)
        _ ≤ r + r :=
          Nat.add_le_add (hleftCard j) (hrightCard j)
        _ = 2 * r := by omega
    rw [hKcard] at hKle
    omega
  · refine ⟨L, hLinf, ?_⟩
    intro i hiL j hjL hij
    have hnone := hLindependent hiL hjL hij
    simp only [Collides, not_or, not_not] at hnone
    exact ⟨hnone.1, hnone.2.1⟩

/-- Apply the bounded cross-collision lemma to an additive binary repair
sequence. -/
theorem LowerTriangularBinaryRepairSequence.exists_infinite_crossDisjoint
    {A : Set ℕ} {k q : ℕ}
    (S : LowerTriangularBinaryRepairSequence A k q) :
    ∃ I : Set ℕ, I.Infinite ∧
      ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        Disjoint (S.leftRepair i)
          ({S.anchor j, S.core j} : Finset ℕ) ∧
        Disjoint (S.rightRepair i)
          ({S.anchor j, S.core j} : Finset ℕ) := by
  apply exists_infinite_crossDisjoint_binaryRepairs
    S.cells_disjoint
  · intro i
    exact additiveSupportFamily_cardAtMost
      A (k + 2) (q + S.anchor i)
      (S.leftRepair i) (S.left_mem i)
  · intro i
    exact additiveSupportFamily_cardAtMost
      A (k + 2) (q + S.anchor i)
      (S.rightRepair i) (S.right_mem i)
  · exact S.forward_disjoint

/-- On the cross-disjoint thinning, every binary selector leaves a support
at every indexed translate target.

If the selector chooses the anchor, use the core-private repair; if it
chooses the core, use the anchor-private repair.  Cross-disjointness removes
all other blocks simultaneously. -/
theorem LowerTriangularBinaryRepairSequence.exists_infinite_commonSurvival
    {A : Set ℕ} {k q : ℕ}
    (S : LowerTriangularBinaryRepairSequence A k q) :
    ∃ I : Set ℕ, I.Infinite ∧
      ∀ s : ∀ i : {i // i ∈ I},
          {y // y ∈ ({S.anchor i.1, S.core i.1} : Finset ℕ)},
        ∀ i : {i // i ∈ I},
          ∃ H ∈ additiveSupportFamily A (k + 2)
              (q + S.anchor i.1),
            Disjoint (H : Set ℕ)
              (Set.range fun j => (s j).1) := by
  classical
  obtain ⟨I, hIinf, hcross⟩ := S.exists_infinite_crossDisjoint
  refine ⟨I, hIinf, ?_⟩
  intro s i
  have hselected :
      (s i).1 = S.anchor i.1 ∨ (s i).1 = S.core i.1 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using (s i).2
  rcases hselected with hanchor | hcore
  · refine ⟨S.rightRepair i.1, S.right_mem i.1, ?_⟩
    rw [Set.disjoint_left]
    intro y hyH hyRange
    obtain ⟨j, rfl⟩ := hyRange
    by_cases hji : j.1 = i.1
    · have hSubtype : j = i := Subtype.ext hji
      subst j
      have hInInter :
          (s i).1 ∈
            S.rightRepair i.1 ∩
              {S.anchor i.1, S.core i.1} :=
        Finset.mem_inter.mpr
          ⟨Finset.mem_coe.mp hyH, (s i).2⟩
      have hEqCore : (s i).1 = S.core i.1 := by
        have : (s i).1 ∈ ({S.core i.1} : Finset ℕ) := by
          exact
            (congrArg (fun Z : Finset ℕ => (s i).1 ∈ Z)
              (S.right_private i.1)).mp hInInter
        simpa using this
      exact S.distinct i.1 (hEqCore.symm.trans hanchor)
    · have hdisj :=
        (hcross i.1 i.2 j.1 j.2 (Ne.symm hji)).2
      exact Finset.disjoint_left.mp hdisj
        (Finset.mem_coe.mp hyH) (s j).2
  · refine ⟨S.leftRepair i.1, S.left_mem i.1, ?_⟩
    rw [Set.disjoint_left]
    intro y hyH hyRange
    obtain ⟨j, rfl⟩ := hyRange
    by_cases hji : j.1 = i.1
    · have hSubtype : j = i := Subtype.ext hji
      subst j
      have hInInter :
          (s i).1 ∈
            S.leftRepair i.1 ∩
              {S.anchor i.1, S.core i.1} :=
        Finset.mem_inter.mpr
          ⟨Finset.mem_coe.mp hyH, (s i).2⟩
      have hEqAnchor : (s i).1 = S.anchor i.1 := by
        have : (s i).1 ∈ ({S.anchor i.1} : Finset ℕ) := by
          exact
            (congrArg (fun Z : Finset ℕ => (s i).1 ∈ Z)
              (S.left_private i.1)).mp hInInter
        simpa using this
      exact S.distinct i.1 (hcore.symm.trans hEqAnchor)
    · have hdisj :=
        (hcross i.1 i.2 j.1 j.2 (Ne.symm hji)).1
      exact Finset.disjoint_left.mp hdisj
        (Finset.mem_coe.mp hyH) (s j).2

/-- Reindex a cross-disjoint thinning by `ℕ` and package its binary cells as
an honest finite block partition.  The corresponding translated targets
remain infinite, and every block selector leaves a successor support at
every one of them. -/
theorem LowerTriangularBinaryRepairSequence.exists_binaryCommonSurvivalPartition
    {A : Set ℕ} {k q : ℕ}
    (S : LowerTriangularBinaryRepairSequence A k q) :
    ∃ K : Set ℕ, ∃ cell : ℕ → Finset ℕ, ∃ target : ℕ → ℕ,
      K ⊆ A ∧ K.Infinite ∧
      IsFiniteBlockPartition K cell ∧
      (∀ i, (cell i).card = 2) ∧
      (Set.range target).Infinite ∧
      ∀ s : BlockSelector cell, ∀ i,
        ∃ H ∈ additiveSupportFamily A (k + 2) (target i),
          Disjoint (H : Set ℕ) (selectedSet s) := by
  classical
  obtain ⟨I, hIinf, hcross⟩ := S.exists_infinite_crossDisjoint
  let e : ℕ ↪ {i // i ∈ I} := hIinf.natEmbedding
  let index : ℕ → ℕ := fun i => (e i).1
  let cell : ℕ → Finset ℕ := fun i =>
    {S.anchor (index i), S.core (index i)}
  let target : ℕ → ℕ := fun i => q + S.anchor (index i)
  let K : Set ℕ := {x | ∃ i, x ∈ cell i}
  have hindexMem : ∀ i, index i ∈ I := fun i => (e i).2
  have hindexInjective : Function.Injective index := by
    intro i j hij
    apply e.injective
    exact Subtype.ext hij
  have hcellNonempty : ∀ i, (cell i).Nonempty := by
    intro i
    exact ⟨S.anchor (index i), by simp [cell]⟩
  have hcellDisjoint :
      Pairwise fun i j => Disjoint (cell i) (cell j) := by
    intro i j hij
    exact S.cells_disjoint (hindexInjective.ne hij)
  have hKA : K ⊆ A := by
    rintro x ⟨i, hxi⟩
    have hcases :
        x = S.anchor (index i) ∨ x = S.core (index i) := by
      simpa [cell] using hxi
    rcases hcases with rfl | rfl
    · exact S.anchor_mem (index i)
    · exact S.core_mem (index i)
  have hpointInjective :
      Function.Injective (fun i => S.anchor (index i)) :=
    S.anchor_strictMono.injective.comp hindexInjective
  have hKinf : K.Infinite := by
    exact
      (Set.infinite_range_of_injective hpointInjective).mono <| by
        rintro x ⟨i, rfl⟩
        exact ⟨i, by simp [cell]⟩
  have P : IsFiniteBlockPartition K cell := by
    refine ⟨hcellNonempty, hcellDisjoint, ?_⟩
    intro x
    rfl
  have hcellCard : ∀ i, (cell i).card = 2 := by
    intro i
    exact Finset.card_pair (S.distinct (index i)).symm
  have htargetInjective : Function.Injective target := by
    intro i j hij
    apply hindexInjective
    apply S.anchor_strictMono.injective
    exact Nat.add_left_cancel hij
  have htargetInfinite : (Set.range target).Infinite :=
    Set.infinite_range_of_injective htargetInjective
  refine ⟨K, cell, target, hKA, hKinf, P, hcellCard,
    htargetInfinite, ?_⟩
  intro s i
  have hselected :
      (s i).1 = S.anchor (index i) ∨
        (s i).1 = S.core (index i) := by
    simpa only [cell, Finset.mem_insert, Finset.mem_singleton] using
      (s i).2
  rcases hselected with hanchor | hcore
  · refine ⟨S.rightRepair (index i), ?_, ?_⟩
    · simpa only [target] using S.right_mem (index i)
    · rw [Set.disjoint_left]
      intro y hyH hySelected
      obtain ⟨j, rfl⟩ := hySelected
      by_cases hji : j = i
      · subst j
        have hInInter :
            (s i).1 ∈
              S.rightRepair (index i) ∩
                {S.anchor (index i), S.core (index i)} :=
          Finset.mem_inter.mpr
            ⟨Finset.mem_coe.mp hyH, by simpa only [cell] using (s i).2⟩
        have hEqCore : (s i).1 = S.core (index i) := by
          have :
              (s i).1 ∈ ({S.core (index i)} : Finset ℕ) := by
            exact
              (congrArg (fun Z : Finset ℕ => (s i).1 ∈ Z)
                (S.right_private (index i))).mp hInInter
          simpa using this
        exact S.distinct (index i) (hEqCore.symm.trans hanchor)
      · have hindexNe : index i ≠ index j :=
          hindexInjective.ne (Ne.symm hji)
        have hdisj :=
          (hcross (index i) (hindexMem i)
            (index j) (hindexMem j) hindexNe).2
        exact Finset.disjoint_left.mp hdisj
          (Finset.mem_coe.mp hyH) (by simpa only [cell] using (s j).2)
  · refine ⟨S.leftRepair (index i), ?_, ?_⟩
    · simpa only [target] using S.left_mem (index i)
    · rw [Set.disjoint_left]
      intro y hyH hySelected
      obtain ⟨j, rfl⟩ := hySelected
      by_cases hji : j = i
      · subst j
        have hInInter :
            (s i).1 ∈
              S.leftRepair (index i) ∩
                {S.anchor (index i), S.core (index i)} :=
          Finset.mem_inter.mpr
            ⟨Finset.mem_coe.mp hyH, by simpa only [cell] using (s i).2⟩
        have hEqAnchor : (s i).1 = S.anchor (index i) := by
          have :
              (s i).1 ∈ ({S.anchor (index i)} : Finset ℕ) := by
            exact
              (congrArg (fun Z : Finset ℕ => (s i).1 ∈ Z)
                (S.left_private (index i))).mp hInInter
          simpa using this
        exact S.distinct (index i) (hcore.symm.trans hEqAnchor)
      · have hindexNe : index i ≠ index j :=
          hindexInjective.ne (Ne.symm hji)
        have hdisj :=
          (hcross (index i) (hindexMem i)
            (index j) (hindexMem j) hindexNe).1
        exact Finset.disjoint_left.mp hdisj
          (Finset.mem_coe.mp hyH) (by simpa only [cell] using (s j).2)

/-- Group cross-disjoint binary repair cells into blocks of increasing size.

Block `i` contains `i+2` binary cells.  A selector chooses only one point
from the whole block, so at most one subcell is touched.  The private repair
in that subcell and cross-disjointness from every other subcell preserve
every translated target indexed by the block.  In particular the common
survival construction is compatible with block capacities tending to
infinity. -/
theorem LowerTriangularBinaryRepairSequence.exists_growingBlockCommonSurvivalPartition
    {A : Set ℕ} {k q : ℕ}
    (S : LowerTriangularBinaryRepairSequence A k q) :
    ∃ K : Set ℕ, ∃ cell : ℕ → Finset ℕ,
      ∃ target : ℕ → ℕ → ℕ,
      K ⊆ A ∧ K.Infinite ∧
      IsFiniteBlockPartition K cell ∧
      (∀ i, (cell i).card = 2 * (i + 2)) ∧
      (Set.range fun i => target i 0).Infinite ∧
      ∀ s : BlockSelector cell, ∀ i j, j < i + 2 →
        ∃ H ∈ additiveSupportFamily A (k + 2) (target i j),
          Disjoint (H : Set ℕ) (selectedSet s) := by
  classical
  obtain ⟨I, hIinf, hcross⟩ := S.exists_infinite_crossDisjoint
  let e : ℕ ↪ {i // i ∈ I} := hIinf.natEmbedding
  let index : ℕ → ℕ := fun n => (e n).1
  let binaryCell : ℕ → Finset ℕ := fun n =>
    {S.anchor (index n), S.core (index n)}
  let slot : ℕ → ℕ → ℕ := fun i j => Nat.pair i j
  let cell : ℕ → Finset ℕ := fun i =>
    (Finset.range (i + 2)).biUnion fun j =>
      binaryCell (slot i j)
  let target : ℕ → ℕ → ℕ := fun i j =>
    q + S.anchor (index (slot i j))
  let K : Set ℕ := {x | ∃ i, x ∈ cell i}
  have hindexMem : ∀ n, index n ∈ I := fun n => (e n).2
  have hindexInjective : Function.Injective index := by
    intro m n hmn
    apply e.injective
    exact Subtype.ext hmn
  have hbinaryNonempty : ∀ n, (binaryCell n).Nonempty := by
    intro n
    exact ⟨S.anchor (index n), by simp [binaryCell]⟩
  have hbinaryCard : ∀ n, (binaryCell n).card = 2 := by
    intro n
    exact Finset.card_pair (S.distinct (index n)).symm
  have hbinaryDisjoint : ∀ m n, m ≠ n →
      Disjoint (binaryCell m) (binaryCell n) := by
    intro m n hmn
    exact S.cells_disjoint (hindexInjective.ne hmn)
  have hcellNonempty : ∀ i, (cell i).Nonempty := by
    intro i
    refine ⟨S.anchor (index (slot i 0)), ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
    simp [binaryCell]
  have hcellDisjoint :
      Pairwise fun i j => Disjoint (cell i) (cell j) := by
    intro i l hil
    rw [Finset.disjoint_left]
    intro x hxi hxl
    obtain ⟨j, hjRange, hxj⟩ := Finset.mem_biUnion.mp hxi
    obtain ⟨m, hmRange, hxm⟩ := Finset.mem_biUnion.mp hxl
    have hslotNe : slot i j ≠ slot l m := by
      intro heq
      exact hil (Nat.pair_eq_pair.mp heq).1
    exact Finset.disjoint_left.mp
      (hbinaryDisjoint (slot i j) (slot l m) hslotNe)
        hxj hxm
  have hKA : K ⊆ A := by
    rintro x ⟨i, hxi⟩
    obtain ⟨j, _hjRange, hxj⟩ := Finset.mem_biUnion.mp hxi
    have hcases :
        x = S.anchor (index (slot i j)) ∨
          x = S.core (index (slot i j)) := by
      simpa [binaryCell] using hxj
    rcases hcases with rfl | rfl
    · exact S.anchor_mem _
    · exact S.core_mem _
  have hpointInjective :
      Function.Injective
        (fun i => S.anchor (index (slot i 0))) := by
    intro i l hil
    have hindex :
        index (slot i 0) = index (slot l 0) :=
      S.anchor_strictMono.injective hil
    have hslot : slot i 0 = slot l 0 :=
      hindexInjective hindex
    exact (Nat.pair_eq_pair.mp hslot).1
  have hKInfinite : K.Infinite := by
    apply (Set.infinite_range_of_injective hpointInjective).mono
    rintro x ⟨i, rfl⟩
    refine ⟨i, ?_⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨0, Finset.mem_range.mpr (by omega), by simp [binaryCell]⟩
  have P : IsFiniteBlockPartition K cell := by
    exact ⟨hcellNonempty, hcellDisjoint, fun x => Iff.rfl⟩
  have hcellCard : ∀ i, (cell i).card = 2 * (i + 2) := by
    intro i
    have hpieces :
        (Finset.range (i + 2) : Set ℕ).PairwiseDisjoint
          (fun j => binaryCell (slot i j)) := by
      intro j _hj m _hm hjm
      apply hbinaryDisjoint
      intro heq
      exact hjm (Nat.pair_eq_pair.mp heq).2
    change
      ((Finset.range (i + 2)).biUnion fun j =>
        binaryCell (slot i j)).card = 2 * (i + 2)
    rw [Finset.card_biUnion hpieces]
    calc
      (∑ j ∈ Finset.range (i + 2),
          (binaryCell (slot i j)).card) =
          ∑ _j ∈ Finset.range (i + 2), 2 := by
            apply Finset.sum_congr rfl
            intro j _hj
            exact hbinaryCard (slot i j)
      _ = 2 * (i + 2) := by simp [Nat.mul_comm]
  have htargetInjective :
      Function.Injective (fun i => target i 0) := by
    intro i l hil
    apply (Nat.pair_eq_pair.mp
      (hindexInjective
        (S.anchor_strictMono.injective
          (Nat.add_left_cancel hil)))).1
  have htargetInfinite :
      (Set.range fun i => target i 0).Infinite :=
    Set.infinite_range_of_injective htargetInjective
  refine ⟨K, cell, target, hKA, hKInfinite, P, hcellCard,
    htargetInfinite, ?_⟩
  intro s i j hj
  let n := slot i j
  have hleftCross : ∀ m, m ≠ n →
      Disjoint (S.leftRepair (index n)) (binaryCell m) := by
    intro m hmn
    have hactual :
        index n ≠ index m := by
      intro heq
      exact hmn (hindexInjective heq.symm)
    exact (hcross (index n) (hindexMem n)
      (index m) (hindexMem m) hactual).1
  have hrightCross : ∀ m, m ≠ n →
      Disjoint (S.rightRepair (index n)) (binaryCell m) := by
    intro m hmn
    have hactual :
        index n ≠ index m := by
      intro heq
      exact hmn (hindexInjective heq.symm)
    exact (hcross (index n) (hindexMem n)
      (index m) (hindexMem m) hactual).2
  have repairDisjoint
      (H : Finset ℕ)
      (hown : (s i).1 ∉ H)
      (hother : ∀ m, m ≠ n → Disjoint H (binaryCell m)) :
      Disjoint (H : Set ℕ) (selectedSet s) := by
    rw [Set.disjoint_left]
    intro x hxH hxSelected
    obtain ⟨l, hlx⟩ := hxSelected
    change (s l).1 = x at hlx
    obtain ⟨m, hmRange, hselectedCell⟩ :=
      Finset.mem_biUnion.mp (s l).2
    by_cases hmn : slot l m = n
    · have hpairs := Nat.pair_eq_pair.mp hmn
      have hli : l = i := hpairs.1
      subst l
      exact hown (hlx ▸ Finset.mem_coe.mp hxH)
    · exact Finset.disjoint_left.mp
        (hother (slot l m) hmn)
          (Finset.mem_coe.mp hxH) (by
            rw [← hlx]
            exact hselectedCell)
  obtain ⟨m, hmRange, hselectedCell⟩ :=
    Finset.mem_biUnion.mp (s i).2
  by_cases hmj : m = j
  · subst m
    have hselectedCases :
        (s i).1 = S.anchor (index n) ∨
          (s i).1 = S.core (index n) := by
      simpa [binaryCell, n] using hselectedCell
    rcases hselectedCases with hanchor | hcore
    · refine ⟨S.rightRepair (index n), ?_, ?_⟩
      · simpa [target, n] using S.right_mem (index n)
      · apply repairDisjoint
        · intro hmem
          have hinter :
              (s i).1 ∈
                S.rightRepair (index n) ∩ binaryCell n :=
            Finset.mem_inter.mpr
              ⟨hmem, by simpa [binaryCell, hanchor]⟩
          have hcoreMem :
              (s i).1 ∈ ({S.core (index n)} : Finset ℕ) := by
            exact
              (congrArg (fun Z : Finset ℕ => (s i).1 ∈ Z)
                (S.right_private (index n))).mp
                (by simpa [binaryCell] using hinter)
          exact S.distinct (index n)
            (by
              have : S.anchor (index n) = S.core (index n) := by
                simpa [hanchor] using hcoreMem
              exact this.symm)
        · exact hrightCross
    · refine ⟨S.leftRepair (index n), ?_, ?_⟩
      · simpa [target, n] using S.left_mem (index n)
      · apply repairDisjoint
        · intro hmem
          have hinter :
              (s i).1 ∈
                S.leftRepair (index n) ∩ binaryCell n :=
            Finset.mem_inter.mpr
              ⟨hmem, by simpa [binaryCell, hcore]⟩
          have hanchorMem :
              (s i).1 ∈ ({S.anchor (index n)} : Finset ℕ) := by
            exact
              (congrArg (fun Z : Finset ℕ => (s i).1 ∈ Z)
                (S.left_private (index n))).mp
                (by simpa [binaryCell] using hinter)
          exact S.distinct (index n)
            (by simpa [hcore] using hanchorMem)
        · exact hleftCross
  · refine ⟨S.leftRepair (index n), ?_, ?_⟩
    · simpa [target, n] using S.left_mem (index n)
    · apply repairDisjoint
      · exact fun hmem =>
          Finset.disjoint_left.mp
            (hleftCross (slot i m) (by
              intro heq
              exact hmj (Nat.pair_eq_pair.mp heq).2))
            hmem hselectedCell
      · exact hleftCross

/-- Gap-free common-survival payoff for the bounded moving branch at a
represented predecessor target. -/
theorem boundedFullTranslateDestroyers_commonSurvival
    {A : Set ℕ} {k q : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hfull :
      HasBoundedFullTranslateDestroyersByAnchor A (k + 1) {q})
    (hqrep : (additiveSupportFamily A (k + 1) q).Nonempty) :
    ∃ K : Set ℕ, ∃ cell : ℕ → Finset ℕ, ∃ target : ℕ → ℕ,
      K ⊆ A ∧ K.Infinite ∧
      IsFiniteBlockPartition K cell ∧
      (∀ i, (cell i).card = 2) ∧
      (Set.range target).Infinite ∧
      ∀ s : BlockSelector cell, ∀ i,
        ∃ H ∈ additiveSupportFamily A (k + 2) (target i),
          Disjoint (H : Set ℕ) (selectedSet s) := by
  obtain ⟨S⟩ :=
    exists_lowerTriangularBinaryRepairSequence hbasis hfull hqrep
  obtain ⟨K, cell, target, hKA, hK, P, hcellCard,
      htarget, hsurvive⟩ :=
    S.exists_binaryCommonSurvivalPartition
  exact ⟨K, cell, target, hKA, hK, P, hcellCard,
    htarget, hsurvive⟩

/-- Growing-block form of bounded-moving common survival.

The same binary repair sequence can be grouped before strong deletion is
invoked, so its certificate partition has unbounded block capacity rather
than permanent two-point blocks. -/
theorem boundedFullTranslateDestroyers_growingBlockCommonSurvival
    {A : Set ℕ} {k q : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hfull :
      HasBoundedFullTranslateDestroyersByAnchor A (k + 1) {q})
    (hqrep : (additiveSupportFamily A (k + 1) q).Nonempty) :
    ∃ K : Set ℕ, ∃ cell : ℕ → Finset ℕ,
      ∃ target : ℕ → ℕ → ℕ,
      K ⊆ A ∧ K.Infinite ∧
      IsFiniteBlockPartition K cell ∧
      (∀ i, (cell i).card = 2 * (i + 2)) ∧
      (Set.range fun i => target i 0).Infinite ∧
      ∀ s : BlockSelector cell, ∀ i j, j < i + 2 →
        ∃ H ∈ additiveSupportFamily A (k + 2) (target i j),
          Disjoint (H : Set ℕ) (selectedSet s) := by
  obtain ⟨S⟩ :=
    exists_lowerTriangularBinaryRepairSequence hbasis hfull hqrep
  exact S.exists_growingBlockCommonSurvivalPartition

/-- Full gap-branch payoff: bounded successor transversals over one
represented primitive gap force an infinite binary deletion reservoir on
which every selector preserves an unbounded family of successor targets. -/
theorem boundedFullTranslateDestroyers_gapBranch_commonSurvival
    {A : Set ℕ} {k q d b : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hfull :
      HasBoundedFullTranslateDestroyersByAnchor A (k + 1) {q})
    (hbA : b ∈ A)
    (hqdb : q = d + b)
    (hqrep : (additiveSupportFamily A (k + 1) q).Nonempty)
    (hgap : additiveSupportFamily A k d = ∅) :
    ∃ S : LowerTriangularBinaryRepairSequence A k q,
      ∃ I : Set ℕ, I.Infinite ∧
        ∀ s : ∀ i : {i // i ∈ I},
            {y // y ∈ ({S.anchor i.1, S.core i.1} : Finset ℕ)},
          ∀ i : {i // i ∈ I},
            ∃ H ∈ additiveSupportFamily A (k + 2)
                (q + S.anchor i.1),
              Disjoint (H : Set ℕ)
                (Set.range fun j => (s j).1) := by
  obtain ⟨S⟩ :=
    exists_lowerTriangularBinaryRepairSequence_over_gap
      hbasis hfull hbA hqdb hqrep hgap
  obtain ⟨I, hIinf, hsurvive⟩ :=
    S.exists_infinite_commonSurvival
  exact ⟨S, I, hIinf, hsurvive⟩

/-- The exact obstruction produced when a binary common-survival partition
is placed inside a strong-deletion counterexample.  The protected targets
are infinite, but every arbitrarily late cardinal-minimal selector
certificate is forced completely away from them. -/
def HasGapBinaryCertificateMigration
    (A : Set ℕ) (h : ℕ) : Prop :=
  ∃ K : Set ℕ, ∃ cell : ℕ → Finset ℕ, ∃ target : ℕ → ℕ,
    K ⊆ A ∧ K.Infinite ∧
    IsFiniteBlockPartition K cell ∧
    (∀ i, (cell i).card = 2) ∧
    (Set.range target).Infinite ∧
    (∀ s : BlockSelector cell, ∀ i,
      ∃ H ∈ additiveSupportFamily A h (target i),
        Disjoint (H : Set ℕ) (selectedSet s)) ∧
    ∀ N, ∃ Q : Finset ℕ,
      Q.Nonempty ∧
      (∀ u ∈ Q, N ≤ u) ∧
      (∀ s : BlockSelector cell, ∃ u ∈ Q,
        DestroysAt (additiveSupportFamily A h)
          (selectedSet s) u) ∧
      (∀ u ∈ Q, ∃ s : BlockSelector cell,
        DestroysAt (additiveSupportFamily A h)
          (selectedSet s) u ∧
        ∀ u' ∈ Q, u' ≠ u →
          ¬ DestroysAt (additiveSupportFamily A h)
            (selectedSet s) u') ∧
      Disjoint (Q : Set ℕ) (Set.range target)

/-- Growing-block binary migration inside a successor counterexample.

Besides the target-localized certificate, this retains the entire grouped
binary grid and the exact formula `|cell i| = 2(i+2)`, allowing the
certificate-safe old/contemporary machinery to operate on the actual repair
reservoir. -/
theorem boundedFullTranslateDestroyers_forces_growingBlockCertificateMigration
    {A : Set ℕ} {k q : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hfull :
      HasBoundedFullTranslateDestroyersByAnchor A (k + 1) {q})
    (hqrep : (additiveSupportFamily A (k + 1) q).Nonempty)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) (k + 2)) :
    ∃ K : Set ℕ, ∃ cell : ℕ → Finset ℕ,
      ∃ target : ℕ → ℕ → ℕ,
      ∃ P : IsFiniteBlockPartition K cell,
      K ⊆ A ∧ K.Infinite ∧
      (∀ i, (cell i).card = 2 * (i + 2)) ∧
      (Set.range fun i => target i 0).Infinite ∧
      (∀ s : BlockSelector cell, ∀ i j, j < i + 2 →
        ∃ H ∈ additiveSupportFamily A (k + 2) (target i j),
          Disjoint (H : Set ℕ) (selectedSet s)) ∧
      ∀ N, ∃ Q : Finset ℕ,
        Q.Nonempty ∧
        (∀ u ∈ Q, N ≤ u) ∧
        (∀ s : BlockSelector cell, ∃ u ∈ Q,
          DestroysAt (additiveSupportFamily A (k + 2))
            (selectedSet s) u) ∧
        (∀ u ∈ Q, ∃ s : BlockSelector cell,
          DestroysAt (additiveSupportFamily A (k + 2))
            (selectedSet s) u ∧
          ∀ u' ∈ Q, u' ≠ u →
            ¬ DestroysAt (additiveSupportFamily A (k + 2))
              (selectedSet s) u') ∧
        Disjoint (Q : Set ℕ)
          (Set.range fun i => target i 0) := by
  obtain ⟨K, cell, target, hKA, hKInfinite, P, hcellCard,
      htargetInfinite, hsurvival⟩ :=
    boundedFullTranslateDestroyers_growingBlockCommonSurvival
      hbasis hfull hqrep
  refine ⟨K, cell, target, P, hKA, hKInfinite, hcellCard,
    htargetInfinite, hsurvival, ?_⟩
  exact strongDeletion_certificate_avoids_unboundedCommonSurvivalTargets
    (strongExactDeletion_of_counterexample hcounter)
    hKA P htargetInfinite (fun s i => hsurvival s i 0 (by omega))

/-- Run the certificate-safe contemporary amplifier on the grouped binary
reservoir.

For every support demand and lateness threshold, a localized successor
certificate has a minimal selected destroyer `D`.  Taking the old prefix to
be the blocks below the exact incidence budget makes every later grouped
block large enough.  Hence either a coherent predecessor difference already
has more than the requested number of supports, or all but at most
`|J| r` points of `D` lie in that finite old prefix. -/
theorem boundedFullTranslateDestroyers_growingBlock_activeSplit
    {A : Set ℕ} {k q₀ : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hfull :
      HasBoundedFullTranslateDestroyersByAnchor A (k + 1) {q₀})
    (hqrep : (additiveSupportFamily A (k + 1) q₀).Nonempty)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) (k + 2)) :
    ∃ K : Set ℕ, ∃ cell : ℕ → Finset ℕ,
      ∃ target : ℕ → ℕ → ℕ,
      ∃ P : IsFiniteBlockPartition K cell,
      K ⊆ A ∧ K.Infinite ∧
      (∀ i, (cell i).card = 2 * (i + 2)) ∧
      (Set.range fun i => target i 0).Infinite ∧
      (∀ s : BlockSelector cell, ∀ i j, j < i + 2 →
        ∃ H ∈ additiveSupportFamily A (k + 2) (target i j),
          Disjoint (H : Set ℕ) (selectedSet s)) ∧
      ∀ r L, ∃ Q : Finset ℕ, ∃ q ∈ Q,
        ∃ s : BlockSelector cell, ∃ D J : Finset ℕ,
        L ≤ q ∧
        (∀ t : BlockSelector cell, ∃ u ∈ Q,
          DestroysAt (additiveSupportFamily A (k + 2))
            (selectedSet t) u) ∧
        DestroysAt (additiveSupportFamily A (k + 2))
          (selectedSet s) q ∧
        (∀ u ∈ Q, u ≠ q →
          ¬ DestroysAt (additiveSupportFamily A (k + 2))
            (selectedSet s) u) ∧
        IsInclusionMinimalDestroyer
          (additiveSupportFamily A (k + 2)) D q ∧
        (D : Set ℕ) ⊆ selectedSet s ∧
        J = Finset.range
          (D.card * ((k + 1) * r) +
            (k + 2) * Q.card + (k + 1) + 3) ∧
        ((∃ d, r <
            (additiveSupportFamily A (k + 1) (q - d)).card) ∨
          (D.filter fun d => blockIndex P d ∉ J).card
            ≤ J.card * r) := by
  classical
  obtain ⟨K, cell, target, P, hKA, hKInfinite, hcellCard,
      htargetInfinite, hsurvival, hcertificates⟩ :=
    boundedFullTranslateDestroyers_forces_growingBlockCertificateMigration
      hbasis hfull hqrep hcounter
  refine ⟨K, cell, target, P, hKA, hKInfinite, hcellCard,
    htargetInfinite, hsurvival, ?_⟩
  intro r L
  obtain ⟨Q, hQnonempty, hQlate, hcert, hlocalized, _hQsafe⟩ :=
    hcertificates L
  obtain ⟨q, hqQ⟩ := hQnonempty
  obtain ⟨s, hqDestroy, hother⟩ := hlocalized q hqQ
  obtain ⟨D, hDselectedRaw, _hDcardRaw, hDdestroy⟩ :=
    exists_finiteSelectedDestroyer_of_destroysAt
      P s hqDestroy
  obtain ⟨D₀, hD₀D, hminimal⟩ :=
    exists_inclusionMinimalDestroyer_subset hDdestroy
  have hD₀selected : (D₀ : Set ℕ) ⊆ selectedSet s := by
    intro x hxD₀
    exact hDselectedRaw (Finset.mem_coe.mpr
      (hD₀D (Finset.mem_coe.mp hxD₀)))
  let budget :=
    D₀.card * ((k + 1) * r) +
      (k + 2) * Q.card + (k + 1) + 3
  let J := Finset.range budget
  have hcontemporary : ∀ j, j ∉ J →
      D₀.card * ((k + 1) * r) +
          (k + 2) * Q.card + (k + 1) + 3 ≤
        (cell j).card := by
    intro j hjJ
    have hbudgetLe : budget ≤ j := by
      apply Nat.le_of_not_gt
      intro hj
      exact hjJ (Finset.mem_range.mpr hj)
    rw [hcellCard j]
    dsimp only [budget] at hbudgetLe ⊢
    omega
  refine ⟨Q, q, hqQ, s, D₀, J, hQlate q hqQ, hcert,
    hqDestroy, hother, hminimal, hD₀selected, rfl, ?_⟩
  by_cases hmany :
      J.card * r <
        (D₀.filter fun d => blockIndex P d ∉ J).card
  · obtain hdirect | hold :=
      positiveOrder_targetLocalized_manyContemporaryPoints_force_growth_onReservoir
        hKA P s (k := k + 1) (by omega) hcert hother
          hminimal hD₀selected hcontemporary hmany
    · exact Or.inl ⟨hdirect.choose,
        hdirect.choose_spec.2.2⟩
    · exact Or.inl ⟨(s hold.choose).1,
        hold.choose_spec.2⟩
  · exact Or.inr (Nat.le_of_not_gt hmany)

/-- The counterexample/migration bridge is likewise gap-free.  At every
represented fixed predecessor target supporting the bounded moving branch,
the hypothetical failure of all infinite successor deletions forces late
finite certificates away from the branch's entire protected target stream.
-/
theorem boundedFullTranslateDestroyers_forces_certificateMigration
    {A : Set ℕ} {k q : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hfull :
      HasBoundedFullTranslateDestroyersByAnchor A (k + 1) {q})
    (hqrep : (additiveSupportFamily A (k + 1) q).Nonempty)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) (k + 2)) :
    HasGapBinaryCertificateMigration A (k + 2) := by
  obtain ⟨K, cell, target, hKA, hK, P, hcellCard,
      htarget, hsurvive⟩ :=
    boundedFullTranslateDestroyers_commonSurvival hbasis hfull hqrep
  refine ⟨K, cell, target, hKA, hK, P, hcellCard,
    htarget, hsurvive, ?_⟩
  exact strongDeletion_certificate_avoids_unboundedCommonSurvivalTargets
    (strongExactDeletion_of_counterexample hcounter)
    hKA P htarget hsurvive

/-- Exhaustive fixed-translate consequence of a successor counterexample.
For every represented predecessor target `q`, either the whole translate
`q+A` already has successor matching growth outside one finite core, or the
bounded moving branch yields the binary common-survival/certificate-migration
obstruction above. -/
theorem singletonTranslateGrowth_or_binaryCertificateMigration
    {A : Set ℕ} {k q : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hqrep : (additiveSupportFamily A (k + 1) q).Nonempty)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) (k + 2)) :
    HasSingletonTranslateMatchingGrowth A (k + 1) q ∨
      HasGapBinaryCertificateMigration A (k + 2) := by
  obtain hgrowth | hmoving :=
    finiteCore_translateMatchingGrowth_or_recurrentBoundedMoving
      (A := A) (Q := {q})
      (R := additiveSupportFamily A (k + 2))
      (additiveSupportFamily_supportsIn A (k + 2))
      (additiveSupportFamily_cardAtMost A (k + 2))
  · exact Or.inl hgrowth
  · right
    apply boundedFullTranslateDestroyers_forces_certificateMigration
      hbasis _ hqrep hcounter
    exact
      boundedFullTranslateDestroyersByAnchor_of_boundedMovingOnFiniteTranslates
        hbasis (by simp) hmoving

/-- Tail form: under a successor counterexample, every sufficiently large
predecessor label is forced into one of the two explicit regimes—relative
matching growth or binary certificate migration. -/
theorem IsExactTupleAsymptoticBasis.eventually_singletonTranslateGrowth_or_binaryMigration
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) (k + 2)) :
    ∃ N, ∀ q, N ≤ q →
      HasSingletonTranslateMatchingGrowth A (k + 1) q ∨
        HasGapBinaryCertificateMigration A (k + 2) := by
  obtain ⟨N, hN⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  refine ⟨N, ?_⟩
  intro q hq
  obtain ⟨E, hER, _hEempty⟩ := hN q hq
  exact singletonTranslateGrowth_or_binaryCertificateMigration
    hbasis ⟨E, hER⟩ hcounter

/-- A counterexample to infinite deletion cannot merely coexist with the
gap-branch repairs: it must produce arbitrarily late finite selector
certificates which migrate off the entire unbounded protected translate
family.  This combines the strong order-`k+2` deletion hypothesis with the
bounded successor transversals and the cross-block thinning in one theorem.
-/
theorem boundedFullTranslateDestroyers_gapBranch_forces_certificateMigration
    {A : Set ℕ} {k q d b : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hfull :
      HasBoundedFullTranslateDestroyersByAnchor A (k + 1) {q})
    (hbA : b ∈ A)
    (hqdb : q = d + b)
    (hqrep : (additiveSupportFamily A (k + 1) q).Nonempty)
    (hgap : additiveSupportFamily A k d = ∅)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) (k + 2)) :
    HasGapBinaryCertificateMigration A (k + 2) := by
  obtain ⟨S⟩ :=
    exists_lowerTriangularBinaryRepairSequence_over_gap
      hbasis hfull hbA hqdb hqrep hgap
  obtain ⟨K, cell, target, hKA, hK, P, hcellCard,
      htarget, hsurvive⟩ :=
    S.exists_binaryCommonSurvivalPartition
  refine ⟨K, cell, target, hKA, hK, P, hcellCard,
    htarget, hsurvive, ?_⟩
  exact strongDeletion_certificate_avoids_unboundedCommonSurvivalTargets
    (strongExactDeletion_of_counterexample hcounter)
    hKA P htarget hsurvive

/-- A represented target immediately above a genuine lower-order gap
transports the entire bounded recurrent successor obstruction down one
order.

Write `q = d + b`, where `b ∈ A`, `q` has an order-`k+1` support, but `d`
has no order-`k` support.  Protect both `b` and one support of `q`.  Any
successor destroyer over `q+a` which avoids that protection must contain
its translate anchor `a`; otherwise ordinary successor descent would make
it destroy the protected support of `q`.  The gap lemma then says that
erasing `a` destroys the order-`k+1` target `d+a`.

Consequently bounded full translate destroyers at order `k+2` over
`q+A` yield bounded full translate destroyers at order `k+1` over the gap
translate `d+A`. -/
theorem boundedFullTranslateDestroyers_descend_over_gap
    {A : Set ℕ} {k q d b : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hfull :
      HasBoundedFullTranslateDestroyersByAnchor A (k + 1) {q})
    (hbA : b ∈ A)
    (hqdb : q = d + b)
    (hqrep : (additiveSupportFamily A (k + 1) q).Nonempty)
    (hgap : additiveSupportFamily A k d = ∅) :
    HasBoundedFullTranslateDestroyersByAnchor A k {d} := by
  classical
  obtain ⟨N, hN⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  obtain ⟨E, hER⟩ := hqrep
  intro F hFA
  let F' := insert b (F ∪ E)
  have hF'A : (F' : Set ℕ) ⊆ A := by
    intro x hxF'
    rcases Finset.mem_insert.mp hxF' with rfl | hxUnion
    · exact hbA
    · rcases Finset.mem_union.mp hxUnion with hxF | hxE
      · exact hFA hxF
      · exact additiveSupportFamily_supportsIn
          A (k + 1) q E hER x hxE
  obtain ⟨m, hm⟩ := hfull F' hF'A
  refine ⟨m - 1, ?_⟩
  intro L
  obtain ⟨n, T, q', a, haLower, hq'singleton, haA, hnq'a,
      hTA, hTF', hTnonempty, hTcard, hdestroy⟩ :=
    hm (max L N)
  have hq'eq : q' = q := by
    simpa using hq'singleton
  subst q'
  have hLa : L ≤ a :=
    le_trans (le_max_left L N) haLower
  have hNa : N ≤ a :=
    le_trans (le_max_right L N) haLower
  have hbT : b ∉ T := by
    intro hbT
    apply Finset.disjoint_left.mp hTF' hbT
    exact Finset.mem_insert_self b (F ∪ E)
  have hET : Disjoint (E : Set ℕ) (T : Set ℕ) := by
    rw [Set.disjoint_left]
    intro x hxE hxT
    apply Finset.disjoint_left.mp hTF' hxT
    exact Finset.mem_insert_of_mem
      (Finset.mem_union_right F hxE)
  have haT : a ∈ T := by
    by_contra haT
    have han : a ≤ n := by omega
    have hnsub : n - a = q := by omega
    have hdescend :
        DestroysAt
          (additiveSupportFamily A (k + 1)) (T : Set ℕ) q := by
      rw [← hnsub]
      exact additiveSuccessorTransversalsDescend
        A (k + 1) T n hdestroy a haA
          (by simpa using haT) han
    exact (hdescend E hER) hET
  let D := T.erase a
  have hgap' : additiveSupportFamily A k (q - b) = ∅ := by
    have hqb : b ≤ q := by omega
    have hsub : q - b = d := by omega
    rw [hsub]
    exact hgap
  have hdestroyD :
      DestroysAt
        (additiveSupportFamily A (k + 1))
        (D : Set ℕ) (d + a) := by
    have hdestroy' :
        DestroysAt
          (additiveSupportFamily A (k + 2))
          (T : Set ℕ) (q + a) := by
      simpa [hnq'a, Nat.add_assoc] using hdestroy
    have hraw :
        DestroysAt
          (additiveSupportFamily A (k + 1))
          ((T.erase a : Finset ℕ) : Set ℕ) (q + a - b) :=
      gapAnchor_erasedCore_destroys_predecessor
        (A := A) (k := k) (q := q) (a := a) (b := b) (T := T)
        hdestroy' hbA hbT (by omega) hgap'
    have htarget : q + a - b = d + a := by omega
    simpa [D, htarget] using hraw
  have hDnonempty : D.Nonempty := by
    obtain ⟨G, hGR, _⟩ :=
      hN (d + a) (le_trans hNa (Nat.le_add_left a d))
    by_contra hDempty
    have hDeq : D = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hDempty
    have hdisj : Disjoint (G : Set ℕ) (D : Set ℕ) := by
      simp [hDeq]
    exact (hdestroyD G hGR) hdisj
  have hDA : ∀ x ∈ D, x ∈ A := by
    intro x hxD
    exact hTA x (Finset.mem_of_mem_erase hxD)
  have hDF : Disjoint D F := by
    rw [Finset.disjoint_left]
    intro x hxD hxF
    apply Finset.disjoint_left.mp hTF'
      (Finset.mem_of_mem_erase hxD)
    exact Finset.mem_insert_of_mem
      (Finset.mem_union_left E hxF)
  have hDcard : D.card ≤ m - 1 := by
    have hcardErase : D.card + 1 = T.card := by
      simpa [D] using Finset.card_erase_add_one haT
    omega
  exact ⟨d + a, D, d, a, hLa, by simp, haA, rfl,
    hDA, hDF, hDnonempty, hDcard, hdestroyD⟩

/-- Cardinal-preserving descent of an entire support star.  If every support
in `𝒢` contains `x`, removing one occurrence of `x` embeds `𝒢` into the
order-one-lower support family at target `m-x`. -/
theorem additiveSupportStar_descends_card
    {A : Set ℕ} {k m x : ℕ} {𝒢 : Finset (Finset ℕ)}
    (hsub : 𝒢 ⊆ additiveSupportFamily A (k + 1) m)
    (hx : ∀ E ∈ 𝒢, x ∈ E) :
    ∃ ℋ : Finset (Finset ℕ),
      ℋ ⊆ additiveSupportFamily A k (m - x) ∧
      ℋ.card = 𝒢.card := by
  classical
  have hlower : ∀ E : {E // E ∈ 𝒢},
      ∃ H ∈ additiveSupportFamily A k (m - x),
        E.1 = insert x H := by
    intro E
    exact additiveSupport_remove_hit_succ
      (hsub E.2) (hx E.1 E.2)
  let lower : {E // E ∈ 𝒢} → Finset ℕ := fun E =>
    (hlower E).choose
  have hlowerR : ∀ E, lower E ∈
      additiveSupportFamily A k (m - x) := by
    intro E
    exact (hlower E).choose_spec.1
  have hreconstruct : ∀ E, E.1 = insert x (lower E) := by
    intro E
    exact (hlower E).choose_spec.2
  have hlowerInjective : Function.Injective lower := by
    intro E D hED
    apply Subtype.ext
    rw [hreconstruct E, hreconstruct D, hED]
  let ℋ := 𝒢.attach.image lower
  refine ⟨ℋ, ?_, ?_⟩
  · intro H hH
    obtain ⟨E, _hEattach, rfl⟩ := Finset.mem_image.mp hH
    exact hlowerR E
  · dsimp only [ℋ]
    rw [Finset.card_image_iff.mpr hlowerInjective.injOn,
      Finset.card_attach]

/-- The additive rank-descent fork.  A sufficiently large order-`k+1`
support family either already contains a large matching, or one common hit
can be removed while retaining more than `s` distinct supports at order
`k`.

Iterating this fork cannot descend past order one, whose support family has
cardinality at most one.  Thus sufficiently rapid support growth forces a
large matching after adjoining only a bounded root of removed summands. -/
theorem large_additiveSupportFamily_matching_or_lowerOrderGrowth
    {A : Set ℕ} {k m r s : ℕ}
    (hlarge : (((k + 1) * r) * s) <
      (additiveSupportFamily A (k + 1) m).card) :
    (∃ M : Finset (Finset ℕ),
        M ⊆ additiveSupportFamily A (k + 1) m ∧
        IsMatching M ∧ r < M.card) ∨
      ∃ x ∈ A, x ≤ m ∧
        s < (additiveSupportFamily A k (m - x)).card := by
  classical
  let H := additiveSupportFamily A (k + 1) m
  have hedges : ∀ E ∈ H, E.Nonempty := by
    intro E hEH
    exact additiveSupportFamily_supportsNonempty
      A (Nat.zero_lt_succ k) m E hEH
  have hsize : ∀ E ∈ H, E.card ≤ k + 1 := by
    intro E hEH
    exact additiveSupportFamily_cardAtMost A (k + 1) m E hEH
  obtain ⟨M, hMH, hMmatching, hMcard⟩ | ⟨x, hxstar⟩ :=
    large_boundedHypergraph_matching_or_star
      hedges hsize hlarge
  · exact Or.inl ⟨M, hMH, hMmatching, hMcard⟩
  · right
    let 𝒢 := H.filter fun E => x ∈ E
    have h𝒢sub : 𝒢 ⊆ additiveSupportFamily A (k + 1) m := by
      intro E hE
      exact (Finset.mem_filter.mp hE).1
    have hx𝒢 : ∀ E ∈ 𝒢, x ∈ E := by
      intro E hE
      exact (Finset.mem_filter.mp hE).2
    obtain ⟨ℋ, hℋsub, hℋcard⟩ :=
      additiveSupportStar_descends_card h𝒢sub hx𝒢
    have hxH : ∃ E ∈ H, x ∈ E := by
      have h𝒢nonempty : 𝒢.Nonempty := by
        rw [← Finset.card_pos]
        exact lt_of_le_of_lt (Nat.zero_le s) (by
          simpa [𝒢] using hxstar)
      obtain ⟨E, hE𝒢⟩ := h𝒢nonempty
      exact ⟨E, (Finset.mem_filter.mp hE𝒢).1,
        (Finset.mem_filter.mp hE𝒢).2⟩
    obtain ⟨E, hEH, hxE⟩ := hxH
    have hxA : x ∈ A :=
      additiveSupportFamily_supportsIn
        A (k + 1) m E hEH x hxE
    have hxm : x ≤ m :=
      additiveSupportFamily_supportsBounded
        A (k + 1) m E hEH x hxE
    refine ⟨x, hxA, hxm, ?_⟩
    exact lt_of_lt_of_le (hℋcard ▸ hxstar)
      (Finset.card_le_card hℋsub)

/- A recursive support-count threshold for the rank descent.  At rank zero
the threshold `2` is impossible because there is at most one support.  At a
successor rank, the matching/star fork either produces the requested
matching or leaves at least the previous threshold after removing one
summand. -/
def additiveSupportRankBound : ℕ → ℕ → ℕ
  | 0, _r => 2
  | k + 1, r =>
      (((k + 1) * r) * additiveSupportRankBound k r) + 1

/-- There is at most one order-zero support (the empty support, and only at
target zero). -/
theorem additiveSupportFamily_zero_card_le_one
    (A : Set ℕ) (m : ℕ) :
    (additiveSupportFamily A 0 m).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro E hER D hDR
  have hEempty : E = ∅ := by
    obtain ⟨v, _hvA, _hvsum, rfl⟩ :=
      mem_additiveSupportFamily_iff.mp hER
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨x, hx⟩
    obtain ⟨i, _hi⟩ := mem_tupleSupport_iff.mp hx
    exact Fin.elim0 i
  have hDempty : D = ∅ := by
    obtain ⟨v, _hvA, _hvsum, rfl⟩ :=
      mem_additiveSupportFamily_iff.mp hDR
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨x, hx⟩
    obtain ⟨i, _hi⟩ := mem_tupleSupport_iff.mp hx
    exact Fin.elim0 i
  exact hEempty.trans hDempty.symm

/-- Iterating the one-step fork: once the support family at order `h`
reaches `additiveSupportRankBound h r`, some positive order `j ≤ h` has a
matching with more than `r` supports (at a target obtained by subtracting
the common hits removed during descent).

This is the formal statement that concentration cannot hide through all
orders.  The descent terminates because order zero has only the empty
support. -/
theorem additiveSupportRankBound_forces_matching_below
    {A : Set ℕ} {r : ℕ} :
    ∀ h m,
      additiveSupportRankBound h r ≤
        (additiveSupportFamily A h m).card →
      ∃ j, 0 < j ∧ j ≤ h ∧
        ∃ t, ∃ M : Finset (Finset ℕ),
          M ⊆ additiveSupportFamily A j t ∧
          IsMatching M ∧ r < M.card := by
  intro h
  induction h with
  | zero =>
      intro m hlarge
      have hle := additiveSupportFamily_zero_card_le_one A m
      simp only [additiveSupportRankBound] at hlarge
      omega
  | succ k ih =>
      intro m hlarge
      have hstrict :
          (((k + 1) * r) * additiveSupportRankBound k r) <
            (additiveSupportFamily A (k + 1) m).card := by
        simp only [additiveSupportRankBound] at hlarge
        omega
      obtain ⟨M, hMsub, hMmatching, hMcard⟩ |
          ⟨x, _hxA, _hxm, hxlarge⟩ :=
        large_additiveSupportFamily_matching_or_lowerOrderGrowth
          hstrict
      · exact ⟨k + 1, by omega, le_rfl, m, M,
          hMsub, hMmatching, hMcard⟩
      · obtain ⟨j, hjpos, hjk, t, M, hMsub, hMmatching, hMcard⟩ :=
          ih (m - x) (Nat.le_of_lt hxlarge)
        exact ⟨j, hjpos, le_trans hjk (Nat.le_succ k),
          t, M, hMsub, hMmatching, hMcard⟩

/-- Matching-normalized global alignment theorem.

Choose the two support budgets in
`arbitrarilyLate_blockAlignedRepair_or_supportGrowth` to be the finite-rank
matching thresholds.  Both growth horns then yield an arbitrarily large
matching at a positive rank at most `k+1`.  The only remaining horn is one
explicit same-block safe replacement of an active private hit. -/
theorem IsStronglyMinimalExactBasis.arbitrarilyLate_blockAlignedRepair_or_matching
    {A : Set ℕ} {k : ℕ}
    (hminimal : IsStronglyMinimalExactBasis A (k + 1))
    (hk : 0 < k) :
    ∀ r L,
      ∃ F : ℕ → Finset ℕ, ∃ P : IsFiniteBlockPartition A F,
        ∃ s : BlockSelector F, ∃ q D,
          L ≤ q ∧
          IsInclusionMinimalDestroyer
            (additiveSupportFamily A (k + 1)) D q ∧
          (D : Set ℕ) ⊆ selectedSet s ∧
          ((∃ i, ∃ b ∈ (F i).erase (s i).1,
                (s i).1 ∈ D ∧
                ¬ DestroysAt
                  (additiveSupportFamily A (k + 1))
                  (((D.erase (s i).1 ∪ {b} : Finset ℕ) : Set ℕ)) q) ∨
            ∃ j, 0 < j ∧ j ≤ k + 1 ∧
              ∃ t, ∃ M : Finset (Finset ℕ),
                M ⊆ additiveSupportFamily A j t ∧
                IsMatching M ∧ r < M.card) := by
  intro r L
  obtain ⟨F, P, s, q, D, _hFcard, hLq, hDminimal,
      hDselected, hexact | hsafe | hdifference⟩ :=
    hminimal.arbitrarilyLate_blockAlignedRepair_or_supportGrowth hk
      (additiveSupportRankBound (k + 1) r)
      (additiveSupportRankBound k r) L
  · have hlarge :
        additiveSupportRankBound (k + 1) r ≤
          (additiveSupportFamily A (k + 1) q).card :=
      Nat.le_of_lt hexact
    obtain ⟨j, hjpos, hjle, t, M, hMsub, hMmatching, hMlarge⟩ :=
      additiveSupportRankBound_forces_matching_below
        (k + 1) q hlarge
    exact ⟨F, P, s, q, D, hLq, hDminimal, hDselected,
      Or.inr ⟨j, hjpos, hjle, t, M, hMsub, hMmatching, hMlarge⟩⟩
  · exact ⟨F, P, s, q, D, hLq, hDminimal, hDselected,
      Or.inl hsafe⟩
  · obtain ⟨x, _hxD, _hxq, hxlarge⟩ := hdifference
    have hlarge :
        additiveSupportRankBound k r ≤
          (additiveSupportFamily A k (q - x)).card :=
      Nat.le_of_lt hxlarge
    obtain ⟨j, hjpos, hjle, t, M, hMsub, hMmatching, hMlarge⟩ :=
      additiveSupportRankBound_forces_matching_below
        k (q - x) hlarge
    exact ⟨F, P, s, q, D, hLq, hDminimal, hDselected,
      Or.inr ⟨j, hjpos, hjle.trans (Nat.le_succ k),
        t, M, hMsub, hMmatching,
        hMlarge⟩⟩

/-- Matching-normalized protected-certificate dichotomy.

The safe-repair horn has disappeared.  For every proposed certificate bound
`C` and matching size `r`, strong minimality yields either a
cardinal-minimal target-localized certificate with more than `C` targets, or
a genuine matching with more than `r` supports at some positive rank no
larger than `k+1`. -/
theorem IsStronglyMinimalExactBasis.arbitrarilyLate_largeMinimalCertificate_or_matching
    {A : Set ℕ} {k : ℕ}
    (hminimal : IsStronglyMinimalExactBasis A (k + 1))
    (hk : 0 < k) :
    ∀ C r L,
      ∃ F : ℕ → Finset ℕ, ∃ P : IsFiniteBlockPartition A F,
        ∃ Q : Finset ℕ,
          (∀ u ∈ Q, L ≤ u) ∧
          (∀ s : BlockSelector F, ∃ u ∈ Q,
            DestroysAt
              (additiveSupportFamily A (k + 1))
              (selectedSet s) u) ∧
          (∀ u ∈ Q, ∃ s : BlockSelector F,
            DestroysAt
                (additiveSupportFamily A (k + 1))
                (selectedSet s) u ∧
              ∀ v ∈ Q, v ≠ u →
                ¬ DestroysAt
                  (additiveSupportFamily A (k + 1))
                  (selectedSet s) v) ∧
          (C < Q.card ∨
            ∃ j, 0 < j ∧ j ≤ k + 1 ∧
              ∃ t, ∃ M : Finset (Finset ℕ),
                M ⊆ additiveSupportFamily A j t ∧
                IsMatching M ∧ r < M.card) := by
  intro C r L
  obtain ⟨F, P, Q, hlate, hcert, hlocalized, houtcome⟩ :=
    hminimal.arbitrarilyLate_largeMinimalCertificate_or_supportGrowth hk
      C (additiveSupportRankBound (k + 1) r)
        (additiveSupportRankBound k r) L
  rcases houtcome with hQlarge | ⟨q, hqQ, hgrowth⟩
  · exact ⟨F, P, Q, hlate, hcert, hlocalized,
      Or.inl hQlarge⟩
  rcases hgrowth with hexact | hdifference
  · have hlarge :
        additiveSupportRankBound (k + 1) r ≤
          (additiveSupportFamily A (k + 1) q).card :=
      Nat.le_of_lt hexact
    obtain ⟨j, hjpos, hjle, t, M, hMsub, hMmatching, hMlarge⟩ :=
      additiveSupportRankBound_forces_matching_below
        (k + 1) q hlarge
    exact ⟨F, P, Q, hlate, hcert, hlocalized,
      Or.inr ⟨j, hjpos, hjle, t, M, hMsub, hMmatching, hMlarge⟩⟩
  · obtain ⟨x, _hxq, hxlarge⟩ := hdifference
    have hlarge :
        additiveSupportRankBound k r ≤
          (additiveSupportFamily A k (q - x)).card :=
      Nat.le_of_lt hxlarge
    obtain ⟨j, hjpos, hjle, t, M, hMsub, hMmatching, hMlarge⟩ :=
      additiveSupportRankBound_forces_matching_below
        k (q - x) hlarge
    exact ⟨F, P, Q, hlate, hcert, hlocalized,
      Or.inr ⟨j, hjpos, hjle.trans (Nat.le_succ k),
        t, M, hMsub, hMmatching, hMlarge⟩⟩

/-- Bounded recurrent successor transversals therefore force arbitrarily
large matchings at some positive predecessor rank.  The rank and target may
move, but the matching size is unbounded.

The remaining lifting step is to retain the removed common summands as a
bounded root and reinsert them, producing a large matching outside that root
at the original successor target. -/
theorem recurrentLowerRankMatchings_of_boundedFullTranslateDestroyers
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hfull : HasBoundedFullTranslateDestroyersByAnchor A (k + 1) Q) :
    ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A → ∀ r L,
      ∃ n T q a x j t M,
        L ≤ a ∧ q ∈ Q ∧ a ∈ A ∧ n = q + a ∧
        (∀ y ∈ T, y ∈ A) ∧ Disjoint T F ∧ T.Nonempty ∧
        DestroysAt
          (additiveSupportFamily A (k + 2)) (T : Set ℕ) n ∧
        x ∈ T ∧ x ≤ n ∧
        0 < j ∧ j ≤ k + 1 ∧
        M ⊆ additiveSupportFamily A j t ∧
        IsMatching M ∧ r < M.card := by
  intro F hFA r L
  obtain ⟨n, T, q, a, x, haLower, hqQ, haA, hnqa,
      hTA, hTF, hTnonempty, hdestroy, hxT, hxn, hxlarge⟩ :=
    recurrentLargeSupportStars_of_boundedFullTranslateDestroyers
      hbasis hfull F hFA
        (additiveSupportRankBound (k + 1) r) L
  obtain ⟨j, hjpos, hjle, t, M, hMsub, hMmatching, hMcard⟩ :=
    additiveSupportRankBound_forces_matching_below
      (A := A) (r := r) (h := k + 1) (m := n - x)
      (Nat.le_of_lt hxlarge)
  exact ⟨n, T, q, a, x, j, t, M,
    haLower, hqQ, haA, hnqa, hTA, hTF, hTnonempty,
    hdestroy, hxT, hxn, hjpos, hjle, hMsub, hMmatching, hMcard⟩

/-- The rank conclusion directly from the bounded moving-transversal branch
on a finite union of translates. -/
theorem recurrentLowerRankMatchings_of_boundedMovingOnFiniteTranslates
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hQ : Q.Nonempty)
    (hmoving :
      HasBoundedMovingOutsideTransversalsOnFiniteTranslates
        (additiveSupportFamily A (k + 2)) A Q) :
    ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A → ∀ r L,
      ∃ n T q a x j t M,
        L ≤ a ∧ q ∈ Q ∧ a ∈ A ∧ n = q + a ∧
        (∀ y ∈ T, y ∈ A) ∧ Disjoint T F ∧ T.Nonempty ∧
        DestroysAt
          (additiveSupportFamily A (k + 2)) (T : Set ℕ) n ∧
        x ∈ T ∧ x ≤ n ∧
        0 < j ∧ j ≤ k + 1 ∧
        M ⊆ additiveSupportFamily A j t ∧
        IsMatching M ∧ r < M.card :=
  recurrentLowerRankMatchings_of_boundedFullTranslateDestroyers
    hbasis
    (boundedFullTranslateDestroyersByAnchor_of_boundedMovingOnFiniteTranslates
      hbasis hQ hmoving)

/-- Exhaustive relative attack dichotomy at every positive predecessor
order.  On `Q + A`, either successor representations already have genuine
matching growth outside one fixed finite core, or the bounded-transversal
branch forces arbitrarily large matchings after descending to some positive
rank at most the original order.

This removes the former terminal "bounded internal anchors" description:
that branch now has an unbounded matching output.  What remains is to retain
the removed common summands as a bounded root and synchronize those roots
with the strong-deletion certificate. -/
theorem finiteCoreTranslateGrowth_or_recurrentLowerRankMatchings
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hQ : Q.Nonempty) :
    (∃ F : Finset ℕ, (F : Set ℕ) ⊆ A ∧
      OutsideMatchingTendsToInfinityAlong
        (additiveSupportFamily A (k + 2)) F
        (finiteTargetTranslates A Q)) ∨
      (∀ F : Finset ℕ, (F : Set ℕ) ⊆ A → ∀ r L,
        ∃ n T q a x j t M,
          L ≤ a ∧ q ∈ Q ∧ a ∈ A ∧ n = q + a ∧
          (∀ y ∈ T, y ∈ A) ∧ Disjoint T F ∧ T.Nonempty ∧
          DestroysAt
            (additiveSupportFamily A (k + 2)) (T : Set ℕ) n ∧
          x ∈ T ∧ x ≤ n ∧
          0 < j ∧ j ≤ k + 1 ∧
          M ⊆ additiveSupportFamily A j t ∧
          IsMatching M ∧ r < M.card) := by
  obtain hgrowth | hmoving :=
    finiteCore_translateMatchingGrowth_or_recurrentBoundedMoving
      (A := A) (Q := Q)
      (R := additiveSupportFamily A (k + 2))
      (additiveSupportFamily_supportsIn A (k + 2))
      (additiveSupportFamily_cardAtMost A (k + 2))
  · exact Or.inl hgrowth
  · exact Or.inr <|
      recurrentLowerRankMatchings_of_boundedMovingOnFiniteTranslates
        hbasis hQ hmoving

/-! ## Retaining the descent root -/

/-- Threshold for a cardinal-preserving rooted matching descent.  In the
star branch the lower-rank induction asks for one extra petal: after the new
root point is inserted, at most one old petal can collapse to that point. -/
def additiveRootedMatchingBound : ℕ → ℕ → ℕ
  | 0, _r => 2
  | k + 1, r =>
      (((k + 1) * r) * additiveRootedMatchingBound k (r + 1)) + 1

/-- A sufficiently large subfamily of order-`h` additive supports contains
a large delta system with a root of cardinality strictly below `h`.

The proof follows the actual additive rank descent, not an abstract
sunflower theorem.  In a large star at `x`, remove one occurrence of `x`,
recurse one order lower, and then reinsert `x` into the root.  At most one
lower petal equals `{x}`, so asking for one extra lower petal preserves the
requested cardinality after reinsertion. -/
theorem additiveSupportSubfamily_has_large_rootedMatching
    {A : Set ℕ} :
    ∀ h r m (𝒢 : Finset (Finset ℕ)),
      𝒢 ⊆ additiveSupportFamily A h m →
      additiveRootedMatchingBound h r ≤ 𝒢.card →
      ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
        R.card < h ∧
        M ⊆ 𝒢 ∧ r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ D ∈ M, E ≠ D →
          Disjoint (E \ R) (D \ R) := by
  intro h
  induction h with
  | zero =>
      intro r m 𝒢 h𝒢sub hlarge
      have hcard :
          𝒢.card ≤ (additiveSupportFamily A 0 m).card :=
        Finset.card_le_card h𝒢sub
      have hzero := additiveSupportFamily_zero_card_le_one A m
      simp only [additiveRootedMatchingBound] at hlarge
      omega
  | succ k ih =>
      intro r m 𝒢 h𝒢sub hlarge
      have hedges : ∀ E ∈ 𝒢, E.Nonempty := by
        intro E hE
        exact additiveSupportFamily_supportsNonempty
          A (Nat.zero_lt_succ k) m E (h𝒢sub hE)
      have hsize : ∀ E ∈ 𝒢, E.card ≤ k + 1 := by
        intro E hE
        exact additiveSupportFamily_cardAtMost
          A (k + 1) m E (h𝒢sub hE)
      have hstrict :
          (((k + 1) * r) *
              additiveRootedMatchingBound k (r + 1)) < 𝒢.card := by
        simp only [additiveRootedMatchingBound] at hlarge
        omega
      obtain ⟨M, _hMsub, _hMmatching, hMcard⟩ |
          ⟨x, hxstar⟩ :=
        large_boundedHypergraph_matching_or_star
          hedges hsize hstrict
      · refine ⟨∅, M, by simp, _hMsub, hMcard, by simp, ?_, ?_⟩
        · intro E hEM
          simpa using hedges E (_hMsub hEM)
        · intro E hEM D hDM hED
          simpa using _hMmatching hEM hDM hED
      · let 𝒢x := 𝒢.filter fun E => x ∈ E
        have h𝒢xsub :
            𝒢x ⊆ additiveSupportFamily A (k + 1) m := by
          intro E hE
          exact h𝒢sub (Finset.mem_filter.mp hE).1
        have hx𝒢x : ∀ E ∈ 𝒢x, x ∈ E := by
          intro E hE
          exact (Finset.mem_filter.mp hE).2
        have hlower : ∀ E : {E // E ∈ 𝒢x},
            ∃ H ∈ additiveSupportFamily A k (m - x),
              E.1 = insert x H := by
          intro E
          exact additiveSupport_remove_hit_succ
            (h𝒢xsub E.2) (hx𝒢x E.1 E.2)
        let lower : {E // E ∈ 𝒢x} → Finset ℕ := fun E =>
          (hlower E).choose
        have hlowerR : ∀ E, lower E ∈
            additiveSupportFamily A k (m - x) := by
          intro E
          exact (hlower E).choose_spec.1
        have hreconstruct : ∀ E, E.1 = insert x (lower E) := by
          intro E
          exact (hlower E).choose_spec.2
        have hlowerInjective : Function.Injective lower := by
          intro E D hED
          apply Subtype.ext
          rw [hreconstruct E, hreconstruct D, hED]
        let ℋ := 𝒢x.attach.image lower
        have hℋsub :
            ℋ ⊆ additiveSupportFamily A k (m - x) := by
          intro H hH
          obtain ⟨E, _hEattach, rfl⟩ := Finset.mem_image.mp hH
          exact hlowerR E
        have hℋcard : ℋ.card = 𝒢x.card := by
          dsimp only [ℋ]
          rw [Finset.card_image_iff.mpr hlowerInjective.injOn,
            Finset.card_attach]
        have hℋlarge :
            additiveRootedMatchingBound k (r + 1) ≤ ℋ.card := by
          rw [hℋcard]
          exact Nat.le_of_lt (by simpa [𝒢x] using hxstar)
        obtain ⟨R, L, hRcard, hLsub, hLcard, hLroot,
            hLnonempty, hLmatching⟩ :=
          ih (r + 1) (m - x) ℋ hℋsub hℋlarge
        let bad := L.filter fun H => H \ R = {x}
        let good := L.filter fun H => H \ R ≠ {x}
        have hbadcard : bad.card ≤ 1 := by
          apply Finset.card_le_one.mpr
          intro H hHbad D hDbad
          have hHL : H ∈ L := (Finset.mem_filter.mp hHbad).1
          have hDL : D ∈ L := (Finset.mem_filter.mp hDbad).1
          have hHeq : H \ R = {x} :=
            (Finset.mem_filter.mp hHbad).2
          have hDeq : D \ R = {x} :=
            (Finset.mem_filter.mp hDbad).2
          by_contra hHD
          have hdisj := hLmatching H hHL D hDL hHD
          rw [hHeq, hDeq] at hdisj
          exact (Finset.not_disjoint_iff.mpr
            ⟨x, by simp, by simp⟩) hdisj
        have hsplit : bad.card + good.card = L.card := by
          simpa [bad, good] using
            (Finset.card_filter_add_card_filter_not
              (s := L) (p := fun H => H \ R = {x}))
        have hgoodcard : r < good.card := by omega
        have hgoodL : good ⊆ L := Finset.filter_subset _ _
        have hgoodPetal :
            ∀ H ∈ good, (H \ insert x R).Nonempty := by
          intro H hHgood
          have hHL : H ∈ L := hgoodL hHgood
          have hHR : (H \ R).Nonempty := hLnonempty H hHL
          have hnotSingleton : H \ R ≠ {x} :=
            (Finset.mem_filter.mp hHgood).2
          by_contra hnot
          have hempty : H \ insert x R = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp hnot
          have hall : ∀ y ∈ H \ R, y = x := by
            intro y hy
            by_contra hyx
            have hyroot : y ∉ insert x R := by
              intro hyroot
              rcases Finset.mem_insert.mp hyroot with hyx' | hyR
              · exact hyx hyx'
              · exact (Finset.mem_sdiff.mp hy).2 hyR
            have hy' : y ∈ H \ insert x R :=
              Finset.mem_sdiff.mpr
                ⟨(Finset.mem_sdiff.mp hy).1, hyroot⟩
            rw [hempty] at hy'
            simp at hy'
          obtain ⟨y, hy⟩ := hHR
          have hyx : y = x := hall y hy
          have hxHR : x ∈ H \ R := hyx ▸ hy
          apply hnotSingleton
          ext z
          simp only [Finset.mem_singleton]
          constructor
          · exact fun hz => hall z hz
          · rintro rfl
            exact hxHR
        have hsource : ∀ H : {H // H ∈ good},
            ∃ E : {E // E ∈ 𝒢x}, lower E = H.1 := by
          intro H
          have hHℋ : H.1 ∈ ℋ :=
            hLsub (hgoodL H.2)
          obtain ⟨E, _hEattach, hEH⟩ :=
            Finset.mem_image.mp hHℋ
          exact ⟨E, hEH⟩
        choose source hsourceEq using hsource
        let upper : {H // H ∈ good} → Finset ℕ := fun H =>
          (source H).1
        have hupperReconstruct : ∀ H,
            upper H = insert x H.1 := by
          intro H
          calc
            upper H = insert x (lower (source H)) :=
              hreconstruct (source H)
            _ = insert x H.1 := by rw [hsourceEq H]
        have hupperInjective : Function.Injective upper := by
          intro H D hHD
          apply Subtype.ext
          have hsource : source H = source D := Subtype.ext hHD
          calc
            H.1 = lower (source H) := (hsourceEq H).symm
            _ = lower (source D) := congrArg lower hsource
            _ = D.1 := hsourceEq D
        let M := good.attach.image upper
        have hMcard : M.card = good.card := by
          dsimp only [M]
          rw [Finset.card_image_iff.mpr hupperInjective.injOn,
            Finset.card_attach]
        have hMsub : M ⊆ 𝒢 := by
          intro E hEM
          obtain ⟨H, _hHattach, rfl⟩ := Finset.mem_image.mp hEM
          exact (Finset.mem_filter.mp (source H).2).1
        have hMroot : ∀ E ∈ M, insert x R ⊆ E := by
          intro E hEM
          obtain ⟨H, _hHattach, rfl⟩ := Finset.mem_image.mp hEM
          rw [hupperReconstruct H]
          intro y hyroot
          rcases Finset.mem_insert.mp hyroot with rfl | hyR
          · exact Finset.mem_insert_self _ H.1
          · exact Finset.mem_insert_of_mem
              (hLroot H.1 (hgoodL H.2) hyR)
        have hpetalSubset : ∀ H : {H // H ∈ good},
            upper H \ insert x R ⊆ H.1 \ R := by
          intro H y hy
          have hy' := Finset.mem_sdiff.mp hy
          rw [hupperReconstruct H] at hy'
          have hyH : y ∈ H.1 := by
            rcases Finset.mem_insert.mp hy'.1 with hyx | hyH
            · subst y
              exact (hy'.2 (Finset.mem_insert_self x R)).elim
            · exact hyH
          exact Finset.mem_sdiff.mpr
            ⟨hyH, fun hyR => hy'.2 (Finset.mem_insert_of_mem hyR)⟩
        have hMnonempty :
            ∀ E ∈ M, (E \ insert x R).Nonempty := by
          intro E hEM
          obtain ⟨H, _hHattach, rfl⟩ := Finset.mem_image.mp hEM
          rw [hupperReconstruct H]
          simpa using hgoodPetal H.1 H.2
        have hMmatching :
            ∀ E ∈ M, ∀ D ∈ M, E ≠ D →
              Disjoint (E \ insert x R) (D \ insert x R) := by
          intro E hEM D hDM hED
          obtain ⟨H, _hHattach, hHE⟩ := Finset.mem_image.mp hEM
          obtain ⟨J, _hJattach, hJD⟩ := Finset.mem_image.mp hDM
          have hHJ : H.1 ≠ J.1 := by
            intro hHJ
            apply hED
            rw [← hHE, ← hJD]
            exact congrArg upper (Subtype.ext hHJ)
          have hdisj :=
            hLmatching H.1 (hgoodL H.2)
              J.1 (hgoodL J.2) hHJ
          rw [← hHE, ← hJD]
          exact hdisj.mono (hpetalSubset H) (hpetalSubset J)
        have hrootCard : (insert x R).card < k + 1 := by
          have hle : (insert x R).card ≤ R.card + 1 :=
            Finset.card_insert_le x R
          omega
        refine ⟨insert x R, M, hrootCard, hMsub, ?_, hMroot,
          hMnonempty, hMmatching⟩
        rw [hMcard]
        exact hgoodcard

/-- Rooted-matching normalization of the old-block dependency trichotomy.

Choose the exact-support bound to be the finite rooted-matching threshold.
If an old block is larger than the capacity of that support family plus
`m` protected supports, then failure of both matching growth and a safe
second choice forces more than `m` distinct strictly larger target
dependencies.  This is the quantitative increasing-branch alternative
needed for an eventual finite-certificate termination argument. -/
theorem oldBlock_rootedMatching_or_safeSecondChoice_or_manyLargerDependencies
    {A : Set ℕ} {k q r m : ℕ} {Q V : Finset ℕ}
    (c :
      FiniteSupportChoice
        (additiveSupportFamily A (k + 1)) Q)
    (hQlarger : ∀ u ∈ Q, q < u)
    (hVlarge :
      (k + 1) *
          (additiveRootedMatchingBound (k + 1) r + m) <
        V.card) :
    (∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
        R.card < k + 1 ∧
        M ⊆ additiveSupportFamily A (k + 1) q ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ D ∈ M, E ≠ D →
          Disjoint (E \ R) (D \ R)) ∨
      (∃ y ∈ V,
        y ∉ finiteSupportChoiceUnion c ∧
        ∀ G ∈ additiveSupportFamily A (k + 1) q, y ∉ G) ∨
      ∃ P : Finset ℕ, ∃ hPQ : P ⊆ Q,
        m < P.card ∧
        P.card ≤ V.card ∧
        (∀ u ∈ P, q < u) ∧
        V ⊆
          (additiveSupportFamily A (k + 1) q).biUnion id ∪
            finiteSupportChoiceUnion
              (restrictFiniteSupportChoice hPQ c) := by
  classical
  let threshold := additiveRootedMatchingBound (k + 1) r
  obtain hgrowth | hsafe | ⟨P, hPQ, hPcard, hPlarger,
      hcover, hcapacity⟩ :=
    oldBlock_exactGrowth_or_safeSecondChoice_or_localLargerDependency
      (r := threshold) c hQlarger
  · left
    apply additiveSupportSubfamily_has_large_rootedMatching
      (k + 1) r q (additiveSupportFamily A (k + 1) q)
        Finset.Subset.rfl
    exact Nat.le_of_lt hgrowth
  · exact Or.inr (Or.inl hsafe)
  · right
    right
    have hmP : m < P.card := by
      by_contra hnot
      have hPm : P.card ≤ m := Nat.le_of_not_gt hnot
      have hsum :
          threshold + P.card ≤ threshold + m :=
        Nat.add_le_add_left hPm threshold
      have hmul :
          (k + 1) * (threshold + P.card) ≤
            (k + 1) * (threshold + m) :=
        Nat.mul_le_mul_left (k + 1) hsum
      exact (not_lt_of_ge (hcapacity.trans hmul)) hVlarge
    exact ⟨P, hPQ, hmP, hPcard, hPlarger, hcover⟩

/-- Certificate-state instantiation of the increasing old-block branch.

The protected support choice is now obtained directly from the targets
strictly above `q` which survive the current selector.  On a sufficiently
large active block, either exact rooted matching growth has already occurred,
or the theorem returns a verified safe aligned swap, or more than `m`
strictly larger certificate targets are genuinely needed to cover that
block.  No bound on the total certificate cardinality occurs. -/
theorem blockAligned_rootedMatching_or_safeSwap_or_manyLargerDependencies
    {A : Set ℕ} {k q r m : ℕ} {Q : Finset ℕ}
    {F : ℕ → Finset ℕ} (s : BlockSelector F)
    {D : Finset ℕ} {i : ℕ}
    (hlarger : ∀ u ∈ Q, q < u →
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet s) u)
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hactive : (s i).1 ∈ D)
    (hblockLarge :
      (k + 1) *
          (additiveRootedMatchingBound (k + 1) r + m) <
        ((F i).erase (s i).1).card) :
    (∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
        R.card < k + 1 ∧
        M ⊆ additiveSupportFamily A (k + 1) q ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
          Disjoint (E \ R) (G \ R)) ∨
      ∃ c :
          FiniteSupportChoice
            (additiveSupportFamily A (k + 1))
            (Q.filter fun u => q < u),
        Disjoint (finiteSupportChoiceUnion c : Set ℕ) (selectedSet s) ∧
        ((∃ b ∈ (F i).erase (s i).1,
            b ∉ finiteSupportChoiceUnion c ∧
            ¬ DestroysAt
              (additiveSupportFamily A (k + 1))
              (((D.erase (s i).1 ∪ {b} : Finset ℕ) : Set ℕ)) q) ∨
          ∃ P : Finset ℕ,
            ∃ hPQ : P ⊆ (Q.filter fun u => q < u),
              m < P.card ∧
              P.card ≤ ((F i).erase (s i).1).card ∧
              (∀ u ∈ P, q < u) ∧
              (F i).erase (s i).1 ⊆
                (additiveSupportFamily A (k + 1) q).biUnion id ∪
                  finiteSupportChoiceUnion
                    (restrictFiniteSupportChoice hPQ c)) := by
  classical
  obtain ⟨c, hcDisjoint⟩ :=
    exists_survivingLargerSupportChoice s hlarger
  have hfilterLarger :
      ∀ u ∈ Q.filter (fun u => q < u), q < u := by
    intro u hu
    exact (Finset.mem_filter.mp hu).2
  obtain hgrowth | ⟨b, hbBlock, hbProtected, hbAvoid⟩ |
      hdependency :=
    oldBlock_rootedMatching_or_safeSecondChoice_or_manyLargerDependencies
      (V := (F i).erase (s i).1) c hfilterLarger hblockLarge
  · exact Or.inl hgrowth
  · right
    refine ⟨c, hcDisjoint, Or.inl
      ⟨b, hbBlock, hbProtected, ?_⟩⟩
    exact hminimal.swap_hit_for_avoidedPoint_repairs hactive hbAvoid
  · exact Or.inr ⟨c, hcDisjoint, Or.inr hdependency⟩

/-- The top certificate target has no dependency branch.

At a maximum member `q` of the certificate, the set of strictly larger
protected targets is empty.  Taking `m = 0` in the local old-block theorem
makes the increasing-dependency horn impossible.  Consequently a single
large active block gives either exact rooted matching growth at `q` or a
verified aligned repair.  Ordinary rank-sized room in the remaining blocks
then completes that repair and forces strict certificate descent.

Unlike the earlier protected-union descent theorem, the large active-block
bound here is completely independent of `Q.card`. -/
theorem blockAligned_at_certificateMax_rootedMatching_or_strictDescent
    {A : Set ℕ} {k q r : ℕ} {Q : Finset ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D : Finset ℕ} {i : ℕ}
    (hqMax : ∀ u ∈ Q, u ≤ q)
    (hcert : ∀ t : BlockSelector F, ∃ u ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u)
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hactive : (s i).1 ∈ D)
    (hactiveLarge :
      (k + 1) * additiveRootedMatchingBound (k + 1) r <
        ((F i).erase (s i).1).card)
    (hblocks : ∀ j,
      (s j).1 ∈
          supportVertices (additiveSupportFamily A (k + 1)) q →
        k + 1 < (F j).card) :
    (∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
        R.card < k + 1 ∧
        M ⊆ additiveSupportFamily A (k + 1) q ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
          Disjoint (E \ R) (G \ R)) ∨
      ∃ t : BlockSelector F, ∃ u ∈ Q, u < q ∧
        DestroysAt
          (additiveSupportFamily A (k + 1))
          (selectedSet t) u := by
  classical
  let c :
      FiniteSupportChoice
        (additiveSupportFamily A (k + 1)) ∅ := fun u =>
    (Finset.notMem_empty u.1 u.2).elim
  have hemptyLarger : ∀ u ∈ (∅ : Finset ℕ), q < u := by simp
  have hlarge :
      (k + 1) *
          (additiveRootedMatchingBound (k + 1) r + 0) <
        ((F i).erase (s i).1).card := by
    simpa using hactiveLarge
  obtain hgrowth | ⟨b, hbBlock, _hbProtected, hbAvoid⟩ |
      ⟨S, hSempty, hSnonempty, _hScard, _hSlarger, _hcover⟩ :=
    oldBlock_rootedMatching_or_safeSecondChoice_or_manyLargerDependencies
      (V := (F i).erase (s i).1) c hemptyLarger hlarge
  · exact Or.inl hgrowth
  · right
    have hrepair :
        ¬ DestroysAt
          (additiveSupportFamily A (k + 1))
          (((D.erase (s i).1 ∪ {b} : Finset ℕ) : Set ℕ)) q :=
      hminimal.swap_hit_for_avoidedPoint_repairs hactive hbAvoid
    obtain ⟨E, hER, hEswap⟩ :=
      not_destroysAt_iff.mp hrepair
    have hhitCapacity :
        ∀ j, (s j).1 ∈ E →
          (∅ : Finset ℕ).card + (k + 1) < (F j).card := by
      intro j hsjE
      simpa using hblocks j
        (Finset.mem_biUnion.mpr ⟨E, hER, hsjE⟩)
    obtain ⟨t, _htEmpty, htq⟩ :=
      blockAlignedRepairWitness_extends_protected_of_hitBlockCapacity
        P s hbBlock (by simp) (by simp) hER hEswap hhitCapacity
    obtain ⟨u, huQ, huDestroy⟩ := hcert t
    have hune : u ≠ q := by
      intro huq
      subst u
      exact htq huDestroy
    exact ⟨t, u, huQ,
      lt_of_le_of_ne (hqMax u huQ) hune, huDestroy⟩
  · have hSEmpty : S = ∅ := Finset.subset_empty.mp hSempty
    rw [hSEmpty] at hSnonempty
    simp at hSnonempty

/-- Descending inside a finite certificate strictly increases the number of
certificate targets above the current target.

The old upper set is properly contained in the new one: every target above
`q` is above `u`, while `q` itself is newly admitted. -/
theorem certificateUpperRank_strictly_grows_under_descent
    {Q : Finset ℕ} {u q : ℕ}
    (hqQ : q ∈ Q) (huq : u < q) :
    (Q.filter fun v => q < v).card <
      (Q.filter fun v => u < v).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro v hv
    rw [Finset.mem_filter] at hv ⊢
    exact ⟨hv.1, lt_trans huq hv.2⟩
  · intro heq
    have hqUpperU : q ∈ Q.filter fun v => u < v :=
      Finset.mem_filter.mpr ⟨hqQ, huq⟩
    rw [← heq] at hqUpperU
    exact (Nat.lt_irrefl q) (Finset.mem_filter.mp hqUpperU).2

/-- Strict descent with capacity measured only by the upper certificate
rank.

Let `Upper = {u ∈ Q | q < u}`.  Store one surviving support for these
targets.  Taking `m = Upper.card` makes the local dependency horn
impossible, since it would produce a subset of `Upper` with cardinality
strictly larger than `Upper`.  A safe second choice avoids the stored union;
rank-times-`Upper.card` room completes the selector and preserves every
larger target.

This replaces every occurrence of the full certificate bound by the actual
descent depth above `q`.  At the top target this depth is zero, and it grows
by at least one after each strict descent. -/
theorem blockAligned_upperRankCapacity_rootedMatching_or_strictDescent
    {A : Set ℕ} {k q r : ℕ} {Q : Finset ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D : Finset ℕ} {i : ℕ}
    (hcert : ∀ t : BlockSelector F, ∃ u ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u)
    (hlarger : ∀ u ∈ Q, q < u →
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet s) u)
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hactive : (s i).1 ∈ D)
    (hactiveLarge :
      (k + 1) *
          (additiveRootedMatchingBound (k + 1) r +
            (Q.filter fun u => q < u).card) <
        ((F i).erase (s i).1).card)
    (hblocks : ∀ j,
      (s j).1 ∈
          supportVertices (additiveSupportFamily A (k + 1)) q →
        (k + 1) * (Q.filter fun u => q < u).card + (k + 1) <
          (F j).card) :
    (∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
        R.card < k + 1 ∧
        M ⊆ additiveSupportFamily A (k + 1) q ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
          Disjoint (E \ R) (G \ R)) ∨
      ∃ t : BlockSelector F, ∃ u ∈ Q, u < q ∧
        DestroysAt
          (additiveSupportFamily A (k + 1))
          (selectedSet t) u := by
  classical
  let Upper : Finset ℕ := Q.filter fun u => q < u
  obtain ⟨c, hcDisjoint⟩ :=
    exists_survivingLargerSupportChoice s hlarger
  let U : Finset ℕ := finiteSupportChoiceUnion c
  have hUcard :
      U.card ≤ (k + 1) * Upper.card := by
    exact finiteSupportChoiceUnion_card_le
      (additiveSupportFamily_cardAtMost A (k + 1)) c
  have hUpperLarger : ∀ u ∈ Upper, q < u := by
    intro u huUpper
    exact (Finset.mem_filter.mp huUpper).2
  obtain hgrowth | ⟨b, hbBlock, hbU, hbAvoid⟩ |
      ⟨S, hSUpper, hSlarge, _hSblock, _hSlarger, _hcover⟩ :=
    oldBlock_rootedMatching_or_safeSecondChoice_or_manyLargerDependencies
      (V := (F i).erase (s i).1) (m := Upper.card)
        c hUpperLarger (by simpa only [Upper] using hactiveLarge)
  · exact Or.inl hgrowth
  · right
    have hrepair :
        ¬ DestroysAt
          (additiveSupportFamily A (k + 1))
          (((D.erase (s i).1 ∪ {b} : Finset ℕ) : Set ℕ)) q :=
      hminimal.swap_hit_for_avoidedPoint_repairs hactive hbAvoid
    obtain ⟨E, hER, hEswap⟩ :=
      not_destroysAt_iff.mp hrepair
    have hhitCapacity :
        ∀ j, (s j).1 ∈ E →
          U.card + (k + 1) < (F j).card := by
      intro j hsjE
      exact lt_of_le_of_lt
        (Nat.add_le_add_right hUcard (k + 1))
        (by
          simpa only [Upper] using
            hblocks j
              (Finset.mem_biUnion.mpr ⟨E, hER, hsjE⟩))
    obtain ⟨t, htU, htq⟩ :=
      blockAlignedRepairWitness_extends_protected_of_hitBlockCapacity
        P s hbBlock hbU (by simpa only [U] using hcDisjoint)
          hER hEswap hhitCapacity
    have hprotected :
        ∀ u ∈ Q, q < u →
          ∃ E ∈ additiveSupportFamily A (k + 1) u,
            (E : Set ℕ) ⊆ (U : Set ℕ) := by
      intro u huQ hqu
      let u' : {n // n ∈ Upper} :=
        ⟨u, Finset.mem_filter.mpr ⟨huQ, hqu⟩⟩
      refine ⟨(c u').1, (c u').2, ?_⟩
      intro x hx
      exact Finset.mem_coe.mpr
        (finiteSupportChoice_subset_union c u'
          (Finset.mem_coe.mp hx))
    obtain ⟨u, huQ, huq, huDestroy⟩ :=
      protectedSelectorRepair_forces_strictCertificateDescent
        hcert hprotected htU htq
    exact ⟨t, u, huQ, huq, huDestroy⟩
  · have hScard : S.card ≤ Upper.card :=
      Finset.card_le_card hSUpper
    exact (not_lt_of_ge hScard hSlarge).elim

/-- Rank-explicit form of upper-rank descent.

Every non-growth outcome consumes at least one unit of the finite
certificate's upper-rank budget.  Thus this branch cannot recur without
eventually reaching a stage at which the support-local capacity hypothesis
fails or rooted matching growth occurs. -/
theorem blockAligned_upperRankCapacity_rootedMatching_or_rankGrowthDescent
    {A : Set ℕ} {k q r : ℕ} {Q : Finset ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D : Finset ℕ} {i : ℕ}
    (hqQ : q ∈ Q)
    (hcert : ∀ t : BlockSelector F, ∃ u ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u)
    (hlarger : ∀ u ∈ Q, q < u →
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet s) u)
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hactive : (s i).1 ∈ D)
    (hactiveLarge :
      (k + 1) *
          (additiveRootedMatchingBound (k + 1) r +
            (Q.filter fun u => q < u).card) <
        ((F i).erase (s i).1).card)
    (hblocks : ∀ j,
      (s j).1 ∈
          supportVertices (additiveSupportFamily A (k + 1)) q →
        (k + 1) * (Q.filter fun u => q < u).card + (k + 1) <
          (F j).card) :
    (∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
        R.card < k + 1 ∧
        M ⊆ additiveSupportFamily A (k + 1) q ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
          Disjoint (E \ R) (G \ R)) ∨
      ∃ t : BlockSelector F, ∃ u ∈ Q, u < q ∧
        (Q.filter fun v => q < v).card <
          (Q.filter fun v => u < v).card ∧
        DestroysAt
          (additiveSupportFamily A (k + 1))
          (selectedSet t) u := by
  obtain hgrowth | ⟨t, u, huQ, huq, huDestroy⟩ :=
    blockAligned_upperRankCapacity_rootedMatching_or_strictDescent
      P s hcert hlarger hminimal hactive hactiveLarge hblocks
  · exact Or.inl hgrowth
  · exact Or.inr ⟨t, u, huQ, huq,
      certificateUpperRank_strictly_grows_under_descent hqQ huq,
      huDestroy⟩

/-- A retained safe swap under upper-target protection has only two
outcomes: strict descent, or a private collision in an exceptional old
block.

This is the collision-preserving version of upper-rank descent.  In the
collision horn the actual support is retained and meets the minimal
destroyer exactly at the active point.  Hence failures arising from
different active points can subsequently be counted injectively. -/
theorem blockAlignedSafeSwap_upperCertificate_forces_descent_or_oldCollision
    {A : Set ℕ} {k q : ℕ} {Q U J : Finset ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D : Finset ℕ} {i b : ℕ}
    (hcert : ∀ t : BlockSelector F, ∃ u ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u)
    (hprotected : ∀ u ∈ Q, q < u →
      ∃ E ∈ additiveSupportFamily A (k + 1) u,
        (E : Set ℕ) ⊆ (U : Set ℕ))
    (hDdestroy :
      DestroysAt
        (additiveSupportFamily A (k + 1)) (D : Set ℕ) q)
    (hactive : (s i).1 ∈ D)
    (hbBlock : b ∈ (F i).erase (s i).1)
    (hbU : b ∉ U)
    (hUselected : Disjoint (U : Set ℕ) (selectedSet s))
    (hrepair :
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1))
        (((D.erase (s i).1 ∪ {b} : Finset ℕ) : Set ℕ)) q)
    (hcontemporary :
      ∀ j, j ∉ J →
        (s j).1 ∈
          supportVertices (additiveSupportFamily A (k + 1)) q →
        U.card + (k + 1) < (F j).card) :
    (∃ t : BlockSelector F, ∃ u ∈ Q, u < q ∧
        DestroysAt
          (additiveSupportFamily A (k + 1))
          (selectedSet t) u) ∨
      ∃ j ∈ J, ∃ E ∈ additiveSupportFamily A (k + 1) q,
        (s j).1 ∈ E ∧ E ∩ D = {(s i).1} := by
  classical
  obtain ⟨E, hER, hEswap⟩ :=
    not_destroysAt_iff.mp hrepair
  obtain ⟨t, hUavoid, hqSurvives⟩ | ⟨j, hjJ, hsjE⟩ :=
    blockAlignedRepairWitness_extends_protected_or_hitBlockCollision
      P s hbBlock hbU hUselected hER hEswap
        (fun j hjJ hsjE =>
          hcontemporary j hjJ
            (Finset.mem_biUnion.mpr ⟨E, hER, hsjE⟩))
  · obtain ⟨u, huQ, huDestroy⟩ := hcert t
    by_cases huq : u = q
    · subst u
      exact (hqSurvives huDestroy).elim
    by_cases hqu : q < u
    · obtain ⟨G, hGR, hGU⟩ := hprotected u huQ hqu
      exact ((huDestroy G hGR)
        (Set.disjoint_of_subset_left hGU hUavoid)).elim
    · left
      refine ⟨t, u, huQ, ?_, huDestroy⟩
      omega
  · right
    have hactiveE : (s i).1 ∈ E := by
      by_contra hsiE
      apply hDdestroy E hER
      rw [Set.disjoint_left]
      intro x hxE hxD
      by_cases hxi : x = (s i).1
      · subst x
        exact hsiE (Finset.mem_coe.mp hxE)
      · apply Set.disjoint_left.mp hEswap hxE
        apply Finset.mem_coe.mpr
        exact Finset.mem_union_left _
          (Finset.mem_erase.mpr
            ⟨hxi, Finset.mem_coe.mp hxD⟩)
    have hprivate : E ∩ D = {(s i).1} := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxE, hxD⟩ := Finset.mem_inter.mp hx
        have hxi : x = (s i).1 := by
          by_contra hne
          apply Set.disjoint_left.mp hEswap
            (Finset.mem_coe.mpr hxE)
          apply Finset.mem_coe.mpr
          exact Finset.mem_union_left _
            (Finset.mem_erase.mpr ⟨hne, Finset.mem_coe.mp hxD⟩)
        simpa [hxi]
      · intro hx
        have hxi : x = (s i).1 := by simpa using hx
        subst x
        exact Finset.mem_inter.mpr ⟨hactiveE, hactive⟩
    exact ⟨j, hjJ, E, hER, hsjE, hprivate⟩

/-- Repeated deficient old-block collisions force genuine lower-order
support growth.

Let `J` contain the blocks too small for protected completion.  At every
active destroyer point outside `J`, the local dependency theorem gives
either a large rooted matching at `q` or a safe replacement; its larger
dependency horn is impossible at the exact upper rank.  Applying the
collision-preserving safe-swap theorem to that replacement gives strict
certificate descent or a private support hitting a block in `J`.

If neither growth nor descent occurs, these private supports inject the
contemporary destroyer points into the disjoint union of the lower-order
families indexed by `J`.  Thus more than `J.card * r` active points force
more than `r` coherent representations at one old coordinate. -/
theorem blockAligned_manyActivePoints_force_rootedMatching_or_rankGrowthDescent_or_oldGrowth
    {A : Set ℕ} {k q r : ℕ} {Q J : Finset ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D : Finset ℕ}
    (hqQ : q ∈ Q)
    (hcert : ∀ t : BlockSelector F, ∃ u ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u)
    (hlarger : ∀ u ∈ Q, q < u →
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet s) u)
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hDselected : (D : Set ℕ) ⊆ selectedSet s)
    (hactiveLarge : ∀ i,
      (s i).1 ∈ D → i ∉ J →
        (k + 1) *
            (additiveRootedMatchingBound (k + 1) r +
              (Q.filter fun u => q < u).card) <
          ((F i).erase (s i).1).card)
    (hcompletion : ∀ j, j ∉ J →
      (s j).1 ∈
          supportVertices (additiveSupportFamily A (k + 1)) q →
      (k + 1) * (Q.filter fun u => q < u).card + (k + 1) <
        (F j).card)
    (hmany :
      J.card * r <
        (D.filter fun d => blockIndex P d ∉ J).card) :
    (∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
        R.card < k + 1 ∧
        M ⊆ additiveSupportFamily A (k + 1) q ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
          Disjoint (E \ R) (G \ R)) ∨
      (∃ t : BlockSelector F, ∃ u ∈ Q, u < q ∧
        (Q.filter fun v => q < v).card <
          (Q.filter fun v => u < v).card ∧
        DestroysAt
          (additiveSupportFamily A (k + 1))
          (selectedSet t) u) ∨
      ∃ j ∈ J,
        r < (additiveSupportFamily A k
          (q - (s j).1)).card := by
  classical
  let C : Finset ℕ :=
    D.filter fun d => blockIndex P d ∉ J
  by_cases hgrowth :
      ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
        R.card < k + 1 ∧
        M ⊆ additiveSupportFamily A (k + 1) q ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
          Disjoint (E \ R) (G \ R)
  · exact Or.inl hgrowth
  right
  by_cases hdescent :
      ∃ t : BlockSelector F, ∃ u ∈ Q, u < q ∧
        (Q.filter fun v => q < v).card <
          (Q.filter fun v => u < v).card ∧
        DestroysAt
          (additiveSupportFamily A (k + 1))
          (selectedSet t) u
  · exact Or.inl hdescent
  right
  by_cases holdGrowth :
      ∃ j ∈ J,
        r < (additiveSupportFamily A k
          (q - (s j).1)).card
  · exact holdGrowth
  push Not at holdGrowth
  have hcollision :
      ∀ d : {d // d ∈ C},
        ∃ j ∈ J, ∃ E ∈ additiveSupportFamily A (k + 1) q,
          (s j).1 ∈ E ∧ E ∩ D = {d.1} := by
    intro d
    have hdParts :
        d.1 ∈ D ∧ blockIndex P d.1 ∉ J :=
      Finset.mem_filter.mp d.2
    have hdSelected : d.1 ∈ selectedSet s :=
      hDselected (Finset.mem_coe.mpr hdParts.1)
    have hselectedAt :
        (s (blockIndex P d.1)).1 = d.1 :=
      (P.mem_selectedSet_iff s).mp hdSelected
    have hactive :
        (s (blockIndex P d.1)).1 ∈ D := by
      rw [hselectedAt]
      exact hdParts.1
    obtain hdirect | ⟨c, hcDisjoint, hsafe | hdependency⟩ :=
      blockAligned_rootedMatching_or_safeSwap_or_manyLargerDependencies
        (r := r) (m := (Q.filter fun u => q < u).card)
        s hlarger hminimal hactive
          (hactiveLarge (blockIndex P d.1) hactive hdParts.2)
    · exact (hgrowth hdirect).elim
    · obtain ⟨b, hbBlock, hbU, hrepair⟩ := hsafe
      let U : Finset ℕ := finiteSupportChoiceUnion c
      have hUcard :
          U.card ≤
            (k + 1) * (Q.filter fun u => q < u).card := by
        exact finiteSupportChoiceUnion_card_le
          (additiveSupportFamily_cardAtMost A (k + 1)) c
      have hprotected :
          ∀ u ∈ Q, q < u →
            ∃ E ∈ additiveSupportFamily A (k + 1) u,
              (E : Set ℕ) ⊆ (U : Set ℕ) := by
        intro u huQ hqu
        let u' : {n // n ∈ Q.filter fun v => q < v} :=
          ⟨u, Finset.mem_filter.mpr ⟨huQ, hqu⟩⟩
        refine ⟨(c u').1, (c u').2, ?_⟩
        intro x hx
        exact Finset.mem_coe.mpr
          (finiteSupportChoice_subset_union c u'
            (Finset.mem_coe.mp hx))
      have hcontemporary :
          ∀ j, j ∉ J →
            (s j).1 ∈
              supportVertices (additiveSupportFamily A (k + 1)) q →
            U.card + (k + 1) < (F j).card := by
        intro j hjJ hsjSupport
        exact lt_of_le_of_lt
          (Nat.add_le_add_right hUcard (k + 1))
          (hcompletion j hjJ hsjSupport)
      obtain hdesc | ⟨j, hjJ, E, hER, hsjE, hprivate⟩ :=
        blockAlignedSafeSwap_upperCertificate_forces_descent_or_oldCollision
          P s hcert hprotected hminimal.1 hactive hbBlock hbU
            (by simpa only [U] using hcDisjoint) hrepair hcontemporary
      · obtain ⟨t, u, huQ, huq, huDestroy⟩ := hdesc
        exact (hdescent ⟨t, u, huQ, huq,
          certificateUpperRank_strictly_grows_under_descent hqQ huq,
          huDestroy⟩).elim
      · refine ⟨j, hjJ, E, hER, hsjE, ?_⟩
        simpa only [hselectedAt] using hprivate
    · obtain ⟨S, hSUpper, hSlarge, _hScard, _hSlarger, _hcover⟩ :=
        hdependency
      have hScard :
          S.card ≤ (Q.filter fun u => q < u).card :=
        Finset.card_le_card hSUpper
      exact (not_lt_of_ge hScard hSlarge).elim
  choose oldIndex holdIndex upper hupperR holdUpper hprivate
    using hcollision
  have hlower :
      ∀ d : {d // d ∈ C},
        ∃ H ∈ additiveSupportFamily A k
            (q - (s (oldIndex d)).1),
          upper d = insert (s (oldIndex d)).1 H := by
    intro d
    exact additiveSupport_remove_hit_succ
      (hupperR d) (holdUpper d)
  choose lower hlowerR hreconstruct using hlower
  let Target :=
    Σ j : {j // j ∈ J},
      {H // H ∈ additiveSupportFamily A k
        (q - (s j.1).1)}
  let encode : {d // d ∈ C} → Target := fun d =>
    ⟨⟨oldIndex d, holdIndex d⟩,
      ⟨lower d, hlowerR d⟩⟩
  have hencode : Function.Injective encode := by
    intro d e hde
    have hj : oldIndex d = oldIndex e :=
      congrArg (fun z : Target => z.1.1) hde
    have hH : lower d = lower e :=
      congrArg (fun z : Target => z.2.1) hde
    apply Subtype.ext
    have hupperEq : upper d = upper e := by
      rw [hreconstruct d, hreconstruct e, hj, hH]
    have hsingle : ({d.1} : Finset ℕ) = {e.1} := by
      rw [← hprivate d, ← hprivate e, hupperEq]
    simpa using hsingle
  have hdomainTarget : C.card ≤ Fintype.card Target := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective encode hencode
  have htargetBound : Fintype.card Target ≤ J.card * r := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe]
    calc
      (∑ j : {j // j ∈ J},
          (additiveSupportFamily A k
            (q - (s j.1).1)).card) ≤
          ∑ _j : {j // j ∈ J}, r := by
        gcongr with j
        exact holdGrowth j.1 j.2
      _ = J.card * r := by simp
  have hCbound : C.card ≤ J.card * r :=
    hdomainTarget.trans htargetBound
  exact ((not_lt_of_ge hCbound) (by
    simpa only [C] using hmany)).elim

/-- Matching-normalized repeated-collision amplification.

Choose the collision threshold large enough both to dominate `r` and to
trigger rooted-matching normalization one order lower.  The preceding
theorem then has only three outputs: a rooted matching of size greater than
`r` at the current order and target, strict finite-certificate descent, or a
rooted matching of size greater than `r` at one coherent old difference.
Thus repeated old-coordinate failures no longer terminate in an
unnormalized support-count statement. -/
theorem blockAligned_manyActivePoints_force_matchingGrowth_or_rankGrowthDescent
    {A : Set ℕ} {k q r : ℕ} {Q J : Finset ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D : Finset ℕ}
    (hqQ : q ∈ Q)
    (hcert : ∀ t : BlockSelector F, ∃ u ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u)
    (hlarger : ∀ u ∈ Q, q < u →
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet s) u)
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hDselected : (D : Set ℕ) ⊆ selectedSet s)
    (hactiveLarge : ∀ i,
      (s i).1 ∈ D → i ∉ J →
        (k + 1) *
            (additiveRootedMatchingBound (k + 1)
                (max r (additiveRootedMatchingBound k r)) +
              (Q.filter fun u => q < u).card) <
          ((F i).erase (s i).1).card)
    (hcompletion : ∀ j, j ∉ J →
      (s j).1 ∈
          supportVertices (additiveSupportFamily A (k + 1)) q →
      (k + 1) * (Q.filter fun u => q < u).card + (k + 1) <
        (F j).card)
    (hmany :
      J.card * (max r (additiveRootedMatchingBound k r)) <
        (D.filter fun d => blockIndex P d ∉ J).card) :
    (∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
        R.card < k + 1 ∧
        M ⊆ additiveSupportFamily A (k + 1) q ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
          Disjoint (E \ R) (G \ R)) ∨
      (∃ t : BlockSelector F, ∃ u ∈ Q, u < q ∧
        (Q.filter fun v => q < v).card <
          (Q.filter fun v => u < v).card ∧
        DestroysAt
          (additiveSupportFamily A (k + 1))
          (selectedSet t) u) ∨
      ∃ j ∈ J, ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
        R.card < k ∧
        M ⊆ additiveSupportFamily A k (q - (s j).1) ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
          Disjoint (E \ R) (G \ R) := by
  let threshold := max r (additiveRootedMatchingBound k r)
  obtain hgrowth | hdescent | ⟨j, hjJ, hjGrowth⟩ :=
    blockAligned_manyActivePoints_force_rootedMatching_or_rankGrowthDescent_or_oldGrowth
      (r := threshold) P s hqQ hcert hlarger hminimal hDselected
        (by simpa only [threshold] using hactiveLarge)
        hcompletion (by simpa only [threshold] using hmany)
  · left
    obtain ⟨R, M, hRcard, hMsub, hMcard, hMroot,
        hMnonempty, hMdisjoint⟩ := hgrowth
    exact ⟨R, M, hRcard, hMsub,
      lt_of_le_of_lt (Nat.le_max_left _ _) hMcard,
      hMroot, hMnonempty, hMdisjoint⟩
  · exact Or.inr (Or.inl hdescent)
  · right
    right
    refine ⟨j, hjJ, ?_⟩
    exact additiveSupportSubfamily_has_large_rootedMatching
      k r (q - (s j).1)
      (additiveSupportFamily A k (q - (s j).1))
      Finset.Subset.rfl
      (le_trans (Nat.le_max_right _ _) (Nat.le_of_lt hjGrowth))

/-- Every point of an inclusion-minimal destroyer occurs in some support at
the destroyed target. -/
theorem IsInclusionMinimalDestroyer.subset_supportVertices
    {R : SupportFamily} {D : Finset ℕ} {q : ℕ}
    (hminimal : IsInclusionMinimalDestroyer R D q) :
    (D : Set ℕ) ⊆ (supportVertices R q : Set ℕ) := by
  intro d hdD
  obtain ⟨E, hER, hprivate⟩ :=
    hminimal.exists_uniqueHitSupport (Finset.mem_coe.mp hdD)
  apply Finset.mem_coe.mpr
  apply Finset.mem_biUnion.mpr
  refine ⟨E, hER, ?_⟩
  have hdSingleton : d ∈ ({d} : Finset ℕ) := by simp
  rw [← hprivate] at hdSingleton
  exact (Finset.mem_inter.mp hdSingleton).1

/-- The intrinsic exceptional set for one repair stage.

Only indices of blocks met by supports at `q` are considered.  Such an
index is deficient when it fails either the room needed to find a safe
active replacement or the smaller room needed to complete a retained
repair support. -/
noncomputable def deficientRepairHitBlocks
    {A : Set ℕ} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F) (s : BlockSelector F)
    (R : SupportFamily) (q activeNeed completionNeed : ℕ) : Finset ℕ :=
  ((supportVertices R q).image (blockIndex P)).filter fun j =>
    ¬ (activeNeed < ((F j).erase (s j).1).card ∧
      completionNeed < (F j).card)

/-- The number of intrinsically deficient repair blocks is at most the
number of vertices occurring in supports at the current target. -/
theorem deficientRepairHitBlocks_card_le_supportVertices
    {A : Set ℕ} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F) (s : BlockSelector F)
    (R : SupportFamily) (q activeNeed completionNeed : ℕ) :
    (deficientRepairHitBlocks P s R q activeNeed completionNeed).card ≤
      (supportVertices R q).card := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
    Finset.card_image_le

/-- Intrinsic-deficient-block form of repeated collision amplification.

The exceptional set is no longer supplied externally: it consists exactly
of support-hit blocks which lack one of the two capacities used by the
repair.  Outside this canonical finite set, both the active safe choice and
the support-local selector completion are automatic.  If the minimal
destroyer has more than the explicit pigeonhole budget of active points
outside that set, the outcome is matching growth at the current order,
strict upper-rank descent, or matching growth one order lower at a
deficient old coordinate. -/
theorem blockAligned_intrinsicDeficientBlocks_force_matchingGrowth_or_rankGrowthDescent
    {A : Set ℕ} {k q r : ℕ} {Q : Finset ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D : Finset ℕ}
    (hqQ : q ∈ Q)
    (hcert : ∀ t : BlockSelector F, ∃ u ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u)
    (hlarger : ∀ u ∈ Q, q < u →
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet s) u)
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hDselected : (D : Set ℕ) ⊆ selectedSet s)
    (hmany :
      let threshold := max r (additiveRootedMatchingBound k r)
      let activeNeed :=
        (k + 1) *
          (additiveRootedMatchingBound (k + 1) threshold +
            (Q.filter fun u => q < u).card)
      let completionNeed :=
        (k + 1) * (Q.filter fun u => q < u).card + (k + 1)
      let J := deficientRepairHitBlocks P s
        (additiveSupportFamily A (k + 1)) q activeNeed completionNeed
      J.card * threshold <
        (D.filter fun d => blockIndex P d ∉ J).card) :
    let threshold := max r (additiveRootedMatchingBound k r)
    let activeNeed :=
      (k + 1) *
        (additiveRootedMatchingBound (k + 1) threshold +
          (Q.filter fun u => q < u).card)
    let completionNeed :=
      (k + 1) * (Q.filter fun u => q < u).card + (k + 1)
    let J := deficientRepairHitBlocks P s
      (additiveSupportFamily A (k + 1)) q activeNeed completionNeed
    (∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
        R.card < k + 1 ∧
        M ⊆ additiveSupportFamily A (k + 1) q ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
          Disjoint (E \ R) (G \ R)) ∨
      (∃ t : BlockSelector F, ∃ u ∈ Q, u < q ∧
        (Q.filter fun v => q < v).card <
          (Q.filter fun v => u < v).card ∧
        DestroysAt
          (additiveSupportFamily A (k + 1))
          (selectedSet t) u) ∨
      ∃ j ∈ J, ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
        R.card < k ∧
        M ⊆ additiveSupportFamily A k (q - (s j).1) ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
          Disjoint (E \ R) (G \ R) := by
  dsimp only
  let threshold := max r (additiveRootedMatchingBound k r)
  let activeNeed :=
    (k + 1) *
      (additiveRootedMatchingBound (k + 1) threshold +
        (Q.filter fun u => q < u).card)
  let completionNeed :=
    (k + 1) * (Q.filter fun u => q < u).card + (k + 1)
  let J := deficientRepairHitBlocks P s
    (additiveSupportFamily A (k + 1)) q activeNeed completionNeed
  apply blockAligned_manyActivePoints_force_matchingGrowth_or_rankGrowthDescent
    (J := J) P s hqQ hcert hlarger hminimal hDselected
  · intro i hactive hiJ
    have hsiVertices :
        (s i).1 ∈ supportVertices
          (additiveSupportFamily A (k + 1)) q :=
      Finset.mem_coe.mp (hminimal.subset_supportVertices
        (Finset.mem_coe.mpr hactive))
    have hiImage :
        i ∈ (supportVertices
          (additiveSupportFamily A (k + 1)) q).image
            (blockIndex P) := by
      apply Finset.mem_image.mpr
      refine ⟨(s i).1, hsiVertices, ?_⟩
      exact P.blockIndex_eq_of_mem (s i).2
    have hiGood :
        activeNeed < ((F i).erase (s i).1).card ∧
          completionNeed < (F i).card := by
      by_contra hnot
      apply hiJ
      exact Finset.mem_filter.mpr ⟨hiImage, hnot⟩
    simpa only [activeNeed, threshold] using hiGood.1
  · intro j hjJ hsjVertices
    have hjImage :
        j ∈ (supportVertices
          (additiveSupportFamily A (k + 1)) q).image
            (blockIndex P) := by
      apply Finset.mem_image.mpr
      refine ⟨(s j).1, hsjVertices, ?_⟩
      exact P.blockIndex_eq_of_mem (s j).2
    have hjGood :
        activeNeed < ((F j).erase (s j).1).card ∧
          completionNeed < (F j).card := by
      by_contra hnot
      apply hjJ
      exact Finset.mem_filter.mpr ⟨hjImage, hnot⟩
    simpa only [completionNeed] using hjGood.2
  · simpa only [J, threshold, activeNeed, completionNeed] using hmany

/-- Uniform concentration bound for the residual branch of the
old-collision attack. -/
def oldCollisionConcentrationBound (k r : ℕ) : ℕ :=
  ((k + 1) * additiveRootedMatchingBound (k + 1) r + 1) *
    (max r (additiveRootedMatchingBound k r) + 1)

/-- Complete local fork after collision amplification.

No density assumption remains.  If the intrinsic deficient-block
pigeonhole inequality holds, the preceding theorem gives matching growth or
strict upper-rank descent.  If it fails, the old part of the destroyer has
at most one point per deficient block and the outside part satisfies the
pigeonhole bound.  In the absence of current-order matching growth, the
number of deficient blocks is itself bounded by the support-vertex union.
Consequently the entire minimal destroyer has the explicit uniform bound
`oldCollisionConcentrationBound k r`. -/
theorem blockAligned_matchingGrowth_or_rankGrowthDescent_or_boundedDestroyer
    {A : Set ℕ} {k q r : ℕ} {Q : Finset ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {D : Finset ℕ}
    (hqQ : q ∈ Q)
    (hcert : ∀ t : BlockSelector F, ∃ u ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u)
    (hlarger : ∀ u ∈ Q, q < u →
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet s) u)
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A (k + 1)) D q)
    (hDselected : (D : Set ℕ) ⊆ selectedSet s) :
    (∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
        R.card < k + 1 ∧
        M ⊆ additiveSupportFamily A (k + 1) q ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
          Disjoint (E \ R) (G \ R)) ∨
      (∃ t : BlockSelector F, ∃ u ∈ Q, u < q ∧
        (Q.filter fun v => q < v).card <
          (Q.filter fun v => u < v).card ∧
        DestroysAt
          (additiveSupportFamily A (k + 1))
          (selectedSet t) u) ∨
      (∃ j : ℕ, ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
        R.card < k ∧
        M ⊆ additiveSupportFamily A k (q - (s j).1) ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
          Disjoint (E \ R) (G \ R)) ∨
      D.card ≤ oldCollisionConcentrationBound k r := by
  classical
  by_cases hgrowth :
      ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
        R.card < k + 1 ∧
        M ⊆ additiveSupportFamily A (k + 1) q ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
          Disjoint (E \ R) (G \ R)
  · exact Or.inl hgrowth
  have hfamilySmall :
      (additiveSupportFamily A (k + 1) q).card <
        additiveRootedMatchingBound (k + 1) r := by
    by_contra hnot
    apply hgrowth
    exact additiveSupportSubfamily_has_large_rootedMatching
      (k + 1) r q (additiveSupportFamily A (k + 1) q)
      Finset.Subset.rfl (Nat.le_of_not_gt hnot)
  let threshold := max r (additiveRootedMatchingBound k r)
  let activeNeed :=
    (k + 1) *
      (additiveRootedMatchingBound (k + 1) threshold +
        (Q.filter fun u => q < u).card)
  let completionNeed :=
    (k + 1) * (Q.filter fun u => q < u).card + (k + 1)
  let J := deficientRepairHitBlocks P s
    (additiveSupportFamily A (k + 1)) q activeNeed completionNeed
  by_cases hmany :
      J.card * threshold <
        (D.filter fun d => blockIndex P d ∉ J).card
  · obtain hcurrent | hdescent | ⟨j, _hjJ, hlower⟩ :=
      blockAligned_intrinsicDeficientBlocks_force_matchingGrowth_or_rankGrowthDescent
        P s hqQ hcert hlarger hminimal hDselected
          (by
            simpa only [J, threshold, activeNeed, completionNeed]
              using hmany)
    · exact (hgrowth hcurrent).elim
    · exact Or.inr (Or.inl hdescent)
    · exact Or.inr (Or.inr (Or.inl ⟨j, hlower⟩))
  · right
    right
    right
    have houtside :
        (D.filter fun d => blockIndex P d ∉ J).card ≤
          J.card * threshold :=
      Nat.le_of_not_gt hmany
    let Dold : Finset ℕ := J.image fun j => (s j).1
    let oldPart : Finset ℕ :=
      D.filter fun d => blockIndex P d ∈ J
    have holdPartSub : oldPart ⊆ Dold := by
      intro d hdOld
      have hdParts : d ∈ D ∧ blockIndex P d ∈ J :=
        Finset.mem_filter.mp hdOld
      have hdSelected : d ∈ selectedSet s :=
        hDselected (Finset.mem_coe.mpr hdParts.1)
      have hselectedAt : (s (blockIndex P d)).1 = d :=
        (P.mem_selectedSet_iff s).mp hdSelected
      exact Finset.mem_image.mpr
        ⟨blockIndex P d, hdParts.2, hselectedAt⟩
    have holdPartCard : oldPart.card ≤ J.card :=
      (Finset.card_le_card holdPartSub).trans Finset.card_image_le
    have hsplit :
        oldPart.card +
          (D.filter fun d => blockIndex P d ∉ J).card = D.card := by
      simpa [oldPart] using
        (Finset.card_filter_add_card_filter_not
          (s := D) (p := fun d => blockIndex P d ∈ J))
    have hDbyJ :
        D.card ≤ (J.card + 1) * (threshold + 1) := by
      have hraw : D.card ≤ J.card + J.card * threshold := by
        omega
      calc
        D.card ≤ J.card + J.card * threshold := hraw
        _ ≤ (J.card + 1) * (threshold + 1) := by
          rw [Nat.mul_add, Nat.add_mul]
          omega
    have hvertices :
        (supportVertices (additiveSupportFamily A (k + 1)) q).card ≤
          (k + 1) *
            (additiveSupportFamily A (k + 1) q).card := by
      exact biUnion_card_le_of_edge_card_le
        (H := additiveSupportFamily A (k + 1) q)
        (M := additiveSupportFamily A (k + 1) q)
        (by simp) (fun E hE =>
          additiveSupportFamily_cardAtMost A (k + 1) q E hE)
    have hJcard :
        J.card ≤
          (k + 1) * additiveRootedMatchingBound (k + 1) r := by
      calc
        J.card ≤
            (supportVertices
              (additiveSupportFamily A (k + 1)) q).card := by
          simpa only [J] using
            deficientRepairHitBlocks_card_le_supportVertices
              P s (additiveSupportFamily A (k + 1)) q
                activeNeed completionNeed
        _ ≤ (k + 1) *
            (additiveSupportFamily A (k + 1) q).card := hvertices
        _ ≤ (k + 1) *
            additiveRootedMatchingBound (k + 1) r :=
          Nat.mul_le_mul_left (k + 1) (Nat.le_of_lt hfamilySmall)
    have hfactor :
        J.card + 1 ≤
          (k + 1) * additiveRootedMatchingBound (k + 1) r + 1 :=
      Nat.add_le_add_right hJcard 1
    exact hDbyJ.trans (by
      simpa only [oldCollisionConcentrationBound, threshold] using
        Nat.mul_le_mul_right (threshold + 1) hfactor)

/-- A surviving support disjoint from the locked deficient coordinates
extends to a full protected selector.

Keep every selected coordinate which does not hit that support.  A selected
coordinate which does hit it cannot belong to the locked set, and only its
own block is rerouted outside the protected union and the support.  Thus
capacity is required solely at actual support-hit coordinates outside the
locked set. -/
theorem lockedPrefixSurvival_extends_avoiding_protected
    {A : Set ℕ} {R : SupportFamily} {q h : ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F) {U J : Finset ℕ}
    (hcard : ∀ E ∈ R q, E.card ≤ h)
    (hUselected : Disjoint (U : Set ℕ) (selectedSet s))
    (hcapacity : ∀ j,
      (s j).1 ∈ supportVertices R q → j ∉ J →
        U.card + h < (F j).card)
    (hlocked :
      ¬ DestroysAt R
        (((J.image fun j => (s j).1 : Finset ℕ) : Set ℕ)) q) :
    ∃ t : BlockSelector F,
      Disjoint (U : Set ℕ) (selectedSet t) ∧
      ¬ DestroysAt R (selectedSet t) q := by
  classical
  obtain ⟨E, hER, hEL⟩ := not_destroysAt_iff.mp hlocked
  have hEcard : E.card ≤ h := hcard E hER
  have hlockedMiss : ∀ j ∈ J, (s j).1 ∉ E := by
    intro j hjJ hsjE
    apply Set.disjoint_left.mp hEL
      (Finset.mem_coe.mpr hsjE)
    apply Finset.mem_coe.mpr
    exact Finset.mem_image.mpr ⟨j, hjJ, rfl⟩
  let W : Finset ℕ := U ∪ E
  have hWcard : W.card ≤ U.card + h := by
    calc
      W.card ≤ U.card + E.card := by
        simpa only [W] using Finset.card_union_le U E
      _ ≤ U.card + h := Nat.add_le_add_left hEcard U.card
  have houtside :
      ∀ j, (hsjE : (s j).1 ∈ E) → (F j \ W).Nonempty := by
    intro j hsjE
    have hjJ : j ∉ J := by
      intro hjJ
      exact hlockedMiss j hjJ hsjE
    by_contra hempty
    have hsubset : F j ⊆ W := by
      intro x hxF
      by_contra hxW
      exact hempty ⟨x, Finset.mem_sdiff.mpr ⟨hxF, hxW⟩⟩
    have hFcard : (F j).card ≤ W.card :=
      Finset.card_le_card hsubset
    have hsjVertices : (s j).1 ∈ supportVertices R q :=
      Finset.mem_biUnion.mpr ⟨E, hER, hsjE⟩
    have hlarge := hcapacity j hsjVertices hjJ
    omega
  choose outside houtsideSpec using houtside
  let t : BlockSelector F := fun j =>
    if hsjE : (s j).1 ∈ E then
      ⟨outside j hsjE,
        (Finset.mem_sdiff.mp (houtsideSpec j hsjE)).1⟩
    else
      s j
  have hUavoid : Disjoint (U : Set ℕ) (selectedSet t) := by
    rw [Set.disjoint_left]
    intro x hxU hxSelected
    obtain ⟨j, hjx⟩ := hxSelected
    by_cases hsjE : (s j).1 ∈ E
    · have htj : (t j).1 = outside j hsjE := by
        dsimp [t]
        rw [dif_pos hsjE]
      have hxOutside : x = outside j hsjE :=
        hjx.symm.trans htj
      have houtW :=
        (Finset.mem_sdiff.mp (houtsideSpec j hsjE)).2
      exact houtW (Finset.mem_union_left E
        (hxOutside ▸ Finset.mem_coe.mp hxU))
    · have htj : (t j).1 = (s j).1 := by
        dsimp [t]
        rw [dif_neg hsjE]
      exact Set.disjoint_left.mp hUselected hxU
        ⟨j, htj.symm.trans hjx⟩
  refine ⟨t, hUavoid, ?_⟩
  apply not_destroysAt_iff.mpr
  refine ⟨E, hER, ?_⟩
  rw [Set.disjoint_left]
  intro x hxE hxSelected
  obtain ⟨j, hjx⟩ := hxSelected
  by_cases hsjE : (s j).1 ∈ E
  · have htj : (t j).1 = outside j hsjE := by
      dsimp [t]
      rw [dif_pos hsjE]
    have hxOutside : x = outside j hsjE :=
      hjx.symm.trans htj
    have houtW :=
      (Finset.mem_sdiff.mp (houtsideSpec j hsjE)).2
    exact houtW (Finset.mem_union_right U
      (hxOutside ▸ Finset.mem_coe.mp hxE))
  · have htj : (t j).1 = (s j).1 := by
      dsimp [t]
      rw [dif_neg hsjE]
    have hxs : x = (s j).1 := hjx.symm.trans htj
    exact hsjE (hxs ▸ Finset.mem_coe.mp hxE)

/-- Every selector in a finite certificate has a largest target which it
destroys, and all larger certificate targets survive. -/
theorem exists_maximalDestroyedCertificateTarget
    {R : SupportFamily} {Q : Finset ℕ}
    {F : ℕ → Finset ℕ}
    (hcert : ∀ t : BlockSelector F, ∃ u ∈ Q,
      DestroysAt R (selectedSet t) u)
    (t : BlockSelector F) :
    ∃ q ∈ Q, DestroysAt R (selectedSet t) q ∧
      ∀ u ∈ Q, q < u →
        ¬ DestroysAt R (selectedSet t) u := by
  classical
  let Bad : Finset ℕ :=
    Q.filter fun u => DestroysAt R (selectedSet t) u
  have hBadNonempty : Bad.Nonempty := by
    obtain ⟨u, huQ, huDestroy⟩ := hcert t
    exact ⟨u, Finset.mem_filter.mpr ⟨huQ, huDestroy⟩⟩
  let q := Bad.max' hBadNonempty
  have hqBad : q ∈ Bad := Finset.max'_mem Bad hBadNonempty
  have hqParts :
      q ∈ Q ∧ DestroysAt R (selectedSet t) q :=
    Finset.mem_filter.mp hqBad
  refine ⟨q, hqParts.1, hqParts.2, ?_⟩
  intro u huQ hqu huDestroy
  have huBad : u ∈ Bad :=
    Finset.mem_filter.mpr ⟨huQ, huDestroy⟩
  exact (not_lt_of_ge (Finset.le_max' Bad u huBad)) hqu

/-- Certificate-safe locked-prefix dichotomy.

If the selected coordinates in the exceptional blocks do not already
destroy `q`, the preceding support-local completion constructs a selector
which preserves `q` and avoids all protected larger-target supports.  The
certificate must then migrate strictly downward, and its upper-rank measure
strictly increases.  Therefore failure of a full certificate-safe repair is
exactly genuine destruction by the finite locked prefix. -/
theorem lockedPrefix_destroys_or_rankGrowthCertificateDescent
    {A : Set ℕ} {k q : ℕ} {Q U J : Finset ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F)
    (hqQ : q ∈ Q)
    (hcert : ∀ t : BlockSelector F, ∃ u ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u)
    (hprotected : ∀ u ∈ Q, q < u →
      ∃ E ∈ additiveSupportFamily A (k + 1) u,
        (E : Set ℕ) ⊆ (U : Set ℕ))
    (hUselected : Disjoint (U : Set ℕ) (selectedSet s))
    (hcapacity : ∀ j,
      (s j).1 ∈ supportVertices
          (additiveSupportFamily A (k + 1)) q →
        j ∉ J → U.card + (k + 1) < (F j).card) :
    DestroysAt
        (additiveSupportFamily A (k + 1))
        (((J.image fun j => (s j).1 : Finset ℕ) : Set ℕ)) q ∨
      ∃ t : BlockSelector F, ∃ u ∈ Q, u < q ∧
        (Q.filter fun v => q < v).card <
          (Q.filter fun v => u < v).card ∧
        DestroysAt
          (additiveSupportFamily A (k + 1))
          (selectedSet t) u ∧
        ∀ v ∈ Q, u < v →
          ¬ DestroysAt
            (additiveSupportFamily A (k + 1))
            (selectedSet t) v := by
  classical
  by_cases hlocked :
      DestroysAt
        (additiveSupportFamily A (k + 1))
        (((J.image fun j => (s j).1 : Finset ℕ) : Set ℕ)) q
  · exact Or.inl hlocked
  right
  obtain ⟨t, htU, htq⟩ :=
    lockedPrefixSurvival_extends_avoiding_protected
      P s (U := U) (J := J)
        (fun E hER =>
          additiveSupportFamily_cardAtMost A (k + 1) q E hER)
        hUselected hcapacity hlocked
  obtain ⟨u, huQ, huDestroy, huMax⟩ :=
    exists_maximalDestroyedCertificateTarget hcert t
  have huqLt : u < q := by
    by_contra hnot
    have hqu : q ≤ u := Nat.le_of_not_gt hnot
    rcases hqu.eq_or_lt with rfl | hqu
    · exact htq huDestroy
    · obtain ⟨E, hER, hEU⟩ := hprotected u huQ hqu
      exact (huDestroy E hER)
        (Set.disjoint_of_subset_left hEU htU)
  exact ⟨t, u, huQ, huqLt,
    certificateUpperRank_strictly_grows_under_descent hqQ huqLt,
    huDestroy, huMax⟩

/-- Intrinsic locked-prefix certificate dichotomy.

Store one surviving support for every certificate target above `q` and let
`J` consist exactly of support-hit blocks below the required completion
capacity.  Outside `J`, the protected completion is automatic.  Hence
either the selected values in `J` genuinely destroy `q`, or the certificate
migrates strictly downward.  The destructive locked prefix has cardinality
at most the support-vertex count at `q`. -/
theorem blockAligned_intrinsicLockedPrefix_destruction_or_rankGrowthDescent
    {A : Set ℕ} {k q : ℕ} {Q : Finset ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F)
    (hqQ : q ∈ Q)
    (hcert : ∀ t : BlockSelector F, ∃ u ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet t) u)
    (hlarger : ∀ u ∈ Q, q < u →
      ¬ DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet s) u) :
    let completionNeed :=
      (k + 1) * (Q.filter fun u => q < u).card + (k + 1)
    let J := deficientRepairHitBlocks P s
      (additiveSupportFamily A (k + 1)) q 0 completionNeed
    (((J.image fun j => (s j).1 : Finset ℕ).card ≤
        (supportVertices
          (additiveSupportFamily A (k + 1)) q).card) ∧
      DestroysAt
        (additiveSupportFamily A (k + 1))
        (((J.image fun j => (s j).1 : Finset ℕ) : Set ℕ)) q) ∨
      ∃ t : BlockSelector F, ∃ u ∈ Q, u < q ∧
        (Q.filter fun v => q < v).card <
          (Q.filter fun v => u < v).card ∧
        DestroysAt
          (additiveSupportFamily A (k + 1))
          (selectedSet t) u ∧
        ∀ v ∈ Q, u < v →
          ¬ DestroysAt
            (additiveSupportFamily A (k + 1))
            (selectedSet t) v := by
  classical
  dsimp only
  let Upper : Finset ℕ := Q.filter fun u => q < u
  let completionNeed := (k + 1) * Upper.card + (k + 1)
  let J := deficientRepairHitBlocks P s
    (additiveSupportFamily A (k + 1)) q 0 completionNeed
  obtain ⟨c, hcDisjoint⟩ :=
    exists_survivingLargerSupportChoice s hlarger
  let U : Finset ℕ := finiteSupportChoiceUnion c
  have hUcard : U.card ≤ (k + 1) * Upper.card := by
    exact finiteSupportChoiceUnion_card_le
      (additiveSupportFamily_cardAtMost A (k + 1)) c
  have hprotected :
      ∀ u ∈ Q, q < u →
        ∃ E ∈ additiveSupportFamily A (k + 1) u,
          (E : Set ℕ) ⊆ (U : Set ℕ) := by
    intro u huQ hqu
    let u' : {n // n ∈ Upper} :=
      ⟨u, Finset.mem_filter.mpr ⟨huQ, hqu⟩⟩
    refine ⟨(c u').1, (c u').2, ?_⟩
    intro x hx
    exact Finset.mem_coe.mpr
      (finiteSupportChoice_subset_union c u'
        (Finset.mem_coe.mp hx))
  have hcapacity :
      ∀ j,
        (s j).1 ∈ supportVertices
            (additiveSupportFamily A (k + 1)) q →
          j ∉ J → U.card + (k + 1) < (F j).card := by
    intro j hsjVertices hjJ
    have hjImage :
        j ∈ (supportVertices
          (additiveSupportFamily A (k + 1)) q).image
            (blockIndex P) := by
      apply Finset.mem_image.mpr
      refine ⟨(s j).1, hsjVertices, ?_⟩
      exact P.blockIndex_eq_of_mem (s j).2
    have hjGood :
        0 < ((F j).erase (s j).1).card ∧
          completionNeed < (F j).card := by
      by_contra hnot
      apply hjJ
      exact Finset.mem_filter.mpr ⟨hjImage, hnot⟩
    exact lt_of_le_of_lt
      (Nat.add_le_add_right hUcard (k + 1)) hjGood.2
  obtain hlocked | hdescent :=
    lockedPrefix_destroys_or_rankGrowthCertificateDescent
      P s hqQ hcert hprotected
        (by simpa only [U] using hcDisjoint) hcapacity
  · left
    refine ⟨?_, hlocked⟩
    exact Finset.card_image_le.trans (by
      simpa only [J] using
        deficientRepairHitBlocks_card_le_supportVertices
          P s (additiveSupportFamily A (k + 1)) q
            0 completionNeed)
  · exact Or.inr (by simpa only [Upper] using hdescent)

/-- Uniform size budget for the locked-prefix composition. -/
def lockedPrefixCompositionBound (k r : ℕ) : ℕ :=
  max ((k + 1) * additiveRootedMatchingBound (k + 1) r)
    (additiveRootedMatchingBound k r)

/-- Rooted exact-target versus gap-translate dichotomy.  Once the available
basis elements below `n` outnumber the rooted-matching threshold, `n` either
carries the requested delta system at its exact label or has a predecessor
`n-b` which is a genuine lower-order gap. -/
theorem many_belowBasisElements_force_exactRootedMatching_or_gap
    {A : Set ℕ} {k n r : ℕ} {B : Finset ℕ}
    (hBA : ∀ b ∈ B, b ∈ A)
    (hBn : ∀ b ∈ B, b ≤ n)
    (hlarge :
      (k + 1) * additiveRootedMatchingBound (k + 1) r < B.card) :
    (∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
        R.card < k + 1 ∧
        M ⊆ additiveSupportFamily A (k + 1) n ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ D ∈ M, E ≠ D →
          Disjoint (E \ R) (D \ R)) ∨
      ∃ b ∈ B, additiveSupportFamily A k (n - b) = ∅ := by
  obtain hrich | hgap :=
    many_belowBasisElements_force_exactSupportGrowth_or_gap
      hBA hBn hlarge
  · left
    exact additiveSupportSubfamily_has_large_rootedMatching
      (k + 1) r n (additiveSupportFamily A (k + 1) n)
      Finset.Subset.rfl (Nat.le_of_lt hrich)
  · exact Or.inr hgap

/-- Cofinal covering form of the rooted/gap dichotomy.  For an exact basis,
fix enough basis elements once and move beyond their maximum.  Every later
target then either has a large rooted matching at that exact target or lies
in `b + Gap_k(A)` for some `b ∈ A`. -/
theorem IsExactTupleAsymptoticBasis.eventually_exactRootedMatching_or_lowerGap
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1)) :
    ∀ r, ∃ N, ∀ n, N ≤ n →
      (∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
          R.card < k + 1 ∧
          M ⊆ additiveSupportFamily A (k + 1) n ∧
          r < M.card ∧
          (∀ E ∈ M, R ⊆ E) ∧
          (∀ E ∈ M, (E \ R).Nonempty) ∧
          ∀ E ∈ M, ∀ D ∈ M, E ≠ D →
            Disjoint (E \ R) (D \ R)) ∨
        ∃ b, b ∈ A ∧ b ≤ n ∧
          additiveSupportFamily A k (n - b) = ∅ := by
  classical
  intro r
  let s :=
    (k + 1) * additiveRootedMatchingBound (k + 1) r + 1
  obtain ⟨B, hBA, hBcard⟩ :=
    hbasis.infinite.exists_subset_card_eq s
  have hBnonempty : B.Nonempty := by
    apply Finset.card_pos.mp
    rw [hBcard]
    simp [s]
  refine ⟨B.max' hBnonempty, ?_⟩
  intro n hn
  have hBn : ∀ b ∈ B, b ≤ n := by
    intro b hbB
    exact (Finset.le_max' B b hbB).trans hn
  have hlarge :
      (k + 1) * additiveRootedMatchingBound (k + 1) r < B.card := by
    rw [hBcard]
    simp [s]
  obtain hrooted | ⟨b, hbB, hgap⟩ :=
    many_belowBasisElements_force_exactRootedMatching_or_gap
      hBA hBn hlarge
  · exact Or.inl hrooted
  · exact Or.inr ⟨b, hBA hbB, hBn b hbB, hgap⟩

/-- Uniform protected-set version of the rooted matching/lower-gap
dichotomy.

Choose a fixed basis pool whose cardinality exceeds the rooted-matching
threshold by `w`.  After an arbitrary protected set `W` of cardinality at
most `w` is revealed, deleting `W` from that fixed pool still leaves enough
test anchors.  Consequently the lower-gap witness can be required to lie
outside `W`, with a late threshold independent of the actual vertices of
`W`. -/
theorem IsExactTupleAsymptoticBasis.eventually_exactRootedMatching_or_lowerGap_avoiding
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1)) :
    ∀ r w, ∃ N, ∀ W : Finset ℕ, W.card ≤ w →
      ∀ n, N ≤ n →
        (∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
            R.card < k + 1 ∧
            M ⊆ additiveSupportFamily A (k + 1) n ∧
            r < M.card ∧
            (∀ E ∈ M, R ⊆ E) ∧
            (∀ E ∈ M, (E \ R).Nonempty) ∧
            ∀ E ∈ M, ∀ D ∈ M, E ≠ D →
              Disjoint (E \ R) (D \ R)) ∨
          ∃ b, b ∈ A ∧ b ∉ W ∧ b ≤ n ∧
            additiveSupportFamily A k (n - b) = ∅ := by
  classical
  intro r w
  let needed :=
    (k + 1) * additiveRootedMatchingBound (k + 1) r + 1
  obtain ⟨B₀, hB₀A, hB₀card⟩ :=
    hbasis.infinite.exists_subset_card_eq (needed + w)
  have hB₀nonempty : B₀.Nonempty := by
    apply Finset.card_pos.mp
    rw [hB₀card]
    simp [needed]
  refine ⟨B₀.max' hB₀nonempty, ?_⟩
  intro W hWcard n hn
  let B : Finset ℕ := B₀ \ W
  have hBA : ∀ b ∈ B, b ∈ A := by
    intro b hbB
    exact hB₀A (Finset.mem_sdiff.mp hbB).1
  have hBW : Disjoint B W := Finset.sdiff_disjoint
  have hBn : ∀ b ∈ B, b ≤ n := by
    intro b hbB
    have hbB₀ := (Finset.mem_sdiff.mp hbB).1
    exact (Finset.le_max' B₀ b hbB₀).trans hn
  have hinterCard : (B₀ ∩ W).card ≤ W.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hsplit :
      B.card + (B₀ ∩ W).card = B₀.card := by
    exact Finset.card_sdiff_add_card_inter B₀ W
  have hlarge :
      (k + 1) * additiveRootedMatchingBound (k + 1) r <
        B.card := by
    rw [hB₀card] at hsplit
    dsimp only [needed] at hsplit
    omega
  obtain hrooted | ⟨b, hbB, hgap⟩ :=
    many_belowBasisElements_force_exactRootedMatching_or_gap
      hBA hBn hlarge
  · exact Or.inl hrooted
  · have hbParts := Finset.mem_sdiff.mp hbB
    exact Or.inr
      ⟨b, hB₀A hbParts.1,
        fun hbW => Finset.disjoint_left.mp hBW hbB hbW,
        hBn b hbB, hgap⟩

/-- Every exact order-`k` basis has arbitrarily large rooted matchings at
*every* sufficiently late successor-order target.

The exact-target rooted/gap argument is run with a fixed finite pool
`B ⊆ A`.  Its only alternative to a large order-`k+1` rooted matching at
`n` is an order-`k` gap at `n-b` for some `b ∈ B`.  Since `B` is fixed, once
`n` is beyond the order-`k` basis threshold plus `max B`, every such
predecessor is represented.  Thus the gap horn vanishes uniformly.

This is stronger than cofinal matching growth: the target label does not
move and no exceptional late targets remain. -/
theorem IsExactTupleAsymptoticBasis.eventually_successorExactRootedMatching
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k) :
    ∀ r, ∃ N, ∀ n, N ≤ n →
      ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
        R.card < k + 1 ∧
        M ⊆ additiveSupportFamily A (k + 1) n ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ D ∈ M, E ≠ D →
          Disjoint (E \ R) (D \ R) := by
  classical
  intro r
  obtain ⟨N₀, hN₀⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  let size :=
    (k + 1) * additiveRootedMatchingBound (k + 1) r + 1
  obtain ⟨B, hBA, hBcard⟩ :=
    hbasis.infinite.exists_subset_card_eq size
  have hBnonempty : B.Nonempty := by
    apply Finset.card_pos.mp
    rw [hBcard]
    simp [size]
  refine ⟨N₀ + B.max' hBnonempty, ?_⟩
  intro n hn
  have hBn : ∀ b ∈ B, b ≤ n := by
    intro b hbB
    have hbmax : b ≤ B.max' hBnonempty :=
      Finset.le_max' B b hbB
    omega
  have hlarge :
      (k + 1) * additiveRootedMatchingBound (k + 1) r <
        B.card := by
    rw [hBcard]
    simp [size]
  obtain hrooted | ⟨b, hbB, hgap⟩ :=
    many_belowBasisElements_force_exactRootedMatching_or_gap
      hBA hBn hlarge
  · exact hrooted
  · have hbmax : b ≤ B.max' hBnonempty :=
      Finset.le_max' B b hbB
    obtain ⟨E, hER, _hEnonempty⟩ :=
      hN₀ (n - b) (by omega)
    rw [hgap] at hER
    simpa using hER

/-- Rooted matching form of the distinguished-anchor fork.  With enough
external tests, either the original predecessor target `q` already carries
the requested large delta system, or a hit in the strict erased core carries
one at its translated target.

Unlike the earlier recurrent rooted-matching theorem, the first branch keeps
the arithmetic label `q` exactly.  The second branch isolates the remaining
obstruction inside `T.erase a`; it does not yet assert that this erased core
destroys the translated target. -/
theorem large_externalAnchorSet_forces_rootedMatching_anchorFork
    {A : Set ℕ} {k n q a r : ℕ} {T B : Finset ℕ}
    (hnqa : n = q + a)
    (hdestroy : DestroysAt
      (additiveSupportFamily A (k + 2)) (T : Set ℕ) n)
    (hBA : ∀ b ∈ B, b ∈ A)
    (hBT : Disjoint B T)
    (hble : ∀ b ∈ B, b ≤ n)
    (hrep : ∀ b ∈ B,
      (additiveSupportFamily A (k + 1) (n - b)).Nonempty)
    (hlarge :
      T.card *
          ((k + 1) * additiveRootedMatchingBound (k + 1) r) <
        B.card) :
    (∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
        R.card < k + 1 ∧
        M ⊆ additiveSupportFamily A (k + 1) q ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ D ∈ M, E ≠ D →
          Disjoint (E \ R) (D \ R)) ∨
      ∃ x ∈ T.erase a, x ≤ n ∧
        ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
          R.card < k + 1 ∧
          M ⊆ additiveSupportFamily A (k + 1) (n - x) ∧
          r < M.card ∧
          (∀ E ∈ M, R ⊆ E) ∧
          (∀ E ∈ M, (E \ R).Nonempty) ∧
          ∀ E ∈ M, ∀ D ∈ M, E ≠ D →
            Disjoint (E \ R) (D \ R) := by
  obtain hexact | hoff :=
    large_externalAnchorSet_forces_supportGrowth_anchorFork
      hnqa hdestroy hBA hBT hble hrep hlarge
  · left
    exact additiveSupportSubfamily_has_large_rootedMatching
      (k + 1) r q (additiveSupportFamily A (k + 1) q)
      Finset.Subset.rfl (Nat.le_of_lt hexact)
  · right
    obtain ⟨x, hxcore, hxn, hxlarge⟩ := hoff
    refine ⟨x, hxcore, hxn, ?_⟩
    exact additiveSupportSubfamily_has_large_rootedMatching
      (k + 1) r (n - x)
      (additiveSupportFamily A (k + 1) (n - x))
      Finset.Subset.rfl (Nat.le_of_lt hxlarge)

/-- Exact-basis version of the rooted anchor fork, using test anchors below
the predecessor target. -/
theorem IsExactTupleAsymptoticBasis.large_belowTargetAnchorSet_forces_rootedMatching_anchorFork
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1)) :
    ∃ N, ∀ {q a r : ℕ} {T B : Finset ℕ},
      DestroysAt
          (additiveSupportFamily A (k + 2)) (T : Set ℕ) (q + a) →
      (∀ b ∈ B, b ∈ A) →
      Disjoint B T →
      (∀ b ∈ B, b ≤ q) →
      N ≤ a →
      T.card *
          ((k + 1) * additiveRootedMatchingBound (k + 1) r) <
        B.card →
      (∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
          R.card < k + 1 ∧
          M ⊆ additiveSupportFamily A (k + 1) q ∧
          r < M.card ∧
          (∀ E ∈ M, R ⊆ E) ∧
          (∀ E ∈ M, (E \ R).Nonempty) ∧
          ∀ E ∈ M, ∀ D ∈ M, E ≠ D →
            Disjoint (E \ R) (D \ R)) ∨
        ∃ x ∈ T.erase a, x ≤ q + a ∧
          ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
            R.card < k + 1 ∧
            M ⊆
              additiveSupportFamily A (k + 1) (q + a - x) ∧
            r < M.card ∧
            (∀ E ∈ M, R ⊆ E) ∧
            (∀ E ∈ M, (E \ R).Nonempty) ∧
            ∀ E ∈ M, ∀ D ∈ M, E ≠ D →
              Disjoint (E \ R) (D \ R) := by
  obtain ⟨N, hN⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  refine ⟨N, ?_⟩
  intro q a r T B hdestroy hBA hBT hbq hNa hlarge
  apply large_externalAnchorSet_forces_rootedMatching_anchorFork
    (n := q + a) (q := q) (a := a) rfl
    hdestroy hBA hBT
  · intro b hbB
    exact (hbq b hbB).trans (Nat.le_add_right q a)
  · intro b hbB
    obtain ⟨E, hER, _⟩ :=
      hN (q + a - b) (by
        have hb := hbq b hbB
        omega)
    exact ⟨E, hER⟩
  · exact hlarge

/-- The bounded successor-transversal branch now yields an arbitrarily large
rooted matching in the *original predecessor order*.  The root has fewer
than `k+1` vertices, uniformly in the matching size.

This is the usable output of rank descent for strong deletion: at the
translated predecessor target `n-x`, all but the bounded root split into
pairwise-disjoint nonempty petals. -/
theorem recurrentRootedPredecessorMatchings_of_boundedFullTranslateDestroyers
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hfull : HasBoundedFullTranslateDestroyersByAnchor A (k + 1) Q) :
    ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A → ∀ r L,
      ∃ n T q a x R M,
        L ≤ a ∧ q ∈ Q ∧ a ∈ A ∧ n = q + a ∧
        (∀ y ∈ T, y ∈ A) ∧ Disjoint T F ∧ T.Nonempty ∧
        DestroysAt
          (additiveSupportFamily A (k + 2)) (T : Set ℕ) n ∧
        x ∈ T ∧ x ≤ n ∧
        R.card < k + 1 ∧
        M ⊆ additiveSupportFamily A (k + 1) (n - x) ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ D ∈ M, E ≠ D →
          Disjoint (E \ R) (D \ R) := by
  intro F hFA r L
  obtain ⟨n, T, q, a, x, haLower, hqQ, haA, hnqa,
      hTA, hTF, hTnonempty, hdestroy, hxT, hxn, hxlarge⟩ :=
    recurrentLargeSupportStars_of_boundedFullTranslateDestroyers
      hbasis hfull F hFA
        (additiveRootedMatchingBound (k + 1) r) L
  obtain ⟨R, M, hRcard, hMsub, hMcard, hMroot,
      hMnonempty, hMmatching⟩ :=
    additiveSupportSubfamily_has_large_rootedMatching
      (A := A) (h := k + 1) (r := r) (m := n - x)
      (𝒢 := additiveSupportFamily A (k + 1) (n - x))
      Finset.Subset.rfl (Nat.le_of_lt hxlarge)
  exact ⟨n, T, q, a, x, R, M,
    haLower, hqQ, haA, hnqa, hTA, hTF, hTnonempty,
    hdestroy, hxT, hxn, hRcard, hMsub, hMcard, hMroot,
    hMnonempty, hMmatching⟩

/-- Direct bounded-moving form of the rooted predecessor matching theorem. -/
theorem recurrentRootedPredecessorMatchings_of_boundedMovingOnFiniteTranslates
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hQ : Q.Nonempty)
    (hmoving :
      HasBoundedMovingOutsideTransversalsOnFiniteTranslates
        (additiveSupportFamily A (k + 2)) A Q) :
    ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A → ∀ r L,
      ∃ n T q a x R M,
        L ≤ a ∧ q ∈ Q ∧ a ∈ A ∧ n = q + a ∧
        (∀ y ∈ T, y ∈ A) ∧ Disjoint T F ∧ T.Nonempty ∧
        DestroysAt
          (additiveSupportFamily A (k + 2)) (T : Set ℕ) n ∧
        x ∈ T ∧ x ≤ n ∧
        R.card < k + 1 ∧
        M ⊆ additiveSupportFamily A (k + 1) (n - x) ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ D ∈ M, E ≠ D →
          Disjoint (E \ R) (D \ R) :=
  recurrentRootedPredecessorMatchings_of_boundedFullTranslateDestroyers
    hbasis
    (boundedFullTranslateDestroyersByAnchor_of_boundedMovingOnFiniteTranslates
      hbasis hQ hmoving)

/-- Exact synchronization fork with a finite deletion prefix.  A genuine
common root is either disjoint from the prefix, or one old prefix element is
common to every support.  In the latter case removing that summand preserves
the full cardinality while lowering the representation order by one.

This is the mechanism needed to consume recurrent old-prefix root hits:
they cannot stall the rooted matching construction without paying one unit
of additive rank. -/
theorem rootedMatching_disjointPrefix_or_descends
    {A : Set ℕ} {k m : ℕ}
    {R F : Finset ℕ} {M : Finset (Finset ℕ)}
    (hMsub : M ⊆ additiveSupportFamily A (k + 1) m)
    (hMnonempty : M.Nonempty)
    (hMroot : ∀ E ∈ M, R ⊆ E) :
    Disjoint R F ∨
      ∃ d ∈ R, d ∈ F ∧ d ∈ A ∧ d ≤ m ∧
        ∃ ℋ : Finset (Finset ℕ),
          ℋ ⊆ additiveSupportFamily A k (m - d) ∧
          ℋ.card = M.card := by
  classical
  by_cases hRF : Disjoint R F
  · exact Or.inl hRF
  · right
    obtain ⟨d, hdR, hdF⟩ := Finset.not_disjoint_iff.mp hRF
    obtain ⟨E, hEM⟩ := hMnonempty
    have hdE : d ∈ E := hMroot E hEM hdR
    have hER := hMsub hEM
    have hdA : d ∈ A :=
      additiveSupportFamily_supportsIn
        A (k + 1) m E hER d hdE
    have hdm : d ≤ m :=
      additiveSupportFamily_supportsBounded
        A (k + 1) m E hER d hdE
    obtain ⟨ℋ, hℋsub, hℋcard⟩ :=
      additiveSupportStar_descends_card hMsub
        (fun G hGM => hMroot G hGM hdR)
    exact ⟨d, hdR, hdF, hdA, hdm, ℋ, hℋsub, hℋcard⟩

/-- A deletion prefix cannot destroy more pairwise-disjoint petals than it
has vertices while remaining disjoint from their common root.

This is the finite repair/growth comparison.  If the root avoids `D`, each
destroyed support must spend a distinct vertex of `D` on its petal. -/
theorem card_rootedMatching_le_destroyer_of_rootDisjoint
    {A : Set ℕ} {k m : ℕ}
    {R D : Finset ℕ} {M : Finset (Finset ℕ)}
    (hdestroy :
      DestroysAt
        (additiveSupportFamily A (k + 1)) (D : Set ℕ) m)
    (hMsub : M ⊆ additiveSupportFamily A (k + 1) m)
    (hrootDisjoint : Disjoint R D)
    (hMmatching :
      ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
        Disjoint (E \ R) (G \ R)) :
    M.card ≤ D.card := by
  classical
  by_contra hnotle
  have hlarge : D.card < M.card := Nat.lt_of_not_ge hnotle
  have hhit :
      ∀ E ∈ M, ¬ Disjoint (E : Set ℕ) (D : Set ℕ) →
        ∃ x ∈ D, x ∈ E \ R := by
    intro E _hEM hED
    obtain ⟨x, hxE, hxD⟩ := Set.not_disjoint_iff.mp hED
    refine ⟨x, Finset.mem_coe.mp hxD,
      Finset.mem_sdiff.mpr ⟨Finset.mem_coe.mp hxE, ?_⟩⟩
    intro hxR
    exact Finset.disjoint_left.mp hrootDisjoint
      hxR (Finset.mem_coe.mp hxD)
  obtain ⟨E, hEM, hED⟩ :=
    exists_surviving_support hMmatching hhit hlarge
  exact (hdestroy E (hMsub hEM)) hED

/-- A selector which destroys a rooted matching larger than the number of
support-active block coordinates must choose a point of the common root.

The selector contributes at most one relevant point per active block.  If it
missed the root, those points would have to hit distinct petals, contradicting
the cardinal inequality. -/
theorem destroyingSelector_meets_root_of_largeRootedMatching
    {A : Set ℕ} {k q : ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (s : BlockSelector F)
    {R : Finset ℕ} {M : Finset (Finset ℕ)}
    (hdestroy :
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet s) q)
    (hMsub : M ⊆ additiveSupportFamily A (k + 1) q)
    (hMmatching :
      ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
        Disjoint (E \ R) (G \ R))
    (hlarge :
      ((supportVertices
          (additiveSupportFamily A (k + 1)) q).image
            (blockIndex P)).card < M.card) :
    ¬ Disjoint (R : Set ℕ) (selectedSet s) := by
  intro hrootSelected
  obtain ⟨D, hDselected, hDcard, hDdestroy⟩ :=
    exists_activeBlockSelectedDestroyer_of_destroysAt
      P s hdestroy
  have hrootD : Disjoint R D := by
    rw [Finset.disjoint_left]
    intro x hxR hxD
    exact Set.disjoint_left.mp hrootSelected
      (Finset.mem_coe.mpr hxR)
      (hDselected (Finset.mem_coe.mpr hxD))
  have hMD :=
    card_rootedMatching_le_destroyer_of_rootDisjoint
      hDdestroy hMsub hrootD hMmatching
  omega

/-- Finite certificate root barrier.

Suppose every certificate target carries a rooted matching with more petals
than support-active selector coordinates.  The preceding theorem says that
every selector which destroys that target must choose one of its root points.
Consequently every block selector meets the finite union of all roots.  A
finite union can meet every selector only by containing one whole partition
block.

This converts certificate destruction into a rigid finite obstruction: the
counterexample must cover an entire block by common summands. -/
theorem finiteCertificate_roots_contain_partitionBlock
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (selectedSet s) q)
    (root : ℕ → Finset ℕ)
    (matching : ℕ → Finset (Finset ℕ))
    (hmatching : ∀ q ∈ Q,
      matching q ⊆ additiveSupportFamily A (k + 1) q ∧
      ((supportVertices
          (additiveSupportFamily A (k + 1)) q).image
            (blockIndex P)).card < (matching q).card ∧
      ∀ E ∈ matching q, ∀ G ∈ matching q, E ≠ G →
        Disjoint (E \ root q) (G \ root q)) :
    ∃ j, F j ⊆ Q.biUnion root := by
  classical
  let U : Finset ℕ := Q.biUnion root
  by_contra hnoBlock
  push Not at hnoBlock
  have houtside : ∀ j, (F j \ U).Nonempty := by
    intro j
    by_contra hempty
    apply hnoBlock j
    intro x hxF
    by_contra hxU
    exact hempty
      ⟨x, Finset.mem_sdiff.mpr ⟨hxF, hxU⟩⟩
  let s : BlockSelector F := fun j =>
    ⟨(houtside j).choose,
      (Finset.mem_sdiff.mp (houtside j).choose_spec).1⟩
  have hUselected :
      Disjoint (U : Set ℕ) (selectedSet s) := by
    rw [Set.disjoint_left]
    intro x hxU hxSelected
    obtain ⟨j, hjx⟩ := hxSelected
    have hxOutside :
        x = (houtside j).choose := hjx.symm
    exact (Finset.mem_sdiff.mp (houtside j).choose_spec).2
      (hxOutside ▸ Finset.mem_coe.mp hxU)
  obtain ⟨q, hqQ, hqDestroy⟩ := hcert s
  have hrootSelected :
      ¬ Disjoint ((root q : Finset ℕ) : Set ℕ) (selectedSet s) :=
    destroyingSelector_meets_root_of_largeRootedMatching
      P s hqDestroy
        (hmatching q hqQ).1
        (hmatching q hqQ).2.2
        (hmatching q hqQ).2.1
  apply hrootSelected
  apply Set.disjoint_of_subset_left
  · intro x hxRoot
    apply Finset.mem_coe.mpr
    exact Finset.mem_biUnion.mpr
      ⟨q, hqQ, Finset.mem_coe.mp hxRoot⟩
  · exact hUselected

/-- A full-block root barrier is already a cardinal-preserving
lower-order representation barrier.

Every point `x` of the covered block belongs to the common root at some
certificate target `q`.  Removing `x` from every support in that target's
rooted matching gives the same number of distinct order-`k` supports at the
coherent difference `q-x`.  In particular, the strict comparison with the
support-active block coordinates survives the descent unchanged.

This is the direct arithmetic content of the root barrier: it does not merely
say that a finite certificate has a special shape; it produces large
lower-order representation families at differences owned by the covered
block points. -/
theorem fullBlockRootBarrier_descends_to_differenceFamilies
    {A : Set ℕ} {k j : ℕ} {Q : Finset ℕ}
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (root : ℕ → Finset ℕ)
    (matching : ℕ → Finset (Finset ℕ))
    (hmatching : ∀ q ∈ Q,
      matching q ⊆ additiveSupportFamily A (k + 1) q ∧
      ((supportVertices
          (additiveSupportFamily A (k + 1)) q).image
            (blockIndex P)).card < (matching q).card ∧
      ∀ E ∈ matching q, root q ⊆ E)
    (hblock : F j ⊆ Q.biUnion root) :
    ∀ x ∈ F j, ∃ q ∈ Q,
      x ∈ root q ∧ x ∈ A ∧ x ≤ q ∧
      ∃ lower : Finset (Finset ℕ),
        lower ⊆ additiveSupportFamily A k (q - x) ∧
        lower.card = (matching q).card ∧
        ((supportVertices
            (additiveSupportFamily A (k + 1)) q).image
              (blockIndex P)).card < lower.card := by
  classical
  intro x hxF
  obtain ⟨q, hqQ, hxRoot⟩ :=
    Finset.mem_biUnion.mp (hblock hxF)
  have hMpos : 0 < (matching q).card :=
    lt_of_le_of_lt (Nat.zero_le _)
      (hmatching q hqQ).2.1
  obtain ⟨E, hEM⟩ :=
    Finset.card_pos.mp hMpos
  have hxE : x ∈ E :=
    (hmatching q hqQ).2.2 E hEM hxRoot
  have hER : E ∈ additiveSupportFamily A (k + 1) q :=
    (hmatching q hqQ).1 hEM
  have hxA : x ∈ A :=
    additiveSupportFamily_supportsIn
      A (k + 1) q E hER x hxE
  have hxq : x ≤ q :=
    additiveSupportFamily_supportsBounded
      A (k + 1) q E hER x hxE
  obtain ⟨lower, hlowerSub, hlowerCard⟩ :=
    additiveSupportStar_descends_card
      (hmatching q hqQ).1
      (fun G hGM => (hmatching q hqQ).2.2 G hGM hxRoot)
  refine ⟨q, hqQ, hxRoot, hxA, hxq, lower,
    hlowerSub, hlowerCard, ?_⟩
  simpa [hlowerCard] using (hmatching q hqQ).2.1

/-- A large rooted predecessor matching forces the translate anchor to lie
inside every smaller successor destroyer whose root is protected.

If the anchor `a` were absent from `T`, successor-transversal descent would
turn `T` into a destroyer of the predecessor target `q`.  Since `T` also
misses the common root, its points must hit distinct petals, so the rooted
matching has cardinality at most `T.card`.

This is the direct cardinal obstruction behind the internal-anchor branch;
unlike an informal lifting argument, it retains the exact quantifier
dependence on the translate label `q`. -/
theorem card_rootedMatching_le_successorDestroyer_of_anchorOutside
    {A : Set ℕ} {k q a : ℕ}
    {R T : Finset ℕ} {M : Finset (Finset ℕ)}
    (hdestroy :
      DestroysAt
        (additiveSupportFamily A (k + 2)) (T : Set ℕ) (q + a))
    (haA : a ∈ A)
    (haT : a ∉ T)
    (hMsub : M ⊆ additiveSupportFamily A (k + 1) q)
    (hrootDisjoint : Disjoint R T)
    (hMmatching :
      ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
        Disjoint (E \ R) (G \ R)) :
    M.card ≤ T.card := by
  have hdescend :
      DestroysAt
        (additiveSupportFamily A (k + 1))
        (T : Set ℕ) ((q + a) - a) :=
    additiveSuccessorTransversalsDescend A (k + 1)
      T (q + a) hdestroy a haA haT (by omega)
  have hdestroysQ :
      DestroysAt
        (additiveSupportFamily A (k + 1))
        (T : Set ℕ) q := by
    simpa using hdescend
  exact card_rootedMatching_le_destroyer_of_rootDisjoint
    hdestroysQ hMsub hrootDisjoint hMmatching

/-- Contrapositive form of
`card_rootedMatching_le_successorDestroyer_of_anchorOutside`: whenever the
protected rooted matching is larger than the successor destroyer, the
translate anchor is necessarily an internal point of that destroyer. -/
theorem anchor_mem_successorDestroyer_of_large_rootedMatching
    {A : Set ℕ} {k q a : ℕ}
    {R T : Finset ℕ} {M : Finset (Finset ℕ)}
    (hdestroy :
      DestroysAt
        (additiveSupportFamily A (k + 2)) (T : Set ℕ) (q + a))
    (haA : a ∈ A)
    (hMsub : M ⊆ additiveSupportFamily A (k + 1) q)
    (hrootDisjoint : Disjoint R T)
    (hMmatching :
      ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
        Disjoint (E \ R) (G \ R))
    (hlarge : T.card < M.card) :
    a ∈ T := by
  by_contra haT
  have hle :=
    card_rootedMatching_le_successorDestroyer_of_anchorOutside
      hdestroy haA haT hMsub hrootDisjoint hMmatching
  omega

/-- If a rooted matching is larger than a finite deletion prefix which
destroys its target, the root must meet that prefix.  Removing such a common
summand preserves the entire matching at the coherent difference `m - d`
and lowers the representation order by one.

This is the rigorous finite-prefix/difference composition: either one petal
repairs the target, or matching growth forces rank descent through a deleted
summand. -/
theorem large_destroyedRootedMatching_descends_through_prefix
    {A : Set ℕ} {k m : ℕ}
    {R D : Finset ℕ} {M : Finset (Finset ℕ)}
    (hdestroy :
      DestroysAt
        (additiveSupportFamily A (k + 1)) (D : Set ℕ) m)
    (hMsub : M ⊆ additiveSupportFamily A (k + 1) m)
    (hMroot : ∀ E ∈ M, R ⊆ E)
    (hMmatching :
      ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
        Disjoint (E \ R) (G \ R))
    (hlarge : D.card < M.card) :
    ∃ d ∈ R, d ∈ D ∧ d ∈ A ∧ d ≤ m ∧
      ∃ ℋ : Finset (Finset ℕ),
        ℋ ⊆ additiveSupportFamily A k (m - d) ∧
        ℋ.card = M.card := by
  have hMnonempty : M.Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain hrootDisjoint | hdescend :=
    rootedMatching_disjointPrefix_or_descends
      hMsub hMnonempty hMroot
  · have hle :=
      card_rootedMatching_le_destroyer_of_rootDisjoint
        hdestroy hMsub hrootDisjoint hMmatching
    omega
  · exact hdescend

/-- Uniform finite-prefix composition at the *successor of an already exact
basis order*, with no gap alternative.

At every sufficiently late order-`k+1` target there is a rooted matching
larger than the prescribed destroyer bound by
`eventually_successorExactRootedMatching`.  A destroyer of size at most
`r` cannot hit distinct petals while missing the root, so it contains a
common root point `d`.  Removing `d` from the whole rooted matching gives
more than `r` distinct order-`k` supports at the coherent difference
`n-d`.

Unlike `eventually_boundedDestroyer_forces_largeDifferenceFamily_or_lowerGap`,
this theorem uses the lower-order basis hypothesis and therefore has no
arithmetic escape horn. -/
theorem IsExactTupleAsymptoticBasis.eventually_boundedSuccessorDestroyer_forces_largeDifferenceFamily
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k) :
    ∀ r, ∃ N, ∀ D : Finset ℕ, D.card ≤ r →
      ∀ n, N ≤ n →
        DestroysAt
            (additiveSupportFamily A (k + 1)) (D : Set ℕ) n →
          ∃ d ∈ D, d ∈ A ∧ d ≤ n ∧
            ∃ ℋ : Finset (Finset ℕ),
              ℋ ⊆ additiveSupportFamily A k (n - d) ∧
              r < ℋ.card := by
  intro r
  obtain ⟨N, hN⟩ :=
    hbasis.eventually_successorExactRootedMatching r
  refine ⟨N, ?_⟩
  intro D hDcard n hn hdestroy
  obtain ⟨R, M, _hRcard, hMsub, hMlarge, hMroot,
      _hMnonempty, hMmatching⟩ :=
    hN n hn
  have hDlarge : D.card < M.card :=
    lt_of_le_of_lt hDcard hMlarge
  obtain ⟨d, _hdR, hdD, hdA, hdn, ℋ, hℋsub, hℋcard⟩ :=
    large_destroyedRootedMatching_descends_through_prefix
      hdestroy hMsub hMroot hMmatching hDlarge
  refine ⟨d, hdD, hdA, hdn, ℋ, hℋsub, ?_⟩
  simpa [hℋcard] using hMlarge

/-- Eventual growth-or-gap form of finite-prefix/difference composition.

For an exact order-`k+1` basis and a fixed finite deletion `D`, every
sufficiently late target destroyed by `D` has one of two concrete defects:

* a deleted common summand `d` exposes more than `|D|` lower-order supports
  of the coherent difference `n-d`; or
* a basis predecessor `n-b` is a genuine order-`k` gap.

Thus a fixed finite prefix cannot indefinitely hide behind isolated
represented differences: it must force matching growth at those differences
or produce the lower-order gap needed for the other branch of the attack. -/
theorem IsExactTupleAsymptoticBasis.finiteDestroyer_forces_largeDifferenceFamily_or_lowerGap
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1)) :
    ∀ D : Finset ℕ, ∃ N, ∀ n, N ≤ n →
      DestroysAt
          (additiveSupportFamily A (k + 1)) (D : Set ℕ) n →
        (∃ d ∈ D, d ∈ A ∧ d ≤ n ∧
          ∃ ℋ : Finset (Finset ℕ),
            ℋ ⊆ additiveSupportFamily A k (n - d) ∧
            D.card < ℋ.card) ∨
        ∃ b, b ∈ A ∧ b ≤ n ∧
          additiveSupportFamily A k (n - b) = ∅ := by
  intro D
  obtain ⟨N, hN⟩ :=
    hbasis.eventually_exactRootedMatching_or_lowerGap D.card
  refine ⟨N, ?_⟩
  intro n hn hdestroy
  obtain ⟨R, M, _hRcard, hMsub, hlarge, hMroot,
      _hMnonempty, hMmatching⟩ | hgap := hN n hn
  · left
    obtain ⟨d, _hdR, hdD, hdA, hdn, ℋ, hℋsub, hℋcard⟩ :=
      large_destroyedRootedMatching_descends_through_prefix
        hdestroy hMsub hMroot hMmatching hlarge
    refine ⟨d, hdD, hdA, hdn, ℋ, hℋsub, ?_⟩
    simpa [hℋcard] using hlarge
  · exact Or.inr hgap

/-- Uniform-cardinality form of the finite-prefix composition.  The late
threshold depends only on the allowed size `r`, not on the actual vertices of
the destroyer.  This is the form that can be scheduled before a moving
certificate and its selector are known. -/
theorem IsExactTupleAsymptoticBasis.eventually_boundedDestroyer_forces_largeDifferenceFamily_or_lowerGap
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1)) :
    ∀ r, ∃ N, ∀ D : Finset ℕ, D.card ≤ r →
      ∀ n, N ≤ n →
        DestroysAt
            (additiveSupportFamily A (k + 1)) (D : Set ℕ) n →
          (∃ d ∈ D, d ∈ A ∧ d ≤ n ∧
            ∃ ℋ : Finset (Finset ℕ),
              ℋ ⊆ additiveSupportFamily A k (n - d) ∧
              r < ℋ.card) ∨
          ∃ b, b ∈ A ∧ b ≤ n ∧
            additiveSupportFamily A k (n - b) = ∅ := by
  intro r
  obtain ⟨N, hN⟩ :=
    hbasis.eventually_exactRootedMatching_or_lowerGap r
  refine ⟨N, ?_⟩
  intro D hDcard n hn hdestroy
  obtain ⟨R, M, _hRcard, hMsub, hlarge, hMroot,
      _hMnonempty, hMmatching⟩ | hgap := hN n hn
  · left
    have hDlarge : D.card < M.card :=
      lt_of_le_of_lt hDcard hlarge
    obtain ⟨d, _hdR, hdD, hdA, hdn, ℋ, hℋsub, hℋcard⟩ :=
      large_destroyedRootedMatching_descends_through_prefix
        hdestroy hMsub hMroot hMmatching hDlarge
    refine ⟨d, hdD, hdA, hdn, ℋ, hℋsub, ?_⟩
    simpa [hℋcard] using hlarge
  · exact Or.inr hgap

/-- Uniform finite-prefix composition whose lower-gap point avoids an
arbitrary protected set of bounded cardinality.

Both the destroyer and protected-set budgets are fixed before their vertices
are known.  The protected rooted/gap theorem supplies the same large
difference family as before, or a gap point outside the protected set. -/
theorem IsExactTupleAsymptoticBasis.eventually_boundedDestroyer_forces_largeDifferenceFamily_or_lowerGap_avoiding
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1)) :
    ∀ r w, ∃ N, ∀ W : Finset ℕ, W.card ≤ w →
      ∀ D : Finset ℕ, D.card ≤ r →
        ∀ n, N ≤ n →
          DestroysAt
              (additiveSupportFamily A (k + 1)) (D : Set ℕ) n →
            (∃ d ∈ D, d ∈ A ∧ d ≤ n ∧
              ∃ ℋ : Finset (Finset ℕ),
                ℋ ⊆ additiveSupportFamily A k (n - d) ∧
                r < ℋ.card) ∨
            ∃ b, b ∈ A ∧ b ∉ W ∧ b ≤ n ∧
              additiveSupportFamily A k (n - b) = ∅ := by
  intro r w
  obtain ⟨N, hN⟩ :=
    hbasis.eventually_exactRootedMatching_or_lowerGap_avoiding r w
  refine ⟨N, ?_⟩
  intro W hWcard D hDcard n hn hdestroy
  obtain ⟨R, M, _hRcard, hMsub, hlarge, hMroot,
      _hMnonempty, hMmatching⟩ | hgap :=
    hN W hWcard n hn
  · left
    have hDlarge : D.card < M.card :=
      lt_of_le_of_lt hDcard hlarge
    obtain ⟨d, _hdR, hdD, hdA, hdn, ℋ, hℋsub, hℋcard⟩ :=
      large_destroyedRootedMatching_descends_through_prefix
        hdestroy hMsub hMroot hMmatching hDlarge
    refine ⟨d, hdD, hdA, hdn, ℋ, hℋsub, ?_⟩
    simpa [hℋcard] using hlarge
  · exact Or.inr hgap

/-- Eventual certificate-safe finite-prefix composition.

If current-order rooted matching growth is absent, the intrinsic locked
prefix has a target-independent cardinal bound.  Genuine destruction by
that prefix feeds directly into uniform finite-prefix/difference
composition, while non-destruction gives strict upper-rank certificate
descent.  The only remaining arithmetic horn is now an actual lower-order
gap point; every represented-difference horn is normalized to a rooted
matching. -/
theorem IsExactTupleAsymptoticBasis.eventually_lockedPrefix_matching_or_gap_or_rankGrowthDescent
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (r : ℕ) :
    ∃ N, ∀ Q : Finset ℕ, ∀ q, N ≤ q → ∀ s : BlockSelector F,
      q ∈ Q →
      (∀ t : BlockSelector F, ∃ u ∈ Q,
        DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet t) u) →
      (∀ u ∈ Q, q < u →
        ¬ DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet s) u) →
      (∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
          R.card < k + 1 ∧
          M ⊆ additiveSupportFamily A (k + 1) q ∧
          r < M.card ∧
          (∀ E ∈ M, R ⊆ E) ∧
          (∀ E ∈ M, (E \ R).Nonempty) ∧
          ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
            Disjoint (E \ R) (G \ R)) ∨
        (∃ d, d ∈ A ∧ d ≤ q ∧
          ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
            R.card < k ∧
            M ⊆ additiveSupportFamily A k (q - d) ∧
            r < M.card ∧
            (∀ E ∈ M, R ⊆ E) ∧
            (∀ E ∈ M, (E \ R).Nonempty) ∧
            ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
              Disjoint (E \ R) (G \ R)) ∨
        (∃ t : BlockSelector F, ∃ u ∈ Q, u < q ∧
          (Q.filter fun v => q < v).card <
            (Q.filter fun v => u < v).card ∧
          DestroysAt
            (additiveSupportFamily A (k + 1))
            (selectedSet t) u ∧
          ∀ v ∈ Q, u < v →
            ¬ DestroysAt
              (additiveSupportFamily A (k + 1))
              (selectedSet t) v) ∨
        ∃ b, b ∈ A ∧ b ≤ q ∧
          additiveSupportFamily A k (q - b) = ∅ := by
  classical
  let B := lockedPrefixCompositionBound k r
  obtain ⟨N, hN⟩ :=
    hbasis.eventually_boundedDestroyer_forces_largeDifferenceFamily_or_lowerGap B
  refine ⟨N, ?_⟩
  intro Q q hn s hqQ hcert hlarger
  by_cases hcurrent :
      ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
        R.card < k + 1 ∧
        M ⊆ additiveSupportFamily A (k + 1) q ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
          Disjoint (E \ R) (G \ R)
  · exact Or.inl hcurrent
  have hfamilySmall :
      (additiveSupportFamily A (k + 1) q).card <
        additiveRootedMatchingBound (k + 1) r := by
    by_contra hnot
    apply hcurrent
    exact additiveSupportSubfamily_has_large_rootedMatching
      (k + 1) r q (additiveSupportFamily A (k + 1) q)
      Finset.Subset.rfl (Nat.le_of_not_gt hnot)
  have hvertices :
      (supportVertices (additiveSupportFamily A (k + 1)) q).card ≤
        (k + 1) * additiveRootedMatchingBound (k + 1) r := by
    calc
      (supportVertices
          (additiveSupportFamily A (k + 1)) q).card ≤
          (k + 1) *
            (additiveSupportFamily A (k + 1) q).card := by
        exact biUnion_card_le_of_edge_card_le
          (H := additiveSupportFamily A (k + 1) q)
          (M := additiveSupportFamily A (k + 1) q)
          (by simp) (fun E hE =>
            additiveSupportFamily_cardAtMost A (k + 1) q E hE)
      _ ≤ (k + 1) *
          additiveRootedMatchingBound (k + 1) r :=
        Nat.mul_le_mul_left (k + 1) (Nat.le_of_lt hfamilySmall)
  let completionNeed :=
    (k + 1) * (Q.filter fun u => q < u).card + (k + 1)
  let J := deficientRepairHitBlocks P s
    (additiveSupportFamily A (k + 1)) q 0 completionNeed
  let L : Finset ℕ := J.image fun j => (s j).1
  have hstep :
      (L.card ≤
          (supportVertices
            (additiveSupportFamily A (k + 1)) q).card ∧
        DestroysAt
          (additiveSupportFamily A (k + 1)) (L : Set ℕ) q) ∨
        ∃ t : BlockSelector F, ∃ u ∈ Q, u < q ∧
          (Q.filter fun v => q < v).card <
            (Q.filter fun v => u < v).card ∧
          DestroysAt
            (additiveSupportFamily A (k + 1))
            (selectedSet t) u ∧
          ∀ v ∈ Q, u < v →
            ¬ DestroysAt
              (additiveSupportFamily A (k + 1))
              (selectedSet t) v := by
    simpa only [L, J, completionNeed] using
      blockAligned_intrinsicLockedPrefix_destruction_or_rankGrowthDescent
        P s hqQ hcert hlarger
  obtain ⟨hLcard, hLdestroy⟩ | hdescent := hstep
  · have hLB : L.card ≤ B :=
      (hLcard.trans hvertices).trans (Nat.le_max_left _ _)
    obtain hgrowth | hgap := hN L hLB q hn hLdestroy
    · right
      left
      obtain ⟨d, _hdL, hdA, hdq, ℋ, hℋsub, hBℋ⟩ := hgrowth
      refine ⟨d, hdA, hdq, ?_⟩
      obtain ⟨R, M, hRcard, hMsub, hMcard, hMroot,
          hMnonempty, hMdisjoint⟩ :=
        additiveSupportSubfamily_has_large_rootedMatching
          k r (q - d) ℋ hℋsub
          (le_trans (Nat.le_max_right _ _) (Nat.le_of_lt hBℋ))
      exact ⟨R, M, hRcard, hMsub.trans hℋsub, hMcard,
        hMroot, hMnonempty, hMdisjoint⟩
    · exact Or.inr (Or.inr (Or.inr hgap))
  · exact Or.inr (Or.inr (Or.inl hdescent))

/-- Protected-set strengthening of the locked-prefix composition.

The predecessor-gap repair point is chosen outside an arbitrary finite set
`W` of bounded cardinality.  Thus certificate migration can be iterated
while keeping every previously locked repair point and support vertex
untouched. -/
theorem IsExactTupleAsymptoticBasis.eventually_lockedPrefix_matching_or_freshGap_or_rankGrowthDescent
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (r w : ℕ) :
    ∃ N, ∀ W : Finset ℕ, W.card ≤ w →
      ∀ Q : Finset ℕ, ∀ q, N ≤ q → ∀ s : BlockSelector F,
      q ∈ Q →
      (∀ t : BlockSelector F, ∃ u ∈ Q,
        DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet t) u) →
      (∀ u ∈ Q, q < u →
        ¬ DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet s) u) →
      (∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
          R.card < k + 1 ∧
          M ⊆ additiveSupportFamily A (k + 1) q ∧
          r < M.card ∧
          (∀ E ∈ M, R ⊆ E) ∧
          (∀ E ∈ M, (E \ R).Nonempty) ∧
          ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
            Disjoint (E \ R) (G \ R)) ∨
        (∃ d, d ∈ A ∧ d ≤ q ∧
          ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
            R.card < k ∧
            M ⊆ additiveSupportFamily A k (q - d) ∧
            r < M.card ∧
            (∀ E ∈ M, R ⊆ E) ∧
            (∀ E ∈ M, (E \ R).Nonempty) ∧
            ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
              Disjoint (E \ R) (G \ R)) ∨
        (∃ t : BlockSelector F, ∃ u ∈ Q, u < q ∧
          (Q.filter fun v => q < v).card <
            (Q.filter fun v => u < v).card ∧
          DestroysAt
            (additiveSupportFamily A (k + 1))
            (selectedSet t) u ∧
          ∀ v ∈ Q, u < v →
            ¬ DestroysAt
              (additiveSupportFamily A (k + 1))
              (selectedSet t) v) ∨
        ∃ b, b ∈ A ∧ b ∉ W ∧ b ≤ q ∧
          additiveSupportFamily A k (q - b) = ∅ := by
  classical
  let B := lockedPrefixCompositionBound k r
  obtain ⟨N, hN⟩ :=
    hbasis.eventually_boundedDestroyer_forces_largeDifferenceFamily_or_lowerGap_avoiding
      B w
  refine ⟨N, ?_⟩
  intro W hWcard Q q hn s hqQ hcert hlarger
  by_cases hcurrent :
      ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
        R.card < k + 1 ∧
        M ⊆ additiveSupportFamily A (k + 1) q ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
          Disjoint (E \ R) (G \ R)
  · exact Or.inl hcurrent
  have hfamilySmall :
      (additiveSupportFamily A (k + 1) q).card <
        additiveRootedMatchingBound (k + 1) r := by
    by_contra hnot
    apply hcurrent
    exact additiveSupportSubfamily_has_large_rootedMatching
      (k + 1) r q (additiveSupportFamily A (k + 1) q)
      Finset.Subset.rfl (Nat.le_of_not_gt hnot)
  have hvertices :
      (supportVertices (additiveSupportFamily A (k + 1)) q).card ≤
        (k + 1) * additiveRootedMatchingBound (k + 1) r := by
    calc
      (supportVertices
          (additiveSupportFamily A (k + 1)) q).card ≤
          (k + 1) *
            (additiveSupportFamily A (k + 1) q).card := by
        exact biUnion_card_le_of_edge_card_le
          (H := additiveSupportFamily A (k + 1) q)
          (M := additiveSupportFamily A (k + 1) q)
          (by simp) (fun E hE =>
            additiveSupportFamily_cardAtMost A (k + 1) q E hE)
      _ ≤ (k + 1) *
          additiveRootedMatchingBound (k + 1) r :=
        Nat.mul_le_mul_left (k + 1) (Nat.le_of_lt hfamilySmall)
  let completionNeed :=
    (k + 1) * (Q.filter fun u => q < u).card + (k + 1)
  let J := deficientRepairHitBlocks P s
    (additiveSupportFamily A (k + 1)) q 0 completionNeed
  let L : Finset ℕ := J.image fun j => (s j).1
  have hstep :
      (L.card ≤
          (supportVertices
            (additiveSupportFamily A (k + 1)) q).card ∧
        DestroysAt
          (additiveSupportFamily A (k + 1)) (L : Set ℕ) q) ∨
        ∃ t : BlockSelector F, ∃ u ∈ Q, u < q ∧
          (Q.filter fun v => q < v).card <
            (Q.filter fun v => u < v).card ∧
          DestroysAt
            (additiveSupportFamily A (k + 1))
            (selectedSet t) u ∧
          ∀ v ∈ Q, u < v →
            ¬ DestroysAt
              (additiveSupportFamily A (k + 1))
              (selectedSet t) v := by
    simpa only [L, J, completionNeed] using
      blockAligned_intrinsicLockedPrefix_destruction_or_rankGrowthDescent
        P s hqQ hcert hlarger
  obtain ⟨hLcard, hLdestroy⟩ | hdescent := hstep
  · have hLB : L.card ≤ B :=
      (hLcard.trans hvertices).trans (Nat.le_max_left _ _)
    obtain hgrowth | hgap :=
      hN W hWcard L hLB q hn hLdestroy
    · right
      left
      obtain ⟨d, _hdL, hdA, hdq, ℋ, hℋsub, hBℋ⟩ := hgrowth
      refine ⟨d, hdA, hdq, ?_⟩
      obtain ⟨R, M, hRcard, hMsub, hMcard, hMroot,
          hMnonempty, hMdisjoint⟩ :=
        additiveSupportSubfamily_has_large_rootedMatching
          k r (q - d) ℋ hℋsub
          (le_trans (Nat.le_max_right _ _) (Nat.le_of_lt hBℋ))
      exact ⟨R, M, hRcard, hMsub.trans hℋsub, hMcard,
        hMroot, hMnonempty, hMdisjoint⟩
    · exact Or.inr (Or.inr (Or.inr hgap))
  · exact Or.inr (Or.inr (Or.inl hdescent))

/-- Gap-free certificate-safe composition at the successor of an exact
basis order.

This is the direct successor-order specialization of
`eventually_lockedPrefix_matching_or_gap_or_rankGrowthDescent`.  The
intrinsic locked-prefix/descent analysis is unchanged, but genuine
destruction by the bounded locked prefix is fed into
`eventually_boundedSuccessorDestroyer_forces_largeDifferenceFamily`.
Because order `k` is already an exact basis, the lower-gap horn is
impossible.  The exhaustive outputs are therefore only current-order
matching growth, coherent predecessor matching growth, or strict
certificate descent. -/
theorem IsExactTupleAsymptoticBasis.eventually_successorLockedPrefix_matching_or_rankGrowthDescent
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (r : ℕ) :
    ∃ N, ∀ Q : Finset ℕ, ∀ q, N ≤ q → ∀ s : BlockSelector F,
      q ∈ Q →
      (∀ t : BlockSelector F, ∃ u ∈ Q,
        DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet t) u) →
      (∀ u ∈ Q, q < u →
        ¬ DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet s) u) →
      (∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
          R.card < k + 1 ∧
          M ⊆ additiveSupportFamily A (k + 1) q ∧
          r < M.card ∧
          (∀ E ∈ M, R ⊆ E) ∧
          (∀ E ∈ M, (E \ R).Nonempty) ∧
          ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
            Disjoint (E \ R) (G \ R)) ∨
        (∃ d, d ∈ A ∧ d ≤ q ∧
          ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
            R.card < k ∧
            M ⊆ additiveSupportFamily A k (q - d) ∧
            r < M.card ∧
            (∀ E ∈ M, R ⊆ E) ∧
            (∀ E ∈ M, (E \ R).Nonempty) ∧
            ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
              Disjoint (E \ R) (G \ R)) ∨
        ∃ t : BlockSelector F, ∃ u ∈ Q, u < q ∧
          (Q.filter fun v => q < v).card <
            (Q.filter fun v => u < v).card ∧
          DestroysAt
            (additiveSupportFamily A (k + 1))
            (selectedSet t) u ∧
          ∀ v ∈ Q, u < v →
            ¬ DestroysAt
              (additiveSupportFamily A (k + 1))
              (selectedSet t) v := by
  classical
  let B := lockedPrefixCompositionBound k r
  obtain ⟨N, hN⟩ :=
    hbasis.eventually_boundedSuccessorDestroyer_forces_largeDifferenceFamily B
  refine ⟨N, ?_⟩
  intro Q q hn s hqQ hcert hlarger
  by_cases hcurrent :
      ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
        R.card < k + 1 ∧
        M ⊆ additiveSupportFamily A (k + 1) q ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
          Disjoint (E \ R) (G \ R)
  · exact Or.inl hcurrent
  have hfamilySmall :
      (additiveSupportFamily A (k + 1) q).card <
        additiveRootedMatchingBound (k + 1) r := by
    by_contra hnot
    apply hcurrent
    exact additiveSupportSubfamily_has_large_rootedMatching
      (k + 1) r q (additiveSupportFamily A (k + 1) q)
      Finset.Subset.rfl (Nat.le_of_not_gt hnot)
  have hvertices :
      (supportVertices (additiveSupportFamily A (k + 1)) q).card ≤
        (k + 1) * additiveRootedMatchingBound (k + 1) r := by
    calc
      (supportVertices
          (additiveSupportFamily A (k + 1)) q).card ≤
          (k + 1) *
            (additiveSupportFamily A (k + 1) q).card := by
        exact biUnion_card_le_of_edge_card_le
          (H := additiveSupportFamily A (k + 1) q)
          (M := additiveSupportFamily A (k + 1) q)
          (by simp) (fun E hE =>
            additiveSupportFamily_cardAtMost A (k + 1) q E hE)
      _ ≤ (k + 1) *
          additiveRootedMatchingBound (k + 1) r :=
        Nat.mul_le_mul_left (k + 1) (Nat.le_of_lt hfamilySmall)
  let completionNeed :=
    (k + 1) * (Q.filter fun u => q < u).card + (k + 1)
  let J := deficientRepairHitBlocks P s
    (additiveSupportFamily A (k + 1)) q 0 completionNeed
  let L : Finset ℕ := J.image fun j => (s j).1
  have hstep :
      (L.card ≤
          (supportVertices
            (additiveSupportFamily A (k + 1)) q).card ∧
        DestroysAt
          (additiveSupportFamily A (k + 1)) (L : Set ℕ) q) ∨
        ∃ t : BlockSelector F, ∃ u ∈ Q, u < q ∧
          (Q.filter fun v => q < v).card <
            (Q.filter fun v => u < v).card ∧
          DestroysAt
            (additiveSupportFamily A (k + 1))
            (selectedSet t) u ∧
          ∀ v ∈ Q, u < v →
            ¬ DestroysAt
              (additiveSupportFamily A (k + 1))
              (selectedSet t) v := by
    simpa only [L, J, completionNeed] using
      blockAligned_intrinsicLockedPrefix_destruction_or_rankGrowthDescent
        P s hqQ hcert hlarger
  obtain ⟨hLcard, hLdestroy⟩ | hdescent := hstep
  · have hLB : L.card ≤ B :=
      (hLcard.trans hvertices).trans (Nat.le_max_left _ _)
    obtain ⟨d, _hdL, hdA, hdq, ℋ, hℋsub, hBℋ⟩ :=
      hN L hLB q hn hLdestroy
    right
    left
    refine ⟨d, hdA, hdq, ?_⟩
    obtain ⟨R, M, hRcard, hMsub, hMcard, hMroot,
        hMnonempty, hMdisjoint⟩ :=
      additiveSupportSubfamily_has_large_rootedMatching
        k r (q - d) ℋ hℋsub
        (le_trans (Nat.le_max_right _ _) (Nat.le_of_lt hBℋ))
    exact ⟨R, M, hRcard, hMsub.trans hℋsub, hMcard,
      hMroot, hMnonempty, hMdisjoint⟩
  · exact Or.inr (Or.inr hdescent)

/-- Successor-order certificate migration terminates with no gap branch.

For a basis of order `k`, consider finite selector certificates for the
desired successor support family of order `k+1`.  Starting at the largest
currently destroyed target, the gap-free locked-prefix theorem gives
current-order rooted matching growth, predecessor rooted matching growth,
or a strictly smaller destroyed target while preserving all larger targets.
Strong induction on that target eliminates the last alternative.

Thus repeated certificate migration at the order relevant to Erdős 881 is
not merely well founded: it must terminate in concrete matching growth. -/
theorem IsExactTupleAsymptoticBasis.eventually_successorFiniteCertificate_matching
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (r : ℕ) :
    ∃ N, ∀ Q : Finset ℕ,
      (∀ q ∈ Q, N ≤ q) →
      (∀ s : BlockSelector F, ∃ q ∈ Q,
        DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet s) q) →
      ((∃ q ∈ Q, ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
          R.card < k + 1 ∧
          M ⊆ additiveSupportFamily A (k + 1) q ∧
          r < M.card ∧
          (∀ E ∈ M, R ⊆ E) ∧
          (∀ E ∈ M, (E \ R).Nonempty) ∧
          ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
            Disjoint (E \ R) (G \ R)) ∨
        ∃ q ∈ Q, ∃ d, d ∈ A ∧ d ≤ q ∧
          ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
            R.card < k ∧
            M ⊆ additiveSupportFamily A k (q - d) ∧
            r < M.card ∧
            (∀ E ∈ M, R ⊆ E) ∧
            (∀ E ∈ M, (E \ R).Nonempty) ∧
            ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
              Disjoint (E \ R) (G \ R)) := by
  classical
  obtain ⟨N, hstep⟩ :=
    hbasis.eventually_successorLockedPrefix_matching_or_rankGrowthDescent
      P r
  refine ⟨N, ?_⟩
  intro Q hQlate hcert
  let Outcome : Prop :=
    ((∃ q ∈ Q, ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
        R.card < k + 1 ∧
        M ⊆ additiveSupportFamily A (k + 1) q ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
          Disjoint (E \ R) (G \ R)) ∨
      ∃ q ∈ Q, ∃ d, d ∈ A ∧ d ≤ q ∧
        ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
          R.card < k ∧
          M ⊆ additiveSupportFamily A k (q - d) ∧
          r < M.card ∧
          (∀ E ∈ M, R ⊆ E) ∧
          (∀ E ∈ M, (E \ R).Nonempty) ∧
          ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
            Disjoint (E \ R) (G \ R))
  have hterminate :
      ∀ q, q ∈ Q → ∀ s : BlockSelector F,
        DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet s) q →
        (∀ v ∈ Q, q < v →
          ¬ DestroysAt
            (additiveSupportFamily A (k + 1)) (selectedSet s) v) →
        Outcome := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
        intro hqQ s hqDestroy hlarger
        obtain hcurrent | hlower | hdescent :=
          hstep Q q (hQlate q hqQ) s hqQ hcert hlarger
        · exact Or.inl ⟨q, hqQ, hcurrent⟩
        · exact Or.inr ⟨q, hqQ, hlower⟩
        · obtain ⟨t, u, huQ, huq, _hrank,
              huDestroy, huLarger⟩ := hdescent
          exact ih u huq huQ t huDestroy huLarger
  let initial : BlockSelector F :=
    fun j => ⟨(P.nonempty j).choose, (P.nonempty j).choose_spec⟩
  obtain ⟨q, hqQ, hqDestroy, hqLarger⟩ :=
    exists_maximalDestroyedCertificateTarget hcert initial
  exact hterminate q hqQ initial hqDestroy hqLarger

/-- Exact-label normalization of gap-free successor certificate migration.

The terminating migration theorem can finish one rank lower at the coherent
difference `q-d`.  This apparent loss is not genuine.  Inserting `d` lifts
the whole lower support family back to the exact successor target `q`, with
cardinality loss at most a factor of two.  Asking migration for more than
twice the rooted-matching threshold therefore forces a large rooted matching
at `q` itself.

Unlike the earlier bounded-certificate normalization, neither the cardinality
of `Q` nor the sizes of the partition blocks are bounded in advance.  Thus
every sufficiently late finite successor certificate contains an exact-label
large delta system. -/
theorem IsExactTupleAsymptoticBasis.eventually_successorFiniteCertificate_exactRootedMatching
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (r : ℕ) :
    ∃ N, ∀ Q : Finset ℕ,
      (∀ q ∈ Q, N ≤ q) →
      (∀ s : BlockSelector F, ∃ q ∈ Q,
        DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet s) q) →
      ∃ q ∈ Q, ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
        R.card < k + 1 ∧
        M ⊆ additiveSupportFamily A (k + 1) q ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
          Disjoint (E \ R) (G \ R) := by
  let threshold := additiveRootedMatchingBound (k + 1) r
  let migrationNeed := max r (2 * threshold)
  obtain ⟨N, hN⟩ :=
    hbasis.eventually_successorFiniteCertificate_matching
      P migrationNeed
  refine ⟨N, ?_⟩
  intro Q hQlate hcert
  obtain ⟨q, hqQ, R, M, hRcard, hMsub, hMlarge,
      hMroot, hMnonempty, hMmatching⟩ |
      ⟨q, hqQ, d, hdA, hdq, R, M, _hRcard, hMsub,
        hMlarge, _hMroot, _hMnonempty, _hMmatching⟩ :=
    hN Q hQlate hcert
  · refine ⟨q, hqQ, R, M, hRcard, hMsub, ?_,
      hMroot, hMnonempty, hMmatching⟩
    exact lt_of_le_of_lt (Nat.le_max_left _ _) hMlarge
  · have hlowerLarge :
        2 * threshold <
          (additiveSupportFamily A k (q - d)).card := by
      exact lt_of_le_of_lt
        (Nat.le_max_right _ _) <|
          lt_of_lt_of_le hMlarge (Finset.card_le_card hMsub)
    have hliftBound :=
      lowerDifferenceSupportFamily_card_le_twice_exact
        (k := k) hdA hdq
    have hthreshold :
        threshold ≤
          (additiveSupportFamily A (k + 1) q).card := by
      omega
    obtain ⟨R', M', hR'card, hM'sub, hM'card, hM'root,
        hM'nonempty, hM'matching⟩ :=
      additiveSupportSubfamily_has_large_rootedMatching
        (k + 1) r q
        (additiveSupportFamily A (k + 1) q)
        Finset.Subset.rfl
        (by simpa only [threshold] using hthreshold)
    exact ⟨q, hqQ, R', M', hR'card, hM'sub, hM'card,
      hM'root, hM'nonempty, hM'matching⟩

/-- A hypothetical negative successor-deletion instance forces exact-label
rooted matching growth inside arbitrarily late finite certificates.

This is the direct counterexample form of the preceding theorem.  Strong
successor deletion supplies the certificate, and gap-free migration plus the
factor-two lift returns the matching at an actual member of that certificate.
There is no bound on the certificate cardinality or on the partition blocks.
-/
theorem successorCounterexample_forces_lateCertificate_exactRootedMatching
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) (k + 1)) :
    ∀ {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F),
      ∀ r L, ∃ Q : Finset ℕ,
        (∀ q ∈ Q, L ≤ q) ∧
        (∀ s : BlockSelector F, ∃ q ∈ Q,
          DestroysAt
            (additiveSupportFamily A (k + 1)) (selectedSet s) q) ∧
        ∃ q ∈ Q, ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
          R.card < k + 1 ∧
          M ⊆ additiveSupportFamily A (k + 1) q ∧
          r < M.card ∧
          (∀ E ∈ M, R ⊆ E) ∧
          (∀ E ∈ M, (E \ R).Nonempty) ∧
          ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
            Disjoint (E \ R) (G \ R) := by
  intro F P r L
  obtain ⟨N, hN⟩ :=
    hbasis.eventually_successorFiniteCertificate_exactRootedMatching
      P r
  obtain ⟨Q, hQlate, hcert⟩ :=
    (finiteBlockCertificates_of_strongInfiniteDeletion
      (strongExactDeletion_of_counterexample hcounter))
      F P (max L N)
  have hLateL : ∀ q ∈ Q, L ≤ q := by
    intro q hqQ
    exact (le_max_left L N).trans (hQlate q hqQ)
  have hLateN : ∀ q ∈ Q, N ≤ q := by
    intro q hqQ
    exact (le_max_right L N).trans (hQlate q hqQ)
  exact ⟨Q, hLateL, hcert, hN Q hLateN hcert⟩

/-- Localized certificate migration terminates.

Start with the maximum certificate target destroyed by an arbitrary
selector.  The localized descent horn above supplies a strictly smaller
destroyed target and, crucially, certifies that every larger certificate
target survives for the new selector.  Strong induction on the target
therefore eliminates migration altogether: on every sufficiently late
finite certificate there is current-order rooted matching growth, coherent
lower-order rooted matching growth, or a genuine lower-order gap. -/
theorem IsExactTupleAsymptoticBasis.eventually_finiteCertificate_matching_or_lowerGap
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (r : ℕ) :
    ∃ N, ∀ Q : Finset ℕ,
      (∀ q ∈ Q, N ≤ q) →
      (∀ s : BlockSelector F, ∃ q ∈ Q,
        DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet s) q) →
      ((∃ q ∈ Q, ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
          R.card < k + 1 ∧
          M ⊆ additiveSupportFamily A (k + 1) q ∧
          r < M.card ∧
          (∀ E ∈ M, R ⊆ E) ∧
          (∀ E ∈ M, (E \ R).Nonempty) ∧
          ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
            Disjoint (E \ R) (G \ R)) ∨
        (∃ q ∈ Q, ∃ d, d ∈ A ∧ d ≤ q ∧
          ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
            R.card < k ∧
            M ⊆ additiveSupportFamily A k (q - d) ∧
            r < M.card ∧
            (∀ E ∈ M, R ⊆ E) ∧
            (∀ E ∈ M, (E \ R).Nonempty) ∧
            ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
              Disjoint (E \ R) (G \ R)) ∨
        ∃ q ∈ Q, ∃ b, b ∈ A ∧ b ≤ q ∧
          additiveSupportFamily A k (q - b) = ∅) := by
  classical
  obtain ⟨N, hstep⟩ :=
    hbasis.eventually_lockedPrefix_matching_or_gap_or_rankGrowthDescent P r
  refine ⟨N, ?_⟩
  intro Q hQlate hcert
  let Outcome : Prop :=
    ((∃ q ∈ Q, ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
        R.card < k + 1 ∧
        M ⊆ additiveSupportFamily A (k + 1) q ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
          Disjoint (E \ R) (G \ R)) ∨
      (∃ q ∈ Q, ∃ d, d ∈ A ∧ d ≤ q ∧
        ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
          R.card < k ∧
          M ⊆ additiveSupportFamily A k (q - d) ∧
          r < M.card ∧
          (∀ E ∈ M, R ⊆ E) ∧
          (∀ E ∈ M, (E \ R).Nonempty) ∧
          ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
            Disjoint (E \ R) (G \ R)) ∨
      ∃ q ∈ Q, ∃ b, b ∈ A ∧ b ≤ q ∧
        additiveSupportFamily A k (q - b) = ∅)
  have hterminate :
      ∀ q, q ∈ Q → ∀ s : BlockSelector F,
        DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet s) q →
        (∀ v ∈ Q, q < v →
          ¬ DestroysAt
            (additiveSupportFamily A (k + 1)) (selectedSet s) v) →
        Outcome := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
        intro hqQ s hqDestroy hlarger
        obtain hcurrent | hlower | hdescent | hgap :=
          hstep Q q (hQlate q hqQ) s hqQ hcert hlarger
        · exact Or.inl ⟨q, hqQ, hcurrent⟩
        · exact Or.inr (Or.inl ⟨q, hqQ, hlower⟩)
        · obtain ⟨t, u, huQ, huq, _hrank,
              huDestroy, huLarger⟩ := hdescent
          exact ih u huq huQ t huDestroy huLarger
        · exact Or.inr (Or.inr ⟨q, hqQ, hgap⟩)
  let initial : BlockSelector F :=
    fun j => ⟨(P.nonempty j).choose, (P.nonempty j).choose_spec⟩
  obtain ⟨q, hqQ, hqDestroy, hqLarger⟩ :=
    exists_maximalDestroyedCertificateTarget hcert initial
  exact hterminate q hqQ initial hqDestroy hqLarger

/-- Finite-certificate migration with a fresh predecessor-gap point.

The strong-induction termination is unchanged, but its arithmetic escape is
now forced outside the caller's finite protected set `W`. -/
theorem IsExactTupleAsymptoticBasis.eventually_finiteCertificate_matching_or_freshLowerGap
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (r w : ℕ) :
    ∃ N, ∀ W : Finset ℕ, W.card ≤ w →
      ∀ Q : Finset ℕ,
      (∀ q ∈ Q, N ≤ q) →
      (∀ s : BlockSelector F, ∃ q ∈ Q,
        DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet s) q) →
      ((∃ q ∈ Q, ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
          R.card < k + 1 ∧
          M ⊆ additiveSupportFamily A (k + 1) q ∧
          r < M.card ∧
          (∀ E ∈ M, R ⊆ E) ∧
          (∀ E ∈ M, (E \ R).Nonempty) ∧
          ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
            Disjoint (E \ R) (G \ R)) ∨
        (∃ q ∈ Q, ∃ d, d ∈ A ∧ d ≤ q ∧
          ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
            R.card < k ∧
            M ⊆ additiveSupportFamily A k (q - d) ∧
            r < M.card ∧
            (∀ E ∈ M, R ⊆ E) ∧
            (∀ E ∈ M, (E \ R).Nonempty) ∧
            ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
              Disjoint (E \ R) (G \ R)) ∨
        ∃ q ∈ Q, ∃ b, b ∈ A ∧ b ∉ W ∧ b ≤ q ∧
          additiveSupportFamily A k (q - b) = ∅) := by
  classical
  obtain ⟨N, hstep⟩ :=
    hbasis.eventually_lockedPrefix_matching_or_freshGap_or_rankGrowthDescent
      P r w
  refine ⟨N, ?_⟩
  intro W hWcard Q hQlate hcert
  let Outcome : Prop :=
    ((∃ q ∈ Q, ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
        R.card < k + 1 ∧
        M ⊆ additiveSupportFamily A (k + 1) q ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
          Disjoint (E \ R) (G \ R)) ∨
      (∃ q ∈ Q, ∃ d, d ∈ A ∧ d ≤ q ∧
        ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
          R.card < k ∧
          M ⊆ additiveSupportFamily A k (q - d) ∧
          r < M.card ∧
          (∀ E ∈ M, R ⊆ E) ∧
          (∀ E ∈ M, (E \ R).Nonempty) ∧
          ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
            Disjoint (E \ R) (G \ R)) ∨
      ∃ q ∈ Q, ∃ b, b ∈ A ∧ b ∉ W ∧ b ≤ q ∧
        additiveSupportFamily A k (q - b) = ∅)
  have hterminate :
      ∀ q, q ∈ Q → ∀ s : BlockSelector F,
        DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet s) q →
        (∀ v ∈ Q, q < v →
          ¬ DestroysAt
            (additiveSupportFamily A (k + 1)) (selectedSet s) v) →
        Outcome := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
        intro hqQ s hqDestroy hlarger
        obtain hcurrent | hlower | hdescent | hgap :=
          hstep W hWcard Q q (hQlate q hqQ) s hqQ hcert hlarger
        · exact Or.inl ⟨q, hqQ, hcurrent⟩
        · exact Or.inr (Or.inl ⟨q, hqQ, hlower⟩)
        · obtain ⟨t, u, huQ, huq, _hrank,
              huDestroy, huLarger⟩ := hdescent
          exact ih u huq huQ t huDestroy huLarger
        · exact Or.inr (Or.inr ⟨q, hqQ, hgap⟩)
  let initial : BlockSelector F :=
    fun j => ⟨(P.nonempty j).choose, (P.nonempty j).choose_spec⟩
  obtain ⟨q, hqQ, hqDestroy, hqLarger⟩ :=
    exists_maximalDestroyedCertificateTarget hcert initial
  exact hterminate q hqQ initial hqDestroy hqLarger

/-- Strong deletion globalizes the terminating certificate composition.

No bound on the certificate cardinality and no diagonal-row hypothesis is
needed.  For arbitrarily late certificates and every requested size, one
gets a large rooted matching at the current order, a large rooted matching
at one coherent predecessor difference, or a genuine predecessor gap. -/
theorem IsStronglyMinimalExactBasis.cofinal_rootedMatching_or_lowerGap
    {A : Set ℕ} {k : ℕ}
    (hminimal : IsStronglyMinimalExactBasis A (k + 1)) :
    ∀ r L,
      ((∃ q, L ≤ q ∧ ∃ R : Finset ℕ,
          ∃ M : Finset (Finset ℕ),
            R.card < k + 1 ∧
            M ⊆ additiveSupportFamily A (k + 1) q ∧
            r < M.card ∧
            (∀ E ∈ M, R ⊆ E) ∧
            (∀ E ∈ M, (E \ R).Nonempty) ∧
            ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
              Disjoint (E \ R) (G \ R)) ∨
        (∃ q, L ≤ q ∧ ∃ d, d ∈ A ∧ d ≤ q ∧
          ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
            R.card < k ∧
            M ⊆ additiveSupportFamily A k (q - d) ∧
            r < M.card ∧
            (∀ E ∈ M, R ⊆ E) ∧
            (∀ E ∈ M, (E \ R).Nonempty) ∧
            ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
              Disjoint (E \ R) (G \ R)) ∨
        ∃ q, L ≤ q ∧ ∃ b, b ∈ A ∧ b ≤ q ∧
          additiveSupportFamily A k (q - b) = ∅) := by
  classical
  obtain ⟨F, P, _hFcard⟩ :=
    exists_finiteBlockPartition_exactCard
      hminimal.1.infinite (show 0 < 1 by omega)
  intro r L
  obtain ⟨N, hN⟩ :=
    hminimal.1.eventually_finiteCertificate_matching_or_lowerGap P r
  obtain ⟨Q, hQlate, hcert⟩ :=
    (finiteBlockCertificates_of_strongInfiniteDeletion hminimal.2)
      F P (max L N)
  have hLateN : ∀ q ∈ Q, N ≤ q := by
    intro q hqQ
    exact (le_max_right L N).trans (hQlate q hqQ)
  have hLateL : ∀ q ∈ Q, L ≤ q := by
    intro q hqQ
    exact (le_max_left L N).trans (hQlate q hqQ)
  obtain hcurrent | hlower | hgap := hN Q hLateN hcert
  · obtain ⟨q, hqQ, hmatch⟩ := hcurrent
    exact Or.inl ⟨q, hLateL q hqQ, hmatch⟩
  · obtain ⟨q, hqQ, hmatch⟩ := hlower
    exact Or.inr (Or.inl ⟨q, hLateL q hqQ, hmatch⟩)
  · obtain ⟨q, hqQ, hgap⟩ := hgap
    exact Or.inr (Or.inr ⟨q, hLateL q hqQ, hgap⟩)

/-- Strong deletion with a genuinely fresh recurrent gap repair.

For every finite protected set `W`, matching demand, and target threshold,
the arithmetic escape point can be chosen in `A \ W`.  This is the
finite-injury form of the global dichotomy: successive gap repairs need
never reuse a previously locked vertex. -/
theorem IsStronglyMinimalExactBasis.cofinal_rootedMatching_or_freshLowerGap
    {A : Set ℕ} {k : ℕ}
    (hminimal : IsStronglyMinimalExactBasis A (k + 1)) :
    ∀ W : Finset ℕ, ∀ r L,
      ((∃ q, L ≤ q ∧ ∃ R : Finset ℕ,
          ∃ M : Finset (Finset ℕ),
            R.card < k + 1 ∧
            M ⊆ additiveSupportFamily A (k + 1) q ∧
            r < M.card ∧
            (∀ E ∈ M, R ⊆ E) ∧
            (∀ E ∈ M, (E \ R).Nonempty) ∧
            ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
              Disjoint (E \ R) (G \ R)) ∨
        (∃ q, L ≤ q ∧ ∃ d, d ∈ A ∧ d ≤ q ∧
          ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
            R.card < k ∧
            M ⊆ additiveSupportFamily A k (q - d) ∧
            r < M.card ∧
            (∀ E ∈ M, R ⊆ E) ∧
            (∀ E ∈ M, (E \ R).Nonempty) ∧
            ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
              Disjoint (E \ R) (G \ R)) ∨
        ∃ q, L ≤ q ∧ ∃ b, b ∈ A ∧ b ∉ W ∧ b ≤ q ∧
          additiveSupportFamily A k (q - b) = ∅) := by
  classical
  obtain ⟨F, P, _hFcard⟩ :=
    exists_finiteBlockPartition_exactCard
      hminimal.1.infinite (show 0 < 1 by omega)
  intro W r L
  obtain ⟨N, hN⟩ :=
    hminimal.1.eventually_finiteCertificate_matching_or_freshLowerGap
      P r W.card
  obtain ⟨Q, hQlate, hcert⟩ :=
    (finiteBlockCertificates_of_strongInfiniteDeletion hminimal.2)
      F P (max L N)
  have hLateN : ∀ q ∈ Q, N ≤ q := by
    intro q hqQ
    exact (le_max_right L N).trans (hQlate q hqQ)
  have hLateL : ∀ q ∈ Q, L ≤ q := by
    intro q hqQ
    exact (le_max_left L N).trans (hQlate q hqQ)
  obtain hcurrent | hlower | hgap :=
    hN W le_rfl Q hLateN hcert
  · obtain ⟨q, hqQ, hmatch⟩ := hcurrent
    exact Or.inl ⟨q, hLateL q hqQ, hmatch⟩
  · obtain ⟨q, hqQ, hmatch⟩ := hlower
    exact Or.inr (Or.inl ⟨q, hLateL q hqQ, hmatch⟩)
  · obtain ⟨q, hqQ, hgap⟩ := hgap
    exact Or.inr (Or.inr ⟨q, hLateL q hqQ, hgap⟩)

/-- Certificate-safe finite-prefix composition for every bounded minimal
destroyer when all blocks have second-choice capacity.

Uniform protected avoidance gives either a large coherent difference family
or a lower-gap point outside `U`.  In the gap branch, the empty-exception
protected completion repairs any private hit of the minimal destroyer.
Unlike the old-collision theorem below, no lower bound on `D.card` is
required; the only extra hypothesis is the all-block capacity needed for
the second choices. -/
theorem IsExactTupleAsymptoticBasis.eventually_boundedMinimalDestroyer_protectedRepair_or_growth
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (B w : ℕ) :
    ∃ N, ∀ q, N ≤ q → ∀ U : Finset ℕ, U.card ≤ w →
      ∀ s : BlockSelector F, ∀ D : Finset ℕ,
      (additiveSupportFamily A (k + 1) q).Nonempty →
      IsInclusionMinimalDestroyer
        (additiveSupportFamily A (k + 1)) D q →
      D.card ≤ B →
      Disjoint (U : Set ℕ) (selectedSet s) →
      (∀ j, U.card + (k + 1) < (F j).card) →
      ((∃ d ∈ D, d ≤ q ∧
          B < (additiveSupportFamily A k (q - d)).card) ∨
        ∃ t : BlockSelector F,
          Disjoint (U : Set ℕ) (selectedSet t) ∧
          ¬ DestroysAt
            (additiveSupportFamily A (k + 1))
            (selectedSet t) q) := by
  obtain ⟨N, hN⟩ :=
    hbasis.eventually_boundedDestroyer_forces_largeDifferenceFamily_or_lowerGap_avoiding
      B w
  refine ⟨N, ?_⟩
  intro q hNq U hUcard s D hrepresented hminimal hDcard
    hUselected hblocks
  obtain hpGrowth | ⟨b, hbA, hbU, _hbq, hbGap⟩ :=
    hN U hUcard D hDcard q hNq hminimal.1
  · left
    obtain ⟨d, hdD, _hdA, hdq, ℋ, hℋsub, hBℋ⟩ :=
      hpGrowth
    have hℋfamily :
        ℋ.card ≤
          (additiveSupportFamily A k (q - d)).card :=
      Finset.card_le_card hℋsub
    exact ⟨d, hdD, hdq,
      lt_of_lt_of_le hBℋ hℋfamily⟩
  · right
    have hDnonempty : D.Nonempty := by
      by_contra hDempty
      rw [Finset.not_nonempty_iff_eq_empty.mp hDempty] at hminimal
      obtain ⟨E, hER⟩ := hrepresented
      exact hminimal.1 E hER (by simp)
    obtain ⟨d, hdD⟩ := hDnonempty
    exact lowerGapRepair_extends_avoiding_protectedUnion
      P s hminimal hdD hbA hbU hbGap hUselected hblocks

/-- Bounded-destroyer strict certificate step.

Store supports for the currently surviving larger certificate targets.  If
all blocks have the uniform protected capacity, the preceding theorem gives
either coherent support growth or a protected repair.  The latter forces
the finite certificate to move to a strictly smaller target.  This closes
the small-destroyer branch completely in the absence of capacity-deficient
old blocks. -/
theorem IsExactTupleAsymptoticBasis.eventually_boundedMinimalDestroyer_growth_or_strictCertificateDescent
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (Q : Finset ℕ)
    (B : ℕ) :
    ∃ N, ∀ q, N ≤ q → ∀ s : BlockSelector F, ∀ D : Finset ℕ,
      (additiveSupportFamily A (k + 1) q).Nonempty →
      (∀ t : BlockSelector F, ∃ u ∈ Q,
        DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet t) u) →
      (∀ u ∈ Q, q < u →
        ¬ DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet s) u) →
      IsInclusionMinimalDestroyer
        (additiveSupportFamily A (k + 1)) D q →
      D.card ≤ B →
      (∀ j,
        (k + 1) * Q.card + (k + 1) < (F j).card) →
      ((∃ d ∈ D, d ≤ q ∧
          B < (additiveSupportFamily A k (q - d)).card) ∨
        ∃ t : BlockSelector F, ∃ u ∈ Q, u < q ∧
          DestroysAt
            (additiveSupportFamily A (k + 1))
            (selectedSet t) u) := by
  obtain ⟨N, hN⟩ :=
    hbasis.eventually_boundedMinimalDestroyer_protectedRepair_or_growth
      P B ((k + 1) * Q.card)
  refine ⟨N, ?_⟩
  intro q hNq s D hrepresented hcert hlarger hminimal
    hDcard hblocks
  obtain ⟨U, hUcard, hUselected, hprotected⟩ :=
    exists_protectedSupportUnion_of_survivingLargerTargets
      s hlarger
  have hcompletion :
      ∀ j, U.card + (k + 1) < (F j).card := by
    intro j
    exact lt_of_le_of_lt
      (Nat.add_le_add_right hUcard (k + 1))
      (hblocks j)
  obtain hgrowth | ⟨t, htU, htq⟩ :=
    hN q hNq U hUcard s D hrepresented hminimal hDcard
      hUselected hcompletion
  · exact Or.inl hgrowth
  · right
    obtain ⟨u, huQ, huq, huDestroy⟩ :=
      protectedSelectorRepair_forces_strictCertificateDescent
        hcert hprotected htU htq
    exact ⟨t, u, huQ, huq, huDestroy⟩

/-- Uniform bounded-certificate payoff of the strict-descent argument.

Fix bounds `C` for the certificate cardinality and `B` for support growth
before the certificate is known.  If every block has the corresponding
protected capacity, then every sufficiently late finite selector
certificate forces one of two genuine arithmetic growth outcomes:

* more than `B` order-`k+1` supports at a certificate target; or
* more than `B` order-`k` supports at a coherent difference `q-d`.

Indeed, in the absence of both outcomes every minimal selected destroyer has
cardinality at most `B`.  Protected finite-prefix composition then supplies
the repair step at the largest currently destroyed target, and
`finiteSelectorCertificate_impossible_of_strictRepairStep` rules out an
infinite descent through the finite certificate. -/
theorem IsExactTupleAsymptoticBasis.eventually_boundedCertificate_forces_supportGrowth
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (C B : ℕ) :
    ∃ N, ∀ Q : Finset ℕ, Q.card ≤ C →
      (∀ q ∈ Q, N ≤ q) →
      (∀ s : BlockSelector F, ∃ q ∈ Q,
        DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet s) q) →
      (∀ j,
        (k + 1) * C + (k + 1) < (F j).card) →
      ((∃ q ∈ Q,
          B < (additiveSupportFamily A (k + 1) q).card) ∨
        ∃ q ∈ Q, ∃ d, d ∈ A ∧ d ≤ q ∧
          B < (additiveSupportFamily A k (q - d)).card) := by
  classical
  obtain ⟨N₀, hN₀⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  obtain ⟨N₁, hN₁⟩ :=
    hbasis.eventually_boundedMinimalDestroyer_protectedRepair_or_growth
      P B ((k + 1) * C)
  refine ⟨max N₀ N₁, ?_⟩
  intro Q hQcard hlate hcert hblocks
  by_cases hExact :
      ∃ q ∈ Q,
        B < (additiveSupportFamily A (k + 1) q).card
  · exact Or.inl hExact
  by_cases hDifference :
      ∃ q ∈ Q, ∃ d, d ∈ A ∧ d ≤ q ∧
        B < (additiveSupportFamily A k (q - d)).card
  · exact Or.inr hDifference
  have hExactBound :
      ∀ q ∈ Q,
        (additiveSupportFamily A (k + 1) q).card ≤ B := by
    intro q hqQ
    apply Nat.le_of_not_gt
    intro hqLarge
    exact hExact ⟨q, hqQ, hqLarge⟩
  have hDifferenceBound :
      ∀ q ∈ Q, ∀ d, d ∈ A → d ≤ q →
        (additiveSupportFamily A k (q - d)).card ≤ B := by
    intro q hqQ d hdA hdq
    apply Nat.le_of_not_gt
    intro hdLarge
    exact hDifference ⟨q, hqQ, d, hdA, hdq, hdLarge⟩
  let s₀ : BlockSelector F := fun j =>
    ⟨(P.nonempty j).choose, (P.nonempty j).choose_spec⟩
  exfalso
  apply finiteSelectorCertificate_impossible_of_strictRepairStep
    s₀ hcert
  intro s q hqQ hqDestroy hlarger
  have hqLate : N₀ ≤ q :=
    (le_max_left N₀ N₁).trans (hlate q hqQ)
  have hqRepairLate : N₁ ≤ q :=
    (le_max_right N₀ N₁).trans (hlate q hqQ)
  obtain ⟨E₀, hE₀R, _hE₀empty⟩ := hN₀ q hqLate
  have hrepresented :
      (additiveSupportFamily A (k + 1) q).Nonempty :=
    ⟨E₀, hE₀R⟩
  obtain ⟨D, hDselected, _hDcard, hDdestroy⟩ :=
    exists_finiteSelectedDestroyer_of_destroysAt
      P s hqDestroy
  obtain ⟨D₀, hD₀D, hminimal⟩ :=
    exists_inclusionMinimalDestroyer_subset hDdestroy
  have hD₀selected : (D₀ : Set ℕ) ⊆ selectedSet s := by
    intro x hxD₀
    exact hDselected (Finset.mem_coe.mpr
      (hD₀D (Finset.mem_coe.mp hxD₀)))
  have hD₀card : D₀.card ≤ B :=
    hminimal.card_le_supportFamily.trans
      (hExactBound q hqQ)
  obtain ⟨U, hUcard, hUselected, hprotected⟩ :=
    exists_protectedSupportUnion_of_survivingLargerTargets
      s hlarger
  have hUbudget :
      U.card ≤ (k + 1) * C :=
    hUcard.trans
      (Nat.mul_le_mul_left (k + 1) hQcard)
  have hcompletion :
      ∀ j, U.card + (k + 1) < (F j).card := by
    intro j
    exact lt_of_le_of_lt
      (Nat.add_le_add_right hUbudget (k + 1))
      (hblocks j)
  obtain hgrowth | ⟨t, htU, htq⟩ :=
    hN₁ q hqRepairLate U hUbudget s D₀ hrepresented
      hminimal hD₀card hUselected hcompletion
  · obtain ⟨d, hdD₀, hdq, hdLarge⟩ := hgrowth
    have hdA : d ∈ A :=
      P.selectedSet_subset s
        (hD₀selected (Finset.mem_coe.mpr hdD₀))
    exact (not_lt_of_ge
      (hDifferenceBound q hqQ d hdA hdq) hdLarge).elim
  · refine ⟨t, htq, ?_⟩
    intro u huQ hqu
    obtain ⟨G, hGR, hGU⟩ := hprotected u huQ hqu
    intro huDestroy
    exact (huDestroy G hGR)
      (Set.disjoint_of_subset_left hGU htU)

/-- Exact-label rooted-matching normalization of bounded certificates.

Difference growth no longer drifts to `q-d`: the factor-two insertion lemma
lifts its cardinality back to the order-`k+1` support family at the original
certificate target `q`.  Applying the rooted matching bound there produces
a large delta system at the exact late label. -/
theorem IsExactTupleAsymptoticBasis.eventually_boundedCertificate_forces_exactRootedMatching
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (C r : ℕ) :
    ∃ N, ∀ Q : Finset ℕ, Q.card ≤ C →
      (∀ q ∈ Q, N ≤ q) →
      (∀ s : BlockSelector F, ∃ q ∈ Q,
        DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet s) q) →
      (∀ j,
        (k + 1) * C + (k + 1) < (F j).card) →
      ∃ q ∈ Q, ∃ R : Finset ℕ,
        ∃ M : Finset (Finset ℕ),
          R.card < k + 1 ∧
          M ⊆ additiveSupportFamily A (k + 1) q ∧
          r < M.card ∧
          (∀ E ∈ M, R ⊆ E) ∧
          (∀ E ∈ M, (E \ R).Nonempty) ∧
          ∀ E ∈ M, ∀ D ∈ M, E ≠ D →
            Disjoint (E \ R) (D \ R) := by
  let threshold := additiveRootedMatchingBound (k + 1) r
  let B := 2 * threshold
  obtain ⟨N, hN⟩ :=
    hbasis.eventually_boundedCertificate_forces_supportGrowth
      P C B
  refine ⟨N, ?_⟩
  intro Q hQcard hlate hcert hblocks
  obtain ⟨q, hqQ, hqLarge⟩ |
      ⟨q, hqQ, d, hdA, hdq, hdLarge⟩ :=
    hN Q hQcard hlate hcert hblocks
  · have hthreshold :
        threshold ≤
          (additiveSupportFamily A (k + 1) q).card := by
      dsimp only [B] at hqLarge
      omega
    obtain ⟨R, M, hRcard, hMsub, hMcard, hMroot,
        hMnonempty, hMmatching⟩ :=
      additiveSupportSubfamily_has_large_rootedMatching
        (k + 1) r q
          (additiveSupportFamily A (k + 1) q)
          (fun _ h => h) (by simpa only [threshold] using hthreshold)
    exact ⟨q, hqQ, R, M, hRcard, hMsub, hMcard,
      hMroot, hMnonempty, hMmatching⟩
  · have hliftBound :=
      lowerDifferenceSupportFamily_card_le_twice_exact
        (k := k) hdA hdq
    have hthreshold :
        threshold ≤
          (additiveSupportFamily A (k + 1) q).card := by
      dsimp only [B] at hdLarge
      omega
    obtain ⟨R, M, hRcard, hMsub, hMcard, hMroot,
        hMnonempty, hMmatching⟩ :=
      additiveSupportSubfamily_has_large_rootedMatching
        (k + 1) r q
          (additiveSupportFamily A (k + 1) q)
          (fun _ h => h) (by simpa only [threshold] using hthreshold)
    exact ⟨q, hqQ, R, M, hRcard, hMsub, hMcard,
      hMroot, hMnonempty, hMmatching⟩

/-- Matching-normalized bounded-certificate payoff.

Choose `B` above the finite-rank matching thresholds at ranks `k+1` and
`k`.  The preceding strict-descent theorem then turns either arithmetic
growth horn into a genuine matching of more than `r` supports at some
positive rank at most `k+1`. -/
theorem IsExactTupleAsymptoticBasis.eventually_boundedCertificate_forces_matching
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (C r : ℕ) :
    ∃ N, ∀ Q : Finset ℕ, Q.card ≤ C →
      (∀ q ∈ Q, N ≤ q) →
      (∀ s : BlockSelector F, ∃ q ∈ Q,
        DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet s) q) →
      (∀ j,
        (k + 1) * C + (k + 1) < (F j).card) →
      ∃ h, 0 < h ∧ h ≤ k + 1 ∧
        ∃ m, ∃ M : Finset (Finset ℕ),
          M ⊆ additiveSupportFamily A h m ∧
          IsMatching M ∧ r < M.card := by
  let B :=
    max (additiveSupportRankBound (k + 1) r)
      (additiveSupportRankBound k r)
  obtain ⟨N, hN⟩ :=
    hbasis.eventually_boundedCertificate_forces_supportGrowth
      P C B
  refine ⟨N, ?_⟩
  intro Q hQcard hlate hcert hblocks
  obtain ⟨q, _hqQ, hqLarge⟩ |
      ⟨q, _hqQ, d, _hdA, _hdq, hdLarge⟩ :=
    hN Q hQcard hlate hcert hblocks
  · have hthreshold :
        additiveSupportRankBound (k + 1) r ≤
          (additiveSupportFamily A (k + 1) q).card := by
      exact (le_max_left _ _).trans (Nat.le_of_lt hqLarge)
    obtain ⟨h, hhpos, hhle, m, M, hMsub, hMmatching, hMcard⟩ :=
      additiveSupportRankBound_forces_matching_below
        (k + 1) q hthreshold
    exact ⟨h, hhpos, hhle, m, M, hMsub, hMmatching, hMcard⟩
  · have hthreshold :
        additiveSupportRankBound k r ≤
          (additiveSupportFamily A k (q - d)).card := by
      exact (le_max_right _ _).trans (Nat.le_of_lt hdLarge)
    obtain ⟨h, hhpos, hhle, m, M, hMsub, hMmatching, hMcard⟩ :=
      additiveSupportRankBound_forces_matching_below
        k (q - d) hthreshold
    exact ⟨h, hhpos, hhle.trans (Nat.le_succ k),
      m, M, hMsub, hMmatching, hMcard⟩

/-- One fixed partition handles every matching threshold at a prescribed
certificate bound.

The block cardinality depends only on `C`, not on the later matching demand
`r`.  After this partition is fixed, strong deletion supplies arbitrarily
late finite certificates.  If such a certificate has cardinality at most
`C`, the bounded-certificate strict-descent theorem gives a matching larger
than the arbitrarily chosen `r`; otherwise the certificate itself has grown
beyond `C`.

This is the scheduled quantifier payoff of the second-choice argument: the
partition is chosen once before `r`, the late threshold, and the certificate
are revealed. -/
theorem IsStronglyMinimalExactBasis.exists_fixedPartition_largeCertificate_or_arbitraryMatching
    {A : Set ℕ} {k : ℕ}
    (hminimal : IsStronglyMinimalExactBasis A (k + 1)) :
    ∀ C,
      ∃ F : ℕ → Finset ℕ,
        ∃ _P : IsFiniteBlockPartition A F,
          (∀ j,
            (F j).card =
              (k + 1) * C + (k + 1) + 1) ∧
          ∀ r L, ∃ Q : Finset ℕ,
            (∀ q ∈ Q, L ≤ q) ∧
            (∀ s : BlockSelector F, ∃ q ∈ Q,
              DestroysAt
                (additiveSupportFamily A (k + 1))
                (selectedSet s) q) ∧
            (C < Q.card ∨
              ∃ h, 0 < h ∧ h ≤ k + 1 ∧
                ∃ m, ∃ M : Finset (Finset ℕ),
                  M ⊆ additiveSupportFamily A h m ∧
                  IsMatching M ∧ r < M.card) := by
  classical
  intro C
  let blockSize := (k + 1) * C + (k + 1) + 1
  have hblockSizePos : 0 < blockSize := by
    dsimp only [blockSize]
    omega
  obtain ⟨F, P, hFcard⟩ :=
    exists_finiteBlockPartition_exactCard
      hminimal.1.infinite hblockSizePos
  refine ⟨F, P, hFcard, ?_⟩
  intro r L
  obtain ⟨N, hN⟩ :=
    hminimal.1.eventually_boundedCertificate_forces_matching
      P C r
  obtain ⟨Q, hQLate, hcert⟩ :=
    (finiteBlockCertificates_of_strongInfiniteDeletion hminimal.2)
      F P (max L N)
  have hLateL : ∀ q ∈ Q, L ≤ q := by
    intro q hqQ
    exact (le_max_left L N).trans (hQLate q hqQ)
  refine ⟨Q, hLateL, hcert, ?_⟩
  by_cases hQcard : Q.card ≤ C
  · right
    have hLateN : ∀ q ∈ Q, N ≤ q := by
      intro q hqQ
      exact (le_max_right L N).trans (hQLate q hqQ)
    have hblocks :
        ∀ j,
          (k + 1) * C + (k + 1) < (F j).card := by
      intro j
      rw [hFcard j]
      dsimp only [blockSize]
      omega
    exact hN Q hQcard hLateN hcert hblocks
  · left
    omega

/-- Fixed-partition exact-label rooted-matching dichotomy.

For a prescribed certificate bound `C`, one partition is chosen before the
matching size and lateness demands.  Every later request returns either a
certificate larger than `C`, or a rooted matching of the requested size in
the original order-`k+1` support family at a certificate target `q ≥ L`.
Thus the bounded-certificate branch now gives cofinal structure at the
correct rank and exact labels. -/
theorem IsStronglyMinimalExactBasis.exists_fixedPartition_largeCertificate_or_cofinalExactRootedMatching
    {A : Set ℕ} {k : ℕ}
    (hminimal : IsStronglyMinimalExactBasis A (k + 1)) :
    ∀ C,
      ∃ F : ℕ → Finset ℕ,
        ∃ _P : IsFiniteBlockPartition A F,
          (∀ j,
            (F j).card =
              (k + 1) * C + (k + 1) + 1) ∧
          ∀ r L, ∃ Q : Finset ℕ,
            (∀ q ∈ Q, L ≤ q) ∧
            (∀ s : BlockSelector F, ∃ q ∈ Q,
              DestroysAt
                (additiveSupportFamily A (k + 1))
                (selectedSet s) q) ∧
            (C < Q.card ∨
              ∃ q ∈ Q, ∃ R : Finset ℕ,
                ∃ M : Finset (Finset ℕ),
                  R.card < k + 1 ∧
                  M ⊆ additiveSupportFamily A (k + 1) q ∧
                  r < M.card ∧
                  (∀ E ∈ M, R ⊆ E) ∧
                  (∀ E ∈ M, (E \ R).Nonempty) ∧
                  ∀ E ∈ M, ∀ D ∈ M, E ≠ D →
                    Disjoint (E \ R) (D \ R)) := by
  classical
  intro C
  let blockSize := (k + 1) * C + (k + 1) + 1
  have hblockSizePos : 0 < blockSize := by
    dsimp only [blockSize]
    omega
  obtain ⟨F, P, hFcard⟩ :=
    exists_finiteBlockPartition_exactCard
      hminimal.1.infinite hblockSizePos
  refine ⟨F, P, hFcard, ?_⟩
  intro r L
  obtain ⟨N, hN⟩ :=
    hminimal.1.eventually_boundedCertificate_forces_exactRootedMatching
      P C r
  obtain ⟨Q, hQLate, hcert⟩ :=
    (finiteBlockCertificates_of_strongInfiniteDeletion hminimal.2)
      F P (max L N)
  have hLateL : ∀ q ∈ Q, L ≤ q := by
    intro q hqQ
    exact (le_max_left L N).trans (hQLate q hqQ)
  refine ⟨Q, hLateL, hcert, ?_⟩
  by_cases hQcard : Q.card ≤ C
  · right
    have hLateN : ∀ q ∈ Q, N ≤ q := by
      intro q hqQ
      exact (le_max_right L N).trans (hQLate q hqQ)
    have hblocks :
        ∀ j,
          (k + 1) * C + (k + 1) < (F j).card := by
      intro j
      rw [hFcard j]
      dsimp only [blockSize]
      omega
    exact hN Q hQcard hLateN hcert hblocks
  · left
    omega

/-- Certificate-safe finite-prefix composition for a large minimal
destroyer.

The protected union has only a cardinal budget when the late threshold is
chosen.  Uniform avoidance gives a lower-gap point outside that union.
Trying this gap point at every private hit either completes a selector which
preserves `q` and all protected targets, or amplifies the old collisions.
Thus a destroyer larger than `|J| * r` cannot leave an unprotected repair
horn. -/
theorem IsExactTupleAsymptoticBasis.eventually_largeMinimalDestroyer_protectedRepair_or_growth
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (J : Finset ℕ)
    (B r w : ℕ) :
    ∃ N, ∀ q, N ≤ q → ∀ U : Finset ℕ, U.card ≤ w →
      ∀ s : BlockSelector F, ∀ D : Finset ℕ,
      (additiveSupportFamily A (k + 1) q).Nonempty →
      IsInclusionMinimalDestroyer
        (additiveSupportFamily A (k + 1)) D q →
      D.card ≤ B →
      J.card * r < D.card →
      Disjoint (U : Set ℕ) (selectedSet s) →
      (∀ j, j ∉ J →
        U.card + (k + 1) < (F j).card) →
      ((∃ d ∈ D, d ≤ q ∧
          B < (additiveSupportFamily A k (q - d)).card) ∨
        (∃ j ∈ J,
          r < (additiveSupportFamily A k
            (q - (s j).1)).card) ∨
        ∃ t : BlockSelector F,
          Disjoint (U : Set ℕ) (selectedSet t) ∧
          ¬ DestroysAt
            (additiveSupportFamily A (k + 1))
            (selectedSet t) q) := by
  obtain ⟨N, hN⟩ :=
    hbasis.eventually_boundedDestroyer_forces_largeDifferenceFamily_or_lowerGap_avoiding
      B w
  refine ⟨N, ?_⟩
  intro q hNq U hUcard s D hrepresented hminimal hDcard
    hDlarge hUselected hcontemporary
  obtain hpGrowth | ⟨b, hbA, hbU, _hbq, hbGap⟩ :=
    hN U hUcard D hDcard q hNq hminimal.1
  · left
    obtain ⟨d, hdD, _hdA, hdq, ℋ, hℋsub, hBℋ⟩ :=
      hpGrowth
    have hℋfamily :
        ℋ.card ≤
          (additiveSupportFamily A k (q - d)).card :=
      Finset.card_le_card hℋsub
    exact ⟨d, hdD, hdq,
      lt_of_lt_of_le hBℋ hℋfamily⟩
  · obtain hrepair | holdGrowth :=
      lowerGapRepair_manyPrivateHits_complete_or_oldGrowth
        P s hminimal hbA hbU hbGap hUselected
          hcontemporary hDlarge
    · exact Or.inr (Or.inr hrepair)
    · exact Or.inr (Or.inl holdGrowth)

/-- Large-destroyer certificate step: growth or strict target descent.

Store supports for every currently surviving larger certificate target,
apply protected finite-prefix composition, and feed a completed repair into
the strict migration lemma.  Hence, above a uniform threshold, a minimal
destroyer larger than `|J| * r` either forces support growth or moves the
certificate obstruction to a strictly smaller target. -/
theorem IsExactTupleAsymptoticBasis.eventually_largeMinimalDestroyer_growth_or_strictCertificateDescent
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (J Q : Finset ℕ)
    (B r : ℕ) :
    ∃ N, ∀ q, N ≤ q → ∀ s : BlockSelector F, ∀ D : Finset ℕ,
      (additiveSupportFamily A (k + 1) q).Nonempty →
      (∀ t : BlockSelector F, ∃ u ∈ Q,
        DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet t) u) →
      (∀ u ∈ Q, q < u →
        ¬ DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet s) u) →
      IsInclusionMinimalDestroyer
        (additiveSupportFamily A (k + 1)) D q →
      D.card ≤ B →
      J.card * r < D.card →
      (∀ j, j ∉ J →
        (k + 1) * Q.card + (k + 1) < (F j).card) →
      ((∃ d ∈ D, d ≤ q ∧
          B < (additiveSupportFamily A k (q - d)).card) ∨
        (∃ j ∈ J,
          r < (additiveSupportFamily A k
            (q - (s j).1)).card) ∨
        ∃ t : BlockSelector F, ∃ u ∈ Q, u < q ∧
          DestroysAt
            (additiveSupportFamily A (k + 1))
            (selectedSet t) u) := by
  obtain ⟨N, hN⟩ :=
    hbasis.eventually_largeMinimalDestroyer_protectedRepair_or_growth
      P J B r ((k + 1) * Q.card)
  refine ⟨N, ?_⟩
  intro q hNq s D hrepresented hcert hlarger hminimal
    hDcard hDlarge hblocks
  obtain ⟨U, hUcard, hUselected, hprotected⟩ :=
    exists_protectedSupportUnion_of_survivingLargerTargets
      s hlarger
  have hcontemporary :
      ∀ j, j ∉ J →
        U.card + (k + 1) < (F j).card := by
    intro j hjJ
    exact lt_of_le_of_lt
      (Nat.add_le_add_right hUcard (k + 1))
      (hblocks j hjJ)
  obtain hpGrowth | holdGrowth | hrepair :=
    hN q hNq U hUcard s D hrepresented hminimal hDcard
      hDlarge hUselected hcontemporary
  · exact Or.inl hpGrowth
  · exact Or.inr (Or.inl holdGrowth)
  · right
    right
    obtain ⟨t, htU, htq⟩ := hrepair
    obtain ⟨u, huQ, huq, huDestroy⟩ :=
      protectedSelectorRepair_forces_strictCertificateDescent
        hcert hprotected htU htq
    exact ⟨t, u, huQ, huq, huDestroy⟩

/-- Uniform finite-prefix composition on a prescribed finite set of old
blocks.

The old selector prefix consists of the selected values in `J` and has
cardinality at most `J.card`, independently of the later selector.  Hence
the exact-basis threshold can be chosen before that selector, target, and
minimal destroyer are known.

If the whole destroyer lies in old blocks, this coherent old prefix destroys
the target.  The finite-prefix theorem then gives either support growth at a
difference by an old selected summand, or a lower-order gap.  The latter is
converted here—not left as an unaligned finite swap—into the full two-block
selector repair. -/
theorem IsExactTupleAsymptoticBasis.eventually_oldBlockDestroyer_growth_or_twoBlockRepair
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (J : Finset ℕ)
    (hblocks : ∀ j, k + 1 < (F j).card) :
    ∃ N, ∀ q, N ≤ q → ∀ s : BlockSelector F, ∀ D : Finset ℕ,
      (additiveSupportFamily A (k + 1) q).Nonempty →
      IsInclusionMinimalDestroyer
        (additiveSupportFamily A (k + 1)) D q →
      (D : Set ℕ) ⊆ selectedSet s →
      (∀ d ∈ D, blockIndex P d ∈ J) →
      ((∃ d ∈ J.image (fun j => (s j).1),
          d ∈ A ∧ d ≤ q ∧
          ∃ ℋ : Finset (Finset ℕ),
            ℋ ⊆ additiveSupportFamily A k (q - d) ∧
            J.card < ℋ.card) ∨
        ∃ t : BlockSelector F,
          ¬ DestroysAt
            (additiveSupportFamily A (k + 1))
            (selectedSet t) q) := by
  classical
  obtain ⟨N, hN⟩ :=
    hbasis.eventually_boundedDestroyer_forces_largeDifferenceFamily_or_lowerGap
      J.card
  refine ⟨N, ?_⟩
  intro q hNq s D hrepresented hminimal hDselected hDold
  let Dold : Finset ℕ := J.image fun j => (s j).1
  have hDoldCard : Dold.card ≤ J.card := by
    exact Finset.card_image_le
  have hDDold : (D : Set ℕ) ⊆ (Dold : Set ℕ) := by
    intro d hdD
    have hdSelected := hDselected hdD
    have hselectedAt :
        (s (blockIndex P d)).1 = d :=
      (P.mem_selectedSet_iff s).mp hdSelected
    apply Finset.mem_coe.mpr
    apply Finset.mem_image.mpr
    exact ⟨blockIndex P d,
      hDold d (Finset.mem_coe.mp hdD), hselectedAt⟩
  have hDoldDestroy :
      DestroysAt
        (additiveSupportFamily A (k + 1)) (Dold : Set ℕ) q :=
    hminimal.1.mono hDDold
  obtain hgrowth | hgap :=
    hN Dold hDoldCard q hNq hDoldDestroy
  · left
    simpa only [Dold] using hgrowth
  · right
    obtain ⟨b, hbA, _hbq, hbGap⟩ := hgap
    have hDnonempty : D.Nonempty := by
      by_contra hDempty
      rw [Finset.not_nonempty_iff_eq_empty.mp hDempty] at hminimal
      obtain ⟨E, hER⟩ := hrepresented
      exact hminimal.1 E hER (by simp)
    obtain ⟨d, hdD⟩ := hDnonempty
    obtain ⟨t, _htb, htSurvives⟩ :=
      lowerGapRepair_extends_to_twoBlockSelectorSurvival
        P s hminimal hdD hbA hbGap hblocks
    exact ⟨t, htSurvives⟩

/-- Exhaustive old/contemporary split for a target-localized minimal
destroyer.

If the destroyer uses a contemporary block, activate one such coordinate.
Protected block alignment then forces either matching growth at a coherent
difference or exposes a represented difference at an old selected summand.

If every point of the destroyer lies in an old block, the coherent old
selector prefix destroys the target.  Uniform finite-prefix composition then
forces matching growth at one of its differences or constructs a complete
selector on which the target survives.  Thus the lower-gap horn is closed as
a full selector repair, rather than remaining an unaligned finite swap. -/
theorem IsExactTupleAsymptoticBasis.eventually_targetLocalized_destroyer_oldContemporarySplit
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (J : Finset ℕ)
    (hk : 0 < k)
    (hblocks : ∀ j, k + 1 < (F j).card) :
    ∃ N, ∀ q, N ≤ q → ∀ (r : ℕ) (Q : Finset ℕ),
      ∀ s : BlockSelector F, ∀ D : Finset ℕ,
      (additiveSupportFamily A (k + 1) q).Nonempty →
      (∀ t : BlockSelector F, ∃ u ∈ Q,
        DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet t) u) →
      (∀ u ∈ Q, u ≠ q →
        ¬ DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet s) u) →
      IsInclusionMinimalDestroyer
        (additiveSupportFamily A (k + 1)) D q →
      (D : Set ℕ) ⊆ selectedSet s →
      (∀ j, j ∉ J →
        D.card * (k * r) + (k + 1) * Q.card + k + 3 ≤
          (F j).card) →
      (((∃ d ∈ D, blockIndex P d ∉ J) ∧
          ((∃ x ∈ D, x ≤ q ∧
              r < (additiveSupportFamily A k (q - x)).card) ∨
            ∃ j ∈ J, (s j).1 ≤ q ∧
              (additiveSupportFamily A k (q - (s j).1)).Nonempty)) ∨
        ((∀ d ∈ D, blockIndex P d ∈ J) ∧
          ((∃ d ∈ J.image (fun j => (s j).1),
              d ∈ A ∧ d ≤ q ∧
              ∃ ℋ : Finset (Finset ℕ),
                ℋ ⊆ additiveSupportFamily A k (q - d) ∧
                J.card < ℋ.card) ∨
            ∃ t : BlockSelector F,
              ¬ DestroysAt
                (additiveSupportFamily A (k + 1))
                (selectedSet t) q))) := by
  classical
  obtain ⟨N, hN⟩ :=
    hbasis.eventually_oldBlockDestroyer_growth_or_twoBlockRepair
      P J hblocks
  refine ⟨N, ?_⟩
  intro q hNq r Q s D hrepresented hcert hother hminimal
    hDselected hcontemporary
  by_cases hDold : ∀ d ∈ D, blockIndex P d ∈ J
  · exact Or.inr
      ⟨hDold,
        hN q hNq s D hrepresented hminimal hDselected hDold⟩
  · have hnew :
        ∃ d, d ∈ D ∧ blockIndex P d ∉ J := by
      by_contra hnone
      apply hDold
      intro d hdD
      by_contra hdNew
      exact hnone ⟨d, hdD, hdNew⟩
    obtain ⟨d, hdD, hdNew⟩ := hnew
    have hdSelected :
        d ∈ selectedSet s :=
      hDselected (Finset.mem_coe.mpr hdD)
    have hselectedAt :
        (s (blockIndex P d)).1 = d :=
      (P.mem_selectedSet_iff s).mp hdSelected
    have hactive :
        (s (blockIndex P d)).1 ∈ D := by
      rw [hselectedAt]
      exact hdD
    exact Or.inl
      ⟨⟨d, hdD, hdNew⟩,
        positiveOrder_targetLocalized_activeBlock_growth_or_oldDifference
          P s hk hcert hother hminimal hDselected hactive
            hcontemporary⟩

/-- Collision-amplified old/contemporary composition.

Fix a desired growth threshold `r`.  If more than `|J| * r` points of the
minimal destroyer lie in contemporary blocks, the private-collision
injection forces support growth either at a destroyer difference or at an
old selected difference.

Otherwise the whole destroyer is uniformly bounded: its old part has at
most one selected point per index in `J`, and its contemporary part has at
most `|J| * r` points.  Uniform finite-prefix composition may therefore be
applied to the whole destroyer.  It again gives support growth, or a
lower-order gap which extends to a complete selector preserving `q`.

This removes the former one-off "represented old difference" escape. -/
theorem IsExactTupleAsymptoticBasis.eventually_targetLocalized_destroyer_growth_or_twoBlockRepair
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (J : Finset ℕ)
    (hk : 0 < k)
    (hblocks : ∀ j, k + 1 < (F j).card)
    (r : ℕ) :
    ∃ N, ∀ q, N ≤ q → ∀ (Q : Finset ℕ),
      ∀ s : BlockSelector F, ∀ D : Finset ℕ,
      (additiveSupportFamily A (k + 1) q).Nonempty →
      (∀ t : BlockSelector F, ∃ u ∈ Q,
        DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet t) u) →
      (∀ u ∈ Q, u ≠ q →
        ¬ DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet s) u) →
      IsInclusionMinimalDestroyer
        (additiveSupportFamily A (k + 1)) D q →
      (D : Set ℕ) ⊆ selectedSet s →
      (∀ j, j ∉ J →
        D.card * (k * r) + (k + 1) * Q.card + k + 3 ≤
          (F j).card) →
      ((∃ x ∈ D, x ≤ q ∧
          r < (additiveSupportFamily A k (q - x)).card) ∨
        (∃ j ∈ J,
          r < (additiveSupportFamily A k
            (q - (s j).1)).card) ∨
        ∃ t : BlockSelector F,
          ¬ DestroysAt
            (additiveSupportFamily A (k + 1))
            (selectedSet t) q) := by
  classical
  let budget : ℕ := (J.card + 1) * (r + 1)
  obtain ⟨N, hN⟩ :=
    hbasis.eventually_boundedDestroyer_forces_largeDifferenceFamily_or_lowerGap
      budget
  refine ⟨N, ?_⟩
  intro q hNq Q s D hrepresented hcert hother hminimal
    hDselected hcontemporary
  by_cases hmany :
      J.card * r <
        (D.filter fun d => blockIndex P d ∉ J).card
  · obtain hgrowth | holdGrowth :=
      positiveOrder_targetLocalized_manyContemporaryPoints_force_growth
        P s hk hcert hother hminimal hDselected hcontemporary hmany
    · exact Or.inl hgrowth
    · exact Or.inr (Or.inl holdGrowth)
  · have hnewCard :
        (D.filter fun d => blockIndex P d ∉ J).card ≤
          J.card * r :=
      Nat.le_of_not_gt hmany
    let Dold : Finset ℕ :=
      J.image fun j => (s j).1
    let oldPart : Finset ℕ :=
      D.filter fun d => blockIndex P d ∈ J
    have holdPartSub : oldPart ⊆ Dold := by
      intro d hdOld
      have hdParts :
          d ∈ D ∧ blockIndex P d ∈ J :=
        Finset.mem_filter.mp hdOld
      have hdSelected :
          d ∈ selectedSet s :=
        hDselected (Finset.mem_coe.mpr hdParts.1)
      have hselectedAt :
          (s (blockIndex P d)).1 = d :=
        (P.mem_selectedSet_iff s).mp hdSelected
      exact Finset.mem_image.mpr
        ⟨blockIndex P d, hdParts.2, hselectedAt⟩
    have holdPartCard : oldPart.card ≤ J.card := by
      exact (Finset.card_le_card holdPartSub).trans
        Finset.card_image_le
    have hsplit :
        oldPart.card +
          (D.filter fun d => blockIndex P d ∉ J).card =
            D.card := by
      simpa [oldPart] using
        (Finset.card_filter_add_card_filter_not
          (s := D) (p := fun d => blockIndex P d ∈ J))
    have hDcard : D.card ≤ budget := by
      have hraw :
          D.card ≤ J.card + J.card * r := by
        omega
      dsimp only [budget]
      calc
        D.card ≤ J.card + J.card * r := hraw
        _ ≤ (J.card + 1) * (r + 1) := by
          rw [Nat.mul_add, Nat.add_mul]
          omega
    obtain hpGrowth | hgap :=
      hN D hDcard q hNq hminimal.1
    · left
      obtain ⟨d, hdD, _hdA, hdq, ℋ, hℋsub, hbudgetℋ⟩ :=
        hpGrowth
      have hone : 1 ≤ J.card + 1 := by omega
      have hrBudget : r < budget := by
        have hmul :=
          Nat.mul_le_mul_right (r + 1) hone
        exact lt_of_lt_of_le (Nat.lt_succ_self r)
          (by simpa only [one_mul, budget] using hmul)
      have hℋfamily :
          ℋ.card ≤
            (additiveSupportFamily A k (q - d)).card :=
        Finset.card_le_card hℋsub
      exact ⟨d, hdD, hdq,
        lt_of_lt_of_le (lt_trans hrBudget hbudgetℋ) hℋfamily⟩
    · right
      right
      obtain ⟨b, hbA, _hbq, hbGap⟩ := hgap
      have hDnonempty : D.Nonempty := by
        by_contra hDempty
        rw [Finset.not_nonempty_iff_eq_empty.mp hDempty] at hminimal
        obtain ⟨E, hER⟩ := hrepresented
        exact hminimal.1 E hER (by simp)
      obtain ⟨d, hdD⟩ := hDnonempty
      obtain ⟨t, _htb, htSurvives⟩ :=
        lowerGapRepair_extends_to_twoBlockSelectorSurvival
          P s hminimal hdD hbA hbGap hblocks
      exact ⟨t, htSurvives⟩

/-- Matching-normalized collision-amplified composition.

Choose the support threshold in the preceding theorem to be the finite-rank
matching bound.  Either growth horn then contains a matching of more than
`r` supports at some positive rank at most `k`; the only remaining outcome
is the complete lower-gap selector repair. -/
theorem IsExactTupleAsymptoticBasis.eventually_targetLocalized_destroyer_matching_or_twoBlockRepair
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    {F : ℕ → Finset ℕ} (P : IsFiniteBlockPartition A F)
    (J : Finset ℕ)
    (hk : 0 < k)
    (hblocks : ∀ j, k + 1 < (F j).card)
    (r : ℕ) :
    ∃ N, ∀ q, N ≤ q → ∀ (Q : Finset ℕ),
      ∀ s : BlockSelector F, ∀ D : Finset ℕ,
      (additiveSupportFamily A (k + 1) q).Nonempty →
      (∀ t : BlockSelector F, ∃ u ∈ Q,
        DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet t) u) →
      (∀ u ∈ Q, u ≠ q →
        ¬ DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet s) u) →
      IsInclusionMinimalDestroyer
        (additiveSupportFamily A (k + 1)) D q →
      (D : Set ℕ) ⊆ selectedSet s →
      (∀ j, j ∉ J →
        D.card * (k * additiveSupportRankBound k r) +
            (k + 1) * Q.card + k + 3 ≤
          (F j).card) →
      ((∃ h, 0 < h ∧ h ≤ k ∧
          ∃ m, ∃ M : Finset (Finset ℕ),
            M ⊆ additiveSupportFamily A h m ∧
            IsMatching M ∧ r < M.card) ∨
        ∃ t : BlockSelector F,
          ¬ DestroysAt
            (additiveSupportFamily A (k + 1))
            (selectedSet t) q) := by
  obtain ⟨N, hN⟩ :=
    hbasis.eventually_targetLocalized_destroyer_growth_or_twoBlockRepair
      P J hk hblocks (additiveSupportRankBound k r)
  refine ⟨N, ?_⟩
  intro q hNq Q s D hrepresented hcert hother hminimal
    hDselected hcontemporary
  obtain ⟨x, _hxD, _hxq, hxGrowth⟩ |
      (⟨j, _hjJ, hjGrowth⟩ | hrepair) :=
    hN q hNq Q s D hrepresented hcert hother hminimal
      hDselected hcontemporary
  · left
    obtain ⟨h, hhpos, hhk, m, M, hMsub, hMmatching, hMcard⟩ :=
      additiveSupportRankBound_forces_matching_below
        k (q - x) (Nat.le_of_lt hxGrowth)
    exact ⟨h, hhpos, hhk, m, M, hMsub, hMmatching, hMcard⟩
  · left
    obtain ⟨h, hhpos, hhk, m, M, hMsub, hMmatching, hMcard⟩ :=
      additiveSupportRankBound_forces_matching_below
        k (q - (s j).1) (Nat.le_of_lt hjGrowth)
    exact ⟨h, hhpos, hhk, m, M, hMsub, hMmatching, hMcard⟩
  · exact Or.inr hrepair

/-- Coarsen a finite-block partition into blocks with prescribed lower
cardinalities while preserving the old even-indexed blocks as distinguished
service cores.

Every even block `F (2*j)` is reserved for the new block `G j`.  The odd
blocks are reindexed by the countable sigma type
`Σ j, Fin (K j)` and supplied as `K j` pairwise-disjoint fillers.  Thus no
point of the partition is lost, the new blocks remain finite and disjoint,
and any distinguished point in `F (2*j)` remains available in `G j`. -/
theorem IsFiniteBlockPartition.exists_coarsening_preserving_evenBlocks_with_cardLower
    {A : Set ℕ} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (K : ℕ → ℕ) (hK : ∀ j, 0 < K j) :
    ∃ G : ℕ → Finset ℕ, IsFiniteBlockPartition A G ∧
      (∀ j, F (2 * j) ⊆ G j) ∧
      ∀ j, K j ≤ (G j).card := by
  classical
  let Fiber := Σ j, Fin (K j)
  let embed : ℕ → Fiber := fun j =>
    ⟨j, ⟨0, hK j⟩⟩
  have hembed : Function.Injective embed := by
    intro i j hij
    exact congrArg Sigma.fst hij
  letI : Infinite Fiber := Infinite.of_injective embed hembed
  letI : Denumerable Fiber :=
    Denumerable.ofEncodableOfInfinite Fiber
  let e : ℕ ≃ Fiber := (Denumerable.eqv Fiber).symm
  let fillerRow (j : ℕ) (a : Fin (K j)) : ℕ :=
    2 * (e.symm ⟨j, a⟩) + 1
  let fillers (j : ℕ) : Finset ℕ :=
    (Finset.univ : Finset (Fin (K j))).biUnion fun a =>
      F (fillerRow j a)
  let G (j : ℕ) : Finset ℕ :=
    F (2 * j) ∪ fillers j
  have hfillerRow_injective :
      ∀ j, Function.Injective (fillerRow j) := by
    intro j a b hab
    apply Fin.ext
    have hindex :
        e.symm (⟨j, a⟩ : Fiber) =
          e.symm (⟨j, b⟩ : Fiber) := by
      dsimp only [fillerRow] at hab
      omega
    have hpairs :
        (⟨j, a⟩ : Fiber) = ⟨j, b⟩ :=
      e.symm.injective hindex
    exact congrArg (fun p : Fiber => p.2.val) hpairs
  have hrowOwners :
      ∀ {i j} {a : Fin (K i)} {b : Fin (K j)},
        fillerRow i a = fillerRow j b → i = j := by
    intro i j a b hab
    have hindex :
        e.symm (⟨i, a⟩ : Fiber) =
          e.symm (⟨j, b⟩ : Fiber) := by
      dsimp only [fillerRow] at hab
      omega
    exact congrArg Sigma.fst (e.symm.injective hindex)
  have hnonempty : ∀ j, (G j).Nonempty := by
    intro j
    obtain ⟨x, hxF⟩ := P.nonempty (2 * j)
    exact ⟨x, Finset.mem_union_left _ hxF⟩
  have hdisjoint : Pairwise fun i j => Disjoint (G i) (G j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    rcases Finset.mem_union.mp hxi with hxiService | hxiFillers
    · rcases Finset.mem_union.mp hxj with hxjService | hxjFillers
      · exact Finset.disjoint_left.mp (P.disjoint (by omega))
          hxiService hxjService
      · obtain ⟨b, _hbUniv, hxb⟩ :=
          Finset.mem_biUnion.mp hxjFillers
        exact Finset.disjoint_left.mp
          (P.disjoint (by
            dsimp only [fillerRow]
            omega))
          hxiService hxb
    · obtain ⟨a, _haUniv, hxa⟩ :=
        Finset.mem_biUnion.mp hxiFillers
      rcases Finset.mem_union.mp hxj with hxjService | hxjFillers
      · exact Finset.disjoint_left.mp
          (P.disjoint (by
            dsimp only [fillerRow]
            omega))
          hxa hxjService
      · obtain ⟨b, _hbUniv, hxb⟩ :=
          Finset.mem_biUnion.mp hxjFillers
        have hrows :
            fillerRow i a ≠ fillerRow j b := by
          intro hrow
          exact hij (hrowOwners hrow)
        exact Finset.disjoint_left.mp (P.disjoint hrows)
          hxa hxb
  have hmem : ∀ x, x ∈ A ↔ ∃ j, x ∈ G j := by
    intro x
    constructor
    · intro hxA
      obtain ⟨r, hxr⟩ := (P.mem_iff x).mp hxA
      rcases Nat.mod_two_eq_zero_or_one r with heven | hodd
      · let j := r / 2
        have hr : r = 2 * j := by
          have hdecomp := Nat.mod_add_div r 2
          dsimp only [j]
          omega
        refine ⟨j, Finset.mem_union_left _ ?_⟩
        rwa [← hr]
      · let n := r / 2
        let p : Fiber := e n
        let j := p.1
        let a : Fin (K j) := p.2
        have hinverse :
            e.symm (⟨j, a⟩ : Fiber) = n := by
          change e.symm p = n
          exact e.symm_apply_apply n
        have hr : r = fillerRow j a := by
          have hdecomp := Nat.mod_add_div r 2
          dsimp only [fillerRow]
          omega
        refine ⟨j, Finset.mem_union_right _ ?_⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨a, Finset.mem_univ a, ?_⟩
        rwa [← hr]
    · rintro ⟨j, hxG⟩
      rcases Finset.mem_union.mp hxG with hxService | hxFillers
      · exact (P.mem_iff x).mpr ⟨2 * j, hxService⟩
      · obtain ⟨a, _haUniv, hxa⟩ :=
          Finset.mem_biUnion.mp hxFillers
        exact (P.mem_iff x).mpr ⟨fillerRow j a, hxa⟩
  have hcore : ∀ j, F (2 * j) ⊆ G j := by
    intro j x hx
    exact Finset.mem_union_left _ hx
  have hcard : ∀ j, K j ≤ (G j).card := by
    intro j
    let pick : Fin (K j) → ℕ := fun a =>
      (P.nonempty (fillerRow j a)).choose
    have hpickMem :
        ∀ a, pick a ∈ F (fillerRow j a) := by
      intro a
      exact (P.nonempty (fillerRow j a)).choose_spec
    have hpickInjective : Function.Injective pick := by
      intro a b hab
      by_contra habne
      have hrows : fillerRow j a ≠ fillerRow j b :=
        (hfillerRow_injective j).ne habne
      exact Finset.disjoint_left.mp (P.disjoint hrows)
        (hpickMem a) (by
          rw [hab]
          exact hpickMem b)
    let picks : Finset ℕ :=
      (Finset.univ : Finset (Fin (K j))).image pick
    have hpicksCard : picks.card = K j := by
      calc
        picks.card =
            (Finset.univ : Finset (Fin (K j))).card := by
          exact Finset.card_image_iff.mpr hpickInjective.injOn
        _ = K j := by simp
    have hpicksSub : picks ⊆ G j := by
      intro x hx
      obtain ⟨a, _haUniv, rfl⟩ := Finset.mem_image.mp hx
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨a, Finset.mem_univ a, hpickMem a⟩
    rw [← hpicksCard]
    exact Finset.card_le_card hpicksSub
  exact ⟨G, ⟨hnonempty, hdisjoint, hmem⟩, hcore, hcard⟩

/-- Partition an infinite set into consecutive finite intervals scheduled
against an arbitrary threshold function.

The `j`-th cut lies beyond every threshold of index at most `j+2`.  Blocks
are the nonempty consecutive slices ending at those cuts.  Consequently, a
target below cut `m` can involve only the first `m+1` block coordinates,
while a target above cut `m-1` is already beyond the threshold for that many
coordinates.  The following theorem records the partition and the two
endpoint inequalities used by the root-barrier argument. -/
theorem exists_scheduledIntervalBlockPartition
    {A : Set ℕ} (hA : A.Infinite) (threshold : ℕ → ℕ) :
    ∃ F : ℕ → Finset ℕ, ∃ _P : IsFiniteBlockPartition A F,
      ∃ cut : ℕ → ℕ,
        StrictMono cut ∧
        (∀ j i, i ≤ j + 2 → threshold i < cut j) ∧
        (∀ x ∈ F 0, x ≤ cut 0) ∧
        (∀ j x, x ∈ F (j + 1) →
          cut j < x ∧ x ≤ cut (j + 1)) := by
  classical
  let budget (r : ℕ) : ℕ :=
    ∑ i ∈ Finset.range (r + 1), (threshold i + 1)
  let next (t : ℕ) : ℕ := (hA.exists_gt t).choose
  have hnextA : ∀ t, next t ∈ A := by
    intro t
    exact (hA.exists_gt t).choose_spec.1
  have hnextGt : ∀ t, t < next t := by
    intro t
    exact (hA.exists_gt t).choose_spec.2
  let cut : ℕ → ℕ :=
    fun j => Nat.rec (next (budget 2))
      (fun i previous => next (max previous (budget (i + 3)))) j
  have hcutZero : cut 0 = next (budget 2) := by
    simp [cut]
  have hcutSucc : ∀ j,
      cut (j + 1) = next (max (cut j) (budget (j + 3))) := by
    intro j
    simp [cut]
  have hcutA : ∀ j, cut j ∈ A := by
    intro j
    cases j with
    | zero =>
        rw [hcutZero]
        exact hnextA _
    | succ j =>
        rw [hcutSucc]
        exact hnextA _
  have hcutStrict : StrictMono cut := by
    apply strictMono_nat_of_lt_succ
    intro j
    rw [hcutSucc]
    exact lt_of_le_of_lt (le_max_left _ _) (hnextGt _)
  have hcutThreshold :
      ∀ j i, i ≤ j + 2 → threshold i < cut j := by
    intro j i hij
    have hiRange : i ∈ Finset.range (j + 2 + 1) := by
      simp
      omega
    have hterm :
        threshold i + 1 ≤ budget (j + 2) := by
      dsimp only [budget]
      exact Finset.single_le_sum
        (f := fun a => threshold a + 1)
        (fun a _ha => Nat.zero_le _) hiRange
    cases j with
    | zero =>
        rw [hcutZero]
        have hgt := hnextGt (budget 2)
        have hterm' : threshold i + 1 ≤ budget 2 := by
          simpa using hterm
        omega
    | succ j =>
        rw [hcutSucc]
        have hgt :=
          hnextGt (max (cut j) (budget (j + 3)))
        have hbudget :
            budget (j + 1 + 2) ≤
              max (cut j) (budget (j + 3)) := by
          exact le_max_right _ _
        omega
  let F : ℕ → Finset ℕ
    | 0 => (Finset.range (cut 0 + 1)).filter fun x => x ∈ A
    | j + 1 =>
        (Finset.Icc (cut j + 1) (cut (j + 1))).filter
          fun x => x ∈ A
  have hFzero :
      ∀ x, x ∈ F 0 ↔ x ∈ A ∧ x ≤ cut 0 := by
    intro x
    simp [F, and_comm]
  have hFsucc :
      ∀ j x, x ∈ F (j + 1) ↔
        x ∈ A ∧ cut j < x ∧ x ≤ cut (j + 1) := by
    intro j x
    simp only [F, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hlower, hupper⟩, hxA⟩
      exact ⟨hxA, by omega, hupper⟩
    · rintro ⟨hxA, hlower, hupper⟩
      exact ⟨⟨by omega, hupper⟩, hxA⟩
  have hFnonempty : ∀ j, (F j).Nonempty := by
    intro j
    cases j with
    | zero =>
        exact ⟨cut 0, (hFzero (cut 0)).2
          ⟨hcutA 0, le_rfl⟩⟩
    | succ j =>
        exact ⟨cut (j + 1), (hFsucc j (cut (j + 1))).2
          ⟨hcutA (j + 1), hcutStrict (Nat.lt_succ_self j),
            le_rfl⟩⟩
  have hFupper : ∀ j x, x ∈ F j → x ≤ cut j := by
    intro j x hx
    cases j with
    | zero => exact (hFzero x).1 hx |>.2
    | succ j => exact (hFsucc j x).1 hx |>.2.2
  have hFlower :
      ∀ j x, x ∈ F (j + 1) → cut j < x := by
    intro j x hx
    exact (hFsucc j x).1 hx |>.2.1
  have hFdisjoint : Pairwise fun i j => Disjoint (F i) (F j) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · rw [Finset.disjoint_left]
      intro x hxi hxj
      have hiUpper := hFupper i x hxi
      have hjpos : 0 < j := lt_of_le_of_lt (Nat.zero_le i) hijlt
      obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt hjpos)
      have hij' : i ≤ j' := by omega
      have hcutLe : cut i ≤ cut j' :=
        hcutStrict.monotone hij'
      have hjLower := hFlower j' x hxj
      omega
    · rw [Finset.disjoint_left]
      intro x hxi hxj
      have hjUpper := hFupper j x hxj
      have hipos : 0 < i := lt_of_le_of_lt (Nat.zero_le j) hjilt
      obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt hipos)
      have hji' : j ≤ i' := by omega
      have hcutLe : cut j ≤ cut i' :=
        hcutStrict.monotone hji'
      have hiLower := hFlower i' x hxi
      omega
  have hFmem : ∀ x, x ∈ A ↔ ∃ j, x ∈ F j := by
    intro x
    constructor
    · intro hxA
      have hex : ∃ j, x ≤ cut j := by
        refine ⟨x + 1, ?_⟩
        have hid : x + 1 ≤ cut (x + 1) :=
          hcutStrict.id_le (x + 1)
        omega
      let dec : DecidablePred (fun j : ℕ => x ≤ cut j) :=
        fun j => Nat.decLe x (cut j)
      let m := @Nat.find (fun j => x ≤ cut j) dec hex
      have hxm : x ≤ cut m :=
        @Nat.find_spec (fun j => x ≤ cut j) dec hex
      by_cases hm : m = 0
      · exact ⟨0, (hFzero x).2 ⟨hxA, hm ▸ hxm⟩⟩
      · obtain ⟨j, hmEq⟩ :=
          Nat.exists_eq_succ_of_ne_zero hm
        have hxm' : x ≤ cut (j + 1) := by
          simpa [hmEq] using hxm
        have hnotPrev : ¬ x ≤ cut j :=
          @Nat.find_min (fun j => x ≤ cut j) dec hex
            j (by omega)
        refine ⟨j + 1, (hFsucc j x).2
          ⟨hxA, ?_, hxm'⟩⟩
        omega
    · rintro ⟨j, hxF⟩
      cases j with
      | zero => exact (hFzero x).1 hxF |>.1
      | succ j => exact (hFsucc j x).1 hxF |>.1
  refine ⟨F, ⟨hFnonempty, hFdisjoint, hFmem⟩, cut,
    hcutStrict, hcutThreshold, ?_, ?_⟩
  · intro x hx
    exact (hFzero x).1 hx |>.2
  · intro j x hx
    exact ⟨hFlower j x hx, hFupper (j + 1) x hx⟩

/-- Scheduled root-barrier normal form of a hypothetical successor
counterexample.

Choose the interval partition after the eventual rooted-matching thresholds
are known.  At a target in the `m`-th interval only the first `m+1` selector
coordinates can occur in a support, while the target is already late enough
for a rooted matching with more than `m+1` petals.  Hence every destroying
selector must select a root point.  Finite compactness then forces the union
of the roots of one late certificate to contain an entire partition block.

This removes the moving-prefix cardinal circularity completely: matching
size is compared with the actual number of active coordinates, not with an
unknown certificate bound. -/
theorem successorCounterexample_forces_scheduledFullBlockRootBarrier_withDemand
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) (k + 1))
    (demand : ℕ) :
    ∃ F : ℕ → Finset ℕ, ∃ _P : IsFiniteBlockPartition A F,
      ∀ L, ∃ Q : Finset ℕ,
        ∃ root : ℕ → Finset ℕ,
          ∃ matching : ℕ → Finset (Finset ℕ),
            (∀ q ∈ Q, L ≤ q) ∧
            (∀ s : BlockSelector F, ∃ q ∈ Q,
              DestroysAt
                (additiveSupportFamily A (k + 1))
                (selectedSet s) q) ∧
            (∀ q ∈ Q,
              (root q).card < k + 1 ∧
              matching q ⊆ additiveSupportFamily A (k + 1) q ∧
              ((supportVertices
                  (additiveSupportFamily A (k + 1)) q).image
                    (blockIndex _P)).card < (matching q).card ∧
              demand < (matching q).card ∧
              (∀ E ∈ matching q, root q ⊆ E) ∧
              (∀ E ∈ matching q, (E \ root q).Nonempty) ∧
              ∀ E ∈ matching q, ∀ G ∈ matching q, E ≠ G →
                Disjoint (E \ root q) (G \ root q)) ∧
            ∃ j, F j ⊆ Q.biUnion root := by
  classical
  have heventual :=
    hbasis.eventually_successorExactRootedMatching
  choose threshold hthreshold using heventual
  obtain ⟨F, P, cut, hcutStrict, hcutThreshold,
      hzeroUpper, hinterval⟩ :=
    exists_scheduledIntervalBlockPartition
      hbasis.infinite (fun r => threshold (max r demand))
  refine ⟨F, P, ?_⟩
  intro L
  obtain ⟨Q, hQlate, hcert⟩ :=
    (finiteBlockCertificates_of_strongInfiniteDeletion
      (strongExactDeletion_of_counterexample hcounter))
      F P (max L (cut 0))
  have hLateL : ∀ q ∈ Q, L ≤ q := by
    intro q hqQ
    exact (le_max_left L (cut 0)).trans (hQlate q hqQ)
  have hLateCut : ∀ q ∈ Q, cut 0 ≤ q := by
    intro q hqQ
    exact (le_max_right L (cut 0)).trans (hQlate q hqQ)
  have hdata :
      ∀ q, q ∈ Q →
        ∃ R : Finset ℕ, ∃ M : Finset (Finset ℕ),
          R.card < k + 1 ∧
          M ⊆ additiveSupportFamily A (k + 1) q ∧
          ((supportVertices
              (additiveSupportFamily A (k + 1)) q).image
                (blockIndex P)).card < M.card ∧
          demand < M.card ∧
          (∀ E ∈ M, R ⊆ E) ∧
          (∀ E ∈ M, (E \ R).Nonempty) ∧
          ∀ E ∈ M, ∀ G ∈ M, E ≠ G →
            Disjoint (E \ R) (G \ R) := by
    intro q hqQ
    have hex : ∃ m, q < cut m := by
      refine ⟨q + 1, ?_⟩
      exact lt_of_lt_of_le (Nat.lt_succ_self q)
        (hcutStrict.id_le (q + 1))
    let dec : DecidablePred (fun m : ℕ => q < cut m) :=
      fun m => Nat.decLt q (cut m)
    let m := @Nat.find (fun m => q < cut m) dec hex
    have hqm : q < cut m :=
      @Nat.find_spec (fun m => q < cut m) dec hex
    have hmpos : 0 < m := by
      apply Nat.pos_of_ne_zero
      intro hm
      have hcutq := hLateCut q hqQ
      rw [hm] at hqm
      omega
    have hprev : cut (m - 1) ≤ q := by
      by_contra hnot
      have hqprev : q < cut (m - 1) :=
        Nat.lt_of_not_ge hnot
      have hmin : m ≤ m - 1 :=
        @Nat.find_min' (fun m => q < cut m) dec hex
          (m - 1) hqprev
      omega
    let Active : Finset ℕ :=
      (supportVertices
        (additiveSupportFamily A (k + 1)) q).image
          (blockIndex P)
    have hActiveSub : Active ⊆ Finset.range (m + 1) := by
      intro i hiActive
      obtain ⟨x, hxVertex, rfl⟩ :=
        Finset.mem_image.mp hiActive
      obtain ⟨E, hER, hxE⟩ :=
        Finset.mem_biUnion.mp hxVertex
      have hxA : x ∈ A :=
        additiveSupportFamily_supportsIn
          A (k + 1) q E hER x hxE
      have hxq : x ≤ q :=
        additiveSupportFamily_supportsBounded
          A (k + 1) q E hER x hxE
      have hxBlock : x ∈ F (blockIndex P x) :=
        P.mem_blockIndex hxA
      have hindex : blockIndex P x ≤ m := by
        cases hidx : blockIndex P x with
        | zero => omega
        | succ j =>
            by_contra hnot
            have hmj : m ≤ j := by omega
            have hxLower :=
              (hinterval j x (by simpa [hidx] using hxBlock)).1
            have hcutLe : cut m ≤ cut j :=
              hcutStrict.monotone hmj
            omega
      exact Finset.mem_range.mpr (by omega)
    have hActiveCard : Active.card ≤ m + 1 := by
      exact (Finset.card_le_card hActiveSub).trans (by simp)
    have hmIdentity : m - 1 + 2 = m + 1 := by omega
    have hthresholdCut :
        threshold (max (m + 1) demand) < cut (m - 1) := by
      apply hcutThreshold (m - 1) (m + 1)
      omega
    obtain ⟨R, M, hRcard, hMsub, hMcard, hMroot,
        hMnonempty, hMmatching⟩ :=
      hthreshold (max (m + 1) demand) q
        ((Nat.le_of_lt hthresholdCut).trans hprev)
    refine ⟨R, M, hRcard, hMsub, ?_, ?_,
      hMroot, hMnonempty, hMmatching⟩
    change Active.card < M.card
    · exact lt_of_le_of_lt hActiveCard
        (lt_of_le_of_lt (Nat.le_max_left _ _) hMcard)
    · exact lt_of_le_of_lt (Nat.le_max_right _ _) hMcard
  let root : ℕ → Finset ℕ := fun q =>
    if hq : q ∈ Q then (hdata q hq).choose else ∅
  let matching : ℕ → Finset (Finset ℕ) := fun q =>
    if hq : q ∈ Q then (hdata q hq).choose_spec.choose else ∅
  have hspec :
      ∀ q ∈ Q,
        (root q).card < k + 1 ∧
        matching q ⊆ additiveSupportFamily A (k + 1) q ∧
        ((supportVertices
            (additiveSupportFamily A (k + 1)) q).image
              (blockIndex P)).card < (matching q).card ∧
        demand < (matching q).card ∧
        (∀ E ∈ matching q, root q ⊆ E) ∧
        (∀ E ∈ matching q, (E \ root q).Nonempty) ∧
        ∀ E ∈ matching q, ∀ G ∈ matching q, E ≠ G →
          Disjoint (E \ root q) (G \ root q) := by
    intro q hqQ
    simpa only [root, matching, dif_pos hqQ] using
      (hdata q hqQ).choose_spec.choose_spec
  have hbarrier : ∃ j, F j ⊆ Q.biUnion root := by
    apply finiteCertificate_roots_contain_partitionBlock
      P hcert root matching
    intro q hqQ
    rcases hspec q hqQ with
      ⟨_hRcard, hMsub, hActive, _hDemand,
        _hMroot, _hMnonempty, hMmatching⟩
    exact ⟨hMsub, hActive, hMmatching⟩
  exact ⟨Q, root, matching, hLateL, hcert, hspec, hbarrier⟩

/-- Demand-free scheduled root-barrier normal form. -/
theorem successorCounterexample_forces_scheduledFullBlockRootBarrier
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) (k + 1)) :
    ∃ F : ℕ → Finset ℕ, ∃ _P : IsFiniteBlockPartition A F,
      ∀ L, ∃ Q : Finset ℕ,
        ∃ root : ℕ → Finset ℕ,
          ∃ matching : ℕ → Finset (Finset ℕ),
            (∀ q ∈ Q, L ≤ q) ∧
            (∀ s : BlockSelector F, ∃ q ∈ Q,
              DestroysAt
                (additiveSupportFamily A (k + 1))
                (selectedSet s) q) ∧
            (∀ q ∈ Q,
              (root q).card < k + 1 ∧
              matching q ⊆ additiveSupportFamily A (k + 1) q ∧
              ((supportVertices
                  (additiveSupportFamily A (k + 1)) q).image
                    (blockIndex _P)).card < (matching q).card ∧
              (∀ E ∈ matching q, root q ⊆ E) ∧
              (∀ E ∈ matching q, (E \ root q).Nonempty) ∧
              ∀ E ∈ matching q, ∀ G ∈ matching q, E ≠ G →
                Disjoint (E \ root q) (G \ root q)) ∧
            ∃ j, F j ⊆ Q.biUnion root := by
  obtain ⟨F, P, hbarrier⟩ :=
    successorCounterexample_forces_scheduledFullBlockRootBarrier_withDemand
      hbasis hcounter 0
  refine ⟨F, P, ?_⟩
  intro L
  obtain ⟨Q, root, matching, hlate, hcert, hspec, hblock⟩ :=
    hbarrier L
  refine ⟨Q, root, matching, hlate, hcert, ?_, hblock⟩
  intro q hqQ
  rcases hspec q hqQ with
    ⟨hRcard, hMsub, hActive, _hDemand,
      hMroot, hMnonempty, hMmatching⟩
  exact ⟨hRcard, hMsub, hActive,
    hMroot, hMnonempty, hMmatching⟩

/-- Scheduled one-cell-per-row partition.  The `j`-th distinguished block
contains an anchor strictly above the prescribed bound `lower j`, and every
partition block is the distinguished block of exactly one row.

Only one cell is retained from each diagonal row.  This bijective thinning is
what makes a cutoff after `M` rows leave exactly `M` potentially relevant
selector values. -/
theorem HasDiagonalAnchoredAlignedTranslateCellRows.exists_scheduledThinAnchoredPartition
    {A : Set ℕ} {k : ℕ}
    (hdiag : HasDiagonalAnchoredAlignedTranslateCellRows A k)
    (lower : ℕ → ℕ) (hlower : Function.Injective lower) :
    ∃ F : ℕ → Finset ℕ, ∃ _P : IsFiniteBlockPartition A F,
      ∃ blockOfRow : ℕ → ℕ, Function.Bijective blockOfRow ∧
        ∃ anchor : ℕ → ℕ,
          (∀ j, anchor j ∈ F (blockOfRow j)) ∧
          ∀ j, lower j < anchor j := by
  classical
  obtain ⟨enumerate, henumerate, rows, hrows, hcross⟩ := hdiag
  let label (j : ℕ) : {Q : Finset ℕ // Q.Nonempty} :=
    ⟨Finset.range (lower j + 1), by simp⟩
  let rowIndex (j : ℕ) : ℕ :=
    Classical.choose (henumerate (label j))
  have hrowIndexSpec : ∀ j, enumerate (rowIndex j) = label j := by
    intro j
    exact Classical.choose_spec (henumerate (label j))
  have hrowIndexInjective : Function.Injective rowIndex := by
    intro i j hij
    have hlabels : label i = label j := by
      rw [← hrowIndexSpec i, ← hrowIndexSpec j, hij]
    have hcard := congrArg (fun Q => Q.1.card) hlabels
    apply hlower
    simpa [label] using hcard
  let scheduledRows (j : ℕ) : Finset (Finset ℕ) :=
    rows (rowIndex j)
  have hscheduledFamily : ∀ j,
      IsAnchoredAlignedTranslateCellFamily
        A k (Finset.range (lower j + 1)) (lower j + 1)
          (scheduledRows j) := by
    intro j
    have hrow := (hrows (rowIndex j)).1
    have hmax :
        (Finset.range (lower j + 1)).max' (by simp) = lower j := by
      apply
        (Finset.max'_eq_iff
          (s := Finset.range (lower j + 1)) (H := by simp)
          (lower j)).2
      constructor
      · simp
      · intro b hb
        simp only [Finset.mem_range] at hb
        omega
    simpa only [scheduledRows, hrowIndexSpec, label, hmax] using hrow
  have hscheduledNonempty :
      ∀ j, (scheduledRows j).Nonempty := by
    intro j
    rw [← Finset.card_pos]
    change 0 < (rows (rowIndex j)).card
    rw [(hrows (rowIndex j)).2]
    omega
  have hscheduledCross :
      ArePairwiseDisjointDestroyerRows scheduledRows := by
    intro i j hij C hCi D hDj
    exact hcross (rowIndex i) (rowIndex j)
      (hrowIndexInjective.ne hij) C hCi D hDj
  let chosenCell :
      ∀ j, {C : Finset ℕ // C ∈ scheduledRows j} := fun j =>
    ⟨(hscheduledNonempty j).choose,
      (hscheduledNonempty j).choose_spec⟩
  let thinRows (j : ℕ) : Finset (Finset ℕ) :=
    {(chosenCell j).1}
  have hthinNonempty : ∀ j, (thinRows j).Nonempty := by
    intro j
    simp [thinRows]
  have hthinMatching : ∀ j, IsMatching (thinRows j) := by
    intro j
    simp [thinRows, IsMatching]
  have hthinCellNonempty :
      ∀ j, ∀ C ∈ thinRows j, C.Nonempty := by
    intro j C hC
    have hCeq : C = (chosenCell j).1 :=
      Finset.mem_singleton.mp
        (show C ∈ {(chosenCell j).1} from hC)
    rw [hCeq]
    exact (hscheduledFamily j).2.1
      (chosenCell j).1 (chosenCell j).2
  have hthinCellA :
      ∀ j, ∀ C ∈ thinRows j, ∀ x ∈ C, x ∈ A := by
    intro j C hC x hxC
    have hCeq : C = (chosenCell j).1 :=
      Finset.mem_singleton.mp
        (show C ∈ {(chosenCell j).1} from hC)
    rw [hCeq] at hxC
    exact (hscheduledFamily j).2.2.1
      (chosenCell j).1 (chosenCell j).2 x hxC
  have hthinCross :
      ArePairwiseDisjointDestroyerRows thinRows := by
    intro i j hij C hCi D hDj
    have hCeq : C = (chosenCell i).1 :=
      Finset.mem_singleton.mp
        (show C ∈ {(chosenCell i).1} from hCi)
    have hDeq : D = (chosenCell j).1 :=
      Finset.mem_singleton.mp
        (show D ∈ {(chosenCell j).1} from hDj)
    rw [hCeq, hDeq]
    exact hscheduledCross i j hij
      (chosenCell i).1 (chosenCell i).2
      (chosenCell j).1 (chosenCell j).2
  obtain ⟨F, P, locate, hlocate, hcell⟩ :=
    exists_finiteBlockPartition_for_disjointRows
      hthinNonempty hthinMatching hthinCellNonempty hthinCellA hthinCross
  let CellIndex :=
    Σ j, {C : Finset ℕ // C ∈ thinRows j}
  have hwitness : ∀ c : CellIndex,
      ∃ T : Finset ℕ,
        ∃ q : {m // m ∈ Finset.range (lower c.1 + 1)},
          ∃ n a,
            c.2.1 = insert a T ∧ lower c.1 + 1 ≤ a ∧ a ∈ A ∧
            n = q.1 + a ∧
            DestroysAt
              (additiveSupportFamily A (k + 1)) (T : Set ℕ) n := by
    intro c
    have hcScheduled : c.2.1 ∈ scheduledRows c.1 := by
      have hceq : c.2.1 = (chosenCell c.1).1 :=
        Finset.mem_singleton.mp
          (show c.2.1 ∈ {(chosenCell c.1).1} from c.2.2)
      rw [hceq]
      exact (chosenCell c.1).2
    exact
      (hscheduledFamily c.1).2.2.2 c.2.1 hcScheduled
  choose core target successor cellAnchor hcellEq hanchorLower
    hanchorA hsuccessor hdestroy using hwitness
  have hanchorMem : ∀ c : CellIndex, cellAnchor c ∈ c.2.1 := by
    intro c
    rw [hcellEq c]
    exact Finset.mem_insert_self _ _
  let thinCell (j : ℕ) : {C : Finset ℕ // C ∈ thinRows j} :=
    ⟨(chosenCell j).1, by simp [thinRows]⟩
  let blockOfRow (j : ℕ) : ℕ :=
    locate ⟨j, thinCell j⟩
  have hblockInjective : Function.Injective blockOfRow := by
    intro i j hij
    have hcells :
        (⟨i, thinCell i⟩ : CellIndex) =
          (⟨j, thinCell j⟩ : CellIndex) :=
      hlocate.1 hij
    exact congrArg Sigma.fst hcells
  have hblockSurjective : Function.Surjective blockOfRow := by
    intro i
    obtain ⟨c, hc⟩ := hlocate.2 i
    refine ⟨c.1, ?_⟩
    change locate ⟨c.1, thinCell c.1⟩ = i
    rw [← hc]
    apply congrArg locate
    have hval : c.2.1 = (chosenCell c.1).1 :=
      Finset.mem_singleton.mp
        (show c.2.1 ∈ {(chosenCell c.1).1} from c.2.2)
    exact Sigma.ext rfl
      (heq_of_eq (Subtype.ext hval.symm))
  let anchor (j : ℕ) : ℕ :=
    cellAnchor (⟨j, thinCell j⟩ : CellIndex)
  have hanchorBlock : ∀ j, anchor j ∈ F (blockOfRow j) := by
    intro j
    exact hcell (⟨j, thinCell j⟩ : CellIndex)
      (hanchorMem (⟨j, thinCell j⟩ : CellIndex))
  have hanchorScheduled : ∀ j, lower j < anchor j := by
    intro j
    have h := hanchorLower (⟨j, thinCell j⟩ : CellIndex)
    change lower j + 1 ≤ anchor j at h
    change lower j < anchor j
    omega
  exact ⟨F, P, blockOfRow, ⟨hblockInjective, hblockSurjective⟩,
    anchor, hanchorBlock, hanchorScheduled⟩

/-- Scheduled anchors with independently prescribed block capacities.

First build the one-cell-per-row anchored partition and reindex it so row
`j` is block `j`.  Then reserve the even rows as service cores and use all
odd rows as filler blocks.  The `j`-th final block contains the anchor from
old row `2*j`, retains its scheduled lower bound, and has at least `K j`
points. -/
theorem HasDiagonalAnchoredAlignedTranslateCellRows.exists_scheduledLargeAnchoredPartition
    {A : Set ℕ} {k : ℕ}
    (hdiag : HasDiagonalAnchoredAlignedTranslateCellRows A k)
    (lower K : ℕ → ℕ)
    (hlower : Function.Injective lower)
    (hK : ∀ j, 0 < K j) :
    ∃ G : ℕ → Finset ℕ, ∃ _PG : IsFiniteBlockPartition A G,
      ∃ anchor : ℕ → ℕ,
        (∀ j, anchor j ∈ G j) ∧
        (∀ j, lower (2 * j) < anchor j) ∧
        ∀ j, K j ≤ (G j).card := by
  classical
  obtain ⟨F, P, blockOfRow, hblockBijective, oldAnchor,
      hanchorBlock, hanchorLower⟩ :=
    hdiag.exists_scheduledThinAnchoredPartition lower hlower
  let Frow : ℕ → Finset ℕ := fun j => F (blockOfRow j)
  have Prow : IsFiniteBlockPartition A Frow := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      exact P.nonempty (blockOfRow j)
    · intro i j hij
      exact P.disjoint (hblockBijective.1.ne hij)
    · intro x
      constructor
      · intro hxA
        obtain ⟨i, hxi⟩ := (P.mem_iff x).mp hxA
        obtain ⟨j, hj⟩ := hblockBijective.2 i
        exact ⟨j, by
          change x ∈ F (blockOfRow j)
          rwa [hj]⟩
      · rintro ⟨j, hxj⟩
        exact (P.mem_iff x).mpr
          ⟨blockOfRow j, hxj⟩
  obtain ⟨G, PG, hcore, hcard⟩ :=
    Prow.exists_coarsening_preserving_evenBlocks_with_cardLower
      K hK
  let anchor : ℕ → ℕ := fun j => oldAnchor (2 * j)
  have hanchorG : ∀ j, anchor j ∈ G j := by
    intro j
    exact hcore j (hanchorBlock (2 * j))
  have hanchorScheduled :
      ∀ j, lower (2 * j) < anchor j := by
    intro j
    exact hanchorLower (2 * j)
  exact ⟨G, PG, anchor, hanchorG, hanchorScheduled, hcard⟩

/-- Scheduled finite-prefix/difference composition with strong deletion.

The anchor schedule is chosen from the uniform destroyer-cardinality
thresholds.  A cardinal-minimal certificate is then localized at its largest
target `q`.  Above the first `M` rows the localized selector is replaced by
scheduled anchors larger than `q`; below them its choices are left unchanged.
Because all other certificate targets are at most `q`, this splice cannot
turn any target preserved by the localized selector into a destroyed one.
The certificate therefore forces `q` itself to remain destroyed, now by
exactly the first `M` choices.

Minimality of the cutoff gives `q` beyond the uniform `M`-point threshold.
Consequently the moving-prefix circularity is eliminated: cofinally often,
either a coherent difference `q-d` has arbitrarily large lower-order support
families, or `q` exposes a genuine lower-order gap translate. -/
theorem HasDiagonalAnchoredAlignedTranslateCellRows.strongDeletion_forces_cofinalLargeDifferenceFamily_or_lowerGap
    {A : Set ℕ} {k : ℕ}
    (hdiag : HasDiagonalAnchoredAlignedTranslateCellRows A (k + 1))
    (hminimal : IsStronglyMinimalExactBasis A (k + 1)) :
    ∀ r L, ∃ q, L ≤ q ∧
      ((∃ d, d ∈ A ∧ d ≤ q ∧
          ∃ ℋ : Finset (Finset ℕ),
            ℋ ⊆ additiveSupportFamily A k (q - d) ∧
            r < ℋ.card) ∨
        ∃ b, b ∈ A ∧ b ≤ q ∧
          additiveSupportFamily A k (q - b) = ∅) := by
  classical
  have huniform :=
    hminimal.1.eventually_boundedDestroyer_forces_largeDifferenceFamily_or_lowerGap
  choose threshold hthreshold using huniform
  let boundary (j : ℕ) : ℕ :=
    ∑ i ∈ Finset.range (j + 1), (threshold (i + 1) + 1)
  have hboundaryStrict : StrictMono boundary := by
    apply strictMono_nat_of_lt_succ
    intro j
    have hstep :
        boundary (j + 1) =
          boundary j + (threshold (j + 2) + 1) := by
      simp [boundary, Finset.sum_range_succ, Nat.add_assoc]
    rw [hstep]
    omega
  have hboundaryThreshold :
      ∀ j, threshold (j + 1) ≤ boundary j := by
    intro j
    have hterm :
        threshold (j + 1) + 1 ≤
          ∑ i ∈ Finset.range (j + 1),
            (threshold (i + 1) + 1) := by
      exact Finset.single_le_sum
        (f := fun i => threshold (i + 1) + 1)
        (fun i _hi => Nat.zero_le _) (by simp)
    change threshold (j + 1) ≤ boundary j
    dsimp only [boundary]
    omega
  obtain ⟨F, P, blockOfRow, hblockBijective, anchor,
      hanchorBlock, hanchorScheduled⟩ :=
    hdiag.exists_scheduledThinAnchoredPartition
      boundary hboundaryStrict.injective
  let rowOfBlock (i : ℕ) : ℕ :=
    Classical.choose (hblockBijective.2 i)
  have hblockRow : ∀ i, blockOfRow (rowOfBlock i) = i := by
    intro i
    exact Classical.choose_spec (hblockBijective.2 i)
  have hrowBlock : ∀ j, rowOfBlock (blockOfRow j) = j := by
    intro j
    exact hblockBijective.1
      ((hblockRow (blockOfRow j)).trans rfl.symm)
  intro r L
  obtain ⟨Qraw, hQrawLower, hcertRaw⟩ :=
    (finiteBlockCertificates_of_strongInfiniteDeletion hminimal.2)
      F P (max L (boundary (r + 1)))
  obtain ⟨Q, hQQraw, hcert, hlocalized⟩ :=
    exists_minimal_targetLocalized_subcertificate hcertRaw
  let arbitrary : BlockSelector F := fun i =>
    ⟨(P.nonempty i).choose, (P.nonempty i).choose_spec⟩
  obtain ⟨q₀, hq₀Q, _hq₀destroy⟩ := hcert arbitrary
  have hQnonempty : Q.Nonempty := ⟨q₀, hq₀Q⟩
  let q := Q.max' hQnonempty
  have hqQ : q ∈ Q := Finset.max'_mem Q hQnonempty
  have hqLargest : ∀ u ∈ Q, u ≤ q := by
    intro u huQ
    exact Finset.le_max' Q u huQ
  have hqLower : max L (boundary (r + 1)) ≤ q :=
    hQrawLower q (hQQraw hqQ)
  obtain ⟨t, htdestroy, htother⟩ := hlocalized q hqQ
  have hcutExists : ∃ M, q < boundary M := by
    refine ⟨q + 1, ?_⟩
    exact lt_of_lt_of_le (Nat.lt_succ_self q)
      (hboundaryStrict.id_le (q + 1))
  let M : ℕ := Nat.find hcutExists
  have hqBoundary : q < boundary M :=
    Nat.find_spec hcutExists
  have hrM : r + 1 < M := by
    by_contra hnot
    have hMle : M ≤ r + 1 := Nat.le_of_not_gt hnot
    have hboundaryLe :
        boundary M ≤ boundary (r + 1) :=
      hboundaryStrict.monotone hMle
    omega
  have hMpos : 0 < M := by omega
  have hprevBoundary : boundary (M - 1) ≤ q := by
    by_contra hnot
    have hqPrev : q < boundary (M - 1) :=
      Nat.lt_of_not_ge hnot
    have hminimalCut : M ≤ M - 1 :=
      Nat.find_min' hcutExists hqPrev
    omega
  have hqThreshold : threshold M ≤ q := by
    have hthresholdPrev := hboundaryThreshold (M - 1)
    have hsucc : M - 1 + 1 = M := Nat.sub_add_cancel hMpos
    rw [hsucc] at hthresholdPrev
    exact hthresholdPrev.trans hprevBoundary
  let s : BlockSelector F := fun i =>
    if hi : M ≤ rowOfBlock i then
      ⟨anchor (rowOfBlock i), by
        simpa only [hblockRow] using
          hanchorBlock (rowOfBlock i)⟩
    else t i
  let D : Finset ℕ :=
    (Finset.range M).image fun j => (t (blockOfRow j)).1
  have hDcard : D.card = M := by
    have hinjective :
        Function.Injective fun j => (t (blockOfRow j)).1 :=
      (P.selector_injective t).comp hblockBijective.1
    unfold D
    rw [Finset.card_image_iff.mpr hinjective.injOn]
    simp
  have hDselectedT : (D : Set ℕ) ⊆ selectedSet t := by
    intro x hxD
    obtain ⟨j, _hjM, hjx⟩ := Finset.mem_image.mp hxD
    exact ⟨blockOfRow j, hjx⟩
  have hDselectedS : (D : Set ℕ) ⊆ selectedSet s := by
    intro x hxD
    obtain ⟨j, hjM, hjx⟩ := Finset.mem_image.mp hxD
    have hjlt : j < M := Finset.mem_range.mp hjM
    refine ⟨blockOfRow j, ?_⟩
    rw [← hjx]
    simp [s, hrowBlock, not_le.mpr hjlt]
  have hselectedTail :
      ∀ x ∈ selectedSet s, x ∈ D ∨ q < x := by
    intro x hxSelected
    obtain ⟨i, rfl⟩ := hxSelected
    by_cases hi : M ≤ rowOfBlock i
    · right
      have hchoice :
          (s i).1 = anchor (rowOfBlock i) := by
        simp [s, hi]
      have hboundaryMono :
          boundary M ≤ boundary (rowOfBlock i) :=
        hboundaryStrict.monotone hi
      have hanchorLarge :=
        hanchorScheduled (rowOfBlock i)
      change q < (s i).1
      rw [hchoice]
      omega
    · left
      apply Finset.mem_image.mpr
      refine ⟨rowOfBlock i, Finset.mem_range.mpr (by omega), ?_⟩
      rw [hblockRow]
      simp [s, hi]
  have hpreservedOther :
      ∀ u ∈ Q, u ≠ q →
        ¬ DestroysAt
          (additiveSupportFamily A (k + 1)) (selectedSet s) u := by
    intro u huQ huq hsdestroy
    apply htother u huQ huq
    intro E hER
    obtain ⟨x, hxE, hxSelected⟩ :=
      Set.not_disjoint_iff.mp (hsdestroy E hER)
    have hxu : x ≤ u :=
      additiveSupportFamily_supportsBounded
        A (k + 1) u E hER x hxE
    obtain hxD | hxLarge := hselectedTail x hxSelected
    · apply Set.not_disjoint_iff.mpr
      exact ⟨x, hxE, hDselectedT (Finset.mem_coe.mpr hxD)⟩
    · have huqle := hqLargest u huQ
      omega
  obtain ⟨u, huQ, hudestroy⟩ := hcert s
  have huq : u = q := by
    by_contra hne
    exact hpreservedOther u huQ hne hudestroy
  subst u
  have hdestroyD :
      DestroysAt
        (additiveSupportFamily A (k + 1)) (D : Set ℕ) q := by
    intro E hER
    obtain ⟨x, hxE, hxSelected⟩ :=
      Set.not_disjoint_iff.mp (hudestroy E hER)
    have hxq : x ≤ q :=
      additiveSupportFamily_supportsBounded
        A (k + 1) q E hER x hxE
    obtain hxD | hxLarge := hselectedTail x hxSelected
    · apply Set.not_disjoint_iff.mpr
      exact ⟨x, hxE, Finset.mem_coe.mpr hxD⟩
    · omega
  obtain hgrowth | hgap :=
    hthreshold M D (by rw [hDcard]) q hqThreshold hdestroyD
  · refine ⟨q,
      le_trans (le_max_left L (boundary (r + 1))) hqLower,
      Or.inl ?_⟩
    obtain ⟨d, _hdD, hdA, hdq, ℋ, hℋsub, hMℋ⟩ := hgrowth
    exact ⟨d, hdA, hdq, ℋ, hℋsub, lt_trans (by omega) hMℋ⟩
  · exact ⟨q,
      le_trans (le_max_left L (boundary (r + 1))) hqLower,
      Or.inr hgap⟩

/-- Coherent scheduled-difference system.

Unlike the target-localized formulation above, this theorem uses the
scheduled anchors themselves as one fixed selector.  Its finite destroyers
are therefore literal initial segments `damagePrefix M` of one coherent
infinite sequence, independent of every later certificate.

The schedule simultaneously guarantees:

* `damagePrefix M` has exactly `M` points;
* all selected anchors after row `M` exceed the destroyed target;
* that target is beyond the uniform threshold for every `M`-point
  destroyer.

Hence arbitrarily long coherent prefixes force either more than `M`
lower-order supports at a difference `q-d` with `d` in that very prefix, or
an explicit lower-order gap translate. -/
theorem HasDiagonalAnchoredAlignedTranslateCellRows.strongDeletion_forces_scheduledCoherentDifferenceSystem
    {A : Set ℕ} {k : ℕ}
    (hdiag : HasDiagonalAnchoredAlignedTranslateCellRows A (k + 1))
    (hminimal : IsStronglyMinimalExactBasis A (k + 1)) :
    ∃ F : ℕ → Finset ℕ, ∃ _P : IsFiniteBlockPartition A F,
      ∃ base : BlockSelector F, ∃ damagePrefix : ℕ → Finset ℕ,
        Monotone damagePrefix ∧
        (∀ M, (damagePrefix M).card = M) ∧
        (∀ M, (damagePrefix M : Set ℕ) ⊆ selectedSet base) ∧
        (∀ x ∈ selectedSet base, ∃ M, x ∈ damagePrefix M) ∧
        ∀ r L, ∃ M q,
          r < M ∧ L ≤ q ∧
          DestroysAt
            (additiveSupportFamily A (k + 1))
              (damagePrefix M : Set ℕ) q ∧
          ((∃ d ∈ damagePrefix M, d ∈ A ∧ d ≤ q ∧
              ∃ ℋ : Finset (Finset ℕ),
                ℋ ⊆ additiveSupportFamily A k (q - d) ∧
                M < ℋ.card) ∨
            ∃ b, b ∈ A ∧ b ≤ q ∧
              additiveSupportFamily A k (q - b) = ∅) := by
  classical
  have huniform :=
    hminimal.1.eventually_boundedDestroyer_forces_largeDifferenceFamily_or_lowerGap
  choose threshold hthreshold using huniform
  let boundary (j : ℕ) : ℕ :=
    ∑ i ∈ Finset.range (j + 1), (threshold (i + 1) + 1)
  have hboundaryStrict : StrictMono boundary := by
    apply strictMono_nat_of_lt_succ
    intro j
    have hstep :
        boundary (j + 1) =
          boundary j + (threshold (j + 2) + 1) := by
      simp [boundary, Finset.sum_range_succ, Nat.add_assoc]
    rw [hstep]
    omega
  have hboundaryThreshold :
      ∀ j, threshold (j + 1) ≤ boundary j := by
    intro j
    have hterm :
        threshold (j + 1) + 1 ≤
          ∑ i ∈ Finset.range (j + 1),
            (threshold (i + 1) + 1) := by
      exact Finset.single_le_sum
        (f := fun i => threshold (i + 1) + 1)
        (fun i _hi => Nat.zero_le _) (by simp)
    change threshold (j + 1) ≤ boundary j
    dsimp only [boundary]
    omega
  obtain ⟨F, P, blockOfRow, hblockBijective, anchor,
      hanchorBlock, hanchorScheduled⟩ :=
    hdiag.exists_scheduledThinAnchoredPartition
      boundary hboundaryStrict.injective
  let rowOfBlock (i : ℕ) : ℕ :=
    Classical.choose (hblockBijective.2 i)
  have hblockRow : ∀ i, blockOfRow (rowOfBlock i) = i := by
    intro i
    exact Classical.choose_spec (hblockBijective.2 i)
  have hrowBlock : ∀ j, rowOfBlock (blockOfRow j) = j := by
    intro j
    exact hblockBijective.1
      ((hblockRow (blockOfRow j)).trans rfl.symm)
  let base : BlockSelector F := fun i =>
    ⟨anchor (rowOfBlock i), by
      simpa only [hblockRow] using hanchorBlock (rowOfBlock i)⟩
  let selectedAnchor (j : ℕ) : ℕ :=
    (base (blockOfRow j)).1
  have hselectedAnchor : ∀ j, selectedAnchor j = anchor j := by
    intro j
    simp [selectedAnchor, base, hrowBlock]
  have hselectedAnchorInjective :
      Function.Injective selectedAnchor :=
    (P.selector_injective base).comp hblockBijective.1
  let damagePrefix (M : ℕ) : Finset ℕ :=
    (Finset.range M).image selectedAnchor
  have hprefixMono : Monotone damagePrefix := by
    intro M N hMN x hx
    obtain ⟨j, hjM, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_image.mpr
    exact ⟨j,
      Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hjM) hMN),
      rfl⟩
  have hprefixCard : ∀ M, (damagePrefix M).card = M := by
    intro M
    unfold damagePrefix
    rw [Finset.card_image_iff.mpr hselectedAnchorInjective.injOn]
    simp
  have hprefixBase :
      ∀ M, (damagePrefix M : Set ℕ) ⊆ selectedSet base := by
    intro M x hx
    obtain ⟨j, _hjM, hjx⟩ := Finset.mem_image.mp hx
    exact ⟨blockOfRow j, hjx⟩
  have hprefixExhausts :
      ∀ x ∈ selectedSet base, ∃ M, x ∈ damagePrefix M := by
    intro x hx
    obtain ⟨i, rfl⟩ := hx
    refine ⟨rowOfBlock i + 1, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨rowOfBlock i, by simp, ?_⟩
    change
      (base (blockOfRow (rowOfBlock i))).1 = (base i).1
    rw [hblockRow]
  refine ⟨F, P, base, damagePrefix, hprefixMono, hprefixCard,
    hprefixBase, hprefixExhausts, ?_⟩
  intro r L
  obtain ⟨Q, hQLower, hcert⟩ :=
    (finiteBlockCertificates_of_strongInfiniteDeletion hminimal.2)
      F P (max L (boundary (r + 1)))
  obtain ⟨q, hqQ, hdestroyBase⟩ := hcert base
  have hqLower : max L (boundary (r + 1)) ≤ q :=
    hQLower q hqQ
  have hcutExists : ∃ M, q < boundary M := by
    refine ⟨q + 1, ?_⟩
    exact lt_of_lt_of_le (Nat.lt_succ_self q)
      (hboundaryStrict.id_le (q + 1))
  let M : ℕ := Nat.find hcutExists
  have hqBoundary : q < boundary M :=
    Nat.find_spec hcutExists
  have hrM : r + 1 < M := by
    by_contra hnot
    have hMle : M ≤ r + 1 := Nat.le_of_not_gt hnot
    have hboundaryLe :
        boundary M ≤ boundary (r + 1) :=
      hboundaryStrict.monotone hMle
    omega
  have hMpos : 0 < M := by omega
  have hprevBoundary : boundary (M - 1) ≤ q := by
    by_contra hnot
    have hqPrev : q < boundary (M - 1) :=
      Nat.lt_of_not_ge hnot
    have hminimalCut : M ≤ M - 1 :=
      Nat.find_min' hcutExists hqPrev
    omega
  have hqThreshold : threshold M ≤ q := by
    have hthresholdPrev := hboundaryThreshold (M - 1)
    have hsucc : M - 1 + 1 = M := Nat.sub_add_cancel hMpos
    rw [hsucc] at hthresholdPrev
    exact hthresholdPrev.trans hprevBoundary
  have hselectedTail :
      ∀ x ∈ selectedSet base,
        x ∈ damagePrefix M ∨ q < x := by
    intro x hxSelected
    obtain ⟨i, rfl⟩ := hxSelected
    by_cases hi : rowOfBlock i < M
    · left
      apply Finset.mem_image.mpr
      refine ⟨rowOfBlock i, Finset.mem_range.mpr hi, ?_⟩
      change
        (base (blockOfRow (rowOfBlock i))).1 = (base i).1
      rw [hblockRow]
    · right
      have hMi : M ≤ rowOfBlock i := Nat.le_of_not_gt hi
      have hboundaryMono :
          boundary M ≤ boundary (rowOfBlock i) :=
        hboundaryStrict.monotone hMi
      have hanchorLarge := hanchorScheduled (rowOfBlock i)
      have hbaseEq :
          (base i).1 = anchor (rowOfBlock i) := by
        simp [base]
      change q < (base i).1
      rw [hbaseEq]
      omega
  have hdestroyPrefix :
      DestroysAt
        (additiveSupportFamily A (k + 1))
          (damagePrefix M : Set ℕ) q := by
    intro E hER
    obtain ⟨x, hxE, hxBase⟩ :=
      Set.not_disjoint_iff.mp (hdestroyBase E hER)
    have hxq : x ≤ q :=
      additiveSupportFamily_supportsBounded
        A (k + 1) q E hER x hxE
    obtain hxD | hxLarge := hselectedTail x hxBase
    · apply Set.not_disjoint_iff.mpr
      exact ⟨x, hxE, Finset.mem_coe.mpr hxD⟩
    · omega
  obtain hgrowth | hgap :=
    hthreshold M (damagePrefix M)
      (by rw [hprefixCard M]) q hqThreshold hdestroyPrefix
  · obtain ⟨d, hdD, hdA, hdq, ℋ, hℋsub, hMℋ⟩ := hgrowth
    exact ⟨M, q, by omega,
      le_trans (le_max_left L (boundary (r + 1))) hqLower,
      hdestroyPrefix, Or.inl
        ⟨d, hdD, hdA, hdq, ℋ, hℋsub, hMℋ⟩⟩
  · exact ⟨M, q, by omega,
      le_trans (le_max_left L (boundary (r + 1))) hqLower,
      hdestroyPrefix, Or.inr hgap⟩

/-- Matching form of the scheduled composition.  Asking the preceding theorem
for the finite-rank threshold converts its large family at `q-d` into a
genuine matching of any prescribed size at some positive order at most `k`.
The only alternative is the explicit lower-order gap translate. -/
theorem HasDiagonalAnchoredAlignedTranslateCellRows.strongDeletion_forces_cofinalDifferenceMatching_or_lowerGap
    {A : Set ℕ} {k : ℕ}
    (hdiag : HasDiagonalAnchoredAlignedTranslateCellRows A (k + 1))
    (hminimal : IsStronglyMinimalExactBasis A (k + 1)) :
    ∀ r L, ∃ q, L ≤ q ∧
      ((∃ d, d ∈ A ∧ d ≤ q ∧
          ∃ j, 0 < j ∧ j ≤ k ∧
            ∃ t, ∃ M : Finset (Finset ℕ),
              M ⊆ additiveSupportFamily A j t ∧
              IsMatching M ∧ r < M.card) ∨
        ∃ b, b ∈ A ∧ b ≤ q ∧
          additiveSupportFamily A k (q - b) = ∅) := by
  intro r L
  obtain ⟨q, hLq, hgrowth | hgap⟩ :=
    hdiag.strongDeletion_forces_cofinalLargeDifferenceFamily_or_lowerGap
      hminimal (additiveSupportRankBound k r) L
  · obtain ⟨d, hdA, hdq, ℋ, hℋsub, hℋlarge⟩ := hgrowth
    obtain ⟨j, hjpos, hjk, t, M, hMsub, hMmatching, hMlarge⟩ :=
      additiveSupportRankBound_forces_matching_below
        k (q - d)
          (le_trans (Nat.le_of_lt hℋlarge)
            (Finset.card_le_card hℋsub))
    exact ⟨q, hLq, Or.inl
      ⟨d, hdA, hdq, j, hjpos, hjk, t, M,
        hMsub, hMmatching, hMlarge⟩⟩
  · exact ⟨q, hLq, Or.inr hgap⟩

/-- Exhaustive scheduled endpoint for a hypothetical strongly minimal basis
of positive order.  Either finite-translate matching growth already holds,
or arbitrarily far out the universal difference composition produces an
arbitrarily large positive-rank matching, unless the corresponding maximum
certificate target lies in a genuine lower-gap translate. -/
theorem IsStronglyMinimalExactBasis.finiteTranslateGrowth_or_cofinalDifferenceMatching_or_lowerGap
    {A : Set ℕ} {k : ℕ}
    (hminimal : IsStronglyMinimalExactBasis A (k + 1)) :
    HasSomeFiniteTranslateMatchingGrowth A (k + 1) ∨
      ∀ r L, ∃ q, L ≤ q ∧
        ((∃ d, d ∈ A ∧ d ≤ q ∧
            ∃ j, 0 < j ∧ j ≤ k ∧
              ∃ t, ∃ M : Finset (Finset ℕ),
                M ⊆ additiveSupportFamily A j t ∧
                IsMatching M ∧ r < M.card) ∨
          ∃ b, b ∈ A ∧ b ≤ q ∧
            additiveSupportFamily A k (q - b) = ∅) := by
  obtain hgrowth | hdiag :=
    finiteTranslateMatchingGrowth_or_diagonalAnchoredCellRows hminimal.1
  · exact Or.inl hgrowth
  · exact Or.inr
      (hdiag.strongDeletion_forces_cofinalDifferenceMatching_or_lowerGap
        hminimal)

/- Threshold for iterating the old-prefix/root descent.  At order `k+1`,
first ask the rooted-matching theorem for enough supports either to satisfy
the requested size `r` immediately or to retain the complete order-`k`
threshold after one old common summand is removed. -/
def additivePrefixAvoidingRootBound : ℕ → ℕ → ℕ
  | 0, _r => 2
  | k + 1, r =>
      additiveRootedMatchingBound (k + 1)
        (max r (additivePrefixAvoidingRootBound k r))

/-- Iterated certificate-prefix synchronization.  From a sufficiently large
order-`h` support family and an arbitrary finite prefix `F`, one obtains a
large genuine rooted matching at some positive rank `j ≤ h` whose common
root is disjoint from `F`.

Whenever the current root meets `F`,
`rootedMatching_disjointPrefix_or_descends` removes an old common summand
and lowers the order.  Cardinality is unchanged, so the recursion must reach
a disjoint root before order zero. -/
theorem additiveSupportFamily_forces_prefixDisjointRootedMatching_below
    {A : Set ℕ} :
    ∀ h r m (F : Finset ℕ) (𝒢 : Finset (Finset ℕ)),
      𝒢 ⊆ additiveSupportFamily A h m →
      additivePrefixAvoidingRootBound h r ≤ 𝒢.card →
      ∃ j, 0 < j ∧ j ≤ h ∧
        ∃ t R M,
          R.card < j ∧ Disjoint R F ∧
          M ⊆ additiveSupportFamily A j t ∧
          r < M.card ∧
          (∀ E ∈ M, R ⊆ E) ∧
          (∀ E ∈ M, (E \ R).Nonempty) ∧
          ∀ E ∈ M, ∀ D ∈ M, E ≠ D →
            Disjoint (E \ R) (D \ R) := by
  intro h
  induction h with
  | zero =>
      intro r m F 𝒢 h𝒢sub hlarge
      have hcard :
          𝒢.card ≤ (additiveSupportFamily A 0 m).card :=
        Finset.card_le_card h𝒢sub
      have hzero := additiveSupportFamily_zero_card_le_one A m
      simp only [additivePrefixAvoidingRootBound] at hlarge
      omega
  | succ k ih =>
      intro r m F 𝒢 h𝒢sub hlarge
      let s := max r (additivePrefixAvoidingRootBound k r)
      have hrootedLarge :
          additiveRootedMatchingBound (k + 1) s ≤ 𝒢.card := by
        simpa [additivePrefixAvoidingRootBound, s] using hlarge
      obtain ⟨R, M, hRcard, hMsub, hMcard, hMroot,
          hMnonempty, hMmatching⟩ :=
        additiveSupportSubfamily_has_large_rootedMatching
          (A := A) (h := k + 1) (r := s) (m := m)
          (𝒢 := 𝒢) h𝒢sub hrootedLarge
      have hMne : M.Nonempty := by
        rw [← Finset.card_pos]
        exact lt_of_le_of_lt (Nat.zero_le s) hMcard
      obtain hRF | ⟨d, _hdR, _hdF, _hdA, _hdm,
          ℋ, hℋsub, hℋcard⟩ :=
        rootedMatching_disjointPrefix_or_descends
          (hMsub.trans h𝒢sub) hMne hMroot
      · refine ⟨k + 1, by omega, le_rfl, m, R, M,
          hRcard, hRF, hMsub.trans h𝒢sub, ?_, hMroot,
          hMnonempty, hMmatching⟩
        exact lt_of_le_of_lt (le_max_left r
          (additivePrefixAvoidingRootBound k r)) hMcard
      · have hℋlarge :
            additivePrefixAvoidingRootBound k r ≤ ℋ.card := by
          rw [hℋcard]
          exact le_trans
            (le_max_right r (additivePrefixAvoidingRootBound k r))
            (Nat.le_of_lt hMcard)
        obtain ⟨j, hjpos, hjk, t, S, L, hScard, hSF,
            hLsub, hLcard, hLroot, hLnonempty, hLmatching⟩ :=
          ih r (m - d) F ℋ hℋsub hℋlarge
        exact ⟨j, hjpos, le_trans hjk (Nat.le_succ k),
          t, S, L, hScard, hSF, hLsub, hLcard,
          hLroot, hLnonempty, hLmatching⟩

/-- Final form of the rank attack on bounded successor transversals.  Against
any prescribed finite deletion prefix, arbitrarily large matching structure
appears at some positive predecessor rank with a genuine common root
disjoint from that prefix.

The only remaining loss is that the positive rank `j` and translated target
may move.  Synchronizing those with the minimal strong order-`k` certificate
is now the sole unresolved step in this route. -/
theorem recurrentPrefixDisjointRootedMatchings_of_boundedFullTranslateDestroyers
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hfull : HasBoundedFullTranslateDestroyersByAnchor A (k + 1) Q) :
    ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A → ∀ r L,
      ∃ n T q a x j t R M,
        L ≤ a ∧ q ∈ Q ∧ a ∈ A ∧ n = q + a ∧
        (∀ y ∈ T, y ∈ A) ∧ Disjoint T F ∧ T.Nonempty ∧
        DestroysAt
          (additiveSupportFamily A (k + 2)) (T : Set ℕ) n ∧
        x ∈ T ∧ x ≤ n ∧
        0 < j ∧ j ≤ k + 1 ∧
        R.card < j ∧ Disjoint R F ∧
        M ⊆ additiveSupportFamily A j t ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ D ∈ M, E ≠ D →
          Disjoint (E \ R) (D \ R) := by
  intro F hFA r L
  obtain ⟨n, T, q, a, x, haLower, hqQ, haA, hnqa,
      hTA, hTF, hTnonempty, hdestroy, hxT, hxn, hxlarge⟩ :=
    recurrentLargeSupportStars_of_boundedFullTranslateDestroyers
      hbasis hfull F hFA
        (additivePrefixAvoidingRootBound (k + 1) r) L
  obtain ⟨j, hjpos, hjle, t, R, M, hRcard, hRF,
      hMsub, hMcard, hMroot, hMnonempty, hMmatching⟩ :=
    additiveSupportFamily_forces_prefixDisjointRootedMatching_below
      (A := A) (h := k + 1) (r := r) (m := n - x)
      (F := F) (𝒢 := additiveSupportFamily A (k + 1) (n - x))
      Finset.Subset.rfl (Nat.le_of_lt hxlarge)
  exact ⟨n, T, q, a, x, j, t, R, M,
    haLower, hqQ, haA, hnqa, hTA, hTF, hTnonempty,
    hdestroy, hxT, hxn, hjpos, hjle, hRcard, hRF,
    hMsub, hMcard, hMroot, hMnonempty, hMmatching⟩

/-- Direct bounded-moving form of the prefix-disjoint rooted-matching
conclusion. -/
theorem recurrentPrefixDisjointRootedMatchings_of_boundedMovingOnFiniteTranslates
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hQ : Q.Nonempty)
    (hmoving :
      HasBoundedMovingOutsideTransversalsOnFiniteTranslates
        (additiveSupportFamily A (k + 2)) A Q) :
    ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A → ∀ r L,
      ∃ n T q a x j t R M,
        L ≤ a ∧ q ∈ Q ∧ a ∈ A ∧ n = q + a ∧
        (∀ y ∈ T, y ∈ A) ∧ Disjoint T F ∧ T.Nonempty ∧
        DestroysAt
          (additiveSupportFamily A (k + 2)) (T : Set ℕ) n ∧
        x ∈ T ∧ x ≤ n ∧
        0 < j ∧ j ≤ k + 1 ∧
        R.card < j ∧ Disjoint R F ∧
        M ⊆ additiveSupportFamily A j t ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ D ∈ M, E ≠ D →
          Disjoint (E \ R) (D \ R) :=
  recurrentPrefixDisjointRootedMatchings_of_boundedFullTranslateDestroyers
    hbasis
    (boundedFullTranslateDestroyersByAnchor_of_boundedMovingOnFiniteTranslates
      hbasis hQ hmoving)

/-- Strongest current exhaustive relative dichotomy.  The bad
moving-transversal branch now returns arbitrarily large rooted matchings
whose roots avoid every prescribed finite prefix; any repeated collision
with the prefix has already been consumed by strict additive-rank descent. -/
theorem finiteCoreTranslateGrowth_or_recurrentPrefixDisjointRootedMatchings
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hQ : Q.Nonempty) :
    (∃ F : Finset ℕ, (F : Set ℕ) ⊆ A ∧
      OutsideMatchingTendsToInfinityAlong
        (additiveSupportFamily A (k + 2)) F
        (finiteTargetTranslates A Q)) ∨
      (∀ F : Finset ℕ, (F : Set ℕ) ⊆ A → ∀ r L,
        ∃ n T q a x j t R M,
          L ≤ a ∧ q ∈ Q ∧ a ∈ A ∧ n = q + a ∧
          (∀ y ∈ T, y ∈ A) ∧ Disjoint T F ∧ T.Nonempty ∧
          DestroysAt
            (additiveSupportFamily A (k + 2)) (T : Set ℕ) n ∧
          x ∈ T ∧ x ≤ n ∧
          0 < j ∧ j ≤ k + 1 ∧
          R.card < j ∧ Disjoint R F ∧
          M ⊆ additiveSupportFamily A j t ∧
          r < M.card ∧
          (∀ E ∈ M, R ⊆ E) ∧
          (∀ E ∈ M, (E \ R).Nonempty) ∧
          ∀ E ∈ M, ∀ D ∈ M, E ≠ D →
            Disjoint (E \ R) (D \ R)) := by
  obtain hgrowth | hmoving :=
    finiteCore_translateMatchingGrowth_or_recurrentBoundedMoving
      (A := A) (Q := Q)
      (R := additiveSupportFamily A (k + 2))
      (additiveSupportFamily_supportsIn A (k + 2))
      (additiveSupportFamily_cardAtMost A (k + 2))
  · exact Or.inl hgrowth
  · exact Or.inr <|
      recurrentPrefixDisjointRootedMatchings_of_boundedMovingOnFiniteTranslates
        hbasis hQ hmoving

/-! ## Cofinality of the descended targets -/

/-- Total number of supports at all ranks at most `h` and all targets below
`L`.  This finite count lets matching cardinality force the moving
lower-rank target itself past `L`. -/
noncomputable def additiveLowerRankSupportCountBelow
    (A : Set ℕ) (h L : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (h + 1),
    ∑ t ∈ Finset.range L,
      (additiveSupportFamily A j t).card

theorem additiveSupportFamily_card_le_lowerRankSupportCountBelow
    {A : Set ℕ} {h L j t : ℕ}
    (hj : j ≤ h) (ht : t < L) :
    (additiveSupportFamily A j t).card ≤
      additiveLowerRankSupportCountBelow A h L := by
  classical
  have hjmem : j ∈ Finset.range (h + 1) :=
    Finset.mem_range.mpr (by omega)
  have htmem : t ∈ Finset.range L := Finset.mem_range.mpr ht
  calc
    (additiveSupportFamily A j t).card ≤
        ∑ u ∈ Finset.range L,
          (additiveSupportFamily A j u).card := by
      exact Finset.single_le_sum
        (f := fun u =>
          (additiveSupportFamily A j u).card)
        (fun _ _ => Nat.zero_le _) htmem
    _ ≤ ∑ i ∈ Finset.range (h + 1),
        ∑ u ∈ Finset.range L,
          (additiveSupportFamily A i u).card := by
      exact Finset.single_le_sum
        (f := fun i =>
          ∑ u ∈ Finset.range L,
            (additiveSupportFamily A i u).card)
        (fun _ _ => Nat.zero_le _) hjmem
    _ = additiveLowerRankSupportCountBelow A h L := rfl

/-- A hypothetical negative successor deletion forces genuinely cofinal
lower-order representation growth.

Fix independently a lower-difference cutoff `Ltarget`, a certificate-target
cutoff `Lcertificate`, and a cardinal demand `r`.  Schedule every successor
rooted matching to be larger than both `r` and the total number of all
order-`k` supports below `Ltarget`.  The finite certificate then covers one
whole partition block by common roots.  Removing any point of that block
preserves the matching cardinality.  The descended target cannot be below
`Ltarget`, since the entire order-`k` support family there would be too
small.

Thus neither a moving contemporary block nor a repeated old-coordinate
collision can trap the descent at bounded differences: under the
counterexample, arbitrarily large order-`k` support families occur at
arbitrarily late coherent differences `q-x`, with `q` itself arbitrarily
late. -/
theorem successorCounterexample_forces_cofinal_largeDifferenceFamily
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) (k + 1)) :
    ∀ r Ltarget Lcertificate, ∃ q x,
      ∃ lower : Finset (Finset ℕ),
        Lcertificate ≤ q ∧ x ∈ A ∧ x ≤ q ∧
        Ltarget ≤ q - x ∧
        lower ⊆ additiveSupportFamily A k (q - x) ∧
        r < lower.card := by
  classical
  intro r Ltarget Lcertificate
  let count :=
    additiveLowerRankSupportCountBelow A k Ltarget
  let demand := max r count
  obtain ⟨F, P, hbarrier⟩ :=
    successorCounterexample_forces_scheduledFullBlockRootBarrier_withDemand
      hbasis hcounter demand
  obtain ⟨Q, root, matching, hlate, _hcert, hspec,
      j, hblock⟩ :=
    hbarrier Lcertificate
  have hmatching :
      ∀ q ∈ Q,
        matching q ⊆ additiveSupportFamily A (k + 1) q ∧
        ((supportVertices
            (additiveSupportFamily A (k + 1)) q).image
              (blockIndex P)).card < (matching q).card ∧
        ∀ E ∈ matching q, root q ⊆ E := by
    intro q hqQ
    rcases hspec q hqQ with
      ⟨_hRcard, hMsub, hActive, _hDemand,
        hMroot, _hMnonempty, _hMmatching⟩
    exact ⟨hMsub, hActive, hMroot⟩
  obtain ⟨x, hxF⟩ := P.nonempty j
  obtain ⟨q, hqQ, _hxRoot, hxA, hxq, lower,
      hlowerSub, hlowerCard, _hActiveLower⟩ :=
    fullBlockRootBarrier_descends_to_differenceFamilies
      P root matching hmatching hblock x hxF
  have hDemandLower : demand < lower.card := by
    have hDemandMatching := (hspec q hqQ).2.2.2.1
    simpa [hlowerCard] using hDemandMatching
  have hTargetLower : Ltarget ≤ q - x := by
    by_contra hnot
    have htargetSmall : q - x < Ltarget :=
      Nat.lt_of_not_ge hnot
    have hfamilyBound :
        (additiveSupportFamily A k (q - x)).card ≤ count := by
      exact additiveSupportFamily_card_le_lowerRankSupportCountBelow
        le_rfl htargetSmall
    have hlowerBound :
        lower.card ≤
          (additiveSupportFamily A k (q - x)).card :=
      Finset.card_le_card hlowerSub
    have hcountLower : count < lower.card :=
      lt_of_le_of_lt (le_max_right r count) hDemandLower
    omega
  refine ⟨q, x, lower, hlate q hqQ, hxA, hxq,
    hTargetLower, hlowerSub, ?_⟩
  exact lt_of_le_of_lt (le_max_left r count) hDemandLower

/-- The descended target in the fresh-rooted-matching branch can be forced
arbitrarily late.  Request a matching larger than the total number of all
supports at every lower rank and every target below `Ltarget`; the returned
matching cannot live in that finite region. -/
theorem cofinalPrefixDisjointRootedMatchings_of_boundedFullTranslateDestroyers
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hfull : HasBoundedFullTranslateDestroyersByAnchor A (k + 1) Q) :
    ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A → ∀ r Lanchor Ltarget,
      ∃ n T q a x j t R M,
        Lanchor ≤ a ∧ Ltarget ≤ t ∧
        q ∈ Q ∧ a ∈ A ∧ n = q + a ∧
        (∀ y ∈ T, y ∈ A) ∧ Disjoint T F ∧ T.Nonempty ∧
        DestroysAt
          (additiveSupportFamily A (k + 2)) (T : Set ℕ) n ∧
        x ∈ T ∧ x ≤ n ∧
        0 < j ∧ j ≤ k + 1 ∧
        R.card < j ∧ Disjoint R F ∧
        M ⊆ additiveSupportFamily A j t ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ D ∈ M, E ≠ D →
          Disjoint (E \ R) (D \ R) := by
  intro F hFA r Lanchor Ltarget
  let count :=
    additiveLowerRankSupportCountBelow A (k + 1) Ltarget
  obtain ⟨n, T, q, a, x, j, t, R, M,
      haLower, hqQ, haA, hnqa, hTA, hTF, hTnonempty,
      hdestroy, hxT, hxn, hjpos, hjle, hRcard, hRF,
      hMsub, hMcard, hMroot, hMnonempty, hMmatching⟩ :=
    recurrentPrefixDisjointRootedMatchings_of_boundedFullTranslateDestroyers
      hbasis hfull F hFA (max r count) Lanchor
  have htLower : Ltarget ≤ t := by
    by_contra hnot
    have ht : t < Ltarget := Nat.lt_of_not_ge hnot
    have hsupportBound :
        (additiveSupportFamily A j t).card ≤ count := by
      exact additiveSupportFamily_card_le_lowerRankSupportCountBelow
        hjle ht
    have hMle :
        M.card ≤ (additiveSupportFamily A j t).card :=
      Finset.card_le_card hMsub
    have hcountM : count < M.card :=
      lt_of_le_of_lt (le_max_right r count) hMcard
    omega
  refine ⟨n, T, q, a, x, j, t, R, M,
    haLower, htLower, hqQ, haA, hnqa, hTA, hTF, hTnonempty,
    hdestroy, hxT, hxn, hjpos, hjle, hRcard, hRF,
    hMsub, ?_, hMroot, hMnonempty, hMmatching⟩
  exact lt_of_le_of_lt (le_max_left r count) hMcard

/-! ## Lifting the descended rank back to the original order -/

/-- Repeatedly insert the same fresh basis element.  At support level the set
stabilizes after the first insertion, while the tuple order and represented
target increase at every step. -/
theorem insert_mem_additiveSupportFamily_iterate
    {A : Set ℕ} {j t c d : ℕ} {E : Finset ℕ}
    (hcA : c ∈ A)
    (hER : E ∈ additiveSupportFamily A j t) :
    insert c E ∈
      additiveSupportFamily A (j + d + 1) (t + (d + 1) * c) := by
  induction d with
  | zero =>
      have h := insert_mem_additiveSupportFamily_succ hcA hER
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  | succ d ih =>
      have h := insert_mem_additiveSupportFamily_succ hcA ih
      have horder : (j + d + 1) + 1 = j + (d + 1) + 1 := by omega
      have htarget :
          c + (t + (d + 1) * c) =
            t + ((d + 1) + 1) * c := by ring
      simpa [horder, htarget] using h

/-- Lift a rooted matching from a strict lower order `j` back to order `h`.
Choose one basis element outside the finite prefix, root, and every support,
and use it repeatedly as padding.  Because the padding point is fresh, the
support map is injective and every petal is unchanged exactly. -/
theorem lift_rootedMatching_to_strictHigherOrder
    {A : Set ℕ} (hA : A.Infinite)
    {j h t : ℕ} (hjh : j < h)
    {F R : Finset ℕ} {M : Finset (Finset ℕ)}
    (hRcard : R.card < j)
    (hRF : Disjoint R F)
    (hMsub : M ⊆ additiveSupportFamily A j t)
    (hMroot : ∀ E ∈ M, R ⊆ E)
    (hMnonempty : ∀ E ∈ M, (E \ R).Nonempty)
    (hMmatching : ∀ E ∈ M, ∀ D ∈ M, E ≠ D →
      Disjoint (E \ R) (D \ R)) :
    ∃ t' R' M',
      t ≤ t' ∧ R'.card < h ∧ Disjoint R' F ∧
      M'.card = M.card ∧
      M' ⊆ additiveSupportFamily A h t' ∧
      (∀ E ∈ M', R' ⊆ E) ∧
      (∀ E ∈ M', (E \ R').Nonempty) ∧
      ∀ E ∈ M', ∀ D ∈ M', E ≠ D →
        Disjoint (E \ R') (D \ R') := by
  classical
  obtain ⟨d, hd⟩ : ∃ d, h = j + d + 1 := by
    exact ⟨h - j - 1, by omega⟩
  let U : Finset ℕ := F ∪ R ∪ M.biUnion id
  have hnotSubset : ¬ A ⊆ (U : Set ℕ) := by
    intro hAU
    exact hA (U.finite_toSet.subset hAU)
  obtain ⟨c, hcA, hcU⟩ := Set.not_subset.mp hnotSubset
  have hcF : c ∉ F := by
    intro hcF
    exact hcU (Finset.mem_union_left _ (Finset.mem_union_left _ hcF))
  have hcR : c ∉ R := by
    intro hcR
    exact hcU (Finset.mem_union_left _
      (Finset.mem_union_right _ hcR))
  have hcM : ∀ E ∈ M, c ∉ E := by
    intro E hEM hcE
    exact hcU (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨E, hEM, hcE⟩))
  let lift : Finset ℕ → Finset ℕ := fun E => insert c E
  have hliftInjective : Set.InjOn lift (M : Set (Finset ℕ)) := by
    intro E hEM D hDM hED
    have hcE : c ∉ E := hcM E hEM
    have hcD : c ∉ D := hcM D hDM
    have herase := congrArg (fun G : Finset ℕ => G.erase c) hED
    simpa [lift, hcE, hcD] using herase
  let M' := M.image lift
  let R' := insert c R
  let t' := t + (d + 1) * c
  have hM'card : M'.card = M.card := by
    exact Finset.card_image_iff.mpr hliftInjective
  have hM'sub : M' ⊆ additiveSupportFamily A h t' := by
    intro G hGM'
    obtain ⟨E, hEM, rfl⟩ := Finset.mem_image.mp hGM'
    have hlift :=
      insert_mem_additiveSupportFamily_iterate
        (d := d) hcA (hMsub hEM)
    simpa [lift, t', hd] using hlift
  have hR'card : R'.card < h := by
    have hle : R'.card ≤ R.card + 1 := Finset.card_insert_le c R
    omega
  have hR'F : Disjoint R' F := by
    rw [Finset.disjoint_left]
    intro y hyR' hyF
    rcases Finset.mem_insert.mp hyR' with rfl | hyR
    · exact hcF hyF
    · exact Finset.disjoint_left.mp hRF hyR hyF
  have hpetalEq : ∀ E ∈ M,
      lift E \ R' = E \ R := by
    intro E hEM
    ext y
    simp only [lift, R', Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · rintro ⟨hyc | hyE, hnot⟩
      · exact (hnot (Or.inl hyc)).elim
      · exact ⟨hyE, fun hyR => hnot (Or.inr hyR)⟩
    · rintro ⟨hyE, hyR⟩
      refine ⟨Or.inr hyE, ?_⟩
      rintro (hyc | hyR')
      · subst y
        exact hcM E hEM hyE
      · exact hyR hyR'
  have hM'root : ∀ G ∈ M', R' ⊆ G := by
    intro G hGM
    obtain ⟨E, hEM, rfl⟩ := Finset.mem_image.mp hGM
    intro y hyR'
    rcases Finset.mem_insert.mp hyR' with rfl | hyR
    · exact Finset.mem_insert_self _ E
    · exact Finset.mem_insert_of_mem (hMroot E hEM hyR)
  have hM'nonempty : ∀ G ∈ M', (G \ R').Nonempty := by
    intro G hGM
    obtain ⟨E, hEM, rfl⟩ := Finset.mem_image.mp hGM
    rw [hpetalEq E hEM]
    exact hMnonempty E hEM
  have hM'matching : ∀ G ∈ M', ∀ H ∈ M', G ≠ H →
      Disjoint (G \ R') (H \ R') := by
    intro G hGM H hHM hGH
    obtain ⟨E, hEM, hEG⟩ := Finset.mem_image.mp hGM
    obtain ⟨D, hDM, hDH⟩ := Finset.mem_image.mp hHM
    have hED : E ≠ D := by
      intro hED
      apply hGH
      rw [← hEG, ← hDH, hED]
    rw [← hEG, ← hDH, hpetalEq E hEM, hpetalEq D hDM]
    exact hMmatching E hEM D hDM hED
  exact ⟨t', R', M', by dsimp [t']; omega,
    hR'card, hR'F, hM'card, hM'sub,
    hM'root, hM'nonempty, hM'matching⟩

/-- Normalize a sufficiently large rooted-matching source simultaneously in
rank, root location, and target location.

First consume every collision of the common root with `F` by strict rank
descent.  A matching larger than the total number of supports of ranks at
most `H` below `L` cannot end at a target below `L`.  Finally, if descent
lowered the rank, one fresh repeated padding point lifts the matching back
to order `H` without changing its petals or their avoidance of `F`. -/
theorem largeSupportFamily_forces_cofinal_prefixDisjointRootedMatching
    {A : Set ℕ} {H h r L m : ℕ} {F : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A H)
    (hhH : h ≤ H)
    {𝒢 : Finset (Finset ℕ)}
    (h𝒢sub : 𝒢 ⊆ additiveSupportFamily A h m)
    (hlarge :
      additivePrefixAvoidingRootBound h
          (max r (additiveLowerRankSupportCountBelow A H L)) ≤
        𝒢.card) :
    ∃ t R M,
      L ≤ t ∧ R.card < H ∧ Disjoint R F ∧
      M ⊆ additiveSupportFamily A H t ∧
      r < M.card ∧
      (∀ E ∈ M, R ⊆ E) ∧
      (∀ E ∈ M, (E \ R).Nonempty) ∧
      ∀ E ∈ M, ∀ D ∈ M, E ≠ D →
        Disjoint (E \ R) (D \ R) := by
  let size := max r (additiveLowerRankSupportCountBelow A H L)
  obtain ⟨j, _hjpos, hjh, t, R, M, hRcard, hRF,
      hMsub, hMcard, hMroot, hMnonempty, hMmatching⟩ :=
    additiveSupportFamily_forces_prefixDisjointRootedMatching_below
      h size m F 𝒢 h𝒢sub (by simpa only [size] using hlarge)
  have hjH : j ≤ H := hjh.trans hhH
  have htLower : L ≤ t := by
    by_contra hnot
    have ht : t < L := Nat.lt_of_not_ge hnot
    have hfamilyBound :
        (additiveSupportFamily A j t).card ≤
          additiveLowerRankSupportCountBelow A H L :=
      additiveSupportFamily_card_le_lowerRankSupportCountBelow hjH ht
    have hMle : M.card ≤
        (additiveSupportFamily A j t).card :=
      Finset.card_le_card hMsub
    have hcountM :
        additiveLowerRankSupportCountBelow A H L < M.card :=
      lt_of_le_of_lt
        (le_max_right r
          (additiveLowerRankSupportCountBelow A H L))
        hMcard
    omega
  by_cases hjtop : j = H
  · subst j
    exact ⟨t, R, M, htLower, hRcard, hRF, hMsub,
      lt_of_le_of_lt
        (le_max_left r
          (additiveLowerRankSupportCountBelow A H L))
        hMcard,
      hMroot, hMnonempty, hMmatching⟩
  · have hjlt : j < H := lt_of_le_of_ne hjH hjtop
    obtain ⟨t', R', M', htt', hR'card, hR'F, hM'card,
        hM'sub, hM'root, hM'nonempty, hM'matching⟩ :=
      lift_rootedMatching_to_strictHigherOrder
        hbasis.infinite hjlt hRcard hRF hMsub
          hMroot hMnonempty hMmatching
    refine ⟨t', R', M', htLower.trans htt', hR'card, hR'F,
      hM'sub, ?_, hM'root, hM'nonempty, hM'matching⟩
    rw [hM'card]
    exact lt_of_le_of_lt
      (le_max_left r
        (additiveLowerRankSupportCountBelow A H L))
      hMcard

/-- The full normalized consequence of the scheduled root-barrier attack.

Under a hypothetical negative successor deletion, every prescribed finite
prefix can be avoided by an arbitrarily large rooted matching back at the
original predecessor order `k`, and both the certificate target which
generated it and the normalized matching target can be forced arbitrarily
late.

The proof first asks the full-block descent theorem for enough order-`k`
supports to absorb every possible root collision with `F` and every
bounded-target outcome.  The prefix synchronization theorem then consumes
root collisions by strict rank descent, forces the resulting target past
`Lmatching`, and pads back to exact order `k` without changing the petals.
-/
theorem successorCounterexample_forces_cofinal_prefixDisjointPredecessorMatching
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) (k + 1)) :
    ∀ F : Finset ℕ, ∀ r Lcertificate Lmatching,
      ∃ q x t R M,
        Lcertificate ≤ q ∧ x ∈ A ∧ x ≤ q ∧
        Lmatching ≤ t ∧ R.card < k ∧ Disjoint R F ∧
        M ⊆ additiveSupportFamily A k t ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ D ∈ M, E ≠ D →
          Disjoint (E \ R) (D \ R) := by
  intro F r Lcertificate Lmatching
  let size :=
    max r (additiveLowerRankSupportCountBelow A k Lmatching)
  let need := additivePrefixAvoidingRootBound k size
  obtain ⟨q, x, lower, hqLate, hxA, hxq, _hdifferenceLate,
      hlowerSub, hlowerLarge⟩ :=
    successorCounterexample_forces_cofinal_largeDifferenceFamily
      hbasis hcounter need Lmatching Lcertificate
  obtain ⟨t, R, M, htLate, hRcard, hRF, hMsub, hMlarge,
      hMroot, hMnonempty, hMmatching⟩ :=
    largeSupportFamily_forces_cofinal_prefixDisjointRootedMatching
      hbasis (h := k) (r := r) (L := Lmatching) (F := F)
        le_rfl hlowerSub (Nat.le_of_lt hlowerLarge)
  exact ⟨q, x, t, R, M, hqLate, hxA, hxq, htLate,
    hRcard, hRF, hMsub, hMlarge, hMroot, hMnonempty, hMmatching⟩

/-- One stage of the coherent predecessor common-survival construction.

The root avoids every previously used support vertex, and the matching has
more than `|used|+2` petals.  After discarding the at most `|used|` supports
which meet the past, at least two completely fresh petals remain. -/
structure FreshPredecessorRootedMatchingStep
    (A : Set ℕ) (k : ℕ) (used : Finset ℕ) (last demand : ℕ) where
  target : ℕ
  root : Finset ℕ
  matching : Finset (Finset ℕ)
  target_gt : last < target
  root_card : root.card < k
  root_disjoint : Disjoint root used
  matching_sub : matching ⊆ additiveSupportFamily A k target
  matching_large : used.card + demand < matching.card
  root_common : ∀ E ∈ matching, root ⊆ E
  petal_nonempty : ∀ E ∈ matching, (E \ root).Nonempty
  petals_disjoint : ∀ E ∈ matching, ∀ D ∈ matching, E ≠ D →
    Disjoint (E \ root) (D \ root)

/-- The cofinal prefix-disjoint matching theorem supplies every fresh stage
needed by the common-survival recursion. -/
theorem freshPredecessorRootedMatchingStep_nonempty
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) (k + 1))
    (used : Finset ℕ) (last demand : ℕ) :
    Nonempty
      (FreshPredecessorRootedMatchingStep A k used last demand) := by
  obtain ⟨_q, _x, t, R, M, _hqLate, _hxA, _hxq, htLate,
      hRcard, hRF, hMsub, hMlarge, hMroot, hMnonempty,
      hMmatching⟩ :=
    successorCounterexample_forces_cofinal_prefixDisjointPredecessorMatching
      hbasis hcounter used (used.card + demand) 0 (last + 1)
  exact ⟨⟨t, R, M, by omega, hRcard, hRF, hMsub, hMlarge,
    hMroot, hMnonempty, hMmatching⟩⟩

/-- A basis point chosen outside one finite set.  Packaging the witness as
data lets the coherent recursion retain a new anchor at every stage. -/
structure FreshBasisPoint (A : Set ℕ) (blocked : Finset ℕ) where
  point : ℕ
  point_mem : point ∈ A
  point_fresh : point ∉ blocked

theorem freshBasisPoint_nonempty
    {A : Set ℕ} (hA : A.Infinite) (blocked : Finset ℕ) :
    Nonempty (FreshBasisPoint A blocked) := by
  obtain ⟨a, haA, haFresh⟩ :=
    hA.exists_notMem_finset blocked
  exact ⟨⟨a, haA, haFresh⟩⟩

/-- A successor counterexample forces one coherent infinite predecessor
common-survival reservoir.

Recursively choose a rooted order-`k` matching beyond the preceding target,
with its root disjoint from every support used earlier.  Discard the supports
which still meet the past.  Pairwise-disjoint petals show that at most
`|used|` supports are discarded, so more than two fresh supports remain.
The union of their petals is the next deletion block.

The blocks are pairwise disjoint.  For the target belonging to block `i`,
every support in its fresh matching is disjoint from all other blocks, and
one selected point in block `i` can meet at most one petal.  A second petal
therefore survives.  Thus every block selector preserves every target in a
strictly increasing, hence infinite, predecessor target stream.

This is an actual infinite deletion object, not merely a sequence of local
certificates; the only remaining migration is that strong deletion must
place its late finite certificates outside this entire protected stream. -/
theorem successorCounterexample_forces_cofinalPredecessorCommonSurvivalPartition_avoiding
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) (k + 1))
    (reserved : Finset ℕ) :
    ∃ K : Set ℕ, ∃ cell : ℕ → Finset ℕ, ∃ target : ℕ → ℕ,
      ∃ retained : ℕ → ℕ,
      K ⊆ A ∧ K.Infinite ∧ Disjoint K (reserved : Set ℕ) ∧
      IsFiniteBlockPartition K cell ∧
      StrictMono target ∧
      Function.Injective retained ∧
      (∀ j, retained j ∈ A) ∧
      Disjoint K (Set.range retained) ∧
      (∀ i, i + 2 < (cell i).card) ∧
      ∀ s : BlockSelector cell, ∀ i,
        ∃ E ∈ additiveSupportFamily A k (target i),
          Disjoint (E : Set ℕ) (selectedSet s) := by
  classical
  let State := Finset ℕ × ℕ
  let initial : State := (reserved, 0)
  let chooseStep : (i : ℕ) → (st : State) →
      FreshPredecessorRootedMatchingStep A k st.1 st.2 (i + 2) :=
    fun _i st => Classical.choice
      (freshPredecessorRootedMatchingStep_nonempty
        hbasis hcounter st.1 st.2 (_i + 2))
  let occupied : ℕ → State → Finset ℕ := fun i st =>
    st.1 ∪ (chooseStep i st).matching.biUnion id
  let chooseAnchor : (i : ℕ) → (st : State) →
      FreshBasisPoint A (occupied i st) :=
    fun i st => Classical.choice
      (freshBasisPoint_nonempty hbasis.infinite (occupied i st))
  let advance : ℕ → State → State := fun i st =>
    (occupied i st ∪ {(chooseAnchor i st).point},
      (chooseStep i st).target)
  let state : ℕ → State := fun i =>
    Nat.rec initial (fun j st => advance j st) i
  let step (i : ℕ) := chooseStep i (state i)
  let used (i : ℕ) : Finset ℕ := (state i).1
  let target (i : ℕ) : ℕ := (step i).target
  let root (i : ℕ) : Finset ℕ := (step i).root
  let matching (i : ℕ) : Finset (Finset ℕ) :=
    (step i).matching
  let retained (i : ℕ) : ℕ :=
    (chooseAnchor i (state i)).point
  have hstate_succ : ∀ i, state (i + 1) = advance i (state i) := by
    intro i
    simp [state]
  have hused_succ : ∀ i,
      used (i + 1) =
        (used i ∪ (matching i).biUnion id) ∪ {retained i} := by
    intro i
    change (state (i + 1)).1 =
      ((state i).1 ∪
        (chooseStep i (state i)).matching.biUnion id) ∪
          {(chooseAnchor i (state i)).point}
    rw [hstate_succ]
  have hlast_succ : ∀ i, (state (i + 1)).2 = target i := by
    intro i
    change (state (i + 1)).2 =
      (chooseStep i (state i)).target
    rw [hstate_succ]
  have hused_step : ∀ i, used i ⊆ used (i + 1) := by
    intro i
    rw [hused_succ]
    exact Finset.Subset.trans Finset.subset_union_left
      Finset.subset_union_left
  have hused_mono : Monotone used :=
    monotone_nat_of_le_succ hused_step
  have hreservedUsed : ∀ i, reserved ⊆ used i := by
    intro i
    have hmono := hused_mono (Nat.zero_le i)
    simpa only [used, state, initial, Nat.rec_zero] using hmono
  have hmatching_into_next :
      ∀ i, ∀ E ∈ matching i, E ⊆ used (i + 1) := by
    intro i E hEM x hxE
    rw [hused_succ]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨E, hEM, hxE⟩))
  have hretainedA : ∀ i, retained i ∈ A := by
    intro i
    exact (chooseAnchor i (state i)).point_mem
  have hretainedFresh : ∀ i,
      retained i ∉ used i ∪ (matching i).biUnion id := by
    intro i
    exact (chooseAnchor i (state i)).point_fresh
  have hretained_into_next : ∀ i, retained i ∈ used (i + 1) := by
    intro i
    rw [hused_succ]
    simp
  have htargetStrict : StrictMono target := by
    apply strictMono_nat_of_lt_succ
    intro i
    have hnext := (step (i + 1)).target_gt
    change (state (i + 1)).2 < target (i + 1) at hnext
    rw [hlast_succ] at hnext
    exact hnext
  let good (i : ℕ) : Finset (Finset ℕ) :=
    (matching i).filter fun E => Disjoint E (used i)
  let bad (i : ℕ) : Finset (Finset ℕ) :=
    (matching i).filter fun E => ¬ Disjoint E (used i)
  have hbadCard : ∀ i, (bad i).card ≤ (used i).card := by
    intro i
    have hcommon :
        ∀ E : {E // E ∈ bad i},
          ∃ x, x ∈ E.1 ∧ x ∈ used i := by
      intro E
      exact Finset.not_disjoint_iff.mp
        (Finset.mem_filter.mp E.2).2
    let pick : {E // E ∈ bad i} → {x // x ∈ used i} := fun E => by
      exact ⟨Classical.choose (hcommon E),
        (Classical.choose_spec (hcommon E)).2⟩
    have hpickMem :
        ∀ E : {E // E ∈ bad i}, (pick E).1 ∈ E.1 \ root i := by
      intro E
      have hxE :
          (pick E).1 ∈ E.1 ∧ (pick E).1 ∈ used i := by
        change Classical.choose (hcommon E) ∈ E.1 ∧
          Classical.choose (hcommon E) ∈ used i
        exact Classical.choose_spec (hcommon E)
      apply Finset.mem_sdiff.mpr
      refine ⟨hxE.1, ?_⟩
      intro hxRoot
      exact Finset.disjoint_left.mp (step i).root_disjoint
        hxRoot hxE.2
    have hpickInjective : Function.Injective pick := by
      intro E D hED
      apply Subtype.ext
      by_contra hne
      have hEM : E.1 ∈ matching i :=
        (Finset.mem_filter.mp E.2).1
      have hDM : D.1 ∈ matching i :=
        (Finset.mem_filter.mp D.2).1
      have hx :
          (pick E).1 = (pick D).1 :=
        congrArg Subtype.val hED
      exact
        (Finset.not_disjoint_iff.mpr
          ⟨(pick E).1, hpickMem E, hx ▸ hpickMem D⟩)
        ((step i).petals_disjoint E.1 hEM D.1 hDM hne)
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective pick hpickInjective
  have hgoodLarge : ∀ i, i + 2 < (good i).card := by
    intro i
    have hsplit :
        (good i).card + (bad i).card = (matching i).card := by
      simpa only [good, bad] using
        (Finset.card_filter_add_card_filter_not
          (s := matching i) fun E => Disjoint E (used i))
    have hlarge := (step i).matching_large
    change (used i).card + (i + 2) < (matching i).card at hlarge
    have hbad := hbadCard i
    omega
  have hgoodSub : ∀ i, good i ⊆ matching i := by
    intro i E hE
    exact (Finset.mem_filter.mp hE).1
  have hgoodPast : ∀ i, ∀ E ∈ good i,
      Disjoint E (used i) := by
    intro i E hE
    exact (Finset.mem_filter.mp hE).2
  let cell (i : ℕ) : Finset ℕ :=
    (good i).biUnion fun E => E \ root i
  have hcellMatchingUnion : ∀ i,
      cell i ⊆ (matching i).biUnion id := by
    intro i x hxCell
    obtain ⟨E, hEgood, hxPetal⟩ :=
      Finset.mem_biUnion.mp hxCell
    exact Finset.mem_biUnion.mpr
      ⟨E, hgoodSub i hEgood, (Finset.mem_sdiff.mp hxPetal).1⟩
  have hcell_into_next : ∀ i, cell i ⊆ used (i + 1) := by
    intro i x hxCell
    rw [hused_succ]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _
        (hcellMatchingUnion i hxCell))
  have hcellNonempty : ∀ i, (cell i).Nonempty := by
    intro i
    have hgoodNonempty : (good i).Nonempty := by
      exact Finset.card_pos.mp
        (by have := hgoodLarge i; omega)
    obtain ⟨E, hEgood⟩ := hgoodNonempty
    obtain ⟨x, hxPetal⟩ :=
      (step i).petal_nonempty E (hgoodSub i hEgood)
    exact ⟨x, Finset.mem_biUnion.mpr
      ⟨E, hEgood, hxPetal⟩⟩
  have hgoodCardLeCell : ∀ i, (good i).card ≤ (cell i).card := by
    intro i
    let pick : {E // E ∈ good i} → {x // x ∈ cell i} := fun E =>
      ⟨Classical.choose
          ((step i).petal_nonempty E.1
            (hgoodSub i E.2)),
        Finset.mem_biUnion.mpr
          ⟨E.1, E.2,
            Classical.choose_spec
              ((step i).petal_nonempty E.1
                (hgoodSub i E.2))⟩⟩
    have hpickPetal : ∀ E : {E // E ∈ good i},
        (pick E).1 ∈ E.1 \ root i := by
      intro E
      change Classical.choose
        ((step i).petal_nonempty E.1
          (hgoodSub i E.2)) ∈ E.1 \ root i
      exact Classical.choose_spec
        ((step i).petal_nonempty E.1
          (hgoodSub i E.2))
    have hpickInjective : Function.Injective pick := by
      intro E D hED
      apply Subtype.ext
      by_contra hne
      have hpointEq : (pick E).1 = (pick D).1 :=
        congrArg Subtype.val hED
      exact
        (Finset.not_disjoint_iff.mpr
          ⟨(pick E).1, hpickPetal E,
            hpointEq ▸ hpickPetal D⟩)
        ((step i).petals_disjoint E.1
          (hgoodSub i E.2) D.1 (hgoodSub i D.2) hne)
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective pick hpickInjective
  have hcellLarge : ∀ i, i + 2 < (cell i).card := by
    intro i
    exact (hgoodLarge i).trans_le (hgoodCardLeCell i)
  have hcellA : ∀ i, ∀ x ∈ cell i, x ∈ A := by
    intro i x hxCell
    obtain ⟨E, hEgood, hxPetal⟩ :=
      Finset.mem_biUnion.mp hxCell
    exact additiveSupportFamily_supportsIn
      A k (target i) E
        ((step i).matching_sub (hgoodSub i hEgood))
        x (Finset.mem_sdiff.mp hxPetal).1
  have hcellPast : ∀ i, Disjoint (cell i) (used i) := by
    intro i
    rw [Finset.disjoint_left]
    intro x hxCell hxUsed
    obtain ⟨E, hEgood, hxPetal⟩ :=
      Finset.mem_biUnion.mp hxCell
    exact Finset.disjoint_left.mp (hgoodPast i E hEgood)
      (Finset.mem_sdiff.mp hxPetal).1 hxUsed
  have hcellPairwise :
      Pairwise fun i j => Disjoint (cell i) (cell j) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hinto : cell i ⊆ used j := by
        intro x hxCell
        obtain ⟨E, hEgood, hxPetal⟩ :=
          Finset.mem_biUnion.mp hxCell
        exact hused_mono (Nat.succ_le_of_lt hij)
          (hmatching_into_next i E (hgoodSub i hEgood)
            (Finset.mem_sdiff.mp hxPetal).1)
      exact (hcellPast j).symm.mono_left hinto
    · have hinto : cell j ⊆ used i := by
        intro x hxCell
        obtain ⟨E, hEgood, hxPetal⟩ :=
          Finset.mem_biUnion.mp hxCell
        exact hused_mono (Nat.succ_le_of_lt hji)
          (hmatching_into_next j E (hgoodSub j hEgood)
            (Finset.mem_sdiff.mp hxPetal).1)
      exact (hcellPast i).mono_right hinto
  have hretainedInjective : Function.Injective retained := by
    intro i j hvalue
    by_contra hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hiUsed : retained i ∈ used j :=
        hused_mono (Nat.succ_le_of_lt hij)
          (hretained_into_next i)
      have hjNotUsed : retained j ∉ used j := by
        intro hjUsed
        exact hretainedFresh j
          (Finset.mem_union_left _ hjUsed)
      exact hjNotUsed (hvalue ▸ hiUsed)
    · have hjUsed : retained j ∈ used i :=
        hused_mono (Nat.succ_le_of_lt hji)
          (hretained_into_next j)
      have hiNotUsed : retained i ∉ used i := by
        intro hiUsed
        exact hretainedFresh i
          (Finset.mem_union_left _ hiUsed)
      exact hiNotUsed (hvalue.symm ▸ hjUsed)
  let K : Set ℕ := {x | ∃ i, x ∈ cell i}
  have P : IsFiniteBlockPartition K cell := by
    exact ⟨hcellNonempty, hcellPairwise, fun x => Iff.rfl⟩
  let point (i : ℕ) := (hcellNonempty i).choose
  have hpointCell : ∀ i, point i ∈ cell i :=
    fun i => (hcellNonempty i).choose_spec
  have hpointInjective : Function.Injective point := by
    intro i j hij
    by_contra hne
    exact Finset.disjoint_left.mp (hcellPairwise hne)
      (hpointCell i) (hij ▸ hpointCell j)
  have hKInfinite : K.Infinite := by
    apply (Set.infinite_range_of_injective hpointInjective).mono
    rintro x ⟨i, rfl⟩
    exact ⟨i, hpointCell i⟩
  have hKA : K ⊆ A := by
    rintro x ⟨i, hxi⟩
    exact hcellA i x hxi
  have hKReserved : Disjoint K (reserved : Set ℕ) := by
    rw [Set.disjoint_left]
    rintro x ⟨i, hxi⟩ hxProtected
    exact Finset.disjoint_left.mp (hcellPast i)
      hxi (hreservedUsed i hxProtected)
  have hKRetained : Disjoint K (Set.range retained) := by
    rw [Set.disjoint_left]
    rintro x ⟨i, hxi⟩ ⟨j, rfl⟩
    rcases lt_trichotomy i j with hij | hij | hji
    · have husedJ : retained j ∈ used j :=
        hused_mono (Nat.succ_le_of_lt hij)
          (hcell_into_next i hxi)
      exact hretainedFresh j
        (Finset.mem_union_left _ husedJ)
    · subst j
      exact hretainedFresh i
        (Finset.mem_union_right _ (hcellMatchingUnion i hxi))
    · have husedI : retained j ∈ used i :=
        hused_mono (Nat.succ_le_of_lt hji)
          (hretained_into_next j)
      exact Finset.disjoint_left.mp (hcellPast i)
        hxi husedI
  refine ⟨K, cell, target, retained, hKA, hKInfinite, hKReserved, P,
    htargetStrict, hretainedInjective, hretainedA, hKRetained,
    hcellLarge, ?_⟩
  intro s i
  let y := (s i).1
  have hyCell : y ∈ cell i := (s i).2
  have hyRoot : y ∉ root i := by
    intro hyR
    obtain ⟨D, hDgood, hyPetal⟩ :=
      Finset.mem_biUnion.mp hyCell
    exact (Finset.mem_sdiff.mp hyPetal).2 hyR
  have honeGood : 1 < (good i).card := by
    have := hgoodLarge i
    omega
  have hhit :
      ∀ E ∈ good i,
        ¬ Disjoint (E : Set ℕ) ({y} : Set ℕ) →
          ∃ x ∈ ({y} : Finset ℕ), x ∈ E \ root i := by
    intro E _hEgood hEy
    obtain ⟨x, hxE, hxy⟩ :=
      Set.not_disjoint_iff.mp hEy
    have hxy' : x = y := by simpa using hxy
    subst x
    exact ⟨y, by simp,
      Finset.mem_sdiff.mpr
        ⟨Finset.mem_coe.mp hxE, hyRoot⟩⟩
  obtain ⟨E, hEgood, hEy⟩ :=
    exists_surviving_support
      (fun G hG D hD hGD =>
        (step i).petals_disjoint G (hgoodSub i hG)
          D (hgoodSub i hD) hGD)
      hhit (by simpa using honeGood)
  refine ⟨E, (step i).matching_sub (hgoodSub i hEgood), ?_⟩
  rw [Set.disjoint_left]
  intro x hxE hxSelected
  obtain ⟨j, hjx⟩ := hxSelected
  change (s j).1 = x at hjx
  by_cases hji : j = i
  · subst j
    apply Set.disjoint_left.mp hEy hxE
    simpa [y] using hjx.symm
  · rcases lt_or_gt_of_ne hji with hji | hij
    · have hxUsed : x ∈ used i := by
        have hxCellJ : x ∈ cell j := by
          rw [← hjx]
          exact (s j).2
        obtain ⟨D, hDgood, hxPetal⟩ :=
          Finset.mem_biUnion.mp hxCellJ
        exact hused_mono (Nat.succ_le_of_lt hji)
          (hmatching_into_next j D (hgoodSub j hDgood)
            (Finset.mem_sdiff.mp hxPetal).1)
      exact Finset.disjoint_left.mp (hgoodPast i E hEgood)
        hxE hxUsed
    · have hxUsed : x ∈ used j :=
        hused_mono (Nat.succ_le_of_lt hij)
          (hmatching_into_next i E (hgoodSub i hEgood) hxE)
      have hxCellJ : x ∈ cell j := by
        rw [← hjx]
        exact (s j).2
      exact Finset.disjoint_left.mp (hcellPast j)
        hxCellJ hxUsed

/-- The unreserved form of the coherent predecessor common-survival
partition. -/
theorem successorCounterexample_forces_cofinalPredecessorCommonSurvivalPartition
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) (k + 1)) :
    ∃ K : Set ℕ, ∃ cell : ℕ → Finset ℕ, ∃ target : ℕ → ℕ,
      K ⊆ A ∧ K.Infinite ∧
      IsFiniteBlockPartition K cell ∧
      StrictMono target ∧
      ∀ s : BlockSelector cell, ∀ i,
        ∃ E ∈ additiveSupportFamily A k (target i),
          Disjoint (E : Set ℕ) (selectedSet s) := by
  obtain ⟨K, cell, target, _retained, hKA, hKInfinite, _hKEmpty, P,
      htarget, _hretainedInjective, _hretainedA, _hKRetained,
      _hcellLarge, hsurvival⟩ :=
    successorCounterexample_forces_cofinalPredecessorCommonSurvivalPartition_avoiding
      hbasis hcounter ∅
  exact ⟨K, cell, target, hKA, hKInfinite, P, htarget, hsurvival⟩

/-- The coherent construction retains infinitely many anchors, not merely
one.  Every selector therefore preserves the entire two-dimensional grid
`retained j + target i` at successor order. -/
theorem successorCounterexample_forces_cofinalRetainedAnchorGridSurvival
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) (k + 1)) :
    ∃ K : Set ℕ, ∃ cell : ℕ → Finset ℕ, ∃ target retained : ℕ → ℕ,
      K ⊆ A ∧ K.Infinite ∧
      IsFiniteBlockPartition K cell ∧
      StrictMono target ∧
      Function.Injective retained ∧
      (∀ j, retained j ∈ A) ∧
      Disjoint K (Set.range retained) ∧
      (∀ i, i + 2 < (cell i).card) ∧
      ∀ s : BlockSelector cell, ∀ i,
        (∃ E ∈ additiveSupportFamily A k (target i),
            Disjoint (E : Set ℕ) (selectedSet s)) ∧
        ∀ j, ∃ H ∈ additiveSupportFamily A (k + 1)
            (retained j + target i),
          Disjoint (H : Set ℕ) (selectedSet s) := by
  classical
  obtain ⟨K, cell, target, retained, hKA, hKInfinite, _hKEmpty,
      P, htarget, hretainedInjective, hretainedA, hKRetained,
      hcellLarge, hsurvival⟩ :=
    successorCounterexample_forces_cofinalPredecessorCommonSurvivalPartition_avoiding
      hbasis hcounter ∅
  refine ⟨K, cell, target, retained, hKA, hKInfinite, P, htarget,
    hretainedInjective, hretainedA, hKRetained, hcellLarge, ?_⟩
  intro s i
  obtain ⟨E, hER, hEselected⟩ := hsurvival s i
  refine ⟨⟨E, hER, hEselected⟩, ?_⟩
  intro j
  have hanchorSelected : retained j ∉ selectedSet s := by
    intro hselected
    exact Set.disjoint_left.mp hKRetained
      (P.selectedSet_subset s hselected) ⟨j, rfl⟩
  refine ⟨insert (retained j) E,
    insert_mem_additiveSupportFamily_succ (hretainedA j) hER, ?_⟩
  rw [Set.disjoint_left]
  intro x hxInsert hxSelected
  rcases Finset.mem_insert.mp hxInsert with hxa | hxE
  · subst x
    exact hanchorSelected hxSelected
  · exact Set.disjoint_left.mp hEselected hxE hxSelected

/-- The coherent reservoir can reserve one basis element and therefore
protect a synchronized predecessor/successor target stream.

Choose `a ∈ A` before the recursion and put it into the permanently used
prefix.  No deletion block can contain `a`.  Every surviving order-`k`
support of `target i` can consequently be padded by `a`; the padded support
survives the same selector and represents `a + target i` at order `k+1`.
Thus the normalization bridge is realized on one coherent cofinal stream,
not separately at unrelated targets. -/
theorem successorCounterexample_forces_cofinalAnchoredTwoRankSurvivalPartition
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) (k + 1)) :
    ∃ a, a ∈ A ∧ 0 < a ∧
      ∃ K : Set ℕ, ∃ cell : ℕ → Finset ℕ, ∃ target : ℕ → ℕ,
        K ⊆ A ∧ K.Infinite ∧ a ∉ K ∧
        IsFiniteBlockPartition K cell ∧
        StrictMono target ∧
        StrictMono (fun i => a + target i) ∧
        ∀ s : BlockSelector cell, ∀ i,
          (∃ E ∈ additiveSupportFamily A k (target i),
              Disjoint (E : Set ℕ) (selectedSet s)) ∧
          ∃ H ∈ additiveSupportFamily A (k + 1) (a + target i),
              Disjoint (H : Set ℕ) (selectedSet s) := by
  classical
  obtain ⟨a, haA, haPos⟩ := hbasis.infinite.exists_gt 0
  obtain ⟨K, cell, target, _retained, hKA, hKInfinite, hKAnchor, P,
      htarget, _hretainedInjective, _hretainedA, _hKRetained,
      _hcellLarge, hsurvival⟩ :=
    successorCounterexample_forces_cofinalPredecessorCommonSurvivalPartition_avoiding
      hbasis hcounter {a}
  have haK : a ∉ K := by
    intro haK
    exact Set.disjoint_left.mp hKAnchor haK (by simp)
  have hshift : StrictMono (fun i => a + target i) := by
    intro i j hij
    exact Nat.add_lt_add_left (htarget hij) a
  refine ⟨a, haA, haPos, K, cell, target, hKA, hKInfinite, haK, P,
    htarget, hshift, ?_⟩
  intro s i
  obtain ⟨E, hER, hEselected⟩ := hsurvival s i
  refine ⟨⟨E, hER, hEselected⟩,
    insert a E,
    insert_mem_additiveSupportFamily_succ haA hER, ?_⟩
  rw [Set.disjoint_left]
  intro x hxInsert hxSelected
  rcases Finset.mem_insert.mp hxInsert with hxa | hxE
  · subst x
    apply haK
    obtain ⟨j, hja⟩ := hxSelected
    exact (P.mem_iff a).2 ⟨j, by
      rw [← hja]
      exact (s j).2⟩
  · exact Set.disjoint_left.mp hEselected hxE hxSelected

/-- A successor destroyer descends through any retained anchor, without a
finiteness hypothesis on the destroying set. -/
theorem additiveSuccessorDestroyer_descends_outsideSet
    {A S : Set ℕ} {k n a : ℕ}
    (hdestroy : DestroysAt
      (additiveSupportFamily A (k + 1)) S n)
    (haA : a ∈ A) (haS : a ∉ S) (han : a ≤ n) :
    DestroysAt (additiveSupportFamily A k) S (n - a) := by
  intro E hER
  have hlift :
      insert a E ∈ additiveSupportFamily A (k + 1) n := by
    have h :=
      insert_mem_additiveSupportFamily_succ haA hER
    have hsum : a + (n - a) = n := by omega
    simpa [hsum] using h
  obtain ⟨x, hxInsert, hxS⟩ :=
    Set.not_disjoint_iff.mp (hdestroy (insert a E) hlift)
  apply Set.not_disjoint_iff.mpr
  rcases Finset.mem_insert.mp hxInsert with hxa | hxE
  · subst x
    exact (haS hxS).elim
  · exact ⟨x, hxE, hxS⟩

/-- Infinite-anchor amplification of certificate descent.

On one fixed infinite deletion partition, every requested finite number of
retained anchors eventually lie below a late private successor defect.
Descending through all of them gives that many distinct predecessor defects
destroyed by the same selector.  None can be one of the protected
predecessor targets, since that would put the original successor target on
the universally surviving retained-anchor grid. -/
theorem successorCounterexample_forces_arbitrarilyManyCoherentDescents
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) (k + 1)) :
    ∃ K : Set ℕ, ∃ cell : ℕ → Finset ℕ, ∃ target retained : ℕ → ℕ,
      K ⊆ A ∧ K.Infinite ∧
      IsFiniteBlockPartition K cell ∧
      StrictMono target ∧
      Function.Injective retained ∧
      (∀ j, retained j ∈ A) ∧
      Disjoint K (Set.range retained) ∧
      (∀ i, i + 2 < (cell i).card) ∧
      ∀ r N, ∃ q, ∃ s : BlockSelector cell,
        N ≤ q ∧
        DestroysAt (additiveSupportFamily A (k + 1))
          (selectedSet s) q ∧
        (∀ j, j < r →
          retained j ≤ q ∧
          DestroysAt (additiveSupportFamily A k)
            (selectedSet s) (q - retained j)) ∧
        Set.InjOn (fun j => q - retained j) {j | j < r} ∧
        ∀ j, j < r → ∀ i, q - retained j ≠ target i := by
  classical
  obtain ⟨K, cell, target, retained, hKA, hKInfinite, P, htarget,
      hretainedInjective, hretainedA, hKRetained, hcellLarge,
      hsurvival⟩ :=
    successorCounterexample_forces_cofinalRetainedAnchorGridSurvival
      hbasis hcounter
  have hgridSafe : ∀ j i,
      retained j + target i ∈
        commonSurvivalTargets
          (additiveSupportFamily A (k + 1)) cell := by
    intro j i s
    exact (hsurvival s i).2 j
  let anchorSum (r : ℕ) : ℕ :=
    ∑ j ∈ Finset.range r, retained j
  have hanchorLe : ∀ r j, j < r → retained j ≤ anchorSum r := by
    intro r j hj
    dsimp only [anchorSum]
    exact Finset.single_le_sum
      (f := retained)
      (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr hj)
  refine ⟨K, cell, target, retained, hKA, hKInfinite, P, htarget,
    hretainedInjective, hretainedA, hKRetained, hcellLarge, ?_⟩
  intro r N
  obtain ⟨Q, hQ, hQlate, _hcert, hlocalized, hQcommon⟩ :=
    strongDeletion_certificate_avoids_allCommonSurvivalTargets
      (strongExactDeletion_of_counterexample hcounter)
      hKA P (max N (anchorSum r))
  obtain ⟨q, hqQ⟩ := hQ
  obtain ⟨s, hqDestroy, _hprivate⟩ :=
    hlocalized q hqQ
  have hNq : N ≤ q :=
    (le_max_left N (anchorSum r)).trans (hQlate q hqQ)
  have hsumq : anchorSum r ≤ q :=
    (le_max_right N (anchorSum r)).trans (hQlate q hqQ)
  have hanchorSelected : ∀ j, retained j ∉ selectedSet s := by
    intro j hselected
    exact Set.disjoint_left.mp hKRetained
      (P.selectedSet_subset s hselected) ⟨j, rfl⟩
  have hdescend : ∀ j, j < r →
      retained j ≤ q ∧
      DestroysAt (additiveSupportFamily A k)
        (selectedSet s) (q - retained j) := by
    intro j hj
    have hajq : retained j ≤ q :=
      (hanchorLe r j hj).trans hsumq
    exact ⟨hajq,
      additiveSuccessorDestroyer_descends_outsideSet
        hqDestroy (hretainedA j) (hanchorSelected j) hajq⟩
  have hdifferenceInjective :
      Set.InjOn (fun j => q - retained j) {j | j < r} := by
    intro i hi j hj heq
    apply hretainedInjective
    have hiq := (hdescend i hi).1
    have hjq := (hdescend j hj).1
    have hiRecover :
        q = (q - retained i) + retained i :=
      (Nat.sub_add_cancel hiq).symm
    have hjRecover :
        q = (q - retained j) + retained j :=
      (Nat.sub_add_cancel hjq).symm
    change q - retained i = q - retained j at heq
    rw [heq] at hiRecover
    omega
  have hdifferenceAvoids : ∀ j, j < r → ∀ i,
      q - retained j ≠ target i := by
    intro j hj i heq
    have hajq := (hdescend j hj).1
    have hqeq : q = retained j + target i := by omega
    exact Set.disjoint_left.mp hQcommon
      (Finset.mem_coe.mpr hqQ) (hqeq ▸ hgridSafe j i)
  exact ⟨q, s, hNq, hqDestroy, hdescend,
    hdifferenceInjective, hdifferenceAvoids⟩

/-- Direct certificate descent on the anchored coherent reservoir.

Every arbitrarily late target-minimal successor certificate avoids the
protected translated stream.  More importantly, each selector's destroying
choice `q` descends through the same retained positive anchor to an
order-`k` defect at `q-a`, strictly below `q`.  This is the finite
prefix/difference composition on one fixed infinite deletion object. -/
theorem successorCounterexample_forces_strictAnchoredCertificateDescent
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) (k + 1)) :
    ∃ a, a ∈ A ∧ 0 < a ∧
      ∃ K : Set ℕ, ∃ cell : ℕ → Finset ℕ, ∃ target : ℕ → ℕ,
        K ⊆ A ∧ K.Infinite ∧ a ∉ K ∧
        IsFiniteBlockPartition K cell ∧
        StrictMono target ∧
        StrictMono (fun i => a + target i) ∧
        (∀ s : BlockSelector cell, ∀ i,
          (∃ E ∈ additiveSupportFamily A k (target i),
              Disjoint (E : Set ℕ) (selectedSet s)) ∧
          ∃ H ∈ additiveSupportFamily A (k + 1) (a + target i),
              Disjoint (H : Set ℕ) (selectedSet s)) ∧
        ∀ N, ∃ Q : Finset ℕ,
          Q.Nonempty ∧
          (∀ q ∈ Q, N + a ≤ q) ∧
          (∀ s : BlockSelector cell, ∃ q ∈ Q,
            DestroysAt (additiveSupportFamily A (k + 1))
              (selectedSet s) q) ∧
          (∀ q ∈ Q, ∃ s : BlockSelector cell,
            DestroysAt (additiveSupportFamily A (k + 1))
              (selectedSet s) q ∧
            ∀ q' ∈ Q, q' ≠ q →
              ¬ DestroysAt (additiveSupportFamily A (k + 1))
                (selectedSet s) q') ∧
          Disjoint (Q : Set ℕ)
            (Set.range fun i => a + target i) ∧
          ∀ s : BlockSelector cell, ∃ q ∈ Q,
            DestroysAt (additiveSupportFamily A (k + 1))
              (selectedSet s) q ∧
            DestroysAt (additiveSupportFamily A k)
              (selectedSet s) (q - a) ∧
            q - a < q := by
  obtain ⟨a, haA, haPos, K, cell, target, hKA, hKInfinite,
      haK, P, htarget, hshift, hsurvival⟩ :=
    successorCounterexample_forces_cofinalAnchoredTwoRankSurvivalPartition
      hbasis hcounter
  have hshiftInfinite :
      (Set.range fun i => a + target i).Infinite :=
    Set.infinite_range_of_injective hshift.injective
  refine ⟨a, haA, haPos, K, cell, target, hKA, hKInfinite,
    haK, P, htarget, hshift, hsurvival, ?_⟩
  intro N
  obtain ⟨Q, hQ, hQlate, hcert, hlocalized, hQsafe⟩ :=
    strongDeletion_certificate_avoids_unboundedCommonSurvivalTargets
      (strongExactDeletion_of_counterexample hcounter)
      hKA P hshiftInfinite (fun s i => (hsurvival s i).2) (N + a)
  refine ⟨Q, hQ, hQlate, hcert, hlocalized, hQsafe, ?_⟩
  intro s
  obtain ⟨q, hqQ, hqDestroy⟩ := hcert s
  have haSelected : a ∉ selectedSet s := by
    intro haSelected
    exact haK (P.selectedSet_subset s haSelected)
  have haq : a ≤ q := by
    have := hQlate q hqQ
    omega
  exact ⟨q, hqQ, hqDestroy,
    additiveSuccessorDestroyer_descends_outsideSet
      hqDestroy haA haSelected haq,
    by omega⟩

/-- Certificate migration, lower-rank drift, root collisions, and bounded
translated targets are all eliminated at once.

For a hypothetical strongly minimal order-`k+1` basis, every finite prefix,
matching demand, and target threshold has only two outcomes:

* a rooted matching of the requested size back at order `k+1`, beyond the
  target threshold, whose common root avoids the prefix; or
* a late genuine order-`k` gap translate.

Thus repeated old-coordinate collisions cannot remain a third branch: they
either amplify into fresh cofinal matching growth or are bypassed by the
second-choice/certificate descent construction above. -/
theorem IsStronglyMinimalExactBasis.cofinal_prefixDisjointRootedMatching_or_lowerGap
    {A : Set ℕ} {k : ℕ}
    (hminimal : IsStronglyMinimalExactBasis A (k + 1)) :
    ∀ F : Finset ℕ, ∀ r L,
      (∃ t R M,
          L ≤ t ∧ R.card < k + 1 ∧ Disjoint R F ∧
          M ⊆ additiveSupportFamily A (k + 1) t ∧
          r < M.card ∧
          (∀ E ∈ M, R ⊆ E) ∧
          (∀ E ∈ M, (E \ R).Nonempty) ∧
          ∀ E ∈ M, ∀ D ∈ M, E ≠ D →
            Disjoint (E \ R) (D \ R)) ∨
        ∃ q, L ≤ q ∧ ∃ b, b ∈ A ∧ b ≤ q ∧
          additiveSupportFamily A k (q - b) = ∅ := by
  intro F r L
  let size :=
    max r (additiveLowerRankSupportCountBelow A (k + 1) L)
  let demand :=
    max (additivePrefixAvoidingRootBound (k + 1) size)
      (additivePrefixAvoidingRootBound k size)
  obtain hcurrent | hlower | hgap :=
    hminimal.cofinal_rootedMatching_or_lowerGap demand L
  · obtain ⟨q, _hLq, R, M, _hRcard, hMsub, hMcard,
        _hMroot, _hMnonempty, _hMmatching⟩ := hcurrent
    left
    apply largeSupportFamily_forces_cofinal_prefixDisjointRootedMatching
      hminimal.1 (h := k + 1) (r := r) (L := L) (F := F)
        le_rfl hMsub
    exact (le_max_left _ _).trans (Nat.le_of_lt hMcard)
  · obtain ⟨q, _hLq, d, _hdA, _hdq, R, M, _hRcard,
        hMsub, hMcard, _hMroot, _hMnonempty, _hMmatching⟩ :=
      hlower
    left
    apply largeSupportFamily_forces_cofinal_prefixDisjointRootedMatching
      hminimal.1 (h := k) (r := r) (L := L) (F := F)
        (Nat.le_succ k) hMsub
    exact (le_max_right _ _).trans (Nat.le_of_lt hMcard)
  · exact Or.inr hgap

/-- Fully prefix-avoiding terminal dichotomy.

Both terminal objects are fresh relative to the same finite set `F`: the
matching root is disjoint from `F`, while the predecessor-gap repair point
does not belong to `F`.  This removes reuse of old repair vertices from the
recurrent-gap branch. -/
theorem IsStronglyMinimalExactBasis.cofinal_prefixDisjointRootedMatching_or_freshLowerGap
    {A : Set ℕ} {k : ℕ}
    (hminimal : IsStronglyMinimalExactBasis A (k + 1)) :
    ∀ F : Finset ℕ, ∀ r L,
      (∃ t R M,
          L ≤ t ∧ R.card < k + 1 ∧ Disjoint R F ∧
          M ⊆ additiveSupportFamily A (k + 1) t ∧
          r < M.card ∧
          (∀ E ∈ M, R ⊆ E) ∧
          (∀ E ∈ M, (E \ R).Nonempty) ∧
          ∀ E ∈ M, ∀ D ∈ M, E ≠ D →
            Disjoint (E \ R) (D \ R)) ∨
        ∃ q, L ≤ q ∧ ∃ b, b ∈ A ∧ b ∉ F ∧ b ≤ q ∧
          additiveSupportFamily A k (q - b) = ∅ := by
  intro F r L
  let size :=
    max r (additiveLowerRankSupportCountBelow A (k + 1) L)
  let demand :=
    max (additivePrefixAvoidingRootBound (k + 1) size)
      (additivePrefixAvoidingRootBound k size)
  obtain hcurrent | hlower | hgap :=
    hminimal.cofinal_rootedMatching_or_freshLowerGap F demand L
  · obtain ⟨q, _hLq, R, M, _hRcard, hMsub, hMcard,
        _hMroot, _hMnonempty, _hMmatching⟩ := hcurrent
    left
    apply largeSupportFamily_forces_cofinal_prefixDisjointRootedMatching
      hminimal.1 (h := k + 1) (r := r) (L := L) (F := F)
        le_rfl hMsub
    exact (le_max_left _ _).trans (Nat.le_of_lt hMcard)
  · obtain ⟨q, _hLq, d, _hdA, _hdq, R, M, _hRcard,
        hMsub, hMcard, _hMroot, _hMnonempty, _hMmatching⟩ :=
      hlower
    left
    apply largeSupportFamily_forces_cofinal_prefixDisjointRootedMatching
      hminimal.1 (h := k) (r := r) (L := L) (F := F)
        (Nat.le_succ k) hMsub
    exact (le_max_right _ _).trans (Nat.le_of_lt hMcard)
  · exact Or.inr hgap

/-- Rank-synchronized output: the bounded successor-transversal branch
produces arbitrarily large, arbitrarily late rooted matchings back at the
*original predecessor order* `k+1`, with the common root disjoint from any
prescribed finite prefix.

Thus both losses introduced by rank descent are repaired: the lower target
is cofinal, and a single fresh repeated padding element restores the original
order without changing any petal. -/
theorem cofinalOriginalOrderRootedMatchings_of_boundedFullTranslateDestroyers
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A (k + 1))
    (hfull : HasBoundedFullTranslateDestroyersByAnchor A (k + 1) Q) :
    ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A → ∀ r Lanchor Ltarget,
      ∃ n T q a x t R M,
        Lanchor ≤ a ∧ Ltarget ≤ t ∧
        q ∈ Q ∧ a ∈ A ∧ n = q + a ∧
        (∀ y ∈ T, y ∈ A) ∧ Disjoint T F ∧ T.Nonempty ∧
        DestroysAt
          (additiveSupportFamily A (k + 2)) (T : Set ℕ) n ∧
        x ∈ T ∧ x ≤ n ∧
        R.card < k + 1 ∧ Disjoint R F ∧
        M ⊆ additiveSupportFamily A (k + 1) t ∧
        r < M.card ∧
        (∀ E ∈ M, R ⊆ E) ∧
        (∀ E ∈ M, (E \ R).Nonempty) ∧
        ∀ E ∈ M, ∀ D ∈ M, E ≠ D →
          Disjoint (E \ R) (D \ R) := by
  intro F hFA r Lanchor Ltarget
  obtain ⟨n, T, q, a, x, j, u, S, L,
      haLower, huLower, hqQ, haA, hnqa, hTA, hTF, hTnonempty,
      hdestroy, hxT, hxn, hjpos, hjle, hScard, hSF,
      hLsub, hLcard, hLroot, hLnonempty, hLmatching⟩ :=
    cofinalPrefixDisjointRootedMatchings_of_boundedFullTranslateDestroyers
      hbasis hfull F hFA r Lanchor Ltarget
  by_cases hjtop : j = k + 1
  · subst j
    exact ⟨n, T, q, a, x, u, S, L,
      haLower, huLower, hqQ, haA, hnqa, hTA, hTF, hTnonempty,
      hdestroy, hxT, hxn, hScard, hSF, hLsub, hLcard,
      hLroot, hLnonempty, hLmatching⟩
  · have hjlt : j < k + 1 := lt_of_le_of_ne hjle hjtop
    obtain ⟨t, R, M, hut, hRcard, hRF, hMcardEq,
        hMsub, hMroot, hMnonempty, hMmatching⟩ :=
      lift_rootedMatching_to_strictHigherOrder
        hbasis.infinite hjlt hScard hSF hLsub
        hLroot hLnonempty hLmatching
    refine ⟨n, T, q, a, x, t, R, M,
      haLower, le_trans huLower hut, hqQ, haA, hnqa,
      hTA, hTF, hTnonempty, hdestroy, hxT, hxn,
      hRcard, hRF, hMsub, ?_, hMroot, hMnonempty, hMmatching⟩
    rw [hMcardEq]
    exact hLcard

end Erdos881
