import Erdos881.PinnedMirror
import Erdos881.GuardianBridge

/-!
# The funnel trichotomy

Foundation stone of Open Link A.  A target destroyed by an infinite
deletion set `B` has all its exact three-term representations meeting
`B` — but the transversal structure of a `≤ 3`-uniform family is tiny:
*any single representation's `B`-part is a transversal candidate*.
With `0` available outside `B`, the zero-augmented representation
`0 + y + z` of a covered target has a `B`-part of size at most two, so
exactly three things can happen:

* that `B`-part is a **singleton funnel** — a private guardian from
  `B` (the machinery of `GuardianRigidity` applies), or
* it is a **pair funnel** — a team edge inside `B` (the machinery of
  `TeamGraphRamsey`/`PinnedMirror` applies), or
* some representation avoids it entirely, producing **two
  representations with disjoint `B`-parts** — the diffuse case.

Consequently a counterexample to Erdős 881 that dodges the funnel
interfaces must, for some infinite `B` and *every* late destroyed
target, realize the diffuse branch — cofinal disjoint-support
destruction (`cofinal_funnel_trichotomy_of_deletionFailure`).  Killing
that hereditary diffuse regime is what remains of Link A.
-/

namespace Erdos881

/-- `B` destroys `m` at order three over `A`, in elementary form: a
representation exists, and every representation meets `B`.  This
generalizes `IsPrivateTriple` (`B = {a}`) and `IsPairDestroyer`
(`B = {u, v}`) to arbitrary deletion sets. -/
def DestroyedBySet (A B : Set ℕ) (m : ℕ) : Prop :=
  (∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = m) ∧
    ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = m →
      x ∈ B ∨ y ∈ B ∨ z ∈ B

/-- The order-two shadow: fixing any representation part outside `B`,
the remaining pair must meet `B`.  With `x = 0` this says every
two-term representation of a destroyed target meets `B`; with general
`x ∈ A \ B` it covers the whole translated family `m - x`. -/
theorem DestroyedBySet.shadow {A B : Set ℕ} {m x y z : ℕ}
    (hdes : DestroyedBySet A B m)
    (hx : x ∈ A) (hxB : x ∉ B) (hy : y ∈ A) (hz : z ∈ A)
    (hsum : x + y + z = m) :
    y ∈ B ∨ z ∈ B := by
  rcases hdes.2 x hx y hy z hz hsum with h | h | h
  · exact absurd h hxB
  · exact Or.inl h
  · exact Or.inr h

/-- Elementary destruction from the tuple form: a target with a
representation but no surviving tuple in `A \ B` is destroyed by `B`. -/
theorem destroyedBySet_of_no_surviving_tuple {A B : Set ℕ} {m : ℕ}
    (hrep : ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = m)
    (hno : ¬ ∃ v : Fin 3 → ℕ, (∀ i, v i ∈ A \ B) ∧ ∑ i, v i = m) :
    DestroyedBySet A B m := by
  refine ⟨hrep, ?_⟩
  intro x hx y hy z hz hsum
  by_contra hne
  push Not at hne
  refine hno ⟨![x, y, z], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp_all [Set.mem_diff]
  · simpa [Fin.sum_univ_three] using hsum

/-- **The funnel trichotomy.**  A destroyed target of a deletion set
not containing zero carries a singleton funnel from `B`, or a pair
funnel from `B`, or two representations with disjoint `B`-parts: a
zero-augmented representation whose `B`-part (at most two elements) is
avoided entirely by a second representation. -/
theorem DestroyedBySet.funnel_trichotomy {A B : Set ℕ} {N₀ m : ℕ}
    (h0 : 0 ∈ A) (h0B : 0 ∉ B)
    (hcov : PairCovers A N₀)
    (hdes : DestroyedBySet A B m) (hm : N₀ ≤ m) :
    (∃ u ∈ B, u ∈ A ∧ IsPrivateTriple A u m) ∨
    (∃ u ∈ B, ∃ v ∈ B, IsPairDestroyer A u v m) ∨
    (∃ y ∈ A, ∃ z ∈ A, y + z = m ∧ (y ∈ B ∨ z ∈ B) ∧
      ∃ x' ∈ A, ∃ y' ∈ A, ∃ z' ∈ A, x' + y' + z' = m ∧
        (y ∈ B → x' ≠ y ∧ y' ≠ y ∧ z' ≠ y) ∧
        (z ∈ B → x' ≠ z ∧ y' ≠ z ∧ z' ≠ z)) := by
  obtain ⟨y, hy, z, hz, hyz⟩ := hcov m hm
  have hB := hdes.shadow h0 h0B hy hz (by omega)
  by_cases hyB : y ∈ B
  · by_cases hzB : z ∈ B
    · by_cases htr : ∀ x' ∈ A, ∀ y' ∈ A, ∀ z' ∈ A, x' + y' + z' = m →
          x' = y ∨ y' = y ∨ z' = y ∨ x' = z ∨ y' = z ∨ z' = z
      · exact Or.inr (Or.inl ⟨y, hyB, z, hzB, hdes.1, htr⟩)
      · push Not at htr
        obtain ⟨x', hx', y', hy', z', hz', hsum', h1, h2, h3, h4, h5, h6⟩ :=
          htr
        exact Or.inr (Or.inr ⟨y, hy, z, hz, hyz, Or.inl hyB, x', hx',
          y', hy', z', hz', hsum',
          fun _ => ⟨h1, h2, h3⟩, fun _ => ⟨h4, h5, h6⟩⟩)
    · by_cases htr : ∀ x' ∈ A, ∀ y' ∈ A, ∀ z' ∈ A, x' + y' + z' = m →
          x' = y ∨ y' = y ∨ z' = y
      · exact Or.inl ⟨y, hyB, hy, hdes.1, htr⟩
      · push Not at htr
        obtain ⟨x', hx', y', hy', z', hz', hsum', h1, h2, h3⟩ := htr
        exact Or.inr (Or.inr ⟨y, hy, z, hz, hyz, Or.inl hyB, x', hx',
          y', hy', z', hz', hsum',
          fun _ => ⟨h1, h2, h3⟩, fun hzB' => absurd hzB' hzB⟩)
  · have hzB : z ∈ B := hB.resolve_left hyB
    by_cases htr : ∀ x' ∈ A, ∀ y' ∈ A, ∀ z' ∈ A, x' + y' + z' = m →
        x' = z ∨ y' = z ∨ z' = z
    · exact Or.inl ⟨z, hzB, hz, hdes.1, htr⟩
    · push Not at htr
      obtain ⟨x', hx', y', hy', z', hz', hsum', h1, h2, h3⟩ := htr
      exact Or.inr (Or.inr ⟨y, hy, z, hz, hyz, Or.inr hzB, x', hx',
        y', hy', z', hz', hsum',
        fun hyB' => absurd hyB' hyB, fun _ => ⟨h1, h2, h3⟩⟩)

/-- **Diffuse destruction pairs up deletion elements.**  In the third
branch of the trichotomy the second representation still meets `B` —
necessarily outside the first representation's `B`-part.  So a target
without singleton or pair funnels from `B` yields two *distinct*
`B`-elements serving it through representations with disjoint
`B`-parts: the raw pairs for a Ramsey argument on the diffuse
regime. -/
theorem DestroyedBySet.diffuse_witness_pair {A B : Set ℕ} {N₀ m : ℕ}
    (h0 : 0 ∈ A) (h0B : 0 ∉ B)
    (hcov : PairCovers A N₀)
    (hdes : DestroyedBySet A B m) (hm : N₀ ≤ m)
    (hsing : ¬ ∃ u ∈ B, u ∈ A ∧ IsPrivateTriple A u m)
    (hpair : ¬ ∃ u ∈ B, ∃ v ∈ B, IsPairDestroyer A u v m) :
    ∃ b₁ ∈ B, ∃ b₂ ∈ B, b₁ ≠ b₂ ∧ b₁ ∈ A ∧ b₂ ∈ A ∧ b₁ ≤ m ∧ b₂ ≤ m := by
  rcases hdes.funnel_trichotomy h0 h0B hcov hm with h | h | h
  · exact absurd h hsing
  · exact absurd h hpair
  obtain ⟨y, hy, z, hz, hyz, hB, x', hx', y', hy', z', hz', hsum',
    havoidy, havoidz⟩ := h
  obtain ⟨b₂, hb₂B, hb₂A, hb₂rep⟩ :
      ∃ b₂ ∈ B, b₂ ∈ A ∧ (b₂ = x' ∨ b₂ = y' ∨ b₂ = z') := by
    rcases hdes.2 x' hx' y' hy' z' hz' hsum' with h' | h' | h'
    · exact ⟨x', h', hx', Or.inl rfl⟩
    · exact ⟨y', h', hy', Or.inr (Or.inl rfl)⟩
    · exact ⟨z', h', hz', Or.inr (Or.inr rfl)⟩
  rcases hB with hyB | hzB
  · have hne : b₂ ≠ y := by
      obtain ⟨e1, e2, e3⟩ := havoidy hyB
      rcases hb₂rep with rfl | rfl | rfl <;> assumption
    exact ⟨y, hyB, b₂, hb₂B, hne.symm, hy, hb₂A, by omega,
      by rcases hb₂rep with rfl | rfl | rfl <;> omega⟩
  · have hne : b₂ ≠ z := by
      obtain ⟨e1, e2, e3⟩ := havoidz hzB
      rcases hb₂rep with rfl | rfl | rfl <;> assumption
    exact ⟨z, hzB, b₂, hb₂B, hne.symm, hz, hb₂A, by omega,
      by rcases hb₂rep with rfl | rfl | rfl <;> omega⟩

/-- **The counting vise.**  Every member of the translated family of a
destroyed target is two-representation-poor: the two-support of
`m - x` (for any representation part `x ∈ A \ B`) lives inside
`B ∪ ((m - x) - B)`, so its size is at most twice the number of
deletion elements below `m`.  A sparse deletion set therefore forces
all its destroyed targets — and their entire `A \ B`-translate
families — to be nearly uniquely representable.  (`x = 0` gives the
bound for the destroyed target itself.) -/
theorem DestroyedBySet.translate_two_support_card_le
    {A B : Set ℕ} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    {m x : ℕ}
    (hdes : DestroyedBySet A B m)
    (hx : x ∈ A) (hxB : x ∉ B) :
    ((Finset.range (m + 1)).filter
        fun y => y ∈ A ∧ x + y ≤ m ∧ m - x - y ∈ A).card ≤
      2 * ((Finset.range (m + 1)).filter fun b => b ∈ B).card := by
  set S := (Finset.range (m + 1)).filter
    fun y => y ∈ A ∧ x + y ≤ m ∧ m - x - y ∈ A with hS
  set T := (Finset.range (m + 1)).filter fun b => b ∈ B with hT
  set g : ℕ → ℕ := fun y => if y ∈ B then y else m - x - y with hg
  have hmem : ∀ y ∈ S, g y ∈ T := by
    intro y hy
    simp only [hS, Finset.mem_filter, Finset.mem_range] at hy
    obtain ⟨hyr, hyA, hxy, hyz⟩ := hy
    have hside := hdes.shadow hx hxB hyA hyz (by omega)
    simp only [hT, hg, Finset.mem_filter, Finset.mem_range]
    by_cases hyB : y ∈ B
    · rw [if_pos hyB]
      exact ⟨hyr, hyB⟩
    · rw [if_neg hyB]
      rcases hside with h | h
      · exact absurd h hyB
      · exact ⟨by omega, h⟩
  have hfiber : ∀ b ∈ T, (S.filter fun y => g y = b).card ≤ 2 := by
    intro b _hb
    have hsub : (S.filter fun y => g y = b) ⊆ {b, m - x - b} := by
      intro y hy
      simp only [hS, hg, Finset.mem_filter, Finset.mem_range] at hy
      obtain ⟨⟨hyr, hyA, hxy, hyz⟩, hgy⟩ := hy
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hyB : y ∈ B
      · rw [if_pos hyB] at hgy
        exact Or.inl hgy
      · rw [if_neg hyB] at hgy
        right
        omega
    calc (S.filter fun y => g y = b).card
        ≤ ({b, m - x - b} : Finset ℕ).card := Finset.card_le_card hsub
      _ ≤ 2 := by
          refine le_trans (Finset.card_insert_le _ _) ?_
          simp
  calc S.card
      = ∑ b ∈ T, (S.filter fun y => g y = b).card :=
        Finset.card_eq_sum_card_fiberwise hmem
    _ ≤ ∑ _b ∈ T, 2 := Finset.sum_le_sum hfiber
    _ = 2 * T.card := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- **Cofinal trichotomy from deletion failure.**  If deleting `B`
(not containing zero) breaks the exact order-three basis property,
then arbitrarily late targets realize the funnel trichotomy.  A
counterexample to Erdős 881 therefore feeds every infinite `B ⊆ A`
into singleton funnels, pair funnels, or cofinal disjoint-support
destruction — Link A is exactly the exclusion of the third regime
along some thinning. -/
theorem cofinal_funnel_trichotomy_of_deletionFailure
    {A B : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (h0B : 0 ∉ B)
    (hcov : PairCovers A N₀)
    (hfail : ¬ IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ N, ∃ m, N ≤ m ∧
      ((∃ u ∈ B, u ∈ A ∧ IsPrivateTriple A u m) ∨
      (∃ u ∈ B, ∃ v ∈ B, IsPairDestroyer A u v m) ∨
      (∃ y ∈ A, ∃ z ∈ A, y + z = m ∧ (y ∈ B ∨ z ∈ B) ∧
        ∃ x' ∈ A, ∃ y' ∈ A, ∃ z' ∈ A, x' + y' + z' = m ∧
          (y ∈ B → x' ≠ y ∧ y' ≠ y ∧ z' ≠ y) ∧
          (z ∈ B → x' ≠ z ∧ y' ≠ z ∧ z' ≠ z))) := by
  intro N
  rw [IsExactTupleAsymptoticBasis] at hfail
  push Not at hfail
  obtain ⟨m, hmN, hno⟩ := hfail (max N N₀)
  have hm₀ : N₀ ≤ m := le_trans (le_max_right _ _) hmN
  obtain ⟨y, hy, z, hz, hyz⟩ := hcov m hm₀
  have hdes : DestroyedBySet A B m :=
    destroyedBySet_of_no_surviving_tuple
      ⟨0, h0, y, hy, z, hz, by omega⟩
      (fun ⟨v, hv, hs⟩ => hno v hv hs)
  exact ⟨m, le_trans (le_max_left _ _) hmN,
    hdes.funnel_trichotomy h0 h0B hcov hm₀⟩

end Erdos881
