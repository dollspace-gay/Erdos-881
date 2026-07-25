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

/-- `n` is two-destroyed by the set `B`: every two-term representation
meets it. -/
def TwoDestroyedBySet (A B : Set ℕ) (n : ℕ) : Prop :=
  ∀ y ∈ A, ∀ z ∈ A, y + z = n → y ∈ B ∨ z ∈ B

/-- An undeleted element is never two-destroyed: its zero-augmented
representation avoids `B`. -/
theorem not_twoDestroyedBySet_of_mem_diff {A B : Set ℕ} {n : ℕ}
    (h0 : 0 ∈ A) (h0B : 0 ∉ B) (hn : n ∈ A) (hnB : n ∉ B) :
    ¬ TwoDestroyedBySet A B n := fun h => by
  rcases h 0 h0 n hn (by omega) with h' | h'
  · exact h0B h'
  · exact hnB h'

/-- **The elementwise fork trichotomy.**  Every undeleted element `x`
below a destroyed target routes through some `u ∈ B`, and the landing
point `m - x - u` either falls back into `B` or is an element whose
cross-sum `u + x` is itself two-destroyed by `B` — otherwise an
avoiding representation of `u + x` would resurrect the target.  This
is the sharp pinning mechanism at set level: every deleted element
that serves a diffuse target plants two-destroyed values, the raw
material for density arguments against the diffuse regime. -/
theorem DestroyedBySet.fork_trichotomy_elt {A B : Set ℕ} {N₀ m x : ℕ}
    (hcov : PairCovers A N₀)
    (hdes : DestroyedBySet A B m)
    (hx : x ∈ A) (hxB : x ∉ B) (hxm : x + N₀ ≤ m) :
    ∃ u ∈ B, u ≤ m - x ∧
      (m - x - u ∈ B ∨
        (m - x - u ∈ A ∧ TwoDestroyedBySet A B (u + x))) := by
  obtain ⟨y, hy, z, hz, hyz⟩ := hcov (m - x) (by omega)
  have hside := hdes.shadow hx hxB hy hz (by omega)
  rcases hside with hyB | hzB
  · refine ⟨y, hyB, by omega, ?_⟩
    by_cases hzB : z ∈ B
    · exact Or.inl (by
        have : m - x - y = z := by omega
        exact this ▸ hzB)
    · refine Or.inr ⟨by
        have : m - x - y = z := by omega
        exact this ▸ hz, ?_⟩
      intro s hs t ht hst
      by_contra hne
      push Not at hne
      rcases hdes.2 s hs t ht z hz (by omega) with h | h | h
      · exact hne.1 h
      · exact hne.2 h
      · exact hzB h
  · refine ⟨z, hzB, by omega, ?_⟩
    by_cases hyB : y ∈ B
    · exact Or.inl (by
        have : m - x - z = y := by omega
        exact this ▸ hyB)
    · refine Or.inr ⟨by
        have : m - x - z = y := by omega
        exact this ▸ hy, ?_⟩
      intro s hs t ht hst
      by_contra hne
      push Not at hne
      rcases hdes.2 s hs t ht y hy (by omega) with h | h | h
      · exact hne.1 h
      · exact hne.2 h
      · exact hyB h

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

/-- Order-three destruction shadows to order two: with `0` undeleted,
a destroyed target is also two-destroyed.  Consequently the
counterexample's demand *at order two* — every infinite deletion
two-destroys cofinally — is exactly the ℵ₀-minimality hypothesis of
Erdős 881, granted for free: the whole content of the problem lives
in whether positive three-term representations can repair the
mandated two-destruction. -/
theorem DestroyedBySet.twoDestroyed {A B : Set ℕ} {m : ℕ}
    (hdes : DestroyedBySet A B m) (h0 : 0 ∈ A) (h0B : 0 ∉ B) :
    TwoDestroyedBySet A B m := by
  intro y hy z hz hyz
  rcases hdes.2 0 h0 y hy z hz (by omega) with h | h | h
  · exact absurd h h0B
  · exact Or.inl h
  · exact Or.inr h

/-- **Anchor supply from two disjoint packages.**  Two anchor packages
with disjoint supports dodge any single prescribed value. -/
theorem anchor_abundance_of_two_packages {A : Set ℕ}
    {c₁ w₁ w₁' c₂ w₂ w₂' : ℕ}
    (h₁ : c₁ ∈ A ∧ 0 < c₁ ∧ w₁ ∈ A ∧ w₁' ∈ A ∧
      w₁ + w₁' = 2 * c₁ ∧ w₁ ≠ c₁)
    (h₂ : c₂ ∈ A ∧ 0 < c₂ ∧ w₂ ∈ A ∧ w₂' ∈ A ∧
      w₂ + w₂' = 2 * c₂ ∧ w₂ ≠ c₂)
    (hdisj : c₁ ≠ c₂ ∧ c₁ ≠ w₂ ∧ c₁ ≠ w₂' ∧ w₁ ≠ c₂ ∧ w₁ ≠ w₂ ∧
      w₁ ≠ w₂' ∧ w₁' ≠ c₂ ∧ w₁' ≠ w₂ ∧ w₁' ≠ w₂') :
    ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g := by
  intro g
  obtain ⟨hc₁, hc₁0, hw₁, hw₁', hs₁, hn₁⟩ := h₁
  obtain ⟨hc₂, hc₂0, hw₂, hw₂', hs₂, hn₂⟩ := h₂
  by_cases hg : g = c₁ ∨ g = w₁ ∨ g = w₁'
  · exact ⟨c₂, hc₂, hc₂0, by omega, w₂, hw₂, w₂', hw₂',
      hs₂, hn₂, by omega, by omega⟩
  · push Not at hg
    exact ⟨c₁, hc₁, hc₁0, by omega, w₁, hw₁, w₁', hw₁',
      hs₁, hn₁, by omega, by omega⟩

/-- **Concentration.**  If the undeleted elements below a destroyed
target outnumber `n` copies of the deleted prefix, some single
deleted element `u` serves more than `n` of the fork routes: for each
such `x`, the landing point `m - x - u` falls back into `B` or plants
the two-destroyed cross-sum `u + x`.  This is the pigeonhole that
converts the fork trichotomy into density statements against the
diffuse regime. -/
theorem DestroyedBySet.concentration {A B : Set ℕ}
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] {N₀ m n : ℕ}
    (hcov : PairCovers A N₀)
    (hdes : DestroyedBySet A B m)
    (hcard : ((Finset.range (m + 1)).filter fun b => b ∈ B).card * n <
      ((Finset.range (m + 1)).filter
        fun x => x ∈ A ∧ x ∉ B ∧ x + N₀ ≤ m).card) :
    ∃ u ∈ B, ∃ S : Finset ℕ, n < S.card ∧
      ∀ x ∈ S, x ∈ A ∧ x ∉ B ∧ x + N₀ ≤ m ∧
        (m - x - u ∈ B ∨
          (m - x - u ∈ A ∧ TwoDestroyedBySet A B (u + x))) := by
  classical
  set X := (Finset.range (m + 1)).filter
    fun x => x ∈ A ∧ x ∉ B ∧ x + N₀ ≤ m with hX
  set T := (Finset.range (m + 1)).filter fun b => b ∈ B with hT
  have hpick : ∀ x ∈ X, ∃ u, u ∈ B ∧ u ≤ m - x ∧
      (m - x - u ∈ B ∨
        (m - x - u ∈ A ∧ TwoDestroyedBySet A B (u + x))) := by
    intro x hx
    simp only [hX, Finset.mem_filter, Finset.mem_range] at hx
    obtain ⟨u, huB, hum, hland⟩ :=
      hdes.fork_trichotomy_elt hcov hx.2.1 hx.2.2.1 hx.2.2.2
    exact ⟨u, huB, hum, hland⟩
  choose f hfB hfle hfland using hpick
  -- total function for the pigeonhole
  let g : ℕ → ℕ := fun x => if hx : x ∈ X then f x hx else 0
  have hmaps : ∀ x ∈ X, g x ∈ T := by
    intro x hx
    simp only [g, dif_pos hx]
    simp only [hT, Finset.mem_filter, Finset.mem_range]
    have h1 := hfB x hx
    have h2 := hfle x hx
    have hx' := hx
    simp only [hX, Finset.mem_filter, Finset.mem_range] at hx'
    exact ⟨by omega, h1⟩
  obtain ⟨u, huT, hufib⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hcard
  refine ⟨u, by
      simp only [hT, Finset.mem_filter] at huT
      exact huT.2, X.filter fun x => g x = u, hufib, ?_⟩
  intro x hx
  simp only [Finset.mem_filter] at hx
  obtain ⟨hxX, hgx⟩ := hx
  have hx' := hxX
  simp only [hX, Finset.mem_filter, Finset.mem_range] at hx'
  have hland := hfland x hxX
  have hgeq : f x hxX = u := by
    simpa [g, dif_pos hxX] using hgx
  rw [hgeq] at hland
  exact ⟨hx'.2.1, hx'.2.2.1, hx'.2.2.2, hland⟩

/-- **Translate exit.**  Combining concentration with the
two-destroyed avoidance of undeleted elements: some single `u ∈ B`
translates more than `n` undeleted elements clean out of `A \ B` —
either the landing point of the fork or the cross-sum itself falls
into `B ∪ (ℕ \ A)`.  A hereditarily diffuse structure must absorb
such translate-exits at every scale for every sparse deletion. -/
theorem DestroyedBySet.translate_exit {A B : Set ℕ}
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] {N₀ m n : ℕ}
    (h0 : 0 ∈ A) (h0B : 0 ∉ B)
    (hcov : PairCovers A N₀)
    (hdes : DestroyedBySet A B m)
    (hcard : ((Finset.range (m + 1)).filter fun b => b ∈ B).card * n <
      ((Finset.range (m + 1)).filter
        fun x => x ∈ A ∧ x ∉ B ∧ x + N₀ ≤ m).card) :
    ∃ u ∈ B, ∃ S : Finset ℕ, n < S.card ∧
      ∀ x ∈ S, x ∈ A ∧ x ∉ B ∧
        (m - x - u ∈ B ∨ u + x ∈ B ∨ u + x ∉ A) := by
  obtain ⟨u, huB, S, hScard, hS⟩ :=
    hdes.concentration hcov hcard
  refine ⟨u, huB, S, hScard, ?_⟩
  intro x hx
  obtain ⟨hxA, hxB, hxm, hland⟩ := hS x hx
  refine ⟨hxA, hxB, ?_⟩
  rcases hland with h | ⟨hwA, htwo⟩
  · exact Or.inl h
  · by_cases huxA : u + x ∈ A
    · by_cases huxB : u + x ∈ B
      · exact Or.inr (Or.inl huxB)
      · exact absurd htwo
          (not_twoDestroyedBySet_of_mem_diff h0 h0B huxA huxB)
    · exact Or.inr (Or.inr huxA)

/-- **Zero-guarded targets repel element differences.**  If every
representation of both `m₁ < m₂` passes through `0`, then `m₂ - m₁`
cannot be an element: the mirror of any positive `x` below `m₁`
would combine with the difference into a positive representation of
`m₂`.  The zero-guardian residue therefore forces the whole cofinal
target family to have an `A`-free difference set. -/
theorem zero_guardian_no_element_gap {A : Set ℕ} {N₀ m₁ m₂ x : ℕ}
    (hcov : PairCovers A N₀)
    (h1 : IsPrivateTriple A 0 m₁) (h2 : IsPrivateTriple A 0 m₂)
    (hlt : m₁ < m₂)
    (hx : x ∈ A) (hx0 : 0 < x) (hxm : x + N₀ ≤ m₁) (hxlt : x < m₁)
    (hd : m₂ - m₁ ∈ A) :
    False := by
  obtain ⟨y, hy, z, hz, hyz⟩ := hcov (m₁ - x) (by omega)
  have hw : m₁ - x ∈ A := by
    rcases h1.2 x hx y hy z hz (by omega) with h | h | h
    · omega
    · have : z = m₁ - x := by omega
      exact this ▸ hz
    · have : y = m₁ - x := by omega
      exact this ▸ hy
  rcases h2.2 x hx (m₁ - x) hw (m₂ - m₁) hd (by omega) with h | h | h <;>
    omega

/-- **Zero-guarded targets are never elements** (once separated): an
element target `m₁ ∈ A` would put the difference `m₂ - m₁` into `A`
by the mirror of the higher target, contradicting
`zero_guardian_no_element_gap`.  The zero residue is thus confined to
cofinal *non-element* targets with an `A`-free difference set. -/
theorem zero_guardian_target_not_elt {A : Set ℕ} {N₀ m₁ m₂ x : ℕ}
    (hcov : PairCovers A N₀)
    (h1 : IsPrivateTriple A 0 m₁) (h2 : IsPrivateTriple A 0 m₂)
    (hlt : m₁ < m₂) (hsep : m₁ + N₀ ≤ m₂)
    (hm₁A : m₁ ∈ A) (hm₁0 : 0 < m₁)
    (hx : x ∈ A) (hx0 : 0 < x) (hxm : x + N₀ ≤ m₁) (hxlt : x < m₁) :
    False := by
  obtain ⟨y, hy, z, hz, hyz⟩ := hcov (m₂ - m₁) (by omega)
  have hd : m₂ - m₁ ∈ A := by
    rcases h2.2 m₁ hm₁A y hy z hz (by omega) with h | h | h
    · omega
    · have : z = m₂ - m₁ := by omega
      exact this ▸ hz
    · have : y = m₂ - m₁ := by omega
      exact this ▸ hy
  exact zero_guardian_no_element_gap hcov h1 h2 hlt hx hx0 hxm hxlt hd

/-- **Three zero-guarded targets carve holes.**  Mirrors of the two
lower targets combine into positive parts, so the balance
`m₃ - (m₁ - x) - (m₂ - y)` can never be a positive element: the zero
residue forces `A⁺` to avoid `m₃ - m₁ - m₂` plus the whole sumset of
the two mirror windows. -/
theorem zero_guardian_hole {A : Set ℕ} {N₀ m₁ m₂ m₃ x y z : ℕ}
    (hcov : PairCovers A N₀)
    (h1 : IsPrivateTriple A 0 m₁) (h2 : IsPrivateTriple A 0 m₂)
    (h3 : IsPrivateTriple A 0 m₃)
    (hx : x ∈ A) (hx0 : 0 < x) (hxm : x + N₀ ≤ m₁) (hxlt : x < m₁)
    (hy : y ∈ A) (hy0 : 0 < y) (hym : y + N₀ ≤ m₂) (hylt : y < m₂)
    (hz : z ∈ A) (hz0 : 0 < z)
    (hsum : (m₁ - x) + (m₂ - y) + z = m₃) :
    False := by
  obtain ⟨y₁, hy₁, z₁, hz₁, hyz₁⟩ := hcov (m₁ - x) (by omega)
  have hw₁ : m₁ - x ∈ A := by
    rcases h1.2 x hx y₁ hy₁ z₁ hz₁ (by omega) with h | h | h
    · omega
    · have : z₁ = m₁ - x := by omega
      exact this ▸ hz₁
    · have : y₁ = m₁ - x := by omega
      exact this ▸ hy₁
  obtain ⟨y₂, hy₂, z₂, hz₂, hyz₂⟩ := hcov (m₂ - y) (by omega)
  have hw₂ : m₂ - y ∈ A := by
    rcases h2.2 y hy y₂ hy₂ z₂ hz₂ (by omega) with h | h | h
    · omega
    · have : z₂ = m₂ - y := by omega
      exact this ▸ hz₂
    · have : y₂ = m₂ - y := by omega
      exact this ▸ hy₂
  rcases h3.2 (m₁ - x) hw₁ (m₂ - y) hw₂ z hz hsum with h | h | h <;>
    omega

/-- **The zero residue, packaged.**  If zero guards cofinally, then
for any pair of separated targets: the lower target is not an
element, the gap between targets is not an element, and every
mirror-window sum combination is barred from being a positive
element.  The residue is an extremely rigid object: cofinal
non-element targets with an `A`-free difference set carving
positive-sumset holes. -/
theorem zero_residue_structure {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hres : ∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A 0 m)
    (x : ℕ) (hx : x ∈ A) (hx0 : 0 < x) :
    ∀ N, ∃ m₁ m₂, N ≤ m₁ ∧ m₁ + N₀ ≤ m₂ ∧
      IsPrivateTriple A 0 m₁ ∧ IsPrivateTriple A 0 m₂ ∧
      (x + N₀ ≤ m₁ → x < m₁ → (m₂ - m₁ ∉ A ∧ (0 < m₁ → m₁ ∉ A))) := by
  intro N
  obtain ⟨m₁, hm₁N, h1⟩ := hres N
  obtain ⟨m₂, hm₂N, h2⟩ := hres (m₁ + N₀)
  refine ⟨m₁, m₂, hm₁N, hm₂N, h1, h2, ?_⟩
  intro hxm hxlt
  constructor
  · intro hd
    exact zero_guardian_no_element_gap hcov h1 h2 (by omega)
      hx hx0 hxm hxlt hd
  · intro hm₁0 hm₁A
    exact zero_guardian_target_not_elt hcov h1 h2 (by omega)
      (by omega) hm₁A hm₁0 hx hx0 hxm hxlt

end Erdos881
