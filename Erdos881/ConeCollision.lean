/-
# The cone–coverage collision

Direct-construction campaign, stage three.  A pinned target's
translate cone (`pinned_forces_gap`) meets the basis property
head-on: at base order `k`, coverage SUPPLIES a representation to
every translate `n - x`, while pinnedness FORCES every one of
those representations through a finite hub.  The collision
produces counting pressure:

- `pinned_cone_hubbed`: every basis translate of a pinned target
  is covered-but-hubbed — representations exist and all meet the
  finite hub `insert f G`.  Coverage demands supply, the cone
  forbids clean supply, so the hub carries the whole load.
- `pinned_reflects_basis`: therefore the hubbed set is at least
  as dense as `A` itself in every reflected window of every
  pinned target — a per-target counting bound.
- `pinned_pair_fiber` / `hornA_giant_fibers`: TWO pinned targets
  at the same element put the whole reflected basis inside a
  fixed-difference fiber of the hubbed set; an unbounded pinned
  family (classification horn (a)) therefore forces hubbed
  fibers of unbounded cardinality at a single finite hub.
- `cleanSupply_failure_forces_fibers`: the crystallized frontier.
  Over an exact order-`k` basis, a failed clean-redundancy supply
  forces either giant fixed-difference hubbed fibers at base
  order `k` over one finite hub, or the atomic tail (every large
  element owns a pinned target above itself).  These are the
  configurations the `k = 2` engine's fiber artillery killed at
  order two — now facing FINITE obstructions.

Shape filter: `HubbedAt` conclusions force every representation
through a named finite set (membership forced), and the fiber
conclusions are cardinality lower bounds — no sumset vacuity.
-/

import Erdos881.DesertConcentration

namespace Erdos881

open Classical

/-- Covered but hubbed: order-`h` representations of `m` exist,
and every one meets the finite hub `H`. -/
def HubbedAt (A : Set ℕ) (h : ℕ) (H : Finset ℕ)
    (m : ℕ) : Prop :=
  (∃ w : Fin h → ℕ, (∀ i, w i ∈ A) ∧ ∑ i, w i = m) ∧
  ∀ w : Fin h → ℕ, (∀ i, w i ∈ A) → ∑ i, w i = m →
    ∃ i, w i ∈ H

/-- Pinnedness is strandedness after inserting the pin. -/
theorem PinnedAt.stranded_insert {A : Set ℕ} {h : ℕ}
    {F : Finset ℕ} {f n : ℕ}
    (hpin : PinnedAt A h F f n) :
    StrandedAt A h (insert f F) n := by
  rintro ⟨v, hv, hsum⟩
  obtain ⟨i, hi⟩ := hpin.2 v
    (fun i => ⟨(hv i).1, fun hmem => (hv i).2
      (Finset.mem_insert_of_mem hmem)⟩) hsum
  exact (hv i).2 (by rw [hi]; exact
    Finset.mem_insert_self f F)

/-- **The cone–coverage collision.**  Every basis translate of a
target pinned at order `k+1` is covered at order `k` — the basis
supplies representations — yet every representation is forced
through the finite hub `insert f G`: the cone forbids clean
supply exactly where coverage demands it. -/
theorem pinned_cone_hubbed {A : Set ℕ} {k : ℕ}
    {G : Finset ℕ} {f n N₀ : ℕ}
    (hcov : ∀ m, N₀ ≤ m → ∃ w : Fin k → ℕ,
      (∀ i, w i ∈ A) ∧ ∑ i, w i = m)
    (hpin : PinnedAt A (k + 1) G f n)
    {x : ℕ} (hx : x ∈ A) (hxG : x ∉ insert f G)
    (hxn : x + N₀ ≤ n) :
    HubbedAt A k (insert f G) (n - x) := by
  have hstr : StrandedAt A k (insert f G) (n - x) :=
    hpin.stranded_insert.descend hx hxG (by omega)
  refine ⟨hcov (n - x) (by omega), ?_⟩
  intro w hw hsum
  by_contra hcon
  push Not at hcon
  exact hstr ⟨w, fun i => ⟨hw i, hcon i⟩, hsum⟩

/-- **Reflection counting**: the hubbed set is at least as dense
as the basis itself in every reflected window of every pinned
target. -/
theorem pinned_reflects_basis {A : Set ℕ} {k : ℕ}
    {G : Finset ℕ} {f n N₀ : ℕ}
    (hcov : ∀ m, N₀ ≤ m → ∃ w : Fin k → ℕ,
      (∀ i, w i ∈ A) ∧ ∑ i, w i = m)
    (hpin : PinnedAt A (k + 1) G f n)
    (y : ℕ) (hy : y + N₀ ≤ n) :
    ((Finset.range (y + 1)).filter
      (fun x => x ∈ A ∧
        x ∉ (insert f G : Finset ℕ))).card ≤
    ((Finset.Icc (n - y) n).filter
      (fun m =>
        HubbedAt A k (insert f G) m)).card := by
  refine Finset.card_le_card_of_injOn
    (fun x => n - x) ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range] at hx
    obtain ⟨hxy, hxA, hxG⟩ := hx
    simp only [Finset.mem_coe, Finset.mem_filter,
      Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    exact pinned_cone_hubbed hcov hpin hxA hxG
      (by omega)
  · intro x₁ h₁ x₂ h₂ heq
    simp only [Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range] at h₁ h₂
    simp only at heq
    omega

/-- **Fixed-difference fibers**: two targets pinned at the same
element place every reflected basis element inside the
difference-`d` fiber of the hubbed set. -/
theorem pinned_pair_fiber {A : Set ℕ} {k : ℕ}
    {G : Finset ℕ} {f n n' N₀ : ℕ}
    (hcov : ∀ m, N₀ ≤ m → ∃ w : Fin k → ℕ,
      (∀ i, w i ∈ A) ∧ ∑ i, w i = m)
    (hpin : PinnedAt A (k + 1) G f n)
    (hpin' : PinnedAt A (k + 1) G f n')
    (hle : n ≤ n')
    {x : ℕ} (hx : x ∈ A) (hxG : x ∉ insert f G)
    (hxn : x + N₀ ≤ n) :
    HubbedAt A k (insert f G) (n - x) ∧
    HubbedAt A k (insert f G)
      ((n - x) + (n' - n)) := by
  refine ⟨pinned_cone_hubbed hcov hpin hx hxG hxn, ?_⟩
  have h1 : (n - x) + (n' - n) = n' - x := by omega
  rw [h1]
  exact pinned_cone_hubbed hcov hpin' hx hxG
    (by omega)

/-- **Giant fibers at horn (a)**: an unbounded pinned family at
one element over one finite codeletion forces, for every `L`, a
positive difference `d` whose hubbed fiber holds `L` distinct
members — the `k = 2` engine's fiber configuration at base order
`k`, over a finite hub. -/
theorem hornA_giant_fibers {A : Set ℕ} {k : ℕ}
    {G : Finset ℕ} {f : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hp : ∀ M, ∃ n, M ≤ n ∧
      PinnedAt A (k + 1) G f n) :
    ∀ L, ∃ d, 0 < d ∧ ∃ S : Finset ℕ, L ≤ S.card ∧
      ∀ m ∈ S, HubbedAt A k (insert f G) m ∧
        HubbedAt A k (insert f G) (m + d) := by
  intro L
  have hinf : A.Infinite :=
    IsExactTupleAsymptoticBasis.infinite hbasis
  obtain ⟨N₀, hcov⟩ := hbasis
  obtain ⟨T, hTsub, hTcard⟩ :=
    hinf.exists_subset_card_eq
      (L + (insert f G).card)
  have hTA : ∀ x ∈ T, x ∈ A := fun x hx => hTsub hx
  set T' := T \ insert f G with hT'
  have hT'card : L ≤ T'.card := by
    have hsd : T.card - (insert f G).card ≤
        T'.card := by
      rw [hT']
      exact Finset.le_card_sdiff _ _
    omega
  set y := T.sup id with hy
  have hTy : ∀ x ∈ T, x ≤ y := fun x hx =>
    Finset.le_sup (f := id) hx
  obtain ⟨n, hn, hpin⟩ := hp (y + N₀)
  obtain ⟨n', hn', hpin'⟩ := hp (n + 1)
  refine ⟨n' - n, by omega, T'.image (fun x => n - x),
    ?_, ?_⟩
  · rw [Finset.card_image_of_injOn]
    · exact hT'card
    · intro x₁ h₁ x₂ h₂ heq
      have hx₁ := hTy x₁ (Finset.mem_sdiff.mp h₁).1
      have hx₂ := hTy x₂ (Finset.mem_sdiff.mp h₂).1
      simp only at heq
      omega
  · intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨x, hxT', rfl⟩ := hm
    rw [Finset.mem_sdiff] at hxT'
    obtain ⟨hxT, hxG⟩ := hxT'
    have hxy := hTy x hxT
    have hcone := pinned_pair_fiber hcov hpin hpin'
      (by omega) (hTA x hxT) hxG (by omega)
    exact ⟨hcone.1, by
      have h1 : n - x + (n' - n) =
          (n - x) + (n' - n) := rfl
      exact hcone.2⟩

/-- **The crystallized frontier.**  Over an exact order-`k`
basis, a failed clean-redundancy supply at order `k+1` forces
one of two configurations at BASE order `k` over finite hubs:

- giant fibers: one finite hub carries fixed-difference hubbed
  fibers of unbounded cardinality, or
- the atomic tail: beyond some bound every element owns a pinned
  target above itself.

Contrapositively: rule these out and the chain theorem delivers
the surviving deletion.  This is the `k = 2` fiber/atomic
artillery's exact target shape, downgraded from infinite
deletions to finite hubs. -/
theorem cleanSupply_failure_forces_fibers {A : Set ℕ}
    {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hfail : ¬ HasCleanSupply A (k + 1)) :
    (∃ H : Finset ℕ, ∀ L, ∃ d, 0 < d ∧
      ∃ S : Finset ℕ, L ≤ S.card ∧
        ∀ m ∈ S, HubbedAt A k H m ∧
          HubbedAt A k H (m + d)) ∨
    (∃ F : Finset ℕ, ∃ M, ∀ b, b ∈ A → M ≤ b →
      ∃ n, b ≤ n ∧ PinnedAt A (k + 1) F b n) := by
  obtain ⟨F, hclass⟩ :=
    cleanSupply_failure_classification
      (hbasis.of_le (by omega)) hfail
  rcases hclass with ⟨f, _, G, _, _, hp⟩ | htail
  · exact Or.inl ⟨insert f G,
      hornA_giant_fibers hbasis hp⟩
  · exact Or.inr ⟨F, htail⟩

end Erdos881
