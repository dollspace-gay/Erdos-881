import Erdos881.TeamGraphRamsey

/-!
# A separated team triangle inside a full covering set

The pigeonhole theorem `infinite_teamClique_has_separated_triple`
extracts, from any infinite team clique, triples of guards at
arbitrarily prescribed separations.  The hoped-for closing move was
`no_separated_triangle`: that one such triple is already contradictory
against covering.  **This file refutes that hope**: the set

  `A = [0, 9] ∪ [18, 26] ∪ {53, 62} ∪ [89, ∞)`

pair-covers every integer from `12` on, contains `0`, and its three
guards `9, 53, 62` — with `53 > 5 · 9` — pairwise destroy the targets
`79`, `88`, `81`.  Guard separation alone therefore kills nothing: a
proof of Open Link B must use the *infinitude* of the clique (the
pinned-mirror route of `PinnedMirror.lean`) or a much stronger
separation regime (the lab finds no triangle whose filler blocks are
wider than its base block: `scripts/probe_pinned_forks.py` P3,
`scripts/probe_pinned_mirror.py` V1).
-/

namespace Erdos881

/-- The witness set: two interval blocks, two high guards, and a full
interval tail restoring covering above the destroyed window. -/
def sepTriangleSet : Set ℕ :=
  {n | n ≤ 9 ∨ (18 ≤ n ∧ n ≤ 26) ∨ n = 53 ∨ n = 62 ∨ 89 ≤ n}

theorem mem_sepTriangleSet {n : ℕ}
    (h : n ≤ 9 ∨ (18 ≤ n ∧ n ≤ 26) ∨ n = 53 ∨ n = 62 ∨ 89 ≤ n) :
    n ∈ sepTriangleSet := h

theorem sepTriangleSet_cases {n : ℕ} (h : n ∈ sepTriangleSet) :
    n ≤ 9 ∨ (18 ≤ n ∧ n ≤ 26) ∨ n = 53 ∨ n = 62 ∨ 89 ≤ n := h

theorem sepTriangleSet_zero_mem : (0 : ℕ) ∈ sepTriangleSet :=
  mem_sepTriangleSet (by omega)

/-- The witness set pair-covers `[12, ∞)`. -/
theorem sepTriangleSet_pairCovers : PairCovers sepTriangleSet 12 := by
  intro n hn
  rcases Nat.lt_or_ge n 19 with h | h
  · exact ⟨9, mem_sepTriangleSet (by omega), n - 9,
      mem_sepTriangleSet (by omega), by omega⟩
  rcases Nat.lt_or_ge n 27 with h' | h'
  · exact ⟨0, sepTriangleSet_zero_mem, n,
      mem_sepTriangleSet (by omega), by omega⟩
  rcases Nat.lt_or_ge n 36 with h'' | h''
  · exact ⟨n - 26, mem_sepTriangleSet (by omega), 26,
      mem_sepTriangleSet (by omega), by omega⟩
  rcases Nat.lt_or_ge n 45 with h₃ | h₃
  · exact ⟨18, mem_sepTriangleSet (by omega), n - 18,
      mem_sepTriangleSet (by omega), by omega⟩
  rcases Nat.lt_or_ge n 53 with h₄ | h₄
  · exact ⟨n - 26, mem_sepTriangleSet (by omega), 26,
      mem_sepTriangleSet (by omega), by omega⟩
  rcases Nat.lt_or_ge n 63 with h₅ | h₅
  · exact ⟨53, mem_sepTriangleSet (by omega), n - 53,
      mem_sepTriangleSet (by omega), by omega⟩
  rcases Nat.lt_or_ge n 72 with h₆ | h₆
  · exact ⟨62, mem_sepTriangleSet (by omega), n - 62,
      mem_sepTriangleSet (by omega), by omega⟩
  rcases Nat.lt_or_ge n 80 with h₇ | h₇
  · exact ⟨53, mem_sepTriangleSet (by omega), n - 53,
      mem_sepTriangleSet (by omega), by omega⟩
  rcases Nat.lt_or_ge n 89 with h₈ | h₈
  · exact ⟨62, mem_sepTriangleSet (by omega), n - 62,
      mem_sepTriangleSet (by omega), by omega⟩
  · exact ⟨0, sepTriangleSet_zero_mem, n,
      mem_sepTriangleSet (by omega), by omega⟩

/-- `{9, 53}` destroys `79`: every three-term representation meets the
pair (the tail is too high, `[18,26]³` tops out at `78`, and the
`62`-route needs a pair summing to `17`, which the guardless blocks
cannot produce). -/
theorem sepTriangleSet_destroyer_79 :
    IsPairDestroyer sepTriangleSet 9 53 79 := by
  constructor
  · exact ⟨53, mem_sepTriangleSet (by omega), 26,
      mem_sepTriangleSet (by omega), 0, sepTriangleSet_zero_mem,
      by omega⟩
  · intro x hx y hy z hz hsum
    have hx' := sepTriangleSet_cases hx
    have hy' := sepTriangleSet_cases hy
    have hz' := sepTriangleSet_cases hz
    omega

/-- `{9, 62}` destroys `88`. -/
theorem sepTriangleSet_destroyer_88 :
    IsPairDestroyer sepTriangleSet 9 62 88 := by
  constructor
  · exact ⟨62, mem_sepTriangleSet (by omega), 26,
      mem_sepTriangleSet (by omega), 0, sepTriangleSet_zero_mem,
      by omega⟩
  · intro x hx y hy z hz hsum
    have hx' := sepTriangleSet_cases hx
    have hy' := sepTriangleSet_cases hy
    have hz' := sepTriangleSet_cases hz
    omega

/-- `{53, 62}` destroys `81`. -/
theorem sepTriangleSet_destroyer_81 :
    IsPairDestroyer sepTriangleSet 53 62 81 := by
  constructor
  · exact ⟨53, mem_sepTriangleSet (by omega), 26,
      mem_sepTriangleSet (by omega), 2, mem_sepTriangleSet (by omega),
      by omega⟩
  · intro x hx y hy z hz hsum
    have hx' := sepTriangleSet_cases hx
    have hy' := sepTriangleSet_cases hy
    have hz' := sepTriangleSet_cases hz
    omega

/-- **Guard separation alone cannot kill a team triangle.**  A full
covering set with `0` carries three pairwise team edges whose guards
are separated by a factor of five.  Any proof of Open Link B must use
more than one triple. -/
theorem separated_triangle_realizable :
    ∃ A : Set ℕ, 0 ∈ A ∧ PairCovers A 12 ∧
      ∃ u v w : ℕ, 5 * u < v ∧ v < w ∧
        TeamEdge A u v ∧ TeamEdge A u w ∧ TeamEdge A v w := by
  refine ⟨sepTriangleSet, sepTriangleSet_zero_mem,
    sepTriangleSet_pairCovers, 9, 53, 62, by omega, by omega,
    ⟨by omega, 79, by omega, by omega, sepTriangleSet_destroyer_79⟩,
    ⟨by omega, 88, by omega, by omega, sepTriangleSet_destroyer_88⟩,
    ⟨by omega, 81, by omega, by omega, sepTriangleSet_destroyer_81⟩⟩

end Erdos881
