# Well-founded-rank program

Status: historical program with a verified foundation and an unresolved
strict-descent step.

## Definition of the rank

Under the order-two counterexample hypothesis, finite free subsets of the
basis form a well-founded extension relation. The following results are proved
in `FreeRank.lean`:

- `freeStep_wf`: the extension relation is well-founded;
- `exists_strict_rank`: the relation admits an ordinal-valued rank that
  strictly decreases along an extension edge;
- `root_rank_dichotomy`: the root rank is either finite or at least `ω`;
- `poolFreeStep_wf`: the construction can be repeated inside an infinite
  pool;
- `pool_rank_mono`: shrinking a pool gives weak rank monotonicity;
- `pool_rank_pos`: the relevant pool ranks are positive;
- `no_pool_rank_descent`: a suitable strictly rank-decreasing pool operation
  would contradict the counterexample hypothesis.

## Missing theorem

No general operation is known that maps each admissible pool to a smaller
pool with strictly smaller rank. Existing operations provide only weak
monotonicity or produce disjoint finite support transversals without
decreasing a known ordinal measure.

Therefore `no_pool_rank_descent` is a conditional closing criterion, not a
completed proof.

## Quantitative information

The rank program developed several additional tools:

- `rep_cofinal_supply_pool` and `pair_cofinal_supply_iteration` construct
  finite obstruction families inside successive pools;
- `robustness_gives_hereditarily_free` shows that uniformly increasing
  disjoint-representation supply yields an infinite free structure;
- bounded-transversal theorems give the complementary fragile case;
- `absolute_rank_layer_stratification` and `depth_tax_of_hfail` constrain the
  location of finite rank layers;
- `disjoint_reps_le_support_transversal_card` relates matching size to
  support-transversal size.

These results show that a counterexample would have to alternate between
targets with large representation supply and targets controlled by small
support transversals. Because the targets are selected independently by
cofinal quantifiers, the two behaviors need not occur at the same positions.

## Why the route was not completed

The main failed inference was to treat cofinal occurrence as simultaneous or
uniform occurrence. A target supplied by one theorem may be arbitrarily far
from targets supplied by another theorem. Static counting estimates therefore
do not by themselves define a decreasing rank.

The current direct-construction approach avoids this problem by fixing a
finite certificate and localizing one target of that certificate. The
selector localization in `PrivateCoreStream.lean` is a finite analogue of the
desired rank control, but it currently yields unbounded finite certificates
rather than a global ordinal descent.

## Reusable results

The following parts remain relevant:

- well-founded recursion on finite obstruction families;
- monotonicity under restriction to an infinite pool;
- matching-versus-support transversal alternatives;
- finite rank layers and their location bounds;
- rank descent once a target-local operation has been constructed.

For the active proof route, see `solution-status.md`.
