> [!NOTE]
> **AI use disclosure**
>
> This project was developed through an iterative conversation between Alberto and OpenAI's Codex. Alberto chose the computational-geometry lab problem, proposed and refined the depth-limited punching variation and the pair/triple constructions, asked questions about the arguments, and directed the progression from definitions to local lemmas and complete algorithms. He also requested explicit, readable tactic proofs.
>
> Codex generated the project's Lean definitions, proof scripts, and supporting lemmas; selected Mathlib results; organized the files; debugged compilation errors; ran builds and axiom checks; and drafted documentation. Codex also helped refine the mathematical model and explanations, including exposed-layer order, the effect of earlier holes, and the distinction between per-batch and total crease bounds. The interaction included discussion and revision, not just code completion. The Lean implementation should therefore be understood as AI-generated work developed under human direction, not as independently human-written code. Codex also helped edit explanations for the accompanying lab post.
>
> The conversation initially explored formalizing Theorem 9 of a paper, but that attempt was stopped and replaced by the current k=2/k=3 project. The checked results here concern the stated idealized model. The final build and axiom checks found no `sorry` or custom axioms in the proofs; Lean checking establishes the formal statements from their definitions and assumptions, not optimality or physical realizability.

# Convex-paper fold and punch

Complete checked algorithms for k=2 and k=3, with explicit geometric crease
bounds: at most n/2 creases for even n, and at most n creases when 3 divides n.
This replaces the previous conditional formalization of Theorem 9.

## Problem and scope

The input is a filled convex polygon with one marked point at every vertex.
A depth-k punch removes the first k layers from the selected side; deeper layers
remain intact. A successful operation must hit exactly k fresh marked vertices.
We unfold fully between batches, retaining holes and the geometric crease history.

For every convex input polygon with an even number n of vertices, the current
milestone constructs consecutive pairs (0,1), (2,3), and so on, and proves:

- Every punch removes exactly its two fresh marked vertices, with no extra holes.
- Each batch unfolds completely, preserving the other vertices and earlier holes.
- After all batches the remaining sheet is exactly the polygon minus its vertices.
- There are exactly n/2 pair operations.
- The actual cumulative crease trace has at most n/2 distinct maximal segments.

`Paper.k2_correct_and_linear` combines these statements. The bound C <= n/2 is
an explicit uniform O(n) upper bound; we have not introduced Mathlib's separate
asymptotic notation or proved a lower bound/optimality result. No `sorry` or custom
axioms are used. The second fold of stacked paper is now proved to contribute
at most two creases, giving at most three for two folds. The depth-three punch
is also checked: fold i onto j, check whether the third vertex is on top or
bottom of its current stack, then bring the pair onto it from that side and
punch from the same side. A fourth layer, if present, is untouched.
The complete iteration is now proved in `Paper.k3_correct_and_linear`. For n
vertices with n divisible by three, it constructs (0,1,2), (3,4,5), and so on,
and proves every punch safe, all and only vertices removed, a well-formed final
state, exactly n/3 batches, and at most n maximal crease segments.

`Paper.triples_correct_and_linear` also accepts any duplicate-free partition
covering all vertices. With m triples, its bound is 3m. This is an upper bound
on the union of actual crease traces: overlap, reuse, and merging may reduce it.
The assumption 3 divides n ensures no vertices are left over under the rule
that every successful punch removes exactly three fresh vertices.
3D physical realizability remains outside the model.

## Reading order

1. `FoldAndPunch/Geometry.lean`
   - `Point`: Mathlib's two-dimensional real Euclidean space.
   - `Paper`: Mathlib's polygon type plus distinctness, nonempty interior,
     exact corner set, and cyclic boundary-order conditions.
   - `region`: the convex hull of its vertices.
   - `Fold`: two distinct current locations determine an oriented perpendicular
     bisector. The source half moves toward the target half, over or under it.
   - `reflect`: Mathlib's reflection in that affine subspace.
   - `pointMap`: reflection on the moving half-plane, identity elsewhere.
2. `FoldAndPunch/Folding.lean`
   - `Configuration`: surviving original paper points, their current positions,
     and finite lists of original points ordered from top to bottom at each location.
   - `WellFormed`: connects those lists to the geometric map and prevents duplicate
     or fictitious layers. It does not by itself certify reachability.
   - `initial`, `unfold`, `fold`, and `foldSequence`: concrete state operations.
     Turning a stack over reverses its order; the placement chooses which stack
     is above. Points on the fold axis are counted once and retain their order.
3. `FoldAndPunch/Punching.lean`
   - `layersFrom`: read a stack from above or below.
   - `punchHits`: take its first k layers.
   - `punch`: remove those original points from material and all stacks.
   - `SuccessfulPunch`: exactly the selected k fresh vertices are hit.
   - `AllVerticesPunched`: the remaining material is the original sheet minus
     precisely the marked points.
   - `Batching`: disjoint batches of size k covering all vertices once.
4. `FoldAndPunch/Creases.lean`
   - `hingeTrace`: original points lying on the current fold axis. This is only a
     candidate trace; a tangential contact need not produce an actual crease.
   - `IsCreaseSegment`: a nondegenerate closed straight segment, represented as a
     set so endpoint reversal does not create a different crease.
   - `cumulativeCreases`: union of geometric traces with closure, so point holes
     do not split an existing crease.
   - `CreaseDecomposition`: finite maximal segments covering the trace. Collinear
     adjoining segments must be merged; crossings do not split a segment.
   - `HasAtMostCreases`: a cardinality bound on such a decomposition.

The proof modules build on those definitions:

5. `FoldAndPunch/FoldLemmas.lean`: reflection swaps source and target, fixes the
   axis, and exchanges the two half-planes. The vacated side has no preimages;
   axis points have one; receiving-side points off the axis have exactly two
   geometric preimages in the plane (not necessarily both in the sheet).
6. `FoldAndPunch/ConfigurationLemmas.lean`: flat material is well formed, and
   folding any well-formed state preserves its consistency. Reflected and
   stationary stacks cannot contain the same original point away from the axis.
7. `FoldAndPunch/Pair.lean`: the pair fold, its exact stack, and successful punch.
8. `FoldAndPunch/CreaseLemmas.lean`: a compact convex set on a line is a segment;
   a bisector through the sheet crosses its interior; the resulting crease is a
   nondegenerate chord with a singleton maximal-segment decomposition.
9. `FoldAndPunch/PairCreases.lean`: the one-crease bound and the combined
   safe-punch/exactly-one-crease theorem.
10. `FoldAndPunch/PunchingLemmas.lean`: punching/unfolding consistency, exact
    removal of a pair, and invariance of flat-fold creases under earlier vertex holes.
11. `FoldAndPunch/PairBatches.lean`: concrete pair operations, recursive execution,
    actual crease history, and induction proving safety and exact remaining material.
12. `FoldAndPunch/PairCreaseCount.lean`: full chords are maximal in the polygon;
    keeping one copy of each distinct chord bounds the cumulative count by the
    number of pair operations.
13. `FoldAndPunch/K2.lean`: consecutive pairing of all vertices for even n, proof
    that no vertex is dropped or repeated, the n/2 operation count, and the combined
    correctness/linear-bound theorem.

14. `FoldAndPunch/CreaseUnions.lean`: a finite segment cover gives a maximal-segment
    decomposition of no greater size. Consequently, union costs at most the sum
    of the individual bounds, even with crossings, overlaps, and adjoining pieces.
15. `FoldAndPunch/SecondFoldCreases.lean`: the first fold leaves two convex open
    material patches. On each, the second hinge pulls back to a straight line;
    each contribution is empty or one segment. The second-fold trace agrees with
    the existing configuration map away from the old hinge. The main results are
    `Paper.second_fold_atMost_two_creases`, `Paper.two_folds_atMost_three_creases`,
    and `Paper.pair_then_fold_atMost_three_creases`.

16. `FoldAndPunch/Triple.lean`: every stack after one flat-sheet fold has at most
    two layers. `exposureSide` checks the stack's top entry; `exposureSide_spec`
    proves the selected side exposes the third point. `secondTripleFold` moves
    the pair to that point's current location. `Paper.tripleFold_successful`
    proves an exactly-three punch for any three fresh distinct vertices, even
    with earlier holes. `Paper.triple_ready_to_punch_with_three_creases` combines
    this with the three-crease bound for a triple on the original sheet.

17. `FoldAndPunch/TripleBatches.lean`: concrete triple operations, recursive
    execution, and actual crease history. `Paper.runTriples_spec` proves safety,
    exact remaining material, and the 3m cumulative bound by induction.
    `Paper.twoFoldCreases_remove_marked` proves that earlier boundary holes do
    not change either fold's trace; placement is recomputed on the current sheet.
18. `FoldAndPunch/K3.lean`: correctness for arbitrary triple partitions, explicit
    consecutive grouping without dropped or repeated vertices when 3 divides n,
    and `Paper.k3_correct_and_linear`, combining completion with the n-crease bound.

Start with `Paper.k2_correct_and_linear` in `K2.lean` or
`Paper.k3_correct_and_linear` in `K3.lean`. The triple proof uses
`Paper.runTriples_spec`, `Paper.twoFoldCreases_remove_marked`, and
`HasAtMostCreases.union` to combine the previously verified local results.

Earlier local results:

- `flat_fold_stack_at_target`: the stack is `[source, target]` for an overfold
  and `[target, source]` for an underfold.
- `flat_fold_pair_hits`: punching from the placement side hits `[source, target]`.
- `Paper.pairFold_successful`: full `SuccessfulPunch` result for any unfolded
  remaining material inside the polygon, with both target vertices present.
- `Paper.pair_ready_to_punch`: the corresponding result for the initial polygon.
- `Paper.single_fold_isCreaseSegment`: the crease of the bisector fold is a
  nondegenerate segment, not merely a set assumed to have unit cost.
- `Paper.pairFold_one_crease`: at most one geometric crease for the pair fold.
- `Paper.pair_ready_to_punch_with_one_crease`: successful punching together with
  at most one crease and impossibility of zero creases.

Proofs use named facts and explicit tactic steps. The geometric/layer definitions
were not weakened to obtain these results. `FoldAndPunch.lean` imports all modules.

## Mathlib reuse

The dependency is Mathlib v4.34.1, locked in `lake-manifest.json` to
`d13f23b723b8a846827a245b89c10fc7d3f11612`, with Lean 4.34.1.
Local cached packages were copied into this project; there is no path dependency
on the neighboring project used to obtain them.

Existing library definitions used directly:

- `EuclideanSpace`, `Polygon`, `Polygon.boundary`
- `convexHull`, `Set.extremePoints`, `interior`, `frontier`, `segment`
- `AffineSubspace.perpBisector`, `EuclideanGeometry.reflection`
- `List`, `Finset`, list reversal and prefixes

Source references at the pinned revision:

- [Polygon](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Geometry/Polygon/Basic.lean)
- [Perpendicular bisector](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Geometry/Euclidean/PerpBisector.lean)
- [Reflection](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Geometry/Euclidean/Projection.lean)

## Explicit modeling choices

- These are real-coordinate mathematical definitions, not an executable numerical
  simulator. Definitions involving arbitrary real comparisons are noncomputable.
- Folds act on all layers in the selected half-plane. This is the agreed baseline;
  independently moving a single layer is not yet modeled.
- Overfolds and underfolds are allowed as idealized operations. We do not model a
  collision-free 3D motion, paper thickness, or mechanical punch reach.
- Polygon order may be clockwise or counterclockwise. Neither algorithm requires
  a specific orientation. The execution invariant works for any duplicate-free
  pair or triple list; the final theorems construct consecutive boundary groups.
- A short stack may physically yield fewer than k hits, but `SuccessfulPunch`
  excludes it when proving an exactly-k operation.
- `Fold.creaseOn` models a single fold of an initially flat sheet: take the axis
  through the sheet's interior, then close this set to include the endpoints.
  A tangential boundary contact alone contributes no crease. The proof shows this
  set is the entire nondegenerate chord for the pair fold. This is the chosen
  geometric crease model, not a differentiability or 3D mechanics theorem.
- Earlier punches remove only boundary points, so they do not change the sheet's
  interior. The later crease is therefore exactly the same full chord as before.
- Cumulative cost is genuinely geometric: repeated chords are deduplicated, and
  maximality inside the same polygon proves that crossing chords are not split.
  We do not charge repeated use of an existing crease as a new crease.
- `Fold.secondCreases` models the second fold while paper is still stacked.
  It closes the trace on each strict side of the first hinge, using reflection
  on the moving piece. Tangencies create no segment; folding only along the
  old hinge creates no new crease. Endpoints are retained through closure.
- `Fold.secondCreases_eq_configuration_trace` connects this definition to the
  actual folded configuration. `Fold.twoFoldCreases_eq_history` connects the
  total trace to the existing cumulative history. The bounds use the original
  maximal-segment counting definition, not a count of folding operations.
- These two-fold bounds hold for arbitrary fold lines and either placement.
  `Triple.lean` supplies the concrete second fold and its successful punch.
  The chosen vertices are the first three layers from the punching side;
  merely being consecutive somewhere inside a stack is not sufficient.
- The first fold is an overfold; the second may be over or under. Its moving
  half always contains the pair, and its target is the third vertex's position
  after the first fold. That location is proved distinct from the pair location.
  The double point retains both original layer labels throughout the proof.

## Scope of the completed results

Both algorithms now have complete safety, coverage, and cumulative-crease proofs
under the stated idealized model and divisibility conditions. The explicit bounds
prove O(n) without requiring separate asymptotic notation. They do not establish
minimum possible crease counts; optimality remains a separate question.

## Build

With Lean's `elan` toolchain manager installed, run these commands in the project directory:

```sh
lake exe cache get
lake build
```

The committed `lean-toolchain` and `lake-manifest.json` pin the toolchain and
dependencies. Lake fetches the dependencies and their compiled Mathlib cache;
the generated `.lake/` directory is excluded from version control.
