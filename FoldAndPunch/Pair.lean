import FoldAndPunch.Punching
import FoldAndPunch.ConfigurationLemmas

/-!
# A pair is ready to punch after one bisector fold

Read `flat_fold_stack_at_target` for the explicit two-point stack, then
`Paper.pair_ready_to_punch` for the complete first-batch statement.
`Paper.pairFold_successful` also permits holes from earlier batches.
Crease counts and batch iteration are proved separately in PairCreases and K2.
-/

noncomputable section
namespace FoldAndPunch

/-- A surviving source/target pair forms exactly a two-point stack.
The statement permits existing holes elsewhere in the unfolded sheet. -/
theorem flat_fold_stack_at_target (material : Set Point) (f : Fold)
    (sourcePresent : f.source ∈ material) (targetPresent : f.target ∈ material) :
    ((flatConfiguration material).fold f).stack f.target =
      match f.placement with
      | .top => [f.source, f.target]
      | .bottom => [f.target, f.source] := by
  -- The target is off the axis on the stationary side; its reflected preimage
  -- is exactly the source. Each of these locations starts with one layer.
  cases placement : f.placement <;>
    simp [Configuration.fold, f.not_moving_target, f.target_not_on_axis,
      f.reflect_target, flatConfiguration, sourcePresent, targetPresent,
      placeStack, placement]

/-- Punching from the side where the pair was placed hits source, then target. -/
theorem flat_fold_pair_hits (material : Set Point) (f : Fold)
    (sourcePresent : f.source ∈ material) (targetPresent : f.target ∈ material) :
    ((flatConfiguration material).fold f).punchHits 2 f.placement f.target =
      [f.source, f.target] := by
  have stack := flat_fold_stack_at_target material f sourcePresent targetPresent
  cases placement : f.placement <;>
    simp [Configuration.punchHits, Configuration.layersFrom, stack, placement]


/-- The prescribed bisector fold for two distinct polygon vertices. -/
def Paper.pairFold {n : ℕ} (P : Paper n) (i j : Fin n)
    (distinct : i ≠ j) (placement : Side) : Fold where
  source := P.polygon.vertices i
  target := P.polygon.vertices j
  distinct := P.vertices_injective.ne distinct
  placement := placement

/-- Two fresh vertices on any unfolded remaining material are ready for an
exactly-two punch after their bisector fold. Holes elsewhere are allowed. -/
theorem Paper.pairFold_successful {n : ℕ} (P : Paper n) (material : Set Point)
    (inside : material ⊆ P.region) (i j : Fin n) (distinct : i ≠ j)
    (sourcePresent : P.polygon.vertices i ∈ material)
    (targetPresent : P.polygon.vertices j ∈ material) (placement : Side) :
    SuccessfulPunch P
      ((flatConfiguration material).fold (P.pairFold i j distinct placement))
      2 {i, j} placement (P.polygon.vertices j) := by
  classical
  let f := P.pairFold i j distinct placement
  have hits : ((flatConfiguration material).fold f).punchHits 2 f.placement f.target =
      [f.source, f.target] := by
    apply flat_fold_pair_hits
    · exact sourcePresent
    · exact targetPresent
  change SuccessfulPunch P ((flatConfiguration material).fold f)
    2 {i, j} f.placement f.target
  unfold SuccessfulPunch
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_⟩
  · -- The computed stacks describe precisely the folded surviving sheet.
    apply Configuration.fold_wellFormed
    apply flatConfiguration_wellFormed
    exact inside
  · -- Distinct vertex indices give a batch of size two.
    simp [distinct]
  · -- Neither target has already been punched out.
    intro index member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with first | second
    · subst index
      exact sourcePresent
    · subst index
      exact targetPresent
  · -- The punch encounters exactly two layers.
    rw [hits]
    rfl
  · -- Those layers are exactly the selected vertices, with no unmarked point.
    intro x
    rw [hits]
    simp [f, Paper.pairFold]

/-- First-batch version: any two distinct vertices of the original polygon
can be stacked and punched by the prescribed single bisector fold. -/
theorem Paper.pair_ready_to_punch {n : ℕ} (P : Paper n) (i j : Fin n)
    (distinct : i ≠ j) (placement : Side) :
    SuccessfulPunch P (P.initial.fold (P.pairFold i j distinct placement))
      2 {i, j} placement (P.polygon.vertices j) := by
  apply P.pairFold_successful P.region Set.Subset.rfl
  · -- Every vertex belongs to the convex hull defining the sheet.
    apply subset_convexHull ℝ
    exact ⟨i, rfl⟩
  · apply subset_convexHull ℝ
    exact ⟨j, rfl⟩

end FoldAndPunch
