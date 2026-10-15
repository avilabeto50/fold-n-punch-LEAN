import FoldAndPunch.Pair
import FoldAndPunch.CreaseLemmas

/-!
# One crease for the pair fold

The existing safe-punch result and this geometric crease bound refer to the
same fold. The result applies to the initially flat, uncreased polygon.
Crease reuse and total costs across batches are handled in PairCreaseCount and K2.
-/

noncomputable section
namespace FoldAndPunch

/-- The pair fold from the punch theorem creates at most one crease. -/
theorem Paper.pairFold_one_crease {n : ℕ} (P : Paper n) (i j : Fin n)
    (distinct : i ≠ j) (placement : Side) :
    HasAtMostCreases ((P.pairFold i j distinct placement).creaseOn P.region) 1 := by
  apply IsCreaseSegment.hasAtMostOne
  apply P.single_fold_isCreaseSegment
  · apply subset_convexHull ℝ
    exact ⟨i, rfl⟩
  · apply subset_convexHull ℝ
    exact ⟨j, rfl⟩

/-- The same fold is safe to punch and has exactly one crease in the
initially flat, uncreased-sheet model (at most one, and not zero). -/
theorem Paper.pair_ready_to_punch_with_one_crease {n : ℕ} (P : Paper n)
    (i j : Fin n) (distinct : i ≠ j) (placement : Side) :
    SuccessfulPunch P (P.initial.fold (P.pairFold i j distinct placement))
      2 {i, j} placement (P.polygon.vertices j) ∧
    HasAtMostCreases ((P.pairFold i j distinct placement).creaseOn P.region) 1 ∧
    ¬ HasAtMostCreases ((P.pairFold i j distinct placement).creaseOn P.region) 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact P.pair_ready_to_punch i j distinct placement
  · exact P.pairFold_one_crease i j distinct placement
  · apply IsCreaseSegment.not_zero_creases
    apply P.single_fold_isCreaseSegment
    · apply subset_convexHull ℝ
      exact ⟨i, rfl⟩
    · apply subset_convexHull ℝ
      exact ⟨j, rfl⟩

end FoldAndPunch
