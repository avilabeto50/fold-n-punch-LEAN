import FoldAndPunch.PairCreases

/-!
Punching removes exactly its selected original points. Unfolding retains holes.
Marked points are boundary points, so earlier punches leave all crease traces unchanged.
-/

noncomputable section
open Set
namespace FoldAndPunch

/-- Every marked point is on the boundary, not in the interior. -/
theorem Paper.marked_not_interior {n : ℕ} (P : Paper n) {x : Point}
    (marked : x ∈ P.marked) : x ∉ interior P.region := by
  obtain ⟨i, rfl⟩ := marked
  have boundary : P.polygon.vertices i ∈ P.polygon.boundary ℝ := by
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    exact left_mem_affineSegment ℝ _ _
  rw [P.boundary_order] at boundary
  exact boundary.2

/-- Removing any collection of marked vertices leaves the interior unchanged. -/
theorem Paper.interior_remove_marked {n : ℕ} (P : Paper n) (holes : Set Point)
    (onlyMarked : holes ⊆ P.marked) :
    interior (P.region \ holes) = interior P.region := by
  apply Set.Subset.antisymm
  · exact interior_mono Set.sdiff_subset
  · apply interior_maximal _ isOpen_interior
    intro x inside
    refine ⟨interior_subset inside, ?_⟩
    intro removed
    exact P.marked_not_interior (onlyMarked removed) inside

/-- Earlier point punches at vertices do not change any subsequent flat-fold
crease trace. This follows from equality of interiors, not a cost assumption. -/
theorem Paper.creaseOn_remove_marked {n : ℕ} (P : Paper n) (holes : Set Point)
    (onlyMarked : holes ⊆ P.marked) (f : Fold) :
    f.creaseOn (P.region \ holes) = f.creaseOn P.region := by
  unfold Fold.creaseOn
  rw [P.interior_remove_marked holes onlyMarked]

/-- Punching a known pair and unfolding removes exactly that pair. -/
theorem flat_pair_punch_unfold (material : Set Point) (f : Fold)
    (sourcePresent : f.source ∈ material) (targetPresent : f.target ∈ material) :
    (((flatConfiguration material).fold f).punch 2 f.placement f.target).unfold =
      flatConfiguration (material \ {f.source, f.target}) := by
  have hits := flat_fold_pair_hits material f sourcePresent targetPresent
  unfold Configuration.unfold
  apply congrArg flatConfiguration
  ext x
  change (x ∈ material ∧ x ∉ ((flatConfiguration material).fold f).punchHits
    2 f.placement f.target) ↔ x ∈ material \ {f.source, f.target}
  rw [hits]
  simp

/-- Point punches preserve the stack/location consistency condition. -/
theorem Configuration.punch_wellFormed {n : ℕ} {P : Paper n} {C : Configuration}
    (consistent : C.WellFormed P) (k : ℕ) (side : Side) (q : Point) :
    (C.punch k side q).WellFormed P := by
  classical
  obtain ⟨inside, nodup, membership⟩ := consistent
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact inside hx.1
  · intro y
    exact (nodup y).filter _
  · intro y x
    simp [Configuration.punch, membership, and_left_comm, and_comm]

theorem Configuration.unfold_wellFormed {n : ℕ} {P : Paper n} {C : Configuration}
    (consistent : C.WellFormed P) : C.unfold.WellFormed P := by
  apply flatConfiguration_wellFormed
  exact consistent.1

end FoldAndPunch
