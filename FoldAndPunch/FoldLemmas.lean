import FoldAndPunch.Geometry

/-! Perpendicular-bisector reflection and geometric preimages of a fold. -/

noncomputable section
namespace FoldAndPunch

namespace Fold

instance axis_nonempty (f : Fold) : Nonempty f.axis :=
  AffineSubspace.perpBisector_nonempty.to_subtype

/-- Applying the reflection twice restores the original location. -/
theorem reflect_reflect (f : Fold) (x : Point) : f.reflect (f.reflect x) = x := by
  exact EuclideanGeometry.reflection_reflection f.axis x

/-- The perpendicular-bisector reflection sends the target to the source. -/
theorem reflect_target (f : Fold) : f.reflect f.target = f.source := by
  -- Use the midpoint as the origin for Mathlib's affine reflection.
  rw [reflect, EuclideanGeometry.reflection_apply_of_mem f.axis f.target
    (AffineSubspace.midpoint_mem_perpBisector f.source f.target)]
  -- The vector from the midpoint to the target is normal to the bisector.
  rw [axis, AffineSubspace.direction_perpBisector, right_vsub_midpoint,
    map_smul, Submodule.reflection_orthogonalComplement_singleton_eq_neg]
  -- Negating that vector lands at the source.
  rw [neg_vsub_eq_vsub_rev, ← left_vsub_midpoint, vsub_vadd]

/-- Reflection also sends the source to the target. -/
theorem reflect_source (f : Fold) : f.reflect f.source = f.target := by
  rw [← f.reflect_target, f.reflect_reflect]

theorem moving_source (f : Fold) : f.moving f.source := by
  simp [moving, f.distinct]

theorem not_moving_target (f : Fold) : ¬ f.moving f.target := by
  simp [moving]

theorem target_not_on_axis (f : Fold) : f.target ∉ f.axis := by
  simp [axis, f.distinct]

/-- The axis consists exactly of the equidistant locations. -/
theorem on_axis_iff (f : Fold) (q : Point) :
    q ∈ f.axis ↔ dist q f.source = dist q f.target := by
  exact AffineSubspace.mem_perpBisector_iff_dist_eq

theorem reflect_fixed_iff (f : Fold) (q : Point) : f.reflect q = q ↔ q ∈ f.axis := by
  exact EuclideanGeometry.reflection_eq_self_iff q

/-- Reflection swaps the distances to the two defining points. -/
theorem dist_reflect_source (f : Fold) (q : Point) :
    dist (f.reflect q) f.source = dist q f.target := by
  rw [← f.reflect_target]
  exact f.reflect.dist_map q f.target

theorem dist_reflect_target (f : Fold) (q : Point) :
    dist (f.reflect q) f.target = dist q f.source := by
  rw [← f.reflect_source]
  exact f.reflect.dist_map q f.source

/-- No folded point lies strictly in the half-plane that has been moved away. -/
theorem pointMap_not_moving (f : Fold) (x : Point) : ¬ f.moving (f.pointMap x) := by
  by_cases moving : f.moving x
  · rw [pointMap, ite_eq_left moving]
    unfold Fold.moving at *
    rw [f.dist_reflect_source, f.dist_reflect_target]
    exact not_lt_of_ge (le_of_lt moving)
  · rw [pointMap, ite_eq_right moving]
    exact moving

/-- Axis locations have only themselves as geometric preimages. -/
theorem pointMap_eq_on_axis (f : Fold) {q x : Point} (onAxis : q ∈ f.axis) :
    f.pointMap x = q ↔ x = q := by
  have fixed : f.reflect q = q := (f.reflect_fixed_iff q).2 onAxis
  by_cases moving : f.moving x
  · rw [pointMap, ite_eq_left moving]
    constructor
    · intro reflected
      have undo := congrArg f.reflect reflected
      simpa only [f.reflect_reflect, fixed] using undo
    · intro same
      rw [same, fixed]
  · rw [pointMap, ite_eq_right moving]

/-- Away from the axis, a location on the stationary side has precisely two
geometric preimages in the plane: itself and its reflection. Material membership
will later decide whether both are actual paper points. -/
theorem pointMap_eq_off_axis (f : Fold) {q x : Point}
    (stationary : ¬ f.moving q) (offAxis : q ∉ f.axis) :
    f.pointMap x = q ↔ x = q ∨ x = f.reflect q := by
  have strict : dist q f.target < dist q f.source := by
    have weak : dist q f.target ≤ dist q f.source := le_of_not_gt stationary
    have unequal : dist q f.source ≠ dist q f.target := by
      intro equal
      exact offAxis ((f.on_axis_iff q).2 equal)
    exact lt_of_le_of_ne weak (Ne.symm unequal)
  have reflectionMoves : f.moving (f.reflect q) := by
    unfold Fold.moving
    rw [f.dist_reflect_source, f.dist_reflect_target]
    exact strict
  constructor
  · intro mapped
    by_cases moving : f.moving x
    · right
      rw [pointMap, ite_eq_left moving] at mapped
      have undo := congrArg f.reflect mapped
      simpa only [f.reflect_reflect] using undo
    · left
      simpa only [pointMap, ite_eq_right moving] using mapped
  · intro preimage
    rcases preimage with same | reflected
    · rw [same, pointMap, ite_eq_right stationary]
    · rw [reflected, pointMap, ite_eq_left reflectionMoves, f.reflect_reflect]

end Fold

end FoldAndPunch
