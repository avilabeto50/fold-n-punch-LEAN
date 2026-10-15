import FoldAndPunch.CreaseUnions

/-!
# At most three creases for two successive folds

The first hinge divides the original interior into two convex open patches.
The second crease pulls back to a line on each patch: the second axis itself
on the stationary patch, and its reflection on the moving patch. Each trace
is empty or one segment. Their union contributes at most two creases.

The trace is proved equal to the existing configuration hinge trace restricted
to interior material away from the old hinge. Adding the first crease gives
at most three maximal segments. This is the crease bound needed for a triple;
the separate depth-three punch and stack-order argument is not proved here.
-/

noncomputable section
open Set
open scoped Topology
namespace FoldAndPunch

/-- The strict moving side is a convex half-plane. -/
theorem Fold.moving_convex (f : Fold) : Convex ℝ {x | f.moving x} := by
  have halfplane : {x | f.moving x} =
      {x | inner ℝ x (f.target - f.source) < (‖f.target‖ ^ 2 - ‖f.source‖ ^ 2) / 2} := by
    ext x
    change dist x f.source < dist x f.target ↔
      inner ℝ x (f.target - f.source) < (‖f.target‖ ^ 2 - ‖f.source‖ ^ 2) / 2
    rw [← sq_lt_sq₀ dist_nonneg dist_nonneg, dist_eq_norm, dist_eq_norm,
      norm_sub_sq_real, norm_sub_sq_real, inner_sub_right]
    constructor <;> intro h <;> linarith
  rw [halfplane]
  apply convex_halfSpace_lt
  exact ⟨fun x y => inner_add_left _ _ _, fun r x => real_inner_smul_left _ _ _⟩

/-- The strict stationary side is also a convex half-plane. -/
theorem Fold.stationary_convex (f : Fold) :
    Convex ℝ {x | dist x f.target < dist x f.source} := by
  let reverse : Fold := ⟨f.target, f.source, f.distinct.symm, f.placement⟩
  exact reverse.moving_convex

/-- Reflect the second fold line back into the original sheet. -/
def Fold.pullback (f g : Fold) : Fold where
  source := f.reflect g.source
  target := f.reflect g.target
  distinct := fun h => g.distinct (f.reflect.injective h)
  placement := g.placement

theorem Fold.mem_pullback_axis (f g : Fold) (x : Point) :
    x ∈ (f.pullback g).axis ↔ f.reflect x ∈ g.axis := by
  rw [(f.pullback g).on_axis_iff, g.on_axis_iff]
  have distance (y : Point) : dist x (f.reflect y) = dist (f.reflect x) y := by
    have same := f.reflect.dist_map x (f.reflect y)
    rw [f.reflect_reflect] at same
    exact same.symm
  change dist x (f.reflect g.source) = dist x (f.reflect g.target) ↔ _
  rw [distance, distance]

/-- An open patch meeting a line contains more than one point of that line. -/
theorem Fold.open_section_nontrivial (f : Fold) {patch : Set Point}
    (patchOpen : IsOpen patch) (meets : (patch ∩ (f.axis : Set Point)).Nonempty) :
    (patch ∩ (f.axis : Set Point)).Nontrivial := by
  obtain ⟨q, hqPatch, hqAxis⟩ := meets
  let : Nontrivial f.axis.direction :=
    Module.nontrivial_of_finrank_eq_succ f.axis_dimension
  obtain ⟨v, nonzero⟩ := exists_ne (0 : f.axis.direction)
  have vectorNonzero : (v : Point) ≠ 0 := by
    intro zero
    exact nonzero (Subtype.ext zero)
  let path : ℝ → Point := fun t => t • (v : Point) + q
  have pathContinuous : Continuous path :=
    (continuous_id.smul continuous_const).add continuous_const
  have nearZero : {t | path t ∈ patch} ∈ 𝓝 (0 : ℝ) := by
    apply pathContinuous.continuousAt.preimage_mem_nhds
    apply patchOpen.mem_nhds
    simpa [path] using hqPatch
  obtain ⟨t, ht, tNonzero⟩ :=
    (infinite_of_mem_nhds (0 : ℝ) nearZero).nontrivial.exists_ne 0
  have otherOnAxis : path t ∈ f.axis :=
    f.axis.vadd_mem_of_mem_direction (f.axis.direction.smul_mem t v.property) hqAxis
  have different : path t ≠ q := by
    intro equal
    have zero : t • (v : Point) = 0 := by
      apply add_right_cancel (b := q)
      simpa [path] using equal
    rcases smul_eq_zero.mp zero with scalarZero | vectorZero
    · exact tNonzero scalarZero
    · exact vectorNonzero vectorZero
  exact ⟨q, ⟨hqPatch, hqAxis⟩, path t, ⟨ht, otherOnAxis⟩, different.symm⟩

/-- On a convex open piece of a bounded polygon, a straight fold produces
no segment or exactly one segment, including its endpoints. -/
theorem Paper.open_patch_crease {n : ℕ} (P : Paper n) (f : Fold) {patch : Set Point}
    (patchOpen : IsOpen patch) (patchConvex : Convex ℝ patch) (inside : patch ⊆ P.region) :
    closure (patch ∩ (f.axis : Set Point)) = ∅ ∨
      IsCreaseSegment (closure (patch ∩ (f.axis : Set Point))) := by
  by_cases meets : (patch ∩ (f.axis : Set Point)).Nonempty
  · right
    apply compact_convex_collinear_segment
    · apply P.region_compact.of_isClosed_subset isClosed_closure
      exact closure_minimal (Set.inter_subset_left.trans inside) P.region_compact.isClosed
    · exact (patchConvex.inter f.axis.convex).closure
    · apply f.axis_collinear.subset
      exact closure_minimal Set.inter_subset_right f.axis_closed
    · exact (f.open_section_nontrivial patchOpen meets).mono subset_closure
  · left
    rw [Set.not_nonempty_iff_eq_empty.mp meets, closure_empty]

/-- The first fold splits the interior into a stationary piece and a moving
piece. The old hinge itself is excluded: folding there again adds no crease. -/
def Fold.stationaryPatch (f : Fold) (sheet : Set Point) : Set Point :=
  interior sheet ∩ {x | dist x f.target < dist x f.source}

def Fold.movingPatch (f : Fold) (sheet : Set Point) : Set Point :=
  interior sheet ∩ {x | f.moving x}

/-- The second-fold crease on the stationary piece, in original coordinates. -/
def Fold.secondStationaryCrease (f g : Fold) (sheet : Set Point) : Set Point :=
  closure (f.stationaryPatch sheet ∩ (g.axis : Set Point))

/-- The second-fold crease on the reflected piece, pulled back to the original
sheet. Reflection turns the second fold line into another straight line. -/
def Fold.secondMovingCrease (f g : Fold) (sheet : Set Point) : Set Point :=
  closure (f.movingPatch sheet ∩ ((f.pullback g).axis : Set Point))

/-- All crease contributions of the second fold, on the original sheet. -/
def Fold.secondCreases (f g : Fold) (sheet : Set Point) : Set Point :=
  f.secondStationaryCrease g sheet ∪ f.secondMovingCrease g sheet

/-- The accumulated trace of the two successive folds. -/
def Fold.twoFoldCreases (f g : Fold) (sheet : Set Point) : Set Point :=
  f.creaseOn sheet ∪ f.secondCreases g sheet

/-- The geometric definition agrees with the existing piecewise fold map.
Away from the old hinge, it is exactly the original interior material that
lands on the second fold axis. Closure restores segment endpoints. -/
theorem Fold.secondCreases_eq_position_trace (f g : Fold) (sheet : Set Point) :
    f.secondCreases g sheet =
      closure {x | x ∈ interior sheet ∧ x ∉ f.axis ∧ f.pointMap x ∈ g.axis} := by
  unfold secondCreases secondStationaryCrease secondMovingCrease
  rw [← closure_union]
  congr 1
  ext x
  simp only [mem_union, mem_inter_iff, stationaryPatch, movingPatch, mem_ofPred_eq]
  constructor
  · rintro (⟨⟨hx, stationary⟩, onSecond⟩ | ⟨⟨hx, moving⟩, onSecond⟩)
    · have offFirst : x ∉ f.axis := by
        rw [f.on_axis_iff]
        exact ne_of_gt stationary
      have notMoving : ¬ f.moving x := not_lt.mpr (le_of_lt stationary)
      exact ⟨hx, offFirst, by simpa [Fold.pointMap, notMoving] using onSecond⟩
    · have offFirst : x ∉ f.axis := by
        rw [f.on_axis_iff]
        exact ne_of_lt moving
      have reflectedOnSecond := (f.mem_pullback_axis g x).mp onSecond
      exact ⟨hx, offFirst, by simpa [Fold.pointMap, moving] using reflectedOnSecond⟩
  · rintro ⟨hx, offFirst, onSecond⟩
    by_cases moving : f.moving x
    · right
      refine ⟨⟨hx, moving⟩, (f.mem_pullback_axis g x).mpr ?_⟩
      simpa [Fold.pointMap, moving] using onSecond
    · left
      have stationary : dist x f.target < dist x f.source := by
        have unequal : dist x f.source ≠ dist x f.target := (f.on_axis_iff x).not.mp offFirst
        exact lt_of_le_of_ne (not_lt.mp moving) (Ne.symm unequal)
      exact ⟨⟨hx, stationary⟩, by simpa [Fold.pointMap, moving] using onSecond⟩

/-- In configuration language, the same trace is obtained by folding the flat
sheet once and looking at the second hinge, away from the old hinge. -/
theorem Fold.secondCreases_eq_configuration_trace (f g : Fold) (sheet : Set Point) :
    f.secondCreases g sheet =
      closure {x | x ∈ interior sheet ∧ x ∉ f.axis ∧
        x ∈ ((flatConfiguration sheet).fold f).hingeTrace g} := by
  rw [f.secondCreases_eq_position_trace]
  congr 1
  ext x
  change (x ∈ interior sheet ∧ x ∉ f.axis ∧ f.pointMap x ∈ g.axis) ↔
    (x ∈ interior sheet ∧ x ∉ f.axis ∧ x ∈ sheet ∧ f.pointMap x ∈ g.axis)
  constructor
  · rintro ⟨hx, offFirst, onSecond⟩
    exact ⟨hx, offFirst, interior_subset hx, onSecond⟩
  · rintro ⟨hx, offFirst, _, onSecond⟩
    exact ⟨hx, offFirst, onSecond⟩

/-- This is the cumulative crease history already used by the project. -/
theorem Fold.twoFoldCreases_eq_history (f g : Fold) (sheet : Set Point) :
    f.twoFoldCreases g sheet =
      cumulativeCreases [f.creaseOn sheet, f.secondCreases g sheet] := by
  have closedFirst : IsClosed (f.creaseOn sheet) := isClosed_closure
  have closedSecond : IsClosed (f.secondCreases g sheet) :=
    isClosed_closure.union isClosed_closure
  have historyUnion : {x | ∃ trace ∈ [f.creaseOn sheet, f.secondCreases g sheet], x ∈ trace} =
      f.creaseOn sheet ∪ f.secondCreases g sheet := by
    ext x
    simp
  unfold cumulativeCreases
  rw [historyUnion, (closedFirst.union closedSecond).closure_eq]
  rfl

/-- Each of the two material pieces contributes at most one crease. -/
theorem Paper.second_fold_pieces {n : ℕ} (P : Paper n) (f g : Fold) :
    (f.secondStationaryCrease g P.region = ∅ ∨ IsCreaseSegment (f.secondStationaryCrease g P.region)) ∧
    (f.secondMovingCrease g P.region = ∅ ∨ IsCreaseSegment (f.secondMovingCrease g P.region)) := by
  constructor
  · apply P.open_patch_crease g
    · exact isOpen_interior.inter
        (isOpen_lt (continuous_id.dist continuous_const) (continuous_id.dist continuous_const))
    · exact (convex_convexHull ℝ _).interior.inter f.stationary_convex
    · exact Set.inter_subset_left.trans interior_subset
  · apply P.open_patch_crease (f.pullback g)
    · exact isOpen_interior.inter
        (isOpen_lt (continuous_id.dist continuous_const) (continuous_id.dist continuous_const))
    · exact (convex_convexHull ℝ _).interior.inter f.moving_convex
    · exact Set.inter_subset_left.trans interior_subset

/-- The second all-layer fold adds at most two crease segments. -/
theorem Paper.second_fold_atMost_two_creases {n : ℕ} (P : Paper n) (f g : Fold) :
    HasAtMostCreases (f.secondCreases g P.region) 2 := by
  have one {s : Set Point} (shape : s = ∅ ∨ IsCreaseSegment s) : HasAtMostCreases s 1 := by
    rcases shape with empty | straight
    · rw [empty]
      exact empty_hasAtMostCreases 1
    · exact straight.hasAtMostOne
  obtain ⟨stationary, moving⟩ := P.second_fold_pieces f g
  exact (one stationary).union (one moving)

/-- One crease from the first fold plus at most two from the second: at most
three maximal straight crease segments on the original sheet. -/
theorem Paper.two_folds_atMost_three_creases {n : ℕ} (P : Paper n) (f g : Fold) :
    HasAtMostCreases (f.twoFoldCreases g P.region) 3 := by
  have first : HasAtMostCreases (f.creaseOn P.region) 1 := by
    have shape := P.open_patch_crease f isOpen_interior
      (convex_convexHull ℝ _).interior interior_subset
    rcases shape with empty | straight
    · change HasAtMostCreases (closure (interior P.region ∩ (f.axis : Set Point))) 1
      change closure (interior P.region ∩ (f.axis : Set Point)) = ∅ at empty
      rw [empty]
      exact empty_hasAtMostCreases 1
    · exact straight.hasAtMostOne
  have second := P.second_fold_atMost_two_creases f g
  exact first.union second

/-- In particular, reuse the proved one-crease pair fold as the first step of
a triple operation. Any second fold still leaves at most three creases. -/
theorem Paper.pair_then_fold_atMost_three_creases {n : ℕ} (P : Paper n)
    (i j : Fin n) (distinct : i ≠ j) (placement : Side) (second : Fold) :
    HasAtMostCreases ((P.pairFold i j distinct placement).twoFoldCreases second P.region) 3 := by
  have first := P.pairFold_one_crease i j distinct placement
  have next := P.second_fold_atMost_two_creases (P.pairFold i j distinct placement) second
  exact first.union next

end FoldAndPunch
