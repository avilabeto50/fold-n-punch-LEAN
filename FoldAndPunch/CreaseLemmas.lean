import FoldAndPunch.Creases
import FoldAndPunch.FoldLemmas
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact

/-!
# A transverse line cuts a convex polygon in one crease segment

First identify a compact convex collinear set with its endpoint segment.
Then prove that the bisector of two sheet points crosses the interior, so its
crease is a nondegenerate chord. Finally construct the one-segment decomposition.
-/

noncomputable section
open Set
open scoped Topology
namespace FoldAndPunch

/-- A nontrivial compact convex set contained in a line is one segment. -/
theorem compact_convex_collinear_segment {s : Set Point}
    (compact : IsCompact s) (convex : Convex ℝ s) (collinear : Collinear ℝ s)
    (nontrivial : s.Nontrivial) : IsCreaseSegment s := by
  -- Pick two points with maximum distance in this compact set.
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, farthest⟩ :=
    (compact.prod compact).exists_isMaxOn
      (nontrivial.nonempty.prod nontrivial.nonempty) (f := fun p : Point × Point => dist p.1 p.2) continuous_dist.continuousOn
  have distinct : a ≠ b := by
    intro equal
    obtain ⟨u, hu, v, hv, different⟩ := nontrivial
    have bound : dist u v ≤ dist a b := (isMaxOn_iff.mp farthest) (u, v) ⟨hu, hv⟩
    rw [equal, dist_self] at bound
    exact different (dist_le_zero.mp bound)
  refine ⟨a, b, distinct, ?_⟩
  apply Set.Subset.antisymm
  · intro x hx
    have triple : Collinear ℝ ({a, x, b} : Set Point) := by
      apply collinear.subset
      intro y member
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at member
      rcases member with rfl | rfl | rfl
      · exact ha
      · exact hx
      · exact hb
    rcases triple.wbtw_or_wbtw_or_wbtw with between | beyondB | beyondA
    · exact mem_segment_iff_wbtw.mpr between
    · have distanceSum := beyondB.dist_add_dist
      have bound : dist x a ≤ dist a b := (isMaxOn_iff.mp farthest) (x, a) ⟨hx, ha⟩
      have same : x = b := by
        apply dist_le_zero.mp
        rw [dist_comm b a] at distanceSum
        linarith
      rw [same]
      exact right_mem_segment ℝ a b
    · have distanceSum := beyondA.dist_add_dist
      have bound : dist b x ≤ dist a b := (isMaxOn_iff.mp farthest) (b, x) ⟨hb, hx⟩
      have same : x = a := by
        apply dist_le_zero.mp
        rw [dist_comm b a, dist_comm a x] at distanceSum
        linarith
      rw [same]
      exact left_mem_segment ℝ a b
  · exact convex.segment_subset ha hb

/-- The filled polygon is compact. -/
theorem Paper.region_compact {n : ℕ} (P : Paper n) : IsCompact P.region := by
  exact (Set.finite_range P.polygon.vertices).isCompact_convexHull ℝ

theorem Fold.axis_closed (f : Fold) : IsClosed (f.axis : Set Point) := by
  have description : (f.axis : Set Point) = {q | dist q f.source = dist q f.target} := by
    ext q
    exact f.on_axis_iff q
  rw [description]
  exact isClosed_eq (continuous_id.dist continuous_const) (continuous_id.dist continuous_const)

theorem Fold.axis_dimension (f : Fold) : Module.finrank ℝ f.axis.direction = 1 := by
  rw [Fold.axis, AffineSubspace.direction_perpBisector]
  let : Fact (Module.finrank ℝ Point = 1 + 1) := ⟨by simp [Point]⟩
  apply Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) (E := Point) (n := 1)
  exact vsub_ne_zero.mpr f.distinct.symm

theorem Fold.axis_collinear (f : Fold) : Collinear ℝ (f.axis : Set Point) := by
  apply collinear_iff_finrank_le_one.mpr
  rw [← AffineSubspace.direction_eq_vectorSpan, f.axis_dimension]

/-- A bisector with its two defining points in the polygon meets the interior. -/
theorem Paper.axis_meets_interior {n : ℕ} (P : Paper n) (f : Fold)
    (sourceInside : f.source ∈ P.region) (targetInside : f.target ∈ P.region) :
    (interior P.region ∩ (f.axis : Set Point)).Nonempty := by
  have convex : Convex ℝ P.region := convex_convexHull ℝ _
  have denseInterior : closure (interior P.region) = P.region := by
    rw [convex.closure_interior_eq_closure_of_nonempty_interior P.interior_nonempty]
    exact P.region_compact.isClosed.closure_eq
  -- Each defining vertex has nearby interior points on its own strict side.
  have sourceClosure : f.source ∈ closure (interior P.region) := by
    rw [denseInterior]
    exact sourceInside
  have targetClosure : f.target ∈ closure (interior P.region) := by
    rw [denseInterior]
    exact targetInside
  have movingOpen : IsOpen {q : Point | dist q f.source < dist q f.target} :=
    isOpen_lt (continuous_id.dist continuous_const) (continuous_id.dist continuous_const)
  have receivingOpen : IsOpen {q : Point | dist q f.target < dist q f.source} :=
    isOpen_lt (continuous_id.dist continuous_const) (continuous_id.dist continuous_const)
  obtain ⟨a, haSide, haInterior⟩ :=
    (mem_closure_iff.1 sourceClosure) _ movingOpen f.moving_source
  have targetStrict : dist f.target f.target < dist f.target f.source := by
    simp [f.distinct.symm]
  obtain ⟨b, hbSide, hbInterior⟩ :=
    (mem_closure_iff.1 targetClosure) _ receivingOpen targetStrict
  -- The interior is convex, so the two distance functions agree somewhere in it.
  obtain ⟨q, hqInterior, equidistant⟩ := convex.interior.isPreconnected.intermediate_value₂
    haInterior hbInterior
    (continuous_id.dist continuous_const).continuousOn
    (continuous_id.dist continuous_const).continuousOn
    (le_of_lt haSide) (le_of_lt hbSide)
  exact ⟨q, hqInterior, (f.on_axis_iff q).2 equidistant⟩


/-- An axis through an interior point contains a genuine interval of paper,
not just one touching point. -/
theorem Paper.axis_section_nontrivial {n : ℕ} (P : Paper n) (f : Fold)
    (meetsInterior : (interior P.region ∩ (f.axis : Set Point)).Nonempty) :
    (P.region ∩ (f.axis : Set Point)).Nontrivial := by
  obtain ⟨q, hqInterior, hqAxis⟩ := meetsInterior
  let : Nontrivial f.axis.direction :=
    Module.nontrivial_of_finrank_eq_succ f.axis_dimension
  obtain ⟨v, nonzero⟩ := exists_ne (0 : f.axis.direction)
  have vectorNonzero : (v : Point) ≠ 0 := by
    intro zero
    apply nonzero
    exact Subtype.ext zero
  -- Move a small nonzero distance along the direction of the fold line.
  let path : ℝ → Point := fun t => t • (v : Point) + q
  have pathContinuous : Continuous path :=
    (continuous_id.smul continuous_const).add continuous_const
  have nearZero : {t | path t ∈ interior P.region} ∈ 𝓝 (0 : ℝ) := by
    apply pathContinuous.continuousAt.preimage_mem_nhds
    apply isOpen_interior.mem_nhds
    simpa [path] using hqInterior
  obtain ⟨t, ht, tNonzero⟩ :=
    (infinite_of_mem_nhds (0 : ℝ) nearZero).nontrivial.exists_ne 0
  have otherOnAxis : path t ∈ f.axis := by
    exact f.axis.vadd_mem_of_mem_direction (f.axis.direction.smul_mem t v.property) hqAxis
  have different : path t ≠ q := by
    intro equal
    have zero : t • (v : Point) = 0 := by
      apply add_right_cancel (b := q)
      simpa [path] using equal
    rcases smul_eq_zero.mp zero with scalarZero | vectorZero
    · exact tNonzero scalarZero
    · exact vectorNonzero vectorZero
  exact ⟨q, ⟨interior_subset hqInterior, hqAxis⟩,
    path t, ⟨interior_subset ht, otherOnAxis⟩, different.symm⟩

/-- When the line crosses the interior, the crease is the whole chord of paper. -/
theorem Paper.creaseOn_eq_section {n : ℕ} (P : Paper n) (f : Fold)
    (meetsInterior : (interior P.region ∩ (f.axis : Set Point)).Nonempty) :
    f.creaseOn P.region = P.region ∩ (f.axis : Set Point) := by
  obtain ⟨q, hqInterior, hqAxis⟩ := meetsInterior
  have convex : Convex ℝ P.region := convex_convexHull ℝ _
  apply Set.Subset.antisymm
  · -- The chord is closed, so it contains the closure of its interior portion.
    apply closure_minimal
    · exact Set.inter_subset_inter_left _ interior_subset
    · exact P.region_compact.isClosed.inter f.axis_closed
  · -- Approach any chord endpoint from the interior point along the fold line.
    intro x hx
    have approach : openSegment ℝ q x ⊆ interior P.region ∩ (f.axis : Set Point) := by
      intro y hy
      constructor
      · exact convex.openSegment_interior_self_subset_interior hqInterior hx.1 hy
      · exact f.axis.convex.segment_subset hqAxis hx.2 (openSegment_subset_segment ℝ q x hy)
    apply closure_mono approach
    exact segment_subset_closure_openSegment (right_mem_segment ℝ q x)

/-- With both defining points on the polygon, one fold creates one
nondegenerate segment on the originally flat, uncreased sheet. -/
theorem Paper.single_fold_isCreaseSegment {n : ℕ} (P : Paper n) (f : Fold)
    (sourceInside : f.source ∈ P.region) (targetInside : f.target ∈ P.region) :
    IsCreaseSegment (f.creaseOn P.region) := by
  have meetsInterior := P.axis_meets_interior f sourceInside targetInside
  rw [P.creaseOn_eq_section f meetsInterior]
  apply compact_convex_collinear_segment
  · exact P.region_compact.inter_right f.axis_closed
  · exact (convex_convexHull ℝ _).inter f.axis.convex
  · exact f.axis_collinear.subset Set.inter_subset_right
  · exact P.axis_section_nontrivial f meetsInterior

/-- One segment has a maximal-segment decomposition with exactly one member. -/
def IsCreaseSegment.decomposition {trace : Set Point} (straight : IsCreaseSegment trace) :
    CreaseDecomposition trace := by
  classical
  refine {
    segments := {trace}
    straight := ?_
    covers := ?_
    maximal := ?_
  }
  · intro s member
    have same : s = trace := Finset.mem_singleton.mp member
    rw [same]
    exact straight
  · intro x
    simp
  · intro s member t _ contains inside
    have same : s = trace := Finset.mem_singleton.mp member
    rw [same] at contains ⊢
    exact Set.Subset.antisymm inside contains

/-- The crease bound uses the geometric decomposition, not the fold count. -/
theorem IsCreaseSegment.hasAtMostOne {trace : Set Point} (straight : IsCreaseSegment trace) :
    HasAtMostCreases trace 1 := by
  classical
  refine ⟨straight.decomposition, ?_⟩
  simp [IsCreaseSegment.decomposition]

/-- A genuine segment cannot be represented by zero crease segments. -/
theorem IsCreaseSegment.not_zero_creases {trace : Set Point}
    (straight : IsCreaseSegment trace) : ¬ HasAtMostCreases trace 0 := by
  intro zeroCreases
  obtain ⟨decomposition, countBound⟩ := zeroCreases
  have empty : decomposition.segments = ∅ := by
    apply Finset.card_eq_zero.mp
    exact Nat.eq_zero_of_le_zero countBound
  obtain ⟨a, b, _, shape⟩ := straight
  have pointOnCrease : a ∈ trace := by
    rw [shape]
    exact left_mem_segment ℝ a b
  obtain ⟨s, member, _⟩ := (decomposition.covers a).1 pointOnCrease
  rw [empty] at member
  exact Finset.notMem_empty s member

end FoldAndPunch
