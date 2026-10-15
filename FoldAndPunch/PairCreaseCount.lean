import FoldAndPunch.PairBatches

/-!
Count the cumulative geometric trace by distinct full chords of the polygon.
Each full chord is already maximal, so crossings add no segments and reuse is free.
-/

noncomputable section
open Set
namespace FoldAndPunch

/-- A straight segment is collinear, using Mathlib's span calculation. -/
theorem IsCreaseSegment.collinear {trace : Set Point} (straight : IsCreaseSegment trace) :
    Collinear ℝ trace := by
  obtain ⟨a, b, distinct, rfl⟩ := straight
  apply collinear_iff_finrank_le_one.mpr
  rw [vectorSpan_segment, finrank_span_singleton (vsub_ne_zero.mpr distinct.symm)]

/-- Each pair contributes the entire chord cut out by its fold line. -/
theorem Paper.pairChord_eq_section {n : ℕ} (P : Paper n) (p : VertexPair n) :
    P.pairChord p = P.region ∩ (P.pairFold p.first p.second p.distinct .top).axis := by
  apply P.creaseOn_eq_section
  apply P.axis_meets_interior
  · apply subset_convexHull ℝ
    exact ⟨p.first, rfl⟩
  · apply subset_convexHull ℝ
    exact ⟨p.second, rfl⟩

theorem Paper.pairChord_straight {n : ℕ} (P : Paper n) (p : VertexPair n) :
    IsCreaseSegment (P.pairChord p) := by
  apply P.single_fold_isCreaseSegment
  · apply subset_convexHull ℝ
    exact ⟨p.first, rfl⟩
  · apply subset_convexHull ℝ
    exact ⟨p.second, rfl⟩

/-- A full polygon chord cannot be extended to a larger straight segment
inside the polygon. Consequently, crossing other chords does not split it. -/
theorem Paper.pairChord_maximal {n : ℕ} (P : Paper n) (p : VertexPair n)
    (t : Set Point) (straight : IsCreaseSegment t)
    (contains : P.pairChord p ⊆ t) (inside : t ⊆ P.region) : t = P.pairChord p := by
  let f := P.pairFold p.first p.second p.distinct .top
  obtain ⟨a, b, distinct, chordShape⟩ := P.pairChord_straight p
  have ha : a ∈ P.pairChord p := by rw [chordShape]; exact left_mem_segment ℝ a b
  have hb : b ∈ P.pairChord p := by rw [chordShape]; exact right_mem_segment ℝ a b
  have haAxis : a ∈ f.axis := by
    rw [P.pairChord_eq_section] at ha
    exact ha.2
  have hbAxis : b ∈ f.axis := by
    rw [P.pairChord_eq_section] at hb
    exact hb.2
  have lineInside : affineSpan ℝ ({a, b} : Set Point) ≤ f.axis := by
    apply affineSpan_le.mpr
    intro x hx
    rcases hx with rfl | rfl
    · exact haAxis
    · exact hbAxis
  apply Set.Subset.antisymm _ contains
  intro x hx
  rw [P.pairChord_eq_section]
  refine ⟨inside hx, ?_⟩
  apply lineInside
  exact straight.collinear.mem_affineSpan_of_mem_of_ne (contains ha) (contains hb) hx distinct

/-- The cumulative trace is the finite union of the pair chords; the closure
in the definition adds nothing because all these chords are closed. -/
theorem Paper.pairChords_union {n : ℕ} (P : Paper n) (pairs : List (VertexPair n)) :
    cumulativeCreases (pairs.map P.pairChord) =
      ⋃ s ∈ (pairs.map P.pairChord).toFinset, s := by
  classical
  have closed : IsClosed (⋃ s ∈ (pairs.map P.pairChord).toFinset, s) := by
    apply isClosed_biUnion_finset
    intro s hs
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hs)
    exact isClosed_closure
  have sameUnion : {x | ∃ s ∈ pairs.map P.pairChord, x ∈ s} =
      ⋃ s ∈ (pairs.map P.pairChord).toFinset, s := by
    ext x
    simp
  unfold cumulativeCreases
  rw [sameUnion, closed.closure_eq]

/-- Keep one copy of each distinct full chord. These are already maximal,
so their number is bounded by the number of pair operations. -/
theorem Paper.pairChords_count {n : ℕ} (P : Paper n) (pairs : List (VertexPair n)) :
    HasAtMostCreases (cumulativeCreases (pairs.map P.pairChord)) pairs.length := by
  classical
  let segments := (pairs.map P.pairChord).toFinset
  have unionInside : cumulativeCreases (pairs.map P.pairChord) ⊆ P.region := by
    intro x hx
    rw [P.pairChords_union] at hx
    obtain ⟨s, hs, member⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hs)
    rw [P.pairChord_eq_section] at member
    exact member.1
  let decomposition : CreaseDecomposition (cumulativeCreases (pairs.map P.pairChord)) := {
    segments := segments
    straight := by
      intro s hs
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hs)
      exact P.pairChord_straight p
    covers := by
      intro x
      rw [P.pairChords_union]
      simp [segments]
    maximal := by
      intro s hs t straight contains inside
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hs)
      exact P.pairChord_maximal p t straight contains (inside.trans unionInside)
  }
  refine ⟨decomposition, ?_⟩
  have bound := (pairs.map P.pairChord).toFinset_card_le
  simpa [decomposition, segments] using bound


end FoldAndPunch
