import FoldAndPunch.PairCreaseCount
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Analysis.InnerProductSpace.Convex

/-!
# Combining geometric crease bounds

A finite cover by segments can be replaced by a maximal-segment decomposition
without increasing its size. This makes crease bounds subadditive under union,
including when pieces cross, overlap, or join along the same line.
-/

noncomputable section
open Set
namespace FoldAndPunch

/-- In a compact trace, every genuine segment extends to a maximal one.
Choose the longest admissible extension; compactness supplies its endpoints. -/
theorem IsCreaseSegment.exists_maximal_extension {s trace : Set Point}
    (straight : IsCreaseSegment s) (compact : IsCompact trace) (inside : s ⊆ trace) :
    ∃ m, IsCreaseSegment m ∧ s ⊆ m ∧ m ⊆ trace ∧
      ∀ t, IsCreaseSegment t → m ⊆ t → t ⊆ trace → t = m := by
  obtain ⟨a, b, distinct, rfl⟩ := straight
  let candidates : Set (Point × Point) :=
    {p | a ∈ segment ℝ p.1 p.2 ∧ b ∈ segment ℝ p.1 p.2 ∧
      segment ℝ p.1 p.2 ⊆ trace}
  have memberClosed (x : Point) : IsClosed {p : Point × Point | x ∈ segment ℝ p.1 p.2} := by
    have description : {p : Point × Point | x ∈ segment ℝ p.1 p.2} =
        {p | dist p.1 x + dist x p.2 = dist p.1 p.2} := by
      ext p
      exact mem_segment_iff_wbtw.trans dist_add_dist_eq_iff.symm
    rw [description]
    exact isClosed_eq
      ((continuous_fst.dist continuous_const).add (continuous_const.dist continuous_snd))
      (continuous_fst.dist continuous_snd)
  have subsetClosed : IsClosed {p : Point × Point | segment ℝ p.1 p.2 ⊆ trace} := by
    have description : {p : Point × Point | segment ℝ p.1 p.2 ⊆ trace} =
        ⋂ t : Icc (0 : ℝ) 1, {p | (1 - (t : ℝ)) • p.1 + (t : ℝ) • p.2 ∈ trace} := by
      ext p
      simp only [segment_eq_image, image_subset_iff, mem_ofPred_eq, mem_iInter]
      exact ⟨fun h t => h t.property, fun h t ht => h ⟨t, ht⟩⟩
    rw [description]
    apply isClosed_iInter
    intro t
    exact compact.isClosed.preimage
      ((continuous_fst.const_smul (1 - (t : ℝ))).add (continuous_snd.const_smul (t : ℝ)))
  have candidatesClosed : IsClosed candidates := (memberClosed a).inter ((memberClosed b).inter subsetClosed)
  have candidatesCompact : IsCompact candidates := by
    apply (compact.prod compact).of_isClosed_subset candidatesClosed
    intro p hp
    exact ⟨hp.2.2 (left_mem_segment ℝ _ _), hp.2.2 (right_mem_segment ℝ _ _)⟩
  have candidatesNonempty : candidates.Nonempty :=
    ⟨(a, b), left_mem_segment ℝ a b, right_mem_segment ℝ a b, inside⟩
  obtain ⟨⟨u, v⟩, admissible, longest⟩ := candidatesCompact.exists_isMaxOn candidatesNonempty
    (f := fun p : Point × Point => dist p.1 p.2) continuous_dist.continuousOn
  have contains : segment ℝ a b ⊆ segment ℝ u v :=
    (convex_segment u v).segment_subset admissible.1 admissible.2.1
  have different : u ≠ v := by
    intro same
    have ha := admissible.1
    have hb := admissible.2.1
    simp only [same, segment_same, mem_singleton_iff] at ha hb
    exact distinct (ha.trans hb.symm)
  refine ⟨segment ℝ u v, ⟨u, v, different, rfl⟩, contains, admissible.2.2, ?_⟩
  intro t tStraight extendsSegment tInside
  have hu := extendsSegment (left_mem_segment ℝ u v)
  have hv := extendsSegment (right_mem_segment ℝ u v)
  have tConvex : Convex ℝ t := by
    obtain ⟨c, d, _, rfl⟩ := tStraight
    exact convex_segment c d
  apply Set.Subset.antisymm _ extendsSegment
  intro x hx
  have triple : Collinear ℝ ({u, x, v} : Set Point) := by
    apply tStraight.collinear.subset
    intro y hy
    rcases hy with rfl | rfl | rfl
    · exact hu
    · exact hx
    · exact hv
  rcases triple.wbtw_or_wbtw_or_wbtw with between | beyondV | beyondU
  · exact mem_segment_iff_wbtw.mpr between
  · have extension : segment ℝ u v ⊆ segment ℝ u x :=
      (convex_segment u x).segment_subset (left_mem_segment ℝ u x)
        (mem_segment_iff_wbtw.mpr beyondV.symm)
    have feasible : (u, x) ∈ candidates := ⟨extension admissible.1,
      extension admissible.2.1, (tConvex.segment_subset hu hx).trans tInside⟩
    have bound : dist u x ≤ dist u v := (isMaxOn_iff.mp longest) (u, x) feasible
    have distanceSum := beyondV.dist_add_dist
    have same : x = v := by
      apply dist_le_zero.mp
      rw [dist_comm x u, dist_comm v u] at distanceSum
      linarith
    rw [same]
    exact right_mem_segment ℝ u v
  · have extension : segment ℝ u v ⊆ segment ℝ x v :=
      (convex_segment x v).segment_subset (mem_segment_iff_wbtw.mpr beyondU.symm)
        (right_mem_segment ℝ x v)
    have feasible : (x, v) ∈ candidates := ⟨extension admissible.1,
      extension admissible.2.1, (tConvex.segment_subset hx hv).trans tInside⟩
    have bound : dist x v ≤ dist u v := (isMaxOn_iff.mp longest) (x, v) feasible
    have distanceSum := beyondU.dist_add_dist
    have same : x = u := by
      apply dist_le_zero.mp
      rw [dist_comm v u, dist_comm u x, dist_comm v x] at distanceSum
      linarith
    rw [same]
    exact left_mem_segment ℝ u v

/-- A finite cover by genuine segments bounds the number of maximal creases.
Extend each covering segment maximally inside the union, then discard duplicates. -/
theorem hasAtMostCreases_of_segment_cover (pieces : Finset (Set Point))
    (straight : ∀ s ∈ pieces, IsCreaseSegment s) :
    HasAtMostCreases (⋃ s ∈ pieces, s) pieces.card := by
  classical
  let trace := ⋃ s ∈ pieces, s
  have compact : IsCompact trace := by
    apply pieces.isCompact_biUnion
    intro s hs
    obtain ⟨a, b, _, rfl⟩ := straight s hs
    rw [segment_eq_image]
    exact isCompact_Icc.image
      (((continuous_const.sub continuous_id).smul continuous_const).add
        (continuous_id.smul continuous_const))
  have extensions : ∀ s : {s // s ∈ pieces}, ∃ m, IsCreaseSegment m ∧
      s.val ⊆ m ∧ m ⊆ trace ∧
      ∀ t, IsCreaseSegment t → m ⊆ t → t ⊆ trace → t = m := by
    intro s
    apply (straight s.val s.property).exists_maximal_extension compact
    intro x hx
    exact mem_iUnion₂.mpr ⟨s.val, s.property, hx⟩
  choose extend properties using extensions
  let maximalPieces := Finset.univ.image extend
  refine ⟨{
    segments := maximalPieces
    straight := ?_
    covers := ?_
    maximal := ?_
  }, ?_⟩
  · intro m hm
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hm
    exact (properties s).1
  · intro x
    constructor
    · intro hx
      obtain ⟨s, hs, member⟩ := mem_iUnion₂.mp hx
      exact ⟨extend ⟨s, hs⟩, Finset.mem_image.mpr ⟨⟨s, hs⟩, Finset.mem_univ _, rfl⟩,
        (properties ⟨s, hs⟩).2.1 member⟩
    · rintro ⟨m, hm, hx⟩
      obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hm
      exact (properties s).2.2.1 hx
  · intro m hm t ht contains inside
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hm
    exact (properties s).2.2.2 t ht contains inside
  · exact Finset.card_image_le.trans (by simp)

/-- Empty contact traces contribute no creases. -/
theorem empty_hasAtMostCreases (bound : ℕ) : HasAtMostCreases ∅ bound := by
  classical
  have count := hasAtMostCreases_of_segment_cover ∅ (by simp)
  simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, Finset.card_empty] at count
  obtain ⟨d, hd⟩ := count
  exact ⟨d, hd.trans (Nat.zero_le bound)⟩

/-- Combining crease traces costs at most the sum of their bounds. -/
theorem HasAtMostCreases.union {s t : Set Point} {m n : ℕ}
    (hs : HasAtMostCreases s m) (ht : HasAtMostCreases t n) :
    HasAtMostCreases (s ∪ t) (m + n) := by
  classical
  obtain ⟨ds, boundS⟩ := hs
  obtain ⟨dt, boundT⟩ := ht
  have shape : (⋃ u ∈ ds.segments ∪ dt.segments, u) = s ∪ t := by
    ext x
    simp only [mem_iUnion, Finset.mem_union, mem_union]
    constructor
    · rintro ⟨u, hu | hu, hx⟩
      · exact Or.inl ((ds.covers x).2 ⟨u, hu, hx⟩)
      · exact Or.inr ((dt.covers x).2 ⟨u, hu, hx⟩)
    · rintro (hx | hx)
      · obtain ⟨u, hu, member⟩ := (ds.covers x).1 hx
        exact ⟨u, Or.inl hu, member⟩
      · obtain ⟨u, hu, member⟩ := (dt.covers x).1 hx
        exact ⟨u, Or.inr hu, member⟩
  have count := hasAtMostCreases_of_segment_cover (ds.segments ∪ dt.segments) (by
    intro u hu
    rcases Finset.mem_union.mp hu with member | member
    · exact ds.straight u member
    · exact dt.straight u member)
  rw [shape] at count
  obtain ⟨decomposition, bound⟩ := count
  have unionBound := Finset.card_union_le ds.segments dt.segments
  have sumBound := Nat.add_le_add boundS boundT
  exact ⟨decomposition, bound.trans (unionBound.trans sumBound)⟩

end FoldAndPunch
