import FoldAndPunch.SecondFoldCreases

/-!
# Exposing three chosen vertices

First fold a onto b. The resulting stack at b contains exactly a and b.
Every other stack has at most two layers, so c is exposed from one side.
Fold the pair onto c's current location from that side and punch from the same
side. The first three layers are precisely the chosen vertices.
-/

noncomputable section
namespace FoldAndPunch

/-- One fold of flat paper leaves at most two layers at every location. -/
theorem flat_fold_stack_length_le_two (material : Set Point) (f : Fold) (q : Point) :
    (((flatConfiguration material).fold f).stack q).length ≤ 2 := by
  classical
  have flatBound (x : Point) : ((flatConfiguration material).stack x).length ≤ 1 := by
    by_cases present : x ∈ material <;> simp [flatConfiguration, present]
  simp only [Configuration.fold]
  split
  · simp
  · split
    · exact (flatBound q).trans (by decide)
    · have first := flatBound (f.reflect q)
      have second := flatBound q
      cases f.placement <;>
        simp only [placeStack, List.length_append, List.length_reverse] <;> omega

/-- Check whether the chosen original point is the top layer; otherwise use
its bottom exposure. The accompanying lemma requires a stack of at most two. -/
def exposureSide (stack : List Point) (c : Point) : Side := by
  classical
  exact if stack.head? = some c then .top else .bottom

/-- A present point in a one- or two-layer stack is exposed from one side. -/
theorem exposureSide_spec (stack : List Point) (c : Point)
    (short : stack.length ≤ 2) (present : c ∈ stack) :
    ∃ rest, (match exposureSide stack c with
      | .top => stack
      | .bottom => stack.reverse) = c :: rest := by
  classical
  cases stack with
  | nil => simp at present
  | cons a tail =>
    by_cases first : a = c
    · subst a
      exact ⟨tail, by simp [exposureSide]⟩
    · cases tail with
      | nil => simp [Ne.symm first] at present
      | cons b tail =>
        have empty : tail = [] := by
          have zero : tail.length = 0 := by simp only [List.length_cons] at short; omega
          simpa using zero
        subst tail
        have second : b = c := by
          have inTail : c ∈ [b] := (List.mem_cons.mp present).resolve_left (Ne.symm first)
          exact (List.mem_singleton.mp inTail).symm
        subst b
        exact ⟨[a], by simp [exposureSide, first]⟩

/-- Bring an exact pair onto a point exposed on the chosen side. There may
be deeper layers behind that point; the depth-three punch does not hit them. -/
theorem fold_pair_onto_exposed_hits (C : Configuration) (g : Fold)
    (a b c : Point) (pair : C.stack g.source = [a, b])
    (exposed : ∃ rest, C.layersFrom g.placement g.target = c :: rest) :
    (C.fold g).punchHits 3 g.placement g.target =
      match g.placement with
      | .top => [b, a, c]
      | .bottom => [a, b, c] := by
  obtain ⟨rest, exposure⟩ := exposed
  have stack : (C.fold g).stack g.target =
      placeStack g.placement [a, b] (C.stack g.target) := by
    simp [Configuration.fold, g.not_moving_target, g.target_not_on_axis,
      g.reflect_target, pair]
  cases placement : g.placement
  · simp only [Configuration.layersFrom, placement] at exposure
    simp [Configuration.punchHits, Configuration.layersFrom, placement, stack,
      placeStack, exposure]
  · simp only [Configuration.layersFrom, placement] at exposure
    simp [Configuration.punchHits, Configuration.layersFrom, placement, stack,
      placeStack, List.reverse_append, exposure]

/-- A third distinct point cannot join the pair during the first fold:
the pair location has exactly the two original geometric preimages. -/
theorem Fold.third_location_ne_target (f : Fold) (c : Point)
    (notSource : c ≠ f.source) (notTarget : c ≠ f.target) :
    f.pointMap c ≠ f.target := by
  intro same
  have preimages := (f.pointMap_eq_off_axis f.not_moving_target f.target_not_on_axis).mp same
  rcases preimages with atTarget | atSource
  · exact notTarget atTarget
  · rw [f.reflect_target] at atSource
    exact notSource atSource

/-- The second fold moves the double stack onto the third point's current
location. Its placement is determined by the exposure check after the first fold. -/
def secondTripleFold (material : Set Point) (first : Fold) (c : Point)
    (notSource : c ≠ first.source) (notTarget : c ≠ first.target) : Fold where
  source := first.target
  target := first.pointMap c
  distinct := (first.third_location_ne_target c notSource notTarget).symm
  placement := exposureSide (((flatConfiguration material).fold first).stack (first.pointMap c)) c

/-- The explicit exposure check makes the selected third point the next layer
behind the pair when the second fold is performed. -/
theorem secondTripleFold_hits {n : ℕ} (P : Paper n) (material : Set Point)
    (inside : material ⊆ P.region) (first : Fold) (c : Point)
    (firstTop : first.placement = .top)
    (sourcePresent : first.source ∈ material) (targetPresent : first.target ∈ material)
    (thirdPresent : c ∈ material) (notSource : c ≠ first.source) (notTarget : c ≠ first.target) :
    let second := secondTripleFold material first c notSource notTarget
    (((flatConfiguration material).fold first).fold second).punchHits 3 second.placement second.target =
      match second.placement with
      | .top => [first.target, first.source, c]
      | .bottom => [first.source, first.target, c] := by
  dsimp only
  let C := (flatConfiguration material).fold first
  let second := secondTripleFold material first c notSource notTarget
  have wellFormed : C.WellFormed P := Configuration.fold_wellFormed (flatConfiguration_wellFormed P material inside) first
  have present : c ∈ C.stack (first.pointMap c) := by
    apply (wellFormed.2.2 _ c).mpr
    exact ⟨thirdPresent, rfl⟩
  have exposure := exposureSide_spec (C.stack (first.pointMap c)) c
    (flat_fold_stack_length_le_two material first _) present
  apply fold_pair_onto_exposed_hits
  · simpa [secondTripleFold, firstTop] using
      flat_fold_stack_at_target material first sourcePresent targetPresent
  · exact exposure

/-- The concrete second fold for three distinct vertex indices. The first fold
is an overfold of i onto j; the second placement uses the exposure test for k. -/
def Paper.tripleSecondFold {n : ℕ} (P : Paper n) (material : Set Point)
    (i j k : Fin n) (ij : i ≠ j) (ki : k ≠ i) (kj : k ≠ j) : Fold :=
  secondTripleFold material (P.pairFold i j ij .top) (P.polygon.vertices k)
    (P.vertices_injective.ne ki) (P.vertices_injective.ne kj)

/-- Any three fresh distinct vertices can be punched by the two prescribed
folds. The remaining material may already have holes from earlier batches. -/
theorem Paper.tripleFold_successful {n : ℕ} (P : Paper n) (material : Set Point)
    (inside : material ⊆ P.region) (i j k : Fin n)
    (ij : i ≠ j) (ki : k ≠ i) (kj : k ≠ j)
    (firstPresent : P.polygon.vertices i ∈ material)
    (secondPresent : P.polygon.vertices j ∈ material)
    (thirdPresent : P.polygon.vertices k ∈ material) :
    let first := P.pairFold i j ij .top
    let second := P.tripleSecondFold material i j k ij ki kj
    SuccessfulPunch P (((flatConfiguration material).fold first).fold second)
      3 {i, j, k} second.placement second.target := by
  classical
  dsimp only
  let first := P.pairFold i j ij .top
  let second := P.tripleSecondFold material i j k ij ki kj
  let C := ((flatConfiguration material).fold first).fold second
  have hits : C.punchHits 3 second.placement second.target =
      match second.placement with
      | .top => [P.polygon.vertices j, P.polygon.vertices i, P.polygon.vertices k]
      | .bottom => [P.polygon.vertices i, P.polygon.vertices j, P.polygon.vertices k] := by
    exact secondTripleFold_hits P material inside first (P.polygon.vertices k) rfl
      firstPresent secondPresent thirdPresent
      (P.vertices_injective.ne ki) (P.vertices_injective.ne kj)
  change SuccessfulPunch P C 3 {i, j, k} second.placement second.target
  unfold SuccessfulPunch
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_⟩
  · apply Configuration.fold_wellFormed
    apply Configuration.fold_wellFormed
    exact flatConfiguration_wellFormed P material inside
  · simp [ij, ki.symm, kj.symm]
  · intro index member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl
    · exact firstPresent
    · exact secondPresent
    · exact thirdPresent
  · rw [hits]
    cases second.placement <;> rfl
  · intro x
    rw [hits]
    cases second.placement <;> simp [or_left_comm]

/-- The first-batch triple is ready for an exactly-three punch, and the two
folds create at most three geometric creases. -/
theorem Paper.triple_ready_to_punch_with_three_creases {n : ℕ} (P : Paper n)
    (i j k : Fin n) (ij : i ≠ j) (ki : k ≠ i) (kj : k ≠ j) :
    let first := P.pairFold i j ij .top
    let second := P.tripleSecondFold P.region i j k ij ki kj
    SuccessfulPunch P ((P.initial.fold first).fold second)
      3 {i, j, k} second.placement second.target ∧
    HasAtMostCreases (first.twoFoldCreases second P.region) 3 := by
  dsimp only
  constructor
  · apply P.tripleFold_successful P.region Set.Subset.rfl
    · exact subset_convexHull ℝ _ ⟨i, rfl⟩
    · exact subset_convexHull ℝ _ ⟨j, rfl⟩
    · exact subset_convexHull ℝ _ ⟨k, rfl⟩
  · exact P.pair_then_fold_atMost_three_creases i j ij .top _

end FoldAndPunch
