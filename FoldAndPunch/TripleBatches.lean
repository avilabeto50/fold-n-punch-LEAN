import FoldAndPunch.Triple

/-!
# Iterating disjoint triples

Each batch uses two folds, punches three fresh vertices, and unfolds completely.
Earlier vertex holes leave the interior, and hence each crease trace, unchanged.
The second fold's placement is recomputed from the material actually present.
-/

noncomputable section
open Set
namespace FoldAndPunch

structure VertexTriple (n : ℕ) where
  first : Fin n
  second : Fin n
  third : Fin n
  first_ne_second : first ≠ second
  third_ne_first : third ≠ first
  third_ne_second : third ≠ second

def tripleVertices {n : ℕ} (triples : List (VertexTriple n)) : List (Fin n) :=
  triples.flatMap (fun t => [t.first, t.second, t.third])

def Paper.triplePoints {n : ℕ} (P : Paper n) (triples : List (VertexTriple n)) : Set Point :=
  {x | ∃ i ∈ tripleVertices triples, x = P.polygon.vertices i}

def Paper.tripleFirst {n : ℕ} (P : Paper n) (t : VertexTriple n) : Fold :=
  P.pairFold t.first t.second t.first_ne_second .top

def Paper.tripleSecond {n : ℕ} (P : Paper n) (material : Set Point) (t : VertexTriple n) : Fold :=
  P.tripleSecondFold material t.first t.second t.third
    t.first_ne_second t.third_ne_first t.third_ne_second

def Paper.doTriple {n : ℕ} (P : Paper n) (C : Configuration) (t : VertexTriple n) : Configuration :=
  let second := P.tripleSecond C.material t
  (((C.fold (P.tripleFirst t)).fold second).punch 3 second.placement second.target).unfold

def Paper.runTriples {n : ℕ} (P : Paper n) (C : Configuration) :
    List (VertexTriple n) → Configuration
  | [] => C
  | t :: rest => P.runTriples (P.doTriple C t) rest

/-- The actual two-fold trace on the material present before each batch. -/
def Paper.tripleHistory {n : ℕ} (P : Paper n) (C : Configuration) :
    List (VertexTriple n) → List (Set Point)
  | [] => []
  | t :: rest =>
    (P.tripleFirst t).twoFoldCreases (P.tripleSecond C.material t) C.material ::
      P.tripleHistory (P.doTriple C t) rest

def Paper.SafeTriples {n : ℕ} (P : Paper n) (C : Configuration) :
    List (VertexTriple n) → Prop
  | [] => True
  | t :: rest =>
    let second := P.tripleSecond C.material t
    SuccessfulPunch P ((C.fold (P.tripleFirst t)).fold second)
      3 {t.first, t.second, t.third} second.placement second.target ∧
    P.SafeTriples (P.doTriple C t) rest

/-- Earlier punches remove boundary points only. Both folds' traces depend on
interior material, which those holes do not change. The fold lines are arbitrary. -/
theorem Paper.twoFoldCreases_remove_marked {n : ℕ} (P : Paper n) (holes : Set Point)
    (onlyMarked : holes ⊆ P.marked) (first second : Fold) :
    first.twoFoldCreases second (P.region \ holes) = first.twoFoldCreases second P.region := by
  unfold Fold.twoFoldCreases Fold.creaseOn Fold.secondCreases
    Fold.secondStationaryCrease Fold.secondMovingCrease Fold.stationaryPatch Fold.movingPatch
  rw [P.interior_remove_marked holes onlyMarked]

/-- Closure respects adjoining batch histories. -/
theorem cumulativeCreases_cons (trace : Set Point) (history : List (Set Point)) :
    cumulativeCreases (trace :: history) = closure trace ∪ cumulativeCreases history := by
  have unionEq : {x | ∃ s ∈ trace :: history, x ∈ s} =
      trace ∪ {x | ∃ s ∈ history, x ∈ s} := by
    ext x
    simp
  unfold cumulativeCreases
  rw [unionEq, closure_union]

theorem Fold.twoFoldCreases_closed (first second : Fold) (sheet : Set Point) :
    IsClosed (first.twoFoldCreases second sheet) := by
  exact isClosed_closure.union (isClosed_closure.union isClosed_closure)

/-- A safe triple operation removes exactly its three original vertices. -/
theorem Paper.doTriple_material {n : ℕ} (P : Paper n) (material : Set Point)
    (inside : material ⊆ P.region) (t : VertexTriple n)
    (firstPresent : P.polygon.vertices t.first ∈ material)
    (secondPresent : P.polygon.vertices t.second ∈ material)
    (thirdPresent : P.polygon.vertices t.third ∈ material) :
    P.doTriple (flatConfiguration material) t =
      flatConfiguration (material \ {P.polygon.vertices t.first,
        P.polygon.vertices t.second, P.polygon.vertices t.third}) := by
  have safe := P.tripleFold_successful material inside t.first t.second t.third
    t.first_ne_second t.third_ne_first t.third_ne_second
    firstPresent secondPresent thirdPresent
  obtain ⟨_, _, _, _, _, hits⟩ := safe
  unfold Paper.doTriple Configuration.unfold
  apply congrArg flatConfiguration
  ext x
  change (x ∈ material ∧ x ∉ _ ) ↔ _
  simp only [Paper.tripleFirst, Paper.tripleSecond, flatConfiguration] at hits ⊢
  rw [hits]
  simp

/-- Execute any duplicate-free list of fresh triples. Every punch is safe,
only those vertices are removed, and the actual cumulative trace has at most
three creases per triple. -/
theorem Paper.runTriples_spec {n : ℕ} (P : Paper n) (triples : List (VertexTriple n))
    (noRepeat : (tripleVertices triples).Nodup) (holes : Set Point)
    (onlyMarked : holes ⊆ P.marked)
    (fresh : ∀ i ∈ tripleVertices triples, P.polygon.vertices i ∉ holes) :
    P.SafeTriples (flatConfiguration (P.region \ holes)) triples ∧
    P.runTriples (flatConfiguration (P.region \ holes)) triples =
      flatConfiguration (P.region \ (holes ∪ P.triplePoints triples)) ∧
    HasAtMostCreases
      (cumulativeCreases (P.tripleHistory (flatConfiguration (P.region \ holes)) triples))
      (3 * triples.length) := by
  classical
  induction triples generalizing holes with
  | nil =>
    refine ⟨trivial, ?_, ?_⟩
    · simp [Paper.runTriples, Paper.triplePoints, tripleVertices]
    · simpa [Paper.tripleHistory, cumulativeCreases] using empty_hasAtMostCreases 0
  | cons t rest inductionHypothesis =>
    change (t.first :: t.second :: t.third :: tripleVertices rest).Nodup at noRepeat
    have firstPresent : P.polygon.vertices t.first ∈ P.region \ holes := by
      refine ⟨subset_convexHull ℝ _ ⟨t.first, rfl⟩, ?_⟩
      apply fresh
      simp [tripleVertices]
    have secondPresent : P.polygon.vertices t.second ∈ P.region \ holes := by
      refine ⟨subset_convexHull ℝ _ ⟨t.second, rfl⟩, ?_⟩
      apply fresh
      simp [tripleVertices]
    have thirdPresent : P.polygon.vertices t.third ∈ P.region \ holes := by
      refine ⟨subset_convexHull ℝ _ ⟨t.third, rfl⟩, ?_⟩
      apply fresh
      simp [tripleVertices]
    let newHoles := holes ∪ {P.polygon.vertices t.first,
      P.polygon.vertices t.second, P.polygon.vertices t.third}
    have newOnlyMarked : newHoles ⊆ P.marked := by
      intro x hx
      rcases hx with old | triple
      · exact onlyMarked old
      · rcases triple with rfl | rfl | rfl
        · exact ⟨t.first, rfl⟩
        · exact ⟨t.second, rfl⟩
        · exact ⟨t.third, rfl⟩
    have remainingFresh : ∀ i ∈ tripleVertices rest, P.polygon.vertices i ∉ newHoles := by
      intro i hi removed
      rcases removed with old | triple
      · apply fresh i _ old
        change i ∈ t.first :: t.second :: t.third :: tripleVertices rest
        simp [hi]
      · rcases triple with first | second | third
        · have same := P.vertices_injective first
          subst i
          exact (List.nodup_cons.mp noRepeat).1 (by simp [hi])
        · have same := P.vertices_injective second
          subst i
          exact (List.nodup_cons.mp noRepeat.tail).1 (by simp [hi])
        · have same := P.vertices_injective third
          subst i
          exact (List.nodup_cons.mp noRepeat.tail.tail).1 hi
    have afterTriple : P.doTriple (flatConfiguration (P.region \ holes)) t =
        flatConfiguration (P.region \ newHoles) := by
      rw [P.doTriple_material (P.region \ holes) Set.sdiff_subset t
        firstPresent secondPresent thirdPresent]
      apply congrArg flatConfiguration
      ext x
      simp [newHoles, and_assoc, and_comm]
    obtain ⟨remainingSafe, remainingMaterial, remainingCount⟩ :=
      inductionHypothesis noRepeat.tail.tail.tail newHoles newOnlyMarked remainingFresh
    refine ⟨?_, ?_, ?_⟩
    · constructor
      · exact P.tripleFold_successful (P.region \ holes) Set.sdiff_subset
          t.first t.second t.third t.first_ne_second t.third_ne_first t.third_ne_second
          firstPresent secondPresent thirdPresent
      · rw [afterTriple]
        exact remainingSafe
    · rw [Paper.runTriples, afterTriple, remainingMaterial]
      apply congrArg flatConfiguration
      ext x
      simp [newHoles, Paper.triplePoints, tripleVertices,
        or_and_right, exists_or, or_assoc, and_left_comm, and_comm]
    · rw [Paper.tripleHistory, afterTriple, cumulativeCreases_cons,
        (Fold.twoFoldCreases_closed _ _ _).closure_eq]
      have unchanged := P.twoFoldCreases_remove_marked holes onlyMarked
        (P.tripleFirst t) (P.tripleSecond (P.region \ holes) t)
      have thisCount : HasAtMostCreases
          ((P.tripleFirst t).twoFoldCreases (P.tripleSecond (P.region \ holes) t)
            (P.region \ holes)) 3 := by
        rw [unchanged]
        exact P.two_folds_atMost_three_creases _ _
      have total := thisCount.union remainingCount
      simpa only [flatConfiguration, List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_comm] using total

end FoldAndPunch
