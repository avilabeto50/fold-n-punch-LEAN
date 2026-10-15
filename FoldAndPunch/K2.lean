import FoldAndPunch.PairCreaseCount
import Mathlib.Data.List.FinRange

/-!
The complete k=2 result for even n: consecutive pairs, safe punches, exact
completion, and at most n/2 distinct maximal crease segments.
Read Paper.k2_correct_and_linear for the combined theorem.
-/

noncomputable section
open Set
namespace FoldAndPunch

/-- Pair a duplicate-free vertex list consecutively. An unmatched last vertex
is dropped; the correctness theorem below requires even length. -/
def pairUp {n : ℕ} : (vertices : List (Fin n)) → vertices.Nodup → List (VertexPair n)
  | [], _ => []
  | [_], _ => []
  | a :: b :: rest, noRepeat =>
    { first := a, second := b, distinct := by
        intro same
        exact (List.nodup_cons.mp noRepeat).1 (by simp [same]) } ::
      pairUp rest noRepeat.tail.tail

/-- With even length no vertex is dropped, duplicated, or reordered. -/
theorem pairUp_vertices {n : ℕ} (vertices : List (Fin n)) (noRepeat : vertices.Nodup)
    (even : vertices.length % 2 = 0) : pairVertices (pairUp vertices noRepeat) = vertices := by
  cases vertices with
  | nil => rfl
  | cons a tail =>
    cases tail with
    | nil => simp at even
    | cons b rest =>
      have restEven : rest.length % 2 = 0 := by
        simp only [List.length_cons] at even
        omega
      change a :: b :: pairVertices (pairUp rest noRepeat.tail.tail) = a :: b :: rest
      rw [pairUp_vertices rest noRepeat.tail.tail restEven]
termination_by vertices.length

/-- The fixed baseline: (0,1), (2,3), ... in polygon boundary order. -/
def consecutivePairs (n : ℕ) : List (VertexPair n) :=
  pairUp (List.finRange n) (List.nodup_finRange n)

theorem consecutivePairs_vertices (n : ℕ) (even : n % 2 = 0) :
    pairVertices (consecutivePairs n) = List.finRange n := by
  apply pairUp_vertices
  simpa using even

theorem pairVertices_length {n : ℕ} (pairs : List (VertexPair n)) :
    (pairVertices pairs).length = 2 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons p rest inductionHypothesis =>
    change (pairVertices rest).length + 1 + 1 = 2 * (rest.length + 1)
    omega

theorem consecutivePairs_length (n : ℕ) (even : n % 2 = 0) :
    (consecutivePairs n).length = n / 2 := by
  have lengthEquality := congrArg List.length (consecutivePairs_vertices n even)
  rw [pairVertices_length, List.length_finRange] at lengthEquality
  omega

/-- Complete k=2 algorithm: all intermediate punches are safe; all and only
vertices are removed; exactly n/2 pair operations are performed; and their
ACTUAL cumulative geometric trace admits at most n/2 maximal crease segments.
This is an explicit uniform linear upper bound, not an optimality assertion. -/
theorem Paper.k2_correct_and_linear {n : ℕ} (P : Paper n) (even : n % 2 = 0) :
    P.SafePairs P.initial (consecutivePairs n) ∧
    AllVerticesPunched P (P.runPairs P.initial (consecutivePairs n)) ∧
    (P.runPairs P.initial (consecutivePairs n)).WellFormed P ∧
    (consecutivePairs n).length = n / 2 ∧
    HasAtMostCreases
      (cumulativeCreases (P.pairHistory P.initial (consecutivePairs n))) (n / 2) := by
  have allIndices := consecutivePairs_vertices n even
  have noRepeat : (pairVertices (consecutivePairs n)).Nodup := by
    rw [allIndices]
    exact List.nodup_finRange n
  -- Start with no holes, then use the induction covering all intermediate states.
  obtain ⟨safe, finalMaterial, actualHistory⟩ :=
    P.runPairs_spec (consecutivePairs n) noRepeat ∅ (Set.empty_subset _)
      (by intro i _; exact Set.notMem_empty _)
  simp only [Set.sdiff_empty, Set.empty_union] at safe finalMaterial actualHistory
  have allMarked : P.pairPoints (consecutivePairs n) = P.marked := by
    ext x
    simp [Paper.pairPoints, allIndices, Paper.marked, eq_comm]
  rw [allMarked] at finalMaterial
  have finalState : P.runPairs P.initial (consecutivePairs n) =
      flatConfiguration (P.region \ P.marked) := finalMaterial
  refine ⟨safe, ?_, ?_, consecutivePairs_length n even, ?_⟩
  · -- Completion is an equality of material sets, so no unmarked point is lost.
    unfold AllVerticesPunched
    rw [finalState]
    rfl
  · rw [finalState]
    apply flatConfiguration_wellFormed
    exact Set.sdiff_subset
  · -- Count actual recorded creases, replacing each by its unchanged full chord.
    change HasAtMostCreases
      (cumulativeCreases (P.pairHistory (flatConfiguration P.region) (consecutivePairs n))) _
    rw [actualHistory, ← consecutivePairs_length n even]
    exact P.pairChords_count (consecutivePairs n)

end FoldAndPunch
