import FoldAndPunch.TripleBatches
import Mathlib.Data.List.FinRange

/-!
# The complete k=3 algorithm

A duplicate-free partition into m triples punches every vertex with at most
3m geometric creases. For n vertices divisible by three, consecutive triples
give m = n/3, so the explicit bound is n creases.
-/

noncomputable section
open Set
namespace FoldAndPunch

/-- Any partition into triples gives a safe, complete algorithm with at most
three creases per triple. The bound is on the actual cumulative geometric trace. -/
theorem Paper.triples_correct_and_linear {n : ℕ} (P : Paper n)
    (triples : List (VertexTriple n)) (noRepeat : (tripleVertices triples).Nodup)
    (covers : ∀ i : Fin n, i ∈ tripleVertices triples) :
    P.SafeTriples P.initial triples ∧
    AllVerticesPunched P (P.runTriples P.initial triples) ∧
    (P.runTriples P.initial triples).WellFormed P ∧
    HasAtMostCreases (cumulativeCreases (P.tripleHistory P.initial triples))
      (3 * triples.length) := by
  obtain ⟨safe, finalMaterial, count⟩ :=
    P.runTriples_spec triples noRepeat ∅ (Set.empty_subset _)
      (by intro i _; exact Set.notMem_empty _)
  simp only [Set.sdiff_empty, Set.empty_union] at safe finalMaterial count
  have allMarked : P.triplePoints triples = P.marked := by
    ext x
    constructor
    · rintro ⟨i, _, same⟩
      exact ⟨i, same.symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, covers i, rfl⟩
  rw [allMarked] at finalMaterial
  have finalState : P.runTriples P.initial triples =
      flatConfiguration (P.region \ P.marked) := finalMaterial
  refine ⟨safe, ?_, ?_, count⟩
  · unfold AllVerticesPunched
    rw [finalState]
    rfl
  · rw [finalState]
    exact flatConfiguration_wellFormed P _ Set.sdiff_subset

/-- Group a duplicate-free vertex list consecutively. One or two trailing
vertices are omitted; the coverage theorem requires length divisible by three. -/
def tripleUp {n : ℕ} : (vertices : List (Fin n)) → vertices.Nodup → List (VertexTriple n)
  | [], _ => []
  | [_], _ => []
  | [_, _], _ => []
  | a :: b :: c :: rest, noRepeat =>
    { first := a, second := b, third := c
      first_ne_second := by
        intro same
        exact (List.nodup_cons.mp noRepeat).1 (by simp [same])
      third_ne_first := by
        intro same
        exact (List.nodup_cons.mp noRepeat).1 (by simp [same])
      third_ne_second := by
        intro same
        exact (List.nodup_cons.mp noRepeat.tail).1 (by simp [same]) } ::
      tripleUp rest noRepeat.tail.tail.tail

/-- Divisibility ensures no vertex is dropped, duplicated, or reordered. -/
theorem tripleUp_vertices {n : ℕ} (vertices : List (Fin n)) (noRepeat : vertices.Nodup)
    (divisible : vertices.length % 3 = 0) : tripleVertices (tripleUp vertices noRepeat) = vertices := by
  cases vertices with
  | nil => rfl
  | cons a tail =>
    cases tail with
    | nil => simp at divisible
    | cons b tail =>
      cases tail with
      | nil => simp at divisible
      | cons c rest =>
        have restDivisible : rest.length % 3 = 0 := by
          simp only [List.length_cons] at divisible
          omega
        change a :: b :: c :: tripleVertices (tripleUp rest noRepeat.tail.tail.tail) =
          a :: b :: c :: rest
        rw [tripleUp_vertices rest noRepeat.tail.tail.tail restDivisible]
termination_by vertices.length

/-- Boundary-order triples: (0,1,2), (3,4,5), and so on. -/
def consecutiveTriples (n : ℕ) : List (VertexTriple n) :=
  tripleUp (List.finRange n) (List.nodup_finRange n)

theorem consecutiveTriples_vertices (n : ℕ) (divisible : n % 3 = 0) :
    tripleVertices (consecutiveTriples n) = List.finRange n := by
  apply tripleUp_vertices
  simpa using divisible

theorem tripleVertices_length {n : ℕ} (triples : List (VertexTriple n)) :
    (tripleVertices triples).length = 3 * triples.length := by
  induction triples with
  | nil => rfl
  | cons t rest inductionHypothesis =>
    change (tripleVertices rest).length + 1 + 1 + 1 = 3 * (rest.length + 1)
    omega

theorem consecutiveTriples_length (n : ℕ) (divisible : n % 3 = 0) :
    (consecutiveTriples n).length = n / 3 := by
  have lengthEquality := congrArg List.length (consecutiveTriples_vertices n divisible)
  rw [tripleVertices_length, List.length_finRange] at lengthEquality
  omega

/-- Complete k=3 algorithm for n divisible by three: every intermediate punch
hits exactly its three fresh vertices; all and only marked vertices are removed;
the final state is well formed; there are n/3 batches; and the total crease count
is at most 3(n/3) = n. This is a uniform O(n) bound, not an optimality claim. -/
theorem Paper.k3_correct_and_linear {n : ℕ} (P : Paper n) (divisible : n % 3 = 0) :
    P.SafeTriples P.initial (consecutiveTriples n) ∧
    AllVerticesPunched P (P.runTriples P.initial (consecutiveTriples n)) ∧
    (P.runTriples P.initial (consecutiveTriples n)).WellFormed P ∧
    (consecutiveTriples n).length = n / 3 ∧
    HasAtMostCreases
      (cumulativeCreases (P.tripleHistory P.initial (consecutiveTriples n))) n := by
  have allIndices := consecutiveTriples_vertices n divisible
  have noRepeat : (tripleVertices (consecutiveTriples n)).Nodup := by
    rw [allIndices]
    exact List.nodup_finRange n
  have covers : ∀ i : Fin n, i ∈ tripleVertices (consecutiveTriples n) := by
    intro i
    rw [allIndices]
    exact List.mem_finRange i
  obtain ⟨safe, complete, wellFormed, count⟩ :=
    P.triples_correct_and_linear (consecutiveTriples n) noRepeat covers
  refine ⟨safe, complete, wellFormed, consecutiveTriples_length n divisible, ?_⟩
  have lengthEquality := congrArg List.length allIndices
  rw [tripleVertices_length, List.length_finRange] at lengthEquality
  rw [lengthEquality] at count
  exact count

end FoldAndPunch
