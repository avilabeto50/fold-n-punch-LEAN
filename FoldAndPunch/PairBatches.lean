import FoldAndPunch.PunchingLemmas

/-!
Concrete successive pair operations and their safety/material/history invariant.
Each operation folds, punches from the top, and completely unfolds.
-/

noncomputable section
open Set
namespace FoldAndPunch

/-- One pair of distinct vertex indices. -/
structure VertexPair (n : ℕ) where
  first : Fin n
  second : Fin n
  distinct : first ≠ second

/-- Original vertex indices in chronological punching order. -/
def pairVertices {n : ℕ} (pairs : List (VertexPair n)) : List (Fin n) :=
  pairs.flatMap (fun p => [p.first, p.second])

/-- The original points selected by a list of pairs. -/
def Paper.pairPoints {n : ℕ} (P : Paper n) (pairs : List (VertexPair n)) : Set Point :=
  {x | ∃ i ∈ pairVertices pairs, x = P.polygon.vertices i}

/-- Every batch uses the overfold version; punch from the top and unfold. -/
def Paper.doPair {n : ℕ} (P : Paper n) (C : Configuration) (p : VertexPair n) : Configuration :=
  ((C.fold (P.pairFold p.first p.second p.distinct .top)).punch
    2 .top (P.polygon.vertices p.second)).unfold

def Paper.runPairs {n : ℕ} (P : Paper n) (C : Configuration) :
    List (VertexPair n) → Configuration
  | [] => C
  | p :: rest => P.runPairs (P.doPair C p) rest

/-- Actual crease trace of each fold on the material present at that step. -/
def Paper.pairHistory {n : ℕ} (P : Paper n) (C : Configuration) :
    List (VertexPair n) → List (Set Point)
  | [] => []
  | p :: rest =>
    (P.pairFold p.first p.second p.distinct .top).creaseOn C.material ::
      P.pairHistory (P.doPair C p) rest

/-- Every individual punch, in its actual intermediate configuration, is safe. -/
def Paper.SafePairs {n : ℕ} (P : Paper n) (C : Configuration) :
    List (VertexPair n) → Prop
  | [] => True
  | p :: rest =>
    SuccessfulPunch P (C.fold (P.pairFold p.first p.second p.distinct .top))
      2 {p.first, p.second} .top (P.polygon.vertices p.second) ∧
    P.SafePairs (P.doPair C p) rest

/-- The full chord associated with a pair, before accounting for earlier holes. -/
def Paper.pairChord {n : ℕ} (P : Paper n) (p : VertexPair n) : Set Point :=
  (P.pairFold p.first p.second p.distinct .top).creaseOn P.region


/-- Run a disjoint list of fresh pairs, starting with holes only at marked points.
Every step is safe, the final material is exact, and every recorded crease is
its original full chord, regardless of the earlier punches. -/
theorem Paper.runPairs_spec {n : ℕ} (P : Paper n) (pairs : List (VertexPair n))
    (noRepeat : (pairVertices pairs).Nodup) (holes : Set Point)
    (onlyMarked : holes ⊆ P.marked)
    (fresh : ∀ i ∈ pairVertices pairs, P.polygon.vertices i ∉ holes) :
    P.SafePairs (flatConfiguration (P.region \ holes)) pairs ∧
    P.runPairs (flatConfiguration (P.region \ holes)) pairs =
      flatConfiguration (P.region \ (holes ∪ P.pairPoints pairs)) ∧
    P.pairHistory (flatConfiguration (P.region \ holes)) pairs =
      pairs.map P.pairChord := by
  classical
  induction pairs generalizing holes with
  | nil =>
    simp [Paper.SafePairs, Paper.runPairs, Paper.pairHistory, Paper.pairPoints, pairVertices]
  | cons p rest inductionHypothesis =>
    change (p.first :: p.second :: pairVertices rest).Nodup at noRepeat
    have firstFresh : P.polygon.vertices p.first ∉ holes := by
      apply fresh
      simp [pairVertices]
    have secondFresh : P.polygon.vertices p.second ∉ holes := by
      apply fresh
      simp [pairVertices]
    have firstPresent : P.polygon.vertices p.first ∈ P.region \ holes := by
      refine ⟨?_, firstFresh⟩
      apply subset_convexHull ℝ
      exact ⟨p.first, rfl⟩
    have secondPresent : P.polygon.vertices p.second ∈ P.region \ holes := by
      refine ⟨?_, secondFresh⟩
      apply subset_convexHull ℝ
      exact ⟨p.second, rfl⟩
    let newHoles := holes ∪ {P.polygon.vertices p.first, P.polygon.vertices p.second}
    have newOnlyMarked : newHoles ⊆ P.marked := by
      intro x hx
      rcases hx with old | pair
      · exact onlyMarked old
      · rcases pair with rfl | rfl
        · exact ⟨p.first, rfl⟩
        · exact ⟨p.second, rfl⟩
    have remainingFresh : ∀ i ∈ pairVertices rest, P.polygon.vertices i ∉ newHoles := by
      intro i hi removed
      rcases removed with old | pair
      · apply fresh i _ old
        change i ∈ p.first :: p.second :: pairVertices rest
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hi)
      · rcases pair with first | second
        · have same := P.vertices_injective first
          subst i
          exact (List.nodup_cons.mp noRepeat).1 (by simp [hi])
        · have same := P.vertices_injective second
          subst i
          exact (List.nodup_cons.mp noRepeat.tail).1 hi
    have afterPair : P.doPair (flatConfiguration (P.region \ holes)) p =
        flatConfiguration (P.region \ newHoles) := by
      calc
        P.doPair (flatConfiguration (P.region \ holes)) p =
            flatConfiguration ((P.region \ holes) \
              {P.polygon.vertices p.first, P.polygon.vertices p.second}) := by
          exact flat_pair_punch_unfold (P.region \ holes)
            (P.pairFold p.first p.second p.distinct .top) firstPresent secondPresent
        _ = flatConfiguration (P.region \ newHoles) := by
          apply congrArg flatConfiguration
          ext x
          simp [newHoles, and_assoc, and_comm]
    obtain ⟨remainingSafe, remainingMaterial, remainingHistory⟩ :=
      inductionHypothesis noRepeat.tail.tail newHoles newOnlyMarked remainingFresh
    refine ⟨?_, ?_, ?_⟩
    · constructor
      · exact P.pairFold_successful (P.region \ holes) Set.sdiff_subset
          p.first p.second p.distinct firstPresent secondPresent .top
      · rw [afterPair]
        exact remainingSafe
    · rw [Paper.runPairs, afterPair, remainingMaterial]
      apply congrArg flatConfiguration
      ext x
      simp [newHoles, Paper.pairPoints, pairVertices, or_and_right, exists_or, or_assoc, and_left_comm, and_comm]
    · rw [Paper.pairHistory, afterPair, remainingHistory]
      change _ :: rest.map P.pairChord = P.pairChord p :: rest.map P.pairChord
      congr 1
      exact P.creaseOn_remove_marked holes onlyMarked _


end FoldAndPunch
