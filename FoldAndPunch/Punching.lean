import FoldAndPunch.Folding

/-! A depth limit selects an exposed prefix, not an arbitrary subset of layers.
Successful punches must remove exactly the chosen, previously unpunched vertices. -/

noncomputable section
namespace FoldAndPunch

/-- Layers in the order encountered by a punch from the specified side. -/
def Configuration.layersFrom (C : Configuration) (side : Side) (q : Point) : List Point :=
  match side with
  | .top => C.stack q
  | .bottom => (C.stack q).reverse

/-- Material actually hit. If fewer than k layers exist, fewer are hit;
`SuccessfulPunch` below rules this out for an exactly-k operation. -/
def Configuration.punchHits (C : Configuration) (k : ℕ) (side : Side)
    (q : Point) : List Point :=
  (C.layersFrom side q).take k

/-- Remove the hit ORIGINAL points. Other layers at the punch position survive.
Filtering every stack ensures a missing original point cannot reappear later. -/
def Configuration.punch (C : Configuration) (k : ℕ) (side : Side)
    (q : Point) : Configuration := by
  classical
  let hits := C.punchHits k side q
  exact {
    material := {x | x ∈ C.material ∧ x ∉ hits}
    position := C.position
    stack := fun y => (C.stack y).filter (fun x => x ∉ hits)
  }

/-- Exactly k fresh target vertices are punched, and no other point is hit.
Well-formedness makes list membership refer to actual surviving paper. -/
def SuccessfulPunch {n : ℕ} (P : Paper n) (C : Configuration)
    (k : ℕ) (batch : Finset (Fin n)) (side : Side) (q : Point) : Prop :=
  0 < k ∧
  C.WellFormed P ∧
  batch.card = k ∧
  (∀ i ∈ batch, P.polygon.vertices i ∈ C.material) ∧
  (C.punchHits k side q).length = k ∧
  ∀ x, x ∈ C.punchHits k side q ↔ ∃ i ∈ batch, x = P.polygon.vertices i

/-- The final goal: every marked point is gone and every unmarked point remains. -/
def AllVerticesPunched {n : ℕ} (P : Paper n) (C : Configuration) : Prop :=
  C.material = P.region \ P.marked

/-- A partition into batches of exactly k vertices, each vertex appearing once.
The baseline algorithm can choose consecutive batches; correctness need not
restrict attention to that choice. Divisibility follows from a valid partition. -/
structure Batching (n k : ℕ) where
  batches : List (Finset (Fin n))
  positive_depth : 0 < k
  batch_size : ∀ b ∈ batches, b.card = k
  disjoint : batches.Pairwise Disjoint
  covers : ∀ i : Fin n, ∃ b ∈ batches, i ∈ b

end FoldAndPunch
