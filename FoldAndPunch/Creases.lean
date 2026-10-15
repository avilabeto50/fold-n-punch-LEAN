import FoldAndPunch.Folding

/-! Geometric crease-count vocabulary and the crease of a single flat-sheet fold.
SecondFoldCreases supplies the piecewise trace for the second fold of stacked paper.
Merely touching the fold axis need not create a crease. -/

noncomputable section
namespace FoldAndPunch

/-- The original points currently on the fold axis. This is a candidate hinge
trace, NOT an assertion that every such point acquires a new crease. -/
def Configuration.hingeTrace (C : Configuration) (f : Fold) : Set Point :=
  {x | x ∈ C.material ∧ C.position x ∈ f.axis}

/-- A nondegenerate straight closed segment, represented as a SET so that
reversing endpoints does not create a different crease. -/
def IsCreaseSegment (s : Set Point) : Prop :=
  ∃ a b : Point, a ≠ b ∧ s = segment ℝ a b

/-- Cumulative crease history on the original sheet. Taking the closure fills
isolated puncture holes, which do not split an existing crease into new ones. -/
def cumulativeCreases (history : List (Set Point)) : Set Point :=
  closure {x | ∃ trace ∈ history, x ∈ trace}

/-- A finite representation by maximal straight segments. Maximality merges
collinear adjoining/overlapping pieces, while crossing creases remain distinct.
The union must equal the entire cumulative geometric crease set. -/
structure CreaseDecomposition (trace : Set Point) where
  segments : Finset (Set Point)
  straight : ∀ s ∈ segments, IsCreaseSegment s
  covers : ∀ x, x ∈ trace ↔ ∃ s ∈ segments, x ∈ s
  maximal : ∀ s ∈ segments, ∀ t, IsCreaseSegment t → s ⊆ t → t ⊆ trace → t = s

/-- A crease-count upper bound requires an actual maximal-segment decomposition.
We do not replace the geometric cost with the number of folding operations. -/
def HasAtMostCreases (trace : Set Point) (bound : ℕ) : Prop :=
  ∃ decomposition : CreaseDecomposition trace, decomposition.segments.card ≤ bound

/-- The crease of a single straight fold of an initially flat sheet:
the fold axis through the INTERIOR material, with its endpoints included.
Tangential contacts alone produce no crease under this convention. This
single-flat-sheet definition is extended to two folds in SecondFoldCreases. -/
def Fold.creaseOn (f : Fold) (sheet : Set Point) : Set Point :=
  closure (interior sheet ∩ (f.axis : Set Point))

end FoldAndPunch
