import FoldAndPunch.Geometry

/-! Original paper points are layer labels. Lists are ordered top to bottom.
These are idealized discrete fold operations, not 3D motion certificates. -/

noncomputable section
namespace FoldAndPunch

/-- A raw configuration. `WellFormed` connects the geometric and layer data.
The map is defined even at missing points, but only `material` is paper. -/
structure Configuration where
  material : Set Point
  position : Point → Point
  stack : Point → List Point

/-- Every surviving original point appears exactly once in the stack at its
current location; there are no fictitious layers or points outside the sheet.
This alone does not assert reachability or physical realizability. -/
def Configuration.WellFormed {n : ℕ} (C : Configuration) (P : Paper n) : Prop :=
  C.material ⊆ P.region ∧
  (∀ q, (C.stack q).Nodup) ∧
  ∀ q x, x ∈ C.stack q ↔ x ∈ C.material ∧ C.position x = q

/-- An unfolded sheet with specified surviving material, possibly with holes. -/
def flatConfiguration (material : Set Point) : Configuration := by
  classical
  exact {
    material := material
    position := id
    stack := fun q => if q ∈ material then [q] else []
  }

/-- Start with the whole, unpunched polygon. -/
def Paper.initial {n : ℕ} (P : Paper n) : Configuration :=
  flatConfiguration P.region

/-- Unfold completely while retaining all holes. Crease history is separate. -/
def Configuration.unfold (C : Configuration) : Configuration :=
  flatConfiguration C.material

/-- Turn over the moving stack and place it above or below the stationary one. -/
def placeStack (side : Side) (moving stationary : List Point) : List Point :=
  match side with
  | .top => moving.reverse ++ stationary
  | .bottom => stationary ++ moving.reverse

/-- One all-layer fold. The moving half-plane becomes empty; the stationary
half receives the reflected, reversed stacks. On the axis we keep the old
stack once, avoiding duplication of points fixed by reflection.
This axis convention is part of the idealized model. The algorithms' punch
locations are away from the axis of the final fold. -/
def Configuration.fold (C : Configuration) (f : Fold) : Configuration := by
  classical
  exact {
    material := C.material
    position := fun x => f.pointMap (C.position x)
    stack := fun q =>
      if f.moving q then []
      else if q ∈ f.axis then C.stack q
      else placeStack f.placement (C.stack (f.reflect q)) (C.stack q)
  }

/-- Folds in chronological order, with no intermediate punches or unfolding. -/
def Configuration.foldSequence (C : Configuration) (folds : List Fold) : Configuration :=
  folds.foldl Configuration.fold C

end FoldAndPunch
