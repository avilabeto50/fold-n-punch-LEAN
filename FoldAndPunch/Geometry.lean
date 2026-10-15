import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Polygon.Basic
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Geometry.Euclidean.Projection

/-! Basic geometry for convex-paper fold and punch. Reuse Mathlib geometry;
only the problem-specific input conditions and oriented fold are new. -/

noncomputable section
namespace FoldAndPunch

abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- A genuine convex polygon whose listed vertices are exactly its corners.
The boundary condition requires cyclic boundary order (either orientation).
Both algorithms work in either orientation, so clockwise is not singled out. -/
structure Paper (n : ℕ) where
  polygon : Polygon Point n
  at_least_three : 3 ≤ n
  vertices_injective : Function.Injective polygon.vertices
  interior_nonempty : (interior (convexHull ℝ (Set.range polygon.vertices))).Nonempty
  vertices_are_corners : Set.range polygon.vertices =
    (convexHull ℝ (Set.range polygon.vertices)).extremePoints ℝ
  boundary_order : polygon.boundary ℝ =
    frontier (convexHull ℝ (Set.range polygon.vertices))

/-- The filled sheet, including its boundary. -/
def Paper.region {n : ℕ} (P : Paper n) : Set Point :=
  convexHull ℝ (Set.range P.polygon.vertices)

/-- The original locations of all marked points. -/
def Paper.marked {n : ℕ} (P : Paper n) : Set Point :=
  Set.range P.polygon.vertices

/-- Side of a stack: also specifies where a moving stack is placed. -/
inductive Side where
  | top
  | bottom
  deriving DecidableEq, Repr

/-- An oriented fold specified by two distinct CURRENT locations.
Its axis is their perpendicular bisector; the source side moves onto the target
side. These witnesses specify a line, not necessarily two marked points. -/
structure Fold where
  source : Point
  target : Point
  distinct : source ≠ target
  placement : Side

/-- Mathlib's affine perpendicular bisector. -/
def Fold.axis (f : Fold) : AffineSubspace ℝ Point :=
  AffineSubspace.perpBisector f.source f.target

/-- Points strictly on the moving side; axis points remain stationary. -/
def Fold.moving (f : Fold) (x : Point) : Prop :=
  dist x f.source < dist x f.target

/-- Mathlib's Euclidean reflection, rather than a new coordinate formula. -/
def Fold.reflect (f : Fold) : Point ≃ᵃⁱ[ℝ] Point := by
  letI : Nonempty f.axis :=
    AffineSubspace.perpBisector_nonempty.to_subtype
  exact EuclideanGeometry.reflection f.axis

/-- The geometric effect of folding one whole half-plane. -/
def Fold.pointMap (f : Fold) (x : Point) : Point := by
  classical
  exact if f.moving x then f.reflect x else x

end FoldAndPunch
