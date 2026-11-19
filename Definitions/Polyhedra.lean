import Mathlib.Analysis.Convex.Hull
import Mathlib.Basic.Real.Basic

/-!
# Convex polyhedra

A convex polyhedron in `ℝ³` is given by finitely many points; the polyhedron is their convex
hull. Points of space are coordinate vectors `Fin 3 → ℝ`.
-/

namespace Nieuwland

/-- A convex polyhedron in `ℝ³`, given by a finite set of points. The polyhedron is their convex
hull, `Polyhedron.hull`. -/
structure Polyhedron where
  /-- The given points. Every vertex of the polyhedron is one of them. -/
  vertices : Finset (Fin 3 → ℝ)

/-- The polyhedron `P` as a subset of `ℝ³`: the convex hull of its vertices. -/
def Polyhedron.hull (P : Polyhedron) : Set (Fin 3 → ℝ) :=
  convexHull ℝ (P.vertices : Set (Fin 3 → ℝ))

open Classical in
/-- The polyhedron `P` scaled by `c`: its points times `c`. -/
noncomputable def Polyhedron.smul (c : ℝ) (P : Polyhedron) : Polyhedron where
  vertices := P.vertices.image (c • ·)

end Nieuwland
