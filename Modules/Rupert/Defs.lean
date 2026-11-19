import Definitions.Rupertness
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# The Rupert property

A convex polyhedron is *Rupert* if a straight tunnel can be cut through it that is large enough
for a second, congruent copy of it to pass through. Looking along the tunnel, this says: after
rotating the two copies suitably, the shadow of one copy, moved by a translation within the
plane, lies in the **interior** of the shadow of the other copy.

This file states exactly that for the polyhedra of `Definitions/Polyhedra.lean` (the convex hull of
a finite set of points), using Mathlib primitives only.

* Points of space and of the plane are coordinate vectors `Fin 3 → ℝ` and `Fin 2 → ℝ`.
  The plane carries the product topology, which is the Euclidean topology, so `interior` is the
  usual interior of a subset of `ℝ²`.
* A rotation is a matrix in `Matrix.specialOrthogonalGroup (Fin 3) ℝ`, written `SO(3)` below:
  a real `3 × 3` matrix `R` with `R * Rᵀ = 1` and `det R = 1`. It acts on points by
  matrix-vector multiplication `R *ᵥ x`.
* Shadows are taken along the `z`-axis: `projXY` sends `(x, y, z)` to `(x, y)`.

## Main definitions

* `Nieuwland.projXY`: the projection `ℝ³ → ℝ²`, `(x, y, z) ↦ (x, y)`.
* `Nieuwland.Polyhedron.IsRupert P`: the polyhedron `P` is Rupert.

## Remarks on the formulation

* Strictness is essential: the moved shadow must lie in the *interior* of the other shadow.
  Weak containment, a closure or a numerical tolerance would be a different statement.
* The translation `t` acts in the plane, after projecting. Translating by a vector of `ℝ³` before
  projecting gives the same property, because `projXY` is linear and onto
  (`Polyhedron.isRupert_iff_exists_translate`).
* Both copies are rotated. `R₂` chooses the direction of the tunnel through the outer copy
  (it is `R₂ᵀ e_z` in the coordinates of `P`), and `R₁` is the attitude of the inner copy.
  Allowing all orthogonal matrices would not change the property: replacing `R` by
  `diag(1, 1, -1) * R` flips the sign of `det R` and leaves every shadow unchanged
  (`Polyhedron.isRupert_iff_orthogonal`).
* No full-dimensionality is built in. Polyhedra whose points do not span `ℝ³` behave degenerately:
  with no points, `IsRupert` holds vacuously; a segment is never Rupert, because its shadows have
  empty interior; and a flat convex polygon is Rupert (a copy seen edge-on passes through a copy
  seen face-on). Results about particular polyhedra concern full-dimensional ones.

## Relation to the project's formulation

`RESEARCH.md` (§1.1, statement (1)) asks, for `K` the convex hull of finitely many points that
span `ℝ³`, whether

  `∃ u ≠ 0, ∃ R ∈ SO(3), ∃ τ ∈ u^⊥, π_u (R K) + τ ⊆ int π_u K`,

where `π_u` is the orthogonal projection onto the plane `u^⊥` and the interior is taken in that
plane. For `K = P.hull` this is equivalent to `P.IsRupert`, by turning `u` to the `z`-axis.
Given a witness `(R₁, R₂, t)` of `P.IsRupert`, take `u = R₂ᵀ e_z`, `R = R₂ᵀ R₁` and
`τ = R₂ᵀ (t₀, t₁, 0)`. Conversely, choose `Q ∈ SO(3)` with `Q u` a multiple of `e_z` and take
`R₁ = Q R`, `R₂ = Q` and `t = projXY (Q τ)`. This equivalence is
`Polyhedron.isRupert_iff_orthProj` (`Modules/Rupert/Projection.lean`).
-/

open Matrix

namespace Nieuwland

/-! ### Checks of the conventions

These only confirm what the primitives above mean; they contain no mathematics. -/

-- `projXY` forgets the `z`-coordinate.
example (x y z : ℝ) : projXY ![x, y, z] = ![x, y] := rfl

-- Mathlib's `SO(3)` is what it should be: `R * Rᵀ = 1` and `det R = 1`.
example (R : Matrix (Fin 3) (Fin 3) ℝ) : R ∈ SO(3) ↔ R * Rᵀ = 1 ∧ R.det = 1 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]

-- The plane carries the product topology.
example : (inferInstance : TopologicalSpace (Fin 2 → ℝ)) = Pi.topologicalSpace := rfl

end Nieuwland
