import Definitions.Polyhedra
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Fitting through, Rupert polyhedra and the Nieuwland number

A polyhedron is looked at along the `z`-axis: its shadow is its orthogonal projection onto the
`xy`-plane. Turning the polyhedron first shows it from any other direction.

`plug` fits through `hole` when some shadow of `plug`, moved within the plane, lies strictly inside
some shadow of `hole`: a straight tunnel with that shadow can be cut through `hole`, and `plug`
passes through it. A polyhedron is Rupert when it fits through itself, and a Nopert when it does
not. Its Nieuwland number `ν P` measures how much room the passage leaves: it is the supremum of
the scales `c` at which the copy `c P` fits through `P`. A Rupert polyhedron has `ν P > 1`; a
Nopert has `ν P = 1`.
-/

open Matrix

namespace Nieuwland

/-- `SO(3)`, the rotations of `ℝ³`: the real `3 × 3` matrices `R` with `R * Rᵀ = 1` and
`det R = 1`. -/
scoped notation "SO(3)" => Matrix.specialOrthogonalGroup (Fin 3) ℝ

/-- The orthogonal projection of `ℝ³` onto the `xy`-plane, `(x, y, z) ↦ (x, y)`: it sends a point
to its shadow seen along the `z`-axis. -/
def projXY (p : Fin 3 → ℝ) : Fin 2 → ℝ :=
  ![p 0, p 1]

/-- `plug` **fits through** `hole`: there are rotations `R₁, R₂ ∈ SO(3)` and a translation
`t ∈ ℝ²` such that the shadow of `R₁ plug`, moved by `t`, lies in the interior of the shadow of
`R₂ hole`. -/
def Polyhedron.FitsThrough (plug hole : Polyhedron) : Prop :=
  ∃ R₁ ∈ SO(3), ∃ R₂ ∈ SO(3), ∃ t : Fin 2 → ℝ,
    {projXY (R₁ *ᵥ x) + t | x ∈ plug.hull} ⊆ interior {projXY (R₂ *ᵥ x) | x ∈ hole.hull}

/-- A polyhedron `P` is **Rupert** if it fits through itself. -/
def Polyhedron.IsRupert (P : Polyhedron) : Prop :=
  P.FitsThrough P

/-- A polyhedron is a **Nopert** if it is not Rupert. -/
def Polyhedron.IsNopert (P : Polyhedron) : Prop :=
  ¬ P.IsRupert

/-- The **Nieuwland number** of `P`: the supremum of the scales `c > 0` such that `P` scaled by
`c` fits through `P`. -/
noncomputable def Polyhedron.nieuwland (P : Polyhedron) : ℝ :=
  sSup {c : ℝ | 0 < c ∧ (P.smul c).FitsThrough P}

/-- `ν P`: the Nieuwland number of `P` (`open Nieuwland.Notation`). -/
scoped[Nieuwland.Notation] notation "ν " P:max => Nieuwland.Polyhedron.nieuwland P

end Nieuwland
