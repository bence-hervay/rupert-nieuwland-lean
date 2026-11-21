import Modules.Check.Number.ThetaRoot
import Polyhedra.Other.DodecagonalTrapezohedron.Proof.FullDim

set_option linter.style.longLine false

/-!
# The dodecagonal trapezohedron: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Other.DodecagonalTrapezohedron.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [-2, 0, 76, 0, -858, 0, 2944, 0, 1] θ = 0 ∧
      (0.2196217310926713836654950026825 : ℝ) ≤ θ ∧
      θ ≤ (0.2196217310926713836654950026826 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.TrapezohedronDodecagonalTrapezohedronDim.root (a := 0.2196217310926713836654950026825) (b := 0.2196217310926713836654950026826) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Other.DodecagonalTrapezohedron.Proof
