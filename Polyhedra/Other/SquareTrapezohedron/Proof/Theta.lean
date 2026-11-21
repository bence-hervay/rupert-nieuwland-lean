import Modules.Check.Number.ThetaRoot
import Polyhedra.Other.SquareTrapezohedron.Proof.FullDim

set_option linter.style.longLine false

/-!
# The square trapezohedron: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Other.SquareTrapezohedron.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [-2, 0, 8, 0, 1] θ = 0 ∧
      (0.4925857155047080193447509819059 : ℝ) ≤ θ ∧
      θ ≤ (0.492585715504708019344750981906 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.TrapezohedronSquareTrapezohedronDim.root (a := 0.4925857155047080193447509819059) (b := 0.492585715504708019344750981906) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Other.SquareTrapezohedron.Proof
