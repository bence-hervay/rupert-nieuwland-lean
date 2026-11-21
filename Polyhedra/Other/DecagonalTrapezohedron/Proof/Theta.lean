import Modules.Check.Number.ThetaRoot
import Polyhedra.Other.DecagonalTrapezohedron.Proof.FullDim

set_option linter.style.longLine false

/-!
# The decagonal trapezohedron: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Other.DecagonalTrapezohedron.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [25, 0, -450, 0, 1090, 0, 1330, 0, 1] θ = 0 ∧
      (0.2598101265935449922378604153267 : ℝ) ≤ θ ∧
      θ ≤ (0.2598101265935449922378604153268 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.TrapezohedronDecagonalTrapezohedronDim.root (a := 0.2598101265935449922378604153267) (b := 0.2598101265935449922378604153268) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Other.DecagonalTrapezohedron.Proof
