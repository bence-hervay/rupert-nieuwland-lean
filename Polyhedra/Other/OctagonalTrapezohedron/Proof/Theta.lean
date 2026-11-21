import Modules.Check.Number.ThetaRoot
import Polyhedra.Other.OctagonalTrapezohedron.Proof.FullDim

set_option linter.style.longLine false

/-!
# The octagonal trapezohedron: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Other.OctagonalTrapezohedron.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [-2, 0, 40, 0, -248, 0, 480, 0, 1] θ = 0 ∧
      (0.3161948661519344012820893758066 : ℝ) ≤ θ ∧
      θ ≤ (0.3161948661519344012820893758067 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.TrapezohedronOctagonalTrapezohedronDim.root (a := 0.3161948661519344012820893758066) (b := 0.3161948661519344012820893758067) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Other.OctagonalTrapezohedron.Proof
