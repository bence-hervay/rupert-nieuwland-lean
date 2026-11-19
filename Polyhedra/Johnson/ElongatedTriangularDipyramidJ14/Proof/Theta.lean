import Modules.Check.Number.ThetaRoot
import Polyhedra.Johnson.ElongatedTriangularDipyramidJ14.Proof.FullDim

set_option linter.style.longLine false

/-!
# The elongated triangular dipyramid j14: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Johnson.ElongatedTriangularDipyramidJ14.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [1/36, 1, 0, -2, 1] θ = 0 ∧
      (1.6051717155225389149870024151529 : ℝ) ≤ θ ∧
      θ ≤ (1.605171715522538914987002415153 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.JohnsonElongatedTriangularDipyramidJ14Dim.root (a := 1.6051717155225389149870024151529) (b := 1.605171715522538914987002415153) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Johnson.ElongatedTriangularDipyramidJ14.Proof
