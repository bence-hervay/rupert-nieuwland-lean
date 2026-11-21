import Modules.Check.Number.ThetaRoot
import Polyhedra.Other.PentagonalTrapezohedron.Proof.FullDim

set_option linter.style.longLine false

/-!
# The pentagonal trapezohedron: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Other.PentagonalTrapezohedron.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [-4/25, 8/5, -12/5, 0, 1] θ = 0 ∧
      (0.7721332917328642654377061459613 : ℝ) ≤ θ ∧
      θ ≤ (0.7721332917328642654377061459614 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.TrapezohedronPentagonalTrapezohedronDim.root (a := 0.7721332917328642654377061459613) (b := 0.7721332917328642654377061459614) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Other.PentagonalTrapezohedron.Proof
