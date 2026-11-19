import Modules.Check.Number.ThetaRoot
import Polyhedra.Prism.HeptagonalPrism.Proof.FullDim

set_option linter.style.longLine false

/-!
# The heptagonal prism: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Prism.HeptagonalPrism.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [-1/448, 0, 1/16, 0, -1/2, 0, 1] θ = 0 ∧
      (0.2564292158181384748733249040688 : ℝ) ≤ θ ∧
      θ ≤ (0.2564292158181384748733249040689 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.PrismHeptagonalPrismDim.root (a := 0.2564292158181384748733249040688) (b := 0.2564292158181384748733249040689) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Prism.HeptagonalPrism.Proof
