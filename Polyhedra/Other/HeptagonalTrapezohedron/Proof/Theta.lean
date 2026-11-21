import Modules.Check.Number.ThetaRoot
import Polyhedra.Other.HeptagonalTrapezohedron.Proof.FullDim

set_option linter.style.longLine false

/-!
# The heptagonal trapezohedron: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Other.HeptagonalTrapezohedron.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [64/2401, 0, -256/343, 0, -16/7, 0, 1248/49, 0, -232/7, 0, 8, 0, 1] θ = 0 ∧
      (0.523104455825618528925954386312 : ℝ) ≤ θ ∧
      θ ≤ (0.5231044558256185289259543863121 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.TrapezohedronHeptagonalTrapezohedronDim.root (a := 0.523104455825618528925954386312) (b := 0.5231044558256185289259543863121) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Other.HeptagonalTrapezohedron.Proof
