import Modules.Check.Number.ThetaRoot
import Polyhedra.Other.Noperthedron.Proof.FullDim

set_option linter.style.longLine false

/-!
# The Noperthedron: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Other.Noperthedron.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [1, 0, -8, 0, 14, 0, -7, 0, 1] θ = 0 ∧
      (1.9890437907365466738453838899611 : ℝ) ≤ θ ∧
      θ ≤ (1.9890437907365466738453838899612 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.ExternalNoperthedronDim.root (a := 1.9890437907365466738453838899611) (b := 1.9890437907365466738453838899612) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Other.Noperthedron.Proof
