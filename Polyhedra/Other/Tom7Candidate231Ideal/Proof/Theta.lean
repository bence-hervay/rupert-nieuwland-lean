import Modules.Check.Number.ThetaRoot
import Polyhedra.Other.Tom7Candidate231Ideal.Proof.FullDim

set_option linter.style.longLine false

/-!
# The candidate 231 of Tom 7 (ideal coordinates): the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Other.Tom7Candidate231Ideal.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [5/16, 0, -5/4, 0, 1] θ = 0 ∧
      (0.9510565162951535721164393333793 : ℝ) ≤ θ ∧
      θ ≤ (0.9510565162951535721164393333794 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.ExternalTom7Candidate231IdealDim.root (a := 0.9510565162951535721164393333793) (b := 0.9510565162951535721164393333794) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Other.Tom7Candidate231Ideal.Proof
