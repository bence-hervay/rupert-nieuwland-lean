import Modules.Check.Number.ThetaRoot
import Polyhedra.Johnson.ElongatedPentagonalOrthobicupola.Proof.FullDim

set_option linter.style.longLine false

/-!
# The elongated pentagonal orthobicupola: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Johnson.ElongatedPentagonalOrthobicupola.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [1/80, 0, -1/4, 0, 1] θ = 0 ∧
      (0.2628655560595668030128345424239 : ℝ) ≤ θ ∧
      θ ≤ (0.262865556059566803012834542424 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.JohnsonElongatedPentagonalOrthobicupolaDim.root (a := 0.2628655560595668030128345424239) (b := 0.262865556059566803012834542424) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Johnson.ElongatedPentagonalOrthobicupola.Proof
