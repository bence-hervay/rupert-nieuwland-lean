import Modules.Check.Number.ThetaRoot
import Polyhedra.Catalan.PentagonalIcositetrahedronLaevo.Proof.FullDim

set_option linter.style.longLine false

/-!
# The pentagonal icositetrahedron laevo: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Catalan.PentagonalIcositetrahedronLaevo.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [-1, -1, -3, 1] θ = 0 ∧
      (3.382975767906237494122708536455 : ℝ) ≤ θ ∧
      θ ≤ (3.3829757679062374941227085364551 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.CatalanPentagonalIcositetrahedronLaevoDim.root (a := 3.382975767906237494122708536455) (b := 3.3829757679062374941227085364551) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Catalan.PentagonalIcositetrahedronLaevo.Proof
