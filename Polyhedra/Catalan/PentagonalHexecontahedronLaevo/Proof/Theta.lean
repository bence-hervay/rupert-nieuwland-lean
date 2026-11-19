import Modules.Check.Number.ThetaRoot
import Polyhedra.Catalan.PentagonalHexecontahedronLaevo.Proof.FullDim

set_option linter.style.longLine false

/-!
# The pentagonal hexecontahedron laevo: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Catalan.PentagonalHexecontahedronLaevo.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [1, -2, -1, 0, -2, 2, 1] θ = 0 ∧
      (1.1326619649523854202571098116849 : ℝ) ≤ θ ∧
      θ ≤ (1.132661964952385420257109811685 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.CatalanPentagonalHexecontahedronLaevoDim.root (a := 1.1326619649523854202571098116849) (b := 1.132661964952385420257109811685) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Catalan.PentagonalHexecontahedronLaevo.Proof
