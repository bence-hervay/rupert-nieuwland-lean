import Modules.Check.Number.ThetaRoot
import Polyhedra.Archimedean.SnubCubeLaevo.Proof.FullDim

set_option linter.style.longLine false

/-!
# The snub cube laevo: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Archimedean.SnubCubeLaevo.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [-1, -1, -1, 1] θ = 0 ∧
      (1.8392867552141611325518525646532 : ℝ) ≤ θ ∧
      θ ≤ (1.8392867552141611325518525646533 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.ArchimedeanSnubCubeLaevoDim.root (a := 1.8392867552141611325518525646532) (b := 1.8392867552141611325518525646533) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Archimedean.SnubCubeLaevo.Proof
