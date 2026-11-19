import Modules.Check.Number.ThetaRoot
import Polyhedra.Johnson.Disphenocingulum.Proof.FullDim

set_option linter.style.longLine false

/-!
# The disphenocingulum: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Johnson.Disphenocingulum.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [2209/60397977600, 0, -1247/52428800, 0, 9000611/2516582400, 0, 1470301/235929600, 0,
      -251632709/1258291200, 0, -12724537/11796480, 0, -63149653/14745600, 0, -769303/921600, 0,
      3074473/153600, 0, 525053/14400, 0, 95083/3600, 0, 637/75, 0, 1] θ = 0 ∧
      (0.3250029759499702709388900655364 : ℝ) ≤ θ ∧
      θ ≤ (0.3250029759499702709388900655365 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.JohnsonDisphenocingulumDim.root (a := 0.3250029759499702709388900655364) (b := 0.3250029759499702709388900655365) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Johnson.Disphenocingulum.Proof
