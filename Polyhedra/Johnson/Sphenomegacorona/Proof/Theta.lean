import Modules.Check.Number.ThetaRoot
import Polyhedra.Johnson.Sphenomegacorona.Proof.FullDim

set_option linter.style.longLine false

/-!
# The sphenomegacorona: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Johnson.Sphenomegacorona.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [49/849346560000, 0, -1/147456000, 0, 42983/130056192000, 0, -1472929/162570240000, 0,
      5255653/32514048000, 0, -41173973/20321280000, 0, 188580733/10160640000, 0,
      -21411977/169344000, 0, 3266781419/5080320000, 0, -4752067/1960000, 0, 351820103/52920000, 0,
      -504078991/39690000, 0, 604136401/39690000, 0, -2618923/330750, 0, -599/175, 0, 3172/735, 0,
      1] θ = 0 ∧
      (0.1821041544594690311588087966257 : ℝ) ≤ θ ∧
      θ ≤ (0.1821041544594690311588087966258 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.JohnsonSphenomegacoronaDim.root (a := 0.1821041544594690311588087966257) (b := 0.1821041544594690311588087966258) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Johnson.Sphenomegacorona.Proof
