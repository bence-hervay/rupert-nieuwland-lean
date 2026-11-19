import Modules.Check.Number.ThetaRoot
import Polyhedra.Johnson.Hebesphenomegacorona.Proof.FullDim

set_option linter.style.longLine false

/-!
# The hebesphenomegacorona: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Johnson.Hebesphenomegacorona.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [729/20552089600, 0, -603/321126400, 0, 435823/11560550400, 0, -637433/1445068800, 0,
      4314871/1156055040, 0, -2194643/90316800, 0, 85548047/722534400, 0, -38449237/90316800, 0,
      156349133/144506880, 0, -758221/470400, 0, 1] θ = 0 ∧
      (0.3529540763371607483505637509522 : ℝ) ≤ θ ∧
      θ ≤ (0.3529540763371607483505637509523 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.JohnsonHebesphenomegacoronaDim.root (a := 0.3529540763371607483505637509522) (b := 0.3529540763371607483505637509523) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Johnson.Hebesphenomegacorona.Proof
