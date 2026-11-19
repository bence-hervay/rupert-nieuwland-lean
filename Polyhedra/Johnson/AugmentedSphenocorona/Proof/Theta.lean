import Modules.Check.Number.ThetaRoot
import Polyhedra.Johnson.AugmentedSphenocorona.Proof.FullDim

set_option linter.style.longLine false

/-!
# The augmented sphenocorona: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Johnson.AugmentedSphenocorona.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [21893041/10485760000, 0, -29434883/491520000, 0, 217315519/368640000, 0,
      -59348687/23040000, 0, 7849427/1280000, 0, -3159839/360000, 0, 694111/90000, 0, -299/75, 0, 1]
      θ = 0 ∧
      (0.864147468128994113735899747097 : ℝ) ≤ θ ∧
      θ ≤ (0.8641474681289941137358997470971 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.JohnsonAugmentedSphenocoronaDim.root (a := 0.864147468128994113735899747097) (b := 0.8641474681289941137358997470971) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Johnson.AugmentedSphenocorona.Proof
