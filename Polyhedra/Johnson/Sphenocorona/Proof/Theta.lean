import Modules.Check.Number.ThetaRoot
import Polyhedra.Johnson.Sphenocorona.Proof.FullDim

set_option linter.style.longLine false

/-!
# The sphenocorona: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Johnson.Sphenocorona.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [1/16, 0, -1/150, 0, -397/450, 0, -2/75, 0, 1] θ = 0 ∧
      (0.9571999001908927793900379941935 : ℝ) ≤ θ ∧
      θ ≤ (0.9571999001908927793900379941936 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.JohnsonSphenocoronaDim.root (a := 0.9571999001908927793900379941935) (b := 0.9571999001908927793900379941936) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Johnson.Sphenocorona.Proof
