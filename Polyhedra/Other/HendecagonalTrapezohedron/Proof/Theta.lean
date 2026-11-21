import Modules.Check.Number.ThetaRoot
import Polyhedra.Other.HendecagonalTrapezohedron.Proof.FullDim

set_option linter.style.longLine false

/-!
# The hendecagonal trapezohedron: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Other.HendecagonalTrapezohedron.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [4707057664/1771561, 0, -5048893440/14641, 0, 218992738304/14641, 0,
      -3981910376448/14641, 0, 2616853364736/1331, 0, -5156253202432/1331, 0, 329090251008/121, 0,
      -8273417472/11, 0, 765225184/11, 0, -16272, 0, 1] θ = 0 ∧
      (0.2814694874282152238043849676342 : ℝ) ≤ θ ∧
      θ ≤ (0.2814694874282152238043849676343 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.TrapezohedronHendecagonalTrapezohedronDim.root (a := 0.2814694874282152238043849676342) (b := 0.2814694874282152238043849676343) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Other.HendecagonalTrapezohedron.Proof
