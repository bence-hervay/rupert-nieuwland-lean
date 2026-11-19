import Modules.Check.Number.ThetaRoot
import Polyhedra.Archimedean.SnubDodecahedronLaevo.Proof.FullDim

set_option linter.style.longLine false

/-!
# The snub dodecahedron laevo: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Archimedean.SnubDodecahedronLaevo.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [-1, 2, 4, -1, -4, 0, 1] θ = 0 ∧
      (1.7155614996973678346812788888899 : ℝ) ≤ θ ∧
      θ ≤ (1.71556149969736783468127888889 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.ArchimedeanSnubDodecahedronLaevoDim.root (a := 1.7155614996973678346812788888899) (b := 1.71556149969736783468127888889) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Archimedean.SnubDodecahedronLaevo.Proof
