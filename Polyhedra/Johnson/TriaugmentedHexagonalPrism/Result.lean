import Polyhedra.Johnson.TriaugmentedHexagonalPrism.Proof.Optimum
import Polyhedra.Johnson.TriaugmentedHexagonalPrism.Proof.Enclosure
import Polyhedra.Johnson.TriaugmentedHexagonalPrism.Proof.Theta

/-!
# The triaugmented hexagonal prism: the result

The triaugmented hexagonal prism is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.TriaugmentedHexagonalPrism

open Notation

/-- **The triaugmented hexagonal prism is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the triaugmented hexagonal prism.** The system `system` has exactly one root in
its box; at the root the first variable is the Nieuwland number `ν polyhedron`, which is greater
than `1`, and the variables of `layout` are rotations `R₁`, `R₂` and a translation `t` with which
the polyhedron scaled by `ν polyhedron` fits weakly through itself; no larger copy fits through it
(`Polyhedron.IsOptimum`, `Definitions/Optimum.lean`). -/
theorem isOptimum : polyhedron.IsOptimum system layout :=
  Proof.isOptimum

/-- The system has exactly one root in its box (a part of `isOptimum`). -/
theorem hasUniqueRoot : system.HasUniqueRoot :=
  isOptimum.uniqueRoot

/-- The Nieuwland number is greater than `1` (a part of `isOptimum`). -/
theorem one_lt_nieuwland : 1 < ν polyhedron :=
  isOptimum.one_lt

/-- Rational intervals for the optimum: for the Nieuwland number `ν` and for the entries of an
optimal pose, the plug's rotation `R₁`, the hole's rotation `R₂` and the translation `t` (the
variables of `layout`, in the order of `PoseLayout.variables`). -/
def enclosure : List (ℚ × ℚ) :=
  [(1.0199597794971351862432807542894, 1.0199597794971351862432807542895),    -- ν
   (0.7552017846006993349124714420838, 0.7552017846006993349124714420839),    -- R₁ 0 0
   (0.4360159536316995343634175925213, 0.4360159536316995343634175925214),    -- R₁ 0 1
   (-0.4894490297411555463250669660339, -0.4894490297411555463250669660338),  -- R₁ 0 2
   (0.4238752936134859522418206404119, 0.423875293613485952241820640412),     -- R₁ 1 0
   (0.2447245148705777731625334830169, 0.244724514870577773162533483017),     -- R₁ 1 1
   (0.8720319072633990687268351850426, 0.8720319072633990687268351850427),    -- R₁ 1 2
   (0.4999999999999999999999999999999, 0.5000000000000000000000000000001),    -- R₁ 2 0
   (-0.866025403784438646763723170753, -0.8660254037844386467637231707529),   -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (0.9858408119706242994495191141298, 0.9858408119706242994495191141299),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.1676839093446362401054020551745, 0.1676839093446362401054020551746),    -- R₂ 0 2
   (-0.0182196246429800345011109353781, -0.018219624642980034501110935378),   -- R₂ 1 0
   (0.9940795654142202529500047678082, 0.9940795654142202529500047678083),    -- R₂ 1 1
   (0.1071161187858480603626110357733, 0.1071161187858480603626110357734),    -- R₂ 1 2
   (-0.166691147728273499991594520745, -0.1666911477282734999915945207449),   -- R₂ 2 0
   (-0.1086545794059090594341081789743, -0.1086545794059090594341081789742),  -- R₂ 2 1
   (0.9800042059313602268781177860207, 0.9800042059313602268781177860208),    -- R₂ 2 2
   (-0.0561203652687545253256275608075, -0.0561203652687545253256275608074),  -- t 0
   (-0.0282490485341672516208540517072, -0.0282490485341672516208540517071)]  -- t 1

/-- **The enclosure of the optimum of the triaugmented hexagonal prism.** At the root of `system`,
the Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

@[inherit_doc] local notation "θ" => theta

/-- **`θ` is a root of its polynomial**, and it lies between these two rationals, which are at most
`2 ^ -100` apart. -/
theorem theta_isRoot :
    polyEval [1/256, 0, -5/8, 0, 1] θ = 0 ∧
      (0.7865660924854930855822837664288 : ℝ) ≤ θ ∧
      θ ≤ (0.7865660924854930855822837664289 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.TriaugmentedHexagonalPrism
