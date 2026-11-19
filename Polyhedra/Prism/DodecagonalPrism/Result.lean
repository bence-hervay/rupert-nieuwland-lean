import Polyhedra.Prism.DodecagonalPrism.Proof.Optimum
import Polyhedra.Prism.DodecagonalPrism.Proof.Enclosure
import Polyhedra.Prism.DodecagonalPrism.Proof.Theta

/-!
# The dodecagonal prism: the result

The dodecagonal prism is Rupert, and its Nieuwland number and an optimal pose are the one root of
the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`. -/

namespace Nieuwland.Prism.DodecagonalPrism

open Notation

/-- **The dodecagonal prism is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the dodecagonal prism.** The system `system` has exactly one root in its box;
at the root the first variable is the Nieuwland number `ν polyhedron`, which is greater than `1`,
and the variables of `layout` are rotations `R₁`, `R₂` and a translation `t` with which the
polyhedron scaled by `ν polyhedron` fits weakly through itself; no larger copy fits through it
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
  [(1.0306908085885388809262239458457, 1.0306908085885388809262239458458),    -- ν
   (0.5086684053628531542931702989432, 0.5086684053628531542931702989433),    -- R₁ 0 0
   (-0.5086684053628531542931702989433, -0.5086684053628531542931702989432),  -- R₁ 0 1
   (0.694631489907579851263315416005, 0.6946314899075798512633154160051),     -- R₁ 0 2
   (-0.4911786369393645609403908737545, -0.4911786369393645609403908737544),  -- R₁ 1 0
   (0.4911786369393645609403908737544, 0.4911786369393645609403908737545),    -- R₁ 1 1
   (0.7193657576148421253386108407002, 0.7193657576148421253386108407003),    -- R₁ 1 2
   (-0.7071067811865475244008443621049, -0.7071067811865475244008443621048),  -- R₁ 2 0
   (-0.7071067811865475244008443621049, -0.7071067811865475244008443621048),  -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (0.9823572738787291218807817475088, 0.9823572738787291218807817475089),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.1870138670194046933281151045702, 0.1870138670194046933281151045703),    -- R₂ 0 2
   (0.0343781784840785633926421481087, 0.0343781784840785633926421481088),    -- R₂ 1 0
   (0.9829586322416277451936984497777, 0.9829586322416277451936984497778),    -- R₂ 1 1
   (-0.1805836873745390600888733430833, -0.1805836873745390600888733430832),  -- R₂ 1 2
   (-0.1838268949356116938160364737468, -0.1838268949356116938160364737467),  -- R₂ 2 0
   (0.1838268949356116938160364737467, 0.1838268949356116938160364737468),    -- R₂ 2 1
   (0.9656165623044496846044402958859, 0.965616562304449684604440295886),     -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the dodecagonal prism.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
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
    polyEval [1, 0, -4, 0, 1] θ = 0 ∧
      (1.9318516525781365734994863994577 : ℝ) ≤ θ ∧
      θ ≤ (1.9318516525781365734994863994578 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Prism.DodecagonalPrism
