import Polyhedra.Prism.TriangularPrism.Proof.Optimum
import Polyhedra.Prism.TriangularPrism.Proof.Enclosure

/-!
# The triangular prism: the result

The triangular prism is Rupert, and its Nieuwland number and an optimal pose are the one root of the
polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Prism.TriangularPrism

open Notation

/-- **The triangular prism is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the triangular prism.** The system `system` has exactly one root in its box; at
the root the first variable is the Nieuwland number `ν polyhedron`, which is greater than `1`, and
the variables of `layout` are rotations `R₁`, `R₂` and a translation `t` with which the polyhedron
scaled by `ν polyhedron` fits weakly through itself; no larger copy fits through it
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
  [(1.0704662693192697958259095291382, 1.0704662693192697958259095291383),    -- ν
   (-0.1798749689112717566722719403208, -0.1798749689112717566722719403207),  -- R₁ 0 0
   (-0.9836894812689464857436013234103, -0.9836894812689464857436013234102),  -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (0.9836894812689464857436013234102, 0.9836894812689464857436013234103),    -- R₁ 1 0
   (-0.1798749689112717566722719403208, -0.1798749689112717566722719403207),  -- R₁ 1 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 2 2
   (0.3360684480523757713577536231251, 0.3360684480523757713577536231252),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.9418375646700802555599932537322, 0.9418375646700802555599932537323),    -- R₂ 0 2
   (-0.1199166459408478377815146268806, -0.1199166459408478377815146268805),  -- R₂ 1 0
   (0.9918614355650067618534878387319, 0.991861435565006761853487838732),     -- R₂ 1 1
   (0.042788908203193047557452523895, 0.0427889082031930475574525238951),     -- R₂ 1 2
   (-0.9341723589627156964511186235481, -0.934172358962715696451118623548),   -- R₂ 2 0
   (-0.1273220037500350505984710552115, -0.1273220037500350505984710552114),  -- R₂ 2 1
   (0.3333333333333333333333333333333, 0.3333333333333333333333333333334),    -- R₂ 2 2
   (-0.0970146044745894570359082288485, -0.0970146044745894570359082288484),  -- t 0
   (-0.0824564076198017905639717637725, -0.0824564076198017905639717637724)]  -- t 1

/-- **The enclosure of the optimum of the triangular prism.** At the root of `system`, the Nieuwland
number and the entries of the optimal pose lie in the intervals of `enclosure`, and no interval is
wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Prism.TriangularPrism
