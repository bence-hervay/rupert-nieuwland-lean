import Polyhedra.Prism.HeptagonalPrism.Proof.Optimum
import Polyhedra.Prism.HeptagonalPrism.Proof.Enclosure
import Polyhedra.Prism.HeptagonalPrism.Proof.Theta

/-!
# The heptagonal prism: the result

The heptagonal prism is Rupert, and its Nieuwland number and an optimal pose are the one root of the
polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Prism.HeptagonalPrism

open Notation

/-- **The heptagonal prism is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the heptagonal prism.** The system `system` has exactly one root in its box; at
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
  [(1.0067963129073993291453446305484, 1.0067963129073993291453446305485),    -- ν
   (-0.7818314824680298087084445266741, -0.781831482468029808708444526674),   -- R₁ 0 0
   (0.6234898018587335305250048840042, 0.6234898018587335305250048840043),    -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 1
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 1 2
   (0.6234898018587335305250048840042, 0.6234898018587335305250048840043),    -- R₁ 2 0
   (0.781831482468029808708444526674, 0.7818314824680298087084445266741),     -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (-0.6234898018587335305250048840043, -0.6234898018587335305250048840042),  -- R₂ 0 0
   (0.781831482468029808708444526674, 0.7818314824680298087084445266741),     -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.0906900973740661915783971864819, 0.090690097374066191578397186482),     -- R₂ 1 0
   (0.0723229392909717703183319862903, 0.0723229392909717703183319862904),    -- R₂ 1 1
   (0.9932495651600340892983722000989, 0.993249565160034089298372200099),     -- R₂ 1 2
   (0.7765537799897954231882631395377, 0.7765537799897954231882631395378),    -- R₂ 2 0
   (0.6192809745779028932721602738312, 0.6192809745779028932721602738313),    -- R₂ 2 1
   (-0.115996988363505351021244897017, -0.1159969883635053510212448970169),   -- R₂ 2 2
   (-0.0574486721152943455817480476435, -0.0574486721152943455817480476434),  -- t 0
   (-0.0259860778504511025013988504786, -0.0259860778504511025013988504785)]  -- t 1

/-- **The enclosure of the optimum of the heptagonal prism.** At the root of `system`, the Nieuwland
number and the entries of the optimal pose lie in the intervals of `enclosure`, and no interval is
wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
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
    polyEval [-1/448, 0, 1/16, 0, -1/2, 0, 1] θ = 0 ∧
      (0.2564292158181384748733249040688 : ℝ) ≤ θ ∧
      θ ≤ (0.2564292158181384748733249040689 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Prism.HeptagonalPrism
