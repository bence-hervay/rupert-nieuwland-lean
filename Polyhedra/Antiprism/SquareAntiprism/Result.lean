import Polyhedra.Antiprism.SquareAntiprism.Proof.Optimum
import Polyhedra.Antiprism.SquareAntiprism.Proof.Enclosure
import Polyhedra.Antiprism.SquareAntiprism.Proof.Theta

/-!
# The square antiprism: the result

The square antiprism is Rupert, and its Nieuwland number and an optimal pose are the one root of the
polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Antiprism.SquareAntiprism

open Notation

/-- **The square antiprism is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the square antiprism.** The system `system` has exactly one root in its box; at
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
  [(1.0285354563001179816676608666056, 1.0285354563001179816676608666057),    -- ν
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 0
   (-0.5451000382863573816426485930197, -0.5451000382863573816426485930196),  -- R₁ 0 1
   (-0.8383710087188199738959250807942, -0.8383710087188199738959250807941),  -- R₁ 0 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 0
   (-0.8383710087188199738959250807942, -0.8383710087188199738959250807941),  -- R₁ 1 1
   (0.5451000382863573816426485930196, 0.5451000382863573816426485930197),    -- R₁ 1 2
   (-1.0000000000000000000000000000001, -0.9999999999999999999999999999999),  -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (0.9074462407885173595148439814637, 0.9074462407885173595148439814638),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.4201682045071808777182734425674, 0.4201682045071808777182734425675),    -- R₂ 0 2
   (-0.2992164755226698645279754328072, -0.2992164755226698645279754328071),  -- R₂ 1 0
   (0.7020425710629921094908977184833, 0.7020425710629921094908977184834),    -- R₂ 1 1
   (0.6462242096912302927512775389482, 0.6462242096912302927512775389483),    -- R₂ 1 2
   (-0.2949759665711423328982835434049, -0.2949759665711423328982835434048),  -- R₂ 2 0
   (-0.7121349790701645305585405474299, -0.7121349790701645305585405474298),  -- R₂ 2 1
   (0.637065891984617747308786202119, 0.6370658919846177473087862021191),     -- R₂ 2 2
   (-0.1286107593827214880204255957814, -0.1286107593827214880204255957813),  -- t 0
   (0.0836213670731446274852576633444, 0.0836213670731446274852576633445)]    -- t 1

/-- **The enclosure of the optimum of the square antiprism.** At the root of `system`, the Nieuwland
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
    polyEval [7/32, -1/2, -1, 0, 1] θ = 0 ∧
      (1.1275549888134047959164071002214 : ℝ) ≤ θ ∧
      θ ≤ (1.1275549888134047959164071002215 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Antiprism.SquareAntiprism
