import Polyhedra.Johnson.GyroelongatedSquareBicupola.Proof.Optimum
import Polyhedra.Johnson.GyroelongatedSquareBicupola.Proof.Enclosure
import Polyhedra.Johnson.GyroelongatedSquareBicupola.Proof.Theta

/-!
# The gyroelongated square bicupola: the result

The gyroelongated square bicupola is Rupert, and its Nieuwland number and an optimal pose are the
one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.GyroelongatedSquareBicupola

open Notation

/-- **The gyroelongated square bicupola is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the gyroelongated square bicupola.** The system `system` has exactly one root
in its box; at the root the first variable is the Nieuwland number `ν polyhedron`, which is greater
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
  [(1.0000320427294996397655153714226, 1.0000320427294996397655153714227),    -- ν
   (-0.3744904706156888679938164495768, -0.3744904706156888679938164495767),  -- R₁ 0 0
   (0.9272268902355529849693854373752, 0.9272268902355529849693854373753),    -- R₁ 0 1
   (0.0026798212898716028256916724778, 0.0026798212898716028256916724779),    -- R₁ 0 2
   (-0.0018626275282385852618598853845, -0.0018626275282385852618598853844),  -- R₁ 1 0
   (-0.0036424042050278406987643258449, -0.0036424042050278406987643258448),  -- R₁ 1 1
   (0.999991631720135067712125131422, 0.9999916317201350677121251314221),     -- R₁ 1 2
   (0.9272288919337721544688770570408, 0.9272288919337721544688770570409),    -- R₁ 2 0
   (0.3744823452657187310271821215273, 0.3744823452657187310271821215274),    -- R₁ 2 1
   (0.0030911239955892382126518131273, 0.0030911239955892382126518131274),    -- R₁ 2 2
   (-0.37840265466024499206140209133, -0.3784026546602449920614020913299),    -- R₂ 0 0
   (0.9256410918634065097084798630714, 0.9256410918634065097084798630715),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.5303902747228633588864430469245, 0.5303902747228633588864430469246),    -- R₂ 1 0
   (0.21682387452903275172044494946, 0.2168238745290327517204449494601),      -- R₂ 1 1
   (0.8195569314657913353734638484185, 0.8195569314657913353734638484186),    -- R₂ 1 2
   (0.7586155728862181105577107014806, 0.7586155728862181105577107014807),    -- R₂ 2 0
   (0.3101225185118599112250212594679, 0.310122518511859911225021259468),     -- R₂ 2 1
   (-0.5729977627237092486664440186653, -0.5729977627237092486664440186652),  -- R₂ 2 2
   (-0.0011527561281197605422402697234, -0.0011527561281197605422402697233),  -- t 0
   (-0.0776273696329590652438301560323, -0.0776273696329590652438301560322)]  -- t 1

/-- **The enclosure of the optimum of the gyroelongated square bicupola.** At the root of `system`,
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
    polyEval [-17/1024, -1/16, 13/32, 3/4, -19/16, -1, 0, 0, 1] θ = 0 ∧
      (0.7007458350045842754210119906852 : ℝ) ≤ θ ∧
      θ ≤ (0.7007458350045842754210119906853 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.GyroelongatedSquareBicupola
