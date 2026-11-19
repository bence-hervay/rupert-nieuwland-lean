import Polyhedra.Johnson.GyroelongatedSquarePyramid.Proof.Optimum
import Polyhedra.Johnson.GyroelongatedSquarePyramid.Proof.Enclosure
import Polyhedra.Johnson.GyroelongatedSquarePyramid.Proof.Theta

/-!
# The gyroelongated square pyramid: the result

The gyroelongated square pyramid is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.GyroelongatedSquarePyramid

open Notation

/-- **The gyroelongated square pyramid is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the gyroelongated square pyramid.** The system `system` has exactly one root in
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
  [(1.0103176446566526499965082242743, 1.0103176446566526499965082242744),    -- ν
   (0.3774175202791215500671317813804, 0.3774175202791215500671317813805),    -- R₁ 0 0
   (0.9222873722628777252211806051776, 0.9222873722628777252211806051777),    -- R₁ 0 1
   (-0.0833187754998528332310852381392, -0.0833187754998528332310852381391),  -- R₁ 0 2
   (0.9173149315420305146650978625812, 0.9173149315420305146650978625813),    -- R₁ 1 0
   (-0.3846678698139535721380975969847, -0.3846678698139535721380975969846),  -- R₁ 1 1
   (-0.1027810600394602692544150166855, -0.1027810600394602692544150166854),  -- R₁ 1 2
   (-0.1268437296692222934049530928814, -0.1268437296692222934049530928813),  -- R₁ 2 0
   (-0.0376381840320607052346877880787, -0.0376381840320607052346877880786),  -- R₁ 2 1
   (-0.9912083713056352041044668276712, -0.9912083713056352041044668276711),  -- R₁ 2 2
   (-0.1979576142267340479935101687656, -0.1979576142267340479935101687655),  -- R₂ 0 0
   (0.9802105809312912847638181447788, 0.9802105809312912847638181447789),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.2856507158064251075990769429745, 0.2856507158064251075990769429746),    -- R₂ 1 0
   (0.0576883532000583820564860399016, 0.0576883532000583820564860399017),    -- R₂ 1 1
   (0.9565959034327620781341297381197, 0.9565959034327620781341297381198),    -- R₂ 1 2
   (0.9376654262203211355175629400726, 0.9376654262203211355175629400727),    -- R₂ 2 0
   (0.1893654428226168518964329907479, 0.189365442822616851896432990748),     -- R₂ 2 1
   (-0.2914177028522078803790545442523, -0.2914177028522078803790545442522),  -- R₂ 2 2
   (0.0011634862746890628715249225144, 0.0011634862746890628715249225145),    -- t 0
   (0.1302595160173324719706039536029, 0.130259516017332471970603953603)]     -- t 1

/-- **The enclosure of the optimum of the gyroelongated square pyramid.** At the root of `system`,
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
    polyEval [-1/32, 0, 0, 0, 1] θ = 0 ∧
      (0.4204482076268572715155627381166 : ℝ) ≤ θ ∧
      θ ≤ (0.4204482076268572715155627381167 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.GyroelongatedSquarePyramid
