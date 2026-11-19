import Polyhedra.Johnson.Disphenocingulum.Proof.Optimum
import Polyhedra.Johnson.Disphenocingulum.Proof.Enclosure
import Polyhedra.Johnson.Disphenocingulum.Proof.Theta

/-!
# The disphenocingulum: the result

The disphenocingulum is Rupert, and its Nieuwland number and an optimal pose are the one root of the
polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Johnson.Disphenocingulum

open Notation

/-- **The disphenocingulum is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the disphenocingulum.** The system `system` has exactly one root in its box; at
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
  [(1.0197539439153241304436257144961, 1.0197539439153241304436257144962),    -- ν
   (0.1952805876004049802919826015206, 0.1952805876004049802919826015207),    -- R₁ 0 0
   (0.8735166328615342484639121479345, 0.8735166328615342484639121479346),    -- R₁ 0 1
   (-0.4459082688408997667096197093381, -0.445908268840899766709619709338),   -- R₁ 0 2
   (0.9373584161184748673995548119041, 0.9373584161184748673995548119042),    -- R₁ 1 0
   (-0.0324959082877338578843280989837, -0.0324959082877338578843280989836),  -- R₁ 1 1
   (0.3468475395276998442148438178211, 0.3468475395276998442148438178212),    -- R₁ 1 2
   (0.288486900635548221011697517952, 0.2884869006355482210116975179521),     -- R₁ 2 0
   (-0.4857084599415608028335238374037, -0.4857084599415608028335238374036),  -- R₁ 2 1
   (-0.825143987497268595561952087891, -0.8251439874972685955619520878909),   -- R₁ 2 2
   (-0.1423430751796817406311875320849, -0.1423430751796817406311875320848),  -- R₂ 0 0
   (0.9898173816156147255122516551257, 0.9898173816156147255122516551258),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.253275534832947809322187530679, 0.2532755348329478093221875306791),     -- R₂ 1 0
   (0.0364228989766324567053170475437, 0.0364228989766324567053170475438),    -- R₂ 1 1
   (0.9667082682408495192397742547365, 0.9667082682408495192397742547366),    -- R₂ 1 2
   (0.9568646468563229935525371848378, 0.9568646468563229935525371848379),    -- R₂ 2 0
   (0.1376042277030271855009379164971, 0.1376042277030271855009379164972),    -- R₂ 2 1
   (-0.2558810741629355689073233615789, -0.2558810741629355689073233615788),  -- R₂ 2 2
   (-0.0362113680673945521086867625892, -0.0362113680673945521086867625891),  -- t 0
   (-0.1208707992834085675408250185524, -0.1208707992834085675408250185523)]  -- t 1

/-- **The enclosure of the optimum of the disphenocingulum.** At the root of `system`, the Nieuwland
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
    polyEval [2209/60397977600, 0, -1247/52428800, 0, 9000611/2516582400, 0, 1470301/235929600, 0,
      -251632709/1258291200, 0, -12724537/11796480, 0, -63149653/14745600, 0, -769303/921600, 0,
      3074473/153600, 0, 525053/14400, 0, 95083/3600, 0, 637/75, 0, 1] θ = 0 ∧
      (0.3250029759499702709388900655364 : ℝ) ≤ θ ∧
      θ ≤ (0.3250029759499702709388900655365 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.Disphenocingulum
