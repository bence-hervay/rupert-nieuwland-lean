import Polyhedra.Johnson.AugmentedSphenocorona.Proof.Optimum
import Polyhedra.Johnson.AugmentedSphenocorona.Proof.Enclosure
import Polyhedra.Johnson.AugmentedSphenocorona.Proof.Theta

/-!
# The augmented sphenocorona: the result

The augmented sphenocorona is Rupert, and its Nieuwland number and an optimal pose are the one root
of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Johnson.AugmentedSphenocorona

open Notation

/-- **The augmented sphenocorona is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the augmented sphenocorona.** The system `system` has exactly one root in its
box; at the root the first variable is the Nieuwland number `ν polyhedron`, which is greater than
`1`, and the variables of `layout` are rotations `R₁`, `R₂` and a translation `t` with which the
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
  [(1.0692018895239081113157160480093, 1.0692018895239081113157160480094),    -- ν
   (-0.9271860436226367736768350498037, -0.9271860436226367736768350498036),  -- R₁ 0 0
   (-0.3673185479515740764439055223679, -0.3673185479515740764439055223678),  -- R₁ 0 1
   (0.0735059510662169015032431790147, 0.0735059510662169015032431790148),    -- R₁ 0 2
   (0.1981719973027420791751425386137, 0.1981719973027420791751425386138),    -- R₁ 1 0
   (-0.314447476723958962762523498407, -0.3144474767239589627625234984069),   -- R₁ 1 1
   (0.9283591136338228852145990523107, 0.9283591136338228852145990523108),    -- R₁ 1 2
   (-0.3178897607606194727797554390154, -0.3178897607606194727797554390153),  -- R₁ 2 0
   (0.87532843476759194229499986602, 0.8753284347675919422949998660201),      -- R₁ 2 1
   (0.3643435621647151513251692511507, 0.3643435621647151513251692511508),    -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (0.6651794328970668970995669807135, 0.6651794328970668970995669807136),    -- R₂ 0 1
   (0.7466835488014561025225335984659, 0.746683548801456102522533598466),     -- R₂ 0 2
   (0.8422800499958419005046072614943, 0.8422800499958419005046072614944),    -- R₂ 1 0
   (-0.4024924357434207770475399215611, -0.402492435743420777047539921561),   -- R₂ 1 1
   (0.3585584423051985055326322008921, 0.3585584423051985055326322008922),    -- R₂ 1 2
   (0.5390401815996670841335210589168, 0.5390401815996670841335210589169),    -- R₂ 2 0
   (0.6289166568155631016179953315862, 0.6289166568155631016179953315863),    -- R₂ 2 1
   (-0.5602673659967472686780932096656, -0.5602673659967472686780932096655),  -- R₂ 2 2
   (-0.0661592570703922305221563577456, -0.0661592570703922305221563577455),  -- t 0
   (0.1323563341772761320647497125877, 0.1323563341772761320647497125878)]    -- t 1

/-- **The enclosure of the optimum of the augmented sphenocorona.** At the root of `system`, the
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
    polyEval [21893041/10485760000, 0, -29434883/491520000, 0, 217315519/368640000, 0,
      -59348687/23040000, 0, 7849427/1280000, 0, -3159839/360000, 0, 694111/90000, 0, -299/75, 0, 1]
      θ = 0 ∧
      (0.864147468128994113735899747097 : ℝ) ≤ θ ∧
      θ ≤ (0.8641474681289941137358997470971 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.AugmentedSphenocorona
