import Polyhedra.Other.DecagonalTrapezohedron.Proof.Optimum
import Polyhedra.Other.DecagonalTrapezohedron.Proof.Enclosure
import Polyhedra.Other.DecagonalTrapezohedron.Proof.Theta

/-!
# The decagonal trapezohedron: the result

The decagonal trapezohedron is Rupert, and its Nieuwland number and an optimal pose are the one root
of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Other.DecagonalTrapezohedron

open Notation

/-- **The decagonal trapezohedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the decagonal trapezohedron.** The system `system` has exactly one root in its
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
  [(1.0018212538284367956934866892377, 1.0018212538284367956934866892378),    -- ν
   (-0.25202960313479450377248944301, -0.2520296031347945037724894430099),    -- R₁ 0 0
   (0.93089277482042361544239858455, 0.9308927748204236154423985845501),      -- R₁ 0 1
   (0.2644233744033421741543133759948, 0.2644233744033421741543133759949),    -- R₁ 0 2
   (0.9659849149243570705604244025656, 0.9659849149243570705604244025657),    -- R₁ 1 0
   (0.2583569812041421104867142171328, 0.2583569812041421104867142171329),    -- R₁ 1 1
   (0.0111720365943364490060425013677, 0.0111720365943364490060425013678),    -- R₁ 1 2
   (-0.0579156566249629337780767720424, -0.0579156566249629337780767720423),  -- R₁ 2 0
   (0.2582446747761019235844874219779, 0.258244674776101923584487421978),     -- R₁ 2 1
   (-0.9643419853285890890846854839119, -0.9643419853285890890846854839118),  -- R₁ 2 2
   (-0.6280501843814762790575936155555, -0.6280501843814762790575936155554),  -- R₂ 0 0
   (0.7781728380625949664302236189078, 0.7781728380625949664302236189079),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.3655457089151736565829624010061, 0.3655457089151736565829624010062),    -- R₂ 1 0
   (0.2950257817474286391974815287035, 0.2950257817474286391974815287036),    -- R₂ 1 1
   (0.8828001601710444485280832405647, 0.8828001601710444485280832405648),    -- R₂ 1 2
   (0.6869711060824150703257460191318, 0.6869711060824150703257460191319),    -- R₂ 2 0
   (0.5544428033674212576237389012092, 0.5544428033674212576237389012093),    -- R₂ 2 1
   (-0.4697487383718856428061735067128, -0.4697487383718856428061735067127),  -- R₂ 2 2
   (0.0025735409935385984263628298447, 0.0025735409935385984263628298448),    -- t 0
   (-0.0014711500542829680474316986504, -0.0014711500542829680474316986503)]  -- t 1

/-- **The enclosure of the optimum of the decagonal trapezohedron.** At the root of `system`, the
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
    polyEval [25, 0, -450, 0, 1090, 0, 1330, 0, 1] θ = 0 ∧
      (0.2598101265935449922378604153267 : ℝ) ≤ θ ∧
      θ ≤ (0.2598101265935449922378604153268 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Other.DecagonalTrapezohedron
