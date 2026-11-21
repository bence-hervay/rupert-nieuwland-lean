import Polyhedra.Other.DodecagonalTrapezohedron.Proof.Optimum
import Polyhedra.Other.DodecagonalTrapezohedron.Proof.Enclosure
import Polyhedra.Other.DodecagonalTrapezohedron.Proof.Theta

/-!
# The dodecagonal trapezohedron: the result

The dodecagonal trapezohedron is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Other.DodecagonalTrapezohedron

open Notation

/-- **The dodecagonal trapezohedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the dodecagonal trapezohedron.** The system `system` has exactly one root in
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
  [(1.0017266171773589662213050349972, 1.0017266171773589662213050349973),    -- ν
   (-0.2126012650996766097913274014769, -0.2126012650996766097913274014768),  -- R₁ 0 0
   (0.9515326998196955593188845989172, 0.9515326998196955593188845989173),    -- R₁ 0 1
   (0.2222301132876869385749695351727, 0.2222301132876869385749695351728),    -- R₁ 0 2
   (0.9762974757348753196937979837211, 0.9762974757348753196937979837212),    -- R₁ 1 0
   (0.2162886398890725360168163883889, 0.216288639889072536016816388389),     -- R₁ 1 1
   (0.0079033618571869136612891910263, 0.0079033618571869136612891910264),    -- R₁ 1 2
   (-0.0405455416997672466808121506849, -0.0405455416997672466808121506848),  -- R₁ 2 0
   (0.2186429633644225997708150818469, 0.218642963364422599770815081847),     -- R₁ 2 1
   (-0.9749622113802648260052944783181, -0.974962211380264826005294478318),   -- R₁ 2 2
   (-0.5365423063602069603212045865512, -0.5365423063602069603212045865511),  -- R₂ 0 0
   (0.8438734226681569200835892996927, 0.8438734226681569200835892996928),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.4039210341639301285711350923478, 0.4039210341639301285711350923479),    -- R₂ 1 0
   (0.2568166237212305719477636661959, 0.256816623721230571947763666196),     -- R₂ 1 1
   (0.8780051366252757069325421422909, 0.878005136625275706932542142291),     -- R₂ 1 2
   (0.7409251997641941504077487057663, 0.7409251997641941504077487057664),    -- R₂ 2 0
   (0.4710869010010340470935608459225, 0.4710869010010340470935608459226),    -- R₂ 2 1
   (-0.4786512091906077483313046052082, -0.4786512091906077483313046052081),  -- R₂ 2 2
   (-0.001432395948689229988191440711, -0.0014323959486892299881914407109),   -- t 0
   (0.000737493511518252383461167797, 0.0007374935115182523834611677971)]     -- t 1

/-- **The enclosure of the optimum of the dodecagonal trapezohedron.** At the root of `system`, the
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
    polyEval [-2, 0, 76, 0, -858, 0, 2944, 0, 1] θ = 0 ∧
      (0.2196217310926713836654950026825 : ℝ) ≤ θ ∧
      θ ≤ (0.2196217310926713836654950026826 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Other.DodecagonalTrapezohedron
