import Polyhedra.Other.HexagonalTrapezohedron.Proof.Optimum
import Polyhedra.Other.HexagonalTrapezohedron.Proof.Enclosure
import Polyhedra.Other.HexagonalTrapezohedron.Proof.Theta

/-!
# The hexagonal trapezohedron: the result

The hexagonal trapezohedron is Rupert, and its Nieuwland number and an optimal pose are the one root
of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Other.HexagonalTrapezohedron

open Notation

/-- **The hexagonal trapezohedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the hexagonal trapezohedron.** The system `system` has exactly one root in its
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
  [(1.0000006133966885370781452429632, 1.0000006133966885370781452429633),    -- ν
   (-0.6140101647662878750655599050703, -0.6140101647662878750655599050702),  -- R₁ 0 0
   (0.7889600769903130615908381498057, 0.7889600769903130615908381498058),    -- R₁ 0 1
   (0.023097932355847396901657070674, 0.0230979323558473969016570706741),     -- R₁ 0 2
   (0.5250758521200316937986001899576, 0.5250758521200316937986001899577),    -- R₁ 1 0
   (0.3864424718867776470702887351572, 0.3864424718867776470702887351573),    -- R₁ 1 1
   (0.7582595633702615399541630231157, 0.7582595633702615399541630231158),    -- R₁ 1 2
   (0.5893105014201754609195482065791, 0.5893105014201754609195482065792),    -- R₁ 2 0
   (0.4777072459545452134873227702076, 0.4777072459545452134873227702077),    -- R₁ 2 1
   (-0.6515434905502663540685224269839, -0.6515434905502663540685224269838),  -- R₁ 2 2
   (-0.5913030870169502643573633362948, -0.5913030870169502643573633362947),  -- R₂ 0 0
   (0.8064494152048378438452981718659, 0.806449415204837843845298171866),     -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.4902198224341860894692977521197, 0.4902198224341860894692977521198),    -- R₂ 1 0
   (0.3594379124803617814396961564742, 0.3594379124803617814396961564743),    -- R₂ 1 1
   (0.7940333196814569727625947867203, 0.7940333196814569727625947867204),    -- R₂ 1 2
   (0.640347706310267035176939506558, 0.6403477063102670351769395065581),     -- R₂ 2 0
   (0.4695143531219624393293527033613, 0.4695143531219624393293527033614),    -- R₂ 2 1
   (-0.6078742363644351351700090406723, -0.6078742363644351351700090406722),  -- R₂ 2 2
   (-0.0033427860608341618126896259306, -0.0033427860608341618126896259305),  -- t 0
   (0.0051437196177132634482583439678, 0.0051437196177132634482583439679)]    -- t 1

/-- **The enclosure of the optimum of the hexagonal trapezohedron.** At the root of `system`, the
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
    polyEval [-18, 0, 114, 0, 1] θ = 0 ∧
      (0.397085192084709558243302057504 : ℝ) ≤ θ ∧
      θ ≤ (0.3970851920847095582433020575041 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Other.HexagonalTrapezohedron
