import Polyhedra.Johnson.GyroelongatedPentagonalCupola.Proof.Optimum
import Polyhedra.Johnson.GyroelongatedPentagonalCupola.Proof.Enclosure
import Polyhedra.Johnson.GyroelongatedPentagonalCupola.Proof.Theta

/-!
# The gyroelongated pentagonal cupola: the result

The gyroelongated pentagonal cupola is Rupert, and its Nieuwland number and an optimal pose are the
one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.GyroelongatedPentagonalCupola

open Notation

/-- **The gyroelongated pentagonal cupola is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the gyroelongated pentagonal cupola.** The system `system` has exactly one root
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
  [(1.0004787708596922884875926396103, 1.0004787708596922884875926396104),    -- ν
   (-0.3470256716575929910824002453908, -0.3470256716575929910824002453907),  -- R₁ 0 0
   (0.9376019619200043880708334382247, 0.9376019619200043880708334382248),    -- R₁ 0 1
   (0.0218115614836513253011551874203, 0.0218115614836513253011551874204),    -- R₁ 0 2
   (0.4613949812799898000996573638412, 0.4613949812799898000996573638413),    -- R₁ 1 0
   (0.1504316402533393817077084856005, 0.1504316402533393817077084856006),    -- R₁ 1 1
   (0.8743483246740555998795340096823, 0.8743483246740555998795340096824),    -- R₁ 1 2
   (0.8165095556453912821190212066762, 0.8165095556453912821190212066763),    -- R₁ 2 0
   (0.3134850596351419806974208849498, 0.3134850596351419806974208849499),    -- R₁ 2 1
   (-0.4848084806656306352403551142709, -0.4848084806656306352403551142708),  -- R₁ 2 2
   (-0.309108524084349474787000973707, -0.3091085240843494747870009737069),   -- R₂ 0 0
   (0.9510267716202289647769710504903, 0.9510267716202289647769710504904),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.5275257811073070715761454572702, 0.5275257811073070715761454572703),    -- R₂ 1 0
   (0.1714596481198099280722508976095, 0.1714596481198099280722508976096),    -- R₂ 1 1
   (0.8320565721955187496959631072216, 0.8320565721955187496959631072217),    -- R₂ 1 2
   (0.7913080756604981636020106941287, 0.7913080756604981636020106941288),    -- R₂ 2 0
   (0.2571957789860397749906089690228, 0.2571957789860397749906089690229),    -- R₂ 2 1
   (-0.5546907793232581711889051997477, -0.5546907793232581711889051997476),  -- R₂ 2 2
   (-0.0098240578743301041803518062504, -0.0098240578743301041803518062503),  -- t 0
   (-0.0168356507139813934887484435744, -0.0168356507139813934887484435743)]  -- t 1

/-- **The enclosure of the optimum of the gyroelongated pentagonal cupola.** At the root of
`system`, the Nieuwland number and the entries of the optimal pose lie in the intervals of
`enclosure`, and no interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`,
`Definitions/Optimum.lean`). -/
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
    polyEval [-1/1600, 1/20, 31/80, 1/4, -49/40, -3/2, 3/2, 0, 1] θ = 0 ∧
      (0.6940640579892960447363608848778 : ℝ) ≤ θ ∧
      θ ≤ (0.6940640579892960447363608848779 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.GyroelongatedPentagonalCupola
