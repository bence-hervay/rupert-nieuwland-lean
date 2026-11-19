import Polyhedra.Johnson.ElongatedTriangularGyrobicupola.Proof.Optimum
import Polyhedra.Johnson.ElongatedTriangularGyrobicupola.Proof.Enclosure

/-!
# The elongated triangular gyrobicupola: the result

The elongated triangular gyrobicupola is Rupert, and its Nieuwland number and an optimal pose are
the one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to
within `2 ^ -100`. -/

namespace Nieuwland.Johnson.ElongatedTriangularGyrobicupola

open Notation

/-- **The elongated triangular gyrobicupola is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the elongated triangular gyrobicupola.** The system `system` has exactly one
root in its box; at the root the first variable is the Nieuwland number `ν polyhedron`, which is
greater than `1`, and the variables of `layout` are rotations `R₁`, `R₂` and a translation `t` with
which the polyhedron scaled by `ν polyhedron` fits weakly through itself; no larger copy fits
through it (`Polyhedron.IsOptimum`, `Definitions/Optimum.lean`). -/
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
  [(1.1155143010664819075625375147133, 1.1155143010664819075625375147134),    -- ν
   (0.344432912398869889435149022399, 0.3444329123988698894351490223991),     -- R₁ 0 0
   (0.4688954502898489645960506401909, 0.468895450289848964596050640191),     -- R₁ 0 1
   (-0.8133283626887188540311996625901, -0.81332836268871885403119966259),    -- R₁ 0 2
   (0.7402922635845244921270829019825, 0.7402922635845244921270829019826),    -- R₁ 1 0
   (-0.6684337838291437265092393294471, -0.668433783829143726509239329447),   -- R₁ 1 1
   (-0.0718584797553807656178435725355, -0.0718584797553807656178435725354),  -- R₁ 1 2
   (-0.577350269189625764509148780502, -0.5773502691896257645091487805019),   -- R₁ 2 0
   (-0.577350269189625764509148780502, -0.5773502691896257645091487805019),   -- R₁ 2 1
   (-0.577350269189625764509148780502, -0.5773502691896257645091487805019),   -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (0.4649806772494977622017022563262, 0.4649806772494977622017022563263),    -- R₂ 0 1
   (0.8853208287308044545669553955435, 0.8853208287308044545669553955436),    -- R₂ 0 2
   (0.8961434720378397545344998894956, 0.8961434720378397545344998894957),    -- R₂ 1 0
   (0.3928739010992163295410434173589, 0.392873901099216329541043417359),     -- R₂ 1 1
   (-0.2063418894918060599685592410625, -0.2063418894918060599685592410624),  -- R₂ 1 2
   (-0.443764439228703315420362014384, -0.4437644392287033154203620143839),   -- R₂ 2 0
   (0.7933744813262407801121513225393, 0.7933744813262407801121513225394),    -- R₂ 2 1
   (-0.4166893985408710895660703368472, -0.4166893985408710895660703368471),  -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the elongated triangular gyrobicupola.** At the root of
`system`, the Nieuwland number and the entries of the optimal pose lie in the intervals of
`enclosure`, and no interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`,
`Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.ElongatedTriangularGyrobicupola
