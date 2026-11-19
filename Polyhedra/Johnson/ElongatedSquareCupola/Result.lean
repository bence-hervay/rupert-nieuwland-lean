import Polyhedra.Johnson.ElongatedSquareCupola.Proof.Optimum
import Polyhedra.Johnson.ElongatedSquareCupola.Proof.Enclosure

/-!
# The elongated square cupola: the result

The elongated square cupola is Rupert, and its Nieuwland number and an optimal pose are the one root
of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Johnson.ElongatedSquareCupola

open Notation

/-- **The elongated square cupola is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the elongated square cupola.** The system `system` has exactly one root in its
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
  [(1.0397942379581936059746745497212, 1.0397942379581936059746745497213),    -- ν
   (0.9991616698433872659682289131223, 0.9991616698433872659682289131224),    -- R₁ 0 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 1
   (0.0409384601050647938556348367285, 0.0409384601050647938556348367286),    -- R₁ 0 2
   (0.0409384601050647938556348367285, 0.0409384601050647938556348367286),    -- R₁ 1 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 1
   (-0.9991616698433872659682289131224, -0.9991616698433872659682289131223),  -- R₁ 1 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 0
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (0.9117853814493802219673887690222, 0.9117853814493802219673887690223),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.4106670405270043156123797891769, 0.410667040527004315612379789177),     -- R₂ 0 2
   (-0.055944736847778607449282608252, -0.0559447368477786074492826082519),   -- R₂ 1 0
   (0.9906773819435427637338405027569, 0.990677381943542763733840502757),     -- R₂ 1 1
   (0.124211558739598355287160475482, 0.1242115587395983552871604754821),     -- R₂ 1 2
   (-0.4068385485597954095598165562711, -0.406838548559795409559816556271),   -- R₂ 2 0
   (-0.1362289429801460730508901251044, -0.1362289429801460730508901251043),  -- R₂ 2 1
   (0.9032851545886664811167135751057, 0.9032851545886664811167135751058),    -- R₂ 2 2
   (-0.0280724536793242354449274738993, -0.0280724536793242354449274738992),  -- t 0
   (0.035258810592086966884571542016, 0.0352588105920869668845715420161)]     -- t 1

/-- **The enclosure of the optimum of the elongated square cupola.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.ElongatedSquareCupola
