import Polyhedra.Catalan.RhombicTriacontahedron.Proof.Optimum
import Polyhedra.Catalan.RhombicTriacontahedron.Proof.Enclosure

/-!
# The rhombic triacontahedron: the result

The rhombic triacontahedron is Rupert, and its Nieuwland number and an optimal pose are the one root
of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Catalan.RhombicTriacontahedron

open Notation

/-- **The rhombic triacontahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the rhombic triacontahedron.** The system `system` has exactly one root in its
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
  [(1.007053639886023980823836670095, 1.0070536398860239808238366700951),     -- ν
   (-0.5256393448309134426909164080697, -0.5256393448309134426909164080696),  -- R₁ 0 0
   (0.8505023257606443000623292385083, 0.8505023257606443000623292385084),    -- R₁ 0 1
   (-0.0186834964999314958341972906035, -0.0186834964999314958341972906034),  -- R₁ 0 2
   (-0.009822495393182925539940715325, -0.0098224953931829255399407153249),   -- R₁ 1 0
   (0.0158931314005092357167584923228, 0.0158931314005092357167584923229),    -- R₁ 1 1
   (0.9998254482451109563499551148981, 0.9998254482451109563499551148982),    -- R₁ 1 2
   (0.850650808352039932181540497063, 0.8506508083520399321815404970631),     -- R₁ 2 0
   (0.5257311121191336060256690848478, 0.5257311121191336060256690848479),    -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (-0.3323633820451040902022495262196, -0.3323633820451040902022495262195),  -- R₂ 0 0
   (0.9431514100480050600106486095249, 0.943151410048005060010648609525),     -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.2011638477115020317962408106567, 0.2011638477115020317962408106568),    -- R₂ 1 0
   (0.0708894627716222520473217959462, 0.0708894627716222520473217959463),    -- R₂ 1 1
   (0.9769891455087177177802461244236, 0.9769891455087177177802461244237),    -- R₂ 1 2
   (0.9214486901881427053763195028829, 0.921448690188142705376319502883),     -- R₂ 2 0
   (0.324715416622633737710408026234, 0.3247154166226337377104080262341),     -- R₂ 2 1
   (-0.2132890282179221671279975421667, -0.2132890282179221671279975421666),  -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the rhombic triacontahedron.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Catalan.RhombicTriacontahedron
