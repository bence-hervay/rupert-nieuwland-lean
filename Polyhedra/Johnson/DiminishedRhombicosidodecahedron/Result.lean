import Polyhedra.Johnson.DiminishedRhombicosidodecahedron.Proof.Optimum
import Polyhedra.Johnson.DiminishedRhombicosidodecahedron.Proof.Enclosure

/-!
# The diminished rhombicosidodecahedron: the result

The diminished rhombicosidodecahedron is Rupert, and its Nieuwland number and an optimal pose are
the one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to
within `2 ^ -100`. -/

namespace Nieuwland.Johnson.DiminishedRhombicosidodecahedron

open Notation

/-- **The diminished rhombicosidodecahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the diminished rhombicosidodecahedron.** The system `system` has exactly one
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
  [(1.0002706314665956296620748554808, 1.0002706314665956296620748554809),    -- ν
   (0.2935925058710912161479234647574, 0.2935925058710912161479234647575),    -- R₁ 0 0
   (0.3398582925412254440019715864909, 0.339858292541225444001971586491),     -- R₁ 0 1
   (0.8934762344278084353218627622806, 0.8934762344278084353218627622807),    -- R₁ 0 2
   (0.7816798596379343981572860601665, 0.7816798596379343981572860601666),    -- R₁ 1 0
   (-0.623367355883909326277932511899, -0.6233673558839093262779325118989),   -- R₁ 1 1
   (-0.0197417490289668722314548369166, -0.0197417490289668722314548369165),  -- R₁ 1 2
   (0.5502545206836127825869638512748, 0.5502545206836127825869638512749),    -- R₁ 2 0
   (0.7042084070850520330299241142861, 0.7042084070850520330299241142862),    -- R₁ 2 1
   (-0.4486763665026064085043535824503, -0.4486763665026064085043535824502),  -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (-0.6749572769624879574001377074285, -0.6749572769624879574001377074284),  -- R₂ 0 1
   (0.737856811498940709788659199565, 0.7378568114989407097886591995651),     -- R₂ 0 2
   (0.9926576773472142920830001286557, 0.9926576773472142920830001286558),    -- R₂ 1 0
   (0.0892493726101333304756465158798, 0.0892493726101333304756465158799),    -- R₂ 1 1
   (0.0816411972739951195782051394133, 0.0816411972739951195782051394134),    -- R₂ 1 2
   (-0.1209575777024069115796109578742, -0.1209575777024069115796109578741),  -- R₂ 2 0
   (0.732439228717359803402765969568, 0.7324392287173598034027659695681),     -- R₂ 2 1
   (0.6700015228581837250400953636482, 0.6700015228581837250400953636483),    -- R₂ 2 2
   (0.0085897631995769772952560167277, 0.0085897631995769772952560167278),    -- t 0
   (-0.0064912946812969378481043099161, -0.006491294681296937848104309916)]   -- t 1

/-- **The enclosure of the optimum of the diminished rhombicosidodecahedron.** At the root of
`system`, the Nieuwland number and the entries of the optimal pose lie in the intervals of
`enclosure`, and no interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`,
`Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.DiminishedRhombicosidodecahedron
