import Polyhedra.Johnson.TriangularDipyramidJ12.Proof.Optimum
import Polyhedra.Johnson.TriangularDipyramidJ12.Proof.Enclosure

/-!
# The triangular dipyramid j12: the result

The triangular dipyramid j12 is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.TriangularDipyramidJ12

open Notation

/-- **The triangular dipyramid j12 is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the triangular dipyramid j12.** The system `system` has exactly one root in its
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
  [(1.039963426289857261784396795346, 1.0399634262898572617843967953461),     -- ν
   (-0.7540243963046562295556053573525, -0.7540243963046562295556053573524),  -- R₁ 0 0
   (-0.3118855473918333401185576210894, -0.3118855473918333401185576210893),  -- R₁ 0 1
   (0.5780783814548812588778528656767, 0.5780783814548812588778528656768),    -- R₁ 0 2
   (-0.3920985707651908838004489926615, -0.3920985707651908838004489926614),  -- R₁ 1 0
   (0.9197978120158517578855953914132, 0.9197978120158517578855953914133),    -- R₁ 1 1
   (-0.0151886738969018735331736002864, -0.0151886738969018735331736002863),  -- R₁ 1 2
   (-0.5269781025633734259201609950043, -0.5269781025633734259201609950042),  -- R₁ 2 0
   (-0.238116337824493494320698964639, -0.2381163378244934943206989646389),   -- R₁ 2 1
   (-0.8158398673022533575196230253696, -0.8158398673022533575196230253695),  -- R₁ 2 2
   (0.2220610650376628696177894609014, 0.2220610650376628696177894609015),    -- R₂ 0 0
   (0.9750327601646720368118193727548, 0.9750327601646720368118193727549),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.2113681222802672274384800180029, 0.211368122280267227438480018003),     -- R₂ 1 0
   (-0.0481385162285624449417767047689, -0.0481385162285624449417767047688),  -- R₂ 1 1
   (0.9762203645381643189684036328676, 0.9762203645381643189684036328677),    -- R₂ 1 2
   (0.9518468365646086770629592690659, 0.951846836564608677062959269066),     -- R₂ 2 0
   (-0.2167805338608002621229551930394, -0.2167805338608002621229551930393),  -- R₂ 2 1
   (-0.2167805338608002621229551930394, -0.2167805338608002621229551930393),  -- R₂ 2 2
   (-0.549041249264392115131207335868, -0.5490412492643921151312073358679),   -- t 0
   (-0.5226031762557924156511503185802, -0.5226031762557924156511503185801)]  -- t 1

/-- **The enclosure of the optimum of the triangular dipyramid j12.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.TriangularDipyramidJ12
