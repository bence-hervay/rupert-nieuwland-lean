import Polyhedra.Johnson.TridiminishedIcosahedron.Proof.Optimum
import Polyhedra.Johnson.TridiminishedIcosahedron.Proof.Enclosure

/-!
# The tridiminished icosahedron: the result

The tridiminished icosahedron is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.TridiminishedIcosahedron

open Notation

/-- **The tridiminished icosahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the tridiminished icosahedron.** The system `system` has exactly one root in
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
  [(1.0129565491707635656762930172255, 1.0129565491707635656762930172256),    -- ν
   (-0.7001980885547445649175942349894, -0.7001980885547445649175942349893),  -- R₁ 0 0
   (0.7120762114153666404571101034192, 0.7120762114153666404571101034193),    -- R₁ 0 1
   (-0.0516730676525030796177580292955, -0.0516730676525030796177580292954),  -- R₁ 0 2
   (-0.5513021561115431628263386683203, -0.5513021561115431628263386683202),  -- R₁ 1 0
   (-0.5852537813089680812384510576425, -0.5852537813089680812384510576424),  -- R₁ 1 1
   (-0.5945956139514638692550670922164, -0.5945956139514638692550670922163),  -- R₁ 1 2
   (-0.4536392503422138625448353709939, -0.4536392503422138625448353709938),  -- R₁ 2 0
   (-0.3878472387421272272280853890409, -0.3878472387421272272280853890408),  -- R₁ 2 1
   (0.802362729661006615223960670188, 0.8023627296610066152239606701881),     -- R₁ 2 2
   (0.6957209846186119793394698164978, 0.6957209846186119793394698164979),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (-0.7183121268371494461977193478454, -0.7183121268371494461977193478453),  -- R₂ 0 2
   (-0.3985176822487249595788910594237, -0.3985176822487249595788910594236),  -- R₂ 1 0
   (0.8319855004305425894061780112214, 0.8319855004305425894061780112215),    -- R₂ 1 1
   (-0.3859841758523837516079211789066, -0.3859841758523837516079211789065),  -- R₂ 1 2
   (0.5976252743119331636598579255375, 0.5976252743119331636598579255376),    -- R₂ 2 0
   (0.5547973747895168409309276985544, 0.5547973747895168409309276985545),    -- R₂ 2 1
   (0.5788297715479457111586514100824, 0.5788297715479457111586514100825),    -- R₂ 2 2
   (-0.0054755981195356445376156690325, -0.0054755981195356445376156690324),  -- t 0
   (-0.0423643582245260008677794638191, -0.042364358224526000867779463819)]   -- t 1

/-- **The enclosure of the optimum of the tridiminished icosahedron.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.TridiminishedIcosahedron
