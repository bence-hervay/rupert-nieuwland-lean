import Polyhedra.Johnson.Bilunabirotunda.Proof.Optimum
import Polyhedra.Johnson.Bilunabirotunda.Proof.Enclosure

/-!
# The bilunabirotunda: the result

The bilunabirotunda is Rupert, and its Nieuwland number and an optimal pose are the one root of the
polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Johnson.Bilunabirotunda

open Notation

/-- **The bilunabirotunda is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the bilunabirotunda.** The system `system` has exactly one root in its box; at
the root the first variable is the Nieuwland number `ν polyhedron`, which is greater than `1`, and
the variables of `layout` are rotations `R₁`, `R₂` and a translation `t` with which the polyhedron
scaled by `ν polyhedron` fits weakly through itself; no larger copy fits through it
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
  [(1.2034092136492963724383486590609, 1.203409213649296372438348659061),     -- ν
   (0.4983616763181758899837788049793, 0.4983616763181758899837788049794),    -- R₁ 0 0
   (0.8669518092926309261334026937447, 0.8669518092926309261334026937448),    -- R₁ 0 1
   (0.0054954473495232088810840224774, 0.0054954473495232088810840224775),    -- R₁ 0 2
   (-0.2900565541021316108062689641236, -0.2900565541021316108062689641235),  -- R₁ 1 0
   (0.1607570379289307020174394947184, 0.1607570379289307020174394947185),    -- R₁ 1 1
   (0.9434110292861290973976990462387, 0.9434110292861290973976990462388),    -- R₁ 1 2
   (0.8170084669082290986341914054988, 0.8170084669082290986341914054989),    -- R₁ 2 0
   (-0.4717538925335434187960887451975, -0.4717538925335434187960887451974),  -- R₁ 2 1
   (0.3315802012782353759620103639031, 0.3315802012782353759620103639032),    -- R₁ 2 2
   (0.9982373303485816208040498811839, 0.998237330348581620804049881184),     -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.0593483976071530258251258556259, 0.059348397607153025825125855626),     -- R₂ 0 2
   (-0.0169963614444241240866355019914, -0.0169963614444241240866355019913),  -- R₂ 1 0
   (0.9581152752399516698750877106349, 0.958115275239951669875087710635),     -- R₂ 1 1
   (0.2858780212774709753388001666551, 0.2858780212774709753388001666552),    -- R₂ 1 2
   (-0.0568626063084275104157695893498, -0.0568626063084275104157695893497),  -- R₂ 2 0
   (-0.2863828195822362082155257346613, -0.2863828195822362082155257346612),  -- R₂ 2 1
   (0.956426434521725839825409704804, 0.9564264345217258398254097048041),     -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the bilunabirotunda.** At the root of `system`, the Nieuwland
number and the entries of the optimal pose lie in the intervals of `enclosure`, and no interval is
wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.Bilunabirotunda
