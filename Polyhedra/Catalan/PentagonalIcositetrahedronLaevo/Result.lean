import Polyhedra.Catalan.PentagonalIcositetrahedronLaevo.Proof.Optimum
import Polyhedra.Catalan.PentagonalIcositetrahedronLaevo.Proof.Enclosure
import Polyhedra.Catalan.PentagonalIcositetrahedronLaevo.Proof.Theta

/-!
# The pentagonal icositetrahedron laevo: the result

The pentagonal icositetrahedron laevo is Rupert, and its Nieuwland number and an optimal pose are
the one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to
within `2 ^ -100`. -/

namespace Nieuwland.Catalan.PentagonalIcositetrahedronLaevo

open Notation

/-- **The pentagonal icositetrahedron laevo is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the pentagonal icositetrahedron laevo.** The system `system` has exactly one
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
  [(1.0004361413347045995199977611888, 1.0004361413347045995199977611889),    -- ν
   (0.8932895751694146041141053427704, 0.8932895751694146041141053427705),    -- R₁ 0 0
   (-0.0012079313397447159144503139077, -0.0012079313397447159144503139076),  -- R₁ 0 1
   (0.4494800060019636046850380060244, 0.4494800060019636046850380060245),    -- R₁ 0 2
   (0.0473514603039919315389148258298, 0.0473514603039919315389148258299),    -- R₁ 1 0
   (0.9946848484036786223315568075545, 0.9946848484036786223315568075546),    -- R₁ 1 1
   (-0.0914324426187464051281822730044, -0.0914324426187464051281822730043),  -- R₁ 1 2
   (-0.4469805075176391312093585027169, -0.4469805075176391312093585027168),  -- R₁ 2 0
   (0.1029591824852418891005316734503, 0.1029591824852418891005316734504),    -- R₁ 2 1
   (0.8885988029708595144967198340363, 0.8885988029708595144967198340364),    -- R₁ 2 2
   (0.996523716465364220963089199004, 0.9965237164653642209630891990041),     -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.083309558407534355674929855768, 0.0833095584075343556749298557681),     -- R₂ 0 2
   (-0.0065714124045161800870210808588, -0.0065714124045161800870210808587),  -- R₂ 1 0
   (0.9968841617158528400165848436353, 0.9968841617158528400165848436354),    -- R₂ 1 1
   (0.078605245747921516978275033132, 0.0786052457479215169782750331321),     -- R₂ 1 2
   (-0.0830499792960127662222390599083, -0.0830499792960127662222390599082),  -- R₂ 2 0
   (-0.0788794530919260548136882745697, -0.0788794530919260548136882745696),  -- R₂ 2 1
   (0.9934187097185408295498207173445, 0.9934187097185408295498207173446),    -- R₂ 2 2
   (0.0075193439728120411679525286946, 0.0075193439728120411679525286947),    -- t 0
   (0.010985343100586566921320577479, 0.0109853431005865669213205774791)]     -- t 1

/-- **The enclosure of the optimum of the pentagonal icositetrahedron laevo.** At the root of
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
    polyEval [-1, -1, -3, 1] θ = 0 ∧
      (3.382975767906237494122708536455 : ℝ) ≤ θ ∧
      θ ≤ (3.3829757679062374941227085364551 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Catalan.PentagonalIcositetrahedronLaevo
