import Polyhedra.Antiprism.HeptagonalAntiprism.Proof.Optimum
import Polyhedra.Antiprism.HeptagonalAntiprism.Proof.Enclosure
import Polyhedra.Antiprism.HeptagonalAntiprism.Proof.Theta

/-!
# The heptagonal antiprism: the result

The heptagonal antiprism is Rupert, and its Nieuwland number and an optimal pose are the one root of
the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`. -/

namespace Nieuwland.Antiprism.HeptagonalAntiprism

open Notation

/-- **The heptagonal antiprism is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the heptagonal antiprism.** The system `system` has exactly one root in its
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
  [(1.0258672970836856172540603812549, 1.025867297083685617254060381255),     -- ν
   (-0.3204474044163606992706020953267, -0.3204474044163606992706020953266),  -- R₁ 0 0
   (0.9462919967214164360337097290533, 0.9462919967214164360337097290534),    -- R₁ 0 1
   (0.0429525080037494258230364594711, 0.0429525080037494258230364594712),    -- R₁ 0 2
   (-0.7258306564678158859979089393458, -0.7258306564678158859979089393457),  -- R₁ 1 0
   (-0.2744220788811724987161431780138, -0.2744220788811724987161431780137),  -- R₁ 1 1
   (0.6307633318084010024361510778083, 0.6307633318084010024361510778084),    -- R₁ 1 2
   (0.608673409255174227007124759007, 0.6086734092551742270071247590071),     -- R₁ 2 0
   (0.1709502253977172267352987373708, 0.1709502253977172267352987373709),    -- R₁ 2 1
   (0.7747855840825594902225280653296, 0.7747855840825594902225280653297),    -- R₁ 2 2
   (0.6666991975771867488795228825369, 0.666699197577186748879522882537),     -- R₂ 0 0
   (0.7453268946911383974527196260163, 0.7453268946911383974527196260164),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (-0.2511888554486006903116296345325, -0.2511888554486006903116296345324),  -- R₂ 1 0
   (0.224689877100586997270498593759, 0.2246898771005869972704985937591),     -- R₂ 1 1
   (0.9414980711753716058148426439105, 0.9414980711753716058148426439106),    -- R₂ 1 2
   (0.7017238337468361163747418990844, 0.7017238337468361163747418990845),    -- R₂ 2 0
   (-0.6276960085730893065514104936916, -0.6276960085730893065514104936915),  -- R₂ 2 1
   (0.3370183703792048511476614997565, 0.3370183703792048511476614997566),    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the heptagonal antiprism.** At the root of `system`, the
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
    polyEval [-1/8, -1/2, 1/4, 3/2, -1, -1, 1] θ = 0 ∧
      (0.8937023058307203190453368994365 : ℝ) ≤ θ ∧
      θ ≤ (0.8937023058307203190453368994366 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Antiprism.HeptagonalAntiprism
