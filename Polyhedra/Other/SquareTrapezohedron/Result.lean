import Polyhedra.Other.SquareTrapezohedron.Proof.Optimum
import Polyhedra.Other.SquareTrapezohedron.Proof.Enclosure
import Polyhedra.Other.SquareTrapezohedron.Proof.Theta

/-!
# The square trapezohedron: the result

The square trapezohedron is Rupert, and its Nieuwland number and an optimal pose are the one root of
the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`. -/

namespace Nieuwland.Other.SquareTrapezohedron

open Notation

/-- **The square trapezohedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the square trapezohedron.** The system `system` has exactly one root in its
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
  [(1.0000685506482099876002347496883, 1.0000685506482099876002347496884),    -- ν
   (-0.5219588985104909098318199434591, -0.521958898510490909831819943459),   -- R₁ 0 0
   (0.8502479212005117542402827450637, 0.8502479212005117542402827450638),    -- R₁ 0 1
   (-0.0680983168655687471228358162698, -0.0680983168655687471228358162697),  -- R₁ 0 2
   (0.5180538675318688380984167900983, 0.5180538675318688380984167900984),    -- R₁ 1 0
   (0.3794259589629319763441696653714, 0.3794259589629319763441696653715),    -- R₁ 1 1
   (0.7665873283588324185077799303571, 0.7665873283588324185077799303572),    -- R₁ 1 2
   (0.6776275515362314017482582835516, 0.6776275515362314017482582835517),    -- R₁ 2 0
   (0.3648484810976575991813619963873, 0.3648484810976575991813619963874),    -- R₁ 2 1
   (-0.638518979545435470834005335082, -0.6385189795454354708340053350819),   -- R₁ 2 2
   (-0.6007989664234608211545730091726, -0.6007989664234608211545730091725),  -- R₂ 0 0
   (0.7994001513287955319201695090571, 0.7994001513287955319201695090572),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.4483436418207789232194071661937, 0.4483436418207789232194071661938),    -- R₂ 1 0
   (0.336958150634204679724988055016, 0.3369581506342046797249880550161),     -- R₂ 1 1
   (0.827917377254552934617208377428, 0.8279173772545529346172083774281),     -- R₂ 1 2
   (0.6618372766650291158108518849876, 0.6618372766650291158108518849877),    -- R₂ 2 0
   (0.4974119045385578943306377909947, 0.4974119045385578943306377909948),    -- R₂ 2 1
   (-0.5608500837478249633281210639456, -0.5608500837478249633281210639455),  -- R₂ 2 2
   (-0.0238530705683426662475110692926, -0.0238530705683426662475110692925),  -- t 0
   (-0.0207945842763354592273585652834, -0.0207945842763354592273585652833)]  -- t 1

/-- **The enclosure of the optimum of the square trapezohedron.** At the root of `system`, the
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
    polyEval [-2, 0, 8, 0, 1] θ = 0 ∧
      (0.4925857155047080193447509819059 : ℝ) ≤ θ ∧
      θ ≤ (0.492585715504708019344750981906 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Other.SquareTrapezohedron
