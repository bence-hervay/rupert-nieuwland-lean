import Definitions.Optimum
import Modules.Nieuwland.Defs
import Modules.System.PolyRootEq

/-!
# Pose roots: the Nieuwland number and an optimal pose as one root

`IsPoseRoot P S N i j k`: the polynomial system `S` (`Modules/System/System.lean`) has exactly
one root in its box (`HasUniqueRoot`), the first coordinate of that root is `N` (`scales [S] = {N}`),
and at the root (at every solution in the box, and there is one) the coordinates

* `x i, …, x (i + 8)` (`matAt x i`, row by row) are a rotation `R₁`,
* `x j, …, x (j + 8)` (`matAt x j`) are a rotation `R₂`, and
* `(x k, x (k + 1))` is a translation `t`

with which `P` scaled by `x 0` fits weakly through `P` (`PoseAt`): the shadow of `R₁ (x 0 • P)`
moved by `t` lies in the shadow of `R₂ P`. So the root carries the scale and one pose that
witnesses `WeakFitsThrough (P.smul (x 0)) P` (`PoseAt.weakFitsThrough`).

With the representatives' theorem `<def>_nu_reps_list` (`IsRootEq [S₀] ν`, the scale of the one
root of `S₀` is the Nieuwland number ν), a theorem `<def>_pose_of_reps : IsRootEq [S₀] N →
IsPoseRoot <def> S N i j k` gives `IsPoseRoot <def> S ν i j k`: ν and an optimal pose as one
root. The generated modules `Nieuwland.Pose.<Name>` prove such theorems
(`lean/scripts/poseroot.py`; the checks in `Modules/Pose/PoseCheck.lean`).

A reader needs the standard definitions (`SO(3)`, `projXY`, `Polyhedron.hull`, `Polyhedron.smul`),
the systems (`PolynomialSystem`, `Solves`, `scales`, `HasUniqueRoot`) and the three definitions here.
-/

open Matrix

namespace Nieuwland

/-- The rotations `R₁ = matAt x i`, `R₂ = matAt x j` and the translation `(x k, x (k + 1))`
witness the weak fit of `P` scaled by `x 0` through `P`. -/
def PoseAt (P : Polyhedron) (x : ℕ → ℝ) (i j k : ℕ) : Prop :=
  matAt x i ∈ SO(3) ∧ matAt x j ∈ SO(3) ∧
    {projXY (matAt x i *ᵥ y) + ![x k, x (k + 1)] | y ∈ (P.smul (x 0)).hull} ⊆
      {projXY (matAt x j *ᵥ y) | y ∈ P.hull}

/-- **A pose at a point is a weak fit** of `P` scaled by `x 0` through `P`. -/
theorem PoseAt.weakFitsThrough {P : Polyhedron} {x : ℕ → ℝ} {i j k : ℕ} (h : PoseAt P x i j k) :
    (P.smul (x 0)).WeakFitsThrough P :=
  ⟨matAt x i, h.1, matAt x j, h.2.1, ![x k, x (k + 1)], h.2.2⟩

namespace PolynomialSystem

/-- **`S`'s one root carries the scale `N` and a pose**: `S` has exactly one root in its box, its
first coordinate is `N`, and at the root (every solution) the coordinates `i, j, k` are a weak
fit of `P` scaled by `x 0` through `P` (`PoseAt`). -/
def IsPoseRoot (P : Polyhedron) (S : PolynomialSystem) (N : ℝ) (i j k : ℕ) : Prop :=
  S.HasUniqueRoot ∧ scales [S] = {N} ∧ ∀ x, S.Solves x → PoseAt P x i j k

/-- **The root's pose is a weak fit at the scale `N`.** -/
theorem IsPoseRoot.weakFitsThrough {P : Polyhedron} {S : PolynomialSystem} {N : ℝ} {i j k : ℕ}
    (h : IsPoseRoot P S N i j k) : (P.smul N).WeakFitsThrough P := by
  obtain ⟨⟨-, -, x, hx, -⟩, hs, hp⟩ := h
  have h0 : x 0 ∈ scales [S] := ⟨S, List.mem_singleton_self _, x, hx, rfl⟩
  rw [hs] at h0
  rw [← Set.mem_singleton_iff.mp h0]
  exact (hp x hx).weakFitsThrough

end PolynomialSystem

end Nieuwland
