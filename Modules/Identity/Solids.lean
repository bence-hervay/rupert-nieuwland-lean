import Modules.Identity.Faces
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Textbook constructions of solids

The solids that the fixtures are proved to be (`Nieuwland/Results/Gen/*Construction.lean`), in the
coordinates of the usual references, over the reals with `φ = Real.goldenRatio = (1 + √5) / 2`:

* `rhombicosidodecahedron`: the even permutations of `(±1, ±1, ±φ³)`, `(±φ², ±φ, ±2φ)` and
  `(±(2 + φ), 0, ±φ²)` (edge length `2`);
* `snubCube t`, for the tribonacci constant `t` (`t³ = t² + t + 1`): the even permutations of
  `(±1, ±1/t, ±t)` with an odd number of plus signs and the odd permutations with an even number
  (the opposite choice gives the mirror image);
* `snubDodecahedron ξ`, for the real root `ξ` of `ξ³ - 2ξ = φ`: the even permutations, with an
  even number of plus signs, of five points in `α = ξ - 1/ξ` and `β = ξφ + φ² + φ/ξ`;
* `gyrate V n t`: the cap `{x ∈ V | t ≤ n ⬝ᵥ x}` rotated by `36°` about the axis `ℝ n`
  (`rotAbout`, Rodrigues' formula), the other points kept; `diminish V n t`: the points with
  `n ⬝ᵥ x ≤ t`. For a pentagonal face of the rhombicosidodecahedron with outer normal `n` and `t`
  the level of the decagon below it, the cap is a pentagonal cupola: the gyrate and diminished
  rhombicosidodecahedra (Johnson solids J72–J83) rotate or remove such cupolae;
* `Polyhedron.IsPolarOf Q P f`: `Q`'s vertices are the images under `f` of the poles `n / h` of
  the planes `n ⬝ᵥ x = h` (`h > 0`) of the facets of `P`, listed by a facet certificate
  (`Modules/Identity/Faces.lean`): for `f = id`, `Q` is the polar reciprocal of `P` in the unit
  sphere about the origin. The certificate's facets are all of `P`'s by the argument in the docs
  of `Faces.lean`, which is not formalised.
-/

open Matrix Real
open scoped goldenRatio

namespace Nieuwland.Identity

/-- The even permutations of the coordinates of `v`: its cyclic shifts. -/
def evenPerms (v : Fin 3 → ℝ) : List (Fin 3 → ℝ) :=
  [v, ![v 1, v 2, v 0], ![v 2, v 0, v 1]]

/-- The odd permutations of the coordinates of `v`: the three transpositions. -/
def oddPerms (v : Fin 3 → ℝ) : List (Fin 3 → ℝ) :=
  [![v 0, v 2, v 1], ![v 2, v 1, v 0], ![v 1, v 0, v 2]]

/-- `v` with the signs `s` (`true` for `+`) on its coordinates. -/
def withSigns (s : Bool × Bool × Bool) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![if s.1 then v 0 else -v 0, if s.2.1 then v 1 else -v 1, if s.2.2 then v 2 else -v 2]

/-- The choices of three signs with an even number of plus signs. -/
def plusEven : List (Bool × Bool × Bool) :=
  [(false, false, false), (true, true, false), (true, false, true), (false, true, true)]

/-- The choices of three signs with an odd number of plus signs. -/
def plusOdd : List (Bool × Bool × Bool) :=
  [(true, true, true), (true, false, false), (false, true, false), (false, false, true)]

/-- All eight choices of three signs. -/
def allSigns : List (Bool × Bool × Bool) :=
  plusEven ++ plusOdd

open Classical in
/-- **The rhombicosidodecahedron** with edge length `2`: the even permutations of `(±1, ±1, ±φ³)`,
`(±φ², ±φ, ±2φ)` and `(±(2 + φ), 0, ±φ²)`. -/
noncomputable def rhombicosidodecahedron : Finset (Fin 3 → ℝ) :=
  ([![1, 1, φ ^ 3], ![φ ^ 2, φ, 2 * φ], ![2 + φ, 0, φ ^ 2]].flatMap fun v ↦
    allSigns.flatMap fun s ↦ evenPerms (withSigns s v)).toFinset

open Classical in
/-- **The snub cube**, for the tribonacci constant `t` (the real root of `t³ = t² + t + 1`): the
even permutations of `(±1, ±1/t, ±t)` with an odd number of plus signs and the odd permutations
with an even number of plus signs. The opposite choice (even with even, odd with odd) gives the
mirror image. -/
noncomputable def snubCube (t : ℝ) : Finset (Fin 3 → ℝ) :=
  ((plusOdd.flatMap fun s ↦ evenPerms (withSigns s ![1, 1 / t, t])) ++
    plusEven.flatMap fun s ↦ oddPerms (withSigns s ![1, 1 / t, t])).toFinset

open Classical in
/-- **The snub dodecahedron**, for the real root `ξ` of `ξ³ - 2ξ = φ`, with `α = ξ - 1/ξ` and
`β = ξφ + φ² + φ/ξ`: the even permutations, with an even number of plus signs, of `(2α, 2, 2β)`,
`(α + β/φ + φ, -αφ + β + 1/φ, α/φ + βφ - 1)`, `(-α/φ + βφ + 1, -α + β/φ - φ, αφ + β - 1/φ)`,
`(-α/φ + βφ - 1, α - β/φ - φ, αφ + β + 1/φ)` and `(α + β/φ - φ, αφ - β + 1/φ, α/φ + βφ + 1)`. -/
noncomputable def snubDodecahedron (ξ : ℝ) : Finset (Fin 3 → ℝ) :=
  let α := ξ - 1 / ξ
  let β := ξ * φ + φ ^ 2 + φ / ξ
  ([![2 * α, 2, 2 * β],
    ![α + β / φ + φ, -α * φ + β + 1 / φ, α / φ + β * φ - 1],
    ![-α / φ + β * φ + 1, -α + β / φ - φ, α * φ + β - 1 / φ],
    ![-α / φ + β * φ - 1, α - β / φ - φ, α * φ + β + 1 / φ],
    ![α + β / φ - φ, α * φ - β + 1 / φ, α / φ + β * φ + 1]].flatMap fun v ↦
    plusEven.flatMap fun s ↦ evenPerms (withSigns s v)).toFinset

/-- **The rotation by the angle `θ` about the axis `ℝ n`** (`n ≠ 0`), by Rodrigues' formula with
the unit vector `u = n / ‖n‖`: `x ↦ cos θ • x + sin θ • (u × x) + (1 - cos θ) (u ⬝ᵥ x) • u`. -/
noncomputable def rotAbout (n : Fin 3 → ℝ) (θ : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  let u := (√(n ⬝ᵥ n))⁻¹ • n
  cos θ • x + sin θ • (u ⨯₃ x) + ((1 - cos θ) * (u ⬝ᵥ x)) • u

open Classical in
/-- **Gyration**: the points `x` of `V` with `t ≤ n ⬝ᵥ x` rotated by `36°` about the axis `ℝ n`,
the others kept. -/
noncomputable def gyrate (V : Finset (Fin 3 → ℝ)) (n : Fin 3 → ℝ) (t : ℝ) :
    Finset (Fin 3 → ℝ) :=
  V.image fun x ↦ if t ≤ n ⬝ᵥ x then rotAbout n (π / 5) x else x

open Classical in
/-- **Diminishing**: the points `x` of `V` with `n ⬝ᵥ x ≤ t`. -/
noncomputable def diminish (V : Finset (Fin 3 → ℝ)) (n : Fin 3 → ℝ) (t : ℝ) :
    Finset (Fin 3 → ℝ) :=
  V.filter fun x ↦ n ⬝ᵥ x ≤ t

end Nieuwland.Identity

namespace Nieuwland

open Identity

/-- **`Q` is the polar reciprocal of `P`, moved by `f`**: `P` is the hull of some of its given
points with a facet certificate (`IsFaceCert`) whose planes `n ⬝ᵥ x = h` have `h > 0` (the origin
is inside), and `Q`'s vertices are the images under `f` of the poles `h⁻¹ • n` of these planes.
For `f = id`, `Q` is the polar of `P` in the unit sphere about the origin (the certificate lists
all facets of `P`: module docs of `Modules/Identity/Faces.lean`). -/
def Polyhedron.IsPolarOf (Q P : Polyhedron) (f : (Fin 3 → ℝ) → Fin 3 → ℝ) : Prop :=
  ∃ pts : List (Fin 3 → ℝ), ∃ faces : List Face, (∀ x ∈ pts, x ∈ P.vertices) ∧
    P.hull = convexHull ℝ {x | x ∈ pts} ∧ IsFaceCert pts faces ∧ (∀ F ∈ faces, 0 < F.h) ∧
    (Q.vertices : Set (Fin 3 → ℝ)) = {y | ∃ F ∈ faces, y = f (F.h⁻¹ • F.n)}

end Nieuwland
