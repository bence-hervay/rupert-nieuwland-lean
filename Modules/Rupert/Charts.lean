import Modules.Rupert.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.FieldSimp

/-!
# Chart coordinates for poses

The parametrisation of `RESEARCH.md` §2.2–2.3, with the conventions of the Rust module
`code/src/geometry/pose.rs`. The exact fits in `fixtures/fits/` are given in these charts.

* **View charts.** Chart `a : Fin 3` with coordinates `(s, t)` views along `viewDir a s t`, the
  vector `u` with `u a = 1`, `u (a + 1) = s`, `u (a + 2) = t` (indices mod 3). Its *screen map*
  `screen a s t x = (x (a + 1) - s * x a, x (a + 2) - t * x a)` is onto (`screen_surjective`) and
  vanishes on `u` (`screen_viewDir`). Chart `2` is the dense chart `u = (s, t, 1)`, with
  `L (x, y, z) = (x - s z, y - t z)`. The screen map is not an orthogonal projection, but by
  `Polyhedron.isRupert_iff_exists_surjective` it describes the same shadows, up to an invertible
  linear map of the plane; for rational `s`, `t` it has rational entries.
* **Rotation charts.** Chart `k : Fin 4` with coordinates `x : Fin 3 → R` gives the quaternion
  `chartQuat k x`, with `q k = 1` and `x` in the other three places in increasing order. Chart `0`
  is the scalar chart `q = (1, r₁, r₂, r₃)`.
* **Quaternion rotations.** `quatMatrix q` is the matrix `Q(q)` of `RESEARCH.md` (3). It
  satisfies `Q Qᵀ = |q|⁴ 1` and `det Q = |q|⁶`, so `quatRotation q = Q(q) / |q|²` is a rotation
  whenever `q ≠ 0` (`quatRotation_mem`), and `chartRotation k x` always is.

The polynomial definitions (`viewDir`, `screen`, `quatMatrix`, `chartQuat`) are stated over any
commutative ring, so that exact computations over `ℤ` or `ℚ` transfer to `ℝ` along ring
homomorphisms.
-/

open Matrix

namespace Nieuwland

section CommRing

variable {R : Type*} [CommRing R]

/-- The viewing direction of view chart `a` at coordinates `(s, t)`: `u a = 1`, `u (a + 1) = s`
and `u (a + 2) = t`, indices mod 3. -/
def viewDir (a : Fin 3) (s t : R) : Fin 3 → R :=
  fun i ↦ ![1, s, t] (i - a)

/-- The screen map of view chart `a` at coordinates `(s, t)`:
`x ↦ (x (a + 1) - s * x a, x (a + 2) - t * x a)`. Its kernel is the line through
`viewDir a s t`. -/
def screen (a : Fin 3) (s t : R) (x : Fin 3 → R) : Fin 2 → R :=
  ![x (a + 1) - s * x a, x (a + 2) - t * x a]

theorem screen_viewDir (a : Fin 3) (s t : R) : screen a s t (viewDir a s t) = 0 := by
  ext i
  fin_cases i <;> simp [screen, viewDir]

theorem screen_surjective (a : Fin 3) (s t : R) : Function.Surjective (screen a s t) := by
  intro y
  refine ⟨fun i ↦ ![0, y 0, y 1] (i - a), ?_⟩
  ext i
  fin_cases i <;> simp [screen]

/-- The screen map of view chart `a` as a linear map. -/
def screenₗ (a : Fin 3) (s t : R) : (Fin 3 → R) →ₗ[R] Fin 2 → R where
  toFun := screen a s t
  map_add' x y := by
    ext i
    fin_cases i <;> simp [screen] <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [screen] <;> ring

@[simp]
theorem screenₗ_apply (a : Fin 3) (s t : R) (x : Fin 3 → R) :
    screenₗ a s t x = screen a s t x :=
  rfl

/-- The matrix `Q(q)` of `RESEARCH.md` (3). For `q ≠ 0`, `Q(q) / |q|²` is the rotation of the
unit quaternion `q / |q|`. -/
def quatMatrix (q : Fin 4 → R) : Matrix (Fin 3) (Fin 3) R :=
  !![q 0 ^ 2 + q 1 ^ 2 - q 2 ^ 2 - q 3 ^ 2, 2 * (q 1 * q 2 - q 0 * q 3),
      2 * (q 1 * q 3 + q 0 * q 2);
    2 * (q 1 * q 2 + q 0 * q 3), q 0 ^ 2 - q 1 ^ 2 + q 2 ^ 2 - q 3 ^ 2,
      2 * (q 2 * q 3 - q 0 * q 1);
    2 * (q 1 * q 3 - q 0 * q 2), 2 * (q 2 * q 3 + q 0 * q 1),
      q 0 ^ 2 - q 1 ^ 2 - q 2 ^ 2 + q 3 ^ 2]

theorem quatMatrix_mul_transpose (q : Fin 4 → R) :
    quatMatrix q * (quatMatrix q)ᵀ = ((q ⬝ᵥ q) ^ 2) • (1 : Matrix (Fin 3) (Fin 3) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatMatrix, mul_apply, Fin.sum_univ_succ, dotProduct, one_apply] <;> ring

theorem det_quatMatrix (q : Fin 4 → R) : (quatMatrix q).det = (q ⬝ᵥ q) ^ 3 := by
  simp [quatMatrix, det_fin_three, dotProduct, Fin.sum_univ_succ]
  ring

/-- The quaternion of rotation chart `k` at coordinates `x`: `q k = 1`, and `x` fills the other
three places in increasing order. -/
def chartQuat (k : Fin 4) (x : Fin 3 → R) : Fin 4 → R :=
  ![![1, x 0, x 1, x 2], ![x 0, 1, x 1, x 2], ![x 0, x 1, 1, x 2], ![x 0, x 1, x 2, 1]] k

theorem chartQuat_self (k : Fin 4) (x : Fin 3 → R) : chartQuat k x k = 1 := by
  fin_cases k <;> rfl

theorem chartQuat_ne_zero [Nontrivial R] (k : Fin 4) (x : Fin 3 → R) : chartQuat k x ≠ 0 :=
  fun h ↦ by
  have := congrFun h k
  rw [chartQuat_self] at this
  exact one_ne_zero this

end CommRing

/-- The rotation `Q(q) / |q|²` of a quaternion `q` (`RESEARCH.md` (3)). It lies in `SO(3)` for
`q ≠ 0` (`quatRotation_mem`). -/
noncomputable def quatRotation (q : Fin 4 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (q ⬝ᵥ q)⁻¹ • quatMatrix q

theorem quatRotation_mem {q : Fin 4 → ℝ} (hq : q ≠ 0) : quatRotation q ∈ SO(3) := by
  have hd : q ⬝ᵥ q ≠ 0 := dotProduct_self_eq_zero.not.mpr hq
  rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff, quatRotation, transpose_smul,
    smul_mul_smul_comm, quatMatrix_mul_transpose, smul_smul, det_smul, det_quatMatrix]
  constructor
  · rw [show (q ⬝ᵥ q)⁻¹ * (q ⬝ᵥ q)⁻¹ * (q ⬝ᵥ q) ^ 2 = 1 by field_simp, one_smul]
  · simp [Fintype.card_fin, inv_pow, hd]

/-- The rotation of rotation chart `k` at coordinates `x`. -/
noncomputable def chartRotation (k : Fin 4) (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  quatRotation (chartQuat k x)

theorem chartRotation_mem (k : Fin 4) (x : Fin 3 → ℝ) : chartRotation k x ∈ SO(3) := by
  refine quatRotation_mem fun h ↦ ?_
  have := congrFun h k
  rw [chartQuat_self] at this
  exact one_ne_zero this

/-- A pose in chart coordinates: view chart `view` at coordinates `(s, t)` and rotation chart
`rot` at coordinates `x`. This is the `Pose` of `code/src/geometry/pose.rs`; its translation is
kept separately. -/
structure ChartPose where
  /-- The view chart. -/
  view : Fin 3
  /-- The first view coordinate. -/
  s : ℝ
  /-- The second view coordinate. -/
  t : ℝ
  /-- The rotation chart. -/
  rot : Fin 4
  /-- The rotation coordinates. -/
  x : Fin 3 → ℝ

namespace ChartPose

/-- The screen map of the pose's view: shadows are seen along `viewDir view s t`. -/
def screen (p : ChartPose) : (Fin 3 → ℝ) → Fin 2 → ℝ :=
  Nieuwland.screen p.view p.s p.t

/-- The rotation of the inner copy. -/
noncomputable def rotation (p : ChartPose) : Matrix (Fin 3) (Fin 3) ℝ :=
  chartRotation p.rot p.x

theorem rotation_mem (p : ChartPose) : p.rotation ∈ SO(3) :=
  chartRotation_mem _ _

end ChartPose

end Nieuwland
