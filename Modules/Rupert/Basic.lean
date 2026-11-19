import Modules.Rupert.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.Basic

/-!
# Basic facts about the Rupert property

Small reformulations of `Polyhedron.IsRupert` that later files and concrete proofs use.

* `projXY` is linear (`projXYₗ`), and for an orthogonal `R` the shadow map `x ↦ projXY (R *ᵥ x)`
  is onto (`projXY_mulVec_surjective`).
* The translation may act in space, before projecting, instead of in the plane
  (`Polyhedron.isRupert_iff_exists_translate`).
* Allowing improper rotations, all of `O(3)`, gives the same property
  (`Polyhedron.isRupert_iff_orthogonal`): `reflectZ = diag(1, 1, -1)` flips the sign of the
  determinant and changes no shadow.

## Notation

* `O(3)`: `Matrix.orthogonalGroup (Fin 3) ℝ`, the real `3 × 3` matrices `R` with `R * Rᵀ = 1`
  (scoped in `Nieuwland`, like `SO(3)`).
-/

open Matrix

namespace Nieuwland

/-- `O(3)`: the real `3 × 3` matrices `R` with `R * Rᵀ = 1`. -/
scoped notation "O(3)" => Matrix.orthogonalGroup (Fin 3) ℝ

/-! ### Orthogonal matrices -/

theorem mul_transpose_of_mem_orthogonalGroup {n : Type*} [Fintype n] [DecidableEq n]
    {R : Matrix n n ℝ} (hR : R ∈ orthogonalGroup n ℝ) : R * Rᵀ = 1 := by
  rwa [mem_orthogonalGroup_iff] at hR

theorem transpose_mul_of_mem_orthogonalGroup {n : Type*} [Fintype n] [DecidableEq n]
    {R : Matrix n n ℝ} (hR : R ∈ orthogonalGroup n ℝ) : Rᵀ * R = 1 := by
  rwa [mem_orthogonalGroup_iff'] at hR

/-- An orthogonal matrix has determinant `1` or `-1`. -/
theorem det_eq_one_or_eq_neg_one_of_mem_orthogonalGroup {n : Type*} [Fintype n] [DecidableEq n]
    {R : Matrix n n ℝ} (hR : R ∈ orthogonalGroup n ℝ) : R.det = 1 ∨ R.det = -1 := by
  have h := congrArg det (mul_transpose_of_mem_orthogonalGroup hR)
  rwa [det_mul, det_transpose, det_one, mul_self_eq_one_iff] at h

/-- The transpose (inverse) of a rotation is a rotation. -/
theorem transpose_mem_SO3 {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO(3)) : Rᵀ ∈ SO(3) := by
  rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff, transpose_transpose,
    det_transpose]
  exact ⟨transpose_mul_of_mem_orthogonalGroup hR.1, hR.2⟩

/-! ### The projection as a linear map -/

/-- `projXY` as a linear map `ℝ³ → ℝ²`. -/
def projXYₗ : (Fin 3 → ℝ) →ₗ[ℝ] Fin 2 → ℝ where
  toFun := projXY
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' c x := by ext i; fin_cases i <;> rfl

@[simp]
theorem projXYₗ_apply (x : Fin 3 → ℝ) : projXYₗ x = projXY x :=
  rfl

theorem projXY_add (x y : Fin 3 → ℝ) : projXY (x + y) = projXY x + projXY y :=
  projXYₗ.map_add x y

/-- `projXY` forgets the third coordinate: `(a, b, 0) ↦ (a, b)`. -/
theorem projXY_vec3 (y : Fin 2 → ℝ) : projXY ![y 0, y 1, 0] = y := by
  ext i; fin_cases i <;> rfl

/-- For an orthogonal matrix `R`, every point of the plane is the shadow `projXY (R *ᵥ x)` of
some point `x`. -/
theorem projXY_mulVec_surjective {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ O(3)) :
    Function.Surjective fun x ↦ projXY (R *ᵥ x) := fun y ↦
  ⟨Rᵀ *ᵥ ![y 0, y 1, 0], by
    simp only [mulVec_mulVec, mul_transpose_of_mem_orthogonalGroup hR, one_mulVec, projXY_vec3]⟩

/-! ### Translating in space -/

/-- The translation may be applied in space, before projecting: `P` is Rupert iff some rotated
copy `R₁ P + s`, with `s ∈ ℝ³`, casts a shadow in the interior of the shadow of `R₂ P`. -/
theorem Polyhedron.isRupert_iff_exists_translate (P : Polyhedron) :
    P.IsRupert ↔ ∃ R₁ ∈ SO(3), ∃ R₂ ∈ SO(3), ∃ s : Fin 3 → ℝ,
      {projXY (R₁ *ᵥ x + s) | x ∈ P.hull} ⊆ interior {projXY (R₂ *ᵥ x) | x ∈ P.hull} := by
  simp only [projXY_add]
  constructor
  · rintro ⟨R₁, hR₁, R₂, hR₂, t, h⟩
    exact ⟨R₁, hR₁, R₂, hR₂, ![t 0, t 1, 0], by rwa [projXY_vec3]⟩
  · rintro ⟨R₁, hR₁, R₂, hR₂, s, h⟩
    exact ⟨R₁, hR₁, R₂, hR₂, projXY s, h⟩

/-! ### Improper rotations -/

/-- The reflection `diag(1, 1, -1)` in the `xy`-plane. It changes no shadow. -/
def reflectZ : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal ![1, 1, -1]

theorem projXY_reflectZ_mulVec (x : Fin 3 → ℝ) : projXY (reflectZ *ᵥ x) = projXY x := by
  ext i; fin_cases i <;> simp [projXY, reflectZ, mulVec_diagonal]

theorem reflectZ_mem : reflectZ ∈ O(3) := by
  rw [mem_orthogonalGroup_iff, reflectZ, diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  ext i; fin_cases i <;> norm_num

theorem det_reflectZ : reflectZ.det = -1 := by
  simp [reflectZ, det_diagonal, Fin.prod_univ_three]

/-- Every orthogonal matrix has the same shadow map as some rotation: itself or `reflectZ * R`. -/
theorem exists_mem_SO3_projXY_mulVec_eq {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ O(3)) :
    ∃ R' ∈ SO(3), ∀ x, projXY (R' *ᵥ x) = projXY (R *ᵥ x) := by
  rcases det_eq_one_or_eq_neg_one_of_mem_orthogonalGroup hR with h | h
  · exact ⟨R, ⟨hR, h⟩, fun _ ↦ rfl⟩
  · refine ⟨reflectZ * R, mem_specialOrthogonalGroup_iff.mpr
      ⟨Submonoid.mul_mem _ reflectZ_mem hR, ?_⟩, fun x ↦ ?_⟩
    · rw [det_mul, det_reflectZ, h]; norm_num
    · rw [← mulVec_mulVec, projXY_reflectZ_mulVec]

/-- **`O(3)` versus `SO(3)`.** Allowing improper rotations for both copies gives the same
property. -/
theorem Polyhedron.isRupert_iff_orthogonal (P : Polyhedron) :
    P.IsRupert ↔ ∃ R₁ ∈ O(3), ∃ R₂ ∈ O(3), ∃ t : Fin 2 → ℝ,
      {projXY (R₁ *ᵥ x) + t | x ∈ P.hull} ⊆ interior {projXY (R₂ *ᵥ x) | x ∈ P.hull} := by
  constructor
  · rintro ⟨R₁, hR₁, R₂, hR₂, t, h⟩
    exact ⟨R₁, hR₁.1, R₂, hR₂.1, t, h⟩
  · rintro ⟨R₁, hR₁, R₂, hR₂, t, h⟩
    obtain ⟨R₁', hR₁', h₁⟩ := exists_mem_SO3_projXY_mulVec_eq hR₁
    obtain ⟨R₂', hR₂', h₂⟩ := exists_mem_SO3_projXY_mulVec_eq hR₂
    exact ⟨R₁', hR₁', R₂', hR₂', t, by simpa only [h₁, h₂]⟩

end Nieuwland
