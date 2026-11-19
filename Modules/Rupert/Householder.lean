import Modules.Rupert.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Turning a direction to the `z`-axis

For every nonzero `u ∈ ℝ³` there is a rotation `Q` whose shadow map `x ↦ projXY (Q *ᵥ x)`
vanishes exactly on the line `ℝ ∙ u` (`exists_mem_SO3_ker_eq_span`): `Q` turns the viewing
direction `u` to the `z`-axis. This lets a fit seen along any direction, in any screen
coordinates, be moved to the standard position of `Polyhedron.IsRupert`
(`Modules/Rupert/Screen.lean`).

`Q` is the Householder reflection (`householder`) exchanging `u` and `‖u‖ e_z`, followed by
`reflectZ` to make the determinant `1`. Its entries involve `√(u ⬝ᵥ u)`, but only its existence is
used: concrete proofs never write it down.
-/

open Matrix

namespace Nieuwland

section Householder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Householder matrix `1 - (2 / (w ⬝ᵥ w)) w wᵀ`: the reflection of `ℝⁿ` in the hyperplane
orthogonal to `w`. For `w = 0` it is the identity, since `2 / 0 = 0` in Lean. -/
noncomputable def householder (w : n → ℝ) : Matrix n n ℝ :=
  1 - (2 / (w ⬝ᵥ w)) • vecMulVec w w

theorem householder_mulVec (w x : n → ℝ) :
    householder w *ᵥ x = x - (2 * (w ⬝ᵥ x) / (w ⬝ᵥ w)) • w := by
  rw [householder, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
    smul_smul]
  ring_nf

theorem householder_transpose (w : n → ℝ) : (householder w)ᵀ = householder w := by
  simp [householder, transpose_sub, transpose_smul]

theorem householder_mul_self (w : n → ℝ) : householder w * householder w = 1 := by
  by_cases hw : w ⬝ᵥ w = 0
  · simp [householder, hw]
  · have hsq : vecMulVec w w * vecMulVec w w = (w ⬝ᵥ w) • vecMulVec w w := by
      rw [vecMulVec_mul_vecMulVec, vecMulVec_smul]
    have hc : 2 / (w ⬝ᵥ w) * (2 / (w ⬝ᵥ w)) * (w ⬝ᵥ w) = 2 * (2 / (w ⬝ᵥ w)) := by
      field_simp
    rw [householder, sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, smul_mul_smul_comm,
      hsq, smul_smul, hc, two_mul, add_smul]
    abel

theorem householder_mem_orthogonalGroup (w : n → ℝ) : householder w ∈ orthogonalGroup n ℝ := by
  rw [mem_orthogonalGroup_iff, householder_transpose, householder_mul_self]

end Householder

/-- **Turning a direction to the `z`-axis.** For every nonzero `u ∈ ℝ³` there is a rotation `Q`
such that `projXY (Q *ᵥ x) = 0` exactly for the multiples `x` of `u`. -/
theorem exists_mem_SO3_ker_eq_span {u : Fin 3 → ℝ} (hu : u ≠ 0) :
    ∃ Q ∈ SO(3), LinearMap.ker (projXYₗ ∘ₗ Q.mulVecLin) = ℝ ∙ u := by
  have huu : u ⬝ᵥ u = u 0 * u 0 + u 1 * u 1 + u 2 * u 2 := by
    simp [dotProduct, Fin.sum_univ_three]
  have hnn : 0 ≤ u ⬝ᵥ u := Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (u i)
  have hpos : 0 < u ⬝ᵥ u := lt_of_le_of_ne hnn (Ne.symm (dotProduct_self_eq_zero.not.mpr hu))
  -- `r = ‖u‖`, `e = e_z`, and `H` is the reflection exchanging `u` and `r • e`.
  set r := √(u ⬝ᵥ u)
  have hr : 0 < r := Real.sqrt_pos.mpr hpos
  have hrr : r * r = u 0 * u 0 + u 1 * u 1 + u 2 * u 2 := by
    rw [← huu]; exact Real.mul_self_sqrt hnn
  set e : Fin 3 → ℝ := Pi.single 2 1
  set w := u - r • e
  set H := householder w
  have hwe : w ⬝ᵥ e = u 2 - r := by simp [w, e, dotProduct, Fin.sum_univ_three]
  have hww : w ⬝ᵥ w = 2 * r * (r - u 2) := by
    simp only [w, e, dotProduct, Fin.sum_univ_three]
    simp
    linear_combination (-1 : ℝ) * hrr
  have hHe : H *ᵥ e = r⁻¹ • u := by
    rw [householder_mulVec, hww, hwe]
    by_cases h2 : r - u 2 = 0
    · -- `u` is a positive multiple of `e`, and `H = 1`.
      have h0 : u 0 = 0 := by nlinarith
      have h1 : u 1 = 0 := by nlinarith
      have h2' : u 2 = r := by linarith
      ext i
      fin_cases i <;> simp [e, h0, h1, h2', hr.ne']
    · ext i
      fin_cases i <;> simp [w, e] <;> field_simp <;> ring
  have hHH (x : Fin 3 → ℝ) : H *ᵥ (H *ᵥ x) = x := by
    rw [mulVec_mulVec, householder_mul_self, one_mulVec]
  have hHu : H *ᵥ u = r • e := by
    calc H *ᵥ u = H *ᵥ (r • (H *ᵥ e)) := by
          rw [hHe, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      _ = r • e := by rw [mulVec_smul, hHH]
  obtain ⟨Q, hQ, hQH⟩ := exists_mem_SO3_projXY_mulVec_eq (R := H)
    (householder_mem_orthogonalGroup w)
  refine ⟨Q, hQ, ?_⟩
  ext x
  simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, mulVecLin_apply,
    projXYₗ_apply, hQH, Submodule.mem_span_singleton]
  constructor
  · intro hx
    set c := (H *ᵥ x) 2
    have hHx : H *ᵥ x = c • e := by
      have h0 : (H *ᵥ x) 0 = 0 := congrFun hx 0
      have h1 : (H *ᵥ x) 1 = 0 := congrFun hx 1
      ext i
      fin_cases i <;> simp [e, h0, h1, c]
    refine ⟨c * r⁻¹, ?_⟩
    calc (c * r⁻¹) • u = c • (H *ᵥ e) := by rw [hHe, smul_smul]
      _ = H *ᵥ (H *ᵥ x) := by rw [hHx, mulVec_smul]
      _ = x := hHH x
  · rintro ⟨a, rfl⟩
    rw [mulVec_smul, hHu, smul_smul]
    ext i
    fin_cases i <;> simp [projXY, e]

end Nieuwland
