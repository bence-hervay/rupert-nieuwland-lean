import Modules.NoFit.Symmetry

/-!
# The orbit score

The score of symmetry exclusion in certificates (`code/src/proof/symmetry.rs`):

  `orbitScore a b w u R = a (u ⬝ᵥ w)² / (|u|² |w|²) + b tr R`.

It does not depend on the length of `u` (`orbitScore_smul`), as
`Polyhedron.not_isRupert_of_excluded` requires. For a rotation `R` with unit quaternion `q`,
`tr R = 4 q₀² - 1`; so with `a = 4 α` and `b = 1` the score is `4 (α cos²(u, w) + q₀²) - 1`, an
increasing function of the score `α cos²(u, w) + q₀² / |q|²` of `symmetry.rs`.

Under a pose map with rotations `A`, `B` and a turn, the score changes by a rational function of
`u` and `R`: `orbitScore_map_sub_one` without a half-turn, `orbitScore_map_sub_neg_one` with one.
`Modules/Check/Leaf/Exclusion.lean` clears its denominators in chart variables.
-/

open Matrix

namespace Nieuwland

/-- The orbit score `a (u ⬝ᵥ w)² / (|u|² |w|²) + b tr R` of a pose `(u, R)`. -/
noncomputable def orbitScore (a b : ℝ) (w u : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  a * (u ⬝ᵥ w) ^ 2 / ((u ⬝ᵥ u) * (w ⬝ᵥ w)) + b * trace R

theorem orbitScore_smul (a b : ℝ) (w : Fin 3 → ℝ) {c : ℝ} (hc : c ≠ 0) (u : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ) : orbitScore a b w (c • u) R = orbitScore a b w u R := by
  rcases eq_or_ne (u ⬝ᵥ u) 0 with hu | hu
  · have h0 : u = 0 := dotProduct_self_eq_zero.mp hu
    simp [orbitScore, h0]
  rcases eq_or_ne (w ⬝ᵥ w) 0 with hw | hw
  · simp [orbitScore, hw]
  simp only [orbitScore, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  field_simp

/-- `tr (x yᵀ N) = y ⬝ᵥ N x`. -/
theorem trace_vecMulVec_mul (x y : Fin 3 → ℝ) (N : Matrix (Fin 3) (Fin 3) ℝ) :
    trace (vecMulVec x y * N) = y ⬝ᵥ (N *ᵥ x) := by
  simp only [trace, diag, mul_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

section Map

variable {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : Aᵀ * A = 1)
include hA

theorem dotProduct_mulVec_of_transpose_mul (u x : Fin 3 → ℝ) :
    (A *ᵥ u) ⬝ᵥ (A *ᵥ x) = u ⬝ᵥ x := by
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hA, one_mulVec]

/-- The trace of the rotation of a folding pose map: with `v = A u`,
`|u|² tr (H_v A R B) = 2 u ⬝ᵥ R B A u - |u|² tr (B A R)`. -/
theorem trace_halfTurn_mul {u : Fin 3 → ℝ} (hu : u ≠ 0) (R B : Matrix (Fin 3) (Fin 3) ℝ) :
    (u ⬝ᵥ u) * trace (halfTurn (A *ᵥ u) * A * R * B) =
      2 * (u ⬝ᵥ (R *ᵥ ((B * A) *ᵥ u))) - (u ⬝ᵥ u) * trace (B * A * R) := by
  have hd : u ⬝ᵥ u ≠ 0 := dotProduct_self_eq_zero.not.mpr hu
  have hv : vecMulVec (A *ᵥ u) (A *ᵥ u) * A * R * B =
      vecMulVec (A *ᵥ u) (A *ᵥ u) * (A * R * B) := by
    simp only [Matrix.mul_assoc]
  have htr : trace (vecMulVec (A *ᵥ u) (A *ᵥ u) * (A * R * B)) = u ⬝ᵥ (R *ᵥ ((B * A) *ᵥ u)) := by
    rw [trace_vecMulVec_mul]
    simp only [← mulVec_mulVec]
    rw [dotProduct_mulVec_of_transpose_mul hA]
  have hcomm : trace (A * R * B) = trace (B * A * R) := by
    rw [trace_mul_comm, Matrix.mul_assoc]
  rw [halfTurn, dotProduct_mulVec_of_transpose_mul hA, sub_mul, sub_mul, sub_mul,
    Matrix.one_mul, smul_mul, smul_mul, smul_mul, trace_sub, trace_smul, hv, htr, hcomm,
    smul_eq_mul]
  field_simp

/-- **Improvement without a half-turn.** -/
theorem orbitScore_map_sub_one (a b : ℝ) {w : Fin 3 → ℝ} (hw : w ≠ 0) {u : Fin 3 → ℝ}
    (hu : u ≠ 0) (R B : Matrix (Fin 3) (Fin 3) ℝ) :
    (u ⬝ᵥ u) * (w ⬝ᵥ w) *
        (orbitScore a b w (A *ᵥ u) (turn 1 (A *ᵥ u) * A * R * B) - orbitScore a b w u R) =
      a * ((u ⬝ᵥ (Aᵀ *ᵥ w)) ^ 2 - (u ⬝ᵥ w) ^ 2) +
        b * (u ⬝ᵥ u) * (w ⬝ᵥ w) * (trace (B * A * R) - trace R) := by
  have hu' : u ⬝ᵥ u ≠ 0 := dotProduct_self_eq_zero.not.mpr hu
  have hw' : w ⬝ᵥ w ≠ 0 := dotProduct_self_eq_zero.not.mpr hw
  have hdot : (A *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (Aᵀ *ᵥ w) := by
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
  have hcomm : trace (A * R * B) = trace (B * A * R) := by
    rw [trace_mul_comm, Matrix.mul_assoc]
  rw [turn_one, Matrix.one_mul, orbitScore, orbitScore, dotProduct_mulVec_of_transpose_mul hA,
    hdot, hcomm]
  field_simp
  ring

/-- **Improvement with a half-turn** (a fold). -/
theorem orbitScore_map_sub_neg_one (a b : ℝ) {w : Fin 3 → ℝ} (hw : w ≠ 0) {u : Fin 3 → ℝ}
    (hu : u ≠ 0) (R B : Matrix (Fin 3) (Fin 3) ℝ) :
    (u ⬝ᵥ u) * (w ⬝ᵥ w) *
        (orbitScore a b w (A *ᵥ u) (turn (-1) (A *ᵥ u) * A * R * B) - orbitScore a b w u R) =
      a * ((u ⬝ᵥ (Aᵀ *ᵥ w)) ^ 2 - (u ⬝ᵥ w) ^ 2) +
        b * (w ⬝ᵥ w) * (2 * (u ⬝ᵥ (R *ᵥ ((B * A) *ᵥ u))) -
          (u ⬝ᵥ u) * (trace (B * A * R) + trace R)) := by
  have hu' : u ⬝ᵥ u ≠ 0 := dotProduct_self_eq_zero.not.mpr hu
  have hw' : w ⬝ᵥ w ≠ 0 := dotProduct_self_eq_zero.not.mpr hw
  have hdot : (A *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (Aᵀ *ᵥ w) := by
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
  have htr := trace_halfTurn_mul hA hu R B
  rw [turn_neg_one, orbitScore, orbitScore, dotProduct_mulVec_of_transpose_mul hA, hdot]
  have : trace (halfTurn (A *ᵥ u) * A * R * B) =
      (2 * (u ⬝ᵥ (R *ᵥ ((B * A) *ᵥ u))) - (u ⬝ᵥ u) * trace (B * A * R)) / (u ⬝ᵥ u) := by
    rw [← htr]
    field_simp
  rw [this]
  field_simp
  ring

end Map

end Nieuwland
