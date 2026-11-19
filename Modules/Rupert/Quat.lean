import Modules.Rupert.Charts

/-!
# Products of quaternions

The Hamilton product `qmul p q` of quaternions `(w, x, y, z)`, as in `qmul` of
`code/src/proof/symmetry.rs`. Rotation matrices and norms multiply: `Q(p q) = Q(p) Q(q)`
(`quatMatrix_qmul`) and `|p q|² = |p|² |q|²` (`qmul_dot_self`), so `R(p q) = R(p) R(q)`
(`quatRotation_qmul`).
-/

open Matrix

namespace Nieuwland

section CommRing

variable {R : Type*} [CommRing R]

/-- The Hamilton product of quaternions `(w, x, y, z)`. -/
def qmul (p q : Fin 4 → R) : Fin 4 → R :=
  ![p 0 * q 0 - p 1 * q 1 - p 2 * q 2 - p 3 * q 3,
    p 0 * q 1 + p 1 * q 0 + p 2 * q 3 - p 3 * q 2,
    p 0 * q 2 - p 1 * q 3 + p 2 * q 0 + p 3 * q 1,
    p 0 * q 3 + p 1 * q 2 - p 2 * q 1 + p 3 * q 0]

/-- **Rotation matrices multiply**: `Q(p q) = Q(p) Q(q)`. -/
theorem quatMatrix_qmul (p q : Fin 4 → R) :
    quatMatrix (qmul p q) = quatMatrix p * quatMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatMatrix, qmul, mul_apply, Fin.sum_univ_three] <;> ring

/-- **Norms multiply**: `|p q|² = |p|² |q|²`. -/
theorem qmul_dot_self (p q : Fin 4 → R) : qmul p q ⬝ᵥ qmul p q = (p ⬝ᵥ p) * (q ⬝ᵥ q) := by
  simp [qmul, dotProduct, Fin.sum_univ_four]
  ring

/-- Right multiplication by `c` scales inner products by `|c|²`. -/
theorem qmul_dot_qmul (a b c : Fin 4 → R) : qmul a c ⬝ᵥ qmul b c = (a ⬝ᵥ b) * (c ⬝ᵥ c) := by
  simp [qmul, dotProduct, Fin.sum_univ_four]
  ring

theorem qmul_smul_left (a : R) (p q : Fin 4 → R) : qmul (a • p) q = a • qmul p q := by
  funext i
  fin_cases i <;> simp [qmul] <;> ring

theorem qmul_add_left (p p' q : Fin 4 → R) : qmul (p + p') q = qmul p q + qmul p' q := by
  funext i
  fin_cases i <;> simp [qmul] <;> ring

theorem qmul_smul_right (a : R) (p q : Fin 4 → R) : qmul p (a • q) = a • qmul p q := by
  funext i
  fin_cases i <;> simp [qmul] <;> ring

/-- The conjugate `(w, -x, -y, -z)`. -/
def qconj (q : Fin 4 → R) : Fin 4 → R :=
  ![q 0, -q 1, -q 2, -q 3]

/-- `(p q̄) q = |q|² p`. -/
theorem qmul_qconj_mul (p q : Fin 4 → R) : qmul (qmul p (qconj q)) q = (q ⬝ᵥ q) • p := by
  funext i
  fin_cases i <;> simp [qmul, qconj, dotProduct, Fin.sum_univ_four] <;> ring

/-- The pure quaternion `(0, w)`. -/
def pureQ (w : Fin 3 → R) : Fin 4 → R :=
  ![0, w 0, w 1, w 2]

theorem pureQ_smul (a : R) (w : Fin 3 → R) : pureQ (a • w) = a • pureQ w := by
  funext i
  fin_cases i <;> simp [pureQ]

end CommRing

theorem qmul_ne_zero {p q : Fin 4 → ℝ} (hp : p ≠ 0) (hq : q ≠ 0) : qmul p q ≠ 0 := fun h ↦ by
  have h2 := qmul_dot_self p q
  rw [h, dotProduct_zero] at h2
  exact mul_ne_zero (dotProduct_self_eq_zero.not.mpr hp) (dotProduct_self_eq_zero.not.mpr hq)
    h2.symm

/-- **Rotations multiply**: `R(p q) = R(p) R(q)`. -/
theorem quatRotation_qmul (p q : Fin 4 → ℝ) :
    quatRotation (qmul p q) = quatRotation p * quatRotation q := by
  rw [quatRotation, quatRotation, quatRotation, quatMatrix_qmul, qmul_dot_self, mul_inv,
    smul_mul_smul_comm]

end Nieuwland
