import Modules.NoFit.Symmetry
import Modules.Rupert.Quat

/-!
# Pre-rotated poses

A chart box can be *pre-rotated* by a nonzero quaternion `q_c` (`ChartBox::pre` in
`code/src/proof/mod.rs`): the quaternion of its chart point `x` is then `q(x) q_c`, whose rotation
`R(q(x) q_c) = R(q(x)) R(q_c)` (`quatRotation_qmul`) turns the body by `R(q_c)` before the chart
rotation. Images of chart boxes under pose maps are pre-rotated boxes, and chart changes in covers
lead into them.

`Polyhedron.NoFitRot P S Rc`: no chart pose `p ∈ S` fits with the rotation `p.rotation * Rc`, along
its view and with any translation. Without a pre-rotation (`Rc = 1`) this is `NoFit`
(`Polyhedron.noFitRot_one`).

Pose maps (`Modules/Check/Chart/Image.lean`) act on quaternions by products, with a half-turn for a fold:
the pure quaternion `(0, w)` is the half-turn about `w` (`quatRotation_pureQ`). Fits along `u` do
not depend on the length of `u` (`Polyhedron.fitsAlong_smul_iff`).
-/

open Matrix

namespace Nieuwland

/-- **Pure quaternions are half-turns.** -/
theorem quatRotation_pureQ {w : Fin 3 → ℝ} (hw : w ≠ 0) : quatRotation (pureQ w) = halfTurn w := by
  have hd : w ⬝ᵥ w ≠ 0 := dotProduct_self_eq_zero.not.mpr hw
  have hd' : w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 ≠ 0 := by
    simpa [dotProduct, Fin.sum_univ_three, sq] using hd
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatRotation, quatMatrix, pureQ, halfTurn, vecMulVec_apply, dotProduct,
      Fin.sum_univ_four, Fin.sum_univ_three, one_apply] <;>
    field_simp <;> ring

namespace Polyhedron

variable {P : Polyhedron}

theorem FitsAlong.smul {u : Fin 3 → ℝ} {R : Matrix (Fin 3) (Fin 3) ℝ} (h : P.FitsAlong u R)
    {c : ℝ} (hc : c ≠ 0) : P.FitsAlong (c • u) R := by
  obtain ⟨L, hL, hker, τ, hτ⟩ := h
  exact ⟨L, hL, by rw [hker, Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc)], τ, hτ⟩

/-- Fits along `u` do not depend on the length of `u`. -/
theorem fitsAlong_smul_iff {u : Fin 3 → ℝ} {R : Matrix (Fin 3) (Fin 3) ℝ} {c : ℝ} (hc : c ≠ 0) :
    P.FitsAlong (c • u) R ↔ P.FitsAlong u R := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.smul hc⟩
  have := h.smul (inv_ne_zero hc)
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

/-- No chart pose `p ∈ S` fits `P` with the rotation `p.rotation * Rc` (the rotation `Rc` first),
along its view and with any translation. -/
def NoFitRot (P : Polyhedron) (S : Set ChartPose) (Rc : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ p ∈ S, ¬ P.FitsAlong (viewDir p.view p.s p.t) (p.rotation * Rc)

theorem NoFitRot.mono {S T : Set ChartPose} {Rc : Matrix (Fin 3) (Fin 3) ℝ}
    (h : P.NoFitRot T Rc) (hST : S ⊆ T) : P.NoFitRot S Rc :=
  fun p hp ↦ h p (hST hp)

/-- **Without a pre-rotation**, `NoFitRot` is `NoFit`. -/
theorem noFitRot_one {S : Set ChartPose} : P.NoFitRot S 1 ↔ P.NoFit S := by
  constructor
  · intro h p hp τ hfit
    exact h p hp (by rw [mul_one]; exact fitsAlong_of_fitsAt hfit)
  · intro h p hp hfit
    rw [mul_one] at hfit
    obtain ⟨τ, hτ⟩ := hfit.exists_fitsAt (p := p) one_ne_zero (one_smul ℝ _).symm rfl
    exact h p hp τ hτ

end Polyhedron

end Nieuwland
