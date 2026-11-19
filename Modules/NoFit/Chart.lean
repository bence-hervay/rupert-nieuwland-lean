import Modules.NoFit.Defs
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# The chart cover

Every pose is a chart pose with coordinates in `[-1, 1]`, in one of twelve charts: three view
charts times four rotation charts (`RESEARCH.md` §2.3). So `NoFit` on the poses `unitPoses` of the
twelve unit chart boxes proves that a polyhedron is not Rupert
(`Polyhedron.not_isRupert_of_noFit`).

* **Rotations.** The rows of the symmetric matrix `rotQuat R` are quaternions of a rotation `R`,
  scaled by their diagonal entries (`rotQuat_spec`); the diagonal sums to `4`, so some row is a
  nonzero quaternion of `R` (`exists_quat_of_mem_SO3`). Scaling a quaternion does not change its
  rotation (`quatRotation_smul`), so dividing by a component of largest absolute value gives a
  chart quaternion with coordinates in `[-1, 1]` (`exists_chartRotation_eq`).
* **Views.** The kernel of a linear surjection `L : ℝ³ → ℝ²` contains a direction `u ≠ 0`.
  Divided by a component of largest absolute value, `u` is a chart view direction with
  coordinates in `[-1, 1]` (`viewDir_div`), whose screen map has kernel `ℝ ∙ u`, so it differs
  from `L` by an invertible linear map of the plane (`exists_screen_eq`).
-/

open Matrix

namespace Nieuwland

/-- A nonzero vector has a nonzero component of largest absolute value. -/
theorem exists_abs_le_abs {n : ℕ} {v : Fin n → ℝ} (hv : v ≠ 0) :
    ∃ k, v k ≠ 0 ∧ ∀ j, |v j| ≤ |v k| := by
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hv
  have : Nonempty (Fin n) := ⟨j₀⟩
  obtain ⟨k, hk⟩ := Finite.exists_max fun j ↦ |v j|
  refine ⟨k, fun h ↦ hj₀ ?_, hk⟩
  have := hk j₀
  rw [h, abs_zero] at this
  exact abs_nonpos_iff.mp this

/-! ### Rotations -/

theorem quatMatrix_smul {R : Type*} [CommRing R] (c : R) (q : Fin 4 → R) :
    quatMatrix (c • q) = c ^ 2 • quatMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quatMatrix] <;> ring

/-- Scaling a quaternion does not change its rotation. -/
theorem quatRotation_smul {c : ℝ} (hc : c ≠ 0) (q : Fin 4 → ℝ) :
    quatRotation (c • q) = quatRotation q := by
  rw [quatRotation, quatRotation, quatMatrix_smul, smul_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq, mul_inv, mul_comm (c ^ 2)⁻¹, mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero 2 hc), mul_one]

theorem quatRotation_eq_of {q : Fin 4 → ℝ} {w : ℝ} {R : Matrix (Fin 3) (Fin 3) ℝ} (hw : w ≠ 0)
    (hn : q ⬝ᵥ q = w) (hm : quatMatrix q = w • R) : quatRotation q = R := by
  rw [quatRotation, hn, hm, smul_smul, inv_mul_cancel₀ hw, one_smul]

/-- Four quaternions of a matrix `R`, the rows of a symmetric matrix. If `R` is the rotation of a
unit quaternion `q`, then `rotQuat R = 4 q qᵀ`: row `k` is `4 q k • q` (`rotQuat_spec`). -/
def rotQuat (R : Matrix (Fin 3) (Fin 3) ℝ) (k : Fin 4) : Fin 4 → ℝ :=
  ![![1 + R 0 0 + R 1 1 + R 2 2, R 2 1 - R 1 2, R 0 2 - R 2 0, R 1 0 - R 0 1],
    ![R 2 1 - R 1 2, 1 + R 0 0 - R 1 1 - R 2 2, R 0 1 + R 1 0, R 0 2 + R 2 0],
    ![R 0 2 - R 2 0, R 0 1 + R 1 0, 1 - R 0 0 + R 1 1 - R 2 2, R 1 2 + R 2 1],
    ![R 1 0 - R 0 1, R 0 2 + R 2 0, R 1 2 + R 2 1, 1 - R 0 0 - R 1 1 + R 2 2]] k

/-- The quadratic relations of a rotation: `R Rᵀ = 1`, `Rᵀ R = 1` and `adjugate R = Rᵀ`. -/
theorem mem_SO3_rels {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO(3)) :
    R * Rᵀ = 1 ∧ Rᵀ * R = 1 ∧ adjugate R = Rᵀ := by
  rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff] at hR
  have h₁ : R * Rᵀ = 1 := by simpa [star_eq_conjTranspose, conjTranspose] using hR.1
  refine ⟨h₁, mul_eq_one_comm.mp h₁, ?_⟩
  calc adjugate R = adjugate R * (R * Rᵀ) := by rw [h₁, Matrix.mul_one]
    _ = Rᵀ := by rw [← Matrix.mul_assoc, adjugate_mul, hR.2, one_smul, Matrix.one_mul]

/-- Row `k` of `rotQuat R` is a quaternion of the rotation `R`, scaled by `4 (rotQuat R k k)`.
Each identity is a linear combination of the quadratic relations of `mem_SO3_rels`. -/
theorem rotQuat_spec {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO(3)) (k : Fin 4) :
    rotQuat R k ⬝ᵥ rotQuat R k = 4 * rotQuat R k k ∧
      quatMatrix (rotQuat R k) = (4 * rotQuat R k k) • R := by
  obtain ⟨h₁, h₂, h₃⟩ := mem_SO3_rels hR
  have e₁ (i j : Fin 3) := congrFun (congrFun h₁ i) j
  have e₂ (i j : Fin 3) := congrFun (congrFun h₂ i) j
  have e₃ (i j : Fin 3) := congrFun (congrFun h₃ i) j
  simp only [mul_apply, Fin.sum_univ_three, transpose_apply, adjugate_fin_three] at e₁ e₂ e₃
  have r₀₀ := e₁ 0 0; have r₀₁ := e₁ 0 1; have r₀₂ := e₁ 0 2
  have r₁₁ := e₁ 1 1; have r₁₂ := e₁ 1 2; have r₂₂ := e₁ 2 2
  have c₀₀ := e₂ 0 0; have c₀₁ := e₂ 0 1; have c₀₂ := e₂ 0 2
  have c₁₁ := e₂ 1 1; have c₁₂ := e₂ 1 2; have c₂₂ := e₂ 2 2
  have a₀₀ := e₃ 0 0; have a₀₁ := e₃ 0 1; have a₀₂ := e₃ 0 2
  have a₁₀ := e₃ 1 0; have a₁₁ := e₃ 1 1; have a₁₂ := e₃ 1 2
  have a₂₀ := e₃ 2 0; have a₂₁ := e₃ 2 1; have a₂₂ := e₃ 2 2
  simp at r₀₀ r₀₁ r₀₂ r₁₁ r₁₂ r₂₂ c₀₀ c₀₁ c₀₂ c₁₁ c₁₂ c₂₂ a₀₀ a₀₁ a₀₂ a₁₀ a₁₁ a₁₂ a₂₀ a₂₁ a₂₂
  clear e₁ e₂ e₃ h₁ h₂ h₃ hR
  refine ⟨?_, Matrix.ext fun i j ↦ ?_⟩
  · fin_cases k <;> simp [rotQuat, dotProduct, Fin.sum_univ_four] <;> linarith
  · fin_cases k <;> fin_cases i <;> fin_cases j <;> simp [rotQuat, quatMatrix] <;> linarith

/-- **Quaternions onto `SO(3)`.** Every rotation is the rotation of a nonzero quaternion. -/
theorem exists_quat_of_mem_SO3 {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO(3)) :
    ∃ q : Fin 4 → ℝ, q ≠ 0 ∧ quatRotation q = R := by
  -- The diagonal of `rotQuat R` sums to `4`, so one of its entries is at least `1`.
  obtain ⟨k, hk⟩ : ∃ k, 1 ≤ rotQuat R k k := by
    by_contra! h
    have h₀ := h 0; have h₁ := h 1; have h₂ := h 2; have h₃ := h 3
    simp [rotQuat] at h₀ h₁ h₂ h₃
    linarith
  obtain ⟨hn, hm⟩ := rotQuat_spec hR k
  refine ⟨rotQuat R k, fun h ↦ ?_, quatRotation_eq_of (by linarith) hn hm⟩
  have := congrFun h k
  rw [Pi.zero_apply] at this
  linarith

theorem chartQuat_succAbove {k : Fin 4} {q : Fin 4 → ℝ} (hk : q k ≠ 0) :
    chartQuat k (fun i ↦ q (k.succAbove i) / q k) = (q k)⁻¹ • q := by
  funext j
  fin_cases k <;> fin_cases j <;> simp at hk <;> simp [chartQuat, Fin.succAbove, hk] <;> field_simp

/-- **Rotation charts cover `SO(3)`.** Every rotation is the rotation of a chart at coordinates
in `[-1, 1]`. -/
theorem exists_chartRotation_eq {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO(3)) :
    ∃ k x, (∀ i, |x i| ≤ 1) ∧ chartRotation k x = R := by
  obtain ⟨q, hq, rfl⟩ := exists_quat_of_mem_SO3 hR
  obtain ⟨k, hk, hmax⟩ := exists_abs_le_abs hq
  refine ⟨k, fun i ↦ q (k.succAbove i) / q k, fun i ↦ ?_, ?_⟩
  · rw [abs_div, div_le_one (abs_pos.mpr hk)]
    exact hmax _
  · rw [chartRotation, chartQuat_succAbove hk, quatRotation_smul (inv_ne_zero hk)]

/-! ### Views -/

theorem viewDir_div {a : Fin 3} {u : Fin 3 → ℝ} (ha : u a ≠ 0) :
    viewDir a (u (a + 1) / u a) (u (a + 2) / u a) = (u a)⁻¹ • u := by
  funext i
  fin_cases a <;> fin_cases i <;> simp at ha <;> simp [viewDir, ha] <;> field_simp

/-- The kernel of the screen map is the line through the view direction. -/
theorem eq_smul_viewDir_of_screen_eq_zero {a : Fin 3} {s t : ℝ} {x : Fin 3 → ℝ}
    (h : screen a s t x = 0) : x = x a • viewDir a s t := by
  have h₀ := congrFun h 0
  have h₁ := congrFun h 1
  simp [screen] at h₀ h₁
  funext i
  fin_cases a <;> fin_cases i <;> simp [viewDir] at h₀ h₁ ⊢ <;> linarith

/-- **View charts cover the screen maps.** Every linear surjection `L : ℝ³ → ℝ²` is the screen
map of a view chart at coordinates in `[-1, 1]`, followed by an invertible linear map of the
plane. -/
theorem exists_screen_eq (L : (Fin 3 → ℝ) →ₗ[ℝ] Fin 2 → ℝ) (hL : Function.Surjective L) :
    ∃ a s t, |s| ≤ 1 ∧ |t| ≤ 1 ∧
      ∃ A : (Fin 2 → ℝ) ≃ₗ[ℝ] Fin 2 → ℝ, ∀ x, L x = A (screen a s t x) := by
  obtain ⟨u, hu, hu₀⟩ : ∃ u ∈ LinearMap.ker L, u ≠ 0 :=
    Submodule.exists_mem_ne_zero_of_ne_bot
      (LinearMap.ker_ne_bot_of_finrank_lt (by simp only [Module.finrank_fin_fun]; norm_num))
  obtain ⟨a, ha, hmax⟩ := exists_abs_le_abs hu₀
  have hle (i : Fin 3) : |u i / u a| ≤ 1 := by
    rw [abs_div, div_le_one (abs_pos.mpr ha)]
    exact hmax i
  refine ⟨a, _, _, hle (a + 1), hle (a + 2), exists_linearEquiv_eq_of_ker_le
    (g := screenₗ a _ _) hL (screen_surjective a _ _) fun x hx ↦ ?_⟩
  rw [LinearMap.mem_ker, screenₗ_apply] at hx
  rw [eq_smul_viewDir_of_screen_eq_zero hx, viewDir_div ha, smul_smul]
  exact (LinearMap.ker L).smul_mem _ hu

/-! ### The unit chart boxes -/

/-- The poses of the twelve unit chart boxes: view and rotation coordinates in `[-1, 1]`. -/
def unitPoses : Set ChartPose :=
  {p | |p.s| ≤ 1 ∧ |p.t| ≤ 1 ∧ ∀ i, |p.x i| ≤ 1}

namespace Polyhedron

/-- **Chart cover.** A Rupert polyhedron fits at a pose of a unit chart box. -/
theorem IsRupert.exists_fitsAt {P : Polyhedron} (h : P.IsRupert) :
    ∃ p ∈ unitPoses, ∃ τ, P.FitsAt p τ := by
  obtain ⟨L, hL, R, hR, τ, hfit⟩ := P.isRupert_iff_exists_surjective.mp h
  obtain ⟨a, s, t, hs, ht, A, hA⟩ := exists_screen_eq L hL
  obtain ⟨k, x, hx, rfl⟩ := exists_chartRotation_eq hR
  refine ⟨⟨a, s, t, k, x⟩, ⟨hs, ht, hx⟩, A.symm τ, ?_⟩
  simp only [hA] at hfit
  exact (linearEquiv_image_add_subset_interior_iff A _ _ _ _ τ).mp hfit

/-- `NoFit` on the twelve unit chart boxes proves that a polyhedron is not Rupert. -/
theorem not_isRupert_of_noFit {P : Polyhedron} (h : P.NoFit unitPoses) : ¬ P.IsRupert :=
  fun hP ↦ by
    obtain ⟨p, hp, τ, hfit⟩ := hP.exists_fitsAt
    exact h p hp τ hfit

end Polyhedron

end Nieuwland
