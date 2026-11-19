import Modules.NoFit.Chart

/-!
# Fits along a direction

`P.FitsAlong u R`: viewed along `u`, a moved shadow of `R P` lies in the interior of the shadow of
`P`, in the screen coordinates of some linear surjection `L : ℝ³ → ℝ²` with kernel `ℝ ∙ u`. The
choice of `L` does not matter (`FitsAlong.exists_add_subset`): two such maps differ by an
invertible linear map of the plane. Pose maps act on fits in this form
(`Modules/NoFit/Symmetry.lean`). Fits at chart poses are fits along their view directions
(`fitsAlong_of_fitsAt`), and conversely every fit along a direction is a fit at a pose of the unit
chart boxes (`FitsAlong.exists_unitPoses`).
-/

open Matrix

namespace Nieuwland

/-- The kernel of the screen map is the line through the view direction. -/
theorem ker_screenₗ (a : Fin 3) (s t : ℝ) : LinearMap.ker (screenₗ a s t) = ℝ ∙ viewDir a s t := by
  ext x
  rw [LinearMap.mem_ker, screenₗ_apply, Submodule.mem_span_singleton]
  constructor
  · intro h
    exact ⟨x a, (eq_smul_viewDir_of_screen_eq_zero h).symm⟩
  · rintro ⟨c, rfl⟩
    rw [← screenₗ_apply, map_smul, screenₗ_apply, screen_viewDir, smul_zero]

theorem viewDir_ne_zero (a : Fin 3) (s t : ℝ) : viewDir a s t ≠ 0 := fun h ↦ by
  have := congrFun h a
  simp [viewDir] at this

namespace Polyhedron

/-- Viewed along `u`, a moved shadow of `R P` lies in the interior of the shadow of `P`, in the
screen coordinates of a linear surjection `L` with kernel `ℝ ∙ u`. -/
def FitsAlong (P : Polyhedron) (u : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∃ L : (Fin 3 → ℝ) →ₗ[ℝ] Fin 2 → ℝ, Function.Surjective L ∧ LinearMap.ker L = ℝ ∙ u ∧
    ∃ τ, {L (R *ᵥ x) + τ | x ∈ P.hull} ⊆ interior {L x | x ∈ P.hull}

variable {P : Polyhedron}

/-- **Any screen map.** A fit along `u` is a fit in the screen coordinates of every linear
surjection with kernel `ℝ ∙ u`. -/
theorem FitsAlong.exists_add_subset {u : Fin 3 → ℝ} {R : Matrix (Fin 3) (Fin 3) ℝ}
    (h : P.FitsAlong u R) {L : (Fin 3 → ℝ) →ₗ[ℝ] Fin 2 → ℝ} (hL : Function.Surjective L)
    (hker : LinearMap.ker L = ℝ ∙ u) :
    ∃ τ, {L (R *ᵥ x) + τ | x ∈ P.hull} ⊆ interior {L x | x ∈ P.hull} := by
  obtain ⟨L₀, hL₀, hker₀, τ, hτ⟩ := h
  obtain ⟨A, hA⟩ := exists_linearEquiv_eq_of_ker_le hL hL₀ (by rw [hker₀, hker])
  refine ⟨A τ, ?_⟩
  simp only [hA]
  rw [linearEquiv_image_add_subset_interior_iff, LinearEquiv.symm_apply_apply]
  exact hτ

theorem fitsAlong_of_fitsAt {p : ChartPose} {τ : Fin 2 → ℝ} (h : P.FitsAt p τ) :
    P.FitsAlong (viewDir p.view p.s p.t) p.rotation :=
  ⟨screenₗ p.view p.s p.t, screen_surjective _ _ _, ker_screenₗ _ _ _, τ, h⟩

/-- A fit along a direction `u` and rotation `R` is a fit at a chart pose with view direction a
multiple of `u` and rotation `R`. -/
theorem FitsAlong.exists_fitsAt {u : Fin 3 → ℝ} {R : Matrix (Fin 3) (Fin 3) ℝ}
    (h : P.FitsAlong u R) {p : ChartPose} {c : ℝ} (hc : c ≠ 0)
    (hu : viewDir p.view p.s p.t = c • u) (hR : p.rotation = R) : ∃ τ, P.FitsAt p τ := by
  have hker : LinearMap.ker (screenₗ p.view p.s p.t) = ℝ ∙ u := by
    rw [ker_screenₗ, hu, Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc)]
  obtain ⟨τ, hτ⟩ := h.exists_add_subset (screen_surjective _ _ _) hker
  exact ⟨τ, by rw [FitsAt, hR]; exact hτ⟩

/-- **Chart cover of fits.** A fit along `u ≠ 0` with a rotation `R` is a fit at a pose of the
unit chart boxes, with rotation `R` and view direction a nonzero multiple of `u`. -/
theorem FitsAlong.exists_unitPoses {u : Fin 3 → ℝ} {R : Matrix (Fin 3) (Fin 3) ℝ}
    (h : P.FitsAlong u R) (hu : u ≠ 0) (hR : R ∈ SO(3)) :
    ∃ p ∈ unitPoses, (∃ τ, P.FitsAt p τ) ∧ (∃ c : ℝ, c ≠ 0 ∧ viewDir p.view p.s p.t = c • u) ∧
      p.rotation = R := by
  obtain ⟨k, x, hx, hkx⟩ := exists_chartRotation_eq hR
  obtain ⟨a, ha, hmax⟩ := exists_abs_le_abs hu
  have hle (i : Fin 3) : |u i / u a| ≤ 1 := by
    rw [abs_div, div_le_one (abs_pos.mpr ha)]
    exact hmax i
  let p : ChartPose := ⟨a, u (a + 1) / u a, u (a + 2) / u a, k, x⟩
  have hp : viewDir p.view p.s p.t = (u a)⁻¹ • u := viewDir_div ha
  refine ⟨p, ⟨hle _, hle _, hx⟩, h.exists_fitsAt (inv_ne_zero ha) hp hkx,
    ⟨_, inv_ne_zero ha, hp⟩, hkx⟩

end Polyhedron

end Nieuwland
