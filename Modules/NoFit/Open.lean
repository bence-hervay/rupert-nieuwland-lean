import Mathlib.Topology.Instances.Matrix
import Modules.NoFit.Along
import Modules.Rupert.Interior

/-!
# Fits form an open set

`Polyhedron.FitsAlong.eventually`: near a fit along `υ t₀ ≠ 0` with rotation `ρ t₀`, for any
`υ`, `ρ` continuous at `t₀`, the polyhedron fits along `υ t` with `ρ t`. So the pairs `(u, q)` of
a nonzero view direction and a nonzero quaternion along which a polyhedron fits
(`FitsAlong u (quatRotation q)`) form an open set (`Polyhedron.isOpen_fitsAlong`). The density
arguments for exceptional sets rest on it (`lean/DESIGN.md` §8, G3).

At a fit, every moved vertex shadow lies strictly inside a small triangle whose corners are shadows
of points of the polyhedron (`mem_interior_convexHull_of_orient_pos`). Near the fit, the screen
map along `u` is the screen map `L` along `u₀` after the projection along `u` onto the plane
`u₀ ⬝ᵥ x = 0` (`projAlong`). The corners and the moved shadows depend continuously on `(u, q)`, so
the same triangles keep the moved shadows inside the hole.

`Polyhedron.isOpen_chartFits`: in the coordinates of one chart, the fitting poses form an open
set; so do those that fit with a fixed rotation applied first (`Polyhedron.isOpen_chartFitsRot`,
for pre-rotated charts).
-/

open Matrix Filter Topology

namespace Nieuwland

/-- The projection along `u` onto the plane `u₀ ⬝ᵥ x = 0`, for `u₀ ⬝ᵥ u ≠ 0`. -/
noncomputable def projAlong (u₀ u : Fin 3 → ℝ) : (Fin 3 → ℝ) →ₗ[ℝ] Fin 3 → ℝ where
  toFun x := x - ((u₀ ⬝ᵥ x) / (u₀ ⬝ᵥ u)) • u
  map_add' x y := by
    simp only [dotProduct_add, add_div, add_smul]
    abel
  map_smul' c x := by
    simp only [dotProduct_smul, smul_eq_mul, mul_div_assoc, mul_smul, smul_sub, RingHom.id_apply]

theorem projAlong_apply (u₀ u x : Fin 3 → ℝ) :
    projAlong u₀ u x = x - ((u₀ ⬝ᵥ x) / (u₀ ⬝ᵥ u)) • u :=
  rfl

theorem dot_projAlong {u₀ u : Fin 3 → ℝ} (h : u₀ ⬝ᵥ u ≠ 0) (x : Fin 3 → ℝ) :
    u₀ ⬝ᵥ projAlong u₀ u x = 0 := by
  rw [projAlong_apply, dotProduct_sub, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ h,
    sub_self]

theorem projAlong_dir {u₀ u : Fin 3 → ℝ} (h : u₀ ⬝ᵥ u ≠ 0) : projAlong u₀ u u = 0 := by
  rw [projAlong_apply, div_self h, one_smul, sub_self]

theorem projAlong_of_dot_eq_zero (u₀ u : Fin 3 → ℝ) {x : Fin 3 → ℝ} (hx : u₀ ⬝ᵥ x = 0) :
    projAlong u₀ u x = x := by
  rw [projAlong_apply, hx, zero_div, zero_smul, sub_zero]

section Screen

variable {L : (Fin 3 → ℝ) →ₗ[ℝ] Fin 2 → ℝ} {u₀ u : Fin 3 → ℝ}

theorem apply_projAlong_of_apply_eq_zero (hL : L u₀ = 0) (x : Fin 3 → ℝ) :
    L (projAlong u₀ u₀ x) = L x := by
  rw [projAlong_apply, map_sub, map_smul, hL, smul_zero, sub_zero]

/-- The screen map along `u`: its kernel is the line of `u`. -/
theorem ker_comp_projAlong (hker : LinearMap.ker L = ℝ ∙ u₀) (hu₀ : u₀ ≠ 0)
    (h : u₀ ⬝ᵥ u ≠ 0) : LinearMap.ker (L ∘ₗ projAlong u₀ u) = ℝ ∙ u := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mem_span_singleton]
  constructor
  · intro hx
    have hmem : projAlong u₀ u x ∈ ℝ ∙ u₀ := by
      rw [← hker]
      exact hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hc0 : c = 0 := by
      have h1 := dot_projAlong h x
      rw [← hc, dotProduct_smul, smul_eq_mul] at h1
      exact (mul_eq_zero.mp h1).resolve_right (dotProduct_self_eq_zero.not.mpr hu₀)
    have h0 : projAlong u₀ u x = 0 := by rw [← hc, hc0, zero_smul]
    rw [projAlong_apply, sub_eq_zero] at h0
    exact ⟨_, h0.symm⟩
  · rintro ⟨c, rfl⟩
    rw [map_smul, projAlong_dir h, smul_zero, map_zero]

/-- The screen map along `u` is onto. -/
theorem surjective_comp_projAlong (hL : Function.Surjective L) (hLu₀ : L u₀ = 0)
    (hu₀ : u₀ ⬝ᵥ u₀ ≠ 0) : Function.Surjective (L ∘ₗ projAlong u₀ u) := by
  intro y
  obtain ⟨x, rfl⟩ := hL y
  refine ⟨projAlong u₀ u₀ x, ?_⟩
  rw [LinearMap.comp_apply, projAlong_of_dot_eq_zero _ _ (dot_projAlong hu₀ x),
    apply_projAlong_of_apply_eq_zero hLu₀]

end Screen

/-- The corner directions of the triangles around moved shadows. -/
def triDir : Fin 3 → Fin 2 → ℝ :=
  ![![1, 0], ![-1, 1], ![-1, -1]]

theorem abs_triDir_le (k : Fin 3) (i : Fin 2) : |triDir k i| ≤ 1 := by
  fin_cases k <;> fin_cases i <;> simp [triDir]

/-- The point `a` lies strictly inside the triangle `a + e • triDir k`. -/
theorem orient_triDir (a : Fin 2 → ℝ) {e : ℝ} (he : 0 < e) (k : Fin 3) :
    0 < orient (a + e • triDir k) (a + e • triDir (k + 1)) a := by
  have he2 : 0 < e * e := mul_pos he he
  fin_cases k <;> simp [orient, triDir] <;> nlinarith

theorem continuous_orient₃ :
    Continuous fun p : ((Fin 2 → ℝ) × (Fin 2 → ℝ)) × (Fin 2 → ℝ) ↦ orient p.1.1 p.1.2 p.2 := by
  unfold orient
  fun_prop

theorem continuous_quatRotation_at {q₀ : Fin 4 → ℝ} (hq₀ : q₀ ≠ 0) :
    ContinuousAt quatRotation q₀ := by
  have hd : q₀ ⬝ᵥ q₀ ≠ 0 := dotProduct_self_eq_zero.not.mpr hq₀
  have hM : Continuous (quatMatrix : (Fin 4 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) := by
    refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    fin_cases i <;> fin_cases j <;>
      simp only [quatMatrix, of_apply, cons_val', cons_val, cons_val_zero, cons_val_one,
        cons_val_fin_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.zero_eta] <;>
      fun_prop
  have hdot : Continuous fun q : Fin 4 → ℝ ↦ q ⬝ᵥ q := by
    simp only [dotProduct]
    fun_prop
  exact ((hdot.continuousAt.inv₀ hd).smul hM.continuousAt)

namespace Polyhedron

/-- **Fits persist.** Let `υ` and `ρ` be continuous at `t₀`, with `υ t₀ ≠ 0`. If the polyhedron
fits along `υ t₀` with the rotation `ρ t₀`, it fits along `υ t` with `ρ t` for every `t` near `t₀`
(with the same translation in suitable screen coordinates). -/
theorem FitsAlong.eventually {P : Polyhedron} {T : Type*} [TopologicalSpace T] {υ : T → Fin 3 → ℝ}
    {ρ : T → Matrix (Fin 3) (Fin 3) ℝ} {t₀ : T} (hυ : ContinuousAt υ t₀) (hρ : ContinuousAt ρ t₀)
    (hu₀ : υ t₀ ≠ 0) (h : P.FitsAlong (υ t₀) (ρ t₀)) : ∀ᶠ t in 𝓝 t₀, P.FitsAlong (υ t) (ρ t) := by
  obtain ⟨L, hL, hker, τ, hfit⟩ := h
  set u₀ := υ t₀
  have hLu₀ : L u₀ = 0 := by
    have : u₀ ∈ LinearMap.ker L := by
      rw [hker]
      exact Submodule.mem_span_singleton_self u₀
    exact this
  have hu₀u₀ : u₀ ⬝ᵥ u₀ ≠ 0 := dotProduct_self_eq_zero.not.mpr hu₀
  have hv := (P.image_add_subset_interior_iff (L ∘ₗ (ρ t₀).mulVecLin) L τ).mp hfit
  -- Triangles of shadows of points of the polyhedron around the moved vertex shadows.
  have htri : ∀ v ∈ P.vertices, ∃ e : ℝ, 0 < e ∧ ∀ k : Fin 3, ∃ y ∈ P.hull,
      L y = L (ρ t₀ *ᵥ v) + τ + e • triDir k := by
    intro v hv'
    have hmem := hv v hv'
    simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply] at hmem
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hmem
    obtain ⟨ε, hε, hball⟩ := hmem
    refine ⟨ε / 2, half_pos hε, fun k ↦ ?_⟩
    have hin : L (ρ t₀ *ᵥ v) + τ + (ε / 2) • triDir k ∈
        convexHull ℝ {L w | w ∈ P.vertices} := by
      apply hball
      rw [Metric.mem_ball, dist_pi_lt_iff hε]
      intro i
      rw [Real.dist_eq, Pi.add_apply, add_sub_cancel_left, Pi.smul_apply, smul_eq_mul, abs_mul,
        abs_of_pos (half_pos hε)]
      have := abs_triDir_le k i
      nlinarith
    rw [← P.image_hull L] at hin
    obtain ⟨y, hy, hyL⟩ := hin
    exact ⟨y, hy, hyL⟩
  choose! e he y hy hyL using htri
  -- The orientations of the triangles near the fit.
  let F (t : T) (v : Fin 3 → ℝ) (k : Fin 3) : ℝ :=
    orient (L (projAlong u₀ (υ t) (y v k))) (L (projAlong u₀ (υ t) (y v (k + 1))))
      (L (projAlong u₀ (υ t) (ρ t *ᵥ v)) + τ)
  have hF₀ : ∀ v ∈ P.vertices, ∀ k, 0 < F t₀ v k := by
    intro v hv' k
    simp only [F]
    rw [show υ t₀ = u₀ from rfl]
    simp only [apply_projAlong_of_apply_eq_zero hLu₀, hyL v hv']
    exact orient_triDir _ (he v hv') k
  have hLc : Continuous L := L.continuous_of_finiteDimensional
  have hden : ContinuousAt (fun t ↦ u₀ ⬝ᵥ υ t) t₀ :=
    (continuous_const.dotProduct continuous_id).continuousAt.comp hυ
  have hproj : ∀ w : T → Fin 3 → ℝ, ContinuousAt w t₀ →
      ContinuousAt (fun t ↦ projAlong u₀ (υ t) (w t)) t₀ := by
    intro w hw
    simp only [projAlong_apply]
    have hnum : ContinuousAt (fun t ↦ u₀ ⬝ᵥ w t) t₀ :=
      (continuous_const.dotProduct continuous_id).continuousAt.comp hw
    exact hw.sub ((hnum.div hden hu₀u₀).smul hυ)
  have hcont : ∀ v k, ContinuousAt (fun t ↦ F t v k) t₀ := by
    intro v k
    have hR : ContinuousAt (fun t ↦ ρ t *ᵥ v) t₀ :=
      (continuous_id.matrix_mulVec continuous_const).continuousAt.comp hρ
    have ha := hLc.continuousAt.comp (hproj (fun _ ↦ y v k) continuousAt_const)
    have hb := hLc.continuousAt.comp (hproj (fun _ ↦ y v (k + 1)) continuousAt_const)
    have hc := (hLc.continuousAt.comp (hproj _ hR)).add (continuousAt_const (y := τ))
    exact continuous_orient₃.continuousAt.comp ((ha.prodMk hb).prodMk hc)
  have hev : ∀ᶠ t in 𝓝 t₀, u₀ ⬝ᵥ υ t ≠ 0 ∧ ∀ v ∈ P.vertices, ∀ k, 0 < F t v k := by
    refine (hden.eventually_ne hu₀u₀).and ?_
    rw [Filter.eventually_all_finset]
    intro v hv'
    rw [Filter.eventually_all]
    intro k
    exact continuousAt_const.eventually_lt (hcont v k) (hF₀ v hv' k)
  filter_upwards [hev] with t ⟨hdot, hpos⟩
  refine ⟨L ∘ₗ projAlong u₀ (υ t), surjective_comp_projAlong hL hLu₀ hu₀u₀,
    ker_comp_projAlong hker hu₀ hdot, τ, ?_⟩
  refine (P.image_add_subset_interior_iff ((L ∘ₗ projAlong u₀ (υ t)) ∘ₗ
    (ρ t).mulVecLin) (L ∘ₗ projAlong u₀ (υ t)) τ).mpr fun v hv' ↦ ?_
  have h0 := hpos v hv' 0
  have h1 := hpos v hv' 1
  have h2 := hpos v hv' 2
  simp only [F] at h0 h1 h2
  have hin := mem_interior_convexHull_of_orient_pos h0 h1 h2
  refine interior_mono (convexHull_min ?_ (convex_convexHull ℝ _)) hin
  have hsub : ∀ k : Fin 3, L (projAlong u₀ (υ t) (y v k)) ∈
      convexHull ℝ {(L ∘ₗ projAlong u₀ (υ t)) w | w ∈ P.vertices} := by
    intro k
    rw [← P.image_hull]
    exact ⟨y v k, hy v hv' k, rfl⟩
  rintro _ (rfl | rfl | rfl)
  · exact hsub 0
  · exact hsub 1
  · exact hsub 2

/-- **Fits form an open set**: along nonzero view directions and quaternions near a fit, the
polyhedron fits too (`FitsAlong.eventually`). -/
theorem isOpen_fitsAlong (P : Polyhedron) :
    IsOpen {x : (Fin 3 → ℝ) × (Fin 4 → ℝ) |
      x.1 ≠ 0 ∧ x.2 ≠ 0 ∧ P.FitsAlong x.1 (quatRotation x.2)} := by
  rw [isOpen_iff_mem_nhds]
  rintro ⟨u₀, q₀⟩ ⟨hu₀, hq₀, hfit⟩
  have h := FitsAlong.eventually (υ := Prod.fst) (ρ := fun x : (Fin 3 → ℝ) × (Fin 4 → ℝ) ↦
    quatRotation x.2) continuousAt_fst ((continuous_quatRotation_at hq₀).comp continuousAt_snd)
    hu₀ hfit
  filter_upwards [h, continuousAt_fst.eventually_ne hu₀, continuousAt_snd.eventually_ne hq₀]
    with x hx h1 h2 using ⟨h1, h2, hx⟩

theorem continuous_viewDir_coords (a : Fin 3) :
    Continuous fun y : Fin 5 → ℝ ↦ viewDir a (y 0) (y 1) := by
  refine continuous_pi fun i ↦ ?_
  simp only [viewDir]
  fin_cases a <;> fin_cases i <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.mk_one, Fin.reduceFinMk,
      Fin.reduceSub, Fin.zero_eta, sub_zero, sub_self, zero_sub, cons_val, cons_val_one,
      cons_val_zero] <;>
    fun_prop

theorem continuous_chartQuat_coords (k : Fin 4) :
    Continuous fun y : Fin 5 → ℝ ↦ chartQuat k ![y 2, y 3, y 4] := by
  refine continuous_pi fun i ↦ ?_
  simp only [chartQuat]
  fin_cases k <;> fin_cases i <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, cons_val_zero, cons_val_one,
      cons_val, Fin.reduceFinMk, Fin.mk_one, Fin.zero_eta, cons_val', cons_val_fin_one] <;>
    fun_prop

/-- **Fits form an open set in chart coordinates**: for view chart `a` and rotation chart `k`, the
coordinates of the fitting poses. -/
theorem isOpen_chartFits (P : Polyhedron) (a : Fin 3) (k : Fin 4) :
    IsOpen {y : Fin 5 → ℝ | ∃ τ, P.FitsAt ⟨a, y 0, y 1, k, ![y 2, y 3, y 4]⟩ τ} := by
  have hv := continuous_viewDir_coords a
  have hq := continuous_chartQuat_coords k
  have hset : {y : Fin 5 → ℝ | ∃ τ, P.FitsAt ⟨a, y 0, y 1, k, ![y 2, y 3, y 4]⟩ τ} =
      (fun y : Fin 5 → ℝ ↦ (viewDir a (y 0) (y 1), chartQuat k ![y 2, y 3, y 4])) ⁻¹'
        {x | x.1 ≠ 0 ∧ x.2 ≠ 0 ∧ P.FitsAlong x.1 (quatRotation x.2)} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · rintro ⟨τ, h⟩
      have h' := fitsAlong_of_fitsAt h
      refine ⟨fun h0 ↦ ?_, fun h0 ↦ ?_, h'⟩
      · have := congrFun h0 a
        simp [viewDir] at this
      · have := congrFun h0 k
        rw [chartQuat_self] at this
        exact one_ne_zero this
    · rintro ⟨-, -, h⟩
      exact h.exists_fitsAt one_ne_zero (one_smul _ _).symm rfl
  rw [hset]
  exact P.isOpen_fitsAlong.preimage (hv.prodMk hq)

/-- **Fits with a rotation applied first form an open set in chart coordinates**: for view chart
`a`, rotation chart `k` and the rotation `Rc`, the coordinates of the poses that fit with their
rotation followed by `Rc`. -/
theorem isOpen_chartFitsRot (P : Polyhedron) (a : Fin 3) (k : Fin 4)
    (Rc : Matrix (Fin 3) (Fin 3) ℝ) :
    IsOpen {y : Fin 5 → ℝ | P.FitsAlong (viewDir a (y 0) (y 1))
      (chartRotation k ![y 2, y 3, y 4] * Rc)} := by
  rw [isOpen_iff_mem_nhds]
  intro y₀ hy₀
  have hq : ContinuousAt (fun y : Fin 5 → ℝ ↦ quatRotation (chartQuat k ![y 2, y 3, y 4])) y₀ :=
    ContinuousAt.comp (g := quatRotation)
      (continuous_quatRotation_at (chartQuat_ne_zero k ![y₀ 2, y₀ 3, y₀ 4]))
      (continuous_chartQuat_coords k).continuousAt
  have hrot : ContinuousAt (fun y : Fin 5 → ℝ ↦ chartRotation k ![y 2, y 3, y 4] * Rc) y₀ :=
    hq.mul continuousAt_const
  exact FitsAlong.eventually (continuous_viewDir_coords a).continuousAt hrot
    (viewDir_ne_zero _ _ _) hy₀

end Polyhedron

end Nieuwland
