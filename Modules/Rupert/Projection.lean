import Modules.Rupert.Screen

/-!
# Statement (1) of `RESEARCH.md`

`RESEARCH.md` (§1.1, statement (1)) asks, for the convex hull `K` of finitely many points, whether

  `∃ u ≠ 0, ∃ R ∈ SO(3), ∃ τ ∈ u^⊥, π_u (R K) + τ ⊆ int π_u K`,

where `π_u` is the orthogonal projection onto the plane `u^⊥` and the interior is taken in that
plane. This file states it literally and proves it equivalent to `Polyhedron.IsRupert`
(`Polyhedron.isRupert_iff_orthProj`).

* `perp u` is the plane `u^⊥ = {x | u ⬝ᵥ x = 0}`, a subspace of `ℝ³`. As a type it carries the
  subspace topology, so `interior` below is the interior in the plane.
* `orthProj u x = x - ((u ⬝ᵥ x) / (u ⬝ᵥ u)) • u` is the orthogonal projection onto `u^⊥`: it
  fixes `u^⊥` and moves each point along `u`.

The proof identifies the plane `u^⊥` with `ℝ²` through the shadow map of a rotation turning `u` to
the `z`-axis (`exists_linearEquiv_orthProj`), and transports the containment along that linear
isomorphism (`linearEquiv_image_add_subset_interior_iff`).
-/

open Matrix

namespace Nieuwland

/-- The plane `u^⊥` of the vectors orthogonal to `u`. -/
def perp (u : Fin 3 → ℝ) : Submodule ℝ (Fin 3 → ℝ) where
  carrier := {x | u ⬝ᵥ x = 0}
  add_mem' {x y} (hx : u ⬝ᵥ x = 0) (hy : u ⬝ᵥ y = 0) :=
    show u ⬝ᵥ (x + y) = 0 by rw [dotProduct_add, hx, hy, add_zero]
  zero_mem' := dotProduct_zero u
  smul_mem' c x (hx : u ⬝ᵥ x = 0) :=
    show u ⬝ᵥ (c • x) = 0 by rw [dotProduct_smul, hx, smul_zero]

theorem mem_perp {u x : Fin 3 → ℝ} : x ∈ perp u ↔ u ⬝ᵥ x = 0 :=
  Iff.rfl

/-- The orthogonal projection `π_u` of `ℝ³` onto the plane `u^⊥`:
`x ↦ x - ((u ⬝ᵥ x) / (u ⬝ᵥ u)) • u`. -/
noncomputable def orthProj (u : Fin 3 → ℝ) : (Fin 3 → ℝ) →ₗ[ℝ] perp u where
  toFun x := ⟨x - ((u ⬝ᵥ x) / (u ⬝ᵥ u)) • u, by
    rw [mem_perp, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    by_cases hu : u ⬝ᵥ u = 0
    · simp [dotProduct_self_eq_zero.mp hu]
    · field_simp
      ring⟩
  map_add' x y := by
    ext1
    simp only [Submodule.coe_add, dotProduct_add, add_div, add_smul]
    abel
  map_smul' c x := by
    ext1
    simp only [Submodule.coe_smul, dotProduct_smul, smul_eq_mul, mul_div_assoc, RingHom.id_apply,
      smul_sub, smul_smul]

theorem orthProj_apply (u x : Fin 3 → ℝ) :
    (orthProj u x : Fin 3 → ℝ) = x - ((u ⬝ᵥ x) / (u ⬝ᵥ u)) • u :=
  rfl

/-- `π_u` fixes the plane `u^⊥`. -/
theorem orthProj_of_mem {u x : Fin 3 → ℝ} (hx : x ∈ perp u) : (orthProj u x : Fin 3 → ℝ) = x := by
  rw [orthProj_apply, mem_perp.mp hx, zero_div, zero_smul, sub_zero]

/-- The shadow map of an orthogonal matrix `Q` vanishes exactly on the line through `Qᵀ e_z`. -/
theorem ker_projXY_mulVec {Q : Matrix (Fin 3) (Fin 3) ℝ} (hQ : Q ∈ O(3)) :
    LinearMap.ker (projXYₗ ∘ₗ Q.mulVecLin) = ℝ ∙ (Qᵀ *ᵥ Pi.single 2 1) := by
  ext x
  simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, mulVecLin_apply,
    projXYₗ_apply, Submodule.mem_span_singleton]
  constructor
  · intro hx
    refine ⟨(Q *ᵥ x) 2, ?_⟩
    have hQx : Q *ᵥ x = (Q *ᵥ x) 2 • Pi.single 2 1 := by
      have h0 : (Q *ᵥ x) 0 = 0 := congrFun hx 0
      have h1 : (Q *ᵥ x) 1 = 0 := congrFun hx 1
      ext i
      fin_cases i <;> simp [h0, h1]
    rw [← mulVec_smul, ← hQx, mulVec_mulVec, transpose_mul_of_mem_orthogonalGroup hQ, one_mulVec]
  · rintro ⟨a, rfl⟩
    rw [mulVec_smul, mulVec_mulVec, mul_transpose_of_mem_orthogonalGroup hQ, one_mulVec]
    ext i
    fin_cases i <;> simp [projXY]

/-- If the shadow map of a rotation `Q` vanishes exactly on the line through `u ≠ 0`, then it
factors through `π_u` and a linear isomorphism `A : u^⊥ ≃ ℝ²`. -/
theorem exists_linearEquiv_orthProj {u : Fin 3 → ℝ} (hu : u ≠ 0) {Q : Matrix (Fin 3) (Fin 3) ℝ}
    (hQ : Q ∈ O(3)) (hker : LinearMap.ker (projXYₗ ∘ₗ Q.mulVecLin) = ℝ ∙ u) :
    ∃ A : perp u ≃ₗ[ℝ] Fin 2 → ℝ, ∀ x, A (orthProj u x) = projXY (Q *ᵥ x) := by
  set g := projXYₗ ∘ₗ Q.mulVecLin
  have hgu : g u = 0 := by
    rw [← LinearMap.mem_ker, hker]
    exact Submodule.mem_span_singleton_self u
  set A₀ : perp u →ₗ[ℝ] Fin 2 → ℝ := g ∘ₗ (perp u).subtype
  have hA₀ (x : Fin 3 → ℝ) : A₀ (orthProj u x) = projXY (Q *ᵥ x) := by
    change g (x - ((u ⬝ᵥ x) / (u ⬝ᵥ u)) • u) = g x
    rw [map_sub, map_smul, hgu, smul_zero, sub_zero]
  have hinj : Function.Injective A₀ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hker ▸ LinearMap.mem_ker.mpr hw :
      (w : Fin 3 → ℝ) ∈ ℝ ∙ u)
    have hw' := mem_perp.mp w.2
    rw [← ha, dotProduct_smul, smul_eq_mul, mul_eq_zero] at hw'
    rcases hw' with h | h
    · ext1
      simp [← ha, h]
    · exact absurd (dotProduct_self_eq_zero.mp h) hu
  have hsurj : Function.Surjective A₀ := fun y ↦ by
    obtain ⟨x, rfl⟩ := projXY_mulVec_surjective hQ y
    exact ⟨orthProj u x, hA₀ x⟩
  exact ⟨LinearEquiv.ofBijective A₀ ⟨hinj, hsurj⟩, hA₀⟩

/-- **Statement (1) of `RESEARCH.md`.** `P` is Rupert iff for some direction `u ≠ 0`, rotation
`R` and translation `τ` in the plane `u^⊥`, the orthogonal projection of `R P` onto `u^⊥`, moved
by `τ`, lies in the interior (within `u^⊥`) of the orthogonal projection of `P`. -/
theorem Polyhedron.isRupert_iff_orthProj (P : Polyhedron) :
    P.IsRupert ↔ ∃ u : Fin 3 → ℝ, u ≠ 0 ∧ ∃ R ∈ SO(3), ∃ τ : perp u,
      {orthProj u (R *ᵥ x) + τ | x ∈ P.hull} ⊆ interior {orthProj u x | x ∈ P.hull} := by
  constructor
  · rintro ⟨R₁, hR₁, R₂, hR₂, t, h⟩
    -- View along the third row `u = R₂ᵀ e_z` of `R₂`.
    set u := R₂ᵀ *ᵥ Pi.single 2 1
    have hu : u ≠ 0 := fun h0 ↦ by
      have := congrArg (R₂ *ᵥ ·) h0
      simp only [u, mulVec_mulVec, mul_transpose_of_mem_orthogonalGroup hR₂.1, one_mulVec,
        mulVec_zero] at this
      simpa using congrFun this 2
    obtain ⟨A, hA⟩ := exists_linearEquiv_orthProj hu hR₂.1 (ker_projXY_mulVec hR₂.1)
    refine ⟨u, hu, R₂ᵀ * R₁, Submonoid.mul_mem _ (transpose_mem_SO3 hR₂) hR₁, A.symm t, ?_⟩
    rw [← linearEquiv_image_add_subset_interior_iff A]
    simpa only [hA, mulVec_mulVec, ← Matrix.mul_assoc, mul_transpose_of_mem_orthogonalGroup hR₂.1,
      Matrix.one_mul] using h
  · rintro ⟨u, hu, R, hR, τ, h⟩
    obtain ⟨Q, hQ, hker⟩ := exists_mem_SO3_ker_eq_span hu
    obtain ⟨A, hA⟩ := exists_linearEquiv_orthProj hu hQ.1 hker
    refine ⟨Q * R, Submonoid.mul_mem _ hQ hR, Q, hQ, A τ, ?_⟩
    rw [← A.symm_apply_apply τ, ← linearEquiv_image_add_subset_interior_iff A] at h
    simpa only [hA, LinearEquiv.apply_symm_apply, mulVec_mulVec] using h

end Nieuwland
