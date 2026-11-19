import Modules.Rupert.Hull
import Modules.Rupert.Householder
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Screen coordinates

`Polyhedron.IsRupert` looks along the `z`-axis after rotating both copies. Statement (1) of
`RESEARCH.md` looks along an arbitrary direction `u ≠ 0` instead and projects onto the plane
`u^⊥`. Writing either down needs the rotation turning `u` to the `z`-axis, or an orthonormal basis
of `u^⊥`, whose entries are generally irrational. This file removes that need.

* Strict containment of shadows does not depend on the coordinates used in the plane: an
  invertible linear map of the plane is a homeomorphism, so it preserves interiors and inclusions
  (`linearEquiv_image_add_subset_interior_iff`).
* Any linear surjection `L : ℝ³ → ℝ²` describes the shadow seen along its kernel, which is a line
  `ℝ ∙ u`: `L` is `projXY ∘ Q` for a rotation `Q` turning `u` to the `z`-axis, followed by an
  invertible linear map of the plane (`exists_mem_SO3_linearEquiv_eq`).

Hence `P` is Rupert iff for some linear surjection `L`, rotation `R` and translation `t`, the
image of `R P` under `L`, moved by `t`, lies in the interior of the image of `P`
(`Polyhedron.isRupert_iff_exists_surjective`). The *screen map* `L` may have rational entries
even when `u^⊥` has no rational orthonormal basis: `RESEARCH.md` §2.2 views along `u = (s, t, 1)`
through `L (x, y, z) = (x - s z, y - t z)` (see `Modules/Rupert/Charts.lean`). The translation `t`
is in the coordinates of `L`.

For concrete proofs, `Polyhedron.isRupert_of_surjective` combines this with the vertex criterion
of `Modules/Rupert/Hull.lean`: finitely many points must lie in the interior of a polygon.
-/

open Matrix

namespace Nieuwland

/-- **Change of screen coordinates.** An invertible linear map `A` between finite-dimensional
real normed spaces (for example, of the plane) preserves strict containment: the images under
`A ∘ f`, moved by `t`, lie in the interior of the image under `A ∘ g` iff the images under `f`,
moved by `A⁻¹ t`, lie in the interior of the image under `g`. -/
theorem linearEquiv_image_add_subset_interior_iff {X Y V W : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (A : V ≃ₗ[ℝ] W) (f : X → V) (g : Y → V) (s : Set X) (s' : Set Y) (t : W) :
    {A (f x) + t | x ∈ s} ⊆ interior {A (g y) | y ∈ s'} ↔
      {f x + A.symm t | x ∈ s} ⊆ interior {g y | y ∈ s'} := by
  let e := A.toContinuousLinearEquiv.toHomeomorph
  have he (z : V) : e z = A z := rfl
  have h₁ : {A (f x) + t | x ∈ s} = e '' {f x + A.symm t | x ∈ s} := by
    ext z
    simp [he, map_add]
  have h₂ : {A (g y) | y ∈ s'} = e '' {g y | y ∈ s'} := by
    ext z
    simp [he]
  rw [h₁, h₂, ← e.image_interior, Set.image_subset_image_iff e.injective]

/-- **Factoring through a smaller kernel.** A linear surjection `L` onto a finite-dimensional
space `W` whose kernel contains the kernel of a linear surjection `g` onto `W` is `g` followed by
an invertible linear map `A` of `W`. -/
theorem exists_linearEquiv_eq_of_ker_le {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W] {L g : V →ₗ[ℝ] W}
    (hL : Function.Surjective L) (hg : Function.Surjective g)
    (hle : LinearMap.ker g ≤ LinearMap.ker L) : ∃ A : W ≃ₗ[ℝ] W, ∀ x, L x = A (g x) := by
  obtain ⟨σ, hσ⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hg)
  -- `A₀ = L ∘ σ` satisfies `L = A₀ ∘ g`, and is bijective.
  set A₀ := L ∘ₗ σ
  have hA₀ (x : V) : L x = A₀ (g x) := by
    have hker : x - σ (g x) ∈ LinearMap.ker g := by
      rw [LinearMap.mem_ker, map_sub, ← LinearMap.comp_apply g σ, hσ, LinearMap.id_apply,
        sub_self]
    have := LinearMap.mem_ker.mp (hle hker)
    rwa [map_sub, sub_eq_zero] at this
  have hsurj : Function.Surjective A₀ := fun y ↦ by
    obtain ⟨x, rfl⟩ := hL y
    exact ⟨g x, (hA₀ x).symm⟩
  have hinj : Function.Injective A₀ := LinearMap.injective_iff_surjective.mpr hsurj
  exact ⟨LinearEquiv.ofBijective A₀ ⟨hinj, hsurj⟩, hA₀⟩

/-- **Normal form of a screen map.** Every linear surjection `L : ℝ³ → ℝ²` is the shadow map
`x ↦ projXY (Q *ᵥ x)` of a rotation `Q`, followed by an invertible linear map `A` of the
plane. -/
theorem exists_mem_SO3_linearEquiv_eq (L : (Fin 3 → ℝ) →ₗ[ℝ] Fin 2 → ℝ)
    (hL : Function.Surjective L) :
    ∃ Q ∈ SO(3), ∃ A : (Fin 2 → ℝ) ≃ₗ[ℝ] Fin 2 → ℝ, ∀ x, L x = A (projXY (Q *ᵥ x)) := by
  -- The kernel of `L` contains a nonzero `u`, the viewing direction.
  obtain ⟨u, hu, hu0⟩ : ∃ u ∈ LinearMap.ker L, u ≠ 0 :=
    Submodule.exists_mem_ne_zero_of_ne_bot
      (LinearMap.ker_ne_bot_of_finrank_lt (by simp only [Module.finrank_fin_fun]; norm_num))
  obtain ⟨Q, hQ, hQu⟩ := exists_mem_SO3_ker_eq_span hu0
  -- The shadow map of `Q` is onto, with kernel `ℝ ∙ u`.
  obtain ⟨A, hA⟩ := exists_linearEquiv_eq_of_ker_le (g := projXYₗ ∘ₗ Q.mulVecLin) hL
    (projXY_mulVec_surjective hQ.1) (by rw [hQu, Submodule.span_singleton_le_iff_mem]; exact hu)
  exact ⟨Q, hQ, A, hA⟩

/-- **Screen coordinates.** `P` is Rupert iff for some linear surjection `L : ℝ³ → ℝ²` (a screen
map viewing along its kernel), rotation `R` and translation `t` of the screen, the image of `R P`
under `L`, moved by `t`, lies in the interior of the image of `P`. -/
theorem Polyhedron.isRupert_iff_exists_surjective (P : Polyhedron) :
    P.IsRupert ↔ ∃ L : (Fin 3 → ℝ) →ₗ[ℝ] Fin 2 → ℝ, Function.Surjective L ∧
      ∃ R ∈ SO(3), ∃ t : Fin 2 → ℝ,
        {L (R *ᵥ x) + t | x ∈ P.hull} ⊆ interior {L x | x ∈ P.hull} := by
  constructor
  · rintro ⟨R₁, hR₁, R₂, hR₂, t, h⟩
    refine ⟨projXYₗ ∘ₗ R₂.mulVecLin, projXY_mulVec_surjective hR₂.1, R₂ᵀ * R₁,
      Submonoid.mul_mem _ (transpose_mem_SO3 hR₂) hR₁, t, ?_⟩
    have hR (x : Fin 3 → ℝ) : R₂ *ᵥ ((R₂ᵀ * R₁) *ᵥ x) = R₁ *ᵥ x := by
      rw [mulVec_mulVec, ← Matrix.mul_assoc, mul_transpose_of_mem_orthogonalGroup hR₂.1,
        Matrix.one_mul]
    simpa only [LinearMap.coe_comp, Function.comp_apply, mulVecLin_apply, projXYₗ_apply, hR]
      using h
  · rintro ⟨L, hL, R, hR, t, h⟩
    obtain ⟨Q, hQ, A, hA⟩ := exists_mem_SO3_linearEquiv_eq L hL
    simp only [hA] at h
    rw [linearEquiv_image_add_subset_interior_iff] at h
    refine ⟨Q * R, Submonoid.mul_mem _ hQ hR, Q, hQ, A.symm t, ?_⟩
    simpa only [mulVec_mulVec] using h

/-- **Vertex criterion in screen coordinates.** `P` is Rupert if, for a linear surjection
`L : ℝ³ → ℝ²`, a rotation `R` and a translation `t`, every vertex `v` of `P` has its moved image
`L (R *ᵥ v) + t` in the interior of the polygon spanned by the images `L w` of the vertices. -/
theorem Polyhedron.isRupert_of_surjective (P : Polyhedron) (L : (Fin 3 → ℝ) →ₗ[ℝ] Fin 2 → ℝ)
    (hL : Function.Surjective L) {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO(3))
    (t : Fin 2 → ℝ)
    (h : ∀ v ∈ P.vertices, L (R *ᵥ v) + t ∈ interior (convexHull ℝ {L w | w ∈ P.vertices})) :
    P.IsRupert :=
  P.isRupert_iff_exists_surjective.mpr
    ⟨L, hL, R, hR, t, (P.image_add_subset_interior_iff (L ∘ₗ R.mulVecLin) L t).mpr h⟩

end Nieuwland
