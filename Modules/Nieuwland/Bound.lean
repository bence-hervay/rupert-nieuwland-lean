import Modules.Nieuwland.Basic
import Modules.NoFit.Generic
import Modules.Rupert.Projection
import Modules.NoFit.Pre

/-!
# Nieuwland numbers: upper bounds and exact values

The statement layer of scaled certificates (`notes/nieuwland-lean.md`). A NoFit certificate at a
plug scale `θ` proves that `P` scaled by `θ` does not fit through `P`, so `nieuwland P ≤ θ`
(`Polyhedron.nieuwland_le_of_not_fitsThrough`); with a weak fit at `θ` this is `nieuwland P = θ`
(`Polyhedron.nieuwland_eq_of_not_fitsThrough`).

Certificates conclude pose by pose, along a view direction `u` with the matrix `θ • R` for a chart
rotation `R` (`Polyhedron.FitsAlong`, which takes any matrix: `P.FitsAlong u (θ • R)` is the fit of
`θ R P` through `P` along `u`). This file proves the two facts that connect them:

* **Chart cover at a scale** (`FitsThrough.exists_fitsAlong_smul`,
  `FitsAlong.exists_unitPoses_smul`): a fit of `P.smul θ` through `P` is a fit along a nonzero
  direction with `θ` times a rotation, and then at a pose of the twelve unit chart boxes.
* **Weak symmetry exclusion at a scale** (`not_fitsThrough_smul_of_excluded_off`): the density
  argument of `Polyhedron.not_isRupert_of_excluded_off` with "fit" read as "fit of `θ R P`". Fits at
  `θ` form an open set of poses, and pose maps of signed symmetries are linear in the matrix, so
  they commute with `θ` (`FitsAlong.symm`).
-/

open Matrix Topology

namespace Nieuwland

namespace Polyhedron

variable {P : Polyhedron}

/-! ### Fits at a scale along a direction -/

/-- **A fit at a scale is a fit along a direction.** If `P` scaled by `θ` fits through `P`, then
`P` fits along a nonzero `u` with the matrix `θ • R` for a rotation `R`. -/
theorem FitsThrough.exists_fitsAlong_smul {θ : ℝ} (h : (P.smul θ).FitsThrough P) :
    ∃ u : Fin 3 → ℝ, u ≠ 0 ∧ ∃ R ∈ SO(3), P.FitsAlong u (θ • R) := by
  obtain ⟨R₁, hR₁, R₂, hR₂, t, h⟩ := h
  rw [shadow_smul] at h
  have he : (Pi.single 2 1 : Fin 3 → ℝ) ≠ 0 := fun h0 ↦ by
    simpa using congrFun h0 2
  refine ⟨R₂ᵀ *ᵥ Pi.single 2 1, mulVec_ne_zero_of_mem_SO3 (transpose_mem_SO3 hR₂) he,
    R₂ᵀ * R₁, Submonoid.mul_mem _ (transpose_mem_SO3 hR₂) hR₁, projXYₗ ∘ₗ R₂.mulVecLin,
    projXY_mulVec_surjective hR₂.1, ker_projXY_mulVec hR₂.1, t, ?_⟩
  have hR (x : Fin 3 → ℝ) : (projXYₗ ∘ₗ R₂.mulVecLin) ((θ • (R₂ᵀ * R₁)) *ᵥ x) =
      θ • projXY (R₁ *ᵥ x) := by
    simp only [LinearMap.coe_comp, Function.comp_apply, mulVecLin_apply, projXYₗ_apply]
    rw [mulVec_mulVec, Matrix.mul_smul, ← Matrix.mul_assoc,
      mul_transpose_of_mem_orthogonalGroup hR₂.1, Matrix.one_mul, smul_mulVec, ← mulVec_smul,
      projXY_mulVec_smul]
  simpa only [hR, LinearMap.coe_comp, Function.comp_apply, mulVecLin_apply, projXYₗ_apply]
    using h

/-- **Chart cover at a scale.** A fit along `u ≠ 0` with the matrix `θ • R`, `R` a rotation, is a
fit along the view direction of a pose of the unit chart boxes, a nonzero multiple of `u`, with
the matrix `θ` times its rotation `R`. -/
theorem FitsAlong.exists_unitPoses_smul {u : Fin 3 → ℝ} {R : Matrix (Fin 3) (Fin 3) ℝ} {θ : ℝ}
    (h : P.FitsAlong u (θ • R)) (hu : u ≠ 0) (hR : R ∈ SO(3)) :
    ∃ p ∈ unitPoses, P.FitsAlong (viewDir p.view p.s p.t) (θ • p.rotation) ∧
      (∃ c : ℝ, c ≠ 0 ∧ viewDir p.view p.s p.t = c • u) ∧ p.rotation = R := by
  obtain ⟨k, x, hx, hkx⟩ := exists_chartRotation_eq hR
  obtain ⟨a, ha, hmax⟩ := exists_abs_le_abs hu
  have hle (i : Fin 3) : |u i / u a| ≤ 1 := by
    rw [abs_div, div_le_one (abs_pos.mpr ha)]
    exact hmax i
  let p : ChartPose := ⟨a, u (a + 1) / u a, u (a + 2) / u a, k, x⟩
  have hp : viewDir p.view p.s p.t = (u a)⁻¹ • u := viewDir_div ha
  have hpR : p.rotation = R := hkx
  refine ⟨p, ⟨hle _, hle _, hx⟩, ?_, ⟨_, inv_ne_zero ha, hp⟩, hpR⟩
  rw [hp, hpR]
  exact h.smul (inv_ne_zero ha)

/-- **Fits at a scale form an open set of poses.** -/
theorem isOpen_fitsPose_smul (P : Polyhedron) (θ : ℝ) :
    IsOpen {x : poseSpace | P.FitsAlong x.1.1 (θ • x.1.2)} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  exact FitsAlong.eventually (υ := fun x : poseSpace ↦ x.1.1) (ρ := fun x : poseSpace ↦ θ • x.1.2)
    (continuous_fst.comp continuous_subtype_val).continuousAt
    ((continuous_snd.comp continuous_subtype_val).const_smul θ).continuousAt x.2.1 hx

/-- Pose maps commute with the scale: `turn σ (A u) * A * (θ • R) * B = θ • (…)`. -/
theorem turn_mul_smul_mul (σ : ℝ) (A B R : Matrix (Fin 3) (Fin 3) ℝ) (u : Fin 3 → ℝ) (θ : ℝ) :
    turn σ (A *ᵥ u) * A * (θ • R) * B = θ • (turn σ (A *ᵥ u) * A * R * B) := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- **Weak symmetry exclusion at a scale.** Let the vertices of `P` span space about `c`, let `f`
be a real function of poses and `N` a meagre set of poses, neither depending on the length of the
view direction. If at every pose `p` of the unit chart boxes, `P` has no fit along the view of `p`
with the matrix `θ` times the rotation of `p`, or some pose map of signed symmetries increases
`f`, or `p` lies in `N`, then `P` scaled by `θ` does not fit through `P`. -/
theorem not_fitsThrough_smul_of_excluded_off {c : Fin 3 → ℝ}
    (hspan : Submodule.span ℝ ((· - c) '' (P.vertices : Set (Fin 3 → ℝ))) = ⊤)
    (f : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ → ℝ)
    (hf : ∀ (a : ℝ) u R, a ≠ 0 → f (a • u) R = f u R)
    {N : Set ((Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ)}
    (hN : IsMeagre ((↑) ⁻¹' N : Set poseSpace))
    (hNs : ∀ (a : ℝ) u R, a ≠ 0 → (a • u, R) ∈ N → (u, R) ∈ N) {θ : ℝ}
    (h : ∀ p ∈ unitPoses, ¬ P.FitsAlong (viewDir p.view p.s p.t) (θ • p.rotation) ∨
      P.Excluded c f p ∨ p.pose ∈ N) :
    ¬ (P.smul θ).FitsThrough P := by
  intro hP
  obtain ⟨u₀, hu₀, R₀, hR₀, hfit₀⟩ := hP.exists_fitsAlong_smul
  -- The pose maps of signed symmetries, finitely many.
  have hS : ({x : Matrix (Fin 3) (Fin 3) ℝ × ℝ | P.IsSignedSymm c x.1 x.2} ×ˢ
      {x : Matrix (Fin 3) (Fin 3) ℝ × ℝ | P.IsSignedSymm c x.1 x.2}).Countable :=
    ((finite_signedSymm hspan).prod (finite_signedSymm hspan)).countable
  have hbad : IsMeagre (⋃ y ∈ {x : Matrix (Fin 3) (Fin 3) ℝ × ℝ | P.IsSignedSymm c x.1 x.2} ×ˢ
      {x : Matrix (Fin 3) (Fin 3) ℝ × ℝ | P.IsSignedSymm c x.1 x.2},
      {x : poseSpace | poseMap y.1.1 y.2.1 (y.1.2 * y.2.2) x ∈ N}) :=
    isMeagre_biUnion hS fun y hy ↦
      isMeagre_poseMap_preimage hy.1.1 hy.2.1 (hy.1.sign_mul hy.2) hN
  -- A fit at `θ` whose orbit avoids `N` (the fits at `θ` are a nonempty open set of poses).
  obtain ⟨x₀, hx₀, hx₀N⟩ : ∃ x : poseSpace, P.FitsAlong x.1.1 (θ • x.1.2) ∧ ∀ A σ B τ,
      P.IsSignedSymm c A σ → P.IsSignedSymm c B τ → poseMap A B (σ * τ) x ∉ N := by
    by_contra! H
    refine not_isMeagre_of_isOpen (P.isOpen_fitsPose_smul θ)
      ⟨⟨(u₀, R₀), hu₀, hR₀⟩, hfit₀⟩ (hbad.mono fun x hx ↦ ?_)
    obtain ⟨A, σ, B, τ, hA, hB, hN'⟩ := H x hx
    exact Set.mem_biUnion (x := ((A, σ), (B, τ))) ⟨hA, hB⟩ hN'
  -- The pose of its orbit that maximises `f`.
  obtain ⟨A₀, σ₀, B₀, τ₀, hA₀, hB₀, hmax, -⟩ := exists_orbit_max hspan f x₀.1.1 x₀.1.2
  have hu : A₀ *ᵥ x₀.1.1 ≠ 0 := mulVec_ne_zero_of_mem_SO3 hA₀.1 x₀.2.1
  have hR : turn (σ₀ * τ₀) (A₀ *ᵥ x₀.1.1) * A₀ * x₀.1.2 * B₀ ∈ SO(3) :=
    mul_mem (mul_mem (mul_mem (turn_mem _ hu) hA₀.1) x₀.2.2) hB₀.1
  have hsym := hx₀.symm hA₀ hB₀
  rw [turn_mul_smul_mul] at hsym
  obtain ⟨p, hp, hfit, ⟨a, ha, hpu⟩, hpR⟩ := hsym.exists_unitPoses_smul hu hR
  rcases h p hp with hno | ⟨A, σ, B, τ', hA, hB, hlt⟩ | hnull
  · exact hno hfit
  · rw [hpu, hpR, mulVec_smul, turn_smul ha, hf _ _ _ ha, hf _ _ _ ha] at hlt
    exact (hmax A σ B τ' hA hB).not_gt hlt
  · refine hx₀N A₀ σ₀ B₀ τ₀ hA₀ hB₀ (hNs a _ _ ha ?_)
    have hpose : p.pose = (a • (A₀ *ᵥ x₀.1.1),
        turn (σ₀ * τ₀) (A₀ *ᵥ x₀.1.1) * A₀ * x₀.1.2 * B₀) := by
      rw [ChartPose.pose, hpu, hpR]
    rw [hpose] at hnull
    exact hnull

/-! ### Exact values -/

/-- **The Nieuwland number from both bounds.** If `P` is full-dimensional, `P` scaled by `L ≥ 0`
does not fit through `P`, and `L ≤ nieuwland P` (from a weak fit at `L`,
`le_nieuwland_of_weakFitsThrough`), then `nieuwland P = L`. -/
theorem nieuwland_eq_of_not_fitsThrough {L : ℝ} (hL : 0 ≤ L) (h : ¬ (P.smul L).FitsThrough P)
    (hle : L ≤ P.nieuwland) : P.nieuwland = L :=
  le_antisymm (nieuwland_le_of_not_fitsThrough hL h) hle

/-- **Upper bounds through a scaling.** If `P = Q.smul a` with `a ≠ 0`, and `Q` scaled by
`θ ≥ 0` does not fit through `Q`, then `nieuwland P ≤ θ`: certificates work with the points
times a common denominator. -/
theorem nieuwland_le_of_eq_smul {Q : Polyhedron} {a θ : ℝ} (hP : P = Q.smul a) (ha : a ≠ 0)
    (hθ : 0 ≤ θ) (h : ¬ (Q.smul θ).FitsThrough Q) : P.nieuwland ≤ θ := by
  rw [hP, nieuwland_smul ha]
  exact nieuwland_le_of_not_fitsThrough hθ h

end Polyhedron

end Nieuwland
