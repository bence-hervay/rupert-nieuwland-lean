import Modules.NoFit.Along
import Mathlib.Algebra.Module.LinearMap.DivisionRing
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Support obstructions

A fit puts every moved point of the inner shadow strictly inside the outer shadow, so every
nonzero linear functional of the screen is smaller there than its maximum over the outer shadow
(`lt_of_mem_interior_convexHull`). The obstructions of `RESEARCH.md` §3 combine such strict
inequalities so that the unknown translation drops out.

* **Balanced supports** (`RESEARCH.md` §3.3): nonnegative weights `λᵢ`, not all zero, with
  `∑ λᵢ φᵢ = 0` cancel the translation from the weighted sum of the inequalities
  (`exists_add_notMem_interior_of_balanced`).
* **Centred mode** (`RESEARCH.md` §3.5): if the outer polygon and the inner point set are
  centrally symmetric, a translated fit gives an untranslated one, by averaging it with its
  reflection (`forall_mem_interior_of_add_mem_interior`).

At a chart pose, a functional of the screen is a vector `n` of space orthogonal to the viewing
direction: `n ⬝ᵥ x = screenFunctional a n (screen a s t x)` (`screenFunctional_screen`); in any
screen coordinates with kernel `ℝ ∙ u`, it is a functional of the screen when `n ⊥ u`
(`exists_functional_comp`). The obstructions hold along any view direction
(`Polyhedron.not_fitsAlong_of_balanced`, for poses given by any representative), and at chart
poses (`Polyhedron.not_fitsAt_of_balanced`, `Polyhedron.not_fitsAt_of_centred`).
-/

open Matrix Set

namespace Nieuwland

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Strict support bound.** A nonzero linear functional is smaller at an interior point of the
convex hull of `S` than any bound for it on `S`. -/
theorem lt_of_mem_interior_convexHull [FiniteDimensional ℝ E] {φ : E →ₗ[ℝ] ℝ} (hφ : φ ≠ 0)
    {S : Set E} {h : ℝ} (hS : ∀ s ∈ S, φ s ≤ h) {y : E} (hy : y ∈ interior (convexHull ℝ S)) :
    φ y < h := by
  have hsub : convexHull ℝ S ⊆ φ ⁻¹' Iic h := convexHull_min hS ((convex_Iic h).linear_preimage φ)
  have hopen : IsOpenMap φ :=
    φ.isOpenMap_of_finiteDimensional (LinearMap.surjective_iff_ne_zero.mpr hφ)
  have := interior_mono hsub hy
  rwa [← hopen.preimage_interior_eq_interior_preimage φ.continuous_of_finiteDimensional,
    interior_Iic] at this

/-- **Translation elimination by balanced weights.** Let `φ i` be nonzero functionals with bounds
`h i` on `S`, and `w i` nonnegative weights, not all zero, with `∑ w i • φ i = 0`. If the points
`y i` satisfy `∑ w i * (φ i (y i) - h i) ≥ 0`, then no translation `t` moves all of them into the
interior of the convex hull of `S`. -/
theorem exists_add_notMem_interior_of_balanced [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    {S : Set E} {φ : ι → E →ₗ[ℝ] ℝ} (hφ : ∀ i, φ i ≠ 0) {h : ι → ℝ}
    (hS : ∀ i, ∀ s ∈ S, φ i s ≤ h i) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw₀ : 0 < ∑ i, w i)
    (hbal : ∑ i, w i • φ i = 0) {y : ι → E} (hy : 0 ≤ ∑ i, w i * (φ i (y i) - h i)) (t : E) :
    ∃ i, y i + t ∉ interior (convexHull ℝ S) := by
  by_contra! hfit
  obtain ⟨j, -, hj⟩ := Finset.exists_lt_of_sum_lt (by simpa using hw₀ :
    ∑ i, (0 : ℝ) < ∑ i, w i)
  have hneg : ∑ i, w i * (φ i (y i + t) - h i) < ∑ _i : ι, (0 : ℝ) := by
    refine Finset.sum_lt_sum (fun i _ ↦ ?_) ⟨j, Finset.mem_univ j, ?_⟩
    · exact mul_nonpos_of_nonneg_of_nonpos (hw i)
        (sub_nonpos.mpr (lt_of_mem_interior_convexHull (hφ i) (hS i) (hfit i)).le)
    · exact mul_neg_of_pos_of_neg hj
        (sub_neg.mpr (lt_of_mem_interior_convexHull (hφ j) (hS j) (hfit j)))
  have ht : ∑ i, w i * φ i t = 0 := by
    simpa [LinearMap.sum_apply] using congrArg (fun f : E →ₗ[ℝ] ℝ ↦ f t) hbal
  have hsplit : ∑ i, w i * (φ i (y i + t) - h i) =
      ∑ i, w i * (φ i (y i) - h i) + ∑ i, w i * φ i t := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_add]
    ring
  simp only [Finset.sum_const_zero] at hneg
  linarith

/-- The interior of the convex hull of a centrally symmetric set is centrally symmetric. -/
theorem neg_mem_interior_convexHull {S : Set E} (hS : ∀ s ∈ S, -s ∈ S) {y : E}
    (hy : y ∈ interior (convexHull ℝ S)) : -y ∈ interior (convexHull ℝ S) := by
  have hS' : -S = S :=
    Set.ext fun s ↦ ⟨fun h ↦ by simpa using hS _ h, fun h ↦ by simpa using hS s h⟩
  have key : (Homeomorph.neg E) '' interior (convexHull ℝ S) = interior (convexHull ℝ S) := by
    rw [Homeomorph.image_interior]
    congr 1
    rw [show ⇑(Homeomorph.neg E) = Neg.neg from rfl, Set.image_neg_eq_neg, ← convexHull_neg, hS']
  rw [← key]
  exact ⟨y, hy, rfl⟩

/-- **Centring.** If the sets `S` and `T` are centrally symmetric and a translation moves `T` into
the interior of the convex hull of `S`, then `T` itself lies there: average `T + t` with its
reflection `T - t`. -/
theorem forall_mem_interior_of_add_mem_interior {S T : Set E} (hS : ∀ s ∈ S, -s ∈ S)
    (hT : ∀ y ∈ T, -y ∈ T) {t : E} (h : ∀ y ∈ T, y + t ∈ interior (convexHull ℝ S)) :
    ∀ y ∈ T, y ∈ interior (convexHull ℝ S) := by
  intro y hy
  have h₂ : y - t ∈ interior (convexHull ℝ S) := by
    simpa [neg_add_eq_sub] using neg_mem_interior_convexHull hS (h (-y) (hT y hy))
  have := (convex_convexHull ℝ S).interior (h y hy) h₂ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  convert this using 1
  module

end Normed

/-! ### Functionals of the screen -/

/-- The functional `y ↦ n (a + 1) * y 0 + n (a + 2) * y 1` of the screen of view chart `a`.
For `n` orthogonal to the viewing direction it pulls back to `x ↦ n ⬝ᵥ x`
(`screenFunctional_screen`). -/
def screenFunctional (a : Fin 3) (n : Fin 3 → ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ where
  toFun y := n (a + 1) * y 0 + n (a + 2) * y 1
  map_add' y z := by simp only [Pi.add_apply]; ring
  map_smul' c y := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem screenFunctional_screen {a : Fin 3} {s t : ℝ} {n : Fin 3 → ℝ}
    (hn : n ⬝ᵥ viewDir a s t = 0) (x : Fin 3 → ℝ) :
    screenFunctional a n (screen a s t x) = n ⬝ᵥ x := by
  simp only [screenFunctional, LinearMap.coe_mk, AddHom.coe_mk, screen]
  fin_cases a
  · simp [viewDir, dotProduct, Fin.sum_univ_three] at hn ⊢
    linear_combination (-x 0) * hn
  · simp [viewDir, dotProduct, Fin.sum_univ_three] at hn ⊢
    linear_combination (-x 1) * hn
  · simp [viewDir, dotProduct, Fin.sum_univ_three] at hn ⊢
    linear_combination (-x 2) * hn

theorem ChartPose.screenFunctional_screen {p : ChartPose} {n : Fin 3 → ℝ}
    (hn : n ⬝ᵥ viewDir p.view p.s p.t = 0) (x : Fin 3 → ℝ) :
    screenFunctional p.view n (p.screen x) = n ⬝ᵥ x :=
  Nieuwland.screenFunctional_screen hn x

theorem ChartPose.screen_neg (p : ChartPose) (x : Fin 3 → ℝ) : p.screen (-x) = -p.screen x :=
  (screenₗ p.view p.s p.t).map_neg x

theorem screenFunctional_ne_zero {a : Fin 3} {s t : ℝ} {n : Fin 3 → ℝ}
    (hn : n ⬝ᵥ viewDir a s t = 0) (hn₀ : n ≠ 0) : screenFunctional a n ≠ 0 := by
  intro h
  have := screenFunctional_screen hn n
  rw [h, LinearMap.zero_apply, eq_comm, dotProduct_self_eq_zero] at this
  exact hn₀ this

namespace Polyhedron

variable {P : Polyhedron} {p : ChartPose}

/-- A functional `x ↦ n ⬝ᵥ x` with `n ⊥ u` factors through every linear surjection `L` with
kernel `ℝ ∙ u`. -/
theorem _root_.Nieuwland.exists_functional_comp {L : (Fin 3 → ℝ) →ₗ[ℝ] Fin 2 → ℝ}
    (hL : Function.Surjective L) {u : Fin 3 → ℝ} (hker : LinearMap.ker L = ℝ ∙ u)
    {n : Fin 3 → ℝ} (hn : n ⬝ᵥ u = 0) : ∃ φ : (Fin 2 → ℝ) →ₗ[ℝ] ℝ, ∀ x, φ (L x) = n ⬝ᵥ x := by
  obtain ⟨S, hS⟩ := L.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hL)
  let ψ : (Fin 3 → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x ↦ n ⬝ᵥ x
      map_add' := fun x y ↦ dotProduct_add n x y
      map_smul' := fun c x ↦ by simp [dotProduct_smul] }
  refine ⟨ψ.comp S, fun x ↦ ?_⟩
  have hx : x - S (L x) ∈ LinearMap.ker L := by
    rw [LinearMap.mem_ker, map_sub, ← LinearMap.comp_apply L S, hS, LinearMap.id_apply, sub_self]
  rw [hker, Submodule.mem_span_singleton] at hx
  obtain ⟨c, hc⟩ := hx
  have h0 : n ⬝ᵥ (x - S (L x)) = 0 := by rw [← hc, dotProduct_smul, hn, smul_zero]
  rw [dotProduct_sub] at h0
  change n ⬝ᵥ S (L x) = n ⬝ᵥ x
  linarith

/-- **Balanced supports along a view direction.** Let `n i` be nonzero vectors orthogonal to
`u`, bounded by `h i` on the vertices of `P`, with nonnegative weights `w i`, not all zero, such
that `∑ w i • n i = 0`. If points `v i` of `P` satisfy `∑ w i * (n i ⬝ᵥ (R *ᵥ v i) - h i) ≥ 0`,
then `R P` does not fit along `u`, with any translation. -/
theorem not_fitsAlong_of_balanced {u : Fin 3 → ℝ} {R : Matrix (Fin 3) (Fin 3) ℝ} {ι : Type*}
    [Fintype ι] {n : ι → Fin 3 → ℝ} (hn : ∀ i, n i ≠ 0) (hnu : ∀ i, n i ⬝ᵥ u = 0) {h : ι → ℝ}
    (hh : ∀ i, ∀ x ∈ P.vertices, n i ⬝ᵥ x ≤ h i) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hw₀ : 0 < ∑ i, w i) (hbal : ∑ i, w i • n i = 0) {v : ι → Fin 3 → ℝ}
    (hv : ∀ i, v i ∈ P.hull) (hp : 0 ≤ ∑ i, w i * (n i ⬝ᵥ (R *ᵥ v i) - h i)) :
    ¬ P.FitsAlong u R := by
  rintro ⟨L, hL, hker, τ, hfit⟩
  choose φ hφ using fun i ↦ exists_functional_comp hL hker (hnu i)
  have hφ₀ (i : ι) : φ i ≠ 0 := fun h0 ↦ hn i (by
    have := hφ i (n i)
    rwa [h0, LinearMap.zero_apply, eq_comm, dotProduct_self_eq_zero] at this)
  have hbal' : ∑ i, w i • φ i = 0 := by
    refine LinearMap.ext fun y ↦ ?_
    obtain ⟨x, rfl⟩ := hL y
    have := congrArg (· ⬝ᵥ x) hbal
    simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul, zero_dotProduct] at this
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hφ,
      LinearMap.zero_apply] using this
  obtain ⟨i, hi⟩ := exists_add_notMem_interior_of_balanced (S := {L x | x ∈ P.vertices}) hφ₀
    (fun i ↦ by rintro _ ⟨x, hx, rfl⟩; rw [hφ]; exact hh i x hx) hw hw₀ hbal'
    (y := fun i ↦ L (R *ᵥ v i)) (by simpa only [hφ] using hp) τ
  rw [← P.image_hull L] at hi
  exact hi (hfit ⟨v i, hv i, rfl⟩)

/-- **Balanced supports at a chart pose.** Let `n i` be nonzero vectors orthogonal to the viewing
direction of `p`, bounded by `h i` on the vertices of `P`, with nonnegative weights `w i`, not all
zero, such that `∑ w i • n i = 0`. If points `v i` of `P` satisfy
`∑ w i * (n i ⬝ᵥ (R *ᵥ v i) - h i) ≥ 0` for the rotation `R` of `p`, no translation makes `p` a
fit. -/
theorem not_fitsAt_of_balanced {ι : Type*} [Fintype ι] {n : ι → Fin 3 → ℝ} (hn : ∀ i, n i ≠ 0)
    (hnu : ∀ i, n i ⬝ᵥ viewDir p.view p.s p.t = 0) {h : ι → ℝ}
    (hh : ∀ i, ∀ x ∈ P.vertices, n i ⬝ᵥ x ≤ h i) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hw₀ : 0 < ∑ i, w i) (hbal : ∑ i, w i • n i = 0) {v : ι → Fin 3 → ℝ}
    (hv : ∀ i, v i ∈ P.hull) (hp : 0 ≤ ∑ i, w i * (n i ⬝ᵥ (p.rotation *ᵥ v i) - h i))
    (τ : Fin 2 → ℝ) : ¬ P.FitsAt p τ := fun hfit ↦
  not_fitsAlong_of_balanced hn hnu hh hw hw₀ hbal hv hp (fitsAlong_of_fitsAt hfit)

/-- **Centring at a chart pose.** If the vertices of `P` are centrally symmetric, a fit with any
translation gives a fit without translation. -/
theorem fitsAt_zero_of_fitsAt (hP : ∀ x ∈ P.vertices, -x ∈ P.vertices) {τ : Fin 2 → ℝ}
    (h : P.FitsAt p τ) : P.FitsAt p 0 := by
  rw [fitsAt_iff_vertices] at h ⊢
  have hS : ∀ y ∈ {p.screen w | w ∈ P.vertices}, -y ∈ {p.screen w | w ∈ P.vertices} := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨-w, hP w hw, p.screen_neg w⟩
  have hT : ∀ y ∈ {p.screen (p.rotation *ᵥ w) | w ∈ P.vertices},
      -y ∈ {p.screen (p.rotation *ᵥ w) | w ∈ P.vertices} := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨-w, hP w hw, by rw [mulVec_neg, p.screen_neg]⟩
  have := forall_mem_interior_of_add_mem_interior hS hT (t := τ) (by
    rintro _ ⟨w, hw, rfl⟩
    exact h w hw)
  intro v hv
  simpa using this _ ⟨v, hv, rfl⟩

/-- **Centred supports at a chart pose.** If the vertices of `P` are centrally symmetric, a
nonzero vector `n` orthogonal to the viewing direction of `p` is bounded by `h` on the vertices,
and `n ⬝ᵥ (R *ᵥ v) ≥ h` for a point `v` of `P` and the rotation `R` of `p`, no translation makes
`p` a fit. -/
theorem not_fitsAt_of_centred (hP : ∀ x ∈ P.vertices, -x ∈ P.vertices) {n : Fin 3 → ℝ}
    (hn : n ≠ 0) (hnu : n ⬝ᵥ viewDir p.view p.s p.t = 0) {h : ℝ}
    (hh : ∀ x ∈ P.vertices, n ⬝ᵥ x ≤ h) {v : Fin 3 → ℝ} (hv : v ∈ P.hull)
    (hp : h ≤ n ⬝ᵥ (p.rotation *ᵥ v)) (τ : Fin 2 → ℝ) : ¬ P.FitsAt p τ := by
  intro hfit
  have h0 := fitsAt_zero_of_fitsAt hP hfit ⟨v, hv, rfl⟩
  rw [add_zero, P.screen_image_hull p] at h0
  have := lt_of_mem_interior_convexHull (screenFunctional_ne_zero hnu hn)
    (S := {p.screen x | x ∈ P.vertices})
    (by rintro _ ⟨x, hx, rfl⟩; rw [ChartPose.screenFunctional_screen hnu]; exact hh x hx) h0
  rw [ChartPose.screenFunctional_screen hnu] at this
  linarith

end Polyhedron

end Nieuwland
