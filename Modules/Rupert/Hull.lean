import Modules.Rupert.Basic
import Mathlib.Analysis.Convex.Topology

/-!
# Shadows of polyhedra

The image of a convex hull under a linear map is the convex hull of the image. So the shadow of a
polyhedron is the convex polygon spanned by the shadows of its vertices
(`Polyhedron.image_hull`, `Polyhedron.shadow_eq_convexHull`).

The interior of a convex set is convex. So a moved shadow lies in the interior of another shadow
as soon as the moved shadows of the vertices do (`Polyhedron.image_add_subset_interior_iff`):
whether a pose is a fit is decided by finitely many points and the interior of one polygon
(`Polyhedron.isRupert_iff_vertices`).

The lemmas are stated for arbitrary linear maps, so that they also apply in the screen coordinates
of `Modules/Rupert/Screen.lean`.
-/

open Matrix

namespace Nieuwland.Polyhedron

/-- The image of a polyhedron under a linear map is the convex hull of the images of its
vertices. -/
theorem image_hull {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Polyhedron)
    (f : (Fin 3 → ℝ) →ₗ[ℝ] E) : {f x | x ∈ P.hull} = convexHull ℝ {f v | v ∈ P.vertices} :=
  f.image_convexHull _

/-- The shadow of a rotated polyhedron is the convex hull of the shadows of its vertices. -/
theorem shadow_eq_convexHull (P : Polyhedron) (R : Matrix (Fin 3) (Fin 3) ℝ) :
    {projXY (R *ᵥ x) | x ∈ P.hull} = convexHull ℝ {projXY (R *ᵥ v) | v ∈ P.vertices} :=
  P.image_hull (projXYₗ ∘ₗ R.mulVecLin)

/-- **Vertex criterion.** For linear maps `f, g : ℝ³ → ℝ²`, the image of `P` under `f`, moved by
`t`, lies in the interior of its image under `g` iff the moved images of the vertices do. -/
theorem image_add_subset_interior_iff (P : Polyhedron) (f g : (Fin 3 → ℝ) →ₗ[ℝ] Fin 2 → ℝ)
    (t : Fin 2 → ℝ) :
    {f x + t | x ∈ P.hull} ⊆ interior {g x | x ∈ P.hull} ↔
      ∀ v ∈ P.vertices, f v + t ∈ interior (convexHull ℝ {g w | w ∈ P.vertices}) := by
  rw [P.image_hull g]
  refine ⟨fun h v hv ↦ h ⟨v, subset_convexHull ℝ _ hv, rfl⟩, ?_⟩
  rintro h _ ⟨x, hx, rfl⟩
  have hconv : Convex ℝ ((fun x ↦ f x + t) ⁻¹' interior (convexHull ℝ {g w | w ∈ P.vertices})) :=
    ((convex_convexHull ℝ _).interior.translate_preimage_left t).linear_preimage f
  exact convexHull_min (fun v hv ↦ h v hv) hconv hx

/-- `P` is Rupert iff for some rotations `R₁, R₂` and translation `t`, the moved shadows
`projXY (R₁ *ᵥ v) + t` of all vertices `v` lie in the interior of the polygon spanned by the
shadows `projXY (R₂ *ᵥ w)` of the vertices. -/
theorem isRupert_iff_vertices (P : Polyhedron) :
    P.IsRupert ↔ ∃ R₁ ∈ SO(3), ∃ R₂ ∈ SO(3), ∃ t : Fin 2 → ℝ, ∀ v ∈ P.vertices,
      projXY (R₁ *ᵥ v) + t ∈ interior (convexHull ℝ {projXY (R₂ *ᵥ w) | w ∈ P.vertices}) := by
  unfold IsRupert FitsThrough
  refine exists_congr fun R₁ ↦ and_congr_right fun _ ↦ exists_congr fun R₂ ↦
    and_congr_right fun _ ↦ exists_congr fun t ↦ ?_
  exact P.image_add_subset_interior_iff (projXYₗ ∘ₗ R₁.mulVecLin) (projXYₗ ∘ₗ R₂.mulVecLin) t

end Nieuwland.Polyhedron
