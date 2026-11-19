import Modules.Rupert.Charts
import Modules.Rupert.Hull
import Modules.Rupert.Screen

/-!
# Fits at chart poses

The negative side of the problem is stated pose by pose, in the charts of
`Modules/Rupert/Charts.lean`.

* `P.FitsAt p τ`: at the chart pose `p`, the shadow of the rotated copy, moved by `τ` in screen
  coordinates, lies in the interior of the shadow of `P`. A fit at any pose proves the Rupert
  property (`Polyhedron.isRupert_of_fitsAt`).
* `P.NoFit S`: no pose of the set `S` of chart poses fits, with any translation. This is the
  `NoFit` claim of `RESEARCH.md` §6; certificates prove it for boxes of chart coordinates and
  assemble boxes into covers (`Polyhedron.noFit_union`).
-/

open Matrix

namespace Nieuwland

namespace Polyhedron

/-- At the chart pose `p`, the shadow of the rotated copy of `P`, moved by `τ` in screen
coordinates, lies in the interior of the shadow of `P`. -/
def FitsAt (P : Polyhedron) (p : ChartPose) (τ : Fin 2 → ℝ) : Prop :=
  {p.screen (p.rotation *ᵥ x) + τ | x ∈ P.hull} ⊆ interior {p.screen x | x ∈ P.hull}

/-- No pose of `S` fits `P`, with any translation. -/
def NoFit (P : Polyhedron) (S : Set ChartPose) : Prop :=
  ∀ p ∈ S, ∀ τ, ¬ P.FitsAt p τ

/-- **Vertex criterion at a chart pose.** -/
theorem fitsAt_iff_vertices (P : Polyhedron) (p : ChartPose) (τ : Fin 2 → ℝ) :
    P.FitsAt p τ ↔ ∀ v ∈ P.vertices,
      p.screen (p.rotation *ᵥ v) + τ ∈ interior (convexHull ℝ {p.screen w | w ∈ P.vertices}) :=
  P.image_add_subset_interior_iff (screenₗ p.view p.s p.t ∘ₗ p.rotation.mulVecLin)
    (screenₗ p.view p.s p.t) τ

/-- The shadow of `P` at a chart pose is the polygon spanned by the shadows of its vertices. -/
theorem screen_image_hull (P : Polyhedron) (p : ChartPose) :
    {p.screen x | x ∈ P.hull} = convexHull ℝ {p.screen w | w ∈ P.vertices} :=
  P.image_hull (screenₗ p.view p.s p.t)

/-- A fit at a chart pose proves the Rupert property. -/
theorem isRupert_of_fitsAt {P : Polyhedron} {p : ChartPose} {τ : Fin 2 → ℝ}
    (h : P.FitsAt p τ) : P.IsRupert :=
  P.isRupert_iff_exists_surjective.mpr
    ⟨screenₗ p.view p.s p.t, screen_surjective _ _ _, p.rotation, p.rotation_mem, τ, h⟩

theorem NoFit.mono {P : Polyhedron} {S T : Set ChartPose} (h : P.NoFit T) (hST : S ⊆ T) :
    P.NoFit S :=
  fun p hp ↦ h p (hST hp)

theorem noFit_union {P : Polyhedron} {S T : Set ChartPose} :
    P.NoFit (S ∪ T) ↔ P.NoFit S ∧ P.NoFit T :=
  ⟨fun h ↦ ⟨h.mono Set.subset_union_left, h.mono Set.subset_union_right⟩,
    fun h p hp ↦ hp.elim (h.1 p) (h.2 p)⟩

theorem noFit_iUnion {ι : Sort*} {P : Polyhedron} {S : ι → Set ChartPose} :
    P.NoFit (⋃ i, S i) ↔ ∀ i, P.NoFit (S i) :=
  ⟨fun h i ↦ h.mono (Set.subset_iUnion S i), fun h p hp ↦ by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    exact h i p hi⟩

end Polyhedron

end Nieuwland
