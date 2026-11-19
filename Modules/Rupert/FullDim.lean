import Modules.Rupert.Scale
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-!
# Full-dimensional polyhedra

`IsRupert` builds in no full-dimensionality (`Modules/Rupert/Defs.lean`): with no points it holds
vacuously, a segment is never Rupert and a flat polygon always is. The project's statement
concerns polyhedra whose points span `ℝ³` (`RESEARCH.md` §1.1), so each result about a particular
polyhedron comes with a proof that it is full-dimensional (`<name>_fullDim`, next to
`<name>_isRupert` or `<name>_not_isRupert`).

## Main definitions and results

* `Nieuwland.Polyhedron.FullDim P`: the hull of `P` has an interior point in `ℝ³`.
* `Polyhedron.fullDim_iff_affineSpan`: equivalently, the vertices of `P` span `ℝ³` affinely.
* `Polyhedron.fullDim_of_span`: the differences of the vertices from one vertex span `ℝ³`.
* `Polyhedron.FullDim.smul`: scaling by a nonzero factor keeps a polyhedron full-dimensional.
-/

namespace Nieuwland

/-- A polyhedron `P` is **full-dimensional** if its hull has an interior point in `ℝ³`. -/
def Polyhedron.FullDim (P : Polyhedron) : Prop :=
  (interior P.hull).Nonempty

namespace Polyhedron

/-- A polyhedron is full-dimensional if and only if its vertices span `ℝ³` affinely. -/
theorem fullDim_iff_affineSpan {P : Polyhedron} :
    P.FullDim ↔ affineSpan ℝ (P.vertices : Set (Fin 3 → ℝ)) = ⊤ :=
  interior_convexHull_nonempty_iff_affineSpan_eq_top

/-- If the differences of the vertices from a vertex `c` span `ℝ³`, the polyhedron is
full-dimensional. -/
theorem fullDim_of_span {P : Polyhedron} {c : Fin 3 → ℝ} (hc : c ∈ P.vertices)
    (h : Submodule.span ℝ ((· - c) '' (P.vertices : Set (Fin 3 → ℝ))) = ⊤) : P.FullDim := by
  rw [fullDim_iff_affineSpan,
    AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ _ _ ⟨c, hc⟩,
    vectorSpan_eq_span_vsub_set_right ℝ (Finset.mem_coe.mpr hc)]
  simpa only [vsub_eq_sub] using h

/-- Scaling by a nonzero factor keeps a polyhedron full-dimensional. -/
theorem FullDim.smul {P : Polyhedron} (h : P.FullDim) {c : ℝ} (hc : c ≠ 0) :
    (P.smul c).FullDim := by
  classical
  rw [fullDim_iff_affineSpan] at h ⊢
  let f : (Fin 3 → ℝ) →ᵃ[ℝ] (Fin 3 → ℝ) := (LinearMap.lsmul ℝ (Fin 3 → ℝ) c).toAffineMap
  have hv : ((P.smul c).vertices : Set (Fin 3 → ℝ)) = f '' P.vertices := by
    ext x
    simp [Polyhedron.smul, f]
  rw [hv, ← AffineSubspace.map_span, h]
  exact AffineMap.map_top_of_surjective f fun y ↦ ⟨c⁻¹ • y, by simp [f, smul_smul, hc]⟩

end Polyhedron

end Nieuwland
