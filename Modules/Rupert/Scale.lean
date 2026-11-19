import Definitions.Polyhedra
import Modules.Rupert.Hull
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Scaling

Scaling a polyhedron by a nonzero factor does not change whether it is Rupert
(`Polyhedron.isRupert_smul_iff`): the same rotations work, with the translation scaled. Exact
checks therefore work with coordinates times a common denominator, and their results are stated
for the coordinates of the fixtures.
-/

open Matrix Pointwise

namespace Nieuwland

namespace Polyhedron

theorem mem_smul_vertices {c : ℝ} {P : Polyhedron} {x : Fin 3 → ℝ} :
    x ∈ (P.smul c).vertices ↔ ∃ v ∈ P.vertices, c • v = x := by
  classical
  simp [Polyhedron.smul]

theorem smul_smul_inv {c : ℝ} (hc : c ≠ 0) (P : Polyhedron) : (P.smul c).smul c⁻¹ = P := by
  classical
  cases P with
  | mk V =>
    simp only [Polyhedron.smul, Polyhedron.mk.injEq]
    convert Finset.image_id (s := V) using 1
    rw [Finset.image_image]
    congr 1
    funext v
    simp [smul_smul, inv_mul_cancel₀ hc]

theorem projXY_mulVec_smul (R : Matrix (Fin 3) (Fin 3) ℝ) (c : ℝ) (v : Fin 3 → ℝ) :
    projXY (R *ᵥ (c • v)) = c • projXY (R *ᵥ v) := by
  rw [mulVec_smul]
  exact map_smul projXYₗ c _

/-- The shadows of the scaled vertices are the scaled shadows. -/
theorem shadows_smul (c : ℝ) (P : Polyhedron) (R : Matrix (Fin 3) (Fin 3) ℝ) :
    {projXY (R *ᵥ w) | w ∈ (P.smul c).vertices} = c • {projXY (R *ᵥ w) | w ∈ P.vertices} := by
  ext y
  simp only [Set.mem_ofPred_eq, mem_smul_vertices, Set.mem_smul_set]
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨_, ⟨v, hv, rfl⟩, (projXY_mulVec_smul R c v).symm⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨c • v, ⟨v, hv, rfl⟩, projXY_mulVec_smul R c v⟩

theorem isRupert_smul {c : ℝ} (hc : c ≠ 0) {P : Polyhedron} (h : P.IsRupert) :
    (P.smul c).IsRupert := by
  rw [isRupert_iff_vertices] at h ⊢
  obtain ⟨R₁, hR₁, R₂, hR₂, t, h⟩ := h
  refine ⟨R₁, hR₁, R₂, hR₂, c • t, fun x hx ↦ ?_⟩
  obtain ⟨v, hv, rfl⟩ := mem_smul_vertices.mp hx
  rw [shadows_smul, convexHull_smul, interior_smul₀ hc, projXY_mulVec_smul, ← smul_add]
  exact Set.smul_mem_smul_set (h v hv)

/-- **Scaling.** A polyhedron scaled by `c ≠ 0` is Rupert iff the polyhedron is. -/
theorem isRupert_smul_iff {c : ℝ} (hc : c ≠ 0) (P : Polyhedron) :
    (P.smul c).IsRupert ↔ P.IsRupert := by
  refine ⟨fun h ↦ ?_, isRupert_smul hc⟩
  rw [← smul_smul_inv hc P]
  exact isRupert_smul (inv_ne_zero hc) h

end Polyhedron

end Nieuwland
