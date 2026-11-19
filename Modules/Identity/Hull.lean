import Definitions.Polyhedra
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Faces of the convex hull of finitely many points

For finitely many points `s` and a linear functional `x ↦ w ⬝ᵥ x` with `w ⬝ᵥ v ≤ c` on `s`:

* the whole hull lies in the half-space `w ⬝ᵥ x ≤ c` (`le_of_mem_convexHull`);
* the hull meets the plane `w ⬝ᵥ x = c` exactly in the hull of the points of `s` on it
  (`convexHull_inter_eq`): a face of a polytope is the hull of the vertices on it;
* if `p` is the only point of `s` on the plane, `p` is an extreme point of the hull
  (`mem_extremePoints_of_contact`), and if two points `a ≠ b` are, the hull meets the plane in
  the segment `[a, b]`.

These are the facts that facet certificates (`Modules/Identity/Faces.lean`) rest on.
-/

open Matrix

namespace Nieuwland.Identity

variable {s : Finset (Fin 3 → ℝ)} {w : Fin 3 → ℝ} {c : ℝ}

/-- `x ↦ w ⬝ᵥ x` is linear. -/
theorem isLinearMap_dot (w : Fin 3 → ℝ) : IsLinearMap ℝ fun x : Fin 3 → ℝ ↦ w ⬝ᵥ x :=
  ⟨fun x y ↦ dotProduct_add w x y, fun a x ↦ dotProduct_smul a w x⟩

/-- A bound of a linear functional on the points holds on their hull. -/
theorem le_of_mem_convexHull {S : Set (Fin 3 → ℝ)} (hle : ∀ v ∈ S, w ⬝ᵥ v ≤ c) {x : Fin 3 → ℝ}
    (hx : x ∈ convexHull ℝ S) : w ⬝ᵥ x ≤ c :=
  convexHull_min (t := {x | w ⬝ᵥ x ≤ c}) hle (convex_halfSpace_le (isLinearMap_dot w) c) hx

/-- **The face of a supporting plane.** If `w ⬝ᵥ v ≤ c` on the points `s`, the hull of `s` meets
the plane `w ⬝ᵥ x = c` in the hull of the points of `s` on it. -/
theorem convexHull_inter_eq (hle : ∀ v ∈ s, w ⬝ᵥ v ≤ c) :
    convexHull ℝ (s : Set (Fin 3 → ℝ)) ∩ {x | w ⬝ᵥ x = c} =
      convexHull ℝ {v | v ∈ s ∧ w ⬝ᵥ v = c} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hxc⟩
    obtain ⟨l, hl₀, hl₁, rfl⟩ := Finset.mem_convexHull.mp hx
    rw [Finset.centerMass_eq_of_sum_1 _ _ hl₁] at hxc
    simp only [id_eq, Set.mem_ofPred_eq, dotProduct_sum, dotProduct_smul, smul_eq_mul] at hxc
    -- `∑ l v (c - w ⬝ᵥ v) = 0` with nonnegative terms
    have hsum : ∑ v ∈ s, l v * (c - w ⬝ᵥ v) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hl₁, one_mul, hxc, sub_self]
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun v hv ↦
      mul_nonneg (hl₀ v hv) (sub_nonneg.mpr (hle v hv))).mp hsum
    classical
    rw [← Finset.centerMass_filter_ne_zero]
    refine Finset.centerMass_mem_convexHull _ (fun v hv ↦ hl₀ v (Finset.mem_filter.mp hv).1) ?_
      fun v hv ↦ ?_
    · rw [Finset.sum_filter_ne_zero, hl₁]
      exact one_pos
    · obtain ⟨hv, hl⟩ := Finset.mem_filter.mp hv
      refine ⟨hv, ?_⟩
      rcases mul_eq_zero.mp (hterm v hv) with h | h
      · exact absurd h hl
      · simp only [id_eq]
        linarith
  · refine Set.subset_inter (convexHull_mono fun v hv ↦ hv.1) ?_
    exact convexHull_min (fun v hv ↦ hv.2) (convex_hyperplane (isLinearMap_dot w) c)

/-- **Exposed points are extreme.** If `w ⬝ᵥ v ≤ c` on `s` with equality only at `p ∈ s`, then `p`
is an extreme point of the hull of `s`. -/
theorem mem_extremePoints_of_contact {p : Fin 3 → ℝ} (hp : p ∈ s) (hle : ∀ v ∈ s, w ⬝ᵥ v ≤ c)
    (heq : ∀ v ∈ s, w ⬝ᵥ v = c ↔ v = p) :
    p ∈ (convexHull ℝ (s : Set (Fin 3 → ℝ))).extremePoints ℝ := by
  have hface : convexHull ℝ (s : Set (Fin 3 → ℝ)) ∩ {x | w ⬝ᵥ x = c} = {p} := by
    rw [convexHull_inter_eq hle]
    convert convexHull_singleton (𝕜 := ℝ) p using 2
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun h ↦ (heq v h.1).mp h.2, fun h ↦ h ▸ ⟨hp, (heq p hp).mpr rfl⟩⟩
  have hpc : w ⬝ᵥ p = c := (heq p hp).mpr rfl
  refine mem_extremePoints.mpr ⟨subset_convexHull ℝ _ hp, fun x hx y hy hxy ↦ ?_⟩
  obtain ⟨a, b, ha, hb, hab, hp'⟩ := hxy
  have hx' := le_of_mem_convexHull hle hx
  have hy' := le_of_mem_convexHull hle hy
  rw [← hp'] at hpc
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at hpc
  have hz : a * (c - w ⬝ᵥ x) + b * (c - w ⬝ᵥ y) = 0 := by linear_combination c * hab - hpc
  have h₁ := mul_nonneg ha.le (sub_nonneg.mpr hx')
  have h₂ := mul_nonneg hb.le (sub_nonneg.mpr hy')
  have hxc : w ⬝ᵥ x = c := by
    have : a * (c - w ⬝ᵥ x) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h <;> [linarith; linarith]
  have hyc : w ⬝ᵥ y = c := by
    have : b * (c - w ⬝ᵥ y) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h <;> [linarith; linarith]
  have h₁ : x ∈ ({p} : Set (Fin 3 → ℝ)) := hface ▸ ⟨hx, hxc⟩
  have h₂ : y ∈ ({p} : Set (Fin 3 → ℝ)) := hface ▸ ⟨hy, hyc⟩
  exact ⟨h₁, h₂⟩

/-- **Edges.** If `w ⬝ᵥ v ≤ c` on `s` with equality exactly at `a, b ∈ s`, the hull of `s` meets
the plane `w ⬝ᵥ x = c` in the segment `[a, b]`. -/
theorem convexHull_inter_eq_segment {a b : Fin 3 → ℝ} (ha : a ∈ s) (hb : b ∈ s)
    (hle : ∀ v ∈ s, w ⬝ᵥ v ≤ c) (heq : ∀ v ∈ s, w ⬝ᵥ v = c ↔ v = a ∨ v = b) :
    convexHull ℝ (s : Set (Fin 3 → ℝ)) ∩ {x | w ⬝ᵥ x = c} = segment ℝ a b := by
  rw [convexHull_inter_eq hle, ← convexHull_pair]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · exact fun h ↦ (heq v h.1).mp h.2
  · rintro (rfl | rfl)
    · exact ⟨ha, (heq _ ha).mpr (Or.inl rfl)⟩
    · exact ⟨hb, (heq _ hb).mpr (Or.inr rfl)⟩

end Nieuwland.Identity
