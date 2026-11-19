import Polyhedra.Johnson.AugmentedTruncatedTetrahedron.Definition
import Modules.Check.Leaf.FullDim

set_option linter.style.longLine false

/-!
# The fixture `johnson/augmented-truncated-tetrahedron` is full-dimensional

The points of `Johnson.AugmentedTruncatedTetrahedron.polyhedron` times `3` as exact values in `ℤ`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Johnson.AugmentedTruncatedTetrahedron.polyhedron`.
-/

namespace Nieuwland.Polyhedra.JohnsonAugmentedTruncatedTetrahedronDim

open Check

/-- The points of `Johnson.AugmentedTruncatedTetrahedron.polyhedron` times `3`. -/
def points : List (V3 ℤ) := [
    ⟨3, -3, 9⟩,
    ⟨3, 3, -9⟩,
    ⟨-3, 3, 9⟩,
    ⟨-3, -3, -9⟩,
    ⟨9, -3, 3⟩,
    ⟨9, 3, -3⟩,
    ⟨-9, 3, 3⟩,
    ⟨-9, -3, -3⟩,
    ⟨3, -9, 3⟩,
    ⟨3, 9, -3⟩,
    ⟨-3, 9, 3⟩,
    ⟨-3, -9, -3⟩,
    ⟨5, 5, 11⟩,
    ⟨11, 5, 5⟩,
    ⟨5, 11, 5⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 3 : ℝ) • Exact.reV (⟨3, -3, 9⟩ : V3 ℤ) = ![1, -1, 3] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt1 : (1 / 3 : ℝ) • Exact.reV (⟨3, 3, -9⟩ : V3 ℤ) = ![1, 1, -3] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt2 : (1 / 3 : ℝ) • Exact.reV (⟨-3, 3, 9⟩ : V3 ℤ) = ![-1, 1, 3] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt3 : (1 / 3 : ℝ) • Exact.reV (⟨-3, -3, -9⟩ : V3 ℤ) = ![-1, -1, -3] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt4 : (1 / 3 : ℝ) • Exact.reV (⟨9, -3, 3⟩ : V3 ℤ) = ![3, -1, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt5 : (1 / 3 : ℝ) • Exact.reV (⟨9, 3, -3⟩ : V3 ℤ) = ![3, 1, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt6 : (1 / 3 : ℝ) • Exact.reV (⟨-9, 3, 3⟩ : V3 ℤ) = ![-3, 1, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt7 : (1 / 3 : ℝ) • Exact.reV (⟨-9, -3, -3⟩ : V3 ℤ) = ![-3, -1, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt8 : (1 / 3 : ℝ) • Exact.reV (⟨3, -9, 3⟩ : V3 ℤ) = ![1, -3, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt9 : (1 / 3 : ℝ) • Exact.reV (⟨3, 9, -3⟩ : V3 ℤ) = ![1, 3, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt10 : (1 / 3 : ℝ) • Exact.reV (⟨-3, 9, 3⟩ : V3 ℤ) = ![-1, 3, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt11 : (1 / 3 : ℝ) • Exact.reV (⟨-3, -9, -3⟩ : V3 ℤ) = ![-1, -3, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt12 : (1 / 3 : ℝ) • Exact.reV (⟨5, 5, 11⟩ : V3 ℤ) = ![5/3, 5/3, 11/3] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt13 : (1 / 3 : ℝ) • Exact.reV (⟨11, 5, 5⟩ : V3 ℤ) = ![11/3, 5/3, 5/3] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt14 : (1 / 3 : ℝ) • Exact.reV (⟨5, 11, 5⟩ : V3 ℤ) = ![5/3, 11/3, 5/3] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem eq_smul : Johnson.AugmentedTruncatedTetrahedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 3) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14]

end Nieuwland.Polyhedra.JohnsonAugmentedTruncatedTetrahedronDim

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/augmented-truncated-tetrahedron` is full-dimensional.** -/
theorem johnsonAugmentedTruncatedTetrahedron_fullDim : Johnson.AugmentedTruncatedTetrahedron.polyhedron.FullDim := by
  rw [JohnsonAugmentedTruncatedTetrahedronDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk JohnsonAugmentedTruncatedTetrahedronDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
