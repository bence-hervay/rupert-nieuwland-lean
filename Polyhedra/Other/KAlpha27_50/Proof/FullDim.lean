import Polyhedra.Other.KAlpha27_50.Definition
import Modules.Check.Leaf.FullDim

/-!
# The fixture `k-alpha/27-50` is full-dimensional

The points of `Other.KAlpha27_50.polyhedron` times `50` as exact values in `ℤ`, exported by `code/lean-export dim`:
three of their differences are linearly independent (`spanOk`, checked by the kernel), so their
polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled back (`eq_smul`,
`Polyhedron.FullDim.smul`), so is `Other.KAlpha27_50.polyhedron`.
-/

namespace Nieuwland.Polyhedra.KAlpha27_50Dim

open Check

/-- The points of `Other.KAlpha27_50.polyhedron` times `50`. -/
def points : List (V3 ℤ) := [
    ⟨50, 50, 50⟩,
    ⟨50, -50, -50⟩,
    ⟨-50, 50, -50⟩,
    ⟨-50, -50, 50⟩,
    ⟨-27, -27, -27⟩,
    ⟨-27, 27, 27⟩,
    ⟨27, -27, 27⟩,
    ⟨27, 27, -27⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 50 : ℝ) • Exact.reV (⟨50, 50, 50⟩ : V3 ℤ) = ![1, 1, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt1 : (1 / 50 : ℝ) • Exact.reV (⟨50, -50, -50⟩ : V3 ℤ) = ![1, -1, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt2 : (1 / 50 : ℝ) • Exact.reV (⟨-50, 50, -50⟩ : V3 ℤ) = ![-1, 1, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt3 : (1 / 50 : ℝ) • Exact.reV (⟨-50, -50, 50⟩ : V3 ℤ) = ![-1, -1, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt4 : (1 / 50 : ℝ) • Exact.reV (⟨-27, -27, -27⟩ : V3 ℤ) = ![-27/50, -27/50, -27/50] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt5 : (1 / 50 : ℝ) • Exact.reV (⟨-27, 27, 27⟩ : V3 ℤ) = ![-27/50, 27/50, 27/50] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt6 : (1 / 50 : ℝ) • Exact.reV (⟨27, -27, 27⟩ : V3 ℤ) = ![27/50, -27/50, 27/50] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt7 : (1 / 50 : ℝ) • Exact.reV (⟨27, 27, -27⟩ : V3 ℤ) = ![27/50, 27/50, -27/50] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem eq_smul : Other.KAlpha27_50.polyhedron = (Polyhedron.ofPoints points).smul (1 / 50) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7]

end Nieuwland.Polyhedra.KAlpha27_50Dim

namespace Nieuwland.Polyhedra

/-- **The fixture `k-alpha/27-50` is full-dimensional.** -/
theorem kAlpha27_50_fullDim : Other.KAlpha27_50.polyhedron.FullDim := by
  rw [KAlpha27_50Dim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk KAlpha27_50Dim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
