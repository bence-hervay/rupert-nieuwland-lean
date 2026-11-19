import Polyhedra.Other.KAlpha14_25.Definition
import Modules.Check.Leaf.FullDim

/-!
# The fixture `k-alpha/14-25` is full-dimensional

The points of `Other.KAlpha14_25.polyhedron` times `25` as exact values in `ℤ`, exported by `code/lean-export dim`:
three of their differences are linearly independent (`spanOk`, checked by the kernel), so their
polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled back (`eq_smul`,
`Polyhedron.FullDim.smul`), so is `Other.KAlpha14_25.polyhedron`.
-/

namespace Nieuwland.Polyhedra.KAlpha14_25Dim

open Check

/-- The points of `Other.KAlpha14_25.polyhedron` times `25`. -/
def points : List (V3 ℤ) := [
    ⟨25, 25, 25⟩,
    ⟨25, -25, -25⟩,
    ⟨-25, 25, -25⟩,
    ⟨-25, -25, 25⟩,
    ⟨-14, -14, -14⟩,
    ⟨-14, 14, 14⟩,
    ⟨14, -14, 14⟩,
    ⟨14, 14, -14⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 25 : ℝ) • Exact.reV (⟨25, 25, 25⟩ : V3 ℤ) = ![1, 1, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt1 : (1 / 25 : ℝ) • Exact.reV (⟨25, -25, -25⟩ : V3 ℤ) = ![1, -1, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt2 : (1 / 25 : ℝ) • Exact.reV (⟨-25, 25, -25⟩ : V3 ℤ) = ![-1, 1, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt3 : (1 / 25 : ℝ) • Exact.reV (⟨-25, -25, 25⟩ : V3 ℤ) = ![-1, -1, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt4 : (1 / 25 : ℝ) • Exact.reV (⟨-14, -14, -14⟩ : V3 ℤ) = ![-14/25, -14/25, -14/25] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt5 : (1 / 25 : ℝ) • Exact.reV (⟨-14, 14, 14⟩ : V3 ℤ) = ![-14/25, 14/25, 14/25] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt6 : (1 / 25 : ℝ) • Exact.reV (⟨14, -14, 14⟩ : V3 ℤ) = ![14/25, -14/25, 14/25] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt7 : (1 / 25 : ℝ) • Exact.reV (⟨14, 14, -14⟩ : V3 ℤ) = ![14/25, 14/25, -14/25] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem eq_smul : Other.KAlpha14_25.polyhedron = (Polyhedron.ofPoints points).smul (1 / 25) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7]

end Nieuwland.Polyhedra.KAlpha14_25Dim

namespace Nieuwland.Polyhedra

/-- **The fixture `k-alpha/14-25` is full-dimensional.** -/
theorem kAlpha14_25_fullDim : Other.KAlpha14_25.polyhedron.FullDim := by
  rw [KAlpha14_25Dim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk KAlpha14_25Dim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
