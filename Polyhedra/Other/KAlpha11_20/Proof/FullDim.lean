import Polyhedra.Other.KAlpha11_20.Definition
import Modules.Check.Leaf.FullDim

/-!
# The fixture `k-alpha/11-20` is full-dimensional

The points of `Other.KAlpha11_20.polyhedron` times `20` as exact values in `ℤ`, exported by `code/lean-export dim`:
three of their differences are linearly independent (`spanOk`, checked by the kernel), so their
polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled back (`eq_smul`,
`Polyhedron.FullDim.smul`), so is `Other.KAlpha11_20.polyhedron`.
-/

namespace Nieuwland.Polyhedra.KAlpha11_20Dim

open Check

/-- The points of `Other.KAlpha11_20.polyhedron` times `20`. -/
def points : List (V3 ℤ) := [
    ⟨20, 20, 20⟩,
    ⟨20, -20, -20⟩,
    ⟨-20, 20, -20⟩,
    ⟨-20, -20, 20⟩,
    ⟨-11, -11, -11⟩,
    ⟨-11, 11, 11⟩,
    ⟨11, -11, 11⟩,
    ⟨11, 11, -11⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 20 : ℝ) • Exact.reV (⟨20, 20, 20⟩ : V3 ℤ) = ![1, 1, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt1 : (1 / 20 : ℝ) • Exact.reV (⟨20, -20, -20⟩ : V3 ℤ) = ![1, -1, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt2 : (1 / 20 : ℝ) • Exact.reV (⟨-20, 20, -20⟩ : V3 ℤ) = ![-1, 1, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt3 : (1 / 20 : ℝ) • Exact.reV (⟨-20, -20, 20⟩ : V3 ℤ) = ![-1, -1, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt4 : (1 / 20 : ℝ) • Exact.reV (⟨-11, -11, -11⟩ : V3 ℤ) = ![-11/20, -11/20, -11/20] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt5 : (1 / 20 : ℝ) • Exact.reV (⟨-11, 11, 11⟩ : V3 ℤ) = ![-11/20, 11/20, 11/20] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt6 : (1 / 20 : ℝ) • Exact.reV (⟨11, -11, 11⟩ : V3 ℤ) = ![11/20, -11/20, 11/20] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt7 : (1 / 20 : ℝ) • Exact.reV (⟨11, 11, -11⟩ : V3 ℤ) = ![11/20, 11/20, -11/20] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem eq_smul : Other.KAlpha11_20.polyhedron = (Polyhedron.ofPoints points).smul (1 / 20) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7]

end Nieuwland.Polyhedra.KAlpha11_20Dim

namespace Nieuwland.Polyhedra

/-- **The fixture `k-alpha/11-20` is full-dimensional.** -/
theorem kAlpha11_20_fullDim : Other.KAlpha11_20.polyhedron.FullDim := by
  rw [KAlpha11_20Dim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk KAlpha11_20Dim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
