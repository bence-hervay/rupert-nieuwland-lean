import Polyhedra.Other.KAlpha51_100.Definition
import Modules.Check.Leaf.FullDim

/-!
# The fixture `k-alpha/51-100` is full-dimensional

The points of `Other.KAlpha51_100.polyhedron` times `100` as exact values in `ℤ`, exported by `code/lean-export dim`:
three of their differences are linearly independent (`spanOk`, checked by the kernel), so their
polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled back (`eq_smul`,
`Polyhedron.FullDim.smul`), so is `Other.KAlpha51_100.polyhedron`.
-/

namespace Nieuwland.Polyhedra.KAlpha51_100Dim

open Check

/-- The points of `Other.KAlpha51_100.polyhedron` times `100`. -/
def points : List (V3 ℤ) := [
    ⟨100, 100, 100⟩,
    ⟨100, -100, -100⟩,
    ⟨-100, 100, -100⟩,
    ⟨-100, -100, 100⟩,
    ⟨-51, -51, -51⟩,
    ⟨-51, 51, 51⟩,
    ⟨51, -51, 51⟩,
    ⟨51, 51, -51⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 100 : ℝ) • Exact.reV (⟨100, 100, 100⟩ : V3 ℤ) = ![1, 1, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt1 : (1 / 100 : ℝ) • Exact.reV (⟨100, -100, -100⟩ : V3 ℤ) = ![1, -1, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt2 : (1 / 100 : ℝ) • Exact.reV (⟨-100, 100, -100⟩ : V3 ℤ) = ![-1, 1, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt3 : (1 / 100 : ℝ) • Exact.reV (⟨-100, -100, 100⟩ : V3 ℤ) = ![-1, -1, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt4 : (1 / 100 : ℝ) • Exact.reV (⟨-51, -51, -51⟩ : V3 ℤ) = ![-51/100, -51/100, -51/100]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt5 : (1 / 100 : ℝ) • Exact.reV (⟨-51, 51, 51⟩ : V3 ℤ) = ![-51/100, 51/100, 51/100] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt6 : (1 / 100 : ℝ) • Exact.reV (⟨51, -51, 51⟩ : V3 ℤ) = ![51/100, -51/100, 51/100] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt7 : (1 / 100 : ℝ) • Exact.reV (⟨51, 51, -51⟩ : V3 ℤ) = ![51/100, 51/100, -51/100] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem eq_smul : Other.KAlpha51_100.polyhedron = (Polyhedron.ofPoints points).smul (1 / 100) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7]

end Nieuwland.Polyhedra.KAlpha51_100Dim

namespace Nieuwland.Polyhedra

/-- **The fixture `k-alpha/51-100` is full-dimensional.** -/
theorem kAlpha51_100_fullDim : Other.KAlpha51_100.polyhedron.FullDim := by
  rw [KAlpha51_100Dim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk KAlpha51_100Dim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
