import Polyhedra.Other.SquarePyramidHeight1.Definition
import Modules.Check.Leaf.FullDim

/-!
# The fixture `other/square-pyramid-height-1` is full-dimensional

The points of `Other.SquarePyramidHeight1.polyhedron` times `1` as exact values in `ℤ`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Other.SquarePyramidHeight1.polyhedron`.
-/

namespace Nieuwland.Polyhedra.OtherSquarePyramidHeight1Dim

open Check

/-- The points of `Other.SquarePyramidHeight1.polyhedron` times `1`. -/
def points : List (V3 ℤ) := [
    ⟨-1, -1, 0⟩,
    ⟨-1, 1, 0⟩,
    ⟨0, 0, 1⟩,
    ⟨1, -1, 0⟩,
    ⟨1, 1, 0⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 1 : ℝ) • Exact.reV (⟨-1, -1, 0⟩ : V3 ℤ) = ![-1, -1, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt1 : (1 / 1 : ℝ) • Exact.reV (⟨-1, 1, 0⟩ : V3 ℤ) = ![-1, 1, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt2 : (1 / 1 : ℝ) • Exact.reV (⟨0, 0, 1⟩ : V3 ℤ) = ![0, 0, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt3 : (1 / 1 : ℝ) • Exact.reV (⟨1, -1, 0⟩ : V3 ℤ) = ![1, -1, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt4 : (1 / 1 : ℝ) • Exact.reV (⟨1, 1, 0⟩ : V3 ℤ) = ![1, 1, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem eq_smul : Other.SquarePyramidHeight1.polyhedron = (Polyhedron.ofPoints points).smul (1 / 1) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4]

end Nieuwland.Polyhedra.OtherSquarePyramidHeight1Dim

namespace Nieuwland.Polyhedra

/-- **The fixture `other/square-pyramid-height-1` is full-dimensional.** -/
theorem otherSquarePyramidHeight1_fullDim : Other.SquarePyramidHeight1.polyhedron.FullDim := by
  rw [OtherSquarePyramidHeight1Dim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk OtherSquarePyramidHeight1Dim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
