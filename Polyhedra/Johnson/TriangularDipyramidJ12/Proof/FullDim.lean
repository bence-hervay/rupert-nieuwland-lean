import Polyhedra.Johnson.TriangularDipyramidJ12.Definition
import Modules.Check.Leaf.FullDim

set_option linter.style.longLine false

/-!
# The fixture `johnson/triangular-dipyramid-j12` is full-dimensional

The points of `Johnson.TriangularDipyramidJ12.polyhedron` times `1` as exact values in `ℤ`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Johnson.TriangularDipyramidJ12.polyhedron`.
-/

namespace Nieuwland.Polyhedra.JohnsonTriangularDipyramidJ12Dim

open Check

/-- The points of `Johnson.TriangularDipyramidJ12.polyhedron` times `1`. -/
def points : List (V3 ℤ) := [
    ⟨2, 2, 2⟩,
    ⟨-2, -2, -2⟩,
    ⟨2, -1, -1⟩,
    ⟨-1, 2, -1⟩,
    ⟨-1, -1, 2⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 1 : ℝ) • Exact.reV (⟨2, 2, 2⟩ : V3 ℤ) = ![2, 2, 2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt1 : (1 / 1 : ℝ) • Exact.reV (⟨-2, -2, -2⟩ : V3 ℤ) = ![-2, -2, -2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt2 : (1 / 1 : ℝ) • Exact.reV (⟨2, -1, -1⟩ : V3 ℤ) = ![2, -1, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt3 : (1 / 1 : ℝ) • Exact.reV (⟨-1, 2, -1⟩ : V3 ℤ) = ![-1, 2, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt4 : (1 / 1 : ℝ) • Exact.reV (⟨-1, -1, 2⟩ : V3 ℤ) = ![-1, -1, 2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem eq_smul : Johnson.TriangularDipyramidJ12.polyhedron = (Polyhedron.ofPoints points).smul (1 / 1) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4]

end Nieuwland.Polyhedra.JohnsonTriangularDipyramidJ12Dim

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/triangular-dipyramid-j12` is full-dimensional.** -/
theorem johnsonTriangularDipyramidJ12_fullDim : Johnson.TriangularDipyramidJ12.polyhedron.FullDim := by
  rw [JohnsonTriangularDipyramidJ12Dim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk JohnsonTriangularDipyramidJ12Dim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
