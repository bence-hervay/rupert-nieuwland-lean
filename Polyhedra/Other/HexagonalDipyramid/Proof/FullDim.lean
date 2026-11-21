import Polyhedra.Other.HexagonalDipyramid.Definition
import Modules.Check.Leaf.FullDim

set_option linter.style.longLine false

/-!
# The fixture `dipyramid/hexagonal-dipyramid` is full-dimensional

The points of `Other.HexagonalDipyramid.polyhedron` times `6` as exact values in `ZSqrt 3`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Other.HexagonalDipyramid.polyhedron`.
-/

namespace Nieuwland.Polyhedra.DipyramidHexagonalDipyramidDim

open Check

/-- The points of `Other.HexagonalDipyramid.polyhedron` times `6`. -/
def points : List (V3 (ZSqrt 3)) := [
    ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨-6, 0⟩⟩,
    ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨6, 0⟩⟩,
    ⟨⟨3, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩⟩,
    ⟨⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩⟩,
    ⟨⟨-3, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩⟩,
    ⟨⟨-3, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩⟩,
    ⟨⟨0, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩⟩,
    ⟨⟨3, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 6 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨-6, 0⟩⟩ : V3 (ZSqrt 3)) = ![0, 0, -1]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt1 : (1 / 6 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨6, 0⟩⟩ : V3 (ZSqrt 3)) = ![0, 0, 1] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt2 : (1 / 6 : ℝ) • Exact.reV (⟨⟨3, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 3)) = ![1/2, 1/6 *
    √3, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt3 : (1 / 6 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 3)) = ![0, 1/3 * √3,
    0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt4 : (1 / 6 : ℝ) • Exact.reV (⟨⟨-3, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 3)) = ![-1/2, 1/6 *
    √3, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt5 : (1 / 6 : ℝ) • Exact.reV (⟨⟨-3, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 3)) = ![-1/2,
    -(1/6 * √3), 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt6 : (1 / 6 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 3)) = ![0, -(1/3 *
    √3), 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt7 : (1 / 6 : ℝ) • Exact.reV (⟨⟨3, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 3)) = ![1/2, -(1/6
    * √3), 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem eq_smul : Other.HexagonalDipyramid.polyhedron = (Polyhedron.ofPoints points).smul (1 / 6) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7]

end Nieuwland.Polyhedra.DipyramidHexagonalDipyramidDim

namespace Nieuwland.Polyhedra

/-- **The fixture `dipyramid/hexagonal-dipyramid` is full-dimensional.** -/
theorem dipyramidHexagonalDipyramid_fullDim : Other.HexagonalDipyramid.polyhedron.FullDim := by
  rw [DipyramidHexagonalDipyramidDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk DipyramidHexagonalDipyramidDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
