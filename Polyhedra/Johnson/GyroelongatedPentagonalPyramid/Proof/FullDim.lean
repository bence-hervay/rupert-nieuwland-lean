import Polyhedra.Johnson.GyroelongatedPentagonalPyramid.Definition
import Modules.Check.Leaf.FullDim

set_option linter.style.longLine false

/-!
# The fixture `johnson/gyroelongated-pentagonal-pyramid` is full-dimensional

The points of `Johnson.GyroelongatedPentagonalPyramid.polyhedron` times `4` as exact values in `ZSqrt 5`,
exported by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`,
checked by the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`),
and scaled back (`eq_smul`, `Polyhedron.FullDim.smul`), so is
`Johnson.GyroelongatedPentagonalPyramid.polyhedron`.
-/

namespace Nieuwland.Polyhedra.JohnsonGyroelongatedPentagonalPyramidDim

open Check

/-- The points of `Johnson.GyroelongatedPentagonalPyramid.polyhedron` times `4`. -/
def points : List (V3 (ZSqrt 5)) := [
    ⟨⟨2, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩⟩,
    ⟨⟨2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩⟩,
    ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩⟩,
    ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩⟩,
    ⟨⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩⟩,
    ⟨⟨1, 1⟩, ⟨-2, 0⟩, ⟨0, 0⟩⟩,
    ⟨⟨-1, -1⟩, ⟨2, 0⟩, ⟨0, 0⟩⟩,
    ⟨⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩⟩,
    ⟨⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩⟩,
    ⟨⟨0, 0⟩, ⟨1, 1⟩, ⟨-2, 0⟩⟩,
    ⟨⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 4 : ℝ) • Exact.reV (⟨⟨2, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩⟩ : V3 (ZSqrt 5)) = ![1/2, 0, 1/4
    + 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt1 : (1 / 4 : ℝ) • Exact.reV (⟨⟨2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩⟩ : V3 (ZSqrt 5)) = ![1/2, 0,
    -1/4 - 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt2 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩⟩ : V3 (ZSqrt 5)) = ![-1/2, 0,
    1/4 + 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt3 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩⟩ : V3 (ZSqrt 5)) = ![-1/2, 0,
    -1/4 - 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt4 : (1 / 4 : ℝ) • Exact.reV (⟨⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![1/4 + 1/4 *
    √5, 1/2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt5 : (1 / 4 : ℝ) • Exact.reV (⟨⟨1, 1⟩, ⟨-2, 0⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![1/4 + 1/4 *
    √5, -1/2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt6 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-1, -1⟩, ⟨2, 0⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![-1/4 - 1/4
    * √5, 1/2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt7 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![-1/4 -
    1/4 * √5, -1/2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt8 : (1 / 4 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩⟩ : V3 (ZSqrt 5)) = ![0, 1/4 + 1/4
    * √5, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt9 : (1 / 4 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨1, 1⟩, ⟨-2, 0⟩⟩ : V3 (ZSqrt 5)) = ![0, 1/4 +
    1/4 * √5, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt10 : (1 / 4 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩⟩ : V3 (ZSqrt 5)) = ![0, -1/4
    - 1/4 * √5, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem eq_smul : Johnson.GyroelongatedPentagonalPyramid.polyhedron = (Polyhedron.ofPoints points).smul (1 / 4) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10]

end Nieuwland.Polyhedra.JohnsonGyroelongatedPentagonalPyramidDim

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/gyroelongated-pentagonal-pyramid` is full-dimensional.** -/
theorem johnsonGyroelongatedPentagonalPyramid_fullDim : Johnson.GyroelongatedPentagonalPyramid.polyhedron.FullDim := by
  rw [JohnsonGyroelongatedPentagonalPyramidDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk JohnsonGyroelongatedPentagonalPyramidDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
