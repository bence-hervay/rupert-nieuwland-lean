import Polyhedra.Other.RectifiedRhombicTriacontahedron.Definition
import Modules.Check.Leaf.FullDim

set_option linter.style.longLine false

/-!
# The fixture `other/rectified-rhombic-triacontahedron` is full-dimensional

The points of `Other.RectifiedRhombicTriacontahedron.polyhedron` times `16` as exact values in `ZSqrt 5`,
exported by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`,
checked by the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`),
and scaled back (`eq_smul`, `Polyhedron.FullDim.smul`), so is
`Other.RectifiedRhombicTriacontahedron.polyhedron`.
-/

namespace Nieuwland.Polyhedra.OtherRectifiedRhombicTriacontahedronDim

open Check

/-- The points of `Other.RectifiedRhombicTriacontahedron.polyhedron` times `16`. -/
def points : List (V3 (ZSqrt 5)) := [
    ⟨⟨5, 1⟩, ⟨0, 2⟩, ⟨10, 6⟩⟩,
    ⟨⟨5, 1⟩, ⟨0, -2⟩, ⟨10, 6⟩⟩,
    ⟨⟨10, 4⟩, ⟨0, 0⟩, ⟨5, 5⟩⟩,
    ⟨⟨10, 2⟩, ⟨5, 1⟩, ⟨10, 4⟩⟩,
    ⟨⟨10, 2⟩, ⟨-5, -1⟩, ⟨10, 4⟩⟩,
    ⟨⟨5, 1⟩, ⟨0, 2⟩, ⟨-10, -6⟩⟩,
    ⟨⟨5, 1⟩, ⟨0, -2⟩, ⟨-10, -6⟩⟩,
    ⟨⟨10, 4⟩, ⟨0, 0⟩, ⟨-5, -5⟩⟩,
    ⟨⟨10, 2⟩, ⟨5, 1⟩, ⟨-10, -4⟩⟩,
    ⟨⟨10, 2⟩, ⟨-5, -1⟩, ⟨-10, -4⟩⟩,
    ⟨⟨-5, -1⟩, ⟨0, 2⟩, ⟨10, 6⟩⟩,
    ⟨⟨-5, -1⟩, ⟨0, -2⟩, ⟨10, 6⟩⟩,
    ⟨⟨-10, -4⟩, ⟨0, 0⟩, ⟨5, 5⟩⟩,
    ⟨⟨-10, -2⟩, ⟨5, 1⟩, ⟨10, 4⟩⟩,
    ⟨⟨-10, -2⟩, ⟨-5, -1⟩, ⟨10, 4⟩⟩,
    ⟨⟨-5, -1⟩, ⟨0, 2⟩, ⟨-10, -6⟩⟩,
    ⟨⟨-5, -1⟩, ⟨0, -2⟩, ⟨-10, -6⟩⟩,
    ⟨⟨-10, -4⟩, ⟨0, 0⟩, ⟨-5, -5⟩⟩,
    ⟨⟨-10, -2⟩, ⟨5, 1⟩, ⟨-10, -4⟩⟩,
    ⟨⟨-10, -2⟩, ⟨-5, -1⟩, ⟨-10, -4⟩⟩,
    ⟨⟨10, 6⟩, ⟨5, 1⟩, ⟨0, 2⟩⟩,
    ⟨⟨10, 6⟩, ⟨5, 1⟩, ⟨0, -2⟩⟩,
    ⟨⟨5, 5⟩, ⟨10, 4⟩, ⟨0, 0⟩⟩,
    ⟨⟨10, 4⟩, ⟨10, 2⟩, ⟨5, 1⟩⟩,
    ⟨⟨10, 4⟩, ⟨10, 2⟩, ⟨-5, -1⟩⟩,
    ⟨⟨10, 6⟩, ⟨-5, -1⟩, ⟨0, 2⟩⟩,
    ⟨⟨10, 6⟩, ⟨-5, -1⟩, ⟨0, -2⟩⟩,
    ⟨⟨5, 5⟩, ⟨-10, -4⟩, ⟨0, 0⟩⟩,
    ⟨⟨10, 4⟩, ⟨-10, -2⟩, ⟨5, 1⟩⟩,
    ⟨⟨10, 4⟩, ⟨-10, -2⟩, ⟨-5, -1⟩⟩,
    ⟨⟨-10, -6⟩, ⟨5, 1⟩, ⟨0, 2⟩⟩,
    ⟨⟨-10, -6⟩, ⟨5, 1⟩, ⟨0, -2⟩⟩,
    ⟨⟨-5, -5⟩, ⟨10, 4⟩, ⟨0, 0⟩⟩,
    ⟨⟨-10, -4⟩, ⟨10, 2⟩, ⟨5, 1⟩⟩,
    ⟨⟨-10, -4⟩, ⟨10, 2⟩, ⟨-5, -1⟩⟩,
    ⟨⟨-10, -6⟩, ⟨-5, -1⟩, ⟨0, 2⟩⟩,
    ⟨⟨-10, -6⟩, ⟨-5, -1⟩, ⟨0, -2⟩⟩,
    ⟨⟨-5, -5⟩, ⟨-10, -4⟩, ⟨0, 0⟩⟩,
    ⟨⟨-10, -4⟩, ⟨-10, -2⟩, ⟨5, 1⟩⟩,
    ⟨⟨-10, -4⟩, ⟨-10, -2⟩, ⟨-5, -1⟩⟩,
    ⟨⟨0, 0⟩, ⟨5, 5⟩, ⟨10, 4⟩⟩,
    ⟨⟨0, 2⟩, ⟨10, 6⟩, ⟨5, 1⟩⟩,
    ⟨⟨0, -2⟩, ⟨10, 6⟩, ⟨5, 1⟩⟩,
    ⟨⟨5, 1⟩, ⟨10, 4⟩, ⟨10, 2⟩⟩,
    ⟨⟨-5, -1⟩, ⟨10, 4⟩, ⟨10, 2⟩⟩,
    ⟨⟨0, 0⟩, ⟨5, 5⟩, ⟨-10, -4⟩⟩,
    ⟨⟨0, 2⟩, ⟨10, 6⟩, ⟨-5, -1⟩⟩,
    ⟨⟨0, -2⟩, ⟨10, 6⟩, ⟨-5, -1⟩⟩,
    ⟨⟨5, 1⟩, ⟨10, 4⟩, ⟨-10, -2⟩⟩,
    ⟨⟨-5, -1⟩, ⟨10, 4⟩, ⟨-10, -2⟩⟩,
    ⟨⟨0, 0⟩, ⟨-5, -5⟩, ⟨10, 4⟩⟩,
    ⟨⟨0, 2⟩, ⟨-10, -6⟩, ⟨5, 1⟩⟩,
    ⟨⟨0, -2⟩, ⟨-10, -6⟩, ⟨5, 1⟩⟩,
    ⟨⟨5, 1⟩, ⟨-10, -4⟩, ⟨10, 2⟩⟩,
    ⟨⟨-5, -1⟩, ⟨-10, -4⟩, ⟨10, 2⟩⟩,
    ⟨⟨0, 0⟩, ⟨-5, -5⟩, ⟨-10, -4⟩⟩,
    ⟨⟨0, 2⟩, ⟨-10, -6⟩, ⟨-5, -1⟩⟩,
    ⟨⟨0, -2⟩, ⟨-10, -6⟩, ⟨-5, -1⟩⟩,
    ⟨⟨5, 1⟩, ⟨-10, -4⟩, ⟨-10, -2⟩⟩,
    ⟨⟨-5, -1⟩, ⟨-10, -4⟩, ⟨-10, -2⟩⟩]

theorem span_ok : spanOk points 0 1 2 5 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 16 : ℝ) • Exact.reV (⟨⟨5, 1⟩, ⟨0, 2⟩, ⟨10, 6⟩⟩ : V3 (ZSqrt 5)) = ![5/16 +
    1/16 * √5, 1/8 * √5, 5/8 + 3/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt1 : (1 / 16 : ℝ) • Exact.reV (⟨⟨5, 1⟩, ⟨0, -2⟩, ⟨10, 6⟩⟩ : V3 (ZSqrt 5)) = ![5/16 +
    1/16 * √5, -(1/8 * √5), 5/8 + 3/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt2 : (1 / 16 : ℝ) • Exact.reV (⟨⟨10, 4⟩, ⟨0, 0⟩, ⟨5, 5⟩⟩ : V3 (ZSqrt 5)) = ![5/8 + 1/4
    * √5, 0, 5/16 + 5/16 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt3 : (1 / 16 : ℝ) • Exact.reV (⟨⟨10, 2⟩, ⟨5, 1⟩, ⟨10, 4⟩⟩ : V3 (ZSqrt 5)) = ![5/8 + 1/8
    * √5, 5/16 + 1/16 * √5, 5/8 + 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt4 : (1 / 16 : ℝ) • Exact.reV (⟨⟨10, 2⟩, ⟨-5, -1⟩, ⟨10, 4⟩⟩ : V3 (ZSqrt 5)) = ![5/8 +
    1/8 * √5, -5/16 - 1/16 * √5, 5/8 + 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt5 : (1 / 16 : ℝ) • Exact.reV (⟨⟨5, 1⟩, ⟨0, 2⟩, ⟨-10, -6⟩⟩ : V3 (ZSqrt 5)) = ![5/16 +
    1/16 * √5, 1/8 * √5, -5/8 - 3/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt6 : (1 / 16 : ℝ) • Exact.reV (⟨⟨5, 1⟩, ⟨0, -2⟩, ⟨-10, -6⟩⟩ : V3 (ZSqrt 5)) = ![5/16 +
    1/16 * √5, -(1/8 * √5), -5/8 - 3/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt7 : (1 / 16 : ℝ) • Exact.reV (⟨⟨10, 4⟩, ⟨0, 0⟩, ⟨-5, -5⟩⟩ : V3 (ZSqrt 5)) = ![5/8 +
    1/4 * √5, 0, -5/16 - 5/16 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt8 : (1 / 16 : ℝ) • Exact.reV (⟨⟨10, 2⟩, ⟨5, 1⟩, ⟨-10, -4⟩⟩ : V3 (ZSqrt 5)) = ![5/8 +
    1/8 * √5, 5/16 + 1/16 * √5, -5/8 - 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt9 : (1 / 16 : ℝ) • Exact.reV (⟨⟨10, 2⟩, ⟨-5, -1⟩, ⟨-10, -4⟩⟩ : V3 (ZSqrt 5)) = ![5/8 +
    1/8 * √5, -5/16 - 1/16 * √5, -5/8 - 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt10 : (1 / 16 : ℝ) • Exact.reV (⟨⟨-5, -1⟩, ⟨0, 2⟩, ⟨10, 6⟩⟩ : V3 (ZSqrt 5)) = ![-5/16 -
    1/16 * √5, 1/8 * √5, 5/8 + 3/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt11 : (1 / 16 : ℝ) • Exact.reV (⟨⟨-5, -1⟩, ⟨0, -2⟩, ⟨10, 6⟩⟩ : V3 (ZSqrt 5)) = ![-5/16
    - 1/16 * √5, -(1/8 * √5), 5/8 + 3/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt12 : (1 / 16 : ℝ) • Exact.reV (⟨⟨-10, -4⟩, ⟨0, 0⟩, ⟨5, 5⟩⟩ : V3 (ZSqrt 5)) = ![-5/8 -
    1/4 * √5, 0, 5/16 + 5/16 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt13 : (1 / 16 : ℝ) • Exact.reV (⟨⟨-10, -2⟩, ⟨5, 1⟩, ⟨10, 4⟩⟩ : V3 (ZSqrt 5)) = ![-5/8 -
    1/8 * √5, 5/16 + 1/16 * √5, 5/8 + 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt14 : (1 / 16 : ℝ) • Exact.reV (⟨⟨-10, -2⟩, ⟨-5, -1⟩, ⟨10, 4⟩⟩ : V3 (ZSqrt 5)) = ![-5/8
    - 1/8 * √5, -5/16 - 1/16 * √5, 5/8 + 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt15 : (1 / 16 : ℝ) • Exact.reV (⟨⟨-5, -1⟩, ⟨0, 2⟩, ⟨-10, -6⟩⟩ : V3 (ZSqrt 5)) = ![-5/16
    - 1/16 * √5, 1/8 * √5, -5/8 - 3/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt16 : (1 / 16 : ℝ) • Exact.reV (⟨⟨-5, -1⟩, ⟨0, -2⟩, ⟨-10, -6⟩⟩ : V3 (ZSqrt 5)) =
    ![-5/16 - 1/16 * √5, -(1/8 * √5), -5/8 - 3/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt17 : (1 / 16 : ℝ) • Exact.reV (⟨⟨-10, -4⟩, ⟨0, 0⟩, ⟨-5, -5⟩⟩ : V3 (ZSqrt 5)) = ![-5/8
    - 1/4 * √5, 0, -5/16 - 5/16 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt18 : (1 / 16 : ℝ) • Exact.reV (⟨⟨-10, -2⟩, ⟨5, 1⟩, ⟨-10, -4⟩⟩ : V3 (ZSqrt 5)) = ![-5/8
    - 1/8 * √5, 5/16 + 1/16 * √5, -5/8 - 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt19 : (1 / 16 : ℝ) • Exact.reV (⟨⟨-10, -2⟩, ⟨-5, -1⟩, ⟨-10, -4⟩⟩ : V3 (ZSqrt 5)) =
    ![-5/8 - 1/8 * √5, -5/16 - 1/16 * √5, -5/8 - 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt20 : (1 / 16 : ℝ) • Exact.reV (⟨⟨10, 6⟩, ⟨5, 1⟩, ⟨0, 2⟩⟩ : V3 (ZSqrt 5)) = ![5/8 + 3/8
    * √5, 5/16 + 1/16 * √5, 1/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt21 : (1 / 16 : ℝ) • Exact.reV (⟨⟨10, 6⟩, ⟨5, 1⟩, ⟨0, -2⟩⟩ : V3 (ZSqrt 5)) = ![5/8 +
    3/8 * √5, 5/16 + 1/16 * √5, -(1/8 * √5)] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt22 : (1 / 16 : ℝ) • Exact.reV (⟨⟨5, 5⟩, ⟨10, 4⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![5/16 +
    5/16 * √5, 5/8 + 1/4 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt23 : (1 / 16 : ℝ) • Exact.reV (⟨⟨10, 4⟩, ⟨10, 2⟩, ⟨5, 1⟩⟩ : V3 (ZSqrt 5)) = ![5/8 +
    1/4 * √5, 5/8 + 1/8 * √5, 5/16 + 1/16 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt24 : (1 / 16 : ℝ) • Exact.reV (⟨⟨10, 4⟩, ⟨10, 2⟩, ⟨-5, -1⟩⟩ : V3 (ZSqrt 5)) = ![5/8 +
    1/4 * √5, 5/8 + 1/8 * √5, -5/16 - 1/16 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt25 : (1 / 16 : ℝ) • Exact.reV (⟨⟨10, 6⟩, ⟨-5, -1⟩, ⟨0, 2⟩⟩ : V3 (ZSqrt 5)) = ![5/8 +
    3/8 * √5, -5/16 - 1/16 * √5, 1/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt26 : (1 / 16 : ℝ) • Exact.reV (⟨⟨10, 6⟩, ⟨-5, -1⟩, ⟨0, -2⟩⟩ : V3 (ZSqrt 5)) = ![5/8 +
    3/8 * √5, -5/16 - 1/16 * √5, -(1/8 * √5)] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt27 : (1 / 16 : ℝ) • Exact.reV (⟨⟨5, 5⟩, ⟨-10, -4⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![5/16 +
    5/16 * √5, -5/8 - 1/4 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt28 : (1 / 16 : ℝ) • Exact.reV (⟨⟨10, 4⟩, ⟨-10, -2⟩, ⟨5, 1⟩⟩ : V3 (ZSqrt 5)) = ![5/8 +
    1/4 * √5, -5/8 - 1/8 * √5, 5/16 + 1/16 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt29 : (1 / 16 : ℝ) • Exact.reV (⟨⟨10, 4⟩, ⟨-10, -2⟩, ⟨-5, -1⟩⟩ : V3 (ZSqrt 5)) = ![5/8
    + 1/4 * √5, -5/8 - 1/8 * √5, -5/16 - 1/16 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt30 : (1 / 16 : ℝ) • Exact.reV (⟨⟨-10, -6⟩, ⟨5, 1⟩, ⟨0, 2⟩⟩ : V3 (ZSqrt 5)) = ![-5/8 -
    3/8 * √5, 5/16 + 1/16 * √5, 1/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt31 : (1 / 16 : ℝ) • Exact.reV (⟨⟨-10, -6⟩, ⟨5, 1⟩, ⟨0, -2⟩⟩ : V3 (ZSqrt 5)) = ![-5/8 -
    3/8 * √5, 5/16 + 1/16 * √5, -(1/8 * √5)] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt32 : (1 / 16 : ℝ) • Exact.reV (⟨⟨-5, -5⟩, ⟨10, 4⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![-5/16 -
    5/16 * √5, 5/8 + 1/4 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt33 : (1 / 16 : ℝ) • Exact.reV (⟨⟨-10, -4⟩, ⟨10, 2⟩, ⟨5, 1⟩⟩ : V3 (ZSqrt 5)) = ![-5/8 -
    1/4 * √5, 5/8 + 1/8 * √5, 5/16 + 1/16 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt34 : (1 / 16 : ℝ) • Exact.reV (⟨⟨-10, -4⟩, ⟨10, 2⟩, ⟨-5, -1⟩⟩ : V3 (ZSqrt 5)) = ![-5/8
    - 1/4 * √5, 5/8 + 1/8 * √5, -5/16 - 1/16 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt35 : (1 / 16 : ℝ) • Exact.reV (⟨⟨-10, -6⟩, ⟨-5, -1⟩, ⟨0, 2⟩⟩ : V3 (ZSqrt 5)) = ![-5/8
    - 3/8 * √5, -5/16 - 1/16 * √5, 1/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt36 : (1 / 16 : ℝ) • Exact.reV (⟨⟨-10, -6⟩, ⟨-5, -1⟩, ⟨0, -2⟩⟩ : V3 (ZSqrt 5)) = ![-5/8
    - 3/8 * √5, -5/16 - 1/16 * √5, -(1/8 * √5)] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt37 : (1 / 16 : ℝ) • Exact.reV (⟨⟨-5, -5⟩, ⟨-10, -4⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![-5/16
    - 5/16 * √5, -5/8 - 1/4 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt38 : (1 / 16 : ℝ) • Exact.reV (⟨⟨-10, -4⟩, ⟨-10, -2⟩, ⟨5, 1⟩⟩ : V3 (ZSqrt 5)) = ![-5/8
    - 1/4 * √5, -5/8 - 1/8 * √5, 5/16 + 1/16 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt39 : (1 / 16 : ℝ) • Exact.reV (⟨⟨-10, -4⟩, ⟨-10, -2⟩, ⟨-5, -1⟩⟩ : V3 (ZSqrt 5)) =
    ![-5/8 - 1/4 * √5, -5/8 - 1/8 * √5, -5/16 - 1/16 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt40 : (1 / 16 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨5, 5⟩, ⟨10, 4⟩⟩ : V3 (ZSqrt 5)) = ![0, 5/16 +
    5/16 * √5, 5/8 + 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt41 : (1 / 16 : ℝ) • Exact.reV (⟨⟨0, 2⟩, ⟨10, 6⟩, ⟨5, 1⟩⟩ : V3 (ZSqrt 5)) = ![1/8 * √5,
    5/8 + 3/8 * √5, 5/16 + 1/16 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt42 : (1 / 16 : ℝ) • Exact.reV (⟨⟨0, -2⟩, ⟨10, 6⟩, ⟨5, 1⟩⟩ : V3 (ZSqrt 5)) = ![-(1/8 *
    √5), 5/8 + 3/8 * √5, 5/16 + 1/16 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt43 : (1 / 16 : ℝ) • Exact.reV (⟨⟨5, 1⟩, ⟨10, 4⟩, ⟨10, 2⟩⟩ : V3 (ZSqrt 5)) = ![5/16 +
    1/16 * √5, 5/8 + 1/4 * √5, 5/8 + 1/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt44 : (1 / 16 : ℝ) • Exact.reV (⟨⟨-5, -1⟩, ⟨10, 4⟩, ⟨10, 2⟩⟩ : V3 (ZSqrt 5)) = ![-5/16
    - 1/16 * √5, 5/8 + 1/4 * √5, 5/8 + 1/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt45 : (1 / 16 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨5, 5⟩, ⟨-10, -4⟩⟩ : V3 (ZSqrt 5)) = ![0, 5/16
    + 5/16 * √5, -5/8 - 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt46 : (1 / 16 : ℝ) • Exact.reV (⟨⟨0, 2⟩, ⟨10, 6⟩, ⟨-5, -1⟩⟩ : V3 (ZSqrt 5)) = ![1/8 *
    √5, 5/8 + 3/8 * √5, -5/16 - 1/16 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt47 : (1 / 16 : ℝ) • Exact.reV (⟨⟨0, -2⟩, ⟨10, 6⟩, ⟨-5, -1⟩⟩ : V3 (ZSqrt 5)) = ![-(1/8
    * √5), 5/8 + 3/8 * √5, -5/16 - 1/16 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt48 : (1 / 16 : ℝ) • Exact.reV (⟨⟨5, 1⟩, ⟨10, 4⟩, ⟨-10, -2⟩⟩ : V3 (ZSqrt 5)) = ![5/16 +
    1/16 * √5, 5/8 + 1/4 * √5, -5/8 - 1/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt49 : (1 / 16 : ℝ) • Exact.reV (⟨⟨-5, -1⟩, ⟨10, 4⟩, ⟨-10, -2⟩⟩ : V3 (ZSqrt 5)) =
    ![-5/16 - 1/16 * √5, 5/8 + 1/4 * √5, -5/8 - 1/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt50 : (1 / 16 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨-5, -5⟩, ⟨10, 4⟩⟩ : V3 (ZSqrt 5)) = ![0,
    -5/16 - 5/16 * √5, 5/8 + 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt51 : (1 / 16 : ℝ) • Exact.reV (⟨⟨0, 2⟩, ⟨-10, -6⟩, ⟨5, 1⟩⟩ : V3 (ZSqrt 5)) = ![1/8 *
    √5, -5/8 - 3/8 * √5, 5/16 + 1/16 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt52 : (1 / 16 : ℝ) • Exact.reV (⟨⟨0, -2⟩, ⟨-10, -6⟩, ⟨5, 1⟩⟩ : V3 (ZSqrt 5)) = ![-(1/8
    * √5), -5/8 - 3/8 * √5, 5/16 + 1/16 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt53 : (1 / 16 : ℝ) • Exact.reV (⟨⟨5, 1⟩, ⟨-10, -4⟩, ⟨10, 2⟩⟩ : V3 (ZSqrt 5)) = ![5/16 +
    1/16 * √5, -5/8 - 1/4 * √5, 5/8 + 1/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt54 : (1 / 16 : ℝ) • Exact.reV (⟨⟨-5, -1⟩, ⟨-10, -4⟩, ⟨10, 2⟩⟩ : V3 (ZSqrt 5)) =
    ![-5/16 - 1/16 * √5, -5/8 - 1/4 * √5, 5/8 + 1/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt55 : (1 / 16 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨-5, -5⟩, ⟨-10, -4⟩⟩ : V3 (ZSqrt 5)) = ![0,
    -5/16 - 5/16 * √5, -5/8 - 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt56 : (1 / 16 : ℝ) • Exact.reV (⟨⟨0, 2⟩, ⟨-10, -6⟩, ⟨-5, -1⟩⟩ : V3 (ZSqrt 5)) = ![1/8 *
    √5, -5/8 - 3/8 * √5, -5/16 - 1/16 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt57 : (1 / 16 : ℝ) • Exact.reV (⟨⟨0, -2⟩, ⟨-10, -6⟩, ⟨-5, -1⟩⟩ : V3 (ZSqrt 5)) =
    ![-(1/8 * √5), -5/8 - 3/8 * √5, -5/16 - 1/16 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt58 : (1 / 16 : ℝ) • Exact.reV (⟨⟨5, 1⟩, ⟨-10, -4⟩, ⟨-10, -2⟩⟩ : V3 (ZSqrt 5)) = ![5/16
    + 1/16 * √5, -5/8 - 1/4 * √5, -5/8 - 1/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt59 : (1 / 16 : ℝ) • Exact.reV (⟨⟨-5, -1⟩, ⟨-10, -4⟩, ⟨-10, -2⟩⟩ : V3 (ZSqrt 5)) =
    ![-5/16 - 1/16 * √5, -5/8 - 1/4 * √5, -5/8 - 1/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem eq_smul : Other.RectifiedRhombicTriacontahedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 16) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17, pt18, pt19, pt20, pt21, pt22, pt23, pt24,
    pt25, pt26, pt27, pt28, pt29, pt30, pt31, pt32, pt33, pt34, pt35, pt36, pt37, pt38, pt39, pt40,
    pt41, pt42, pt43, pt44, pt45, pt46, pt47, pt48, pt49, pt50, pt51, pt52, pt53, pt54, pt55, pt56,
    pt57, pt58, pt59]

end Nieuwland.Polyhedra.OtherRectifiedRhombicTriacontahedronDim

namespace Nieuwland.Polyhedra

/-- **The fixture `other/rectified-rhombic-triacontahedron` is full-dimensional.** -/
theorem otherRectifiedRhombicTriacontahedron_fullDim : Other.RectifiedRhombicTriacontahedron.polyhedron.FullDim := by
  rw [OtherRectifiedRhombicTriacontahedronDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk OtherRectifiedRhombicTriacontahedronDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
