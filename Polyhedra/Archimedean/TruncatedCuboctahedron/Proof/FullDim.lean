import Polyhedra.Archimedean.TruncatedCuboctahedron.Definition
import Modules.Check.Leaf.FullDim

set_option linter.style.longLine false

/-!
# The fixture `archimedean/truncated-cuboctahedron` is full-dimensional

The points of `Archimedean.TruncatedCuboctahedron.polyhedron` times `2` as exact values in `ZSqrt 2`, exported
by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Archimedean.TruncatedCuboctahedron.polyhedron`.
-/

namespace Nieuwland.Polyhedra.ArchimedeanTruncatedCuboctahedronDim

open Check

/-- The points of `Archimedean.TruncatedCuboctahedron.polyhedron` times `2`. -/
def points : List (V3 (ZSqrt 2)) := [
    ⟨⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩⟩,
    ⟨⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, -2⟩⟩,
    ⟨⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩⟩,
    ⟨⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩⟩,
    ⟨⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 2⟩⟩,
    ⟨⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩⟩,
    ⟨⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 2⟩⟩,
    ⟨⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩⟩,
    ⟨⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 0⟩⟩,
    ⟨⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 0⟩⟩,
    ⟨⟨1, 2⟩, ⟨-1, -1⟩, ⟨1, 0⟩⟩,
    ⟨⟨1, 2⟩, ⟨-1, -1⟩, ⟨-1, 0⟩⟩,
    ⟨⟨-1, -2⟩, ⟨1, 1⟩, ⟨1, 0⟩⟩,
    ⟨⟨-1, -2⟩, ⟨1, 1⟩, ⟨-1, 0⟩⟩,
    ⟨⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩⟩,
    ⟨⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, 0⟩⟩,
    ⟨⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩⟩,
    ⟨⟨1, 0⟩, ⟨1, 2⟩, ⟨-1, -1⟩⟩,
    ⟨⟨1, 0⟩, ⟨-1, -2⟩, ⟨1, 1⟩⟩,
    ⟨⟨1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩⟩,
    ⟨⟨-1, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩⟩,
    ⟨⟨-1, 0⟩, ⟨1, 2⟩, ⟨-1, -1⟩⟩,
    ⟨⟨-1, 0⟩, ⟨-1, -2⟩, ⟨1, 1⟩⟩,
    ⟨⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩⟩,
    ⟨⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 2⟩⟩,
    ⟨⟨1, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩⟩,
    ⟨⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩⟩,
    ⟨⟨1, 0⟩, ⟨-1, -1⟩, ⟨-1, -2⟩⟩,
    ⟨⟨-1, 0⟩, ⟨1, 1⟩, ⟨1, 2⟩⟩,
    ⟨⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩⟩,
    ⟨⟨-1, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩⟩,
    ⟨⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -2⟩⟩,
    ⟨⟨1, 2⟩, ⟨1, 0⟩, ⟨1, 1⟩⟩,
    ⟨⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, -1⟩⟩,
    ⟨⟨1, 2⟩, ⟨-1, 0⟩, ⟨1, 1⟩⟩,
    ⟨⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, -1⟩⟩,
    ⟨⟨-1, -2⟩, ⟨1, 0⟩, ⟨1, 1⟩⟩,
    ⟨⟨-1, -2⟩, ⟨1, 0⟩, ⟨-1, -1⟩⟩,
    ⟨⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, 1⟩⟩,
    ⟨⟨-1, -2⟩, ⟨-1, 0⟩, ⟨-1, -1⟩⟩,
    ⟨⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩⟩,
    ⟨⟨1, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩⟩,
    ⟨⟨1, 1⟩, ⟨-1, -2⟩, ⟨1, 0⟩⟩,
    ⟨⟨1, 1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩⟩,
    ⟨⟨-1, -1⟩, ⟨1, 2⟩, ⟨1, 0⟩⟩,
    ⟨⟨-1, -1⟩, ⟨1, 2⟩, ⟨-1, 0⟩⟩,
    ⟨⟨-1, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩⟩,
    ⟨⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩⟩ : V3 (ZSqrt 2)) = ![1/2 + 1/2 *
    √2, 1/2, 1/2 + √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt1 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, -2⟩⟩ : V3 (ZSqrt 2)) = ![1/2 + 1/2
    * √2, 1/2, -1/2 - √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt2 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩⟩ : V3 (ZSqrt 2)) = ![1/2 + 1/2 *
    √2, -1/2, 1/2 + √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt3 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩⟩ : V3 (ZSqrt 2)) = ![1/2 + 1/2
    * √2, -1/2, -1/2 - √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt4 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 2⟩⟩ : V3 (ZSqrt 2)) = ![-1/2 - 1/2
    * √2, 1/2, 1/2 + √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt5 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩⟩ : V3 (ZSqrt 2)) = ![-1/2 -
    1/2 * √2, 1/2, -1/2 - √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt6 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 2⟩⟩ : V3 (ZSqrt 2)) = ![-1/2 -
    1/2 * √2, -1/2, 1/2 + √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt7 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩⟩ : V3 (ZSqrt 2)) = ![-1/2 -
    1/2 * √2, -1/2, -1/2 - √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt8 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 0⟩⟩ : V3 (ZSqrt 2)) = ![1/2 + √2,
    1/2 + 1/2 * √2, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt9 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 0⟩⟩ : V3 (ZSqrt 2)) = ![1/2 + √2,
    1/2 + 1/2 * √2, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt10 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 2⟩, ⟨-1, -1⟩, ⟨1, 0⟩⟩ : V3 (ZSqrt 2)) = ![1/2 + √2,
    -1/2 - 1/2 * √2, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt11 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 2⟩, ⟨-1, -1⟩, ⟨-1, 0⟩⟩ : V3 (ZSqrt 2)) = ![1/2 +
    √2, -1/2 - 1/2 * √2, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt12 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, -2⟩, ⟨1, 1⟩, ⟨1, 0⟩⟩ : V3 (ZSqrt 2)) = ![-1/2 -
    √2, 1/2 + 1/2 * √2, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt13 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, -2⟩, ⟨1, 1⟩, ⟨-1, 0⟩⟩ : V3 (ZSqrt 2)) = ![-1/2 -
    √2, 1/2 + 1/2 * √2, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt14 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩⟩ : V3 (ZSqrt 2)) = ![-1/2 -
    √2, -1/2 - 1/2 * √2, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt15 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, 0⟩⟩ : V3 (ZSqrt 2)) = ![-1/2 -
    √2, -1/2 - 1/2 * √2, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt16 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩⟩ : V3 (ZSqrt 2)) = ![1/2, 1/2 +
    √2, 1/2 + 1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt17 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 0⟩, ⟨1, 2⟩, ⟨-1, -1⟩⟩ : V3 (ZSqrt 2)) = ![1/2, 1/2
    + √2, -1/2 - 1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt18 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 0⟩, ⟨-1, -2⟩, ⟨1, 1⟩⟩ : V3 (ZSqrt 2)) = ![1/2, -1/2
    - √2, 1/2 + 1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt19 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩⟩ : V3 (ZSqrt 2)) = ![1/2,
    -1/2 - √2, -1/2 - 1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt20 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩⟩ : V3 (ZSqrt 2)) = ![-1/2, 1/2
    + √2, 1/2 + 1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt21 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, 0⟩, ⟨1, 2⟩, ⟨-1, -1⟩⟩ : V3 (ZSqrt 2)) = ![-1/2,
    1/2 + √2, -1/2 - 1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt22 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, 0⟩, ⟨-1, -2⟩, ⟨1, 1⟩⟩ : V3 (ZSqrt 2)) = ![-1/2,
    -1/2 - √2, 1/2 + 1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt23 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩⟩ : V3 (ZSqrt 2)) = ![-1/2,
    -1/2 - √2, -1/2 - 1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt24 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 2⟩⟩ : V3 (ZSqrt 2)) = ![1/2, 1/2 +
    1/2 * √2, 1/2 + √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt25 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩⟩ : V3 (ZSqrt 2)) = ![1/2, 1/2
    + 1/2 * √2, -1/2 - √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt26 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩⟩ : V3 (ZSqrt 2)) = ![1/2, -1/2
    - 1/2 * √2, 1/2 + √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt27 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 0⟩, ⟨-1, -1⟩, ⟨-1, -2⟩⟩ : V3 (ZSqrt 2)) = ![1/2,
    -1/2 - 1/2 * √2, -1/2 - √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt28 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, 0⟩, ⟨1, 1⟩, ⟨1, 2⟩⟩ : V3 (ZSqrt 2)) = ![-1/2, 1/2
    + 1/2 * √2, 1/2 + √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt29 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩⟩ : V3 (ZSqrt 2)) = ![-1/2,
    1/2 + 1/2 * √2, -1/2 - √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt30 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩⟩ : V3 (ZSqrt 2)) = ![-1/2,
    -1/2 - 1/2 * √2, 1/2 + √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt31 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -2⟩⟩ : V3 (ZSqrt 2)) = ![-1/2,
    -1/2 - 1/2 * √2, -1/2 - √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt32 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 2⟩, ⟨1, 0⟩, ⟨1, 1⟩⟩ : V3 (ZSqrt 2)) = ![1/2 + √2,
    1/2, 1/2 + 1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt33 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, -1⟩⟩ : V3 (ZSqrt 2)) = ![1/2 + √2,
    1/2, -1/2 - 1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt34 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 2⟩, ⟨-1, 0⟩, ⟨1, 1⟩⟩ : V3 (ZSqrt 2)) = ![1/2 + √2,
    -1/2, 1/2 + 1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt35 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, -1⟩⟩ : V3 (ZSqrt 2)) = ![1/2 +
    √2, -1/2, -1/2 - 1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt36 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, -2⟩, ⟨1, 0⟩, ⟨1, 1⟩⟩ : V3 (ZSqrt 2)) = ![-1/2 -
    √2, 1/2, 1/2 + 1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt37 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, -2⟩, ⟨1, 0⟩, ⟨-1, -1⟩⟩ : V3 (ZSqrt 2)) = ![-1/2 -
    √2, 1/2, -1/2 - 1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt38 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, 1⟩⟩ : V3 (ZSqrt 2)) = ![-1/2 -
    √2, -1/2, 1/2 + 1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt39 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, -2⟩, ⟨-1, 0⟩, ⟨-1, -1⟩⟩ : V3 (ZSqrt 2)) = ![-1/2 -
    √2, -1/2, -1/2 - 1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt40 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩⟩ : V3 (ZSqrt 2)) = ![1/2 + 1/2 *
    √2, 1/2 + √2, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt41 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩⟩ : V3 (ZSqrt 2)) = ![1/2 + 1/2
    * √2, 1/2 + √2, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt42 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 1⟩, ⟨-1, -2⟩, ⟨1, 0⟩⟩ : V3 (ZSqrt 2)) = ![1/2 + 1/2
    * √2, -1/2 - √2, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt43 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩⟩ : V3 (ZSqrt 2)) = ![1/2 +
    1/2 * √2, -1/2 - √2, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt44 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, -1⟩, ⟨1, 2⟩, ⟨1, 0⟩⟩ : V3 (ZSqrt 2)) = ![-1/2 -
    1/2 * √2, 1/2 + √2, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt45 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, -1⟩, ⟨1, 2⟩, ⟨-1, 0⟩⟩ : V3 (ZSqrt 2)) = ![-1/2 -
    1/2 * √2, 1/2 + √2, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt46 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩⟩ : V3 (ZSqrt 2)) = ![-1/2 -
    1/2 * √2, -1/2 - √2, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt47 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩⟩ : V3 (ZSqrt 2)) = ![-1/2 -
    1/2 * √2, -1/2 - √2, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem eq_smul : Archimedean.TruncatedCuboctahedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 2) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17, pt18, pt19, pt20, pt21, pt22, pt23, pt24,
    pt25, pt26, pt27, pt28, pt29, pt30, pt31, pt32, pt33, pt34, pt35, pt36, pt37, pt38, pt39, pt40,
    pt41, pt42, pt43, pt44, pt45, pt46, pt47]

end Nieuwland.Polyhedra.ArchimedeanTruncatedCuboctahedronDim

namespace Nieuwland.Polyhedra

/-- **The fixture `archimedean/truncated-cuboctahedron` is full-dimensional.** -/
theorem archimedeanTruncatedCuboctahedron_fullDim : Archimedean.TruncatedCuboctahedron.polyhedron.FullDim := by
  rw [ArchimedeanTruncatedCuboctahedronDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk ArchimedeanTruncatedCuboctahedronDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
