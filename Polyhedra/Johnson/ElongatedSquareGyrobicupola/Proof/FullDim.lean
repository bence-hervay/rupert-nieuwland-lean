import Polyhedra.Johnson.ElongatedSquareGyrobicupola.Definition
import Modules.Check.Leaf.FullDim

set_option linter.style.longLine false

/-!
# The fixture `johnson/elongated-square-gyrobicupola` is full-dimensional

The points of `Johnson.ElongatedSquareGyrobicupola.polyhedron` times `2` as exact values in `ZSqrt 2`, exported
by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Johnson.ElongatedSquareGyrobicupola.polyhedron`.
-/

namespace Nieuwland.Polyhedra.JohnsonElongatedSquareGyrobicupolaDim

open Check

/-- The points of `Johnson.ElongatedSquareGyrobicupola.polyhedron` times `2`. -/
def points : List (V3 (ZSqrt 2)) := [
    ⟨⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩⟩,
    ⟨⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩⟩,
    ⟨⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩⟩,
    ⟨⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩⟩,
    ⟨⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩⟩,
    ⟨⟨1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩⟩,
    ⟨⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩⟩,
    ⟨⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩⟩,
    ⟨⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩⟩,
    ⟨⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩⟩,
    ⟨⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 0⟩⟩,
    ⟨⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩⟩,
    ⟨⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩⟩,
    ⟨⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, 0⟩⟩,
    ⟨⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩⟩,
    ⟨⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩⟩,
    ⟨⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩⟩,
    ⟨⟨1, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩⟩,
    ⟨⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩⟩,
    ⟨⟨1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩⟩,
    ⟨⟨-1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩⟩,
    ⟨⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩⟩,
    ⟨⟨-1, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩⟩,
    ⟨⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 2 : ℝ) • Exact.reV (⟨⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩⟩ : V3 (ZSqrt 2)) = ![1/2 * √2, 0,
    1/2 + 1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt1 : (1 / 2 : ℝ) • Exact.reV (⟨⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩⟩ : V3 (ZSqrt 2)) = ![-(1/2 *
    √2), 0, 1/2 + 1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt2 : (1 / 2 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩⟩ : V3 (ZSqrt 2)) = ![0, 1/2 * √2,
    1/2 + 1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt3 : (1 / 2 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩⟩ : V3 (ZSqrt 2)) = ![0, -(1/2 *
    √2), 1/2 + 1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt4 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩⟩ : V3 (ZSqrt 2)) = ![1/2, 1/2,
    -1/2 - 1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt5 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩⟩ : V3 (ZSqrt 2)) = ![1/2,
    -1/2, -1/2 - 1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt6 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩⟩ : V3 (ZSqrt 2)) = ![-1/2,
    1/2, -1/2 - 1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt7 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩⟩ : V3 (ZSqrt 2)) = ![-1/2,
    -1/2, -1/2 - 1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt8 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩⟩ : V3 (ZSqrt 2)) = ![1/2 + 1/2 *
    √2, 1/2, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt9 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩⟩ : V3 (ZSqrt 2)) = ![1/2 + 1/2 *
    √2, 1/2, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt10 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 0⟩⟩ : V3 (ZSqrt 2)) = ![1/2 + 1/2
    * √2, -1/2, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt11 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩⟩ : V3 (ZSqrt 2)) = ![1/2 + 1/2
    * √2, -1/2, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt12 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩⟩ : V3 (ZSqrt 2)) = ![-1/2 -
    1/2 * √2, 1/2, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt13 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, 0⟩⟩ : V3 (ZSqrt 2)) = ![-1/2 -
    1/2 * √2, 1/2, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt14 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩⟩ : V3 (ZSqrt 2)) = ![-1/2 -
    1/2 * √2, -1/2, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt15 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩⟩ : V3 (ZSqrt 2)) = ![-1/2 -
    1/2 * √2, -1/2, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt16 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩⟩ : V3 (ZSqrt 2)) = ![1/2, 1/2 +
    1/2 * √2, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt17 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩⟩ : V3 (ZSqrt 2)) = ![1/2, 1/2 +
    1/2 * √2, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt18 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩⟩ : V3 (ZSqrt 2)) = ![1/2, -1/2
    - 1/2 * √2, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt19 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩⟩ : V3 (ZSqrt 2)) = ![1/2,
    -1/2 - 1/2 * √2, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt20 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩⟩ : V3 (ZSqrt 2)) = ![-1/2, 1/2
    + 1/2 * √2, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt21 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩⟩ : V3 (ZSqrt 2)) = ![-1/2, 1/2
    + 1/2 * √2, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt22 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩⟩ : V3 (ZSqrt 2)) = ![-1/2,
    -1/2 - 1/2 * √2, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt23 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩⟩ : V3 (ZSqrt 2)) = ![-1/2,
    -1/2 - 1/2 * √2, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem eq_smul : Johnson.ElongatedSquareGyrobicupola.polyhedron = (Polyhedron.ofPoints points).smul (1 / 2) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17, pt18, pt19, pt20, pt21, pt22, pt23]

end Nieuwland.Polyhedra.JohnsonElongatedSquareGyrobicupolaDim

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/elongated-square-gyrobicupola` is full-dimensional.** -/
theorem johnsonElongatedSquareGyrobicupola_fullDim : Johnson.ElongatedSquareGyrobicupola.polyhedron.FullDim := by
  rw [JohnsonElongatedSquareGyrobicupolaDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk JohnsonElongatedSquareGyrobicupolaDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
