import Polyhedra.Catalan.DeltoidalHexecontahedron.Definition
import Modules.Check.Leaf.FullDim

set_option linter.style.longLine false

/-!
# The fixture `catalan/deltoidal-hexecontahedron` is full-dimensional

The points of `Catalan.DeltoidalHexecontahedron.polyhedron` times `132` as exact values in `ZSqrt 5`, exported
by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Catalan.DeltoidalHexecontahedron.polyhedron`.
-/

namespace Nieuwland.Polyhedra.CatalanDeltoidalHexecontahedronDim

open Check

/-- The points of `Catalan.DeltoidalHexecontahedron.polyhedron` times `132`. -/
def points : List (V3 (ZSqrt 5)) := [
    ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨-264, 132⟩⟩,
    ⟨⟨66, -22⟩, ⟨0, 0⟩, ⟨-22, 22⟩⟩,
    ⟨⟨0, 0⟩, ⟨78, -30⟩, ⟨42, -6⟩⟩,
    ⟨⟨231, -99⟩, ⟨-132, 66⟩, ⟨99, -33⟩⟩,
    ⟨⟨0, 0⟩, ⟨-264, 132⟩, ⟨0, 0⟩⟩,
    ⟨⟨0, 0⟩, ⟨-22, 22⟩, ⟨66, -22⟩⟩,
    ⟨⟨78, -30⟩, ⟨42, -6⟩, ⟨0, 0⟩⟩,
    ⟨⟨-132, 66⟩, ⟨99, -33⟩, ⟨231, -99⟩⟩,
    ⟨⟨-264, 132⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩,
    ⟨⟨-22, 22⟩, ⟨66, -22⟩, ⟨0, 0⟩⟩,
    ⟨⟨42, -6⟩, ⟨0, 0⟩, ⟨78, -30⟩⟩,
    ⟨⟨99, -33⟩, ⟨231, -99⟩, ⟨-132, 66⟩⟩,
    ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨264, -132⟩⟩,
    ⟨⟨66, -22⟩, ⟨0, 0⟩, ⟨22, -22⟩⟩,
    ⟨⟨0, 0⟩, ⟨78, -30⟩, ⟨-42, 6⟩⟩,
    ⟨⟨231, -99⟩, ⟨-132, 66⟩, ⟨-99, 33⟩⟩,
    ⟨⟨0, 0⟩, ⟨264, -132⟩, ⟨0, 0⟩⟩,
    ⟨⟨0, 0⟩, ⟨22, -22⟩, ⟨66, -22⟩⟩,
    ⟨⟨78, -30⟩, ⟨-42, 6⟩, ⟨0, 0⟩⟩,
    ⟨⟨-132, 66⟩, ⟨-99, 33⟩, ⟨231, -99⟩⟩,
    ⟨⟨264, -132⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩,
    ⟨⟨22, -22⟩, ⟨66, -22⟩, ⟨0, 0⟩⟩,
    ⟨⟨-42, 6⟩, ⟨0, 0⟩, ⟨78, -30⟩⟩,
    ⟨⟨-99, 33⟩, ⟨231, -99⟩, ⟨-132, 66⟩⟩,
    ⟨⟨0, 0⟩, ⟨-78, 30⟩, ⟨42, -6⟩⟩,
    ⟨⟨231, -99⟩, ⟨132, -66⟩, ⟨99, -33⟩⟩,
    ⟨⟨-78, 30⟩, ⟨42, -6⟩, ⟨0, 0⟩⟩,
    ⟨⟨132, -66⟩, ⟨99, -33⟩, ⟨231, -99⟩⟩,
    ⟨⟨42, -6⟩, ⟨0, 0⟩, ⟨-78, 30⟩⟩,
    ⟨⟨99, -33⟩, ⟨231, -99⟩, ⟨132, -66⟩⟩,
    ⟨⟨0, 0⟩, ⟨-78, 30⟩, ⟨-42, 6⟩⟩,
    ⟨⟨231, -99⟩, ⟨132, -66⟩, ⟨-99, 33⟩⟩,
    ⟨⟨-78, 30⟩, ⟨-42, 6⟩, ⟨0, 0⟩⟩,
    ⟨⟨132, -66⟩, ⟨-99, 33⟩, ⟨231, -99⟩⟩,
    ⟨⟨-42, 6⟩, ⟨0, 0⟩, ⟨-78, 30⟩⟩,
    ⟨⟨-99, 33⟩, ⟨231, -99⟩, ⟨132, -66⟩⟩,
    ⟨⟨-66, 22⟩, ⟨0, 0⟩, ⟨-22, 22⟩⟩,
    ⟨⟨-231, 99⟩, ⟨-132, 66⟩, ⟨99, -33⟩⟩,
    ⟨⟨0, 0⟩, ⟨-22, 22⟩, ⟨-66, 22⟩⟩,
    ⟨⟨-132, 66⟩, ⟨99, -33⟩, ⟨-231, 99⟩⟩,
    ⟨⟨-22, 22⟩, ⟨-66, 22⟩, ⟨0, 0⟩⟩,
    ⟨⟨99, -33⟩, ⟨-231, 99⟩, ⟨-132, 66⟩⟩,
    ⟨⟨-66, 22⟩, ⟨0, 0⟩, ⟨22, -22⟩⟩,
    ⟨⟨-231, 99⟩, ⟨-132, 66⟩, ⟨-99, 33⟩⟩,
    ⟨⟨0, 0⟩, ⟨22, -22⟩, ⟨-66, 22⟩⟩,
    ⟨⟨-132, 66⟩, ⟨-99, 33⟩, ⟨-231, 99⟩⟩,
    ⟨⟨22, -22⟩, ⟨-66, 22⟩, ⟨0, 0⟩⟩,
    ⟨⟨-99, 33⟩, ⟨-231, 99⟩, ⟨-132, 66⟩⟩,
    ⟨⟨-231, 99⟩, ⟨132, -66⟩, ⟨99, -33⟩⟩,
    ⟨⟨132, -66⟩, ⟨99, -33⟩, ⟨-231, 99⟩⟩,
    ⟨⟨99, -33⟩, ⟨-231, 99⟩, ⟨132, -66⟩⟩,
    ⟨⟨-231, 99⟩, ⟨132, -66⟩, ⟨-99, 33⟩⟩,
    ⟨⟨132, -66⟩, ⟨-99, 33⟩, ⟨-231, 99⟩⟩,
    ⟨⟨-99, 33⟩, ⟨-231, 99⟩, ⟨132, -66⟩⟩,
    ⟨⟨-36, 24⟩, ⟨-36, 24⟩, ⟨-36, 24⟩⟩,
    ⟨⟨-36, 24⟩, ⟨-36, 24⟩, ⟨36, -24⟩⟩,
    ⟨⟨-36, 24⟩, ⟨36, -24⟩, ⟨-36, 24⟩⟩,
    ⟨⟨36, -24⟩, ⟨-36, 24⟩, ⟨-36, 24⟩⟩,
    ⟨⟨-36, 24⟩, ⟨36, -24⟩, ⟨36, -24⟩⟩,
    ⟨⟨36, -24⟩, ⟨36, -24⟩, ⟨-36, 24⟩⟩,
    ⟨⟨36, -24⟩, ⟨-36, 24⟩, ⟨36, -24⟩⟩,
    ⟨⟨36, -24⟩, ⟨36, -24⟩, ⟨36, -24⟩⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 132 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨-264, 132⟩⟩ : V3 (ZSqrt 5)) = ![0, 0,
    -2 + √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt1 : (1 / 132 : ℝ) • Exact.reV (⟨⟨66, -22⟩, ⟨0, 0⟩, ⟨-22, 22⟩⟩ : V3 (ZSqrt 5)) = ![1/2
    - 1/6 * √5, 0, -1/6 + 1/6 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt2 : (1 / 132 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨78, -30⟩, ⟨42, -6⟩⟩ : V3 (ZSqrt 5)) = ![0,
    13/22 - 5/22 * √5, 7/22 - 1/22 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt3 : (1 / 132 : ℝ) • Exact.reV (⟨⟨231, -99⟩, ⟨-132, 66⟩, ⟨99, -33⟩⟩ : V3 (ZSqrt 5)) =
    ![7/4 - 3/4 * √5, -1 + 1/2 * √5, 3/4 - 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt4 : (1 / 132 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨-264, 132⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![0, -2
    + √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt5 : (1 / 132 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨-22, 22⟩, ⟨66, -22⟩⟩ : V3 (ZSqrt 5)) = ![0,
    -1/6 + 1/6 * √5, 1/2 - 1/6 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt6 : (1 / 132 : ℝ) • Exact.reV (⟨⟨78, -30⟩, ⟨42, -6⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![13/22
    - 5/22 * √5, 7/22 - 1/22 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt7 : (1 / 132 : ℝ) • Exact.reV (⟨⟨-132, 66⟩, ⟨99, -33⟩, ⟨231, -99⟩⟩ : V3 (ZSqrt 5)) =
    ![-1 + 1/2 * √5, 3/4 - 1/4 * √5, 7/4 - 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt8 : (1 / 132 : ℝ) • Exact.reV (⟨⟨-264, 132⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![-2 +
    √5, 0, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt9 : (1 / 132 : ℝ) • Exact.reV (⟨⟨-22, 22⟩, ⟨66, -22⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![-1/6
    + 1/6 * √5, 1/2 - 1/6 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt10 : (1 / 132 : ℝ) • Exact.reV (⟨⟨42, -6⟩, ⟨0, 0⟩, ⟨78, -30⟩⟩ : V3 (ZSqrt 5)) = ![7/22
    - 1/22 * √5, 0, 13/22 - 5/22 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt11 : (1 / 132 : ℝ) • Exact.reV (⟨⟨99, -33⟩, ⟨231, -99⟩, ⟨-132, 66⟩⟩ : V3 (ZSqrt 5)) =
    ![3/4 - 1/4 * √5, 7/4 - 3/4 * √5, -1 + 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt12 : (1 / 132 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨264, -132⟩⟩ : V3 (ZSqrt 5)) = ![0,
    0, 2 - √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt13 : (1 / 132 : ℝ) • Exact.reV (⟨⟨66, -22⟩, ⟨0, 0⟩, ⟨22, -22⟩⟩ : V3 (ZSqrt 5)) = ![1/2
    - 1/6 * √5, 0, 1/6 - 1/6 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt14 : (1 / 132 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨78, -30⟩, ⟨-42, 6⟩⟩ : V3 (ZSqrt 5)) = ![0,
    13/22 - 5/22 * √5, -7/22 + 1/22 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt15 : (1 / 132 : ℝ) • Exact.reV (⟨⟨231, -99⟩, ⟨-132, 66⟩, ⟨-99, 33⟩⟩ : V3 (ZSqrt 5)) =
    ![7/4 - 3/4 * √5, -1 + 1/2 * √5, -3/4 + 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt16 : (1 / 132 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨264, -132⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![0, 2
    - √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt17 : (1 / 132 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨22, -22⟩, ⟨66, -22⟩⟩ : V3 (ZSqrt 5)) = ![0,
    1/6 - 1/6 * √5, 1/2 - 1/6 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt18 : (1 / 132 : ℝ) • Exact.reV (⟨⟨78, -30⟩, ⟨-42, 6⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) =
    ![13/22 - 5/22 * √5, -7/22 + 1/22 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt19 : (1 / 132 : ℝ) • Exact.reV (⟨⟨-132, 66⟩, ⟨-99, 33⟩, ⟨231, -99⟩⟩ : V3 (ZSqrt 5)) =
    ![-1 + 1/2 * √5, -3/4 + 1/4 * √5, 7/4 - 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt20 : (1 / 132 : ℝ) • Exact.reV (⟨⟨264, -132⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![2 -
    √5, 0, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt21 : (1 / 132 : ℝ) • Exact.reV (⟨⟨22, -22⟩, ⟨66, -22⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![1/6
    - 1/6 * √5, 1/2 - 1/6 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt22 : (1 / 132 : ℝ) • Exact.reV (⟨⟨-42, 6⟩, ⟨0, 0⟩, ⟨78, -30⟩⟩ : V3 (ZSqrt 5)) =
    ![-7/22 + 1/22 * √5, 0, 13/22 - 5/22 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt23 : (1 / 132 : ℝ) • Exact.reV (⟨⟨-99, 33⟩, ⟨231, -99⟩, ⟨-132, 66⟩⟩ : V3 (ZSqrt 5)) =
    ![-3/4 + 1/4 * √5, 7/4 - 3/4 * √5, -1 + 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt24 : (1 / 132 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨-78, 30⟩, ⟨42, -6⟩⟩ : V3 (ZSqrt 5)) = ![0,
    -13/22 + 5/22 * √5, 7/22 - 1/22 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt25 : (1 / 132 : ℝ) • Exact.reV (⟨⟨231, -99⟩, ⟨132, -66⟩, ⟨99, -33⟩⟩ : V3 (ZSqrt 5)) =
    ![7/4 - 3/4 * √5, 1 - 1/2 * √5, 3/4 - 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt26 : (1 / 132 : ℝ) • Exact.reV (⟨⟨-78, 30⟩, ⟨42, -6⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) =
    ![-13/22 + 5/22 * √5, 7/22 - 1/22 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt27 : (1 / 132 : ℝ) • Exact.reV (⟨⟨132, -66⟩, ⟨99, -33⟩, ⟨231, -99⟩⟩ : V3 (ZSqrt 5)) =
    ![1 - 1/2 * √5, 3/4 - 1/4 * √5, 7/4 - 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt28 : (1 / 132 : ℝ) • Exact.reV (⟨⟨42, -6⟩, ⟨0, 0⟩, ⟨-78, 30⟩⟩ : V3 (ZSqrt 5)) = ![7/22
    - 1/22 * √5, 0, -13/22 + 5/22 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt29 : (1 / 132 : ℝ) • Exact.reV (⟨⟨99, -33⟩, ⟨231, -99⟩, ⟨132, -66⟩⟩ : V3 (ZSqrt 5)) =
    ![3/4 - 1/4 * √5, 7/4 - 3/4 * √5, 1 - 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt30 : (1 / 132 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨-78, 30⟩, ⟨-42, 6⟩⟩ : V3 (ZSqrt 5)) = ![0,
    -13/22 + 5/22 * √5, -7/22 + 1/22 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt31 : (1 / 132 : ℝ) • Exact.reV (⟨⟨231, -99⟩, ⟨132, -66⟩, ⟨-99, 33⟩⟩ : V3 (ZSqrt 5)) =
    ![7/4 - 3/4 * √5, 1 - 1/2 * √5, -3/4 + 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt32 : (1 / 132 : ℝ) • Exact.reV (⟨⟨-78, 30⟩, ⟨-42, 6⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) =
    ![-13/22 + 5/22 * √5, -7/22 + 1/22 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt33 : (1 / 132 : ℝ) • Exact.reV (⟨⟨132, -66⟩, ⟨-99, 33⟩, ⟨231, -99⟩⟩ : V3 (ZSqrt 5)) =
    ![1 - 1/2 * √5, -3/4 + 1/4 * √5, 7/4 - 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt34 : (1 / 132 : ℝ) • Exact.reV (⟨⟨-42, 6⟩, ⟨0, 0⟩, ⟨-78, 30⟩⟩ : V3 (ZSqrt 5)) =
    ![-7/22 + 1/22 * √5, 0, -13/22 + 5/22 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt35 : (1 / 132 : ℝ) • Exact.reV (⟨⟨-99, 33⟩, ⟨231, -99⟩, ⟨132, -66⟩⟩ : V3 (ZSqrt 5)) =
    ![-3/4 + 1/4 * √5, 7/4 - 3/4 * √5, 1 - 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt36 : (1 / 132 : ℝ) • Exact.reV (⟨⟨-66, 22⟩, ⟨0, 0⟩, ⟨-22, 22⟩⟩ : V3 (ZSqrt 5)) =
    ![-1/2 + 1/6 * √5, 0, -1/6 + 1/6 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt37 : (1 / 132 : ℝ) • Exact.reV (⟨⟨-231, 99⟩, ⟨-132, 66⟩, ⟨99, -33⟩⟩ : V3 (ZSqrt 5)) =
    ![-7/4 + 3/4 * √5, -1 + 1/2 * √5, 3/4 - 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt38 : (1 / 132 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨-22, 22⟩, ⟨-66, 22⟩⟩ : V3 (ZSqrt 5)) = ![0,
    -1/6 + 1/6 * √5, -1/2 + 1/6 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt39 : (1 / 132 : ℝ) • Exact.reV (⟨⟨-132, 66⟩, ⟨99, -33⟩, ⟨-231, 99⟩⟩ : V3 (ZSqrt 5)) =
    ![-1 + 1/2 * √5, 3/4 - 1/4 * √5, -7/4 + 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt40 : (1 / 132 : ℝ) • Exact.reV (⟨⟨-22, 22⟩, ⟨-66, 22⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) =
    ![-1/6 + 1/6 * √5, -1/2 + 1/6 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt41 : (1 / 132 : ℝ) • Exact.reV (⟨⟨99, -33⟩, ⟨-231, 99⟩, ⟨-132, 66⟩⟩ : V3 (ZSqrt 5)) =
    ![3/4 - 1/4 * √5, -7/4 + 3/4 * √5, -1 + 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt42 : (1 / 132 : ℝ) • Exact.reV (⟨⟨-66, 22⟩, ⟨0, 0⟩, ⟨22, -22⟩⟩ : V3 (ZSqrt 5)) =
    ![-1/2 + 1/6 * √5, 0, 1/6 - 1/6 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt43 : (1 / 132 : ℝ) • Exact.reV (⟨⟨-231, 99⟩, ⟨-132, 66⟩, ⟨-99, 33⟩⟩ : V3 (ZSqrt 5)) =
    ![-7/4 + 3/4 * √5, -1 + 1/2 * √5, -3/4 + 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt44 : (1 / 132 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨22, -22⟩, ⟨-66, 22⟩⟩ : V3 (ZSqrt 5)) = ![0,
    1/6 - 1/6 * √5, -1/2 + 1/6 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt45 : (1 / 132 : ℝ) • Exact.reV (⟨⟨-132, 66⟩, ⟨-99, 33⟩, ⟨-231, 99⟩⟩ : V3 (ZSqrt 5)) =
    ![-1 + 1/2 * √5, -3/4 + 1/4 * √5, -7/4 + 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt46 : (1 / 132 : ℝ) • Exact.reV (⟨⟨22, -22⟩, ⟨-66, 22⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![1/6
    - 1/6 * √5, -1/2 + 1/6 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt47 : (1 / 132 : ℝ) • Exact.reV (⟨⟨-99, 33⟩, ⟨-231, 99⟩, ⟨-132, 66⟩⟩ : V3 (ZSqrt 5)) =
    ![-3/4 + 1/4 * √5, -7/4 + 3/4 * √5, -1 + 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt48 : (1 / 132 : ℝ) • Exact.reV (⟨⟨-231, 99⟩, ⟨132, -66⟩, ⟨99, -33⟩⟩ : V3 (ZSqrt 5)) =
    ![-7/4 + 3/4 * √5, 1 - 1/2 * √5, 3/4 - 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt49 : (1 / 132 : ℝ) • Exact.reV (⟨⟨132, -66⟩, ⟨99, -33⟩, ⟨-231, 99⟩⟩ : V3 (ZSqrt 5)) =
    ![1 - 1/2 * √5, 3/4 - 1/4 * √5, -7/4 + 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt50 : (1 / 132 : ℝ) • Exact.reV (⟨⟨99, -33⟩, ⟨-231, 99⟩, ⟨132, -66⟩⟩ : V3 (ZSqrt 5)) =
    ![3/4 - 1/4 * √5, -7/4 + 3/4 * √5, 1 - 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt51 : (1 / 132 : ℝ) • Exact.reV (⟨⟨-231, 99⟩, ⟨132, -66⟩, ⟨-99, 33⟩⟩ : V3 (ZSqrt 5)) =
    ![-7/4 + 3/4 * √5, 1 - 1/2 * √5, -3/4 + 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt52 : (1 / 132 : ℝ) • Exact.reV (⟨⟨132, -66⟩, ⟨-99, 33⟩, ⟨-231, 99⟩⟩ : V3 (ZSqrt 5)) =
    ![1 - 1/2 * √5, -3/4 + 1/4 * √5, -7/4 + 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt53 : (1 / 132 : ℝ) • Exact.reV (⟨⟨-99, 33⟩, ⟨-231, 99⟩, ⟨132, -66⟩⟩ : V3 (ZSqrt 5)) =
    ![-3/4 + 1/4 * √5, -7/4 + 3/4 * √5, 1 - 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt54 : (1 / 132 : ℝ) • Exact.reV (⟨⟨-36, 24⟩, ⟨-36, 24⟩, ⟨-36, 24⟩⟩ : V3 (ZSqrt 5)) =
    ![-3/11 + 2/11 * √5, -3/11 + 2/11 * √5, -3/11 + 2/11 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt55 : (1 / 132 : ℝ) • Exact.reV (⟨⟨-36, 24⟩, ⟨-36, 24⟩, ⟨36, -24⟩⟩ : V3 (ZSqrt 5)) =
    ![-3/11 + 2/11 * √5, -3/11 + 2/11 * √5, 3/11 - 2/11 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt56 : (1 / 132 : ℝ) • Exact.reV (⟨⟨-36, 24⟩, ⟨36, -24⟩, ⟨-36, 24⟩⟩ : V3 (ZSqrt 5)) =
    ![-3/11 + 2/11 * √5, 3/11 - 2/11 * √5, -3/11 + 2/11 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt57 : (1 / 132 : ℝ) • Exact.reV (⟨⟨36, -24⟩, ⟨-36, 24⟩, ⟨-36, 24⟩⟩ : V3 (ZSqrt 5)) =
    ![3/11 - 2/11 * √5, -3/11 + 2/11 * √5, -3/11 + 2/11 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt58 : (1 / 132 : ℝ) • Exact.reV (⟨⟨-36, 24⟩, ⟨36, -24⟩, ⟨36, -24⟩⟩ : V3 (ZSqrt 5)) =
    ![-3/11 + 2/11 * √5, 3/11 - 2/11 * √5, 3/11 - 2/11 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt59 : (1 / 132 : ℝ) • Exact.reV (⟨⟨36, -24⟩, ⟨36, -24⟩, ⟨-36, 24⟩⟩ : V3 (ZSqrt 5)) =
    ![3/11 - 2/11 * √5, 3/11 - 2/11 * √5, -3/11 + 2/11 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt60 : (1 / 132 : ℝ) • Exact.reV (⟨⟨36, -24⟩, ⟨-36, 24⟩, ⟨36, -24⟩⟩ : V3 (ZSqrt 5)) =
    ![3/11 - 2/11 * √5, -3/11 + 2/11 * √5, 3/11 - 2/11 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt61 : (1 / 132 : ℝ) • Exact.reV (⟨⟨36, -24⟩, ⟨36, -24⟩, ⟨36, -24⟩⟩ : V3 (ZSqrt 5)) =
    ![3/11 - 2/11 * √5, 3/11 - 2/11 * √5, 3/11 - 2/11 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem eq_smul : Catalan.DeltoidalHexecontahedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 132) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17, pt18, pt19, pt20, pt21, pt22, pt23, pt24,
    pt25, pt26, pt27, pt28, pt29, pt30, pt31, pt32, pt33, pt34, pt35, pt36, pt37, pt38, pt39, pt40,
    pt41, pt42, pt43, pt44, pt45, pt46, pt47, pt48, pt49, pt50, pt51, pt52, pt53, pt54, pt55, pt56,
    pt57, pt58, pt59, pt60, pt61]

end Nieuwland.Polyhedra.CatalanDeltoidalHexecontahedronDim

namespace Nieuwland.Polyhedra

/-- **The fixture `catalan/deltoidal-hexecontahedron` is full-dimensional.** -/
theorem catalanDeltoidalHexecontahedron_fullDim : Catalan.DeltoidalHexecontahedron.polyhedron.FullDim := by
  rw [CatalanDeltoidalHexecontahedronDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk CatalanDeltoidalHexecontahedronDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
