import Polyhedra.Catalan.DisdyakisTriacontahedron.Definition
import Modules.Check.Leaf.FullDim

set_option linter.style.longLine false

/-!
# The fixture `catalan/disdyakis-triacontahedron` is full-dimensional

The points of `Catalan.DisdyakisTriacontahedron.polyhedron` times `220` as exact values in `ZSqrt 5`, exported
by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Catalan.DisdyakisTriacontahedron.polyhedron`.
-/

namespace Nieuwland.Polyhedra.CatalanDisdyakisTriacontahedronDim

open Check

/-- The points of `Catalan.DisdyakisTriacontahedron.polyhedron` times `220`. -/
def points : List (V3 (ZSqrt 5)) := [
    ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨300, 240⟩⟩,
    ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨-300, -240⟩⟩,
    ⟨⟨300, 240⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩,
    ⟨⟨-300, -240⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩,
    ⟨⟨0, 0⟩, ⟨300, 240⟩, ⟨0, 0⟩⟩,
    ⟨⟨0, 0⟩, ⟨-300, -240⟩, ⟨0, 0⟩⟩,
    ⟨⟨0, 0⟩, ⟨550, -110⟩, ⟨550, 110⟩⟩,
    ⟨⟨0, 0⟩, ⟨550, -110⟩, ⟨-550, -110⟩⟩,
    ⟨⟨0, 0⟩, ⟨-550, 110⟩, ⟨550, 110⟩⟩,
    ⟨⟨0, 0⟩, ⟨-550, 110⟩, ⟨-550, -110⟩⟩,
    ⟨⟨550, 110⟩, ⟨0, 0⟩, ⟨550, -110⟩⟩,
    ⟨⟨550, 110⟩, ⟨0, 0⟩, ⟨-550, 110⟩⟩,
    ⟨⟨-550, -110⟩, ⟨0, 0⟩, ⟨550, -110⟩⟩,
    ⟨⟨-550, -110⟩, ⟨0, 0⟩, ⟨-550, 110⟩⟩,
    ⟨⟨550, -110⟩, ⟨550, 110⟩, ⟨0, 0⟩⟩,
    ⟨⟨550, -110⟩, ⟨-550, -110⟩, ⟨0, 0⟩⟩,
    ⟨⟨-550, 110⟩, ⟨550, 110⟩, ⟨0, 0⟩⟩,
    ⟨⟨-550, 110⟩, ⟨-550, -110⟩, ⟨0, 0⟩⟩,
    ⟨⟨330, 66⟩, ⟨0, 0⟩, ⟨330, 198⟩⟩,
    ⟨⟨330, 66⟩, ⟨0, 0⟩, ⟨-330, -198⟩⟩,
    ⟨⟨-330, -66⟩, ⟨0, 0⟩, ⟨330, 198⟩⟩,
    ⟨⟨-330, -66⟩, ⟨0, 0⟩, ⟨-330, -198⟩⟩,
    ⟨⟨330, 198⟩, ⟨330, 66⟩, ⟨0, 0⟩⟩,
    ⟨⟨330, 198⟩, ⟨-330, -66⟩, ⟨0, 0⟩⟩,
    ⟨⟨-330, -198⟩, ⟨330, 66⟩, ⟨0, 0⟩⟩,
    ⟨⟨-330, -198⟩, ⟨-330, -66⟩, ⟨0, 0⟩⟩,
    ⟨⟨0, 0⟩, ⟨330, 198⟩, ⟨330, 66⟩⟩,
    ⟨⟨0, 0⟩, ⟨330, 198⟩, ⟨-330, -66⟩⟩,
    ⟨⟨0, 0⟩, ⟨-330, -198⟩, ⟨330, 66⟩⟩,
    ⟨⟨0, 0⟩, ⟨-330, -198⟩, ⟨-330, -66⟩⟩,
    ⟨⟨225, 15⟩, ⟨150, 120⟩, ⟨375, 135⟩⟩,
    ⟨⟨225, 15⟩, ⟨150, 120⟩, ⟨-375, -135⟩⟩,
    ⟨⟨225, 15⟩, ⟨-150, -120⟩, ⟨375, 135⟩⟩,
    ⟨⟨225, 15⟩, ⟨-150, -120⟩, ⟨-375, -135⟩⟩,
    ⟨⟨-225, -15⟩, ⟨150, 120⟩, ⟨375, 135⟩⟩,
    ⟨⟨-225, -15⟩, ⟨150, 120⟩, ⟨-375, -135⟩⟩,
    ⟨⟨-225, -15⟩, ⟨-150, -120⟩, ⟨375, 135⟩⟩,
    ⟨⟨-225, -15⟩, ⟨-150, -120⟩, ⟨-375, -135⟩⟩,
    ⟨⟨375, 135⟩, ⟨225, 15⟩, ⟨150, 120⟩⟩,
    ⟨⟨375, 135⟩, ⟨225, 15⟩, ⟨-150, -120⟩⟩,
    ⟨⟨375, 135⟩, ⟨-225, -15⟩, ⟨150, 120⟩⟩,
    ⟨⟨375, 135⟩, ⟨-225, -15⟩, ⟨-150, -120⟩⟩,
    ⟨⟨-375, -135⟩, ⟨225, 15⟩, ⟨150, 120⟩⟩,
    ⟨⟨-375, -135⟩, ⟨225, 15⟩, ⟨-150, -120⟩⟩,
    ⟨⟨-375, -135⟩, ⟨-225, -15⟩, ⟨150, 120⟩⟩,
    ⟨⟨-375, -135⟩, ⟨-225, -15⟩, ⟨-150, -120⟩⟩,
    ⟨⟨150, 120⟩, ⟨375, 135⟩, ⟨225, 15⟩⟩,
    ⟨⟨150, 120⟩, ⟨375, 135⟩, ⟨-225, -15⟩⟩,
    ⟨⟨150, 120⟩, ⟨-375, -135⟩, ⟨225, 15⟩⟩,
    ⟨⟨150, 120⟩, ⟨-375, -135⟩, ⟨-225, -15⟩⟩,
    ⟨⟨-150, -120⟩, ⟨375, 135⟩, ⟨225, 15⟩⟩,
    ⟨⟨-150, -120⟩, ⟨375, 135⟩, ⟨-225, -15⟩⟩,
    ⟨⟨-150, -120⟩, ⟨-375, -135⟩, ⟨225, 15⟩⟩,
    ⟨⟨-150, -120⟩, ⟨-375, -135⟩, ⟨-225, -15⟩⟩,
    ⟨⟨0, 220⟩, ⟨0, 220⟩, ⟨0, 220⟩⟩,
    ⟨⟨0, 220⟩, ⟨0, 220⟩, ⟨0, -220⟩⟩,
    ⟨⟨0, 220⟩, ⟨0, -220⟩, ⟨0, 220⟩⟩,
    ⟨⟨0, 220⟩, ⟨0, -220⟩, ⟨0, -220⟩⟩,
    ⟨⟨0, -220⟩, ⟨0, 220⟩, ⟨0, 220⟩⟩,
    ⟨⟨0, -220⟩, ⟨0, 220⟩, ⟨0, -220⟩⟩,
    ⟨⟨0, -220⟩, ⟨0, -220⟩, ⟨0, 220⟩⟩,
    ⟨⟨0, -220⟩, ⟨0, -220⟩, ⟨0, -220⟩⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 220 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨300, 240⟩⟩ : V3 (ZSqrt 5)) = ![0, 0,
    15/11 + 12/11 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt1 : (1 / 220 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨-300, -240⟩⟩ : V3 (ZSqrt 5)) = ![0,
    0, -15/11 - 12/11 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt2 : (1 / 220 : ℝ) • Exact.reV (⟨⟨300, 240⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![15/11
    + 12/11 * √5, 0, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt3 : (1 / 220 : ℝ) • Exact.reV (⟨⟨-300, -240⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) =
    ![-15/11 - 12/11 * √5, 0, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt4 : (1 / 220 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨300, 240⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![0,
    15/11 + 12/11 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt5 : (1 / 220 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨-300, -240⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![0,
    -15/11 - 12/11 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt6 : (1 / 220 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨550, -110⟩, ⟨550, 110⟩⟩ : V3 (ZSqrt 5)) =
    ![0, 5/2 - 1/2 * √5, 5/2 + 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt7 : (1 / 220 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨550, -110⟩, ⟨-550, -110⟩⟩ : V3 (ZSqrt 5)) =
    ![0, 5/2 - 1/2 * √5, -5/2 - 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt8 : (1 / 220 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨-550, 110⟩, ⟨550, 110⟩⟩ : V3 (ZSqrt 5)) =
    ![0, -5/2 + 1/2 * √5, 5/2 + 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt9 : (1 / 220 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨-550, 110⟩, ⟨-550, -110⟩⟩ : V3 (ZSqrt 5)) =
    ![0, -5/2 + 1/2 * √5, -5/2 - 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt10 : (1 / 220 : ℝ) • Exact.reV (⟨⟨550, 110⟩, ⟨0, 0⟩, ⟨550, -110⟩⟩ : V3 (ZSqrt 5)) =
    ![5/2 + 1/2 * √5, 0, 5/2 - 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt11 : (1 / 220 : ℝ) • Exact.reV (⟨⟨550, 110⟩, ⟨0, 0⟩, ⟨-550, 110⟩⟩ : V3 (ZSqrt 5)) =
    ![5/2 + 1/2 * √5, 0, -5/2 + 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt12 : (1 / 220 : ℝ) • Exact.reV (⟨⟨-550, -110⟩, ⟨0, 0⟩, ⟨550, -110⟩⟩ : V3 (ZSqrt 5)) =
    ![-5/2 - 1/2 * √5, 0, 5/2 - 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt13 : (1 / 220 : ℝ) • Exact.reV (⟨⟨-550, -110⟩, ⟨0, 0⟩, ⟨-550, 110⟩⟩ : V3 (ZSqrt 5)) =
    ![-5/2 - 1/2 * √5, 0, -5/2 + 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt14 : (1 / 220 : ℝ) • Exact.reV (⟨⟨550, -110⟩, ⟨550, 110⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) =
    ![5/2 - 1/2 * √5, 5/2 + 1/2 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt15 : (1 / 220 : ℝ) • Exact.reV (⟨⟨550, -110⟩, ⟨-550, -110⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) =
    ![5/2 - 1/2 * √5, -5/2 - 1/2 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt16 : (1 / 220 : ℝ) • Exact.reV (⟨⟨-550, 110⟩, ⟨550, 110⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) =
    ![-5/2 + 1/2 * √5, 5/2 + 1/2 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt17 : (1 / 220 : ℝ) • Exact.reV (⟨⟨-550, 110⟩, ⟨-550, -110⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) =
    ![-5/2 + 1/2 * √5, -5/2 - 1/2 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt18 : (1 / 220 : ℝ) • Exact.reV (⟨⟨330, 66⟩, ⟨0, 0⟩, ⟨330, 198⟩⟩ : V3 (ZSqrt 5)) =
    ![3/2 + 3/10 * √5, 0, 3/2 + 9/10 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt19 : (1 / 220 : ℝ) • Exact.reV (⟨⟨330, 66⟩, ⟨0, 0⟩, ⟨-330, -198⟩⟩ : V3 (ZSqrt 5)) =
    ![3/2 + 3/10 * √5, 0, -3/2 - 9/10 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt20 : (1 / 220 : ℝ) • Exact.reV (⟨⟨-330, -66⟩, ⟨0, 0⟩, ⟨330, 198⟩⟩ : V3 (ZSqrt 5)) =
    ![-3/2 - 3/10 * √5, 0, 3/2 + 9/10 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt21 : (1 / 220 : ℝ) • Exact.reV (⟨⟨-330, -66⟩, ⟨0, 0⟩, ⟨-330, -198⟩⟩ : V3 (ZSqrt 5)) =
    ![-3/2 - 3/10 * √5, 0, -3/2 - 9/10 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt22 : (1 / 220 : ℝ) • Exact.reV (⟨⟨330, 198⟩, ⟨330, 66⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) =
    ![3/2 + 9/10 * √5, 3/2 + 3/10 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt23 : (1 / 220 : ℝ) • Exact.reV (⟨⟨330, 198⟩, ⟨-330, -66⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) =
    ![3/2 + 9/10 * √5, -3/2 - 3/10 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt24 : (1 / 220 : ℝ) • Exact.reV (⟨⟨-330, -198⟩, ⟨330, 66⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) =
    ![-3/2 - 9/10 * √5, 3/2 + 3/10 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt25 : (1 / 220 : ℝ) • Exact.reV (⟨⟨-330, -198⟩, ⟨-330, -66⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) =
    ![-3/2 - 9/10 * √5, -3/2 - 3/10 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt26 : (1 / 220 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨330, 198⟩, ⟨330, 66⟩⟩ : V3 (ZSqrt 5)) = ![0,
    3/2 + 9/10 * √5, 3/2 + 3/10 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt27 : (1 / 220 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨330, 198⟩, ⟨-330, -66⟩⟩ : V3 (ZSqrt 5)) =
    ![0, 3/2 + 9/10 * √5, -3/2 - 3/10 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt28 : (1 / 220 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨-330, -198⟩, ⟨330, 66⟩⟩ : V3 (ZSqrt 5)) =
    ![0, -3/2 - 9/10 * √5, 3/2 + 3/10 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt29 : (1 / 220 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨-330, -198⟩, ⟨-330, -66⟩⟩ : V3 (ZSqrt 5)) =
    ![0, -3/2 - 9/10 * √5, -3/2 - 3/10 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt30 : (1 / 220 : ℝ) • Exact.reV (⟨⟨225, 15⟩, ⟨150, 120⟩, ⟨375, 135⟩⟩ : V3 (ZSqrt 5)) =
    ![45/44 + 3/44 * √5, 15/22 + 6/11 * √5, 75/44 + 27/44 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt31 : (1 / 220 : ℝ) • Exact.reV (⟨⟨225, 15⟩, ⟨150, 120⟩, ⟨-375, -135⟩⟩ : V3 (ZSqrt 5))
    = ![45/44 + 3/44 * √5, 15/22 + 6/11 * √5, -75/44 - 27/44 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt32 : (1 / 220 : ℝ) • Exact.reV (⟨⟨225, 15⟩, ⟨-150, -120⟩, ⟨375, 135⟩⟩ : V3 (ZSqrt 5))
    = ![45/44 + 3/44 * √5, -15/22 - 6/11 * √5, 75/44 + 27/44 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt33 : (1 / 220 : ℝ) • Exact.reV (⟨⟨225, 15⟩, ⟨-150, -120⟩, ⟨-375, -135⟩⟩ : V3 (ZSqrt
    5)) = ![45/44 + 3/44 * √5, -15/22 - 6/11 * √5, -75/44 - 27/44 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt34 : (1 / 220 : ℝ) • Exact.reV (⟨⟨-225, -15⟩, ⟨150, 120⟩, ⟨375, 135⟩⟩ : V3 (ZSqrt 5))
    = ![-45/44 - 3/44 * √5, 15/22 + 6/11 * √5, 75/44 + 27/44 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt35 : (1 / 220 : ℝ) • Exact.reV (⟨⟨-225, -15⟩, ⟨150, 120⟩, ⟨-375, -135⟩⟩ : V3 (ZSqrt
    5)) = ![-45/44 - 3/44 * √5, 15/22 + 6/11 * √5, -75/44 - 27/44 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt36 : (1 / 220 : ℝ) • Exact.reV (⟨⟨-225, -15⟩, ⟨-150, -120⟩, ⟨375, 135⟩⟩ : V3 (ZSqrt
    5)) = ![-45/44 - 3/44 * √5, -15/22 - 6/11 * √5, 75/44 + 27/44 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt37 : (1 / 220 : ℝ) • Exact.reV (⟨⟨-225, -15⟩, ⟨-150, -120⟩, ⟨-375, -135⟩⟩ : V3 (ZSqrt
    5)) = ![-45/44 - 3/44 * √5, -15/22 - 6/11 * √5, -75/44 - 27/44 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt38 : (1 / 220 : ℝ) • Exact.reV (⟨⟨375, 135⟩, ⟨225, 15⟩, ⟨150, 120⟩⟩ : V3 (ZSqrt 5)) =
    ![75/44 + 27/44 * √5, 45/44 + 3/44 * √5, 15/22 + 6/11 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt39 : (1 / 220 : ℝ) • Exact.reV (⟨⟨375, 135⟩, ⟨225, 15⟩, ⟨-150, -120⟩⟩ : V3 (ZSqrt 5))
    = ![75/44 + 27/44 * √5, 45/44 + 3/44 * √5, -15/22 - 6/11 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt40 : (1 / 220 : ℝ) • Exact.reV (⟨⟨375, 135⟩, ⟨-225, -15⟩, ⟨150, 120⟩⟩ : V3 (ZSqrt 5))
    = ![75/44 + 27/44 * √5, -45/44 - 3/44 * √5, 15/22 + 6/11 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt41 : (1 / 220 : ℝ) • Exact.reV (⟨⟨375, 135⟩, ⟨-225, -15⟩, ⟨-150, -120⟩⟩ : V3 (ZSqrt
    5)) = ![75/44 + 27/44 * √5, -45/44 - 3/44 * √5, -15/22 - 6/11 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt42 : (1 / 220 : ℝ) • Exact.reV (⟨⟨-375, -135⟩, ⟨225, 15⟩, ⟨150, 120⟩⟩ : V3 (ZSqrt 5))
    = ![-75/44 - 27/44 * √5, 45/44 + 3/44 * √5, 15/22 + 6/11 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt43 : (1 / 220 : ℝ) • Exact.reV (⟨⟨-375, -135⟩, ⟨225, 15⟩, ⟨-150, -120⟩⟩ : V3 (ZSqrt
    5)) = ![-75/44 - 27/44 * √5, 45/44 + 3/44 * √5, -15/22 - 6/11 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt44 : (1 / 220 : ℝ) • Exact.reV (⟨⟨-375, -135⟩, ⟨-225, -15⟩, ⟨150, 120⟩⟩ : V3 (ZSqrt
    5)) = ![-75/44 - 27/44 * √5, -45/44 - 3/44 * √5, 15/22 + 6/11 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt45 : (1 / 220 : ℝ) • Exact.reV (⟨⟨-375, -135⟩, ⟨-225, -15⟩, ⟨-150, -120⟩⟩ : V3 (ZSqrt
    5)) = ![-75/44 - 27/44 * √5, -45/44 - 3/44 * √5, -15/22 - 6/11 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt46 : (1 / 220 : ℝ) • Exact.reV (⟨⟨150, 120⟩, ⟨375, 135⟩, ⟨225, 15⟩⟩ : V3 (ZSqrt 5)) =
    ![15/22 + 6/11 * √5, 75/44 + 27/44 * √5, 45/44 + 3/44 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt47 : (1 / 220 : ℝ) • Exact.reV (⟨⟨150, 120⟩, ⟨375, 135⟩, ⟨-225, -15⟩⟩ : V3 (ZSqrt 5))
    = ![15/22 + 6/11 * √5, 75/44 + 27/44 * √5, -45/44 - 3/44 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt48 : (1 / 220 : ℝ) • Exact.reV (⟨⟨150, 120⟩, ⟨-375, -135⟩, ⟨225, 15⟩⟩ : V3 (ZSqrt 5))
    = ![15/22 + 6/11 * √5, -75/44 - 27/44 * √5, 45/44 + 3/44 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt49 : (1 / 220 : ℝ) • Exact.reV (⟨⟨150, 120⟩, ⟨-375, -135⟩, ⟨-225, -15⟩⟩ : V3 (ZSqrt
    5)) = ![15/22 + 6/11 * √5, -75/44 - 27/44 * √5, -45/44 - 3/44 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt50 : (1 / 220 : ℝ) • Exact.reV (⟨⟨-150, -120⟩, ⟨375, 135⟩, ⟨225, 15⟩⟩ : V3 (ZSqrt 5))
    = ![-15/22 - 6/11 * √5, 75/44 + 27/44 * √5, 45/44 + 3/44 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt51 : (1 / 220 : ℝ) • Exact.reV (⟨⟨-150, -120⟩, ⟨375, 135⟩, ⟨-225, -15⟩⟩ : V3 (ZSqrt
    5)) = ![-15/22 - 6/11 * √5, 75/44 + 27/44 * √5, -45/44 - 3/44 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt52 : (1 / 220 : ℝ) • Exact.reV (⟨⟨-150, -120⟩, ⟨-375, -135⟩, ⟨225, 15⟩⟩ : V3 (ZSqrt
    5)) = ![-15/22 - 6/11 * √5, -75/44 - 27/44 * √5, 45/44 + 3/44 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt53 : (1 / 220 : ℝ) • Exact.reV (⟨⟨-150, -120⟩, ⟨-375, -135⟩, ⟨-225, -15⟩⟩ : V3 (ZSqrt
    5)) = ![-15/22 - 6/11 * √5, -75/44 - 27/44 * √5, -45/44 - 3/44 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt54 : (1 / 220 : ℝ) • Exact.reV (⟨⟨0, 220⟩, ⟨0, 220⟩, ⟨0, 220⟩⟩ : V3 (ZSqrt 5)) = ![√5,
    √5, √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt55 : (1 / 220 : ℝ) • Exact.reV (⟨⟨0, 220⟩, ⟨0, 220⟩, ⟨0, -220⟩⟩ : V3 (ZSqrt 5)) =
    ![√5, √5, -(√5)] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt56 : (1 / 220 : ℝ) • Exact.reV (⟨⟨0, 220⟩, ⟨0, -220⟩, ⟨0, 220⟩⟩ : V3 (ZSqrt 5)) =
    ![√5, -(√5), √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt57 : (1 / 220 : ℝ) • Exact.reV (⟨⟨0, 220⟩, ⟨0, -220⟩, ⟨0, -220⟩⟩ : V3 (ZSqrt 5)) =
    ![√5, -(√5), -(√5)] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt58 : (1 / 220 : ℝ) • Exact.reV (⟨⟨0, -220⟩, ⟨0, 220⟩, ⟨0, 220⟩⟩ : V3 (ZSqrt 5)) =
    ![-(√5), √5, √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt59 : (1 / 220 : ℝ) • Exact.reV (⟨⟨0, -220⟩, ⟨0, 220⟩, ⟨0, -220⟩⟩ : V3 (ZSqrt 5)) =
    ![-(√5), √5, -(√5)] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt60 : (1 / 220 : ℝ) • Exact.reV (⟨⟨0, -220⟩, ⟨0, -220⟩, ⟨0, 220⟩⟩ : V3 (ZSqrt 5)) =
    ![-(√5), -(√5), √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt61 : (1 / 220 : ℝ) • Exact.reV (⟨⟨0, -220⟩, ⟨0, -220⟩, ⟨0, -220⟩⟩ : V3 (ZSqrt 5)) =
    ![-(√5), -(√5), -(√5)] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem eq_smul : Catalan.DisdyakisTriacontahedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 220) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17, pt18, pt19, pt20, pt21, pt22, pt23, pt24,
    pt25, pt26, pt27, pt28, pt29, pt30, pt31, pt32, pt33, pt34, pt35, pt36, pt37, pt38, pt39, pt40,
    pt41, pt42, pt43, pt44, pt45, pt46, pt47, pt48, pt49, pt50, pt51, pt52, pt53, pt54, pt55, pt56,
    pt57, pt58, pt59, pt60, pt61]

end Nieuwland.Polyhedra.CatalanDisdyakisTriacontahedronDim

namespace Nieuwland.Polyhedra

/-- **The fixture `catalan/disdyakis-triacontahedron` is full-dimensional.** -/
theorem catalanDisdyakisTriacontahedron_fullDim : Catalan.DisdyakisTriacontahedron.polyhedron.FullDim := by
  rw [CatalanDisdyakisTriacontahedronDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk CatalanDisdyakisTriacontahedronDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
