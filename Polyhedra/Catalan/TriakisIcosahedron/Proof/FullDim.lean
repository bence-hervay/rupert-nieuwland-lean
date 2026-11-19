import Polyhedra.Catalan.TriakisIcosahedron.Definition
import Modules.Check.Leaf.FullDim

/-!
# The fixture `catalan/triakis-icosahedron` is full-dimensional

The points of `Catalan.TriakisIcosahedron.polyhedron` times `44` as exact values in `ZSqrt 5`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Catalan.TriakisIcosahedron.polyhedron`.
-/

namespace Nieuwland.Polyhedra.CatalanTriakisIcosahedronDim

open Check

/-- The points of `Catalan.TriakisIcosahedron.polyhedron` times `44`. -/
def points : List (V3 (ZSqrt 5)) := [
    ⟨⟨55, 11⟩, ⟨0, 0⟩, ⟨55, 33⟩⟩,
    ⟨⟨55, 11⟩, ⟨0, 0⟩, ⟨-55, -33⟩⟩,
    ⟨⟨-55, -11⟩, ⟨0, 0⟩, ⟨55, 33⟩⟩,
    ⟨⟨-55, -11⟩, ⟨0, 0⟩, ⟨-55, -33⟩⟩,
    ⟨⟨55, 33⟩, ⟨55, 11⟩, ⟨0, 0⟩⟩,
    ⟨⟨55, 33⟩, ⟨-55, -11⟩, ⟨0, 0⟩⟩,
    ⟨⟨-55, -33⟩, ⟨55, 11⟩, ⟨0, 0⟩⟩,
    ⟨⟨-55, -33⟩, ⟨-55, -11⟩, ⟨0, 0⟩⟩,
    ⟨⟨0, 0⟩, ⟨55, 33⟩, ⟨55, 11⟩⟩,
    ⟨⟨0, 0⟩, ⟨55, 33⟩, ⟨-55, -11⟩⟩,
    ⟨⟨0, 0⟩, ⟨-55, -33⟩, ⟨55, 11⟩⟩,
    ⟨⟨0, 0⟩, ⟨-55, -33⟩, ⟨-55, -11⟩⟩,
    ⟨⟨0, 0⟩, ⟨35, 5⟩, ⟨65, 25⟩⟩,
    ⟨⟨0, 0⟩, ⟨35, 5⟩, ⟨-65, -25⟩⟩,
    ⟨⟨0, 0⟩, ⟨-35, -5⟩, ⟨65, 25⟩⟩,
    ⟨⟨0, 0⟩, ⟨-35, -5⟩, ⟨-65, -25⟩⟩,
    ⟨⟨65, 25⟩, ⟨0, 0⟩, ⟨35, 5⟩⟩,
    ⟨⟨65, 25⟩, ⟨0, 0⟩, ⟨-35, -5⟩⟩,
    ⟨⟨-65, -25⟩, ⟨0, 0⟩, ⟨35, 5⟩⟩,
    ⟨⟨-65, -25⟩, ⟨0, 0⟩, ⟨-35, -5⟩⟩,
    ⟨⟨35, 5⟩, ⟨65, 25⟩, ⟨0, 0⟩⟩,
    ⟨⟨35, 5⟩, ⟨-65, -25⟩, ⟨0, 0⟩⟩,
    ⟨⟨-35, -5⟩, ⟨65, 25⟩, ⟨0, 0⟩⟩,
    ⟨⟨-35, -5⟩, ⟨-65, -25⟩, ⟨0, 0⟩⟩,
    ⟨⟨30, 20⟩, ⟨30, 20⟩, ⟨30, 20⟩⟩,
    ⟨⟨30, 20⟩, ⟨30, 20⟩, ⟨-30, -20⟩⟩,
    ⟨⟨30, 20⟩, ⟨-30, -20⟩, ⟨30, 20⟩⟩,
    ⟨⟨30, 20⟩, ⟨-30, -20⟩, ⟨-30, -20⟩⟩,
    ⟨⟨-30, -20⟩, ⟨30, 20⟩, ⟨30, 20⟩⟩,
    ⟨⟨-30, -20⟩, ⟨30, 20⟩, ⟨-30, -20⟩⟩,
    ⟨⟨-30, -20⟩, ⟨-30, -20⟩, ⟨30, 20⟩⟩,
    ⟨⟨-30, -20⟩, ⟨-30, -20⟩, ⟨-30, -20⟩⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 44 : ℝ) • Exact.reV (⟨⟨55, 11⟩, ⟨0, 0⟩, ⟨55, 33⟩⟩ : V3 (ZSqrt 5)) = ![5/4 +
    1/4 * √5, 0, 5/4 + 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt1 : (1 / 44 : ℝ) • Exact.reV (⟨⟨55, 11⟩, ⟨0, 0⟩, ⟨-55, -33⟩⟩ : V3 (ZSqrt 5)) = ![5/4 +
    1/4 * √5, 0, -5/4 - 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt2 : (1 / 44 : ℝ) • Exact.reV (⟨⟨-55, -11⟩, ⟨0, 0⟩, ⟨55, 33⟩⟩ : V3 (ZSqrt 5)) = ![-5/4
    - 1/4 * √5, 0, 5/4 + 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt3 : (1 / 44 : ℝ) • Exact.reV (⟨⟨-55, -11⟩, ⟨0, 0⟩, ⟨-55, -33⟩⟩ : V3 (ZSqrt 5)) =
    ![-5/4 - 1/4 * √5, 0, -5/4 - 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt4 : (1 / 44 : ℝ) • Exact.reV (⟨⟨55, 33⟩, ⟨55, 11⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![5/4 +
    3/4 * √5, 5/4 + 1/4 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt5 : (1 / 44 : ℝ) • Exact.reV (⟨⟨55, 33⟩, ⟨-55, -11⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![5/4 +
    3/4 * √5, -5/4 - 1/4 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt6 : (1 / 44 : ℝ) • Exact.reV (⟨⟨-55, -33⟩, ⟨55, 11⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![-5/4
    - 3/4 * √5, 5/4 + 1/4 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt7 : (1 / 44 : ℝ) • Exact.reV (⟨⟨-55, -33⟩, ⟨-55, -11⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) =
    ![-5/4 - 3/4 * √5, -5/4 - 1/4 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt8 : (1 / 44 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨55, 33⟩, ⟨55, 11⟩⟩ : V3 (ZSqrt 5)) = ![0, 5/4
    + 3/4 * √5, 5/4 + 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt9 : (1 / 44 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨55, 33⟩, ⟨-55, -11⟩⟩ : V3 (ZSqrt 5)) = ![0,
    5/4 + 3/4 * √5, -5/4 - 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt10 : (1 / 44 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨-55, -33⟩, ⟨55, 11⟩⟩ : V3 (ZSqrt 5)) = ![0,
    -5/4 - 3/4 * √5, 5/4 + 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt11 : (1 / 44 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨-55, -33⟩, ⟨-55, -11⟩⟩ : V3 (ZSqrt 5)) = ![0,
    -5/4 - 3/4 * √5, -5/4 - 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt12 : (1 / 44 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨35, 5⟩, ⟨65, 25⟩⟩ : V3 (ZSqrt 5)) = ![0,
    35/44 + 5/44 * √5, 65/44 + 25/44 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt13 : (1 / 44 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨35, 5⟩, ⟨-65, -25⟩⟩ : V3 (ZSqrt 5)) = ![0,
    35/44 + 5/44 * √5, -65/44 - 25/44 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt14 : (1 / 44 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨-35, -5⟩, ⟨65, 25⟩⟩ : V3 (ZSqrt 5)) = ![0,
    -35/44 - 5/44 * √5, 65/44 + 25/44 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt15 : (1 / 44 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨-35, -5⟩, ⟨-65, -25⟩⟩ : V3 (ZSqrt 5)) = ![0,
    -35/44 - 5/44 * √5, -65/44 - 25/44 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt16 : (1 / 44 : ℝ) • Exact.reV (⟨⟨65, 25⟩, ⟨0, 0⟩, ⟨35, 5⟩⟩ : V3 (ZSqrt 5)) = ![65/44 +
    25/44 * √5, 0, 35/44 + 5/44 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt17 : (1 / 44 : ℝ) • Exact.reV (⟨⟨65, 25⟩, ⟨0, 0⟩, ⟨-35, -5⟩⟩ : V3 (ZSqrt 5)) = ![65/44
    + 25/44 * √5, 0, -35/44 - 5/44 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt18 : (1 / 44 : ℝ) • Exact.reV (⟨⟨-65, -25⟩, ⟨0, 0⟩, ⟨35, 5⟩⟩ : V3 (ZSqrt 5)) =
    ![-65/44 - 25/44 * √5, 0, 35/44 + 5/44 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt19 : (1 / 44 : ℝ) • Exact.reV (⟨⟨-65, -25⟩, ⟨0, 0⟩, ⟨-35, -5⟩⟩ : V3 (ZSqrt 5)) =
    ![-65/44 - 25/44 * √5, 0, -35/44 - 5/44 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt20 : (1 / 44 : ℝ) • Exact.reV (⟨⟨35, 5⟩, ⟨65, 25⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![35/44 +
    5/44 * √5, 65/44 + 25/44 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt21 : (1 / 44 : ℝ) • Exact.reV (⟨⟨35, 5⟩, ⟨-65, -25⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![35/44
    + 5/44 * √5, -65/44 - 25/44 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt22 : (1 / 44 : ℝ) • Exact.reV (⟨⟨-35, -5⟩, ⟨65, 25⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) =
    ![-35/44 - 5/44 * √5, 65/44 + 25/44 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt23 : (1 / 44 : ℝ) • Exact.reV (⟨⟨-35, -5⟩, ⟨-65, -25⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) =
    ![-35/44 - 5/44 * √5, -65/44 - 25/44 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt24 : (1 / 44 : ℝ) • Exact.reV (⟨⟨30, 20⟩, ⟨30, 20⟩, ⟨30, 20⟩⟩ : V3 (ZSqrt 5)) =
    ![15/22 + 5/11 * √5, 15/22 + 5/11 * √5, 15/22 + 5/11 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt25 : (1 / 44 : ℝ) • Exact.reV (⟨⟨30, 20⟩, ⟨30, 20⟩, ⟨-30, -20⟩⟩ : V3 (ZSqrt 5)) =
    ![15/22 + 5/11 * √5, 15/22 + 5/11 * √5, -15/22 - 5/11 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt26 : (1 / 44 : ℝ) • Exact.reV (⟨⟨30, 20⟩, ⟨-30, -20⟩, ⟨30, 20⟩⟩ : V3 (ZSqrt 5)) =
    ![15/22 + 5/11 * √5, -15/22 - 5/11 * √5, 15/22 + 5/11 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt27 : (1 / 44 : ℝ) • Exact.reV (⟨⟨30, 20⟩, ⟨-30, -20⟩, ⟨-30, -20⟩⟩ : V3 (ZSqrt 5)) =
    ![15/22 + 5/11 * √5, -15/22 - 5/11 * √5, -15/22 - 5/11 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt28 : (1 / 44 : ℝ) • Exact.reV (⟨⟨-30, -20⟩, ⟨30, 20⟩, ⟨30, 20⟩⟩ : V3 (ZSqrt 5)) =
    ![-15/22 - 5/11 * √5, 15/22 + 5/11 * √5, 15/22 + 5/11 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt29 : (1 / 44 : ℝ) • Exact.reV (⟨⟨-30, -20⟩, ⟨30, 20⟩, ⟨-30, -20⟩⟩ : V3 (ZSqrt 5)) =
    ![-15/22 - 5/11 * √5, 15/22 + 5/11 * √5, -15/22 - 5/11 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt30 : (1 / 44 : ℝ) • Exact.reV (⟨⟨-30, -20⟩, ⟨-30, -20⟩, ⟨30, 20⟩⟩ : V3 (ZSqrt 5)) =
    ![-15/22 - 5/11 * √5, -15/22 - 5/11 * √5, 15/22 + 5/11 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt31 : (1 / 44 : ℝ) • Exact.reV (⟨⟨-30, -20⟩, ⟨-30, -20⟩, ⟨-30, -20⟩⟩ : V3 (ZSqrt 5)) =
    ![-15/22 - 5/11 * √5, -15/22 - 5/11 * √5, -15/22 - 5/11 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem eq_smul : Catalan.TriakisIcosahedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 44) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17, pt18, pt19, pt20, pt21, pt22, pt23, pt24,
    pt25, pt26, pt27, pt28, pt29, pt30, pt31]

end Nieuwland.Polyhedra.CatalanTriakisIcosahedronDim

namespace Nieuwland.Polyhedra

/-- **The fixture `catalan/triakis-icosahedron` is full-dimensional.** -/
theorem catalanTriakisIcosahedron_fullDim : Catalan.TriakisIcosahedron.polyhedron.FullDim := by
  rw [CatalanTriakisIcosahedronDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk CatalanTriakisIcosahedronDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
