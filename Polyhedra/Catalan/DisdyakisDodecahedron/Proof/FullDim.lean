import Polyhedra.Catalan.DisdyakisDodecahedron.Definition
import Modules.Check.Leaf.FullDim

set_option linter.style.longLine false

/-!
# The fixture `catalan/disdyakis-dodecahedron` is full-dimensional

The points of `Catalan.DisdyakisDodecahedron.polyhedron` times `7` as exact values in `ZSqrt 2`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Catalan.DisdyakisDodecahedron.polyhedron`.
-/

namespace Nieuwland.Polyhedra.CatalanDisdyakisDodecahedronDim

open Check

/-- The points of `Catalan.DisdyakisDodecahedron.polyhedron` times `7`. -/
def points : List (V3 (ZSqrt 2)) := [
    ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨6, 9⟩⟩,
    ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨-6, -9⟩⟩,
    ⟨⟨6, 9⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩,
    ⟨⟨-6, -9⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩,
    ⟨⟨0, 0⟩, ⟨6, 9⟩, ⟨0, 0⟩⟩,
    ⟨⟨0, 0⟩, ⟨-6, -9⟩, ⟨0, 0⟩⟩,
    ⟨⟨3, 6⟩, ⟨0, 0⟩, ⟨3, 6⟩⟩,
    ⟨⟨3, 6⟩, ⟨0, 0⟩, ⟨-3, -6⟩⟩,
    ⟨⟨-3, -6⟩, ⟨0, 0⟩, ⟨3, 6⟩⟩,
    ⟨⟨-3, -6⟩, ⟨0, 0⟩, ⟨-3, -6⟩⟩,
    ⟨⟨3, 6⟩, ⟨3, 6⟩, ⟨0, 0⟩⟩,
    ⟨⟨3, 6⟩, ⟨-3, -6⟩, ⟨0, 0⟩⟩,
    ⟨⟨-3, -6⟩, ⟨3, 6⟩, ⟨0, 0⟩⟩,
    ⟨⟨-3, -6⟩, ⟨-3, -6⟩, ⟨0, 0⟩⟩,
    ⟨⟨0, 0⟩, ⟨3, 6⟩, ⟨3, 6⟩⟩,
    ⟨⟨0, 0⟩, ⟨3, 6⟩, ⟨-3, -6⟩⟩,
    ⟨⟨0, 0⟩, ⟨-3, -6⟩, ⟨3, 6⟩⟩,
    ⟨⟨0, 0⟩, ⟨-3, -6⟩, ⟨-3, -6⟩⟩,
    ⟨⟨0, 7⟩, ⟨0, 7⟩, ⟨0, 7⟩⟩,
    ⟨⟨0, 7⟩, ⟨0, 7⟩, ⟨0, -7⟩⟩,
    ⟨⟨0, 7⟩, ⟨0, -7⟩, ⟨0, 7⟩⟩,
    ⟨⟨0, 7⟩, ⟨0, -7⟩, ⟨0, -7⟩⟩,
    ⟨⟨0, -7⟩, ⟨0, 7⟩, ⟨0, 7⟩⟩,
    ⟨⟨0, -7⟩, ⟨0, 7⟩, ⟨0, -7⟩⟩,
    ⟨⟨0, -7⟩, ⟨0, -7⟩, ⟨0, 7⟩⟩,
    ⟨⟨0, -7⟩, ⟨0, -7⟩, ⟨0, -7⟩⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 7 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨6, 9⟩⟩ : V3 (ZSqrt 2)) = ![0, 0, 6/7 +
    9/7 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt1 : (1 / 7 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨-6, -9⟩⟩ : V3 (ZSqrt 2)) = ![0, 0, -6/7
    - 9/7 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt2 : (1 / 7 : ℝ) • Exact.reV (⟨⟨6, 9⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 2)) = ![6/7 + 9/7 *
    √2, 0, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt3 : (1 / 7 : ℝ) • Exact.reV (⟨⟨-6, -9⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 2)) = ![-6/7 - 9/7
    * √2, 0, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt4 : (1 / 7 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨6, 9⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 2)) = ![0, 6/7 + 9/7
    * √2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt5 : (1 / 7 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨-6, -9⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 2)) = ![0, -6/7 -
    9/7 * √2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt6 : (1 / 7 : ℝ) • Exact.reV (⟨⟨3, 6⟩, ⟨0, 0⟩, ⟨3, 6⟩⟩ : V3 (ZSqrt 2)) = ![3/7 + 6/7 *
    √2, 0, 3/7 + 6/7 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt7 : (1 / 7 : ℝ) • Exact.reV (⟨⟨3, 6⟩, ⟨0, 0⟩, ⟨-3, -6⟩⟩ : V3 (ZSqrt 2)) = ![3/7 + 6/7
    * √2, 0, -3/7 - 6/7 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt8 : (1 / 7 : ℝ) • Exact.reV (⟨⟨-3, -6⟩, ⟨0, 0⟩, ⟨3, 6⟩⟩ : V3 (ZSqrt 2)) = ![-3/7 - 6/7
    * √2, 0, 3/7 + 6/7 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt9 : (1 / 7 : ℝ) • Exact.reV (⟨⟨-3, -6⟩, ⟨0, 0⟩, ⟨-3, -6⟩⟩ : V3 (ZSqrt 2)) = ![-3/7 -
    6/7 * √2, 0, -3/7 - 6/7 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt10 : (1 / 7 : ℝ) • Exact.reV (⟨⟨3, 6⟩, ⟨3, 6⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 2)) = ![3/7 + 6/7 *
    √2, 3/7 + 6/7 * √2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt11 : (1 / 7 : ℝ) • Exact.reV (⟨⟨3, 6⟩, ⟨-3, -6⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 2)) = ![3/7 + 6/7
    * √2, -3/7 - 6/7 * √2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt12 : (1 / 7 : ℝ) • Exact.reV (⟨⟨-3, -6⟩, ⟨3, 6⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 2)) = ![-3/7 -
    6/7 * √2, 3/7 + 6/7 * √2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt13 : (1 / 7 : ℝ) • Exact.reV (⟨⟨-3, -6⟩, ⟨-3, -6⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 2)) = ![-3/7 -
    6/7 * √2, -3/7 - 6/7 * √2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt14 : (1 / 7 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨3, 6⟩, ⟨3, 6⟩⟩ : V3 (ZSqrt 2)) = ![0, 3/7 +
    6/7 * √2, 3/7 + 6/7 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt15 : (1 / 7 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨3, 6⟩, ⟨-3, -6⟩⟩ : V3 (ZSqrt 2)) = ![0, 3/7 +
    6/7 * √2, -3/7 - 6/7 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt16 : (1 / 7 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨-3, -6⟩, ⟨3, 6⟩⟩ : V3 (ZSqrt 2)) = ![0, -3/7 -
    6/7 * √2, 3/7 + 6/7 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt17 : (1 / 7 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨-3, -6⟩, ⟨-3, -6⟩⟩ : V3 (ZSqrt 2)) = ![0, -3/7
    - 6/7 * √2, -3/7 - 6/7 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt18 : (1 / 7 : ℝ) • Exact.reV (⟨⟨0, 7⟩, ⟨0, 7⟩, ⟨0, 7⟩⟩ : V3 (ZSqrt 2)) = ![√2, √2, √2]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt19 : (1 / 7 : ℝ) • Exact.reV (⟨⟨0, 7⟩, ⟨0, 7⟩, ⟨0, -7⟩⟩ : V3 (ZSqrt 2)) = ![√2, √2,
    -(√2)] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt20 : (1 / 7 : ℝ) • Exact.reV (⟨⟨0, 7⟩, ⟨0, -7⟩, ⟨0, 7⟩⟩ : V3 (ZSqrt 2)) = ![√2, -(√2),
    √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt21 : (1 / 7 : ℝ) • Exact.reV (⟨⟨0, 7⟩, ⟨0, -7⟩, ⟨0, -7⟩⟩ : V3 (ZSqrt 2)) = ![√2,
    -(√2), -(√2)] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt22 : (1 / 7 : ℝ) • Exact.reV (⟨⟨0, -7⟩, ⟨0, 7⟩, ⟨0, 7⟩⟩ : V3 (ZSqrt 2)) = ![-(√2), √2,
    √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt23 : (1 / 7 : ℝ) • Exact.reV (⟨⟨0, -7⟩, ⟨0, 7⟩, ⟨0, -7⟩⟩ : V3 (ZSqrt 2)) = ![-(√2),
    √2, -(√2)] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt24 : (1 / 7 : ℝ) • Exact.reV (⟨⟨0, -7⟩, ⟨0, -7⟩, ⟨0, 7⟩⟩ : V3 (ZSqrt 2)) = ![-(√2),
    -(√2), √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt25 : (1 / 7 : ℝ) • Exact.reV (⟨⟨0, -7⟩, ⟨0, -7⟩, ⟨0, -7⟩⟩ : V3 (ZSqrt 2)) = ![-(√2),
    -(√2), -(√2)] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem eq_smul : Catalan.DisdyakisDodecahedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 7) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17, pt18, pt19, pt20, pt21, pt22, pt23, pt24,
    pt25]

end Nieuwland.Polyhedra.CatalanDisdyakisDodecahedronDim

namespace Nieuwland.Polyhedra

/-- **The fixture `catalan/disdyakis-dodecahedron` is full-dimensional.** -/
theorem catalanDisdyakisDodecahedron_fullDim : Catalan.DisdyakisDodecahedron.polyhedron.FullDim := by
  rw [CatalanDisdyakisDodecahedronDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk CatalanDisdyakisDodecahedronDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
