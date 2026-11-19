import Polyhedra.Catalan.RhombicTriacontahedron.Definition
import Modules.Check.Leaf.FullDim

set_option linter.style.longLine false

/-!
# The fixture `catalan/rhombic-triacontahedron` is full-dimensional

The points of `Catalan.RhombicTriacontahedron.polyhedron` times `8` as exact values in `ZSqrt 5`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Catalan.RhombicTriacontahedron.polyhedron`.
-/

namespace Nieuwland.Polyhedra.CatalanRhombicTriacontahedronDim

open Check

/-- The points of `Catalan.RhombicTriacontahedron.polyhedron` times `8`. -/
def points : List (V3 (ZSqrt 5)) := [
    ⟨⟨5, 1⟩, ⟨0, 0⟩, ⟨5, 3⟩⟩,
    ⟨⟨5, 1⟩, ⟨0, 0⟩, ⟨-5, -3⟩⟩,
    ⟨⟨-5, -1⟩, ⟨0, 0⟩, ⟨5, 3⟩⟩,
    ⟨⟨-5, -1⟩, ⟨0, 0⟩, ⟨-5, -3⟩⟩,
    ⟨⟨5, 3⟩, ⟨5, 1⟩, ⟨0, 0⟩⟩,
    ⟨⟨5, 3⟩, ⟨-5, -1⟩, ⟨0, 0⟩⟩,
    ⟨⟨-5, -3⟩, ⟨5, 1⟩, ⟨0, 0⟩⟩,
    ⟨⟨-5, -3⟩, ⟨-5, -1⟩, ⟨0, 0⟩⟩,
    ⟨⟨0, 0⟩, ⟨5, 3⟩, ⟨5, 1⟩⟩,
    ⟨⟨0, 0⟩, ⟨5, 3⟩, ⟨-5, -1⟩⟩,
    ⟨⟨0, 0⟩, ⟨-5, -3⟩, ⟨5, 1⟩⟩,
    ⟨⟨0, 0⟩, ⟨-5, -3⟩, ⟨-5, -1⟩⟩,
    ⟨⟨0, 0⟩, ⟨0, 2⟩, ⟨5, 3⟩⟩,
    ⟨⟨0, 0⟩, ⟨0, 2⟩, ⟨-5, -3⟩⟩,
    ⟨⟨0, 0⟩, ⟨0, -2⟩, ⟨5, 3⟩⟩,
    ⟨⟨0, 0⟩, ⟨0, -2⟩, ⟨-5, -3⟩⟩,
    ⟨⟨5, 3⟩, ⟨0, 0⟩, ⟨0, 2⟩⟩,
    ⟨⟨5, 3⟩, ⟨0, 0⟩, ⟨0, -2⟩⟩,
    ⟨⟨-5, -3⟩, ⟨0, 0⟩, ⟨0, 2⟩⟩,
    ⟨⟨-5, -3⟩, ⟨0, 0⟩, ⟨0, -2⟩⟩,
    ⟨⟨0, 2⟩, ⟨5, 3⟩, ⟨0, 0⟩⟩,
    ⟨⟨0, 2⟩, ⟨-5, -3⟩, ⟨0, 0⟩⟩,
    ⟨⟨0, -2⟩, ⟨5, 3⟩, ⟨0, 0⟩⟩,
    ⟨⟨0, -2⟩, ⟨-5, -3⟩, ⟨0, 0⟩⟩,
    ⟨⟨5, 1⟩, ⟨5, 1⟩, ⟨5, 1⟩⟩,
    ⟨⟨5, 1⟩, ⟨5, 1⟩, ⟨-5, -1⟩⟩,
    ⟨⟨5, 1⟩, ⟨-5, -1⟩, ⟨5, 1⟩⟩,
    ⟨⟨5, 1⟩, ⟨-5, -1⟩, ⟨-5, -1⟩⟩,
    ⟨⟨-5, -1⟩, ⟨5, 1⟩, ⟨5, 1⟩⟩,
    ⟨⟨-5, -1⟩, ⟨5, 1⟩, ⟨-5, -1⟩⟩,
    ⟨⟨-5, -1⟩, ⟨-5, -1⟩, ⟨5, 1⟩⟩,
    ⟨⟨-5, -1⟩, ⟨-5, -1⟩, ⟨-5, -1⟩⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 8 : ℝ) • Exact.reV (⟨⟨5, 1⟩, ⟨0, 0⟩, ⟨5, 3⟩⟩ : V3 (ZSqrt 5)) = ![5/8 + 1/8 *
    √5, 0, 5/8 + 3/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt1 : (1 / 8 : ℝ) • Exact.reV (⟨⟨5, 1⟩, ⟨0, 0⟩, ⟨-5, -3⟩⟩ : V3 (ZSqrt 5)) = ![5/8 + 1/8
    * √5, 0, -5/8 - 3/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt2 : (1 / 8 : ℝ) • Exact.reV (⟨⟨-5, -1⟩, ⟨0, 0⟩, ⟨5, 3⟩⟩ : V3 (ZSqrt 5)) = ![-5/8 - 1/8
    * √5, 0, 5/8 + 3/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt3 : (1 / 8 : ℝ) • Exact.reV (⟨⟨-5, -1⟩, ⟨0, 0⟩, ⟨-5, -3⟩⟩ : V3 (ZSqrt 5)) = ![-5/8 -
    1/8 * √5, 0, -5/8 - 3/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt4 : (1 / 8 : ℝ) • Exact.reV (⟨⟨5, 3⟩, ⟨5, 1⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![5/8 + 3/8 *
    √5, 5/8 + 1/8 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt5 : (1 / 8 : ℝ) • Exact.reV (⟨⟨5, 3⟩, ⟨-5, -1⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![5/8 + 3/8
    * √5, -5/8 - 1/8 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt6 : (1 / 8 : ℝ) • Exact.reV (⟨⟨-5, -3⟩, ⟨5, 1⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![-5/8 - 3/8
    * √5, 5/8 + 1/8 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt7 : (1 / 8 : ℝ) • Exact.reV (⟨⟨-5, -3⟩, ⟨-5, -1⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![-5/8 -
    3/8 * √5, -5/8 - 1/8 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt8 : (1 / 8 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨5, 3⟩, ⟨5, 1⟩⟩ : V3 (ZSqrt 5)) = ![0, 5/8 + 3/8
    * √5, 5/8 + 1/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt9 : (1 / 8 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨5, 3⟩, ⟨-5, -1⟩⟩ : V3 (ZSqrt 5)) = ![0, 5/8 +
    3/8 * √5, -5/8 - 1/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt10 : (1 / 8 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨-5, -3⟩, ⟨5, 1⟩⟩ : V3 (ZSqrt 5)) = ![0, -5/8 -
    3/8 * √5, 5/8 + 1/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt11 : (1 / 8 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨-5, -3⟩, ⟨-5, -1⟩⟩ : V3 (ZSqrt 5)) = ![0, -5/8
    - 3/8 * √5, -5/8 - 1/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt12 : (1 / 8 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨0, 2⟩, ⟨5, 3⟩⟩ : V3 (ZSqrt 5)) = ![0, 1/4 *
    √5, 5/8 + 3/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt13 : (1 / 8 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨0, 2⟩, ⟨-5, -3⟩⟩ : V3 (ZSqrt 5)) = ![0, 1/4 *
    √5, -5/8 - 3/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt14 : (1 / 8 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨0, -2⟩, ⟨5, 3⟩⟩ : V3 (ZSqrt 5)) = ![0, -(1/4 *
    √5), 5/8 + 3/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt15 : (1 / 8 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨0, -2⟩, ⟨-5, -3⟩⟩ : V3 (ZSqrt 5)) = ![0, -(1/4
    * √5), -5/8 - 3/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt16 : (1 / 8 : ℝ) • Exact.reV (⟨⟨5, 3⟩, ⟨0, 0⟩, ⟨0, 2⟩⟩ : V3 (ZSqrt 5)) = ![5/8 + 3/8 *
    √5, 0, 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt17 : (1 / 8 : ℝ) • Exact.reV (⟨⟨5, 3⟩, ⟨0, 0⟩, ⟨0, -2⟩⟩ : V3 (ZSqrt 5)) = ![5/8 + 3/8
    * √5, 0, -(1/4 * √5)] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt18 : (1 / 8 : ℝ) • Exact.reV (⟨⟨-5, -3⟩, ⟨0, 0⟩, ⟨0, 2⟩⟩ : V3 (ZSqrt 5)) = ![-5/8 -
    3/8 * √5, 0, 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt19 : (1 / 8 : ℝ) • Exact.reV (⟨⟨-5, -3⟩, ⟨0, 0⟩, ⟨0, -2⟩⟩ : V3 (ZSqrt 5)) = ![-5/8 -
    3/8 * √5, 0, -(1/4 * √5)] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt20 : (1 / 8 : ℝ) • Exact.reV (⟨⟨0, 2⟩, ⟨5, 3⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![1/4 * √5,
    5/8 + 3/8 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt21 : (1 / 8 : ℝ) • Exact.reV (⟨⟨0, 2⟩, ⟨-5, -3⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![1/4 * √5,
    -5/8 - 3/8 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt22 : (1 / 8 : ℝ) • Exact.reV (⟨⟨0, -2⟩, ⟨5, 3⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![-(1/4 *
    √5), 5/8 + 3/8 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt23 : (1 / 8 : ℝ) • Exact.reV (⟨⟨0, -2⟩, ⟨-5, -3⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![-(1/4 *
    √5), -5/8 - 3/8 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt24 : (1 / 8 : ℝ) • Exact.reV (⟨⟨5, 1⟩, ⟨5, 1⟩, ⟨5, 1⟩⟩ : V3 (ZSqrt 5)) = ![5/8 + 1/8 *
    √5, 5/8 + 1/8 * √5, 5/8 + 1/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt25 : (1 / 8 : ℝ) • Exact.reV (⟨⟨5, 1⟩, ⟨5, 1⟩, ⟨-5, -1⟩⟩ : V3 (ZSqrt 5)) = ![5/8 + 1/8
    * √5, 5/8 + 1/8 * √5, -5/8 - 1/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt26 : (1 / 8 : ℝ) • Exact.reV (⟨⟨5, 1⟩, ⟨-5, -1⟩, ⟨5, 1⟩⟩ : V3 (ZSqrt 5)) = ![5/8 + 1/8
    * √5, -5/8 - 1/8 * √5, 5/8 + 1/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt27 : (1 / 8 : ℝ) • Exact.reV (⟨⟨5, 1⟩, ⟨-5, -1⟩, ⟨-5, -1⟩⟩ : V3 (ZSqrt 5)) = ![5/8 +
    1/8 * √5, -5/8 - 1/8 * √5, -5/8 - 1/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt28 : (1 / 8 : ℝ) • Exact.reV (⟨⟨-5, -1⟩, ⟨5, 1⟩, ⟨5, 1⟩⟩ : V3 (ZSqrt 5)) = ![-5/8 -
    1/8 * √5, 5/8 + 1/8 * √5, 5/8 + 1/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt29 : (1 / 8 : ℝ) • Exact.reV (⟨⟨-5, -1⟩, ⟨5, 1⟩, ⟨-5, -1⟩⟩ : V3 (ZSqrt 5)) = ![-5/8 -
    1/8 * √5, 5/8 + 1/8 * √5, -5/8 - 1/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt30 : (1 / 8 : ℝ) • Exact.reV (⟨⟨-5, -1⟩, ⟨-5, -1⟩, ⟨5, 1⟩⟩ : V3 (ZSqrt 5)) = ![-5/8 -
    1/8 * √5, -5/8 - 1/8 * √5, 5/8 + 1/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt31 : (1 / 8 : ℝ) • Exact.reV (⟨⟨-5, -1⟩, ⟨-5, -1⟩, ⟨-5, -1⟩⟩ : V3 (ZSqrt 5)) = ![-5/8
    - 1/8 * √5, -5/8 - 1/8 * √5, -5/8 - 1/8 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem eq_smul : Catalan.RhombicTriacontahedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 8) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17, pt18, pt19, pt20, pt21, pt22, pt23, pt24,
    pt25, pt26, pt27, pt28, pt29, pt30, pt31]

end Nieuwland.Polyhedra.CatalanRhombicTriacontahedronDim

namespace Nieuwland.Polyhedra

/-- **The fixture `catalan/rhombic-triacontahedron` is full-dimensional.** -/
theorem catalanRhombicTriacontahedron_fullDim : Catalan.RhombicTriacontahedron.polyhedron.FullDim := by
  rw [CatalanRhombicTriacontahedronDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk CatalanRhombicTriacontahedronDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
