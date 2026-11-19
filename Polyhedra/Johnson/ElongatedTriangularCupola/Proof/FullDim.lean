import Polyhedra.Johnson.ElongatedTriangularCupola.Definition
import Modules.Check.Leaf.FullDim

set_option linter.style.longLine false

/-!
# The fixture `johnson/elongated-triangular-cupola` is full-dimensional

The points of `Johnson.ElongatedTriangularCupola.polyhedron` times `1` as exact values in `ZSqrt 6`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Johnson.ElongatedTriangularCupola.polyhedron`.
-/

namespace Nieuwland.Polyhedra.JohnsonElongatedTriangularCupolaDim

open Check

/-- The points of `Johnson.ElongatedTriangularCupola.polyhedron` times `1`. -/
def points : List (V3 (ZSqrt 6)) := [
    ⟨⟨1, 1⟩, ⟨1, -1⟩, ⟨1, 0⟩⟩,
    ⟨⟨-1, -1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩⟩,
    ⟨⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩⟩,
    ⟨⟨1, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩⟩,
    ⟨⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩⟩,
    ⟨⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩⟩,
    ⟨⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩⟩,
    ⟨⟨1, 1⟩, ⟨1, 0⟩, ⟨1, -1⟩⟩,
    ⟨⟨1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩⟩,
    ⟨⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩⟩,
    ⟨⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩⟩,
    ⟨⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩⟩,
    ⟨⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩⟩,
    ⟨⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩⟩,
    ⟨⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 1 : ℝ) • Exact.reV (⟨⟨1, 1⟩, ⟨1, -1⟩, ⟨1, 0⟩⟩ : V3 (ZSqrt 6)) = ![1 + √6, 1 -
    √6, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt1 : (1 / 1 : ℝ) • Exact.reV (⟨⟨-1, -1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩⟩ : V3 (ZSqrt 6)) = ![-1 - √6,
    -1 + √6, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt2 : (1 / 1 : ℝ) • Exact.reV (⟨⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩⟩ : V3 (ZSqrt 6)) = ![-1, -1 -
    √6, -1 + √6] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt3 : (1 / 1 : ℝ) • Exact.reV (⟨⟨1, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩⟩ : V3 (ZSqrt 6)) = ![1, 1 + √6,
    1 - √6] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt4 : (1 / 1 : ℝ) • Exact.reV (⟨⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩⟩ : V3 (ZSqrt 6)) = ![1 - √6, 1,
    1 + √6] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt5 : (1 / 1 : ℝ) • Exact.reV (⟨⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩⟩ : V3 (ZSqrt 6)) = ![-1 + √6,
    -1, -1 - √6] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt6 : (1 / 1 : ℝ) • Exact.reV (⟨⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩⟩ : V3 (ZSqrt 6)) = ![-1 - √6,
    -1, -1 + √6] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt7 : (1 / 1 : ℝ) • Exact.reV (⟨⟨1, 1⟩, ⟨1, 0⟩, ⟨1, -1⟩⟩ : V3 (ZSqrt 6)) = ![1 + √6, 1,
    1 - √6] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt8 : (1 / 1 : ℝ) • Exact.reV (⟨⟨1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩⟩ : V3 (ZSqrt 6)) = ![1 - √6, 1 +
    √6, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt9 : (1 / 1 : ℝ) • Exact.reV (⟨⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩⟩ : V3 (ZSqrt 6)) = ![-1 + √6,
    -1 - √6, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt10 : (1 / 1 : ℝ) • Exact.reV (⟨⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩⟩ : V3 (ZSqrt 6)) = ![1, 1 - √6,
    1 + √6] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt11 : (1 / 1 : ℝ) • Exact.reV (⟨⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩⟩ : V3 (ZSqrt 6)) = ![-1, -1
    + √6, -1 - √6] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt12 : (1 / 1 : ℝ) • Exact.reV (⟨⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩⟩ : V3 (ZSqrt 6)) = ![1, 1 + √6,
    1 + √6] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt13 : (1 / 1 : ℝ) • Exact.reV (⟨⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩⟩ : V3 (ZSqrt 6)) = ![1 + √6, 1,
    1 + √6] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt14 : (1 / 1 : ℝ) • Exact.reV (⟨⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩⟩ : V3 (ZSqrt 6)) = ![1 + √6, 1 +
    √6, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem eq_smul : Johnson.ElongatedTriangularCupola.polyhedron = (Polyhedron.ofPoints points).smul (1 / 1) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14]

end Nieuwland.Polyhedra.JohnsonElongatedTriangularCupolaDim

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/elongated-triangular-cupola` is full-dimensional.** -/
theorem johnsonElongatedTriangularCupola_fullDim : Johnson.ElongatedTriangularCupola.polyhedron.FullDim := by
  rw [JohnsonElongatedTriangularCupolaDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk JohnsonElongatedTriangularCupolaDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
