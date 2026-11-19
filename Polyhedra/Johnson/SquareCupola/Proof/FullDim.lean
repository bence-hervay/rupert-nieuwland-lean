import Polyhedra.Johnson.SquareCupola.Definition
import Modules.Check.Leaf.FullDim

/-!
# The fixture `johnson/square-cupola` is full-dimensional

The points of `Johnson.SquareCupola.polyhedron` times `2` as exact values in `ZSqrt 2`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Johnson.SquareCupola.polyhedron`.
-/

namespace Nieuwland.Polyhedra.JohnsonSquareCupolaDim

open Check

/-- The points of `Johnson.SquareCupola.polyhedron` times `2`. -/
def points : List (V3 (ZSqrt 2)) := [
    ⟨⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩⟩,
    ⟨⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩⟩,
    ⟨⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩⟩,
    ⟨⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩⟩,
    ⟨⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩⟩,
    ⟨⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩⟩,
    ⟨⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩⟩,
    ⟨⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩⟩,
    ⟨⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩⟩,
    ⟨⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩⟩,
    ⟨⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩⟩,
    ⟨⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩⟩]

theorem span_ok : spanOk points 0 1 2 8 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 2)) = ![1/2 + 1/2 *
    √2, 1/2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt1 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 2)) = ![1/2 + 1/2 *
    √2, -1/2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt2 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 2)) = ![-1/2 - 1/2
    * √2, 1/2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt3 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 2)) = ![-1/2 -
    1/2 * √2, -1/2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt4 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 2)) = ![1/2, 1/2 +
    1/2 * √2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt5 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 2)) = ![1/2, -1/2
    - 1/2 * √2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt6 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 2)) = ![-1/2, 1/2 +
    1/2 * √2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt7 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 2)) = ![-1/2,
    -1/2 - 1/2 * √2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt8 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩⟩ : V3 (ZSqrt 2)) = ![1/2, 1/2,
    1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt9 : (1 / 2 : ℝ) • Exact.reV (⟨⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩⟩ : V3 (ZSqrt 2)) = ![1/2, -1/2,
    1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt10 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩⟩ : V3 (ZSqrt 2)) = ![-1/2, 1/2,
    1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt11 : (1 / 2 : ℝ) • Exact.reV (⟨⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩⟩ : V3 (ZSqrt 2)) = ![-1/2,
    -1/2, 1/2 * √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem eq_smul : Johnson.SquareCupola.polyhedron = (Polyhedron.ofPoints points).smul (1 / 2) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11]

end Nieuwland.Polyhedra.JohnsonSquareCupolaDim

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/square-cupola` is full-dimensional.** -/
theorem johnsonSquareCupola_fullDim : Johnson.SquareCupola.polyhedron.FullDim := by
  rw [JohnsonSquareCupolaDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk JohnsonSquareCupolaDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
