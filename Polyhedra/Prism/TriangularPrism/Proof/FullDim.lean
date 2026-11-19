import Polyhedra.Prism.TriangularPrism.Definition
import Modules.Check.Leaf.FullDim

/-!
# The fixture `prism/triangular-prism` is full-dimensional

The points of `Prism.TriangularPrism.polyhedron` times `6` as exact values in `ZSqrt 3`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Prism.TriangularPrism.polyhedron`.
-/

namespace Nieuwland.Polyhedra.PrismTriangularPrismDim

open Check

/-- The points of `Prism.TriangularPrism.polyhedron` times `6`. -/
def points : List (V3 (ZSqrt 3)) := [
    ⟨⟨0, 2⟩, ⟨0, 0⟩, ⟨-3, 0⟩⟩,
    ⟨⟨0, -1⟩, ⟨3, 0⟩, ⟨-3, 0⟩⟩,
    ⟨⟨0, -1⟩, ⟨-3, 0⟩, ⟨-3, 0⟩⟩,
    ⟨⟨0, 2⟩, ⟨0, 0⟩, ⟨3, 0⟩⟩,
    ⟨⟨0, -1⟩, ⟨3, 0⟩, ⟨3, 0⟩⟩,
    ⟨⟨0, -1⟩, ⟨-3, 0⟩, ⟨3, 0⟩⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 6 : ℝ) • Exact.reV (⟨⟨0, 2⟩, ⟨0, 0⟩, ⟨-3, 0⟩⟩ : V3 (ZSqrt 3)) = ![1/3 * √3,
    0, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt1 : (1 / 6 : ℝ) • Exact.reV (⟨⟨0, -1⟩, ⟨3, 0⟩, ⟨-3, 0⟩⟩ : V3 (ZSqrt 3)) = ![-(1/6 *
    √3), 1/2, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt2 : (1 / 6 : ℝ) • Exact.reV (⟨⟨0, -1⟩, ⟨-3, 0⟩, ⟨-3, 0⟩⟩ : V3 (ZSqrt 3)) = ![-(1/6 *
    √3), -1/2, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt3 : (1 / 6 : ℝ) • Exact.reV (⟨⟨0, 2⟩, ⟨0, 0⟩, ⟨3, 0⟩⟩ : V3 (ZSqrt 3)) = ![1/3 * √3, 0,
    1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt4 : (1 / 6 : ℝ) • Exact.reV (⟨⟨0, -1⟩, ⟨3, 0⟩, ⟨3, 0⟩⟩ : V3 (ZSqrt 3)) = ![-(1/6 *
    √3), 1/2, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt5 : (1 / 6 : ℝ) • Exact.reV (⟨⟨0, -1⟩, ⟨-3, 0⟩, ⟨3, 0⟩⟩ : V3 (ZSqrt 3)) = ![-(1/6 *
    √3), -1/2, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem eq_smul : Prism.TriangularPrism.polyhedron = (Polyhedron.ofPoints points).smul (1 / 6) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5]

end Nieuwland.Polyhedra.PrismTriangularPrismDim

namespace Nieuwland.Polyhedra

/-- **The fixture `prism/triangular-prism` is full-dimensional.** -/
theorem prismTriangularPrism_fullDim : Prism.TriangularPrism.polyhedron.FullDim := by
  rw [PrismTriangularPrismDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk PrismTriangularPrismDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
