import Polyhedra.Other.TriangularDipyramid.Definition
import Modules.Check.Leaf.FullDim

set_option linter.style.longLine false

/-!
# The fixture `dipyramid/triangular-dipyramid` is full-dimensional

The points of `Other.TriangularDipyramid.polyhedron` times `2` as exact values in `ZSqrt 3`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Other.TriangularDipyramid.polyhedron`.
-/

namespace Nieuwland.Polyhedra.DipyramidTriangularDipyramidDim

open Check

/-- The points of `Other.TriangularDipyramid.polyhedron` times `2`. -/
def points : List (V3 (ZSqrt 3)) := [
    ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩⟩,
    ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩⟩,
    ⟨⟨0, 1⟩, ⟨3, 0⟩, ⟨0, 0⟩⟩,
    ⟨⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩,
    ⟨⟨0, 1⟩, ⟨-3, 0⟩, ⟨0, 0⟩⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 2 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩⟩ : V3 (ZSqrt 3)) = ![0, 0, -1]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt1 : (1 / 2 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩⟩ : V3 (ZSqrt 3)) = ![0, 0, 1] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt2 : (1 / 2 : ℝ) • Exact.reV (⟨⟨0, 1⟩, ⟨3, 0⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 3)) = ![1/2 * √3,
    3/2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt3 : (1 / 2 : ℝ) • Exact.reV (⟨⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 3)) = ![-(√3), 0,
    0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt4 : (1 / 2 : ℝ) • Exact.reV (⟨⟨0, 1⟩, ⟨-3, 0⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 3)) = ![1/2 * √3,
    -3/2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem eq_smul : Other.TriangularDipyramid.polyhedron = (Polyhedron.ofPoints points).smul (1 / 2) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4]

end Nieuwland.Polyhedra.DipyramidTriangularDipyramidDim

namespace Nieuwland.Polyhedra

/-- **The fixture `dipyramid/triangular-dipyramid` is full-dimensional.** -/
theorem dipyramidTriangularDipyramid_fullDim : Other.TriangularDipyramid.polyhedron.FullDim := by
  rw [DipyramidTriangularDipyramidDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk DipyramidTriangularDipyramidDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
