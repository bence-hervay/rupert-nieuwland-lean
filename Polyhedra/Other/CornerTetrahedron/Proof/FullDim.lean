import Polyhedra.Other.CornerTetrahedron.Definition
import Modules.Check.Leaf.FullDim

/-!
# The fixture `other/corner-tetrahedron` is full-dimensional

The points of `Other.CornerTetrahedron.polyhedron` times `1` as exact values in `ℤ`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Other.CornerTetrahedron.polyhedron`.
-/

namespace Nieuwland.Polyhedra.OtherCornerTetrahedronDim

open Check

/-- The points of `Other.CornerTetrahedron.polyhedron` times `1`. -/
def points : List (V3 ℤ) := [
    ⟨0, 0, 0⟩,
    ⟨1, 0, 0⟩,
    ⟨0, 1, 0⟩,
    ⟨0, 0, 1⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 1 : ℝ) • Exact.reV (⟨0, 0, 0⟩ : V3 ℤ) = ![0, 0, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt1 : (1 / 1 : ℝ) • Exact.reV (⟨1, 0, 0⟩ : V3 ℤ) = ![1, 0, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt2 : (1 / 1 : ℝ) • Exact.reV (⟨0, 1, 0⟩ : V3 ℤ) = ![0, 1, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt3 : (1 / 1 : ℝ) • Exact.reV (⟨0, 0, 1⟩ : V3 ℤ) = ![0, 0, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem eq_smul : Other.CornerTetrahedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 1) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3]

end Nieuwland.Polyhedra.OtherCornerTetrahedronDim

namespace Nieuwland.Polyhedra

/-- **The fixture `other/corner-tetrahedron` is full-dimensional.** -/
theorem otherCornerTetrahedron_fullDim : Other.CornerTetrahedron.polyhedron.FullDim := by
  rw [OtherCornerTetrahedronDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk OtherCornerTetrahedronDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
