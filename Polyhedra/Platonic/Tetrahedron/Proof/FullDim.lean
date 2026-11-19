import Polyhedra.Platonic.Tetrahedron.Definition
import Modules.Check.Leaf.FullDim

/-!
# The fixture `platonic/tetrahedron` is full-dimensional

The points of `Platonic.Tetrahedron.polyhedron` times `1` as exact values in `ℤ`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Platonic.Tetrahedron.polyhedron`.
-/

namespace Nieuwland.Polyhedra.PlatonicTetrahedronDim

open Check

/-- The points of `Platonic.Tetrahedron.polyhedron` times `1`. -/
def points : List (V3 ℤ) := [
    ⟨1, -1, 1⟩,
    ⟨1, 1, -1⟩,
    ⟨-1, 1, 1⟩,
    ⟨-1, -1, -1⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 1 : ℝ) • Exact.reV (⟨1, -1, 1⟩ : V3 ℤ) = ![1, -1, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt1 : (1 / 1 : ℝ) • Exact.reV (⟨1, 1, -1⟩ : V3 ℤ) = ![1, 1, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt2 : (1 / 1 : ℝ) • Exact.reV (⟨-1, 1, 1⟩ : V3 ℤ) = ![-1, 1, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt3 : (1 / 1 : ℝ) • Exact.reV (⟨-1, -1, -1⟩ : V3 ℤ) = ![-1, -1, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem eq_smul : Platonic.Tetrahedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 1) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3]

end Nieuwland.Polyhedra.PlatonicTetrahedronDim

namespace Nieuwland.Polyhedra

/-- **The fixture `platonic/tetrahedron` is full-dimensional.** -/
theorem platonicTetrahedron_fullDim : Platonic.Tetrahedron.polyhedron.FullDim := by
  rw [PlatonicTetrahedronDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk PlatonicTetrahedronDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
