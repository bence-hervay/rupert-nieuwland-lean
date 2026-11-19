import Polyhedra.Catalan.TriakisTetrahedron.Definition
import Modules.Check.Leaf.FullDim

/-!
# The fixture `catalan/triakis-tetrahedron` is full-dimensional

The points of `Catalan.TriakisTetrahedron.polyhedron` times `3` as exact values in `ℤ`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Catalan.TriakisTetrahedron.polyhedron`.
-/

namespace Nieuwland.Polyhedra.CatalanTriakisTetrahedronDim

open Check

/-- The points of `Catalan.TriakisTetrahedron.polyhedron` times `3`. -/
def points : List (V3 ℤ) := [
    ⟨5, 5, 5⟩,
    ⟨5, -5, -5⟩,
    ⟨-5, -5, 5⟩,
    ⟨-5, 5, -5⟩,
    ⟨3, -3, 3⟩,
    ⟨3, 3, -3⟩,
    ⟨-3, 3, 3⟩,
    ⟨-3, -3, -3⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 3 : ℝ) • Exact.reV (⟨5, 5, 5⟩ : V3 ℤ) = ![5/3, 5/3, 5/3] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt1 : (1 / 3 : ℝ) • Exact.reV (⟨5, -5, -5⟩ : V3 ℤ) = ![5/3, -5/3, -5/3] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt2 : (1 / 3 : ℝ) • Exact.reV (⟨-5, -5, 5⟩ : V3 ℤ) = ![-5/3, -5/3, 5/3] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt3 : (1 / 3 : ℝ) • Exact.reV (⟨-5, 5, -5⟩ : V3 ℤ) = ![-5/3, 5/3, -5/3] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt4 : (1 / 3 : ℝ) • Exact.reV (⟨3, -3, 3⟩ : V3 ℤ) = ![1, -1, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt5 : (1 / 3 : ℝ) • Exact.reV (⟨3, 3, -3⟩ : V3 ℤ) = ![1, 1, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt6 : (1 / 3 : ℝ) • Exact.reV (⟨-3, 3, 3⟩ : V3 ℤ) = ![-1, 1, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt7 : (1 / 3 : ℝ) • Exact.reV (⟨-3, -3, -3⟩ : V3 ℤ) = ![-1, -1, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem eq_smul : Catalan.TriakisTetrahedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 3) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7]

end Nieuwland.Polyhedra.CatalanTriakisTetrahedronDim

namespace Nieuwland.Polyhedra

/-- **The fixture `catalan/triakis-tetrahedron` is full-dimensional.** -/
theorem catalanTriakisTetrahedron_fullDim : Catalan.TriakisTetrahedron.polyhedron.FullDim := by
  rw [CatalanTriakisTetrahedronDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk CatalanTriakisTetrahedronDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
