import Polyhedra.Archimedean.TruncatedTetrahedron.Definition
import Modules.Check.Leaf.FullDim

set_option linter.style.longLine false

/-!
# The fixture `archimedean/truncated-tetrahedron` is full-dimensional

The points of `Archimedean.TruncatedTetrahedron.polyhedron` times `1` as exact values in `ℤ`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Archimedean.TruncatedTetrahedron.polyhedron`.
-/

namespace Nieuwland.Polyhedra.ArchimedeanTruncatedTetrahedronDim

open Check

/-- The points of `Archimedean.TruncatedTetrahedron.polyhedron` times `1`. -/
def points : List (V3 ℤ) := [
    ⟨1, -1, 3⟩,
    ⟨1, 1, -3⟩,
    ⟨-1, 1, 3⟩,
    ⟨-1, -1, -3⟩,
    ⟨3, -1, 1⟩,
    ⟨3, 1, -1⟩,
    ⟨-3, 1, 1⟩,
    ⟨-3, -1, -1⟩,
    ⟨1, -3, 1⟩,
    ⟨1, 3, -1⟩,
    ⟨-1, 3, 1⟩,
    ⟨-1, -3, -1⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 1 : ℝ) • Exact.reV (⟨1, -1, 3⟩ : V3 ℤ) = ![1, -1, 3] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt1 : (1 / 1 : ℝ) • Exact.reV (⟨1, 1, -3⟩ : V3 ℤ) = ![1, 1, -3] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt2 : (1 / 1 : ℝ) • Exact.reV (⟨-1, 1, 3⟩ : V3 ℤ) = ![-1, 1, 3] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt3 : (1 / 1 : ℝ) • Exact.reV (⟨-1, -1, -3⟩ : V3 ℤ) = ![-1, -1, -3] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt4 : (1 / 1 : ℝ) • Exact.reV (⟨3, -1, 1⟩ : V3 ℤ) = ![3, -1, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt5 : (1 / 1 : ℝ) • Exact.reV (⟨3, 1, -1⟩ : V3 ℤ) = ![3, 1, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt6 : (1 / 1 : ℝ) • Exact.reV (⟨-3, 1, 1⟩ : V3 ℤ) = ![-3, 1, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt7 : (1 / 1 : ℝ) • Exact.reV (⟨-3, -1, -1⟩ : V3 ℤ) = ![-3, -1, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt8 : (1 / 1 : ℝ) • Exact.reV (⟨1, -3, 1⟩ : V3 ℤ) = ![1, -3, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt9 : (1 / 1 : ℝ) • Exact.reV (⟨1, 3, -1⟩ : V3 ℤ) = ![1, 3, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt10 : (1 / 1 : ℝ) • Exact.reV (⟨-1, 3, 1⟩ : V3 ℤ) = ![-1, 3, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt11 : (1 / 1 : ℝ) • Exact.reV (⟨-1, -3, -1⟩ : V3 ℤ) = ![-1, -3, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem eq_smul : Archimedean.TruncatedTetrahedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 1) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11]

end Nieuwland.Polyhedra.ArchimedeanTruncatedTetrahedronDim

namespace Nieuwland.Polyhedra

/-- **The fixture `archimedean/truncated-tetrahedron` is full-dimensional.** -/
theorem archimedeanTruncatedTetrahedron_fullDim : Archimedean.TruncatedTetrahedron.polyhedron.FullDim := by
  rw [ArchimedeanTruncatedTetrahedronDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk ArchimedeanTruncatedTetrahedronDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
