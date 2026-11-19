import Polyhedra.Archimedean.TruncatedOctahedron.Definition
import Modules.Check.Leaf.FullDim

set_option linter.style.longLine false

/-!
# The fixture `archimedean/truncated-octahedron` is full-dimensional

The points of `Archimedean.TruncatedOctahedron.polyhedron` times `1` as exact values in `ℤ`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Archimedean.TruncatedOctahedron.polyhedron`.
-/

namespace Nieuwland.Polyhedra.ArchimedeanTruncatedOctahedronDim

open Check

/-- The points of `Archimedean.TruncatedOctahedron.polyhedron` times `1`. -/
def points : List (V3 ℤ) := [
    ⟨1, 0, 2⟩,
    ⟨1, 0, -2⟩,
    ⟨-1, 0, 2⟩,
    ⟨-1, 0, -2⟩,
    ⟨2, 1, 0⟩,
    ⟨2, -1, 0⟩,
    ⟨-2, 1, 0⟩,
    ⟨-2, -1, 0⟩,
    ⟨0, 2, 1⟩,
    ⟨0, 2, -1⟩,
    ⟨0, -2, 1⟩,
    ⟨0, -2, -1⟩,
    ⟨0, 1, 2⟩,
    ⟨0, 1, -2⟩,
    ⟨0, -1, 2⟩,
    ⟨0, -1, -2⟩,
    ⟨2, 0, 1⟩,
    ⟨2, 0, -1⟩,
    ⟨-2, 0, 1⟩,
    ⟨-2, 0, -1⟩,
    ⟨1, 2, 0⟩,
    ⟨1, -2, 0⟩,
    ⟨-1, 2, 0⟩,
    ⟨-1, -2, 0⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 1 : ℝ) • Exact.reV (⟨1, 0, 2⟩ : V3 ℤ) = ![1, 0, 2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt1 : (1 / 1 : ℝ) • Exact.reV (⟨1, 0, -2⟩ : V3 ℤ) = ![1, 0, -2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt2 : (1 / 1 : ℝ) • Exact.reV (⟨-1, 0, 2⟩ : V3 ℤ) = ![-1, 0, 2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt3 : (1 / 1 : ℝ) • Exact.reV (⟨-1, 0, -2⟩ : V3 ℤ) = ![-1, 0, -2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt4 : (1 / 1 : ℝ) • Exact.reV (⟨2, 1, 0⟩ : V3 ℤ) = ![2, 1, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt5 : (1 / 1 : ℝ) • Exact.reV (⟨2, -1, 0⟩ : V3 ℤ) = ![2, -1, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt6 : (1 / 1 : ℝ) • Exact.reV (⟨-2, 1, 0⟩ : V3 ℤ) = ![-2, 1, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt7 : (1 / 1 : ℝ) • Exact.reV (⟨-2, -1, 0⟩ : V3 ℤ) = ![-2, -1, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt8 : (1 / 1 : ℝ) • Exact.reV (⟨0, 2, 1⟩ : V3 ℤ) = ![0, 2, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt9 : (1 / 1 : ℝ) • Exact.reV (⟨0, 2, -1⟩ : V3 ℤ) = ![0, 2, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt10 : (1 / 1 : ℝ) • Exact.reV (⟨0, -2, 1⟩ : V3 ℤ) = ![0, -2, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt11 : (1 / 1 : ℝ) • Exact.reV (⟨0, -2, -1⟩ : V3 ℤ) = ![0, -2, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt12 : (1 / 1 : ℝ) • Exact.reV (⟨0, 1, 2⟩ : V3 ℤ) = ![0, 1, 2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt13 : (1 / 1 : ℝ) • Exact.reV (⟨0, 1, -2⟩ : V3 ℤ) = ![0, 1, -2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt14 : (1 / 1 : ℝ) • Exact.reV (⟨0, -1, 2⟩ : V3 ℤ) = ![0, -1, 2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt15 : (1 / 1 : ℝ) • Exact.reV (⟨0, -1, -2⟩ : V3 ℤ) = ![0, -1, -2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt16 : (1 / 1 : ℝ) • Exact.reV (⟨2, 0, 1⟩ : V3 ℤ) = ![2, 0, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt17 : (1 / 1 : ℝ) • Exact.reV (⟨2, 0, -1⟩ : V3 ℤ) = ![2, 0, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt18 : (1 / 1 : ℝ) • Exact.reV (⟨-2, 0, 1⟩ : V3 ℤ) = ![-2, 0, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt19 : (1 / 1 : ℝ) • Exact.reV (⟨-2, 0, -1⟩ : V3 ℤ) = ![-2, 0, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt20 : (1 / 1 : ℝ) • Exact.reV (⟨1, 2, 0⟩ : V3 ℤ) = ![1, 2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt21 : (1 / 1 : ℝ) • Exact.reV (⟨1, -2, 0⟩ : V3 ℤ) = ![1, -2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt22 : (1 / 1 : ℝ) • Exact.reV (⟨-1, 2, 0⟩ : V3 ℤ) = ![-1, 2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt23 : (1 / 1 : ℝ) • Exact.reV (⟨-1, -2, 0⟩ : V3 ℤ) = ![-1, -2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem eq_smul : Archimedean.TruncatedOctahedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 1) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17, pt18, pt19, pt20, pt21, pt22, pt23]

end Nieuwland.Polyhedra.ArchimedeanTruncatedOctahedronDim

namespace Nieuwland.Polyhedra

/-- **The fixture `archimedean/truncated-octahedron` is full-dimensional.** -/
theorem archimedeanTruncatedOctahedron_fullDim : Archimedean.TruncatedOctahedron.polyhedron.FullDim := by
  rw [ArchimedeanTruncatedOctahedronDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk ArchimedeanTruncatedOctahedronDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
