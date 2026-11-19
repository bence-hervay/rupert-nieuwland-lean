import Polyhedra.Catalan.RhombicDodecahedron.Definition
import Modules.Check.Leaf.FullDim

set_option linter.style.longLine false

/-!
# The fixture `catalan/rhombic-dodecahedron` is full-dimensional

The points of `Catalan.RhombicDodecahedron.polyhedron` times `1` as exact values in `ℤ`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Catalan.RhombicDodecahedron.polyhedron`.
-/

namespace Nieuwland.Polyhedra.CatalanRhombicDodecahedronDim

open Check

/-- The points of `Catalan.RhombicDodecahedron.polyhedron` times `1`. -/
def points : List (V3 ℤ) := [
    ⟨0, 0, 2⟩,
    ⟨0, 0, -2⟩,
    ⟨2, 0, 0⟩,
    ⟨-2, 0, 0⟩,
    ⟨0, 2, 0⟩,
    ⟨0, -2, 0⟩,
    ⟨1, 1, 1⟩,
    ⟨1, 1, -1⟩,
    ⟨1, -1, 1⟩,
    ⟨1, -1, -1⟩,
    ⟨-1, 1, 1⟩,
    ⟨-1, 1, -1⟩,
    ⟨-1, -1, 1⟩,
    ⟨-1, -1, -1⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 1 : ℝ) • Exact.reV (⟨0, 0, 2⟩ : V3 ℤ) = ![0, 0, 2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt1 : (1 / 1 : ℝ) • Exact.reV (⟨0, 0, -2⟩ : V3 ℤ) = ![0, 0, -2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt2 : (1 / 1 : ℝ) • Exact.reV (⟨2, 0, 0⟩ : V3 ℤ) = ![2, 0, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt3 : (1 / 1 : ℝ) • Exact.reV (⟨-2, 0, 0⟩ : V3 ℤ) = ![-2, 0, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt4 : (1 / 1 : ℝ) • Exact.reV (⟨0, 2, 0⟩ : V3 ℤ) = ![0, 2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt5 : (1 / 1 : ℝ) • Exact.reV (⟨0, -2, 0⟩ : V3 ℤ) = ![0, -2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt6 : (1 / 1 : ℝ) • Exact.reV (⟨1, 1, 1⟩ : V3 ℤ) = ![1, 1, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt7 : (1 / 1 : ℝ) • Exact.reV (⟨1, 1, -1⟩ : V3 ℤ) = ![1, 1, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt8 : (1 / 1 : ℝ) • Exact.reV (⟨1, -1, 1⟩ : V3 ℤ) = ![1, -1, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt9 : (1 / 1 : ℝ) • Exact.reV (⟨1, -1, -1⟩ : V3 ℤ) = ![1, -1, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt10 : (1 / 1 : ℝ) • Exact.reV (⟨-1, 1, 1⟩ : V3 ℤ) = ![-1, 1, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt11 : (1 / 1 : ℝ) • Exact.reV (⟨-1, 1, -1⟩ : V3 ℤ) = ![-1, 1, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt12 : (1 / 1 : ℝ) • Exact.reV (⟨-1, -1, 1⟩ : V3 ℤ) = ![-1, -1, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt13 : (1 / 1 : ℝ) • Exact.reV (⟨-1, -1, -1⟩ : V3 ℤ) = ![-1, -1, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem eq_smul : Catalan.RhombicDodecahedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 1) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13]

end Nieuwland.Polyhedra.CatalanRhombicDodecahedronDim

namespace Nieuwland.Polyhedra

/-- **The fixture `catalan/rhombic-dodecahedron` is full-dimensional.** -/
theorem catalanRhombicDodecahedron_fullDim : Catalan.RhombicDodecahedron.polyhedron.FullDim := by
  rw [CatalanRhombicDodecahedronDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk CatalanRhombicDodecahedronDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
