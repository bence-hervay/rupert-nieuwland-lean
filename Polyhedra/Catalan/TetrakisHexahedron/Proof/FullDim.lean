import Polyhedra.Catalan.TetrakisHexahedron.Definition
import Modules.Check.Leaf.FullDim

/-!
# The fixture `catalan/tetrakis-hexahedron` is full-dimensional

The points of `Catalan.TetrakisHexahedron.polyhedron` times `2` as exact values in `ℤ`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Catalan.TetrakisHexahedron.polyhedron`.
-/

namespace Nieuwland.Polyhedra.CatalanTetrakisHexahedronDim

open Check

/-- The points of `Catalan.TetrakisHexahedron.polyhedron` times `2`. -/
def points : List (V3 ℤ) := [
    ⟨0, 0, 3⟩,
    ⟨0, 0, -3⟩,
    ⟨3, 0, 0⟩,
    ⟨-3, 0, 0⟩,
    ⟨0, 3, 0⟩,
    ⟨0, -3, 0⟩,
    ⟨2, 2, 2⟩,
    ⟨2, 2, -2⟩,
    ⟨2, -2, 2⟩,
    ⟨2, -2, -2⟩,
    ⟨-2, 2, 2⟩,
    ⟨-2, 2, -2⟩,
    ⟨-2, -2, 2⟩,
    ⟨-2, -2, -2⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 2 : ℝ) • Exact.reV (⟨0, 0, 3⟩ : V3 ℤ) = ![0, 0, 3/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt1 : (1 / 2 : ℝ) • Exact.reV (⟨0, 0, -3⟩ : V3 ℤ) = ![0, 0, -3/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt2 : (1 / 2 : ℝ) • Exact.reV (⟨3, 0, 0⟩ : V3 ℤ) = ![3/2, 0, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt3 : (1 / 2 : ℝ) • Exact.reV (⟨-3, 0, 0⟩ : V3 ℤ) = ![-3/2, 0, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt4 : (1 / 2 : ℝ) • Exact.reV (⟨0, 3, 0⟩ : V3 ℤ) = ![0, 3/2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt5 : (1 / 2 : ℝ) • Exact.reV (⟨0, -3, 0⟩ : V3 ℤ) = ![0, -3/2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt6 : (1 / 2 : ℝ) • Exact.reV (⟨2, 2, 2⟩ : V3 ℤ) = ![1, 1, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt7 : (1 / 2 : ℝ) • Exact.reV (⟨2, 2, -2⟩ : V3 ℤ) = ![1, 1, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt8 : (1 / 2 : ℝ) • Exact.reV (⟨2, -2, 2⟩ : V3 ℤ) = ![1, -1, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt9 : (1 / 2 : ℝ) • Exact.reV (⟨2, -2, -2⟩ : V3 ℤ) = ![1, -1, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt10 : (1 / 2 : ℝ) • Exact.reV (⟨-2, 2, 2⟩ : V3 ℤ) = ![-1, 1, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt11 : (1 / 2 : ℝ) • Exact.reV (⟨-2, 2, -2⟩ : V3 ℤ) = ![-1, 1, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt12 : (1 / 2 : ℝ) • Exact.reV (⟨-2, -2, 2⟩ : V3 ℤ) = ![-1, -1, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt13 : (1 / 2 : ℝ) • Exact.reV (⟨-2, -2, -2⟩ : V3 ℤ) = ![-1, -1, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem eq_smul : Catalan.TetrakisHexahedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 2) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13]

end Nieuwland.Polyhedra.CatalanTetrakisHexahedronDim

namespace Nieuwland.Polyhedra

/-- **The fixture `catalan/tetrakis-hexahedron` is full-dimensional.** -/
theorem catalanTetrakisHexahedron_fullDim : Catalan.TetrakisHexahedron.polyhedron.FullDim := by
  rw [CatalanTetrakisHexahedronDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk CatalanTetrakisHexahedronDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
