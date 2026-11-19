import Polyhedra.Johnson.TriangularOrthobicupola.Definition
import Modules.Check.Leaf.FullDim

set_option linter.style.longLine false

/-!
# The fixture `johnson/triangular-orthobicupola` is full-dimensional

The points of `Johnson.TriangularOrthobicupola.polyhedron` times `1` as exact values in `ℤ`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Johnson.TriangularOrthobicupola.polyhedron`.
-/

namespace Nieuwland.Polyhedra.JohnsonTriangularOrthobicupolaDim

open Check

/-- The points of `Johnson.TriangularOrthobicupola.polyhedron` times `1`. -/
def points : List (V3 ℤ) := [
    ⟨-1, -1, -4⟩,
    ⟨-1, -4, -1⟩,
    ⟨-4, -1, -1⟩,
    ⟨3, 0, 3⟩,
    ⟨3, 0, -3⟩,
    ⟨-3, 0, 3⟩,
    ⟨3, 3, 0⟩,
    ⟨3, -3, 0⟩,
    ⟨-3, 3, 0⟩,
    ⟨0, 3, 3⟩,
    ⟨0, 3, -3⟩,
    ⟨0, -3, 3⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 1 : ℝ) • Exact.reV (⟨-1, -1, -4⟩ : V3 ℤ) = ![-1, -1, -4] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt1 : (1 / 1 : ℝ) • Exact.reV (⟨-1, -4, -1⟩ : V3 ℤ) = ![-1, -4, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt2 : (1 / 1 : ℝ) • Exact.reV (⟨-4, -1, -1⟩ : V3 ℤ) = ![-4, -1, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt3 : (1 / 1 : ℝ) • Exact.reV (⟨3, 0, 3⟩ : V3 ℤ) = ![3, 0, 3] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt4 : (1 / 1 : ℝ) • Exact.reV (⟨3, 0, -3⟩ : V3 ℤ) = ![3, 0, -3] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt5 : (1 / 1 : ℝ) • Exact.reV (⟨-3, 0, 3⟩ : V3 ℤ) = ![-3, 0, 3] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt6 : (1 / 1 : ℝ) • Exact.reV (⟨3, 3, 0⟩ : V3 ℤ) = ![3, 3, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt7 : (1 / 1 : ℝ) • Exact.reV (⟨3, -3, 0⟩ : V3 ℤ) = ![3, -3, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt8 : (1 / 1 : ℝ) • Exact.reV (⟨-3, 3, 0⟩ : V3 ℤ) = ![-3, 3, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt9 : (1 / 1 : ℝ) • Exact.reV (⟨0, 3, 3⟩ : V3 ℤ) = ![0, 3, 3] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt10 : (1 / 1 : ℝ) • Exact.reV (⟨0, 3, -3⟩ : V3 ℤ) = ![0, 3, -3] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt11 : (1 / 1 : ℝ) • Exact.reV (⟨0, -3, 3⟩ : V3 ℤ) = ![0, -3, 3] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem eq_smul : Johnson.TriangularOrthobicupola.polyhedron = (Polyhedron.ofPoints points).smul (1 / 1) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11]

end Nieuwland.Polyhedra.JohnsonTriangularOrthobicupolaDim

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/triangular-orthobicupola` is full-dimensional.** -/
theorem johnsonTriangularOrthobicupola_fullDim : Johnson.TriangularOrthobicupola.polyhedron.FullDim := by
  rw [JohnsonTriangularOrthobicupolaDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk JohnsonTriangularOrthobicupolaDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
