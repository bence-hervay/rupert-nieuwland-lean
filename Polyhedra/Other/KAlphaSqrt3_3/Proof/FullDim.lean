import Polyhedra.Other.KAlphaSqrt3_3.Definition
import Modules.Check.Leaf.FullDim

/-!
# The fixture `k-alpha/sqrt3-3` is full-dimensional

The points of `Other.KAlphaSqrt3_3.polyhedron` times `3` as exact values in `ZSqrt 3`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Other.KAlphaSqrt3_3.polyhedron`.
-/

namespace Nieuwland.Polyhedra.KAlphaSqrt3_3Dim

open Check

/-- The points of `Other.KAlphaSqrt3_3.polyhedron` times `3`. -/
def points : List (V3 (ZSqrt 3)) := [
    ⟨⟨3, 0⟩, ⟨3, 0⟩, ⟨3, 0⟩⟩,
    ⟨⟨3, 0⟩, ⟨-3, 0⟩, ⟨-3, 0⟩⟩,
    ⟨⟨-3, 0⟩, ⟨3, 0⟩, ⟨-3, 0⟩⟩,
    ⟨⟨-3, 0⟩, ⟨-3, 0⟩, ⟨3, 0⟩⟩,
    ⟨⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩⟩,
    ⟨⟨0, -1⟩, ⟨0, 1⟩, ⟨0, 1⟩⟩,
    ⟨⟨0, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩⟩,
    ⟨⟨0, 1⟩, ⟨0, 1⟩, ⟨0, -1⟩⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 3 : ℝ) • Exact.reV (⟨⟨3, 0⟩, ⟨3, 0⟩, ⟨3, 0⟩⟩ : V3 (ZSqrt 3)) = ![1, 1, 1] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt1 : (1 / 3 : ℝ) • Exact.reV (⟨⟨3, 0⟩, ⟨-3, 0⟩, ⟨-3, 0⟩⟩ : V3 (ZSqrt 3)) = ![1, -1, -1]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt2 : (1 / 3 : ℝ) • Exact.reV (⟨⟨-3, 0⟩, ⟨3, 0⟩, ⟨-3, 0⟩⟩ : V3 (ZSqrt 3)) = ![-1, 1, -1]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt3 : (1 / 3 : ℝ) • Exact.reV (⟨⟨-3, 0⟩, ⟨-3, 0⟩, ⟨3, 0⟩⟩ : V3 (ZSqrt 3)) = ![-1, -1, 1]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt4 : (1 / 3 : ℝ) • Exact.reV (⟨⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩⟩ : V3 (ZSqrt 3)) = ![-(1/3 *
    √3), -(1/3 * √3), -(1/3 * √3)] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt5 : (1 / 3 : ℝ) • Exact.reV (⟨⟨0, -1⟩, ⟨0, 1⟩, ⟨0, 1⟩⟩ : V3 (ZSqrt 3)) = ![-(1/3 *
    √3), 1/3 * √3, 1/3 * √3] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt6 : (1 / 3 : ℝ) • Exact.reV (⟨⟨0, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩⟩ : V3 (ZSqrt 3)) = ![1/3 * √3,
    -(1/3 * √3), 1/3 * √3] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt7 : (1 / 3 : ℝ) • Exact.reV (⟨⟨0, 1⟩, ⟨0, 1⟩, ⟨0, -1⟩⟩ : V3 (ZSqrt 3)) = ![1/3 * √3,
    1/3 * √3, -(1/3 * √3)] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem eq_smul : Other.KAlphaSqrt3_3.polyhedron = (Polyhedron.ofPoints points).smul (1 / 3) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7]

end Nieuwland.Polyhedra.KAlphaSqrt3_3Dim

namespace Nieuwland.Polyhedra

/-- **The fixture `k-alpha/sqrt3-3` is full-dimensional.** -/
theorem kAlphaSqrt3_3_fullDim : Other.KAlphaSqrt3_3.polyhedron.FullDim := by
  rw [KAlphaSqrt3_3Dim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk KAlphaSqrt3_3Dim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
