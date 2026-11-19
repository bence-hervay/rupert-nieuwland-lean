import Polyhedra.Catalan.TriakisOctahedron.Definition
import Modules.Check.Leaf.FullDim

/-!
# The fixture `catalan/triakis-octahedron` is full-dimensional

The points of `Catalan.TriakisOctahedron.polyhedron` times `1` as exact values in `ZSqrt 2`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Catalan.TriakisOctahedron.polyhedron`.
-/

namespace Nieuwland.Polyhedra.CatalanTriakisOctahedronDim

open Check

/-- The points of `Catalan.TriakisOctahedron.polyhedron` times `1`. -/
def points : List (V3 (ZSqrt 2)) := [
    ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩⟩,
    ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩⟩,
    ⟨⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩,
    ⟨⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩,
    ⟨⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩⟩,
    ⟨⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩⟩,
    ⟨⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩⟩,
    ⟨⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩⟩,
    ⟨⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩⟩,
    ⟨⟨1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩⟩,
    ⟨⟨-1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩⟩,
    ⟨⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩⟩,
    ⟨⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩⟩,
    ⟨⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 1 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩⟩ : V3 (ZSqrt 2)) = ![0, 0, 1 +
    √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt1 : (1 / 1 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩⟩ : V3 (ZSqrt 2)) = ![0, 0, -1 -
    √2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt2 : (1 / 1 : ℝ) • Exact.reV (⟨⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 2)) = ![1 + √2, 0,
    0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt3 : (1 / 1 : ℝ) • Exact.reV (⟨⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 2)) = ![-1 - √2,
    0, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt4 : (1 / 1 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 2)) = ![0, 1 + √2,
    0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt5 : (1 / 1 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 2)) = ![0, -1 -
    √2, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt6 : (1 / 1 : ℝ) • Exact.reV (⟨⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩⟩ : V3 (ZSqrt 2)) = ![1, 1, 1] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt7 : (1 / 1 : ℝ) • Exact.reV (⟨⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩⟩ : V3 (ZSqrt 2)) = ![1, 1, -1]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt8 : (1 / 1 : ℝ) • Exact.reV (⟨⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩⟩ : V3 (ZSqrt 2)) = ![1, -1, 1]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt9 : (1 / 1 : ℝ) • Exact.reV (⟨⟨1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩⟩ : V3 (ZSqrt 2)) = ![1, -1, -1]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt10 : (1 / 1 : ℝ) • Exact.reV (⟨⟨-1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩⟩ : V3 (ZSqrt 2)) = ![-1, 1, 1]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt11 : (1 / 1 : ℝ) • Exact.reV (⟨⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩⟩ : V3 (ZSqrt 2)) = ![-1, 1,
    -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt12 : (1 / 1 : ℝ) • Exact.reV (⟨⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩⟩ : V3 (ZSqrt 2)) = ![-1, -1,
    1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt13 : (1 / 1 : ℝ) • Exact.reV (⟨⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩⟩ : V3 (ZSqrt 2)) = ![-1, -1,
    -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem eq_smul : Catalan.TriakisOctahedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 1) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13]

end Nieuwland.Polyhedra.CatalanTriakisOctahedronDim

namespace Nieuwland.Polyhedra

/-- **The fixture `catalan/triakis-octahedron` is full-dimensional.** -/
theorem catalanTriakisOctahedron_fullDim : Catalan.TriakisOctahedron.polyhedron.FullDim := by
  rw [CatalanTriakisOctahedronDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk CatalanTriakisOctahedronDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
