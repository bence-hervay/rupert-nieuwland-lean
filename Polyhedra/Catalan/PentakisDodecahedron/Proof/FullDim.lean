import Polyhedra.Catalan.PentakisDodecahedron.Definition
import Modules.Check.Leaf.FullDim

set_option linter.style.longLine false

/-!
# The fixture `catalan/pentakis-dodecahedron` is full-dimensional

The points of `Catalan.PentakisDodecahedron.polyhedron` times `76` as exact values in `ZSqrt 5`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Catalan.PentakisDodecahedron.polyhedron`.
-/

namespace Nieuwland.Polyhedra.CatalanPentakisDodecahedronDim

open Check

/-- The points of `Catalan.PentakisDodecahedron.polyhedron` times `76`. -/
def points : List (V3 (ZSqrt 5)) := [
    ⟨⟨0, 0⟩, ⟨-57, 57⟩, ⟨57, 57⟩⟩,
    ⟨⟨0, 0⟩, ⟨-57, 57⟩, ⟨-57, -57⟩⟩,
    ⟨⟨0, 0⟩, ⟨57, -57⟩, ⟨57, 57⟩⟩,
    ⟨⟨0, 0⟩, ⟨57, -57⟩, ⟨-57, -57⟩⟩,
    ⟨⟨57, 57⟩, ⟨0, 0⟩, ⟨-57, 57⟩⟩,
    ⟨⟨57, 57⟩, ⟨0, 0⟩, ⟨57, -57⟩⟩,
    ⟨⟨-57, -57⟩, ⟨0, 0⟩, ⟨-57, 57⟩⟩,
    ⟨⟨-57, -57⟩, ⟨0, 0⟩, ⟨57, -57⟩⟩,
    ⟨⟨-57, 57⟩, ⟨57, 57⟩, ⟨0, 0⟩⟩,
    ⟨⟨-57, 57⟩, ⟨-57, -57⟩, ⟨0, 0⟩⟩,
    ⟨⟨57, -57⟩, ⟨57, 57⟩, ⟨0, 0⟩⟩,
    ⟨⟨57, -57⟩, ⟨-57, -57⟩, ⟨0, 0⟩⟩,
    ⟨⟨81, 9⟩, ⟨0, 0⟩, ⟨63, 45⟩⟩,
    ⟨⟨81, 9⟩, ⟨0, 0⟩, ⟨-63, -45⟩⟩,
    ⟨⟨-81, -9⟩, ⟨0, 0⟩, ⟨63, 45⟩⟩,
    ⟨⟨-81, -9⟩, ⟨0, 0⟩, ⟨-63, -45⟩⟩,
    ⟨⟨63, 45⟩, ⟨81, 9⟩, ⟨0, 0⟩⟩,
    ⟨⟨63, 45⟩, ⟨-81, -9⟩, ⟨0, 0⟩⟩,
    ⟨⟨-63, -45⟩, ⟨81, 9⟩, ⟨0, 0⟩⟩,
    ⟨⟨-63, -45⟩, ⟨-81, -9⟩, ⟨0, 0⟩⟩,
    ⟨⟨0, 0⟩, ⟨63, 45⟩, ⟨81, 9⟩⟩,
    ⟨⟨0, 0⟩, ⟨63, 45⟩, ⟨-81, -9⟩⟩,
    ⟨⟨0, 0⟩, ⟨-63, -45⟩, ⟨81, 9⟩⟩,
    ⟨⟨0, 0⟩, ⟨-63, -45⟩, ⟨-81, -9⟩⟩,
    ⟨⟨114, 0⟩, ⟨114, 0⟩, ⟨114, 0⟩⟩,
    ⟨⟨114, 0⟩, ⟨114, 0⟩, ⟨-114, 0⟩⟩,
    ⟨⟨114, 0⟩, ⟨-114, 0⟩, ⟨114, 0⟩⟩,
    ⟨⟨114, 0⟩, ⟨-114, 0⟩, ⟨-114, 0⟩⟩,
    ⟨⟨-114, 0⟩, ⟨114, 0⟩, ⟨114, 0⟩⟩,
    ⟨⟨-114, 0⟩, ⟨114, 0⟩, ⟨-114, 0⟩⟩,
    ⟨⟨-114, 0⟩, ⟨-114, 0⟩, ⟨114, 0⟩⟩,
    ⟨⟨-114, 0⟩, ⟨-114, 0⟩, ⟨-114, 0⟩⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 76 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨-57, 57⟩, ⟨57, 57⟩⟩ : V3 (ZSqrt 5)) = ![0,
    -3/4 + 3/4 * √5, 3/4 + 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt1 : (1 / 76 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨-57, 57⟩, ⟨-57, -57⟩⟩ : V3 (ZSqrt 5)) = ![0,
    -3/4 + 3/4 * √5, -3/4 - 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt2 : (1 / 76 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨57, -57⟩, ⟨57, 57⟩⟩ : V3 (ZSqrt 5)) = ![0, 3/4
    - 3/4 * √5, 3/4 + 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt3 : (1 / 76 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨57, -57⟩, ⟨-57, -57⟩⟩ : V3 (ZSqrt 5)) = ![0,
    3/4 - 3/4 * √5, -3/4 - 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt4 : (1 / 76 : ℝ) • Exact.reV (⟨⟨57, 57⟩, ⟨0, 0⟩, ⟨-57, 57⟩⟩ : V3 (ZSqrt 5)) = ![3/4 +
    3/4 * √5, 0, -3/4 + 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt5 : (1 / 76 : ℝ) • Exact.reV (⟨⟨57, 57⟩, ⟨0, 0⟩, ⟨57, -57⟩⟩ : V3 (ZSqrt 5)) = ![3/4 +
    3/4 * √5, 0, 3/4 - 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt6 : (1 / 76 : ℝ) • Exact.reV (⟨⟨-57, -57⟩, ⟨0, 0⟩, ⟨-57, 57⟩⟩ : V3 (ZSqrt 5)) = ![-3/4
    - 3/4 * √5, 0, -3/4 + 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt7 : (1 / 76 : ℝ) • Exact.reV (⟨⟨-57, -57⟩, ⟨0, 0⟩, ⟨57, -57⟩⟩ : V3 (ZSqrt 5)) = ![-3/4
    - 3/4 * √5, 0, 3/4 - 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt8 : (1 / 76 : ℝ) • Exact.reV (⟨⟨-57, 57⟩, ⟨57, 57⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![-3/4 +
    3/4 * √5, 3/4 + 3/4 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt9 : (1 / 76 : ℝ) • Exact.reV (⟨⟨-57, 57⟩, ⟨-57, -57⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![-3/4
    + 3/4 * √5, -3/4 - 3/4 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt10 : (1 / 76 : ℝ) • Exact.reV (⟨⟨57, -57⟩, ⟨57, 57⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![3/4 -
    3/4 * √5, 3/4 + 3/4 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt11 : (1 / 76 : ℝ) • Exact.reV (⟨⟨57, -57⟩, ⟨-57, -57⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![3/4
    - 3/4 * √5, -3/4 - 3/4 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt12 : (1 / 76 : ℝ) • Exact.reV (⟨⟨81, 9⟩, ⟨0, 0⟩, ⟨63, 45⟩⟩ : V3 (ZSqrt 5)) = ![81/76 +
    9/76 * √5, 0, 63/76 + 45/76 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt13 : (1 / 76 : ℝ) • Exact.reV (⟨⟨81, 9⟩, ⟨0, 0⟩, ⟨-63, -45⟩⟩ : V3 (ZSqrt 5)) = ![81/76
    + 9/76 * √5, 0, -63/76 - 45/76 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt14 : (1 / 76 : ℝ) • Exact.reV (⟨⟨-81, -9⟩, ⟨0, 0⟩, ⟨63, 45⟩⟩ : V3 (ZSqrt 5)) =
    ![-81/76 - 9/76 * √5, 0, 63/76 + 45/76 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt15 : (1 / 76 : ℝ) • Exact.reV (⟨⟨-81, -9⟩, ⟨0, 0⟩, ⟨-63, -45⟩⟩ : V3 (ZSqrt 5)) =
    ![-81/76 - 9/76 * √5, 0, -63/76 - 45/76 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt16 : (1 / 76 : ℝ) • Exact.reV (⟨⟨63, 45⟩, ⟨81, 9⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![63/76 +
    45/76 * √5, 81/76 + 9/76 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt17 : (1 / 76 : ℝ) • Exact.reV (⟨⟨63, 45⟩, ⟨-81, -9⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) = ![63/76
    + 45/76 * √5, -81/76 - 9/76 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt18 : (1 / 76 : ℝ) • Exact.reV (⟨⟨-63, -45⟩, ⟨81, 9⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) =
    ![-63/76 - 45/76 * √5, 81/76 + 9/76 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt19 : (1 / 76 : ℝ) • Exact.reV (⟨⟨-63, -45⟩, ⟨-81, -9⟩, ⟨0, 0⟩⟩ : V3 (ZSqrt 5)) =
    ![-63/76 - 45/76 * √5, -81/76 - 9/76 * √5, 0] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt20 : (1 / 76 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨63, 45⟩, ⟨81, 9⟩⟩ : V3 (ZSqrt 5)) = ![0,
    63/76 + 45/76 * √5, 81/76 + 9/76 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt21 : (1 / 76 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨63, 45⟩, ⟨-81, -9⟩⟩ : V3 (ZSqrt 5)) = ![0,
    63/76 + 45/76 * √5, -81/76 - 9/76 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt22 : (1 / 76 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨-63, -45⟩, ⟨81, 9⟩⟩ : V3 (ZSqrt 5)) = ![0,
    -63/76 - 45/76 * √5, 81/76 + 9/76 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt23 : (1 / 76 : ℝ) • Exact.reV (⟨⟨0, 0⟩, ⟨-63, -45⟩, ⟨-81, -9⟩⟩ : V3 (ZSqrt 5)) = ![0,
    -63/76 - 45/76 * √5, -81/76 - 9/76 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt24 : (1 / 76 : ℝ) • Exact.reV (⟨⟨114, 0⟩, ⟨114, 0⟩, ⟨114, 0⟩⟩ : V3 (ZSqrt 5)) = ![3/2,
    3/2, 3/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt25 : (1 / 76 : ℝ) • Exact.reV (⟨⟨114, 0⟩, ⟨114, 0⟩, ⟨-114, 0⟩⟩ : V3 (ZSqrt 5)) =
    ![3/2, 3/2, -3/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt26 : (1 / 76 : ℝ) • Exact.reV (⟨⟨114, 0⟩, ⟨-114, 0⟩, ⟨114, 0⟩⟩ : V3 (ZSqrt 5)) =
    ![3/2, -3/2, 3/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt27 : (1 / 76 : ℝ) • Exact.reV (⟨⟨114, 0⟩, ⟨-114, 0⟩, ⟨-114, 0⟩⟩ : V3 (ZSqrt 5)) =
    ![3/2, -3/2, -3/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt28 : (1 / 76 : ℝ) • Exact.reV (⟨⟨-114, 0⟩, ⟨114, 0⟩, ⟨114, 0⟩⟩ : V3 (ZSqrt 5)) =
    ![-3/2, 3/2, 3/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt29 : (1 / 76 : ℝ) • Exact.reV (⟨⟨-114, 0⟩, ⟨114, 0⟩, ⟨-114, 0⟩⟩ : V3 (ZSqrt 5)) =
    ![-3/2, 3/2, -3/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt30 : (1 / 76 : ℝ) • Exact.reV (⟨⟨-114, 0⟩, ⟨-114, 0⟩, ⟨114, 0⟩⟩ : V3 (ZSqrt 5)) =
    ![-3/2, -3/2, 3/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt31 : (1 / 76 : ℝ) • Exact.reV (⟨⟨-114, 0⟩, ⟨-114, 0⟩, ⟨-114, 0⟩⟩ : V3 (ZSqrt 5)) =
    ![-3/2, -3/2, -3/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem eq_smul : Catalan.PentakisDodecahedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 76) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17, pt18, pt19, pt20, pt21, pt22, pt23, pt24,
    pt25, pt26, pt27, pt28, pt29, pt30, pt31]

end Nieuwland.Polyhedra.CatalanPentakisDodecahedronDim

namespace Nieuwland.Polyhedra

/-- **The fixture `catalan/pentakis-dodecahedron` is full-dimensional.** -/
theorem catalanPentakisDodecahedron_fullDim : Catalan.PentakisDodecahedron.polyhedron.FullDim := by
  rw [CatalanPentakisDodecahedronDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk CatalanPentakisDodecahedronDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
