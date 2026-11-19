import Polyhedra.Johnson.TriangularHebesphenorotunda.Definition
import Modules.Check.Leaf.FullDim

set_option linter.style.longLine false

/-!
# The fixture `johnson/triangular-hebesphenorotunda` is full-dimensional

The points of `Johnson.TriangularHebesphenorotunda.polyhedron` times `32` as exact values in `ZSqrt 5`, exported
by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Johnson.TriangularHebesphenorotunda.polyhedron`.
-/

namespace Nieuwland.Polyhedra.JohnsonTriangularHebesphenorotundaDim

open Check

/-- The points of `Johnson.TriangularHebesphenorotunda.polyhedron` times `32`. -/
def points : List (V3 (ZSqrt 5)) := [
    ⟨⟨15, 11⟩, ⟨-1, -5⟩, ⟨-1, -5⟩⟩,
    ⟨⟨-1, -5⟩, ⟨15, 11⟩, ⟨-1, -5⟩⟩,
    ⟨⟨-1, -5⟩, ⟨-1, -5⟩, ⟨15, 11⟩⟩,
    ⟨⟨23, 3⟩, ⟨7, 3⟩, ⟨-17, -5⟩⟩,
    ⟨⟨-17, -5⟩, ⟨23, 3⟩, ⟨7, 3⟩⟩,
    ⟨⟨7, 3⟩, ⟨-17, -5⟩, ⟨23, 3⟩⟩,
    ⟨⟨7, 3⟩, ⟨-17, -5⟩, ⟨7, -13⟩⟩,
    ⟨⟨7, -13⟩, ⟨7, 3⟩, ⟨-17, -5⟩⟩,
    ⟨⟨-17, -5⟩, ⟨7, -13⟩, ⟨7, 3⟩⟩,
    ⟨⟨15, -5⟩, ⟨-9, 3⟩, ⟨-9, -13⟩⟩,
    ⟨⟨-9, -13⟩, ⟨15, -5⟩, ⟨-9, 3⟩⟩,
    ⟨⟨-9, 3⟩, ⟨-9, -13⟩, ⟨15, -5⟩⟩,
    ⟨⟨23, 3⟩, ⟨7, 3⟩, ⟨15, -5⟩⟩,
    ⟨⟨15, -5⟩, ⟨23, 3⟩, ⟨7, 3⟩⟩,
    ⟨⟨7, 3⟩, ⟨15, -5⟩, ⟨23, 3⟩⟩,
    ⟨⟨23, 3⟩, ⟨-9, -13⟩, ⟨15, -5⟩⟩,
    ⟨⟨15, -5⟩, ⟨23, 3⟩, ⟨-9, -13⟩⟩,
    ⟨⟨-9, -13⟩, ⟨15, -5⟩, ⟨23, 3⟩⟩]

theorem span_ok : spanOk points 0 1 2 6 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 32 : ℝ) • Exact.reV (⟨⟨15, 11⟩, ⟨-1, -5⟩, ⟨-1, -5⟩⟩ : V3 (ZSqrt 5)) = ![15/32
    + 11/32 * √5, -1/32 - 5/32 * √5, -1/32 - 5/32 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt1 : (1 / 32 : ℝ) • Exact.reV (⟨⟨-1, -5⟩, ⟨15, 11⟩, ⟨-1, -5⟩⟩ : V3 (ZSqrt 5)) = ![-1/32
    - 5/32 * √5, 15/32 + 11/32 * √5, -1/32 - 5/32 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt2 : (1 / 32 : ℝ) • Exact.reV (⟨⟨-1, -5⟩, ⟨-1, -5⟩, ⟨15, 11⟩⟩ : V3 (ZSqrt 5)) = ![-1/32
    - 5/32 * √5, -1/32 - 5/32 * √5, 15/32 + 11/32 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt3 : (1 / 32 : ℝ) • Exact.reV (⟨⟨23, 3⟩, ⟨7, 3⟩, ⟨-17, -5⟩⟩ : V3 (ZSqrt 5)) = ![23/32 +
    3/32 * √5, 7/32 + 3/32 * √5, -17/32 - 5/32 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt4 : (1 / 32 : ℝ) • Exact.reV (⟨⟨-17, -5⟩, ⟨23, 3⟩, ⟨7, 3⟩⟩ : V3 (ZSqrt 5)) = ![-17/32
    - 5/32 * √5, 23/32 + 3/32 * √5, 7/32 + 3/32 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt5 : (1 / 32 : ℝ) • Exact.reV (⟨⟨7, 3⟩, ⟨-17, -5⟩, ⟨23, 3⟩⟩ : V3 (ZSqrt 5)) = ![7/32 +
    3/32 * √5, -17/32 - 5/32 * √5, 23/32 + 3/32 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt6 : (1 / 32 : ℝ) • Exact.reV (⟨⟨7, 3⟩, ⟨-17, -5⟩, ⟨7, -13⟩⟩ : V3 (ZSqrt 5)) = ![7/32 +
    3/32 * √5, -17/32 - 5/32 * √5, 7/32 - 13/32 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt7 : (1 / 32 : ℝ) • Exact.reV (⟨⟨7, -13⟩, ⟨7, 3⟩, ⟨-17, -5⟩⟩ : V3 (ZSqrt 5)) = ![7/32 -
    13/32 * √5, 7/32 + 3/32 * √5, -17/32 - 5/32 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt8 : (1 / 32 : ℝ) • Exact.reV (⟨⟨-17, -5⟩, ⟨7, -13⟩, ⟨7, 3⟩⟩ : V3 (ZSqrt 5)) = ![-17/32
    - 5/32 * √5, 7/32 - 13/32 * √5, 7/32 + 3/32 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt9 : (1 / 32 : ℝ) • Exact.reV (⟨⟨15, -5⟩, ⟨-9, 3⟩, ⟨-9, -13⟩⟩ : V3 (ZSqrt 5)) = ![15/32
    - 5/32 * √5, -9/32 + 3/32 * √5, -9/32 - 13/32 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt10 : (1 / 32 : ℝ) • Exact.reV (⟨⟨-9, -13⟩, ⟨15, -5⟩, ⟨-9, 3⟩⟩ : V3 (ZSqrt 5)) =
    ![-9/32 - 13/32 * √5, 15/32 - 5/32 * √5, -9/32 + 3/32 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt11 : (1 / 32 : ℝ) • Exact.reV (⟨⟨-9, 3⟩, ⟨-9, -13⟩, ⟨15, -5⟩⟩ : V3 (ZSqrt 5)) =
    ![-9/32 + 3/32 * √5, -9/32 - 13/32 * √5, 15/32 - 5/32 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt12 : (1 / 32 : ℝ) • Exact.reV (⟨⟨23, 3⟩, ⟨7, 3⟩, ⟨15, -5⟩⟩ : V3 (ZSqrt 5)) = ![23/32 +
    3/32 * √5, 7/32 + 3/32 * √5, 15/32 - 5/32 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt13 : (1 / 32 : ℝ) • Exact.reV (⟨⟨15, -5⟩, ⟨23, 3⟩, ⟨7, 3⟩⟩ : V3 (ZSqrt 5)) = ![15/32 -
    5/32 * √5, 23/32 + 3/32 * √5, 7/32 + 3/32 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt14 : (1 / 32 : ℝ) • Exact.reV (⟨⟨7, 3⟩, ⟨15, -5⟩, ⟨23, 3⟩⟩ : V3 (ZSqrt 5)) = ![7/32 +
    3/32 * √5, 15/32 - 5/32 * √5, 23/32 + 3/32 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt15 : (1 / 32 : ℝ) • Exact.reV (⟨⟨23, 3⟩, ⟨-9, -13⟩, ⟨15, -5⟩⟩ : V3 (ZSqrt 5)) =
    ![23/32 + 3/32 * √5, -9/32 - 13/32 * √5, 15/32 - 5/32 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt16 : (1 / 32 : ℝ) • Exact.reV (⟨⟨15, -5⟩, ⟨23, 3⟩, ⟨-9, -13⟩⟩ : V3 (ZSqrt 5)) =
    ![15/32 - 5/32 * √5, 23/32 + 3/32 * √5, -9/32 - 13/32 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt17 : (1 / 32 : ℝ) • Exact.reV (⟨⟨-9, -13⟩, ⟨15, -5⟩, ⟨23, 3⟩⟩ : V3 (ZSqrt 5)) =
    ![-9/32 - 13/32 * √5, 15/32 - 5/32 * √5, 23/32 + 3/32 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem eq_smul : Johnson.TriangularHebesphenorotunda.polyhedron = (Polyhedron.ofPoints points).smul (1 / 32) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17]

end Nieuwland.Polyhedra.JohnsonTriangularHebesphenorotundaDim

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/triangular-hebesphenorotunda` is full-dimensional.** -/
theorem johnsonTriangularHebesphenorotunda_fullDim : Johnson.TriangularHebesphenorotunda.polyhedron.FullDim := by
  rw [JohnsonTriangularHebesphenorotundaDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk JohnsonTriangularHebesphenorotundaDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
