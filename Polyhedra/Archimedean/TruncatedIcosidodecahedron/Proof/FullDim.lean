import Polyhedra.Archimedean.TruncatedIcosidodecahedron.Definition
import Modules.Check.Leaf.FullDim

set_option linter.style.longLine false

/-!
# The fixture `archimedean/truncated-icosidodecahedron` is full-dimensional

The points of `Archimedean.TruncatedIcosidodecahedron.polyhedron` times `4` as exact values in `ZSqrt 5`,
exported by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`,
checked by the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`),
and scaled back (`eq_smul`, `Polyhedron.FullDim.smul`), so is
`Archimedean.TruncatedIcosidodecahedron.polyhedron`.
-/

namespace Nieuwland.Polyhedra.ArchimedeanTruncatedIcosidodecahedronDim

open Check

/-- The points of `Archimedean.TruncatedIcosidodecahedron.polyhedron` times `4`. -/
def points : List (V3 (ZSqrt 5)) := [
    ⟨⟨2, 0⟩, ⟨2, 0⟩, ⟨6, 4⟩⟩,
    ⟨⟨2, 0⟩, ⟨2, 0⟩, ⟨-6, -4⟩⟩,
    ⟨⟨2, 0⟩, ⟨-2, 0⟩, ⟨6, 4⟩⟩,
    ⟨⟨2, 0⟩, ⟨-2, 0⟩, ⟨-6, -4⟩⟩,
    ⟨⟨-2, 0⟩, ⟨2, 0⟩, ⟨6, 4⟩⟩,
    ⟨⟨-2, 0⟩, ⟨2, 0⟩, ⟨-6, -4⟩⟩,
    ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨6, 4⟩⟩,
    ⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-6, -4⟩⟩,
    ⟨⟨6, 4⟩, ⟨2, 0⟩, ⟨2, 0⟩⟩,
    ⟨⟨6, 4⟩, ⟨2, 0⟩, ⟨-2, 0⟩⟩,
    ⟨⟨6, 4⟩, ⟨-2, 0⟩, ⟨2, 0⟩⟩,
    ⟨⟨6, 4⟩, ⟨-2, 0⟩, ⟨-2, 0⟩⟩,
    ⟨⟨-6, -4⟩, ⟨2, 0⟩, ⟨2, 0⟩⟩,
    ⟨⟨-6, -4⟩, ⟨2, 0⟩, ⟨-2, 0⟩⟩,
    ⟨⟨-6, -4⟩, ⟨-2, 0⟩, ⟨2, 0⟩⟩,
    ⟨⟨-6, -4⟩, ⟨-2, 0⟩, ⟨-2, 0⟩⟩,
    ⟨⟨2, 0⟩, ⟨6, 4⟩, ⟨2, 0⟩⟩,
    ⟨⟨2, 0⟩, ⟨6, 4⟩, ⟨-2, 0⟩⟩,
    ⟨⟨2, 0⟩, ⟨-6, -4⟩, ⟨2, 0⟩⟩,
    ⟨⟨2, 0⟩, ⟨-6, -4⟩, ⟨-2, 0⟩⟩,
    ⟨⟨-2, 0⟩, ⟨6, 4⟩, ⟨2, 0⟩⟩,
    ⟨⟨-2, 0⟩, ⟨6, 4⟩, ⟨-2, 0⟩⟩,
    ⟨⟨-2, 0⟩, ⟨-6, -4⟩, ⟨2, 0⟩⟩,
    ⟨⟨-2, 0⟩, ⟨-6, -4⟩, ⟨-2, 0⟩⟩,
    ⟨⟨4, 0⟩, ⟨3, 1⟩, ⟨7, 3⟩⟩,
    ⟨⟨4, 0⟩, ⟨3, 1⟩, ⟨-7, -3⟩⟩,
    ⟨⟨4, 0⟩, ⟨-3, -1⟩, ⟨7, 3⟩⟩,
    ⟨⟨4, 0⟩, ⟨-3, -1⟩, ⟨-7, -3⟩⟩,
    ⟨⟨-4, 0⟩, ⟨3, 1⟩, ⟨7, 3⟩⟩,
    ⟨⟨-4, 0⟩, ⟨3, 1⟩, ⟨-7, -3⟩⟩,
    ⟨⟨-4, 0⟩, ⟨-3, -1⟩, ⟨7, 3⟩⟩,
    ⟨⟨-4, 0⟩, ⟨-3, -1⟩, ⟨-7, -3⟩⟩,
    ⟨⟨7, 3⟩, ⟨4, 0⟩, ⟨3, 1⟩⟩,
    ⟨⟨7, 3⟩, ⟨4, 0⟩, ⟨-3, -1⟩⟩,
    ⟨⟨7, 3⟩, ⟨-4, 0⟩, ⟨3, 1⟩⟩,
    ⟨⟨7, 3⟩, ⟨-4, 0⟩, ⟨-3, -1⟩⟩,
    ⟨⟨-7, -3⟩, ⟨4, 0⟩, ⟨3, 1⟩⟩,
    ⟨⟨-7, -3⟩, ⟨4, 0⟩, ⟨-3, -1⟩⟩,
    ⟨⟨-7, -3⟩, ⟨-4, 0⟩, ⟨3, 1⟩⟩,
    ⟨⟨-7, -3⟩, ⟨-4, 0⟩, ⟨-3, -1⟩⟩,
    ⟨⟨3, 1⟩, ⟨7, 3⟩, ⟨4, 0⟩⟩,
    ⟨⟨3, 1⟩, ⟨7, 3⟩, ⟨-4, 0⟩⟩,
    ⟨⟨3, 1⟩, ⟨-7, -3⟩, ⟨4, 0⟩⟩,
    ⟨⟨3, 1⟩, ⟨-7, -3⟩, ⟨-4, 0⟩⟩,
    ⟨⟨-3, -1⟩, ⟨7, 3⟩, ⟨4, 0⟩⟩,
    ⟨⟨-3, -1⟩, ⟨7, 3⟩, ⟨-4, 0⟩⟩,
    ⟨⟨-3, -1⟩, ⟨-7, -3⟩, ⟨4, 0⟩⟩,
    ⟨⟨-3, -1⟩, ⟨-7, -3⟩, ⟨-4, 0⟩⟩,
    ⟨⟨2, 0⟩, ⟨4, 2⟩, ⟨8, 2⟩⟩,
    ⟨⟨2, 0⟩, ⟨4, 2⟩, ⟨-8, -2⟩⟩,
    ⟨⟨2, 0⟩, ⟨-4, -2⟩, ⟨8, 2⟩⟩,
    ⟨⟨2, 0⟩, ⟨-4, -2⟩, ⟨-8, -2⟩⟩,
    ⟨⟨-2, 0⟩, ⟨4, 2⟩, ⟨8, 2⟩⟩,
    ⟨⟨-2, 0⟩, ⟨4, 2⟩, ⟨-8, -2⟩⟩,
    ⟨⟨-2, 0⟩, ⟨-4, -2⟩, ⟨8, 2⟩⟩,
    ⟨⟨-2, 0⟩, ⟨-4, -2⟩, ⟨-8, -2⟩⟩,
    ⟨⟨8, 2⟩, ⟨2, 0⟩, ⟨4, 2⟩⟩,
    ⟨⟨8, 2⟩, ⟨2, 0⟩, ⟨-4, -2⟩⟩,
    ⟨⟨8, 2⟩, ⟨-2, 0⟩, ⟨4, 2⟩⟩,
    ⟨⟨8, 2⟩, ⟨-2, 0⟩, ⟨-4, -2⟩⟩,
    ⟨⟨-8, -2⟩, ⟨2, 0⟩, ⟨4, 2⟩⟩,
    ⟨⟨-8, -2⟩, ⟨2, 0⟩, ⟨-4, -2⟩⟩,
    ⟨⟨-8, -2⟩, ⟨-2, 0⟩, ⟨4, 2⟩⟩,
    ⟨⟨-8, -2⟩, ⟨-2, 0⟩, ⟨-4, -2⟩⟩,
    ⟨⟨4, 2⟩, ⟨8, 2⟩, ⟨2, 0⟩⟩,
    ⟨⟨4, 2⟩, ⟨8, 2⟩, ⟨-2, 0⟩⟩,
    ⟨⟨4, 2⟩, ⟨-8, -2⟩, ⟨2, 0⟩⟩,
    ⟨⟨4, 2⟩, ⟨-8, -2⟩, ⟨-2, 0⟩⟩,
    ⟨⟨-4, -2⟩, ⟨8, 2⟩, ⟨2, 0⟩⟩,
    ⟨⟨-4, -2⟩, ⟨8, 2⟩, ⟨-2, 0⟩⟩,
    ⟨⟨-4, -2⟩, ⟨-8, -2⟩, ⟨2, 0⟩⟩,
    ⟨⟨-4, -2⟩, ⟨-8, -2⟩, ⟨-2, 0⟩⟩,
    ⟨⟨5, 1⟩, ⟨2, 2⟩, ⟨5, 3⟩⟩,
    ⟨⟨5, 1⟩, ⟨2, 2⟩, ⟨-5, -3⟩⟩,
    ⟨⟨5, 1⟩, ⟨-2, -2⟩, ⟨5, 3⟩⟩,
    ⟨⟨5, 1⟩, ⟨-2, -2⟩, ⟨-5, -3⟩⟩,
    ⟨⟨-5, -1⟩, ⟨2, 2⟩, ⟨5, 3⟩⟩,
    ⟨⟨-5, -1⟩, ⟨2, 2⟩, ⟨-5, -3⟩⟩,
    ⟨⟨-5, -1⟩, ⟨-2, -2⟩, ⟨5, 3⟩⟩,
    ⟨⟨-5, -1⟩, ⟨-2, -2⟩, ⟨-5, -3⟩⟩,
    ⟨⟨5, 3⟩, ⟨5, 1⟩, ⟨2, 2⟩⟩,
    ⟨⟨5, 3⟩, ⟨5, 1⟩, ⟨-2, -2⟩⟩,
    ⟨⟨5, 3⟩, ⟨-5, -1⟩, ⟨2, 2⟩⟩,
    ⟨⟨5, 3⟩, ⟨-5, -1⟩, ⟨-2, -2⟩⟩,
    ⟨⟨-5, -3⟩, ⟨5, 1⟩, ⟨2, 2⟩⟩,
    ⟨⟨-5, -3⟩, ⟨5, 1⟩, ⟨-2, -2⟩⟩,
    ⟨⟨-5, -3⟩, ⟨-5, -1⟩, ⟨2, 2⟩⟩,
    ⟨⟨-5, -3⟩, ⟨-5, -1⟩, ⟨-2, -2⟩⟩,
    ⟨⟨2, 2⟩, ⟨5, 3⟩, ⟨5, 1⟩⟩,
    ⟨⟨2, 2⟩, ⟨5, 3⟩, ⟨-5, -1⟩⟩,
    ⟨⟨2, 2⟩, ⟨-5, -3⟩, ⟨5, 1⟩⟩,
    ⟨⟨2, 2⟩, ⟨-5, -3⟩, ⟨-5, -1⟩⟩,
    ⟨⟨-2, -2⟩, ⟨5, 3⟩, ⟨5, 1⟩⟩,
    ⟨⟨-2, -2⟩, ⟨5, 3⟩, ⟨-5, -1⟩⟩,
    ⟨⟨-2, -2⟩, ⟨-5, -3⟩, ⟨5, 1⟩⟩,
    ⟨⟨-2, -2⟩, ⟨-5, -3⟩, ⟨-5, -1⟩⟩,
    ⟨⟨3, 1⟩, ⟨3, 3⟩, ⟨6, 2⟩⟩,
    ⟨⟨3, 1⟩, ⟨3, 3⟩, ⟨-6, -2⟩⟩,
    ⟨⟨3, 1⟩, ⟨-3, -3⟩, ⟨6, 2⟩⟩,
    ⟨⟨3, 1⟩, ⟨-3, -3⟩, ⟨-6, -2⟩⟩,
    ⟨⟨-3, -1⟩, ⟨3, 3⟩, ⟨6, 2⟩⟩,
    ⟨⟨-3, -1⟩, ⟨3, 3⟩, ⟨-6, -2⟩⟩,
    ⟨⟨-3, -1⟩, ⟨-3, -3⟩, ⟨6, 2⟩⟩,
    ⟨⟨-3, -1⟩, ⟨-3, -3⟩, ⟨-6, -2⟩⟩,
    ⟨⟨6, 2⟩, ⟨3, 1⟩, ⟨3, 3⟩⟩,
    ⟨⟨6, 2⟩, ⟨3, 1⟩, ⟨-3, -3⟩⟩,
    ⟨⟨6, 2⟩, ⟨-3, -1⟩, ⟨3, 3⟩⟩,
    ⟨⟨6, 2⟩, ⟨-3, -1⟩, ⟨-3, -3⟩⟩,
    ⟨⟨-6, -2⟩, ⟨3, 1⟩, ⟨3, 3⟩⟩,
    ⟨⟨-6, -2⟩, ⟨3, 1⟩, ⟨-3, -3⟩⟩,
    ⟨⟨-6, -2⟩, ⟨-3, -1⟩, ⟨3, 3⟩⟩,
    ⟨⟨-6, -2⟩, ⟨-3, -1⟩, ⟨-3, -3⟩⟩,
    ⟨⟨3, 3⟩, ⟨6, 2⟩, ⟨3, 1⟩⟩,
    ⟨⟨3, 3⟩, ⟨6, 2⟩, ⟨-3, -1⟩⟩,
    ⟨⟨3, 3⟩, ⟨-6, -2⟩, ⟨3, 1⟩⟩,
    ⟨⟨3, 3⟩, ⟨-6, -2⟩, ⟨-3, -1⟩⟩,
    ⟨⟨-3, -3⟩, ⟨6, 2⟩, ⟨3, 1⟩⟩,
    ⟨⟨-3, -3⟩, ⟨6, 2⟩, ⟨-3, -1⟩⟩,
    ⟨⟨-3, -3⟩, ⟨-6, -2⟩, ⟨3, 1⟩⟩,
    ⟨⟨-3, -3⟩, ⟨-6, -2⟩, ⟨-3, -1⟩⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 4 : ℝ) • Exact.reV (⟨⟨2, 0⟩, ⟨2, 0⟩, ⟨6, 4⟩⟩ : V3 (ZSqrt 5)) = ![1/2, 1/2,
    3/2 + √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt1 : (1 / 4 : ℝ) • Exact.reV (⟨⟨2, 0⟩, ⟨2, 0⟩, ⟨-6, -4⟩⟩ : V3 (ZSqrt 5)) = ![1/2, 1/2,
    -3/2 - √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt2 : (1 / 4 : ℝ) • Exact.reV (⟨⟨2, 0⟩, ⟨-2, 0⟩, ⟨6, 4⟩⟩ : V3 (ZSqrt 5)) = ![1/2, -1/2,
    3/2 + √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt3 : (1 / 4 : ℝ) • Exact.reV (⟨⟨2, 0⟩, ⟨-2, 0⟩, ⟨-6, -4⟩⟩ : V3 (ZSqrt 5)) = ![1/2,
    -1/2, -3/2 - √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt4 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-2, 0⟩, ⟨2, 0⟩, ⟨6, 4⟩⟩ : V3 (ZSqrt 5)) = ![-1/2, 1/2,
    3/2 + √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt5 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-2, 0⟩, ⟨2, 0⟩, ⟨-6, -4⟩⟩ : V3 (ZSqrt 5)) = ![-1/2,
    1/2, -3/2 - √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt6 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨6, 4⟩⟩ : V3 (ZSqrt 5)) = ![-1/2,
    -1/2, 3/2 + √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt7 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-6, -4⟩⟩ : V3 (ZSqrt 5)) = ![-1/2,
    -1/2, -3/2 - √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt8 : (1 / 4 : ℝ) • Exact.reV (⟨⟨6, 4⟩, ⟨2, 0⟩, ⟨2, 0⟩⟩ : V3 (ZSqrt 5)) = ![3/2 + √5,
    1/2, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt9 : (1 / 4 : ℝ) • Exact.reV (⟨⟨6, 4⟩, ⟨2, 0⟩, ⟨-2, 0⟩⟩ : V3 (ZSqrt 5)) = ![3/2 + √5,
    1/2, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt10 : (1 / 4 : ℝ) • Exact.reV (⟨⟨6, 4⟩, ⟨-2, 0⟩, ⟨2, 0⟩⟩ : V3 (ZSqrt 5)) = ![3/2 + √5,
    -1/2, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt11 : (1 / 4 : ℝ) • Exact.reV (⟨⟨6, 4⟩, ⟨-2, 0⟩, ⟨-2, 0⟩⟩ : V3 (ZSqrt 5)) = ![3/2 + √5,
    -1/2, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt12 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-6, -4⟩, ⟨2, 0⟩, ⟨2, 0⟩⟩ : V3 (ZSqrt 5)) = ![-3/2 -
    √5, 1/2, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt13 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-6, -4⟩, ⟨2, 0⟩, ⟨-2, 0⟩⟩ : V3 (ZSqrt 5)) = ![-3/2 -
    √5, 1/2, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt14 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-6, -4⟩, ⟨-2, 0⟩, ⟨2, 0⟩⟩ : V3 (ZSqrt 5)) = ![-3/2 -
    √5, -1/2, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt15 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-6, -4⟩, ⟨-2, 0⟩, ⟨-2, 0⟩⟩ : V3 (ZSqrt 5)) = ![-3/2 -
    √5, -1/2, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt16 : (1 / 4 : ℝ) • Exact.reV (⟨⟨2, 0⟩, ⟨6, 4⟩, ⟨2, 0⟩⟩ : V3 (ZSqrt 5)) = ![1/2, 3/2 +
    √5, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt17 : (1 / 4 : ℝ) • Exact.reV (⟨⟨2, 0⟩, ⟨6, 4⟩, ⟨-2, 0⟩⟩ : V3 (ZSqrt 5)) = ![1/2, 3/2 +
    √5, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt18 : (1 / 4 : ℝ) • Exact.reV (⟨⟨2, 0⟩, ⟨-6, -4⟩, ⟨2, 0⟩⟩ : V3 (ZSqrt 5)) = ![1/2, -3/2
    - √5, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt19 : (1 / 4 : ℝ) • Exact.reV (⟨⟨2, 0⟩, ⟨-6, -4⟩, ⟨-2, 0⟩⟩ : V3 (ZSqrt 5)) = ![1/2,
    -3/2 - √5, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt20 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-2, 0⟩, ⟨6, 4⟩, ⟨2, 0⟩⟩ : V3 (ZSqrt 5)) = ![-1/2, 3/2
    + √5, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt21 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-2, 0⟩, ⟨6, 4⟩, ⟨-2, 0⟩⟩ : V3 (ZSqrt 5)) = ![-1/2, 3/2
    + √5, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt22 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-2, 0⟩, ⟨-6, -4⟩, ⟨2, 0⟩⟩ : V3 (ZSqrt 5)) = ![-1/2,
    -3/2 - √5, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt23 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-2, 0⟩, ⟨-6, -4⟩, ⟨-2, 0⟩⟩ : V3 (ZSqrt 5)) = ![-1/2,
    -3/2 - √5, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt24 : (1 / 4 : ℝ) • Exact.reV (⟨⟨4, 0⟩, ⟨3, 1⟩, ⟨7, 3⟩⟩ : V3 (ZSqrt 5)) = ![1, 3/4 +
    1/4 * √5, 7/4 + 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt25 : (1 / 4 : ℝ) • Exact.reV (⟨⟨4, 0⟩, ⟨3, 1⟩, ⟨-7, -3⟩⟩ : V3 (ZSqrt 5)) = ![1, 3/4 +
    1/4 * √5, -7/4 - 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt26 : (1 / 4 : ℝ) • Exact.reV (⟨⟨4, 0⟩, ⟨-3, -1⟩, ⟨7, 3⟩⟩ : V3 (ZSqrt 5)) = ![1, -3/4 -
    1/4 * √5, 7/4 + 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt27 : (1 / 4 : ℝ) • Exact.reV (⟨⟨4, 0⟩, ⟨-3, -1⟩, ⟨-7, -3⟩⟩ : V3 (ZSqrt 5)) = ![1, -3/4
    - 1/4 * √5, -7/4 - 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt28 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-4, 0⟩, ⟨3, 1⟩, ⟨7, 3⟩⟩ : V3 (ZSqrt 5)) = ![-1, 3/4 +
    1/4 * √5, 7/4 + 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt29 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-4, 0⟩, ⟨3, 1⟩, ⟨-7, -3⟩⟩ : V3 (ZSqrt 5)) = ![-1, 3/4
    + 1/4 * √5, -7/4 - 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt30 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-4, 0⟩, ⟨-3, -1⟩, ⟨7, 3⟩⟩ : V3 (ZSqrt 5)) = ![-1, -3/4
    - 1/4 * √5, 7/4 + 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt31 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-4, 0⟩, ⟨-3, -1⟩, ⟨-7, -3⟩⟩ : V3 (ZSqrt 5)) = ![-1,
    -3/4 - 1/4 * √5, -7/4 - 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt32 : (1 / 4 : ℝ) • Exact.reV (⟨⟨7, 3⟩, ⟨4, 0⟩, ⟨3, 1⟩⟩ : V3 (ZSqrt 5)) = ![7/4 + 3/4 *
    √5, 1, 3/4 + 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt33 : (1 / 4 : ℝ) • Exact.reV (⟨⟨7, 3⟩, ⟨4, 0⟩, ⟨-3, -1⟩⟩ : V3 (ZSqrt 5)) = ![7/4 + 3/4
    * √5, 1, -3/4 - 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt34 : (1 / 4 : ℝ) • Exact.reV (⟨⟨7, 3⟩, ⟨-4, 0⟩, ⟨3, 1⟩⟩ : V3 (ZSqrt 5)) = ![7/4 + 3/4
    * √5, -1, 3/4 + 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt35 : (1 / 4 : ℝ) • Exact.reV (⟨⟨7, 3⟩, ⟨-4, 0⟩, ⟨-3, -1⟩⟩ : V3 (ZSqrt 5)) = ![7/4 +
    3/4 * √5, -1, -3/4 - 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt36 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-7, -3⟩, ⟨4, 0⟩, ⟨3, 1⟩⟩ : V3 (ZSqrt 5)) = ![-7/4 -
    3/4 * √5, 1, 3/4 + 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt37 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-7, -3⟩, ⟨4, 0⟩, ⟨-3, -1⟩⟩ : V3 (ZSqrt 5)) = ![-7/4 -
    3/4 * √5, 1, -3/4 - 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt38 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-7, -3⟩, ⟨-4, 0⟩, ⟨3, 1⟩⟩ : V3 (ZSqrt 5)) = ![-7/4 -
    3/4 * √5, -1, 3/4 + 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt39 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-7, -3⟩, ⟨-4, 0⟩, ⟨-3, -1⟩⟩ : V3 (ZSqrt 5)) = ![-7/4 -
    3/4 * √5, -1, -3/4 - 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt40 : (1 / 4 : ℝ) • Exact.reV (⟨⟨3, 1⟩, ⟨7, 3⟩, ⟨4, 0⟩⟩ : V3 (ZSqrt 5)) = ![3/4 + 1/4 *
    √5, 7/4 + 3/4 * √5, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt41 : (1 / 4 : ℝ) • Exact.reV (⟨⟨3, 1⟩, ⟨7, 3⟩, ⟨-4, 0⟩⟩ : V3 (ZSqrt 5)) = ![3/4 + 1/4
    * √5, 7/4 + 3/4 * √5, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt42 : (1 / 4 : ℝ) • Exact.reV (⟨⟨3, 1⟩, ⟨-7, -3⟩, ⟨4, 0⟩⟩ : V3 (ZSqrt 5)) = ![3/4 + 1/4
    * √5, -7/4 - 3/4 * √5, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt43 : (1 / 4 : ℝ) • Exact.reV (⟨⟨3, 1⟩, ⟨-7, -3⟩, ⟨-4, 0⟩⟩ : V3 (ZSqrt 5)) = ![3/4 +
    1/4 * √5, -7/4 - 3/4 * √5, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt44 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-3, -1⟩, ⟨7, 3⟩, ⟨4, 0⟩⟩ : V3 (ZSqrt 5)) = ![-3/4 -
    1/4 * √5, 7/4 + 3/4 * √5, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt45 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-3, -1⟩, ⟨7, 3⟩, ⟨-4, 0⟩⟩ : V3 (ZSqrt 5)) = ![-3/4 -
    1/4 * √5, 7/4 + 3/4 * √5, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt46 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-3, -1⟩, ⟨-7, -3⟩, ⟨4, 0⟩⟩ : V3 (ZSqrt 5)) = ![-3/4 -
    1/4 * √5, -7/4 - 3/4 * √5, 1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt47 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-3, -1⟩, ⟨-7, -3⟩, ⟨-4, 0⟩⟩ : V3 (ZSqrt 5)) = ![-3/4 -
    1/4 * √5, -7/4 - 3/4 * √5, -1] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt48 : (1 / 4 : ℝ) • Exact.reV (⟨⟨2, 0⟩, ⟨4, 2⟩, ⟨8, 2⟩⟩ : V3 (ZSqrt 5)) = ![1/2, 1 +
    1/2 * √5, 2 + 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt49 : (1 / 4 : ℝ) • Exact.reV (⟨⟨2, 0⟩, ⟨4, 2⟩, ⟨-8, -2⟩⟩ : V3 (ZSqrt 5)) = ![1/2, 1 +
    1/2 * √5, -2 - 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt50 : (1 / 4 : ℝ) • Exact.reV (⟨⟨2, 0⟩, ⟨-4, -2⟩, ⟨8, 2⟩⟩ : V3 (ZSqrt 5)) = ![1/2, -1 -
    1/2 * √5, 2 + 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt51 : (1 / 4 : ℝ) • Exact.reV (⟨⟨2, 0⟩, ⟨-4, -2⟩, ⟨-8, -2⟩⟩ : V3 (ZSqrt 5)) = ![1/2, -1
    - 1/2 * √5, -2 - 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt52 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-2, 0⟩, ⟨4, 2⟩, ⟨8, 2⟩⟩ : V3 (ZSqrt 5)) = ![-1/2, 1 +
    1/2 * √5, 2 + 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt53 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-2, 0⟩, ⟨4, 2⟩, ⟨-8, -2⟩⟩ : V3 (ZSqrt 5)) = ![-1/2, 1
    + 1/2 * √5, -2 - 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt54 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-2, 0⟩, ⟨-4, -2⟩, ⟨8, 2⟩⟩ : V3 (ZSqrt 5)) = ![-1/2, -1
    - 1/2 * √5, 2 + 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt55 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-2, 0⟩, ⟨-4, -2⟩, ⟨-8, -2⟩⟩ : V3 (ZSqrt 5)) = ![-1/2,
    -1 - 1/2 * √5, -2 - 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt56 : (1 / 4 : ℝ) • Exact.reV (⟨⟨8, 2⟩, ⟨2, 0⟩, ⟨4, 2⟩⟩ : V3 (ZSqrt 5)) = ![2 + 1/2 *
    √5, 1/2, 1 + 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt57 : (1 / 4 : ℝ) • Exact.reV (⟨⟨8, 2⟩, ⟨2, 0⟩, ⟨-4, -2⟩⟩ : V3 (ZSqrt 5)) = ![2 + 1/2 *
    √5, 1/2, -1 - 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt58 : (1 / 4 : ℝ) • Exact.reV (⟨⟨8, 2⟩, ⟨-2, 0⟩, ⟨4, 2⟩⟩ : V3 (ZSqrt 5)) = ![2 + 1/2 *
    √5, -1/2, 1 + 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt59 : (1 / 4 : ℝ) • Exact.reV (⟨⟨8, 2⟩, ⟨-2, 0⟩, ⟨-4, -2⟩⟩ : V3 (ZSqrt 5)) = ![2 + 1/2
    * √5, -1/2, -1 - 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt60 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-8, -2⟩, ⟨2, 0⟩, ⟨4, 2⟩⟩ : V3 (ZSqrt 5)) = ![-2 - 1/2
    * √5, 1/2, 1 + 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt61 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-8, -2⟩, ⟨2, 0⟩, ⟨-4, -2⟩⟩ : V3 (ZSqrt 5)) = ![-2 -
    1/2 * √5, 1/2, -1 - 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt62 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-8, -2⟩, ⟨-2, 0⟩, ⟨4, 2⟩⟩ : V3 (ZSqrt 5)) = ![-2 - 1/2
    * √5, -1/2, 1 + 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt63 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-8, -2⟩, ⟨-2, 0⟩, ⟨-4, -2⟩⟩ : V3 (ZSqrt 5)) = ![-2 -
    1/2 * √5, -1/2, -1 - 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt64 : (1 / 4 : ℝ) • Exact.reV (⟨⟨4, 2⟩, ⟨8, 2⟩, ⟨2, 0⟩⟩ : V3 (ZSqrt 5)) = ![1 + 1/2 *
    √5, 2 + 1/2 * √5, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt65 : (1 / 4 : ℝ) • Exact.reV (⟨⟨4, 2⟩, ⟨8, 2⟩, ⟨-2, 0⟩⟩ : V3 (ZSqrt 5)) = ![1 + 1/2 *
    √5, 2 + 1/2 * √5, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt66 : (1 / 4 : ℝ) • Exact.reV (⟨⟨4, 2⟩, ⟨-8, -2⟩, ⟨2, 0⟩⟩ : V3 (ZSqrt 5)) = ![1 + 1/2 *
    √5, -2 - 1/2 * √5, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt67 : (1 / 4 : ℝ) • Exact.reV (⟨⟨4, 2⟩, ⟨-8, -2⟩, ⟨-2, 0⟩⟩ : V3 (ZSqrt 5)) = ![1 + 1/2
    * √5, -2 - 1/2 * √5, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt68 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-4, -2⟩, ⟨8, 2⟩, ⟨2, 0⟩⟩ : V3 (ZSqrt 5)) = ![-1 - 1/2
    * √5, 2 + 1/2 * √5, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt69 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-4, -2⟩, ⟨8, 2⟩, ⟨-2, 0⟩⟩ : V3 (ZSqrt 5)) = ![-1 - 1/2
    * √5, 2 + 1/2 * √5, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt70 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-4, -2⟩, ⟨-8, -2⟩, ⟨2, 0⟩⟩ : V3 (ZSqrt 5)) = ![-1 -
    1/2 * √5, -2 - 1/2 * √5, 1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt71 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-4, -2⟩, ⟨-8, -2⟩, ⟨-2, 0⟩⟩ : V3 (ZSqrt 5)) = ![-1 -
    1/2 * √5, -2 - 1/2 * √5, -1/2] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt72 : (1 / 4 : ℝ) • Exact.reV (⟨⟨5, 1⟩, ⟨2, 2⟩, ⟨5, 3⟩⟩ : V3 (ZSqrt 5)) = ![5/4 + 1/4 *
    √5, 1/2 + 1/2 * √5, 5/4 + 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt73 : (1 / 4 : ℝ) • Exact.reV (⟨⟨5, 1⟩, ⟨2, 2⟩, ⟨-5, -3⟩⟩ : V3 (ZSqrt 5)) = ![5/4 + 1/4
    * √5, 1/2 + 1/2 * √5, -5/4 - 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt74 : (1 / 4 : ℝ) • Exact.reV (⟨⟨5, 1⟩, ⟨-2, -2⟩, ⟨5, 3⟩⟩ : V3 (ZSqrt 5)) = ![5/4 + 1/4
    * √5, -1/2 - 1/2 * √5, 5/4 + 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt75 : (1 / 4 : ℝ) • Exact.reV (⟨⟨5, 1⟩, ⟨-2, -2⟩, ⟨-5, -3⟩⟩ : V3 (ZSqrt 5)) = ![5/4 +
    1/4 * √5, -1/2 - 1/2 * √5, -5/4 - 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt76 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-5, -1⟩, ⟨2, 2⟩, ⟨5, 3⟩⟩ : V3 (ZSqrt 5)) = ![-5/4 -
    1/4 * √5, 1/2 + 1/2 * √5, 5/4 + 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt77 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-5, -1⟩, ⟨2, 2⟩, ⟨-5, -3⟩⟩ : V3 (ZSqrt 5)) = ![-5/4 -
    1/4 * √5, 1/2 + 1/2 * √5, -5/4 - 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt78 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-5, -1⟩, ⟨-2, -2⟩, ⟨5, 3⟩⟩ : V3 (ZSqrt 5)) = ![-5/4 -
    1/4 * √5, -1/2 - 1/2 * √5, 5/4 + 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt79 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-5, -1⟩, ⟨-2, -2⟩, ⟨-5, -3⟩⟩ : V3 (ZSqrt 5)) = ![-5/4
    - 1/4 * √5, -1/2 - 1/2 * √5, -5/4 - 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt80 : (1 / 4 : ℝ) • Exact.reV (⟨⟨5, 3⟩, ⟨5, 1⟩, ⟨2, 2⟩⟩ : V3 (ZSqrt 5)) = ![5/4 + 3/4 *
    √5, 5/4 + 1/4 * √5, 1/2 + 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt81 : (1 / 4 : ℝ) • Exact.reV (⟨⟨5, 3⟩, ⟨5, 1⟩, ⟨-2, -2⟩⟩ : V3 (ZSqrt 5)) = ![5/4 + 3/4
    * √5, 5/4 + 1/4 * √5, -1/2 - 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt82 : (1 / 4 : ℝ) • Exact.reV (⟨⟨5, 3⟩, ⟨-5, -1⟩, ⟨2, 2⟩⟩ : V3 (ZSqrt 5)) = ![5/4 + 3/4
    * √5, -5/4 - 1/4 * √5, 1/2 + 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt83 : (1 / 4 : ℝ) • Exact.reV (⟨⟨5, 3⟩, ⟨-5, -1⟩, ⟨-2, -2⟩⟩ : V3 (ZSqrt 5)) = ![5/4 +
    3/4 * √5, -5/4 - 1/4 * √5, -1/2 - 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt84 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-5, -3⟩, ⟨5, 1⟩, ⟨2, 2⟩⟩ : V3 (ZSqrt 5)) = ![-5/4 -
    3/4 * √5, 5/4 + 1/4 * √5, 1/2 + 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt85 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-5, -3⟩, ⟨5, 1⟩, ⟨-2, -2⟩⟩ : V3 (ZSqrt 5)) = ![-5/4 -
    3/4 * √5, 5/4 + 1/4 * √5, -1/2 - 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt86 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-5, -3⟩, ⟨-5, -1⟩, ⟨2, 2⟩⟩ : V3 (ZSqrt 5)) = ![-5/4 -
    3/4 * √5, -5/4 - 1/4 * √5, 1/2 + 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt87 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-5, -3⟩, ⟨-5, -1⟩, ⟨-2, -2⟩⟩ : V3 (ZSqrt 5)) = ![-5/4
    - 3/4 * √5, -5/4 - 1/4 * √5, -1/2 - 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt88 : (1 / 4 : ℝ) • Exact.reV (⟨⟨2, 2⟩, ⟨5, 3⟩, ⟨5, 1⟩⟩ : V3 (ZSqrt 5)) = ![1/2 + 1/2 *
    √5, 5/4 + 3/4 * √5, 5/4 + 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt89 : (1 / 4 : ℝ) • Exact.reV (⟨⟨2, 2⟩, ⟨5, 3⟩, ⟨-5, -1⟩⟩ : V3 (ZSqrt 5)) = ![1/2 + 1/2
    * √5, 5/4 + 3/4 * √5, -5/4 - 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt90 : (1 / 4 : ℝ) • Exact.reV (⟨⟨2, 2⟩, ⟨-5, -3⟩, ⟨5, 1⟩⟩ : V3 (ZSqrt 5)) = ![1/2 + 1/2
    * √5, -5/4 - 3/4 * √5, 5/4 + 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt91 : (1 / 4 : ℝ) • Exact.reV (⟨⟨2, 2⟩, ⟨-5, -3⟩, ⟨-5, -1⟩⟩ : V3 (ZSqrt 5)) = ![1/2 +
    1/2 * √5, -5/4 - 3/4 * √5, -5/4 - 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt92 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-2, -2⟩, ⟨5, 3⟩, ⟨5, 1⟩⟩ : V3 (ZSqrt 5)) = ![-1/2 -
    1/2 * √5, 5/4 + 3/4 * √5, 5/4 + 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt93 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-2, -2⟩, ⟨5, 3⟩, ⟨-5, -1⟩⟩ : V3 (ZSqrt 5)) = ![-1/2 -
    1/2 * √5, 5/4 + 3/4 * √5, -5/4 - 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt94 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-2, -2⟩, ⟨-5, -3⟩, ⟨5, 1⟩⟩ : V3 (ZSqrt 5)) = ![-1/2 -
    1/2 * √5, -5/4 - 3/4 * √5, 5/4 + 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt95 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-2, -2⟩, ⟨-5, -3⟩, ⟨-5, -1⟩⟩ : V3 (ZSqrt 5)) = ![-1/2
    - 1/2 * √5, -5/4 - 3/4 * √5, -5/4 - 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt96 : (1 / 4 : ℝ) • Exact.reV (⟨⟨3, 1⟩, ⟨3, 3⟩, ⟨6, 2⟩⟩ : V3 (ZSqrt 5)) = ![3/4 + 1/4 *
    √5, 3/4 + 3/4 * √5, 3/2 + 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt97 : (1 / 4 : ℝ) • Exact.reV (⟨⟨3, 1⟩, ⟨3, 3⟩, ⟨-6, -2⟩⟩ : V3 (ZSqrt 5)) = ![3/4 + 1/4
    * √5, 3/4 + 3/4 * √5, -3/2 - 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt98 : (1 / 4 : ℝ) • Exact.reV (⟨⟨3, 1⟩, ⟨-3, -3⟩, ⟨6, 2⟩⟩ : V3 (ZSqrt 5)) = ![3/4 + 1/4
    * √5, -3/4 - 3/4 * √5, 3/2 + 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt99 : (1 / 4 : ℝ) • Exact.reV (⟨⟨3, 1⟩, ⟨-3, -3⟩, ⟨-6, -2⟩⟩ : V3 (ZSqrt 5)) = ![3/4 +
    1/4 * √5, -3/4 - 3/4 * √5, -3/2 - 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt100 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-3, -1⟩, ⟨3, 3⟩, ⟨6, 2⟩⟩ : V3 (ZSqrt 5)) = ![-3/4 -
    1/4 * √5, 3/4 + 3/4 * √5, 3/2 + 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt101 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-3, -1⟩, ⟨3, 3⟩, ⟨-6, -2⟩⟩ : V3 (ZSqrt 5)) = ![-3/4 -
    1/4 * √5, 3/4 + 3/4 * √5, -3/2 - 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt102 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-3, -1⟩, ⟨-3, -3⟩, ⟨6, 2⟩⟩ : V3 (ZSqrt 5)) = ![-3/4 -
    1/4 * √5, -3/4 - 3/4 * √5, 3/2 + 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt103 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-3, -1⟩, ⟨-3, -3⟩, ⟨-6, -2⟩⟩ : V3 (ZSqrt 5)) = ![-3/4
    - 1/4 * √5, -3/4 - 3/4 * √5, -3/2 - 1/2 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt104 : (1 / 4 : ℝ) • Exact.reV (⟨⟨6, 2⟩, ⟨3, 1⟩, ⟨3, 3⟩⟩ : V3 (ZSqrt 5)) = ![3/2 + 1/2
    * √5, 3/4 + 1/4 * √5, 3/4 + 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt105 : (1 / 4 : ℝ) • Exact.reV (⟨⟨6, 2⟩, ⟨3, 1⟩, ⟨-3, -3⟩⟩ : V3 (ZSqrt 5)) = ![3/2 +
    1/2 * √5, 3/4 + 1/4 * √5, -3/4 - 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt106 : (1 / 4 : ℝ) • Exact.reV (⟨⟨6, 2⟩, ⟨-3, -1⟩, ⟨3, 3⟩⟩ : V3 (ZSqrt 5)) = ![3/2 +
    1/2 * √5, -3/4 - 1/4 * √5, 3/4 + 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt107 : (1 / 4 : ℝ) • Exact.reV (⟨⟨6, 2⟩, ⟨-3, -1⟩, ⟨-3, -3⟩⟩ : V3 (ZSqrt 5)) = ![3/2 +
    1/2 * √5, -3/4 - 1/4 * √5, -3/4 - 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt108 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-6, -2⟩, ⟨3, 1⟩, ⟨3, 3⟩⟩ : V3 (ZSqrt 5)) = ![-3/2 -
    1/2 * √5, 3/4 + 1/4 * √5, 3/4 + 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt109 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-6, -2⟩, ⟨3, 1⟩, ⟨-3, -3⟩⟩ : V3 (ZSqrt 5)) = ![-3/2 -
    1/2 * √5, 3/4 + 1/4 * √5, -3/4 - 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt110 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-6, -2⟩, ⟨-3, -1⟩, ⟨3, 3⟩⟩ : V3 (ZSqrt 5)) = ![-3/2 -
    1/2 * √5, -3/4 - 1/4 * √5, 3/4 + 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt111 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-6, -2⟩, ⟨-3, -1⟩, ⟨-3, -3⟩⟩ : V3 (ZSqrt 5)) = ![-3/2
    - 1/2 * √5, -3/4 - 1/4 * √5, -3/4 - 3/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt112 : (1 / 4 : ℝ) • Exact.reV (⟨⟨3, 3⟩, ⟨6, 2⟩, ⟨3, 1⟩⟩ : V3 (ZSqrt 5)) = ![3/4 + 3/4
    * √5, 3/2 + 1/2 * √5, 3/4 + 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt113 : (1 / 4 : ℝ) • Exact.reV (⟨⟨3, 3⟩, ⟨6, 2⟩, ⟨-3, -1⟩⟩ : V3 (ZSqrt 5)) = ![3/4 +
    3/4 * √5, 3/2 + 1/2 * √5, -3/4 - 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt114 : (1 / 4 : ℝ) • Exact.reV (⟨⟨3, 3⟩, ⟨-6, -2⟩, ⟨3, 1⟩⟩ : V3 (ZSqrt 5)) = ![3/4 +
    3/4 * √5, -3/2 - 1/2 * √5, 3/4 + 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt115 : (1 / 4 : ℝ) • Exact.reV (⟨⟨3, 3⟩, ⟨-6, -2⟩, ⟨-3, -1⟩⟩ : V3 (ZSqrt 5)) = ![3/4 +
    3/4 * √5, -3/2 - 1/2 * √5, -3/4 - 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt116 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-3, -3⟩, ⟨6, 2⟩, ⟨3, 1⟩⟩ : V3 (ZSqrt 5)) = ![-3/4 -
    3/4 * √5, 3/2 + 1/2 * √5, 3/4 + 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt117 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-3, -3⟩, ⟨6, 2⟩, ⟨-3, -1⟩⟩ : V3 (ZSqrt 5)) = ![-3/4 -
    3/4 * √5, 3/2 + 1/2 * √5, -3/4 - 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt118 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-3, -3⟩, ⟨-6, -2⟩, ⟨3, 1⟩⟩ : V3 (ZSqrt 5)) = ![-3/4 -
    3/4 * √5, -3/2 - 1/2 * √5, 3/4 + 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem pt119 : (1 / 4 : ℝ) • Exact.reV (⟨⟨-3, -3⟩, ⟨-6, -2⟩, ⟨-3, -1⟩⟩ : V3 (ZSqrt 5)) = ![-3/4
    - 3/4 * √5, -3/2 - 1/2 * √5, -3/4 - 1/4 * √5] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [ZSqrt.re_mk] <;> ring

theorem eq_smul : Archimedean.TruncatedIcosidodecahedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 4) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17, pt18, pt19, pt20, pt21, pt22, pt23, pt24,
    pt25, pt26, pt27, pt28, pt29, pt30, pt31, pt32, pt33, pt34, pt35, pt36, pt37, pt38, pt39, pt40,
    pt41, pt42, pt43, pt44, pt45, pt46, pt47, pt48, pt49, pt50, pt51, pt52, pt53, pt54, pt55, pt56,
    pt57, pt58, pt59, pt60, pt61, pt62, pt63, pt64, pt65, pt66, pt67, pt68, pt69, pt70, pt71, pt72,
    pt73, pt74, pt75, pt76, pt77, pt78, pt79, pt80, pt81, pt82, pt83, pt84, pt85, pt86, pt87, pt88,
    pt89, pt90, pt91, pt92, pt93, pt94, pt95, pt96, pt97, pt98, pt99, pt100, pt101, pt102, pt103,
    pt104, pt105, pt106, pt107, pt108, pt109, pt110, pt111, pt112, pt113, pt114, pt115, pt116,
    pt117, pt118, pt119]

end Nieuwland.Polyhedra.ArchimedeanTruncatedIcosidodecahedronDim

namespace Nieuwland.Polyhedra

/-- **The fixture `archimedean/truncated-icosidodecahedron` is full-dimensional.** -/
theorem archimedeanTruncatedIcosidodecahedron_fullDim : Archimedean.TruncatedIcosidodecahedron.polyhedron.FullDim := by
  rw [ArchimedeanTruncatedIcosidodecahedronDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk ArchimedeanTruncatedIcosidodecahedronDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
