import Polyhedra.Other.OctagonalDipyramid.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `dipyramid/octagonal-dipyramid` is full-dimensional

The points of `Other.OctagonalDipyramid.polyhedron` times `2` as exact values in `ZTheta root`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Other.OctagonalDipyramid.polyhedron`.
-/

namespace Nieuwland.Polyhedra.DipyramidOctagonalDipyramidDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Other.OctagonalDipyramid.theta

/-- The root `θ`, with `α = 2 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[1/8, 0, -1, 0, 1], 0, 3/4,
    2, [2, 0, -4, 0, 1],
    16, 11, 14, 24, 6,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    10261891918244604315160023986249183187138251422389018716652300293089249245402561216793137658312748666843434503001628025439694564710962063604966778143596916,
    10261891918244604315160023986249183187138251422389018716652300293089249245402561216793137658312748666843434503001628025439694564710962063604966778143596917,
    by decide +kernel⟩

theorem root_α : root.α = (2 : ℕ) * θ := rfl

theorem root_n : root.n = 4 := rfl

/-- The points of `Other.OctagonalDipyramid.polyhedron` times `2`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[0]⟩, ⟨[0]⟩, ⟨[-2]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0]⟩, ⟨[2]⟩⟩,
    ⟨⟨[0, 1]⟩, ⟨[0, 1, 0, -1]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0, 1, 0, -1]⟩, ⟨[0, 1]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0, -1, 0, 1]⟩, ⟨[0, 1]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0, -1]⟩, ⟨[0, 1, 0, -1]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0, -1]⟩, ⟨[0, -1, 0, 1]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0, -1, 0, 1]⟩, ⟨[0, -1]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0, 1, 0, -1]⟩, ⟨[0, -1]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0, 1]⟩, ⟨[0, -1, 0, 1]⟩, ⟨[0]⟩⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0]⟩, ⟨[-2]⟩⟩ : V3 (ZTheta root)) = ![polyEval
    [0] θ, polyEval [0] θ, polyEval [-1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0]⟩, ⟨[2]⟩⟩ : V3 (ZTheta root)) = ![polyEval
    [0] θ, polyEval [0] θ, polyEval [1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 1]⟩, ⟨[0, 1, 0, -1]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1] θ, polyEval [0, 1, 0, -4] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 1, 0, -1]⟩, ⟨[0, 1]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1, 0, -4] θ, polyEval [0, 1] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -1, 0, 1]⟩, ⟨[0, 1]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, -1, 0, 4] θ, polyEval [0, 1] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -1]⟩, ⟨[0, 1, 0, -1]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, -1] θ, polyEval [0, 1, 0, -4] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -1]⟩, ⟨[0, -1, 0, 1]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, -1] θ, polyEval [0, -1, 0, 4] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -1, 0, 1]⟩, ⟨[0, -1]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, -1, 0, 4] θ, polyEval [0, -1] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 1, 0, -1]⟩, ⟨[0, -1]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1, 0, -4] θ, polyEval [0, -1] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt9 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 1]⟩, ⟨[0, -1, 0, 1]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1] θ, polyEval [0, -1, 0, 4] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem eq_smul : Other.OctagonalDipyramid.polyhedron = (Polyhedron.ofPoints points).smul (1 / 2) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9]

end Nieuwland.Polyhedra.DipyramidOctagonalDipyramidDim

namespace Nieuwland.Polyhedra

/-- **The fixture `dipyramid/octagonal-dipyramid` is full-dimensional.** -/
theorem dipyramidOctagonalDipyramid_fullDim : Other.OctagonalDipyramid.polyhedron.FullDim := by
  rw [DipyramidOctagonalDipyramidDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk DipyramidOctagonalDipyramidDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
