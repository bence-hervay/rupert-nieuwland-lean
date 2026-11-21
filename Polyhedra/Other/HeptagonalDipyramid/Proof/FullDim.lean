import Polyhedra.Other.HeptagonalDipyramid.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `dipyramid/heptagonal-dipyramid` is full-dimensional

The points of `Other.HeptagonalDipyramid.polyhedron` times `2` as exact values in `ZTheta root`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Other.HeptagonalDipyramid.polyhedron`.
-/

namespace Nieuwland.Polyhedra.DipyramidHeptagonalDipyramidDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Other.HeptagonalDipyramid.theta

/-- The root `θ`, with `α = 2 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[-7/64, 0, 7/8, 0, -7/4, 0, 1], 0, 3/4,
    2, [-7, 0, 14, 0, -7, 0, 1],
    64, 54, 57, 96, 13,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    11634859676027081569755774244848379008759863598809356500501976512285991259390728137252677120710501017707573912206048890646964199563254681620726159472166513,
    11634859676027081569755774244848379008759863598809356500501976512285991259390728137252677120710501017707573912206048890646964199563254681620726159472166514,
    by decide +kernel⟩

theorem root_α : root.α = (2 : ℕ) * θ := rfl

theorem root_n : root.n = 6 := rfl

/-- The points of `Other.HeptagonalDipyramid.polyhedron` times `2`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[0]⟩, ⟨[0]⟩, ⟨[-2]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0]⟩, ⟨[2]⟩⟩,
    ⟨⟨[0, 1]⟩, ⟨[7, 0, -11, 0, 3]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0, 1, 0, -1]⟩, ⟨[0, 0, 2, 0, -1]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0, 1, 0, -3, 0, 1]⟩, ⟨[0, 0, 1]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0, -6, 0, 8, 0, -2]⟩, ⟨[0]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0, 1, 0, -3, 0, 1]⟩, ⟨[0, 0, -1]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0, 1, 0, -1]⟩, ⟨[0, 0, -2, 0, 1]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0, 1]⟩, ⟨[-7, 0, 11, 0, -3]⟩, ⟨[0]⟩⟩]

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

theorem pt2 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 1]⟩, ⟨[7, 0, -11, 0, 3]⟩, ⟨[0]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [0, 1] θ, polyEval [7/2, 0, -22, 0, 24] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 1, 0, -1]⟩, ⟨[0, 0, 2, 0, -1]⟩, ⟨[0]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [0, 1, 0, -4] θ, polyEval [0, 0, 4, 0, -8] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 1, 0, -3, 0, 1]⟩, ⟨[0, 0, 1]⟩, ⟨[0]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [0, 1, 0, -12, 0, 16] θ, polyEval [0, 0, 2] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -6, 0, 8, 0, -2]⟩, ⟨[0]⟩, ⟨[0]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [0, -6, 0, 32, 0, -32] θ, polyEval [0] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 1, 0, -3, 0, 1]⟩, ⟨[0, 0, -1]⟩, ⟨[0]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [0, 1, 0, -12, 0, 16] θ, polyEval [0, 0, -2] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 1, 0, -1]⟩, ⟨[0, 0, -2, 0, 1]⟩, ⟨[0]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [0, 1, 0, -4] θ, polyEval [0, 0, -4, 0, 8] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 1]⟩, ⟨[-7, 0, 11, 0, -3]⟩, ⟨[0]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [0, 1] θ, polyEval [-7/2, 0, 22, 0, -24] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem eq_smul : Other.HeptagonalDipyramid.polyhedron = (Polyhedron.ofPoints points).smul (1 / 2) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8]

end Nieuwland.Polyhedra.DipyramidHeptagonalDipyramidDim

namespace Nieuwland.Polyhedra

/-- **The fixture `dipyramid/heptagonal-dipyramid` is full-dimensional.** -/
theorem dipyramidHeptagonalDipyramid_fullDim : Other.HeptagonalDipyramid.polyhedron.FullDim := by
  rw [DipyramidHeptagonalDipyramidDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk DipyramidHeptagonalDipyramidDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
