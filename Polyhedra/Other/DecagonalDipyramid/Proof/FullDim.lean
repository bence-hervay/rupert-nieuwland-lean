import Polyhedra.Other.DecagonalDipyramid.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `dipyramid/decagonal-dipyramid` is full-dimensional

The points of `Other.DecagonalDipyramid.polyhedron` times `100` as exact values in `ZTheta root`, exported
by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Other.DecagonalDipyramid.polyhedron`.
-/

namespace Nieuwland.Polyhedra.DipyramidDecagonalDipyramidDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Other.DecagonalDipyramid.theta

/-- The root `θ`, with `α = 10 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[-1/20, 1/2, -3/2, 1, 1], 5/16, 1/2,
    10, [-500, 500, -150, 10, 1],
    64, 261, 264, 320, 14,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    54894609548386264660088068475936877421095403000399779064822944604802637020585288460147669049779332209017863774440913732645561627977919652091191716192874016,
    54894609548386264660088068475936877421095403000399779064822944604802637020585288460147669049779332209017863774440913732645561627977919652091191716192874017,
    by decide +kernel⟩

theorem root_α : root.α = (10 : ℕ) * θ := rfl

theorem root_n : root.n = 4 := rfl

/-- The points of `Other.DecagonalDipyramid.polyhedron` times `100`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[0]⟩, ⟨[0]⟩, ⟨[-100]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0]⟩, ⟨[100]⟩⟩,
    ⟨⟨[850, -550, 65, 5]⟩, ⟨[-850, 560, -65, -5]⟩, ⟨[0]⟩⟩,
    ⟨⟨[-800, 550, -65, -5]⟩, ⟨[-400, 240, -25, -2]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0]⟩, ⟨[900, -640, 80, 6]⟩, ⟨[0]⟩⟩,
    ⟨⟨[800, -550, 65, 5]⟩, ⟨[-400, 240, -25, -2]⟩, ⟨[0]⟩⟩,
    ⟨⟨[-850, 550, -65, -5]⟩, ⟨[-850, 560, -65, -5]⟩, ⟨[0]⟩⟩,
    ⟨⟨[-850, 550, -65, -5]⟩, ⟨[850, -560, 65, 5]⟩, ⟨[0]⟩⟩,
    ⟨⟨[800, -550, 65, 5]⟩, ⟨[400, -240, 25, 2]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0]⟩, ⟨[-900, 640, -80, -6]⟩, ⟨[0]⟩⟩,
    ⟨⟨[-800, 550, -65, -5]⟩, ⟨[400, -240, 25, 2]⟩, ⟨[0]⟩⟩,
    ⟨⟨[850, -550, 65, 5]⟩, ⟨[850, -560, 65, 5]⟩, ⟨[0]⟩⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 100 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0]⟩, ⟨[-100]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0] θ, polyEval [0] θ, polyEval [-1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 100) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 100 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0]⟩, ⟨[100]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0] θ, polyEval [0] θ, polyEval [1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 100) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 100 : ℝ) • Exact.reV (⟨⟨[850, -550, 65, 5]⟩, ⟨[-850, 560, -65, -5]⟩, ⟨[0]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [17/2, -55, 65, 50] θ, polyEval [-17/2, 56, -65, -50] θ, polyEval
    [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 100) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 100 : ℝ) • Exact.reV (⟨⟨[-800, 550, -65, -5]⟩, ⟨[-400, 240, -25, -2]⟩, ⟨[0]⟩⟩
    : V3 (ZTheta root)) = ![polyEval [-8, 55, -65, -50] θ, polyEval [-4, 24, -25, -20] θ, polyEval
    [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 100) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 100 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[900, -640, 80, 6]⟩, ⟨[0]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [0] θ, polyEval [9, -64, 80, 60] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 100) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 100 : ℝ) • Exact.reV (⟨⟨[800, -550, 65, 5]⟩, ⟨[-400, 240, -25, -2]⟩, ⟨[0]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [8, -55, 65, 50] θ, polyEval [-4, 24, -25, -20] θ, polyEval [0]
    θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 100) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 100 : ℝ) • Exact.reV (⟨⟨[-850, 550, -65, -5]⟩, ⟨[-850, 560, -65, -5]⟩, ⟨[0]⟩⟩
    : V3 (ZTheta root)) = ![polyEval [-17/2, 55, -65, -50] θ, polyEval [-17/2, 56, -65, -50] θ,
    polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 100) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 100 : ℝ) • Exact.reV (⟨⟨[-850, 550, -65, -5]⟩, ⟨[850, -560, 65, 5]⟩, ⟨[0]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [-17/2, 55, -65, -50] θ, polyEval [17/2, -56, 65, 50] θ, polyEval
    [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 100) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 100 : ℝ) • Exact.reV (⟨⟨[800, -550, 65, 5]⟩, ⟨[400, -240, 25, 2]⟩, ⟨[0]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [8, -55, 65, 50] θ, polyEval [4, -24, 25, 20] θ, polyEval [0] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 100) (by norm_num) (by decide +kernel)

theorem pt9 : (1 / 100 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[-900, 640, -80, -6]⟩, ⟨[0]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [0] θ, polyEval [-9, 64, -80, -60] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 100) (by norm_num) (by decide +kernel)

theorem pt10 : (1 / 100 : ℝ) • Exact.reV (⟨⟨[-800, 550, -65, -5]⟩, ⟨[400, -240, 25, 2]⟩, ⟨[0]⟩⟩
    : V3 (ZTheta root)) = ![polyEval [-8, 55, -65, -50] θ, polyEval [4, -24, 25, 20] θ, polyEval [0]
    θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 100) (by norm_num) (by decide +kernel)

theorem pt11 : (1 / 100 : ℝ) • Exact.reV (⟨⟨[850, -550, 65, 5]⟩, ⟨[850, -560, 65, 5]⟩, ⟨[0]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [17/2, -55, 65, 50] θ, polyEval [17/2, -56, 65, 50] θ, polyEval
    [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 100) (by norm_num) (by decide +kernel)

theorem eq_smul : Other.DecagonalDipyramid.polyhedron = (Polyhedron.ofPoints points).smul (1 / 100) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11]

end Nieuwland.Polyhedra.DipyramidDecagonalDipyramidDim

namespace Nieuwland.Polyhedra

/-- **The fixture `dipyramid/decagonal-dipyramid` is full-dimensional.** -/
theorem dipyramidDecagonalDipyramid_fullDim : Other.DecagonalDipyramid.polyhedron.FullDim := by
  rw [DipyramidDecagonalDipyramidDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk DipyramidDecagonalDipyramidDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
