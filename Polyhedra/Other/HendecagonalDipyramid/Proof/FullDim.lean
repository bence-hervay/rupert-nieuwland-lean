import Polyhedra.Other.HendecagonalDipyramid.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `dipyramid/hendecagonal-dipyramid` is full-dimensional

The points of `Other.HendecagonalDipyramid.polyhedron` times `2` as exact values in `ZTheta root`, exported
by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Other.HendecagonalDipyramid.polyhedron`.
-/

namespace Nieuwland.Polyhedra.DipyramidHendecagonalDipyramidDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Other.HendecagonalDipyramid.theta

/-- The root `θ`, with `α = 2 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[-11/1024, 0, 55/256, 0, -77/64, 0, 11/4, 0, -11/4, 0, 1], 1/8, 1/2,
    2, [-11, 0, 55, 0, -77, 0, 44, 0, -11, 0, 1],
    128, 71, 74, 128, 11,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    7554832019483049175211056091455360865512499850361591604512742100413624566467390259118538994482567730358624358238463732376049370868288080170767985360965298,
    7554832019483049175211056091455360865512499850361591604512742100413624566467390259118538994482567730358624358238463732376049370868288080170767985360965299,
    by decide +kernel⟩

theorem root_α : root.α = (2 : ℕ) * θ := rfl

theorem root_n : root.n = 10 := rfl

/-- The points of `Other.HendecagonalDipyramid.polyhedron` times `2`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[0]⟩, ⟨[0]⟩, ⟨[-2]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0]⟩, ⟨[2]⟩⟩,
    ⟨⟨[0, 1]⟩, ⟨[11, 0, -50, 0, 57, 0, -23, 0, 3]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0, 1, 0, -1]⟩, ⟨[0, 0, 4, 0, -10, 0, 6, 0, -1]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0, 1, 0, -3, 0, 1]⟩, ⟨[0, 0, 3, 0, -4, 0, 1]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0, 1, 0, -6, 0, 5, 0, -1]⟩, ⟨[0, 0, 2, 0, -1]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0, 1, 0, -10, 0, 15, 0, -7, 0, 1]⟩, ⟨[0, 0, 1]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0, -10, 0, 40, 0, -42, 0, 16, 0, -2]⟩, ⟨[0]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0, 1, 0, -10, 0, 15, 0, -7, 0, 1]⟩, ⟨[0, 0, -1]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0, 1, 0, -6, 0, 5, 0, -1]⟩, ⟨[0, 0, -2, 0, 1]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0, 1, 0, -3, 0, 1]⟩, ⟨[0, 0, -3, 0, 4, 0, -1]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0, 1, 0, -1]⟩, ⟨[0, 0, -4, 0, 10, 0, -6, 0, 1]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0, 1]⟩, ⟨[-11, 0, 50, 0, -57, 0, 23, 0, -3]⟩, ⟨[0]⟩⟩]

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

theorem pt2 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 1]⟩, ⟨[11, 0, -50, 0, 57, 0, -23, 0, 3]⟩, ⟨[0]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [0, 1] θ, polyEval [11/2, 0, -100, 0, 456, 0, -736, 0, 384] θ,
    polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 1, 0, -1]⟩, ⟨[0, 0, 4, 0, -10, 0, 6, 0, -1]⟩,
    ⟨[0]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 1, 0, -4] θ, polyEval [0, 0, 8, 0, -80, 0, 192, 0,
    -128] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 1, 0, -3, 0, 1]⟩, ⟨[0, 0, 3, 0, -4, 0, 1]⟩, ⟨[0]⟩⟩
    : V3 (ZTheta root)) = ![polyEval [0, 1, 0, -12, 0, 16] θ, polyEval [0, 0, 6, 0, -32, 0, 32] θ,
    polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 1, 0, -6, 0, 5, 0, -1]⟩, ⟨[0, 0, 2, 0, -1]⟩, ⟨[0]⟩⟩
    : V3 (ZTheta root)) = ![polyEval [0, 1, 0, -24, 0, 80, 0, -64] θ, polyEval [0, 0, 4, 0, -8] θ,
    polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 1, 0, -10, 0, 15, 0, -7, 0, 1]⟩, ⟨[0, 0, 1]⟩,
    ⟨[0]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 1, 0, -40, 0, 240, 0, -448, 0, 256] θ, polyEval [0,
    0, 2] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -10, 0, 40, 0, -42, 0, 16, 0, -2]⟩, ⟨[0]⟩, ⟨[0]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [0, -10, 0, 160, 0, -672, 0, 1024, 0, -512] θ, polyEval [0] θ,
    polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 1, 0, -10, 0, 15, 0, -7, 0, 1]⟩, ⟨[0, 0, -1]⟩,
    ⟨[0]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 1, 0, -40, 0, 240, 0, -448, 0, 256] θ, polyEval [0,
    0, -2] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt9 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 1, 0, -6, 0, 5, 0, -1]⟩, ⟨[0, 0, -2, 0, 1]⟩, ⟨[0]⟩⟩
    : V3 (ZTheta root)) = ![polyEval [0, 1, 0, -24, 0, 80, 0, -64] θ, polyEval [0, 0, -4, 0, 8] θ,
    polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt10 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 1, 0, -3, 0, 1]⟩, ⟨[0, 0, -3, 0, 4, 0, -1]⟩,
    ⟨[0]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 1, 0, -12, 0, 16] θ, polyEval [0, 0, -6, 0, 32, 0,
    -32] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt11 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 1, 0, -1]⟩, ⟨[0, 0, -4, 0, 10, 0, -6, 0, 1]⟩,
    ⟨[0]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 1, 0, -4] θ, polyEval [0, 0, -8, 0, 80, 0, -192, 0,
    128] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt12 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 1]⟩, ⟨[-11, 0, 50, 0, -57, 0, 23, 0, -3]⟩, ⟨[0]⟩⟩
    : V3 (ZTheta root)) = ![polyEval [0, 1] θ, polyEval [-11/2, 0, 100, 0, -456, 0, 736, 0, -384] θ,
    polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem eq_smul : Other.HendecagonalDipyramid.polyhedron = (Polyhedron.ofPoints points).smul (1 / 2) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12]

end Nieuwland.Polyhedra.DipyramidHendecagonalDipyramidDim

namespace Nieuwland.Polyhedra

/-- **The fixture `dipyramid/hendecagonal-dipyramid` is full-dimensional.** -/
theorem dipyramidHendecagonalDipyramid_fullDim : Other.HendecagonalDipyramid.polyhedron.FullDim := by
  rw [DipyramidHendecagonalDipyramidDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk DipyramidHendecagonalDipyramidDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
