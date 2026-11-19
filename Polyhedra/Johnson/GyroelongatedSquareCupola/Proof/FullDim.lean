import Polyhedra.Johnson.GyroelongatedSquareCupola.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `johnson/gyroelongated-square-cupola` is full-dimensional

The points of `Johnson.GyroelongatedSquareCupola.polyhedron` times `64` as exact values in `ZTheta root`,
exported by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`,
checked by the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`),
and scaled back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Johnson.GyroelongatedSquareCupola.polyhedron`.
-/

namespace Nieuwland.Polyhedra.JohnsonGyroelongatedSquareCupolaDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Johnson.GyroelongatedSquareCupola.theta

/-- The root `θ`, with `α = 4 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[-1/512, 0, 1/16, 0, -1/2, 0, 1, 0, 1], 13/32, 29/64,
    4, [-128, 0, 256, 0, -128, 0, 16, 0, 1],
    512, 879, 882, 928, 14,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    23069355527406471441951701309011578651573491068111170384107255675050366055307766614165697009432457762443927821885653241262330465262649035412961590463465514,
    23069355527406471441951701309011578651573491068111170384107255675050366055307766614165697009432457762443927821885653241262330465262649035412961590463465515,
    by decide +kernel⟩

theorem root_α : root.α = (4 : ℕ) * θ := rfl

theorem root_n : root.n = 8 := rfl

/-- The points of `Johnson.GyroelongatedSquareCupola.polyhedron` times `64`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[160, 0, -288, 0, 76, 0, 4]⟩, ⟨[32]⟩, ⟨[0, 16]⟩⟩,
    ⟨⟨[160, 0, -288, 0, 76, 0, 4]⟩, ⟨[-32]⟩, ⟨[0, 16]⟩⟩,
    ⟨⟨[-160, 0, 288, 0, -76, 0, -4]⟩, ⟨[32]⟩, ⟨[0, 16]⟩⟩,
    ⟨⟨[-160, 0, 288, 0, -76, 0, -4]⟩, ⟨[-32]⟩, ⟨[0, 16]⟩⟩,
    ⟨⟨[32]⟩, ⟨[160, 0, -288, 0, 76, 0, 4]⟩, ⟨[0, 16]⟩⟩,
    ⟨⟨[32]⟩, ⟨[-160, 0, 288, 0, -76, 0, -4]⟩, ⟨[0, 16]⟩⟩,
    ⟨⟨[-32]⟩, ⟨[160, 0, -288, 0, 76, 0, 4]⟩, ⟨[0, 16]⟩⟩,
    ⟨⟨[-32]⟩, ⟨[-160, 0, 288, 0, -76, 0, -4]⟩, ⟨[0, 16]⟩⟩,
    ⟨⟨[320, 0, -464, 0, 112, 0, 6]⟩, ⟨[0]⟩, ⟨[0, -16]⟩⟩,
    ⟨⟨[-320, 0, 464, 0, -112, 0, -6]⟩, ⟨[0]⟩, ⟨[0, -16]⟩⟩,
    ⟨⟨[0]⟩, ⟨[320, 0, -464, 0, 112, 0, 6]⟩, ⟨[0, -16]⟩⟩,
    ⟨⟨[0]⟩, ⟨[-320, 0, 464, 0, -112, 0, -6]⟩, ⟨[0, -16]⟩⟩,
    ⟨⟨[0, 0, -48, 0, 20, 0, 1]⟩, ⟨[0, 0, -48, 0, 20, 0, 1]⟩, ⟨[0, -16]⟩⟩,
    ⟨⟨[0, 0, -48, 0, 20, 0, 1]⟩, ⟨[0, 0, 48, 0, -20, 0, -1]⟩, ⟨[0, -16]⟩⟩,
    ⟨⟨[0, 0, 48, 0, -20, 0, -1]⟩, ⟨[0, 0, -48, 0, 20, 0, 1]⟩, ⟨[0, -16]⟩⟩,
    ⟨⟨[0, 0, 48, 0, -20, 0, -1]⟩, ⟨[0, 0, 48, 0, -20, 0, -1]⟩, ⟨[0, -16]⟩⟩,
    ⟨⟨[32]⟩, ⟨[32]⟩, ⟨[128, 16, -288, 0, 76, 0, 4]⟩⟩,
    ⟨⟨[32]⟩, ⟨[-32]⟩, ⟨[128, 16, -288, 0, 76, 0, 4]⟩⟩,
    ⟨⟨[-32]⟩, ⟨[32]⟩, ⟨[128, 16, -288, 0, 76, 0, 4]⟩⟩,
    ⟨⟨[-32]⟩, ⟨[-32]⟩, ⟨[128, 16, -288, 0, 76, 0, 4]⟩⟩]

theorem span_ok : spanOk points 0 1 2 8 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 64 : ℝ) • Exact.reV (⟨⟨[160, 0, -288, 0, 76, 0, 4]⟩, ⟨[32]⟩, ⟨[0, 16]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [5/2, 0, -72, 0, 304, 0, 256] θ, polyEval [1/2] θ, polyEval [0, 1]
    θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 64) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 64 : ℝ) • Exact.reV (⟨⟨[160, 0, -288, 0, 76, 0, 4]⟩, ⟨[-32]⟩, ⟨[0, 16]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [5/2, 0, -72, 0, 304, 0, 256] θ, polyEval [-1/2] θ, polyEval [0, 1]
    θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 64) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 64 : ℝ) • Exact.reV (⟨⟨[-160, 0, 288, 0, -76, 0, -4]⟩, ⟨[32]⟩, ⟨[0, 16]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [-5/2, 0, 72, 0, -304, 0, -256] θ, polyEval [1/2] θ, polyEval [0,
    1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 64) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 64 : ℝ) • Exact.reV (⟨⟨[-160, 0, 288, 0, -76, 0, -4]⟩, ⟨[-32]⟩, ⟨[0, 16]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [-5/2, 0, 72, 0, -304, 0, -256] θ, polyEval [-1/2] θ, polyEval
    [0, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 64) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 64 : ℝ) • Exact.reV (⟨⟨[32]⟩, ⟨[160, 0, -288, 0, 76, 0, 4]⟩, ⟨[0, 16]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [1/2] θ, polyEval [5/2, 0, -72, 0, 304, 0, 256] θ, polyEval [0, 1]
    θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 64) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 64 : ℝ) • Exact.reV (⟨⟨[32]⟩, ⟨[-160, 0, 288, 0, -76, 0, -4]⟩, ⟨[0, 16]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [1/2] θ, polyEval [-5/2, 0, 72, 0, -304, 0, -256] θ, polyEval [0,
    1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 64) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 64 : ℝ) • Exact.reV (⟨⟨[-32]⟩, ⟨[160, 0, -288, 0, 76, 0, 4]⟩, ⟨[0, 16]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [-1/2] θ, polyEval [5/2, 0, -72, 0, 304, 0, 256] θ, polyEval [0, 1]
    θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 64) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 64 : ℝ) • Exact.reV (⟨⟨[-32]⟩, ⟨[-160, 0, 288, 0, -76, 0, -4]⟩, ⟨[0, 16]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [-1/2] θ, polyEval [-5/2, 0, 72, 0, -304, 0, -256] θ, polyEval
    [0, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 64) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 64 : ℝ) • Exact.reV (⟨⟨[320, 0, -464, 0, 112, 0, 6]⟩, ⟨[0]⟩, ⟨[0, -16]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [5, 0, -116, 0, 448, 0, 384] θ, polyEval [0] θ, polyEval [0, -1] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 64) (by norm_num) (by decide +kernel)

theorem pt9 : (1 / 64 : ℝ) • Exact.reV (⟨⟨[-320, 0, 464, 0, -112, 0, -6]⟩, ⟨[0]⟩, ⟨[0, -16]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [-5, 0, 116, 0, -448, 0, -384] θ, polyEval [0] θ, polyEval [0,
    -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 64) (by norm_num) (by decide +kernel)

theorem pt10 : (1 / 64 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[320, 0, -464, 0, 112, 0, 6]⟩, ⟨[0, -16]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [0] θ, polyEval [5, 0, -116, 0, 448, 0, 384] θ, polyEval [0, -1]
    θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 64) (by norm_num) (by decide +kernel)

theorem pt11 : (1 / 64 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[-320, 0, 464, 0, -112, 0, -6]⟩, ⟨[0, -16]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [0] θ, polyEval [-5, 0, 116, 0, -448, 0, -384] θ, polyEval [0,
    -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 64) (by norm_num) (by decide +kernel)

theorem pt12 : (1 / 64 : ℝ) • Exact.reV (⟨⟨[0, 0, -48, 0, 20, 0, 1]⟩, ⟨[0, 0, -48, 0, 20, 0,
    1]⟩, ⟨[0, -16]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 0, -12, 0, 80, 0, 64] θ, polyEval [0, 0,
    -12, 0, 80, 0, 64] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 64) (by norm_num) (by decide +kernel)

theorem pt13 : (1 / 64 : ℝ) • Exact.reV (⟨⟨[0, 0, -48, 0, 20, 0, 1]⟩, ⟨[0, 0, 48, 0, -20, 0,
    -1]⟩, ⟨[0, -16]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 0, -12, 0, 80, 0, 64] θ, polyEval [0, 0,
    12, 0, -80, 0, -64] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 64) (by norm_num) (by decide +kernel)

theorem pt14 : (1 / 64 : ℝ) • Exact.reV (⟨⟨[0, 0, 48, 0, -20, 0, -1]⟩, ⟨[0, 0, -48, 0, 20, 0,
    1]⟩, ⟨[0, -16]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 0, 12, 0, -80, 0, -64] θ, polyEval [0, 0,
    -12, 0, 80, 0, 64] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 64) (by norm_num) (by decide +kernel)

theorem pt15 : (1 / 64 : ℝ) • Exact.reV (⟨⟨[0, 0, 48, 0, -20, 0, -1]⟩, ⟨[0, 0, 48, 0, -20, 0,
    -1]⟩, ⟨[0, -16]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 0, 12, 0, -80, 0, -64] θ, polyEval [0, 0,
    12, 0, -80, 0, -64] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 64) (by norm_num) (by decide +kernel)

theorem pt16 : (1 / 64 : ℝ) • Exact.reV (⟨⟨[32]⟩, ⟨[32]⟩, ⟨[128, 16, -288, 0, 76, 0, 4]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [1/2] θ, polyEval [1/2] θ, polyEval [2, 1, -72, 0, 304, 0, 256] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 64) (by norm_num) (by decide +kernel)

theorem pt17 : (1 / 64 : ℝ) • Exact.reV (⟨⟨[32]⟩, ⟨[-32]⟩, ⟨[128, 16, -288, 0, 76, 0, 4]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [1/2] θ, polyEval [-1/2] θ, polyEval [2, 1, -72, 0, 304, 0, 256] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 64) (by norm_num) (by decide +kernel)

theorem pt18 : (1 / 64 : ℝ) • Exact.reV (⟨⟨[-32]⟩, ⟨[32]⟩, ⟨[128, 16, -288, 0, 76, 0, 4]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [-1/2] θ, polyEval [1/2] θ, polyEval [2, 1, -72, 0, 304, 0, 256] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 64) (by norm_num) (by decide +kernel)

theorem pt19 : (1 / 64 : ℝ) • Exact.reV (⟨⟨[-32]⟩, ⟨[-32]⟩, ⟨[128, 16, -288, 0, 76, 0, 4]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [-1/2] θ, polyEval [-1/2] θ, polyEval [2, 1, -72, 0, 304, 0, 256] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 64) (by norm_num) (by decide +kernel)

theorem eq_smul : Johnson.GyroelongatedSquareCupola.polyhedron = (Polyhedron.ofPoints points).smul (1 / 64) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17, pt18, pt19]

end Nieuwland.Polyhedra.JohnsonGyroelongatedSquareCupolaDim

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/gyroelongated-square-cupola` is full-dimensional.** -/
theorem johnsonGyroelongatedSquareCupola_fullDim : Johnson.GyroelongatedSquareCupola.polyhedron.FullDim := by
  rw [JohnsonGyroelongatedSquareCupolaDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk JohnsonGyroelongatedSquareCupolaDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
