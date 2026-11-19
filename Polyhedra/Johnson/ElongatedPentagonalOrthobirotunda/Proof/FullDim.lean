import Polyhedra.Johnson.ElongatedPentagonalOrthobirotunda.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `johnson/elongated-pentagonal-orthobirotunda` is full-dimensional

The points of `Johnson.ElongatedPentagonalOrthobirotunda.polyhedron` times `50` as exact values in
`ZTheta root`, exported by `code/lean-export dim`: three of their differences are linearly
independent (`spanOk`, checked by the kernel), so their polyhedron is full-dimensional
(`Polyhedron.fullDim_of_spanOk`), and scaled back (`eq_smul`, `Polyhedron.FullDim.smul`), so is
`Johnson.ElongatedPentagonalOrthobirotunda.polyhedron`.
-/

namespace Nieuwland.Polyhedra.JohnsonElongatedPentagonalOrthobirotundaDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Johnson.ElongatedPentagonalOrthobirotunda.theta

/-- The root `θ`, with `α = 10 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[1/80, 0, -1/4, 0, 1], 3/16, 3/8,
    10, [125, 0, -25, 0, 1],
    16, 41, 44, 60, 7,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    35244508870442300884603250067388407451867365573644937015346321220677018202096567685149093858442629233841304118641037970970903179764574519813420750309310454,
    35244508870442300884603250067388407451867365573644937015346321220677018202096567685149093858442629233841304118641037970970903179764574519813420750309310455,
    by decide +kernel⟩

theorem root_α : root.α = (10 : ℕ) * θ := rfl

theorem root_n : root.n = 4 := rfl

/-- The points of `Johnson.ElongatedPentagonalOrthobirotunda.polyhedron` times `50`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[150, 0, -10]⟩, ⟨[0]⟩, ⟨[25]⟩⟩,
    ⟨⟨[150, 0, -10]⟩, ⟨[0]⟩, ⟨[-25]⟩⟩,
    ⟨⟨[-150, 0, 10]⟩, ⟨[0]⟩, ⟨[25]⟩⟩,
    ⟨⟨[-150, 0, 10]⟩, ⟨[0]⟩, ⟨[-25]⟩⟩,
    ⟨⟨[100, 0, -5]⟩, ⟨[0, 25, 0, -1]⟩, ⟨[25]⟩⟩,
    ⟨⟨[100, 0, -5]⟩, ⟨[0, 25, 0, -1]⟩, ⟨[-25]⟩⟩,
    ⟨⟨[100, 0, -5]⟩, ⟨[0, -25, 0, 1]⟩, ⟨[25]⟩⟩,
    ⟨⟨[100, 0, -5]⟩, ⟨[0, -25, 0, 1]⟩, ⟨[-25]⟩⟩,
    ⟨⟨[-100, 0, 5]⟩, ⟨[0, 25, 0, -1]⟩, ⟨[25]⟩⟩,
    ⟨⟨[-100, 0, 5]⟩, ⟨[0, 25, 0, -1]⟩, ⟨[-25]⟩⟩,
    ⟨⟨[-100, 0, 5]⟩, ⟨[0, -25, 0, 1]⟩, ⟨[25]⟩⟩,
    ⟨⟨[-100, 0, 5]⟩, ⟨[0, -25, 0, 1]⟩, ⟨[-25]⟩⟩,
    ⟨⟨[25]⟩, ⟨[0, 50, 0, -3]⟩, ⟨[25]⟩⟩,
    ⟨⟨[25]⟩, ⟨[0, 50, 0, -3]⟩, ⟨[-25]⟩⟩,
    ⟨⟨[25]⟩, ⟨[0, -50, 0, 3]⟩, ⟨[25]⟩⟩,
    ⟨⟨[25]⟩, ⟨[0, -50, 0, 3]⟩, ⟨[-25]⟩⟩,
    ⟨⟨[-25]⟩, ⟨[0, 50, 0, -3]⟩, ⟨[25]⟩⟩,
    ⟨⟨[-25]⟩, ⟨[0, 50, 0, -3]⟩, ⟨[-25]⟩⟩,
    ⟨⟨[-25]⟩, ⟨[0, -50, 0, 3]⟩, ⟨[25]⟩⟩,
    ⟨⟨[-25]⟩, ⟨[0, -50, 0, 3]⟩, ⟨[-25]⟩⟩,
    ⟨⟨[75, 0, -5]⟩, ⟨[0, 5]⟩, ⟨[25, 40, 0, -2]⟩⟩,
    ⟨⟨[75, 0, -5]⟩, ⟨[0, 5]⟩, ⟨[-25, -40, 0, 2]⟩⟩,
    ⟨⟨[-75, 0, 5]⟩, ⟨[0, 5]⟩, ⟨[25, 40, 0, -2]⟩⟩,
    ⟨⟨[-75, 0, 5]⟩, ⟨[0, 5]⟩, ⟨[-25, -40, 0, 2]⟩⟩,
    ⟨⟨[25]⟩, ⟨[0, -20, 0, 1]⟩, ⟨[25, 40, 0, -2]⟩⟩,
    ⟨⟨[25]⟩, ⟨[0, -20, 0, 1]⟩, ⟨[-25, -40, 0, 2]⟩⟩,
    ⟨⟨[-25]⟩, ⟨[0, -20, 0, 1]⟩, ⟨[25, 40, 0, -2]⟩⟩,
    ⟨⟨[-25]⟩, ⟨[0, -20, 0, 1]⟩, ⟨[-25, -40, 0, 2]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0, 30, 0, -2]⟩, ⟨[25, 40, 0, -2]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0, 30, 0, -2]⟩, ⟨[-25, -40, 0, 2]⟩⟩,
    ⟨⟨[100, 0, -5]⟩, ⟨[0, -15, 0, 1]⟩, ⟨[25, 30, 0, -2]⟩⟩,
    ⟨⟨[100, 0, -5]⟩, ⟨[0, -15, 0, 1]⟩, ⟨[-25, -30, 0, 2]⟩⟩,
    ⟨⟨[-100, 0, 5]⟩, ⟨[0, -15, 0, 1]⟩, ⟨[25, 30, 0, -2]⟩⟩,
    ⟨⟨[-100, 0, 5]⟩, ⟨[0, -15, 0, 1]⟩, ⟨[-25, -30, 0, 2]⟩⟩,
    ⟨⟨[75, 0, -5]⟩, ⟨[0, 35, 0, -2]⟩, ⟨[25, 30, 0, -2]⟩⟩,
    ⟨⟨[75, 0, -5]⟩, ⟨[0, 35, 0, -2]⟩, ⟨[-25, -30, 0, 2]⟩⟩,
    ⟨⟨[-75, 0, 5]⟩, ⟨[0, 35, 0, -2]⟩, ⟨[25, 30, 0, -2]⟩⟩,
    ⟨⟨[-75, 0, 5]⟩, ⟨[0, 35, 0, -2]⟩, ⟨[-25, -30, 0, 2]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0, -40, 0, 2]⟩, ⟨[25, 30, 0, -2]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0, -40, 0, 2]⟩, ⟨[-25, -30, 0, 2]⟩⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[150, 0, -10]⟩, ⟨[0]⟩, ⟨[25]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [3, 0, -20] θ, polyEval [0] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[150, 0, -10]⟩, ⟨[0]⟩, ⟨[-25]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [3, 0, -20] θ, polyEval [0] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[-150, 0, 10]⟩, ⟨[0]⟩, ⟨[25]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [-3, 0, 20] θ, polyEval [0] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[-150, 0, 10]⟩, ⟨[0]⟩, ⟨[-25]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [-3, 0, 20] θ, polyEval [0] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[100, 0, -5]⟩, ⟨[0, 25, 0, -1]⟩, ⟨[25]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [2, 0, -10] θ, polyEval [0, 5, 0, -20] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[100, 0, -5]⟩, ⟨[0, 25, 0, -1]⟩, ⟨[-25]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [2, 0, -10] θ, polyEval [0, 5, 0, -20] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[100, 0, -5]⟩, ⟨[0, -25, 0, 1]⟩, ⟨[25]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [2, 0, -10] θ, polyEval [0, -5, 0, 20] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[100, 0, -5]⟩, ⟨[0, -25, 0, 1]⟩, ⟨[-25]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [2, 0, -10] θ, polyEval [0, -5, 0, 20] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[-100, 0, 5]⟩, ⟨[0, 25, 0, -1]⟩, ⟨[25]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [-2, 0, 10] θ, polyEval [0, 5, 0, -20] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt9 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[-100, 0, 5]⟩, ⟨[0, 25, 0, -1]⟩, ⟨[-25]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [-2, 0, 10] θ, polyEval [0, 5, 0, -20] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt10 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[-100, 0, 5]⟩, ⟨[0, -25, 0, 1]⟩, ⟨[25]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [-2, 0, 10] θ, polyEval [0, -5, 0, 20] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt11 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[-100, 0, 5]⟩, ⟨[0, -25, 0, 1]⟩, ⟨[-25]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [-2, 0, 10] θ, polyEval [0, -5, 0, 20] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt12 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[25]⟩, ⟨[0, 50, 0, -3]⟩, ⟨[25]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [1/2] θ, polyEval [0, 10, 0, -60] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt13 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[25]⟩, ⟨[0, 50, 0, -3]⟩, ⟨[-25]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [1/2] θ, polyEval [0, 10, 0, -60] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt14 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[25]⟩, ⟨[0, -50, 0, 3]⟩, ⟨[25]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [1/2] θ, polyEval [0, -10, 0, 60] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt15 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[25]⟩, ⟨[0, -50, 0, 3]⟩, ⟨[-25]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [1/2] θ, polyEval [0, -10, 0, 60] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt16 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[-25]⟩, ⟨[0, 50, 0, -3]⟩, ⟨[25]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [-1/2] θ, polyEval [0, 10, 0, -60] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt17 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[-25]⟩, ⟨[0, 50, 0, -3]⟩, ⟨[-25]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [-1/2] θ, polyEval [0, 10, 0, -60] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt18 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[-25]⟩, ⟨[0, -50, 0, 3]⟩, ⟨[25]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [-1/2] θ, polyEval [0, -10, 0, 60] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt19 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[-25]⟩, ⟨[0, -50, 0, 3]⟩, ⟨[-25]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [-1/2] θ, polyEval [0, -10, 0, 60] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt20 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[75, 0, -5]⟩, ⟨[0, 5]⟩, ⟨[25, 40, 0, -2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [3/2, 0, -10] θ, polyEval [0, 1] θ, polyEval [1/2, 8, 0, -40] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt21 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[75, 0, -5]⟩, ⟨[0, 5]⟩, ⟨[-25, -40, 0, 2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [3/2, 0, -10] θ, polyEval [0, 1] θ, polyEval [-1/2, -8, 0, 40] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt22 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[-75, 0, 5]⟩, ⟨[0, 5]⟩, ⟨[25, 40, 0, -2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [-3/2, 0, 10] θ, polyEval [0, 1] θ, polyEval [1/2, 8, 0, -40] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt23 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[-75, 0, 5]⟩, ⟨[0, 5]⟩, ⟨[-25, -40, 0, 2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [-3/2, 0, 10] θ, polyEval [0, 1] θ, polyEval [-1/2, -8, 0, 40] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt24 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[25]⟩, ⟨[0, -20, 0, 1]⟩, ⟨[25, 40, 0, -2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [1/2] θ, polyEval [0, -4, 0, 20] θ, polyEval [1/2, 8, 0, -40] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt25 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[25]⟩, ⟨[0, -20, 0, 1]⟩, ⟨[-25, -40, 0, 2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [1/2] θ, polyEval [0, -4, 0, 20] θ, polyEval [-1/2, -8, 0, 40] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt26 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[-25]⟩, ⟨[0, -20, 0, 1]⟩, ⟨[25, 40, 0, -2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [-1/2] θ, polyEval [0, -4, 0, 20] θ, polyEval [1/2, 8, 0, -40] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt27 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[-25]⟩, ⟨[0, -20, 0, 1]⟩, ⟨[-25, -40, 0, 2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [-1/2] θ, polyEval [0, -4, 0, 20] θ, polyEval [-1/2, -8, 0, 40] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt28 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0, 30, 0, -2]⟩, ⟨[25, 40, 0, -2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0] θ, polyEval [0, 6, 0, -40] θ, polyEval [1/2, 8, 0, -40] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt29 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0, 30, 0, -2]⟩, ⟨[-25, -40, 0, 2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0] θ, polyEval [0, 6, 0, -40] θ, polyEval [-1/2, -8, 0, 40] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt30 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[100, 0, -5]⟩, ⟨[0, -15, 0, 1]⟩, ⟨[25, 30, 0, -2]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [2, 0, -10] θ, polyEval [0, -3, 0, 20] θ, polyEval [1/2, 6, 0,
    -40] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt31 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[100, 0, -5]⟩, ⟨[0, -15, 0, 1]⟩, ⟨[-25, -30, 0, 2]⟩⟩
    : V3 (ZTheta root)) = ![polyEval [2, 0, -10] θ, polyEval [0, -3, 0, 20] θ, polyEval [-1/2, -6,
    0, 40] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt32 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[-100, 0, 5]⟩, ⟨[0, -15, 0, 1]⟩, ⟨[25, 30, 0, -2]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [-2, 0, 10] θ, polyEval [0, -3, 0, 20] θ, polyEval [1/2, 6, 0,
    -40] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt33 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[-100, 0, 5]⟩, ⟨[0, -15, 0, 1]⟩, ⟨[-25, -30, 0, 2]⟩⟩
    : V3 (ZTheta root)) = ![polyEval [-2, 0, 10] θ, polyEval [0, -3, 0, 20] θ, polyEval [-1/2, -6,
    0, 40] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt34 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[75, 0, -5]⟩, ⟨[0, 35, 0, -2]⟩, ⟨[25, 30, 0, -2]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [3/2, 0, -10] θ, polyEval [0, 7, 0, -40] θ, polyEval [1/2, 6, 0,
    -40] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt35 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[75, 0, -5]⟩, ⟨[0, 35, 0, -2]⟩, ⟨[-25, -30, 0, 2]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [3/2, 0, -10] θ, polyEval [0, 7, 0, -40] θ, polyEval [-1/2, -6,
    0, 40] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt36 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[-75, 0, 5]⟩, ⟨[0, 35, 0, -2]⟩, ⟨[25, 30, 0, -2]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [-3/2, 0, 10] θ, polyEval [0, 7, 0, -40] θ, polyEval [1/2, 6, 0,
    -40] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt37 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[-75, 0, 5]⟩, ⟨[0, 35, 0, -2]⟩, ⟨[-25, -30, 0, 2]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [-3/2, 0, 10] θ, polyEval [0, 7, 0, -40] θ, polyEval [-1/2, -6,
    0, 40] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt38 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0, -40, 0, 2]⟩, ⟨[25, 30, 0, -2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0] θ, polyEval [0, -8, 0, 40] θ, polyEval [1/2, 6, 0, -40] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt39 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0, -40, 0, 2]⟩, ⟨[-25, -30, 0, 2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0] θ, polyEval [0, -8, 0, 40] θ, polyEval [-1/2, -6, 0, 40] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem eq_smul : Johnson.ElongatedPentagonalOrthobirotunda.polyhedron = (Polyhedron.ofPoints points).smul (1 / 50) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17, pt18, pt19, pt20, pt21, pt22, pt23, pt24,
    pt25, pt26, pt27, pt28, pt29, pt30, pt31, pt32, pt33, pt34, pt35, pt36, pt37, pt38, pt39]

end Nieuwland.Polyhedra.JohnsonElongatedPentagonalOrthobirotundaDim

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/elongated-pentagonal-orthobirotunda` is full-dimensional.** -/
theorem johnsonElongatedPentagonalOrthobirotunda_fullDim : Johnson.ElongatedPentagonalOrthobirotunda.polyhedron.FullDim := by
  rw [JohnsonElongatedPentagonalOrthobirotundaDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk JohnsonElongatedPentagonalOrthobirotundaDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
