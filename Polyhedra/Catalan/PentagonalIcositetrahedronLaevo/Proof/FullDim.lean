import Polyhedra.Catalan.PentagonalIcositetrahedronLaevo.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `catalan/pentagonal-icositetrahedron-laevo` is full-dimensional

The points of `Catalan.PentagonalIcositetrahedronLaevo.polyhedron` times `2` as exact values in `ZTheta root`,
exported by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`,
checked by the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`),
and scaled back (`eq_smul`, `Polyhedron.FullDim.smul`), so is
`Catalan.PentagonalIcositetrahedronLaevo.polyhedron`.
-/

namespace Nieuwland.Polyhedra.CatalanPentagonalIcositetrahedronLaevoDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Catalan.PentagonalIcositetrahedronLaevo.theta

/-- The root `θ`, with `α = 1 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[-1, -1, -3, 1], 5/2, 4,
    1, [-1, -1, -3, 1],
    16, 53, 56, 64, 6,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    45358289327736897949013171839105691806285561455152620022257008162047727265564158526285244101884319116297389208740205532921051588384710914181966356713654841,
    45358289327736897949013171839105691806285561455152620022257008162047727265564158526285244101884319116297389208740205532921051588384710914181966356713654842,
    by decide +kernel⟩

theorem root_α : root.α = (1 : ℕ) * θ := rfl

theorem root_n : root.n = 3 := rfl

/-- The points of `Catalan.PentagonalIcositetrahedronLaevo.polyhedron` times `2`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[0]⟩, ⟨[0]⟩, ⟨[-1, 0, -1]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0]⟩, ⟨[1, 0, 1]⟩⟩,
    ⟨⟨[-1, 0, -1]⟩, ⟨[0]⟩, ⟨[0]⟩⟩,
    ⟨⟨[1, 0, 1]⟩, ⟨[0]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0]⟩, ⟨[-1, 0, -1]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0]⟩, ⟨[1, 0, 1]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0, -2]⟩, ⟨[2]⟩, ⟨[0, 4, -2]⟩⟩,
    ⟨⟨[0, -2]⟩, ⟨[-2]⟩, ⟨[0, -4, 2]⟩⟩,
    ⟨⟨[0, 2]⟩, ⟨[-2]⟩, ⟨[0, 4, -2]⟩⟩,
    ⟨⟨[0, 2]⟩, ⟨[2]⟩, ⟨[0, -4, 2]⟩⟩,
    ⟨⟨[0, 4, -2]⟩, ⟨[0, 2]⟩, ⟨[-2]⟩⟩,
    ⟨⟨[0, 4, -2]⟩, ⟨[0, -2]⟩, ⟨[2]⟩⟩,
    ⟨⟨[0, -4, 2]⟩, ⟨[0, -2]⟩, ⟨[-2]⟩⟩,
    ⟨⟨[0, -4, 2]⟩, ⟨[0, 2]⟩, ⟨[2]⟩⟩,
    ⟨⟨[-2]⟩, ⟨[0, -4, 2]⟩, ⟨[0, -2]⟩⟩,
    ⟨⟨[-2]⟩, ⟨[0, 4, -2]⟩, ⟨[0, 2]⟩⟩,
    ⟨⟨[2]⟩, ⟨[0, 4, -2]⟩, ⟨[0, -2]⟩⟩,
    ⟨⟨[2]⟩, ⟨[0, -4, 2]⟩, ⟨[0, 2]⟩⟩,
    ⟨⟨[-2]⟩, ⟨[0, -2]⟩, ⟨[0, 4, -2]⟩⟩,
    ⟨⟨[-2]⟩, ⟨[0, 2]⟩, ⟨[0, -4, 2]⟩⟩,
    ⟨⟨[2]⟩, ⟨[0, 2]⟩, ⟨[0, 4, -2]⟩⟩,
    ⟨⟨[2]⟩, ⟨[0, -2]⟩, ⟨[0, -4, 2]⟩⟩,
    ⟨⟨[0, 4, -2]⟩, ⟨[-2]⟩, ⟨[0, -2]⟩⟩,
    ⟨⟨[0, 4, -2]⟩, ⟨[2]⟩, ⟨[0, 2]⟩⟩,
    ⟨⟨[0, -4, 2]⟩, ⟨[2]⟩, ⟨[0, -2]⟩⟩,
    ⟨⟨[0, -4, 2]⟩, ⟨[-2]⟩, ⟨[0, 2]⟩⟩,
    ⟨⟨[0, -2]⟩, ⟨[0, 4, -2]⟩, ⟨[-2]⟩⟩,
    ⟨⟨[0, -2]⟩, ⟨[0, -4, 2]⟩, ⟨[2]⟩⟩,
    ⟨⟨[0, 2]⟩, ⟨[0, -4, 2]⟩, ⟨[-2]⟩⟩,
    ⟨⟨[0, 2]⟩, ⟨[0, 4, -2]⟩, ⟨[2]⟩⟩,
    ⟨⟨[0, -2]⟩, ⟨[0, -2]⟩, ⟨[0, -2]⟩⟩,
    ⟨⟨[0, -2]⟩, ⟨[0, -2]⟩, ⟨[0, 2]⟩⟩,
    ⟨⟨[0, -2]⟩, ⟨[0, 2]⟩, ⟨[0, -2]⟩⟩,
    ⟨⟨[0, -2]⟩, ⟨[0, 2]⟩, ⟨[0, 2]⟩⟩,
    ⟨⟨[0, 2]⟩, ⟨[0, -2]⟩, ⟨[0, -2]⟩⟩,
    ⟨⟨[0, 2]⟩, ⟨[0, -2]⟩, ⟨[0, 2]⟩⟩,
    ⟨⟨[0, 2]⟩, ⟨[0, 2]⟩, ⟨[0, -2]⟩⟩,
    ⟨⟨[0, 2]⟩, ⟨[0, 2]⟩, ⟨[0, 2]⟩⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0]⟩, ⟨[-1, 0, -1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0] θ, polyEval [0] θ, polyEval [-1/2, 0, -1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0]⟩, ⟨[1, 0, 1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0] θ, polyEval [0] θ, polyEval [1/2, 0, 1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[-1, 0, -1]⟩, ⟨[0]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [-1/2, 0, -1/2] θ, polyEval [0] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[1, 0, 1]⟩, ⟨[0]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [1/2, 0, 1/2] θ, polyEval [0] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[-1, 0, -1]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0] θ, polyEval [-1/2, 0, -1/2] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[1, 0, 1]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0] θ, polyEval [1/2, 0, 1/2] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -2]⟩, ⟨[2]⟩, ⟨[0, 4, -2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, -1] θ, polyEval [1] θ, polyEval [0, 2, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -2]⟩, ⟨[-2]⟩, ⟨[0, -4, 2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, -1] θ, polyEval [-1] θ, polyEval [0, -2, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 2]⟩, ⟨[-2]⟩, ⟨[0, 4, -2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1] θ, polyEval [-1] θ, polyEval [0, 2, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt9 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 2]⟩, ⟨[2]⟩, ⟨[0, -4, 2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1] θ, polyEval [1] θ, polyEval [0, -2, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt10 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 4, -2]⟩, ⟨[0, 2]⟩, ⟨[-2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 2, -1] θ, polyEval [0, 1] θ, polyEval [-1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt11 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 4, -2]⟩, ⟨[0, -2]⟩, ⟨[2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 2, -1] θ, polyEval [0, -1] θ, polyEval [1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt12 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -4, 2]⟩, ⟨[0, -2]⟩, ⟨[-2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, -2, 1] θ, polyEval [0, -1] θ, polyEval [-1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt13 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -4, 2]⟩, ⟨[0, 2]⟩, ⟨[2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, -2, 1] θ, polyEval [0, 1] θ, polyEval [1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt14 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[-2]⟩, ⟨[0, -4, 2]⟩, ⟨[0, -2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [-1] θ, polyEval [0, -2, 1] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt15 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[-2]⟩, ⟨[0, 4, -2]⟩, ⟨[0, 2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [-1] θ, polyEval [0, 2, -1] θ, polyEval [0, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt16 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[2]⟩, ⟨[0, 4, -2]⟩, ⟨[0, -2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [1] θ, polyEval [0, 2, -1] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt17 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[2]⟩, ⟨[0, -4, 2]⟩, ⟨[0, 2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [1] θ, polyEval [0, -2, 1] θ, polyEval [0, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt18 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[-2]⟩, ⟨[0, -2]⟩, ⟨[0, 4, -2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [-1] θ, polyEval [0, -1] θ, polyEval [0, 2, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt19 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[-2]⟩, ⟨[0, 2]⟩, ⟨[0, -4, 2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [-1] θ, polyEval [0, 1] θ, polyEval [0, -2, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt20 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[2]⟩, ⟨[0, 2]⟩, ⟨[0, 4, -2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [1] θ, polyEval [0, 1] θ, polyEval [0, 2, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt21 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[2]⟩, ⟨[0, -2]⟩, ⟨[0, -4, 2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [1] θ, polyEval [0, -1] θ, polyEval [0, -2, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt22 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 4, -2]⟩, ⟨[-2]⟩, ⟨[0, -2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 2, -1] θ, polyEval [-1] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt23 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 4, -2]⟩, ⟨[2]⟩, ⟨[0, 2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 2, -1] θ, polyEval [1] θ, polyEval [0, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt24 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -4, 2]⟩, ⟨[2]⟩, ⟨[0, -2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, -2, 1] θ, polyEval [1] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt25 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -4, 2]⟩, ⟨[-2]⟩, ⟨[0, 2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, -2, 1] θ, polyEval [-1] θ, polyEval [0, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt26 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -2]⟩, ⟨[0, 4, -2]⟩, ⟨[-2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, -1] θ, polyEval [0, 2, -1] θ, polyEval [-1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt27 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -2]⟩, ⟨[0, -4, 2]⟩, ⟨[2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, -1] θ, polyEval [0, -2, 1] θ, polyEval [1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt28 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 2]⟩, ⟨[0, -4, 2]⟩, ⟨[-2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1] θ, polyEval [0, -2, 1] θ, polyEval [-1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt29 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 2]⟩, ⟨[0, 4, -2]⟩, ⟨[2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1] θ, polyEval [0, 2, -1] θ, polyEval [1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt30 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -2]⟩, ⟨[0, -2]⟩, ⟨[0, -2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, -1] θ, polyEval [0, -1] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt31 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -2]⟩, ⟨[0, -2]⟩, ⟨[0, 2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, -1] θ, polyEval [0, -1] θ, polyEval [0, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt32 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -2]⟩, ⟨[0, 2]⟩, ⟨[0, -2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, -1] θ, polyEval [0, 1] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt33 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -2]⟩, ⟨[0, 2]⟩, ⟨[0, 2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, -1] θ, polyEval [0, 1] θ, polyEval [0, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt34 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 2]⟩, ⟨[0, -2]⟩, ⟨[0, -2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1] θ, polyEval [0, -1] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt35 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 2]⟩, ⟨[0, -2]⟩, ⟨[0, 2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1] θ, polyEval [0, -1] θ, polyEval [0, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt36 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 2]⟩, ⟨[0, 2]⟩, ⟨[0, -2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1] θ, polyEval [0, 1] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt37 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 2]⟩, ⟨[0, 2]⟩, ⟨[0, 2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1] θ, polyEval [0, 1] θ, polyEval [0, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem eq_smul : Catalan.PentagonalIcositetrahedronLaevo.polyhedron = (Polyhedron.ofPoints points).smul (1 / 2) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17, pt18, pt19, pt20, pt21, pt22, pt23, pt24,
    pt25, pt26, pt27, pt28, pt29, pt30, pt31, pt32, pt33, pt34, pt35, pt36, pt37]

end Nieuwland.Polyhedra.CatalanPentagonalIcositetrahedronLaevoDim

namespace Nieuwland.Polyhedra

/-- **The fixture `catalan/pentagonal-icositetrahedron-laevo` is full-dimensional.** -/
theorem catalanPentagonalIcositetrahedronLaevo_fullDim : Catalan.PentagonalIcositetrahedronLaevo.polyhedron.FullDim := by
  rw [CatalanPentagonalIcositetrahedronLaevoDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk CatalanPentagonalIcositetrahedronLaevoDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
