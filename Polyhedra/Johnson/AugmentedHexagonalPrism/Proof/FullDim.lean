import Polyhedra.Johnson.AugmentedHexagonalPrism.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `johnson/augmented-hexagonal-prism` is full-dimensional

The points of `Johnson.AugmentedHexagonalPrism.polyhedron` times `80` as exact values in `ZTheta root`, exported
by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Johnson.AugmentedHexagonalPrism.polyhedron`.
-/

namespace Nieuwland.Polyhedra.JohnsonAugmentedHexagonalPrismDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Johnson.AugmentedHexagonalPrism.theta

/-- The root `θ`, with `α = 2 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[25/4, 0, -7, 0, 1], 3/2, 3,
    2, [100, 0, -28, 0, 1],
    16, 77, 80, 96, 9,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    65407512921789297968294306667379476209277563065068831281816664564185409890589647474671405609007974672244447165586614408828227676744752100251923686437131737,
    65407512921789297968294306667379476209277563065068831281816664564185409890589647474671405609007974672244447165586614408828227676744752100251923686437131738,
    by decide +kernel⟩

theorem root_α : root.α = (2 : ℕ) * θ := rfl

theorem root_n : root.n = 4 := rfl

/-- The points of `Johnson.AugmentedHexagonalPrism.polyhedron` times `80`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[80]⟩, ⟨[40]⟩, ⟨[0]⟩⟩,
    ⟨⟨[80]⟩, ⟨[-40]⟩, ⟨[0]⟩⟩,
    ⟨⟨[-80]⟩, ⟨[40]⟩, ⟨[0]⟩⟩,
    ⟨⟨[-80]⟩, ⟨[-40]⟩, ⟨[0]⟩⟩,
    ⟨⟨[40]⟩, ⟨[40]⟩, ⟨[0, 38, 0, -1]⟩⟩,
    ⟨⟨[40]⟩, ⟨[40]⟩, ⟨[0, -38, 0, 1]⟩⟩,
    ⟨⟨[40]⟩, ⟨[-40]⟩, ⟨[0, 38, 0, -1]⟩⟩,
    ⟨⟨[40]⟩, ⟨[-40]⟩, ⟨[0, -38, 0, 1]⟩⟩,
    ⟨⟨[-40]⟩, ⟨[40]⟩, ⟨[0, 38, 0, -1]⟩⟩,
    ⟨⟨[-40]⟩, ⟨[40]⟩, ⟨[0, -38, 0, 1]⟩⟩,
    ⟨⟨[-40]⟩, ⟨[-40]⟩, ⟨[0, 38, 0, -1]⟩⟩,
    ⟨⟨[-40]⟩, ⟨[-40]⟩, ⟨[0, -38, 0, 1]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0]⟩, ⟨[0, 2, 0, 1]⟩⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 80 : ℝ) • Exact.reV (⟨⟨[80]⟩, ⟨[40]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) = ![polyEval
    [1] θ, polyEval [1/2] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 80) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 80 : ℝ) • Exact.reV (⟨⟨[80]⟩, ⟨[-40]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [1] θ, polyEval [-1/2] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 80) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 80 : ℝ) • Exact.reV (⟨⟨[-80]⟩, ⟨[40]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [-1] θ, polyEval [1/2] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 80) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 80 : ℝ) • Exact.reV (⟨⟨[-80]⟩, ⟨[-40]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [-1] θ, polyEval [-1/2] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 80) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 80 : ℝ) • Exact.reV (⟨⟨[40]⟩, ⟨[40]⟩, ⟨[0, 38, 0, -1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [1/2] θ, polyEval [1/2] θ, polyEval [0, 19/20, 0, -1/10] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 80) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 80 : ℝ) • Exact.reV (⟨⟨[40]⟩, ⟨[40]⟩, ⟨[0, -38, 0, 1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [1/2] θ, polyEval [1/2] θ, polyEval [0, -19/20, 0, 1/10] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 80) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 80 : ℝ) • Exact.reV (⟨⟨[40]⟩, ⟨[-40]⟩, ⟨[0, 38, 0, -1]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [1/2] θ, polyEval [-1/2] θ, polyEval [0, 19/20, 0, -1/10] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 80) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 80 : ℝ) • Exact.reV (⟨⟨[40]⟩, ⟨[-40]⟩, ⟨[0, -38, 0, 1]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [1/2] θ, polyEval [-1/2] θ, polyEval [0, -19/20, 0, 1/10] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 80) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 80 : ℝ) • Exact.reV (⟨⟨[-40]⟩, ⟨[40]⟩, ⟨[0, 38, 0, -1]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [-1/2] θ, polyEval [1/2] θ, polyEval [0, 19/20, 0, -1/10] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 80) (by norm_num) (by decide +kernel)

theorem pt9 : (1 / 80 : ℝ) • Exact.reV (⟨⟨[-40]⟩, ⟨[40]⟩, ⟨[0, -38, 0, 1]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [-1/2] θ, polyEval [1/2] θ, polyEval [0, -19/20, 0, 1/10] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 80) (by norm_num) (by decide +kernel)

theorem pt10 : (1 / 80 : ℝ) • Exact.reV (⟨⟨[-40]⟩, ⟨[-40]⟩, ⟨[0, 38, 0, -1]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [-1/2] θ, polyEval [-1/2] θ, polyEval [0, 19/20, 0, -1/10] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 80) (by norm_num) (by decide +kernel)

theorem pt11 : (1 / 80 : ℝ) • Exact.reV (⟨⟨[-40]⟩, ⟨[-40]⟩, ⟨[0, -38, 0, 1]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [-1/2] θ, polyEval [-1/2] θ, polyEval [0, -19/20, 0, 1/10] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 80) (by norm_num) (by decide +kernel)

theorem pt12 : (1 / 80 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0]⟩, ⟨[0, 2, 0, 1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0] θ, polyEval [0] θ, polyEval [0, 1/20, 0, 1/10] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 80) (by norm_num) (by decide +kernel)

theorem eq_smul : Johnson.AugmentedHexagonalPrism.polyhedron = (Polyhedron.ofPoints points).smul (1 / 80) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12]

end Nieuwland.Polyhedra.JohnsonAugmentedHexagonalPrismDim

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/augmented-hexagonal-prism` is full-dimensional.** -/
theorem johnsonAugmentedHexagonalPrism_fullDim : Johnson.AugmentedHexagonalPrism.polyhedron.FullDim := by
  rw [JohnsonAugmentedHexagonalPrismDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk JohnsonAugmentedHexagonalPrismDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
