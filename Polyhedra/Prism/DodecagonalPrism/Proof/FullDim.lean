import Polyhedra.Prism.DodecagonalPrism.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `prism/dodecagonal-prism` is full-dimensional

The points of `Prism.DodecagonalPrism.polyhedron` times `2` as exact values in `ZTheta root`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Prism.DodecagonalPrism.polyhedron`.
-/

namespace Nieuwland.Polyhedra.PrismDodecagonalPrismDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Prism.DodecagonalPrism.theta

/-- The root `θ`, with `α = 1 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[1, 0, -4, 0, 1], 1, 5/2,
    1, [1, 0, -4, 0, 1],
    32, 60, 63, 80, 11,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    25901895906909850606738743570489423433491659194460218061804454554618648006849202956996943349000449476777019418450853860963428028552630516390646891611415319,
    25901895906909850606738743570489423433491659194460218061804454554618648006849202956996943349000449476777019418450853860963428028552630516390646891611415320,
    by decide +kernel⟩

theorem root_α : root.α = (1 : ℕ) * θ := rfl

theorem root_n : root.n = 4 := rfl

/-- The points of `Prism.DodecagonalPrism.polyhedron` times `2`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[0, 2]⟩, ⟨[0]⟩, ⟨[-1]⟩⟩,
    ⟨⟨[0, -2, 0, 1]⟩, ⟨[0, 1]⟩, ⟨[-1]⟩⟩,
    ⟨⟨[0, 1]⟩, ⟨[0, -2, 0, 1]⟩, ⟨[-1]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0, 2]⟩, ⟨[-1]⟩⟩,
    ⟨⟨[0, -1]⟩, ⟨[0, -2, 0, 1]⟩, ⟨[-1]⟩⟩,
    ⟨⟨[0, 2, 0, -1]⟩, ⟨[0, 1]⟩, ⟨[-1]⟩⟩,
    ⟨⟨[0, -2]⟩, ⟨[0]⟩, ⟨[-1]⟩⟩,
    ⟨⟨[0, 2, 0, -1]⟩, ⟨[0, -1]⟩, ⟨[-1]⟩⟩,
    ⟨⟨[0, -1]⟩, ⟨[0, 2, 0, -1]⟩, ⟨[-1]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0, -2]⟩, ⟨[-1]⟩⟩,
    ⟨⟨[0, 1]⟩, ⟨[0, 2, 0, -1]⟩, ⟨[-1]⟩⟩,
    ⟨⟨[0, -2, 0, 1]⟩, ⟨[0, -1]⟩, ⟨[-1]⟩⟩,
    ⟨⟨[0, 2]⟩, ⟨[0]⟩, ⟨[1]⟩⟩,
    ⟨⟨[0, -2, 0, 1]⟩, ⟨[0, 1]⟩, ⟨[1]⟩⟩,
    ⟨⟨[0, 1]⟩, ⟨[0, -2, 0, 1]⟩, ⟨[1]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0, 2]⟩, ⟨[1]⟩⟩,
    ⟨⟨[0, -1]⟩, ⟨[0, -2, 0, 1]⟩, ⟨[1]⟩⟩,
    ⟨⟨[0, 2, 0, -1]⟩, ⟨[0, 1]⟩, ⟨[1]⟩⟩,
    ⟨⟨[0, -2]⟩, ⟨[0]⟩, ⟨[1]⟩⟩,
    ⟨⟨[0, 2, 0, -1]⟩, ⟨[0, -1]⟩, ⟨[1]⟩⟩,
    ⟨⟨[0, -1]⟩, ⟨[0, 2, 0, -1]⟩, ⟨[1]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0, -2]⟩, ⟨[1]⟩⟩,
    ⟨⟨[0, 1]⟩, ⟨[0, 2, 0, -1]⟩, ⟨[1]⟩⟩,
    ⟨⟨[0, -2, 0, 1]⟩, ⟨[0, -1]⟩, ⟨[1]⟩⟩]

theorem span_ok : spanOk points 0 1 2 12 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 2]⟩, ⟨[0]⟩, ⟨[-1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1] θ, polyEval [0] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -2, 0, 1]⟩, ⟨[0, 1]⟩, ⟨[-1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, -1, 0, 1/2] θ, polyEval [0, 1/2] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 1]⟩, ⟨[0, -2, 0, 1]⟩, ⟨[-1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1/2] θ, polyEval [0, -1, 0, 1/2] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0, 2]⟩, ⟨[-1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0] θ, polyEval [0, 1] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -1]⟩, ⟨[0, -2, 0, 1]⟩, ⟨[-1]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [0, -1/2] θ, polyEval [0, -1, 0, 1/2] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 2, 0, -1]⟩, ⟨[0, 1]⟩, ⟨[-1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1, 0, -1/2] θ, polyEval [0, 1/2] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -2]⟩, ⟨[0]⟩, ⟨[-1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, -1] θ, polyEval [0] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 2, 0, -1]⟩, ⟨[0, -1]⟩, ⟨[-1]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [0, 1, 0, -1/2] θ, polyEval [0, -1/2] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -1]⟩, ⟨[0, 2, 0, -1]⟩, ⟨[-1]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [0, -1/2] θ, polyEval [0, 1, 0, -1/2] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt9 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0, -2]⟩, ⟨[-1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0] θ, polyEval [0, -1] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt10 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 1]⟩, ⟨[0, 2, 0, -1]⟩, ⟨[-1]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [0, 1/2] θ, polyEval [0, 1, 0, -1/2] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt11 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -2, 0, 1]⟩, ⟨[0, -1]⟩, ⟨[-1]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [0, -1, 0, 1/2] θ, polyEval [0, -1/2] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt12 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 2]⟩, ⟨[0]⟩, ⟨[1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1] θ, polyEval [0] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt13 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -2, 0, 1]⟩, ⟨[0, 1]⟩, ⟨[1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, -1, 0, 1/2] θ, polyEval [0, 1/2] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt14 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 1]⟩, ⟨[0, -2, 0, 1]⟩, ⟨[1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1/2] θ, polyEval [0, -1, 0, 1/2] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt15 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0, 2]⟩, ⟨[1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0] θ, polyEval [0, 1] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt16 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -1]⟩, ⟨[0, -2, 0, 1]⟩, ⟨[1]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [0, -1/2] θ, polyEval [0, -1, 0, 1/2] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt17 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 2, 0, -1]⟩, ⟨[0, 1]⟩, ⟨[1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1, 0, -1/2] θ, polyEval [0, 1/2] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt18 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -2]⟩, ⟨[0]⟩, ⟨[1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, -1] θ, polyEval [0] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt19 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 2, 0, -1]⟩, ⟨[0, -1]⟩, ⟨[1]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [0, 1, 0, -1/2] θ, polyEval [0, -1/2] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt20 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -1]⟩, ⟨[0, 2, 0, -1]⟩, ⟨[1]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [0, -1/2] θ, polyEval [0, 1, 0, -1/2] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt21 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0, -2]⟩, ⟨[1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0] θ, polyEval [0, -1] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt22 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, 1]⟩, ⟨[0, 2, 0, -1]⟩, ⟨[1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1/2] θ, polyEval [0, 1, 0, -1/2] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt23 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0, -2, 0, 1]⟩, ⟨[0, -1]⟩, ⟨[1]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [0, -1, 0, 1/2] θ, polyEval [0, -1/2] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem eq_smul : Prism.DodecagonalPrism.polyhedron = (Polyhedron.ofPoints points).smul (1 / 2) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17, pt18, pt19, pt20, pt21, pt22, pt23]

end Nieuwland.Polyhedra.PrismDodecagonalPrismDim

namespace Nieuwland.Polyhedra

/-- **The fixture `prism/dodecagonal-prism` is full-dimensional.** -/
theorem prismDodecagonalPrism_fullDim : Prism.DodecagonalPrism.polyhedron.FullDim := by
  rw [PrismDodecagonalPrismDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk PrismDodecagonalPrismDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
