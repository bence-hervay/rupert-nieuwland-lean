import Polyhedra.Antiprism.HexagonalAntiprism.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `prism/hexagonal-antiprism` is full-dimensional

The points of `Antiprism.HexagonalAntiprism.polyhedron` times `2` as exact values in `ZTheta root`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Antiprism.HexagonalAntiprism.polyhedron`.
-/

namespace Nieuwland.Polyhedra.PrismHexagonalAntiprismDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Antiprism.HexagonalAntiprism.theta

/-- The root `θ`, with `α = 2 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[-1/8, 0, 1/2, 0, 1], 0, 3/4,
    2, [-2, 0, 2, 0, 1],
    16, 12, 15, 24, 10,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    11471716136380750766922875677031602598377299957506993800470868357626435956850828877950875064772353740633881546754317532077573490596404023715337957565158944,
    11471716136380750766922875677031602598377299957506993800470868357626435956850828877950875064772353740633881546754317532077573490596404023715337957565158945,
    by decide +kernel⟩

theorem root_α : root.α = (2 : ℕ) * θ := rfl

theorem root_n : root.n = 4 := rfl

/-- The points of `Antiprism.HexagonalAntiprism.polyhedron` times `2`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[2]⟩, ⟨[0]⟩, ⟨[0, -1]⟩⟩,
    ⟨⟨[1]⟩, ⟨[1, 0, 1]⟩, ⟨[0, -1]⟩⟩,
    ⟨⟨[-1]⟩, ⟨[1, 0, 1]⟩, ⟨[0, -1]⟩⟩,
    ⟨⟨[-2]⟩, ⟨[0]⟩, ⟨[0, -1]⟩⟩,
    ⟨⟨[-1]⟩, ⟨[-1, 0, -1]⟩, ⟨[0, -1]⟩⟩,
    ⟨⟨[1]⟩, ⟨[-1, 0, -1]⟩, ⟨[0, -1]⟩⟩,
    ⟨⟨[1, 0, 1]⟩, ⟨[1]⟩, ⟨[0, 1]⟩⟩,
    ⟨⟨[0]⟩, ⟨[2]⟩, ⟨[0, 1]⟩⟩,
    ⟨⟨[-1, 0, -1]⟩, ⟨[1]⟩, ⟨[0, 1]⟩⟩,
    ⟨⟨[-1, 0, -1]⟩, ⟨[-1]⟩, ⟨[0, 1]⟩⟩,
    ⟨⟨[0]⟩, ⟨[-2]⟩, ⟨[0, 1]⟩⟩,
    ⟨⟨[1, 0, 1]⟩, ⟨[-1]⟩, ⟨[0, 1]⟩⟩]

theorem span_ok : spanOk points 0 1 2 6 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[2]⟩, ⟨[0]⟩, ⟨[0, -1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [1] θ, polyEval [0] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[1]⟩, ⟨[1, 0, 1]⟩, ⟨[0, -1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [1/2] θ, polyEval [1/2, 0, 2] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[-1]⟩, ⟨[1, 0, 1]⟩, ⟨[0, -1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [-1/2] θ, polyEval [1/2, 0, 2] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[-2]⟩, ⟨[0]⟩, ⟨[0, -1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [-1] θ, polyEval [0] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[-1]⟩, ⟨[-1, 0, -1]⟩, ⟨[0, -1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [-1/2] θ, polyEval [-1/2, 0, -2] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[1]⟩, ⟨[-1, 0, -1]⟩, ⟨[0, -1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [1/2] θ, polyEval [-1/2, 0, -2] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[1, 0, 1]⟩, ⟨[1]⟩, ⟨[0, 1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [1/2, 0, 2] θ, polyEval [1/2] θ, polyEval [0, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[2]⟩, ⟨[0, 1]⟩⟩ : V3 (ZTheta root)) = ![polyEval
    [0] θ, polyEval [1] θ, polyEval [0, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[-1, 0, -1]⟩, ⟨[1]⟩, ⟨[0, 1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [-1/2, 0, -2] θ, polyEval [1/2] θ, polyEval [0, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt9 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[-1, 0, -1]⟩, ⟨[-1]⟩, ⟨[0, 1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [-1/2, 0, -2] θ, polyEval [-1/2] θ, polyEval [0, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt10 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[-2]⟩, ⟨[0, 1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0] θ, polyEval [-1] θ, polyEval [0, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem pt11 : (1 / 2 : ℝ) • Exact.reV (⟨⟨[1, 0, 1]⟩, ⟨[-1]⟩, ⟨[0, 1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [1/2, 0, 2] θ, polyEval [-1/2] θ, polyEval [0, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 2) (by norm_num) (by decide +kernel)

theorem eq_smul : Antiprism.HexagonalAntiprism.polyhedron = (Polyhedron.ofPoints points).smul (1 / 2) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11]

end Nieuwland.Polyhedra.PrismHexagonalAntiprismDim

namespace Nieuwland.Polyhedra

/-- **The fixture `prism/hexagonal-antiprism` is full-dimensional.** -/
theorem prismHexagonalAntiprism_fullDim : Antiprism.HexagonalAntiprism.polyhedron.FullDim := by
  rw [PrismHexagonalAntiprismDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk PrismHexagonalAntiprismDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
