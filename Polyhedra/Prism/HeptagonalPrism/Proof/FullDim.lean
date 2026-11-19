import Polyhedra.Prism.HeptagonalPrism.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `prism/heptagonal-prism` is full-dimensional

The points of `Prism.HeptagonalPrism.polyhedron` times `4802` as exact values in `ZTheta root`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Prism.HeptagonalPrism.polyhedron`.
-/

namespace Nieuwland.Polyhedra.PrismHeptagonalPrismDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Prism.HeptagonalPrism.theta

/-- The root `θ`, with `α = 14 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[-1/448, 0, 1/16, 0, -1/2, 0, 1], 7/32, 5/16,
    14, [-16807, 0, 2401, 0, -98, 0, 1],
    32, 113, 116, 140, 9,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    48134151426415581807038527125188604723642344153283395107769661188425797736723326968990542570823508272646626254697255891680865099040494225764499673065593032,
    48134151426415581807038527125188604723642344153283395107769661188425797736723326968990542570823508272646626254697255891680865099040494225764499673065593033,
    by decide +kernel⟩

theorem root_α : root.α = (14 : ℕ) * θ := rfl

theorem root_n : root.n = 6 := rfl

/-- The points of `Prism.HeptagonalPrism.polyhedron` times `4802`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[24010, 0, -1715, 0, 21]⟩, ⟨[0, -343]⟩, ⟨[2401]⟩⟩,
    ⟨⟨[24010, 0, -1715, 0, 21]⟩, ⟨[0, -343]⟩, ⟨[-2401]⟩⟩,
    ⟨⟨[-24010, 0, 1715, 0, -21]⟩, ⟨[0, -343]⟩, ⟨[2401]⟩⟩,
    ⟨⟨[-24010, 0, 1715, 0, -21]⟩, ⟨[0, -343]⟩, ⟨[-2401]⟩⟩,
    ⟨⟨[12005, 0, -686, 0, 7]⟩, ⟨[0, 2058, 0, -98, 0, 1]⟩, ⟨[2401]⟩⟩,
    ⟨⟨[12005, 0, -686, 0, 7]⟩, ⟨[0, 2058, 0, -98, 0, 1]⟩, ⟨[-2401]⟩⟩,
    ⟨⟨[-12005, 0, 686, 0, -7]⟩, ⟨[0, 2058, 0, -98, 0, 1]⟩, ⟨[2401]⟩⟩,
    ⟨⟨[-12005, 0, 686, 0, -7]⟩, ⟨[0, 2058, 0, -98, 0, 1]⟩, ⟨[-2401]⟩⟩,
    ⟨⟨[2401]⟩, ⟨[0, -5145, 0, 343, 0, -4]⟩, ⟨[2401]⟩⟩,
    ⟨⟨[2401]⟩, ⟨[0, -5145, 0, 343, 0, -4]⟩, ⟨[-2401]⟩⟩,
    ⟨⟨[-2401]⟩, ⟨[0, -5145, 0, 343, 0, -4]⟩, ⟨[2401]⟩⟩,
    ⟨⟨[-2401]⟩, ⟨[0, -5145, 0, 343, 0, -4]⟩, ⟨[-2401]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0, 6860, 0, -490, 0, 6]⟩, ⟨[2401]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0, 6860, 0, -490, 0, 6]⟩, ⟨[-2401]⟩⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 4802 : ℝ) • Exact.reV (⟨⟨[24010, 0, -1715, 0, 21]⟩, ⟨[0, -343]⟩, ⟨[2401]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [5, 0, -70, 0, 168] θ, polyEval [0, -1] θ, polyEval [1/2] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 4802) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 4802 : ℝ) • Exact.reV (⟨⟨[24010, 0, -1715, 0, 21]⟩, ⟨[0, -343]⟩, ⟨[-2401]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [5, 0, -70, 0, 168] θ, polyEval [0, -1] θ, polyEval [-1/2] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 4802) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 4802 : ℝ) • Exact.reV (⟨⟨[-24010, 0, 1715, 0, -21]⟩, ⟨[0, -343]⟩, ⟨[2401]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [-5, 0, 70, 0, -168] θ, polyEval [0, -1] θ, polyEval [1/2] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 4802) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 4802 : ℝ) • Exact.reV (⟨⟨[-24010, 0, 1715, 0, -21]⟩, ⟨[0, -343]⟩, ⟨[-2401]⟩⟩
    : V3 (ZTheta root)) = ![polyEval [-5, 0, 70, 0, -168] θ, polyEval [0, -1] θ, polyEval [-1/2] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 4802) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 4802 : ℝ) • Exact.reV (⟨⟨[12005, 0, -686, 0, 7]⟩, ⟨[0, 2058, 0, -98, 0, 1]⟩,
    ⟨[2401]⟩⟩ : V3 (ZTheta root)) = ![polyEval [5/2, 0, -28, 0, 56] θ, polyEval [0, 6, 0, -56, 0,
    112] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 4802) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 4802 : ℝ) • Exact.reV (⟨⟨[12005, 0, -686, 0, 7]⟩, ⟨[0, 2058, 0, -98, 0, 1]⟩,
    ⟨[-2401]⟩⟩ : V3 (ZTheta root)) = ![polyEval [5/2, 0, -28, 0, 56] θ, polyEval [0, 6, 0, -56, 0,
    112] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 4802) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 4802 : ℝ) • Exact.reV (⟨⟨[-12005, 0, 686, 0, -7]⟩, ⟨[0, 2058, 0, -98, 0, 1]⟩,
    ⟨[2401]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-5/2, 0, 28, 0, -56] θ, polyEval [0, 6, 0, -56, 0,
    112] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 4802) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 4802 : ℝ) • Exact.reV (⟨⟨[-12005, 0, 686, 0, -7]⟩, ⟨[0, 2058, 0, -98, 0, 1]⟩,
    ⟨[-2401]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-5/2, 0, 28, 0, -56] θ, polyEval [0, 6, 0, -56, 0,
    112] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 4802) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 4802 : ℝ) • Exact.reV (⟨⟨[2401]⟩, ⟨[0, -5145, 0, 343, 0, -4]⟩, ⟨[2401]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [1/2] θ, polyEval [0, -15, 0, 196, 0, -448] θ, polyEval [1/2] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 4802) (by norm_num) (by decide +kernel)

theorem pt9 : (1 / 4802 : ℝ) • Exact.reV (⟨⟨[2401]⟩, ⟨[0, -5145, 0, 343, 0, -4]⟩, ⟨[-2401]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [1/2] θ, polyEval [0, -15, 0, 196, 0, -448] θ, polyEval [-1/2] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 4802) (by norm_num) (by decide +kernel)

theorem pt10 : (1 / 4802 : ℝ) • Exact.reV (⟨⟨[-2401]⟩, ⟨[0, -5145, 0, 343, 0, -4]⟩, ⟨[2401]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [-1/2] θ, polyEval [0, -15, 0, 196, 0, -448] θ, polyEval [1/2] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 4802) (by norm_num) (by decide +kernel)

theorem pt11 : (1 / 4802 : ℝ) • Exact.reV (⟨⟨[-2401]⟩, ⟨[0, -5145, 0, 343, 0, -4]⟩, ⟨[-2401]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [-1/2] θ, polyEval [0, -15, 0, 196, 0, -448] θ, polyEval [-1/2]
    θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 4802) (by norm_num) (by decide +kernel)

theorem pt12 : (1 / 4802 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0, 6860, 0, -490, 0, 6]⟩, ⟨[2401]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0] θ, polyEval [0, 20, 0, -280, 0, 672] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 4802) (by norm_num) (by decide +kernel)

theorem pt13 : (1 / 4802 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0, 6860, 0, -490, 0, 6]⟩, ⟨[-2401]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0] θ, polyEval [0, 20, 0, -280, 0, 672] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 4802) (by norm_num) (by decide +kernel)

theorem eq_smul : Prism.HeptagonalPrism.polyhedron = (Polyhedron.ofPoints points).smul (1 / 4802) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13]

end Nieuwland.Polyhedra.PrismHeptagonalPrismDim

namespace Nieuwland.Polyhedra

/-- **The fixture `prism/heptagonal-prism` is full-dimensional.** -/
theorem prismHeptagonalPrism_fullDim : Prism.HeptagonalPrism.polyhedron.FullDim := by
  rw [PrismHeptagonalPrismDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk PrismHeptagonalPrismDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
