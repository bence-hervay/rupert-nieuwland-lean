import Polyhedra.Other.PentagonalTrapezohedron.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `trapezohedron/pentagonal-trapezohedron` is full-dimensional

The points of `Other.PentagonalTrapezohedron.polyhedron` times `100` as exact values in `ZTheta root`,
exported by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`,
checked by the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`),
and scaled back (`eq_smul`, `Polyhedron.FullDim.smul`), so is
`Other.PentagonalTrapezohedron.polyhedron`.
-/

namespace Nieuwland.Polyhedra.TrapezohedronPentagonalTrapezohedronDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Other.PentagonalTrapezohedron.theta

/-- The root `θ`, with `α = 5 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[-4/25, 8/5, -12/5, 0, 1], 11/16, 7/8,
    5, [-100, 200, -60, 0, 1],
    32, 122, 125, 140, 7,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    51763074359342891246441897351785657809452294539116482205702172666826530080858369350809644145561115765510336297269957908076498817185311673099608607029159254,
    51763074359342891246441897351785657809452294539116482205702172666826530080858369350809644145561115765510336297269957908076498817185311673099608607029159255,
    by decide +kernel⟩

theorem root_α : root.α = (5 : ℕ) * θ := rfl

theorem root_n : root.n = 4 := rfl

/-- The points of `Other.PentagonalTrapezohedron.polyhedron` times `100`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[0]⟩, ⟨[0]⟩, ⟨[-100]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0]⟩, ⟨[100]⟩⟩,
    ⟨⟨[0, 80, -10, -2]⟩, ⟨[0, -60, 10, 2]⟩, ⟨[-100, 160, -20, -4]⟩⟩,
    ⟨⟨[-50, 120, -15, -3]⟩, ⟨[-150, 170, -15, -4]⟩, ⟨[100, -160, 20, 4]⟩⟩,
    ⟨⟨[50, -120, 15, 3]⟩, ⟨[-150, 170, -15, -4]⟩, ⟨[-100, 160, -20, -4]⟩⟩,
    ⟨⟨[0, -80, 10, 2]⟩, ⟨[0, -60, 10, 2]⟩, ⟨[100, -160, 20, 4]⟩⟩,
    ⟨⟨[-100, 80, -10, -2]⟩, ⟨[0]⟩, ⟨[-100, 160, -20, -4]⟩⟩,
    ⟨⟨[0, -80, 10, 2]⟩, ⟨[0, 60, -10, -2]⟩, ⟨[100, -160, 20, 4]⟩⟩,
    ⟨⟨[50, -120, 15, 3]⟩, ⟨[150, -170, 15, 4]⟩, ⟨[-100, 160, -20, -4]⟩⟩,
    ⟨⟨[-50, 120, -15, -3]⟩, ⟨[150, -170, 15, 4]⟩, ⟨[100, -160, 20, 4]⟩⟩,
    ⟨⟨[0, 80, -10, -2]⟩, ⟨[0, 60, -10, -2]⟩, ⟨[-100, 160, -20, -4]⟩⟩,
    ⟨⟨[100, -80, 10, 2]⟩, ⟨[0]⟩, ⟨[100, -160, 20, 4]⟩⟩]

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

theorem pt2 : (1 / 100 : ℝ) • Exact.reV (⟨⟨[0, 80, -10, -2]⟩, ⟨[0, -60, 10, 2]⟩, ⟨[-100, 160,
    -20, -4]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 4, -5/2, -5/2] θ, polyEval [0, -3, 5/2, 5/2] θ,
    polyEval [-1, 8, -5, -5] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 100) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 100 : ℝ) • Exact.reV (⟨⟨[-50, 120, -15, -3]⟩, ⟨[-150, 170, -15, -4]⟩, ⟨[100,
    -160, 20, 4]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1/2, 6, -15/4, -15/4] θ, polyEval [-3/2, 17/2,
    -15/4, -5] θ, polyEval [1, -8, 5, 5] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 100) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 100 : ℝ) • Exact.reV (⟨⟨[50, -120, 15, 3]⟩, ⟨[-150, 170, -15, -4]⟩, ⟨[-100,
    160, -20, -4]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1/2, -6, 15/4, 15/4] θ, polyEval [-3/2, 17/2,
    -15/4, -5] θ, polyEval [-1, 8, -5, -5] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 100) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 100 : ℝ) • Exact.reV (⟨⟨[0, -80, 10, 2]⟩, ⟨[0, -60, 10, 2]⟩, ⟨[100, -160, 20,
    4]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, -4, 5/2, 5/2] θ, polyEval [0, -3, 5/2, 5/2] θ,
    polyEval [1, -8, 5, 5] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 100) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 100 : ℝ) • Exact.reV (⟨⟨[-100, 80, -10, -2]⟩, ⟨[0]⟩, ⟨[-100, 160, -20, -4]⟩⟩
    : V3 (ZTheta root)) = ![polyEval [-1, 4, -5/2, -5/2] θ, polyEval [0] θ, polyEval [-1, 8, -5, -5]
    θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 100) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 100 : ℝ) • Exact.reV (⟨⟨[0, -80, 10, 2]⟩, ⟨[0, 60, -10, -2]⟩, ⟨[100, -160,
    20, 4]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, -4, 5/2, 5/2] θ, polyEval [0, 3, -5/2, -5/2] θ,
    polyEval [1, -8, 5, 5] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 100) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 100 : ℝ) • Exact.reV (⟨⟨[50, -120, 15, 3]⟩, ⟨[150, -170, 15, 4]⟩, ⟨[-100,
    160, -20, -4]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1/2, -6, 15/4, 15/4] θ, polyEval [3/2, -17/2,
    15/4, 5] θ, polyEval [-1, 8, -5, -5] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 100) (by norm_num) (by decide +kernel)

theorem pt9 : (1 / 100 : ℝ) • Exact.reV (⟨⟨[-50, 120, -15, -3]⟩, ⟨[150, -170, 15, 4]⟩, ⟨[100,
    -160, 20, 4]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1/2, 6, -15/4, -15/4] θ, polyEval [3/2, -17/2,
    15/4, 5] θ, polyEval [1, -8, 5, 5] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 100) (by norm_num) (by decide +kernel)

theorem pt10 : (1 / 100 : ℝ) • Exact.reV (⟨⟨[0, 80, -10, -2]⟩, ⟨[0, 60, -10, -2]⟩, ⟨[-100, 160,
    -20, -4]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 4, -5/2, -5/2] θ, polyEval [0, 3, -5/2, -5/2] θ,
    polyEval [-1, 8, -5, -5] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 100) (by norm_num) (by decide +kernel)

theorem pt11 : (1 / 100 : ℝ) • Exact.reV (⟨⟨[100, -80, 10, 2]⟩, ⟨[0]⟩, ⟨[100, -160, 20, 4]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [1, -4, 5/2, 5/2] θ, polyEval [0] θ, polyEval [1, -8, 5, 5] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 100) (by norm_num) (by decide +kernel)

theorem eq_smul : Other.PentagonalTrapezohedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 100) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11]

end Nieuwland.Polyhedra.TrapezohedronPentagonalTrapezohedronDim

namespace Nieuwland.Polyhedra

/-- **The fixture `trapezohedron/pentagonal-trapezohedron` is full-dimensional.** -/
theorem trapezohedronPentagonalTrapezohedron_fullDim : Other.PentagonalTrapezohedron.polyhedron.FullDim := by
  rw [TrapezohedronPentagonalTrapezohedronDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk TrapezohedronPentagonalTrapezohedronDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
