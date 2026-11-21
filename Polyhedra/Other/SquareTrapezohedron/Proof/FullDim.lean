import Polyhedra.Other.SquareTrapezohedron.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `trapezohedron/square-trapezohedron` is full-dimensional

The points of `Other.SquareTrapezohedron.polyhedron` times `3` as exact values in `ZTheta root`,
exported by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`,
checked by the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`),
and scaled back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Other.SquareTrapezohedron.polyhedron`.
-/

namespace Nieuwland.Polyhedra.TrapezohedronSquareTrapezohedronDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Other.SquareTrapezohedron.theta

/-- The root `θ`, with `α = 1 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[-2, 0, 8, 0, 1], 0, 3/4,
    1, [-2, 0, 8, 0, 1],
    32, 14, 17, 24, 6,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    6604494662520472285326771214064397502883909739879984131786864615586737719642059537026871292055307391770650630539988792944705612545994208286002820554494191,
    6604494662520472285326771214064397502883909739879984131786864615586737719642059537026871292055307391770650630539988792944705612545994208286002820554494192,
    by decide +kernel⟩

theorem root_α : root.α = (1 : ℕ) * θ := rfl

theorem root_n : root.n = 4 := rfl

/-- The points of `Other.SquareTrapezohedron.polyhedron` times `3`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[0]⟩, ⟨[0]⟩, ⟨[-3]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0]⟩, ⟨[3]⟩⟩,
    ⟨⟨[0, 3]⟩, ⟨[0, 3]⟩, ⟨[-1, 0, 2]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0, 4, 0, 1]⟩, ⟨[1, 0, -2]⟩⟩,
    ⟨⟨[0, -3]⟩, ⟨[0, 3]⟩, ⟨[-1, 0, 2]⟩⟩,
    ⟨⟨[0, -4, 0, -1]⟩, ⟨[0]⟩, ⟨[1, 0, -2]⟩⟩,
    ⟨⟨[0, -3]⟩, ⟨[0, -3]⟩, ⟨[-1, 0, 2]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0, -4, 0, -1]⟩, ⟨[1, 0, -2]⟩⟩,
    ⟨⟨[0, 3]⟩, ⟨[0, -3]⟩, ⟨[-1, 0, 2]⟩⟩,
    ⟨⟨[0, 4, 0, 1]⟩, ⟨[0]⟩, ⟨[1, 0, -2]⟩⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 3 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0]⟩, ⟨[-3]⟩⟩ : V3 (ZTheta root)) = ![polyEval
    [0] θ, polyEval [0] θ, polyEval [-1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 3) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 3 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0]⟩, ⟨[3]⟩⟩ : V3 (ZTheta root)) = ![polyEval
    [0] θ, polyEval [0] θ, polyEval [1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 3) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 3 : ℝ) • Exact.reV (⟨⟨[0, 3]⟩, ⟨[0, 3]⟩, ⟨[-1, 0, 2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1] θ, polyEval [0, 1] θ, polyEval [-1/3, 0, 2/3] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 3) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 3 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0, 4, 0, 1]⟩, ⟨[1, 0, -2]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [0] θ, polyEval [0, 4/3, 0, 1/3] θ, polyEval [1/3, 0, -2/3] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 3) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 3 : ℝ) • Exact.reV (⟨⟨[0, -3]⟩, ⟨[0, 3]⟩, ⟨[-1, 0, 2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, -1] θ, polyEval [0, 1] θ, polyEval [-1/3, 0, 2/3] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 3) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 3 : ℝ) • Exact.reV (⟨⟨[0, -4, 0, -1]⟩, ⟨[0]⟩, ⟨[1, 0, -2]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [0, -4/3, 0, -1/3] θ, polyEval [0] θ, polyEval [1/3, 0, -2/3] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 3) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 3 : ℝ) • Exact.reV (⟨⟨[0, -3]⟩, ⟨[0, -3]⟩, ⟨[-1, 0, 2]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [0, -1] θ, polyEval [0, -1] θ, polyEval [-1/3, 0, 2/3] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 3) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 3 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0, -4, 0, -1]⟩, ⟨[1, 0, -2]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [0] θ, polyEval [0, -4/3, 0, -1/3] θ, polyEval [1/3, 0, -2/3] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 3) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 3 : ℝ) • Exact.reV (⟨⟨[0, 3]⟩, ⟨[0, -3]⟩, ⟨[-1, 0, 2]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1] θ, polyEval [0, -1] θ, polyEval [-1/3, 0, 2/3] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 3) (by norm_num) (by decide +kernel)

theorem pt9 : (1 / 3 : ℝ) • Exact.reV (⟨⟨[0, 4, 0, 1]⟩, ⟨[0]⟩, ⟨[1, 0, -2]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [0, 4/3, 0, 1/3] θ, polyEval [0] θ, polyEval [1/3, 0, -2/3] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 3) (by norm_num) (by decide +kernel)

theorem eq_smul : Other.SquareTrapezohedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 3) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9]

end Nieuwland.Polyhedra.TrapezohedronSquareTrapezohedronDim

namespace Nieuwland.Polyhedra

/-- **The fixture `trapezohedron/square-trapezohedron` is full-dimensional.** -/
theorem trapezohedronSquareTrapezohedron_fullDim : Other.SquareTrapezohedron.polyhedron.FullDim := by
  rw [TrapezohedronSquareTrapezohedronDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk TrapezohedronSquareTrapezohedronDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
