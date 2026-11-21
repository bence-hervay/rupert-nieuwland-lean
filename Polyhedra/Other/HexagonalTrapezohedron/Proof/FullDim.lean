import Polyhedra.Other.HexagonalTrapezohedron.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `trapezohedron/hexagonal-trapezohedron` is full-dimensional

The points of `Other.HexagonalTrapezohedron.polyhedron` times `99` as exact values in `ZTheta root`,
exported by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`,
checked by the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`),
and scaled back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Other.HexagonalTrapezohedron.polyhedron`.
-/

namespace Nieuwland.Polyhedra.TrapezohedronHexagonalTrapezohedronDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Other.HexagonalTrapezohedron.theta

/-- The root `θ`, with `α = 1 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[-18, 0, 114, 0, 1], 0, 3/4,
    1, [-18, 0, 114, 0, 1],
    16, 5, 8, 12, 5,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    5324041987296148205019474456277044744070695246412214321559435643800395218595837342682464556151418610883301594760160491765772769429134121515497519788683688,
    5324041987296148205019474456277044744070695246412214321559435643800395218595837342682464556151418610883301594760160491765772769429134121515497519788683689,
    by decide +kernel⟩

theorem root_α : root.α = (1 : ℕ) * θ := rfl

theorem root_n : root.n = 4 := rfl

/-- The points of `Other.HexagonalTrapezohedron.polyhedron` times `99`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[0]⟩, ⟨[0]⟩, ⟨[-99]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0]⟩, ⟨[99]⟩⟩,
    ⟨⟨[0, 99]⟩, ⟨[0, 57, 0, 1]⟩, ⟨[-9, 0, 12]⟩⟩,
    ⟨⟨[0, 57, 0, 1]⟩, ⟨[0, 99]⟩, ⟨[9, 0, -12]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0, 114, 0, 2]⟩, ⟨[-9, 0, 12]⟩⟩,
    ⟨⟨[0, -57, 0, -1]⟩, ⟨[0, 99]⟩, ⟨[9, 0, -12]⟩⟩,
    ⟨⟨[0, -99]⟩, ⟨[0, 57, 0, 1]⟩, ⟨[-9, 0, 12]⟩⟩,
    ⟨⟨[0, -114, 0, -2]⟩, ⟨[0]⟩, ⟨[9, 0, -12]⟩⟩,
    ⟨⟨[0, -99]⟩, ⟨[0, -57, 0, -1]⟩, ⟨[-9, 0, 12]⟩⟩,
    ⟨⟨[0, -57, 0, -1]⟩, ⟨[0, -99]⟩, ⟨[9, 0, -12]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0, -114, 0, -2]⟩, ⟨[-9, 0, 12]⟩⟩,
    ⟨⟨[0, 57, 0, 1]⟩, ⟨[0, -99]⟩, ⟨[9, 0, -12]⟩⟩,
    ⟨⟨[0, 99]⟩, ⟨[0, -57, 0, -1]⟩, ⟨[-9, 0, 12]⟩⟩,
    ⟨⟨[0, 114, 0, 2]⟩, ⟨[0]⟩, ⟨[9, 0, -12]⟩⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 99 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0]⟩, ⟨[-99]⟩⟩ : V3 (ZTheta root)) = ![polyEval
    [0] θ, polyEval [0] θ, polyEval [-1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 99) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 99 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0]⟩, ⟨[99]⟩⟩ : V3 (ZTheta root)) = ![polyEval
    [0] θ, polyEval [0] θ, polyEval [1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 99) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 99 : ℝ) • Exact.reV (⟨⟨[0, 99]⟩, ⟨[0, 57, 0, 1]⟩, ⟨[-9, 0, 12]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [0, 1] θ, polyEval [0, 19/33, 0, 1/99] θ, polyEval [-1/11, 0, 4/33] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 99) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 99 : ℝ) • Exact.reV (⟨⟨[0, 57, 0, 1]⟩, ⟨[0, 99]⟩, ⟨[9, 0, -12]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [0, 19/33, 0, 1/99] θ, polyEval [0, 1] θ, polyEval [1/11, 0, -4/33] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 99) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 99 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0, 114, 0, 2]⟩, ⟨[-9, 0, 12]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [0] θ, polyEval [0, 38/33, 0, 2/99] θ, polyEval [-1/11, 0, 4/33] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 99) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 99 : ℝ) • Exact.reV (⟨⟨[0, -57, 0, -1]⟩, ⟨[0, 99]⟩, ⟨[9, 0, -12]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0, -19/33, 0, -1/99] θ, polyEval [0, 1] θ, polyEval [1/11, 0,
    -4/33] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 99) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 99 : ℝ) • Exact.reV (⟨⟨[0, -99]⟩, ⟨[0, 57, 0, 1]⟩, ⟨[-9, 0, 12]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0, -1] θ, polyEval [0, 19/33, 0, 1/99] θ, polyEval [-1/11, 0, 4/33]
    θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 99) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 99 : ℝ) • Exact.reV (⟨⟨[0, -114, 0, -2]⟩, ⟨[0]⟩, ⟨[9, 0, -12]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [0, -38/33, 0, -2/99] θ, polyEval [0] θ, polyEval [1/11, 0, -4/33] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 99) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 99 : ℝ) • Exact.reV (⟨⟨[0, -99]⟩, ⟨[0, -57, 0, -1]⟩, ⟨[-9, 0, 12]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0, -1] θ, polyEval [0, -19/33, 0, -1/99] θ, polyEval [-1/11, 0,
    4/33] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 99) (by norm_num) (by decide +kernel)

theorem pt9 : (1 / 99 : ℝ) • Exact.reV (⟨⟨[0, -57, 0, -1]⟩, ⟨[0, -99]⟩, ⟨[9, 0, -12]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0, -19/33, 0, -1/99] θ, polyEval [0, -1] θ, polyEval [1/11, 0,
    -4/33] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 99) (by norm_num) (by decide +kernel)

theorem pt10 : (1 / 99 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0, -114, 0, -2]⟩, ⟨[-9, 0, 12]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [0] θ, polyEval [0, -38/33, 0, -2/99] θ, polyEval [-1/11, 0, 4/33] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 99) (by norm_num) (by decide +kernel)

theorem pt11 : (1 / 99 : ℝ) • Exact.reV (⟨⟨[0, 57, 0, 1]⟩, ⟨[0, -99]⟩, ⟨[9, 0, -12]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0, 19/33, 0, 1/99] θ, polyEval [0, -1] θ, polyEval [1/11, 0, -4/33]
    θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 99) (by norm_num) (by decide +kernel)

theorem pt12 : (1 / 99 : ℝ) • Exact.reV (⟨⟨[0, 99]⟩, ⟨[0, -57, 0, -1]⟩, ⟨[-9, 0, 12]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0, 1] θ, polyEval [0, -19/33, 0, -1/99] θ, polyEval [-1/11, 0,
    4/33] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 99) (by norm_num) (by decide +kernel)

theorem pt13 : (1 / 99 : ℝ) • Exact.reV (⟨⟨[0, 114, 0, 2]⟩, ⟨[0]⟩, ⟨[9, 0, -12]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [0, 38/33, 0, 2/99] θ, polyEval [0] θ, polyEval [1/11, 0, -4/33] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 99) (by norm_num) (by decide +kernel)

theorem eq_smul : Other.HexagonalTrapezohedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 99) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13]

end Nieuwland.Polyhedra.TrapezohedronHexagonalTrapezohedronDim

namespace Nieuwland.Polyhedra

/-- **The fixture `trapezohedron/hexagonal-trapezohedron` is full-dimensional.** -/
theorem trapezohedronHexagonalTrapezohedron_fullDim : Other.HexagonalTrapezohedron.polyhedron.FullDim := by
  rw [TrapezohedronHexagonalTrapezohedronDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk TrapezohedronHexagonalTrapezohedronDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
