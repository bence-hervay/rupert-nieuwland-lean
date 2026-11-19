import Polyhedra.Antiprism.SquareAntiprism.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `prism/square-antiprism` is full-dimensional

The points of `Antiprism.SquareAntiprism.polyhedron` times `132` as exact values in `ZTheta root`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Antiprism.SquareAntiprism.polyhedron`.
-/

namespace Nieuwland.Polyhedra.PrismSquareAntiprismDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Antiprism.SquareAntiprism.theta

/-- The root `θ`, with `α = 4 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[7/32, -1/2, -1, 0, 1], 1/2, 2,
    4, [56, -32, -16, 0, 1],
    16, 71, 74, 128, 16,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    60472162881834820744961470011660967428794900054880596396550685124914568471646671677719362357171870011239839692121001405314769292552736054334956589339681874,
    60472162881834820744961470011660967428794900054880596396550685124914568471646671677719362357171870011239839692121001405314769292552736054334956589339681875,
    by decide +kernel⟩

theorem root_α : root.α = (4 : ℕ) * θ := rfl

theorem root_n : root.n = 4 := rfl

/-- The points of `Antiprism.SquareAntiprism.polyhedron` times `132`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[40, 48, 1, -2]⟩, ⟨[0]⟩, ⟨[40, 15, 1, -2]⟩⟩,
    ⟨⟨[0]⟩, ⟨[40, 48, 1, -2]⟩, ⟨[40, 15, 1, -2]⟩⟩,
    ⟨⟨[-40, -48, -1, 2]⟩, ⟨[0]⟩, ⟨[40, 15, 1, -2]⟩⟩,
    ⟨⟨[0]⟩, ⟨[-40, -48, -1, 2]⟩, ⟨[40, 15, 1, -2]⟩⟩,
    ⟨⟨[66]⟩, ⟨[66]⟩, ⟨[-40, -15, -1, 2]⟩⟩,
    ⟨⟨[-66]⟩, ⟨[66]⟩, ⟨[-40, -15, -1, 2]⟩⟩,
    ⟨⟨[-66]⟩, ⟨[-66]⟩, ⟨[-40, -15, -1, 2]⟩⟩,
    ⟨⟨[66]⟩, ⟨[-66]⟩, ⟨[-40, -15, -1, 2]⟩⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 132 : ℝ) • Exact.reV (⟨⟨[40, 48, 1, -2]⟩, ⟨[0]⟩, ⟨[40, 15, 1, -2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [10/33, 16/11, 4/33, -32/33] θ, polyEval [0] θ, polyEval [10/33,
    5/11, 4/33, -32/33] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 132) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 132 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[40, 48, 1, -2]⟩, ⟨[40, 15, 1, -2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0] θ, polyEval [10/33, 16/11, 4/33, -32/33] θ, polyEval [10/33,
    5/11, 4/33, -32/33] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 132) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 132 : ℝ) • Exact.reV (⟨⟨[-40, -48, -1, 2]⟩, ⟨[0]⟩, ⟨[40, 15, 1, -2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [-10/33, -16/11, -4/33, 32/33] θ, polyEval [0] θ, polyEval [10/33,
    5/11, 4/33, -32/33] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 132) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 132 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[-40, -48, -1, 2]⟩, ⟨[40, 15, 1, -2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0] θ, polyEval [-10/33, -16/11, -4/33, 32/33] θ, polyEval [10/33,
    5/11, 4/33, -32/33] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 132) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 132 : ℝ) • Exact.reV (⟨⟨[66]⟩, ⟨[66]⟩, ⟨[-40, -15, -1, 2]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [1/2] θ, polyEval [1/2] θ, polyEval [-10/33, -5/11, -4/33, 32/33] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 132) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 132 : ℝ) • Exact.reV (⟨⟨[-66]⟩, ⟨[66]⟩, ⟨[-40, -15, -1, 2]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [-1/2] θ, polyEval [1/2] θ, polyEval [-10/33, -5/11, -4/33, 32/33] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 132) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 132 : ℝ) • Exact.reV (⟨⟨[-66]⟩, ⟨[-66]⟩, ⟨[-40, -15, -1, 2]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [-1/2] θ, polyEval [-1/2] θ, polyEval [-10/33, -5/11, -4/33, 32/33] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 132) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 132 : ℝ) • Exact.reV (⟨⟨[66]⟩, ⟨[-66]⟩, ⟨[-40, -15, -1, 2]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [1/2] θ, polyEval [-1/2] θ, polyEval [-10/33, -5/11, -4/33, 32/33] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 132) (by norm_num) (by decide +kernel)

theorem eq_smul : Antiprism.SquareAntiprism.polyhedron = (Polyhedron.ofPoints points).smul (1 / 132) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7]

end Nieuwland.Polyhedra.PrismSquareAntiprismDim

namespace Nieuwland.Polyhedra

/-- **The fixture `prism/square-antiprism` is full-dimensional.** -/
theorem prismSquareAntiprism_fullDim : Antiprism.SquareAntiprism.polyhedron.FullDim := by
  rw [PrismSquareAntiprismDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk PrismSquareAntiprismDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
