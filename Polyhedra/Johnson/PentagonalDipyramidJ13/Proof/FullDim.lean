import Polyhedra.Johnson.PentagonalDipyramidJ13.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `johnson/pentagonal-dipyramid-j13` is full-dimensional

The points of `Johnson.PentagonalDipyramidJ13.polyhedron` times `50` as exact values in `ZTheta root`, exported
by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Johnson.PentagonalDipyramidJ13.polyhedron`.
-/

namespace Nieuwland.Polyhedra.JohnsonPentagonalDipyramidJ13Dim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Johnson.PentagonalDipyramidJ13.theta

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

/-- The points of `Johnson.PentagonalDipyramidJ13.polyhedron` times `50`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[0]⟩, ⟨[0]⟩, ⟨[0, -10]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0]⟩, ⟨[0, 10]⟩⟩,
    ⟨⟨[75, 0, -5]⟩, ⟨[0, 5]⟩, ⟨[0]⟩⟩,
    ⟨⟨[-75, 0, 5]⟩, ⟨[0, 5]⟩, ⟨[0]⟩⟩,
    ⟨⟨[25]⟩, ⟨[0, -20, 0, 1]⟩, ⟨[0]⟩⟩,
    ⟨⟨[-25]⟩, ⟨[0, -20, 0, 1]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0, 30, 0, -2]⟩, ⟨[0]⟩⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0]⟩, ⟨[0, -10]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0] θ, polyEval [0] θ, polyEval [0, -2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0]⟩, ⟨[0, 10]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0] θ, polyEval [0] θ, polyEval [0, 2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[75, 0, -5]⟩, ⟨[0, 5]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [3/2, 0, -10] θ, polyEval [0, 1] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[-75, 0, 5]⟩, ⟨[0, 5]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [-3/2, 0, 10] θ, polyEval [0, 1] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[25]⟩, ⟨[0, -20, 0, 1]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [1/2] θ, polyEval [0, -4, 0, 20] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[-25]⟩, ⟨[0, -20, 0, 1]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [-1/2] θ, polyEval [0, -4, 0, 20] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 50 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0, 30, 0, -2]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0] θ, polyEval [0, 6, 0, -40] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 50) (by norm_num) (by decide +kernel)

theorem eq_smul : Johnson.PentagonalDipyramidJ13.polyhedron = (Polyhedron.ofPoints points).smul (1 / 50) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6]

end Nieuwland.Polyhedra.JohnsonPentagonalDipyramidJ13Dim

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/pentagonal-dipyramid-j13` is full-dimensional.** -/
theorem johnsonPentagonalDipyramidJ13_fullDim : Johnson.PentagonalDipyramidJ13.polyhedron.FullDim := by
  rw [JohnsonPentagonalDipyramidJ13Dim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk JohnsonPentagonalDipyramidJ13Dim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
