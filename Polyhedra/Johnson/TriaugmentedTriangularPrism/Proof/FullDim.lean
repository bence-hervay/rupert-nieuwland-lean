import Polyhedra.Johnson.TriaugmentedTriangularPrism.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `johnson/triaugmented-triangular-prism` is full-dimensional

The points of `Johnson.TriaugmentedTriangularPrism.polyhedron` times `24` as exact values in `ZTheta root`,
exported by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`,
checked by the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`),
and scaled back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Johnson.TriaugmentedTriangularPrism.polyhedron`.
-/

namespace Nieuwland.Polyhedra.JohnsonTriaugmentedTriangularPrismDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Johnson.TriaugmentedTriangularPrism.theta

/-- The root `θ`, with `α = 4 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[1/256, 0, -5/8, 0, 1], 1/2, 5/4,
    4, [1, 0, -10, 0, 1],
    16, 49, 52, 80, 13,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    42184508369003825710979679789341897364723323276565745504700775617143357248772964562131158532911408069129156673407486987038182155610617360776398918959100501,
    42184508369003825710979679789341897364723323276565745504700775617143357248772964562131158532911408069129156673407486987038182155610617360776398918959100502,
    by decide +kernel⟩

theorem root_α : root.α = (4 : ℕ) * θ := rfl

theorem root_n : root.n = 4 := rfl

/-- The points of `Johnson.TriaugmentedTriangularPrism.polyhedron` times `24`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[12]⟩, ⟨[0, -22, 0, 2]⟩, ⟨[12]⟩⟩,
    ⟨⟨[12]⟩, ⟨[0, -22, 0, 2]⟩, ⟨[-12]⟩⟩,
    ⟨⟨[-12]⟩, ⟨[0, -22, 0, 2]⟩, ⟨[12]⟩⟩,
    ⟨⟨[-12]⟩, ⟨[0, -22, 0, 2]⟩, ⟨[-12]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0, 44, 0, -4]⟩, ⟨[12]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0, 44, 0, -4]⟩, ⟨[-12]⟩⟩,
    ⟨⟨[-9, 0, 3]⟩, ⟨[0, -16, 0, 2]⟩, ⟨[0]⟩⟩,
    ⟨⟨[9, 0, -3]⟩, ⟨[0, -16, 0, 2]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0, 32, 0, -4]⟩, ⟨[0]⟩⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 24 : ℝ) • Exact.reV (⟨⟨[12]⟩, ⟨[0, -22, 0, 2]⟩, ⟨[12]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [1/2] θ, polyEval [0, -11/3, 0, 16/3] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 24) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 24 : ℝ) • Exact.reV (⟨⟨[12]⟩, ⟨[0, -22, 0, 2]⟩, ⟨[-12]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [1/2] θ, polyEval [0, -11/3, 0, 16/3] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 24) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 24 : ℝ) • Exact.reV (⟨⟨[-12]⟩, ⟨[0, -22, 0, 2]⟩, ⟨[12]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [-1/2] θ, polyEval [0, -11/3, 0, 16/3] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 24) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 24 : ℝ) • Exact.reV (⟨⟨[-12]⟩, ⟨[0, -22, 0, 2]⟩, ⟨[-12]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [-1/2] θ, polyEval [0, -11/3, 0, 16/3] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 24) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 24 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0, 44, 0, -4]⟩, ⟨[12]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0] θ, polyEval [0, 22/3, 0, -32/3] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 24) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 24 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0, 44, 0, -4]⟩, ⟨[-12]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0] θ, polyEval [0, 22/3, 0, -32/3] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 24) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 24 : ℝ) • Exact.reV (⟨⟨[-9, 0, 3]⟩, ⟨[0, -16, 0, 2]⟩, ⟨[0]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [-3/8, 0, 2] θ, polyEval [0, -8/3, 0, 16/3] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 24) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 24 : ℝ) • Exact.reV (⟨⟨[9, 0, -3]⟩, ⟨[0, -16, 0, 2]⟩, ⟨[0]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [3/8, 0, -2] θ, polyEval [0, -8/3, 0, 16/3] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 24) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 24 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0, 32, 0, -4]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0] θ, polyEval [0, 16/3, 0, -32/3] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 24) (by norm_num) (by decide +kernel)

theorem eq_smul : Johnson.TriaugmentedTriangularPrism.polyhedron = (Polyhedron.ofPoints points).smul (1 / 24) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8]

end Nieuwland.Polyhedra.JohnsonTriaugmentedTriangularPrismDim

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/triaugmented-triangular-prism` is full-dimensional.** -/
theorem johnsonTriaugmentedTriangularPrism_fullDim : Johnson.TriaugmentedTriangularPrism.polyhedron.FullDim := by
  rw [JohnsonTriaugmentedTriangularPrismDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk JohnsonTriaugmentedTriangularPrismDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
