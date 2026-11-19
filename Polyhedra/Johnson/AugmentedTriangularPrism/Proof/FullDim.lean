import Polyhedra.Johnson.AugmentedTriangularPrism.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `johnson/augmented-triangular-prism` is full-dimensional

The points of `Johnson.AugmentedTriangularPrism.polyhedron` times `144` as exact values in `ZTheta root`,
exported by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`,
checked by the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`),
and scaled back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Johnson.AugmentedTriangularPrism.polyhedron`.
-/

namespace Nieuwland.Polyhedra.JohnsonAugmentedTriangularPrismDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Johnson.AugmentedTriangularPrism.theta

/-- The root `θ`, with `α = 6 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[1/36, 0, -5/3, 0, 1], 1/2, 2,
    6, [36, 0, -60, 0, 1],
    16, 122, 125, 192, 16,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    103330520554226004875624412489988113249615730041194150736986437904388019104502210773853228522637657604272179528043333539324500945697717342853671989399270268,
    103330520554226004875624412489988113249615730041194150736986437904388019104502210773853228522637657604272179528043333539324500945697717342853671989399270269,
    by decide +kernel⟩

theorem root_α : root.α = (6 : ℕ) * θ := rfl

theorem root_n : root.n = 4 := rfl

/-- The points of `Johnson.AugmentedTriangularPrism.polyhedron` times `144`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[72]⟩, ⟨[72]⟩, ⟨[0, -54, 0, 1]⟩⟩,
    ⟨⟨[72]⟩, ⟨[-72]⟩, ⟨[0, -54, 0, 1]⟩⟩,
    ⟨⟨[-72]⟩, ⟨[72]⟩, ⟨[0, -54, 0, 1]⟩⟩,
    ⟨⟨[-72]⟩, ⟨[-72]⟩, ⟨[0, -54, 0, 1]⟩⟩,
    ⟨⟨[0]⟩, ⟨[72]⟩, ⟨[0, 108, 0, -2]⟩⟩,
    ⟨⟨[0]⟩, ⟨[-72]⟩, ⟨[0, 108, 0, -2]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0]⟩, ⟨[0, 78, 0, -1]⟩⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 144 : ℝ) • Exact.reV (⟨⟨[72]⟩, ⟨[72]⟩, ⟨[0, -54, 0, 1]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [1/2] θ, polyEval [1/2] θ, polyEval [0, -9/4, 0, 3/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 144) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 144 : ℝ) • Exact.reV (⟨⟨[72]⟩, ⟨[-72]⟩, ⟨[0, -54, 0, 1]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [1/2] θ, polyEval [-1/2] θ, polyEval [0, -9/4, 0, 3/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 144) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 144 : ℝ) • Exact.reV (⟨⟨[-72]⟩, ⟨[72]⟩, ⟨[0, -54, 0, 1]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [-1/2] θ, polyEval [1/2] θ, polyEval [0, -9/4, 0, 3/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 144) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 144 : ℝ) • Exact.reV (⟨⟨[-72]⟩, ⟨[-72]⟩, ⟨[0, -54, 0, 1]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [-1/2] θ, polyEval [-1/2] θ, polyEval [0, -9/4, 0, 3/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 144) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 144 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[72]⟩, ⟨[0, 108, 0, -2]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [0] θ, polyEval [1/2] θ, polyEval [0, 9/2, 0, -3] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 144) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 144 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[-72]⟩, ⟨[0, 108, 0, -2]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [0] θ, polyEval [-1/2] θ, polyEval [0, 9/2, 0, -3] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 144) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 144 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0]⟩, ⟨[0, 78, 0, -1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0] θ, polyEval [0] θ, polyEval [0, 13/4, 0, -3/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 144) (by norm_num) (by decide +kernel)

theorem eq_smul : Johnson.AugmentedTriangularPrism.polyhedron = (Polyhedron.ofPoints points).smul (1 / 144) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6]

end Nieuwland.Polyhedra.JohnsonAugmentedTriangularPrismDim

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/augmented-triangular-prism` is full-dimensional.** -/
theorem johnsonAugmentedTriangularPrism_fullDim : Johnson.AugmentedTriangularPrism.polyhedron.FullDim := by
  rw [JohnsonAugmentedTriangularPrismDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk JohnsonAugmentedTriangularPrismDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
