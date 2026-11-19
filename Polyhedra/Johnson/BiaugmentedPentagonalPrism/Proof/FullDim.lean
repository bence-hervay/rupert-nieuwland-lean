import Polyhedra.Johnson.BiaugmentedPentagonalPrism.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `johnson/biaugmented-pentagonal-prism` is full-dimensional

The points of `Johnson.BiaugmentedPentagonalPrism.polyhedron` times `440` as exact values in `ZTheta root`,
exported by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`,
checked by the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`),
and scaled back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Johnson.BiaugmentedPentagonalPrism.polyhedron`.
-/

namespace Nieuwland.Polyhedra.JohnsonBiaugmentedPentagonalPrismDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Johnson.BiaugmentedPentagonalPrism.theta

/-- The root `θ`, with `α = 4 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[121/65536, 0, -119/2048, 0, 139/256, 0, -11/8, 0, 1], 5/8, 13/16,
    4, [121, 0, -238, 0, 139, 0, -22, 0, 1],
    256, 709, 712, 832, 13,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    37222020038245263854328455615978889644495796208539934384622812853558232583219756308413898520254025565454416971468366833537831077080038712670912544873191701,
    37222020038245263854328455615978889644495796208539934384622812853558232583219756308413898520254025565454416971468366833537831077080038712670912544873191702,
    by decide +kernel⟩

theorem root_α : root.α = (4 : ℕ) * θ := rfl

theorem root_n : root.n = 8 := rfl

/-- The points of `Johnson.BiaugmentedPentagonalPrism.polyhedron` times `440`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[4180, 0, -4440, 0, 820, 0, -40]⟩, ⟨[220]⟩, ⟨[0, 2284, 0, -2514, 0, 458, 0, -22]⟩⟩,
    ⟨⟨[4180, 0, -4440, 0, 820, 0, -40]⟩, ⟨[-220]⟩, ⟨[0, 2284, 0, -2514, 0, 458, 0, -22]⟩⟩,
    ⟨⟨[-4180, 0, 4440, 0, -820, 0, 40]⟩, ⟨[220]⟩, ⟨[0, 2284, 0, -2514, 0, 458, 0, -22]⟩⟩,
    ⟨⟨[-4180, 0, 4440, 0, -820, 0, 40]⟩, ⟨[-220]⟩, ⟨[0, 2284, 0, -2514, 0, 458, 0, -22]⟩⟩,
    ⟨⟨[220]⟩, ⟨[220]⟩, ⟨[0, -3066, 0, 3206, 0, -582, 0, 28]⟩⟩,
    ⟨⟨[220]⟩, ⟨[-220]⟩, ⟨[0, -3066, 0, 3206, 0, -582, 0, 28]⟩⟩,
    ⟨⟨[-220]⟩, ⟨[220]⟩, ⟨[0, -3066, 0, 3206, 0, -582, 0, 28]⟩⟩,
    ⟨⟨[-220]⟩, ⟨[-220]⟩, ⟨[0, -3066, 0, 3206, 0, -582, 0, 28]⟩⟩,
    ⟨⟨[0]⟩, ⟨[220]⟩, ⟨[0, 1564, 0, -1384, 0, 248, 0, -12]⟩⟩,
    ⟨⟨[0]⟩, ⟨[-220]⟩, ⟨[0, 1564, 0, -1384, 0, 248, 0, -12]⟩⟩,
    ⟨⟨[-1760, 0, 1995, 0, -335, 0, 15]⟩, ⟨[0]⟩, ⟨[0, 2174, 0, -2514, 0, 458, 0, -22]⟩⟩,
    ⟨⟨[1760, 0, -1995, 0, 335, 0, -15]⟩, ⟨[0]⟩, ⟨[0, 2174, 0, -2514, 0, 458, 0, -22]⟩⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 440 : ℝ) • Exact.reV (⟨⟨[4180, 0, -4440, 0, 820, 0, -40]⟩, ⟨[220]⟩, ⟨[0,
    2284, 0, -2514, 0, 458, 0, -22]⟩⟩ : V3 (ZTheta root)) = ![polyEval [19/2, 0, -1776/11, 0,
    5248/11, 0, -4096/11] θ, polyEval [1/2] θ, polyEval [0, 1142/55, 0, -20112/55, 0, 58624/55, 0,
    -4096/5] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 440) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 440 : ℝ) • Exact.reV (⟨⟨[4180, 0, -4440, 0, 820, 0, -40]⟩, ⟨[-220]⟩, ⟨[0,
    2284, 0, -2514, 0, 458, 0, -22]⟩⟩ : V3 (ZTheta root)) = ![polyEval [19/2, 0, -1776/11, 0,
    5248/11, 0, -4096/11] θ, polyEval [-1/2] θ, polyEval [0, 1142/55, 0, -20112/55, 0, 58624/55, 0,
    -4096/5] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 440) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 440 : ℝ) • Exact.reV (⟨⟨[-4180, 0, 4440, 0, -820, 0, 40]⟩, ⟨[220]⟩, ⟨[0,
    2284, 0, -2514, 0, 458, 0, -22]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-19/2, 0, 1776/11, 0,
    -5248/11, 0, 4096/11] θ, polyEval [1/2] θ, polyEval [0, 1142/55, 0, -20112/55, 0, 58624/55, 0,
    -4096/5] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 440) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 440 : ℝ) • Exact.reV (⟨⟨[-4180, 0, 4440, 0, -820, 0, 40]⟩, ⟨[-220]⟩, ⟨[0,
    2284, 0, -2514, 0, 458, 0, -22]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-19/2, 0, 1776/11, 0,
    -5248/11, 0, 4096/11] θ, polyEval [-1/2] θ, polyEval [0, 1142/55, 0, -20112/55, 0, 58624/55, 0,
    -4096/5] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 440) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 440 : ℝ) • Exact.reV (⟨⟨[220]⟩, ⟨[220]⟩, ⟨[0, -3066, 0, 3206, 0, -582, 0,
    28]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1/2] θ, polyEval [1/2] θ, polyEval [0, -1533/55, 0,
    25648/55, 0, -74496/55, 0, 57344/55] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 440) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 440 : ℝ) • Exact.reV (⟨⟨[220]⟩, ⟨[-220]⟩, ⟨[0, -3066, 0, 3206, 0, -582, 0,
    28]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1/2] θ, polyEval [-1/2] θ, polyEval [0, -1533/55, 0,
    25648/55, 0, -74496/55, 0, 57344/55] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 440) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 440 : ℝ) • Exact.reV (⟨⟨[-220]⟩, ⟨[220]⟩, ⟨[0, -3066, 0, 3206, 0, -582, 0,
    28]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1/2] θ, polyEval [1/2] θ, polyEval [0, -1533/55, 0,
    25648/55, 0, -74496/55, 0, 57344/55] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 440) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 440 : ℝ) • Exact.reV (⟨⟨[-220]⟩, ⟨[-220]⟩, ⟨[0, -3066, 0, 3206, 0, -582, 0,
    28]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1/2] θ, polyEval [-1/2] θ, polyEval [0, -1533/55, 0,
    25648/55, 0, -74496/55, 0, 57344/55] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 440) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 440 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[220]⟩, ⟨[0, 1564, 0, -1384, 0, 248, 0, -12]⟩⟩
    : V3 (ZTheta root)) = ![polyEval [0] θ, polyEval [1/2] θ, polyEval [0, 782/55, 0, -11072/55, 0,
    31744/55, 0, -24576/55] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 440) (by norm_num) (by decide +kernel)

theorem pt9 : (1 / 440 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[-220]⟩, ⟨[0, 1564, 0, -1384, 0, 248, 0,
    -12]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0] θ, polyEval [-1/2] θ, polyEval [0, 782/55, 0,
    -11072/55, 0, 31744/55, 0, -24576/55] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 440) (by norm_num) (by decide +kernel)

theorem pt10 : (1 / 440 : ℝ) • Exact.reV (⟨⟨[-1760, 0, 1995, 0, -335, 0, 15]⟩, ⟨[0]⟩, ⟨[0, 2174,
    0, -2514, 0, 458, 0, -22]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-4, 0, 798/11, 0, -2144/11, 0,
    1536/11] θ, polyEval [0] θ, polyEval [0, 1087/55, 0, -20112/55, 0, 58624/55, 0, -4096/5] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 440) (by norm_num) (by decide +kernel)

theorem pt11 : (1 / 440 : ℝ) • Exact.reV (⟨⟨[1760, 0, -1995, 0, 335, 0, -15]⟩, ⟨[0]⟩, ⟨[0, 2174,
    0, -2514, 0, 458, 0, -22]⟩⟩ : V3 (ZTheta root)) = ![polyEval [4, 0, -798/11, 0, 2144/11, 0,
    -1536/11] θ, polyEval [0] θ, polyEval [0, 1087/55, 0, -20112/55, 0, 58624/55, 0, -4096/5] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 440) (by norm_num) (by decide +kernel)

theorem eq_smul : Johnson.BiaugmentedPentagonalPrism.polyhedron = (Polyhedron.ofPoints points).smul (1 / 440) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11]

end Nieuwland.Polyhedra.JohnsonBiaugmentedPentagonalPrismDim

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/biaugmented-pentagonal-prism` is full-dimensional.** -/
theorem johnsonBiaugmentedPentagonalPrism_fullDim : Johnson.BiaugmentedPentagonalPrism.polyhedron.FullDim := by
  rw [JohnsonBiaugmentedPentagonalPrismDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk JohnsonBiaugmentedPentagonalPrismDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
