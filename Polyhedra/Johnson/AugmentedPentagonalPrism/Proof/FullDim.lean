import Polyhedra.Johnson.AugmentedPentagonalPrism.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `johnson/augmented-pentagonal-prism` is full-dimensional

The points of `Johnson.AugmentedPentagonalPrism.polyhedron` times `220` as exact values in `ZTheta root`,
exported by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`,
checked by the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`),
and scaled back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Johnson.AugmentedPentagonalPrism.polyhedron`.
-/

namespace Nieuwland.Polyhedra.JohnsonAugmentedPentagonalPrismDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Johnson.AugmentedPentagonalPrism.theta

/-- The root `θ`, with `α = 2 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[1/256, 0, -11/32, 0, 79/16, 0, -9/2, 0, 1], 3/2, 15/8,
    2, [1, 0, -22, 0, 79, 0, -18, 0, 1],
    512, 1696, 1699, 1920, 20,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    44464670018229835218237566521760280661901176224795643652248102526715303888698412841252987739146066313140031591950628283909661621633516911794936111905176929,
    44464670018229835218237566521760280661901176224795643652248102526715303888698412841252987739146066313140031591950628283909661621633516911794936111905176930,
    by decide +kernel⟩

theorem root_α : root.α = (2 : ℕ) * θ := rfl

theorem root_n : root.n = 8 := rfl

/-- The points of `Johnson.AugmentedPentagonalPrism.polyhedron` times `220`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[-150, 0, 1460, 0, -350, 0, 20]⟩, ⟨[110]⟩, ⟨[0, 562, 0, -3023, 0, 699, 0, -39]⟩⟩,
    ⟨⟨[-150, 0, 1460, 0, -350, 0, 20]⟩, ⟨[-110]⟩, ⟨[0, 562, 0, -3023, 0, 699, 0, -39]⟩⟩,
    ⟨⟨[150, 0, -1460, 0, 350, 0, -20]⟩, ⟨[110]⟩, ⟨[0, 562, 0, -3023, 0, 699, 0, -39]⟩⟩,
    ⟨⟨[150, 0, -1460, 0, 350, 0, -20]⟩, ⟨[-110]⟩, ⟨[0, 562, 0, -3023, 0, 699, 0, -39]⟩⟩,
    ⟨⟨[110]⟩, ⟨[110]⟩, ⟨[0, -303, 0, 2727, 0, -641, 0, 36]⟩⟩,
    ⟨⟨[110]⟩, ⟨[-110]⟩, ⟨[0, -303, 0, 2727, 0, -641, 0, 36]⟩⟩,
    ⟨⟨[-110]⟩, ⟨[110]⟩, ⟨[0, -303, 0, 2727, 0, -641, 0, 36]⟩⟩,
    ⟨⟨[-110]⟩, ⟨[-110]⟩, ⟨[0, -303, 0, 2727, 0, -641, 0, 36]⟩⟩,
    ⟨⟨[0]⟩, ⟨[110]⟩, ⟨[0, -518, 0, 592, 0, -116, 0, 6]⟩⟩,
    ⟨⟨[0]⟩, ⟨[-110]⟩, ⟨[0, -518, 0, 592, 0, -116, 0, 6]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0]⟩, ⟨[0, 672, 0, -3023, 0, 699, 0, -39]⟩⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 220 : ℝ) • Exact.reV (⟨⟨[-150, 0, 1460, 0, -350, 0, 20]⟩, ⟨[110]⟩, ⟨[0, 562,
    0, -3023, 0, 699, 0, -39]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-15/22, 0, 292/11, 0, -280/11, 0,
    64/11] θ, polyEval [1/2] θ, polyEval [0, 281/55, 0, -6046/55, 0, 5592/55, 0, -1248/55] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 220) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 220 : ℝ) • Exact.reV (⟨⟨[-150, 0, 1460, 0, -350, 0, 20]⟩, ⟨[-110]⟩, ⟨[0, 562,
    0, -3023, 0, 699, 0, -39]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-15/22, 0, 292/11, 0, -280/11, 0,
    64/11] θ, polyEval [-1/2] θ, polyEval [0, 281/55, 0, -6046/55, 0, 5592/55, 0, -1248/55] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 220) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 220 : ℝ) • Exact.reV (⟨⟨[150, 0, -1460, 0, 350, 0, -20]⟩, ⟨[110]⟩, ⟨[0, 562,
    0, -3023, 0, 699, 0, -39]⟩⟩ : V3 (ZTheta root)) = ![polyEval [15/22, 0, -292/11, 0, 280/11, 0,
    -64/11] θ, polyEval [1/2] θ, polyEval [0, 281/55, 0, -6046/55, 0, 5592/55, 0, -1248/55] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 220) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 220 : ℝ) • Exact.reV (⟨⟨[150, 0, -1460, 0, 350, 0, -20]⟩, ⟨[-110]⟩, ⟨[0, 562,
    0, -3023, 0, 699, 0, -39]⟩⟩ : V3 (ZTheta root)) = ![polyEval [15/22, 0, -292/11, 0, 280/11, 0,
    -64/11] θ, polyEval [-1/2] θ, polyEval [0, 281/55, 0, -6046/55, 0, 5592/55, 0, -1248/55] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 220) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 220 : ℝ) • Exact.reV (⟨⟨[110]⟩, ⟨[110]⟩, ⟨[0, -303, 0, 2727, 0, -641, 0,
    36]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1/2] θ, polyEval [1/2] θ, polyEval [0, -303/110, 0,
    5454/55, 0, -5128/55, 0, 1152/55] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 220) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 220 : ℝ) • Exact.reV (⟨⟨[110]⟩, ⟨[-110]⟩, ⟨[0, -303, 0, 2727, 0, -641, 0,
    36]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1/2] θ, polyEval [-1/2] θ, polyEval [0, -303/110, 0,
    5454/55, 0, -5128/55, 0, 1152/55] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 220) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 220 : ℝ) • Exact.reV (⟨⟨[-110]⟩, ⟨[110]⟩, ⟨[0, -303, 0, 2727, 0, -641, 0,
    36]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1/2] θ, polyEval [1/2] θ, polyEval [0, -303/110, 0,
    5454/55, 0, -5128/55, 0, 1152/55] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 220) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 220 : ℝ) • Exact.reV (⟨⟨[-110]⟩, ⟨[-110]⟩, ⟨[0, -303, 0, 2727, 0, -641, 0,
    36]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1/2] θ, polyEval [-1/2] θ, polyEval [0, -303/110, 0,
    5454/55, 0, -5128/55, 0, 1152/55] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 220) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 220 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[110]⟩, ⟨[0, -518, 0, 592, 0, -116, 0, 6]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [0] θ, polyEval [1/2] θ, polyEval [0, -259/55, 0, 1184/55, 0,
    -928/55, 0, 192/55] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 220) (by norm_num) (by decide +kernel)

theorem pt9 : (1 / 220 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[-110]⟩, ⟨[0, -518, 0, 592, 0, -116, 0, 6]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [0] θ, polyEval [-1/2] θ, polyEval [0, -259/55, 0, 1184/55, 0,
    -928/55, 0, 192/55] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 220) (by norm_num) (by decide +kernel)

theorem pt10 : (1 / 220 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0]⟩, ⟨[0, 672, 0, -3023, 0, 699, 0, -39]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [0] θ, polyEval [0] θ, polyEval [0, 336/55, 0, -6046/55, 0,
    5592/55, 0, -1248/55] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 220) (by norm_num) (by decide +kernel)

theorem eq_smul : Johnson.AugmentedPentagonalPrism.polyhedron = (Polyhedron.ofPoints points).smul (1 / 220) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10]

end Nieuwland.Polyhedra.JohnsonAugmentedPentagonalPrismDim

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/augmented-pentagonal-prism` is full-dimensional.** -/
theorem johnsonAugmentedPentagonalPrism_fullDim : Johnson.AugmentedPentagonalPrism.polyhedron.FullDim := by
  rw [JohnsonAugmentedPentagonalPrismDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk JohnsonAugmentedPentagonalPrismDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
