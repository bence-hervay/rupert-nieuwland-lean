import Polyhedra.Antiprism.HeptagonalAntiprism.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `prism/heptagonal-antiprism` is full-dimensional

The points of `Antiprism.HeptagonalAntiprism.polyhedron` times `8` as exact values in `ZTheta root`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Antiprism.HeptagonalAntiprism.polyhedron`.
-/

namespace Nieuwland.Polyhedra.PrismHeptagonalAntiprismDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Antiprism.HeptagonalAntiprism.theta

/-- The root `θ`, with `α = 2 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[-1/8, -1/2, 1/4, 3/2, -1, -1, 1], 0, 3/2,
    2, [-8, -16, 4, 12, -4, -2, 1],
    128, 227, 230, 384, 21,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    23965177726250232053672266026110550147011397636013844677462859994963936873758321823497835570737010418402327096567140919655572493596445954857662106494267896,
    23965177726250232053672266026110550147011397636013844677462859994963936873758321823497835570737010418402327096567140919655572493596445954857662106494267897,
    by decide +kernel⟩

theorem root_α : root.α = (2 : ℕ) * θ := rfl

theorem root_n : root.n = 6 := rfl

/-- The points of `Antiprism.HeptagonalAntiprism.polyhedron` times `8`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[4]⟩, ⟨[0]⟩, ⟨[-16, -8, 24, -4, -5, 2]⟩⟩,
    ⟨⟨[4]⟩, ⟨[0]⟩, ⟨[16, 8, -24, 4, 5, -2]⟩⟩,
    ⟨⟨[-4]⟩, ⟨[0]⟩, ⟨[-16, -8, 24, -4, -5, 2]⟩⟩,
    ⟨⟨[-4]⟩, ⟨[0]⟩, ⟨[16, 8, -24, 4, 5, -2]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0, 8, -2, -2, 1]⟩, ⟨[-4, -4, 10, -2, -2, 1]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0, 8, -2, -2, 1]⟩, ⟨[4, 4, -10, 2, 2, -1]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0, -8, 2, 2, -1]⟩, ⟨[-4, -4, 10, -2, -2, 1]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0, -8, 2, 2, -1]⟩, ⟨[4, 4, -10, 2, 2, -1]⟩⟩,
    ⟨⟨[-4, -4, 10, -2, -2, 1]⟩, ⟨[12, 8, -14, 2, 3, -1]⟩, ⟨[4]⟩⟩,
    ⟨⟨[-4, -4, 10, -2, -2, 1]⟩, ⟨[12, 8, -14, 2, 3, -1]⟩, ⟨[-4]⟩⟩,
    ⟨⟨[4, 4, -10, 2, 2, -1]⟩, ⟨[-12, -8, 14, -2, -3, 1]⟩, ⟨[4]⟩⟩,
    ⟨⟨[4, 4, -10, 2, 2, -1]⟩, ⟨[-12, -8, 14, -2, -3, 1]⟩, ⟨[-4]⟩⟩,
    ⟨⟨[-12, -4, 14, -2, -3, 1]⟩, ⟨[16, 16, -18, 0, 4, -1]⟩, ⟨[0]⟩⟩,
    ⟨⟨[12, 4, -14, 2, 3, -1]⟩, ⟨[-16, -16, 18, 0, -4, 1]⟩, ⟨[0]⟩⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 8 : ℝ) • Exact.reV (⟨⟨[4]⟩, ⟨[0]⟩, ⟨[-16, -8, 24, -4, -5, 2]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [1/2] θ, polyEval [0] θ, polyEval [-2, -2, 12, -4, -10, 8] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 8) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 8 : ℝ) • Exact.reV (⟨⟨[4]⟩, ⟨[0]⟩, ⟨[16, 8, -24, 4, 5, -2]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [1/2] θ, polyEval [0] θ, polyEval [2, 2, -12, 4, 10, -8] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 8) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 8 : ℝ) • Exact.reV (⟨⟨[-4]⟩, ⟨[0]⟩, ⟨[-16, -8, 24, -4, -5, 2]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [-1/2] θ, polyEval [0] θ, polyEval [-2, -2, 12, -4, -10, 8] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 8) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 8 : ℝ) • Exact.reV (⟨⟨[-4]⟩, ⟨[0]⟩, ⟨[16, 8, -24, 4, 5, -2]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [-1/2] θ, polyEval [0] θ, polyEval [2, 2, -12, 4, 10, -8] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 8) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 8 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0, 8, -2, -2, 1]⟩, ⟨[-4, -4, 10, -2, -2, 1]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [0] θ, polyEval [0, 2, -1, -2, 2] θ, polyEval [-1/2, -1, 5, -2,
    -4, 4] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 8) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 8 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0, 8, -2, -2, 1]⟩, ⟨[4, 4, -10, 2, 2, -1]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [0] θ, polyEval [0, 2, -1, -2, 2] θ, polyEval [1/2, 1, -5, 2, 4,
    -4] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 8) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 8 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0, -8, 2, 2, -1]⟩, ⟨[-4, -4, 10, -2, -2, 1]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [0] θ, polyEval [0, -2, 1, 2, -2] θ, polyEval [-1/2, -1, 5, -2,
    -4, 4] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 8) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 8 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0, -8, 2, 2, -1]⟩, ⟨[4, 4, -10, 2, 2, -1]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [0] θ, polyEval [0, -2, 1, 2, -2] θ, polyEval [1/2, 1, -5, 2, 4,
    -4] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 8) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 8 : ℝ) • Exact.reV (⟨⟨[-4, -4, 10, -2, -2, 1]⟩, ⟨[12, 8, -14, 2, 3, -1]⟩,
    ⟨[4]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1/2, -1, 5, -2, -4, 4] θ, polyEval [3/2, 2, -7, 2, 6,
    -4] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 8) (by norm_num) (by decide +kernel)

theorem pt9 : (1 / 8 : ℝ) • Exact.reV (⟨⟨[-4, -4, 10, -2, -2, 1]⟩, ⟨[12, 8, -14, 2, 3, -1]⟩,
    ⟨[-4]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1/2, -1, 5, -2, -4, 4] θ, polyEval [3/2, 2, -7, 2, 6,
    -4] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 8) (by norm_num) (by decide +kernel)

theorem pt10 : (1 / 8 : ℝ) • Exact.reV (⟨⟨[4, 4, -10, 2, 2, -1]⟩, ⟨[-12, -8, 14, -2, -3, 1]⟩,
    ⟨[4]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1/2, 1, -5, 2, 4, -4] θ, polyEval [-3/2, -2, 7, -2, -6,
    4] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 8) (by norm_num) (by decide +kernel)

theorem pt11 : (1 / 8 : ℝ) • Exact.reV (⟨⟨[4, 4, -10, 2, 2, -1]⟩, ⟨[-12, -8, 14, -2, -3, 1]⟩,
    ⟨[-4]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1/2, 1, -5, 2, 4, -4] θ, polyEval [-3/2, -2, 7, -2,
    -6, 4] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 8) (by norm_num) (by decide +kernel)

theorem pt12 : (1 / 8 : ℝ) • Exact.reV (⟨⟨[-12, -4, 14, -2, -3, 1]⟩, ⟨[16, 16, -18, 0, 4, -1]⟩,
    ⟨[0]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-3/2, -1, 7, -2, -6, 4] θ, polyEval [2, 4, -9, 0, 8,
    -4] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 8) (by norm_num) (by decide +kernel)

theorem pt13 : (1 / 8 : ℝ) • Exact.reV (⟨⟨[12, 4, -14, 2, 3, -1]⟩, ⟨[-16, -16, 18, 0, -4, 1]⟩,
    ⟨[0]⟩⟩ : V3 (ZTheta root)) = ![polyEval [3/2, 1, -7, 2, 6, -4] θ, polyEval [-2, -4, 9, 0, -8, 4]
    θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 8) (by norm_num) (by decide +kernel)

theorem eq_smul : Antiprism.HeptagonalAntiprism.polyhedron = (Polyhedron.ofPoints points).smul (1 / 8) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13]

end Nieuwland.Polyhedra.PrismHeptagonalAntiprismDim

namespace Nieuwland.Polyhedra

/-- **The fixture `prism/heptagonal-antiprism` is full-dimensional.** -/
theorem prismHeptagonalAntiprism_fullDim : Antiprism.HeptagonalAntiprism.polyhedron.FullDim := by
  rw [PrismHeptagonalAntiprismDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk PrismHeptagonalAntiprismDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
