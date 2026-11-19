import Polyhedra.Prism.DecagonalPrism.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `prism/decagonal-prism` is full-dimensional

The points of `Prism.DecagonalPrism.polyhedron` times `82` as exact values in `ZTheta root`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Prism.DecagonalPrism.polyhedron`.
-/

namespace Nieuwland.Polyhedra.PrismDecagonalPrismDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Prism.DecagonalPrism.theta

/-- The root `θ`, with `α = 2 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[1/16, 2, -9/4, -2, 1], 2, 7/2,
    2, [1, 16, -9, -4, 1],
    16, 81, 84, 112, 11,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    68891744092566463941535618110332877725605386133711750930811834346123351590253094616410494889731007506219618868490482997196862290662844640510056665266744061,
    68891744092566463941535618110332877725605386133711750930811834346123351590253094616410494889731007506219618868490482997196862290662844640510056665266744062,
    by decide +kernel⟩

theorem root_α : root.α = (2 : ℕ) * θ := rfl

theorem root_n : root.n = 4 := rfl

/-- The points of `Prism.DecagonalPrism.polyhedron` times `82`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[-44, 112, 26, -8]⟩, ⟨[0]⟩, ⟨[-41]⟩⟩,
    ⟨⟨[19, 56, 13, -4]⟩, ⟨[44, -71, -26, 8]⟩, ⟨[-41]⟩⟩,
    ⟨⟨[41]⟩, ⟨[-34, -70, -6, 5]⟩, ⟨[-41]⟩⟩,
    ⟨⟨[-41]⟩, ⟨[-34, -70, -6, 5]⟩, ⟨[-41]⟩⟩,
    ⟨⟨[-19, -56, -13, 4]⟩, ⟨[44, -71, -26, 8]⟩, ⟨[-41]⟩⟩,
    ⟨⟨[44, -112, -26, 8]⟩, ⟨[0]⟩, ⟨[-41]⟩⟩,
    ⟨⟨[-19, -56, -13, 4]⟩, ⟨[-44, 71, 26, -8]⟩, ⟨[-41]⟩⟩,
    ⟨⟨[-41]⟩, ⟨[34, 70, 6, -5]⟩, ⟨[-41]⟩⟩,
    ⟨⟨[41]⟩, ⟨[34, 70, 6, -5]⟩, ⟨[-41]⟩⟩,
    ⟨⟨[19, 56, 13, -4]⟩, ⟨[-44, 71, 26, -8]⟩, ⟨[-41]⟩⟩,
    ⟨⟨[-44, 112, 26, -8]⟩, ⟨[0]⟩, ⟨[41]⟩⟩,
    ⟨⟨[19, 56, 13, -4]⟩, ⟨[44, -71, -26, 8]⟩, ⟨[41]⟩⟩,
    ⟨⟨[41]⟩, ⟨[-34, -70, -6, 5]⟩, ⟨[41]⟩⟩,
    ⟨⟨[-41]⟩, ⟨[-34, -70, -6, 5]⟩, ⟨[41]⟩⟩,
    ⟨⟨[-19, -56, -13, 4]⟩, ⟨[44, -71, -26, 8]⟩, ⟨[41]⟩⟩,
    ⟨⟨[44, -112, -26, 8]⟩, ⟨[0]⟩, ⟨[41]⟩⟩,
    ⟨⟨[-19, -56, -13, 4]⟩, ⟨[-44, 71, 26, -8]⟩, ⟨[41]⟩⟩,
    ⟨⟨[-41]⟩, ⟨[34, 70, 6, -5]⟩, ⟨[41]⟩⟩,
    ⟨⟨[41]⟩, ⟨[34, 70, 6, -5]⟩, ⟨[41]⟩⟩,
    ⟨⟨[19, 56, 13, -4]⟩, ⟨[-44, 71, 26, -8]⟩, ⟨[41]⟩⟩]

theorem span_ok : spanOk points 0 1 2 10 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 82 : ℝ) • Exact.reV (⟨⟨[-44, 112, 26, -8]⟩, ⟨[0]⟩, ⟨[-41]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [-22/41, 112/41, 52/41, -32/41] θ, polyEval [0] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 82) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 82 : ℝ) • Exact.reV (⟨⟨[19, 56, 13, -4]⟩, ⟨[44, -71, -26, 8]⟩, ⟨[-41]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [19/82, 56/41, 26/41, -16/41] θ, polyEval [22/41, -71/41, -52/41,
    32/41] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 82) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 82 : ℝ) • Exact.reV (⟨⟨[41]⟩, ⟨[-34, -70, -6, 5]⟩, ⟨[-41]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [1/2] θ, polyEval [-17/41, -70/41, -12/41, 20/41] θ, polyEval [-1/2] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 82) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 82 : ℝ) • Exact.reV (⟨⟨[-41]⟩, ⟨[-34, -70, -6, 5]⟩, ⟨[-41]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [-1/2] θ, polyEval [-17/41, -70/41, -12/41, 20/41] θ, polyEval [-1/2] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 82) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 82 : ℝ) • Exact.reV (⟨⟨[-19, -56, -13, 4]⟩, ⟨[44, -71, -26, 8]⟩, ⟨[-41]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [-19/82, -56/41, -26/41, 16/41] θ, polyEval [22/41, -71/41,
    -52/41, 32/41] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 82) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 82 : ℝ) • Exact.reV (⟨⟨[44, -112, -26, 8]⟩, ⟨[0]⟩, ⟨[-41]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [22/41, -112/41, -52/41, 32/41] θ, polyEval [0] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 82) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 82 : ℝ) • Exact.reV (⟨⟨[-19, -56, -13, 4]⟩, ⟨[-44, 71, 26, -8]⟩, ⟨[-41]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [-19/82, -56/41, -26/41, 16/41] θ, polyEval [-22/41, 71/41,
    52/41, -32/41] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 82) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 82 : ℝ) • Exact.reV (⟨⟨[-41]⟩, ⟨[34, 70, 6, -5]⟩, ⟨[-41]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [-1/2] θ, polyEval [17/41, 70/41, 12/41, -20/41] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 82) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 82 : ℝ) • Exact.reV (⟨⟨[41]⟩, ⟨[34, 70, 6, -5]⟩, ⟨[-41]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [1/2] θ, polyEval [17/41, 70/41, 12/41, -20/41] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 82) (by norm_num) (by decide +kernel)

theorem pt9 : (1 / 82 : ℝ) • Exact.reV (⟨⟨[19, 56, 13, -4]⟩, ⟨[-44, 71, 26, -8]⟩, ⟨[-41]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [19/82, 56/41, 26/41, -16/41] θ, polyEval [-22/41, 71/41, 52/41,
    -32/41] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 82) (by norm_num) (by decide +kernel)

theorem pt10 : (1 / 82 : ℝ) • Exact.reV (⟨⟨[-44, 112, 26, -8]⟩, ⟨[0]⟩, ⟨[41]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [-22/41, 112/41, 52/41, -32/41] θ, polyEval [0] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 82) (by norm_num) (by decide +kernel)

theorem pt11 : (1 / 82 : ℝ) • Exact.reV (⟨⟨[19, 56, 13, -4]⟩, ⟨[44, -71, -26, 8]⟩, ⟨[41]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [19/82, 56/41, 26/41, -16/41] θ, polyEval [22/41, -71/41, -52/41,
    32/41] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 82) (by norm_num) (by decide +kernel)

theorem pt12 : (1 / 82 : ℝ) • Exact.reV (⟨⟨[41]⟩, ⟨[-34, -70, -6, 5]⟩, ⟨[41]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [1/2] θ, polyEval [-17/41, -70/41, -12/41, 20/41] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 82) (by norm_num) (by decide +kernel)

theorem pt13 : (1 / 82 : ℝ) • Exact.reV (⟨⟨[-41]⟩, ⟨[-34, -70, -6, 5]⟩, ⟨[41]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [-1/2] θ, polyEval [-17/41, -70/41, -12/41, 20/41] θ, polyEval [1/2] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 82) (by norm_num) (by decide +kernel)

theorem pt14 : (1 / 82 : ℝ) • Exact.reV (⟨⟨[-19, -56, -13, 4]⟩, ⟨[44, -71, -26, 8]⟩, ⟨[41]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [-19/82, -56/41, -26/41, 16/41] θ, polyEval [22/41, -71/41,
    -52/41, 32/41] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 82) (by norm_num) (by decide +kernel)

theorem pt15 : (1 / 82 : ℝ) • Exact.reV (⟨⟨[44, -112, -26, 8]⟩, ⟨[0]⟩, ⟨[41]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [22/41, -112/41, -52/41, 32/41] θ, polyEval [0] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 82) (by norm_num) (by decide +kernel)

theorem pt16 : (1 / 82 : ℝ) • Exact.reV (⟨⟨[-19, -56, -13, 4]⟩, ⟨[-44, 71, 26, -8]⟩, ⟨[41]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [-19/82, -56/41, -26/41, 16/41] θ, polyEval [-22/41, 71/41,
    52/41, -32/41] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 82) (by norm_num) (by decide +kernel)

theorem pt17 : (1 / 82 : ℝ) • Exact.reV (⟨⟨[-41]⟩, ⟨[34, 70, 6, -5]⟩, ⟨[41]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [-1/2] θ, polyEval [17/41, 70/41, 12/41, -20/41] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 82) (by norm_num) (by decide +kernel)

theorem pt18 : (1 / 82 : ℝ) • Exact.reV (⟨⟨[41]⟩, ⟨[34, 70, 6, -5]⟩, ⟨[41]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [1/2] θ, polyEval [17/41, 70/41, 12/41, -20/41] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 82) (by norm_num) (by decide +kernel)

theorem pt19 : (1 / 82 : ℝ) • Exact.reV (⟨⟨[19, 56, 13, -4]⟩, ⟨[-44, 71, 26, -8]⟩, ⟨[41]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [19/82, 56/41, 26/41, -16/41] θ, polyEval [-22/41, 71/41, 52/41,
    -32/41] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 82) (by norm_num) (by decide +kernel)

theorem eq_smul : Prism.DecagonalPrism.polyhedron = (Polyhedron.ofPoints points).smul (1 / 82) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17, pt18, pt19]

end Nieuwland.Polyhedra.PrismDecagonalPrismDim

namespace Nieuwland.Polyhedra

/-- **The fixture `prism/decagonal-prism` is full-dimensional.** -/
theorem prismDecagonalPrism_fullDim : Prism.DecagonalPrism.polyhedron.FullDim := by
  rw [PrismDecagonalPrismDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk PrismDecagonalPrismDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
