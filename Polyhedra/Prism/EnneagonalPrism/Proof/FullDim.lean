import Polyhedra.Prism.EnneagonalPrism.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `prism/enneagonal-prism` is full-dimensional

The points of `Prism.EnneagonalPrism.polyhedron` times `162` as exact values in `ZTheta root`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Prism.EnneagonalPrism.polyhedron`.
-/

namespace Nieuwland.Polyhedra.PrismEnneagonalPrismDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Prism.EnneagonalPrism.theta

/-- The root `θ`, with `α = 3 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[-1/3, 0, 2, 0, -3, 0, 1], 1, 7/4,
    3, [-243, 0, 162, 0, -27, 0, 1],
    32, 139, 142, 168, 13,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    58802711733161549551380968345157969366387084792655274302305968954725771892260630320295573520531738890107294808298916187119755024999801649881003572867297879,
    58802711733161549551380968345157969366387084792655274302305968954725771892260630320295573520531738890107294808298916187119755024999801649881003572867297880,
    by decide +kernel⟩

theorem root_α : root.α = (3 : ℕ) * θ := rfl

theorem root_n : root.n = 6 := rfl

/-- The points of `Prism.EnneagonalPrism.polyhedron` times `162`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[0, 54]⟩, ⟨[0]⟩, ⟨[-81]⟩⟩,
    ⟨⟨[0, -108, 0, 27, 0, -1]⟩, ⟨[81, 0, -54, 0, 3]⟩, ⟨[-81]⟩⟩,
    ⟨⟨[0, 135, 0, -45, 0, 2]⟩, ⟨[162, 0, -54, 0, 3]⟩, ⟨[-81]⟩⟩,
    ⟨⟨[0, -27]⟩, ⟨[-243, 0, 81, 0, -3]⟩, ⟨[-81]⟩⟩,
    ⟨⟨[0, -27, 0, 18, 0, -1]⟩, ⟨[81]⟩, ⟨[-81]⟩⟩,
    ⟨⟨[0, -27, 0, 18, 0, -1]⟩, ⟨[-81]⟩, ⟨[-81]⟩⟩,
    ⟨⟨[0, -27]⟩, ⟨[243, 0, -81, 0, 3]⟩, ⟨[-81]⟩⟩,
    ⟨⟨[0, 135, 0, -45, 0, 2]⟩, ⟨[-162, 0, 54, 0, -3]⟩, ⟨[-81]⟩⟩,
    ⟨⟨[0, -108, 0, 27, 0, -1]⟩, ⟨[-81, 0, 54, 0, -3]⟩, ⟨[-81]⟩⟩,
    ⟨⟨[0, 54]⟩, ⟨[0]⟩, ⟨[81]⟩⟩,
    ⟨⟨[0, -108, 0, 27, 0, -1]⟩, ⟨[81, 0, -54, 0, 3]⟩, ⟨[81]⟩⟩,
    ⟨⟨[0, 135, 0, -45, 0, 2]⟩, ⟨[162, 0, -54, 0, 3]⟩, ⟨[81]⟩⟩,
    ⟨⟨[0, -27]⟩, ⟨[-243, 0, 81, 0, -3]⟩, ⟨[81]⟩⟩,
    ⟨⟨[0, -27, 0, 18, 0, -1]⟩, ⟨[81]⟩, ⟨[81]⟩⟩,
    ⟨⟨[0, -27, 0, 18, 0, -1]⟩, ⟨[-81]⟩, ⟨[81]⟩⟩,
    ⟨⟨[0, -27]⟩, ⟨[243, 0, -81, 0, 3]⟩, ⟨[81]⟩⟩,
    ⟨⟨[0, 135, 0, -45, 0, 2]⟩, ⟨[-162, 0, 54, 0, -3]⟩, ⟨[81]⟩⟩,
    ⟨⟨[0, -108, 0, 27, 0, -1]⟩, ⟨[-81, 0, 54, 0, -3]⟩, ⟨[81]⟩⟩]

theorem span_ok : spanOk points 0 1 2 9 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 162 : ℝ) • Exact.reV (⟨⟨[0, 54]⟩, ⟨[0]⟩, ⟨[-81]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1] θ, polyEval [0] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 162) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 162 : ℝ) • Exact.reV (⟨⟨[0, -108, 0, 27, 0, -1]⟩, ⟨[81, 0, -54, 0, 3]⟩,
    ⟨[-81]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, -2, 0, 9/2, 0, -3/2] θ, polyEval [1/2, 0, -3, 0,
    3/2] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 162) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 162 : ℝ) • Exact.reV (⟨⟨[0, 135, 0, -45, 0, 2]⟩, ⟨[162, 0, -54, 0, 3]⟩,
    ⟨[-81]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 5/2, 0, -15/2, 0, 3] θ, polyEval [1, 0, -3, 0,
    3/2] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 162) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 162 : ℝ) • Exact.reV (⟨⟨[0, -27]⟩, ⟨[-243, 0, 81, 0, -3]⟩, ⟨[-81]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0, -1/2] θ, polyEval [-3/2, 0, 9/2, 0, -3/2] θ, polyEval [-1/2] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 162) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 162 : ℝ) • Exact.reV (⟨⟨[0, -27, 0, 18, 0, -1]⟩, ⟨[81]⟩, ⟨[-81]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0, -1/2, 0, 3, 0, -3/2] θ, polyEval [1/2] θ, polyEval [-1/2] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 162) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 162 : ℝ) • Exact.reV (⟨⟨[0, -27, 0, 18, 0, -1]⟩, ⟨[-81]⟩, ⟨[-81]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0, -1/2, 0, 3, 0, -3/2] θ, polyEval [-1/2] θ, polyEval [-1/2] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 162) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 162 : ℝ) • Exact.reV (⟨⟨[0, -27]⟩, ⟨[243, 0, -81, 0, 3]⟩, ⟨[-81]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0, -1/2] θ, polyEval [3/2, 0, -9/2, 0, 3/2] θ, polyEval [-1/2] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 162) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 162 : ℝ) • Exact.reV (⟨⟨[0, 135, 0, -45, 0, 2]⟩, ⟨[-162, 0, 54, 0, -3]⟩,
    ⟨[-81]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 5/2, 0, -15/2, 0, 3] θ, polyEval [-1, 0, 3, 0,
    -3/2] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 162) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 162 : ℝ) • Exact.reV (⟨⟨[0, -108, 0, 27, 0, -1]⟩, ⟨[-81, 0, 54, 0, -3]⟩,
    ⟨[-81]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, -2, 0, 9/2, 0, -3/2] θ, polyEval [-1/2, 0, 3, 0,
    -3/2] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 162) (by norm_num) (by decide +kernel)

theorem pt9 : (1 / 162 : ℝ) • Exact.reV (⟨⟨[0, 54]⟩, ⟨[0]⟩, ⟨[81]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1] θ, polyEval [0] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 162) (by norm_num) (by decide +kernel)

theorem pt10 : (1 / 162 : ℝ) • Exact.reV (⟨⟨[0, -108, 0, 27, 0, -1]⟩, ⟨[81, 0, -54, 0, 3]⟩,
    ⟨[81]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, -2, 0, 9/2, 0, -3/2] θ, polyEval [1/2, 0, -3, 0,
    3/2] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 162) (by norm_num) (by decide +kernel)

theorem pt11 : (1 / 162 : ℝ) • Exact.reV (⟨⟨[0, 135, 0, -45, 0, 2]⟩, ⟨[162, 0, -54, 0, 3]⟩,
    ⟨[81]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 5/2, 0, -15/2, 0, 3] θ, polyEval [1, 0, -3, 0, 3/2]
    θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 162) (by norm_num) (by decide +kernel)

theorem pt12 : (1 / 162 : ℝ) • Exact.reV (⟨⟨[0, -27]⟩, ⟨[-243, 0, 81, 0, -3]⟩, ⟨[81]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0, -1/2] θ, polyEval [-3/2, 0, 9/2, 0, -3/2] θ, polyEval [1/2] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 162) (by norm_num) (by decide +kernel)

theorem pt13 : (1 / 162 : ℝ) • Exact.reV (⟨⟨[0, -27, 0, 18, 0, -1]⟩, ⟨[81]⟩, ⟨[81]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0, -1/2, 0, 3, 0, -3/2] θ, polyEval [1/2] θ, polyEval [1/2] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 162) (by norm_num) (by decide +kernel)

theorem pt14 : (1 / 162 : ℝ) • Exact.reV (⟨⟨[0, -27, 0, 18, 0, -1]⟩, ⟨[-81]⟩, ⟨[81]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0, -1/2, 0, 3, 0, -3/2] θ, polyEval [-1/2] θ, polyEval [1/2] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 162) (by norm_num) (by decide +kernel)

theorem pt15 : (1 / 162 : ℝ) • Exact.reV (⟨⟨[0, -27]⟩, ⟨[243, 0, -81, 0, 3]⟩, ⟨[81]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0, -1/2] θ, polyEval [3/2, 0, -9/2, 0, 3/2] θ, polyEval [1/2] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 162) (by norm_num) (by decide +kernel)

theorem pt16 : (1 / 162 : ℝ) • Exact.reV (⟨⟨[0, 135, 0, -45, 0, 2]⟩, ⟨[-162, 0, 54, 0, -3]⟩,
    ⟨[81]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 5/2, 0, -15/2, 0, 3] θ, polyEval [-1, 0, 3, 0,
    -3/2] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 162) (by norm_num) (by decide +kernel)

theorem pt17 : (1 / 162 : ℝ) • Exact.reV (⟨⟨[0, -108, 0, 27, 0, -1]⟩, ⟨[-81, 0, 54, 0, -3]⟩,
    ⟨[81]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, -2, 0, 9/2, 0, -3/2] θ, polyEval [-1/2, 0, 3, 0,
    -3/2] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 162) (by norm_num) (by decide +kernel)

theorem eq_smul : Prism.EnneagonalPrism.polyhedron = (Polyhedron.ofPoints points).smul (1 / 162) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17]

end Nieuwland.Polyhedra.PrismEnneagonalPrismDim

namespace Nieuwland.Polyhedra

/-- **The fixture `prism/enneagonal-prism` is full-dimensional.** -/
theorem prismEnneagonalPrism_fullDim : Prism.EnneagonalPrism.polyhedron.FullDim := by
  rw [PrismEnneagonalPrismDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk PrismEnneagonalPrismDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
