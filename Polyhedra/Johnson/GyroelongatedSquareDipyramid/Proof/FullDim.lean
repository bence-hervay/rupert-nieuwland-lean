import Polyhedra.Johnson.GyroelongatedSquareDipyramid.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `johnson/gyroelongated-square-dipyramid` is full-dimensional

The points of `Johnson.GyroelongatedSquareDipyramid.polyhedron` times `4` as exact values in `ZTheta root`,
exported by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`,
checked by the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`),
and scaled back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Johnson.GyroelongatedSquareDipyramid.polyhedron`.
-/

namespace Nieuwland.Polyhedra.JohnsonGyroelongatedSquareDipyramidDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Johnson.GyroelongatedSquareDipyramid.theta

/-- The root `θ`, with `α = 4 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[-1/32, 0, 0, 0, 1], 0, 3/4,
    4, [-8, 0, 0, 0, 1],
    32, 52, 55, 96, 15,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    22549155249398113837631364189052330388456733078755276941380911784711959257734108378537539443542187079212107329664282274818496023599770811733208286377543343,
    22549155249398113837631364189052330388456733078755276941380911784711959257734108378537539443542187079212107329664282274818496023599770811733208286377543344,
    by decide +kernel⟩

theorem root_α : root.α = (4 : ℕ) * θ := rfl

theorem root_n : root.n = 4 := rfl

/-- The points of `Johnson.GyroelongatedSquareDipyramid.polyhedron` times `4`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[0, 0, 1]⟩, ⟨[0]⟩, ⟨[0, 1]⟩⟩,
    ⟨⟨[0, 0, -1]⟩, ⟨[0]⟩, ⟨[0, 1]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0, 0, 1]⟩, ⟨[0, 1]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0, 0, -1]⟩, ⟨[0, 1]⟩⟩,
    ⟨⟨[2]⟩, ⟨[2]⟩, ⟨[0, -1]⟩⟩,
    ⟨⟨[2]⟩, ⟨[-2]⟩, ⟨[0, -1]⟩⟩,
    ⟨⟨[-2]⟩, ⟨[2]⟩, ⟨[0, -1]⟩⟩,
    ⟨⟨[-2]⟩, ⟨[-2]⟩, ⟨[0, -1]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0]⟩, ⟨[0, 1, 1]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0]⟩, ⟨[0, -1, -1]⟩⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 4 : ℝ) • Exact.reV (⟨⟨[0, 0, 1]⟩, ⟨[0]⟩, ⟨[0, 1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 0, 4] θ, polyEval [0] θ, polyEval [0, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 4) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 4 : ℝ) • Exact.reV (⟨⟨[0, 0, -1]⟩, ⟨[0]⟩, ⟨[0, 1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 0, -4] θ, polyEval [0] θ, polyEval [0, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 4) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 4 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0, 0, 1]⟩, ⟨[0, 1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0] θ, polyEval [0, 0, 4] θ, polyEval [0, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 4) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 4 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0, 0, -1]⟩, ⟨[0, 1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0] θ, polyEval [0, 0, -4] θ, polyEval [0, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 4) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 4 : ℝ) • Exact.reV (⟨⟨[2]⟩, ⟨[2]⟩, ⟨[0, -1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [1/2] θ, polyEval [1/2] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 4) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 4 : ℝ) • Exact.reV (⟨⟨[2]⟩, ⟨[-2]⟩, ⟨[0, -1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [1/2] θ, polyEval [-1/2] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 4) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 4 : ℝ) • Exact.reV (⟨⟨[-2]⟩, ⟨[2]⟩, ⟨[0, -1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [-1/2] θ, polyEval [1/2] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 4) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 4 : ℝ) • Exact.reV (⟨⟨[-2]⟩, ⟨[-2]⟩, ⟨[0, -1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [-1/2] θ, polyEval [-1/2] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 4) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 4 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0]⟩, ⟨[0, 1, 1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0] θ, polyEval [0] θ, polyEval [0, 1, 4] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 4) (by norm_num) (by decide +kernel)

theorem pt9 : (1 / 4 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0]⟩, ⟨[0, -1, -1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0] θ, polyEval [0] θ, polyEval [0, -1, -4] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 4) (by norm_num) (by decide +kernel)

theorem eq_smul : Johnson.GyroelongatedSquareDipyramid.polyhedron = (Polyhedron.ofPoints points).smul (1 / 4) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9]

end Nieuwland.Polyhedra.JohnsonGyroelongatedSquareDipyramidDim

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/gyroelongated-square-dipyramid` is full-dimensional.** -/
theorem johnsonGyroelongatedSquareDipyramid_fullDim : Johnson.GyroelongatedSquareDipyramid.polyhedron.FullDim := by
  rw [JohnsonGyroelongatedSquareDipyramidDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk JohnsonGyroelongatedSquareDipyramidDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
