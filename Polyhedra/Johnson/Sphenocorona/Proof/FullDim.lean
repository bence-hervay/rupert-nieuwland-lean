import Polyhedra.Johnson.Sphenocorona.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `johnson/sphenocorona` is full-dimensional

The points of `Johnson.Sphenocorona.polyhedron` times `787320000000` as exact values in `ZTheta root`, exported
by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Johnson.Sphenocorona.polyhedron`.
-/

namespace Nieuwland.Polyhedra.JohnsonSphenocoronaDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Johnson.Sphenocorona.theta

/-- The root `θ`, with `α = 30 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[1/16, 0, -1/150, 0, -397/450, 0, -2/75, 0, 1], 3/4, 9/8,
    30, [41006250000, 0, -4860000, 0, -714600, 0, -24, 0, 1],
    16, 458, 461, 540, 15,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    385018572369591440121812428596668201626610137820994427219860199119198882296793767400275440052844234793253115295586819238543619149262013512270149285575514581,
    385018572369591440121812428596668201626610137820994427219860199119198882296793767400275440052844234793253115295586819238543619149262013512270149285575514582,
    by decide +kernel⟩

theorem root_α : root.α = (30 : ℕ) * θ := rfl

theorem root_n : root.n = 8 := rfl

/-- The points of `Johnson.Sphenocorona.polyhedron` times `787320000000`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[488612250000, 0, -3003615000, 0, -1160100, 0, 6150]⟩, ⟨[393660000000]⟩, ⟨[0]⟩⟩,
    ⟨⟨[488612250000, 0, -3003615000, 0, -1160100, 0, 6150]⟩, ⟨[-393660000000]⟩, ⟨[0]⟩⟩,
    ⟨⟨[-488612250000, 0, 3003615000, 0, 1160100, 0, -6150]⟩, ⟨[393660000000]⟩, ⟨[0]⟩⟩,
    ⟨⟨[-488612250000, 0, 3003615000, 0, 1160100, 0, -6150]⟩, ⟨[-393660000000]⟩, ⟨[0]⟩⟩,
    ⟨⟨[393660000000]⟩, ⟨[0]⟩, ⟨[0, 8921745000, 0, 31880700, 0, 35358, 0, -67]⟩⟩,
    ⟨⟨[-393660000000]⟩, ⟨[0]⟩, ⟨[0, 8921745000, 0, 31880700, 0, 35358, 0, -67]⟩⟩,
    ⟨⟨[0]⟩, ⟨[393660000000]⟩, ⟨[0, -1399680000, 0, -205804800, 0, -6912, 0, 288]⟩⟩,
    ⟨⟨[0]⟩, ⟨[-393660000000]⟩, ⟨[0, -1399680000, 0, -205804800, 0, -6912, 0, 288]⟩⟩,
    ⟨⟨[0]⟩, ⟨[565886250000, 0, -3553875000, 0, -1174500, 0, 6750]⟩, ⟨[0, 24844320000, 0, -205804800, 0, -6912, 0, 288]⟩⟩,
    ⟨⟨[0]⟩, ⟨[-565886250000, 0, 3553875000, 0, 1174500, 0, -6750]⟩, ⟨[0, 24844320000, 0, -205804800, 0, -6912, 0, 288]⟩⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 787320000000 : ℝ) • Exact.reV (⟨⟨[488612250000, 0, -3003615000, 0, -1160100,
    0, 6150]⟩, ⟨[393660000000]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) = ![polyEval [2681/4320, 0, -22249/6480,
    0, -1289/1080, 0, 205/36] θ, polyEval [1/2] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 787320000000) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 787320000000 : ℝ) • Exact.reV (⟨⟨[488612250000, 0, -3003615000, 0, -1160100,
    0, 6150]⟩, ⟨[-393660000000]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) = ![polyEval [2681/4320, 0,
    -22249/6480, 0, -1289/1080, 0, 205/36] θ, polyEval [-1/2] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 787320000000) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 787320000000 : ℝ) • Exact.reV (⟨⟨[-488612250000, 0, 3003615000, 0, 1160100,
    0, -6150]⟩, ⟨[393660000000]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-2681/4320, 0,
    22249/6480, 0, 1289/1080, 0, -205/36] θ, polyEval [1/2] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 787320000000) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 787320000000 : ℝ) • Exact.reV (⟨⟨[-488612250000, 0, 3003615000, 0, 1160100,
    0, -6150]⟩, ⟨[-393660000000]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-2681/4320, 0,
    22249/6480, 0, 1289/1080, 0, -205/36] θ, polyEval [-1/2] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 787320000000) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 787320000000 : ℝ) • Exact.reV (⟨⟨[393660000000]⟩, ⟨[0]⟩, ⟨[0, 8921745000, 0,
    31880700, 0, 35358, 0, -67]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1/2] θ, polyEval [0] θ, polyEval
    [0, 7343/21600, 0, 35423/32400, 0, 5893/5400, 0, -67/36] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 787320000000) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 787320000000 : ℝ) • Exact.reV (⟨⟨[-393660000000]⟩, ⟨[0]⟩, ⟨[0, 8921745000, 0,
    31880700, 0, 35358, 0, -67]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1/2] θ, polyEval [0] θ,
    polyEval [0, 7343/21600, 0, 35423/32400, 0, 5893/5400, 0, -67/36] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 787320000000) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 787320000000 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[393660000000]⟩, ⟨[0, -1399680000, 0,
    -205804800, 0, -6912, 0, 288]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0] θ, polyEval [1/2] θ,
    polyEval [0, -4/75, 0, -1588/225, 0, -16/75, 0, 8] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 787320000000) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 787320000000 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[-393660000000]⟩, ⟨[0, -1399680000,
    0, -205804800, 0, -6912, 0, 288]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0] θ, polyEval [-1/2] θ,
    polyEval [0, -4/75, 0, -1588/225, 0, -16/75, 0, 8] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 787320000000) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 787320000000 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[565886250000, 0, -3553875000, 0,
    -1174500, 0, 6750]⟩, ⟨[0, 24844320000, 0, -205804800, 0, -6912, 0, 288]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0] θ, polyEval [23/32, 0, -65/16, 0, -29/24, 0, 25/4] θ, polyEval [0, 71/75, 0,
    -1588/225, 0, -16/75, 0, 8] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 787320000000) (by norm_num) (by decide +kernel)

theorem pt9 : (1 / 787320000000 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[-565886250000, 0, 3553875000, 0,
    1174500, 0, -6750]⟩, ⟨[0, 24844320000, 0, -205804800, 0, -6912, 0, 288]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0] θ, polyEval [-23/32, 0, 65/16, 0, 29/24, 0, -25/4] θ, polyEval [0, 71/75, 0,
    -1588/225, 0, -16/75, 0, 8] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 787320000000) (by norm_num) (by decide +kernel)

theorem eq_smul : Johnson.Sphenocorona.polyhedron = (Polyhedron.ofPoints points).smul (1 / 787320000000) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9]

end Nieuwland.Polyhedra.JohnsonSphenocoronaDim

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/sphenocorona` is full-dimensional.** -/
theorem johnsonSphenocorona_fullDim : Johnson.Sphenocorona.polyhedron.FullDim := by
  rw [JohnsonSphenocoronaDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk JohnsonSphenocoronaDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
