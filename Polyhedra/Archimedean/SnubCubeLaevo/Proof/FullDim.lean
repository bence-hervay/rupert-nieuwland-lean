import Polyhedra.Archimedean.SnubCubeLaevo.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `archimedean/snub-cube-laevo` is full-dimensional

The points of `Archimedean.SnubCubeLaevo.polyhedron` times `1` as exact values in `ZTheta root`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Archimedean.SnubCubeLaevo.polyhedron`.
-/

namespace Nieuwland.Polyhedra.ArchimedeanSnubCubeLaevoDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Archimedean.SnubCubeLaevo.theta

/-- The root `θ`, with `α = 1 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[-1, -1, -1, 1], 9/5, 19/10,
    1, [-1, -1, -1, 1],
    64, 116, 119, 122, 5,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    24660803541998818086862136803621097301164334678345065298750398714007843973879847761164890242539638337152130218363552450097087132220397080821077748503193096,
    24660803541998818086862136803621097301164334678345065298750398714007843973879847761164890242539638337152130218363552450097087132220397080821077748503193097,
    by decide +kernel⟩

theorem root_α : root.α = (1 : ℕ) * θ := rfl

theorem root_n : root.n = 3 := rfl

/-- The points of `Archimedean.SnubCubeLaevo.polyhedron` times `1`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[1]⟩, ⟨[-1, -1, 1]⟩, ⟨[0, 1]⟩⟩,
    ⟨⟨[-1]⟩, ⟨[1, 1, -1]⟩, ⟨[0, 1]⟩⟩,
    ⟨⟨[-1]⟩, ⟨[-1, -1, 1]⟩, ⟨[0, -1]⟩⟩,
    ⟨⟨[1]⟩, ⟨[1, 1, -1]⟩, ⟨[0, -1]⟩⟩,
    ⟨⟨[-1, -1, 1]⟩, ⟨[0, 1]⟩, ⟨[1]⟩⟩,
    ⟨⟨[1, 1, -1]⟩, ⟨[0, -1]⟩, ⟨[1]⟩⟩,
    ⟨⟨[1, 1, -1]⟩, ⟨[0, 1]⟩, ⟨[-1]⟩⟩,
    ⟨⟨[-1, -1, 1]⟩, ⟨[0, -1]⟩, ⟨[-1]⟩⟩,
    ⟨⟨[0, 1]⟩, ⟨[1]⟩, ⟨[-1, -1, 1]⟩⟩,
    ⟨⟨[0, -1]⟩, ⟨[-1]⟩, ⟨[-1, -1, 1]⟩⟩,
    ⟨⟨[0, -1]⟩, ⟨[1]⟩, ⟨[1, 1, -1]⟩⟩,
    ⟨⟨[0, 1]⟩, ⟨[-1]⟩, ⟨[1, 1, -1]⟩⟩,
    ⟨⟨[-1]⟩, ⟨[0, 1]⟩, ⟨[-1, -1, 1]⟩⟩,
    ⟨⟨[1]⟩, ⟨[0, -1]⟩, ⟨[-1, -1, 1]⟩⟩,
    ⟨⟨[1]⟩, ⟨[0, 1]⟩, ⟨[1, 1, -1]⟩⟩,
    ⟨⟨[-1]⟩, ⟨[0, -1]⟩, ⟨[1, 1, -1]⟩⟩,
    ⟨⟨[0, -1]⟩, ⟨[-1, -1, 1]⟩, ⟨[1]⟩⟩,
    ⟨⟨[0, 1]⟩, ⟨[1, 1, -1]⟩, ⟨[1]⟩⟩,
    ⟨⟨[0, 1]⟩, ⟨[-1, -1, 1]⟩, ⟨[-1]⟩⟩,
    ⟨⟨[0, -1]⟩, ⟨[1, 1, -1]⟩, ⟨[-1]⟩⟩,
    ⟨⟨[1, 1, -1]⟩, ⟨[1]⟩, ⟨[0, 1]⟩⟩,
    ⟨⟨[-1, -1, 1]⟩, ⟨[-1]⟩, ⟨[0, 1]⟩⟩,
    ⟨⟨[-1, -1, 1]⟩, ⟨[1]⟩, ⟨[0, -1]⟩⟩,
    ⟨⟨[1, 1, -1]⟩, ⟨[-1]⟩, ⟨[0, -1]⟩⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[1]⟩, ⟨[-1, -1, 1]⟩, ⟨[0, 1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [1] θ, polyEval [-1, -1, 1] θ, polyEval [0, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-1]⟩, ⟨[1, 1, -1]⟩, ⟨[0, 1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [-1] θ, polyEval [1, 1, -1] θ, polyEval [0, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-1]⟩, ⟨[-1, -1, 1]⟩, ⟨[0, -1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [-1] θ, polyEval [-1, -1, 1] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[1]⟩, ⟨[1, 1, -1]⟩, ⟨[0, -1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [1] θ, polyEval [1, 1, -1] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-1, -1, 1]⟩, ⟨[0, 1]⟩, ⟨[1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [-1, -1, 1] θ, polyEval [0, 1] θ, polyEval [1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[1, 1, -1]⟩, ⟨[0, -1]⟩, ⟨[1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [1, 1, -1] θ, polyEval [0, -1] θ, polyEval [1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[1, 1, -1]⟩, ⟨[0, 1]⟩, ⟨[-1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [1, 1, -1] θ, polyEval [0, 1] θ, polyEval [-1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-1, -1, 1]⟩, ⟨[0, -1]⟩, ⟨[-1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [-1, -1, 1] θ, polyEval [0, -1] θ, polyEval [-1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[0, 1]⟩, ⟨[1]⟩, ⟨[-1, -1, 1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1] θ, polyEval [1] θ, polyEval [-1, -1, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt9 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[0, -1]⟩, ⟨[-1]⟩, ⟨[-1, -1, 1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, -1] θ, polyEval [-1] θ, polyEval [-1, -1, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt10 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[0, -1]⟩, ⟨[1]⟩, ⟨[1, 1, -1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, -1] θ, polyEval [1] θ, polyEval [1, 1, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt11 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[0, 1]⟩, ⟨[-1]⟩, ⟨[1, 1, -1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1] θ, polyEval [-1] θ, polyEval [1, 1, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt12 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-1]⟩, ⟨[0, 1]⟩, ⟨[-1, -1, 1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [-1] θ, polyEval [0, 1] θ, polyEval [-1, -1, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt13 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[1]⟩, ⟨[0, -1]⟩, ⟨[-1, -1, 1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [1] θ, polyEval [0, -1] θ, polyEval [-1, -1, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt14 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[1]⟩, ⟨[0, 1]⟩, ⟨[1, 1, -1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [1] θ, polyEval [0, 1] θ, polyEval [1, 1, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt15 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-1]⟩, ⟨[0, -1]⟩, ⟨[1, 1, -1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [-1] θ, polyEval [0, -1] θ, polyEval [1, 1, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt16 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[0, -1]⟩, ⟨[-1, -1, 1]⟩, ⟨[1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, -1] θ, polyEval [-1, -1, 1] θ, polyEval [1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt17 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[0, 1]⟩, ⟨[1, 1, -1]⟩, ⟨[1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1] θ, polyEval [1, 1, -1] θ, polyEval [1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt18 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[0, 1]⟩, ⟨[-1, -1, 1]⟩, ⟨[-1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1] θ, polyEval [-1, -1, 1] θ, polyEval [-1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt19 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[0, -1]⟩, ⟨[1, 1, -1]⟩, ⟨[-1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, -1] θ, polyEval [1, 1, -1] θ, polyEval [-1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt20 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[1, 1, -1]⟩, ⟨[1]⟩, ⟨[0, 1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [1, 1, -1] θ, polyEval [1] θ, polyEval [0, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt21 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-1, -1, 1]⟩, ⟨[-1]⟩, ⟨[0, 1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [-1, -1, 1] θ, polyEval [-1] θ, polyEval [0, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt22 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-1, -1, 1]⟩, ⟨[1]⟩, ⟨[0, -1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [-1, -1, 1] θ, polyEval [1] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt23 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[1, 1, -1]⟩, ⟨[-1]⟩, ⟨[0, -1]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [1, 1, -1] θ, polyEval [-1] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem eq_smul : Archimedean.SnubCubeLaevo.polyhedron = (Polyhedron.ofPoints points).smul (1 / 1) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17, pt18, pt19, pt20, pt21, pt22, pt23]

end Nieuwland.Polyhedra.ArchimedeanSnubCubeLaevoDim

namespace Nieuwland.Polyhedra

/-- **The fixture `archimedean/snub-cube-laevo` is full-dimensional.** -/
theorem archimedeanSnubCubeLaevo_fullDim : Archimedean.SnubCubeLaevo.polyhedron.FullDim := by
  rw [ArchimedeanSnubCubeLaevoDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk ArchimedeanSnubCubeLaevoDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
