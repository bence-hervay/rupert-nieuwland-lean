import Polyhedra.Archimedean.SnubDodecahedronLaevo.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `archimedean/snub-dodecahedron-laevo` is full-dimensional

The points of `Archimedean.SnubDodecahedronLaevo.polyhedron` times `1` as exact values in `ZTheta root`,
exported by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`,
checked by the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`),
and scaled back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Archimedean.SnubDodecahedronLaevo.polyhedron`.
-/

namespace Nieuwland.Polyhedra.ArchimedeanSnubDodecahedronLaevoDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Archimedean.SnubDodecahedronLaevo.theta

/-- The root `θ`, with `α = 1 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[-1, 2, 4, -1, -4, 0, 1], 3431/2000, 4289/2500,
    1, [-1, 2, 4, -1, -4, 0, 1],
    65536, 112430, 112433, 112434, 3,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    23001919079946582848024815760011714386367023889214022030940138728125162777913184968519590255638075170075246216587536783906417695001268584915861602929566141,
    23001919079946582848024815760011714386367023889214022030940138728125162777913184968519590255638075170075246216587536783906417695001268584915861602929566142,
    by decide +kernel⟩

theorem root_α : root.α = (1 : ℕ) * θ := rfl

theorem root_n : root.n = 6 := rfl

/-- The points of `Archimedean.SnubDodecahedronLaevo.polyhedron` times `1`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[-6, -4, 6, 6, -2, -2]⟩, ⟨[0, -2]⟩, ⟨[-2, 0, 2]⟩⟩,
    ⟨⟨[-6, -4, 6, 6, -2, -2]⟩, ⟨[0, 2]⟩, ⟨[2, 0, -2]⟩⟩,
    ⟨⟨[-4, -8, 2, 8, 0, -2]⟩, ⟨[-2, 0, 4, 0, -2]⟩, ⟨[2, 2, -2, -2]⟩⟩,
    ⟨⟨[-4, -8, 2, 8, 0, -2]⟩, ⟨[2, 0, -4, 0, 2]⟩, ⟨[-2, -2, 2, 2]⟩⟩,
    ⟨⟨[-4, -6, 2, 8, 0, -2]⟩, ⟨[-2]⟩, ⟨[-2, -4, -2, 2, 2]⟩⟩,
    ⟨⟨[-4, -6, 2, 8, 0, -2]⟩, ⟨[2]⟩, ⟨[2, 4, 2, -2, -2]⟩⟩,
    ⟨⟨[-4, -4, 2, 2]⟩, ⟨[-4, -4, 6, 6, -2, -2]⟩, ⟨[0, -2, 0, 2]⟩⟩,
    ⟨⟨[-4, -4, 2, 2]⟩, ⟨[4, 4, -6, -6, 2, 2]⟩, ⟨[0, 2, 0, -2]⟩⟩,
    ⟨⟨[-4, -4, 2, 6, 0, -2]⟩, ⟨[0, -4, -4, 2, 2]⟩, ⟨[4, 2, -2, -2]⟩⟩,
    ⟨⟨[-4, -4, 2, 6, 0, -2]⟩, ⟨[0, 4, 4, -2, -2]⟩, ⟨[-4, -2, 2, 2]⟩⟩,
    ⟨⟨[-4, -4, 6, 6, -2, -2]⟩, ⟨[0, -2, 0, 2]⟩, ⟨[-4, -4, 2, 2]⟩⟩,
    ⟨⟨[-4, -4, 6, 6, -2, -2]⟩, ⟨[0, 2, 0, -2]⟩, ⟨[4, 4, -2, -2]⟩⟩,
    ⟨⟨[-4, -2, 2, 2]⟩, ⟨[-4, -4, 2, 6, 0, -2]⟩, ⟨[0, 4, 4, -2, -2]⟩⟩,
    ⟨⟨[-4, -2, 2, 2]⟩, ⟨[4, 4, -2, -6, 0, 2]⟩, ⟨[0, -4, -4, 2, 2]⟩⟩,
    ⟨⟨[-2, -4, -2, 2, 2]⟩, ⟨[-4, -6, 2, 8, 0, -2]⟩, ⟨[-2]⟩⟩,
    ⟨⟨[-2, -4, -2, 2, 2]⟩, ⟨[4, 6, -2, -8, 0, 2]⟩, ⟨[2]⟩⟩,
    ⟨⟨[-2, -2, 2, 2]⟩, ⟨[-4, -8, 2, 8, 0, -2]⟩, ⟨[2, 0, -4, 0, 2]⟩⟩,
    ⟨⟨[-2, -2, 2, 2]⟩, ⟨[4, 8, -2, -8, 0, 2]⟩, ⟨[-2, 0, 4, 0, -2]⟩⟩,
    ⟨⟨[-2]⟩, ⟨[-2, -4, -2, 2, 2]⟩, ⟨[-4, -6, 2, 8, 0, -2]⟩⟩,
    ⟨⟨[-2]⟩, ⟨[2, 4, 2, -2, -2]⟩, ⟨[4, 6, -2, -8, 0, 2]⟩⟩,
    ⟨⟨[-2, 0, 2]⟩, ⟨[-6, -4, 6, 6, -2, -2]⟩, ⟨[0, -2]⟩⟩,
    ⟨⟨[-2, 0, 2]⟩, ⟨[6, 4, -6, -6, 2, 2]⟩, ⟨[0, 2]⟩⟩,
    ⟨⟨[-2, 0, 4, 0, -2]⟩, ⟨[-2, -2, 2, 2]⟩, ⟨[4, 8, -2, -8, 0, 2]⟩⟩,
    ⟨⟨[-2, 0, 4, 0, -2]⟩, ⟨[2, 2, -2, -2]⟩, ⟨[-4, -8, 2, 8, 0, -2]⟩⟩,
    ⟨⟨[0, -4, -4, 2, 2]⟩, ⟨[-4, -2, 2, 2]⟩, ⟨[4, 4, -2, -6, 0, 2]⟩⟩,
    ⟨⟨[0, -4, -4, 2, 2]⟩, ⟨[4, 2, -2, -2]⟩, ⟨[-4, -4, 2, 6, 0, -2]⟩⟩,
    ⟨⟨[0, -2]⟩, ⟨[-2, 0, 2]⟩, ⟨[-6, -4, 6, 6, -2, -2]⟩⟩,
    ⟨⟨[0, -2]⟩, ⟨[2, 0, -2]⟩, ⟨[6, 4, -6, -6, 2, 2]⟩⟩,
    ⟨⟨[0, -2, 0, 2]⟩, ⟨[-4, -4, 2, 2]⟩, ⟨[-4, -4, 6, 6, -2, -2]⟩⟩,
    ⟨⟨[0, -2, 0, 2]⟩, ⟨[4, 4, -2, -2]⟩, ⟨[4, 4, -6, -6, 2, 2]⟩⟩,
    ⟨⟨[0, 2, 0, -2]⟩, ⟨[-4, -4, 2, 2]⟩, ⟨[4, 4, -6, -6, 2, 2]⟩⟩,
    ⟨⟨[0, 2, 0, -2]⟩, ⟨[4, 4, -2, -2]⟩, ⟨[-4, -4, 6, 6, -2, -2]⟩⟩,
    ⟨⟨[0, 2]⟩, ⟨[-2, 0, 2]⟩, ⟨[6, 4, -6, -6, 2, 2]⟩⟩,
    ⟨⟨[0, 2]⟩, ⟨[2, 0, -2]⟩, ⟨[-6, -4, 6, 6, -2, -2]⟩⟩,
    ⟨⟨[0, 4, 4, -2, -2]⟩, ⟨[-4, -2, 2, 2]⟩, ⟨[-4, -4, 2, 6, 0, -2]⟩⟩,
    ⟨⟨[0, 4, 4, -2, -2]⟩, ⟨[4, 2, -2, -2]⟩, ⟨[4, 4, -2, -6, 0, 2]⟩⟩,
    ⟨⟨[2, 0, -4, 0, 2]⟩, ⟨[-2, -2, 2, 2]⟩, ⟨[-4, -8, 2, 8, 0, -2]⟩⟩,
    ⟨⟨[2, 0, -4, 0, 2]⟩, ⟨[2, 2, -2, -2]⟩, ⟨[4, 8, -2, -8, 0, 2]⟩⟩,
    ⟨⟨[2, 0, -2]⟩, ⟨[-6, -4, 6, 6, -2, -2]⟩, ⟨[0, 2]⟩⟩,
    ⟨⟨[2, 0, -2]⟩, ⟨[6, 4, -6, -6, 2, 2]⟩, ⟨[0, -2]⟩⟩,
    ⟨⟨[2]⟩, ⟨[-2, -4, -2, 2, 2]⟩, ⟨[4, 6, -2, -8, 0, 2]⟩⟩,
    ⟨⟨[2]⟩, ⟨[2, 4, 2, -2, -2]⟩, ⟨[-4, -6, 2, 8, 0, -2]⟩⟩,
    ⟨⟨[2, 2, -2, -2]⟩, ⟨[-4, -8, 2, 8, 0, -2]⟩, ⟨[-2, 0, 4, 0, -2]⟩⟩,
    ⟨⟨[2, 2, -2, -2]⟩, ⟨[4, 8, -2, -8, 0, 2]⟩, ⟨[2, 0, -4, 0, 2]⟩⟩,
    ⟨⟨[2, 4, 2, -2, -2]⟩, ⟨[-4, -6, 2, 8, 0, -2]⟩, ⟨[2]⟩⟩,
    ⟨⟨[2, 4, 2, -2, -2]⟩, ⟨[4, 6, -2, -8, 0, 2]⟩, ⟨[-2]⟩⟩,
    ⟨⟨[4, 2, -2, -2]⟩, ⟨[-4, -4, 2, 6, 0, -2]⟩, ⟨[0, -4, -4, 2, 2]⟩⟩,
    ⟨⟨[4, 2, -2, -2]⟩, ⟨[4, 4, -2, -6, 0, 2]⟩, ⟨[0, 4, 4, -2, -2]⟩⟩,
    ⟨⟨[4, 4, -6, -6, 2, 2]⟩, ⟨[0, -2, 0, 2]⟩, ⟨[4, 4, -2, -2]⟩⟩,
    ⟨⟨[4, 4, -6, -6, 2, 2]⟩, ⟨[0, 2, 0, -2]⟩, ⟨[-4, -4, 2, 2]⟩⟩,
    ⟨⟨[4, 4, -2, -6, 0, 2]⟩, ⟨[0, -4, -4, 2, 2]⟩, ⟨[-4, -2, 2, 2]⟩⟩,
    ⟨⟨[4, 4, -2, -6, 0, 2]⟩, ⟨[0, 4, 4, -2, -2]⟩, ⟨[4, 2, -2, -2]⟩⟩,
    ⟨⟨[4, 4, -2, -2]⟩, ⟨[-4, -4, 6, 6, -2, -2]⟩, ⟨[0, 2, 0, -2]⟩⟩,
    ⟨⟨[4, 4, -2, -2]⟩, ⟨[4, 4, -6, -6, 2, 2]⟩, ⟨[0, -2, 0, 2]⟩⟩,
    ⟨⟨[4, 6, -2, -8, 0, 2]⟩, ⟨[-2]⟩, ⟨[2, 4, 2, -2, -2]⟩⟩,
    ⟨⟨[4, 6, -2, -8, 0, 2]⟩, ⟨[2]⟩, ⟨[-2, -4, -2, 2, 2]⟩⟩,
    ⟨⟨[4, 8, -2, -8, 0, 2]⟩, ⟨[-2, 0, 4, 0, -2]⟩, ⟨[-2, -2, 2, 2]⟩⟩,
    ⟨⟨[4, 8, -2, -8, 0, 2]⟩, ⟨[2, 0, -4, 0, 2]⟩, ⟨[2, 2, -2, -2]⟩⟩,
    ⟨⟨[6, 4, -6, -6, 2, 2]⟩, ⟨[0, -2]⟩, ⟨[2, 0, -2]⟩⟩,
    ⟨⟨[6, 4, -6, -6, 2, 2]⟩, ⟨[0, 2]⟩, ⟨[-2, 0, 2]⟩⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-6, -4, 6, 6, -2, -2]⟩, ⟨[0, -2]⟩, ⟨[-2, 0, 2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [-6, -4, 6, 6, -2, -2] θ, polyEval [0, -2] θ, polyEval [-2, 0, 2] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-6, -4, 6, 6, -2, -2]⟩, ⟨[0, 2]⟩, ⟨[2, 0, -2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [-6, -4, 6, 6, -2, -2] θ, polyEval [0, 2] θ, polyEval [2, 0, -2] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-4, -8, 2, 8, 0, -2]⟩, ⟨[-2, 0, 4, 0, -2]⟩, ⟨[2, 2,
    -2, -2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-4, -8, 2, 8, 0, -2] θ, polyEval [-2, 0, 4, 0, -2]
    θ, polyEval [2, 2, -2, -2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-4, -8, 2, 8, 0, -2]⟩, ⟨[2, 0, -4, 0, 2]⟩, ⟨[-2, -2,
    2, 2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-4, -8, 2, 8, 0, -2] θ, polyEval [2, 0, -4, 0, 2] θ,
    polyEval [-2, -2, 2, 2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-4, -6, 2, 8, 0, -2]⟩, ⟨[-2]⟩, ⟨[-2, -4, -2, 2, 2]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [-4, -6, 2, 8, 0, -2] θ, polyEval [-2] θ, polyEval [-2, -4, -2,
    2, 2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-4, -6, 2, 8, 0, -2]⟩, ⟨[2]⟩, ⟨[2, 4, 2, -2, -2]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [-4, -6, 2, 8, 0, -2] θ, polyEval [2] θ, polyEval [2, 4, 2, -2,
    -2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-4, -4, 2, 2]⟩, ⟨[-4, -4, 6, 6, -2, -2]⟩, ⟨[0, -2, 0,
    2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-4, -4, 2, 2] θ, polyEval [-4, -4, 6, 6, -2, -2] θ,
    polyEval [0, -2, 0, 2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-4, -4, 2, 2]⟩, ⟨[4, 4, -6, -6, 2, 2]⟩, ⟨[0, 2, 0,
    -2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-4, -4, 2, 2] θ, polyEval [4, 4, -6, -6, 2, 2] θ,
    polyEval [0, 2, 0, -2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-4, -4, 2, 6, 0, -2]⟩, ⟨[0, -4, -4, 2, 2]⟩, ⟨[4, 2,
    -2, -2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-4, -4, 2, 6, 0, -2] θ, polyEval [0, -4, -4, 2, 2]
    θ, polyEval [4, 2, -2, -2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt9 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-4, -4, 2, 6, 0, -2]⟩, ⟨[0, 4, 4, -2, -2]⟩, ⟨[-4, -2,
    2, 2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-4, -4, 2, 6, 0, -2] θ, polyEval [0, 4, 4, -2, -2] θ,
    polyEval [-4, -2, 2, 2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt10 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-4, -4, 6, 6, -2, -2]⟩, ⟨[0, -2, 0, 2]⟩, ⟨[-4, -4, 2,
    2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-4, -4, 6, 6, -2, -2] θ, polyEval [0, -2, 0, 2] θ,
    polyEval [-4, -4, 2, 2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt11 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-4, -4, 6, 6, -2, -2]⟩, ⟨[0, 2, 0, -2]⟩, ⟨[4, 4, -2,
    -2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-4, -4, 6, 6, -2, -2] θ, polyEval [0, 2, 0, -2] θ,
    polyEval [4, 4, -2, -2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt12 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-4, -2, 2, 2]⟩, ⟨[-4, -4, 2, 6, 0, -2]⟩, ⟨[0, 4, 4,
    -2, -2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-4, -2, 2, 2] θ, polyEval [-4, -4, 2, 6, 0, -2] θ,
    polyEval [0, 4, 4, -2, -2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt13 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-4, -2, 2, 2]⟩, ⟨[4, 4, -2, -6, 0, 2]⟩, ⟨[0, -4, -4,
    2, 2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-4, -2, 2, 2] θ, polyEval [4, 4, -2, -6, 0, 2] θ,
    polyEval [0, -4, -4, 2, 2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt14 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-2, -4, -2, 2, 2]⟩, ⟨[-4, -6, 2, 8, 0, -2]⟩, ⟨[-2]⟩⟩
    : V3 (ZTheta root)) = ![polyEval [-2, -4, -2, 2, 2] θ, polyEval [-4, -6, 2, 8, 0, -2] θ,
    polyEval [-2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt15 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-2, -4, -2, 2, 2]⟩, ⟨[4, 6, -2, -8, 0, 2]⟩, ⟨[2]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [-2, -4, -2, 2, 2] θ, polyEval [4, 6, -2, -8, 0, 2] θ, polyEval
    [2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt16 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-2, -2, 2, 2]⟩, ⟨[-4, -8, 2, 8, 0, -2]⟩, ⟨[2, 0, -4,
    0, 2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-2, -2, 2, 2] θ, polyEval [-4, -8, 2, 8, 0, -2] θ,
    polyEval [2, 0, -4, 0, 2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt17 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-2, -2, 2, 2]⟩, ⟨[4, 8, -2, -8, 0, 2]⟩, ⟨[-2, 0, 4,
    0, -2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-2, -2, 2, 2] θ, polyEval [4, 8, -2, -8, 0, 2] θ,
    polyEval [-2, 0, 4, 0, -2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt18 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-2]⟩, ⟨[-2, -4, -2, 2, 2]⟩, ⟨[-4, -6, 2, 8, 0, -2]⟩⟩
    : V3 (ZTheta root)) = ![polyEval [-2] θ, polyEval [-2, -4, -2, 2, 2] θ, polyEval [-4, -6, 2, 8,
    0, -2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt19 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-2]⟩, ⟨[2, 4, 2, -2, -2]⟩, ⟨[4, 6, -2, -8, 0, 2]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [-2] θ, polyEval [2, 4, 2, -2, -2] θ, polyEval [4, 6, -2, -8, 0,
    2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt20 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-2, 0, 2]⟩, ⟨[-6, -4, 6, 6, -2, -2]⟩, ⟨[0, -2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [-2, 0, 2] θ, polyEval [-6, -4, 6, 6, -2, -2] θ, polyEval [0, -2] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt21 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-2, 0, 2]⟩, ⟨[6, 4, -6, -6, 2, 2]⟩, ⟨[0, 2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [-2, 0, 2] θ, polyEval [6, 4, -6, -6, 2, 2] θ, polyEval [0, 2] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt22 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-2, 0, 4, 0, -2]⟩, ⟨[-2, -2, 2, 2]⟩, ⟨[4, 8, -2, -8,
    0, 2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-2, 0, 4, 0, -2] θ, polyEval [-2, -2, 2, 2] θ,
    polyEval [4, 8, -2, -8, 0, 2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt23 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[-2, 0, 4, 0, -2]⟩, ⟨[2, 2, -2, -2]⟩, ⟨[-4, -8, 2, 8,
    0, -2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-2, 0, 4, 0, -2] θ, polyEval [2, 2, -2, -2] θ,
    polyEval [-4, -8, 2, 8, 0, -2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt24 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[0, -4, -4, 2, 2]⟩, ⟨[-4, -2, 2, 2]⟩, ⟨[4, 4, -2, -6,
    0, 2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, -4, -4, 2, 2] θ, polyEval [-4, -2, 2, 2] θ,
    polyEval [4, 4, -2, -6, 0, 2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt25 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[0, -4, -4, 2, 2]⟩, ⟨[4, 2, -2, -2]⟩, ⟨[-4, -4, 2, 6,
    0, -2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, -4, -4, 2, 2] θ, polyEval [4, 2, -2, -2] θ,
    polyEval [-4, -4, 2, 6, 0, -2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt26 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[0, -2]⟩, ⟨[-2, 0, 2]⟩, ⟨[-6, -4, 6, 6, -2, -2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0, -2] θ, polyEval [-2, 0, 2] θ, polyEval [-6, -4, 6, 6, -2, -2] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt27 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[0, -2]⟩, ⟨[2, 0, -2]⟩, ⟨[6, 4, -6, -6, 2, 2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0, -2] θ, polyEval [2, 0, -2] θ, polyEval [6, 4, -6, -6, 2, 2] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt28 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[0, -2, 0, 2]⟩, ⟨[-4, -4, 2, 2]⟩, ⟨[-4, -4, 6, 6, -2,
    -2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, -2, 0, 2] θ, polyEval [-4, -4, 2, 2] θ, polyEval [-4,
    -4, 6, 6, -2, -2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt29 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[0, -2, 0, 2]⟩, ⟨[4, 4, -2, -2]⟩, ⟨[4, 4, -6, -6, 2,
    2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, -2, 0, 2] θ, polyEval [4, 4, -2, -2] θ, polyEval [4,
    4, -6, -6, 2, 2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt30 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[0, 2, 0, -2]⟩, ⟨[-4, -4, 2, 2]⟩, ⟨[4, 4, -6, -6, 2,
    2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 2, 0, -2] θ, polyEval [-4, -4, 2, 2] θ, polyEval [4,
    4, -6, -6, 2, 2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt31 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[0, 2, 0, -2]⟩, ⟨[4, 4, -2, -2]⟩, ⟨[-4, -4, 6, 6, -2,
    -2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 2, 0, -2] θ, polyEval [4, 4, -2, -2] θ, polyEval [-4,
    -4, 6, 6, -2, -2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt32 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[0, 2]⟩, ⟨[-2, 0, 2]⟩, ⟨[6, 4, -6, -6, 2, 2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0, 2] θ, polyEval [-2, 0, 2] θ, polyEval [6, 4, -6, -6, 2, 2] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt33 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[0, 2]⟩, ⟨[2, 0, -2]⟩, ⟨[-6, -4, 6, 6, -2, -2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0, 2] θ, polyEval [2, 0, -2] θ, polyEval [-6, -4, 6, 6, -2, -2] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt34 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[0, 4, 4, -2, -2]⟩, ⟨[-4, -2, 2, 2]⟩, ⟨[-4, -4, 2, 6,
    0, -2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 4, 4, -2, -2] θ, polyEval [-4, -2, 2, 2] θ,
    polyEval [-4, -4, 2, 6, 0, -2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt35 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[0, 4, 4, -2, -2]⟩, ⟨[4, 2, -2, -2]⟩, ⟨[4, 4, -2, -6,
    0, 2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 4, 4, -2, -2] θ, polyEval [4, 2, -2, -2] θ,
    polyEval [4, 4, -2, -6, 0, 2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt36 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[2, 0, -4, 0, 2]⟩, ⟨[-2, -2, 2, 2]⟩, ⟨[-4, -8, 2, 8,
    0, -2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [2, 0, -4, 0, 2] θ, polyEval [-2, -2, 2, 2] θ,
    polyEval [-4, -8, 2, 8, 0, -2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt37 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[2, 0, -4, 0, 2]⟩, ⟨[2, 2, -2, -2]⟩, ⟨[4, 8, -2, -8,
    0, 2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [2, 0, -4, 0, 2] θ, polyEval [2, 2, -2, -2] θ, polyEval
    [4, 8, -2, -8, 0, 2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt38 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[2, 0, -2]⟩, ⟨[-6, -4, 6, 6, -2, -2]⟩, ⟨[0, 2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [2, 0, -2] θ, polyEval [-6, -4, 6, 6, -2, -2] θ, polyEval [0, 2] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt39 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[2, 0, -2]⟩, ⟨[6, 4, -6, -6, 2, 2]⟩, ⟨[0, -2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [2, 0, -2] θ, polyEval [6, 4, -6, -6, 2, 2] θ, polyEval [0, -2] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt40 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[2]⟩, ⟨[-2, -4, -2, 2, 2]⟩, ⟨[4, 6, -2, -8, 0, 2]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [2] θ, polyEval [-2, -4, -2, 2, 2] θ, polyEval [4, 6, -2, -8, 0,
    2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt41 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[2]⟩, ⟨[2, 4, 2, -2, -2]⟩, ⟨[-4, -6, 2, 8, 0, -2]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [2] θ, polyEval [2, 4, 2, -2, -2] θ, polyEval [-4, -6, 2, 8, 0,
    -2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt42 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[2, 2, -2, -2]⟩, ⟨[-4, -8, 2, 8, 0, -2]⟩, ⟨[-2, 0, 4,
    0, -2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [2, 2, -2, -2] θ, polyEval [-4, -8, 2, 8, 0, -2] θ,
    polyEval [-2, 0, 4, 0, -2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt43 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[2, 2, -2, -2]⟩, ⟨[4, 8, -2, -8, 0, 2]⟩, ⟨[2, 0, -4,
    0, 2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [2, 2, -2, -2] θ, polyEval [4, 8, -2, -8, 0, 2] θ,
    polyEval [2, 0, -4, 0, 2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt44 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[2, 4, 2, -2, -2]⟩, ⟨[-4, -6, 2, 8, 0, -2]⟩, ⟨[2]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [2, 4, 2, -2, -2] θ, polyEval [-4, -6, 2, 8, 0, -2] θ, polyEval
    [2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt45 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[2, 4, 2, -2, -2]⟩, ⟨[4, 6, -2, -8, 0, 2]⟩, ⟨[-2]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [2, 4, 2, -2, -2] θ, polyEval [4, 6, -2, -8, 0, 2] θ, polyEval
    [-2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt46 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[4, 2, -2, -2]⟩, ⟨[-4, -4, 2, 6, 0, -2]⟩, ⟨[0, -4, -4,
    2, 2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [4, 2, -2, -2] θ, polyEval [-4, -4, 2, 6, 0, -2] θ,
    polyEval [0, -4, -4, 2, 2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt47 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[4, 2, -2, -2]⟩, ⟨[4, 4, -2, -6, 0, 2]⟩, ⟨[0, 4, 4,
    -2, -2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [4, 2, -2, -2] θ, polyEval [4, 4, -2, -6, 0, 2] θ,
    polyEval [0, 4, 4, -2, -2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt48 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[4, 4, -6, -6, 2, 2]⟩, ⟨[0, -2, 0, 2]⟩, ⟨[4, 4, -2,
    -2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [4, 4, -6, -6, 2, 2] θ, polyEval [0, -2, 0, 2] θ,
    polyEval [4, 4, -2, -2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt49 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[4, 4, -6, -6, 2, 2]⟩, ⟨[0, 2, 0, -2]⟩, ⟨[-4, -4, 2,
    2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [4, 4, -6, -6, 2, 2] θ, polyEval [0, 2, 0, -2] θ, polyEval
    [-4, -4, 2, 2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt50 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[4, 4, -2, -6, 0, 2]⟩, ⟨[0, -4, -4, 2, 2]⟩, ⟨[-4, -2,
    2, 2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [4, 4, -2, -6, 0, 2] θ, polyEval [0, -4, -4, 2, 2] θ,
    polyEval [-4, -2, 2, 2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt51 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[4, 4, -2, -6, 0, 2]⟩, ⟨[0, 4, 4, -2, -2]⟩, ⟨[4, 2,
    -2, -2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [4, 4, -2, -6, 0, 2] θ, polyEval [0, 4, 4, -2, -2] θ,
    polyEval [4, 2, -2, -2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt52 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[4, 4, -2, -2]⟩, ⟨[-4, -4, 6, 6, -2, -2]⟩, ⟨[0, 2, 0,
    -2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [4, 4, -2, -2] θ, polyEval [-4, -4, 6, 6, -2, -2] θ,
    polyEval [0, 2, 0, -2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt53 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[4, 4, -2, -2]⟩, ⟨[4, 4, -6, -6, 2, 2]⟩, ⟨[0, -2, 0,
    2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [4, 4, -2, -2] θ, polyEval [4, 4, -6, -6, 2, 2] θ,
    polyEval [0, -2, 0, 2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt54 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[4, 6, -2, -8, 0, 2]⟩, ⟨[-2]⟩, ⟨[2, 4, 2, -2, -2]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [4, 6, -2, -8, 0, 2] θ, polyEval [-2] θ, polyEval [2, 4, 2, -2,
    -2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt55 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[4, 6, -2, -8, 0, 2]⟩, ⟨[2]⟩, ⟨[-2, -4, -2, 2, 2]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [4, 6, -2, -8, 0, 2] θ, polyEval [2] θ, polyEval [-2, -4, -2, 2,
    2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt56 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[4, 8, -2, -8, 0, 2]⟩, ⟨[-2, 0, 4, 0, -2]⟩, ⟨[-2, -2,
    2, 2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [4, 8, -2, -8, 0, 2] θ, polyEval [-2, 0, 4, 0, -2] θ,
    polyEval [-2, -2, 2, 2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt57 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[4, 8, -2, -8, 0, 2]⟩, ⟨[2, 0, -4, 0, 2]⟩, ⟨[2, 2, -2,
    -2]⟩⟩ : V3 (ZTheta root)) = ![polyEval [4, 8, -2, -8, 0, 2] θ, polyEval [2, 0, -4, 0, 2] θ,
    polyEval [2, 2, -2, -2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt58 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[6, 4, -6, -6, 2, 2]⟩, ⟨[0, -2]⟩, ⟨[2, 0, -2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [6, 4, -6, -6, 2, 2] θ, polyEval [0, -2] θ, polyEval [2, 0, -2] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem pt59 : (1 / 1 : ℝ) • Exact.reV (⟨⟨[6, 4, -6, -6, 2, 2]⟩, ⟨[0, 2]⟩, ⟨[-2, 0, 2]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [6, 4, -6, -6, 2, 2] θ, polyEval [0, 2] θ, polyEval [-2, 0, 2] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 1) (by norm_num) (by decide +kernel)

theorem eq_smul : Archimedean.SnubDodecahedronLaevo.polyhedron = (Polyhedron.ofPoints points).smul (1 / 1) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17, pt18, pt19, pt20, pt21, pt22, pt23, pt24,
    pt25, pt26, pt27, pt28, pt29, pt30, pt31, pt32, pt33, pt34, pt35, pt36, pt37, pt38, pt39, pt40,
    pt41, pt42, pt43, pt44, pt45, pt46, pt47, pt48, pt49, pt50, pt51, pt52, pt53, pt54, pt55, pt56,
    pt57, pt58, pt59]

end Nieuwland.Polyhedra.ArchimedeanSnubDodecahedronLaevoDim

namespace Nieuwland.Polyhedra

/-- **The fixture `archimedean/snub-dodecahedron-laevo` is full-dimensional.** -/
theorem archimedeanSnubDodecahedronLaevo_fullDim : Archimedean.SnubDodecahedronLaevo.polyhedron.FullDim := by
  rw [ArchimedeanSnubDodecahedronLaevoDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk ArchimedeanSnubDodecahedronLaevoDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
