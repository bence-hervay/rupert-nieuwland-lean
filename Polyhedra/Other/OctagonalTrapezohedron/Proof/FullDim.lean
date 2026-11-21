import Polyhedra.Other.OctagonalTrapezohedron.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `trapezohedron/octagonal-trapezohedron` is full-dimensional

The points of `Other.OctagonalTrapezohedron.polyhedron` times `119` as exact values in `ZTheta root`,
exported by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`,
checked by the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`),
and scaled back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Other.OctagonalTrapezohedron.polyhedron`.
-/

namespace Nieuwland.Polyhedra.TrapezohedronOctagonalTrapezohedronDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Other.OctagonalTrapezohedron.theta

/-- The root `θ`, with `α = 1 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[-2, 0, 40, 0, -248, 0, 480, 0, 1], 9/32, 3/8,
    1, [-2, 0, 40, 0, -248, 0, 480, 0, 1],
    512, 160, 163, 192, 8,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    4239480033799044147932876115989362364374284040546042731759346053161473163090168070279857375365986101404915963380841909102308559278892376017047764036926550,
    4239480033799044147932876115989362364374284040546042731759346053161473163090168070279857375365986101404915963380841909102308559278892376017047764036926551,
    by decide +kernel⟩

theorem root_α : root.α = (1 : ℕ) * θ := rfl

theorem root_n : root.n = 8 := rfl

/-- The points of `Other.OctagonalTrapezohedron.polyhedron` times `119`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[0]⟩, ⟨[0]⟩, ⟨[-119]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0]⟩, ⟨[119]⟩⟩,
    ⟨⟨[0, 119]⟩, ⟨[0, 1113, 0, -14000, 0, 33607, 0, 70]⟩, ⟨[-141, 0, 2612, 0, -12488, 0, -26]⟩⟩,
    ⟨⟨[0, 1670, 0, -22467, 0, 66745, 0, 139]⟩, ⟨[0, 1670, 0, -22467, 0, 66745, 0, 139]⟩, ⟨[141, 0, -2612, 0, 12488, 0, 26]⟩⟩,
    ⟨⟨[0, 1113, 0, -14000, 0, 33607, 0, 70]⟩, ⟨[0, 119]⟩, ⟨[-141, 0, 2612, 0, -12488, 0, -26]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0, -1290, 0, 21058, 0, -68670, 0, -143]⟩, ⟨[141, 0, -2612, 0, 12488, 0, 26]⟩⟩,
    ⟨⟨[0, -1113, 0, 14000, 0, -33607, 0, -70]⟩, ⟨[0, 119]⟩, ⟨[-141, 0, 2612, 0, -12488, 0, -26]⟩⟩,
    ⟨⟨[0, -1670, 0, 22467, 0, -66745, 0, -139]⟩, ⟨[0, 1670, 0, -22467, 0, 66745, 0, 139]⟩, ⟨[141, 0, -2612, 0, 12488, 0, 26]⟩⟩,
    ⟨⟨[0, -119]⟩, ⟨[0, 1113, 0, -14000, 0, 33607, 0, 70]⟩, ⟨[-141, 0, 2612, 0, -12488, 0, -26]⟩⟩,
    ⟨⟨[0, 1290, 0, -21058, 0, 68670, 0, 143]⟩, ⟨[0]⟩, ⟨[141, 0, -2612, 0, 12488, 0, 26]⟩⟩,
    ⟨⟨[0, -119]⟩, ⟨[0, -1113, 0, 14000, 0, -33607, 0, -70]⟩, ⟨[-141, 0, 2612, 0, -12488, 0, -26]⟩⟩,
    ⟨⟨[0, -1670, 0, 22467, 0, -66745, 0, -139]⟩, ⟨[0, -1670, 0, 22467, 0, -66745, 0, -139]⟩, ⟨[141, 0, -2612, 0, 12488, 0, 26]⟩⟩,
    ⟨⟨[0, -1113, 0, 14000, 0, -33607, 0, -70]⟩, ⟨[0, -119]⟩, ⟨[-141, 0, 2612, 0, -12488, 0, -26]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0, 1290, 0, -21058, 0, 68670, 0, 143]⟩, ⟨[141, 0, -2612, 0, 12488, 0, 26]⟩⟩,
    ⟨⟨[0, 1113, 0, -14000, 0, 33607, 0, 70]⟩, ⟨[0, -119]⟩, ⟨[-141, 0, 2612, 0, -12488, 0, -26]⟩⟩,
    ⟨⟨[0, 1670, 0, -22467, 0, 66745, 0, 139]⟩, ⟨[0, -1670, 0, 22467, 0, -66745, 0, -139]⟩, ⟨[141, 0, -2612, 0, 12488, 0, 26]⟩⟩,
    ⟨⟨[0, 119]⟩, ⟨[0, -1113, 0, 14000, 0, -33607, 0, -70]⟩, ⟨[-141, 0, 2612, 0, -12488, 0, -26]⟩⟩,
    ⟨⟨[0, -1290, 0, 21058, 0, -68670, 0, -143]⟩, ⟨[0]⟩, ⟨[141, 0, -2612, 0, 12488, 0, 26]⟩⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 119 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0]⟩, ⟨[-119]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0] θ, polyEval [0] θ, polyEval [-1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 119) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 119 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0]⟩, ⟨[119]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0] θ, polyEval [0] θ, polyEval [1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 119) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 119 : ℝ) • Exact.reV (⟨⟨[0, 119]⟩, ⟨[0, 1113, 0, -14000, 0, 33607, 0, 70]⟩,
    ⟨[-141, 0, 2612, 0, -12488, 0, -26]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 1] θ, polyEval [0,
    159/17, 0, -2000/17, 0, 4801/17, 0, 10/17] θ, polyEval [-141/119, 0, 2612/119, 0, -1784/17, 0,
    -26/119] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 119) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 119 : ℝ) • Exact.reV (⟨⟨[0, 1670, 0, -22467, 0, 66745, 0, 139]⟩, ⟨[0, 1670,
    0, -22467, 0, 66745, 0, 139]⟩, ⟨[141, 0, -2612, 0, 12488, 0, 26]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1670/119, 0, -22467/119, 0, 9535/17, 0, 139/119] θ, polyEval [0, 1670/119, 0,
    -22467/119, 0, 9535/17, 0, 139/119] θ, polyEval [141/119, 0, -2612/119, 0, 1784/17, 0, 26/119]
    θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 119) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 119 : ℝ) • Exact.reV (⟨⟨[0, 1113, 0, -14000, 0, 33607, 0, 70]⟩, ⟨[0, 119]⟩,
    ⟨[-141, 0, 2612, 0, -12488, 0, -26]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 159/17, 0, -2000/17,
    0, 4801/17, 0, 10/17] θ, polyEval [0, 1] θ, polyEval [-141/119, 0, 2612/119, 0, -1784/17, 0,
    -26/119] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 119) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 119 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0, -1290, 0, 21058, 0, -68670, 0, -143]⟩,
    ⟨[141, 0, -2612, 0, 12488, 0, 26]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0] θ, polyEval [0,
    -1290/119, 0, 21058/119, 0, -9810/17, 0, -143/119] θ, polyEval [141/119, 0, -2612/119, 0,
    1784/17, 0, 26/119] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 119) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 119 : ℝ) • Exact.reV (⟨⟨[0, -1113, 0, 14000, 0, -33607, 0, -70]⟩, ⟨[0, 119]⟩,
    ⟨[-141, 0, 2612, 0, -12488, 0, -26]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, -159/17, 0, 2000/17,
    0, -4801/17, 0, -10/17] θ, polyEval [0, 1] θ, polyEval [-141/119, 0, 2612/119, 0, -1784/17, 0,
    -26/119] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 119) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 119 : ℝ) • Exact.reV (⟨⟨[0, -1670, 0, 22467, 0, -66745, 0, -139]⟩, ⟨[0, 1670,
    0, -22467, 0, 66745, 0, 139]⟩, ⟨[141, 0, -2612, 0, 12488, 0, 26]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, -1670/119, 0, 22467/119, 0, -9535/17, 0, -139/119] θ, polyEval [0, 1670/119, 0,
    -22467/119, 0, 9535/17, 0, 139/119] θ, polyEval [141/119, 0, -2612/119, 0, 1784/17, 0, 26/119]
    θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 119) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 119 : ℝ) • Exact.reV (⟨⟨[0, -119]⟩, ⟨[0, 1113, 0, -14000, 0, 33607, 0, 70]⟩,
    ⟨[-141, 0, 2612, 0, -12488, 0, -26]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, -1] θ, polyEval [0,
    159/17, 0, -2000/17, 0, 4801/17, 0, 10/17] θ, polyEval [-141/119, 0, 2612/119, 0, -1784/17, 0,
    -26/119] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 119) (by norm_num) (by decide +kernel)

theorem pt9 : (1 / 119 : ℝ) • Exact.reV (⟨⟨[0, 1290, 0, -21058, 0, 68670, 0, 143]⟩, ⟨[0]⟩,
    ⟨[141, 0, -2612, 0, 12488, 0, 26]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 1290/119, 0,
    -21058/119, 0, 9810/17, 0, 143/119] θ, polyEval [0] θ, polyEval [141/119, 0, -2612/119, 0,
    1784/17, 0, 26/119] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 119) (by norm_num) (by decide +kernel)

theorem pt10 : (1 / 119 : ℝ) • Exact.reV (⟨⟨[0, -119]⟩, ⟨[0, -1113, 0, 14000, 0, -33607, 0,
    -70]⟩, ⟨[-141, 0, 2612, 0, -12488, 0, -26]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, -1] θ,
    polyEval [0, -159/17, 0, 2000/17, 0, -4801/17, 0, -10/17] θ, polyEval [-141/119, 0, 2612/119, 0,
    -1784/17, 0, -26/119] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 119) (by norm_num) (by decide +kernel)

theorem pt11 : (1 / 119 : ℝ) • Exact.reV (⟨⟨[0, -1670, 0, 22467, 0, -66745, 0, -139]⟩, ⟨[0,
    -1670, 0, 22467, 0, -66745, 0, -139]⟩, ⟨[141, 0, -2612, 0, 12488, 0, 26]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, -1670/119, 0, 22467/119, 0, -9535/17, 0, -139/119] θ, polyEval [0, -1670/119, 0,
    22467/119, 0, -9535/17, 0, -139/119] θ, polyEval [141/119, 0, -2612/119, 0, 1784/17, 0, 26/119]
    θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 119) (by norm_num) (by decide +kernel)

theorem pt12 : (1 / 119 : ℝ) • Exact.reV (⟨⟨[0, -1113, 0, 14000, 0, -33607, 0, -70]⟩, ⟨[0,
    -119]⟩, ⟨[-141, 0, 2612, 0, -12488, 0, -26]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, -159/17, 0,
    2000/17, 0, -4801/17, 0, -10/17] θ, polyEval [0, -1] θ, polyEval [-141/119, 0, 2612/119, 0,
    -1784/17, 0, -26/119] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 119) (by norm_num) (by decide +kernel)

theorem pt13 : (1 / 119 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0, 1290, 0, -21058, 0, 68670, 0, 143]⟩,
    ⟨[141, 0, -2612, 0, 12488, 0, 26]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0] θ, polyEval [0,
    1290/119, 0, -21058/119, 0, 9810/17, 0, 143/119] θ, polyEval [141/119, 0, -2612/119, 0, 1784/17,
    0, 26/119] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 119) (by norm_num) (by decide +kernel)

theorem pt14 : (1 / 119 : ℝ) • Exact.reV (⟨⟨[0, 1113, 0, -14000, 0, 33607, 0, 70]⟩, ⟨[0, -119]⟩,
    ⟨[-141, 0, 2612, 0, -12488, 0, -26]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 159/17, 0, -2000/17,
    0, 4801/17, 0, 10/17] θ, polyEval [0, -1] θ, polyEval [-141/119, 0, 2612/119, 0, -1784/17, 0,
    -26/119] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 119) (by norm_num) (by decide +kernel)

theorem pt15 : (1 / 119 : ℝ) • Exact.reV (⟨⟨[0, 1670, 0, -22467, 0, 66745, 0, 139]⟩, ⟨[0, -1670,
    0, 22467, 0, -66745, 0, -139]⟩, ⟨[141, 0, -2612, 0, 12488, 0, 26]⟩⟩ : V3 (ZTheta root)) =
    ![polyEval [0, 1670/119, 0, -22467/119, 0, 9535/17, 0, 139/119] θ, polyEval [0, -1670/119, 0,
    22467/119, 0, -9535/17, 0, -139/119] θ, polyEval [141/119, 0, -2612/119, 0, 1784/17, 0, 26/119]
    θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 119) (by norm_num) (by decide +kernel)

theorem pt16 : (1 / 119 : ℝ) • Exact.reV (⟨⟨[0, 119]⟩, ⟨[0, -1113, 0, 14000, 0, -33607, 0,
    -70]⟩, ⟨[-141, 0, 2612, 0, -12488, 0, -26]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 1] θ, polyEval
    [0, -159/17, 0, 2000/17, 0, -4801/17, 0, -10/17] θ, polyEval [-141/119, 0, 2612/119, 0,
    -1784/17, 0, -26/119] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 119) (by norm_num) (by decide +kernel)

theorem pt17 : (1 / 119 : ℝ) • Exact.reV (⟨⟨[0, -1290, 0, 21058, 0, -68670, 0, -143]⟩, ⟨[0]⟩,
    ⟨[141, 0, -2612, 0, 12488, 0, 26]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, -1290/119, 0,
    21058/119, 0, -9810/17, 0, -143/119] θ, polyEval [0] θ, polyEval [141/119, 0, -2612/119, 0,
    1784/17, 0, 26/119] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 119) (by norm_num) (by decide +kernel)

theorem eq_smul : Other.OctagonalTrapezohedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 119) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17]

end Nieuwland.Polyhedra.TrapezohedronOctagonalTrapezohedronDim

namespace Nieuwland.Polyhedra

/-- **The fixture `trapezohedron/octagonal-trapezohedron` is full-dimensional.** -/
theorem trapezohedronOctagonalTrapezohedron_fullDim : Other.OctagonalTrapezohedron.polyhedron.FullDim := by
  rw [TrapezohedronOctagonalTrapezohedronDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk TrapezohedronOctagonalTrapezohedronDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
