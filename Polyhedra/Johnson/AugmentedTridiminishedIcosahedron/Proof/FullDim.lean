import Polyhedra.Johnson.AugmentedTridiminishedIcosahedron.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `johnson/augmented-tridiminished-icosahedron` is full-dimensional

The points of `Johnson.AugmentedTridiminishedIcosahedron.polyhedron` times `192` as exact values in
`ZTheta root`, exported by `code/lean-export dim`: three of their differences are linearly
independent (`spanOk`, checked by the kernel), so their polyhedron is full-dimensional
(`Polyhedron.fullDim_of_spanOk`), and scaled back (`eq_smul`, `Polyhedron.FullDim.smul`), so is
`Johnson.AugmentedTridiminishedIcosahedron.polyhedron`.
-/

namespace Nieuwland.Polyhedra.JohnsonAugmentedTridiminishedIcosahedronDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Johnson.AugmentedTridiminishedIcosahedron.theta

/-- The root `θ`, with `α = 6 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[-31/144, 19/18, -1/18, -2, 1], 1, 5/2,
    6, [-279, 228, -2, -12, 1],
    16, 163, 166, 240, 18,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    138107971343489268360830339820568314335564119590675246845190571762943077861008037125480534426596151677904671136179633738420701758776532512580171361653495423,
    138107971343489268360830339820568314335564119590675246845190571762943077861008037125480534426596151677904671136179633738420701758776532512580171361653495424,
    by decide +kernel⟩

theorem root_α : root.α = (6 : ℕ) * θ := rfl

theorem root_n : root.n = 4 := rfl

/-- The points of `Johnson.AugmentedTridiminishedIcosahedron.polyhedron` times `192`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[-129, 41, 9, -1]⟩, ⟨[96]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0]⟩, ⟨[-129, 41, 9, -1]⟩, ⟨[96]⟩⟩,
    ⟨⟨[96]⟩, ⟨[0]⟩, ⟨[-129, 41, 9, -1]⟩⟩,
    ⟨⟨[129, -41, -9, 1]⟩, ⟨[96]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0]⟩, ⟨[129, -41, -9, 1]⟩, ⟨[96]⟩⟩,
    ⟨⟨[96]⟩, ⟨[0]⟩, ⟨[129, -41, -9, 1]⟩⟩,
    ⟨⟨[129, -41, -9, 1]⟩, ⟨[-96]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0]⟩, ⟨[129, -41, -9, 1]⟩, ⟨[-96]⟩⟩,
    ⟨⟨[-96]⟩, ⟨[0]⟩, ⟨[129, -41, -9, 1]⟩⟩,
    ⟨⟨[129, -9, -9, 1]⟩, ⟨[129, -9, -9, 1]⟩, ⟨[129, -9, -9, 1]⟩⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 192 : ℝ) • Exact.reV (⟨⟨[-129, 41, 9, -1]⟩, ⟨[96]⟩, ⟨[0]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [-43/64, 41/32, 27/16, -9/8] θ, polyEval [1/2] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 192) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 192 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[-129, 41, 9, -1]⟩, ⟨[96]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [0] θ, polyEval [-43/64, 41/32, 27/16, -9/8] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 192) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 192 : ℝ) • Exact.reV (⟨⟨[96]⟩, ⟨[0]⟩, ⟨[-129, 41, 9, -1]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [1/2] θ, polyEval [0] θ, polyEval [-43/64, 41/32, 27/16, -9/8] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 192) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 192 : ℝ) • Exact.reV (⟨⟨[129, -41, -9, 1]⟩, ⟨[96]⟩, ⟨[0]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [43/64, -41/32, -27/16, 9/8] θ, polyEval [1/2] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 192) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 192 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[129, -41, -9, 1]⟩, ⟨[96]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [0] θ, polyEval [43/64, -41/32, -27/16, 9/8] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 192) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 192 : ℝ) • Exact.reV (⟨⟨[96]⟩, ⟨[0]⟩, ⟨[129, -41, -9, 1]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [1/2] θ, polyEval [0] θ, polyEval [43/64, -41/32, -27/16, 9/8] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 192) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 192 : ℝ) • Exact.reV (⟨⟨[129, -41, -9, 1]⟩, ⟨[-96]⟩, ⟨[0]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [43/64, -41/32, -27/16, 9/8] θ, polyEval [-1/2] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 192) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 192 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[129, -41, -9, 1]⟩, ⟨[-96]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [0] θ, polyEval [43/64, -41/32, -27/16, 9/8] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 192) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 192 : ℝ) • Exact.reV (⟨⟨[-96]⟩, ⟨[0]⟩, ⟨[129, -41, -9, 1]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [-1/2] θ, polyEval [0] θ, polyEval [43/64, -41/32, -27/16, 9/8] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 192) (by norm_num) (by decide +kernel)

theorem pt9 : (1 / 192 : ℝ) • Exact.reV (⟨⟨[129, -9, -9, 1]⟩, ⟨[129, -9, -9, 1]⟩, ⟨[129, -9, -9,
    1]⟩⟩ : V3 (ZTheta root)) = ![polyEval [43/64, -9/32, -27/16, 9/8] θ, polyEval [43/64, -9/32,
    -27/16, 9/8] θ, polyEval [43/64, -9/32, -27/16, 9/8] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 192) (by norm_num) (by decide +kernel)

theorem eq_smul : Johnson.AugmentedTridiminishedIcosahedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 192) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9]

end Nieuwland.Polyhedra.JohnsonAugmentedTridiminishedIcosahedronDim

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/augmented-tridiminished-icosahedron` is full-dimensional.** -/
theorem johnsonAugmentedTridiminishedIcosahedron_fullDim : Johnson.AugmentedTridiminishedIcosahedron.polyhedron.FullDim := by
  rw [JohnsonAugmentedTridiminishedIcosahedronDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk JohnsonAugmentedTridiminishedIcosahedronDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
