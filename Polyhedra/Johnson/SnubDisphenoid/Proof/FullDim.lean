import Polyhedra.Johnson.SnubDisphenoid.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `johnson/snub-disphenoid` is full-dimensional

The points of `Johnson.SnubDisphenoid.polyhedron` times `128` as exact values in `ZTheta root`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Johnson.SnubDisphenoid.polyhedron`.
-/

namespace Nieuwland.Polyhedra.JohnsonSnubDisphenoidDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Johnson.SnubDisphenoid.theta

/-- The root `θ`, with `α = 4 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[-1/128, 0, 1/8, 0, 11/8, 0, 1], 0, 3/8,
    4, [-32, 0, 32, 0, 22, 0, 1],
    16, 12, 15, 24, 8,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    11024519970955002483569072462987106140011165650039768879561214976616909146972378207623507660875952616997886835535035077327574939732464219438577037463967566,
    11024519970955002483569072462987106140011165650039768879561214976616909146972378207623507660875952616997886835535035077327574939732464219438577037463967567,
    by decide +kernel⟩

theorem root_α : root.α = (4 : ℕ) * θ := rfl

theorem root_n : root.n = 6 := rfl

/-- The points of `Johnson.SnubDisphenoid.polyhedron` times `128`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[64]⟩, ⟨[0]⟩, ⟨[0, -104, 0, -26, 0, -1]⟩⟩,
    ⟨⟨[-64]⟩, ⟨[0]⟩, ⟨[0, -104, 0, -26, 0, -1]⟩⟩,
    ⟨⟨[0]⟩, ⟨[64]⟩, ⟨[0, 104, 0, 26, 0, 1]⟩⟩,
    ⟨⟨[0]⟩, ⟨[-64]⟩, ⟨[0, 104, 0, 26, 0, 1]⟩⟩,
    ⟨⟨[32, 0, 72, 0, 4]⟩, ⟨[0]⟩, ⟨[0, 32]⟩⟩,
    ⟨⟨[-32, 0, -72, 0, -4]⟩, ⟨[0]⟩, ⟨[0, 32]⟩⟩,
    ⟨⟨[0]⟩, ⟨[32, 0, 72, 0, 4]⟩, ⟨[0, -32]⟩⟩,
    ⟨⟨[0]⟩, ⟨[-32, 0, -72, 0, -4]⟩, ⟨[0, -32]⟩⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 128 : ℝ) • Exact.reV (⟨⟨[64]⟩, ⟨[0]⟩, ⟨[0, -104, 0, -26, 0, -1]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [1/2] θ, polyEval [0] θ, polyEval [0, -13/4, 0, -13, 0, -8] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 128) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 128 : ℝ) • Exact.reV (⟨⟨[-64]⟩, ⟨[0]⟩, ⟨[0, -104, 0, -26, 0, -1]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [-1/2] θ, polyEval [0] θ, polyEval [0, -13/4, 0, -13, 0, -8] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 128) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 128 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[64]⟩, ⟨[0, 104, 0, 26, 0, 1]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [0] θ, polyEval [1/2] θ, polyEval [0, 13/4, 0, 13, 0, 8] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 128) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 128 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[-64]⟩, ⟨[0, 104, 0, 26, 0, 1]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [0] θ, polyEval [-1/2] θ, polyEval [0, 13/4, 0, 13, 0, 8] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 128) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 128 : ℝ) • Exact.reV (⟨⟨[32, 0, 72, 0, 4]⟩, ⟨[0]⟩, ⟨[0, 32]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [1/4, 0, 9, 0, 8] θ, polyEval [0] θ, polyEval [0, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 128) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 128 : ℝ) • Exact.reV (⟨⟨[-32, 0, -72, 0, -4]⟩, ⟨[0]⟩, ⟨[0, 32]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [-1/4, 0, -9, 0, -8] θ, polyEval [0] θ, polyEval [0, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 128) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 128 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[32, 0, 72, 0, 4]⟩, ⟨[0, -32]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [0] θ, polyEval [1/4, 0, 9, 0, 8] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 128) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 128 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[-32, 0, -72, 0, -4]⟩, ⟨[0, -32]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0] θ, polyEval [-1/4, 0, -9, 0, -8] θ, polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 128) (by norm_num) (by decide +kernel)

theorem eq_smul : Johnson.SnubDisphenoid.polyhedron = (Polyhedron.ofPoints points).smul (1 / 128) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7]

end Nieuwland.Polyhedra.JohnsonSnubDisphenoidDim

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/snub-disphenoid` is full-dimensional.** -/
theorem johnsonSnubDisphenoid_fullDim : Johnson.SnubDisphenoid.polyhedron.FullDim := by
  rw [JohnsonSnubDisphenoidDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk JohnsonSnubDisphenoidDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
