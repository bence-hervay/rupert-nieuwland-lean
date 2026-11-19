import Polyhedra.Johnson.ElongatedTriangularDipyramidJ14.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `johnson/elongated-triangular-dipyramid-j14` is full-dimensional

The points of `Johnson.ElongatedTriangularDipyramidJ14.polyhedron` times `252` as exact values in `ZTheta root`,
exported by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`,
checked by the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`),
and scaled back (`eq_smul`, `Polyhedron.FullDim.smul`), so is
`Johnson.ElongatedTriangularDipyramidJ14.polyhedron`.
-/

namespace Nieuwland.Polyhedra.JohnsonElongatedTriangularDipyramidJ14Dim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Johnson.ElongatedTriangularDipyramidJ14.theta

/-- The root `θ`, with `α = 6 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[1/36, 1, 0, -2, 1], 5/4, 2,
    6, [36, 216, 0, -12, 1],
    16, 153, 156, 192, 13,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    129131004337815959075661570332004173920620807051995818702334618156479327545521572371751820452969391861265731378085281887708746014827531272275664977979806270,
    129131004337815959075661570332004173920620807051995818702334618156479327545521572371751820452969391861265731378085281887708746014827531272275664977979806271,
    by decide +kernel⟩

theorem root_α : root.α = (6 : ℕ) * θ := rfl

theorem root_n : root.n = 4 := rfl

/-- The points of `Johnson.ElongatedTriangularDipyramidJ14.polyhedron` times `252`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[126]⟩, ⟨[-72, 6, 9, -1]⟩, ⟨[126]⟩⟩,
    ⟨⟨[126]⟩, ⟨[-72, 6, 9, -1]⟩, ⟨[-126]⟩⟩,
    ⟨⟨[-126]⟩, ⟨[-72, 6, 9, -1]⟩, ⟨[126]⟩⟩,
    ⟨⟨[-126]⟩, ⟨[-72, 6, 9, -1]⟩, ⟨[-126]⟩⟩,
    ⟨⟨[0]⟩, ⟨[144, -12, -18, 2]⟩, ⟨[126]⟩⟩,
    ⟨⟨[0]⟩, ⟨[144, -12, -18, 2]⟩, ⟨[-126]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0]⟩, ⟨[-72, 48, 9, -1]⟩⟩,
    ⟨⟨[0]⟩, ⟨[0]⟩, ⟨[72, -48, -9, 1]⟩⟩]

theorem span_ok : spanOk points 0 1 2 4 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 252 : ℝ) • Exact.reV (⟨⟨[126]⟩, ⟨[-72, 6, 9, -1]⟩, ⟨[126]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [1/2] θ, polyEval [-2/7, 1/7, 9/7, -6/7] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 252) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 252 : ℝ) • Exact.reV (⟨⟨[126]⟩, ⟨[-72, 6, 9, -1]⟩, ⟨[-126]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [1/2] θ, polyEval [-2/7, 1/7, 9/7, -6/7] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 252) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 252 : ℝ) • Exact.reV (⟨⟨[-126]⟩, ⟨[-72, 6, 9, -1]⟩, ⟨[126]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [-1/2] θ, polyEval [-2/7, 1/7, 9/7, -6/7] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 252) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 252 : ℝ) • Exact.reV (⟨⟨[-126]⟩, ⟨[-72, 6, 9, -1]⟩, ⟨[-126]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [-1/2] θ, polyEval [-2/7, 1/7, 9/7, -6/7] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 252) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 252 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[144, -12, -18, 2]⟩, ⟨[126]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [0] θ, polyEval [4/7, -2/7, -18/7, 12/7] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 252) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 252 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[144, -12, -18, 2]⟩, ⟨[-126]⟩⟩ : V3 (ZTheta
    root)) = ![polyEval [0] θ, polyEval [4/7, -2/7, -18/7, 12/7] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 252) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 252 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0]⟩, ⟨[-72, 48, 9, -1]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [0] θ, polyEval [0] θ, polyEval [-2/7, 8/7, 9/7, -6/7] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 252) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 252 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[0]⟩, ⟨[72, -48, -9, 1]⟩⟩ : V3 (ZTheta root))
    = ![polyEval [0] θ, polyEval [0] θ, polyEval [2/7, -8/7, -9/7, 6/7] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 252) (by norm_num) (by decide +kernel)

theorem eq_smul : Johnson.ElongatedTriangularDipyramidJ14.polyhedron = (Polyhedron.ofPoints points).smul (1 / 252) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7]

end Nieuwland.Polyhedra.JohnsonElongatedTriangularDipyramidJ14Dim

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/elongated-triangular-dipyramid-j14` is full-dimensional.** -/
theorem johnsonElongatedTriangularDipyramidJ14_fullDim : Johnson.ElongatedTriangularDipyramidJ14.polyhedron.FullDim := by
  rw [JohnsonElongatedTriangularDipyramidJ14Dim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk JohnsonElongatedTriangularDipyramidJ14Dim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
