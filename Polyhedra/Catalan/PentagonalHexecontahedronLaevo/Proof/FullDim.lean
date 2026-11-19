import Polyhedra.Catalan.PentagonalHexecontahedronLaevo.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `catalan/pentagonal-hexecontahedron-laevo` is full-dimensional

The points of `Catalan.PentagonalHexecontahedronLaevo.polyhedron` times `62` as exact values in `ZTheta root`,
exported by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`,
checked by the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`),
and scaled back (`eq_smul`, `Polyhedron.FullDim.smul`), so is
`Catalan.PentagonalHexecontahedronLaevo.polyhedron`.
-/

namespace Nieuwland.Polyhedra.CatalanPentagonalHexecontahedronLaevoDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Catalan.PentagonalHexecontahedronLaevo.theta

/-- The root `θ`, with `α = 1 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[1, -2, -1, 0, -2, 2, 1], 1/2, 2,
    1, [1, -2, -1, 0, -2, 2, 1],
    64, 71, 74, 128, 19,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    15186514075632957228149208604396546283690023476550530132818186165544419919797879565653690361645869056720987063278756084530489516159568955509370844790344772,
    15186514075632957228149208604396546283690023476550530132818186165544419919797879565653690361645869056720987063278756084530489516159568955509370844790344773,
    by decide +kernel⟩

theorem root_α : root.α = (1 : ℕ) * θ := rfl

theorem root_n : root.n = 6 := rfl

/-- The points of `Catalan.PentagonalHexecontahedronLaevo.polyhedron` times `62`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[-62]⟩, ⟨[0, -62]⟩, ⟨[124, -93, -31, -124, -217, -62]⟩⟩,
    ⟨⟨[-62]⟩, ⟨[0, 62]⟩, ⟨[-124, 93, 31, 124, 217, 62]⟩⟩,
    ⟨⟨[62]⟩, ⟨[0, 62]⟩, ⟨[124, -93, -31, -124, -217, -62]⟩⟩,
    ⟨⟨[62]⟩, ⟨[0, -62]⟩, ⟨[-124, 93, 31, 124, 217, 62]⟩⟩,
    ⟨⟨[124, -93, -31, -124, -217, -62]⟩, ⟨[-62]⟩, ⟨[0, -62]⟩⟩,
    ⟨⟨[124, -93, -31, -124, -217, -62]⟩, ⟨[62]⟩, ⟨[0, 62]⟩⟩,
    ⟨⟨[-124, 93, 31, 124, 217, 62]⟩, ⟨[62]⟩, ⟨[0, -62]⟩⟩,
    ⟨⟨[-124, 93, 31, 124, 217, 62]⟩, ⟨[-62]⟩, ⟨[0, 62]⟩⟩,
    ⟨⟨[0, -62]⟩, ⟨[124, -93, -31, -124, -217, -62]⟩, ⟨[-62]⟩⟩,
    ⟨⟨[0, -62]⟩, ⟨[-124, 93, 31, 124, 217, 62]⟩, ⟨[62]⟩⟩,
    ⟨⟨[0, 62]⟩, ⟨[-124, 93, 31, 124, 217, 62]⟩, ⟨[-62]⟩⟩,
    ⟨⟨[0, 62]⟩, ⟨[124, -93, -31, -124, -217, -62]⟩, ⟨[62]⟩⟩,
    ⟨⟨[0]⟩, ⟨[-31, -124, 0, -124, 31, 31]⟩, ⟨[31, -93, -93, -124, -124, -31]⟩⟩,
    ⟨⟨[0]⟩, ⟨[-31, -124, 0, -124, 31, 31]⟩, ⟨[-31, 93, 93, 124, 124, 31]⟩⟩,
    ⟨⟨[0]⟩, ⟨[31, 124, 0, 124, -31, -31]⟩, ⟨[31, -93, -93, -124, -124, -31]⟩⟩,
    ⟨⟨[0]⟩, ⟨[31, 124, 0, 124, -31, -31]⟩, ⟨[-31, 93, 93, 124, 124, 31]⟩⟩,
    ⟨⟨[31, -93, -93, -124, -124, -31]⟩, ⟨[0]⟩, ⟨[-31, -124, 0, -124, 31, 31]⟩⟩,
    ⟨⟨[31, -93, -93, -124, -124, -31]⟩, ⟨[0]⟩, ⟨[31, 124, 0, 124, -31, -31]⟩⟩,
    ⟨⟨[-31, 93, 93, 124, 124, 31]⟩, ⟨[0]⟩, ⟨[-31, -124, 0, -124, 31, 31]⟩⟩,
    ⟨⟨[-31, 93, 93, 124, 124, 31]⟩, ⟨[0]⟩, ⟨[31, 124, 0, 124, -31, -31]⟩⟩,
    ⟨⟨[-31, -124, 0, -124, 31, 31]⟩, ⟨[31, -93, -93, -124, -124, -31]⟩, ⟨[0]⟩⟩,
    ⟨⟨[-31, -124, 0, -124, 31, 31]⟩, ⟨[-31, 93, 93, 124, 124, 31]⟩, ⟨[0]⟩⟩,
    ⟨⟨[31, 124, 0, 124, -31, -31]⟩, ⟨[31, -93, -93, -124, -124, -31]⟩, ⟨[0]⟩⟩,
    ⟨⟨[31, 124, 0, 124, -31, -31]⟩, ⟨[-31, 93, 93, 124, 124, 31]⟩, ⟨[0]⟩⟩,
    ⟨⟨[-41, 1, -109, -18, -70, -29]⟩, ⟨[0]⟩, ⟨[89, -74, -56, -94, -183, -55]⟩⟩,
    ⟨⟨[-41, 1, -109, -18, -70, -29]⟩, ⟨[0]⟩, ⟨[-89, 74, 56, 94, 183, 55]⟩⟩,
    ⟨⟨[41, -1, 109, 18, 70, 29]⟩, ⟨[0]⟩, ⟨[89, -74, -56, -94, -183, -55]⟩⟩,
    ⟨⟨[41, -1, 109, 18, 70, 29]⟩, ⟨[0]⟩, ⟨[-89, 74, 56, 94, 183, 55]⟩⟩,
    ⟨⟨[89, -74, -56, -94, -183, -55]⟩, ⟨[-41, 1, -109, -18, -70, -29]⟩, ⟨[0]⟩⟩,
    ⟨⟨[89, -74, -56, -94, -183, -55]⟩, ⟨[41, -1, 109, 18, 70, 29]⟩, ⟨[0]⟩⟩,
    ⟨⟨[-89, 74, 56, 94, 183, 55]⟩, ⟨[-41, 1, -109, -18, -70, -29]⟩, ⟨[0]⟩⟩,
    ⟨⟨[-89, 74, 56, 94, 183, 55]⟩, ⟨[41, -1, 109, 18, 70, 29]⟩, ⟨[0]⟩⟩,
    ⟨⟨[0]⟩, ⟨[89, -74, -56, -94, -183, -55]⟩, ⟨[-41, 1, -109, -18, -70, -29]⟩⟩,
    ⟨⟨[0]⟩, ⟨[89, -74, -56, -94, -183, -55]⟩, ⟨[41, -1, 109, 18, 70, 29]⟩⟩,
    ⟨⟨[0]⟩, ⟨[-89, 74, 56, 94, 183, 55]⟩, ⟨[-41, 1, -109, -18, -70, -29]⟩⟩,
    ⟨⟨[0]⟩, ⟨[-89, 74, 56, 94, 183, 55]⟩, ⟨[41, -1, 109, 18, 70, 29]⟩⟩,
    ⟨⟨[-93, 31, -62, -31]⟩, ⟨[-31, 62, 31, 93, 31]⟩, ⟨[62, -62, -62, -62, -186, -62]⟩⟩,
    ⟨⟨[-93, 31, -62, -31]⟩, ⟨[31, -62, -31, -93, -31]⟩, ⟨[-62, 62, 62, 62, 186, 62]⟩⟩,
    ⟨⟨[93, -31, 62, 31]⟩, ⟨[31, -62, -31, -93, -31]⟩, ⟨[62, -62, -62, -62, -186, -62]⟩⟩,
    ⟨⟨[93, -31, 62, 31]⟩, ⟨[-31, 62, 31, 93, 31]⟩, ⟨[-62, 62, 62, 62, 186, 62]⟩⟩,
    ⟨⟨[62, -62, -62, -62, -186, -62]⟩, ⟨[93, -31, 62, 31]⟩, ⟨[31, -62, -31, -93, -31]⟩⟩,
    ⟨⟨[62, -62, -62, -62, -186, -62]⟩, ⟨[-93, 31, -62, -31]⟩, ⟨[-31, 62, 31, 93, 31]⟩⟩,
    ⟨⟨[-62, 62, 62, 62, 186, 62]⟩, ⟨[-93, 31, -62, -31]⟩, ⟨[31, -62, -31, -93, -31]⟩⟩,
    ⟨⟨[-62, 62, 62, 62, 186, 62]⟩, ⟨[93, -31, 62, 31]⟩, ⟨[-31, 62, 31, 93, 31]⟩⟩,
    ⟨⟨[31, -62, -31, -93, -31]⟩, ⟨[-62, 62, 62, 62, 186, 62]⟩, ⟨[-93, 31, -62, -31]⟩⟩,
    ⟨⟨[31, -62, -31, -93, -31]⟩, ⟨[62, -62, -62, -62, -186, -62]⟩, ⟨[93, -31, 62, 31]⟩⟩,
    ⟨⟨[-31, 62, 31, 93, 31]⟩, ⟨[62, -62, -62, -62, -186, -62]⟩, ⟨[-93, 31, -62, -31]⟩⟩,
    ⟨⟨[-31, 62, 31, 93, 31]⟩, ⟨[-62, 62, 62, 62, 186, 62]⟩, ⟨[93, -31, 62, 31]⟩⟩,
    ⟨⟨[-31, 31, -62, -31]⟩, ⟨[62, -62, 31, -93, -124, -31]⟩, ⟨[-31, -62, -124, -62, -93, -31]⟩⟩,
    ⟨⟨[-31, 31, -62, -31]⟩, ⟨[-62, 62, -31, 93, 124, 31]⟩, ⟨[31, 62, 124, 62, 93, 31]⟩⟩,
    ⟨⟨[31, -31, 62, 31]⟩, ⟨[-62, 62, -31, 93, 124, 31]⟩, ⟨[-31, -62, -124, -62, -93, -31]⟩⟩,
    ⟨⟨[31, -31, 62, 31]⟩, ⟨[62, -62, 31, -93, -124, -31]⟩, ⟨[31, 62, 124, 62, 93, 31]⟩⟩,
    ⟨⟨[-31, -62, -124, -62, -93, -31]⟩, ⟨[-31, 31, -62, -31]⟩, ⟨[62, -62, 31, -93, -124, -31]⟩⟩,
    ⟨⟨[-31, -62, -124, -62, -93, -31]⟩, ⟨[31, -31, 62, 31]⟩, ⟨[-62, 62, -31, 93, 124, 31]⟩⟩,
    ⟨⟨[31, 62, 124, 62, 93, 31]⟩, ⟨[31, -31, 62, 31]⟩, ⟨[62, -62, 31, -93, -124, -31]⟩⟩,
    ⟨⟨[31, 62, 124, 62, 93, 31]⟩, ⟨[-31, 31, -62, -31]⟩, ⟨[-62, 62, -31, 93, 124, 31]⟩⟩,
    ⟨⟨[62, -62, 31, -93, -124, -31]⟩, ⟨[-31, -62, -124, -62, -93, -31]⟩, ⟨[-31, 31, -62, -31]⟩⟩,
    ⟨⟨[62, -62, 31, -93, -124, -31]⟩, ⟨[31, 62, 124, 62, 93, 31]⟩, ⟨[31, -31, 62, 31]⟩⟩,
    ⟨⟨[-62, 62, -31, 93, 124, 31]⟩, ⟨[31, 62, 124, 62, 93, 31]⟩, ⟨[-31, 31, -62, -31]⟩⟩,
    ⟨⟨[-62, 62, -31, 93, 124, 31]⟩, ⟨[-31, -62, -124, -62, -93, -31]⟩, ⟨[31, -31, 62, 31]⟩⟩,
    ⟨⟨[-62, 0, -93, 31, -62, -31]⟩, ⟨[62, -31, -62, -31, -93, -31]⟩, ⟨[62, 0, -62, -62, -186, -62]⟩⟩,
    ⟨⟨[-62, 0, -93, 31, -62, -31]⟩, ⟨[-62, 31, 62, 31, 93, 31]⟩, ⟨[-62, 0, 62, 62, 186, 62]⟩⟩,
    ⟨⟨[62, 0, 93, -31, 62, 31]⟩, ⟨[-62, 31, 62, 31, 93, 31]⟩, ⟨[62, 0, -62, -62, -186, -62]⟩⟩,
    ⟨⟨[62, 0, 93, -31, 62, 31]⟩, ⟨[62, -31, -62, -31, -93, -31]⟩, ⟨[-62, 0, 62, 62, 186, 62]⟩⟩,
    ⟨⟨[62, 0, -62, -62, -186, -62]⟩, ⟨[-62, 0, -93, 31, -62, -31]⟩, ⟨[62, -31, -62, -31, -93, -31]⟩⟩,
    ⟨⟨[62, 0, -62, -62, -186, -62]⟩, ⟨[62, 0, 93, -31, 62, 31]⟩, ⟨[-62, 31, 62, 31, 93, 31]⟩⟩,
    ⟨⟨[-62, 0, 62, 62, 186, 62]⟩, ⟨[62, 0, 93, -31, 62, 31]⟩, ⟨[62, -31, -62, -31, -93, -31]⟩⟩,
    ⟨⟨[-62, 0, 62, 62, 186, 62]⟩, ⟨[-62, 0, -93, 31, -62, -31]⟩, ⟨[-62, 31, 62, 31, 93, 31]⟩⟩,
    ⟨⟨[62, -31, -62, -31, -93, -31]⟩, ⟨[62, 0, -62, -62, -186, -62]⟩, ⟨[-62, 0, -93, 31, -62, -31]⟩⟩,
    ⟨⟨[62, -31, -62, -31, -93, -31]⟩, ⟨[-62, 0, 62, 62, 186, 62]⟩, ⟨[62, 0, 93, -31, 62, 31]⟩⟩,
    ⟨⟨[-62, 31, 62, 31, 93, 31]⟩, ⟨[-62, 0, 62, 62, 186, 62]⟩, ⟨[-62, 0, -93, 31, -62, -31]⟩⟩,
    ⟨⟨[-62, 31, 62, 31, 93, 31]⟩, ⟨[62, 0, -62, -62, -186, -62]⟩, ⟨[62, 0, 93, -31, 62, 31]⟩⟩,
    ⟨⟨[0, 0, -93, 31, -62, -31]⟩, ⟨[-93, 31, 0, 31, 186, 62]⟩, ⟨[-31, 0, -124, -62, -93, -31]⟩⟩,
    ⟨⟨[0, 0, -93, 31, -62, -31]⟩, ⟨[93, -31, 0, -31, -186, -62]⟩, ⟨[31, 0, 124, 62, 93, 31]⟩⟩,
    ⟨⟨[0, 0, 93, -31, 62, 31]⟩, ⟨[93, -31, 0, -31, -186, -62]⟩, ⟨[-31, 0, -124, -62, -93, -31]⟩⟩,
    ⟨⟨[0, 0, 93, -31, 62, 31]⟩, ⟨[-93, 31, 0, 31, 186, 62]⟩, ⟨[31, 0, 124, 62, 93, 31]⟩⟩,
    ⟨⟨[-31, 0, -124, -62, -93, -31]⟩, ⟨[0, 0, 93, -31, 62, 31]⟩, ⟨[93, -31, 0, -31, -186, -62]⟩⟩,
    ⟨⟨[-31, 0, -124, -62, -93, -31]⟩, ⟨[0, 0, -93, 31, -62, -31]⟩, ⟨[-93, 31, 0, 31, 186, 62]⟩⟩,
    ⟨⟨[31, 0, 124, 62, 93, 31]⟩, ⟨[0, 0, -93, 31, -62, -31]⟩, ⟨[93, -31, 0, -31, -186, -62]⟩⟩,
    ⟨⟨[31, 0, 124, 62, 93, 31]⟩, ⟨[0, 0, 93, -31, 62, 31]⟩, ⟨[-93, 31, 0, 31, 186, 62]⟩⟩,
    ⟨⟨[93, -31, 0, -31, -186, -62]⟩, ⟨[31, 0, 124, 62, 93, 31]⟩, ⟨[0, 0, -93, 31, -62, -31]⟩⟩,
    ⟨⟨[93, -31, 0, -31, -186, -62]⟩, ⟨[-31, 0, -124, -62, -93, -31]⟩, ⟨[0, 0, 93, -31, 62, 31]⟩⟩,
    ⟨⟨[-93, 31, 0, 31, 186, 62]⟩, ⟨[-31, 0, -124, -62, -93, -31]⟩, ⟨[0, 0, -93, 31, -62, -31]⟩⟩,
    ⟨⟨[-93, 31, 0, 31, 186, 62]⟩, ⟨[31, 0, 124, 62, 93, 31]⟩, ⟨[0, 0, 93, -31, 62, 31]⟩⟩,
    ⟨⟨[62, 31, -93, 0, -155, -62]⟩, ⟨[62, 31, -93, 0, -155, -62]⟩, ⟨[62, 31, -93, 0, -155, -62]⟩⟩,
    ⟨⟨[62, 31, -93, 0, -155, -62]⟩, ⟨[62, 31, -93, 0, -155, -62]⟩, ⟨[-62, -31, 93, 0, 155, 62]⟩⟩,
    ⟨⟨[62, 31, -93, 0, -155, -62]⟩, ⟨[-62, -31, 93, 0, 155, 62]⟩, ⟨[62, 31, -93, 0, -155, -62]⟩⟩,
    ⟨⟨[62, 31, -93, 0, -155, -62]⟩, ⟨[-62, -31, 93, 0, 155, 62]⟩, ⟨[-62, -31, 93, 0, 155, 62]⟩⟩,
    ⟨⟨[-62, -31, 93, 0, 155, 62]⟩, ⟨[62, 31, -93, 0, -155, -62]⟩, ⟨[62, 31, -93, 0, -155, -62]⟩⟩,
    ⟨⟨[-62, -31, 93, 0, 155, 62]⟩, ⟨[62, 31, -93, 0, -155, -62]⟩, ⟨[-62, -31, 93, 0, 155, 62]⟩⟩,
    ⟨⟨[-62, -31, 93, 0, 155, 62]⟩, ⟨[-62, -31, 93, 0, 155, 62]⟩, ⟨[62, 31, -93, 0, -155, -62]⟩⟩,
    ⟨⟨[-62, -31, 93, 0, 155, 62]⟩, ⟨[-62, -31, 93, 0, 155, 62]⟩, ⟨[-62, -31, 93, 0, 155, 62]⟩⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-62]⟩, ⟨[0, -62]⟩, ⟨[124, -93, -31, -124, -217,
    -62]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1] θ, polyEval [0, -1] θ, polyEval [2, -3/2, -1/2, -2,
    -7/2, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-62]⟩, ⟨[0, 62]⟩, ⟨[-124, 93, 31, 124, 217, 62]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [-1] θ, polyEval [0, 1] θ, polyEval [-2, 3/2, 1/2, 2, 7/2, 1] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[62]⟩, ⟨[0, 62]⟩, ⟨[124, -93, -31, -124, -217, -62]⟩⟩
    : V3 (ZTheta root)) = ![polyEval [1] θ, polyEval [0, 1] θ, polyEval [2, -3/2, -1/2, -2, -7/2,
    -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[62]⟩, ⟨[0, -62]⟩, ⟨[-124, 93, 31, 124, 217, 62]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [1] θ, polyEval [0, -1] θ, polyEval [-2, 3/2, 1/2, 2, 7/2, 1] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[124, -93, -31, -124, -217, -62]⟩, ⟨[-62]⟩, ⟨[0,
    -62]⟩⟩ : V3 (ZTheta root)) = ![polyEval [2, -3/2, -1/2, -2, -7/2, -1] θ, polyEval [-1] θ,
    polyEval [0, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[124, -93, -31, -124, -217, -62]⟩, ⟨[62]⟩, ⟨[0, 62]⟩⟩
    : V3 (ZTheta root)) = ![polyEval [2, -3/2, -1/2, -2, -7/2, -1] θ, polyEval [1] θ, polyEval [0,
    1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-124, 93, 31, 124, 217, 62]⟩, ⟨[62]⟩, ⟨[0, -62]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [-2, 3/2, 1/2, 2, 7/2, 1] θ, polyEval [1] θ, polyEval [0, -1] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-124, 93, 31, 124, 217, 62]⟩, ⟨[-62]⟩, ⟨[0, 62]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [-2, 3/2, 1/2, 2, 7/2, 1] θ, polyEval [-1] θ, polyEval [0, 1] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[0, -62]⟩, ⟨[124, -93, -31, -124, -217, -62]⟩,
    ⟨[-62]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, -1] θ, polyEval [2, -3/2, -1/2, -2, -7/2, -1] θ,
    polyEval [-1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt9 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[0, -62]⟩, ⟨[-124, 93, 31, 124, 217, 62]⟩, ⟨[62]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [0, -1] θ, polyEval [-2, 3/2, 1/2, 2, 7/2, 1] θ, polyEval [1] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt10 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[0, 62]⟩, ⟨[-124, 93, 31, 124, 217, 62]⟩, ⟨[-62]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [0, 1] θ, polyEval [-2, 3/2, 1/2, 2, 7/2, 1] θ, polyEval [-1] θ]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt11 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[0, 62]⟩, ⟨[124, -93, -31, -124, -217, -62]⟩, ⟨[62]⟩⟩
    : V3 (ZTheta root)) = ![polyEval [0, 1] θ, polyEval [2, -3/2, -1/2, -2, -7/2, -1] θ, polyEval
    [1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt12 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[-31, -124, 0, -124, 31, 31]⟩, ⟨[31, -93, -93,
    -124, -124, -31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0] θ, polyEval [-1/2, -2, 0, -2, 1/2, 1/2]
    θ, polyEval [1/2, -3/2, -3/2, -2, -2, -1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt13 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[-31, -124, 0, -124, 31, 31]⟩, ⟨[-31, 93, 93,
    124, 124, 31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0] θ, polyEval [-1/2, -2, 0, -2, 1/2, 1/2] θ,
    polyEval [-1/2, 3/2, 3/2, 2, 2, 1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt14 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[31, 124, 0, 124, -31, -31]⟩, ⟨[31, -93, -93,
    -124, -124, -31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0] θ, polyEval [1/2, 2, 0, 2, -1/2, -1/2]
    θ, polyEval [1/2, -3/2, -3/2, -2, -2, -1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt15 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[31, 124, 0, 124, -31, -31]⟩, ⟨[-31, 93, 93,
    124, 124, 31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0] θ, polyEval [1/2, 2, 0, 2, -1/2, -1/2] θ,
    polyEval [-1/2, 3/2, 3/2, 2, 2, 1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt16 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[31, -93, -93, -124, -124, -31]⟩, ⟨[0]⟩, ⟨[-31, -124,
    0, -124, 31, 31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1/2, -3/2, -3/2, -2, -2, -1/2] θ, polyEval
    [0] θ, polyEval [-1/2, -2, 0, -2, 1/2, 1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt17 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[31, -93, -93, -124, -124, -31]⟩, ⟨[0]⟩, ⟨[31, 124,
    0, 124, -31, -31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1/2, -3/2, -3/2, -2, -2, -1/2] θ, polyEval
    [0] θ, polyEval [1/2, 2, 0, 2, -1/2, -1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt18 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-31, 93, 93, 124, 124, 31]⟩, ⟨[0]⟩, ⟨[-31, -124, 0,
    -124, 31, 31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1/2, 3/2, 3/2, 2, 2, 1/2] θ, polyEval [0] θ,
    polyEval [-1/2, -2, 0, -2, 1/2, 1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt19 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-31, 93, 93, 124, 124, 31]⟩, ⟨[0]⟩, ⟨[31, 124, 0,
    124, -31, -31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1/2, 3/2, 3/2, 2, 2, 1/2] θ, polyEval [0] θ,
    polyEval [1/2, 2, 0, 2, -1/2, -1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt20 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-31, -124, 0, -124, 31, 31]⟩, ⟨[31, -93, -93, -124,
    -124, -31]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1/2, -2, 0, -2, 1/2, 1/2] θ, polyEval
    [1/2, -3/2, -3/2, -2, -2, -1/2] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt21 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-31, -124, 0, -124, 31, 31]⟩, ⟨[-31, 93, 93, 124,
    124, 31]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1/2, -2, 0, -2, 1/2, 1/2] θ, polyEval
    [-1/2, 3/2, 3/2, 2, 2, 1/2] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt22 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[31, 124, 0, 124, -31, -31]⟩, ⟨[31, -93, -93, -124,
    -124, -31]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1/2, 2, 0, 2, -1/2, -1/2] θ, polyEval
    [1/2, -3/2, -3/2, -2, -2, -1/2] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt23 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[31, 124, 0, 124, -31, -31]⟩, ⟨[-31, 93, 93, 124,
    124, 31]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1/2, 2, 0, 2, -1/2, -1/2] θ, polyEval [-1/2,
    3/2, 3/2, 2, 2, 1/2] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt24 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-41, 1, -109, -18, -70, -29]⟩, ⟨[0]⟩, ⟨[89, -74,
    -56, -94, -183, -55]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-41/62, 1/62, -109/62, -9/31, -35/31,
    -29/62] θ, polyEval [0] θ, polyEval [89/62, -37/31, -28/31, -47/31, -183/62, -55/62] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt25 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-41, 1, -109, -18, -70, -29]⟩, ⟨[0]⟩, ⟨[-89, 74, 56,
    94, 183, 55]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-41/62, 1/62, -109/62, -9/31, -35/31, -29/62]
    θ, polyEval [0] θ, polyEval [-89/62, 37/31, 28/31, 47/31, 183/62, 55/62] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt26 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[41, -1, 109, 18, 70, 29]⟩, ⟨[0]⟩, ⟨[89, -74, -56,
    -94, -183, -55]⟩⟩ : V3 (ZTheta root)) = ![polyEval [41/62, -1/62, 109/62, 9/31, 35/31, 29/62] θ,
    polyEval [0] θ, polyEval [89/62, -37/31, -28/31, -47/31, -183/62, -55/62] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt27 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[41, -1, 109, 18, 70, 29]⟩, ⟨[0]⟩, ⟨[-89, 74, 56, 94,
    183, 55]⟩⟩ : V3 (ZTheta root)) = ![polyEval [41/62, -1/62, 109/62, 9/31, 35/31, 29/62] θ,
    polyEval [0] θ, polyEval [-89/62, 37/31, 28/31, 47/31, 183/62, 55/62] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt28 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[89, -74, -56, -94, -183, -55]⟩, ⟨[-41, 1, -109, -18,
    -70, -29]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) = ![polyEval [89/62, -37/31, -28/31, -47/31, -183/62,
    -55/62] θ, polyEval [-41/62, 1/62, -109/62, -9/31, -35/31, -29/62] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt29 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[89, -74, -56, -94, -183, -55]⟩, ⟨[41, -1, 109, 18,
    70, 29]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) = ![polyEval [89/62, -37/31, -28/31, -47/31, -183/62,
    -55/62] θ, polyEval [41/62, -1/62, 109/62, 9/31, 35/31, 29/62] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt30 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-89, 74, 56, 94, 183, 55]⟩, ⟨[-41, 1, -109, -18,
    -70, -29]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-89/62, 37/31, 28/31, 47/31, 183/62, 55/62]
    θ, polyEval [-41/62, 1/62, -109/62, -9/31, -35/31, -29/62] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt31 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-89, 74, 56, 94, 183, 55]⟩, ⟨[41, -1, 109, 18, 70,
    29]⟩, ⟨[0]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-89/62, 37/31, 28/31, 47/31, 183/62, 55/62] θ,
    polyEval [41/62, -1/62, 109/62, 9/31, 35/31, 29/62] θ, polyEval [0] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt32 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[89, -74, -56, -94, -183, -55]⟩, ⟨[-41, 1,
    -109, -18, -70, -29]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0] θ, polyEval [89/62, -37/31, -28/31,
    -47/31, -183/62, -55/62] θ, polyEval [-41/62, 1/62, -109/62, -9/31, -35/31, -29/62] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt33 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[89, -74, -56, -94, -183, -55]⟩, ⟨[41, -1,
    109, 18, 70, 29]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0] θ, polyEval [89/62, -37/31, -28/31,
    -47/31, -183/62, -55/62] θ, polyEval [41/62, -1/62, 109/62, 9/31, 35/31, 29/62] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt34 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[-89, 74, 56, 94, 183, 55]⟩, ⟨[-41, 1, -109,
    -18, -70, -29]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0] θ, polyEval [-89/62, 37/31, 28/31, 47/31,
    183/62, 55/62] θ, polyEval [-41/62, 1/62, -109/62, -9/31, -35/31, -29/62] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt35 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[0]⟩, ⟨[-89, 74, 56, 94, 183, 55]⟩, ⟨[41, -1, 109,
    18, 70, 29]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0] θ, polyEval [-89/62, 37/31, 28/31, 47/31,
    183/62, 55/62] θ, polyEval [41/62, -1/62, 109/62, 9/31, 35/31, 29/62] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt36 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-93, 31, -62, -31]⟩, ⟨[-31, 62, 31, 93, 31]⟩, ⟨[62,
    -62, -62, -62, -186, -62]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-3/2, 1/2, -1, -1/2] θ, polyEval
    [-1/2, 1, 1/2, 3/2, 1/2] θ, polyEval [1, -1, -1, -1, -3, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt37 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-93, 31, -62, -31]⟩, ⟨[31, -62, -31, -93, -31]⟩,
    ⟨[-62, 62, 62, 62, 186, 62]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-3/2, 1/2, -1, -1/2] θ, polyEval
    [1/2, -1, -1/2, -3/2, -1/2] θ, polyEval [-1, 1, 1, 1, 3, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt38 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[93, -31, 62, 31]⟩, ⟨[31, -62, -31, -93, -31]⟩, ⟨[62,
    -62, -62, -62, -186, -62]⟩⟩ : V3 (ZTheta root)) = ![polyEval [3/2, -1/2, 1, 1/2] θ, polyEval
    [1/2, -1, -1/2, -3/2, -1/2] θ, polyEval [1, -1, -1, -1, -3, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt39 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[93, -31, 62, 31]⟩, ⟨[-31, 62, 31, 93, 31]⟩, ⟨[-62,
    62, 62, 62, 186, 62]⟩⟩ : V3 (ZTheta root)) = ![polyEval [3/2, -1/2, 1, 1/2] θ, polyEval [-1/2,
    1, 1/2, 3/2, 1/2] θ, polyEval [-1, 1, 1, 1, 3, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt40 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[62, -62, -62, -62, -186, -62]⟩, ⟨[93, -31, 62, 31]⟩,
    ⟨[31, -62, -31, -93, -31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1, -1, -1, -1, -3, -1] θ, polyEval
    [3/2, -1/2, 1, 1/2] θ, polyEval [1/2, -1, -1/2, -3/2, -1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt41 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[62, -62, -62, -62, -186, -62]⟩, ⟨[-93, 31, -62,
    -31]⟩, ⟨[-31, 62, 31, 93, 31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1, -1, -1, -1, -3, -1] θ,
    polyEval [-3/2, 1/2, -1, -1/2] θ, polyEval [-1/2, 1, 1/2, 3/2, 1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt42 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-62, 62, 62, 62, 186, 62]⟩, ⟨[-93, 31, -62, -31]⟩,
    ⟨[31, -62, -31, -93, -31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1, 1, 1, 1, 3, 1] θ, polyEval
    [-3/2, 1/2, -1, -1/2] θ, polyEval [1/2, -1, -1/2, -3/2, -1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt43 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-62, 62, 62, 62, 186, 62]⟩, ⟨[93, -31, 62, 31]⟩,
    ⟨[-31, 62, 31, 93, 31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1, 1, 1, 1, 3, 1] θ, polyEval [3/2,
    -1/2, 1, 1/2] θ, polyEval [-1/2, 1, 1/2, 3/2, 1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt44 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[31, -62, -31, -93, -31]⟩, ⟨[-62, 62, 62, 62, 186,
    62]⟩, ⟨[-93, 31, -62, -31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1/2, -1, -1/2, -3/2, -1/2] θ,
    polyEval [-1, 1, 1, 1, 3, 1] θ, polyEval [-3/2, 1/2, -1, -1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt45 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[31, -62, -31, -93, -31]⟩, ⟨[62, -62, -62, -62, -186,
    -62]⟩, ⟨[93, -31, 62, 31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1/2, -1, -1/2, -3/2, -1/2] θ,
    polyEval [1, -1, -1, -1, -3, -1] θ, polyEval [3/2, -1/2, 1, 1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt46 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-31, 62, 31, 93, 31]⟩, ⟨[62, -62, -62, -62, -186,
    -62]⟩, ⟨[-93, 31, -62, -31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1/2, 1, 1/2, 3/2, 1/2] θ,
    polyEval [1, -1, -1, -1, -3, -1] θ, polyEval [-3/2, 1/2, -1, -1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt47 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-31, 62, 31, 93, 31]⟩, ⟨[-62, 62, 62, 62, 186, 62]⟩,
    ⟨[93, -31, 62, 31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1/2, 1, 1/2, 3/2, 1/2] θ, polyEval [-1,
    1, 1, 1, 3, 1] θ, polyEval [3/2, -1/2, 1, 1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt48 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-31, 31, -62, -31]⟩, ⟨[62, -62, 31, -93, -124,
    -31]⟩, ⟨[-31, -62, -124, -62, -93, -31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1/2, 1/2, -1, -1/2]
    θ, polyEval [1, -1, 1/2, -3/2, -2, -1/2] θ, polyEval [-1/2, -1, -2, -1, -3/2, -1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt49 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-31, 31, -62, -31]⟩, ⟨[-62, 62, -31, 93, 124, 31]⟩,
    ⟨[31, 62, 124, 62, 93, 31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1/2, 1/2, -1, -1/2] θ, polyEval
    [-1, 1, -1/2, 3/2, 2, 1/2] θ, polyEval [1/2, 1, 2, 1, 3/2, 1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt50 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[31, -31, 62, 31]⟩, ⟨[-62, 62, -31, 93, 124, 31]⟩,
    ⟨[-31, -62, -124, -62, -93, -31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1/2, -1/2, 1, 1/2] θ,
    polyEval [-1, 1, -1/2, 3/2, 2, 1/2] θ, polyEval [-1/2, -1, -2, -1, -3/2, -1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt51 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[31, -31, 62, 31]⟩, ⟨[62, -62, 31, -93, -124, -31]⟩,
    ⟨[31, 62, 124, 62, 93, 31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1/2, -1/2, 1, 1/2] θ, polyEval
    [1, -1, 1/2, -3/2, -2, -1/2] θ, polyEval [1/2, 1, 2, 1, 3/2, 1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt52 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-31, -62, -124, -62, -93, -31]⟩, ⟨[-31, 31, -62,
    -31]⟩, ⟨[62, -62, 31, -93, -124, -31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1/2, -1, -2, -1,
    -3/2, -1/2] θ, polyEval [-1/2, 1/2, -1, -1/2] θ, polyEval [1, -1, 1/2, -3/2, -2, -1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt53 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-31, -62, -124, -62, -93, -31]⟩, ⟨[31, -31, 62,
    31]⟩, ⟨[-62, 62, -31, 93, 124, 31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1/2, -1, -2, -1, -3/2,
    -1/2] θ, polyEval [1/2, -1/2, 1, 1/2] θ, polyEval [-1, 1, -1/2, 3/2, 2, 1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt54 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[31, 62, 124, 62, 93, 31]⟩, ⟨[31, -31, 62, 31]⟩,
    ⟨[62, -62, 31, -93, -124, -31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1/2, 1, 2, 1, 3/2, 1/2] θ,
    polyEval [1/2, -1/2, 1, 1/2] θ, polyEval [1, -1, 1/2, -3/2, -2, -1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt55 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[31, 62, 124, 62, 93, 31]⟩, ⟨[-31, 31, -62, -31]⟩,
    ⟨[-62, 62, -31, 93, 124, 31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1/2, 1, 2, 1, 3/2, 1/2] θ,
    polyEval [-1/2, 1/2, -1, -1/2] θ, polyEval [-1, 1, -1/2, 3/2, 2, 1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt56 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[62, -62, 31, -93, -124, -31]⟩, ⟨[-31, -62, -124,
    -62, -93, -31]⟩, ⟨[-31, 31, -62, -31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1, -1, 1/2, -3/2, -2,
    -1/2] θ, polyEval [-1/2, -1, -2, -1, -3/2, -1/2] θ, polyEval [-1/2, 1/2, -1, -1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt57 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[62, -62, 31, -93, -124, -31]⟩, ⟨[31, 62, 124, 62,
    93, 31]⟩, ⟨[31, -31, 62, 31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1, -1, 1/2, -3/2, -2, -1/2] θ,
    polyEval [1/2, 1, 2, 1, 3/2, 1/2] θ, polyEval [1/2, -1/2, 1, 1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt58 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-62, 62, -31, 93, 124, 31]⟩, ⟨[31, 62, 124, 62, 93,
    31]⟩, ⟨[-31, 31, -62, -31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1, 1, -1/2, 3/2, 2, 1/2] θ,
    polyEval [1/2, 1, 2, 1, 3/2, 1/2] θ, polyEval [-1/2, 1/2, -1, -1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt59 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-62, 62, -31, 93, 124, 31]⟩, ⟨[-31, -62, -124, -62,
    -93, -31]⟩, ⟨[31, -31, 62, 31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1, 1, -1/2, 3/2, 2, 1/2] θ,
    polyEval [-1/2, -1, -2, -1, -3/2, -1/2] θ, polyEval [1/2, -1/2, 1, 1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt60 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-62, 0, -93, 31, -62, -31]⟩, ⟨[62, -31, -62, -31,
    -93, -31]⟩, ⟨[62, 0, -62, -62, -186, -62]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1, 0, -3/2, 1/2,
    -1, -1/2] θ, polyEval [1, -1/2, -1, -1/2, -3/2, -1/2] θ, polyEval [1, 0, -1, -1, -3, -1] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt61 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-62, 0, -93, 31, -62, -31]⟩, ⟨[-62, 31, 62, 31, 93,
    31]⟩, ⟨[-62, 0, 62, 62, 186, 62]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1, 0, -3/2, 1/2, -1, -1/2]
    θ, polyEval [-1, 1/2, 1, 1/2, 3/2, 1/2] θ, polyEval [-1, 0, 1, 1, 3, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt62 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[62, 0, 93, -31, 62, 31]⟩, ⟨[-62, 31, 62, 31, 93,
    31]⟩, ⟨[62, 0, -62, -62, -186, -62]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1, 0, 3/2, -1/2, 1, 1/2]
    θ, polyEval [-1, 1/2, 1, 1/2, 3/2, 1/2] θ, polyEval [1, 0, -1, -1, -3, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt63 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[62, 0, 93, -31, 62, 31]⟩, ⟨[62, -31, -62, -31, -93,
    -31]⟩, ⟨[-62, 0, 62, 62, 186, 62]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1, 0, 3/2, -1/2, 1, 1/2]
    θ, polyEval [1, -1/2, -1, -1/2, -3/2, -1/2] θ, polyEval [-1, 0, 1, 1, 3, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt64 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[62, 0, -62, -62, -186, -62]⟩, ⟨[-62, 0, -93, 31,
    -62, -31]⟩, ⟨[62, -31, -62, -31, -93, -31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1, 0, -1, -1, -3,
    -1] θ, polyEval [-1, 0, -3/2, 1/2, -1, -1/2] θ, polyEval [1, -1/2, -1, -1/2, -3/2, -1/2] θ] :=
    by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt65 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[62, 0, -62, -62, -186, -62]⟩, ⟨[62, 0, 93, -31, 62,
    31]⟩, ⟨[-62, 31, 62, 31, 93, 31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1, 0, -1, -1, -3, -1] θ,
    polyEval [1, 0, 3/2, -1/2, 1, 1/2] θ, polyEval [-1, 1/2, 1, 1/2, 3/2, 1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt66 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-62, 0, 62, 62, 186, 62]⟩, ⟨[62, 0, 93, -31, 62,
    31]⟩, ⟨[62, -31, -62, -31, -93, -31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1, 0, 1, 1, 3, 1] θ,
    polyEval [1, 0, 3/2, -1/2, 1, 1/2] θ, polyEval [1, -1/2, -1, -1/2, -3/2, -1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt67 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-62, 0, 62, 62, 186, 62]⟩, ⟨[-62, 0, -93, 31, -62,
    -31]⟩, ⟨[-62, 31, 62, 31, 93, 31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1, 0, 1, 1, 3, 1] θ,
    polyEval [-1, 0, -3/2, 1/2, -1, -1/2] θ, polyEval [-1, 1/2, 1, 1/2, 3/2, 1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt68 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[62, -31, -62, -31, -93, -31]⟩, ⟨[62, 0, -62, -62,
    -186, -62]⟩, ⟨[-62, 0, -93, 31, -62, -31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1, -1/2, -1, -1/2,
    -3/2, -1/2] θ, polyEval [1, 0, -1, -1, -3, -1] θ, polyEval [-1, 0, -3/2, 1/2, -1, -1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt69 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[62, -31, -62, -31, -93, -31]⟩, ⟨[-62, 0, 62, 62,
    186, 62]⟩, ⟨[62, 0, 93, -31, 62, 31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1, -1/2, -1, -1/2,
    -3/2, -1/2] θ, polyEval [-1, 0, 1, 1, 3, 1] θ, polyEval [1, 0, 3/2, -1/2, 1, 1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt70 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-62, 31, 62, 31, 93, 31]⟩, ⟨[-62, 0, 62, 62, 186,
    62]⟩, ⟨[-62, 0, -93, 31, -62, -31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1, 1/2, 1, 1/2, 3/2,
    1/2] θ, polyEval [-1, 0, 1, 1, 3, 1] θ, polyEval [-1, 0, -3/2, 1/2, -1, -1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt71 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-62, 31, 62, 31, 93, 31]⟩, ⟨[62, 0, -62, -62, -186,
    -62]⟩, ⟨[62, 0, 93, -31, 62, 31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1, 1/2, 1, 1/2, 3/2, 1/2]
    θ, polyEval [1, 0, -1, -1, -3, -1] θ, polyEval [1, 0, 3/2, -1/2, 1, 1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt72 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[0, 0, -93, 31, -62, -31]⟩, ⟨[-93, 31, 0, 31, 186,
    62]⟩, ⟨[-31, 0, -124, -62, -93, -31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 0, -3/2, 1/2, -1,
    -1/2] θ, polyEval [-3/2, 1/2, 0, 1/2, 3, 1] θ, polyEval [-1/2, 0, -2, -1, -3/2, -1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt73 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[0, 0, -93, 31, -62, -31]⟩, ⟨[93, -31, 0, -31, -186,
    -62]⟩, ⟨[31, 0, 124, 62, 93, 31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 0, -3/2, 1/2, -1, -1/2]
    θ, polyEval [3/2, -1/2, 0, -1/2, -3, -1] θ, polyEval [1/2, 0, 2, 1, 3/2, 1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt74 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[0, 0, 93, -31, 62, 31]⟩, ⟨[93, -31, 0, -31, -186,
    -62]⟩, ⟨[-31, 0, -124, -62, -93, -31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 0, 3/2, -1/2, 1,
    1/2] θ, polyEval [3/2, -1/2, 0, -1/2, -3, -1] θ, polyEval [-1/2, 0, -2, -1, -3/2, -1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt75 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[0, 0, 93, -31, 62, 31]⟩, ⟨[-93, 31, 0, 31, 186,
    62]⟩, ⟨[31, 0, 124, 62, 93, 31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, 0, 3/2, -1/2, 1, 1/2] θ,
    polyEval [-3/2, 1/2, 0, 1/2, 3, 1] θ, polyEval [1/2, 0, 2, 1, 3/2, 1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt76 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-31, 0, -124, -62, -93, -31]⟩, ⟨[0, 0, 93, -31, 62,
    31]⟩, ⟨[93, -31, 0, -31, -186, -62]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1/2, 0, -2, -1, -3/2,
    -1/2] θ, polyEval [0, 0, 3/2, -1/2, 1, 1/2] θ, polyEval [3/2, -1/2, 0, -1/2, -3, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt77 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-31, 0, -124, -62, -93, -31]⟩, ⟨[0, 0, -93, 31, -62,
    -31]⟩, ⟨[-93, 31, 0, 31, 186, 62]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1/2, 0, -2, -1, -3/2,
    -1/2] θ, polyEval [0, 0, -3/2, 1/2, -1, -1/2] θ, polyEval [-3/2, 1/2, 0, 1/2, 3, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt78 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[31, 0, 124, 62, 93, 31]⟩, ⟨[0, 0, -93, 31, -62,
    -31]⟩, ⟨[93, -31, 0, -31, -186, -62]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1/2, 0, 2, 1, 3/2, 1/2]
    θ, polyEval [0, 0, -3/2, 1/2, -1, -1/2] θ, polyEval [3/2, -1/2, 0, -1/2, -3, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt79 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[31, 0, 124, 62, 93, 31]⟩, ⟨[0, 0, 93, -31, 62, 31]⟩,
    ⟨[-93, 31, 0, 31, 186, 62]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1/2, 0, 2, 1, 3/2, 1/2] θ,
    polyEval [0, 0, 3/2, -1/2, 1, 1/2] θ, polyEval [-3/2, 1/2, 0, 1/2, 3, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt80 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[93, -31, 0, -31, -186, -62]⟩, ⟨[31, 0, 124, 62, 93,
    31]⟩, ⟨[0, 0, -93, 31, -62, -31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [3/2, -1/2, 0, -1/2, -3, -1]
    θ, polyEval [1/2, 0, 2, 1, 3/2, 1/2] θ, polyEval [0, 0, -3/2, 1/2, -1, -1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt81 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[93, -31, 0, -31, -186, -62]⟩, ⟨[-31, 0, -124, -62,
    -93, -31]⟩, ⟨[0, 0, 93, -31, 62, 31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [3/2, -1/2, 0, -1/2, -3,
    -1] θ, polyEval [-1/2, 0, -2, -1, -3/2, -1/2] θ, polyEval [0, 0, 3/2, -1/2, 1, 1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt82 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-93, 31, 0, 31, 186, 62]⟩, ⟨[-31, 0, -124, -62, -93,
    -31]⟩, ⟨[0, 0, -93, 31, -62, -31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-3/2, 1/2, 0, 1/2, 3, 1]
    θ, polyEval [-1/2, 0, -2, -1, -3/2, -1/2] θ, polyEval [0, 0, -3/2, 1/2, -1, -1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt83 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-93, 31, 0, 31, 186, 62]⟩, ⟨[31, 0, 124, 62, 93,
    31]⟩, ⟨[0, 0, 93, -31, 62, 31]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-3/2, 1/2, 0, 1/2, 3, 1] θ,
    polyEval [1/2, 0, 2, 1, 3/2, 1/2] θ, polyEval [0, 0, 3/2, -1/2, 1, 1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt84 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[62, 31, -93, 0, -155, -62]⟩, ⟨[62, 31, -93, 0, -155,
    -62]⟩, ⟨[62, 31, -93, 0, -155, -62]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1, 1/2, -3/2, 0, -5/2,
    -1] θ, polyEval [1, 1/2, -3/2, 0, -5/2, -1] θ, polyEval [1, 1/2, -3/2, 0, -5/2, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt85 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[62, 31, -93, 0, -155, -62]⟩, ⟨[62, 31, -93, 0, -155,
    -62]⟩, ⟨[-62, -31, 93, 0, 155, 62]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1, 1/2, -3/2, 0, -5/2,
    -1] θ, polyEval [1, 1/2, -3/2, 0, -5/2, -1] θ, polyEval [-1, -1/2, 3/2, 0, 5/2, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt86 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[62, 31, -93, 0, -155, -62]⟩, ⟨[-62, -31, 93, 0, 155,
    62]⟩, ⟨[62, 31, -93, 0, -155, -62]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1, 1/2, -3/2, 0, -5/2,
    -1] θ, polyEval [-1, -1/2, 3/2, 0, 5/2, 1] θ, polyEval [1, 1/2, -3/2, 0, -5/2, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt87 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[62, 31, -93, 0, -155, -62]⟩, ⟨[-62, -31, 93, 0, 155,
    62]⟩, ⟨[-62, -31, 93, 0, 155, 62]⟩⟩ : V3 (ZTheta root)) = ![polyEval [1, 1/2, -3/2, 0, -5/2, -1]
    θ, polyEval [-1, -1/2, 3/2, 0, 5/2, 1] θ, polyEval [-1, -1/2, 3/2, 0, 5/2, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt88 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-62, -31, 93, 0, 155, 62]⟩, ⟨[62, 31, -93, 0, -155,
    -62]⟩, ⟨[62, 31, -93, 0, -155, -62]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1, -1/2, 3/2, 0, 5/2,
    1] θ, polyEval [1, 1/2, -3/2, 0, -5/2, -1] θ, polyEval [1, 1/2, -3/2, 0, -5/2, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt89 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-62, -31, 93, 0, 155, 62]⟩, ⟨[62, 31, -93, 0, -155,
    -62]⟩, ⟨[-62, -31, 93, 0, 155, 62]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1, -1/2, 3/2, 0, 5/2, 1]
    θ, polyEval [1, 1/2, -3/2, 0, -5/2, -1] θ, polyEval [-1, -1/2, 3/2, 0, 5/2, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt90 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-62, -31, 93, 0, 155, 62]⟩, ⟨[-62, -31, 93, 0, 155,
    62]⟩, ⟨[62, 31, -93, 0, -155, -62]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1, -1/2, 3/2, 0, 5/2, 1]
    θ, polyEval [-1, -1/2, 3/2, 0, 5/2, 1] θ, polyEval [1, 1/2, -3/2, 0, -5/2, -1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem pt91 : (1 / 62 : ℝ) • Exact.reV (⟨⟨[-62, -31, 93, 0, 155, 62]⟩, ⟨[-62, -31, 93, 0, 155,
    62]⟩, ⟨[-62, -31, 93, 0, 155, 62]⟩⟩ : V3 (ZTheta root)) = ![polyEval [-1, -1/2, 3/2, 0, 5/2, 1]
    θ, polyEval [-1, -1/2, 3/2, 0, 5/2, 1] θ, polyEval [-1, -1/2, 3/2, 0, 5/2, 1] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 62) (by norm_num) (by decide +kernel)

theorem eq_smul : Catalan.PentagonalHexecontahedronLaevo.polyhedron = (Polyhedron.ofPoints points).smul (1 / 62) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17, pt18, pt19, pt20, pt21, pt22, pt23, pt24,
    pt25, pt26, pt27, pt28, pt29, pt30, pt31, pt32, pt33, pt34, pt35, pt36, pt37, pt38, pt39, pt40,
    pt41, pt42, pt43, pt44, pt45, pt46, pt47, pt48, pt49, pt50, pt51, pt52, pt53, pt54, pt55, pt56,
    pt57, pt58, pt59, pt60, pt61, pt62, pt63, pt64, pt65, pt66, pt67, pt68, pt69, pt70, pt71, pt72,
    pt73, pt74, pt75, pt76, pt77, pt78, pt79, pt80, pt81, pt82, pt83, pt84, pt85, pt86, pt87, pt88,
    pt89, pt90, pt91]

end Nieuwland.Polyhedra.CatalanPentagonalHexecontahedronLaevoDim

namespace Nieuwland.Polyhedra

/-- **The fixture `catalan/pentagonal-hexecontahedron-laevo` is full-dimensional.** -/
theorem catalanPentagonalHexecontahedronLaevo_fullDim : Catalan.PentagonalHexecontahedronLaevo.polyhedron.FullDim := by
  rw [CatalanPentagonalHexecontahedronLaevoDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk CatalanPentagonalHexecontahedronLaevoDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
