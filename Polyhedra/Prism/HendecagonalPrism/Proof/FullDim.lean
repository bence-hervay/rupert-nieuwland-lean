import Polyhedra.Prism.HendecagonalPrism.Definition
import Modules.Check.Leaf.FullDim
import Modules.Check.Number.Theta

set_option linter.style.longLine false

/-!
# The fixture `prism/hendecagonal-prism` is full-dimensional

The points of `Prism.HendecagonalPrism.polyhedron` times `428717762` as exact values in `ZTheta root`, exported
by `code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Prism.HendecagonalPrism.polyhedron`.
-/

namespace Nieuwland.Polyhedra.PrismHendecagonalPrismDim

open Check

@[inherit_doc] local notation "θ" => Nieuwland.Prism.HendecagonalPrism.theta

/-- The root `θ`, with `α = 11 θ` a root of a monic integer polynomial, enclosed in
`[Xl/D, Xh/D]`. -/
def root : Root :=
  ⟨[-1/11, 0, 1, 0, -4, 0, 7, 0, -5, 0, 1], 1, 5/2,
    11, [-2357947691, 0, 214358881, 0, -7086244, 0, 102487, 0, -605, 0, 1],
    32, 623, 626, 880, 29,
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
    261748036653746586140147789725674917787014792955448208944364165566689347793256957110894564763725458356381075966143676156057753261033804613989863710547956742,
    261748036653746586140147789725674917787014792955448208944364165566689347793256957110894564763725458356381075966143676156057753261033804613989863710547956743,
    by decide +kernel⟩

theorem root_α : root.α = (11 : ℕ) * θ := rfl

theorem root_n : root.n = 10 := rfl

/-- The points of `Prism.HendecagonalPrism.polyhedron` times `428717762`. -/
def points : List (V3 (ZTheta root)) := [
    ⟨⟨[0, 38974342]⟩, ⟨[0]⟩, ⟨[-214358881]⟩⟩,
    ⟨⟨[0, -175384539, 0, 7086244, 0, -102487, 0, 605, 0, -1]⟩, ⟨[9003073002, 0, -584615130, 0, 12078825, 0, -86515, 0, 154]⟩, ⟨[-214358881]⟩⟩,
    ⟨⟨[0, 682050985, 0, -37202781, 0, 644204, 0, -4114, 0, 7]⟩, ⟨[-10289226288, 0, 643076643, 0, -12723029, 0, 87846, 0, -154]⟩, ⟨[-214358881]⟩⟩,
    ⟨⟨[0, -1461537825, 0, 88578050, 0, -1698356, 0, 11495, 0, -20]⟩, ⟨[5787689787, 0, -331281907, 0, 5958887, 0, -38599, 0, 66]⟩, ⟨[-214358881]⟩⟩,
    ⟨⟨[0, 1753845390, 0, -111608343, 0, 2254714, 0, -15851, 0, 28]⟩, ⟨[-1714871048, 0, 77948684, 0, -1127357, 0, 6655, 0, -11]⟩, ⟨[-214358881]⟩⟩,
    ⟨⟨[0, -818461182, 0, 53146830, 0, -1098075, 0, 7865, 0, -14]⟩, ⟨[214358881]⟩, ⟨[-214358881]⟩⟩,
    ⟨⟨[0, -818461182, 0, 53146830, 0, -1098075, 0, 7865, 0, -14]⟩, ⟨[-214358881]⟩, ⟨[-214358881]⟩⟩,
    ⟨⟨[0, 1753845390, 0, -111608343, 0, 2254714, 0, -15851, 0, 28]⟩, ⟨[1714871048, 0, -77948684, 0, 1127357, 0, -6655, 0, 11]⟩, ⟨[-214358881]⟩⟩,
    ⟨⟨[0, -1461537825, 0, 88578050, 0, -1698356, 0, 11495, 0, -20]⟩, ⟨[-5787689787, 0, 331281907, 0, -5958887, 0, 38599, 0, -66]⟩, ⟨[-214358881]⟩⟩,
    ⟨⟨[0, 682050985, 0, -37202781, 0, 644204, 0, -4114, 0, 7]⟩, ⟨[10289226288, 0, -643076643, 0, 12723029, 0, -87846, 0, 154]⟩, ⟨[-214358881]⟩⟩,
    ⟨⟨[0, -175384539, 0, 7086244, 0, -102487, 0, 605, 0, -1]⟩, ⟨[-9003073002, 0, 584615130, 0, -12078825, 0, 86515, 0, -154]⟩, ⟨[-214358881]⟩⟩,
    ⟨⟨[0, 38974342]⟩, ⟨[0]⟩, ⟨[214358881]⟩⟩,
    ⟨⟨[0, -175384539, 0, 7086244, 0, -102487, 0, 605, 0, -1]⟩, ⟨[9003073002, 0, -584615130, 0, 12078825, 0, -86515, 0, 154]⟩, ⟨[214358881]⟩⟩,
    ⟨⟨[0, 682050985, 0, -37202781, 0, 644204, 0, -4114, 0, 7]⟩, ⟨[-10289226288, 0, 643076643, 0, -12723029, 0, 87846, 0, -154]⟩, ⟨[214358881]⟩⟩,
    ⟨⟨[0, -1461537825, 0, 88578050, 0, -1698356, 0, 11495, 0, -20]⟩, ⟨[5787689787, 0, -331281907, 0, 5958887, 0, -38599, 0, 66]⟩, ⟨[214358881]⟩⟩,
    ⟨⟨[0, 1753845390, 0, -111608343, 0, 2254714, 0, -15851, 0, 28]⟩, ⟨[-1714871048, 0, 77948684, 0, -1127357, 0, 6655, 0, -11]⟩, ⟨[214358881]⟩⟩,
    ⟨⟨[0, -818461182, 0, 53146830, 0, -1098075, 0, 7865, 0, -14]⟩, ⟨[214358881]⟩, ⟨[214358881]⟩⟩,
    ⟨⟨[0, -818461182, 0, 53146830, 0, -1098075, 0, 7865, 0, -14]⟩, ⟨[-214358881]⟩, ⟨[214358881]⟩⟩,
    ⟨⟨[0, 1753845390, 0, -111608343, 0, 2254714, 0, -15851, 0, 28]⟩, ⟨[1714871048, 0, -77948684, 0, 1127357, 0, -6655, 0, 11]⟩, ⟨[214358881]⟩⟩,
    ⟨⟨[0, -1461537825, 0, 88578050, 0, -1698356, 0, 11495, 0, -20]⟩, ⟨[-5787689787, 0, 331281907, 0, -5958887, 0, 38599, 0, -66]⟩, ⟨[214358881]⟩⟩,
    ⟨⟨[0, 682050985, 0, -37202781, 0, 644204, 0, -4114, 0, 7]⟩, ⟨[10289226288, 0, -643076643, 0, 12723029, 0, -87846, 0, 154]⟩, ⟨[214358881]⟩⟩,
    ⟨⟨[0, -175384539, 0, 7086244, 0, -102487, 0, 605, 0, -1]⟩, ⟨[-9003073002, 0, 584615130, 0, -12078825, 0, 86515, 0, -154]⟩, ⟨[214358881]⟩⟩]

theorem span_ok : spanOk points 0 1 2 11 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 428717762 : ℝ) • Exact.reV (⟨⟨[0, 38974342]⟩, ⟨[0]⟩, ⟨[-214358881]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0, 1] θ, polyEval [0] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 428717762) (by norm_num) (by decide +kernel)

theorem pt1 : (1 / 428717762 : ℝ) • Exact.reV (⟨⟨[0, -175384539, 0, 7086244, 0, -102487, 0, 605,
    0, -1]⟩, ⟨[9003073002, 0, -584615130, 0, 12078825, 0, -86515, 0, 154]⟩, ⟨[-214358881]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0, -9/2, 0, 22, 0, -77/2, 0, 55/2, 0, -11/2] θ, polyEval [21, 0,
    -165, 0, 825/2, 0, -715/2, 0, 77] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 428717762) (by norm_num) (by decide +kernel)

theorem pt2 : (1 / 428717762 : ℝ) • Exact.reV (⟨⟨[0, 682050985, 0, -37202781, 0, 644204, 0,
    -4114, 0, 7]⟩, ⟨[-10289226288, 0, 643076643, 0, -12723029, 0, 87846, 0, -154]⟩, ⟨[-214358881]⟩⟩
    : V3 (ZTheta root)) = ![polyEval [0, 35/2, 0, -231/2, 0, 242, 0, -187, 0, 77/2] θ, polyEval
    [-24, 0, 363/2, 0, -869/2, 0, 363, 0, -77] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 428717762) (by norm_num) (by decide +kernel)

theorem pt3 : (1 / 428717762 : ℝ) • Exact.reV (⟨⟨[0, -1461537825, 0, 88578050, 0, -1698356, 0,
    11495, 0, -20]⟩, ⟨[5787689787, 0, -331281907, 0, 5958887, 0, -38599, 0, 66]⟩, ⟨[-214358881]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [0, -75/2, 0, 275, 0, -638, 0, 1045/2, 0, -110] θ, polyEval
    [27/2, 0, -187/2, 0, 407/2, 0, -319/2, 0, 33] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 428717762) (by norm_num) (by decide +kernel)

theorem pt4 : (1 / 428717762 : ℝ) • Exact.reV (⟨⟨[0, 1753845390, 0, -111608343, 0, 2254714, 0,
    -15851, 0, 28]⟩, ⟨[-1714871048, 0, 77948684, 0, -1127357, 0, 6655, 0, -11]⟩, ⟨[-214358881]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [0, 45, 0, -693/2, 0, 847, 0, -1441/2, 0, 154] θ, polyEval [-4,
    0, 22, 0, -77/2, 0, 55/2, 0, -11/2] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 428717762) (by norm_num) (by decide +kernel)

theorem pt5 : (1 / 428717762 : ℝ) • Exact.reV (⟨⟨[0, -818461182, 0, 53146830, 0, -1098075, 0,
    7865, 0, -14]⟩, ⟨[214358881]⟩, ⟨[-214358881]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, -21, 0, 165,
    0, -825/2, 0, 715/2, 0, -77] θ, polyEval [1/2] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 428717762) (by norm_num) (by decide +kernel)

theorem pt6 : (1 / 428717762 : ℝ) • Exact.reV (⟨⟨[0, -818461182, 0, 53146830, 0, -1098075, 0,
    7865, 0, -14]⟩, ⟨[-214358881]⟩, ⟨[-214358881]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, -21, 0,
    165, 0, -825/2, 0, 715/2, 0, -77] θ, polyEval [-1/2] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 428717762) (by norm_num) (by decide +kernel)

theorem pt7 : (1 / 428717762 : ℝ) • Exact.reV (⟨⟨[0, 1753845390, 0, -111608343, 0, 2254714, 0,
    -15851, 0, 28]⟩, ⟨[1714871048, 0, -77948684, 0, 1127357, 0, -6655, 0, 11]⟩, ⟨[-214358881]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0, 45, 0, -693/2, 0, 847, 0, -1441/2, 0, 154] θ, polyEval [4, 0,
    -22, 0, 77/2, 0, -55/2, 0, 11/2] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 428717762) (by norm_num) (by decide +kernel)

theorem pt8 : (1 / 428717762 : ℝ) • Exact.reV (⟨⟨[0, -1461537825, 0, 88578050, 0, -1698356, 0,
    11495, 0, -20]⟩, ⟨[-5787689787, 0, 331281907, 0, -5958887, 0, 38599, 0, -66]⟩, ⟨[-214358881]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [0, -75/2, 0, 275, 0, -638, 0, 1045/2, 0, -110] θ, polyEval
    [-27/2, 0, 187/2, 0, -407/2, 0, 319/2, 0, -33] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 428717762) (by norm_num) (by decide +kernel)

theorem pt9 : (1 / 428717762 : ℝ) • Exact.reV (⟨⟨[0, 682050985, 0, -37202781, 0, 644204, 0,
    -4114, 0, 7]⟩, ⟨[10289226288, 0, -643076643, 0, 12723029, 0, -87846, 0, 154]⟩, ⟨[-214358881]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [0, 35/2, 0, -231/2, 0, 242, 0, -187, 0, 77/2] θ, polyEval [24,
    0, -363/2, 0, 869/2, 0, -363, 0, 77] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 428717762) (by norm_num) (by decide +kernel)

theorem pt10 : (1 / 428717762 : ℝ) • Exact.reV (⟨⟨[0, -175384539, 0, 7086244, 0, -102487, 0,
    605, 0, -1]⟩, ⟨[-9003073002, 0, 584615130, 0, -12078825, 0, 86515, 0, -154]⟩, ⟨[-214358881]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [0, -9/2, 0, 22, 0, -77/2, 0, 55/2, 0, -11/2] θ, polyEval [-21,
    0, 165, 0, -825/2, 0, 715/2, 0, -77] θ, polyEval [-1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 428717762) (by norm_num) (by decide +kernel)

theorem pt11 : (1 / 428717762 : ℝ) • Exact.reV (⟨⟨[0, 38974342]⟩, ⟨[0]⟩, ⟨[214358881]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0, 1] θ, polyEval [0] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 428717762) (by norm_num) (by decide +kernel)

theorem pt12 : (1 / 428717762 : ℝ) • Exact.reV (⟨⟨[0, -175384539, 0, 7086244, 0, -102487, 0,
    605, 0, -1]⟩, ⟨[9003073002, 0, -584615130, 0, 12078825, 0, -86515, 0, 154]⟩, ⟨[214358881]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0, -9/2, 0, 22, 0, -77/2, 0, 55/2, 0, -11/2] θ, polyEval [21, 0,
    -165, 0, 825/2, 0, -715/2, 0, 77] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 428717762) (by norm_num) (by decide +kernel)

theorem pt13 : (1 / 428717762 : ℝ) • Exact.reV (⟨⟨[0, 682050985, 0, -37202781, 0, 644204, 0,
    -4114, 0, 7]⟩, ⟨[-10289226288, 0, 643076643, 0, -12723029, 0, 87846, 0, -154]⟩, ⟨[214358881]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [0, 35/2, 0, -231/2, 0, 242, 0, -187, 0, 77/2] θ, polyEval [-24,
    0, 363/2, 0, -869/2, 0, 363, 0, -77] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 428717762) (by norm_num) (by decide +kernel)

theorem pt14 : (1 / 428717762 : ℝ) • Exact.reV (⟨⟨[0, -1461537825, 0, 88578050, 0, -1698356, 0,
    11495, 0, -20]⟩, ⟨[5787689787, 0, -331281907, 0, 5958887, 0, -38599, 0, 66]⟩, ⟨[214358881]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [0, -75/2, 0, 275, 0, -638, 0, 1045/2, 0, -110] θ, polyEval
    [27/2, 0, -187/2, 0, 407/2, 0, -319/2, 0, 33] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 428717762) (by norm_num) (by decide +kernel)

theorem pt15 : (1 / 428717762 : ℝ) • Exact.reV (⟨⟨[0, 1753845390, 0, -111608343, 0, 2254714, 0,
    -15851, 0, 28]⟩, ⟨[-1714871048, 0, 77948684, 0, -1127357, 0, 6655, 0, -11]⟩, ⟨[214358881]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0, 45, 0, -693/2, 0, 847, 0, -1441/2, 0, 154] θ, polyEval [-4, 0,
    22, 0, -77/2, 0, 55/2, 0, -11/2] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 428717762) (by norm_num) (by decide +kernel)

theorem pt16 : (1 / 428717762 : ℝ) • Exact.reV (⟨⟨[0, -818461182, 0, 53146830, 0, -1098075, 0,
    7865, 0, -14]⟩, ⟨[214358881]⟩, ⟨[214358881]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, -21, 0, 165,
    0, -825/2, 0, 715/2, 0, -77] θ, polyEval [1/2] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 428717762) (by norm_num) (by decide +kernel)

theorem pt17 : (1 / 428717762 : ℝ) • Exact.reV (⟨⟨[0, -818461182, 0, 53146830, 0, -1098075, 0,
    7865, 0, -14]⟩, ⟨[-214358881]⟩, ⟨[214358881]⟩⟩ : V3 (ZTheta root)) = ![polyEval [0, -21, 0, 165,
    0, -825/2, 0, 715/2, 0, -77] θ, polyEval [-1/2] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 428717762) (by norm_num) (by decide +kernel)

theorem pt18 : (1 / 428717762 : ℝ) • Exact.reV (⟨⟨[0, 1753845390, 0, -111608343, 0, 2254714, 0,
    -15851, 0, 28]⟩, ⟨[1714871048, 0, -77948684, 0, 1127357, 0, -6655, 0, 11]⟩, ⟨[214358881]⟩⟩ : V3
    (ZTheta root)) = ![polyEval [0, 45, 0, -693/2, 0, 847, 0, -1441/2, 0, 154] θ, polyEval [4, 0,
    -22, 0, 77/2, 0, -55/2, 0, 11/2] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 428717762) (by norm_num) (by decide +kernel)

theorem pt19 : (1 / 428717762 : ℝ) • Exact.reV (⟨⟨[0, -1461537825, 0, 88578050, 0, -1698356, 0,
    11495, 0, -20]⟩, ⟨[-5787689787, 0, 331281907, 0, -5958887, 0, 38599, 0, -66]⟩, ⟨[214358881]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [0, -75/2, 0, 275, 0, -638, 0, 1045/2, 0, -110] θ, polyEval
    [-27/2, 0, 187/2, 0, -407/2, 0, 319/2, 0, -33] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 428717762) (by norm_num) (by decide +kernel)

theorem pt20 : (1 / 428717762 : ℝ) • Exact.reV (⟨⟨[0, 682050985, 0, -37202781, 0, 644204, 0,
    -4114, 0, 7]⟩, ⟨[10289226288, 0, -643076643, 0, 12723029, 0, -87846, 0, 154]⟩, ⟨[214358881]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [0, 35/2, 0, -231/2, 0, 242, 0, -187, 0, 77/2] θ, polyEval [24,
    0, -363/2, 0, 869/2, 0, -363, 0, 77] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 428717762) (by norm_num) (by decide +kernel)

theorem pt21 : (1 / 428717762 : ℝ) • Exact.reV (⟨⟨[0, -175384539, 0, 7086244, 0, -102487, 0,
    605, 0, -1]⟩, ⟨[-9003073002, 0, 584615130, 0, -12078825, 0, 86515, 0, -154]⟩, ⟨[214358881]⟩⟩ :
    V3 (ZTheta root)) = ![polyEval [0, -9/2, 0, 22, 0, -77/2, 0, 55/2, 0, -11/2] θ, polyEval [-21,
    0, 165, 0, -825/2, 0, 715/2, 0, -77] θ, polyEval [1/2] θ] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;>
    exact ZTheta.smul_re_eq (S := 428717762) (by norm_num) (by decide +kernel)

theorem eq_smul : Prism.HendecagonalPrism.polyhedron = (Polyhedron.ofPoints points).smul (1 / 428717762) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17, pt18, pt19, pt20, pt21]

end Nieuwland.Polyhedra.PrismHendecagonalPrismDim

namespace Nieuwland.Polyhedra

/-- **The fixture `prism/hendecagonal-prism` is full-dimensional.** -/
theorem prismHendecagonalPrism_fullDim : Prism.HendecagonalPrism.polyhedron.FullDim := by
  rw [PrismHendecagonalPrismDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk PrismHendecagonalPrismDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
