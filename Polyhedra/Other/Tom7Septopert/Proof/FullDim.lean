import Polyhedra.Other.Tom7Septopert.Definition
import Modules.Check.Leaf.FullDim

/-!
# The fixture `external/tom7/septopert` is full-dimensional

The points of `Other.Tom7Septopert.polyhedron` times `1048576` as exact values in `ℤ`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Other.Tom7Septopert.polyhedron`.
-/

namespace Nieuwland.Polyhedra.ExternalTom7SeptopertDim

open Check

/-- The points of `Other.Tom7Septopert.polyhedron` times `1048576`. -/
def points : List (V3 ℤ) := [
    ⟨-940638, 327651, 327651⟩,
    ⟨327651, -940638, 327651⟩,
    ⟨327651, 327651, -940638⟩,
    ⟨703968, 47788, 47788⟩,
    ⟨47788, 703968, 47788⟩,
    ⟨47788, 47788, 703968⟩,
    ⟨-514207, -514207, -514207⟩]

theorem span_ok : spanOk points 0 1 2 3 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 1048576 : ℝ) • Exact.reV (⟨-940638, 327651, 327651⟩ : V3 ℤ) =
    ![-470319/524288, 327651/1048576, 327651/1048576] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt1 : (1 / 1048576 : ℝ) • Exact.reV (⟨327651, -940638, 327651⟩ : V3 ℤ) =
    ![327651/1048576, -470319/524288, 327651/1048576] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt2 : (1 / 1048576 : ℝ) • Exact.reV (⟨327651, 327651, -940638⟩ : V3 ℤ) =
    ![327651/1048576, 327651/1048576, -470319/524288] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt3 : (1 / 1048576 : ℝ) • Exact.reV (⟨703968, 47788, 47788⟩ : V3 ℤ) = ![21999/32768,
    11947/262144, 11947/262144] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt4 : (1 / 1048576 : ℝ) • Exact.reV (⟨47788, 703968, 47788⟩ : V3 ℤ) = ![11947/262144,
    21999/32768, 11947/262144] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt5 : (1 / 1048576 : ℝ) • Exact.reV (⟨47788, 47788, 703968⟩ : V3 ℤ) = ![11947/262144,
    11947/262144, 21999/32768] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt6 : (1 / 1048576 : ℝ) • Exact.reV (⟨-514207, -514207, -514207⟩ : V3 ℤ) =
    ![-514207/1048576, -514207/1048576, -514207/1048576] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem eq_smul : Other.Tom7Septopert.polyhedron = (Polyhedron.ofPoints points).smul (1 / 1048576) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6]

end Nieuwland.Polyhedra.ExternalTom7SeptopertDim

namespace Nieuwland.Polyhedra

/-- **The fixture `external/tom7/septopert` is full-dimensional.** -/
theorem externalTom7Septopert_fullDim : Other.Tom7Septopert.polyhedron.FullDim := by
  rw [ExternalTom7SeptopertDim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk ExternalTom7SeptopertDim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
