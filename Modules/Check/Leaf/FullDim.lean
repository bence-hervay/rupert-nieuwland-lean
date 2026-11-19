import Modules.Rupert.FullDim
import Modules.Check.Leaf.Symmetry
import Modules.Check.Leaf.FitCheck

/-!
# Full-dimensionality from the spanning check

`spanOk` (`Modules/Check/Leaf/Symmetry.lean`) checks that three differences of the points are linearly
independent; the polyhedron of the points is then full-dimensional (`fullDim_of_spanOk`). Results
about a particular polyhedron prove `<name>_fullDim` this way, scaled back to the fixture's
polyhedron by `Polyhedron.FullDim.smul` (`Polyhedron.eq_smul_ofPoints`, imported with
`Modules/Check/Leaf/FitCheck.lean`, writes the fixture's polyhedron as the scaled one).
-/

namespace Nieuwland.Check

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- **Full-dimensionality.** If `spanOk` holds, the polyhedron of the points is
full-dimensional. -/
theorem Polyhedron.fullDim_of_spanOk {pts : List (V3 κ)} {i j k l : ℕ}
    (h : spanOk pts i j k l = true) : (Polyhedron.ofPoints pts).FullDim := by
  have hi : i < pts.length := by
    simp only [spanOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1.1
  exact Polyhedron.fullDim_of_span (Polyhedron.pt_mem_ofPoints hi) (spanOk_sound h _)

end Nieuwland.Check
