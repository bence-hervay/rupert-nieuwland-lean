import Polyhedra.Johnson.TriangularHebesphenorotunda.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Johnson.TriangularHebesphenorotunda.Certificates.Weak
import Polyhedra.Johnson.TriangularHebesphenorotunda.Certificates.Diameter

set_option linter.style.longLine false

/-!
# The fixture `johnson/triangular-hebesphenorotunda`: an exact Nieuwland number from the diameter bound

The exact certificate `gs://main-69696-data/noperts-results/johnson-diameter-2026-11-15/triangular-hebesphenorotunda/exact.jsonl`, exported by `code/lean-export scaled --fit`: one record for every pose, a diameter cover at the exact scale `Θ` (`Lift.cover_ok`: scaled by `Θ`, the solid does not fit through itself in any pose, `Check.Diam.Cover.not_fitsThrough`), and a weak fit at `Θ` (`Lift.weak_check`). The Nieuwland number of `Johnson.TriangularHebesphenorotunda.polyhedron` is `Θ`.
-/

namespace Nieuwland.Polyhedra

open Check

/-- **The fixture `johnson/triangular-hebesphenorotunda`: the Nieuwland number.** From the diameter cover and the weak fit at the exact scale `Θ` (`Check.Polyhedron.nieuwland_eq_of_diameter_lift`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem johnsonTriangularHebesphenorotunda_nieuwland : Johnson.TriangularHebesphenorotunda.polyhedron.nieuwland = realRoot [9, 0, -9, 0, 1] 0 2 := by
  have hdim : Johnson.TriangularHebesphenorotunda.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandJohnsonTriangularHebesphenorotunda.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandJohnsonTriangularHebesphenorotunda.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandJohnsonTriangularHebesphenorotunda.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_diameter_lift (c := (((1 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandJohnsonTriangularHebesphenorotunda.Lift.points_eq Nieuwland.Certs.NieuwlandJohnsonTriangularHebesphenorotunda.Lift.cover_ok Nieuwland.Certs.NieuwlandJohnsonTriangularHebesphenorotunda.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandJohnsonTriangularHebesphenorotunda.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
