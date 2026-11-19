import Polyhedra.Johnson.SquareCupola.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Johnson.SquareCupola.Certificates.Weak
import Polyhedra.Johnson.SquareCupola.Certificates.Diameter

set_option linter.style.longLine false

/-!
# The fixture `johnson/square-cupola`: an exact Nieuwland number from the diameter bound

The exact certificate `gs://main-69696-data/noperts-results/johnson-diameter-2026-11-15/square-cupola/exact.jsonl`, exported by `code/lean-export scaled --fit`: one record for every pose, a diameter cover at the exact scale `Θ` (`Lift.cover_ok`: scaled by `Θ`, the solid does not fit through itself in any pose, `Check.Diam.Cover.not_fitsThrough`), and a weak fit at `Θ` (`Lift.weak_check`). The Nieuwland number of `Johnson.SquareCupola.polyhedron` is `Θ`.
-/

namespace Nieuwland.Polyhedra

open Check

/-- **The fixture `johnson/square-cupola`: the Nieuwland number.** From the diameter cover and the weak fit at the exact scale `Θ` (`Check.Polyhedron.nieuwland_eq_of_diameter_lift`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem johnsonSquareCupola_nieuwland : Johnson.SquareCupola.polyhedron.nieuwland = realRoot [8, 0, -8, 0, 1] 0 2 := by
  have hdim : Johnson.SquareCupola.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandJohnsonSquareCupola.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandJohnsonSquareCupola.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandJohnsonSquareCupola.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_diameter_lift (c := (((1 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) / ((1 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandJohnsonSquareCupola.Lift.points_eq Nieuwland.Certs.NieuwlandJohnsonSquareCupola.Lift.cover_ok Nieuwland.Certs.NieuwlandJohnsonSquareCupola.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandJohnsonSquareCupola.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
