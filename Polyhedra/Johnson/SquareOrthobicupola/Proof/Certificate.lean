import Polyhedra.Johnson.SquareOrthobicupola.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Johnson.SquareOrthobicupola.Certificates.Weak
import Polyhedra.Johnson.SquareOrthobicupola.Certificates.Diameter

set_option linter.style.longLine false

/-!
# The fixture `johnson/square-orthobicupola`: an exact Nieuwland number from the diameter bound

The exact certificate `gs://main-69696-data/noperts-results/johnson-diameter-2026-11-15/square-orthobicupola/exact.jsonl`, exported by `code/lean-export scaled --fit`: one record for every pose, a diameter cover at the exact scale `Θ` (`Lift.cover_ok`: scaled by `Θ`, the solid does not fit through itself in any pose, `Check.Diam.Cover.not_fitsThrough`), and a weak fit at `Θ` (`Lift.weak_check`). The Nieuwland number of `Johnson.SquareOrthobicupola.polyhedron` is `Θ`.
-/

namespace Nieuwland.Polyhedra

open Check

/-- **The fixture `johnson/square-orthobicupola`: the Nieuwland number.** From the diameter cover and the weak fit at the exact scale `Θ` (`Check.Polyhedron.nieuwland_eq_of_diameter_lift`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem johnsonSquareOrthobicupola_nieuwland : Johnson.SquareOrthobicupola.polyhedron.nieuwland = realRoot [8, 0, -8, 0, 1] 0 2 := by
  have hdim : Johnson.SquareOrthobicupola.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandJohnsonSquareOrthobicupola.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandJohnsonSquareOrthobicupola.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandJohnsonSquareOrthobicupola.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_diameter_lift (c := (((1 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) / ((1 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandJohnsonSquareOrthobicupola.Lift.points_eq Nieuwland.Certs.NieuwlandJohnsonSquareOrthobicupola.Lift.cover_ok Nieuwland.Certs.NieuwlandJohnsonSquareOrthobicupola.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandJohnsonSquareOrthobicupola.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
