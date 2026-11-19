import Polyhedra.Johnson.PentagonalOrthobicupola.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Johnson.PentagonalOrthobicupola.Certificates.Weak
import Polyhedra.Johnson.PentagonalOrthobicupola.Certificates.Diameter

set_option linter.style.longLine false

/-!
# The fixture `johnson/pentagonal-orthobicupola`: an exact Nieuwland number from the diameter bound

The exact certificate `gs://main-69696-data/noperts-results/johnson-diameter-2026-11-15/pentagonal-orthobicupola/exact.jsonl`, exported by `code/lean-export scaled --fit`: one record for every pose, a diameter cover at the exact scale `Θ` (`Lift.cover_ok`: scaled by `Θ`, the solid does not fit through itself in any pose, `Check.Diam.Cover.not_fitsThrough`), and a weak fit at `Θ` (`Lift.weak_check`). The Nieuwland number of `Johnson.PentagonalOrthobicupola.polyhedron` is `Θ`.
-/

namespace Nieuwland.Polyhedra

open Check

/-- **The fixture `johnson/pentagonal-orthobicupola`: the Nieuwland number.** From the diameter cover and the weak fit at the exact scale `Θ` (`Check.Polyhedron.nieuwland_eq_of_diameter_lift`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem johnsonPentagonalOrthobicupola_nieuwland : Johnson.PentagonalOrthobicupola.polyhedron.nieuwland = realRoot [16/5, 0, -4, 0, 1] 1 (3/2) := by
  have hdim : Johnson.PentagonalOrthobicupola.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobicupola.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobicupola.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobicupola.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_diameter_lift (c := (((1 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) ^ 3 / ((1 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobicupola.Lift.points_eq Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobicupola.Lift.cover_ok Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobicupola.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobicupola.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
