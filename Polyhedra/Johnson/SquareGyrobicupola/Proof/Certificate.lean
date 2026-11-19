import Polyhedra.Johnson.SquareGyrobicupola.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Johnson.SquareGyrobicupola.Certificates.Weak
import Polyhedra.Johnson.SquareGyrobicupola.Certificates.Diameter

set_option linter.style.longLine false

/-!
# The fixture `johnson/square-gyrobicupola`: an exact Nieuwland number from the diameter bound

The exact certificate `gs://main-69696-data/noperts-results/johnson-diameter-2026-11-15/square-gyrobicupola/exact.jsonl`, exported by `code/lean-export scaled --fit`: one record for every pose, a diameter cover at the exact scale `Θ` (`Lift.cover_ok`: scaled by `Θ`, the solid does not fit through itself in any pose, `Check.Diam.Cover.not_fitsThrough`), and a weak fit at `Θ` (`Lift.weak_check`). The Nieuwland number of `Johnson.SquareGyrobicupola.polyhedron` is `Θ`.
-/

namespace Nieuwland.Polyhedra

open Check

/-- **The fixture `johnson/square-gyrobicupola`: the Nieuwland number.** From the diameter cover and the weak fit at the exact scale `Θ` (`Check.Polyhedron.nieuwland_eq_of_diameter_lift`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem johnsonSquareGyrobicupola_nieuwland : Johnson.SquareGyrobicupola.polyhedron.nieuwland = polyEval [460842649249975642061277860035016662281/61458881299431843877750721137020882332, 28899591611098728339434847178179013859/215106084548011453572127523979573088162, -2147061445934050772803074278555576235/107553042274005726786063761989786544081, -5809710522092467323457536146455948/15364720324857960969437680284255220583, 956136629159220112919148553249302/107553042274005726786063761989786544081, 2653382571355575346898315426164/15364720324857960969437680284255220583, -113978319681577364142685054760/107553042274005726786063761989786544081, -2196964818310889361807981120/107553042274005726786063761989786544081] (realRoot [-696587858354447/64, 888368381200, 24534067523/4, -1693412544, 74716381/4, 625632, -8922, -64, 1] 56 57) := by
  have hdim : Johnson.SquareGyrobicupola.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandJohnsonSquareGyrobicupola.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandJohnsonSquareGyrobicupola.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandJohnsonSquareGyrobicupola.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_diameter_lift (c := (((1 : ℕ) : ℝ) * ((9872553890115473309142908 : ℕ) : ℝ) / ((1 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandJohnsonSquareGyrobicupola.Lift.points_eq Nieuwland.Certs.NieuwlandJohnsonSquareGyrobicupola.Lift.cover_ok Nieuwland.Certs.NieuwlandJohnsonSquareGyrobicupola.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandJohnsonSquareGyrobicupola.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
