import Polyhedra.Johnson.ParabiaugmentedTruncatedDodecahedron.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Johnson.ParabiaugmentedTruncatedDodecahedron.Certificates.Weak
import Polyhedra.Johnson.ParabiaugmentedTruncatedDodecahedron.Certificates.Root0
import Polyhedra.Johnson.ParabiaugmentedTruncatedDodecahedron.Certificates.Root1
import Polyhedra.Johnson.ParabiaugmentedTruncatedDodecahedron.Certificates.Root2
import Polyhedra.Johnson.ParabiaugmentedTruncatedDodecahedron.Certificates.Root3
import Polyhedra.Johnson.ParabiaugmentedTruncatedDodecahedron.Certificates.Root4
import Polyhedra.Johnson.ParabiaugmentedTruncatedDodecahedron.Certificates.Root5
import Polyhedra.Johnson.ParabiaugmentedTruncatedDodecahedron.Certificates.Root6
import Polyhedra.Johnson.ParabiaugmentedTruncatedDodecahedron.Certificates.Root7
import Polyhedra.Johnson.ParabiaugmentedTruncatedDodecahedron.Certificates.Root8
import Polyhedra.Johnson.ParabiaugmentedTruncatedDodecahedron.Certificates.Root9
import Polyhedra.Johnson.ParabiaugmentedTruncatedDodecahedron.Certificates.Root10
import Polyhedra.Johnson.ParabiaugmentedTruncatedDodecahedron.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `johnson/parabiaugmented-truncated-dodecahedron`: an exact Nieuwland number from a cover at the exact scale

The exact certificate `gs://main-69696-data/noperts-results/jch2-2026-11-15/parabiaugmented-truncated-dodecahedron/exact.jsonl`, exported by `code/lean-export scaled --fit`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the exact scale `Θ` over the lift (`Lift.Root<k>.settled`: chord pairs, supports and excluded leaves), so the lift's polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough`); with the weak fit at `Θ` (`Lift.weak_check`) the Nieuwland number of `Johnson.ParabiaugmentedTruncatedDodecahedron.polyhedron` is `Θ`.
-/

namespace Nieuwland.Certs.NieuwlandJohnsonParabiaugmentedTruncatedDodecahedron

open Check Cert

/-- The roots of the cover. -/
def roots : List ChartBox :=
  [Lift.Root0.box, Lift.Root1.box, Lift.Root2.box, Lift.Root3.box, Lift.Root4.box, Lift.Root5.box, Lift.Root6.box, Lift.Root7.box, Lift.Root8.box, Lift.Root9.box, Lift.Root10.box, Lift.Root11.box]

/-- **The certificate**: the lift's polyhedron scaled by `Θ` does not fit through it. -/
theorem not_fitsThrough : ¬ ((Polyhedron.ofPoints Lift.points).smul Lift.Theta.re).FitsThrough (Polyhedron.ofPoints Lift.points) :=
  Polyhedron.not_fitsThrough_smul_of_roots Lift.span_ok (roots := roots) (by decide +kernel) (by simp only [roots, List.Forall]; exact ⟨Lift.Root0.settled, Lift.Root1.settled, Lift.Root2.settled, Lift.Root3.settled, Lift.Root4.settled, Lift.Root5.settled, Lift.Root6.settled, Lift.Root7.settled, Lift.Root8.settled, Lift.Root9.settled, Lift.Root10.settled, Lift.Root11.settled⟩)

end Nieuwland.Certs.NieuwlandJohnsonParabiaugmentedTruncatedDodecahedron

namespace Nieuwland.Polyhedra

open Check

/-- **The fixture `johnson/parabiaugmented-truncated-dodecahedron`: the Nieuwland number.** From the cover at the exact scale `Θ` and the weak fit there (`Check.Polyhedron.nieuwland_eq_of_not_fitsThrough_lift`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem johnsonParabiaugmentedTruncatedDodecahedron_nieuwland : Johnson.ParabiaugmentedTruncatedDodecahedron.polyhedron.nieuwland = realRoot [61/25, 0, -17/5, 0, 1] (2284382542877589/2251799813685248) (2284451262354325/2251799813685248) := by
  have hdim : Johnson.ParabiaugmentedTruncatedDodecahedron.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandJohnsonParabiaugmentedTruncatedDodecahedron.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandJohnsonParabiaugmentedTruncatedDodecahedron.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandJohnsonParabiaugmentedTruncatedDodecahedron.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_not_fitsThrough_lift (c := (((1 : ℕ) : ℝ) * ((15 : ℕ) : ℝ) / ((2 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandJohnsonParabiaugmentedTruncatedDodecahedron.Lift.points_eq (Check.Scale.re_nonneg_of_ok (by decide +kernel)) Nieuwland.Certs.NieuwlandJohnsonParabiaugmentedTruncatedDodecahedron.not_fitsThrough Nieuwland.Certs.NieuwlandJohnsonParabiaugmentedTruncatedDodecahedron.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandJohnsonParabiaugmentedTruncatedDodecahedron.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
