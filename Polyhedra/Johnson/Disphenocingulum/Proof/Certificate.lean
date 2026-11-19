import Polyhedra.Johnson.Disphenocingulum.Proof.Points
import Polyhedra.Johnson.Disphenocingulum.Certificates.Touch
import Polyhedra.Johnson.Disphenocingulum.Certificates.Root0
import Polyhedra.Johnson.Disphenocingulum.Certificates.Root1
import Polyhedra.Johnson.Disphenocingulum.Certificates.Root2
import Polyhedra.Johnson.Disphenocingulum.Certificates.Root3
import Polyhedra.Johnson.Disphenocingulum.Certificates.Root4
import Polyhedra.Johnson.Disphenocingulum.Certificates.Root5
import Polyhedra.Johnson.Disphenocingulum.Certificates.Root6
import Polyhedra.Johnson.Disphenocingulum.Certificates.Root7
import Polyhedra.Johnson.Disphenocingulum.Certificates.Root8
import Polyhedra.Johnson.Disphenocingulum.Certificates.Root9
import Polyhedra.Johnson.Disphenocingulum.Certificates.Root10
import Polyhedra.Johnson.Disphenocingulum.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `johnson/disphenocingulum`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/d2c-2026-11-13/disphenocingulum/far.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Johnson.Disphenocingulum.polyhedron` is `Θ` (`johnsonDisphenocingulum_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonDisphenocingulum

open Check Cert

/-- The roots of the cover. -/
def roots : List ChartBox :=
  [Root0.box, Root1.box, Root2.box, Root3.box, Root4.box, Root5.box, Root6.box, Root7.box, Root8.box, Root9.box, Root10.box, Root11.box]

/-- **The far field**: every pose of every root is settled at `theta` or lies in a claim box. -/
theorem far_field : roots.Forall fun B ↦ ∀ p ∈ B.poses, SettledS points symm theta.re p ∨ ∃ C ∈ claimBoxes, p ∈ C.poses := by
  simp only [roots, List.Forall]; exact ⟨Root0.settled, Root1.settled, Root2.settled, Root3.settled, Root4.settled, Root5.settled, Root6.settled, Root7.settled, Root8.settled, Root9.settled, Root10.settled, Root11.settled⟩

/-- **The certificate with the claims as hypotheses**: for `Θ ≥ theta` with no fit at `Θ` in the claim boxes, the polyhedron of Lean's points scaled by `Θ` does not fit through it. -/
theorem not_fitsThrough_of_claims {Θ : ℝ} (hle : theta.re ≤ Θ) (hc : ∀ C ∈ claimBoxes, (Polyhedron.ofPoints points).NoFitRot C.poses (Θ • 1)) : ¬ ((Polyhedron.ofPoints points).smul Θ).FitsThrough (Polyhedron.ofPoints points) :=
  Polyhedron.not_fitsThrough_smul_of_claims span_ok (roots := roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle far_field hc

end Nieuwland.Certs.NieuwlandJohnsonDisphenocingulum

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/disphenocingulum`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem johnsonDisphenocingulum_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandJohnsonDisphenocingulum.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandJohnsonDisphenocingulum.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandJohnsonDisphenocingulum.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Johnson.Disphenocingulum.polyhedron.nieuwland) : Johnson.Disphenocingulum.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandJohnsonDisphenocingulum.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonDisphenocingulum.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandJohnsonDisphenocingulum.far_field hc Nieuwland.Certs.NieuwlandJohnsonDisphenocingulum.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Polyhedra

open Check

/-- **The fixture `johnson/disphenocingulum`: the Nieuwland number in root form.** The unknowns of a root's system are the pose `(s, t, x₁, x₂, x₃)` in its charts, the translation `(y₁, y₂)` of the plug's shadow, the scale `l` (the unknown `7`) and one multiplier per contact; its equations are the contacts' slacks and the stationarity of `l` under them (`Root.Sys.eqs`). The system has exactly one zero `y` in its box (Krawczyk's test), and the Nieuwland number is the scale there: the far field at `theta`, the touch leaf and the weak fit at the root (`Root.nieuwland_eq_of_certOk_one`). -/
theorem johnsonDisphenocingulum_nieuwland : ∃ y, ((Nieuwland.Certs.NieuwlandJohnsonDisphenocingulum.touch0).kraw Nieuwland.Certs.NieuwlandJohnsonDisphenocingulum.points).IsZero (Root.basisPar (ZTheta Nieuwland.Certs.NieuwlandJohnsonDisphenocingulum.root)) y ∧ Johnson.Disphenocingulum.polyhedron.nieuwland = ((Nieuwland.Certs.NieuwlandJohnsonDisphenocingulum.touch0).kraw Nieuwland.Certs.NieuwlandJohnsonDisphenocingulum.points).env (Root.basisPar (ZTheta Nieuwland.Certs.NieuwlandJohnsonDisphenocingulum.root)) y 7 :=
  Root.nieuwland_eq_of_certOk_one Nieuwland.Certs.NieuwlandJohnsonDisphenocingulum.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonDisphenocingulum.roots) (by decide +kernel) (by decide +kernel) Nieuwland.Certs.NieuwlandJohnsonDisphenocingulum.far_field Nieuwland.Certs.NieuwlandJohnsonDisphenocingulum.eq_smul (by norm_num) rfl Nieuwland.Certs.NieuwlandJohnsonDisphenocingulum.touch_ok

/-- **The fixture `johnson/disphenocingulum`: the Nieuwland number to 40 decimals.** -/
theorem johnsonDisphenocingulum_nieuwland_mem : Johnson.Disphenocingulum.polyhedron.nieuwland ∈ Set.Icc (((10197539439153241304436257144961111225080 : ℤ) : ℝ) / 10 ^ 40) (((10197539439153241304436257144961111225083 : ℤ) : ℝ) / 10 ^ 40) :=
  Root.nieuwland_mem_Icc_of_certOk Nieuwland.Certs.NieuwlandJohnsonDisphenocingulum.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonDisphenocingulum.roots) (by decide +kernel) (by decide +kernel) Nieuwland.Certs.NieuwlandJohnsonDisphenocingulum.far_field Nieuwland.Certs.NieuwlandJohnsonDisphenocingulum.eq_smul (by norm_num) rfl Nieuwland.Certs.NieuwlandJohnsonDisphenocingulum.touch_ok Nieuwland.Certs.NieuwlandJohnsonDisphenocingulum.touch_in

end Nieuwland.Polyhedra
