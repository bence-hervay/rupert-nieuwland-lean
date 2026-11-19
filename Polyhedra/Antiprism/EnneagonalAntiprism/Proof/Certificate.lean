import Polyhedra.Antiprism.EnneagonalAntiprism.Proof.Points
import Polyhedra.Antiprism.EnneagonalAntiprism.Certificates.Touch
import Polyhedra.Antiprism.EnneagonalAntiprism.Certificates.Root0
import Polyhedra.Antiprism.EnneagonalAntiprism.Certificates.Root1
import Polyhedra.Antiprism.EnneagonalAntiprism.Certificates.Root2
import Polyhedra.Antiprism.EnneagonalAntiprism.Certificates.Root3
import Polyhedra.Antiprism.EnneagonalAntiprism.Certificates.Root4
import Polyhedra.Antiprism.EnneagonalAntiprism.Certificates.Root5
import Polyhedra.Antiprism.EnneagonalAntiprism.Certificates.Root6
import Polyhedra.Antiprism.EnneagonalAntiprism.Certificates.Root7
import Polyhedra.Antiprism.EnneagonalAntiprism.Certificates.Root8
import Polyhedra.Antiprism.EnneagonalAntiprism.Certificates.Root9
import Polyhedra.Antiprism.EnneagonalAntiprism.Certificates.Root10
import Polyhedra.Antiprism.EnneagonalAntiprism.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `prism/enneagonal-antiprism`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/nieuwland-exact-2026-11-16-prism/enneagonal-antiprism/far.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Antiprism.EnneagonalAntiprism.polyhedron` is `Θ` (`prismEnneagonalAntiprism_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandPrismEnneagonalAntiprism

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

end Nieuwland.Certs.NieuwlandPrismEnneagonalAntiprism

namespace Nieuwland.Polyhedra

/-- **The fixture `prism/enneagonal-antiprism`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem prismEnneagonalAntiprism_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandPrismEnneagonalAntiprism.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandPrismEnneagonalAntiprism.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandPrismEnneagonalAntiprism.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Antiprism.EnneagonalAntiprism.polyhedron.nieuwland) : Antiprism.EnneagonalAntiprism.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandPrismEnneagonalAntiprism.span_ok (roots := Nieuwland.Certs.NieuwlandPrismEnneagonalAntiprism.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandPrismEnneagonalAntiprism.far_field hc Nieuwland.Certs.NieuwlandPrismEnneagonalAntiprism.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Polyhedra

open Check

/-- **The fixture `prism/enneagonal-antiprism`: the Nieuwland number in root form.** The unknowns of a root's system are the pose `(s, t, x₁, x₂, x₃)` in its charts, the scale `l` (the unknown `5`) and one multiplier per contact; its equations are the contacts' slacks and the stationarity of `l` under them (`Root.Sys.eqs`). The system has exactly one zero `y` in its box (Krawczyk's test), and the Nieuwland number is the scale there: the far field at `theta`, the touch leaf and the weak fit at the root (`Root.nieuwland_eq_of_certOk_one`). -/
theorem prismEnneagonalAntiprism_nieuwland : ∃ y, ((Nieuwland.Certs.NieuwlandPrismEnneagonalAntiprism.touch0).kraw Nieuwland.Certs.NieuwlandPrismEnneagonalAntiprism.points).IsZero (Root.basisPar (ZTheta Nieuwland.Certs.NieuwlandPrismEnneagonalAntiprism.root)) y ∧ Antiprism.EnneagonalAntiprism.polyhedron.nieuwland = ((Nieuwland.Certs.NieuwlandPrismEnneagonalAntiprism.touch0).kraw Nieuwland.Certs.NieuwlandPrismEnneagonalAntiprism.points).env (Root.basisPar (ZTheta Nieuwland.Certs.NieuwlandPrismEnneagonalAntiprism.root)) y 5 :=
  Root.nieuwland_eq_of_certOk_one Nieuwland.Certs.NieuwlandPrismEnneagonalAntiprism.span_ok (roots := Nieuwland.Certs.NieuwlandPrismEnneagonalAntiprism.roots) (by decide +kernel) (by decide +kernel) Nieuwland.Certs.NieuwlandPrismEnneagonalAntiprism.far_field Nieuwland.Certs.NieuwlandPrismEnneagonalAntiprism.eq_smul (by norm_num) rfl Nieuwland.Certs.NieuwlandPrismEnneagonalAntiprism.touch_ok

/-- **The fixture `prism/enneagonal-antiprism`: the Nieuwland number to 40 decimals.** -/
theorem prismEnneagonalAntiprism_nieuwland_mem : Antiprism.EnneagonalAntiprism.polyhedron.nieuwland ∈ Set.Icc (((10174700937839692077058927197732232615392 : ℤ) : ℝ) / 10 ^ 40) (((10174700937839692077058927197732232615395 : ℤ) : ℝ) / 10 ^ 40) :=
  Root.nieuwland_mem_Icc_of_certOk Nieuwland.Certs.NieuwlandPrismEnneagonalAntiprism.span_ok (roots := Nieuwland.Certs.NieuwlandPrismEnneagonalAntiprism.roots) (by decide +kernel) (by decide +kernel) Nieuwland.Certs.NieuwlandPrismEnneagonalAntiprism.far_field Nieuwland.Certs.NieuwlandPrismEnneagonalAntiprism.eq_smul (by norm_num) rfl Nieuwland.Certs.NieuwlandPrismEnneagonalAntiprism.touch_ok Nieuwland.Certs.NieuwlandPrismEnneagonalAntiprism.touch_in

end Nieuwland.Polyhedra
