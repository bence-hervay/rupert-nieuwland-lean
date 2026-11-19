import Polyhedra.Johnson.PentagonalRotunda.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Weak
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Claim0
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Claim1
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Claim2
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Claim3
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Claim4
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Claim5
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Claim6
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Claim7
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Claim8
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Claim9
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Claim10
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Claim11
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Claim12
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Claim13
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Claim14
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Claim15
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Claim16
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Claim17
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Claim18
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Claim19
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Root0
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Root1
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Root2
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Root3
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Root4
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Root5
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Root6
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Root7
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Root8
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Root9
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Root10
import Polyhedra.Johnson.PentagonalRotunda.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `johnson/pentagonal-rotunda`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/optima-rerun-2026-11-13/pentagonal-rotunda/exact.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Johnson.PentagonalRotunda.polyhedron` is `Θ` (`johnsonPentagonalRotunda_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonPentagonalRotunda

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

end Nieuwland.Certs.NieuwlandJohnsonPentagonalRotunda

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/pentagonal-rotunda`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem johnsonPentagonalRotunda_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandJohnsonPentagonalRotunda.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandJohnsonPentagonalRotunda.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandJohnsonPentagonalRotunda.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Johnson.PentagonalRotunda.polyhedron.nieuwland) : Johnson.PentagonalRotunda.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandJohnsonPentagonalRotunda.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonPentagonalRotunda.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandJohnsonPentagonalRotunda.far_field hc Nieuwland.Certs.NieuwlandJohnsonPentagonalRotunda.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Certs.NieuwlandJohnsonPentagonalRotunda

open Check Cert

/-- The claims' chart trees as texts, in the order of `claimBoxes`. -/
def claimTexts : List String :=
  [Lift.Claim0.data, Lift.Claim1.data, Lift.Claim2.data, Lift.Claim3.data, Lift.Claim4.data, Lift.Claim5.data, Lift.Claim6.data, Lift.Claim7.data, Lift.Claim8.data, Lift.Claim9.data, Lift.Claim10.data, Lift.Claim11.data, Lift.Claim12.data, Lift.Claim13.data, Lift.Claim14.data, Lift.Claim15.data, Lift.Claim16.data, Lift.Claim17.data, Lift.Claim18.data, Lift.Claim19.data]

/-- **The claims**: every claim's chart tree checks at the exact scale `Θ` on its box. -/
theorem claims_ok : List.Forall₂ (fun C t ↦ NativeS.checkT Lift.Theta Lift.points C t = true) claimBoxes claimTexts :=
  .cons Lift.Claim0.t_ok (.cons Lift.Claim1.t_ok (.cons Lift.Claim2.t_ok (.cons Lift.Claim3.t_ok (.cons Lift.Claim4.t_ok (.cons Lift.Claim5.t_ok (.cons Lift.Claim6.t_ok (.cons Lift.Claim7.t_ok (.cons Lift.Claim8.t_ok (.cons Lift.Claim9.t_ok (.cons Lift.Claim10.t_ok (.cons Lift.Claim11.t_ok (.cons Lift.Claim12.t_ok (.cons Lift.Claim13.t_ok (.cons Lift.Claim14.t_ok (.cons Lift.Claim15.t_ok (.cons Lift.Claim16.t_ok (.cons Lift.Claim17.t_ok (.cons Lift.Claim18.t_ok (.cons Lift.Claim19.t_ok (.nil))))))))))))))))))))

end Nieuwland.Certs.NieuwlandJohnsonPentagonalRotunda

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/pentagonal-rotunda`: the Nieuwland number.** From the far field at `theta`, the claims' chart trees at the exact scale `Θ ≥ theta` and the weak fit at `Θ` (`Check.Polyhedron.nieuwland_eq_of_lift_smul`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem johnsonPentagonalRotunda_nieuwland : Johnson.PentagonalRotunda.polyhedron.nieuwland = realRoot [1952000/6241, 0, -4240000/6241, 0, 2930800/6241, 0, -638840/6241, 0, 1] 1 (17/16) := by
  have hdim : Johnson.PentagonalRotunda.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandJohnsonPentagonalRotunda.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandJohnsonPentagonalRotunda.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandJohnsonPentagonalRotunda.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_lift_smul Nieuwland.Certs.NieuwlandJohnsonPentagonalRotunda.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonPentagonalRotunda.roots) (by decide +kernel) (θ := Nieuwland.Certs.NieuwlandJohnsonPentagonalRotunda.theta) (by decide +kernel) Nieuwland.Certs.NieuwlandJohnsonPentagonalRotunda.far_field (c := (((1 : ℕ) : ℝ) * ((57828534015345680 : ℕ) : ℝ) / ((1 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandJohnsonPentagonalRotunda.Lift.points_eq ((Check.Scale.re_lift _ _).trans Nieuwland.Certs.NieuwlandJohnsonPentagonalRotunda.Lift.thetaQ_re) Nieuwland.Certs.NieuwlandJohnsonPentagonalRotunda.Lift.theta_le (Check.noFitRot_of_texts Nieuwland.Certs.NieuwlandJohnsonPentagonalRotunda.claims_ok) Nieuwland.Certs.NieuwlandJohnsonPentagonalRotunda.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandJohnsonPentagonalRotunda.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
