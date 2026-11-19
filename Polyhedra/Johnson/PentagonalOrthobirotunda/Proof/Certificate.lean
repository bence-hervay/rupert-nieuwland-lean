import Polyhedra.Johnson.PentagonalOrthobirotunda.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Weak
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim0
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim1
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim2
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim3
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim4
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim5
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim6
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim7
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim8
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim9
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim10
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim11
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim12
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim13
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim14
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim15
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim16
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim17
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim18
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim19
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim20
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim21
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim22
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim23
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim24
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim25
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim26
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim27
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim28
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim29
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim30
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim31
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim32
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim33
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim34
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim35
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim36
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim37
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim38
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Claim39
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Root0
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Root1
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Root2
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Root3
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Root4
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Root5
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Root6
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Root7
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Root8
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Root9
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Root10
import Polyhedra.Johnson.PentagonalOrthobirotunda.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `johnson/pentagonal-orthobirotunda`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/optima-rerun-2026-11-13/pentagonal-orthobirotunda/exact.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Johnson.PentagonalOrthobirotunda.polyhedron` is `Θ` (`johnsonPentagonalOrthobirotunda_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobirotunda

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

end Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobirotunda

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/pentagonal-orthobirotunda`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem johnsonPentagonalOrthobirotunda_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobirotunda.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobirotunda.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobirotunda.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Johnson.PentagonalOrthobirotunda.polyhedron.nieuwland) : Johnson.PentagonalOrthobirotunda.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobirotunda.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobirotunda.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobirotunda.far_field hc Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobirotunda.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobirotunda

open Check Cert

/-- The claims' chart trees as texts, in the order of `claimBoxes`. -/
def claimTexts : List String :=
  [Lift.Claim0.data, Lift.Claim1.data, Lift.Claim2.data, Lift.Claim3.data, Lift.Claim4.data, Lift.Claim5.data, Lift.Claim6.data, Lift.Claim7.data, Lift.Claim8.data, Lift.Claim9.data, Lift.Claim10.data, Lift.Claim11.data, Lift.Claim12.data, Lift.Claim13.data, Lift.Claim14.data, Lift.Claim15.data, Lift.Claim16.data, Lift.Claim17.data, Lift.Claim18.data, Lift.Claim19.data, Lift.Claim20.data, Lift.Claim21.data, Lift.Claim22.data, Lift.Claim23.data, Lift.Claim24.data, Lift.Claim25.data, Lift.Claim26.data, Lift.Claim27.data, Lift.Claim28.data, Lift.Claim29.data, Lift.Claim30.data, Lift.Claim31.data, Lift.Claim32.data, Lift.Claim33.data, Lift.Claim34.data, Lift.Claim35.data, Lift.Claim36.data, Lift.Claim37.data, Lift.Claim38.data, Lift.Claim39.data]

/-- **The claims**: every claim's chart tree checks at the exact scale `Θ` on its box. -/
theorem claims_ok : List.Forall₂ (fun C t ↦ NativeS.checkT Lift.Theta Lift.points C t = true) claimBoxes claimTexts :=
  .cons Lift.Claim0.t_ok (.cons Lift.Claim1.t_ok (.cons Lift.Claim2.t_ok (.cons Lift.Claim3.t_ok (.cons Lift.Claim4.t_ok (.cons Lift.Claim5.t_ok (.cons Lift.Claim6.t_ok (.cons Lift.Claim7.t_ok (.cons Lift.Claim8.t_ok (.cons Lift.Claim9.t_ok (.cons Lift.Claim10.t_ok (.cons Lift.Claim11.t_ok (.cons Lift.Claim12.t_ok (.cons Lift.Claim13.t_ok (.cons Lift.Claim14.t_ok (.cons Lift.Claim15.t_ok (.cons Lift.Claim16.t_ok (.cons Lift.Claim17.t_ok (.cons Lift.Claim18.t_ok (.cons Lift.Claim19.t_ok (.cons Lift.Claim20.t_ok (.cons Lift.Claim21.t_ok (.cons Lift.Claim22.t_ok (.cons Lift.Claim23.t_ok (.cons Lift.Claim24.t_ok (.cons Lift.Claim25.t_ok (.cons Lift.Claim26.t_ok (.cons Lift.Claim27.t_ok (.cons Lift.Claim28.t_ok (.cons Lift.Claim29.t_ok (.cons Lift.Claim30.t_ok (.cons Lift.Claim31.t_ok (.cons Lift.Claim32.t_ok (.cons Lift.Claim33.t_ok (.cons Lift.Claim34.t_ok (.cons Lift.Claim35.t_ok (.cons Lift.Claim36.t_ok (.cons Lift.Claim37.t_ok (.cons Lift.Claim38.t_ok (.cons Lift.Claim39.t_ok (.nil))))))))))))))))))))))))))))))))))))))))

end Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobirotunda

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/pentagonal-orthobirotunda`: the Nieuwland number.** From the far field at `theta`, the claims' chart trees at the exact scale `Θ ≥ theta` and the weak fit at `Θ` (`Check.Polyhedron.nieuwland_eq_of_lift_smul`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem johnsonPentagonalOrthobirotunda_nieuwland : Johnson.PentagonalOrthobirotunda.polyhedron.nieuwland = realRoot [15625/92416, 0, -3125/1444, 0, 424625/11552, 0, -99875/722, 0, 1323275/5776, 0, -70950/361, 0, 63625/722, 0, -6540/361, 0, 1] 1 (129/128) := by
  have hdim : Johnson.PentagonalOrthobirotunda.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobirotunda.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobirotunda.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobirotunda.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_lift_smul Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobirotunda.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobirotunda.roots) (by decide +kernel) (θ := Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobirotunda.theta) (by decide +kernel) Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobirotunda.far_field (c := (((1 : ℕ) : ℝ) * ((199336384830904352701805155520000 : ℕ) : ℝ) ^ 3 / ((198674971587271974626394916433173499038700611972256932352000000000 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobirotunda.Lift.points_eq ((Check.Scale.re_lift _ _).trans Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobirotunda.Lift.thetaQ_re) Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobirotunda.Lift.theta_le (Check.noFitRot_of_texts Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobirotunda.claims_ok) Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobirotunda.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandJohnsonPentagonalOrthobirotunda.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
