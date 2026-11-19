import Polyhedra.Johnson.PentagonalDipyramidJ13.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Weak
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Claim0
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Claim1
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Claim2
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Claim3
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Claim4
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Claim5
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Claim6
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Claim7
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Claim8
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Claim9
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Claim10
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Claim11
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Claim12
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Claim13
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Claim14
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Claim15
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Claim16
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Claim17
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Claim18
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Claim19
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Claim20
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Claim21
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Claim22
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Claim23
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Root0
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Root1
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Root2
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Root3
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Root4
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Root5
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Root6
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Root7
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Root8
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Root9
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Root10
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `johnson/pentagonal-dipyramid-j13`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/nieuwland-exact-2026-11-10/rerun2/out/pentagonal-dipyramid-j13/exact.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Johnson.PentagonalDipyramidJ13.polyhedron` is `Θ` (`johnsonPentagonalDipyramidJ13_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonPentagonalDipyramidJ13

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

end Nieuwland.Certs.NieuwlandJohnsonPentagonalDipyramidJ13

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/pentagonal-dipyramid-j13`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem johnsonPentagonalDipyramidJ13_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandJohnsonPentagonalDipyramidJ13.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandJohnsonPentagonalDipyramidJ13.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandJohnsonPentagonalDipyramidJ13.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Johnson.PentagonalDipyramidJ13.polyhedron.nieuwland) : Johnson.PentagonalDipyramidJ13.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandJohnsonPentagonalDipyramidJ13.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonPentagonalDipyramidJ13.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandJohnsonPentagonalDipyramidJ13.far_field hc Nieuwland.Certs.NieuwlandJohnsonPentagonalDipyramidJ13.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Certs.NieuwlandJohnsonPentagonalDipyramidJ13

open Check Cert

/-- The claims' chart trees as texts, in the order of `claimBoxes`. -/
def claimTexts : List String :=
  [Lift.Claim0.data, Lift.Claim1.data, Lift.Claim2.data, Lift.Claim3.data, Lift.Claim4.data, Lift.Claim5.data, Lift.Claim6.data, Lift.Claim7.data, Lift.Claim8.data, Lift.Claim9.data, Lift.Claim10.data, Lift.Claim11.data, Lift.Claim12.data, Lift.Claim13.data, Lift.Claim14.data, Lift.Claim15.data, Lift.Claim16.data, Lift.Claim17.data, Lift.Claim18.data, Lift.Claim19.data, Lift.Claim20.data, Lift.Claim21.data, Lift.Claim22.data, Lift.Claim23.data]

/-- **The claims**: every claim's chart tree checks at the exact scale `Θ` on its box. -/
theorem claims_ok : List.Forall₂ (fun C t ↦ NativeS.checkT Lift.Theta Lift.points C t = true) claimBoxes claimTexts :=
  .cons Lift.Claim0.t_ok (.cons Lift.Claim1.t_ok (.cons Lift.Claim2.t_ok (.cons Lift.Claim3.t_ok (.cons Lift.Claim4.t_ok (.cons Lift.Claim5.t_ok (.cons Lift.Claim6.t_ok (.cons Lift.Claim7.t_ok (.cons Lift.Claim8.t_ok (.cons Lift.Claim9.t_ok (.cons Lift.Claim10.t_ok (.cons Lift.Claim11.t_ok (.cons Lift.Claim12.t_ok (.cons Lift.Claim13.t_ok (.cons Lift.Claim14.t_ok (.cons Lift.Claim15.t_ok (.cons Lift.Claim16.t_ok (.cons Lift.Claim17.t_ok (.cons Lift.Claim18.t_ok (.cons Lift.Claim19.t_ok (.cons Lift.Claim20.t_ok (.cons Lift.Claim21.t_ok (.cons Lift.Claim22.t_ok (.cons Lift.Claim23.t_ok (.nil))))))))))))))))))))))))

end Nieuwland.Certs.NieuwlandJohnsonPentagonalDipyramidJ13

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/pentagonal-dipyramid-j13`: the Nieuwland number.** From the far field at `theta`, the claims' chart trees at the exact scale `Θ ≥ theta` and the weak fit at `Θ` (`Check.Polyhedron.nieuwland_eq_of_lift_smul`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem johnsonPentagonalDipyramidJ13_nieuwland : Johnson.PentagonalDipyramidJ13.polyhedron.nieuwland = realRoot [518400, 0, -604800, 0, 120240, 0, -1800, 0, 1] 0 2 := by
  have hdim : Johnson.PentagonalDipyramidJ13.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandJohnsonPentagonalDipyramidJ13.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandJohnsonPentagonalDipyramidJ13.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandJohnsonPentagonalDipyramidJ13.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_lift_smul Nieuwland.Certs.NieuwlandJohnsonPentagonalDipyramidJ13.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonPentagonalDipyramidJ13.roots) (by decide +kernel) (θ := Nieuwland.Certs.NieuwlandJohnsonPentagonalDipyramidJ13.theta) (by decide +kernel) Nieuwland.Certs.NieuwlandJohnsonPentagonalDipyramidJ13.far_field (c := (((1 : ℕ) : ℝ) * ((38741760 : ℕ) : ℝ) ^ 3 / ((7504619839488000 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandJohnsonPentagonalDipyramidJ13.Lift.points_eq ((Check.Scale.re_lift _ _).trans Nieuwland.Certs.NieuwlandJohnsonPentagonalDipyramidJ13.Lift.thetaQ_re) Nieuwland.Certs.NieuwlandJohnsonPentagonalDipyramidJ13.Lift.theta_le (Check.noFitRot_of_texts Nieuwland.Certs.NieuwlandJohnsonPentagonalDipyramidJ13.claims_ok) Nieuwland.Certs.NieuwlandJohnsonPentagonalDipyramidJ13.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandJohnsonPentagonalDipyramidJ13.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
