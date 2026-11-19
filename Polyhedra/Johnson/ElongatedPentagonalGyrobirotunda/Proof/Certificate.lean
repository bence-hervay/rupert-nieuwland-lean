import Polyhedra.Johnson.ElongatedPentagonalGyrobirotunda.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Johnson.ElongatedPentagonalGyrobirotunda.Certificates.Weak
import Polyhedra.Johnson.ElongatedPentagonalGyrobirotunda.Certificates.Claim0
import Polyhedra.Johnson.ElongatedPentagonalGyrobirotunda.Certificates.Claim1
import Polyhedra.Johnson.ElongatedPentagonalGyrobirotunda.Certificates.Root0
import Polyhedra.Johnson.ElongatedPentagonalGyrobirotunda.Certificates.Root1
import Polyhedra.Johnson.ElongatedPentagonalGyrobirotunda.Certificates.Root2
import Polyhedra.Johnson.ElongatedPentagonalGyrobirotunda.Certificates.Root3
import Polyhedra.Johnson.ElongatedPentagonalGyrobirotunda.Certificates.Root4
import Polyhedra.Johnson.ElongatedPentagonalGyrobirotunda.Certificates.Root5
import Polyhedra.Johnson.ElongatedPentagonalGyrobirotunda.Certificates.Root6
import Polyhedra.Johnson.ElongatedPentagonalGyrobirotunda.Certificates.Root7
import Polyhedra.Johnson.ElongatedPentagonalGyrobirotunda.Certificates.Root8
import Polyhedra.Johnson.ElongatedPentagonalGyrobirotunda.Certificates.Root9
import Polyhedra.Johnson.ElongatedPentagonalGyrobirotunda.Certificates.Root10
import Polyhedra.Johnson.ElongatedPentagonalGyrobirotunda.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `johnson/elongated-pentagonal-gyrobirotunda`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/optima-rerun-2026-11-13/elongated-pentagonal-gyrobirotunda/exact.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Johnson.ElongatedPentagonalGyrobirotunda.polyhedron` is `Θ` (`johnsonElongatedPentagonalGyrobirotunda_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalGyrobirotunda

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

end Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalGyrobirotunda

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/elongated-pentagonal-gyrobirotunda`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem johnsonElongatedPentagonalGyrobirotunda_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalGyrobirotunda.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalGyrobirotunda.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalGyrobirotunda.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Johnson.ElongatedPentagonalGyrobirotunda.polyhedron.nieuwland) : Johnson.ElongatedPentagonalGyrobirotunda.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalGyrobirotunda.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalGyrobirotunda.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalGyrobirotunda.far_field hc Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalGyrobirotunda.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalGyrobirotunda

open Check Cert

/-- The claims' chart trees as texts, in the order of `claimBoxes`. -/
def claimTexts : List String :=
  [Lift.Claim0.data, Lift.Claim1.data]

/-- **The claims**: every claim's chart tree checks at the exact scale `Θ` on its box. -/
theorem claims_ok : List.Forall₂ (fun C t ↦ NativeS.checkT Lift.Theta Lift.points C t = true) claimBoxes claimTexts :=
  .cons Lift.Claim0.t_ok (.cons Lift.Claim1.t_ok (.nil))

end Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalGyrobirotunda

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/elongated-pentagonal-gyrobirotunda`: the Nieuwland number.** From the far field at `theta`, the claims' chart trees at the exact scale `Θ ≥ theta` and the weak fit at `Θ` (`Check.Polyhedron.nieuwland_eq_of_lift_smul`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem johnsonElongatedPentagonalGyrobirotunda_nieuwland : Johnson.ElongatedPentagonalGyrobirotunda.polyhedron.nieuwland = realRoot [33181/20480, 91/64, -565/64, -475/64, 791/64, 71/8, -25/4, -3, 1] 1 (5/4) := by
  have hdim : Johnson.ElongatedPentagonalGyrobirotunda.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalGyrobirotunda.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalGyrobirotunda.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalGyrobirotunda.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_lift_smul Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalGyrobirotunda.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalGyrobirotunda.roots) (by decide +kernel) (θ := Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalGyrobirotunda.theta) (by decide +kernel) Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalGyrobirotunda.far_field (c := (((1 : ℕ) : ℝ) * ((12533602374973790000 : ℕ) : ℝ) ^ 3 / ((785455942469743145942515934820500000000 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalGyrobirotunda.Lift.points_eq ((Check.Scale.re_lift _ _).trans Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalGyrobirotunda.Lift.thetaQ_re) Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalGyrobirotunda.Lift.theta_le (Check.noFitRot_of_texts Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalGyrobirotunda.claims_ok) Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalGyrobirotunda.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalGyrobirotunda.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
