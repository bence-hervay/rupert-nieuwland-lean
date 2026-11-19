import Polyhedra.Johnson.Gyrobifastigium.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Johnson.Gyrobifastigium.Certificates.Weak
import Polyhedra.Johnson.Gyrobifastigium.Certificates.Claim0
import Polyhedra.Johnson.Gyrobifastigium.Certificates.Claim1
import Polyhedra.Johnson.Gyrobifastigium.Certificates.Root0
import Polyhedra.Johnson.Gyrobifastigium.Certificates.Root1
import Polyhedra.Johnson.Gyrobifastigium.Certificates.Root2
import Polyhedra.Johnson.Gyrobifastigium.Certificates.Root3
import Polyhedra.Johnson.Gyrobifastigium.Certificates.Root4
import Polyhedra.Johnson.Gyrobifastigium.Certificates.Root5
import Polyhedra.Johnson.Gyrobifastigium.Certificates.Root6
import Polyhedra.Johnson.Gyrobifastigium.Certificates.Root7
import Polyhedra.Johnson.Gyrobifastigium.Certificates.Root8
import Polyhedra.Johnson.Gyrobifastigium.Certificates.Root9
import Polyhedra.Johnson.Gyrobifastigium.Certificates.Root10
import Polyhedra.Johnson.Gyrobifastigium.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `johnson/gyrobifastigium`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/optima-rerun-2026-11-13/gyrobifastigium/exact.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Johnson.Gyrobifastigium.polyhedron` is `Θ` (`johnsonGyrobifastigium_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonGyrobifastigium

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

end Nieuwland.Certs.NieuwlandJohnsonGyrobifastigium

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/gyrobifastigium`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem johnsonGyrobifastigium_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandJohnsonGyrobifastigium.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandJohnsonGyrobifastigium.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandJohnsonGyrobifastigium.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Johnson.Gyrobifastigium.polyhedron.nieuwland) : Johnson.Gyrobifastigium.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandJohnsonGyrobifastigium.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonGyrobifastigium.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandJohnsonGyrobifastigium.far_field hc Nieuwland.Certs.NieuwlandJohnsonGyrobifastigium.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Certs.NieuwlandJohnsonGyrobifastigium

open Check Cert

/-- The claims' chart trees as texts, in the order of `claimBoxes`. -/
def claimTexts : List String :=
  [Lift.Claim0.data, Lift.Claim1.data]

/-- **The claims**: every claim's chart tree checks at the exact scale `Θ` on its box. -/
theorem claims_ok : List.Forall₂ (fun C t ↦ NativeS.checkT Lift.Theta Lift.points C t = true) claimBoxes claimTexts :=
  .cons Lift.Claim0.t_ok (.cons Lift.Claim1.t_ok (.nil))

end Nieuwland.Certs.NieuwlandJohnsonGyrobifastigium

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/gyrobifastigium`: the Nieuwland number.** From the far field at `theta`, the claims' chart trees at the exact scale `Θ ≥ theta` and the weak fit at `Θ` (`Check.Polyhedron.nieuwland_eq_of_lift_smul`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem johnsonGyrobifastigium_nieuwland : Johnson.Gyrobifastigium.polyhedron.nieuwland = polyEval [1530602157077/2653474728392, 8929870101623/5306949456784, -2901121835601/2653474728392, -4936417023969/5306949456784, 1200863950703/2653474728392, 1192644734129/5306949456784, -117443605803/2653474728392, -100642953559/5306949456784] (realRoot [33889/961, -31184/961, -73084/961, 58128/961, 35494/961, -24944/961, -10428/961, 80/31, 1] 0 2) := by
  have hdim : Johnson.Gyrobifastigium.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandJohnsonGyrobifastigium.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandJohnsonGyrobifastigium.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandJohnsonGyrobifastigium.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_lift_smul Nieuwland.Certs.NieuwlandJohnsonGyrobifastigium.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonGyrobifastigium.roots) (by decide +kernel) (θ := Nieuwland.Certs.NieuwlandJohnsonGyrobifastigium.theta) (by decide +kernel) Nieuwland.Certs.NieuwlandJohnsonGyrobifastigium.far_field (c := (((1 : ℕ) : ℝ) * ((151933457347637110384 : ℕ) : ℝ) / ((1 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandJohnsonGyrobifastigium.Lift.points_eq ((Check.Scale.re_lift _ _).trans Nieuwland.Certs.NieuwlandJohnsonGyrobifastigium.Lift.thetaQ_re) Nieuwland.Certs.NieuwlandJohnsonGyrobifastigium.Lift.theta_le (Check.noFitRot_of_texts Nieuwland.Certs.NieuwlandJohnsonGyrobifastigium.claims_ok) Nieuwland.Certs.NieuwlandJohnsonGyrobifastigium.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandJohnsonGyrobifastigium.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
