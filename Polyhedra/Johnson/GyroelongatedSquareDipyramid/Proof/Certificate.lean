import Polyhedra.Johnson.GyroelongatedSquareDipyramid.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Johnson.GyroelongatedSquareDipyramid.Certificates.Weak
import Polyhedra.Johnson.GyroelongatedSquareDipyramid.Certificates.Claim0
import Polyhedra.Johnson.GyroelongatedSquareDipyramid.Certificates.Claim1
import Polyhedra.Johnson.GyroelongatedSquareDipyramid.Certificates.Root0
import Polyhedra.Johnson.GyroelongatedSquareDipyramid.Certificates.Root1
import Polyhedra.Johnson.GyroelongatedSquareDipyramid.Certificates.Root2
import Polyhedra.Johnson.GyroelongatedSquareDipyramid.Certificates.Root3
import Polyhedra.Johnson.GyroelongatedSquareDipyramid.Certificates.Root4
import Polyhedra.Johnson.GyroelongatedSquareDipyramid.Certificates.Root5
import Polyhedra.Johnson.GyroelongatedSquareDipyramid.Certificates.Root6
import Polyhedra.Johnson.GyroelongatedSquareDipyramid.Certificates.Root7
import Polyhedra.Johnson.GyroelongatedSquareDipyramid.Certificates.Root8
import Polyhedra.Johnson.GyroelongatedSquareDipyramid.Certificates.Root9
import Polyhedra.Johnson.GyroelongatedSquareDipyramid.Certificates.Root10
import Polyhedra.Johnson.GyroelongatedSquareDipyramid.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `johnson/gyroelongated-square-dipyramid`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/nieuwland-exact-2026-11-10/rerun2/out/gyroelongated-square-dipyramid/exact.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Johnson.GyroelongatedSquareDipyramid.polyhedron` is `Θ` (`johnsonGyroelongatedSquareDipyramid_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonGyroelongatedSquareDipyramid

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

end Nieuwland.Certs.NieuwlandJohnsonGyroelongatedSquareDipyramid

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/gyroelongated-square-dipyramid`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem johnsonGyroelongatedSquareDipyramid_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandJohnsonGyroelongatedSquareDipyramid.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandJohnsonGyroelongatedSquareDipyramid.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandJohnsonGyroelongatedSquareDipyramid.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Johnson.GyroelongatedSquareDipyramid.polyhedron.nieuwland) : Johnson.GyroelongatedSquareDipyramid.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandJohnsonGyroelongatedSquareDipyramid.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonGyroelongatedSquareDipyramid.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandJohnsonGyroelongatedSquareDipyramid.far_field hc Nieuwland.Certs.NieuwlandJohnsonGyroelongatedSquareDipyramid.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Certs.NieuwlandJohnsonGyroelongatedSquareDipyramid

open Check Cert

/-- The claims' chart trees as texts, in the order of `claimBoxes`. -/
def claimTexts : List String :=
  [Lift.Claim0.data, Lift.Claim1.data]

/-- **The claims**: every claim's chart tree checks at the exact scale `Θ` on its box. -/
theorem claims_ok : List.Forall₂ (fun C t ↦ NativeS.checkT Lift.Theta Lift.points C t = true) claimBoxes claimTexts :=
  .cons Lift.Claim0.t_ok (.cons Lift.Claim1.t_ok (.nil))

end Nieuwland.Certs.NieuwlandJohnsonGyroelongatedSquareDipyramid

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/gyroelongated-square-dipyramid`: the Nieuwland number.** From the far field at `theta`, the claims' chart trees at the exact scale `Θ ≥ theta` and the weak fit at `Θ` (`Check.Polyhedron.nieuwland_eq_of_lift_smul`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem johnsonGyroelongatedSquareDipyramid_nieuwland : Johnson.GyroelongatedSquareDipyramid.polyhedron.nieuwland = polyEval [0, -13952155564720885828177381836529640855/1022708567003472146543408854250712106368, 0, -25074260163065685104886434605664537456/7989910679714626144870381673833688331, 0, -366365533212850211454681553692597056975/31959642718858504579481526695334753324, 0, 51606381585265662815810044862935346672/2663303559904875381623460557944562777, 0, 535705069456119137228068474310651400/2663303559904875381623460557944562777, 0, -40084769515271562386351335281121457152/7989910679714626144870381673833688331, 0, 3324993512151693085308453946598368000/7989910679714626144870381673833688331, 0, 1800912347391362183784275019783159808/7989910679714626144870381673833688331] (realRoot [1502880289/2517630976, 0, 44836161/9834496, 0, -167494001/19668992, 0, -17139687/307328, 0, 104369987/1229312, 0, 20619/9604, 0, -428305/19208, 0, 88/49, 0, 1] (-3/4) (-1/2)) := by
  have hdim : Johnson.GyroelongatedSquareDipyramid.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandJohnsonGyroelongatedSquareDipyramid.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandJohnsonGyroelongatedSquareDipyramid.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandJohnsonGyroelongatedSquareDipyramid.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_lift_smul Nieuwland.Certs.NieuwlandJohnsonGyroelongatedSquareDipyramid.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonGyroelongatedSquareDipyramid.roots) (by decide +kernel) (θ := Nieuwland.Certs.NieuwlandJohnsonGyroelongatedSquareDipyramid.theta) (by decide +kernel) Nieuwland.Certs.NieuwlandJohnsonGyroelongatedSquareDipyramid.far_field (c := (((1 : ℕ) : ℝ) * ((1035381247913560498798539437001176204654237183705088 : ℕ) : ℝ) ^ 3 / ((1072014328531041826746540313086947694599796150862189326685731420965689740323783611194269063271357087744 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandJohnsonGyroelongatedSquareDipyramid.Lift.points_eq ((Check.Scale.re_lift _ _).trans Nieuwland.Certs.NieuwlandJohnsonGyroelongatedSquareDipyramid.Lift.thetaQ_re) Nieuwland.Certs.NieuwlandJohnsonGyroelongatedSquareDipyramid.Lift.theta_le (Check.noFitRot_of_texts Nieuwland.Certs.NieuwlandJohnsonGyroelongatedSquareDipyramid.claims_ok) Nieuwland.Certs.NieuwlandJohnsonGyroelongatedSquareDipyramid.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandJohnsonGyroelongatedSquareDipyramid.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
