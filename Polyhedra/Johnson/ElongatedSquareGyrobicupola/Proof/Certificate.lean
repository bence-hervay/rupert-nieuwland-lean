import Polyhedra.Johnson.ElongatedSquareGyrobicupola.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Johnson.ElongatedSquareGyrobicupola.Certificates.Weak
import Polyhedra.Johnson.ElongatedSquareGyrobicupola.Certificates.Claim0
import Polyhedra.Johnson.ElongatedSquareGyrobicupola.Certificates.Claim1
import Polyhedra.Johnson.ElongatedSquareGyrobicupola.Certificates.Root0
import Polyhedra.Johnson.ElongatedSquareGyrobicupola.Certificates.Root1
import Polyhedra.Johnson.ElongatedSquareGyrobicupola.Certificates.Root2
import Polyhedra.Johnson.ElongatedSquareGyrobicupola.Certificates.Root3
import Polyhedra.Johnson.ElongatedSquareGyrobicupola.Certificates.Root4
import Polyhedra.Johnson.ElongatedSquareGyrobicupola.Certificates.Root5
import Polyhedra.Johnson.ElongatedSquareGyrobicupola.Certificates.Root6
import Polyhedra.Johnson.ElongatedSquareGyrobicupola.Certificates.Root7
import Polyhedra.Johnson.ElongatedSquareGyrobicupola.Certificates.Root8
import Polyhedra.Johnson.ElongatedSquareGyrobicupola.Certificates.Root9
import Polyhedra.Johnson.ElongatedSquareGyrobicupola.Certificates.Root10
import Polyhedra.Johnson.ElongatedSquareGyrobicupola.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `johnson/elongated-square-gyrobicupola`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/optima-rerun-2026-11-13/elongated-square-gyrobicupola/exact.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Johnson.ElongatedSquareGyrobicupola.polyhedron` is `Θ` (`johnsonElongatedSquareGyrobicupola_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonElongatedSquareGyrobicupola

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

end Nieuwland.Certs.NieuwlandJohnsonElongatedSquareGyrobicupola

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/elongated-square-gyrobicupola`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem johnsonElongatedSquareGyrobicupola_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandJohnsonElongatedSquareGyrobicupola.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandJohnsonElongatedSquareGyrobicupola.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandJohnsonElongatedSquareGyrobicupola.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Johnson.ElongatedSquareGyrobicupola.polyhedron.nieuwland) : Johnson.ElongatedSquareGyrobicupola.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandJohnsonElongatedSquareGyrobicupola.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonElongatedSquareGyrobicupola.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandJohnsonElongatedSquareGyrobicupola.far_field hc Nieuwland.Certs.NieuwlandJohnsonElongatedSquareGyrobicupola.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Certs.NieuwlandJohnsonElongatedSquareGyrobicupola

open Check Cert

/-- The claims' chart trees as texts, in the order of `claimBoxes`. -/
def claimTexts : List String :=
  [Lift.Claim0.data, Lift.Claim1.data]

/-- **The claims**: every claim's chart tree checks at the exact scale `Θ` on its box. -/
theorem claims_ok : List.Forall₂ (fun C t ↦ NativeS.checkT Lift.Theta Lift.points C t = true) claimBoxes claimTexts :=
  .cons Lift.Claim0.t_ok (.cons Lift.Claim1.t_ok (.nil))

end Nieuwland.Certs.NieuwlandJohnsonElongatedSquareGyrobicupola

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/elongated-square-gyrobicupola`: the Nieuwland number.** From the far field at `theta`, the claims' chart trees at the exact scale `Θ ≥ theta` and the weak fit at `Θ` (`Check.Polyhedron.nieuwland_eq_of_lift_smul`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem johnsonElongatedSquareGyrobicupola_nieuwland : Johnson.ElongatedSquareGyrobicupola.polyhedron.nieuwland = realRoot [513240280207249/23367556, 0, -606539716456610/5841889, 0, 1318767729867288/5841889, 0, -1779014047726776/5841889, 0, 3331204530857333/11683778, 0, -1115616857490376/5841889, 0, 524596862453093/5841889, 0, -164636964476892/5841889, 0, 126008790204233/23367556, 0, -3014069505062/5841889, 0, 68817459825/5841889, 0, 1391119652/5841889, 0, 1] 1 (9/8) := by
  have hdim : Johnson.ElongatedSquareGyrobicupola.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandJohnsonElongatedSquareGyrobicupola.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandJohnsonElongatedSquareGyrobicupola.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandJohnsonElongatedSquareGyrobicupola.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_lift_smul Nieuwland.Certs.NieuwlandJohnsonElongatedSquareGyrobicupola.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonElongatedSquareGyrobicupola.roots) (by decide +kernel) (θ := Nieuwland.Certs.NieuwlandJohnsonElongatedSquareGyrobicupola.theta) (by decide +kernel) Nieuwland.Certs.NieuwlandJohnsonElongatedSquareGyrobicupola.far_field (c := (((1 : ℕ) : ℝ) * ((744993332751532155555340231960075300969619642628203094267653532938365133559393612083525502026194698085292224463174098399390056296806289476943872 : ℕ) : ℝ) / ((1 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandJohnsonElongatedSquareGyrobicupola.Lift.points_eq ((Check.Scale.re_lift _ _).trans Nieuwland.Certs.NieuwlandJohnsonElongatedSquareGyrobicupola.Lift.thetaQ_re) Nieuwland.Certs.NieuwlandJohnsonElongatedSquareGyrobicupola.Lift.theta_le (Check.noFitRot_of_texts Nieuwland.Certs.NieuwlandJohnsonElongatedSquareGyrobicupola.claims_ok) Nieuwland.Certs.NieuwlandJohnsonElongatedSquareGyrobicupola.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandJohnsonElongatedSquareGyrobicupola.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
