import Polyhedra.Johnson.BiaugmentedTriangularPrism.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Johnson.BiaugmentedTriangularPrism.Certificates.Weak
import Polyhedra.Johnson.BiaugmentedTriangularPrism.Certificates.Claim0
import Polyhedra.Johnson.BiaugmentedTriangularPrism.Certificates.Claim1
import Polyhedra.Johnson.BiaugmentedTriangularPrism.Certificates.Root0
import Polyhedra.Johnson.BiaugmentedTriangularPrism.Certificates.Root1
import Polyhedra.Johnson.BiaugmentedTriangularPrism.Certificates.Root2
import Polyhedra.Johnson.BiaugmentedTriangularPrism.Certificates.Root3
import Polyhedra.Johnson.BiaugmentedTriangularPrism.Certificates.Root4
import Polyhedra.Johnson.BiaugmentedTriangularPrism.Certificates.Root5
import Polyhedra.Johnson.BiaugmentedTriangularPrism.Certificates.Root6
import Polyhedra.Johnson.BiaugmentedTriangularPrism.Certificates.Root7
import Polyhedra.Johnson.BiaugmentedTriangularPrism.Certificates.Root8
import Polyhedra.Johnson.BiaugmentedTriangularPrism.Certificates.Root9
import Polyhedra.Johnson.BiaugmentedTriangularPrism.Certificates.Root10
import Polyhedra.Johnson.BiaugmentedTriangularPrism.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `johnson/biaugmented-triangular-prism`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/nieuwland-exact-2026-11-09/small/out/biaugmented-triangular-prism/exact.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Johnson.BiaugmentedTriangularPrism.polyhedron` is `Θ` (`johnsonBiaugmentedTriangularPrism_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonBiaugmentedTriangularPrism

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

end Nieuwland.Certs.NieuwlandJohnsonBiaugmentedTriangularPrism

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/biaugmented-triangular-prism`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem johnsonBiaugmentedTriangularPrism_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandJohnsonBiaugmentedTriangularPrism.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandJohnsonBiaugmentedTriangularPrism.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandJohnsonBiaugmentedTriangularPrism.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Johnson.BiaugmentedTriangularPrism.polyhedron.nieuwland) : Johnson.BiaugmentedTriangularPrism.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandJohnsonBiaugmentedTriangularPrism.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonBiaugmentedTriangularPrism.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandJohnsonBiaugmentedTriangularPrism.far_field hc Nieuwland.Certs.NieuwlandJohnsonBiaugmentedTriangularPrism.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Certs.NieuwlandJohnsonBiaugmentedTriangularPrism

open Check Cert

/-- The claims' chart trees as texts, in the order of `claimBoxes`. -/
def claimTexts : List String :=
  [Lift.Claim0.data, Lift.Claim1.data]

/-- **The claims**: every claim's chart tree checks at the exact scale `Θ` on its box. -/
theorem claims_ok : List.Forall₂ (fun C t ↦ NativeS.checkT Lift.Theta Lift.points C t = true) claimBoxes claimTexts :=
  .cons Lift.Claim0.t_ok (.cons Lift.Claim1.t_ok (.nil))

end Nieuwland.Certs.NieuwlandJohnsonBiaugmentedTriangularPrism

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/biaugmented-triangular-prism`: the Nieuwland number.** From the far field at `theta`, the claims' chart trees at the exact scale `Θ ≥ theta` and the weak fit at `Θ` (`Check.Polyhedron.nieuwland_eq_of_lift_smul`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem johnsonBiaugmentedTriangularPrism_nieuwland : Johnson.BiaugmentedTriangularPrism.polyhedron.nieuwland = polyEval [0, -2167260752092162448508309621244380691448905721574971900113493/577142610291694215382065181364933124859660389120318165270528, 0, 434970727711172021903961843412409146193932537886313959433629/108214239429692665384137221505924960911186322960059655988224, 0, -16529098689465941926566263117335204275175268968992187103147/6763389964355791586508576344120310056949145185003728499264, 0, 321553686571061340873284304004337337434181710022358534241/422711872772236974156786021507519378559321574062733031204, 0, -4123949737688432061934635188786257193136353081298189820/35225989397686414513065501792293281546610131171894419267, 0, 97703605208512158814804337901864262244025722858481600/11741996465895471504355167264097760515536710390631473089, 0, -2824860208759277221648733730595799034770705322624000/11741996465895471504355167264097760515536710390631473089, 0, 27807551410547360432364438031104941171034716160000/11741996465895471504355167264097760515536710390631473089] (realRoot [263227307731307929/24159191040000, 0, -14458500894720191/113246208000, 0, 66989778138539743/212336640000, 0, -396508516863859/1327104000, 0, 220062136724243/1658880000, 0, -49510995017/1728000, 0, 13344133/4800, 0, -2807/30, 0, 1] (-1/2) 0) := by
  have hdim : Johnson.BiaugmentedTriangularPrism.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandJohnsonBiaugmentedTriangularPrism.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandJohnsonBiaugmentedTriangularPrism.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandJohnsonBiaugmentedTriangularPrism.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_lift_smul Nieuwland.Certs.NieuwlandJohnsonBiaugmentedTriangularPrism.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonBiaugmentedTriangularPrism.roots) (by decide +kernel) (θ := Nieuwland.Certs.NieuwlandJohnsonBiaugmentedTriangularPrism.theta) (by decide +kernel) Nieuwland.Certs.NieuwlandJohnsonBiaugmentedTriangularPrism.far_field (c := (((1 : ℕ) : ℝ) * ((14976428025196692652190434670398507070729627776098193655738997600000000000 : ℕ) : ℝ) ^ 3 / ((1345760378363381443933148969212808314375288986698434424310321707184953593580424844151459118299664089428452383857839440716834560000000000000000000000 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandJohnsonBiaugmentedTriangularPrism.Lift.points_eq ((Check.Scale.re_lift _ _).trans Nieuwland.Certs.NieuwlandJohnsonBiaugmentedTriangularPrism.Lift.thetaQ_re) Nieuwland.Certs.NieuwlandJohnsonBiaugmentedTriangularPrism.Lift.theta_le (Check.noFitRot_of_texts Nieuwland.Certs.NieuwlandJohnsonBiaugmentedTriangularPrism.claims_ok) Nieuwland.Certs.NieuwlandJohnsonBiaugmentedTriangularPrism.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandJohnsonBiaugmentedTriangularPrism.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
