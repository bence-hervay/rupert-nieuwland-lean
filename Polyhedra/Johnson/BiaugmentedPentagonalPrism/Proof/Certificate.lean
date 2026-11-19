import Polyhedra.Johnson.BiaugmentedPentagonalPrism.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Johnson.BiaugmentedPentagonalPrism.Certificates.Weak
import Polyhedra.Johnson.BiaugmentedPentagonalPrism.Certificates.Claim0
import Polyhedra.Johnson.BiaugmentedPentagonalPrism.Certificates.Claim1
import Polyhedra.Johnson.BiaugmentedPentagonalPrism.Certificates.Claim2
import Polyhedra.Johnson.BiaugmentedPentagonalPrism.Certificates.Claim3
import Polyhedra.Johnson.BiaugmentedPentagonalPrism.Certificates.Claim4
import Polyhedra.Johnson.BiaugmentedPentagonalPrism.Certificates.Claim5
import Polyhedra.Johnson.BiaugmentedPentagonalPrism.Certificates.Root0
import Polyhedra.Johnson.BiaugmentedPentagonalPrism.Certificates.Root1
import Polyhedra.Johnson.BiaugmentedPentagonalPrism.Certificates.Root2
import Polyhedra.Johnson.BiaugmentedPentagonalPrism.Certificates.Root3
import Polyhedra.Johnson.BiaugmentedPentagonalPrism.Certificates.Root4
import Polyhedra.Johnson.BiaugmentedPentagonalPrism.Certificates.Root5
import Polyhedra.Johnson.BiaugmentedPentagonalPrism.Certificates.Root6
import Polyhedra.Johnson.BiaugmentedPentagonalPrism.Certificates.Root7
import Polyhedra.Johnson.BiaugmentedPentagonalPrism.Certificates.Root8
import Polyhedra.Johnson.BiaugmentedPentagonalPrism.Certificates.Root9
import Polyhedra.Johnson.BiaugmentedPentagonalPrism.Certificates.Root10
import Polyhedra.Johnson.BiaugmentedPentagonalPrism.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `johnson/biaugmented-pentagonal-prism`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/optima-rerun-2026-11-13/biaugmented-pentagonal-prism/exact.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Johnson.BiaugmentedPentagonalPrism.polyhedron` is `Θ` (`johnsonBiaugmentedPentagonalPrism_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonBiaugmentedPentagonalPrism

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

end Nieuwland.Certs.NieuwlandJohnsonBiaugmentedPentagonalPrism

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/biaugmented-pentagonal-prism`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem johnsonBiaugmentedPentagonalPrism_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandJohnsonBiaugmentedPentagonalPrism.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandJohnsonBiaugmentedPentagonalPrism.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandJohnsonBiaugmentedPentagonalPrism.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Johnson.BiaugmentedPentagonalPrism.polyhedron.nieuwland) : Johnson.BiaugmentedPentagonalPrism.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandJohnsonBiaugmentedPentagonalPrism.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonBiaugmentedPentagonalPrism.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandJohnsonBiaugmentedPentagonalPrism.far_field hc Nieuwland.Certs.NieuwlandJohnsonBiaugmentedPentagonalPrism.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Certs.NieuwlandJohnsonBiaugmentedPentagonalPrism

open Check Cert

/-- The claims' chart trees as texts, in the order of `claimBoxes`. -/
def claimTexts : List String :=
  [Lift.Claim0.data, Lift.Claim1.data, Lift.Claim2.data, Lift.Claim3.data, Lift.Claim4.data, Lift.Claim5.data]

/-- **The claims**: every claim's chart tree checks at the exact scale `Θ` on its box. -/
theorem claims_ok : List.Forall₂ (fun C t ↦ NativeS.checkT Lift.Theta Lift.points C t = true) claimBoxes claimTexts :=
  .cons Lift.Claim0.t_ok (.cons Lift.Claim1.t_ok (.cons Lift.Claim2.t_ok (.cons Lift.Claim3.t_ok (.cons Lift.Claim4.t_ok (.cons Lift.Claim5.t_ok (.nil))))))

end Nieuwland.Certs.NieuwlandJohnsonBiaugmentedPentagonalPrism

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/biaugmented-pentagonal-prism`: the Nieuwland number.** From the far field at `theta`, the claims' chart trees at the exact scale `Θ ≥ theta` and the weak fit at `Θ` (`Check.Polyhedron.nieuwland_eq_of_lift_smul`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem johnsonBiaugmentedPentagonalPrism_nieuwland : Johnson.BiaugmentedPentagonalPrism.polyhedron.nieuwland = realRoot [723394816/92173567201, 0, -3509276471296/92173567201, 0, 1107419246419712/92173567201, 0, -1976118973902848/92173567201, 0, 1251877849913440/92173567201, 0, -19386351235328/4851240379, 0, 53427483829232/92173567201, 0, -12033664/303601, 0, 1] 1 (3/2) := by
  have hdim : Johnson.BiaugmentedPentagonalPrism.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandJohnsonBiaugmentedPentagonalPrism.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandJohnsonBiaugmentedPentagonalPrism.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandJohnsonBiaugmentedPentagonalPrism.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_lift_smul Nieuwland.Certs.NieuwlandJohnsonBiaugmentedPentagonalPrism.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonBiaugmentedPentagonalPrism.roots) (by decide +kernel) (θ := Nieuwland.Certs.NieuwlandJohnsonBiaugmentedPentagonalPrism.theta) (by decide +kernel) Nieuwland.Certs.NieuwlandJohnsonBiaugmentedPentagonalPrism.far_field (c := (((1 : ℕ) : ℝ) * ((674217223908315787412613349753344152098718677275343151825673991409704981240369538658304000 : ℕ) : ℝ) ^ 7 / ((5166087381479449173105634863170743311306082292535560674855601130095736272363925442267358485768760887061750092333607977437297657595961218898119068809919131325266382095298912073479835016631226086320493523105081366132645546036925988477762996448185929876109707524515986362038474560677764570476090458071025791694518789115864303809467816973310879735729347441148991711414117642094844853793588594832857949441936671717789609513605259075650390996075761855895068633704018639413118012474493300203521890072878356489589718008185780961280000000000000000000 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandJohnsonBiaugmentedPentagonalPrism.Lift.points_eq ((Check.Scale.re_lift _ _).trans Nieuwland.Certs.NieuwlandJohnsonBiaugmentedPentagonalPrism.Lift.thetaQ_re) Nieuwland.Certs.NieuwlandJohnsonBiaugmentedPentagonalPrism.Lift.theta_le (Check.noFitRot_of_texts Nieuwland.Certs.NieuwlandJohnsonBiaugmentedPentagonalPrism.claims_ok) Nieuwland.Certs.NieuwlandJohnsonBiaugmentedPentagonalPrism.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandJohnsonBiaugmentedPentagonalPrism.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
