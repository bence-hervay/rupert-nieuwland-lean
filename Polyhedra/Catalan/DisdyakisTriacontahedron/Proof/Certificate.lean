import Polyhedra.Catalan.DisdyakisTriacontahedron.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Catalan.DisdyakisTriacontahedron.Certificates.Weak
import Polyhedra.Catalan.DisdyakisTriacontahedron.Certificates.Claim0
import Polyhedra.Catalan.DisdyakisTriacontahedron.Certificates.Claim1
import Polyhedra.Catalan.DisdyakisTriacontahedron.Certificates.Claim2
import Polyhedra.Catalan.DisdyakisTriacontahedron.Certificates.Claim3
import Polyhedra.Catalan.DisdyakisTriacontahedron.Certificates.Root0
import Polyhedra.Catalan.DisdyakisTriacontahedron.Certificates.Root1
import Polyhedra.Catalan.DisdyakisTriacontahedron.Certificates.Root2
import Polyhedra.Catalan.DisdyakisTriacontahedron.Certificates.Root3
import Polyhedra.Catalan.DisdyakisTriacontahedron.Certificates.Root4
import Polyhedra.Catalan.DisdyakisTriacontahedron.Certificates.Root5
import Polyhedra.Catalan.DisdyakisTriacontahedron.Certificates.Root6
import Polyhedra.Catalan.DisdyakisTriacontahedron.Certificates.Root7
import Polyhedra.Catalan.DisdyakisTriacontahedron.Certificates.Root8
import Polyhedra.Catalan.DisdyakisTriacontahedron.Certificates.Root9
import Polyhedra.Catalan.DisdyakisTriacontahedron.Certificates.Root10
import Polyhedra.Catalan.DisdyakisTriacontahedron.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `catalan/disdyakis-triacontahedron`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/optima-rerun-2026-11-13/disdyakis-triacontahedron/exact.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Catalan.DisdyakisTriacontahedron.polyhedron` is `Θ` (`catalanDisdyakisTriacontahedron_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandCatalanDisdyakisTriacontahedron

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

end Nieuwland.Certs.NieuwlandCatalanDisdyakisTriacontahedron

namespace Nieuwland.Polyhedra

/-- **The fixture `catalan/disdyakis-triacontahedron`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem catalanDisdyakisTriacontahedron_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandCatalanDisdyakisTriacontahedron.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandCatalanDisdyakisTriacontahedron.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandCatalanDisdyakisTriacontahedron.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Catalan.DisdyakisTriacontahedron.polyhedron.nieuwland) : Catalan.DisdyakisTriacontahedron.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandCatalanDisdyakisTriacontahedron.span_ok (roots := Nieuwland.Certs.NieuwlandCatalanDisdyakisTriacontahedron.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandCatalanDisdyakisTriacontahedron.far_field hc Nieuwland.Certs.NieuwlandCatalanDisdyakisTriacontahedron.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Certs.NieuwlandCatalanDisdyakisTriacontahedron

open Check Cert

/-- The claims' chart trees as texts, in the order of `claimBoxes`. -/
def claimTexts : List String :=
  [Lift.Claim0.data, Lift.Claim1.data, Lift.Claim2.data, Lift.Claim3.data]

/-- **The claims**: every claim's chart tree checks at the exact scale `Θ` on its box. -/
theorem claims_ok : List.Forall₂ (fun C t ↦ NativeS.checkT Lift.Theta Lift.points C t = true) claimBoxes claimTexts :=
  .cons Lift.Claim0.t_ok (.cons Lift.Claim1.t_ok (.cons Lift.Claim2.t_ok (.cons Lift.Claim3.t_ok (.nil))))

end Nieuwland.Certs.NieuwlandCatalanDisdyakisTriacontahedron

namespace Nieuwland.Polyhedra

/-- **The fixture `catalan/disdyakis-triacontahedron`: the Nieuwland number.** From the far field at `theta`, the claims' chart trees at the exact scale `Θ ≥ theta` and the weak fit at `Θ` (`Check.Polyhedron.nieuwland_eq_of_lift_smul`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem catalanDisdyakisTriacontahedron_nieuwland : Catalan.DisdyakisTriacontahedron.polyhedron.nieuwland = realRoot [31820881/891136, 0, -1485953/6962, 0, 31111725/55696, 0, -5797217/6962, 0, 21330207/27848, 0, -1520956/3481, 0, 506345/3481, 0, -82344/3481, 0, 1] 1 (65/64) := by
  have hdim : Catalan.DisdyakisTriacontahedron.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandCatalanDisdyakisTriacontahedron.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandCatalanDisdyakisTriacontahedron.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandCatalanDisdyakisTriacontahedron.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_lift_smul Nieuwland.Certs.NieuwlandCatalanDisdyakisTriacontahedron.span_ok (roots := Nieuwland.Certs.NieuwlandCatalanDisdyakisTriacontahedron.roots) (by decide +kernel) (θ := Nieuwland.Certs.NieuwlandCatalanDisdyakisTriacontahedron.theta) (by decide +kernel) Nieuwland.Certs.NieuwlandCatalanDisdyakisTriacontahedron.far_field (c := (((1 : ℕ) : ℝ) * ((108801309261757214638245715902464 : ℕ) : ℝ) / ((1 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandCatalanDisdyakisTriacontahedron.Lift.points_eq ((Check.Scale.re_lift _ _).trans Nieuwland.Certs.NieuwlandCatalanDisdyakisTriacontahedron.Lift.thetaQ_re) Nieuwland.Certs.NieuwlandCatalanDisdyakisTriacontahedron.Lift.theta_le (Check.noFitRot_of_texts Nieuwland.Certs.NieuwlandCatalanDisdyakisTriacontahedron.claims_ok) Nieuwland.Certs.NieuwlandCatalanDisdyakisTriacontahedron.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandCatalanDisdyakisTriacontahedron.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
