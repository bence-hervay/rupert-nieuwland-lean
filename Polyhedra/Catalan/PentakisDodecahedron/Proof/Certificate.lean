import Polyhedra.Catalan.PentakisDodecahedron.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Catalan.PentakisDodecahedron.Certificates.Weak
import Polyhedra.Catalan.PentakisDodecahedron.Certificates.Claim0
import Polyhedra.Catalan.PentakisDodecahedron.Certificates.Claim1
import Polyhedra.Catalan.PentakisDodecahedron.Certificates.Root0
import Polyhedra.Catalan.PentakisDodecahedron.Certificates.Root1
import Polyhedra.Catalan.PentakisDodecahedron.Certificates.Root2
import Polyhedra.Catalan.PentakisDodecahedron.Certificates.Root3
import Polyhedra.Catalan.PentakisDodecahedron.Certificates.Root4
import Polyhedra.Catalan.PentakisDodecahedron.Certificates.Root5
import Polyhedra.Catalan.PentakisDodecahedron.Certificates.Root6
import Polyhedra.Catalan.PentakisDodecahedron.Certificates.Root7
import Polyhedra.Catalan.PentakisDodecahedron.Certificates.Root8
import Polyhedra.Catalan.PentakisDodecahedron.Certificates.Root9
import Polyhedra.Catalan.PentakisDodecahedron.Certificates.Root10
import Polyhedra.Catalan.PentakisDodecahedron.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `catalan/pentakis-dodecahedron`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/optima-rerun-2026-11-13/pentakis-dodecahedron/exact.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Catalan.PentakisDodecahedron.polyhedron` is `Θ` (`catalanPentakisDodecahedron_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandCatalanPentakisDodecahedron

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

end Nieuwland.Certs.NieuwlandCatalanPentakisDodecahedron

namespace Nieuwland.Polyhedra

/-- **The fixture `catalan/pentakis-dodecahedron`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem catalanPentakisDodecahedron_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandCatalanPentakisDodecahedron.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandCatalanPentakisDodecahedron.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandCatalanPentakisDodecahedron.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Catalan.PentakisDodecahedron.polyhedron.nieuwland) : Catalan.PentakisDodecahedron.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandCatalanPentakisDodecahedron.span_ok (roots := Nieuwland.Certs.NieuwlandCatalanPentakisDodecahedron.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandCatalanPentakisDodecahedron.far_field hc Nieuwland.Certs.NieuwlandCatalanPentakisDodecahedron.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Certs.NieuwlandCatalanPentakisDodecahedron

open Check Cert

/-- The claims' chart trees as texts, in the order of `claimBoxes`. -/
def claimTexts : List String :=
  [Lift.Claim0.data, Lift.Claim1.data]

/-- **The claims**: every claim's chart tree checks at the exact scale `Θ` on its box. -/
theorem claims_ok : List.Forall₂ (fun C t ↦ NativeS.checkT Lift.Theta Lift.points C t = true) claimBoxes claimTexts :=
  .cons Lift.Claim0.t_ok (.cons Lift.Claim1.t_ok (.nil))

end Nieuwland.Certs.NieuwlandCatalanPentakisDodecahedron

namespace Nieuwland.Polyhedra

/-- **The fixture `catalan/pentakis-dodecahedron`: the Nieuwland number.** From the far field at `theta`, the claims' chart trees at the exact scale `Θ ≥ theta` and the weak fit at `Θ` (`Check.Polyhedron.nieuwland_eq_of_lift_smul`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem catalanPentakisDodecahedron_nieuwland : Catalan.PentakisDodecahedron.polyhedron.nieuwland = realRoot [7822518025/11019960576, 0, -1848235165/306110016, 0, 7592167363/340122240, 0, -295572797/6298560, 0, 103164865/1679616, 0, -5978249/116640, 0, 19151/720, 0, -47/6, 0, 1] 1 2 := by
  have hdim : Catalan.PentakisDodecahedron.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandCatalanPentakisDodecahedron.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandCatalanPentakisDodecahedron.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandCatalanPentakisDodecahedron.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_lift_smul Nieuwland.Certs.NieuwlandCatalanPentakisDodecahedron.span_ok (roots := Nieuwland.Certs.NieuwlandCatalanPentakisDodecahedron.roots) (by decide +kernel) (θ := Nieuwland.Certs.NieuwlandCatalanPentakisDodecahedron.theta) (by decide +kernel) Nieuwland.Certs.NieuwlandCatalanPentakisDodecahedron.far_field (c := (((1 : ℕ) : ℝ) * ((145956781772064856250000000000 : ℕ) : ℝ) / ((1 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandCatalanPentakisDodecahedron.Lift.points_eq ((Check.Scale.re_lift _ _).trans Nieuwland.Certs.NieuwlandCatalanPentakisDodecahedron.Lift.thetaQ_re) Nieuwland.Certs.NieuwlandCatalanPentakisDodecahedron.Lift.theta_le (Check.noFitRot_of_texts Nieuwland.Certs.NieuwlandCatalanPentakisDodecahedron.claims_ok) Nieuwland.Certs.NieuwlandCatalanPentakisDodecahedron.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandCatalanPentakisDodecahedron.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
