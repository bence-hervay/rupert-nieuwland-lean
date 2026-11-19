import Polyhedra.Archimedean.TruncatedTetrahedron.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Archimedean.TruncatedTetrahedron.Certificates.Weak
import Polyhedra.Archimedean.TruncatedTetrahedron.Certificates.Claim0
import Polyhedra.Archimedean.TruncatedTetrahedron.Certificates.Root0
import Polyhedra.Archimedean.TruncatedTetrahedron.Certificates.Root1
import Polyhedra.Archimedean.TruncatedTetrahedron.Certificates.Root2
import Polyhedra.Archimedean.TruncatedTetrahedron.Certificates.Root3
import Polyhedra.Archimedean.TruncatedTetrahedron.Certificates.Root4
import Polyhedra.Archimedean.TruncatedTetrahedron.Certificates.Root5
import Polyhedra.Archimedean.TruncatedTetrahedron.Certificates.Root6
import Polyhedra.Archimedean.TruncatedTetrahedron.Certificates.Root7
import Polyhedra.Archimedean.TruncatedTetrahedron.Certificates.Root8
import Polyhedra.Archimedean.TruncatedTetrahedron.Certificates.Root9
import Polyhedra.Archimedean.TruncatedTetrahedron.Certificates.Root10
import Polyhedra.Archimedean.TruncatedTetrahedron.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `archimedean/truncated-tetrahedron`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/nieuwland-exact-2026-11-09/held/out/truncated-tetrahedron/exact.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Archimedean.TruncatedTetrahedron.polyhedron` is `Θ` (`archimedeanTruncatedTetrahedron_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandArchimedeanTruncatedTetrahedron

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

end Nieuwland.Certs.NieuwlandArchimedeanTruncatedTetrahedron

namespace Nieuwland.Polyhedra

/-- **The fixture `archimedean/truncated-tetrahedron`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem archimedeanTruncatedTetrahedron_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandArchimedeanTruncatedTetrahedron.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandArchimedeanTruncatedTetrahedron.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandArchimedeanTruncatedTetrahedron.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Archimedean.TruncatedTetrahedron.polyhedron.nieuwland) : Archimedean.TruncatedTetrahedron.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandArchimedeanTruncatedTetrahedron.span_ok (roots := Nieuwland.Certs.NieuwlandArchimedeanTruncatedTetrahedron.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandArchimedeanTruncatedTetrahedron.far_field hc Nieuwland.Certs.NieuwlandArchimedeanTruncatedTetrahedron.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Certs.NieuwlandArchimedeanTruncatedTetrahedron

open Check Cert

/-- The claims' chart trees as texts, in the order of `claimBoxes`. -/
def claimTexts : List String :=
  [Lift.Claim0.data]

/-- **The claims**: every claim's chart tree checks at the exact scale `Θ` on its box. -/
theorem claims_ok : List.Forall₂ (fun C t ↦ NativeS.checkT Lift.Theta Lift.points C t = true) claimBoxes claimTexts :=
  .cons Lift.Claim0.t_ok (.nil)

end Nieuwland.Certs.NieuwlandArchimedeanTruncatedTetrahedron

namespace Nieuwland.Polyhedra

/-- **The fixture `archimedean/truncated-tetrahedron`: the Nieuwland number.** From the far field at `theta`, the claims' chart trees at the exact scale `Θ ≥ theta` and the weak fit at `Θ` (`Check.Polyhedron.nieuwland_eq_of_lift`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem archimedeanTruncatedTetrahedron_nieuwland : Archimedean.TruncatedTetrahedron.polyhedron.nieuwland = realRoot [64/625, 0, -84/625, 0, 64441/10000, 0, -363/50, 0, 1] 0 2 := by
  have hdim : Archimedean.TruncatedTetrahedron.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandArchimedeanTruncatedTetrahedron.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandArchimedeanTruncatedTetrahedron.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandArchimedeanTruncatedTetrahedron.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_lift Nieuwland.Certs.NieuwlandArchimedeanTruncatedTetrahedron.span_ok (roots := Nieuwland.Certs.NieuwlandArchimedeanTruncatedTetrahedron.roots) (by decide +kernel) (θ := Nieuwland.Certs.NieuwlandArchimedeanTruncatedTetrahedron.theta) (by decide +kernel) Nieuwland.Certs.NieuwlandArchimedeanTruncatedTetrahedron.far_field Nieuwland.Certs.NieuwlandArchimedeanTruncatedTetrahedron.Lift.points_eq (Check.Scale.re_lift _ Nieuwland.Certs.NieuwlandArchimedeanTruncatedTetrahedron.theta) Nieuwland.Certs.NieuwlandArchimedeanTruncatedTetrahedron.Lift.theta_le (Check.noFitRot_of_texts Nieuwland.Certs.NieuwlandArchimedeanTruncatedTetrahedron.claims_ok) Nieuwland.Certs.NieuwlandArchimedeanTruncatedTetrahedron.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandArchimedeanTruncatedTetrahedron.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
