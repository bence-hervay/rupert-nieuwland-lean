import Polyhedra.Archimedean.Icosidodecahedron.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Archimedean.Icosidodecahedron.Certificates.Weak
import Polyhedra.Archimedean.Icosidodecahedron.Certificates.Claim0
import Polyhedra.Archimedean.Icosidodecahedron.Certificates.Claim1
import Polyhedra.Archimedean.Icosidodecahedron.Certificates.Claim2
import Polyhedra.Archimedean.Icosidodecahedron.Certificates.Claim3
import Polyhedra.Archimedean.Icosidodecahedron.Certificates.Claim4
import Polyhedra.Archimedean.Icosidodecahedron.Certificates.Claim5
import Polyhedra.Archimedean.Icosidodecahedron.Certificates.Claim6
import Polyhedra.Archimedean.Icosidodecahedron.Certificates.Claim7
import Polyhedra.Archimedean.Icosidodecahedron.Certificates.Claim8
import Polyhedra.Archimedean.Icosidodecahedron.Certificates.Claim9
import Polyhedra.Archimedean.Icosidodecahedron.Certificates.Root0
import Polyhedra.Archimedean.Icosidodecahedron.Certificates.Root1
import Polyhedra.Archimedean.Icosidodecahedron.Certificates.Root2
import Polyhedra.Archimedean.Icosidodecahedron.Certificates.Root3
import Polyhedra.Archimedean.Icosidodecahedron.Certificates.Root4
import Polyhedra.Archimedean.Icosidodecahedron.Certificates.Root5
import Polyhedra.Archimedean.Icosidodecahedron.Certificates.Root6
import Polyhedra.Archimedean.Icosidodecahedron.Certificates.Root7
import Polyhedra.Archimedean.Icosidodecahedron.Certificates.Root8
import Polyhedra.Archimedean.Icosidodecahedron.Certificates.Root9
import Polyhedra.Archimedean.Icosidodecahedron.Certificates.Root10
import Polyhedra.Archimedean.Icosidodecahedron.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `archimedean/icosidodecahedron`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/ico-x512-2026-11-13/icosidodecahedron/exact.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Archimedean.Icosidodecahedron.polyhedron` is `Θ` (`archimedeanIcosidodecahedron_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandArchimedeanIcosidodecahedron

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

end Nieuwland.Certs.NieuwlandArchimedeanIcosidodecahedron

namespace Nieuwland.Polyhedra

/-- **The fixture `archimedean/icosidodecahedron`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem archimedeanIcosidodecahedron_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandArchimedeanIcosidodecahedron.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandArchimedeanIcosidodecahedron.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandArchimedeanIcosidodecahedron.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Archimedean.Icosidodecahedron.polyhedron.nieuwland) : Archimedean.Icosidodecahedron.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandArchimedeanIcosidodecahedron.span_ok (roots := Nieuwland.Certs.NieuwlandArchimedeanIcosidodecahedron.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandArchimedeanIcosidodecahedron.far_field hc Nieuwland.Certs.NieuwlandArchimedeanIcosidodecahedron.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Certs.NieuwlandArchimedeanIcosidodecahedron

open Check Cert

/-- The claims' chart trees as texts, in the order of `claimBoxes`. -/
def claimTexts : List String :=
  [Lift.Claim0.data, Lift.Claim1.data, Lift.Claim2.data, Lift.Claim3.data, Lift.Claim4.data, Lift.Claim5.data, Lift.Claim6.data, Lift.Claim7.data, Lift.Claim8.data, Lift.Claim9.data]

/-- **The claims**: every claim's chart tree checks at the exact scale `Θ` on its box. -/
theorem claims_ok : List.Forall₂ (fun C t ↦ NativeS.checkT Lift.Theta Lift.points C t = true) claimBoxes claimTexts :=
  .cons Lift.Claim0.t_ok (.cons Lift.Claim1.t_ok (.cons Lift.Claim2.t_ok (.cons Lift.Claim3.t_ok (.cons Lift.Claim4.t_ok (.cons Lift.Claim5.t_ok (.cons Lift.Claim6.t_ok (.cons Lift.Claim7.t_ok (.cons Lift.Claim8.t_ok (.cons Lift.Claim9.t_ok (.nil))))))))))

end Nieuwland.Certs.NieuwlandArchimedeanIcosidodecahedron

namespace Nieuwland.Polyhedra

/-- **The fixture `archimedean/icosidodecahedron`: the Nieuwland number.** From the far field at `theta`, the claims' chart trees at the exact scale `Θ ≥ theta` and the weak fit at `Θ` (`Check.Polyhedron.nieuwland_eq_of_lift_smul`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem archimedeanIcosidodecahedron_nieuwland : Archimedean.Icosidodecahedron.polyhedron.nieuwland = realRoot [1050625/57121, 0, -7392500/57121, 0, 22183250/57121, 0, -36293000/57121, 0, 34809675/57121, 0, -19705400/57121, 0, 6295890/57121, 0, -1005660/57121, 0, 1] 1 (129/128) := by
  have hdim : Archimedean.Icosidodecahedron.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandArchimedeanIcosidodecahedron.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandArchimedeanIcosidodecahedron.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandArchimedeanIcosidodecahedron.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_lift_smul Nieuwland.Certs.NieuwlandArchimedeanIcosidodecahedron.span_ok (roots := Nieuwland.Certs.NieuwlandArchimedeanIcosidodecahedron.roots) (by decide +kernel) (θ := Nieuwland.Certs.NieuwlandArchimedeanIcosidodecahedron.theta) (by decide +kernel) Nieuwland.Certs.NieuwlandArchimedeanIcosidodecahedron.far_field (c := (((1 : ℕ) : ℝ) * ((3941627203206853256660053220501176295968856125 : ℕ) : ℝ) / ((2 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandArchimedeanIcosidodecahedron.Lift.points_eq ((Check.Scale.re_lift _ _).trans Nieuwland.Certs.NieuwlandArchimedeanIcosidodecahedron.Lift.thetaQ_re) Nieuwland.Certs.NieuwlandArchimedeanIcosidodecahedron.Lift.theta_le (Check.noFitRot_of_texts Nieuwland.Certs.NieuwlandArchimedeanIcosidodecahedron.claims_ok) Nieuwland.Certs.NieuwlandArchimedeanIcosidodecahedron.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandArchimedeanIcosidodecahedron.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
