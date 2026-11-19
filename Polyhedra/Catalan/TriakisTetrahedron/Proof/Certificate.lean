import Polyhedra.Catalan.TriakisTetrahedron.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Catalan.TriakisTetrahedron.Certificates.Weak
import Polyhedra.Catalan.TriakisTetrahedron.Certificates.Zones
import Polyhedra.Catalan.TriakisTetrahedron.Certificates.Claim0
import Polyhedra.Catalan.TriakisTetrahedron.Certificates.Claim1
import Polyhedra.Catalan.TriakisTetrahedron.Certificates.Claim2
import Polyhedra.Catalan.TriakisTetrahedron.Certificates.Claim3
import Polyhedra.Catalan.TriakisTetrahedron.Certificates.Root0
import Polyhedra.Catalan.TriakisTetrahedron.Certificates.Root1
import Polyhedra.Catalan.TriakisTetrahedron.Certificates.Root2
import Polyhedra.Catalan.TriakisTetrahedron.Certificates.Root3
import Polyhedra.Catalan.TriakisTetrahedron.Certificates.Root4
import Polyhedra.Catalan.TriakisTetrahedron.Certificates.Root5
import Polyhedra.Catalan.TriakisTetrahedron.Certificates.Root6
import Polyhedra.Catalan.TriakisTetrahedron.Certificates.Root7
import Polyhedra.Catalan.TriakisTetrahedron.Certificates.Root8
import Polyhedra.Catalan.TriakisTetrahedron.Certificates.Root9
import Polyhedra.Catalan.TriakisTetrahedron.Certificates.Root10
import Polyhedra.Catalan.TriakisTetrahedron.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `catalan/triakis-tetrahedron`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/nieuwland-exact-2026-11-14/stretch/triakis-tetrahedron/exact.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Catalan.TriakisTetrahedron.polyhedron` is `Θ` (`catalanTriakisTetrahedron_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron

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

end Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron

namespace Nieuwland.Polyhedra

/-- **The fixture `catalan/triakis-tetrahedron`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem catalanTriakisTetrahedron_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Catalan.TriakisTetrahedron.polyhedron.nieuwland) : Catalan.TriakisTetrahedron.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron.span_ok (roots := Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron.far_field hc Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron

open Check Cert

/-- The claims' chart trees as texts, in the order of `treeBoxes`. -/
def claimTexts : List String :=
  [Lift.Claim0.data, Lift.Claim1.data, Lift.Claim2.data, Lift.Claim3.data]

/-- **The claims**: every claim's chart tree checks at the exact scale `Θ` on its box. -/
theorem claims_ok : List.Forall₂ (fun C t ↦ NativeS.checkT Lift.Theta Lift.points C t = true) treeBoxes claimTexts :=
  .cons Lift.Claim0.t_ok (.cons Lift.Claim1.t_ok (.cons Lift.Claim2.t_ok (.cons Lift.Claim3.t_ok (.nil))))

end Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron

namespace Nieuwland.Polyhedra

/-- **The fixture `catalan/triakis-tetrahedron`: the Nieuwland number.** From the far field at `theta`, the claims' chart trees at the exact scale `Θ ≥ theta`, the claims at scale 1 (`Zones.settled`, with `1 ≤ Θ`) and the weak fit at `Θ` (`Check.Polyhedron.nieuwland_eq_of_lift_zones`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem catalanTriakisTetrahedron_nieuwland : Catalan.TriakisTetrahedron.polyhedron.nieuwland = realRoot [-308986084/26780625, 0, 7788757288/241025625, 0, -583210213/26780625, 0, 1] 1 2 := by
  have hdim : Catalan.TriakisTetrahedron.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_lift_zones Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron.span_ok (roots := Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron.roots) (by decide +kernel) (θ := Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron.theta) (by decide +kernel) Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron.far_field (trees := Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron.treeBoxes) (zones := Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron.zoneBoxes) rfl (c := 1) one_ne_zero (by rw [Nieuwland.Polyhedron.smul_one]; exact Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron.Lift.points_eq) (Check.Scale.re_lift _ Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron.theta) Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron.Lift.theta_le (Check.noFitRot_of_texts Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron.claims_ok) Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron.Zones.settled Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron.Lift.one_le Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandCatalanTriakisTetrahedron.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
