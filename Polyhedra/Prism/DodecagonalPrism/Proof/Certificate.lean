import Polyhedra.Prism.DodecagonalPrism.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Prism.DodecagonalPrism.Certificates.Weak
import Polyhedra.Prism.DodecagonalPrism.Certificates.Claim0
import Polyhedra.Prism.DodecagonalPrism.Certificates.Claim1
import Polyhedra.Prism.DodecagonalPrism.Certificates.Root0
import Polyhedra.Prism.DodecagonalPrism.Certificates.Root1
import Polyhedra.Prism.DodecagonalPrism.Certificates.Root2
import Polyhedra.Prism.DodecagonalPrism.Certificates.Root3
import Polyhedra.Prism.DodecagonalPrism.Certificates.Root4
import Polyhedra.Prism.DodecagonalPrism.Certificates.Root5
import Polyhedra.Prism.DodecagonalPrism.Certificates.Root6
import Polyhedra.Prism.DodecagonalPrism.Certificates.Root7
import Polyhedra.Prism.DodecagonalPrism.Certificates.Root8
import Polyhedra.Prism.DodecagonalPrism.Certificates.Root9
import Polyhedra.Prism.DodecagonalPrism.Certificates.Root10
import Polyhedra.Prism.DodecagonalPrism.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `prism/dodecagonal-prism`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/nieuwland-exact-2026-11-18-prism/dodecagonal-prism/exact.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Prism.DodecagonalPrism.polyhedron` is `Θ` (`prismDodecagonalPrism_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandPrismDodecagonalPrism

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

end Nieuwland.Certs.NieuwlandPrismDodecagonalPrism

namespace Nieuwland.Polyhedra

/-- **The fixture `prism/dodecagonal-prism`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem prismDodecagonalPrism_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandPrismDodecagonalPrism.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandPrismDodecagonalPrism.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandPrismDodecagonalPrism.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Prism.DodecagonalPrism.polyhedron.nieuwland) : Prism.DodecagonalPrism.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandPrismDodecagonalPrism.span_ok (roots := Nieuwland.Certs.NieuwlandPrismDodecagonalPrism.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandPrismDodecagonalPrism.far_field hc Nieuwland.Certs.NieuwlandPrismDodecagonalPrism.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Certs.NieuwlandPrismDodecagonalPrism

open Check Cert

/-- The claims' chart trees as texts, in the order of `claimBoxes`. -/
def claimTexts : List String :=
  [Lift.Claim0.data, Lift.Claim1.data]

/-- **The claims**: every claim's chart tree checks at the exact scale `Θ` on its box. -/
theorem claims_ok : List.Forall₂ (fun C t ↦ NativeS.checkT Lift.Theta Lift.points C t = true) claimBoxes claimTexts :=
  .cons Lift.Claim0.t_ok (.cons Lift.Claim1.t_ok (.nil))

end Nieuwland.Certs.NieuwlandPrismDodecagonalPrism

namespace Nieuwland.Polyhedra

/-- **The fixture `prism/dodecagonal-prism`: the Nieuwland number.** From the far field at `theta`, the claims' chart trees at the exact scale `Θ ≥ theta` and the weak fit at `Θ` (`Check.Polyhedron.nieuwland_eq_of_lift_smul`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem prismDodecagonalPrism_nieuwland : Prism.DodecagonalPrism.polyhedron.nieuwland = polyEval [-32278904314546/27124672262547, 35725642375955/54249344525094, 8484374443493/9041557420849, 25374472542320/27124672262547, 7409318362936/27124672262547, 323865653584/9041557420849, -739640056928/27124672262547, -349777320064/27124672262547] (realRoot [94321/1024, 3977/32, -7105/64, -1181/16, -145/2, -41/2, -5/2, 2, 1] 0 2) := by
  have hdim : Prism.DodecagonalPrism.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandPrismDodecagonalPrism.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandPrismDodecagonalPrism.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandPrismDodecagonalPrism.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_lift_smul Nieuwland.Certs.NieuwlandPrismDodecagonalPrism.span_ok (roots := Nieuwland.Certs.NieuwlandPrismDodecagonalPrism.roots) (by decide +kernel) (θ := Nieuwland.Certs.NieuwlandPrismDodecagonalPrism.theta) (by decide +kernel) Nieuwland.Certs.NieuwlandPrismDodecagonalPrism.far_field (c := (((1 : ℕ) : ℝ) * ((3471958049606016 : ℕ) : ℝ) ^ 3 / ((12054492698224010659412823392256 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandPrismDodecagonalPrism.Lift.points_eq ((Check.Scale.re_lift _ _).trans Nieuwland.Certs.NieuwlandPrismDodecagonalPrism.Lift.thetaQ_re) Nieuwland.Certs.NieuwlandPrismDodecagonalPrism.Lift.theta_le (Check.noFitRot_of_texts Nieuwland.Certs.NieuwlandPrismDodecagonalPrism.claims_ok) Nieuwland.Certs.NieuwlandPrismDodecagonalPrism.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandPrismDodecagonalPrism.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
