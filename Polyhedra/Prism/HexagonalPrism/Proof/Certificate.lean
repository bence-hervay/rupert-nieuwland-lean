import Polyhedra.Prism.HexagonalPrism.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Prism.HexagonalPrism.Certificates.Weak
import Polyhedra.Prism.HexagonalPrism.Certificates.Claim0
import Polyhedra.Prism.HexagonalPrism.Certificates.Claim1
import Polyhedra.Prism.HexagonalPrism.Certificates.Root0
import Polyhedra.Prism.HexagonalPrism.Certificates.Root1
import Polyhedra.Prism.HexagonalPrism.Certificates.Root2
import Polyhedra.Prism.HexagonalPrism.Certificates.Root3
import Polyhedra.Prism.HexagonalPrism.Certificates.Root4
import Polyhedra.Prism.HexagonalPrism.Certificates.Root5
import Polyhedra.Prism.HexagonalPrism.Certificates.Root6
import Polyhedra.Prism.HexagonalPrism.Certificates.Root7
import Polyhedra.Prism.HexagonalPrism.Certificates.Root8
import Polyhedra.Prism.HexagonalPrism.Certificates.Root9
import Polyhedra.Prism.HexagonalPrism.Certificates.Root10
import Polyhedra.Prism.HexagonalPrism.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `prism/hexagonal-prism`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/nieuwland-exact-2026-11-16-prism/hexagonal-prism/exact.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Prism.HexagonalPrism.polyhedron` is `Θ` (`prismHexagonalPrism_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandPrismHexagonalPrism

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

end Nieuwland.Certs.NieuwlandPrismHexagonalPrism

namespace Nieuwland.Polyhedra

/-- **The fixture `prism/hexagonal-prism`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem prismHexagonalPrism_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandPrismHexagonalPrism.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandPrismHexagonalPrism.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandPrismHexagonalPrism.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Prism.HexagonalPrism.polyhedron.nieuwland) : Prism.HexagonalPrism.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandPrismHexagonalPrism.span_ok (roots := Nieuwland.Certs.NieuwlandPrismHexagonalPrism.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandPrismHexagonalPrism.far_field hc Nieuwland.Certs.NieuwlandPrismHexagonalPrism.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Certs.NieuwlandPrismHexagonalPrism

open Check Cert

/-- The claims' chart trees as texts, in the order of `claimBoxes`. -/
def claimTexts : List String :=
  [Lift.Claim0.data, Lift.Claim1.data]

/-- **The claims**: every claim's chart tree checks at the exact scale `Θ` on its box. -/
theorem claims_ok : List.Forall₂ (fun C t ↦ NativeS.checkT Lift.Theta Lift.points C t = true) claimBoxes claimTexts :=
  .cons Lift.Claim0.t_ok (.cons Lift.Claim1.t_ok (.nil))

end Nieuwland.Certs.NieuwlandPrismHexagonalPrism

namespace Nieuwland.Polyhedra

/-- **The fixture `prism/hexagonal-prism`: the Nieuwland number.** From the far field at `theta`, the claims' chart trees at the exact scale `Θ ≥ theta` and the weak fit at `Θ` (`Check.Polyhedron.nieuwland_eq_of_lift_smul`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem prismHexagonalPrism_nieuwland : Prism.HexagonalPrism.polyhedron.nieuwland = polyEval [13/12] (realRoot [-263/144, 13/6, 1] 0 4) := by
  have hdim : Prism.HexagonalPrism.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandPrismHexagonalPrism.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandPrismHexagonalPrism.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandPrismHexagonalPrism.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_lift_smul Nieuwland.Certs.NieuwlandPrismHexagonalPrism.span_ok (roots := Nieuwland.Certs.NieuwlandPrismHexagonalPrism.roots) (by decide +kernel) (θ := Nieuwland.Certs.NieuwlandPrismHexagonalPrism.theta) (by decide +kernel) Nieuwland.Certs.NieuwlandPrismHexagonalPrism.far_field (c := (((1 : ℕ) : ℝ) * ((12 : ℕ) : ℝ) / ((1 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandPrismHexagonalPrism.Lift.points_eq ((Check.Scale.re_lift _ _).trans Nieuwland.Certs.NieuwlandPrismHexagonalPrism.Lift.thetaQ_re) Nieuwland.Certs.NieuwlandPrismHexagonalPrism.Lift.theta_le (Check.noFitRot_of_texts Nieuwland.Certs.NieuwlandPrismHexagonalPrism.claims_ok) Nieuwland.Certs.NieuwlandPrismHexagonalPrism.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandPrismHexagonalPrism.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
