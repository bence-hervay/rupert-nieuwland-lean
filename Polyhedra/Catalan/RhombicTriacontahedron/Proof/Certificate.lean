import Polyhedra.Catalan.RhombicTriacontahedron.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Catalan.RhombicTriacontahedron.Certificates.Weak
import Polyhedra.Catalan.RhombicTriacontahedron.Certificates.Claim0
import Polyhedra.Catalan.RhombicTriacontahedron.Certificates.Root0
import Polyhedra.Catalan.RhombicTriacontahedron.Certificates.Root1
import Polyhedra.Catalan.RhombicTriacontahedron.Certificates.Root2
import Polyhedra.Catalan.RhombicTriacontahedron.Certificates.Root3
import Polyhedra.Catalan.RhombicTriacontahedron.Certificates.Root4
import Polyhedra.Catalan.RhombicTriacontahedron.Certificates.Root5
import Polyhedra.Catalan.RhombicTriacontahedron.Certificates.Root6
import Polyhedra.Catalan.RhombicTriacontahedron.Certificates.Root7
import Polyhedra.Catalan.RhombicTriacontahedron.Certificates.Root8
import Polyhedra.Catalan.RhombicTriacontahedron.Certificates.Root9
import Polyhedra.Catalan.RhombicTriacontahedron.Certificates.Root10
import Polyhedra.Catalan.RhombicTriacontahedron.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `catalan/rhombic-triacontahedron`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/optima-rerun-2026-11-13/rhombic-triacontahedron/exact.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Catalan.RhombicTriacontahedron.polyhedron` is `Θ` (`catalanRhombicTriacontahedron_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandCatalanRhombicTriacontahedron

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

end Nieuwland.Certs.NieuwlandCatalanRhombicTriacontahedron

namespace Nieuwland.Polyhedra

/-- **The fixture `catalan/rhombic-triacontahedron`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem catalanRhombicTriacontahedron_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandCatalanRhombicTriacontahedron.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandCatalanRhombicTriacontahedron.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandCatalanRhombicTriacontahedron.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Catalan.RhombicTriacontahedron.polyhedron.nieuwland) : Catalan.RhombicTriacontahedron.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandCatalanRhombicTriacontahedron.span_ok (roots := Nieuwland.Certs.NieuwlandCatalanRhombicTriacontahedron.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandCatalanRhombicTriacontahedron.far_field hc Nieuwland.Certs.NieuwlandCatalanRhombicTriacontahedron.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Certs.NieuwlandCatalanRhombicTriacontahedron

open Check Cert

/-- The claims' chart trees as texts, in the order of `claimBoxes`. -/
def claimTexts : List String :=
  [Lift.Claim0.data]

/-- **The claims**: every claim's chart tree checks at the exact scale `Θ` on its box. -/
theorem claims_ok : List.Forall₂ (fun C t ↦ NativeS.checkT Lift.Theta Lift.points C t = true) claimBoxes claimTexts :=
  .cons Lift.Claim0.t_ok (.nil)

end Nieuwland.Certs.NieuwlandCatalanRhombicTriacontahedron

namespace Nieuwland.Polyhedra

/-- **The fixture `catalan/rhombic-triacontahedron`: the Nieuwland number.** From the far field at `theta`, the claims' chart trees at the exact scale `Θ ≥ theta` and the weak fit at `Θ` (`Check.Polyhedron.nieuwland_eq_of_lift_smul`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem catalanRhombicTriacontahedron_nieuwland : Catalan.RhombicTriacontahedron.polyhedron.nieuwland = realRoot [2828125/92416, 0, -5171875/11552, 0, 55940625/23104, 0, -160903125/23104, 0, 572329375/46208, 0, -342139375/23104, 0, 289109625/23104, 0, -176524875/23104, 0, 308930525/92416, 0, -23268875/23104, 0, 561975/2888, 0, -7715/361, 0, 1] 1 (5/4) := by
  have hdim : Catalan.RhombicTriacontahedron.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandCatalanRhombicTriacontahedron.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandCatalanRhombicTriacontahedron.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandCatalanRhombicTriacontahedron.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_lift_smul Nieuwland.Certs.NieuwlandCatalanRhombicTriacontahedron.span_ok (roots := Nieuwland.Certs.NieuwlandCatalanRhombicTriacontahedron.roots) (by decide +kernel) (θ := Nieuwland.Certs.NieuwlandCatalanRhombicTriacontahedron.theta) (by decide +kernel) Nieuwland.Certs.NieuwlandCatalanRhombicTriacontahedron.far_field (c := (((1 : ℕ) : ℝ) * ((10911289083421819902458082206674686469267153715200000 : ℕ) : ℝ) / ((1 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandCatalanRhombicTriacontahedron.Lift.points_eq ((Check.Scale.re_lift _ _).trans Nieuwland.Certs.NieuwlandCatalanRhombicTriacontahedron.Lift.thetaQ_re) Nieuwland.Certs.NieuwlandCatalanRhombicTriacontahedron.Lift.theta_le (Check.noFitRot_of_texts Nieuwland.Certs.NieuwlandCatalanRhombicTriacontahedron.claims_ok) Nieuwland.Certs.NieuwlandCatalanRhombicTriacontahedron.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandCatalanRhombicTriacontahedron.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
