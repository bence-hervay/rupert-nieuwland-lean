import Polyhedra.Other.DodecagonalDipyramid.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Other.DodecagonalDipyramid.Certificates.Weak
import Polyhedra.Other.DodecagonalDipyramid.Certificates.Claim0
import Polyhedra.Other.DodecagonalDipyramid.Certificates.Claim1
import Polyhedra.Other.DodecagonalDipyramid.Certificates.Claim2
import Polyhedra.Other.DodecagonalDipyramid.Certificates.Claim3
import Polyhedra.Other.DodecagonalDipyramid.Certificates.Claim4
import Polyhedra.Other.DodecagonalDipyramid.Certificates.Claim5
import Polyhedra.Other.DodecagonalDipyramid.Certificates.Claim6
import Polyhedra.Other.DodecagonalDipyramid.Certificates.Claim7
import Polyhedra.Other.DodecagonalDipyramid.Certificates.Root0
import Polyhedra.Other.DodecagonalDipyramid.Certificates.Root1
import Polyhedra.Other.DodecagonalDipyramid.Certificates.Root2
import Polyhedra.Other.DodecagonalDipyramid.Certificates.Root3
import Polyhedra.Other.DodecagonalDipyramid.Certificates.Root4
import Polyhedra.Other.DodecagonalDipyramid.Certificates.Root5
import Polyhedra.Other.DodecagonalDipyramid.Certificates.Root6
import Polyhedra.Other.DodecagonalDipyramid.Certificates.Root7
import Polyhedra.Other.DodecagonalDipyramid.Certificates.Root8
import Polyhedra.Other.DodecagonalDipyramid.Certificates.Root9
import Polyhedra.Other.DodecagonalDipyramid.Certificates.Root10
import Polyhedra.Other.DodecagonalDipyramid.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `dipyramid/dodecagonal-dipyramid`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/nieuwland-exact-2026-11-20-dipyramid/dodecagonal-dipyramid/exact.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Other.DodecagonalDipyramid.polyhedron` is `Θ` (`dipyramidDodecagonalDipyramid_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandDipyramidDodecagonalDipyramid

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

end Nieuwland.Certs.NieuwlandDipyramidDodecagonalDipyramid

namespace Nieuwland.Polyhedra

/-- **The fixture `dipyramid/dodecagonal-dipyramid`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem dipyramidDodecagonalDipyramid_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandDipyramidDodecagonalDipyramid.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandDipyramidDodecagonalDipyramid.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandDipyramidDodecagonalDipyramid.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Other.DodecagonalDipyramid.polyhedron.nieuwland) : Other.DodecagonalDipyramid.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandDipyramidDodecagonalDipyramid.span_ok (roots := Nieuwland.Certs.NieuwlandDipyramidDodecagonalDipyramid.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandDipyramidDodecagonalDipyramid.far_field hc Nieuwland.Certs.NieuwlandDipyramidDodecagonalDipyramid.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Certs.NieuwlandDipyramidDodecagonalDipyramid

open Check Cert

/-- The claims' chart trees as texts, in the order of `claimBoxes`. -/
def claimTexts : List String :=
  [Lift.Claim0.data, Lift.Claim1.data, Lift.Claim2.data, Lift.Claim3.data, Lift.Claim4.data, Lift.Claim5.data, Lift.Claim6.data, Lift.Claim7.data]

/-- **The claims**: every claim's chart tree checks at the exact scale `Θ` on its box. -/
theorem claims_ok : List.Forall₂ (fun C t ↦ NativeS.checkT Lift.Theta Lift.points C t = true) claimBoxes claimTexts :=
  .cons Lift.Claim0.t_ok (.cons Lift.Claim1.t_ok (.cons Lift.Claim2.t_ok (.cons Lift.Claim3.t_ok (.cons Lift.Claim4.t_ok (.cons Lift.Claim5.t_ok (.cons Lift.Claim6.t_ok (.cons Lift.Claim7.t_ok (.nil))))))))

end Nieuwland.Certs.NieuwlandDipyramidDodecagonalDipyramid

namespace Nieuwland.Polyhedra

/-- **The fixture `dipyramid/dodecagonal-dipyramid`: the Nieuwland number.** From the far field at `theta`, the claims' chart trees at the exact scale `Θ ≥ theta` and the weak fit at `Θ` (`Check.Polyhedron.nieuwland_eq_of_lift_smul`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem dipyramidDodecagonalDipyramid_nieuwland : Other.DodecagonalDipyramid.polyhedron.nieuwland = polyEval [1001083774639/2954033506700, -5517316761281/4431050260050, -296978615013/738508376675, 27571731416/738508376675, -7514512624/2215525130025, 35482778768/738508376675, 2438050528/147701675335, 22532013184/2215525130025] (realRoot [47041/1024, 2797/64, -2881/64, -467/16, -5/4, -4, 7/2, 2, 1] (-1) 0) := by
  have hdim : Other.DodecagonalDipyramid.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandDipyramidDodecagonalDipyramid.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandDipyramidDodecagonalDipyramid.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandDipyramidDodecagonalDipyramid.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_lift_smul Nieuwland.Certs.NieuwlandDipyramidDodecagonalDipyramid.span_ok (roots := Nieuwland.Certs.NieuwlandDipyramidDodecagonalDipyramid.roots) (by decide +kernel) (θ := Nieuwland.Certs.NieuwlandDipyramidDodecagonalDipyramid.theta) (by decide +kernel) Nieuwland.Certs.NieuwlandDipyramidDodecagonalDipyramid.far_field (c := (((1 : ℕ) : ℝ) * ((141793608321600 : ℕ) : ℝ) ^ 3 / ((20105427360859312769026560000 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandDipyramidDodecagonalDipyramid.Lift.points_eq ((Check.Scale.re_lift _ _).trans Nieuwland.Certs.NieuwlandDipyramidDodecagonalDipyramid.Lift.thetaQ_re) Nieuwland.Certs.NieuwlandDipyramidDodecagonalDipyramid.Lift.theta_le (Check.noFitRot_of_texts Nieuwland.Certs.NieuwlandDipyramidDodecagonalDipyramid.claims_ok) Nieuwland.Certs.NieuwlandDipyramidDodecagonalDipyramid.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandDipyramidDodecagonalDipyramid.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
