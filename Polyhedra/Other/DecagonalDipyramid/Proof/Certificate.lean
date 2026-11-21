import Polyhedra.Other.DecagonalDipyramid.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Other.DecagonalDipyramid.Certificates.Weak
import Polyhedra.Other.DecagonalDipyramid.Certificates.Claim0
import Polyhedra.Other.DecagonalDipyramid.Certificates.Claim1
import Polyhedra.Other.DecagonalDipyramid.Certificates.Claim2
import Polyhedra.Other.DecagonalDipyramid.Certificates.Claim3
import Polyhedra.Other.DecagonalDipyramid.Certificates.Claim4
import Polyhedra.Other.DecagonalDipyramid.Certificates.Claim5
import Polyhedra.Other.DecagonalDipyramid.Certificates.Root0
import Polyhedra.Other.DecagonalDipyramid.Certificates.Root1
import Polyhedra.Other.DecagonalDipyramid.Certificates.Root2
import Polyhedra.Other.DecagonalDipyramid.Certificates.Root3
import Polyhedra.Other.DecagonalDipyramid.Certificates.Root4
import Polyhedra.Other.DecagonalDipyramid.Certificates.Root5
import Polyhedra.Other.DecagonalDipyramid.Certificates.Root6
import Polyhedra.Other.DecagonalDipyramid.Certificates.Root7
import Polyhedra.Other.DecagonalDipyramid.Certificates.Root8
import Polyhedra.Other.DecagonalDipyramid.Certificates.Root9
import Polyhedra.Other.DecagonalDipyramid.Certificates.Root10
import Polyhedra.Other.DecagonalDipyramid.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `dipyramid/decagonal-dipyramid`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/nieuwland-exact-2026-11-20-dipyramid/decagonal-dipyramid/exact.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Other.DecagonalDipyramid.polyhedron` is `Θ` (`dipyramidDecagonalDipyramid_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandDipyramidDecagonalDipyramid

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

end Nieuwland.Certs.NieuwlandDipyramidDecagonalDipyramid

namespace Nieuwland.Polyhedra

/-- **The fixture `dipyramid/decagonal-dipyramid`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem dipyramidDecagonalDipyramid_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandDipyramidDecagonalDipyramid.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandDipyramidDecagonalDipyramid.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandDipyramidDecagonalDipyramid.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Other.DecagonalDipyramid.polyhedron.nieuwland) : Other.DecagonalDipyramid.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandDipyramidDecagonalDipyramid.span_ok (roots := Nieuwland.Certs.NieuwlandDipyramidDecagonalDipyramid.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandDipyramidDecagonalDipyramid.far_field hc Nieuwland.Certs.NieuwlandDipyramidDecagonalDipyramid.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Certs.NieuwlandDipyramidDecagonalDipyramid

open Check Cert

/-- The claims' chart trees as texts, in the order of `claimBoxes`. -/
def claimTexts : List String :=
  [Lift.Claim0.data, Lift.Claim1.data, Lift.Claim2.data, Lift.Claim3.data, Lift.Claim4.data, Lift.Claim5.data]

/-- **The claims**: every claim's chart tree checks at the exact scale `Θ` on its box. -/
theorem claims_ok : List.Forall₂ (fun C t ↦ NativeS.checkT Lift.Theta Lift.points C t = true) claimBoxes claimTexts :=
  .cons Lift.Claim0.t_ok (.cons Lift.Claim1.t_ok (.cons Lift.Claim2.t_ok (.cons Lift.Claim3.t_ok (.cons Lift.Claim4.t_ok (.cons Lift.Claim5.t_ok (.nil))))))

end Nieuwland.Certs.NieuwlandDipyramidDecagonalDipyramid

namespace Nieuwland.Polyhedra

/-- **The fixture `dipyramid/decagonal-dipyramid`: the Nieuwland number.** From the far field at `theta`, the claims' chart trees at the exact scale `Θ ≥ theta` and the weak fit at `Θ` (`Check.Polyhedron.nieuwland_eq_of_lift_smul`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem dipyramidDecagonalDipyramid_nieuwland : Other.DecagonalDipyramid.polyhedron.nieuwland = polyEval [2975619908485/1274053674808, 2303329829609/318513418702, 1724805484140/159256709351, 117406001360/159256709351, -1075767259150/159256709351, -264298464640/159256709351, 144570522000/159256709351, 42814684000/159256709351] (realRoot [32441/6400, 2249/80, 1153/20, 843/20, -557/40, -29, -4, 4, 1] (-3/4) (-1/2)) := by
  have hdim : Other.DecagonalDipyramid.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandDipyramidDecagonalDipyramid.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandDipyramidDecagonalDipyramid.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandDipyramidDecagonalDipyramid.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_lift_smul Nieuwland.Certs.NieuwlandDipyramidDecagonalDipyramid.span_ok (roots := Nieuwland.Certs.NieuwlandDipyramidDecagonalDipyramid.roots) (by decide +kernel) (θ := Nieuwland.Certs.NieuwlandDipyramidDecagonalDipyramid.theta) (by decide +kernel) Nieuwland.Certs.NieuwlandDipyramidDecagonalDipyramid.far_field (c := (((1 : ℕ) : ℝ) * ((79628354675500 : ℕ) : ℝ) ^ 3 / ((6340674868327222710300250000 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandDipyramidDecagonalDipyramid.Lift.points_eq ((Check.Scale.re_lift _ _).trans Nieuwland.Certs.NieuwlandDipyramidDecagonalDipyramid.Lift.thetaQ_re) Nieuwland.Certs.NieuwlandDipyramidDecagonalDipyramid.Lift.theta_le (Check.noFitRot_of_texts Nieuwland.Certs.NieuwlandDipyramidDecagonalDipyramid.claims_ok) Nieuwland.Certs.NieuwlandDipyramidDecagonalDipyramid.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandDipyramidDecagonalDipyramid.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
