import Polyhedra.Johnson.TriaugmentedTriangularPrism.Proof.Points
import Polyhedra.Johnson.TriaugmentedTriangularPrism.Certificates.Touch
import Polyhedra.Johnson.TriaugmentedTriangularPrism.Certificates.Root0
import Polyhedra.Johnson.TriaugmentedTriangularPrism.Certificates.Root1
import Polyhedra.Johnson.TriaugmentedTriangularPrism.Certificates.Root2
import Polyhedra.Johnson.TriaugmentedTriangularPrism.Certificates.Root3
import Polyhedra.Johnson.TriaugmentedTriangularPrism.Certificates.Root4
import Polyhedra.Johnson.TriaugmentedTriangularPrism.Certificates.Root5
import Polyhedra.Johnson.TriaugmentedTriangularPrism.Certificates.Root6
import Polyhedra.Johnson.TriaugmentedTriangularPrism.Certificates.Root7
import Polyhedra.Johnson.TriaugmentedTriangularPrism.Certificates.Root8
import Polyhedra.Johnson.TriaugmentedTriangularPrism.Certificates.Root9
import Polyhedra.Johnson.TriaugmentedTriangularPrism.Certificates.Root10
import Polyhedra.Johnson.TriaugmentedTriangularPrism.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `johnson/triaugmented-triangular-prism`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/jd2b-2026-11-15/triaugmented-triangular-prism/far.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Johnson.TriaugmentedTriangularPrism.polyhedron` is `Θ` (`johnsonTriaugmentedTriangularPrism_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonTriaugmentedTriangularPrism

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

end Nieuwland.Certs.NieuwlandJohnsonTriaugmentedTriangularPrism

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/triaugmented-triangular-prism`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem johnsonTriaugmentedTriangularPrism_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandJohnsonTriaugmentedTriangularPrism.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandJohnsonTriaugmentedTriangularPrism.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandJohnsonTriaugmentedTriangularPrism.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Johnson.TriaugmentedTriangularPrism.polyhedron.nieuwland) : Johnson.TriaugmentedTriangularPrism.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandJohnsonTriaugmentedTriangularPrism.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonTriaugmentedTriangularPrism.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandJohnsonTriaugmentedTriangularPrism.far_field hc Nieuwland.Certs.NieuwlandJohnsonTriaugmentedTriangularPrism.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Polyhedra

open Check

/-- **The fixture `johnson/triaugmented-triangular-prism`: the Nieuwland number in root form.** The unknowns of a root's system are the pose `(s, t, x₁, x₂, x₃)` in its charts, the translation `(y₁, y₂)` of the plug's shadow, the scale `l` (the unknown `7`) and one multiplier per contact; its equations are the contacts' slacks and the stationarity of `l` under them (`Root.Sys.eqs`). The system has exactly one zero `y` in its box (Krawczyk's test), and the Nieuwland number is the scale there: the far field at `theta`, the touch leaf and the weak fit at the root (`Root.nieuwland_eq_of_certOk_one`). -/
theorem johnsonTriaugmentedTriangularPrism_nieuwland : ∃ y, ((Nieuwland.Certs.NieuwlandJohnsonTriaugmentedTriangularPrism.touch0).kraw Nieuwland.Certs.NieuwlandJohnsonTriaugmentedTriangularPrism.points).IsZero (Root.basisPar (ZTheta Nieuwland.Certs.NieuwlandJohnsonTriaugmentedTriangularPrism.root)) y ∧ Johnson.TriaugmentedTriangularPrism.polyhedron.nieuwland = ((Nieuwland.Certs.NieuwlandJohnsonTriaugmentedTriangularPrism.touch0).kraw Nieuwland.Certs.NieuwlandJohnsonTriaugmentedTriangularPrism.points).env (Root.basisPar (ZTheta Nieuwland.Certs.NieuwlandJohnsonTriaugmentedTriangularPrism.root)) y 7 :=
  Root.nieuwland_eq_of_certOk_one Nieuwland.Certs.NieuwlandJohnsonTriaugmentedTriangularPrism.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonTriaugmentedTriangularPrism.roots) (by decide +kernel) (by decide +kernel) Nieuwland.Certs.NieuwlandJohnsonTriaugmentedTriangularPrism.far_field Nieuwland.Certs.NieuwlandJohnsonTriaugmentedTriangularPrism.eq_smul (by norm_num) rfl Nieuwland.Certs.NieuwlandJohnsonTriaugmentedTriangularPrism.touch_ok

/-- **The fixture `johnson/triaugmented-triangular-prism`: the Nieuwland number to 40 decimals.** -/
theorem johnsonTriaugmentedTriangularPrism_nieuwland_mem : Johnson.TriaugmentedTriangularPrism.polyhedron.nieuwland ∈ Set.Icc (((10081152528281092502574502058057761994980 : ℤ) : ℝ) / 10 ^ 40) (((10081152528281092502574502058057761994983 : ℤ) : ℝ) / 10 ^ 40) :=
  Root.nieuwland_mem_Icc_of_certOk Nieuwland.Certs.NieuwlandJohnsonTriaugmentedTriangularPrism.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonTriaugmentedTriangularPrism.roots) (by decide +kernel) (by decide +kernel) Nieuwland.Certs.NieuwlandJohnsonTriaugmentedTriangularPrism.far_field Nieuwland.Certs.NieuwlandJohnsonTriaugmentedTriangularPrism.eq_smul (by norm_num) rfl Nieuwland.Certs.NieuwlandJohnsonTriaugmentedTriangularPrism.touch_ok Nieuwland.Certs.NieuwlandJohnsonTriaugmentedTriangularPrism.touch_in

end Nieuwland.Polyhedra
