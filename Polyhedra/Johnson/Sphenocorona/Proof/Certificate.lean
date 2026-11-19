import Polyhedra.Johnson.Sphenocorona.Proof.Points
import Polyhedra.Johnson.Sphenocorona.Certificates.Touch
import Polyhedra.Johnson.Sphenocorona.Certificates.Root0
import Polyhedra.Johnson.Sphenocorona.Certificates.Root1
import Polyhedra.Johnson.Sphenocorona.Certificates.Root2
import Polyhedra.Johnson.Sphenocorona.Certificates.Root3
import Polyhedra.Johnson.Sphenocorona.Certificates.Root4
import Polyhedra.Johnson.Sphenocorona.Certificates.Root5
import Polyhedra.Johnson.Sphenocorona.Certificates.Root6
import Polyhedra.Johnson.Sphenocorona.Certificates.Root7
import Polyhedra.Johnson.Sphenocorona.Certificates.Root8
import Polyhedra.Johnson.Sphenocorona.Certificates.Root9
import Polyhedra.Johnson.Sphenocorona.Certificates.Root10
import Polyhedra.Johnson.Sphenocorona.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `johnson/sphenocorona`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/d2c-2026-11-13/sphenocorona/far.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Johnson.Sphenocorona.polyhedron` is `Θ` (`johnsonSphenocorona_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonSphenocorona

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

end Nieuwland.Certs.NieuwlandJohnsonSphenocorona

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/sphenocorona`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem johnsonSphenocorona_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandJohnsonSphenocorona.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandJohnsonSphenocorona.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandJohnsonSphenocorona.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Johnson.Sphenocorona.polyhedron.nieuwland) : Johnson.Sphenocorona.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandJohnsonSphenocorona.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonSphenocorona.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandJohnsonSphenocorona.far_field hc Nieuwland.Certs.NieuwlandJohnsonSphenocorona.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Polyhedra

open Check

/-- **The fixture `johnson/sphenocorona`: the Nieuwland number in root form.** It is the largest of the scales of the 2 roots (`Root.RootRec.scale`: the scale coordinate of the only zero of the root's system in its box, `johnsonSphenocorona_scale<i>`): the far field at `theta`, the touch leaves and the weak fits at the roots (`Root.nieuwland_eq_of_certOk`). -/
theorem johnsonSphenocorona_nieuwland : Johnson.Sphenocorona.polyhedron.nieuwland = max ((Nieuwland.Certs.NieuwlandJohnsonSphenocorona.touch1).scale Nieuwland.Certs.NieuwlandJohnsonSphenocorona.points) ((Nieuwland.Certs.NieuwlandJohnsonSphenocorona.touch0).scale Nieuwland.Certs.NieuwlandJohnsonSphenocorona.points) :=
  Root.nieuwland_eq_of_certOk Nieuwland.Certs.NieuwlandJohnsonSphenocorona.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonSphenocorona.roots) (by decide +kernel) (by decide +kernel) Nieuwland.Certs.NieuwlandJohnsonSphenocorona.far_field Nieuwland.Certs.NieuwlandJohnsonSphenocorona.eq_smul (by norm_num) rfl Nieuwland.Certs.NieuwlandJohnsonSphenocorona.touch_ok

/-- **The fixture `johnson/sphenocorona`: the scale of root 0.** The unknowns of a root's system are the pose `(s, t, x₁, x₂, x₃)` in its charts, the translation `(y₁, y₂)` of the plug's shadow, the scale `l` (the unknown `7`) and one multiplier per contact; its equations are the contacts' slacks and the stationarity of `l` under them (`Root.Sys.eqs`). The system has exactly one zero `y` in its box (Krawczyk's test), and the root's scale is the scale there. -/
theorem johnsonSphenocorona_scale0 : ∃ y, ((Nieuwland.Certs.NieuwlandJohnsonSphenocorona.touch0).kraw Nieuwland.Certs.NieuwlandJohnsonSphenocorona.points).IsZero (Root.basisPar (ZTheta Nieuwland.Certs.NieuwlandJohnsonSphenocorona.root)) y ∧ (Nieuwland.Certs.NieuwlandJohnsonSphenocorona.touch0).scale Nieuwland.Certs.NieuwlandJohnsonSphenocorona.points = ((Nieuwland.Certs.NieuwlandJohnsonSphenocorona.touch0).kraw Nieuwland.Certs.NieuwlandJohnsonSphenocorona.points).env (Root.basisPar (ZTheta Nieuwland.Certs.NieuwlandJohnsonSphenocorona.root)) y 7 :=
  Root.exists_scale Nieuwland.Certs.NieuwlandJohnsonSphenocorona.span_ok Nieuwland.Certs.NieuwlandJohnsonSphenocorona.touch_ok List.mem_cons_self

/-- **The fixture `johnson/sphenocorona`: the scale of root 1.** The unknowns of a root's system are the pose `(s, t, x₁, x₂, x₃)` in its charts, the translation `(y₁, y₂)` of the plug's shadow, the scale `l` (the unknown `7`) and one multiplier per contact; its equations are the contacts' slacks and the stationarity of `l` under them (`Root.Sys.eqs`). The system has exactly one zero `y` in its box (Krawczyk's test), and the root's scale is the scale there. -/
theorem johnsonSphenocorona_scale1 : ∃ y, ((Nieuwland.Certs.NieuwlandJohnsonSphenocorona.touch1).kraw Nieuwland.Certs.NieuwlandJohnsonSphenocorona.points).IsZero (Root.basisPar (ZTheta Nieuwland.Certs.NieuwlandJohnsonSphenocorona.root)) y ∧ (Nieuwland.Certs.NieuwlandJohnsonSphenocorona.touch1).scale Nieuwland.Certs.NieuwlandJohnsonSphenocorona.points = ((Nieuwland.Certs.NieuwlandJohnsonSphenocorona.touch1).kraw Nieuwland.Certs.NieuwlandJohnsonSphenocorona.points).env (Root.basisPar (ZTheta Nieuwland.Certs.NieuwlandJohnsonSphenocorona.root)) y 7 :=
  Root.exists_scale Nieuwland.Certs.NieuwlandJohnsonSphenocorona.span_ok Nieuwland.Certs.NieuwlandJohnsonSphenocorona.touch_ok (List.mem_cons_of_mem _ List.mem_cons_self)

/-- **The fixture `johnson/sphenocorona`: the Nieuwland number to 40 decimals.** -/
theorem johnsonSphenocorona_nieuwland_mem : Johnson.Sphenocorona.polyhedron.nieuwland ∈ Set.Icc (((10803187257574734432175125460219498035794 : ℤ) : ℝ) / 10 ^ 40) (((10803187257574734432175125460219498035797 : ℤ) : ℝ) / 10 ^ 40) :=
  Root.nieuwland_mem_Icc_of_certOk Nieuwland.Certs.NieuwlandJohnsonSphenocorona.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonSphenocorona.roots) (by decide +kernel) (by decide +kernel) Nieuwland.Certs.NieuwlandJohnsonSphenocorona.far_field Nieuwland.Certs.NieuwlandJohnsonSphenocorona.eq_smul (by norm_num) rfl Nieuwland.Certs.NieuwlandJohnsonSphenocorona.touch_ok Nieuwland.Certs.NieuwlandJohnsonSphenocorona.touch_in

end Nieuwland.Polyhedra
