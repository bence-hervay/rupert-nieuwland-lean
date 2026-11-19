import Polyhedra.Johnson.TridiminishedRhombicosidodecahedron.Proof.Points
import Polyhedra.Johnson.TridiminishedRhombicosidodecahedron.Certificates.Touch
import Polyhedra.Johnson.TridiminishedRhombicosidodecahedron.Certificates.Root0
import Polyhedra.Johnson.TridiminishedRhombicosidodecahedron.Certificates.Root1
import Polyhedra.Johnson.TridiminishedRhombicosidodecahedron.Certificates.Root2
import Polyhedra.Johnson.TridiminishedRhombicosidodecahedron.Certificates.Root3
import Polyhedra.Johnson.TridiminishedRhombicosidodecahedron.Certificates.Root4
import Polyhedra.Johnson.TridiminishedRhombicosidodecahedron.Certificates.Root5
import Polyhedra.Johnson.TridiminishedRhombicosidodecahedron.Certificates.Root6
import Polyhedra.Johnson.TridiminishedRhombicosidodecahedron.Certificates.Root7
import Polyhedra.Johnson.TridiminishedRhombicosidodecahedron.Certificates.Root8
import Polyhedra.Johnson.TridiminishedRhombicosidodecahedron.Certificates.Root9
import Polyhedra.Johnson.TridiminishedRhombicosidodecahedron.Certificates.Root10
import Polyhedra.Johnson.TridiminishedRhombicosidodecahedron.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `johnson/tridiminished-rhombicosidodecahedron`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/jd2b-2026-11-15/tridiminished-rhombicosidodecahedron/far.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Johnson.TridiminishedRhombicosidodecahedron.polyhedron` is `Θ` (`johnsonTridiminishedRhombicosidodecahedron_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron

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

end Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/tridiminished-rhombicosidodecahedron`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem johnsonTridiminishedRhombicosidodecahedron_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Johnson.TridiminishedRhombicosidodecahedron.polyhedron.nieuwland) : Johnson.TridiminishedRhombicosidodecahedron.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.far_field hc Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Polyhedra

open Check

/-- **The fixture `johnson/tridiminished-rhombicosidodecahedron`: the Nieuwland number in root form.** It is the largest of the scales of the 2 roots (`Root.RootRec.scale`: the scale coordinate of the only zero of the root's system in its box, `johnsonTridiminishedRhombicosidodecahedron_scale<i>`): the far field at `theta`, the touch leaves and the weak fits at the roots (`Root.nieuwland_eq_of_certOk`). -/
theorem johnsonTridiminishedRhombicosidodecahedron_nieuwland : Johnson.TridiminishedRhombicosidodecahedron.polyhedron.nieuwland = max ((Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.touch1).scale Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.points) ((Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.touch0).scale Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.points) :=
  Root.nieuwland_eq_of_certOk Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.roots) (by decide +kernel) (by decide +kernel) Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.far_field Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.eq_smul (by norm_num) rfl Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.touch_ok

/-- **The fixture `johnson/tridiminished-rhombicosidodecahedron`: the scale of root 0.** The unknowns of a root's system are the pose `(s, t, x₁, x₂, x₃)` in its charts, the translation `(y₁, y₂)` of the plug's shadow, the scale `l` (the unknown `7`) and one multiplier per contact; its equations are the contacts' slacks and the stationarity of `l` under them (`Root.Sys.eqs`). The system has exactly one zero `y` in its box (Krawczyk's test), and the root's scale is the scale there. -/
theorem johnsonTridiminishedRhombicosidodecahedron_scale0 : ∃ y, ((Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.touch0).kraw Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.points).IsZero (Root.basisPar (ZSqrt 5)) y ∧ (Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.touch0).scale Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.points = ((Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.touch0).kraw Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.points).env (Root.basisPar (ZSqrt 5)) y 7 :=
  Root.exists_scale Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.span_ok Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.touch_ok List.mem_cons_self

/-- **The fixture `johnson/tridiminished-rhombicosidodecahedron`: the scale of root 1.** The unknowns of a root's system are the pose `(s, t, x₁, x₂, x₃)` in its charts, the translation `(y₁, y₂)` of the plug's shadow, the scale `l` (the unknown `7`) and one multiplier per contact; its equations are the contacts' slacks and the stationarity of `l` under them (`Root.Sys.eqs`). The system has exactly one zero `y` in its box (Krawczyk's test), and the root's scale is the scale there. -/
theorem johnsonTridiminishedRhombicosidodecahedron_scale1 : ∃ y, ((Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.touch1).kraw Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.points).IsZero (Root.basisPar (ZSqrt 5)) y ∧ (Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.touch1).scale Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.points = ((Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.touch1).kraw Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.points).env (Root.basisPar (ZSqrt 5)) y 7 :=
  Root.exists_scale Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.span_ok Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.touch_ok (List.mem_cons_of_mem _ List.mem_cons_self)

/-- **The fixture `johnson/tridiminished-rhombicosidodecahedron`: the Nieuwland number to 40 decimals.** -/
theorem johnsonTridiminishedRhombicosidodecahedron_nieuwland_mem : Johnson.TridiminishedRhombicosidodecahedron.polyhedron.nieuwland ∈ Set.Icc (((10038252929000918231074569816840031483183 : ℤ) : ℝ) / 10 ^ 40) (((10038252929000918231074569816840031483186 : ℤ) : ℝ) / 10 ^ 40) :=
  Root.nieuwland_mem_Icc_of_certOk Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.roots) (by decide +kernel) (by decide +kernel) Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.far_field Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.eq_smul (by norm_num) rfl Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.touch_ok Nieuwland.Certs.NieuwlandJohnsonTridiminishedRhombicosidodecahedron.touch_in

end Nieuwland.Polyhedra
