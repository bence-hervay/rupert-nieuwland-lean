import Polyhedra.Prism.HendecagonalPrism.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Prism.HendecagonalPrism.Certificates.Weak
import Polyhedra.Prism.HendecagonalPrism.Certificates.Claim0
import Polyhedra.Prism.HendecagonalPrism.Certificates.Claim1
import Polyhedra.Prism.HendecagonalPrism.Certificates.Root0
import Polyhedra.Prism.HendecagonalPrism.Certificates.Root1
import Polyhedra.Prism.HendecagonalPrism.Certificates.Root2
import Polyhedra.Prism.HendecagonalPrism.Certificates.Root3
import Polyhedra.Prism.HendecagonalPrism.Certificates.Root4
import Polyhedra.Prism.HendecagonalPrism.Certificates.Root5
import Polyhedra.Prism.HendecagonalPrism.Certificates.Root6
import Polyhedra.Prism.HendecagonalPrism.Certificates.Root7
import Polyhedra.Prism.HendecagonalPrism.Certificates.Root8
import Polyhedra.Prism.HendecagonalPrism.Certificates.Root9
import Polyhedra.Prism.HendecagonalPrism.Certificates.Root10
import Polyhedra.Prism.HendecagonalPrism.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `prism/hendecagonal-prism`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/nieuwland-exact-2026-11-18-prism/hendecagonal-prism/exact.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Prism.HendecagonalPrism.polyhedron` is `Θ` (`prismHendecagonalPrism_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandPrismHendecagonalPrism

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

end Nieuwland.Certs.NieuwlandPrismHendecagonalPrism

namespace Nieuwland.Polyhedra

/-- **The fixture `prism/hendecagonal-prism`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem prismHendecagonalPrism_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandPrismHendecagonalPrism.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandPrismHendecagonalPrism.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandPrismHendecagonalPrism.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Prism.HendecagonalPrism.polyhedron.nieuwland) : Prism.HendecagonalPrism.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandPrismHendecagonalPrism.span_ok (roots := Nieuwland.Certs.NieuwlandPrismHendecagonalPrism.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandPrismHendecagonalPrism.far_field hc Nieuwland.Certs.NieuwlandPrismHendecagonalPrism.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Certs.NieuwlandPrismHendecagonalPrism

open Check Cert

/-- The claims' chart trees as texts, in the order of `claimBoxes`. -/
def claimTexts : List String :=
  [Lift.Claim0.data, Lift.Claim1.data]

/-- **The claims**: every claim's chart tree checks at the exact scale `Θ` on its box. -/
theorem claims_ok : List.Forall₂ (fun C t ↦ NativeS.checkT Lift.Theta Lift.points C t = true) claimBoxes claimTexts :=
  .cons Lift.Claim0.t_ok (.cons Lift.Claim1.t_ok (.nil))

end Nieuwland.Certs.NieuwlandPrismHendecagonalPrism

namespace Nieuwland.Polyhedra

/-- **The fixture `prism/hendecagonal-prism`: the Nieuwland number.** From the far field at `theta`, the claims' chart trees at the exact scale `Θ ≥ theta` and the weak fit at `Θ` (`Check.Polyhedron.nieuwland_eq_of_lift_smul`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem prismHendecagonalPrism_nieuwland : Prism.HendecagonalPrism.polyhedron.nieuwland = realRoot [21129981853696/36590401, 0, -154655086608384/36590401, 0, 495680929267712/36590401, 0, -909719444422656/36590401, 0, 45560132407296/1590887, 0, -778943106359296/36590401, 0, 368265816701696/36590401, 0, -103814057328640/36590401, 0, 14808917668656/36590401, 0, -637032730872/36590401, 0, 1] (257/256) (515/512) := by
  have hdim : Prism.HendecagonalPrism.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandPrismHendecagonalPrism.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandPrismHendecagonalPrism.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandPrismHendecagonalPrism.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_lift_smul Nieuwland.Certs.NieuwlandPrismHendecagonalPrism.span_ok (roots := Nieuwland.Certs.NieuwlandPrismHendecagonalPrism.roots) (by decide +kernel) (θ := Nieuwland.Certs.NieuwlandPrismHendecagonalPrism.theta) (by decide +kernel) Nieuwland.Certs.NieuwlandPrismHendecagonalPrism.far_field (c := (((1 : ℕ) : ℝ) * ((12358688719126556892484239733200021671536064933731667072147266764134834723042479329274180257353064684963593178054656 : ℕ) : ℝ) ^ 9 / ((2651355448643487032893594503955183322310407611429018166405149716138239048694866117020394212721158527529531087592835330518096462901120037069619335581420236117240108760882981325558336621748367013769627200867814985179861239457396004217890584512755300748262482051759402083195359012100297910293576918415337132527091356097208806116645631742233152369621790630435672616379863292735681647252929323654404640400087119584856307764461655940881291852230141815465271161282234049848175061373945833874363427427124342459814854229662859482770581546356698786735387484458133310078361240435674497316797837657488642305336165867979440520774571191219364673360877289424549700146090870083981613123977066370347636703018152666385667423318227523964834527630306544879910335352388162051979923574854462533137523349476637440460864631214799786774793674591062344341106723587063317233324447621818136119661910782329818680010004658307403446372237695485294516197392384 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandPrismHendecagonalPrism.Lift.points_eq ((Check.Scale.re_lift _ _).trans Nieuwland.Certs.NieuwlandPrismHendecagonalPrism.Lift.thetaQ_re) Nieuwland.Certs.NieuwlandPrismHendecagonalPrism.Lift.theta_le (Check.noFitRot_of_texts Nieuwland.Certs.NieuwlandPrismHendecagonalPrism.claims_ok) Nieuwland.Certs.NieuwlandPrismHendecagonalPrism.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandPrismHendecagonalPrism.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
