import Polyhedra.Johnson.SnubSquareAntiprism.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Johnson.SnubSquareAntiprism.Certificates.Weak
import Polyhedra.Johnson.SnubSquareAntiprism.Certificates.Claim0
import Polyhedra.Johnson.SnubSquareAntiprism.Certificates.Claim1
import Polyhedra.Johnson.SnubSquareAntiprism.Certificates.Root0
import Polyhedra.Johnson.SnubSquareAntiprism.Certificates.Root1
import Polyhedra.Johnson.SnubSquareAntiprism.Certificates.Root2
import Polyhedra.Johnson.SnubSquareAntiprism.Certificates.Root3
import Polyhedra.Johnson.SnubSquareAntiprism.Certificates.Root4
import Polyhedra.Johnson.SnubSquareAntiprism.Certificates.Root5
import Polyhedra.Johnson.SnubSquareAntiprism.Certificates.Root6
import Polyhedra.Johnson.SnubSquareAntiprism.Certificates.Root7
import Polyhedra.Johnson.SnubSquareAntiprism.Certificates.Root8
import Polyhedra.Johnson.SnubSquareAntiprism.Certificates.Root9
import Polyhedra.Johnson.SnubSquareAntiprism.Certificates.Root10
import Polyhedra.Johnson.SnubSquareAntiprism.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `johnson/snub-square-antiprism`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/optima-rerun-2026-11-13/snub-square-antiprism/exact.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Johnson.SnubSquareAntiprism.polyhedron` is `Θ` (`johnsonSnubSquareAntiprism_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonSnubSquareAntiprism

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

end Nieuwland.Certs.NieuwlandJohnsonSnubSquareAntiprism

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/snub-square-antiprism`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem johnsonSnubSquareAntiprism_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandJohnsonSnubSquareAntiprism.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandJohnsonSnubSquareAntiprism.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandJohnsonSnubSquareAntiprism.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Johnson.SnubSquareAntiprism.polyhedron.nieuwland) : Johnson.SnubSquareAntiprism.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandJohnsonSnubSquareAntiprism.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonSnubSquareAntiprism.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandJohnsonSnubSquareAntiprism.far_field hc Nieuwland.Certs.NieuwlandJohnsonSnubSquareAntiprism.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Certs.NieuwlandJohnsonSnubSquareAntiprism

open Check Cert

/-- The claims' chart trees as texts, in the order of `claimBoxes`. -/
def claimTexts : List String :=
  [Lift.Claim0.data, Lift.Claim1.data]

/-- **The claims**: every claim's chart tree checks at the exact scale `Θ` on its box. -/
theorem claims_ok : List.Forall₂ (fun C t ↦ NativeS.checkT Lift.Theta Lift.points C t = true) claimBoxes claimTexts :=
  .cons Lift.Claim0.t_ok (.cons Lift.Claim1.t_ok (.nil))

end Nieuwland.Certs.NieuwlandJohnsonSnubSquareAntiprism

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/snub-square-antiprism`: the Nieuwland number.** From the far field at `theta`, the claims' chart trees at the exact scale `Θ ≥ theta` and the weak fit at `Θ` (`Check.Polyhedron.nieuwland_eq_of_lift_smul`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem johnsonSnubSquareAntiprism_nieuwland : Johnson.SnubSquareAntiprism.polyhedron.nieuwland = realRoot [113163299454976/6420907670401, 0, -1101110439313408/6420907670401, 0, 99823938109440/131038932049, 0, -13113142195716096/6420907670401, 0, 23620859044098048/6420907670401, 0, -30106468025090048/6420907670401, 0, 27828720795240448/6420907670401, 0, -18786794881923072/6420907670401, 0, 9187629019799488/6420907670401, 0, -3172223211011968/6420907670401, 0, 733439622318320/6420907670401, 0, -101866902889648/6420907670401, 0, 1] (65/64) (33/32) := by
  have hdim : Johnson.SnubSquareAntiprism.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandJohnsonSnubSquareAntiprism.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandJohnsonSnubSquareAntiprism.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandJohnsonSnubSquareAntiprism.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_lift_smul Nieuwland.Certs.NieuwlandJohnsonSnubSquareAntiprism.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonSnubSquareAntiprism.roots) (by decide +kernel) (θ := Nieuwland.Certs.NieuwlandJohnsonSnubSquareAntiprism.theta) (by decide +kernel) Nieuwland.Certs.NieuwlandJohnsonSnubSquareAntiprism.far_field (c := (((1 : ℕ) : ℝ) * ((162775324087820802142083063274817572879715917791811600070825169615127420336663667929313478215427711238435160459108546423379003923173852556921538792110878978402339310931663241569191280781515764392519018707323502931058096628913004385364208223450125010408781648410626789681196147115134656913199938681176064 : ℕ) : ℝ) ^ 11 / ((4150084926885219025782137400537897840436083966446755136329149268900694651266726729313329343686272514243312965774493850228224158529204504631937179270526076037837954788273515883306396170665177760000205593736059519040312289224092854267219651363708230806320004570924417881526853294105201358241286091897193871377042913835288403729894810251813082260618450132569660809432769564588878883938510788981847881192711646964578075753874400861026828154086065859868976285175389742545038445155673123064027347559195419601549048684630853941976508718186329209175471501420837384784422684727626513508392555318472951027896859692487557028564502288665511999327520130075877806756644987577409621316448180756697652649192353544056932986645149364450504425251394434882312427144280587437851962433939008336799440931376682822584331402137208768672041008413650570207525509259547061758467597694767176196187130024308377268670109343568592661378269241544063336149411403848885415075094421815257122544647056827101173090594145050556727533042098897913450653777346050978293241951522109430660817145092291176191394864167436142746755004740400533615559249490235501098615824444210347006781812281907200659854987005816099364836192619787356888448830460036792443473950888753427613928770227783292369354253765881919541091649510110596123097830625000681049489009123214666928835787044710925954569975772110991266689408135277007496164485060637277455371310900847741284717390240085614869460979953685581943784834706713772749767092477446282043873679343573207914630990272483519557230769374632768383638084104660561721059169672907405575623135419496661375451576297744507059373891084797188687384357272376865273940644219279806823987213389161942730385618923303673355511187921826487618518242686668092453570799564665853027528199012964504209306565280636905363692389923644239285104586673242665660022825606942959235985565786075933700840443142937879892933030366933308706565633536703230217418494590874800278304215259039464526290015091478054544590656942889186881796918919229592349880847098108706717930240239418348259883842125585936447216291801325550717660880492693366326433146473553679016436807634356329297822318731826139763232048118727051212536705760891198215758721225192112668902274495963335142442302660905014711478748710975667937117370959371826908614941377398466211014921146807228955040920454267884499539681773948768112550749828319813763559510591421986679316292557005486371119105484873946026663409633612394687373541502988727184079550141138232511412643893206668817322470305121792859268533844302198962870897851411491850051525811817349332817332790225035644696252905514279960462675603066240964725611248786972952792870124616157635017317003520287226652699515019831821406547259333919767532409867093765293566440905709483297368539765561289501488526395120060479649277986023244883411564101507770990670561728970236278425089029764236013284461752141238348023958469575734226897587517513654639745594548480044132506576023268950066866179905514204185906585282827247370551400835884206398995582731985966227813404658872242810126336 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandJohnsonSnubSquareAntiprism.Lift.points_eq ((Check.Scale.re_lift _ _).trans Nieuwland.Certs.NieuwlandJohnsonSnubSquareAntiprism.Lift.thetaQ_re) Nieuwland.Certs.NieuwlandJohnsonSnubSquareAntiprism.Lift.theta_le (Check.noFitRot_of_texts Nieuwland.Certs.NieuwlandJohnsonSnubSquareAntiprism.claims_ok) Nieuwland.Certs.NieuwlandJohnsonSnubSquareAntiprism.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandJohnsonSnubSquareAntiprism.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
