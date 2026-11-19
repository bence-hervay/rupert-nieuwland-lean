import Polyhedra.Antiprism.SquareAntiprism.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Antiprism.SquareAntiprism.Certificates.Weak
import Polyhedra.Antiprism.SquareAntiprism.Certificates.Claim0
import Polyhedra.Antiprism.SquareAntiprism.Certificates.Claim1
import Polyhedra.Antiprism.SquareAntiprism.Certificates.Root0
import Polyhedra.Antiprism.SquareAntiprism.Certificates.Root1
import Polyhedra.Antiprism.SquareAntiprism.Certificates.Root2
import Polyhedra.Antiprism.SquareAntiprism.Certificates.Root3
import Polyhedra.Antiprism.SquareAntiprism.Certificates.Root4
import Polyhedra.Antiprism.SquareAntiprism.Certificates.Root5
import Polyhedra.Antiprism.SquareAntiprism.Certificates.Root6
import Polyhedra.Antiprism.SquareAntiprism.Certificates.Root7
import Polyhedra.Antiprism.SquareAntiprism.Certificates.Root8
import Polyhedra.Antiprism.SquareAntiprism.Certificates.Root9
import Polyhedra.Antiprism.SquareAntiprism.Certificates.Root10
import Polyhedra.Antiprism.SquareAntiprism.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `prism/square-antiprism`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/nieuwland-exact-2026-11-18-prism/square-antiprism/exact.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Antiprism.SquareAntiprism.polyhedron` is `Θ` (`prismSquareAntiprism_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandPrismSquareAntiprism

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

end Nieuwland.Certs.NieuwlandPrismSquareAntiprism

namespace Nieuwland.Polyhedra

/-- **The fixture `prism/square-antiprism`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem prismSquareAntiprism_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandPrismSquareAntiprism.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandPrismSquareAntiprism.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandPrismSquareAntiprism.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Antiprism.SquareAntiprism.polyhedron.nieuwland) : Antiprism.SquareAntiprism.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandPrismSquareAntiprism.span_ok (roots := Nieuwland.Certs.NieuwlandPrismSquareAntiprism.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandPrismSquareAntiprism.far_field hc Nieuwland.Certs.NieuwlandPrismSquareAntiprism.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Certs.NieuwlandPrismSquareAntiprism

open Check Cert

/-- The claims' chart trees as texts, in the order of `claimBoxes`. -/
def claimTexts : List String :=
  [Lift.Claim0.data, Lift.Claim1.data]

/-- **The claims**: every claim's chart tree checks at the exact scale `Θ` on its box. -/
theorem claims_ok : List.Forall₂ (fun C t ↦ NativeS.checkT Lift.Theta Lift.points C t = true) claimBoxes claimTexts :=
  .cons Lift.Claim0.t_ok (.cons Lift.Claim1.t_ok (.nil))

end Nieuwland.Certs.NieuwlandPrismSquareAntiprism

namespace Nieuwland.Polyhedra

/-- **The fixture `prism/square-antiprism`: the Nieuwland number.** From the far field at `theta`, the claims' chart trees at the exact scale `Θ ≥ theta` and the weak fit at `Θ` (`Check.Polyhedron.nieuwland_eq_of_lift_smul`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem prismSquareAntiprism_nieuwland : Antiprism.SquareAntiprism.polyhedron.nieuwland = polyEval [401138297967955962521939087653858930317171309202939758406390055846226780995588049046494276960860952046761777/3326429733013566562758547069895858434897170109893807997142852616265703749079439702172722138587902508145088, -22179968853137351808287535748934867549266584634490082740668308894213419328992374259480860789638883010273012245/46570016262189931878619658978542018088560381538513311959999936627719852487112155830418109940230635114031232, -64353998431676640511636677394039203554509416086053460065937321264122558460435150928814759368741537838808479363/11642504065547482969654914744635504522140095384628327989999984156929963121778038957604527485057658778507808, -23830165174748908893827789777822882220437258383931936144198048509418255046957943846048715982500062324326293493/1455313008193435371206864343079438065267511923078540998749998019616245390222254869700565935632207347313476, -16610082511603668652599856336606145397324027263858367095039133164221216012333639822800503285553784600512522915/727656504096717685603432171539719032633755961539270499374999009808122695111127434850282967816103673656738, -2660442634031193939649868571487361681961176936830993210885919650650044393787433732906962952799025736001723395/207901858313347910172409191868491152181073131868362999821428288516606484317464981385795133661743906759068, 143026667156678270548203375070941228010855720050421756039492691915739198077942632100361901413584275915435297/21401661885197578988336240339403500959816351809978544099264676759062432209150806907361263759297166872257, 5767645367158581275721340168026767715910409317209439061693422034072033377273414330551546722064504229751910064/363828252048358842801716085769859516316877980769635249687499504904061347555563717425141483908051836828369, 3414008878417630804164821553150349886072835001190431326449891510846703324228243487282219983392250598481076496/363828252048358842801716085769859516316877980769635249687499504904061347555563717425141483908051836828369, -5382873142341080105246028224027626316328873567087427404675217807943885130455054307005144246571323827663240/51975464578336977543102297967122788045268282967090749955357072129151621079366245346448783415435976689767, -1045064125800219625878241124713677468971220100368682113195686165004703829108340780703570580703213755321020192/363828252048358842801716085769859516316877980769635249687499504904061347555563717425141483908051836828369, -63133576579067792064412608740449449537203035072256346330827224059308489067470362319968577789659185958181632/51975464578336977543102297967122788045268282967090749955357072129151621079366245346448783415435976689767, 50635478828035318964042917117382914194813670231162756919698247598202056660892611501727115042222656191591936/363828252048358842801716085769859516316877980769635249687499504904061347555563717425141483908051836828369, 66234740041795233194740374488286555276111843567150009002834140617863405053541820255161096410998475209179392/363828252048358842801716085769859516316877980769635249687499504904061347555563717425141483908051836828369, 2067513382527116966116936870785971999486609644560670973673853727709183378460173020040079269762567421897728/363828252048358842801716085769859516316877980769635249687499504904061347555563717425141483908051836828369, -2926266426613632597682505399416644010395326626610945130986794868221888077238841279577467529443450893139968/363828252048358842801716085769859516316877980769635249687499504904061347555563717425141483908051836828369] (realRoot [-315621285081599/29777713954816, 12822117623945/465276780544, 127503618260325/232638390272, 30990715596427/14539899392, 12891228359727/3186827264, 57595435243949/14539899392, 7268970530469/7269949696, -505761663183/227185928, -40644844512077/14539899392, -525616574933/454371856, 60330774695/227185928, 13171069798/28398241, 31521319703/227185928, -177442/5329, -123268/5329, 0, 1] 0 1) := by
  have hdim : Antiprism.SquareAntiprism.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandPrismSquareAntiprism.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandPrismSquareAntiprism.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandPrismSquareAntiprism.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_lift_smul Nieuwland.Certs.NieuwlandPrismSquareAntiprism.span_ok (roots := Nieuwland.Certs.NieuwlandPrismSquareAntiprism.roots) (by decide +kernel) (θ := Nieuwland.Certs.NieuwlandPrismSquareAntiprism.theta) (by decide +kernel) Nieuwland.Certs.NieuwlandPrismSquareAntiprism.far_field (c := (((1 : ℕ) : ℝ) * ((7480451506586347023639339643436154166516437004220527923490259608649020774471699479505417643101349130945855526583402066119695597568 : ℕ) : ℝ) ^ 3 / ((1846586106498868316616765538675087348331616866502460616903821653134324894705988562195667303903166925707227539408095609051276472126388134196483341677507402172850278147391657379629348657984644136017651637683660831662134130649385734519366647370993372754300047982592 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandPrismSquareAntiprism.Lift.points_eq ((Check.Scale.re_lift _ _).trans Nieuwland.Certs.NieuwlandPrismSquareAntiprism.Lift.thetaQ_re) Nieuwland.Certs.NieuwlandPrismSquareAntiprism.Lift.theta_le (Check.noFitRot_of_texts Nieuwland.Certs.NieuwlandPrismSquareAntiprism.claims_ok) Nieuwland.Certs.NieuwlandPrismSquareAntiprism.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandPrismSquareAntiprism.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
