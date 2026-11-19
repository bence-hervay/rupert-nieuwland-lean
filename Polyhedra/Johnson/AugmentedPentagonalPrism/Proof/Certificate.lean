import Polyhedra.Johnson.AugmentedPentagonalPrism.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Johnson.AugmentedPentagonalPrism.Certificates.Weak
import Polyhedra.Johnson.AugmentedPentagonalPrism.Certificates.Root0
import Polyhedra.Johnson.AugmentedPentagonalPrism.Certificates.Root1
import Polyhedra.Johnson.AugmentedPentagonalPrism.Certificates.Root2
import Polyhedra.Johnson.AugmentedPentagonalPrism.Certificates.Root3
import Polyhedra.Johnson.AugmentedPentagonalPrism.Certificates.Root4
import Polyhedra.Johnson.AugmentedPentagonalPrism.Certificates.Root5
import Polyhedra.Johnson.AugmentedPentagonalPrism.Certificates.Root6
import Polyhedra.Johnson.AugmentedPentagonalPrism.Certificates.Root7
import Polyhedra.Johnson.AugmentedPentagonalPrism.Certificates.Root8
import Polyhedra.Johnson.AugmentedPentagonalPrism.Certificates.Root9
import Polyhedra.Johnson.AugmentedPentagonalPrism.Certificates.Root10
import Polyhedra.Johnson.AugmentedPentagonalPrism.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `johnson/augmented-pentagonal-prism`: an exact Nieuwland number from a cover at the exact scale

The exact certificate `gs://main-69696-data/noperts-results/jch2-2026-11-15/augmented-pentagonal-prism/exact.jsonl`, exported by `code/lean-export scaled --fit`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the exact scale `Θ` over the lift (`Lift.Root<k>.settled`: chord pairs, supports and excluded leaves), so the lift's polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough`); with the weak fit at `Θ` (`Lift.weak_check`) the Nieuwland number of `Johnson.AugmentedPentagonalPrism.polyhedron` is `Θ`.
-/

namespace Nieuwland.Certs.NieuwlandJohnsonAugmentedPentagonalPrism

open Check Cert

/-- The roots of the cover. -/
def roots : List ChartBox :=
  [Lift.Root0.box, Lift.Root1.box, Lift.Root2.box, Lift.Root3.box, Lift.Root4.box, Lift.Root5.box, Lift.Root6.box, Lift.Root7.box, Lift.Root8.box, Lift.Root9.box, Lift.Root10.box, Lift.Root11.box]

/-- **The certificate**: the lift's polyhedron scaled by `Θ` does not fit through it. -/
theorem not_fitsThrough : ¬ ((Polyhedron.ofPoints Lift.points).smul Lift.Theta.re).FitsThrough (Polyhedron.ofPoints Lift.points) :=
  Polyhedron.not_fitsThrough_smul_of_roots Lift.span_ok (roots := roots) (by decide +kernel) (by simp only [roots, List.Forall]; exact ⟨Lift.Root0.settled, Lift.Root1.settled, Lift.Root2.settled, Lift.Root3.settled, Lift.Root4.settled, Lift.Root5.settled, Lift.Root6.settled, Lift.Root7.settled, Lift.Root8.settled, Lift.Root9.settled, Lift.Root10.settled, Lift.Root11.settled⟩)

end Nieuwland.Certs.NieuwlandJohnsonAugmentedPentagonalPrism

namespace Nieuwland.Polyhedra

open Check

/-- **The fixture `johnson/augmented-pentagonal-prism`: the Nieuwland number.** From the cover at the exact scale `Θ` and the weak fit there (`Check.Polyhedron.nieuwland_eq_of_not_fitsThrough_lift`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem johnsonAugmentedPentagonalPrism_nieuwland : Johnson.AugmentedPentagonalPrism.polyhedron.nieuwland = polyEval [0, -95355390285516727832925428852123700350229488600118670776877777662668825714725514521243547994405617571951049/100709755163188485641322780501698605224918399983822397926705043667408022101300199634307434340546630411777200, 0, 634081442627221531558200440147271605706318286246800268507090948774141688299315606136644318046564925635689/402839020652753942565291122006794420899673599935289591706820174669632088405200798537229737362186521647108800, 0, -92552291746507975813966099822796750597871483636303743098642744609515309102295448679281924645375392423/134279673550917980855097040668931473633224533311763197235606724889877362801733599512409912454062173882369600, 0, 42366911056559221812774910920004394346968418408960492164898483538784326659002748751367207712764149/429694955362937538736310530140580715626318506597642231153941519647607560965547518439711719852998956423582720, 0, -3258182456041441691150890404595533900519232212708476494354275336890656893939365706621699480619/1289084866088812616208931590421742146878955519792926693461824558942822682896642555319135159558996869270748160, 0, 2678295755472768608239548243469706842422685007726232806242042293788652967667413587252547987/103126789287105009296714527233739371750316441583434135476945964715425814631731404425530812764719749541659852800, 0, -16351381860247186081050375124274795725817642170624632289949818018672211113703383592609/137502385716140012395619369644985829000421922111245513969261286287234419508975205900707750352959666055546470400, 0, 166771489144197141259602599339866903849668644274747673496725305350926574121824249/825014314296840074373716217869914974002531532667473083815567717723406517053851235404246502117757996333278822400] (realRoot [71661770526378701432095321338944532054016/13845841, 0, -193085728852325013198066754261142142976/13845841, 0, 172001288663510435678937770170949632/13845841, 0, -57433224590408183607639011115008/13845841, 0, 7019361447765460723493487360/13845841, 0, -2883127159278314755072/226981, 0, 481457608726432/3721, 0, -35979824/61, 0, 1] (-931183808387043/2199023255552) (-931183741278179/2199023255552)) := by
  have hdim : Johnson.AugmentedPentagonalPrism.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandJohnsonAugmentedPentagonalPrism.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandJohnsonAugmentedPentagonalPrism.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandJohnsonAugmentedPentagonalPrism.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_not_fitsThrough_lift (c := (((1 : ℕ) : ℝ) * ((4595149427272695235582715886442519933991906820144011773762403893159850684721810505264943713282411655894998026860625976076092519219200 : ℕ) : ℝ) ^ 7 / ((126415571631057791498033479007555636025019566504617429135631029686412809258462353862036027180954339237808750465239672613312142731708839770810612666644619019094407908902057232088331015326544138142593050798886151685033013377330479596252990149734079795802183773815428096382301760619728443210756635830602976186792320905262086868565921816341965321327901020622068902134121242984010733034227073009685803836842196858392006477644445305072483733646527329832296415382251957708767454208490635813874123641513916286272038392943838756478941634625486581821970968243471193695640710543574170047281058426713306437897245674091125062165849924411951519837604106957180899976445733639277632266681826435514470319763180444148496384644965066625320170522638518343684648503192857706068001489722370745708335595520000000000000 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandJohnsonAugmentedPentagonalPrism.Lift.points_eq (Check.Scale.re_nonneg_of_ok (by decide +kernel)) Nieuwland.Certs.NieuwlandJohnsonAugmentedPentagonalPrism.not_fitsThrough Nieuwland.Certs.NieuwlandJohnsonAugmentedPentagonalPrism.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandJohnsonAugmentedPentagonalPrism.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
