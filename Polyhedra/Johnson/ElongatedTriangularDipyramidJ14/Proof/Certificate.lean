import Polyhedra.Johnson.ElongatedTriangularDipyramidJ14.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Johnson.ElongatedTriangularDipyramidJ14.Certificates.Weak
import Polyhedra.Johnson.ElongatedTriangularDipyramidJ14.Certificates.Claim0
import Polyhedra.Johnson.ElongatedTriangularDipyramidJ14.Certificates.Root0
import Polyhedra.Johnson.ElongatedTriangularDipyramidJ14.Certificates.Root1
import Polyhedra.Johnson.ElongatedTriangularDipyramidJ14.Certificates.Root2
import Polyhedra.Johnson.ElongatedTriangularDipyramidJ14.Certificates.Root3
import Polyhedra.Johnson.ElongatedTriangularDipyramidJ14.Certificates.Root4
import Polyhedra.Johnson.ElongatedTriangularDipyramidJ14.Certificates.Root5
import Polyhedra.Johnson.ElongatedTriangularDipyramidJ14.Certificates.Root6
import Polyhedra.Johnson.ElongatedTriangularDipyramidJ14.Certificates.Root7
import Polyhedra.Johnson.ElongatedTriangularDipyramidJ14.Certificates.Root8
import Polyhedra.Johnson.ElongatedTriangularDipyramidJ14.Certificates.Root9
import Polyhedra.Johnson.ElongatedTriangularDipyramidJ14.Certificates.Root10
import Polyhedra.Johnson.ElongatedTriangularDipyramidJ14.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `johnson/elongated-triangular-dipyramid-j14`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/nieuwland-exact-2026-11-09/small/out/elongated-triangular-dipyramid-j14/exact.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Johnson.ElongatedTriangularDipyramidJ14.polyhedron` is `Θ` (`johnsonElongatedTriangularDipyramidJ14_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonElongatedTriangularDipyramidJ14

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

end Nieuwland.Certs.NieuwlandJohnsonElongatedTriangularDipyramidJ14

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/elongated-triangular-dipyramid-j14`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem johnsonElongatedTriangularDipyramidJ14_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandJohnsonElongatedTriangularDipyramidJ14.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandJohnsonElongatedTriangularDipyramidJ14.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandJohnsonElongatedTriangularDipyramidJ14.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Johnson.ElongatedTriangularDipyramidJ14.polyhedron.nieuwland) : Johnson.ElongatedTriangularDipyramidJ14.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandJohnsonElongatedTriangularDipyramidJ14.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonElongatedTriangularDipyramidJ14.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandJohnsonElongatedTriangularDipyramidJ14.far_field hc Nieuwland.Certs.NieuwlandJohnsonElongatedTriangularDipyramidJ14.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Certs.NieuwlandJohnsonElongatedTriangularDipyramidJ14

open Check Cert

/-- The claims' chart trees as texts, in the order of `claimBoxes`. -/
def claimTexts : List String :=
  [Lift.Claim0.data]

/-- **The claims**: every claim's chart tree checks at the exact scale `Θ` on its box. -/
theorem claims_ok : List.Forall₂ (fun C t ↦ NativeS.checkT Lift.Theta Lift.points C t = true) claimBoxes claimTexts :=
  .cons Lift.Claim0.t_ok (.nil)

end Nieuwland.Certs.NieuwlandJohnsonElongatedTriangularDipyramidJ14

namespace Nieuwland.Polyhedra

/-- **The fixture `johnson/elongated-triangular-dipyramid-j14`: the Nieuwland number.** From the far field at `theta`, the claims' chart trees at the exact scale `Θ ≥ theta` and the weak fit at `Θ` (`Check.Polyhedron.nieuwland_eq_of_lift_smul`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem johnsonElongatedTriangularDipyramidJ14_nieuwland : Johnson.ElongatedTriangularDipyramidJ14.polyhedron.nieuwland = polyEval [8036563749642755241820266815755676537/515944012035008083323275002268723200, 4046799589781268603302080822024794589/25797200601750404166163750113436160, -50809628821514826145126649170227026787/257972006017504041661637501134361600, -12063983095349055157642181713996446357/8061625188047001301926171910448800, 93900571604839108944124476415970715207/128986003008752020830818750567180800, 226704218088967603314406287117778956789/32246500752188005207704687641795200, -351032234661553623890167596222045322893/64493001504376010415409375283590400, -22149024898400711341024392760570931853/2015406297011750325481542977612200, 376017965286860990466222029412868544931/32246500752188005207704687641795200, 48309970542247450402210344504817505511/8061625188047001301926171910448800, -32085853127213789674217630792565113661/3224650075218800520770468764179520, 42910459522263958187514440327572179/100770314850587516274077148880610, 956843094325081391093253791755983645/322465007521880052077046876417952, -58159931917728730709141351696467269/80616251880470013019261719104488, -43314799943793826659841047223626015/161232503760940026038523438208976, 908811805664708897996076686221950/10077031485058751627407714888061] (realRoot [-68357183/1049760000, -691693/1215000, 1437037/607500, 8663521/1822500, -127851971/7290000, -2404043/101250, 4711387/50625, -15857/1875, -21469991/135000, 179914/1875, 563204/5625, -39836/375, -6319/1125, 856/25, -176/25, -16/5, 1] 0 (1/2)) := by
  have hdim : Johnson.ElongatedTriangularDipyramidJ14.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandJohnsonElongatedTriangularDipyramidJ14.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandJohnsonElongatedTriangularDipyramidJ14.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandJohnsonElongatedTriangularDipyramidJ14.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_lift_smul Nieuwland.Certs.NieuwlandJohnsonElongatedTriangularDipyramidJ14.span_ok (roots := Nieuwland.Certs.NieuwlandJohnsonElongatedTriangularDipyramidJ14.roots) (by decide +kernel) (θ := Nieuwland.Certs.NieuwlandJohnsonElongatedTriangularDipyramidJ14.theta) (by decide +kernel) Nieuwland.Certs.NieuwlandJohnsonElongatedTriangularDipyramidJ14.far_field (c := (((1 : ℕ) : ℝ) * ((391794984139084263273611954847811680000000000000 : ℕ) : ℝ) ^ 3 / ((716348778117211350660348796425228811443058998871848214983340395473971200000000000000000000000000 : ℕ) : ℝ))) (by norm_num) Nieuwland.Certs.NieuwlandJohnsonElongatedTriangularDipyramidJ14.Lift.points_eq ((Check.Scale.re_lift _ _).trans Nieuwland.Certs.NieuwlandJohnsonElongatedTriangularDipyramidJ14.Lift.thetaQ_re) Nieuwland.Certs.NieuwlandJohnsonElongatedTriangularDipyramidJ14.Lift.theta_le (Check.noFitRot_of_texts Nieuwland.Certs.NieuwlandJohnsonElongatedTriangularDipyramidJ14.claims_ok) Nieuwland.Certs.NieuwlandJohnsonElongatedTriangularDipyramidJ14.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandJohnsonElongatedTriangularDipyramidJ14.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
