import Polyhedra.Other.HexagonalTrapezohedron.Proof.Points
import Polyhedra.Other.HexagonalTrapezohedron.Certificates.Touch
import Polyhedra.Other.HexagonalTrapezohedron.Certificates.Zones
import Polyhedra.Other.HexagonalTrapezohedron.Certificates.Root0
import Polyhedra.Other.HexagonalTrapezohedron.Certificates.Root1
import Polyhedra.Other.HexagonalTrapezohedron.Certificates.Root2
import Polyhedra.Other.HexagonalTrapezohedron.Certificates.Root3
import Polyhedra.Other.HexagonalTrapezohedron.Certificates.Root4
import Polyhedra.Other.HexagonalTrapezohedron.Certificates.Root5
import Polyhedra.Other.HexagonalTrapezohedron.Certificates.Root6
import Polyhedra.Other.HexagonalTrapezohedron.Certificates.Root7
import Polyhedra.Other.HexagonalTrapezohedron.Certificates.Root8
import Polyhedra.Other.HexagonalTrapezohedron.Certificates.Root9
import Polyhedra.Other.HexagonalTrapezohedron.Certificates.Root10
import Polyhedra.Other.HexagonalTrapezohedron.Certificates.Root11

set_option linter.style.longLine false

/-!
# The fixture `trapezohedron/hexagonal-trapezohedron`: the far field of an exact Nieuwland number

The far field of the scaled certificate `gs://main-69696-data/noperts-results/nieuwland-exact-2026-11-21b-trapezohedron/hexagonal-trapezohedron/far.jsonl`, exported by `code/lean-export scaled`: the roots cover the twelve unit chart boxes (`unitsIn`) and every pose of every root is settled at the leaves' largest plug scale `theta` or lies in one of the claim boxes `claimBoxes` (`far_field`). The claims are hypotheses: for every `Θ ≥ theta` at which no pose of a claim box fits, the polyhedron scaled by `Θ` does not fit through itself (`not_fitsThrough_of_claims`), and with the lower bound `Θ ≤ nieuwland` (a weak fit at `Θ`) the Nieuwland number of `Other.HexagonalTrapezohedron.polyhedron` is `Θ` (`trapezohedronHexagonalTrapezohedron_nieuwland_eq_of_claims`).
-/

namespace Nieuwland.Certs.NieuwlandTrapezohedronHexagonalTrapezohedron

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

/-- **A far field with claims at scale 1 keeps only its other claim boxes.** For claim boxes `ts ++ zs` with every pose of the boxes `zs` settled at scale 1, a far field at `θ ≥ 1` is one with the claim boxes `ts` alone: a pose in a box of `zs` is settled at `θ` (`settledS_of_settled`, Lemma M). The old library's `far_field_of_zones`, stated here because the library of this tree does not have it. -/
theorem far_field_drop_zones {κF : Type} [Add κF] [Sub κF] [Mul κF] [Exact κF] {pts : List (V3 κF)} {D : SymmData κF} {θ : ℝ}
    {rs cs ts zs : List ChartBox} (hsplit : cs = ts ++ zs)
    (h : rs.Forall fun B ↦ ∀ p ∈ B.poses, SettledS pts D θ p ∨ ∃ C ∈ cs, p ∈ C.poses)
    (hz : ∀ C ∈ zs, ∀ p ∈ C.poses, Settled pts D p) (hθ : 1 ≤ θ) :
    rs.Forall fun B ↦ ∀ p ∈ B.poses, SettledS pts D θ p ∨ ∃ C ∈ ts, p ∈ C.poses := by
  subst hsplit
  rw [List.forall_iff_forall_mem] at h ⊢
  intro B hB p hp
  rcases h B hB p hp with hs | ⟨C, hC, hpC⟩
  · exact Or.inl hs
  · rcases List.mem_append.mp hC with hC | hC
    · exact Or.inr ⟨C, hC, hpC⟩
    · exact Or.inl (settledS_of_settled (hz C hC p hpC) hθ)

/-- **The far field without the claims at scale 1**: every pose of every root is settled at `theta` or lies in a touch leaf's box. The claims at scale 1 settle their boxes at scale 1 (`Zones.settled`), so at `theta ≥ 1` too (`far_field_drop_zones`, Lemma M). -/
theorem far_field_touch : roots.Forall fun B ↦ ∀ p ∈ B.poses, SettledS points symm theta.re p ∨ ∃ C ∈ touchBoxes, p ∈ C.poses :=
  far_field_drop_zones rfl far_field Zones.settled (by rw [theta_re]; norm_num)

end Nieuwland.Certs.NieuwlandTrapezohedronHexagonalTrapezohedron

namespace Nieuwland.Polyhedra

/-- **The fixture `trapezohedron/hexagonal-trapezohedron`: the exact Nieuwland number from the far field and the claims.** For `Θ ≥ theta` with no fit at `Θ` in the claim boxes and `Θ ≤ nieuwland`, the Nieuwland number is `Θ`. -/
theorem trapezohedronHexagonalTrapezohedron_nieuwland_eq_of_claims {Θ : ℝ} (hle : Nieuwland.Certs.NieuwlandTrapezohedronHexagonalTrapezohedron.theta.re ≤ Θ) (hc : ∀ C ∈ Nieuwland.Certs.NieuwlandTrapezohedronHexagonalTrapezohedron.claimBoxes, (Polyhedron.ofPoints Nieuwland.Certs.NieuwlandTrapezohedronHexagonalTrapezohedron.points).NoFitRot C.poses (Θ • 1)) (hlo : Θ ≤ Other.HexagonalTrapezohedron.polyhedron.nieuwland) : Other.HexagonalTrapezohedron.polyhedron.nieuwland = Θ :=
  Check.Polyhedron.nieuwland_eq_of_claims Nieuwland.Certs.NieuwlandTrapezohedronHexagonalTrapezohedron.span_ok (roots := Nieuwland.Certs.NieuwlandTrapezohedronHexagonalTrapezohedron.roots) (by decide +kernel) (Check.Scale.re_nonneg_of_ok (by decide +kernel)) hle Nieuwland.Certs.NieuwlandTrapezohedronHexagonalTrapezohedron.far_field hc Nieuwland.Certs.NieuwlandTrapezohedronHexagonalTrapezohedron.eq_smul (by norm_num) hlo

end Nieuwland.Polyhedra

namespace Nieuwland.Polyhedra

open Check

/-- **The fixture `trapezohedron/hexagonal-trapezohedron`: the Nieuwland number in root form.** The unknowns of a root's system are the pose `(s, t, x₁, x₂, x₃)` in its charts, the translation `(y₁, y₂)` of the plug's shadow, the scale `l` (the unknown `7`) and one multiplier per contact; its equations are the contacts' slacks and the stationarity of `l` under them (`Root.Sys.eqs`). The system has exactly one zero `y` in its box (Krawczyk's test), and the Nieuwland number is the scale there: the far field at `theta`, the touch leaf and the weak fit at the root (`Root.nieuwland_eq_of_certOkW_one`). -/
theorem trapezohedronHexagonalTrapezohedron_nieuwland : ∃ y, ((Nieuwland.Certs.NieuwlandTrapezohedronHexagonalTrapezohedron.touch0).kraw Nieuwland.Certs.NieuwlandTrapezohedronHexagonalTrapezohedron.points).IsZero (Root.basisPar (ZTheta Nieuwland.Certs.NieuwlandTrapezohedronHexagonalTrapezohedron.root)) y ∧ Other.HexagonalTrapezohedron.polyhedron.nieuwland = ((Nieuwland.Certs.NieuwlandTrapezohedronHexagonalTrapezohedron.touch0).kraw Nieuwland.Certs.NieuwlandTrapezohedronHexagonalTrapezohedron.points).env (Root.basisPar (ZTheta Nieuwland.Certs.NieuwlandTrapezohedronHexagonalTrapezohedron.root)) y 7 :=
  Root.nieuwland_eq_of_certOkW_one Nieuwland.Certs.NieuwlandTrapezohedronHexagonalTrapezohedron.span_ok (roots := Nieuwland.Certs.NieuwlandTrapezohedronHexagonalTrapezohedron.roots) (by decide +kernel) (by decide +kernel) Nieuwland.Certs.NieuwlandTrapezohedronHexagonalTrapezohedron.far_field_touch Nieuwland.Certs.NieuwlandTrapezohedronHexagonalTrapezohedron.eq_smul (by norm_num) rfl Nieuwland.Certs.NieuwlandTrapezohedronHexagonalTrapezohedron.touch_ok

/-- **The fixture `trapezohedron/hexagonal-trapezohedron`: the Nieuwland number to 40 decimals.** -/
theorem trapezohedronHexagonalTrapezohedron_nieuwland_mem : Other.HexagonalTrapezohedron.polyhedron.nieuwland ∈ Set.Icc (((10000006133966885370781452429632375679869 : ℤ) : ℝ) / 10 ^ 40) (((10000006133966885370781452429632375679872 : ℤ) : ℝ) / 10 ^ 40) :=
  Root.nieuwland_mem_Icc_of_certOkW Nieuwland.Certs.NieuwlandTrapezohedronHexagonalTrapezohedron.span_ok (roots := Nieuwland.Certs.NieuwlandTrapezohedronHexagonalTrapezohedron.roots) (by decide +kernel) (by decide +kernel) Nieuwland.Certs.NieuwlandTrapezohedronHexagonalTrapezohedron.far_field_touch Nieuwland.Certs.NieuwlandTrapezohedronHexagonalTrapezohedron.eq_smul (by norm_num) rfl Nieuwland.Certs.NieuwlandTrapezohedronHexagonalTrapezohedron.touch_ok Nieuwland.Certs.NieuwlandTrapezohedronHexagonalTrapezohedron.touch_in

end Nieuwland.Polyhedra
