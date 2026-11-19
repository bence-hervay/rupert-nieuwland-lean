import Modules.Nieuwland.Tree
import Modules.Nieuwland.Weak
import Modules.Nieuwland.Cover
import Modules.Check.Number.Theta

/-!
# Exact Nieuwland numbers: the assembly

An exact certificate of a Nieuwland number (`nieuwland certify`, `rupert check --weak-fit`) has
three parts, and this file puts their Lean checks together:

* the **far field** over the solid's field `κF` at a rational scale `θ′`: every pose of the unit
  chart boxes is settled at `θ′` or lies in a claim box (`Modules/Nieuwland/Cover.lean`);
* the **claims** over a lift `κE ⊇ κF` that holds the exact scale `Θ = λ*`: one chart tree per
  claim box, checked at `Θ` (`Modules/Nieuwland/Tree.lean`);
* the **weak fit** over `κE` at `Θ` (`Modules/Nieuwland/Weak.lean`).

With `θ′ ≤ Θ` and the points of the lift spanning the polyhedron of the far field's,
`Polyhedron.nieuwland_eq_of_lift` gives `nieuwland P = Θ`.

* `liftPts`, `ofPoints_liftPts`: integer points as exact values of the lift.
* `Scale.lift`, `Scale.re_lift`: a scale of `ℤ` in the lift.
* `noFitRot_of_claims`: the claims' checks give the claim facts of the cover.
* `NativeS.checkT`, `noFitRot_of_texts`: the same from the trees as texts, decoded by compiled
  code (a tree of thousands of nodes is too large a term to elaborate).
* `ZTheta.scale_re_eq`, `polyEval_X`: the scale of the header as a polynomial in the root `θ` of
  the lift's field; when it is the generator, `Θ = realRoot m lo hi`.
-/

open Matrix

namespace Nieuwland.Cert.NativeS

open Check

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] [Dec κ]

/-- The chart tree of a text: its entries, with the tree as the entry `tree`. -/
def decodeT (text : String) : Option (ChartTree κ) := do
  let env ← Syn.entries text
  Dec.dec env (← env["tree"]?)

/-- The check of the chart tree in `text` at the plug scale `Θ` on the box `B`
(`ChartTree.checkS`). -/
@[nospecialize]
def checkT (Θ : Scale κ) (pts : List (V3 κ)) (B : ChartBox) (text : String) : Bool :=
  match decodeT (κ := κ) text with
  | some T => T.checkS Θ pts B
  | none => false

/-- **Native chart trees at a scale.** If the tree in `text` checks at `Θ` on `B`, no pose of `B`
fits the plug scaled by `Θ`. -/
theorem noFitRot_of_checkT {Θ : Scale κ} {pts : List (V3 κ)} {B : ChartBox} {text : String}
    (h : checkT Θ pts B text = true) :
    (Polyhedron.ofPoints pts).NoFitRot B.poses (Θ.re • 1) := by
  unfold checkT at h
  split at h
  next T _ => exact ChartTree.checkS_sound h
  next => simp at h

end Nieuwland.Cert.NativeS

namespace Nieuwland.Check

/-- Integer points as exact values of `κ`. -/
def liftPts (κ : Type) [Add κ] [Sub κ] [Mul κ] [Exact κ] (pts : List (V3 ℤ)) : List (V3 κ) :=
  pts.map (V3.map Exact.ofInt)

/-- The lifted points span the polyhedron of the integer points. -/
theorem ofPoints_liftPts (κ : Type) [Add κ] [Sub κ] [Mul κ] [Exact κ] (pts : List (V3 ℤ)) :
    Polyhedron.ofPoints (liftPts κ pts) = Polyhedron.ofPoints pts := by
  have h : (liftPts κ pts).map Exact.reV = pts.map Exact.reV := by
    rw [liftPts, List.map_map]
    refine List.map_congr_left fun v _ ↦ ?_
    rw [Function.comp_apply, Exact.reV_map_ofInt, Exact.reV_int]
  unfold Polyhedron.ofPoints
  rw [h]

namespace Scale

/-- A scale of `ℤ` in `κ`. -/
def lift (κ : Type) [Add κ] [Sub κ] [Mul κ] [Exact κ] (s : Scale ℤ) : Scale κ :=
  ⟨Exact.ofInt s.num, s.den⟩

theorem re_lift (κ : Type) [Add κ] [Sub κ] [Mul κ] [Exact κ] (s : Scale ℤ) :
    (lift κ s).re = s.re := by
  simp only [re, lift, Exact.re_ofInt, Exact.re_int]

end Scale

/-- **The claims of an exact certificate**: one chart tree per claim box, each checked at the
scale `Θ`. No pose of a claim box fits the plug scaled by `Θ`. -/
theorem noFitRot_of_claims {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] {Θ : Scale κ}
    {pts : List (V3 κ)} {claims : List ChartBox} {trees : List (ChartTree κ)}
    (h : List.Forall₂ (fun C T ↦ ChartTree.checkS Θ pts C T = true) claims trees) :
    ∀ C ∈ claims, (Polyhedron.ofPoints pts).NoFitRot C.poses (Θ.re • 1) := by
  induction h with
  | nil => intro C hC; simp at hC
  | cons hab _ ih =>
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · exact ChartTree.checkS_sound hab
    · exact ih C hC

/-- **The claims of an exact certificate, as texts**: one chart tree per claim box, each a text
checked at the scale `Θ` by compiled code. No pose of a claim box fits the plug scaled by `Θ`. -/
theorem noFitRot_of_texts {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] [Cert.Dec κ]
    {Θ : Scale κ} {pts : List (V3 κ)} {claims : List ChartBox} {texts : List String}
    (h : List.Forall₂ (fun C t ↦ Cert.NativeS.checkT Θ pts C t = true) claims texts) :
    ∀ C ∈ claims, (Polyhedron.ofPoints pts).NoFitRot C.poses (Θ.re • 1) := by
  induction h with
  | nil => intro C hC; simp at hC
  | cons hab _ ih =>
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · exact Cert.NativeS.noFitRot_of_checkT hab
    · exact ih C hC

/-- **Exact Nieuwland numbers from a certificate over a lift.** For `P = a • (polyhedron of
ptsF)`, `a ≠ 0`, of full dimension:

* a far field over `κF` settled at `θ` outside the claim boxes;
* points `ptsE` over a lift `κE` that span the same polyhedron;
* a scale `Θ` of `κE` with `θ ≤ Θ` (`θE` is `θ` in `κE`);
* the claim facts at `Θ` over the lift's points (`noFitRot_of_texts`, `noFitRot_of_claims`: one
  chart tree per claim box, checked at `Θ`);
* a weak fit at `Θ`.

Then `nieuwland P = Θ`. -/
theorem Polyhedron.nieuwland_eq_of_lift {κF κE : Type} [Add κF] [Sub κF] [Mul κF] [Exact κF]
    [Countable κF] [Add κE] [Sub κE] [Mul κE] [Exact κE]
    {ptsF : List (V3 κF)} {D : SymmData κF} {i j k l : ℕ} (hspan : spanOk ptsF i j k l = true)
    {roots : List ChartBox} (hroots : unitsIn roots = true) {claims : List ChartBox}
    {θ : Scale κF} (hθ : θ.ok = true)
    (h : roots.Forall fun B ↦ ∀ p ∈ B.poses, SettledS ptsF D θ.re p ∨ ∃ C ∈ claims, p ∈ C.poses)
    {ptsE : List (V3 κE)} (hpts : Polyhedron.ofPoints ptsE = Polyhedron.ofPoints ptsF)
    {Θ θE : Scale κE} (hθE : θE.re = θ.re) (hle : θE.le Θ = true)
    (hc : ∀ C ∈ claims, (Polyhedron.ofPoints ptsE).NoFitRot C.poses (Θ.re • 1))
    {W : WeakFitData κE} (hW : W.check ptsE = true) (hWn : W.scaleNum = Θ.num)
    (hWd : W.scaleDen = Θ.den) {P : Polyhedron} {a : ℝ}
    (hP : P = (Polyhedron.ofPoints ptsF).smul a) (ha : a ≠ 0) (hdim : P.FullDim) :
    P.nieuwland = Θ.re := by
  have hlo : Θ.re ≤ P.nieuwland := by
    have h0 := W.le_nieuwland_smul hW ha (hpts ▸ hP) hdim
    rwa [WeakFitData.scale, hWn, hWd] at h0
  refine Polyhedron.nieuwland_eq_of_claims hspan hroots (Scale.re_nonneg_of_ok hθ) ?_ h ?_ hP ha
    hlo
  · rw [← hθE]
    exact Scale.re_le_of_le hle
  · rw [← hpts]
    exact hc

/-- The polynomial `X` at `x`. -/
theorem polyEval_X (x : ℝ) : polyEval [0, 1] x = x := by
  simp [polyEval, Finset.sum_range_succ]

namespace ZTheta

/-- **The scale of the header in the root of the lift.** The value with coordinates `l` (in
powers of `α = c θ`) over `S` is the rational polynomial `q` at `θ = realRoot m lo hi`. -/
theorem scale_re_eq {R : Root} {S : ℕ} {l : List ℤ} {q : List ℚ} (hS : 0 < S)
    (h : scaleOk R S l q = true) :
    (⟨⟨l⟩, S⟩ : Scale (ZTheta R)).re = polyEval q (realRoot R.m R.lo R.hi) := by
  have hS' : (S : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
  rw [Scale.re, div_eq_inv_mul]
  exact smul_re_eq (inv_mul_cancel₀ hS') h

end ZTheta

end Nieuwland.Check
