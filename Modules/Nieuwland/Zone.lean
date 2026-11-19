import Modules.Nieuwland.Embed

/-!
# Claims at scale 1 in an exact certificate

The claims of an exact certificate (`Modules/Nieuwland/Exact.lean`) are of two kinds. Around the
optimal poses a claim is a chart tree at the exact scale `Θ`, over the lift. Around the identity
(and wherever the solid as it is has no fit on a box) a claim is evidence at scale 1, over the
solid's own field, as in a certificate that the solid is a Nopert: a weighted or polar zoom, or a
chart tree, possibly with exclusion leaves of the symmetry data. Such a claim settles its box at
scale 1 (`Settled`), and a pose settled at scale 1 is settled at every `Θ ≥ 1`
(`settledS_of_settled`: Lemma M, `SettledS.mono`).

* `Native.Ext.has`, `Native.boxesCheck`: every box of a list lies in the region of a claim or a
  leaf of a claims text (`Modules/Certificate/Native.lean`), without a pre-rotation.
* `Native.settled_of_boxesCheck`: with the text's own check (`Native.claimsCheck`, in its claims
  module), every pose of every such box is settled.
* `settledS_of_trees_zones`: the claim facts of a list of claim boxes `trees ++ zones`, from no
  fit at `Θ` on the boxes `trees` over the lift's points and settled poses on the boxes `zones`
  over the far field's.
* `Polyhedron.nieuwland_eq_of_lift_zones`: the assembly of `nieuwland_eq_of_lift_smul` with both
  kinds of claims.
-/

namespace Nieuwland

namespace Cert.Native

open Check

section Boxes

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- Some claim or leaf of the claims module has the box `B` in its region, without a
pre-rotation. -/
def Ext.has (e : Ext κ) (B : ChartBox) : Bool :=
  e.claims.toList.any (fun c ↦ Leaf.ok B none (.claim c)) || e.leaves.toList.any (Leaf.ok B none)

/-- **Boxes of a checked claims module are settled.** -/
theorem Ext.settled_of_has {pts : List (V3 κ)} {D : SymmData κ} {depth : ℕ}
    (hD : D.ok pts = true) {e : Ext κ} (he : e.check pts D depth = true) {B : ChartBox}
    (hB : e.has B = true) : ∀ p ∈ B.poses, Settled pts D p := by
  simp only [Ext.check, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at he
  have key : ∀ l : Leaf κ, l.check pts D depth = true → Leaf.ok B none l = true →
      ∀ p ∈ B.poses, Settled pts D p := by
    intro l hl hok p hp
    simp only [Leaf.ok, Bool.and_eq_true] at hok
    have hs := Leaf.check_sound hD hl p (ChartBox.poses_subset hok.1 hp)
    rw [Exact.rePre_eq_of_preEq hok.2] at hs
    exact settledRot_none.mp hs
  simp only [Ext.has, Bool.or_eq_true, List.any_eq_true] at hB
  rcases hB with ⟨c, hc, hok⟩ | ⟨l, hl, hok⟩
  · exact key (.claim c) (he.1 c (Array.mem_def.mpr hc)) hok
  · exact key l (he.2 l (Array.mem_def.mpr hl)) hok

variable [Dec κ]

/-- Every box of `boxes` lies in the region of a claim or a leaf of the claims text `text`,
without a pre-rotation (`pts` gives the type of the field). -/
@[nospecialize]
def boxesCheck (_pts : List (V3 κ)) (text : String) (boxes : List ChartBox) : Bool :=
  match decodeClaims (κ := κ) text with
  | some e => boxes.all e.has
  | none => false

/-- **The boxes of a claims text.** If the claims text checks (`claimsCheck`, in its claims
module) and every box of `boxes` lies in the region of one of its claims or leaves, every pose
of every box is settled. -/
theorem settled_of_boxesCheck {pts : List (V3 κ)} {D : SymmData κ} {depth : ℕ} {text : String}
    {boxes : List ChartBox} (hD : D.ok pts = true)
    (hok : claimsCheck pts D depth text = true) (hb : boxesCheck pts text boxes = true) :
    ∀ B ∈ boxes, ∀ p ∈ B.poses, Settled pts D p := by
  unfold claimsCheck at hok
  unfold boxesCheck at hb
  split at hok
  next e he =>
    rw [he] at hb
    simp only [List.all_eq_true] at hb
    exact fun B hB ↦ Ext.settled_of_has hD hok (hb B hB)
  next => simp at hok

end Boxes

end Cert.Native

namespace Check

variable {κF κE : Type} [Add κF] [Sub κF] [Mul κF] [Exact κF] [Add κE] [Sub κE] [Mul κE]
  [Exact κE]

/-- **A pose settled at scale 1 is settled at every plug scale `Θ ≥ 1`** (Lemma M). -/
theorem settledS_of_settled {pts : List (V3 κF)} {D : SymmData κF} {Θ : ℝ} {p : ChartPose}
    (h : Settled pts D p) (hΘ : 1 ≤ Θ) : SettledS pts D Θ p := by
  have h1 : SettledS pts D 1 p := by
    rcases h with h | h | h
    · refine Or.inl fun hfit ↦ ?_
      rw [one_smul] at hfit
      obtain ⟨τ, hτ⟩ := hfit.exists_fitsAt (p := p) one_ne_zero (one_smul ℝ _).symm rfl
      exact h τ hτ
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  exact h1.mono zero_le_one hΘ

/-- **The claim facts of an exact certificate with claims of both kinds.** For claim boxes
`trees ++ zones`: no fit at `Θ` on the boxes `trees` over the lift's points (a multiple of the
far field's) and settled poses at scale 1 on the boxes `zones` over the far field's points
settle every pose of every claim box at `Θ ≥ 1`. -/
theorem settledS_of_trees_zones {ptsF : List (V3 κF)} {D : SymmData κF} {ptsE : List (V3 κE)}
    {c : ℝ} (hc : c ≠ 0)
    (hpts : Polyhedron.ofPoints ptsE = (Polyhedron.ofPoints ptsF).smul c) {Θ : ℝ}
    {claims trees zones : List ChartBox} (hsplit : claims = trees ++ zones)
    (ht : ∀ C ∈ trees, (Polyhedron.ofPoints ptsE).NoFitRot C.poses (Θ • 1))
    (hz : ∀ C ∈ zones, ∀ p ∈ C.poses, Settled ptsF D p) (hΘ : 1 ≤ Θ) :
    ∀ C ∈ claims, ∀ p ∈ C.poses, SettledS ptsF D Θ p := by
  subst hsplit
  intro C hC
  rcases List.mem_append.mp hC with hC | hC
  · have h1 := ht C hC
    rw [hpts] at h1
    exact settledS_of_noFitRot ((Polyhedron.noFitRot_smul_iff hc).mp h1)
  · exact fun p hp ↦ settledS_of_settled (hz C hC p hp) hΘ

/-- **Exact Nieuwland numbers from a certificate over a lift with claims of both kinds.** As
`Polyhedron.nieuwland_eq_of_lift_smul` (`c = 1` for a rational solid, `Polyhedron.smul_one`),
with the claim boxes `trees ++ zones`: one chart tree at `Θ` per box of `trees`
(`noFitRot_of_texts`), settled poses at scale 1 on the boxes `zones`
(`Cert.Native.settled_of_boxesCheck`), and `1 ≤ Θ`. -/
theorem Polyhedron.nieuwland_eq_of_lift_zones [Countable κF]
    {ptsF : List (V3 κF)} {D : SymmData κF} {i j k l : ℕ} (hspan : spanOk ptsF i j k l = true)
    {roots : List ChartBox} (hroots : unitsIn roots = true) {claims : List ChartBox}
    {θ : Scale κF} (hθ : θ.ok = true)
    (h : roots.Forall fun B ↦ ∀ p ∈ B.poses, SettledS ptsF D θ.re p ∨ ∃ C ∈ claims, p ∈ C.poses)
    {trees zones : List ChartBox} (hsplit : claims = trees ++ zones)
    {ptsE : List (V3 κE)} {c : ℝ} (hc : c ≠ 0)
    (hpts : Polyhedron.ofPoints ptsE = (Polyhedron.ofPoints ptsF).smul c)
    {Θ θE : Scale κE} (hθE : θE.re = θ.re) (hle : θE.le Θ = true)
    (hcl : ∀ C ∈ trees, (Polyhedron.ofPoints ptsE).NoFitRot C.poses (Θ.re • 1))
    (hz : ∀ C ∈ zones, ∀ p ∈ C.poses, Settled ptsF D p)
    (h1 : (Scale.one : Scale κE).le Θ = true)
    {W : WeakFitData κE} (hW : W.check ptsE = true) (hWn : W.scaleNum = Θ.num)
    (hWd : W.scaleDen = Θ.den) {P : Polyhedron} {a : ℝ}
    (hP : P = (Polyhedron.ofPoints ptsF).smul a) (ha : a ≠ 0) (hdim : P.FullDim) :
    P.nieuwland = Θ.re := by
  have hlo : Θ.re ≤ P.nieuwland := by
    have hP' : P = (Polyhedron.ofPoints ptsE).smul (a * c⁻¹) := by
      rw [hpts, Polyhedron.smul_smul_eq, inv_mul_cancel_right₀ hc]
      exact hP
    have h0 := W.le_nieuwland_smul hW (mul_ne_zero ha (inv_ne_zero hc)) hP' hdim
    rwa [WeakFitData.scale, hWn, hWd] at h0
  have hΘ : 1 ≤ Θ.re := by
    have := Scale.re_le_of_le h1
    rwa [Scale.re_one] at this
  refine Polyhedron.nieuwland_eq_of_settled_claims hspan hroots (Scale.re_nonneg_of_ok hθ) ?_ h
    (settledS_of_trees_zones hc hpts hsplit hcl hz hΘ) hP ha hlo
  rw [← hθE]
  exact Scale.re_le_of_le hle

end Check

end Nieuwland
