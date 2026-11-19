import Modules.Nieuwland.Mult
import Modules.Nieuwland.Supports
import Modules.Nieuwland.Chord
import Modules.Certificate.Native

/-!
# Scaled cover trees and their native check

A scaled certificate's cover (`notes/nieuwland-lean.md`) is a `Cover` of scaled leaves (`SLeaf`)
over the boxes of the stream's split steps. Each leaf is evidence for the box of its node:

* `.centred s w`: a centred support at its own plug scale `s` (`Centred.checkScaled`), which
  must satisfy `0 ≤ s ≤ Θ` (`Scale.ok`, `Scale.le`): no fit of `s P` gives none of `Θ P`
  (`NoFitRot.smul_of_le`);
* `.balanced s w`, `.width s w`: a balanced or width support at its plug scale `s`
  (`Balanced.checkScaled`, `Width.checkScaled`), with `0 ≤ s ≤ Θ` as for centred supports;
* `.mult s m`: a multiplier leaf at its plug scale `s` (`Mult.check`), with `0 ≤ s ≤ Θ`;
* `.chord s w`: a chord pair at its plug scale `s` (`Chord.checkScaled`,
  `Modules/Nieuwland/Chord.lean`), with `0 ≤ s ≤ Θ`;
* `.excl i j`: an excluded leaf of the symmetry data (`Excl.check`), which does not depend on the
  scale;
* `.claim k`: the box lies in the box `k` of a list of claim boxes (`ChartBox.subset`). The leaf
  proves nothing by itself: its poses are left to facts about the claim boxes, hypotheses of the
  assembled theorem: every pose of a claim box is settled at `Θ`
  (`Polyhedron.not_fitsThrough_smul_of_settled_claims`), which holds where no pose of the box fits
  at `Θ` (`Polyhedron.not_fitsThrough_smul_of_claims`) and where the box is settled at scale 1
  (`Modules/Nieuwland/Zone.lean`).

`SCover.settledS_or_claim_of_check` proves every pose of the box settled at `Θ` (`SettledS`) or in
a claim box; without claim boxes (`SCover.settledS_of_check`) every pose is settled. The native
form (`NativeS.checkC`, and `NativeS.check` without claim boxes) decodes the tree from the entry
`cover` of a text of entries `@name term` (`Cert/Syn.lean`; the decoder is not trusted) and is
evaluated by `native_decide`, as the chunks of whole certificates are (`Cert/Native.lean`).
-/

namespace Nieuwland.Check

/-- A leaf of a scaled cover tree, evidence for the box of its node. -/
inductive SLeaf (κ : Type) where
  /-- A centred support at the plug scale `s`. -/
  | centred (s : Scale κ) (w : Centred κ)
  /-- An excluded leaf of the symmetry pair `(i, j)`. -/
  | excl (i j : ℕ)
  /-- A balanced support at the plug scale `s`. -/
  | balanced (s : Scale κ) (w : Balanced)
  /-- A width support at the plug scale `s`. -/
  | width (s : Scale κ) (w : Width κ)
  /-- A multiplier leaf at the plug scale `s`. -/
  | mult (s : Scale κ) (m : MLeaf κ)
  /-- A chord pair at the plug scale `s`. -/
  | chord (s : Scale κ) (w : Chord)
  /-- The box lies in the claim box `k`. -/
  | claim (k : ℕ)

namespace SLeaf

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The check of the leaf on the box `B`, for the plug scale `Θ` and the claim boxes
`claims`. -/
def check (claims : List ChartBox) (pts : List (V3 κ)) (D : SymmData κ) (Θ : Scale κ)
    (depth : ℕ) (B : ChartBox) : SLeaf κ → Bool
  | centred s w => s.ok && s.le Θ && w.checkScaled pts B depth s
  | excl i j => (Excl.mk B i j).check D depth
  | balanced s w => s.ok && s.le Θ && w.checkScaled pts B depth s
  | width s w => s.ok && s.le Θ && w.checkScaled pts B depth s
  | mult s m => s.ok && s.le Θ && Mult.check pts B s m
  | chord s w => s.ok && s.le Θ && w.checkScaled pts B depth s
  | claim k => match claims[k]? with
    | some C => B.subset C
    | none => false

/-- A leaf at a plug scale `0 ≤ s ≤ Θ` with no fit at `s` settles its box at `Θ`. -/
theorem settledS_of_scaled {pts : List (V3 κ)} {D : SymmData κ} {Θ s : Scale κ} {B : ChartBox}
    (hok : s.ok = true) (hle : s.le Θ = true)
    (h : (Polyhedron.ofPoints pts).NoFitRot B.poses (s.re • 1)) :
    ∀ p ∈ B.poses, SettledS pts D Θ.re p :=
  settledS_of_noFitRot (Polyhedron.NoFitRot.smul_of_le h (Scale.re_nonneg_of_ok hok)
    (Scale.re_le_of_le hle))

/-- **Soundness of scaled leaves**: every pose of the box is settled at `Θ` or lies in a claim
box. -/
theorem check_sound {claims : List ChartBox} {pts : List (V3 κ)} {D : SymmData κ} {Θ : Scale κ}
    {depth : ℕ} {B : ChartBox} {l : SLeaf κ} (hD : D.ok pts = true)
    (h : l.check claims pts D Θ depth B = true) :
    ∀ p ∈ B.poses, SettledS pts D Θ.re p ∨ ∃ C ∈ claims, p ∈ C.poses := by
  cases l with
  | centred s w =>
    simp only [check, Bool.and_eq_true] at h
    obtain ⟨⟨hok, hle⟩, hw⟩ := h
    have h0 := Centred.checkScaled_sound_pre hw
    rw [Exact.rePre_none, preRot_none] at h0
    exact fun p hp ↦ Or.inl (settledS_of_scaled hok hle h0 p hp)
  | excl i j =>
    exact fun p hp ↦ Or.inl (settledS_of_excluded (Excl.check_sound hD h p hp))
  | balanced s w =>
    simp only [check, Bool.and_eq_true] at h
    obtain ⟨⟨hok, hle⟩, hw⟩ := h
    have h0 := Balanced.checkScaled_sound_pre hw
    rw [Exact.rePre_none, preRot_none] at h0
    exact fun p hp ↦ Or.inl (settledS_of_scaled hok hle h0 p hp)
  | width s w =>
    simp only [check, Bool.and_eq_true] at h
    obtain ⟨⟨hok, hle⟩, hw⟩ := h
    have h0 := Width.checkScaled_sound_pre hw
    rw [Exact.rePre_none, preRot_none] at h0
    exact fun p hp ↦ Or.inl (settledS_of_scaled hok hle h0 p hp)
  | mult s m =>
    simp only [check, Bool.and_eq_true] at h
    obtain ⟨⟨hok, hle⟩, hm⟩ := h
    exact fun p hp ↦ Or.inl (settledS_of_scaled hok hle (Mult.check_sound hm) p hp)
  | chord s w =>
    simp only [check, Bool.and_eq_true] at h
    obtain ⟨⟨hok, hle⟩, hw⟩ := h
    exact fun p hp ↦ Or.inl (settledS_of_scaled hok hle (Chord.checkScaled_sound hw) p hp)
  | claim k =>
    simp only [check] at h
    split at h
    next C hC =>
      exact fun p hp ↦ Or.inr ⟨C, List.mem_of_getElem? hC, ChartBox.poses_subset h hp⟩
    next => simp at h

end SLeaf

namespace SCover

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The check of a scaled cover tree on the box `B`, with the claim boxes `claims`. -/
def check (claims : List ChartBox) (pts : List (V3 κ)) (D : SymmData κ) (Θ : Scale κ)
    (depth : ℕ) (B : ChartBox) (T : Cover (SLeaf κ)) : Bool :=
  T.check (fun B l ↦ l.check claims pts D Θ depth B) B

/-- **Soundness of scaled cover trees**: every pose of the box is settled at `Θ` or lies in a
claim box. -/
theorem settledS_or_claim_of_check {claims : List ChartBox} {pts : List (V3 κ)}
    {D : SymmData κ} {Θ : Scale κ} {depth : ℕ} {B : ChartBox} {T : Cover (SLeaf κ)}
    (hD : D.ok pts = true) (h : check claims pts D Θ depth B T = true) :
    ∀ p ∈ B.poses, SettledS pts D Θ.re p ∨ ∃ C ∈ claims, p ∈ C.poses :=
  Cover.check_sound (Q := fun p ↦ SettledS pts D Θ.re p ∨ ∃ C ∈ claims, p ∈ C.poses)
    (fun _ _ _ hl ↦ SLeaf.check_sound hD hl) h

/-- **Soundness of scaled cover trees without claim boxes.** -/
theorem settledS_of_check {pts : List (V3 κ)} {D : SymmData κ} {Θ : Scale κ} {depth : ℕ}
    {B : ChartBox} {T : Cover (SLeaf κ)} (hD : D.ok pts = true)
    (h : check [] pts D Θ depth B T = true) : ∀ p ∈ B.poses, SettledS pts D Θ.re p :=
  fun p hp ↦ (settledS_or_claim_of_check hD h p hp).resolve_right (by simp)

end SCover

/-! ### Claims as hypotheses -/

section Claims

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- Settled poses stay settled at a larger plug scale. -/
theorem SettledS.mono {pts : List (V3 κ)} {D : SymmData κ} {θ Θ : ℝ} {p : ChartPose}
    (h : SettledS pts D θ p) (hθ : 0 ≤ θ) (hle : θ ≤ Θ) : SettledS pts D Θ p := by
  rcases h with h | h | h
  · exact Or.inl fun hfit ↦ h (hfit.smul_of_le hθ hle)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- **Scaled certificates with claims, the claims' facts as settled poses.** If the points span
space, every unit chart box lies in one of the boxes `roots`, every pose of every root is settled
at `θ` or lies in a claim box, and every pose of a claim box is settled at `Θ ≥ θ ≥ 0` (the claim
facts), the polyhedron of `pts` scaled by `Θ` does not fit through it. -/
theorem Polyhedron.not_fitsThrough_smul_of_settled_claims [Countable κ] {pts : List (V3 κ)}
    {D : SymmData κ} {i j k l : ℕ} (hspan : spanOk pts i j k l = true) {roots : List ChartBox}
    (hroots : unitsIn roots = true) {claims : List ChartBox} {θ Θ : ℝ} (hθ : 0 ≤ θ)
    (hle : θ ≤ Θ)
    (h : roots.Forall fun B ↦ ∀ p ∈ B.poses, SettledS pts D θ p ∨ ∃ C ∈ claims, p ∈ C.poses)
    (hc : ∀ C ∈ claims, ∀ p ∈ C.poses, SettledS pts D Θ p) :
    ¬ ((Polyhedron.ofPoints pts).smul Θ).FitsThrough (Polyhedron.ofPoints pts) := by
  refine Polyhedron.not_fitsThrough_smul_of_settled (D := D) hspan fun a k p hp ↦ ?_
  simp only [unitsIn, List.all_eq_true, List.any_eq_true] at hroots
  obtain ⟨B, hB, hsub⟩ := hroots a (by fin_cases a <;> simp) k (by fin_cases k <;> simp)
  rcases List.forall_iff_forall_mem.mp h B hB p (ChartBox.poses_subset hsub hp) with h1 | h1
  · exact h1.mono hθ hle
  · obtain ⟨C, hC, hpC⟩ := h1
    exact hc C hC p hpC

/-- **Scaled certificates with claims.** As `not_fitsThrough_smul_of_settled_claims`, with the
claim facts as no fit: no pose of a claim box fits at `Θ`. -/
theorem Polyhedron.not_fitsThrough_smul_of_claims [Countable κ] {pts : List (V3 κ)}
    {D : SymmData κ} {i j k l : ℕ} (hspan : spanOk pts i j k l = true) {roots : List ChartBox}
    (hroots : unitsIn roots = true) {claims : List ChartBox} {θ Θ : ℝ} (hθ : 0 ≤ θ)
    (hle : θ ≤ Θ)
    (h : roots.Forall fun B ↦ ∀ p ∈ B.poses, SettledS pts D θ p ∨ ∃ C ∈ claims, p ∈ C.poses)
    (hc : ∀ C ∈ claims, (Polyhedron.ofPoints pts).NoFitRot C.poses (Θ • 1)) :
    ¬ ((Polyhedron.ofPoints pts).smul Θ).FitsThrough (Polyhedron.ofPoints pts) :=
  Polyhedron.not_fitsThrough_smul_of_settled_claims hspan hroots hθ hle h fun C hC ↦
    settledS_of_noFitRot (hc C hC)

/-- **Exact Nieuwland numbers from a far field and claims, the claims' facts as settled poses.**
For `P = a • (polyhedron of pts)`, `a ≠ 0`: a far field settled at `θ` outside the claim boxes,
every pose of the claim boxes settled at `Θ ≥ θ ≥ 0`, and the lower bound `Θ ≤ nieuwland P`
(from a weak fit at `Θ`, `le_nieuwland_of_weakFitsThrough`) give `nieuwland P = Θ` (as
`nieuwland_eq_of_not_fitsThrough`, through the scaling). -/
theorem Polyhedron.nieuwland_eq_of_settled_claims [Countable κ] {pts : List (V3 κ)}
    {D : SymmData κ} {i j k l : ℕ} (hspan : spanOk pts i j k l = true) {roots : List ChartBox}
    (hroots : unitsIn roots = true) {claims : List ChartBox} {θ Θ : ℝ} (hθ : 0 ≤ θ)
    (hle : θ ≤ Θ)
    (h : roots.Forall fun B ↦ ∀ p ∈ B.poses, SettledS pts D θ p ∨ ∃ C ∈ claims, p ∈ C.poses)
    (hc : ∀ C ∈ claims, ∀ p ∈ C.poses, SettledS pts D Θ p) {P : Polyhedron}
    {a : ℝ} (hP : P = (Polyhedron.ofPoints pts).smul a) (ha : a ≠ 0) (hlo : Θ ≤ P.nieuwland) :
    P.nieuwland = Θ :=
  le_antisymm (Polyhedron.nieuwland_le_of_eq_smul hP ha (hθ.trans hle)
    (Polyhedron.not_fitsThrough_smul_of_settled_claims hspan hroots hθ hle h hc)) hlo

/-- **Exact Nieuwland numbers from a far field and claims.** As
`nieuwland_eq_of_settled_claims`, with the claim facts as no fit at `Θ`. -/
theorem Polyhedron.nieuwland_eq_of_claims [Countable κ] {pts : List (V3 κ)} {D : SymmData κ}
    {i j k l : ℕ} (hspan : spanOk pts i j k l = true) {roots : List ChartBox}
    (hroots : unitsIn roots = true) {claims : List ChartBox} {θ Θ : ℝ} (hθ : 0 ≤ θ)
    (hle : θ ≤ Θ)
    (h : roots.Forall fun B ↦ ∀ p ∈ B.poses, SettledS pts D θ p ∨ ∃ C ∈ claims, p ∈ C.poses)
    (hc : ∀ C ∈ claims, (Polyhedron.ofPoints pts).NoFitRot C.poses (Θ • 1)) {P : Polyhedron}
    {a : ℝ} (hP : P = (Polyhedron.ofPoints pts).smul a) (ha : a ≠ 0) (hlo : Θ ≤ P.nieuwland) :
    P.nieuwland = Θ :=
  Polyhedron.nieuwland_eq_of_settled_claims hspan hroots hθ hle h
    (fun C hC ↦ settledS_of_noFitRot (hc C hC)) hP ha hlo

end Claims

end Nieuwland.Check

namespace Nieuwland.Cert

open Check

namespace Dec

variable {κ : Type} [Dec κ]

instance : Dec (Scale κ) where
  dec env s := match view env s with
    | .anon #[n, d] => return ⟨← dec env n, ← dec env d⟩
    | _ => none

instance : Dec (MGroup κ) where
  dec env s := match view env s with
    | .anon #[d, ts] => return ⟨← dec env d, ← dec env ts⟩
    | _ => none

instance : Dec (MLeaf κ) where
  dec env s := match view env s with
    | .anon #[c, gs] => return ⟨← dec env c, ← dec env gs⟩
    | _ => none

instance : Dec Chord where
  dec env s := match view env s with
    | .anon #[a₁, c₁, a₂, c₂] =>
      return ⟨← dec env a₁, ← dec env c₁, ← dec env a₂, ← dec env c₂⟩
    | _ => none

instance : Dec (SLeaf κ) where
  dec env s := match view env s with
    | .dot "centred" #[t, w] => return .centred (← dec env t) (← dec env w)
    | .dot "excl" #[i, j] => return .excl (← dec env i) (← dec env j)
    | .dot "balanced" #[t, w] => return .balanced (← dec env t) (← dec env w)
    | .dot "width" #[t, w] => return .width (← dec env t) (← dec env w)
    | .dot "mult" #[t, m] => return .mult (← dec env t) (← dec env m)
    | .dot "chord" #[t, w] => return .chord (← dec env t) (← dec env w)
    | .dot "claim" #[k] => return .claim (← dec env k)
    | _ => none

end Dec

namespace NativeS

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] [Dec κ]

/-- The scaled cover tree of a text: its entries, with the tree as the entry `cover`. -/
def decode (text : String) : Option (Cover (SLeaf κ)) := do
  let env ← Syn.entries text
  Dec.dec env (← env["cover"]?)

/-- The check of the scaled cover tree in `text` on the box `B`, for the plug scale `Θ` and the
claim boxes `claims`. -/
@[nospecialize]
def checkC (claims : List ChartBox) (pts : List (V3 κ)) (D : SymmData κ) (Θ : Scale κ)
    (depth : ℕ) (B : ChartBox) (text : String) : Bool :=
  match decode (κ := κ) text with
  | some T => SCover.check claims pts D Θ depth B T
  | none => false

/-- The check of the scaled cover tree in `text` on the box `B`, for the plug scale `Θ`, without
claim boxes. -/
@[nospecialize]
def check (pts : List (V3 κ)) (D : SymmData κ) (Θ : Scale κ) (depth : ℕ) (B : ChartBox)
    (text : String) : Bool :=
  checkC [] pts D Θ depth B text

/-- **Native scaled checks with claim boxes.** If the tree in `text` checks on `B`, every pose of
`B` is settled at `Θ` or lies in a claim box. -/
theorem settledS_or_claim_of_checkC {claims : List ChartBox} {pts : List (V3 κ)}
    {D : SymmData κ} {Θ : Scale κ} {depth : ℕ} {B : ChartBox} {text : String}
    (hD : D.ok pts = true) (h : checkC claims pts D Θ depth B text = true) :
    ∀ p ∈ B.poses, SettledS pts D Θ.re p ∨ ∃ C ∈ claims, p ∈ C.poses := by
  unfold checkC at h
  split at h
  next T _ => exact SCover.settledS_or_claim_of_check hD h
  next => simp at h

/-- **Native scaled checks.** If the tree in `text` checks on `B`, every pose of `B` is settled
at `Θ`. -/
theorem settledS_of_check {pts : List (V3 κ)} {D : SymmData κ} {Θ : Scale κ} {depth : ℕ}
    {B : ChartBox} {text : String} (hD : D.ok pts = true)
    (h : check pts D Θ depth B text = true) : ∀ p ∈ B.poses, SettledS pts D Θ.re p :=
  fun p hp ↦ (settledS_or_claim_of_checkC hD h p hp).resolve_right (by simp)

end NativeS

end Nieuwland.Cert
