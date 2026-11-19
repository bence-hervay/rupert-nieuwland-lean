import Modules.Check.Leaf.Polar
import Modules.Check.Leaf.SupportSparse
import Modules.Check.Number.Width
import Modules.Check.Leaf.WZoom
import Modules.Check.Chart.Tree

/-!
# Claims

A claim (`Claim` in `code/src/proof/cert.rs`) is a chart box, its region, pre-rotated by a
quaternion `q_c` or not (`ChartBox::pre`), with evidence for `NoFit` there: no pose of the region
fits with its rotation followed by `R(q_c)`. `Evidence` collects the evidence kinds the Lean
checker supports, with one check and one soundness theorem (`Evidence.check_sound_pre`; without a
pre-rotation, `Evidence.check_sound`). A claim without a pre-rotation discharges a cover leaf whose
box lies in its region (`Claim.leafOk`); regions may be larger than leaves, as in `cert.rs`.
Pre-rotated claims discharge the leaves of chart changes and mapped leaves
(`Modules/Check/Leaf/Global.lean`).
-/

namespace Nieuwland.Check

/-- The evidence of a claim (`BoxEvidence` in `code/src/proof/regional.rs`). -/
inductive Evidence (κ : Type) where
  /-- Balanced supports (`BalancedSupport`). -/
  | balanced (w : Balanced)
  /-- A width pair (`WidthSupport`). -/
  | width (w : Width κ)
  /-- A centred support (`CentredSupport`), as a width pair with paired anchors. -/
  | centred (w : Centred κ)
  /-- A polar zoom (`PolarZoom`). -/
  | polar (z : Polar κ)
  /-- A weighted zoom without excluded leaves (`WeightedZoom`); its leaves carry their own
  bisection depths. -/
  | wzoom (z : WZoom κ)
  /-- A chart tree (`ChartTree`) of steps and leaves L1–L3, without exclusion leaves; its leaves
  carry their own bisection depths. -/
  | tree (t : ChartTree κ)
  /-- A weighted zoom with local exclusion leaves (`WeightedZoom` with `LocalExcluded` leaves): the
  symmetry data whose pose maps its leaves use, and points `i, j, k, l` whose differences span
  space (`spanOk`). It proves `NoFit` on its own (`noFitRot_of_local`). -/
  | wzoomLoc (z : WZoom κ) (D : SymmData κ) (i j k l : ℕ)

namespace Evidence

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The check of evidence on the chart box `B` pre-rotated by `pre`, if any, bisecting at most
`depth` times along each branch. -/
def check (pts : List (V3 κ)) (B : ChartBox) (depth : ℕ) (pre : Option (Q4 κ)) :
    Evidence κ → Bool
  | balanced w => w.checkAny pts B depth pre
  | width w => w.check pts B depth pre
  | centred w => w.checkAny pts B depth pre
  | polar z => z.check pts B depth pre
  | wzoom z => z.check pts none B pre
  | tree t => t.check pts none B pre
  | wzoomLoc z D i j k l =>
    D.ok pts && spanOk pts i j k l && Exact.preOk pre && z.check pts (some D) B pre true

/-- The check of a weighted zoom as evidence, from the zoom's own check (for checks in parts,
`WZoom.check_of_parts`). -/
theorem check_wzoom {pts : List (V3 κ)} {B : ChartBox} {depth : ℕ} {pre : Option (Q4 κ)}
    {z : WZoom κ} (h : z.check pts none B pre = true) : (wzoom z).check pts B depth pre = true :=
  h

/-- The check of a weighted zoom with local exclusion as evidence, from the checks of the symmetry
data and the spanning points (as in a certificate's shared module, so that the kernel checks them
once) and the zoom's own check. -/
theorem check_wzoomLoc {pts : List (V3 κ)} {B : ChartBox} {depth : ℕ} {pre : Option (Q4 κ)}
    {z : WZoom κ} {D : SymmData κ} {i j k l : ℕ} (hD : D.ok pts = true)
    (hspan : spanOk pts i j k l = true) (hpre : Exact.preOk pre = true)
    (h : z.check pts (some D) B pre true = true) :
    (wzoomLoc z D i j k l).check pts B depth pre = true := by
  simp only [check, hD, hspan, hpre, h, Bool.and_self]

/-- The check of a chart tree as evidence, from the tree's own check (for checks in parts,
`ChartTree.check_of_parts`). -/
theorem check_tree {pts : List (V3 κ)} {B : ChartBox} {depth : ℕ} {pre : Option (Q4 κ)}
    {t : ChartTree κ} (h : t.check pts none B pre = true) : (tree t).check pts B depth pre = true :=
  h

/-- **Soundness of evidence**, on a box pre-rotated by `pre`, if any. -/
theorem check_sound_pre {pts : List (V3 κ)} {B : ChartBox} {depth : ℕ} {pre : Option (Q4 κ)} :
    ∀ {e : Evidence κ}, e.check pts B depth pre = true →
      (Polyhedron.ofPoints pts).NoFitRot B.poses (preRot (Exact.rePre pre))
  | balanced _, h => Balanced.checkAny_sound_pre h
  | width _, h => Width.check_sound_pre h
  | centred _, h => Centred.checkAny_sound_pre h
  | polar _, h => Polar.check_sound_pre h
  | wzoom _, h => fun _ hp ↦ by
    rcases WZoom.check_sound_pre (fun _ h ↦ by cases h) h hp with h' | ⟨_, h', -⟩
    · exact h'
    · cases h'
  | tree _, h => ChartTree.check_sound_pre h
  | wzoomLoc _ D _ _ _ _, h => by
    simp only [check, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hD, hspan⟩, hpre⟩, hz⟩ := h
    exact noFitRot_of_local hD (spanOk_sound hspan D.centre) hpre fun _ hp ↦
      WZoom.check_sound_loc hD hz hp

theorem check_sound {pts : List (V3 κ)} {B : ChartBox} {depth : ℕ} {e : Evidence κ}
    (h : e.check pts B depth none = true) : (Polyhedron.ofPoints pts).NoFit B.poses := by
  have h0 := check_sound_pre h
  rwa [Exact.rePre_none, preRot_none, Polyhedron.noFitRot_one] at h0

end Evidence

/-- A claim: evidence for `NoFit` on the chart box `region`, pre-rotated by `pre` if any. -/
structure Claim (κ : Type) where
  /-- The region of the claim. -/
  region : ChartBox
  /-- The pre-rotation of the region, if any. -/
  pre : Option (Q4 κ)
  /-- The evidence. -/
  ev : Evidence κ

namespace Claim

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The check of the claim's evidence on its region. -/
def check (pts : List (V3 κ)) (depth : ℕ) (c : Claim κ) : Bool :=
  c.ev.check pts c.region depth c.pre

/-- **Soundness of claims.** -/
theorem check_sound {pts : List (V3 κ)} {depth : ℕ} {c : Claim κ} (h : c.check pts depth = true) :
    (Polyhedron.ofPoints pts).NoFitRot c.region.poses (preRot (Exact.rePre c.pre)) :=
  Evidence.check_sound_pre h

/-- The claim discharges the cover leaf `B`: it has no pre-rotation, and `B` lies in its region,
where the evidence checks. -/
def leafOk (pts : List (V3 κ)) (depth : ℕ) (B : ChartBox) (c : Claim κ) : Bool :=
  B.subset c.region && c.pre.isNone && c.check pts depth

theorem leafOk_sound {pts : List (V3 κ)} {depth : ℕ} {B : ChartBox} {c : Claim κ}
    (h : c.leafOk pts depth B = true) : (Polyhedron.ofPoints pts).NoFit B.poses := by
  simp only [leafOk, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨hsub, hpre⟩, hc⟩ := h
  have h0 := check_sound hc
  rw [hpre, Exact.rePre_none, preRot_none, Polyhedron.noFitRot_one] at h0
  exact h0.mono (ChartBox.poses_subset hsub)

end Claim

section Covers

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- **Cover trees of claims.** -/
theorem Cover.noFit_of_claims {pts : List (V3 κ)} {depth : ℕ} {T : Cover (Claim κ)}
    {B : ChartBox} (h : T.check (Claim.leafOk pts depth) B = true) :
    (Polyhedron.ofPoints pts).NoFit B.poses :=
  Cover.check_sound (fun _ _ _ hc ↦ Claim.leafOk_sound hc) h

/-- **Cover trees of claims checked separately.** Each leaf lies in the region of its claim, which
has no pre-rotation (`T.check`), and the claims check (`hT`, one theorem per claim, so that the
kernel's memory is released between claims). -/
theorem Cover.noFit_of_checked {pts : List (V3 κ)} {depth : ℕ} {T : Cover (Claim κ)}
    (hT : T.data.Forall fun c ↦ c.check pts depth = true) {B : ChartBox}
    (h : T.check (fun B c ↦ B.subset c.region && c.pre.isNone) B = true) :
    (Polyhedron.ofPoints pts).NoFit B.poses :=
  Cover.check_sound (fun _ c hc hsub ↦ Claim.leafOk_sound (c := c) (depth := depth) (by
    simp only [Bool.and_eq_true] at hsub
    simp only [Claim.leafOk, hsub.1, hsub.2, List.forall_iff_forall_mem.mp hT c hc,
      Bool.and_self])) h

end Covers

end Nieuwland.Check
