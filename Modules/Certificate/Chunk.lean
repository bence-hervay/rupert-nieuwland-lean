import Modules.Check.Leaf.Global
import Modules.Certificate.Data

/-!
# Exported cover trees with unsupported parts

The exporter `code/lean-export` writes a subtree of a certificate's cover as a global cover tree
(`GCover`, `Modules/Check/Leaf/Global.lean`) of items, with its chart changes. Each leaf is either

* a leaf Lean checks (`Item.leaf`): a claim with supported evidence, an excluded leaf, a weighted
  zoom or chart tree with the symmetry data, or a mapped leaf; or
* an unsupported part (`Item.missing`): a region, its pre-rotation if any, and the certificate's
  data for it (`Missing`), kept as data (`Modules/Certificate/Data.lean`) and not checked.

`GCover.settled_of_items` concludes that every pose of the subtree's box is settled (no fit, or
excluded) **under the hypothesis that every unsupported region is settled**, with its
pre-rotation (`SettledRot`). The hypothesis lists exactly the unsupported parts
(`GCover.missing`), so the unconditional theorem becomes available once each of them is supported
and proved, and nothing is dropped silently.

Regions of unsupported parts: a leaf's own box (evidence on the leaf, a mapped, decided or open
leaf, or a whole chart change below a node in data-only exports), or the region of a cited claim
(its proof then discharges every leaf that cites it).
-/

namespace Nieuwland.Cert

open Check

/-- What a certificate gives for a region where Lean has no check yet. -/
inductive Missing where
  /-- A leaf's discharge (evidence, mapped, decided or open). -/
  | leaf (d : Discharge)
  /-- A cited claim: its id and evidence (the region is the claim's). -/
  | claim (id : String) (e : BoxEvidence)
  /-- A mapped leaf with the claim it cites. -/
  | mapped (sym : Nat) (id : String) (region : CBox) (e : BoxEvidence)
  /-- A decided leaf with its decision. -/
  | decided (id : String) (d : Decision)
  /-- A chart change at a node: the target region, the leaves below it by path from the node
  (`r` first), and the claims they cite (id, region, evidence). -/
  | rechart (region : CBox) (leaves : List (String × Discharge))
      (claims : List (String × CBox × BoxEvidence))

/-- An unsupported part: a region, its pre-rotation if any, and its data. -/
structure Unsupported (κ : Type) where
  /-- The region the part settles in the certificate. -/
  region : ChartBox
  /-- The pre-rotation of the region, if any. -/
  pre : Option (Q4 κ)
  /-- The certificate's data for it. -/
  data : Missing

/-- A leaf of an exported cover tree. -/
inductive Item (κ : Type) where
  /-- A leaf that Lean checks. -/
  | leaf (l : Leaf κ)
  /-- An unsupported part. -/
  | missing (u : Unsupported κ)

namespace Item

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The region of the item. -/
def region : Item κ → ChartBox
  | leaf l => l.region
  | missing u => u.region

/-- The pre-rotation of the item's region, if any. -/
def pre : Item κ → Option (Q4 κ)
  | leaf l => l.pre
  | missing u => u.pre

/-- The check of the item: that of a leaf; an unsupported part is assumed (`GCover.missing`). -/
def check (pts : List (V3 κ)) (D : SymmData κ) (depth : ℕ) : Item κ → Bool
  | leaf l => l.check pts D depth
  | missing _ => true

/-- The item fits the tree at the box `B` with the pre-rotation `pre`: `B` lies in its region,
with the same pre-rotation. -/
def ok (B : ChartBox) (pre : Option (Q4 κ)) (i : Item κ) : Bool :=
  B.subset i.region && Exact.preEq i.pre pre

end Item

section Covers

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The unsupported parts of a tree. -/
def _root_.Nieuwland.Check.GCover.missing (T : GCover κ (Item κ)) : List (Unsupported κ) :=
  T.data.filterMap fun
    | .missing u => some u
    | .leaf _ => none

/-- **Exported covers.** If every checked leaf and every chart change checks, every leaf lies in
its item's region with its pre-rotation, and every unsupported region is settled, then every pose
of the box is settled. -/
theorem _root_.Nieuwland.Check.GCover.settled_of_items {pts : List (V3 κ)} {D : SymmData κ}
    {depth : ℕ} (hD : D.ok pts = true) {T : GCover κ (Item κ)}
    (hT : T.data.Forall fun i ↦ i.check pts D depth = true)
    (hR : T.recharts.Forall fun r ↦ r.check depth = true)
    (hM : ∀ u ∈ T.missing, ∀ p ∈ u.region.poses, SettledRot pts D (Exact.rePre u.pre) p)
    {B : ChartBox} (h : T.check Item.ok B none = true) : ∀ p ∈ B.poses, Settled pts D p := by
  have := GCover.check_sound (depth := depth) (fun C pre i hi hok p hp ↦ by
    simp only [Item.ok, Bool.and_eq_true] at hok
    have hp' := ChartBox.poses_subset hok.1 hp
    rw [← Exact.rePre_eq_of_preEq hok.2]
    cases i with
    | leaf l => exact Leaf.check_sound hD (List.forall_iff_forall_mem.mp hT _ hi) p hp'
    | missing u => exact hM u (List.mem_filterMap.mpr ⟨_, hi, rfl⟩) p hp')
    (List.forall_iff_forall_mem.mp hR) h
  exact fun p hp ↦ settledRot_none.mp (this p hp)

/-- **Assembly of exported chunks.** A cover tree whose leaves are chunks (a box and the
unsupported parts of its subtree), each settled on its box when its unsupported parts are,
settles its box when all unsupported parts are. -/
theorem _root_.Nieuwland.Check.Cover.settled_of_chunks {pts : List (V3 κ)} {D : SymmData κ}
    {T : Cover (ChartBox × List (Unsupported κ))}
    (hT : T.data.Forall fun c ↦
      (∀ u ∈ c.2, ∀ p ∈ u.region.poses, SettledRot pts D (Exact.rePre u.pre) p) →
        ∀ p ∈ c.1.poses, Settled pts D p)
    (hM : ∀ u ∈ T.data.flatMap Prod.snd, ∀ p ∈ u.region.poses,
      SettledRot pts D (Exact.rePre u.pre) p) {B : ChartBox}
    (h : T.check (fun B c ↦ B.subset c.1) B = true) : ∀ p ∈ B.poses, Settled pts D p :=
  Cover.check_sound (fun _ c hc hsub p hp ↦ List.forall_iff_forall_mem.mp hT c hc
    (fun u hu ↦ hM u (List.mem_flatMap.mpr ⟨c, hc, hu⟩)) p (ChartBox.poses_subset hsub hp)) h

end Covers

end Nieuwland.Cert
