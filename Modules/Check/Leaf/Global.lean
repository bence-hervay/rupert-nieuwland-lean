import Modules.Check.Leaf.Claim
import Modules.Check.Leaf.Exclusion
import Modules.Check.Chart.Image

/-!
# Global covers

A global certificate (`code/src/proof/cert.rs`) covers the twelve unit chart boxes with trees
(`GCover`, `CoverNode` in `cert.rs`) of splits, chart changes and leaves: claims, excluded leaves,
weighted zooms and chart trees with exclusion leaves, and mapped leaves (`Leaf`). At every pose of
such a tree, the polyhedron has no fit, the pose is excluded, or it lies in the null set of the
score (`Settled`, `Modules/Check/Leaf/Null.lean`); weak symmetry exclusion turns this into the
conclusion that the polyhedron is not Rupert (`Polyhedron.not_isRupert_of_settled`) when its
points span space (`spanOk`).

**Pre-rotations.** Below a chart change, boxes are pre-rotated (`ChartBox::pre`), and their poses
are settled with the rotation followed by the pre-rotation (`SettledRot`). Each leaf has its own
pre-rotation (`Leaf.pre`), which must be that of the tree at its box (`Exact.preEq`).

* A **mapped leaf** (`Leaf.mapped`) cites a claim, possibly pre-rotated: the pose map of two
  symmetries sends its box into the claim's region (`Image.check`), so no pose of the box fits
  (`Image.noFitRot_of_check`).
* A **chart change** (`GCover.rechart`, `ChartChange`) sends its box into a region of other charts,
  possibly pre-rotated, by the identity map; the subtree below it covers that region, and its
  settled poses are those of the box (`Image.settledRot_of_check`).

As for claims, every leaf and chart change is checked in its own theorem
(`GCover.settled_of_checked`), and large trees are assembled from separately proved boxes
(`Cover.forall_of_proved`).
-/

namespace Nieuwland.Check

/-- A leaf of a global cover tree: a claim, an excluded leaf, a weighted zoom or a chart tree with
the symmetry data, or a mapped leaf. -/
inductive Leaf (κ : Type) where
  /-- A claim. -/
  | claim (c : Claim κ)
  /-- An excluded leaf. -/
  | excl (e : Excl)
  /-- A weighted zoom on the region, whose leaves may be excluded by the symmetry data. -/
  | zoom (region : ChartBox) (z : WZoom κ)
  /-- A chart tree on the region pre-rotated by `pre`, if any, whose leaves may be exclusion
  leaves of the symmetry data. -/
  | tree (region : ChartBox) (pre : Option (Q4 κ)) (t : ChartTree κ)
  /-- A mapped leaf (`Mapped` in `cert.rs`): the pose map of the symmetries `i`, `j` sends the
  region, pre-rotated by `pre` if any, into the region of the claim `c`. -/
  | mapped (region : ChartBox) (pre : Option (Q4 κ)) (i j : ℕ) (c : Claim κ)

namespace Leaf

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The region of the leaf. -/
def region : Leaf κ → ChartBox
  | claim c => c.region
  | excl e => e.region
  | zoom r _ => r
  | tree r _ _ => r
  | mapped r _ _ _ _ => r

/-- The pre-rotation of the region of the leaf, if any. -/
def pre : Leaf κ → Option (Q4 κ)
  | claim c => c.pre
  | excl _ => none
  | zoom _ _ => none
  | tree _ pre _ => pre
  | mapped _ pre _ _ _ => pre

/-- The check of a mapped leaf's image: the pose map `(i, j)` sends the region into the claim's. -/
def imageOk (D : SymmData κ) (depth : ℕ) (r : ChartBox) (pre : Option (Q4 κ)) (i j : ℕ)
    (c : Claim κ) : Bool :=
  match D.pmap i j with
  | some P => Image.check P r pre c.region c.pre depth
  | none => false

/-- The check of the leaf on its region. -/
def check (pts : List (V3 κ)) (D : SymmData κ) (depth : ℕ) : Leaf κ → Bool
  | claim c => c.check pts depth
  | excl e => e.check D depth
  | zoom r z => z.check pts (some D) r
  | tree r pre t => t.check pts (some D) r pre
  | mapped r pre i j c => imageOk D depth r pre i j c && c.check pts depth

/-- The check of a weighted-zoom leaf, from the zoom's own check (for checks in parts,
`WZoom.check_of_parts`). -/
theorem check_zoom {pts : List (V3 κ)} {D : SymmData κ} {depth : ℕ} {r : ChartBox}
    {z : WZoom κ}
    (h : z.check pts (some D) r = true) : (zoom r z).check pts D depth = true :=
  h

/-- The check of a chart-tree leaf, from the tree's own check (for checks in parts,
`ChartTree.check_of_parts`). -/
theorem check_tree {pts : List (V3 κ)} {D : SymmData κ} {depth : ℕ} {r : ChartBox}
    {pre : Option (Q4 κ)} {t : ChartTree κ}
    (h : t.check pts (some D) r pre = true) : (tree r pre t).check pts D depth = true :=
  h

/-- The check of a mapped leaf, from its image check and the claim's own check. -/
theorem check_mapped {pts : List (V3 κ)} {D : SymmData κ} {depth : ℕ} {r : ChartBox}
    {pre : Option (Q4 κ)} {i j : ℕ} {c : Claim κ} (himg : imageOk D depth r pre i j c = true)
    (hc : c.check pts depth = true) : (mapped r pre i j c).check pts D depth = true := by
  simp only [check, himg, hc, Bool.and_self]

theorem settledRot_of_noFitRot {pts : List (V3 κ)} {D : SymmData κ} {S : Set ChartPose}
    {c : Option (Fin 4 → ℝ)} (h : (Polyhedron.ofPoints pts).NoFitRot S (preRot c)) :
    ∀ p ∈ S, SettledRot pts D c p :=
  fun p hp ↦ Or.inl (h p hp)

/-- **Soundness of leaves.** Every pose of the region is settled, with the rotation followed by
the leaf's pre-rotation. -/
theorem check_sound {pts : List (V3 κ)} {D : SymmData κ} {depth : ℕ} (hD : D.ok pts = true) :
    ∀ {l : Leaf κ}, l.check pts D depth = true →
      ∀ p ∈ l.region.poses, SettledRot pts D (Exact.rePre l.pre) p
  | claim _, h, p, hp => settledRot_of_noFitRot (Claim.check_sound h) p hp
  | excl _, h, p, hp => settledRot_none.mpr (Or.inr (Or.inl (Excl.check_sound hD h p hp)))
  | zoom _ _, h, p, hp => by
    refine settledRot_none.mpr ?_
    rcases WZoom.check_sound (fun _ h ↦ by cases h; exact hD) h hp with h' | ⟨_, h', hx⟩
    · exact Or.inl h'
    · cases h'
      exact Or.inr (Or.inl hx)
  | tree _ _ _, h, p, hp => ChartTree.check_settled_pre hD h p hp
  | mapped r pre i j c, h, p, hp => by
    simp only [check, imageOk, Bool.and_eq_true] at h
    obtain ⟨himg, hc⟩ := h
    split at himg
    next P hP =>
      exact settledRot_of_noFitRot (Image.noFitRot_of_check hD hP himg (Claim.check_sound hc))
        p hp
    next => simp at himg

end Leaf

/-! ### Cover trees with chart changes -/

/-- A chart change (`CoverNode::Rechart` in `cert.rs`): the identity sends the box `src`,
pre-rotated by `srcPre` if any, into the box `dst`, pre-rotated by `dstPre` if any. (Chart changes
inside chart trees are `Rechart` steps, `Modules/Check/Chart/Rechart.lean`.) -/
structure ChartChange (κ : Type) where
  /-- The box of the node. -/
  src : ChartBox
  /-- Its pre-rotation, if any. -/
  srcPre : Option (Q4 κ)
  /-- The region of the subtree. -/
  dst : ChartBox
  /-- Its pre-rotation, if any. -/
  dstPre : Option (Q4 κ)

/-- The check of a chart change: the identity sends `src` into `dst`, bisecting at most `depth`
times along each branch. -/
def ChartChange.check {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] (depth : ℕ)
    (r : ChartChange κ) : Bool :=
  Image.check PMap.id r.src r.srcPre r.dst r.dstPre depth

/-- A cover tree of a global certificate (`CoverNode` in `cert.rs`): leaves with data of type
`E`, splits that halve a coordinate, and chart changes, whose subtrees cover their regions. -/
inductive GCover (κ E : Type) where
  /-- A leaf. -/
  | leaf (e : E)
  /-- Halve coordinate `dim`. -/
  | split (dim : ℕ) (lo hi : GCover κ E)
  /-- A chart change and the subtree over its region. -/
  | rechart (r : ChartChange κ) (T : GCover κ E)

namespace GCover

variable {κ E : Type}

/-- The data of the leaves. -/
def data : GCover κ E → List E
  | leaf e => [e]
  | split _ lo hi => lo.data ++ hi.data
  | rechart _ T => T.data

/-- The chart changes. -/
def recharts : GCover κ E → List (ChartChange κ)
  | leaf _ => []
  | split _ lo hi => lo.recharts ++ hi.recharts
  | rechart r T => r :: T.recharts

variable [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- Check every leaf with `ok`, on the box of the leaf and its pre-rotation; a chart change must
start at the box of its node, with the same pre-rotation. The chart changes themselves are checked
separately (`ChartChange.check`). -/
def check (ok : ChartBox → Option (Q4 κ) → E → Bool) :
    ChartBox → Option (Q4 κ) → GCover κ E → Bool
  | B, pre, leaf e => ok B pre e
  | B, pre, split d lo hi => decide (0 < B.box.den) && check ok (B.lowerHalf d) pre lo &&
      check ok (B.upperHalf d) pre hi
  | B, pre, rechart r T => B.subset r.src && Exact.preEq r.srcPre pre && check ok r.dst r.dstPre T

/-- **Soundness of global cover trees.** If every leaf that `ok` accepts settles its box and every
chart change checks, every pose of the box is settled. -/
theorem check_sound {pts : List (V3 κ)} {D : SymmData κ} {depth : ℕ}
    {ok : ChartBox → Option (Q4 κ) → E → Bool} :
    ∀ {T : GCover κ E} {B : ChartBox} {pre : Option (Q4 κ)},
      (∀ B pre, ∀ e ∈ T.data, ok B pre e = true →
        ∀ p ∈ B.poses, SettledRot pts D (Exact.rePre pre) p) →
      (∀ r ∈ T.recharts, r.check depth = true) →
      T.check ok B pre = true → ∀ p ∈ B.poses, SettledRot pts D (Exact.rePre pre) p
  | leaf e, B, pre, hok, _, h => hok B pre e (List.mem_singleton_self e) h
  | split d lo hi, B, pre, hok, hr, h => by
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hden, hlo⟩, hhi⟩ := h
    intro p hp
    rcases ChartBox.poses_subset_union hden d hp with hp | hp
    · exact check_sound (fun B pre e he ↦ hok B pre e (List.mem_append_left _ he))
        (fun r hr' ↦ hr r (List.mem_append_left _ hr')) hlo p hp
    · exact check_sound (fun B pre e he ↦ hok B pre e (List.mem_append_right _ he))
        (fun r hr' ↦ hr r (List.mem_append_right _ hr')) hhi p hp
  | rechart r T, B, pre, hok, hr, h => by
    simp only [check, Bool.and_eq_true] at h
    obtain ⟨⟨hsub, hpre⟩, hT⟩ := h
    have hdst := check_sound (T := T) hok (fun r' hr' ↦ hr r' (List.mem_cons_of_mem _ hr')) hT
    have hsrc := Image.settledRot_of_check (hr r List.mem_cons_self) hdst
    rw [Exact.rePre_eq_of_preEq hpre] at hsrc
    exact fun p hp ↦ hsrc p (ChartBox.poses_subset hsub hp)

end GCover

section Global

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- A leaf fits the tree at the box `B` with the pre-rotation `pre`: `B` lies in its region, with
the same pre-rotation. -/
def Leaf.ok (B : ChartBox) (pre : Option (Q4 κ)) (l : Leaf κ) : Bool :=
  B.subset l.region && Exact.preEq l.pre pre

/-- **Global cover trees checked separately.** Each leaf lies in its region (`T.check`), and the
leaves and chart changes check (`hT`, `hR`, one theorem each). -/
theorem GCover.settled_of_checked {pts : List (V3 κ)} {D : SymmData κ} {depth : ℕ}
    (hD : D.ok pts = true) {T : GCover κ (Leaf κ)}
    (hT : T.data.Forall fun l ↦ l.check pts D depth = true)
    (hR : T.recharts.Forall fun r ↦ r.check depth = true) {B : ChartBox}
    (h : T.check Leaf.ok B none = true) : ∀ p ∈ B.poses, Settled pts D p := by
  have := GCover.check_sound (depth := depth) (fun B pre l hl hok p hp ↦ by
    simp only [Leaf.ok, Bool.and_eq_true] at hok
    have hs := Leaf.check_sound hD (List.forall_iff_forall_mem.mp hT l hl) p
      (ChartBox.poses_subset hok.1 hp)
    rwa [Exact.rePre_eq_of_preEq hok.2] at hs) (List.forall_iff_forall_mem.mp hR) h
  exact fun p hp ↦ settledRot_none.mp (this p hp)

/-- **Global covers decide the problem.** If the points span space and every pose of the twelve
unit chart boxes is settled, the polyhedron is not Rupert. (Settled poses carry their signed
symmetries, so the symmetry data is checked where leaves are, by `GCover.settled_of_checked`; the
null set is meagre, `isMeagre_null`.) -/
theorem Polyhedron.not_isRupert_of_settled [Countable κ] {pts : List (V3 κ)} {D : SymmData κ}
    {i j k l : ℕ} (hspan : spanOk pts i j k l = true)
    (h : ∀ a k, ∀ p ∈ (ChartBox.unit a k).poses, Settled pts D p) :
    ¬ (Polyhedron.ofPoints pts).IsRupert :=
  Polyhedron.not_isRupert_of_excluded_off (spanOk_sound hspan D.centre) D.score.f
    (fun _ u R ha ↦ orbitScore_smul _ _ _ ha u R) (isMeagre_null κ D.score)
    (fun a u R ha hN ↦ null_smul D.score a u R ha hN) fun p hp ↦
      h p.view p.rot p (ChartBox.mem_unit_poses hp)

end Global

end Nieuwland.Check
