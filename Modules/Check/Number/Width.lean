import Modules.Check.Leaf.Support

/-!
# Width pairs

A width pair (`WidthSupport` in `code/src/proof/regional.rs`) compares the two shadows along one
screen direction. Let `n = u ⨯₃ c` be the normal of an exact vector `c`, which need not be a
difference of points. At a fit, the moved plug's extent `n ⬝ᵥ R (v₊ - v₋)` between two of its
points is smaller than the hole's extent `n ⬝ᵥ (a - b)` between its supporting anchors, for any
translation. This is the balanced obstruction with the two opposite normals `n`, `-n` and equal
weights (`Polyhedron.not_fitsAt_of_balanced`).

The premises, on a cone of view directions (`ConeBound`), are that `n` does not vanish and that
the envelopes of `c` (anchors `A₊`) and `-c` (anchors `A₋`) hold. The witness polynomials
`u ⬝ᵥ (c ⨯₃ (Q(q) (v₊ - v₋) - |q|² (a - b)))`, one for each `a ∈ A₊` and `b ∈ A₋`, have degree 1
in the view variables and 2 in the rotation variables (`supportGen`).

Anchors need not be points of the body: they only bound the support functions, which the envelope
checks for every point. The plugs must be points, since the argument moves them.
-/

open Matrix

namespace Nieuwland.Check

/-- One side of a width pair: the anchors and the plug. -/
structure WidthSide where
  /-- The anchors (indices of points). -/
  anchors : List ℕ
  /-- The plug (the index of a point of the inner copy). -/
  plug : ℕ

/-- Width-pair evidence (`WidthSupport` in `regional.rs`): the exact direction `c` and the sides
along `c` and along `-c`. -/
structure Width (κ : Type) where
  /-- The direction. -/
  c : V3 κ
  /-- The side along `c`. -/
  pos : WidthSide
  /-- The side along `-c`. -/
  neg : WidthSide

namespace Width

section Exact

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The premises at the view directions of the cone over `us`: the plugs are points, the normal
`u ⨯₃ c` does not vanish, and the envelopes of `c` and `-c` hold. -/
def premisesOk (pts us : List (V3 κ)) (w : Width κ) : Bool :=
  decide (w.pos.plug < pts.length) && decide (w.neg.plug < pts.length) && normalOk us w.c &&
    envelopeOk pts us w.c w.pos.anchors &&
    envelopeOk pts us (V3.smul (Exact.ofInt (-1)) w.c) w.neg.anchors

/-- The difference `v₊ - v₋` of the plugs. -/
def plugDiff (pts : List (V3 κ)) (w : Width κ) : V3 κ :=
  (pt pts w.pos.plug).sub (pt pts w.neg.plug)

/-- The witness polynomials are nonnegative at the view direction `u` and the quaternion `q`, for
every pair of anchors. -/
def PolyNonneg (pts : List (V3 κ)) (w : Width κ) (u : Fin 3 → ℝ) (q : Fin 4 → ℝ) : Prop :=
  ∀ i ∈ w.pos.anchors, ∀ j ∈ w.neg.anchors,
    0 ≤ supportPoly u q (Exact.reV w.c) (Exact.reV (w.plugDiff pts))
      (Exact.reV ((pt pts i).sub (pt pts j)))

/-- The premises of a width pair at the view direction `u` (checked on a cone of views by
`premisesOk`, and on views with a blow-up by `premisesOkV`). -/
structure Premises (pts : List (V3 κ)) (w : Width κ) (u : Fin 3 → ℝ) : Prop where
  /-- The plug along `c` is a point. -/
  plugPos : w.pos.plug < pts.length
  /-- The plug along `-c` is a point. -/
  plugNeg : w.neg.plug < pts.length
  /-- The normal does not vanish. -/
  normal : u ⨯₃ Exact.reV w.c ≠ 0
  /-- The envelope of `c`. -/
  envPos : Envelope pts (u ⨯₃ Exact.reV w.c) w.pos.anchors
  /-- The envelope of `-c`. -/
  envNeg : Envelope pts (u ⨯₃ Exact.reV (V3.smul (Exact.ofInt (-1)) w.c)) w.neg.anchors

theorem premises_of_ok {pts us : List (V3 κ)} {w : Width κ} (h : w.premisesOk pts us = true)
    {u : Fin 3 → ℝ} (hu : ConeBound us u) : w.Premises pts u := by
  simp only [premisesOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hpP, hpN⟩, hn⟩, heP⟩, heN⟩ := h
  exact ⟨hpP, hpN, normalOk_sound hn hu, envelopeOk_sound heP hu, envelopeOk_sound heN hu⟩

/-- The premises on views with a blow-up: at all views (`strong`), or where the blow-up
parameter is positive (the normal may use the blow-up; the envelopes are checked at the
points). -/
def premisesOkV (pts : List (V3 κ)) (V : Views κ) (strong : Bool) (w : Width κ) : Bool :=
  if strong then w.premisesOk pts V.us else
    decide (w.pos.plug < pts.length) && decide (w.neg.plug < pts.length) && V.normal w.c &&
      envelopeOk pts V.us w.c w.pos.anchors &&
      envelopeOk pts V.us (V3.smul (Exact.ofInt (-1)) w.c) w.neg.anchors

theorem premises_of_okV {pts : List (V3 κ)} {V : Views κ} {strong : Bool} {w : Width κ}
    (h : w.premisesOkV pts V strong = true) {u : Fin 3 → ℝ} {r : ℝ} (hu : V.Mem u r)
    (hs : strong = true ∨ 0 < r) : w.Premises pts u := by
  unfold premisesOkV at h
  cases strong with
  | true => exact premises_of_ok h hu.1
  | false =>
    have hr : 0 < r := hs.resolve_left (by simp)
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hpP, hpN⟩, hn⟩, heP⟩, heN⟩ := h
    exact ⟨hpP, hpN, Views.normal_sound hn hu hr, envelopeOk_sound heP hu.1,
      envelopeOk_sound heN hu.1⟩

/-- **Anchor bounds.** If every point is dominated by an anchor along `n` and some point exists,
one anchor bounds `n` on the whole body. -/
theorem exists_anchor_bound {pts : List (V3 κ)} {n : Fin 3 → ℝ} {A : List ℕ}
    (h : Envelope pts n A) {j : ℕ} (hj : j < pts.length) :
    ∃ i ∈ A, ∀ x ∈ (Polyhedron.ofPoints pts).vertices,
      n ⬝ᵥ x ≤ n ⬝ᵥ Exact.reV (pt pts i) := by
  classical
  have hne : A.toFinset.Nonempty := by
    obtain ⟨i, hi, -⟩ := h _ (Polyhedron.pt_mem_ofPoints hj)
    exact ⟨i, List.mem_toFinset.mpr hi⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image _ (fun i ↦ n ⬝ᵥ Exact.reV (pt pts i)) hne
  refine ⟨i, List.mem_toFinset.mp hi, fun x hx ↦ ?_⟩
  obtain ⟨i', hi', hle⟩ := h x hx
  exact hle.trans (hmax i' (List.mem_toFinset.mpr hi'))

/-- **The width argument.** If the plugs are points, the normal `n = u ⨯₃ c` does not vanish, the
anchor `i₀` bounds `n` and the anchor `j₀` bounds `-n` on the body, and the witness polynomial of
`(i₀, j₀)` is nonnegative at the view direction `u` and the quaternion `q ≠ 0`, the rotation of `q`
does not fit along `u`, with any translation. -/
theorem not_fitsAlong_of_bounds {pts : List (V3 κ)} {w : Width κ} {u : Fin 3 → ℝ}
    {q : Fin 4 → ℝ} (hq0 : q ≠ 0) (hpP : w.pos.plug < pts.length)
    (hpN : w.neg.plug < pts.length) (hn₀ : u ⨯₃ Exact.reV w.c ≠ 0) {i₀ j₀ : ℕ}
    (hbP : ∀ x ∈ (Polyhedron.ofPoints pts).vertices,
      (u ⨯₃ Exact.reV w.c) ⬝ᵥ x ≤ (u ⨯₃ Exact.reV w.c) ⬝ᵥ Exact.reV (pt pts i₀))
    (hbN : ∀ x ∈ (Polyhedron.ofPoints pts).vertices,
      -(u ⨯₃ Exact.reV w.c) ⬝ᵥ x ≤ -(u ⨯₃ Exact.reV w.c) ⬝ᵥ Exact.reV (pt pts j₀))
    (h0 : 0 ≤ supportPoly u q (Exact.reV w.c) (Exact.reV (w.plugDiff pts))
      (Exact.reV ((pt pts i₀).sub (pt pts j₀)))) :
    ¬ (Polyhedron.ofPoints pts).FitsAlong u (quatRotation q) := by
  rw [supportPoly_rep hq0] at h0
  have h1 := nonneg_of_mul_nonneg_right h0 (dotProduct_self_pos hq0)
  simp only [plugDiff, Exact.reV_sub, mulVec_sub, dotProduct_sub] at h1
  have hz : (u ⨯₃ Exact.reV w.c) ⬝ᵥ u = 0 := by
    rw [dotProduct_comm]
    exact dot_self_cross _ _
  refine Polyhedron.not_fitsAlong_of_balanced (n := ![u ⨯₃ Exact.reV w.c, -(u ⨯₃ Exact.reV w.c)])
    (h := ![(u ⨯₃ Exact.reV w.c) ⬝ᵥ Exact.reV (pt pts i₀),
      -(u ⨯₃ Exact.reV w.c) ⬝ᵥ Exact.reV (pt pts j₀)])
    (w := fun _ ↦ 1) (v := ![Exact.reV (pt pts w.pos.plug), Exact.reV (pt pts w.neg.plug)])
    (fun i ↦ ?_) (fun i ↦ ?_) (fun i x hx ↦ ?_) (fun _ ↦ zero_le_one) (by simp) (by simp)
    (fun i ↦ ?_) ?_
  · fin_cases i
    · exact hn₀
    · exact neg_ne_zero.mpr hn₀
  · fin_cases i
    · exact hz
    · change -(u ⨯₃ Exact.reV w.c) ⬝ᵥ u = 0
      rw [neg_dotProduct, hz, neg_zero]
  · fin_cases i
    · exact hbP x hx
    · exact hbN x hx
  · fin_cases i
    · exact subset_convexHull ℝ _ (Polyhedron.pt_mem_ofPoints hpP)
    · exact subset_convexHull ℝ _ (Polyhedron.pt_mem_ofPoints hpN)
  · -- The witness for the bounding anchors.
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul,
      neg_dotProduct]
    change 0 ≤ (u ⨯₃ Exact.reV w.c) ⬝ᵥ (quatRotation q *ᵥ Exact.reV (pt pts w.pos.plug)) -
      (u ⨯₃ Exact.reV w.c) ⬝ᵥ Exact.reV (pt pts i₀) + (-((u ⨯₃ Exact.reV w.c) ⬝ᵥ
        (quatRotation q *ᵥ Exact.reV (pt pts w.neg.plug))) -
          -((u ⨯₃ Exact.reV w.c) ⬝ᵥ Exact.reV (pt pts j₀)))
    linarith

/-- The envelope of `-c` bounds `-n` for the normal `n = u ⨯₃ c`. -/
theorem envelope_neg {pts : List (V3 κ)} {c : V3 κ} {u : Fin 3 → ℝ} {A : List ℕ}
    (h : Envelope pts (u ⨯₃ Exact.reV (V3.smul (Exact.ofInt (-1)) c)) A) :
    Envelope pts (-(u ⨯₃ Exact.reV c)) A := by
  rwa [reV_neg_one_smul, map_neg] at h

/-- **Width pairs at a representative.** If the premises hold at the view direction `u`, and the
witness polynomials are nonnegative at `u` and the quaternion `q ≠ 0`, the rotation of `q` does
not fit along `u`, with any translation. -/
theorem not_fitsAlong_of_premises {pts : List (V3 κ)} {w : Width κ} {u : Fin 3 → ℝ}
    {q : Fin 4 → ℝ} (hq0 : q ≠ 0) (h : w.Premises pts u) (hq : w.PolyNonneg pts u q) :
    ¬ (Polyhedron.ofPoints pts).FitsAlong u (quatRotation q) := by
  obtain ⟨i₀, hi₀, hbP⟩ := exists_anchor_bound h.envPos h.plugPos
  obtain ⟨j₀, hj₀, hbN⟩ := exists_anchor_bound (envelope_neg h.envNeg) h.plugNeg
  exact not_fitsAlong_of_bounds hq0 h.plugPos h.plugNeg h.normal hbP hbN (hq i₀ hi₀ j₀ hj₀)

/-- **At a fit, some witness polynomial is negative**: the contrapositive of
`not_fitsAlong_of_premises`, for combinations of witnesses. -/
theorem exists_neg_of_fitsAlong {pts : List (V3 κ)} {w : Width κ} {u : Fin 3 → ℝ}
    {q : Fin 4 → ℝ} (hq0 : q ≠ 0) (h : w.Premises pts u)
    (hfit : (Polyhedron.ofPoints pts).FitsAlong u (quatRotation q)) :
    ∃ i ∈ w.pos.anchors, ∃ j ∈ w.neg.anchors,
      supportPoly u q (Exact.reV w.c) (Exact.reV (w.plugDiff pts))
        (Exact.reV ((pt pts i).sub (pt pts j))) < 0 := by
  by_contra hne
  refine not_fitsAlong_of_premises hq0 h (fun i hi j hj ↦ ?_) hfit
  by_contra hlt
  exact hne ⟨i, hi, j, hj, lt_of_not_ge hlt⟩

/-- **Width pairs at a pose.** If the premises hold at the view of the pose `p`, and the witness
polynomials are nonnegative at the view direction and the chart quaternion of `p`, no translation
makes `p` a fit. -/
theorem not_fitsAt_of_premises {pts : List (V3 κ)} {w : Width κ} {p : ChartPose}
    (h : w.Premises pts (viewDir p.view p.s p.t))
    (hq : w.PolyNonneg pts (viewDir p.view p.s p.t) (chartQuat p.rot p.x)) (τ : Fin 2 → ℝ) :
    ¬ (Polyhedron.ofPoints pts).FitsAt p τ := fun hfit ↦
  not_fitsAlong_of_premises (chartQuat_ne_zero _ _) h hq (Polyhedron.fitsAlong_of_fitsAt hfit)

/-- **At a fit, some witness polynomial is negative**: the contrapositive of
`not_fitsAt_of_premises`, for combinations of witnesses. -/
theorem exists_neg_of_premises {pts : List (V3 κ)} {w : Width κ} {p : ChartPose}
    (h : w.Premises pts (viewDir p.view p.s p.t)) {τ : Fin 2 → ℝ}
    (hfit : (Polyhedron.ofPoints pts).FitsAt p τ) :
    ∃ i ∈ w.pos.anchors, ∃ j ∈ w.neg.anchors,
      supportPoly (viewDir p.view p.s p.t) (chartQuat p.rot p.x) (Exact.reV w.c)
        (Exact.reV (w.plugDiff pts)) (Exact.reV ((pt pts i).sub (pt pts j))) < 0 :=
  exists_neg_of_fitsAlong (chartQuat_ne_zero _ _) h (Polyhedron.fitsAlong_of_fitsAt hfit)

/-- **Width pairs at a pose**, with the premises checked on a cone of views. -/
theorem not_fitsAt {pts us : List (V3 κ)} {w : Width κ} (h : w.premisesOk pts us = true)
    {p : ChartPose} (hu : ConeBound us (viewDir p.view p.s p.t))
    (hq : w.PolyNonneg pts (viewDir p.view p.s p.t) (chartQuat p.rot p.x)) (τ : Fin 2 → ℝ) :
    ¬ (Polyhedron.ofPoints pts).FitsAt p τ :=
  not_fitsAt_of_premises (premises_of_ok h hu) hq τ

/-- **At a fit, some witness polynomial is negative**, with the premises checked on a cone of
views. -/
theorem exists_neg_of_fitsAt {pts us : List (V3 κ)} {w : Width κ} (h : w.premisesOk pts us = true)
    {p : ChartPose} (hu : ConeBound us (viewDir p.view p.s p.t)) {τ : Fin 2 → ℝ}
    (hfit : (Polyhedron.ofPoints pts).FitsAt p τ) :
    ∃ i ∈ w.pos.anchors, ∃ j ∈ w.neg.anchors,
      supportPoly (viewDir p.view p.s p.t) (chartQuat p.rot p.x) (Exact.reV w.c)
        (Exact.reV (w.plugDiff pts)) (Exact.reV ((pt pts i).sub (pt pts j))) < 0 :=
  exists_neg_of_premises (premises_of_ok h hu) hfit

end Exact

section Basis

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The check of a width-pair claim on the chart box `B`, pre-rotated by `pre` if any, bisecting
at most `depth` times along each branch. -/
def check (pts : List (V3 κ)) (B : ChartBox) (depth : ℕ) (w : Width κ)
    (pre : Option (Q4 κ) := none) : Bool :=
  decide (0 < B.box.den) && Exact.preOk pre && w.premisesOk pts (viewCorners B.view B.box) &&
    w.pos.anchors.all fun i ↦ w.neg.anchors.all fun j ↦
      nonnegOn (supportGen B.view B.rot w.c (w.plugDiff pts) ((pt pts i).sub (pt pts j)) pre) 5
        depth B.box

/-- **Soundness of width-pair claims**, on a box pre-rotated by `pre`. -/
theorem check_sound_pre {pts : List (V3 κ)} {B : ChartBox} {depth : ℕ} {w : Width κ}
    {pre : Option (Q4 κ)} (h : w.check pts B depth pre = true) :
    (Polyhedron.ofPoints pts).NoFitRot B.poses (preRot (Exact.rePre pre)) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hden, hpre⟩, hprem⟩, hpoly⟩ := h
  intro p hp
  have hq := preQuat_ne_zero (chartQuat_ne_zero p.rot p.x) (Exact.rePre_ne_zero hpre)
  rw [ChartPose.rotation, chartRotation, ← quatRotation_preQuat]
  refine not_fitsAlong_of_premises hq
    (premises_of_ok hprem (Balanced.coneBound_of_mem_poses hden hp)) fun i hi j hj ↦ ?_
  obtain ⟨hview, hrot, hy⟩ := hp
  have h0 := nonnegOn_hom (supportGen_isHomogeneous _ _ _ _ _ _) hden (hpoly i hi j hj) hy
  rw [supportGen_homEnv, one_pow, one_mul, ← hrot, rotCoords_coords, ← hview] at h0
  exact h0

/-- **Soundness of width-pair claims.** -/
theorem check_sound {pts : List (V3 κ)} {B : ChartBox} {depth : ℕ} {w : Width κ}
    (h : w.check pts B depth = true) : (Polyhedron.ofPoints pts).NoFit B.poses := by
  have h0 := check_sound_pre h
  rwa [Exact.rePre_none, preRot_none, Polyhedron.noFitRot_one] at h0

end Basis

end Width

end Nieuwland.Check
