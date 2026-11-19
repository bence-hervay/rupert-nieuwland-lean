import Modules.Nieuwland.Centred
import Modules.Check.Leaf.SupportSparse

/-!
# Balanced and width supports at a plug scale

The balanced-support and width-pair checks (`Balanced.check`, `Width.check`) for the plug `θ P`
in the hole `P`, `θ = ν / d` (`Scale`), as `Centred.checkScaled` does it for centred supports:
the plug points `θ v` (`rupert::proof::scale`), so the witness polynomials are computed times
`d > 0`, with the plugs times `ν` and the anchors times `d`. At `ν / d = 1 / 1` they are the
polynomials of the unscaled checks up to the products by `1`; the unscaled checks are unchanged.

A balanced support's polynomial is bounded on the five coordinates of the box. A width pair's is
affine in the view, so it is bounded at the four view corners of the box on the three rotation
coordinates, as rupert's checker does it: next to a face of the box where the rotation fixes the
plug difference the margin is small on the whole view square, and five-variable bisection runs
out of depth there (the pentagonal icositetrahedron's far field, root 8).

* `Balanced.not_fitsAlong_smul_of_premises`, `Width.not_fitsAlong_smul_of_premises`: the
  arguments for the matrix `(a / b) • R(q)`.
* `Balanced.checkScaled_sound_pre`, `Width.checkScaled_sound_pre`: the scaled checks on a chart
  box with an optional pre-rotation, `NoFitRot B.poses (θ • preRot c)`.
-/

open Matrix

namespace Nieuwland.Check

theorem balancedPoly_smul_smul (σ : ℝ) (u : Fin 3 → ℝ) (q : Fin 4 → ℝ) (c v w : Fin 3 → Fin 3 → ℝ)
    (a : ℝ) : balancedPoly σ u q c (fun i ↦ a • v i) (fun i ↦ a • w i) =
      a * balancedPoly σ u q c v w := by
  simp only [balancedPoly, supportPoly_smul_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

namespace Balanced

section Exact

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- **Balanced supports at a representative, at a scale.** As `not_fitsAlong_of_premises`, for
the matrix `(a / b) • R(q)`, with the witness polynomials of the plugs times `a` and the anchors
times `b > 0`. -/
theorem not_fitsAlong_smul_of_premises {pts : List (V3 κ)} {w : Balanced} {u : Fin 3 → ℝ}
    {q : Fin 4 → ℝ} (hq0 : q ≠ 0) (h : w.Premises pts u) {a b : ℝ} (hb : 0 < b)
    (hq : ∀ t : Fin 3 → ℕ, (∀ i, t i ∈ (w.sup i).anchors) →
      0 ≤ balancedPoly (w.sigma : ℝ) u q (fun i ↦ Exact.reV (w.dir pts i))
        (fun i ↦ a • Exact.reV (pt pts (w.sup i).plug))
        (fun i ↦ b • Exact.reV (pt pts (t i)))) :
    ¬ (Polyhedron.ofPoints pts).FitsAlong u ((a / b) • quatRotation q) := by
  set c : Fin 3 → Fin 3 → ℝ := fun i ↦ Exact.reV (w.dir pts i)
  have hplug (i : Fin 3) := Polyhedron.pt_mem_ofPoints (h.plug i)
  have hA (i : Fin 3) : ∃ j ∈ (w.sup i).anchors, ∀ j' ∈ (w.sup i).anchors,
      (u ⨯₃ c i) ⬝ᵥ Exact.reV (pt pts j') ≤ (u ⨯₃ c i) ⬝ᵥ Exact.reV (pt pts j) := by
    classical
    have hne : (w.sup i).anchors.toFinset.Nonempty := by
      obtain ⟨j, hj, -⟩ := h.envelope i _ (hplug i)
      exact ⟨j, List.mem_toFinset.mpr hj⟩
    obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image _
      (fun j ↦ (u ⨯₃ c i) ⬝ᵥ Exact.reV (pt pts j)) hne
    exact ⟨j, List.mem_toFinset.mp hj, fun j' hj' ↦ hmax j' (List.mem_toFinset.mpr hj')⟩
  choose t ht htmax using hA
  refine Polyhedron.not_fitsAlong_of_balanced (n := fun i ↦ u ⨯₃ c i)
    (h := fun i ↦ (u ⨯₃ c i) ⬝ᵥ Exact.reV (pt pts (t i)))
    (w := fun i ↦ weightPoly (w.sigma : ℝ) u (c (i + 1)) (c (i + 2)))
    (v := fun i ↦ Exact.reV (pt pts (w.sup i).plug))
    (fun i ↦ h.normal i) (fun i ↦ ?_) (fun i x hx ↦ ?_) h.weights h.sum
    (sum_weightPoly_smul_cross _ u c) (fun i ↦ subset_convexHull ℝ _ (hplug i)) ?_
  · rw [dotProduct_comm]
    exact dot_self_cross _ _
  · obtain ⟨j, hj, hle⟩ := h.envelope i x hx
    exact hle.trans (htmax i j hj)
  · have h0 := hq t ht
    have hab : (fun i ↦ a • Exact.reV (pt pts (w.sup i).plug)) =
        fun i ↦ b • ((a / b) • Exact.reV (pt pts (w.sup i).plug)) := by
      funext i
      rw [smul_smul, mul_div_cancel₀ a hb.ne']
    rw [hab, balancedPoly_smul_smul, balancedPoly_rep _ _ hq0] at h0
    have h1 := nonneg_of_mul_nonneg_right (nonneg_of_mul_nonneg_right h0 hb)
      (dotProduct_self_pos hq0)
    simpa only [smul_mulVec, mulVec_smul] using h1

end Exact

section Basis

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- **The check of a balanced-support claim at the plug scale `s`** on the chart box `B`,
pre-rotated by `pre` if any: `check` with the plugs times `s.num` and the anchors times
`s.den`. -/
def checkScaled (pts : List (V3 κ)) (B : ChartBox) (depth : ℕ) (w : Balanced) (s : Scale κ)
    (pre : Option (Q4 κ) := none) : Bool :=
  decide (0 < s.den) && decide (0 < B.box.den) && Exact.preOk pre &&
    w.premisesOk pts (viewCorners B.view B.box) &&
    allTriples (fun i ↦ (w.sup i).anchors) fun t ↦
      nonnegOn (balancedGen (Exact.ofInt w.sigma) B.view B.rot (w.dir pts)
        (fun i ↦ V3.smul s.num (pt pts (w.sup i).plug))
        (fun i ↦ V3.smul (Exact.ofInt (s.den : ℤ)) (pt pts (t i))) pre) 5 depth B.box

/-- **Soundness of balanced-support claims at a plug scale**, on a box pre-rotated by `pre`. -/
theorem checkScaled_sound_pre {pts : List (V3 κ)} {B : ChartBox} {depth : ℕ} {w : Balanced}
    {s : Scale κ} {pre : Option (Q4 κ)} (h : w.checkScaled pts B depth s pre = true) :
    (Polyhedron.ofPoints pts).NoFitRot B.poses (s.re • preRot (Exact.rePre pre)) := by
  simp only [checkScaled, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hsd, hden⟩, hpre⟩, hprem⟩, hpoly⟩ := h
  intro p hp
  have hq := preQuat_ne_zero (chartQuat_ne_zero p.rot p.x) (Exact.rePre_ne_zero hpre)
  rw [ChartPose.rotation, chartRotation, Matrix.mul_smul, ← quatRotation_preQuat]
  have hb : (0 : ℝ) < s.den := by exact_mod_cast hsd
  refine not_fitsAlong_smul_of_premises hq
    (premises_of_ok hprem (coneBound_of_mem_poses hden hp)) hb fun t ht ↦ ?_
  obtain ⟨hview, hrot, hy⟩ := hp
  have h0 := nonnegOn_hom (balancedGen_isHomogeneous _ _ _ _ _ _ _) hden
    (allTriples_sound hpoly ht) hy
  rw [balancedGen_homEnv, one_pow, one_mul, Exact.re_ofInt, ← hrot, rotCoords_coords,
    ← hview] at h0
  simp only [Exact.reV_smul, Exact.re_ofInt, Int.cast_natCast] at h0
  exact h0

end Basis

end Balanced

namespace Width

section Exact

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- **Width pairs at a representative, at a scale.** As `not_fitsAlong_of_premises`, for the
matrix `(a / b) • R(q)`, with the plug difference times `a` and the anchor differences times
`b > 0`. -/
theorem not_fitsAlong_smul_of_premises {pts : List (V3 κ)} {w : Width κ} {u : Fin 3 → ℝ}
    {q : Fin 4 → ℝ} (hq0 : q ≠ 0) (h : w.Premises pts u) {a b : ℝ} (hb : 0 < b)
    (hq : ∀ i ∈ w.pos.anchors, ∀ j ∈ w.neg.anchors,
      0 ≤ supportPoly u q (Exact.reV w.c) (a • Exact.reV (w.plugDiff pts))
        (b • Exact.reV ((pt pts i).sub (pt pts j)))) :
    ¬ (Polyhedron.ofPoints pts).FitsAlong u ((a / b) • quatRotation q) := by
  obtain ⟨i₀, hi₀, hbP⟩ := exists_anchor_bound h.envPos h.plugPos
  obtain ⟨j₀, hj₀, hbN⟩ := exists_anchor_bound (envelope_neg h.envNeg) h.plugNeg
  exact not_fitsAlong_smul_of_bounds hq0 h.plugPos h.plugNeg h.normal hbP hbN hb
    (hq i₀ hi₀ j₀ hj₀)

end Exact

section Basis

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- **The check of a width-pair claim at the plug scale `s`** on the chart box `B`, pre-rotated
by `pre` if any: the premises of `check`, and per pair of anchors the support polynomial with the
plug difference times `s.num` and the anchor difference times `s.den`, at each view corner of the
box on its rotation coordinates (`Centred.checkScaled`'s form; the polynomial is affine in the
view, and `rupert::proof::regional` checks a width support this way). -/
def checkScaled (pts : List (V3 κ)) (B : ChartBox) (depth : ℕ) (w : Width κ) (s : Scale κ)
    (pre : Option (Q4 κ) := none) : Bool :=
  decide (0 < s.den) && decide (0 < B.box.den) && Exact.preOk pre &&
    w.premisesOk pts (viewCorners B.view B.box) &&
    w.pos.anchors.all fun i ↦ w.neg.anchors.all fun j ↦
      (viewCorners B.view B.box).all fun U ↦
        nonnegOn (supportRotGen U B.rot w.c (V3.smul s.num (w.plugDiff pts))
          (V3.smul (Exact.ofInt (s.den : ℤ)) ((pt pts i).sub (pt pts j))) pre) 3 depth
          (B.box.drop 2)

/-- **Soundness of width-pair claims at a plug scale**, on a box pre-rotated by `pre`. -/
theorem checkScaled_sound_pre {pts : List (V3 κ)} {B : ChartBox} {depth : ℕ} {w : Width κ}
    {s : Scale κ} {pre : Option (Q4 κ)} (h : w.checkScaled pts B depth s pre = true) :
    (Polyhedron.ofPoints pts).NoFitRot B.poses (s.re • preRot (Exact.rePre pre)) := by
  simp only [checkScaled, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hsd, hden⟩, hpre⟩, hprem⟩, hpoly⟩ := h
  intro p hp
  have hq := preQuat_ne_zero (chartQuat_ne_zero p.rot p.x) (Exact.rePre_ne_zero hpre)
  rw [ChartPose.rotation, chartRotation, Matrix.mul_smul, ← quatRotation_preQuat]
  have hb : (0 : ℝ) < s.den := by exact_mod_cast hsd
  refine not_fitsAlong_smul_of_premises hq
    (premises_of_ok hprem (Balanced.coneBound_of_mem_poses hden hp)) hb fun i hi j hj ↦ ?_
  obtain ⟨hview, hrot, hy⟩ := hp
  set q := preQuat (chartQuat p.rot p.x) (Exact.rePre pre)
  set G : Fin 3 → ℝ := Exact.reV w.c ⨯₃ (quatMatrix q *ᵥ
    (Exact.re s.num • Exact.reV (w.plugDiff pts)) -
      (q ⬝ᵥ q) • ((s.den : ℝ) • Exact.reV ((pt pts i).sub (pt pts j))))
  obtain ⟨U, hU, hle⟩ := exists_viewCorner_le (κ := κ) G B.view hden hy
  have h0 := nonnegOn_hom (b := B.box.drop 2) (supportRotGen_isHomogeneous _ _ _ _ _ _) hden
    (hpoly i hi j hj U hU) (Box.mem_drop_two hy)
  rw [supportRotGen_homEnv, one_pow, one_mul, show (![p.coords 2, p.coords 3, p.coords 4] :
    Fin 3 → ℝ) = p.x from rotCoords_coords p, ← hrot, Exact.reV_smul, Exact.reV_smul,
    Exact.re_ofInt, Int.cast_natCast] at h0
  have h1 : 0 ≤ G ⬝ᵥ Exact.reV U := by
    rw [dotProduct_comm]
    exact h0
  have hd : (0 : ℝ) < B.box.den := by exact_mod_cast hden
  have h2 : 0 ≤ G ⬝ᵥ viewDir B.view (p.coords 0) (p.coords 1) :=
    nonneg_of_mul_nonneg_right (h1.trans hle) hd
  change 0 ≤ viewDir p.view p.s p.t ⬝ᵥ G
  rw [dotProduct_comm, hview]
  exact h2

end Basis

end Width

end Nieuwland.Check
