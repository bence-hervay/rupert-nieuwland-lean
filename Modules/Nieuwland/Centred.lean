import Modules.Check.Leaf.Centred
import Modules.Nieuwland.Settled

/-!
# Centred supports at a plug scale

A centred support (`Modules/Check/Leaf/Centred.lean`) for the plug `θ P` in the hole `P`, with
`θ = ν / d` (`Scale`): the plugs are the points `θ v_j` (`rupert::proof::scale`: plug points
`θ v`, everything else unchanged), so the witness polynomial of a pair `(a, a*)` is
`u ⬝ᵥ (c ⨯₃ (Q(q) θ (v_j - v_{j*}) - |q|² (v_a - v_{a*})))`. Over integral exact values it is
computed times `d > 0`, with the plug difference times `ν` and the anchor difference times `d`
(`Centred.checkScaled`); its sign is unchanged.

* `Width.not_fitsAlong_smul_of_bounds`: the width argument (`Width.not_fitsAlong_of_bounds`)
  for the matrix `θ • R(q)`: the plug points `R v` become `θ R v`.
* `Centred.checkScaled_sound_pre`: the scaled check on a chart box with an optional
  pre-rotation,`NoFitRot B.poses (θ • preRot c)`.

At the scale `ν / d = 1 / 1` the polynomial is the one of `Centred.check`, up to the products by
`1` (`Nieuwland/Examples/NieuwlandBound.lean` runs both).
-/

open Matrix

namespace Nieuwland.Check

/-- The support polynomial is linear in its plug and anchor vectors together. -/
theorem supportPoly_smul_smul (u : Fin 3 → ℝ) (q : Fin 4 → ℝ) (c v w : Fin 3 → ℝ) (a : ℝ) :
    supportPoly u q c (a • v) (a • w) = a * supportPoly u q c v w := by
  simp only [supportPoly, mulVec_smul, smul_comm (q ⬝ᵥ q) a w, ← smul_sub, map_smul,
    dotProduct_smul, smul_eq_mul]

namespace Width

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- **The width argument at a scale.** As `Width.not_fitsAlong_of_bounds`, for the plug `θ P`:
if the anchor `i₀` bounds `n = u ⨯₃ c` and `j₀` bounds `-n` on the body, and the witness
polynomial with the plug difference times `a` and the anchor difference times `b > 0` is
nonnegative, the matrix `(a / b) • R(q)` does not fit along `u`. -/
theorem not_fitsAlong_smul_of_bounds {pts : List (V3 κ)} {w : Width κ} {u : Fin 3 → ℝ}
    {q : Fin 4 → ℝ} (hq0 : q ≠ 0) (hpP : w.pos.plug < pts.length)
    (hpN : w.neg.plug < pts.length) (hn₀ : u ⨯₃ Exact.reV w.c ≠ 0) {i₀ j₀ : ℕ}
    (hbP : ∀ x ∈ (Polyhedron.ofPoints pts).vertices,
      (u ⨯₃ Exact.reV w.c) ⬝ᵥ x ≤ (u ⨯₃ Exact.reV w.c) ⬝ᵥ Exact.reV (pt pts i₀))
    (hbN : ∀ x ∈ (Polyhedron.ofPoints pts).vertices,
      -(u ⨯₃ Exact.reV w.c) ⬝ᵥ x ≤ -(u ⨯₃ Exact.reV w.c) ⬝ᵥ Exact.reV (pt pts j₀))
    {a b : ℝ} (hb : 0 < b)
    (h0 : 0 ≤ supportPoly u q (Exact.reV w.c) (a • Exact.reV (w.plugDiff pts))
      (b • Exact.reV ((pt pts i₀).sub (pt pts j₀)))) :
    ¬ (Polyhedron.ofPoints pts).FitsAlong u ((a / b) • quatRotation q) := by
  have hab : a • Exact.reV (w.plugDiff pts) = b • ((a / b) • Exact.reV (w.plugDiff pts)) := by
    rw [smul_smul, mul_div_cancel₀ a hb.ne']
  rw [hab, supportPoly_smul_smul, supportPoly_rep hq0] at h0
  have h1 := nonneg_of_mul_nonneg_right (nonneg_of_mul_nonneg_right h0 hb)
    (dotProduct_self_pos hq0)
  simp only [plugDiff, Exact.reV_sub, smul_sub, mulVec_sub, dotProduct_sub] at h1
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
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul,
      neg_dotProduct]
    change 0 ≤ (u ⨯₃ Exact.reV w.c) ⬝ᵥ (((a / b) • quatRotation q) *ᵥ
        Exact.reV (pt pts w.pos.plug)) - (u ⨯₃ Exact.reV w.c) ⬝ᵥ Exact.reV (pt pts i₀) +
      (-((u ⨯₃ Exact.reV w.c) ⬝ᵥ (((a / b) • quatRotation q) *ᵥ
        Exact.reV (pt pts w.neg.plug))) - -((u ⨯₃ Exact.reV w.c) ⬝ᵥ Exact.reV (pt pts j₀)))
    simp only [smul_mulVec, mulVec_smul, dotProduct_smul, smul_eq_mul] at h1 ⊢
    linarith

end Width

namespace Centred

section Exact

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The witness polynomial of the pair `p` at a scale: the plug difference times `a`, the anchor
difference times `b`. -/
noncomputable def polyS (pts : List (V3 κ)) (w : Centred κ) (a b : ℝ) (u : Fin 3 → ℝ)
    (q : Fin 4 → ℝ) (p : ℕ × ℕ) : ℝ :=
  supportPoly u q (Exact.reV w.c) (a • Exact.reV (w.toWidth.plugDiff pts))
    (b • Exact.reV ((pt pts p.1).sub (pt pts p.2)))

/-- **Centred supports at a representative, at a scale** (`Centred.not_fitsAlong_of_premises`
for the matrix `(a / b) • R(q)`). -/
theorem not_fitsAlong_smul_of_premises {pts : List (V3 κ)} {w : Centred κ} {u : Fin 3 → ℝ}
    {q : Fin 4 → ℝ} (hq0 : q ≠ 0) (h : w.Premises pts u) {a b : ℝ} (hb : 0 < b)
    (hq : ∀ p ∈ w.pairs, 0 ≤ w.polyS pts a b u q p) :
    ¬ (Polyhedron.ofPoints pts).FitsAlong u ((a / b) • quatRotation q) := by
  classical
  have hW := h.width
  set n := u ⨯₃ Exact.reV w.c with hn
  obtain ⟨i, hi, -⟩ := hW.envPos _ (Polyhedron.pt_mem_ofPoints hW.plugPos)
  have hne : w.pairs.toFinset.Nonempty := by
    obtain ⟨p, hp, -⟩ := List.mem_map.mp hi
    exact ⟨p, List.mem_toFinset.mpr hp⟩
  obtain ⟨p₀, hp₀, hmax⟩ :=
    Finset.exists_max_image _ (fun p : ℕ × ℕ ↦ n ⬝ᵥ Exact.reV (pt pts p.1)) hne
  have hp₀' := List.mem_toFinset.mp hp₀
  refine Width.not_fitsAlong_smul_of_bounds (w := w.toWidth) (i₀ := p₀.1) (j₀ := p₀.2) hq0
    hW.plugPos hW.plugNeg hW.normal (fun x hx ↦ ?_) (fun x hx ↦ ?_) hb (hq p₀ hp₀')
  · obtain ⟨i, hi, hle⟩ := hW.envPos x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
    exact hle.trans (hmax p (List.mem_toFinset.mpr hp))
  · obtain ⟨j, hj, hle⟩ := Width.envelope_neg hW.envNeg x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hj
    have hs := congrArg (n ⬝ᵥ ·) (h.sums p hp p₀ hp₀')
    simp only [dotProduct_add] at hs
    have hm : n ⬝ᵥ Exact.reV (pt pts p.1) ≤ n ⬝ᵥ Exact.reV (pt pts p₀.1) :=
      hmax p (List.mem_toFinset.mpr hp)
    have hle' : -(n ⬝ᵥ x) ≤ -(n ⬝ᵥ Exact.reV (pt pts p.2)) := by
      simp only [neg_dotProduct] at hle
      exact hle
    rw [neg_dotProduct, neg_dotProduct]
    change -(n ⬝ᵥ x) ≤ -(n ⬝ᵥ Exact.reV (pt pts p₀.2))
    linarith

end Exact

section Basis

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- **The check of a centred-support claim at the plug scale `s`** on the chart box `B`,
pre-rotated by `pre` if any: `Centred.check` with the plug difference times `s.num` and the
anchor differences times `s.den`. -/
def checkScaled (pts : List (V3 κ)) (B : ChartBox) (depth : ℕ) (w : Centred κ) (s : Scale κ)
    (pre : Option (Q4 κ) := none) : Bool :=
  decide (0 < s.den) && decide (0 < B.box.den) && Exact.preOk pre &&
    w.premisesOk pts (viewCorners B.view B.box) &&
    w.pairs.all fun p ↦ (viewCorners B.view B.box).all fun U ↦
      nonnegOn (supportRotGen U B.rot w.c (V3.smul s.num (w.toWidth.plugDiff pts))
        (V3.smul (Exact.ofInt (s.den : ℤ)) ((pt pts p.1).sub (pt pts p.2))) pre) 3 depth
        (B.box.drop 2)

/-- **Soundness of centred-support claims at a plug scale**, on a box pre-rotated by `pre`: no
pose of the box fits with the scale times its rotation followed by the pre-rotation. -/
theorem checkScaled_sound_pre {pts : List (V3 κ)} {B : ChartBox} {depth : ℕ} {w : Centred κ}
    {s : Scale κ} {pre : Option (Q4 κ)} (h : w.checkScaled pts B depth s pre = true) :
    (Polyhedron.ofPoints pts).NoFitRot B.poses (s.re • preRot (Exact.rePre pre)) := by
  simp only [checkScaled, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hsd, hden⟩, hpre⟩, hprem⟩, hpoly⟩ := h
  intro p hp
  have hq := preQuat_ne_zero (chartQuat_ne_zero p.rot p.x) (Exact.rePre_ne_zero hpre)
  rw [ChartPose.rotation, chartRotation, Matrix.mul_smul, ← quatRotation_preQuat]
  have hb : (0 : ℝ) < s.den := by exact_mod_cast hsd
  refine not_fitsAlong_smul_of_premises hq
    (premises_of_ok hprem (Balanced.coneBound_of_mem_poses hden hp)) hb fun r hr ↦ ?_
  obtain ⟨hview, hrot, hy⟩ := hp
  set q := preQuat (chartQuat p.rot p.x) (Exact.rePre pre)
  set G : Fin 3 → ℝ := Exact.reV w.c ⨯₃ (quatMatrix q *ᵥ
    (Exact.re s.num • Exact.reV (w.toWidth.plugDiff pts)) -
      (q ⬝ᵥ q) • ((s.den : ℝ) • Exact.reV ((pt pts r.1).sub (pt pts r.2))))
  obtain ⟨U, hU, hle⟩ := exists_viewCorner_le (κ := κ) G B.view hden hy
  have h0 := nonnegOn_hom (b := B.box.drop 2) (supportRotGen_isHomogeneous _ _ _ _ _ _) hden
    (hpoly r hr U hU) (Box.mem_drop_two hy)
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

end Centred

end Nieuwland.Check
