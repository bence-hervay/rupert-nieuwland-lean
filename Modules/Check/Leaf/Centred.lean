import Modules.Check.Number.Width

/-!
# Centred supports

A centred support (`CentredSupport` in `code/src/proof/regional.rs`) of a centrally symmetric body
with centre `m` says that the moved plug passes the hole's support along the normal `n = u ⨯₃ c`:
`n ⬝ᵥ R (v_j - m) ≥ n ⬝ᵥ (v_a - m)` for the anchor `a` that bounds `n`, so no pose fits with zero
translation, hence with any (`RESEARCH.md` §3.5).

Here it is a width pair whose anchors pair up (`Centred`): the plugs are `v_j` and its antipode
`v_{j*} = 2 m - v_j`, and the anchors come in pairs `(a, a*)` along `c` and `-c` whose sums
`v_a + v_{a*}` are all equal. Then the anchor along `c` that bounds `n` is paired with one along
`-c` that bounds `-n` (`Centred.not_fitsAlong_of_premises`), so only the pairs need witnesses, and
the witness of `(a, a*)`, `u ⬝ᵥ (c ⨯₃ (Q(q) (v_j - v_{j*}) - |q|² (v_a - v_{a*})))`, is twice the
centred one, `u ⬝ᵥ (c ⨯₃ (Q(q) (v_j - m) - |q|² (v_a - m)))`.

No symmetry of the body is assumed or checked: the width argument (`Width.not_fitsAlong_of_bounds`)
holds for any two plugs, the envelopes along `c` and `-c` are checked at every point, and the pairs
only need equal sums (`Centred.sumsOk`, exact). On a centrally symmetric body every point has its
antipode, so every centred support has this form; `code/lean-export` pairs the anchors.
-/

open Matrix

namespace Nieuwland.Check

/-- Centred-support evidence: the exact direction `c`, the plugs (a point and its antipode) and the
anchor pairs (an anchor along `c` and one along `-c`, all pairs with the same sum). -/
structure Centred (κ : Type) where
  /-- The direction. -/
  c : V3 κ
  /-- The plugs (indices of points). -/
  plugs : ℕ × ℕ
  /-- The anchor pairs (indices of points). -/
  pairs : List (ℕ × ℕ)

namespace Centred

section Exact

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The width pair of the plugs and the anchors of the pairs. -/
def toWidth (w : Centred κ) : Width κ :=
  ⟨w.c, ⟨w.pairs.map Prod.fst, w.plugs.1⟩, ⟨w.pairs.map Prod.snd, w.plugs.2⟩⟩

/-- The sum of the points of the pair `p` minus that of `p₀`. -/
def sumDiff (pts : List (V3 κ)) (p p₀ : ℕ × ℕ) : V3 κ :=
  ((pt pts p.1).add (pt pts p.2)).sub ((pt pts p₀.1).add (pt pts p₀.2))

/-- Every pair has the sum of the first one (exact zero tests). -/
def sumsOk (pts : List (V3 κ)) (w : Centred κ) : Bool :=
  w.pairs.all fun p ↦ Exact.isZeroV (sumDiff pts p (w.pairs.headD (0, 0)))

/-- All pairs have the same sum. -/
def Sums (pts : List (V3 κ)) (w : Centred κ) : Prop :=
  ∀ p ∈ w.pairs, ∀ p' ∈ w.pairs, Exact.reV (pt pts p.1) + Exact.reV (pt pts p.2) =
    Exact.reV (pt pts p'.1) + Exact.reV (pt pts p'.2)

theorem sums_of_ok {pts : List (V3 κ)} {w : Centred κ} (h : w.sumsOk pts = true) :
    w.Sums pts := by
  have he (p : ℕ × ℕ) (hp : p ∈ w.pairs) : Exact.reV (pt pts p.1) + Exact.reV (pt pts p.2) =
      Exact.reV (pt pts (w.pairs.headD (0, 0)).1) +
        Exact.reV (pt pts (w.pairs.headD (0, 0)).2) := by
    have h0 := Exact.reV_eq_zero_of_isZeroV (List.all_eq_true.mp h p hp)
    rw [sumDiff, Exact.reV_sub, Exact.reV_add, Exact.reV_add] at h0
    exact sub_eq_zero.mp h0
  intro p hp p' hp'
  rw [he p hp, he p' hp']

/-- The premises at the view directions of the cone over `us`: those of the width pair, and equal
sums. -/
def premisesOk (pts us : List (V3 κ)) (w : Centred κ) : Bool :=
  w.toWidth.premisesOk pts us && w.sumsOk pts

/-- The premises on views with a blow-up (`Width.premisesOkV`), and equal sums. -/
def premisesOkV (pts : List (V3 κ)) (V : Views κ) (strong : Bool) (w : Centred κ) : Bool :=
  w.toWidth.premisesOkV pts V strong && w.sumsOk pts

/-- The premises of a centred support at the view direction `u`. -/
structure Premises (pts : List (V3 κ)) (w : Centred κ) (u : Fin 3 → ℝ) : Prop where
  /-- The premises of the width pair. -/
  width : w.toWidth.Premises pts u
  /-- Equal sums. -/
  sums : w.Sums pts

theorem premises_of_ok {pts us : List (V3 κ)} {w : Centred κ} (h : w.premisesOk pts us = true)
    {u : Fin 3 → ℝ} (hu : ConeBound us u) : w.Premises pts u := by
  simp only [premisesOk, Bool.and_eq_true] at h
  exact ⟨Width.premises_of_ok h.1 hu, sums_of_ok h.2⟩

theorem premises_of_okV {pts : List (V3 κ)} {V : Views κ} {strong : Bool} {w : Centred κ}
    (h : w.premisesOkV pts V strong = true) {u : Fin 3 → ℝ} {r : ℝ} (hu : V.Mem u r)
    (hs : strong = true ∨ 0 < r) : w.Premises pts u := by
  simp only [premisesOkV, Bool.and_eq_true] at h
  exact ⟨Width.premises_of_okV h.1 hu hs, sums_of_ok h.2⟩

/-- The witness polynomial of the pair `p`, at the view direction `u` and the quaternion `q`. -/
noncomputable def poly (pts : List (V3 κ)) (w : Centred κ) (u : Fin 3 → ℝ) (q : Fin 4 → ℝ)
    (p : ℕ × ℕ) : ℝ :=
  supportPoly u q (Exact.reV w.c) (Exact.reV (w.toWidth.plugDiff pts))
    (Exact.reV ((pt pts p.1).sub (pt pts p.2)))

/-- **Centred supports at a representative.** If the premises hold at the view direction `u`, and
the witness polynomials of the pairs are nonnegative at `u` and the quaternion `q ≠ 0`, the
rotation of `q` does not fit along `u`, with any translation. -/
theorem not_fitsAlong_of_premises {pts : List (V3 κ)} {w : Centred κ} {u : Fin 3 → ℝ}
    {q : Fin 4 → ℝ} (hq0 : q ≠ 0) (h : w.Premises pts u)
    (hq : ∀ p ∈ w.pairs, 0 ≤ w.poly pts u q p) :
    ¬ (Polyhedron.ofPoints pts).FitsAlong u (quatRotation q) := by
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
  refine Width.not_fitsAlong_of_bounds (w := w.toWidth) (i₀ := p₀.1) (j₀ := p₀.2) hq0
    hW.plugPos hW.plugNeg hW.normal (fun x hx ↦ ?_) (fun x hx ↦ ?_) (hq p₀ hp₀')
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

/-- **At a fit, some witness polynomial is negative**: the contrapositive of
`not_fitsAlong_of_premises`, for combinations of witnesses. -/
theorem exists_neg_of_fitsAlong {pts : List (V3 κ)} {w : Centred κ} {u : Fin 3 → ℝ}
    {q : Fin 4 → ℝ} (hq0 : q ≠ 0) (h : w.Premises pts u)
    (hfit : (Polyhedron.ofPoints pts).FitsAlong u (quatRotation q)) :
    ∃ p ∈ w.pairs, w.poly pts u q p < 0 := by
  by_contra hne
  refine not_fitsAlong_of_premises hq0 h (fun p hp ↦ ?_) hfit
  by_contra hlt
  exact hne ⟨p, hp, lt_of_not_ge hlt⟩

end Exact

section Basis

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The check of a centred-support claim on the chart box `B`, pre-rotated by `pre` if any: the
witness polynomial of each pair is linear in the view, so it is checked at each corner of the view
box on the rotation box (`supportRotGen`, three variables), bisecting at most `depth` times along
each branch, as the Rust check does. -/
def check (pts : List (V3 κ)) (B : ChartBox) (depth : ℕ) (w : Centred κ)
    (pre : Option (Q4 κ) := none) : Bool :=
  decide (0 < B.box.den) && Exact.preOk pre && w.premisesOk pts (viewCorners B.view B.box) &&
    w.pairs.all fun p ↦ (viewCorners B.view B.box).all fun U ↦
      nonnegOn (supportRotGen U B.rot w.c (w.toWidth.plugDiff pts)
        ((pt pts p.1).sub (pt pts p.2)) pre) 3 depth (B.box.drop 2)

/-- **Soundness of centred-support claims from the signs of their polynomials**, on a box
pre-rotated by `pre`: the premises hold at the corners of the view box, and the witness polynomial
of every pair at every corner is nonnegative at the points of the rotation box (`check_sound_pre`;
with the sparse sign check, `checkS_sound_pre` in `Modules/Check/Leaf/SupportSparse.lean`). -/
theorem sound_of_nonneg {pts : List (V3 κ)} {B : ChartBox} {w : Centred κ} {pre : Option (Q4 κ)}
    (hden : 0 < B.box.den) (hpre : Exact.preOk pre = true)
    (hprem : w.premisesOk pts (viewCorners B.view B.box) = true)
    (hpoly : ∀ r ∈ w.pairs, ∀ U ∈ (viewCorners B.view B.box : List (V3 κ)), ∀ x : Fin 3 → ℝ,
      (B.box.drop 2).Mem 3 x → 0 ≤ (supportRotGen U B.rot w.c (w.toWidth.plugDiff pts)
        ((pt pts r.1).sub (pt pts r.2)) pre).run Exact.re (homEnv 3 1 x)) :
    (Polyhedron.ofPoints pts).NoFitRot B.poses (preRot (Exact.rePre pre)) := by
  intro p hp
  have hq := preQuat_ne_zero (chartQuat_ne_zero p.rot p.x) (Exact.rePre_ne_zero hpre)
  rw [ChartPose.rotation, chartRotation, ← quatRotation_preQuat]
  refine not_fitsAlong_of_premises hq
    (premises_of_ok hprem (Balanced.coneBound_of_mem_poses hden hp)) fun r hr ↦ ?_
  obtain ⟨hview, hrot, hy⟩ := hp
  -- The witness polynomial is the view dotted with `G`; a corner `U` of the view box bounds it.
  set q := preQuat (chartQuat p.rot p.x) (Exact.rePre pre)
  set G : Fin 3 → ℝ := Exact.reV w.c ⨯₃ (quatMatrix q *ᵥ Exact.reV (w.toWidth.plugDiff pts) -
    (q ⬝ᵥ q) • Exact.reV ((pt pts r.1).sub (pt pts r.2)))
  obtain ⟨U, hU, hle⟩ := exists_viewCorner_le (κ := κ) G B.view hden hy
  have h0 := hpoly r hr U hU _ (Box.mem_drop_two hy)
  rw [supportRotGen_homEnv, one_pow, one_mul, show (![p.coords 2, p.coords 3, p.coords 4] :
    Fin 3 → ℝ) = p.x from rotCoords_coords p, ← hrot] at h0
  have h1 : 0 ≤ G ⬝ᵥ Exact.reV U := by
    rw [dotProduct_comm]
    exact h0
  have hd : (0 : ℝ) < B.box.den := by exact_mod_cast hden
  have h2 : 0 ≤ G ⬝ᵥ viewDir B.view (p.coords 0) (p.coords 1) :=
    nonneg_of_mul_nonneg_right (h1.trans hle) hd
  change 0 ≤ viewDir p.view p.s p.t ⬝ᵥ G
  rw [dotProduct_comm, hview]
  exact h2

/-- **Soundness of centred-support claims**, on a box pre-rotated by `pre`. -/
theorem check_sound_pre {pts : List (V3 κ)} {B : ChartBox} {depth : ℕ} {w : Centred κ}
    {pre : Option (Q4 κ)} (h : w.check pts B depth pre = true) :
    (Polyhedron.ofPoints pts).NoFitRot B.poses (preRot (Exact.rePre pre)) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hden, hpre⟩, hprem⟩, hpoly⟩ := h
  exact sound_of_nonneg hden hpre hprem fun r hr U hU x hx ↦
    nonnegOn_hom (b := B.box.drop 2) (supportRotGen_isHomogeneous _ _ _ _ _ _) hden
      (hpoly r hr U hU) hx

/-- **Soundness of centred-support claims.** -/
theorem check_sound {pts : List (V3 κ)} {B : ChartBox} {depth : ℕ} {w : Centred κ}
    (h : w.check pts B depth = true) : (Polyhedron.ofPoints pts).NoFit B.poses := by
  have h0 := check_sound_pre h
  rwa [Exact.rePre_none, preRot_none, Polyhedron.noFitRot_one] at h0

end Basis

end Centred

end Nieuwland.Check
