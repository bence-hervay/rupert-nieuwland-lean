import Modules.Check.Chart.ChartBox
import Modules.Check.Polynomial.Witness
import Modules.NoFit.Pre
import Modules.NoFit.Support

/-!
# Support claims

Checks of the support witnesses of `code/src/proof/regional.rs` on a chart box, with their
soundness. A claim concerns the polyhedron `Polyhedron.ofPoints pts` spanned by points with exact
coordinates (`Modules/Check/Number/Exact.lean`); evidence refers to points by their index in `pts`, as
Rust evidence refers to input points.

* **Premises on a cone of view directions.** They are linear in the view direction `u`, so they
  hold on the cone over a finite set of exact points when they hold at the points
  (`ConeBound`): `normalOk` (the support normal `u ⨯₃ c` does not vanish), `envelopeOk` (along
  that normal, every point is dominated by an anchor), `weightsOk` (the balance weights are
  nonnegative with positive sum). The corners of a view box are one such set
  (`coneBound_viewCorners`).
* **Balanced supports** (`Balanced.check`, `Balanced.check_sound`): the premises at the corners of
  the view box, and for every choice of anchors the witness `balancedGen` nonnegative on the box
  (`nonnegOn`). The conclusion is `NoFit` on the box, for all translations
  (`Polyhedron.not_fitsAt_of_balanced`). On a box pre-rotated by `c` (`Balanced.check_sound_pre`)
  the witness uses the quaternion `q(x) c` (`balancedGen`, `preQ`), and the conclusion is
  `NoFitRot` with the rotation of `c` first.
-/

open Matrix

namespace Nieuwland

/-- Point `j` of `pts`, or `0` if there is none. -/
def Check.pt {κ : Type} [Add κ] [Sub κ] [Mul κ] [Check.Exact κ] (pts : List (Check.V3 κ))
    (j : ℕ) : Check.V3 κ :=
  pts.getD j ⟨Check.Exact.ofInt 0, Check.Exact.ofInt 0, Check.Exact.ofInt 0⟩

theorem Polyhedron.pt_mem_ofPoints {κ : Type} [Add κ] [Sub κ] [Mul κ] [Check.Exact κ]
    {pts : List (Check.V3 κ)} {j : ℕ} (hj : j < pts.length) :
    Check.Exact.reV (Check.pt pts j) ∈ (ofPoints pts).vertices :=
  mem_ofPoints.mpr ⟨_, by
    rw [Check.pt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    exact List.getElem_mem hj, rfl⟩

namespace Check

theorem rotCoords_coords (p : ChartPose) : rotCoords p.coords = p.x := by
  funext i
  fin_cases i <;> rfl

/-! ### Finite conjunctions -/

/-- `f 0 && f 1 && f 2`. -/
def allFin3 (f : Fin 3 → Bool) : Bool :=
  f 0 && f 1 && f 2

theorem allFin3_eq_true {f : Fin 3 → Bool} : allFin3 f = true ↔ ∀ i, f i = true := by
  refine ⟨fun h i ↦ ?_, fun h ↦ by simp [allFin3, h]⟩
  simp only [allFin3, Bool.and_eq_true] at h
  fin_cases i
  exacts [h.1.1, h.1.2, h.2]

/-- `f t` for every triple `t` with `t i ∈ A i`. -/
def allTriples (A : Fin 3 → List ℕ) (f : (Fin 3 → ℕ) → Bool) : Bool :=
  (A 0).all fun i₀ ↦ (A 1).all fun i₁ ↦ (A 2).all fun i₂ ↦ f ![i₀, i₁, i₂]

theorem allTriples_sound {A : Fin 3 → List ℕ} {f : (Fin 3 → ℕ) → Bool}
    (h : allTriples A f = true) {t : Fin 3 → ℕ} (ht : ∀ i, t i ∈ A i) : f t = true := by
  simp only [allTriples, List.all_eq_true] at h
  have := h _ (ht 0) _ (ht 1) _ (ht 2)
  convert this using 2
  funext i
  fin_cases i <;> rfl

theorem dot_homView {R : Type*} [CommRing R] (g : Fin 3 → R) (a : Fin 3) (D S T : R) :
    g ⬝ᵥ (homView a D S T).toFun = g a * D + g (a + 1) * S + g (a + 2) * T := by
  fin_cases a <;> simp [homView, dotProduct, Fin.sum_univ_three] <;> ring

theorem dot_viewDir {R : Type*} [CommRing R] (g : Fin 3 → R) (a : Fin 3) (s t : R) :
    g ⬝ᵥ viewDir a s t = g a + g (a + 1) * s + g (a + 2) * t := by
  fin_cases a <;> simp [viewDir, dotProduct, Fin.sum_univ_three] <;> ring

/-- The view coordinates of a point of a box, times the denominator, lie between the
numerators of the ends. -/
theorem Box.mem_view {b : Box} (hden : 0 < b.den) {y : Fin 5 → ℝ} (hy : b.Mem 5 y) :
    ((b.lo.getD 0 0 : ℝ) ≤ b.den * y 0 ∧ b.den * y 0 ≤ b.hi.getD 0 0) ∧
      ((b.lo.getD 1 0 : ℝ) ≤ b.den * y 1 ∧ b.den * y 1 ≤ b.hi.getD 1 0) := by
  have hd : (0 : ℝ) < b.den := by exact_mod_cast hden
  have h₀ := hy 0
  have h₁ := hy 1
  simp only [Fin.val_zero, Fin.val_one] at h₀ h₁
  rw [div_le_iff₀ hd, le_div_iff₀ hd] at h₀ h₁
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2]

section Exact

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-! ### Premises on sets of view directions -/

/-- **Cone bounds.** The view direction `u` lies in `c` times the convex hull of the exact
points `us`, for some `c > 0`: every functional `g` has `c (g ⬝ᵥ p) ≤ g ⬝ᵥ u` at some point `p`
of `us`. Premises linear in `u` then hold at `u` when they hold at the points. The corners of a
view box are one instance (`coneBound_viewCorners`), the images of the vertices of a parameter box
under a view map another (`Modules/Check/Leaf/WZoom.lean`). -/
def ConeBound (us : List (V3 κ)) (u : Fin 3 → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ g : Fin 3 → ℝ, ∃ p ∈ us, c * (g ⬝ᵥ Exact.reV p) ≤ g ⬝ᵥ u

/-- `g ⬝ᵥ p ≥ 0` at the points `p` of `us`, by the sign tests of `κ`. -/
def nonnegAt (us : List (V3 κ)) (g : V3 κ) : Bool :=
  us.all fun p ↦ Exact.nonneg (g.dot p)

/-- `g ⬝ᵥ p > 0` at the points `p` of `us`, by the sign tests of `κ`. -/
def posAt (us : List (V3 κ)) (g : V3 κ) : Bool :=
  us.all fun p ↦ Exact.pos (g.dot p)

namespace ConeBound

variable {us : List (V3 κ)} {u : Fin 3 → ℝ}

theorem nonneg_of (hu : ConeBound us u) {g : Fin 3 → ℝ}
    (h : ∀ p ∈ us, 0 ≤ g ⬝ᵥ Exact.reV p) : 0 ≤ g ⬝ᵥ u := by
  obtain ⟨c, hc, hg⟩ := hu
  obtain ⟨p, hp, hle⟩ := hg g
  exact (mul_nonneg hc.le (h p hp)).trans hle

theorem pos_of (hu : ConeBound us u) {g : Fin 3 → ℝ}
    (h : ∀ p ∈ us, 0 < g ⬝ᵥ Exact.reV p) : 0 < g ⬝ᵥ u := by
  obtain ⟨c, hc, hg⟩ := hu
  obtain ⟨p, hp, hle⟩ := hg g
  exact (mul_pos hc (h p hp)).trans_le hle

theorem nonneg (hu : ConeBound us u) {g : V3 κ} (h : nonnegAt us g = true) :
    0 ≤ Exact.reV g ⬝ᵥ u :=
  hu.nonneg_of fun p hp ↦ by
    rw [← Exact.re_dot]
    exact Exact.nonneg_sound _ (List.all_eq_true.mp h p hp)

theorem pos (hu : ConeBound us u) {g : V3 κ} (h : posAt us g = true) :
    0 < Exact.reV g ⬝ᵥ u :=
  hu.pos_of fun p hp ↦ by
    rw [← Exact.re_dot]
    exact Exact.pos_sound _ (List.all_eq_true.mp h p hp)

/-- Cone bounds of positive multiples. -/
theorem of_smul {r : ℝ} (hr : 0 < r) (hu : ConeBound us (r • u)) : ConeBound us u := by
  obtain ⟨c, hc, hg⟩ := hu
  refine ⟨c / r, div_pos hc hr, fun g ↦ ?_⟩
  obtain ⟨p, hp, hle⟩ := hg g
  refine ⟨p, hp, ?_⟩
  rw [dotProduct_smul, smul_eq_mul] at hle
  rw [div_mul_eq_mul_div, div_le_iff₀ hr]
  linarith

end ConeBound

/-- The four corners of the view box of `b` (coordinates `0` and `1`), as homogeneous view
directions of view chart `a` over the denominator of `b`. -/
def viewCorners (a : Fin 3) (b : Box) : List (V3 κ) :=
  [homView a (Exact.ofInt b.den) (Exact.ofInt (b.lo.getD 0 0)) (Exact.ofInt (b.lo.getD 1 0)),
    homView a (Exact.ofInt b.den) (Exact.ofInt (b.lo.getD 0 0)) (Exact.ofInt (b.hi.getD 1 0)),
    homView a (Exact.ofInt b.den) (Exact.ofInt (b.hi.getD 0 0)) (Exact.ofInt (b.lo.getD 1 0)),
    homView a (Exact.ofInt b.den) (Exact.ofInt (b.hi.getD 0 0)) (Exact.ofInt (b.hi.getD 1 0))]

/-- **Corners.** At a point of the view box, `den` times an affine function of the view
coordinates is at least its homogeneous value at one of the four corners. -/
theorem exists_viewCorner_le (G : Fin 3 → ℝ) (a : Fin 3) {b : Box} (hden : 0 < b.den)
    {y : Fin 5 → ℝ} (hy : b.Mem 5 y) : ∃ u ∈ (viewCorners a b : List (V3 κ)),
      G ⬝ᵥ Exact.reV u ≤ b.den * (G ⬝ᵥ viewDir a (y 0) (y 1)) := by
  obtain ⟨⟨hs₀, hs₁⟩, ht₀, ht₁⟩ := Box.mem_view hden hy
  have key (S T : ℤ) : G ⬝ᵥ Exact.reV (homView a (Exact.ofInt (b.den : ℤ)) (Exact.ofInt S)
      (Exact.ofInt T) : V3 κ) = G a * b.den + G (a + 1) * S + G (a + 2) * T := by
    rw [Exact.reV, map_homView, dot_homView]
    simp [Exact.re_ofInt]
  have hf : (b.den : ℝ) * (G ⬝ᵥ viewDir a (y 0) (y 1)) =
      G a * b.den + G (a + 1) * (b.den * y 0) + G (a + 2) * (b.den * y 1) := by
    rw [dot_viewDir]; ring
  simp only [viewCorners, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left, key, hf]
  rcases le_total 0 (G (a + 1)) with hβ | hβ <;>
    rcases le_total 0 (G (a + 2)) with hγ | hγ
  · left; nlinarith [mul_le_mul_of_nonneg_left hs₀ hβ, mul_le_mul_of_nonneg_left ht₀ hγ]
  · right; left
    nlinarith [mul_le_mul_of_nonneg_left hs₀ hβ, mul_le_mul_of_nonpos_left ht₁ hγ]
  · right; right; left
    nlinarith [mul_le_mul_of_nonpos_left hs₁ hβ, mul_le_mul_of_nonneg_left ht₀ hγ]
  · right; right; right
    nlinarith [mul_le_mul_of_nonpos_left hs₁ hβ, mul_le_mul_of_nonpos_left ht₁ hγ]

/-- **The corners of a view box** bound the view directions of its points, with `c = 1 / den`. -/
theorem coneBound_viewCorners {a : Fin 3} {b : Box} (hden : 0 < b.den) {y : Fin 5 → ℝ}
    (hy : b.Mem 5 y) : ConeBound (viewCorners a b : List (V3 κ)) (viewDir a (y 0) (y 1)) := by
  have hd : (0 : ℝ) < b.den := by exact_mod_cast hden
  refine ⟨(b.den : ℝ)⁻¹, inv_pos.mpr hd, fun g ↦ ?_⟩
  obtain ⟨u, hu, hle⟩ := exists_viewCorner_le (κ := κ) g a hden hy
  exact ⟨u, hu, by rw [inv_mul_le_iff₀ hd]; exact hle⟩

/-- The functionals `c ⨯₃ eₖ` for `k = 0, 1, 2`: coordinate `k` of `u ⨯₃ c` is
`(c ⨯₃ eₖ) ⬝ᵥ u`. -/
def crossAxes (c : V3 κ) : List (V3 κ) :=
  [⟨Exact.ofInt 0, c.z, Exact.ofInt 0 - c.y⟩, ⟨Exact.ofInt 0 - c.z, Exact.ofInt 0, c.x⟩,
    ⟨c.y, Exact.ofInt 0 - c.x, Exact.ofInt 0⟩]

theorem dot_crossAxes_eq_zero {c : V3 κ} {u : Fin 3 → ℝ} (h : u ⨯₃ Exact.reV c = 0) :
    ∀ g ∈ crossAxes c, Exact.reV g ⬝ᵥ u = 0 := by
  have h₀ := congrFun h 0
  have h₁ := congrFun h 1
  have h₂ := congrFun h 2
  simp only [cross_apply, Exact.reV, V3.toFun_map, Pi.zero_apply] at h₀ h₁ h₂
  simp only [crossAxes, List.mem_cons, List.not_mem_nil, or_false]
  rintro g (rfl | rfl | rfl) <;>
    simp [Exact.reV, V3.toFun_map, dotProduct, Fin.sum_univ_three, Exact.re_sub,
      Exact.re_ofInt] at h₀ h₁ h₂ ⊢ <;> linarith

/-- The support normal `u ⨯₃ c` does not vanish: one of its coordinates, a functional of `u`, has
the same strict sign at all the points. -/
def normalOk (us : List (V3 κ)) (c : V3 κ) : Bool :=
  (crossAxes c).any fun g ↦ posAt us g || posAt us (V3.smul (Exact.ofInt (-1)) g)

theorem reV_neg_one_smul (g : V3 κ) :
    Exact.reV (V3.smul (Exact.ofInt (-1)) g) = -Exact.reV g := by
  rw [Exact.reV_smul, Exact.re_ofInt]
  simp

theorem normalOk_sound {us : List (V3 κ)} {c : V3 κ} (h : normalOk us c = true)
    {u : Fin 3 → ℝ} (hu : ConeBound us u) : u ⨯₃ Exact.reV c ≠ 0 := by
  intro h0
  obtain ⟨g, hg, hpos⟩ := List.any_eq_true.mp h
  have hz := dot_crossAxes_eq_zero h0 g hg
  rcases Bool.or_eq_true_iff.mp hpos with hp | hp
  · exact (hu.pos hp).ne' hz
  · have := hu.pos hp
    rw [reV_neg_one_smul, neg_dotProduct, hz, neg_zero] at this
    exact lt_irrefl _ this

theorem allIdx_getElem {α : Type} {f : ℕ → α → Bool} :
    ∀ {k : ℕ} {l : List α}, allIdx f k l = true → ∀ j (hj : j < l.length), f (k + j) l[j] = true
  | _, [], _, j, hj => absurd hj (Nat.not_lt_zero j)
  | k, a :: l, h, j, hj => by
    simp only [allIdx, Bool.and_eq_true] at h
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have := allIdx_getElem h.2 j (by simpa using hj)
      rwa [show k + 1 + j = k + (j + 1) by omega] at this

theorem all₂_map {α β γ : Type} {r : β → γ → Bool} {g : α → β} {h : α → γ} {l : List α}
    (H : List.all₂ r (l.map g) (l.map h) = true) : ∀ x ∈ l, r (g x) (h x) = true := by
  rw [List.all₂_eq_true, List.forall₂_map_left_iff, List.forall₂_map_right_iff,
    List.forall₂_same] at H
  exact H

/-- From the points of `us` to their cone: if every point `j` of `pts` has an anchor `i ∈ A` that
dominates it along `u ⨯₃ c` at every `u ∈ us`, it does at every direction of the cone. -/
theorem envelope_of_corners {pts us : List (V3 κ)} {c : V3 κ} {A : List ℕ}
    (h : ∀ j < pts.length, ∃ i ∈ A, ∀ p ∈ us,
      0 ≤ (Exact.reV p ⨯₃ Exact.reV c) ⬝ᵥ (Exact.reV (pt pts i) - Exact.reV (pt pts j)))
    {u : Fin 3 → ℝ} (hu : ConeBound us u) :
    ∀ x ∈ (Polyhedron.ofPoints pts).vertices, ∃ i ∈ A,
      (u ⨯₃ Exact.reV c) ⬝ᵥ x ≤ (u ⨯₃ Exact.reV c) ⬝ᵥ Exact.reV (pt pts i) := by
  intro x hx
  obtain ⟨w, hw, rfl⟩ := Polyhedron.mem_ofPoints.mp hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hw
  obtain ⟨i, hi, hc⟩ := h j hj
  refine ⟨i, hi, ?_⟩
  have hpj : pt pts j = pts[j] := by rw [pt, List.getD_eq_getElem _ _ hj]
  have key : ∀ v : Fin 3 → ℝ,
      Exact.reV c ⨯₃ (Exact.reV (pt pts i) - Exact.reV (pt pts j)) ⬝ᵥ v =
        (v ⨯₃ Exact.reV c) ⬝ᵥ (Exact.reV (pt pts i) - Exact.reV (pt pts j)) := by
    intro v
    rw [dotProduct_comm, dot_cross_eq_cross_dot]
  have := hu.nonneg_of (g := Exact.reV c ⨯₃ (Exact.reV (pt pts i) - Exact.reV (pt pts j)))
    fun p hp ↦ by rw [key]; exact hc p hp
  rw [key, dotProduct_sub, hpj] at this
  linarith

/-- The exact route of `envelopeOk`: the values `n ⬝ᵥ p` once per normal `n = u ⨯₃ c` and point,
a row per point, and each test the sign of a difference of two of them. -/
def envelopeOkX (pts us : List (V3 κ)) (c : V3 κ) (A : List ℕ) : Bool :=
  let ns := us.map fun u ↦ u.cross c
  let rows := pts.map fun p ↦ ns.map fun n ↦ n.dot p
  let ar := A.map fun i ↦ (i, rows.getD i [])
  let N := pts.length
  A.all (fun i ↦ decide (i < N)) &&
    allIdx (fun j r ↦ ar.any fun a ↦
      a.1 == j || List.all₂ (fun x y ↦ Exact.nonneg (x - y)) a.2 r) 0 rows

/-- The ball route of `envelopeOk`, as Rust's `envelope_valid` on `f64` intervals: the balls
(`Exact.ballV`) of the normals once, of the differences once per point and anchor tried, and the
exact sign where a ball leaves it open. (A table of the values `n ⬝ᵥ p` as in `envelopeOkX` does
not pay here: nearly every point passes with the first anchor tried, and the table holds as many
ball products as the tests.) -/
def envelopeOkB (pts us : List (V3 κ)) (c : V3 κ) (A : List ℕ) : Bool :=
  let cb := Exact.ballV c
  let nbs := us.map fun u ↦ (u, (Exact.ballV u).cross cb)
  let N := pts.length
  A.all (fun i ↦ decide (i < N)) &&
    pts.all fun w ↦ A.any fun i ↦
      let d := (pt pts i).sub w
      let db := Exact.ballV d
      nbs.all fun p ↦
        let v := p.2.dot db
        v.isNonneg || (!v.isNeg && Exact.nonneg ((p.1.cross c).dot d))

/-- The tests of `envelopeOkX` at point `j`: an anchor `i ∈ A` that is the point itself, or whose
row passes the test `t` against the row of `j`. -/
theorem anchor_of_rows {β : Type} (f : V3 κ → β) (t : ℕ → β → β → Bool) {pts : List (V3 κ)}
    {A : List ℕ} {z : β} (hA : ∀ i ∈ A, i < pts.length) {j : ℕ} (hj : j < (pts.map f).length)
    (h : ((A.map fun i ↦ (i, (pts.map f).getD i z)).any fun a ↦
      a.1 == j || t a.1 a.2 (pts.map f)[j]) = true) :
    ∃ i ∈ A, i = j ∨ t i (f (pt pts i)) (f (pt pts j)) = true := by
  obtain ⟨a, ha, h⟩ := List.any_eq_true.mp h
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  refine ⟨i, hi, ?_⟩
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact .inl h
  · right
    rw [List.length_map] at hj
    rwa [getD_map_of_lt f ⟨Exact.ofInt 0, Exact.ofInt 0, Exact.ofInt 0⟩ z (hA i hi),
      List.getElem_map, ← List.getD_eq_getElem _ ⟨Exact.ofInt 0, Exact.ofInt 0, Exact.ofInt 0⟩
      hj] at h

theorem envelopeOkX_sound {pts us : List (V3 κ)} {c : V3 κ} {A : List ℕ}
    (h : envelopeOkX pts us c A = true) : ∀ j < pts.length, ∃ i ∈ A, ∀ p ∈ us,
      0 ≤ (Exact.reV p ⨯₃ Exact.reV c) ⬝ᵥ (Exact.reV (pt pts i) - Exact.reV (pt pts j)) := by
  unfold envelopeOkX at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  intro j hj
  have hj' : j < (pts.map fun p ↦ (us.map fun u ↦ u.cross c).map fun n ↦ n.dot p).length := by
    simpa using hj
  have := allIdx_getElem h.2 j hj'
  rw [Nat.zero_add] at this
  obtain ⟨i, hi, hij⟩ := anchor_of_rows (fun p ↦ (us.map fun u ↦ u.cross c).map fun n ↦ n.dot p)
    (fun _ x y ↦ List.all₂ (fun x y ↦ Exact.nonneg (x - y)) x y) h.1 hj' this
  refine ⟨i, hi, fun p hp ↦ ?_⟩
  rcases hij with rfl | hij
  · simp
  · simp only [List.map_map] at hij
    have := Exact.nonneg_sound _ (all₂_map hij p hp)
    simpa only [Function.comp_apply, Exact.re_sub, Exact.re_dot, Exact.reV_cross,
      dotProduct_sub, sub_nonneg] using this

theorem envelopeOkB_sound {pts us : List (V3 κ)} {c : V3 κ} {A : List ℕ}
    (h : envelopeOkB pts us c A = true) : ∀ j < pts.length, ∃ i ∈ A, ∀ p ∈ us,
      0 ≤ (Exact.reV p ⨯₃ Exact.reV c) ⬝ᵥ (Exact.reV (pt pts i) - Exact.reV (pt pts j)) := by
  unfold envelopeOkB at h
  simp only [Bool.and_eq_true] at h
  intro j hj
  have hw : pt pts j ∈ pts := by
    rw [pt, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  obtain ⟨i, hi, hc⟩ := List.any_eq_true.mp (List.all_eq_true.mp h.2 _ hw)
  refine ⟨i, hi, fun p hp ↦ ?_⟩
  have hn := List.all_eq_true.mp hc (p, (Exact.ballV p).cross (Exact.ballV c))
    (List.mem_map.mpr ⟨p, hp, rfl⟩)
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hn
  rcases hn with hb | ⟨-, he⟩
  · have henc := V3.Encl.dot (V3.Encl.cross (Exact.encl_ballV p) (Exact.encl_ballV c))
      (Exact.encl_ballV ((pt pts i).sub (pt pts j)))
    rw [Exact.reV_sub] at henc
    exact Ball.nonneg_sound henc hb
  · have := Exact.nonneg_sound _ he
    rwa [Exact.re_dot, Exact.reV_cross, Exact.reV_sub] at this

/-- **Envelope** of the support with direction `c` and anchors `A`: along the normal
`n = u ⨯₃ c`, every point `w` is dominated by some anchor `v i`, `i ∈ A`, at every direction of
the cone over `us`. The values `n ⬝ᵥ (v i - w)` are linear in `u`, so the check compares them at
the points of `us`: exactly over `ℤ` and `ℤ[√d]` (`envelopeOkX`), by balls first where
`Exact.ballFirst` (`envelopeOkB`). Both routes refuse an anchor out of range, as Rust does. -/
def envelopeOk (pts us : List (V3 κ)) (c : V3 κ) (A : List ℕ) : Bool :=
  if Exact.ballFirst (α := κ) then envelopeOkB pts us c A else envelopeOkX pts us c A

theorem envelopeOk_sound {pts us : List (V3 κ)} {c : V3 κ} {A : List ℕ}
    (h : envelopeOk pts us c A = true) {u : Fin 3 → ℝ} (hu : ConeBound us u) :
    ∀ x ∈ (Polyhedron.ofPoints pts).vertices, ∃ i ∈ A,
      (u ⨯₃ Exact.reV c) ⬝ᵥ x ≤ (u ⨯₃ Exact.reV c) ⬝ᵥ Exact.reV (pt pts i) := by
  unfold envelopeOk at h
  split_ifs at h
  · exact envelope_of_corners (envelopeOkB_sound h) hu
  · exact envelope_of_corners (envelopeOkX_sound h) hu

/-- The vectors `σ (c (i + 1) ⨯₃ c (i + 2))` of the balance weights. -/
def weightVec (σ : ℤ) (c : Fin 3 → V3 κ) (i : Fin 3) : V3 κ :=
  V3.smul (Exact.ofInt σ) ((c (i + 1)).cross (c (i + 2)))

/-- The balance weights `σ u ⬝ᵥ (c (i + 1) ⨯₃ c (i + 2))` are nonnegative, with a positive sum,
at the points. -/
def weightsOk (us : List (V3 κ)) (σ : ℤ) (c : Fin 3 → V3 κ) : Bool :=
  allFin3 (fun i ↦ nonnegAt us (weightVec σ c i)) &&
    posAt us (((weightVec σ c 0).add (weightVec σ c 1)).add (weightVec σ c 2))

theorem weightPoly_eq (σ : ℤ) (c : Fin 3 → V3 κ) (i : Fin 3) (u : Fin 3 → ℝ) :
    weightPoly (σ : ℝ) u (Exact.reV (c (i + 1))) (Exact.reV (c (i + 2))) =
      Exact.reV (weightVec σ c i) ⬝ᵥ u := by
  rw [weightVec, Exact.reV_smul, Exact.reV_cross, Exact.re_ofInt, smul_dotProduct, smul_eq_mul,
    weightPoly, dotProduct_comm]

theorem weightsOk_sound {us : List (V3 κ)} {σ : ℤ} {c : Fin 3 → V3 κ}
    (h : weightsOk us σ c = true) {u : Fin 3 → ℝ} (hu : ConeBound us u) :
    (∀ i, 0 ≤ weightPoly (σ : ℝ) u (Exact.reV (c (i + 1))) (Exact.reV (c (i + 2)))) ∧
    0 < ∑ i, weightPoly (σ : ℝ) u (Exact.reV (c (i + 1))) (Exact.reV (c (i + 2))) := by
  simp only [weightsOk, Bool.and_eq_true, allFin3_eq_true] at h
  refine ⟨fun i ↦ ?_, ?_⟩
  · rw [weightPoly_eq]
    exact hu.nonneg (h.1 i)
  · simp only [weightPoly_eq, Fin.sum_univ_three]
    have := hu.pos h.2
    simpa [Exact.reV_add, add_dotProduct] using this

/-! ### Blown-up views -/

/-- Along the normal `n`, every vertex of the polyhedron of `pts` is dominated by an anchor `i ∈ A`
(the envelope premise, at one view). -/
def Envelope (pts : List (V3 κ)) (n : Fin 3 → ℝ) (A : List ℕ) : Prop :=
  ∀ x ∈ (Polyhedron.ofPoints pts).vertices, ∃ i ∈ A, n ⬝ᵥ x ≤ n ⬝ᵥ Exact.reV (pt pts i)

/-- View directions for premises (`ViewCorners` in `regional.rs`): the cone over the points `us`
(`ConeBound`), and optionally a *blow-up* `(U₀, ws)` at the view `U₀`: a positive multiple of
each view is `U₀ + r w`, with a parameter `r ≥ 0` and `w` in the cone over the inner points `ws`.
Where `r > 0`, premises that fail at `U₀` alone can still hold (`Views.pos`, `Views.normal`): a
zoom piece at the centre view of its zoom (`Modules/Check/Leaf/WZoom.lean`). -/
structure Views (κ : Type) where
  /-- The points whose cone contains the views. -/
  us : List (V3 κ)
  /-- The blow-up: the centre view and the inner points. -/
  blow : Option (V3 κ × List (V3 κ))

namespace Views

/-- The view direction `u` lies in the views `V`, with blow-up parameter `r`. -/
def Mem (V : Views κ) (u : Fin 3 → ℝ) (r : ℝ) : Prop :=
  ConeBound V.us u ∧ ∀ U₀ ws, V.blow = some (U₀, ws) →
    ∃ s : ℝ, 0 < s ∧ ∃ w : Fin 3 → ℝ, ConeBound ws w ∧ s • u = Exact.reV U₀ + r • w

/-- `g ⬝ᵥ u > 0` on the views: at the points, or through the blow-up where `r > 0`, since
`g ⬝ᵥ U₀ = 0` and `g ⬝ᵥ w > 0` at the inner points. -/
def pos (V : Views κ) (g : V3 κ) : Bool :=
  posAt V.us g || match V.blow with
    | some (U₀, ws) => Exact.isZero (g.dot U₀) && posAt ws g
    | none => false

/-- The normal `u ⨯₃ c` does not vanish on the views: by `normalOk` at the points, or through the
blow-up where `r > 0`, since a coordinate of the normal vanishes at `U₀` and has a strict sign at
the inner points. -/
def normal (V : Views κ) (c : V3 κ) : Bool :=
  normalOk V.us c || match V.blow with
    | some (U₀, ws) => (crossAxes c).any fun g ↦
        Exact.isZero (g.dot U₀) && (posAt ws g || posAt ws (V3.smul (Exact.ofInt (-1)) g))
    | none => false

theorem dot_blow {U₀ : V3 κ} {g : V3 κ} (hg : Exact.re (g.dot U₀) = 0) {u w : Fin 3 → ℝ}
    {s r : ℝ} (heq : s • u = Exact.reV U₀ + r • w) :
    s * (Exact.reV g ⬝ᵥ u) = r * (Exact.reV g ⬝ᵥ w) := by
  have h := congrArg (Exact.reV g ⬝ᵥ ·) heq
  simp only [dotProduct_smul, smul_eq_mul, dotProduct_add] at h
  rw [h, ← Exact.re_dot, hg]
  simp

theorem pos_sound {V : Views κ} {g : V3 κ} (h : V.pos g = true) {u : Fin 3 → ℝ} {r : ℝ}
    (hu : V.Mem u r) (hr : 0 < r) : 0 < Exact.reV g ⬝ᵥ u := by
  unfold pos at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact hu.1.pos h
  · split at h
    next U₀ ws hb =>
      simp only [Bool.and_eq_true] at h
      obtain ⟨s, hs, w, hw, heq⟩ := hu.2 U₀ ws hb
      have h1 := dot_blow (Exact.isZero_sound _ h.1) heq
      have h2 : 0 < s * (Exact.reV g ⬝ᵥ u) := by rw [h1]; exact mul_pos hr (hw.pos h.2)
      exact pos_of_mul_pos_right h2 hs.le
    next => exact absurd h (by simp)

theorem normal_sound {V : Views κ} {c : V3 κ} (h : V.normal c = true) {u : Fin 3 → ℝ} {r : ℝ}
    (hu : V.Mem u r) (hr : 0 < r) : u ⨯₃ Exact.reV c ≠ 0 := by
  unfold normal at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact normalOk_sound h hu.1
  · split at h
    next U₀ ws hb =>
      obtain ⟨g, hg, hz⟩ := List.any_eq_true.mp h
      simp only [Bool.and_eq_true] at hz
      obtain ⟨s, hs, w, hw, heq⟩ := hu.2 U₀ ws hb
      intro h0
      have h1 := dot_blow (Exact.isZero_sound _ hz.1) heq
      rw [dot_crossAxes_eq_zero h0 g hg, mul_zero] at h1
      rcases Bool.or_eq_true_iff.mp hz.2 with hp | hp
      · have := mul_pos hr (hw.pos hp)
        linarith
      · have h2 := hw.pos hp
        rw [reV_neg_one_smul, neg_dotProduct] at h2
        have h3 : Exact.reV g ⬝ᵥ w < 0 := by linarith
        have := mul_neg_of_pos_of_neg hr h3
        linarith
    next => exact absurd h (by simp)

end Views

end Exact

/-! ### Balanced supports -/

/-- A support of a witness (`regional.rs`): the direction `c = v o₁ - v o₀` between two points,
the anchors `A` (indices of points), and the plug (the index of a point of the inner copy). -/
structure SupportData where
  /-- The start of the direction. -/
  o₀ : ℕ
  /-- The end of the direction. -/
  o₁ : ℕ
  /-- The anchors. -/
  anchors : List ℕ
  /-- The plug. -/
  plug : ℕ

/-- Balanced-support evidence (`BalancedSupport` in `regional.rs`): three supports and the sign
`σ` of the balance weights. -/
structure Balanced where
  /-- Support `0`. -/
  s₀ : SupportData
  /-- Support `1`. -/
  s₁ : SupportData
  /-- Support `2`. -/
  s₂ : SupportData
  /-- The sign of the weights. -/
  sigma : ℤ

namespace Balanced

/-- Support `i`. -/
def sup (w : Balanced) (i : Fin 3) : SupportData :=
  match i with
  | 0 => w.s₀
  | 1 => w.s₁
  | 2 => w.s₂

section Exact

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The direction `c i` of support `i`. -/
def dir (pts : List (V3 κ)) (w : Balanced) (i : Fin 3) : V3 κ :=
  (pt pts (w.sup i).o₁).sub (pt pts (w.sup i).o₀)

/-- The premises of the witness at the view directions of the cone over `us`: the plugs are
points, and the normals, envelopes and balance weights are valid. They concern the view only, so
every check that uses the witness on poses with those views shares them. -/
def premisesOk (pts us : List (V3 κ)) (w : Balanced) : Bool :=
  allFin3 (fun i ↦ decide ((w.sup i).plug < pts.length) && normalOk us (w.dir pts i) &&
      envelopeOk pts us (w.dir pts i) (w.sup i).anchors) &&
    weightsOk us w.sigma (w.dir pts)

/-- The witness polynomials are nonnegative at the view direction `u` and the quaternion `q`, for
every choice of anchors. -/
def PolyNonneg (pts : List (V3 κ)) (w : Balanced) (u : Fin 3 → ℝ) (q : Fin 4 → ℝ) : Prop :=
  ∀ t : Fin 3 → ℕ, (∀ i, t i ∈ (w.sup i).anchors) →
    0 ≤ balancedPoly (w.sigma : ℝ) u q (fun i ↦ Exact.reV (w.dir pts i))
      (fun i ↦ Exact.reV (pt pts (w.sup i).plug)) (fun i ↦ Exact.reV (pt pts (t i)))

/-- The premises of a balanced witness at the view direction `u` (checked on a cone of views by
`premisesOk`, and on views with a blow-up by `premisesOkV`). -/
structure Premises (pts : List (V3 κ)) (w : Balanced) (u : Fin 3 → ℝ) : Prop where
  /-- The plugs are points. -/
  plug : ∀ i, (w.sup i).plug < pts.length
  /-- The support normals do not vanish. -/
  normal : ∀ i, u ⨯₃ Exact.reV (w.dir pts i) ≠ 0
  /-- Along each normal, every point is dominated by an anchor. -/
  envelope : ∀ i, Envelope pts (u ⨯₃ Exact.reV (w.dir pts i)) (w.sup i).anchors
  /-- The balance weights are nonnegative. -/
  weights : ∀ i, 0 ≤ weightPoly (w.sigma : ℝ) u (Exact.reV (w.dir pts (i + 1)))
    (Exact.reV (w.dir pts (i + 2)))
  /-- The balance weights have a positive sum. -/
  sum : 0 < ∑ i, weightPoly (w.sigma : ℝ) u (Exact.reV (w.dir pts (i + 1)))
    (Exact.reV (w.dir pts (i + 2)))

theorem premises_of_ok {pts us : List (V3 κ)} {w : Balanced} (h : w.premisesOk pts us = true)
    {u : Fin 3 → ℝ} (hu : ConeBound us u) : w.Premises pts u := by
  simp only [premisesOk, Bool.and_eq_true, decide_eq_true_eq, allFin3_eq_true] at h
  obtain ⟨hsup, hwt⟩ := h
  obtain ⟨hw, hw₀⟩ := weightsOk_sound hwt hu
  exact ⟨fun i ↦ (hsup i).1.1, fun i ↦ normalOk_sound (hsup i).1.2 hu,
    fun i ↦ envelopeOk_sound (hsup i).2 hu, hw, hw₀⟩

/-- The premises on views with a blow-up: at all views (`strong`), or where the blow-up
parameter is positive. The envelopes and the weights' signs are checked at the points (they are
weak inequalities, valid at the centre view); the normals and the weights' sum may use the
blow-up. -/
def premisesOkV (pts : List (V3 κ)) (V : Views κ) (strong : Bool) (w : Balanced) : Bool :=
  if strong then w.premisesOk pts V.us else
    allFin3 (fun i ↦ decide ((w.sup i).plug < pts.length) && V.normal (w.dir pts i) &&
        envelopeOk pts V.us (w.dir pts i) (w.sup i).anchors) &&
      allFin3 (fun i ↦ nonnegAt V.us (weightVec w.sigma (w.dir pts) i)) &&
      V.pos (((weightVec w.sigma (w.dir pts) 0).add (weightVec w.sigma (w.dir pts) 1)).add
        (weightVec w.sigma (w.dir pts) 2))

theorem premises_of_okV {pts : List (V3 κ)} {V : Views κ} {strong : Bool} {w : Balanced}
    (h : w.premisesOkV pts V strong = true) {u : Fin 3 → ℝ} {r : ℝ} (hu : V.Mem u r)
    (hs : strong = true ∨ 0 < r) : w.Premises pts u := by
  unfold premisesOkV at h
  cases strong with
  | true => exact premises_of_ok h hu.1
  | false =>
    have hr : 0 < r := hs.resolve_left (by simp)
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
      allFin3_eq_true] at h
    obtain ⟨⟨hsup, hnn⟩, hsum⟩ := h
    refine ⟨fun i ↦ (hsup i).1.1, fun i ↦ Views.normal_sound (hsup i).1.2 hu hr,
      fun i ↦ envelopeOk_sound (hsup i).2 hu.1, fun i ↦ ?_, ?_⟩
    · rw [weightPoly_eq]
      exact hu.1.nonneg (hnn i)
    · simp only [weightPoly_eq, Fin.sum_univ_three]
      have := Views.pos_sound hsum hu hr
      simpa [Exact.reV_add, add_dotProduct] using this

/-- **Balanced supports at a representative.** If the premises hold at the view direction `u`,
and the witness polynomials are nonnegative at `u` and the quaternion `q ≠ 0`, the rotation of
`q` does not fit along `u`, with any translation. -/
theorem not_fitsAlong_of_premises {pts : List (V3 κ)} {w : Balanced} {u : Fin 3 → ℝ}
    {q : Fin 4 → ℝ} (hq0 : q ≠ 0) (h : w.Premises pts u) (hq : w.PolyNonneg pts u q) :
    ¬ (Polyhedron.ofPoints pts).FitsAlong u (quatRotation q) := by
  set c : Fin 3 → Fin 3 → ℝ := fun i ↦ Exact.reV (w.dir pts i)
  have hplug (i : Fin 3) := Polyhedron.pt_mem_ofPoints (h.plug i)
  -- For each support, an anchor maximising the normal.
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
  · -- The witness for the maximising anchors.
    have h0 := hq t ht
    rw [balancedPoly_rep _ _ hq0] at h0
    exact nonneg_of_mul_nonneg_right h0 (dotProduct_self_pos hq0)

/-- **At a fit, some witness polynomial is negative**: the contrapositive of
`not_fitsAlong_of_premises`, for combinations of witnesses. -/
theorem exists_neg_of_fitsAlong {pts : List (V3 κ)} {w : Balanced} {u : Fin 3 → ℝ}
    {q : Fin 4 → ℝ} (hq0 : q ≠ 0) (h : w.Premises pts u)
    (hfit : (Polyhedron.ofPoints pts).FitsAlong u (quatRotation q)) :
    ∃ t : Fin 3 → ℕ, (∀ i, t i ∈ (w.sup i).anchors) ∧
      balancedPoly (w.sigma : ℝ) u q (fun i ↦ Exact.reV (w.dir pts i))
        (fun i ↦ Exact.reV (pt pts (w.sup i).plug)) (fun i ↦ Exact.reV (pt pts (t i))) < 0 := by
  by_contra hne
  refine not_fitsAlong_of_premises hq0 h (fun t ht ↦ ?_) hfit
  by_contra hlt
  exact hne ⟨t, ht, lt_of_not_ge hlt⟩

/-- **Balanced supports at a pose.** If the premises hold at the view of the pose `p`, and the
witness polynomials are nonnegative at the view direction and the chart quaternion of `p`, no
translation makes `p` a fit. -/
theorem not_fitsAt_of_premises {pts : List (V3 κ)} {w : Balanced} {p : ChartPose}
    (h : w.Premises pts (viewDir p.view p.s p.t))
    (hq : w.PolyNonneg pts (viewDir p.view p.s p.t) (chartQuat p.rot p.x)) (τ : Fin 2 → ℝ) :
    ¬ (Polyhedron.ofPoints pts).FitsAt p τ := fun hfit ↦
  not_fitsAlong_of_premises (chartQuat_ne_zero _ _) h hq (Polyhedron.fitsAlong_of_fitsAt hfit)

/-- **At a fit, some witness polynomial is negative**: the contrapositive of
`not_fitsAt_of_premises`, for combinations of witnesses. -/
theorem exists_neg_of_premises {pts : List (V3 κ)} {w : Balanced} {p : ChartPose}
    (h : w.Premises pts (viewDir p.view p.s p.t)) {τ : Fin 2 → ℝ}
    (hfit : (Polyhedron.ofPoints pts).FitsAt p τ) :
    ∃ t : Fin 3 → ℕ, (∀ i, t i ∈ (w.sup i).anchors) ∧
      balancedPoly (w.sigma : ℝ) (viewDir p.view p.s p.t) (chartQuat p.rot p.x)
        (fun i ↦ Exact.reV (w.dir pts i)) (fun i ↦ Exact.reV (pt pts (w.sup i).plug))
        (fun i ↦ Exact.reV (pt pts (t i))) < 0 :=
  exists_neg_of_fitsAlong (chartQuat_ne_zero _ _) h (Polyhedron.fitsAlong_of_fitsAt hfit)

/-- **Balanced supports at a pose**, with the premises checked on a cone of views. -/
theorem not_fitsAt {pts us : List (V3 κ)} {w : Balanced} (h : w.premisesOk pts us = true)
    {p : ChartPose} (hu : ConeBound us (viewDir p.view p.s p.t))
    (hq : w.PolyNonneg pts (viewDir p.view p.s p.t) (chartQuat p.rot p.x)) (τ : Fin 2 → ℝ) :
    ¬ (Polyhedron.ofPoints pts).FitsAt p τ :=
  not_fitsAt_of_premises (premises_of_ok h hu) hq τ

/-- **At a fit, some witness polynomial is negative**, with the premises checked on a cone of
views. -/
theorem exists_neg_of_fitsAt {pts us : List (V3 κ)} {w : Balanced}
    (h : w.premisesOk pts us = true) {p : ChartPose} (hu : ConeBound us (viewDir p.view p.s p.t))
    {τ : Fin 2 → ℝ} (hfit : (Polyhedron.ofPoints pts).FitsAt p τ) :
    ∃ t : Fin 3 → ℕ, (∀ i, t i ∈ (w.sup i).anchors) ∧
      balancedPoly (w.sigma : ℝ) (viewDir p.view p.s p.t) (chartQuat p.rot p.x)
        (fun i ↦ Exact.reV (w.dir pts i)) (fun i ↦ Exact.reV (pt pts (w.sup i).plug))
        (fun i ↦ Exact.reV (pt pts (t i))) < 0 :=
  exists_neg_of_premises (premises_of_ok h hu) hfit

/-- The view directions of the poses of a chart box lie in the cone over its view corners. -/
theorem coneBound_of_mem_poses {B : ChartBox} (hden : 0 < B.box.den) {p : ChartPose}
    (hp : p ∈ B.poses) :
    ConeBound (viewCorners B.view B.box : List (V3 κ)) (viewDir p.view p.s p.t) := by
  obtain ⟨hview, -, hy⟩ := hp
  rw [hview]
  exact coneBound_viewCorners hden hy

end Exact

section Basis

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The check of a balanced-support claim on the chart box `B`, pre-rotated by `pre` if any,
bisecting at most `depth` times along each branch. -/
def check (pts : List (V3 κ)) (B : ChartBox) (depth : ℕ) (w : Balanced)
    (pre : Option (Q4 κ) := none) : Bool :=
  decide (0 < B.box.den) && Exact.preOk pre && w.premisesOk pts (viewCorners B.view B.box) &&
    allTriples (fun i ↦ (w.sup i).anchors) fun t ↦
      nonnegOn (balancedGen (Exact.ofInt w.sigma) B.view B.rot (w.dir pts)
        (fun i ↦ pt pts (w.sup i).plug) (fun i ↦ pt pts (t i)) pre) 5 depth B.box

/-- **Soundness of balanced-support claims from the signs of their polynomials**, on a box
pre-rotated by `pre`: the premises hold at the corners of the view box, and the witness polynomial
of every choice of anchors is nonnegative at the box's points (`check_sound_pre`; with the sparse
sign check, `checkS_sound_pre` in `Modules/Check/Leaf/SupportSparse.lean`). -/
theorem sound_of_nonneg {pts : List (V3 κ)} {B : ChartBox} {ev : Balanced} {pre : Option (Q4 κ)}
    (hden : 0 < B.box.den) (hpre : Exact.preOk pre = true)
    (hprem : ev.premisesOk pts (viewCorners B.view B.box) = true)
    (hpoly : ∀ t : Fin 3 → ℕ, (∀ i, t i ∈ (ev.sup i).anchors) → ∀ y : Fin 5 → ℝ, B.box.Mem 5 y →
      0 ≤ (balancedGen (Exact.ofInt ev.sigma) B.view B.rot (ev.dir pts)
        (fun i ↦ pt pts (ev.sup i).plug) (fun i ↦ pt pts (t i)) pre).run Exact.re
          (homEnv 5 1 y)) :
    (Polyhedron.ofPoints pts).NoFitRot B.poses (preRot (Exact.rePre pre)) := by
  intro p hp
  have hq := preQuat_ne_zero (chartQuat_ne_zero p.rot p.x) (Exact.rePre_ne_zero hpre)
  rw [ChartPose.rotation, chartRotation, ← quatRotation_preQuat]
  refine not_fitsAlong_of_premises hq (premises_of_ok hprem (coneBound_of_mem_poses hden hp))
    fun t ht ↦ ?_
  obtain ⟨hview, hrot, hy⟩ := hp
  have h0 := hpoly t ht _ hy
  rw [balancedGen_homEnv, one_pow, one_mul, Exact.re_ofInt, ← hrot, rotCoords_coords,
    ← hview] at h0
  exact h0

/-- **Soundness of balanced-support claims**, on a box pre-rotated by `pre`. -/
theorem check_sound_pre {pts : List (V3 κ)} {B : ChartBox} {depth : ℕ} {ev : Balanced}
    {pre : Option (Q4 κ)} (h : ev.check pts B depth pre = true) :
    (Polyhedron.ofPoints pts).NoFitRot B.poses (preRot (Exact.rePre pre)) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hden, hpre⟩, hprem⟩, hpoly⟩ := h
  exact sound_of_nonneg hden hpre hprem fun t ht y hy ↦
    nonnegOn_hom (balancedGen_isHomogeneous _ _ _ _ _ _ _) hden (allTriples_sound hpoly ht) hy

/-- **Soundness of balanced-support claims.** -/
theorem check_sound {pts : List (V3 κ)} {B : ChartBox} {depth : ℕ} {ev : Balanced}
    (h : ev.check pts B depth = true) : (Polyhedron.ofPoints pts).NoFit B.poses := by
  have h0 := check_sound_pre h
  rwa [Exact.rePre_none, preRot_none, Polyhedron.noFitRot_one] at h0

end Basis

end Balanced

end Check

end Nieuwland
