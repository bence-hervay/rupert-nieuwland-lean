import Modules.Check.Leaf.FitCheck
import Modules.Nieuwland.Basic

/-!
# Nieuwland lower bounds from weak fits

A weak fit record (`FitRecord` with `weak`, `code/src/io.rs`) at the plug scale `λ` is a pose and
a translation at which the shadow of `λ K`, rotated and moved, lies in the closed shadow of `K`
(`verify_weak_fit` in `code/src/geometry/contain.rs`; a strict record at a scale is one too).
`WeakFitData α` holds it over exact values `α`, with the hole polygon of `FitData`
(`Modules/Check/Leaf/FitCheck.lean`) and an *interior witness* `h`, a point strictly inside every edge
of the hole polygon. `WeakFitData.check` tests every moved point weakly (`Exact.nonneg`) and the
witness strictly (`Exact.pos`).

`WeakFitData.check_sound`: a passing check makes every smaller scale pass strictly through. For
`0 ≤ c < λ` and `t = c / λ`, the translation `t τ + (1 - t) h` moves the point `c X` of the
rotated plug to `t (λ X + τ) + (1 - t) h`. The orientation against an edge is affine in the point
(`orient_add_smul`), so it is `t` times a nonnegative value plus `1 - t > 0` times a positive one.
`WeakFitData.le_nieuwland_smul` concludes `λ ≤ nieuwland P` for the polyhedron of a fixture.

The witness is needed: on the hole polygon of a segment, whose two edges have opposite
orientations, the points of the segment pass both edges weakly, and no witness passes
(`Nieuwland/Examples/WeakRejections.lean`).

Everything is scaled as in `FitData`, and further:

* the scale: `λ = scaleNum / scaleDen` with `scaleNum : α` and a positive natural `scaleDen`;
* the witness: `h = (h₀ / H, h₁ / H)` with `H > 0`.

For a hole edge from `A = L' cᵢ` to `B = L' cᵢ₊₁` and a point `v`, the weak test value is
`det (B - A, scaleNum E · L' (M v) + scaleDen N D · τ - scaleDen N E · A)`, the orientation of
the moved point against the edge times `D² scaleDen N E > 0` (`orient_weak`), and the witness
value is `det (B - A, D · h - H · A)`, the orientation of `h` times `D² H > 0`
(`orient_witness`).
-/

open Matrix

namespace Nieuwland

namespace Polyhedron

/-- **Vertex criterion for a plug and a hole.** For linear maps `f, g : ℝ³ → ℝ²`, the image of
`P` under `f`, moved by `t`, lies in the interior of the image of `Q` under `g` iff the moved
images of the vertices of `P` do. -/
theorem image_add_subset_interior_image_iff (P Q : Polyhedron)
    (f g : (Fin 3 → ℝ) →ₗ[ℝ] Fin 2 → ℝ) (t : Fin 2 → ℝ) :
    {f x + t | x ∈ P.hull} ⊆ interior {g x | x ∈ Q.hull} ↔
      ∀ v ∈ P.vertices, f v + t ∈ interior (convexHull ℝ {g w | w ∈ Q.vertices}) := by
  rw [Q.image_hull g]
  refine ⟨fun h v hv ↦ h ⟨v, subset_convexHull ℝ _ hv, rfl⟩, ?_⟩
  rintro h _ ⟨x, hx, rfl⟩
  have hconv : Convex ℝ ((fun x ↦ f x + t) ⁻¹' interior (convexHull ℝ {g w | w ∈ Q.vertices})) :=
    ((convex_convexHull ℝ _).interior.translate_preimage_left t).linear_preimage f
  exact convexHull_min (fun v hv ↦ h v hv) hconv hx

/-- **Fits in screen coordinates.** `P` passes through `Q` if, for a linear surjection
`L : ℝ³ → ℝ²`, a rotation `R` and a translation `t`, every vertex `v` of `P` has its moved image
`L (R *ᵥ v) + t` in the interior of the polygon spanned by the images `L w` of the vertices of
`Q`. -/
theorem fitsThrough_of_surjective (P Q : Polyhedron) (L : (Fin 3 → ℝ) →ₗ[ℝ] Fin 2 → ℝ)
    (hL : Function.Surjective L) {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO(3))
    (t : Fin 2 → ℝ)
    (h : ∀ v ∈ P.vertices, L (R *ᵥ v) + t ∈ interior (convexHull ℝ {L w | w ∈ Q.vertices})) :
    P.FitsThrough Q := by
  have h' : {L (R *ᵥ x) + t | x ∈ P.hull} ⊆ interior {L x | x ∈ Q.hull} :=
    (image_add_subset_interior_image_iff P Q (L ∘ₗ R.mulVecLin) L t).mpr h
  obtain ⟨Q₀, hQ₀, A, hA⟩ := exists_mem_SO3_linearEquiv_eq L hL
  simp only [hA] at h'
  rw [linearEquiv_image_add_subset_interior_iff] at h'
  exact ⟨Q₀ * R, Submonoid.mul_mem _ hQ₀ hR, Q₀, hQ₀, A.symm t,
    by simpa only [mulVec_mulVec] using h'⟩

end Polyhedron

/-- The orientation is affine in its point. -/
theorem orient_add_smul (a b p q : Fin 2 → ℝ) (t : ℝ) :
    orient a b (t • p + (1 - t) • q) = t * orient a b p + (1 - t) * orient a b q := by
  simp only [orient, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

namespace Check

variable {α : Type} [Add α] [Sub α] [Mul α] [Exact α]

/-- Exact data of a weak fit at a scale, with an interior witness (module docs). -/
structure WeakFitData (α : Type) where
  /-- The pose, the translation and the hole polygon. -/
  fit : FitData α
  /-- The numerator of the scale. -/
  scaleNum : α
  /-- The denominator of the scale, positive. -/
  scaleDen : ℕ
  /-- The numerator of the first coordinate of the witness. -/
  h₀ : α
  /-- The numerator of the second coordinate of the witness. -/
  h₁ : α
  /-- The denominator of the witness, positive. -/
  H : α

namespace WeakFitData

variable (W : WeakFitData α)

/-- The plug scale `λ`. -/
noncomputable def scale : ℝ :=
  Exact.re W.scaleNum / W.scaleDen

/-- The interior witness `h`, in screen coordinates. -/
noncomputable def witness : Fin 2 → ℝ :=
  ![Exact.re W.h₀ / Exact.re W.H, Exact.re W.h₁ / Exact.re W.H]

/-- The weak test value of edge `i` of the hole polygon and the point `v` (module docs). -/
def value (pts : List (V3 α)) (i : ℕ) (v : V3 α) : α :=
  let F := W.fit
  let n := F.corners.length
  let A := F.scr (Exact.pt pts (F.corners.getD i 0))
  let B := F.scr (Exact.pt pts (F.corners.getD ((i + 1) % n) 0))
  let P := F.scr (F.q.rotate v)
  let GN := Exact.ofInt W.scaleDen * F.q.norm2
  let LE := W.scaleNum * F.E
  let GND := GN * F.D
  let GNE := GN * F.E
  FitData.det2 (B.1 - A.1, B.2 - A.2)
    (LE * P.1 + GND * F.τ₀ - GNE * A.1, LE * P.2 + GND * F.τ₁ - GNE * A.2)

/-- The witness value of edge `i` of the hole polygon (module docs). -/
def witnessValue (pts : List (V3 α)) (i : ℕ) : α :=
  let F := W.fit
  let n := F.corners.length
  let A := F.scr (Exact.pt pts (F.corners.getD i 0))
  let B := F.scr (Exact.pt pts (F.corners.getD ((i + 1) % n) 0))
  FitData.det2 (B.1 - A.1, B.2 - A.2) (F.D * W.h₀ - W.H * A.1, F.D * W.h₁ - W.H * A.2)

/-- The head of `check`: the head of the fit's check, positive denominators of the scale and the
witness, and the witness strictly inside every edge of the hole polygon. -/
def checkHead (pts : List (V3 α)) : Bool :=
  W.fit.checkHead pts && decide (0 < W.scaleDen) && Exact.pos W.H &&
    (List.range W.fit.corners.length).all fun i ↦ Exact.pos (W.witnessValue pts i)

/-- **The weak fit check**: the head, and every moved point inside or on every edge of the hole
polygon. -/
def check (pts : List (V3 α)) : Bool :=
  W.checkHead pts && (List.range W.fit.corners.length).all fun i ↦
    pts.all fun v ↦ Exact.nonneg (W.value pts i v)

/-- The points `j, …, j + k - 1` against every edge of the hole polygon: a block of `check`. -/
def checkBlock (pts : List (V3 α)) (j k : ℕ) : Bool :=
  (List.range W.fit.corners.length).all fun i ↦
    ((pts.drop j).take k).all fun v ↦ Exact.nonneg (W.value pts i v)

/-- **The weak fit check in blocks** of `k` points (`FitData.check_of_blocks`). -/
theorem check_of_blocks {pts : List (V3 α)} {k nb : ℕ} (hn : pts.length ≤ nb * k)
    (hh : W.checkHead pts = true) (hb : ∀ c < nb, W.checkBlock pts (c * k) k = true) :
    W.check pts = true := by
  rw [check, hh, Bool.true_and, List.all_eq_true]
  intro i hi
  rw [List.all_eq_true]
  intro v hv
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  have hk : 0 < k := Nat.pos_of_ne_zero fun h ↦ by rw [h, Nat.mul_zero] at hn; omega
  have hc : j / k < nb := (Nat.div_lt_iff_lt_mul hk).mpr (by omega)
  have hblk := hb (j / k) hc
  simp only [checkBlock, List.all_eq_true] at hblk
  refine hblk i hi _ (List.mem_iff_getElem.mpr ⟨j % k, ?_, ?_⟩)
  · simp only [List.length_take, List.length_drop]
    have := Nat.mod_lt j hk
    have := Nat.div_add_mod' j k
    omega
  · simp only [List.getElem_take, List.getElem_drop]
    congr 1
    have := Nat.div_add_mod' j k
    omega

/-! ### Meaning -/

/-- **The scaled orientation of a scaled point.** -/
theorem orient_weak {D N E G l a₀ a₁ b₀ b₁ p₀ p₁ τ₀ τ₁ : ℝ} (hD : D ≠ 0) (hN : N ≠ 0)
    (hE : E ≠ 0) (hG : G ≠ 0) :
    orient ![a₀ / D, a₁ / D] ![b₀ / D, b₁ / D]
        ((l / G) • (N⁻¹ • ![p₀ / D, p₁ / D]) + ![τ₀ / E, τ₁ / E]) =
      ((b₀ - a₀) * (l * E * p₁ + G * N * D * τ₁ - G * N * E * a₁) -
        (b₁ - a₁) * (l * E * p₀ + G * N * D * τ₀ - G * N * E * a₀)) / (D ^ 2 * G * N * E) := by
  simp only [orient]
  simp
  field_simp

/-- **The scaled orientation of the witness.** -/
theorem orient_witness {D H a₀ a₁ b₀ b₁ h₀ h₁ : ℝ} (hD : D ≠ 0) (hH : H ≠ 0) :
    orient ![a₀ / D, a₁ / D] ![b₀ / D, b₁ / D] ![h₀ / H, h₁ / H] =
      ((b₀ - a₀) * (D * h₁ - H * a₁) - (b₁ - a₁) * (D * h₀ - H * a₀)) / (D ^ 2 * H) := by
  simp only [orient]
  simp
  field_simp

theorem re_value (pts : List (V3 α)) (i : ℕ) (v : V3 α) :
    Exact.re (W.value pts i v) =
      let F := W.fit
      let n := F.corners.length
      let A := F.scr (Exact.pt pts (F.corners.getD i 0))
      let B := F.scr (Exact.pt pts (F.corners.getD ((i + 1) % n) 0))
      let P := F.scr (F.q.rotate v)
      let N := Exact.re F.q.norm2
      let G : ℝ := W.scaleDen
      (Exact.re B.1 - Exact.re A.1) *
          (Exact.re W.scaleNum * Exact.re F.E * Exact.re P.2 +
            G * N * Exact.re F.D * Exact.re F.τ₁ - G * N * Exact.re F.E * Exact.re A.2) -
        (Exact.re B.2 - Exact.re A.2) *
          (Exact.re W.scaleNum * Exact.re F.E * Exact.re P.1 +
            G * N * Exact.re F.D * Exact.re F.τ₀ - G * N * Exact.re F.E * Exact.re A.1) := by
  simp only [value, FitData.det2, Exact.re_sub, Exact.re_add, Exact.re_mul, Exact.re_ofInt,
    Int.cast_natCast]

theorem re_witnessValue (pts : List (V3 α)) (i : ℕ) :
    Exact.re (W.witnessValue pts i) =
      let F := W.fit
      let n := F.corners.length
      let A := F.scr (Exact.pt pts (F.corners.getD i 0))
      let B := F.scr (Exact.pt pts (F.corners.getD ((i + 1) % n) 0))
      (Exact.re B.1 - Exact.re A.1) * (Exact.re F.D * Exact.re W.h₁ - Exact.re W.H * Exact.re A.2) -
        (Exact.re B.2 - Exact.re A.2) *
          (Exact.re F.D * Exact.re W.h₀ - Exact.re W.H * Exact.re A.1) := by
  simp only [witnessValue, FitData.det2, Exact.re_sub, Exact.re_mul]

/-- **Soundness of the weak fit check**: every scale `0 ≤ c < λ` passes strictly through. -/
theorem check_sound {pts : List (V3 α)} (h : W.check pts = true) :
    ∀ c, 0 ≤ c → c < W.scale →
      ((Polyhedron.ofPoints pts).smul c).FitsThrough (Polyhedron.ofPoints pts) := by
  intro c hc hlt
  simp only [check, checkHead, FitData.checkHead, Bool.and_eq_true, List.all_eq_true,
    List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hD, hk⟩, hE⟩, hcor⟩, hlen⟩, hG⟩, hH⟩, hw⟩, hv⟩ := h
  have hD' := Exact.pos_sound _ hD
  have hk' := Exact.pos_sound _ hk
  have hE' := Exact.pos_sound _ hE
  have hH' := Exact.pos_sound _ hH
  have hG' : (0 : ℝ) < W.scaleDen := by exact_mod_cast hG
  have hN' : 0 < Exact.re W.fit.q.norm2 := by
    rw [Q4.map_norm2 Exact.isArith, Q4.norm2_eq_dotProduct]
    refine lt_of_lt_of_le (pow_pos hk' 2) ?_
    rw [FitData.re_qget, sq]
    exact Finset.single_le_sum (f := fun j ↦ (W.fit.q.map Exact.re).toFun j *
      (W.fit.q.map Exact.re).toFun j) (fun j _ ↦ mul_self_nonneg _) (Finset.mem_univ W.fit.rot)
  have hs : 0 < W.scale := hc.trans_lt hlt
  have ht0 : 0 ≤ c / W.scale := div_nonneg hc hs.le
  have ht1 : 0 < 1 - c / W.scale := by rw [sub_pos, div_lt_one hs]; exact hlt
  have hn : W.fit.corners.length - 1 + 1 = W.fit.corners.length := by omega
  refine Polyhedron.fitsThrough_of_surjective _ _
    (screenₗ W.fit.pose.view W.fit.pose.s W.fit.pose.t) (screen_surjective _ _ _)
    W.fit.pose.rotation_mem ((c / W.scale) • W.fit.translation + (1 - c / W.scale) • W.witness)
    fun x hx ↦ ?_
  obtain ⟨y, hy, rfl⟩ := Polyhedron.mem_smul_vertices.mp hx
  obtain ⟨v, hvm, rfl⟩ := Polyhedron.mem_ofPoints.mp hy
  have key : ∀ i : Fin (W.fit.corners.length - 1 + 1),
      0 < orient (W.fit.pose.screen (Exact.reV (Exact.pt pts (W.fit.corners.getD i 0))))
        (W.fit.pose.screen (Exact.reV (Exact.pt pts (W.fit.corners.getD ↑(i + 1) 0))))
        (W.fit.pose.screen (W.fit.pose.rotation *ᵥ (c • Exact.reV v)) +
          ((c / W.scale) • W.fit.translation + (1 - c / W.scale) • W.witness)) := by
    intro i
    have hi : ((i + 1 : Fin (W.fit.corners.length - 1 + 1)) : ℕ) =
        (i.val + 1) % W.fit.corners.length := by
      rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
      exact congrArg _ hn
    have h0 := Exact.nonneg_sound _ (hv i (by omega) v hvm)
    have h1 := Exact.pos_sound _ (hw i (by omega))
    rw [re_value] at h0
    rw [re_witnessValue] at h1
    have hp : W.fit.pose.screen (W.fit.pose.rotation *ᵥ (c • Exact.reV v)) +
        ((c / W.scale) • W.fit.translation + (1 - c / W.scale) • W.witness) =
        (c / W.scale) • (W.scale • W.fit.pose.screen (W.fit.pose.rotation *ᵥ Exact.reV v) +
          W.fit.translation) + (1 - c / W.scale) • W.witness := by
      rw [Matrix.mulVec_smul, FitData.screen_smul, smul_add, smul_smul, div_mul_cancel₀ c hs.ne',
        add_assoc]
    rw [hp, orient_add_smul, hi]
    refine add_pos_of_nonneg_of_pos (mul_nonneg ht0 ?_) (mul_pos ht1 ?_)
    · rw [W.fit.screen_eq hD'.ne', W.fit.screen_eq hD'.ne', W.fit.rotation_mulVec hk'.ne',
        FitData.screen_smul, W.fit.screen_eq hD'.ne', FitData.translation, scale,
        orient_weak hD'.ne' hN'.ne' hE'.ne' hG'.ne']
      exact div_nonneg h0 (by positivity)
    · rw [W.fit.screen_eq hD'.ne', W.fit.screen_eq hD'.ne', witness,
        orient_witness hD'.ne' hH'.ne']
      exact div_pos h1 (by positivity)
  refine interior_mono (convexHull_mono ?_) (mem_interior_convexHull_of_forall_orient_pos
    (w := fun i ↦ W.fit.pose.screen (Exact.reV (Exact.pt pts (W.fit.corners.getD i 0)))) key)
  rintro _ ⟨i, rfl⟩
  exact ⟨_, Exact.reV_pt_mem (hcor _ (getD_mem_of_lt 0 (by omega))), rfl⟩

/-- **A passing weak fit check bounds the Nieuwland number** of the polyhedron of the points. -/
theorem le_nieuwland {pts : List (V3 α)} (h : W.check pts = true)
    (hP : (Polyhedron.ofPoints pts).FullDim) : W.scale ≤ (Polyhedron.ofPoints pts).nieuwland :=
  Polyhedron.le_nieuwland_of_forall_lt hP fun c hc hlt ↦ W.check_sound h c hc.le hlt

/-- **A passing weak fit check bounds the Nieuwland number** of a polyhedron whose points are
those of `pts` times `s ≠ 0` (a fixture, `Polyhedron.eq_smul_ofPoints`). -/
theorem le_nieuwland_smul {pts : List (V3 α)} (h : W.check pts = true) {P : Polyhedron} {s : ℝ}
    (hs : s ≠ 0) (hP : P = (Polyhedron.ofPoints pts).smul s) (hdim : P.FullDim) :
    W.scale ≤ P.nieuwland := by
  subst hP
  rw [Polyhedron.nieuwland_smul hs]
  refine W.le_nieuwland h ?_
  simpa only [Polyhedron.smul_smul_inv hs] using hdim.smul (inv_ne_zero hs)

end WeakFitData

end Check

end Nieuwland
