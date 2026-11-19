import Modules.Check.Number.Exact
import Modules.Rupert.Fit
import Modules.Rupert.Scale

/-!
# Fits from exact data

A fit record (`FitRecord` in `code/src/io.rs`) is a pose and a translation in chart coordinates.
`FitData α` holds it over exact values `α` (`Modules/Check/Number/Exact.lean`), with the hole polygon,
the counterclockwise corners of the outer shadow as indices of points (computed by the exporter,
as `PoseData::new` in `code/src/geometry/contain.rs` does). `FitData.check` is the strict test of
`verify_fit` in `contain.rs`, and `FitData.isRupert` turns a passing check into `IsRupert` for
the polyhedron of the points, through `Polyhedron.Fit`.

Everything is scaled to stay in `α`:

* the view: `s = S / D`, `t = T / D` with `D > 0`, and the screen map times `D`,
  `L' x = (D x (a + 1) - S x a, D x (a + 2) - T x a)` (`FitData.scr`);
* the rotation: any positive multiple `q` of the chart quaternion (`q rot > 0`); the rotation is
  `M / N` with `M = Q(q)` and `N = |q|²`;
* the translation `τ / E` with `E > 0`.

For a hole edge from `A = L' cᵢ` to `B = L' cᵢ₊₁` and a point `v`, the test value is
`det (B - A, E · L' (M v) + N D · τ - N E · A)`, the orientation of the moved point against the
edge times `D² N E > 0` (`orient_scaled`).
-/

open Matrix

namespace Nieuwland.Check

variable {α : Type} [Add α] [Sub α] [Mul α] [Exact α]

/-- Component `k` of a quaternion, for the kernel. -/
def Q4.get {β : Type*} (q : Q4 β) (k : Fin 4) : β :=
  match k with
  | 0 => q.w
  | 1 => q.x
  | 2 => q.y
  | 3 => q.z

theorem Q4.get_eq_toFun {β : Type*} (q : Q4 β) (k : Fin 4) : q.get k = q.toFun k := by
  fin_cases k <;> rfl

/-- Point `j` of `pts`, or `0` if there is none. -/
def Exact.pt (pts : List (V3 α)) (j : ℕ) : V3 α :=
  pts.getD j ⟨Exact.ofInt 0, Exact.ofInt 0, Exact.ofInt 0⟩

theorem Exact.reV_pt_mem {pts : List (V3 α)} {j : ℕ} (hj : j < pts.length) :
    Exact.reV (Exact.pt pts j) ∈ (Polyhedron.ofPoints pts).vertices :=
  Polyhedron.mem_ofPoints.mpr ⟨_, by
    rw [Exact.pt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    exact List.getElem_mem hj, rfl⟩

theorem getD_mem_of_lt {β : Type*} {l : List β} {i : ℕ} (d : β) (h : i < l.length) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

/-- The index of chart coordinate `j` of rotation chart `k`: the places other than `k`, in
increasing order. -/
def chartSlot (k : Fin 4) (j : Fin 3) : Fin 4 :=
  if j.val < k.val then ⟨j.val, by omega⟩ else ⟨j.val + 1, by omega⟩

/-- Exact fit data (module docs). -/
structure FitData (α : Type) where
  /-- The view chart. -/
  view : Fin 3
  /-- The denominator of the view coordinates, positive. -/
  D : α
  /-- The numerator of `s`. -/
  S : α
  /-- The numerator of `t`. -/
  T : α
  /-- The rotation chart. -/
  rot : Fin 4
  /-- A positive multiple of the chart quaternion. -/
  q : Q4 α
  /-- The numerator of the first translation coordinate. -/
  τ₀ : α
  /-- The numerator of the second translation coordinate. -/
  τ₁ : α
  /-- The denominator of the translation, positive. -/
  E : α
  /-- The hole polygon: indices of points whose shadows trace the outer shadow
  counterclockwise. -/
  corners : List ℕ

namespace FitData

variable (F : FitData α)

/-- The scaled screen map `L'` (module docs). -/
def scr (v : V3 α) : α × α :=
  (F.D * v.get (F.view + 1) - F.S * v.get F.view, F.D * v.get (F.view + 2) - F.T * v.get F.view)

/-- `det (p, q)`. -/
def det2 (p r : α × α) : α :=
  p.1 * r.2 - p.2 * r.1

/-- The test value of edge `i` of the hole polygon and the point `v` (module docs). -/
def value (pts : List (V3 α)) (i : ℕ) (v : V3 α) : α :=
  let n := F.corners.length
  let A := F.scr (Exact.pt pts (F.corners.getD i 0))
  let B := F.scr (Exact.pt pts (F.corners.getD ((i + 1) % n) 0))
  let P := F.scr (F.q.rotate v)
  let N := F.q.norm2
  let ND := N * F.D
  let NE := N * F.E
  det2 (B.1 - A.1, B.2 - A.2)
    (F.E * P.1 + ND * F.τ₀ - NE * A.1, F.E * P.2 + ND * F.τ₁ - NE * A.2)

/-- **The fit check**: the denominators are positive, the corners are points, and every moved
point lies strictly inside every edge of the hole polygon. -/
def check (pts : List (V3 α)) : Bool :=
  Exact.pos F.D && Exact.pos (F.q.get F.rot) && Exact.pos F.E &&
    F.corners.all (· < pts.length) && decide (0 < F.corners.length) &&
    (List.range F.corners.length).all fun i ↦ pts.all fun v ↦ Exact.pos (F.value pts i v)

/-- The head of `check`: positive denominators and corners that are points. -/
def checkHead (pts : List (V3 α)) : Bool :=
  Exact.pos F.D && Exact.pos (F.q.get F.rot) && Exact.pos F.E &&
    F.corners.all (· < pts.length) && decide (0 < F.corners.length)

/-- The points `j, …, j + k - 1` against every edge of the hole polygon: a block of `check`. -/
def checkBlock (pts : List (V3 α)) (j k : ℕ) : Bool :=
  (List.range F.corners.length).all fun i ↦
    ((pts.drop j).take k).all fun v ↦ Exact.pos (F.value pts i v)

theorem check_eq_head (pts : List (V3 α)) : F.check pts =
    (F.checkHead pts && (List.range F.corners.length).all fun i ↦
      pts.all fun v ↦ Exact.pos (F.value pts i v)) := rfl

/-- **The fit check in blocks** of `k` points, for separate kernel checks (a `decide +kernel`
holds the work of its declaration in memory). -/
theorem check_of_blocks {pts : List (V3 α)} {k nb : ℕ} (hn : pts.length ≤ nb * k)
    (hh : F.checkHead pts = true) (hb : ∀ c < nb, F.checkBlock pts (c * k) k = true) :
    F.check pts = true := by
  rw [check_eq_head, hh, Bool.true_and, List.all_eq_true]
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

/-- The chart pose of the data. -/
noncomputable def pose : ChartPose where
  view := F.view
  s := Exact.re F.S / Exact.re F.D
  t := Exact.re F.T / Exact.re F.D
  rot := F.rot
  x j := Exact.re (F.q.get (chartSlot F.rot j)) / Exact.re (F.q.get F.rot)

/-- The translation of the data. -/
noncomputable def translation : Fin 2 → ℝ :=
  ![Exact.re F.τ₀ / Exact.re F.E, Exact.re F.τ₁ / Exact.re F.E]

theorem re_get (v : V3 α) (i : Fin 3) : Exact.re (v.get i) = Exact.reV v i := by
  fin_cases i <;> rfl

theorem re_qget (q : Q4 α) (k : Fin 4) : Exact.re (q.get k) = (q.map Exact.re).toFun k := by
  fin_cases k <;> rfl

/-- The chart quaternion of the pose is the data's quaternion, scaled. -/
theorem chartQuat_pose (hk : Exact.re (F.q.get F.rot) ≠ 0) :
    chartQuat F.rot F.pose.x = (Exact.re (F.q.get F.rot))⁻¹ • (F.q.map Exact.re).toFun := by
  have h := hk
  rw [re_qget] at h
  funext i
  simp only [pose, re_qget, Pi.smul_apply, smul_eq_mul]
  generalize (F.q.map Exact.re).toFun = Q at h ⊢
  generalize F.rot = k at h ⊢
  fin_cases k <;> fin_cases i <;> simp [chartQuat, chartSlot] at h ⊢ <;> field_simp

theorem quatMatrix_smul {R : Type*} [CommRing R] (c : R) (q : Fin 4 → R) :
    quatMatrix (c • q) = c ^ 2 • quatMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quatMatrix] <;> ring

theorem quatRotation_smul {c : ℝ} (hc : c ≠ 0) (q : Fin 4 → ℝ) :
    quatRotation (c • q) = quatRotation q := by
  rw [quatRotation, quatRotation, quatMatrix_smul, smul_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, smul_eq_mul]
  by_cases hq : q ⬝ᵥ q = 0
  · simp [hq]
  · congr 1
    field_simp

/-- The rotation of the pose applied to a point: `M v / N`. -/
theorem rotation_mulVec (hk : Exact.re (F.q.get F.rot) ≠ 0) (v : V3 α) :
    F.pose.rotation *ᵥ Exact.reV v =
      (Exact.re F.q.norm2)⁻¹ • Exact.reV (F.q.rotate v) := by
  rw [ChartPose.rotation, chartRotation, show F.pose.rot = F.rot from rfl, F.chartQuat_pose hk,
    quatRotation_smul (inv_ne_zero hk), quatRotation, smul_mulVec, Exact.reV, Exact.reV,
    Q4.map_rotate Exact.isArith, Q4.toFun_rotate, Q4.map_norm2 Exact.isArith,
    Q4.norm2_eq_dotProduct]

/-- The screen map of the pose: `L' x / D`. -/
theorem screen_eq (hD : Exact.re F.D ≠ 0) (v : V3 α) :
    F.pose.screen (Exact.reV v) =
      ![Exact.re (F.scr v).1 / Exact.re F.D, Exact.re (F.scr v).2 / Exact.re F.D] := by
  simp only [ChartPose.screen, screen, pose, scr, Exact.re_sub, Exact.re_mul, re_get]
  funext i
  fin_cases i <;> simp <;> field_simp

theorem screen_smul (p : ChartPose) (c : ℝ) (x : Fin 3 → ℝ) :
    p.screen (c • x) = c • p.screen x := by
  funext i
  fin_cases i <;> simp [ChartPose.screen, screen] <;> ring

/-- **The scaled orientation.** -/
theorem orient_scaled {D N E a₀ a₁ b₀ b₁ p₀ p₁ τ₀ τ₁ : ℝ} (hD : D ≠ 0) (hN : N ≠ 0) (hE : E ≠ 0) :
    orient ![a₀ / D, a₁ / D] ![b₀ / D, b₁ / D] (N⁻¹ • ![p₀ / D, p₁ / D] + ![τ₀ / E, τ₁ / E]) =
      ((b₀ - a₀) * (E * p₁ + N * D * τ₁ - N * E * a₁) -
        (b₁ - a₁) * (E * p₀ + N * D * τ₀ - N * E * a₀)) / (D ^ 2 * N * E) := by
  simp only [orient]
  simp
  field_simp

theorem re_value (pts : List (V3 α)) (i : ℕ) (v : V3 α) :
    Exact.re (F.value pts i v) =
      let n := F.corners.length
      let A := F.scr (Exact.pt pts (F.corners.getD i 0))
      let B := F.scr (Exact.pt pts (F.corners.getD ((i + 1) % n) 0))
      let P := F.scr (F.q.rotate v)
      let N := Exact.re F.q.norm2
      (Exact.re B.1 - Exact.re A.1) *
          (Exact.re F.E * Exact.re P.2 + N * Exact.re F.D * Exact.re F.τ₁ -
            N * Exact.re F.E * Exact.re A.2) -
        (Exact.re B.2 - Exact.re A.2) *
          (Exact.re F.E * Exact.re P.1 + N * Exact.re F.D * Exact.re F.τ₀ -
            N * Exact.re F.E * Exact.re A.1) := by
  simp only [value, det2, Exact.re_sub, Exact.re_add, Exact.re_mul]

/-- **Soundness of the fit check.** -/
noncomputable def toFit {pts : List (V3 α)} (h : F.check pts = true) :
    (Polyhedron.ofPoints pts).Fit := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hD, hk⟩, hE⟩, hc⟩, hlen⟩, hv⟩ := h
  have hD' := Exact.pos_sound _ hD
  have hk' := Exact.pos_sound _ hk
  have hE' := Exact.pos_sound _ hE
  have hN' : 0 < Exact.re F.q.norm2 := by
    rw [Q4.map_norm2 Exact.isArith, Q4.norm2_eq_dotProduct]
    refine lt_of_lt_of_le (pow_pos hk' 2) ?_
    rw [re_qget, sq]
    exact Finset.single_le_sum (f := fun j ↦ (F.q.map Exact.re).toFun j *
      (F.q.map Exact.re).toFun j) (fun j _ ↦ mul_self_nonneg _) (Finset.mem_univ F.rot)
  have hn : F.corners.length - 1 + 1 = F.corners.length := by omega
  exact
    { pose := F.pose
      translation := F.translation
      n := F.corners.length - 1
      corner := fun i ↦ Exact.reV (Exact.pt pts (F.corners.getD i 0))
      corner_mem := fun i ↦ Exact.reV_pt_mem (hc _ (getD_mem_of_lt 0 (by omega)))
      orient_pos := by
        intro x hx i
        obtain ⟨v, hvm, rfl⟩ := Polyhedron.mem_ofPoints.mp hx
        have h0 := Exact.pos_sound _ (hv i (by omega) v hvm)
        rw [re_value] at h0
        have hi : ((i + 1 : Fin (F.corners.length - 1 + 1)) : ℕ) =
            (i.val + 1) % F.corners.length := by
          rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
          exact congrArg _ hn
        rw [hi, F.screen_eq hD'.ne', F.screen_eq hD'.ne', F.rotation_mulVec hk'.ne',
          screen_smul, F.screen_eq hD'.ne', translation, orient_scaled hD'.ne' hN'.ne' hE'.ne']
        exact div_pos h0 (by positivity) }

/-- **A passing fit check proves the Rupert property.** -/
theorem isRupert {pts : List (V3 α)} (h : F.check pts = true) :
    (Polyhedron.ofPoints pts).IsRupert :=
  (F.toFit h).isRupert

end FitData

/-- A polyhedron whose points are `c • reV v` for the exact points `v` of `pts` is the polyhedron
of `pts` scaled by `c` (for the coordinates of a fixture from its points times a common
denominator). -/
theorem _root_.Nieuwland.Polyhedron.eq_smul_ofPoints {P : Polyhedron} {pts : List (V3 α)} {c : ℝ}
    {L : List (Fin 3 → ℝ)} {inst : DecidableEq (Fin 3 → ℝ)}
    (hP : P.vertices = @List.toFinset _ inst L) (h : pts.map (fun v ↦ c • Exact.reV v) = L) :
    P = (Polyhedron.ofPoints pts).smul c := by
  classical
  cases P with
  | mk V =>
    simp only at hP
    subst hP h
    congr 1
    ext x
    simp [Polyhedron.mem_ofPoints]

end Nieuwland.Check
