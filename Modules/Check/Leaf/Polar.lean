import Modules.Check.Chart.Cover
import Modules.Check.Leaf.FamilyLeaf

/-!
# Polar zooms

Polar zoom evidence (`PolarZoom` in `code/src/proof/regional/zoom.rs`) proves `NoFit` on a chart
box `B` around an exact centre `x₀` of its rotation box `X`: typically a pose where support
obstructions vanish exactly (an alignment or another touch), so that no witness is positive on a
neighbourhood of `x₀`.

**Polar coordinates.** Every `x ∈ X` other than `x₀` is `x₀ + δ f` with `0 < δ ≤ 1` and `f` on a
face of `X - x₀` that does not contain `0` (`exists_polar`): `f axis = hi axis - x₀ axis` with
`x₀ axis < hi axis`, or the same with `lo`. For each such face, a cover tree splits the pieces
`(δ, y₁, y₂)` (`Polar.faceBox`), with `y₁`, `y₂` the free coordinates of the face point `x₀ + f`
of `X`, and each leaf carries a support witness (balanced or centred), whose premises concern the
view box only (`Wit.premisesOk` at its corners). The pieces are rational boxes even when `x₀` is
irrational: Rust's splits halve the free coordinates of `f`, which halves those of `x₀ + f`.

**The witness along a ray.** With the chart quaternion `q₀` of `x₀` and the direction `q₁` of `f`
(`chartQuat_add_smul`), the witness `g(δ) = balancedPoly u (q₀ + δ q₁)` is quadratic in `δ`
(`balancedPoly_add_smul`). On a piece `[δ₀, δ₁]` with `δ₀ ≥ 0` (`Polar.pieceTripleOk`):

* if every support obstruction vanishes at `x₀` (`Polar.vanishes`, an exact integer check), then
  `g(0) = 0` and `g(δ) = δ N(δ)` with `N` affine, so it suffices that `N(δ₀) ≥ 0`, from the
  derivative `N(0)` if `δ₀ = 0` and from the slice `g(δ₀)` otherwise, and that `g(δ₁) ≥ 0`
  (`nonneg_of_vanishing`). Slices and the derivative are polynomials in `(s, t, y₁, y₂)` of degree
  4 (`Polar.sliceGen`, `Polar.derivGen`);
* otherwise `g ≥ 0` is checked on the piece as a polynomial in `(s, t, δ, y₁, y₂)` of degree 6
  (`Polar.fullGen`).

The Rust checker also requires `δ₀ > 0` in the second case and treats `x₀` separately; here a
piece with `δ₀ = 0` covers `x₀` in either case, and any face covers `x₀` at `δ = 0`. Rust also
requires the faces with trees to be exactly those that do not contain `x₀`; here a face without a
tree must be shown not to be needed by an exact sign test (`Polar.notRequired`), since the sign
tests of number fields may refuse.

**Exact data.** With a common denominator `C`, the centre is `A / C`, with `A` over the field, and
`f axis = E / C` (`PolarFrame`). The quaternions `C q₀` and `C q₁` are `homQuat k C A` and
`homQuat k 0 (placeAxis axis E (C y₁ - A f₁) (C y₂ - A f₂))`, with `f₁`, `f₂` the free axes, and
every polynomial of a piece is the witness at `l C q₀ + m C q₁` (`polarQ`, `polarG`) in
homogeneous variables, for suitable `l` and `m`. An irrational centre (an alignment over a number
field) only puts field elements into the coefficients.

**Pre-rotated boxes.** On a box pre-rotated by `q_c` (`NoFitRot`), the quaternion of `x₀ + δ f`
is `(q₀ + δ q₁) q_c = q₀ q_c + δ q₁ q_c` (`preQuat_add`, `preQuat_smul`), so all of the above holds
with `q₀ q_c` and `q₁ q_c`: the polynomials are the witness at `polarQ … · q_c` (`preQ`), and the
vanishing test is at the exact quaternion `C q₀ q_c`.
-/

open Matrix

namespace Nieuwland.Check

/-! ### Faces of a box -/

section Place

variable {α β : Type*}

/-- The vector with `z` at place `axis`, and `y₁`, `y₂` at the other two places in increasing
order. -/
def placeAxis (axis : Fin 3) (z y₁ y₂ : α) : V3 α :=
  match axis with
  | 0 => ⟨z, y₁, y₂⟩
  | 1 => ⟨y₁, z, y₂⟩
  | 2 => ⟨y₁, y₂, z⟩

/-- The two places other than `axis`, in increasing order. -/
def freeAxes (axis : Fin 3) : Fin 3 × Fin 3 :=
  match axis with
  | 0 => (1, 2)
  | 1 => (0, 2)
  | 2 => (0, 1)

theorem map_placeAxis (f : α → β) (axis : Fin 3) (z y₁ y₂ : α) :
    (placeAxis axis z y₁ y₂).map f = placeAxis axis (f z) (f y₁) (f y₂) := by
  fin_cases axis <;> rfl

theorem toFun_placeAxis_self (x : Fin 3 → α) (axis : Fin 3) :
    (placeAxis axis (x axis) (x (freeAxes axis).1) (x (freeAxes axis).2)).toFun = x := by
  funext i
  fin_cases axis <;> fin_cases i <;> rfl

end Place

/-! ### Polar coordinates in a box -/

/-- **Polar coordinates around a point of a box.** A point `x ≠ x₀` of the box
`∏ [lo j, hi j] ∋ x₀` is `x₀ + δ f` with `0 < δ ≤ 1` and `f` in the box
`∏ [lo j - x₀ j, hi j - x₀ j]`, on a face of it that does not contain `0`: `f j = hi j - x₀ j`
with `x₀ j < hi j` (`upper`), or `f j = lo j - x₀ j` with `lo j < x₀ j`. (`δ` is the largest ratio
of `x - x₀` to the extent of the box beyond `x₀`, over the six faces.) -/
theorem exists_polar {lo hi x₀ x : Fin 3 → ℝ} (h₀ : ∀ j, lo j ≤ x₀ j ∧ x₀ j ≤ hi j)
    (hx : ∀ j, lo j ≤ x j ∧ x j ≤ hi j) (hne : x ≠ x₀) :
    ∃ (j : Fin 3) (upper : Bool) (δ : ℝ) (f : Fin 3 → ℝ), 0 < δ ∧ δ ≤ 1 ∧
      (bif upper then x₀ j < hi j else lo j < x₀ j) ∧
      f j = (bif upper then hi j else lo j) - x₀ j ∧
      (∀ i, lo i - x₀ i ≤ f i ∧ f i ≤ hi i - x₀ i) ∧ x = x₀ + δ • f := by
  classical
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Fin 3 × Bool → ℝ, ∀ i b,
      ρ (i, b) = gaugeRatio (x i - x₀ i) ((bif b then hi i else lo i) - x₀ i) :=
    ⟨fun ib ↦ gaugeRatio (x ib.1 - x₀ ib.1) ((bif ib.2 then hi ib.1 else lo ib.1) - x₀ ib.1),
      fun _ _ ↦ rfl⟩
  obtain ⟨⟨j, b⟩, -, hmax⟩ := Finset.exists_max_image Finset.univ ρ Finset.univ_nonempty
  have hup (i : Fin 3) : gaugeRatio (x i - x₀ i) (hi i - x₀ i) ≤ ρ (j, b) := by
    have h := hmax (i, true) (Finset.mem_univ _)
    rwa [hρ i true, Bool.cond_true] at h
  have hlo (i : Fin 3) : gaugeRatio (x i - x₀ i) (lo i - x₀ i) ≤ ρ (j, b) := by
    have h := hmax (i, false) (Finset.mem_univ _)
    rwa [hρ i false, Bool.cond_false] at h
  -- The largest ratio is positive, since `x ≠ x₀`.
  obtain ⟨i, hxi⟩ := Function.ne_iff.mp hne
  have hpos : 0 < ρ (j, b) := by
    rcases lt_or_gt_of_ne hxi with h | h
    · exact (gaugeRatio_pos_of_neg (by linarith) (by linarith [(hx i).1])).trans_le (hlo i)
    · exact (gaugeRatio_pos_of_pos (by linarith) (by linarith [(hx i).2])).trans_le (hup i)
  have hpos' : 0 < gaugeRatio (x j - x₀ j) ((bif b then hi j else lo j) - x₀ j) := by
    rw [← hρ j b]
    exact hpos
  obtain ⟨he, hmul⟩ := gaugeRatio_mul hpos'
  rw [← hρ j b] at hmul
  refine ⟨j, b, ρ (j, b), (ρ (j, b))⁻¹ • (x - x₀), hpos, ?_, ?_, ?_, fun i ↦ ?_, ?_⟩
  · rw [hρ j b]
    cases b
    · exact gaugeRatio_le_one_of_nonpos (e := lo j - x₀ j) (by linarith [(h₀ j).1])
        (by linarith [(hx j).1])
    · exact gaugeRatio_le_one_of_nonneg (e := hi j - x₀ j) (by linarith [(h₀ j).2])
        (by linarith [(hx j).2])
  · cases b
    · have he' : lo j - x₀ j ≠ 0 := he
      exact lt_of_le_of_ne (h₀ j).1 fun h ↦ he' (by rw [h, sub_self])
    · have he' : hi j - x₀ j ≠ 0 := he
      exact lt_of_le_of_ne (h₀ j).2 fun h ↦ he' (by rw [h, sub_self])
  · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [← hmul, inv_mul_cancel_left₀ hpos.ne']
  · have h₁ := le_mul_of_gaugeRatio_le (by linarith [(h₀ i).2]) (by linarith [(hx i).2]) (hup i)
    have h₂ := mul_le_of_gaugeRatio_le (by linarith [(h₀ i).1]) (by linarith [(hx i).1]) (hlo i)
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    exact ⟨(le_inv_mul_iff₀ hpos).mpr h₂, (inv_mul_le_iff₀ hpos).mpr h₁⟩
  · rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    abel

/-! ### The frame of a face -/

/-- The exact data of a polar zoom on one face, in rotation chart `k`. With the common
denominator `C > 0`, the centre is `x₀ = A / C` (`PolarFrame.centre`), and the face point with
free coordinates `y₁`, `y₂` is `x₀ + f` with `f = placeAxis axis (E / C) (y₁ - x₀ f₁) (y₂ - x₀ f₂)`
(`PolarFrame.face`). -/
structure PolarFrame (κ : Type) where
  /-- The rotation chart. -/
  k : Fin 4
  /-- The axis of the face. -/
  axis : Fin 3
  /-- The common denominator. -/
  C : ℤ
  /-- The numerators of the centre. -/
  A : V3 κ
  /-- The numerator of the coordinate of `f` along the axis. -/
  E : κ

namespace PolarFrame

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The centre `A / C`. -/
noncomputable def centre (F : PolarFrame κ) : Fin 3 → ℝ :=
  (F.C : ℝ)⁻¹ • Exact.reV F.A

/-- The vector `f` from the centre to the face point with free coordinates `y₁`, `y₂`. -/
noncomputable def face (F : PolarFrame κ) (y₁ y₂ : ℝ) : Fin 3 → ℝ :=
  (placeAxis F.axis (Exact.re F.E / F.C) (y₁ - F.centre (freeAxes F.axis).1)
    (y₂ - F.centre (freeAxes F.axis).2)).toFun

/-- The quaternion `C q₀ = homQuat k C A` of the centre. -/
def centreQuat (F : PolarFrame κ) : Q4 κ :=
  homQuat F.k (Exact.ofInt F.C) F.A

end PolarFrame

/-- The direction of rotation chart `k` along `f`, so that
`chartQuat k (x + δ • f) = chartQuat k x + δ • dirQuat k f` (`chartQuat_add_smul`). -/
def dirQuat {R : Type*} [CommRing R] (k : Fin 4) (f : Fin 3 → R) : Fin 4 → R :=
  chartQuat k f - chartQuat k 0

theorem chartQuat_add_smul {R : Type*} [CommRing R] (k : Fin 4) (x f : Fin 3 → R) (δ : R) :
    chartQuat k (x + δ • f) = chartQuat k x + δ • dirQuat k f := by
  funext i
  fin_cases k <;> fin_cases i <;> simp [chartQuat, dirQuat]

/-! ### Witness polynomials of a face, generically -/

section Generic

variable {κ α β : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] [Add α] [Sub α] [Mul α] [Add β]
  [Sub β] [Mul β]

/-- The quaternion `l C q₀ + m C q₁` in homogeneous coordinates (`toFun_polarQ`): `q₀` is the chart
quaternion of the centre and `q₁` the direction of the vector `f` to the face point with free
coordinates `Y₁ / D`, `Y₂ / D`. The exact data of the frame are embedded by `k`. -/
def polarQ (k : κ → α) (F : PolarFrame κ) (D l m Y₁ Y₂ : α) : Q4 α :=
  (Q4.smul l (homQuat F.k (k (Exact.ofInt F.C) * D) (V3.smul D (F.A.map k)))).add
    (Q4.smul m (homQuat F.k (k (Exact.ofInt 0)) (placeAxis F.axis (k F.E * D)
      (k (Exact.ofInt F.C) * Y₁ - D * k (F.A.get (freeAxes F.axis).1))
      (k (Exact.ofInt F.C) * Y₂ - D * k (F.A.get (freeAxes F.axis).2)))))

/-- The witness polynomial of the anchor choice `t` of `W` at the view direction
`homView a D S T` and the quaternion `polarQ k F D l m Y₁ Y₂` followed by the pre-rotation `pre`, if
any, with the exact data embedded by `k`. -/
def polarG (k : κ → α) (pts : List (V3 κ)) (W : Wit κ) (t : List ℕ) (a : Fin 3)
    (F : PolarFrame κ) (pre : Option (Q4 κ)) (S T D l m Y₁ Y₂ : α) : α :=
  (W.poly pts t).run k (homView a D S T) (preQ k (polarQ k F D l m Y₁ Y₂) pre)

variable {f : α → β}

theorem map_polarQ (hf : IsArith f) (k : κ → α) (F : PolarFrame κ) (D l m Y₁ Y₂ : α) :
    (polarQ k F D l m Y₁ Y₂).map f = polarQ (f ∘ k) F (f D) (f l) (f m) (f Y₁) (f Y₂) := by
  simp only [polarQ, Q4.map_add hf, Q4.map_smul hf, map_homQuat, V3.map_smul hf, map_placeAxis,
    hf.map_mul, hf.map_sub, V3.map_map]
  rfl

theorem map_polarG (hf : IsArith f) (k : κ → α) (pts : List (V3 κ)) (W : Wit κ) (t : List ℕ)
    (a : Fin 3) (F : PolarFrame κ) (pre : Option (Q4 κ)) (S T D l m Y₁ Y₂ : α) :
    f (polarG k pts W t a F pre S T D l m Y₁ Y₂) =
      polarG (f ∘ k) pts W t a F pre (f S) (f T) (f D) (f l) (f m) (f Y₁) (f Y₂) := by
  rw [polarG, (W.poly pts t).natural f hf, map_homView, map_preQ hf, map_polarQ hf]
  rfl

/-- The witness polynomial of the anchor choice `t` of `W` at the fixed view vector `U` and the
quaternion `polarQ k F D l m Y₁ Y₂` followed by the pre-rotation `pre`, if any. -/
def polarGAt (k : κ → α) (pts : List (V3 κ)) (W : Wit κ) (t : List ℕ) (U : V3 κ)
    (F : PolarFrame κ) (pre : Option (Q4 κ)) (D l m Y₁ Y₂ : α) : α :=
  (W.poly pts t).run k (U.map k) (preQ k (polarQ k F D l m Y₁ Y₂) pre)

theorem map_polarGAt (hf : IsArith f) (k : κ → α) (pts : List (V3 κ)) (W : Wit κ) (t : List ℕ)
    (U : V3 κ) (F : PolarFrame κ) (pre : Option (Q4 κ)) (D l m Y₁ Y₂ : α) :
    f (polarGAt k pts W t U F pre D l m Y₁ Y₂) =
      polarGAt (f ∘ k) pts W t U F pre (f D) (f l) (f m) (f Y₁) (f Y₂) := by
  rw [polarGAt, (W.poly pts t).natural f hf, map_preQ hf, map_polarQ hf]
  rfl

end Generic

/-! ### Meaning -/

section Meaning

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

theorem polarG_re (pts : List (V3 κ)) (W : Wit κ) (t : List ℕ) (a : Fin 3) (F : PolarFrame κ)
    (pre : Option (Q4 κ)) (S T D l m Y₁ Y₂ : ℝ) :
    polarG Exact.re pts W t a F pre S T D l m Y₁ Y₂ =
      W.val pts t (homView a D S T).toFun
        (preQuat (polarQ Exact.re F D l m Y₁ Y₂).toFun (Exact.rePre pre)) := by
  rw [polarG, Wit.run_re, toFun_preQ]

theorem polarGAt_re (pts : List (V3 κ)) (W : Wit κ) (t : List ℕ) (U : V3 κ) (F : PolarFrame κ)
    (pre : Option (Q4 κ)) (D l m Y₁ Y₂ : ℝ) :
    polarGAt Exact.re pts W t U F pre D l m Y₁ Y₂ =
      W.val pts t (Exact.reV U)
        (preQuat (polarQ Exact.re F D l m Y₁ Y₂).toFun (Exact.rePre pre)) := by
  rw [polarGAt, Wit.run_re, toFun_preQ]
  rfl

theorem toFun_polarQ_smul (F : PolarFrame κ) (d e D l m Y₁ Y₂ : ℝ) :
    (polarQ (Exact.re : κ → ℝ) F (d * D) (e * l) (e * m) (d * Y₁) (d * Y₂)).toFun =
      (d * e) • (polarQ Exact.re F D l m Y₁ Y₂).toFun := by
  obtain ⟨k, axis, C, A, E⟩ := F
  funext i
  fin_cases k <;> fin_cases axis <;> fin_cases i <;>
    simp [polarQ, homQuat, placeAxis, freeAxes, Q4.toFun, Q4.add, Q4.smul, V3.smul, V3.map,
      V3.get, Exact.re_ofInt] <;> ring

theorem toFun_polarQ_hom (F : PolarFrame κ) (d l m y₁ y₂ : ℝ) :
    (polarQ (Exact.re : κ → ℝ) F d l m (d * y₁) (d * y₂)).toFun =
      d • (polarQ Exact.re F 1 l m y₁ y₂).toFun := by
  simpa using toFun_polarQ_smul F d 1 1 l m y₁ y₂

theorem toFun_polarQ_hom₂ (F : PolarFrame κ) (d δ y₁ y₂ : ℝ) :
    (polarQ (Exact.re : κ → ℝ) F d d (d * δ) (d * y₁) (d * y₂)).toFun =
      d ^ 2 • (polarQ Exact.re F 1 1 δ y₁ y₂).toFun := by
  simpa [sq] using toFun_polarQ_smul F d d 1 1 δ y₁ y₂

/-- **The quaternion of a face point**: `C (l q₀ + m q₁)`. -/
theorem toFun_polarQ (F : PolarFrame κ) (hC : (F.C : ℝ) ≠ 0) (l m y₁ y₂ : ℝ) :
    (polarQ (Exact.re : κ → ℝ) F 1 l m y₁ y₂).toFun =
      (F.C : ℝ) • (l • chartQuat F.k F.centre + m • dirQuat F.k (F.face y₁ y₂)) := by
  obtain ⟨k, axis, C, A, E⟩ := F
  simp only [PolarFrame.centre, PolarFrame.face] at hC ⊢
  funext i
  fin_cases k <;> fin_cases axis <;> fin_cases i <;>
    simp [polarQ, homQuat, placeAxis, freeAxes, Q4.toFun, Q4.add, Q4.smul, V3.smul, V3.map,
      chartQuat, dirQuat, V3.get, Exact.reV, V3.toFun, Exact.re_ofInt] <;> field_simp

theorem toFun_centreQuat (F : PolarFrame κ) (hC : (F.C : ℝ) ≠ 0) :
    (F.centreQuat.map Exact.re).toFun = (F.C : ℝ) • chartQuat F.k F.centre := by
  obtain ⟨k, axis, C, A, E⟩ := F
  simp only [PolarFrame.centreQuat, PolarFrame.centre] at hC ⊢
  funext i
  fin_cases k <;> fin_cases i <;>
    simp [homQuat, Q4.map, Q4.toFun, chartQuat, Exact.reV, V3.map, V3.toFun, Exact.re_ofInt] <;>
      field_simp

end Meaning

/-! ### Witness polynomials of a face on boxes -/

section Env

variable {R : Type*} [CommRing R] (d : R) (y : Fin 4 → R)

@[simp] theorem homEnv_four_zero : homEnv 4 d y 0 = d * y 0 := rfl
@[simp] theorem homEnv_four_one : homEnv 4 d y 1 = d * y 1 := rfl
@[simp] theorem homEnv_four_two : homEnv 4 d y 2 = d * y 2 := rfl
@[simp] theorem homEnv_four_three : homEnv 4 d y 3 = d * y 3 := rfl
@[simp] theorem homEnv_four_four : homEnv 4 d y 4 = d := rfl

variable (z : Fin 2 → R) (w : Fin 3 → R)

@[simp] theorem homEnv_two_zero : homEnv 2 d z 0 = d * z 0 := rfl
@[simp] theorem homEnv_two_one : homEnv 2 d z 1 = d * z 1 := rfl
@[simp] theorem homEnv_two_two : homEnv 2 d z 2 = d := rfl
@[simp] theorem homEnv_three_zero : homEnv 3 d w 0 = d * w 0 := rfl
@[simp] theorem homEnv_three_one : homEnv 3 d w 1 = d * w 1 := rfl
@[simp] theorem homEnv_three_two : homEnv 3 d w 2 = d * w 2 := rfl
@[simp] theorem homEnv_three_three : homEnv 3 d w 3 = d := rfl

end Env

section Gen

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] (pts : List (V3 κ)) (W : Wit κ)
  (t : List ℕ) (a : Fin 3) (F : PolarFrame κ) (pre : Option (Q4 κ))

/-- The witness on the slice `δ = m / l` of a face, in the variables `(s, t, y₁, y₂)` with the
homogenising variable `4`. -/
def sliceGen (l m : ℤ) : GenPoly κ where
  run k x := polarG k pts W t a F pre (x 0) (x 1) (x 4) (k (Exact.ofInt l)) (k (Exact.ofInt m))
    (x 2) (x 3)
  natural f hf k x := by
    rw [map_polarG hf]
    rfl

/-- The derivative in `δ` at the centre of a witness that vanishes there: the slices at
`q₀ + q₁` and at `q₁`. -/
def derivGen : GenPoly κ where
  run k x := (sliceGen pts W t a F pre 1 1).run k x - (sliceGen pts W t a F pre 0 1).run k x
  natural f hf k x := by
    rw [hf.map_sub, (sliceGen pts W t a F pre 1 1).natural f hf,
      (sliceGen pts W t a F pre 0 1).natural f hf]

/-- The witness on the pieces of a face, in the variables `(s, t, δ, y₁, y₂)` with the
homogenising variable `5`. -/
def fullGen : GenPoly κ where
  run k x := polarG k pts W t a F pre (x 0) (x 1) (x 5) (x 5) (x 2) (x 3) (x 4)
  natural f hf k x := by
    rw [map_polarG hf]
    rfl

theorem sliceGen_homEnv (l m : ℤ) (d : ℝ) (y : Fin 4 → ℝ) :
    (sliceGen pts W t a F pre l m).run Exact.re (homEnv 4 d y) =
      d ^ W.deg * W.val pts t (viewDir a (y 0) (y 1))
        (preQuat (polarQ Exact.re F 1 (l : ℝ) (m : ℝ) (y 2) (y 3)).toFun (Exact.rePre pre)) := by
  change polarG Exact.re pts W t a F pre (homEnv 4 d y 0) (homEnv 4 d y 1) (homEnv 4 d y 4)
    (Exact.re (Exact.ofInt l : κ)) (Exact.re (Exact.ofInt m : κ)) (homEnv 4 d y 2)
    (homEnv 4 d y 3) = _
  rw [polarG_re, Exact.re_ofInt, Exact.re_ofInt]
  simp only [homEnv_four_zero, homEnv_four_one, homEnv_four_two, homEnv_four_three,
    homEnv_four_four]
  rw [toFun_homView, toFun_polarQ_hom, preQuat_smul, Wit.val_smul]

theorem fullGen_homEnv (d : ℝ) (y : Fin 5 → ℝ) :
    (fullGen pts W t a F pre).run Exact.re (homEnv 5 d y) =
      d ^ (W.deg + 2) * W.val pts t (viewDir a (y 0) (y 1))
        (preQuat (polarQ Exact.re F 1 1 (y 2) (y 3) (y 4)).toFun (Exact.rePre pre)) := by
  change polarG Exact.re pts W t a F pre (homEnv 5 d y 0) (homEnv 5 d y 1) (homEnv 5 d y 5)
    (homEnv 5 d y 5) (homEnv 5 d y 2) (homEnv 5 d y 3) (homEnv 5 d y 4) = _
  rw [polarG_re]
  simp only [homEnv_five_zero, homEnv_five_one, homEnv_five_two, homEnv_five_three,
    homEnv_five_four, homEnv_five_five]
  rw [toFun_homView, toFun_polarQ_hom₂, preQuat_smul, sq, mul_smul, Wit.val_smul,
    Wit.val_smul_quat]
  ring

theorem sliceGen_isHomogeneous (l m : ℤ) :
    (sliceGen pts W t a F pre l m).IsHomogeneous 4 W.deg :=
  fun d y ↦ by rw [sliceGen_homEnv, sliceGen_homEnv, one_pow, one_mul]

theorem derivGen_isHomogeneous : (derivGen pts W t a F pre).IsHomogeneous 4 W.deg :=
    fun d y ↦ by
  change (sliceGen pts W t a F pre 1 1).run Exact.re _ -
      (sliceGen pts W t a F pre 0 1).run Exact.re _ =
    _ * ((sliceGen pts W t a F pre 1 1).run Exact.re _ -
      (sliceGen pts W t a F pre 0 1).run Exact.re _)
  simp only [sliceGen_homEnv, one_pow, one_mul]
  ring

theorem fullGen_isHomogeneous : (fullGen pts W t a F pre).IsHomogeneous 5 (W.deg + 2) :=
    fun d y ↦ by
  rw [fullGen_homEnv, fullGen_homEnv, one_pow, one_mul]

/-! A width pair or centred support is linear in the view vector (`Wit.linear`), so on a piece it
is checked at each corner `U` of the view box (`exists_viewCorner_le`) in the coordinates of the
piece only, as `check_zoom_piece_in` in `regional/zoom.rs` checks centred supports. -/

/-- The witness at the view `U` on the slice `δ = m / l` of a face, in the variables `(y₁, y₂)`
with the homogenising variable `2`. -/
def sliceGenAt (U : V3 κ) (l m : ℤ) : GenPoly κ where
  run k x := polarGAt k pts W t U F pre (x 2) (k (Exact.ofInt l)) (k (Exact.ofInt m)) (x 0) (x 1)
  natural f hf k x := by
    rw [map_polarGAt hf]
    rfl

/-- The derivative in `δ` at the centre at the view `U`. -/
def derivGenAt (U : V3 κ) : GenPoly κ where
  run k x := (sliceGenAt pts W t F pre U 1 1).run k x - (sliceGenAt pts W t F pre U 0 1).run k x
  natural f hf k x := by
    rw [hf.map_sub, (sliceGenAt pts W t F pre U 1 1).natural f hf,
      (sliceGenAt pts W t F pre U 0 1).natural f hf]

/-- The witness at the view `U` on the pieces of a face, in the variables `(δ, y₁, y₂)` with the
homogenising variable `3`. -/
def fullGenAt (U : V3 κ) : GenPoly κ where
  run k x := polarGAt k pts W t U F pre (x 3) (x 3) (x 0) (x 1) (x 2)
  natural f hf k x := by
    rw [map_polarGAt hf]
    rfl

theorem sliceGenAt_homEnv (U : V3 κ) (l m : ℤ) (d : ℝ) (y : Fin 2 → ℝ) :
    (sliceGenAt pts W t F pre U l m).run Exact.re (homEnv 2 d y) =
      d ^ 2 * W.val pts t (Exact.reV U)
        (preQuat (polarQ Exact.re F 1 (l : ℝ) (m : ℝ) (y 0) (y 1)).toFun (Exact.rePre pre)) := by
  change polarGAt Exact.re pts W t U F pre (homEnv 2 d y 2) (Exact.re (Exact.ofInt l : κ))
    (Exact.re (Exact.ofInt m : κ)) (homEnv 2 d y 0) (homEnv 2 d y 1) = _
  rw [polarGAt_re, Exact.re_ofInt, Exact.re_ofInt]
  simp only [homEnv_two_zero, homEnv_two_one, homEnv_two_two]
  rw [toFun_polarQ_hom, preQuat_smul, Wit.val_smul_quat]

theorem fullGenAt_homEnv (U : V3 κ) (d : ℝ) (y : Fin 3 → ℝ) :
    (fullGenAt pts W t F pre U).run Exact.re (homEnv 3 d y) =
      d ^ 4 * W.val pts t (Exact.reV U)
        (preQuat (polarQ Exact.re F 1 1 (y 0) (y 1) (y 2)).toFun (Exact.rePre pre)) := by
  change polarGAt Exact.re pts W t U F pre (homEnv 3 d y 3) (homEnv 3 d y 3) (homEnv 3 d y 0)
    (homEnv 3 d y 1) (homEnv 3 d y 2) = _
  rw [polarGAt_re]
  simp only [homEnv_three_zero, homEnv_three_one, homEnv_three_two, homEnv_three_three]
  rw [toFun_polarQ_hom₂, preQuat_smul, Wit.val_smul_quat]
  ring

theorem sliceGenAt_isHomogeneous (U : V3 κ) (l m : ℤ) :
    (sliceGenAt pts W t F pre U l m).IsHomogeneous 2 2 :=
  fun d y ↦ by rw [sliceGenAt_homEnv, sliceGenAt_homEnv, one_pow, one_mul]

theorem derivGenAt_isHomogeneous (U : V3 κ) : (derivGenAt pts W t F pre U).IsHomogeneous 2 2 :=
    fun d y ↦ by
  change (sliceGenAt pts W t F pre U 1 1).run Exact.re _ -
      (sliceGenAt pts W t F pre U 0 1).run Exact.re _ =
    _ * ((sliceGenAt pts W t F pre U 1 1).run Exact.re _ -
      (sliceGenAt pts W t F pre U 0 1).run Exact.re _)
  simp only [sliceGenAt_homEnv, one_pow, one_mul]
  ring

theorem fullGenAt_isHomogeneous (U : V3 κ) : (fullGenAt pts W t F pre U).IsHomogeneous 3 4 :=
  fun d y ↦ by rw [fullGenAt_homEnv, fullGenAt_homEnv, one_pow, one_mul]

end Gen

/-! ### Polar zoom evidence -/

/-- A face of a polar zoom (`ZoomFace` in `regional/zoom.rs`): the face `x axis = hi` (`upper`) or
`x axis = lo` of the rotation box, with a cover tree of the pieces of its cone in the coordinates
`(δ, y₁, y₂)` (`Polar.faceBox`), whose leaves are support witnesses. A split of Rust's coordinate
`d` (free coordinates `0`, `1`, radius `2`) is a split of coordinate `d + 1 mod 3` here. -/
structure PolarFace (κ : Type) where
  /-- The axis. -/
  axis : Fin 3
  /-- Whether the face is the upper one. -/
  upper : Bool
  /-- The cover tree of the pieces. -/
  tree : Cover (Wit κ)

/-- Polar zoom evidence (`PolarZoom` in `regional/zoom.rs`): the centre `centre / den` in the
rotation chart, over the field, and the faces. -/
structure Polar (κ : Type) where
  /-- The numerators of the centre. -/
  centre : V3 κ
  /-- The denominator of the centre. -/
  den : ℕ
  /-- The faces. -/
  faces : List (PolarFace κ)

namespace Polar

/-! #### The boxes of a piece -/

/-- The box of `(s, t, y₁, y₂)`: the view box of `vb` and the free coordinates of the piece `b`
(coordinates `δ, y₁, y₂`), over the product of the denominators. -/
def sliceRegion (vb b : Box) : Box where
  lo := [vb.lo.getD 0 0 * b.den, vb.lo.getD 1 0 * b.den, b.lo.getD 1 0 * vb.den,
    b.lo.getD 2 0 * vb.den]
  hi := [vb.hi.getD 0 0 * b.den, vb.hi.getD 1 0 * b.den, b.hi.getD 1 0 * vb.den,
    b.hi.getD 2 0 * vb.den]
  den := vb.den * b.den

/-- The box of `(s, t, δ, y₁, y₂)`: the view box of `vb` and the piece `b`. -/
def pieceRegion (vb b : Box) : Box where
  lo := [vb.lo.getD 0 0 * b.den, vb.lo.getD 1 0 * b.den, b.lo.getD 0 0 * vb.den,
    b.lo.getD 1 0 * vb.den, b.lo.getD 2 0 * vb.den]
  hi := [vb.hi.getD 0 0 * b.den, vb.hi.getD 1 0 * b.den, b.hi.getD 0 0 * vb.den,
    b.hi.getD 1 0 * vb.den, b.hi.getD 2 0 * vb.den]
  den := vb.den * b.den

theorem cast_mul_div_left (x : ℤ) {d d' : ℕ} (hd' : 0 < d') :
    ((x * d' : ℤ) : ℝ) / ((d * d' : ℕ) : ℝ) = (x : ℝ) / d := by
  push_cast
  exact mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr hd'.ne')

theorem cast_mul_div_right (x : ℤ) {d d' : ℕ} (hd : 0 < d) :
    ((x * d : ℤ) : ℝ) / ((d * d' : ℕ) : ℝ) = (x : ℝ) / d' := by
  push_cast
  rw [mul_comm (d : ℝ)]
  exact mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr hd.ne')

theorem mem_sliceRegion {vb b : Box} (hvb : 0 < vb.den) (hb : 0 < b.den) {y : Fin 5 → ℝ}
    (hy : vb.Mem 5 y) {z : Fin 3 → ℝ} (hz : b.Mem 3 z) :
    (sliceRegion vb b).Mem 4 ![y 0, y 1, z 1, z 2] := by
  intro i
  fin_cases i
  · change ((vb.lo.getD 0 0 * b.den : ℤ) : ℝ) / ((vb.den * b.den : ℕ) : ℝ) ≤ y 0 ∧
      y 0 ≤ ((vb.hi.getD 0 0 * b.den : ℤ) : ℝ) / ((vb.den * b.den : ℕ) : ℝ)
    rw [cast_mul_div_left _ hb, cast_mul_div_left _ hb]
    exact hy 0
  · change ((vb.lo.getD 1 0 * b.den : ℤ) : ℝ) / ((vb.den * b.den : ℕ) : ℝ) ≤ y 1 ∧
      y 1 ≤ ((vb.hi.getD 1 0 * b.den : ℤ) : ℝ) / ((vb.den * b.den : ℕ) : ℝ)
    rw [cast_mul_div_left _ hb, cast_mul_div_left _ hb]
    exact hy 1
  · change ((b.lo.getD 1 0 * vb.den : ℤ) : ℝ) / ((vb.den * b.den : ℕ) : ℝ) ≤ z 1 ∧
      z 1 ≤ ((b.hi.getD 1 0 * vb.den : ℤ) : ℝ) / ((vb.den * b.den : ℕ) : ℝ)
    rw [cast_mul_div_right _ hvb, cast_mul_div_right _ hvb]
    exact hz 1
  · change ((b.lo.getD 2 0 * vb.den : ℤ) : ℝ) / ((vb.den * b.den : ℕ) : ℝ) ≤ z 2 ∧
      z 2 ≤ ((b.hi.getD 2 0 * vb.den : ℤ) : ℝ) / ((vb.den * b.den : ℕ) : ℝ)
    rw [cast_mul_div_right _ hvb, cast_mul_div_right _ hvb]
    exact hz 2

theorem mem_pieceRegion {vb b : Box} (hvb : 0 < vb.den) (hb : 0 < b.den) {y : Fin 5 → ℝ}
    (hy : vb.Mem 5 y) {z : Fin 3 → ℝ} (hz : b.Mem 3 z) :
    (pieceRegion vb b).Mem 5 ![y 0, y 1, z 0, z 1, z 2] := by
  intro i
  fin_cases i
  · change ((vb.lo.getD 0 0 * b.den : ℤ) : ℝ) / ((vb.den * b.den : ℕ) : ℝ) ≤ y 0 ∧
      y 0 ≤ ((vb.hi.getD 0 0 * b.den : ℤ) : ℝ) / ((vb.den * b.den : ℕ) : ℝ)
    rw [cast_mul_div_left _ hb, cast_mul_div_left _ hb]
    exact hy 0
  · change ((vb.lo.getD 1 0 * b.den : ℤ) : ℝ) / ((vb.den * b.den : ℕ) : ℝ) ≤ y 1 ∧
      y 1 ≤ ((vb.hi.getD 1 0 * b.den : ℤ) : ℝ) / ((vb.den * b.den : ℕ) : ℝ)
    rw [cast_mul_div_left _ hb, cast_mul_div_left _ hb]
    exact hy 1
  · change ((b.lo.getD 0 0 * vb.den : ℤ) : ℝ) / ((vb.den * b.den : ℕ) : ℝ) ≤ z 0 ∧
      z 0 ≤ ((b.hi.getD 0 0 * vb.den : ℤ) : ℝ) / ((vb.den * b.den : ℕ) : ℝ)
    rw [cast_mul_div_right _ hvb, cast_mul_div_right _ hvb]
    exact hz 0
  · change ((b.lo.getD 1 0 * vb.den : ℤ) : ℝ) / ((vb.den * b.den : ℕ) : ℝ) ≤ z 1 ∧
      z 1 ≤ ((b.hi.getD 1 0 * vb.den : ℤ) : ℝ) / ((vb.den * b.den : ℕ) : ℝ)
    rw [cast_mul_div_right _ hvb, cast_mul_div_right _ hvb]
    exact hz 1
  · change ((b.lo.getD 2 0 * vb.den : ℤ) : ℝ) / ((vb.den * b.den : ℕ) : ℝ) ≤ z 2 ∧
      z 2 ≤ ((b.hi.getD 2 0 * vb.den : ℤ) : ℝ) / ((vb.den * b.den : ℕ) : ℝ)
    rw [cast_mul_div_right _ hvb, cast_mul_div_right _ hvb]
    exact hz 2

/-! #### Signs of the witness on a piece -/

section Signs

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]
variable {pts : List (V3 κ)} {W : Wit κ} {t : List ℕ} {a : Fin 3} {F : PolarFrame κ}
  {pre : Option (Q4 κ)} {depth : ℕ} {vb b : Box}

theorem sliceGen_sound {l m : ℤ}
    (h : nonnegOn (sliceGen pts W t a F pre l m) 4 depth (sliceRegion vb b) = true)
    (hC : 0 < F.C) (hl : 0 < l) (hvb : 0 < vb.den) (hb : 0 < b.den) {y : Fin 5 → ℝ}
    (hy : vb.Mem 5 y) {z : Fin 3 → ℝ} (hz : b.Mem 3 z) :
    0 ≤ W.val pts t (viewDir a (y 0) (y 1)) (preQuat
      (chartQuat F.k F.centre + ((m : ℝ) / l) • dirQuat F.k (F.face (z 1) (z 2)))
      (Exact.rePre pre)) := by
  have hC' : (0 : ℝ) < F.C := by exact_mod_cast hC
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have h0 := nonnegOn_hom (sliceGen_isHomogeneous pts W t a F pre l m) (Nat.mul_pos hvb hb) h
    (mem_sliceRegion hvb hb hy hz)
  rw [sliceGen_homEnv, one_pow, one_mul, toFun_polarQ F hC'.ne'] at h0
  change 0 ≤ W.val pts t (viewDir a (y 0) (y 1)) (preQuat ((F.C : ℝ) • ((l : ℝ) •
    chartQuat F.k F.centre + (m : ℝ) • dirQuat F.k (F.face (z 1) (z 2)))) (Exact.rePre pre)) at h0
  have hq : (F.C : ℝ) • ((l : ℝ) • chartQuat F.k F.centre +
      (m : ℝ) • dirQuat F.k (F.face (z 1) (z 2))) = ((F.C : ℝ) * l) •
      (chartQuat F.k F.centre + ((m : ℝ) / l) • dirQuat F.k (F.face (z 1) (z 2))) := by
    funext i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    field_simp
  rw [hq, preQuat_smul, Wit.val_smul_quat] at h0
  exact nonneg_of_mul_nonneg_right h0 (pow_pos (mul_pos hC' hl') 2)

theorem derivGen_sound
    (h : nonnegOn (derivGen pts W t a F pre) 4 depth (sliceRegion vb b) = true)
    (hC : 0 < F.C) (hvb : 0 < vb.den) (hb : 0 < b.den) {y : Fin 5 → ℝ} (hy : vb.Mem 5 y)
    {z : Fin 3 → ℝ} (hz : b.Mem 3 z) :
    0 ≤ W.val pts t (viewDir a (y 0) (y 1))
        (preQuat (chartQuat F.k F.centre + dirQuat F.k (F.face (z 1) (z 2))) (Exact.rePre pre)) -
      W.val pts t (viewDir a (y 0) (y 1))
        (preQuat (dirQuat F.k (F.face (z 1) (z 2))) (Exact.rePre pre)) := by
  have hC' : (0 : ℝ) < F.C := by exact_mod_cast hC
  have h0 := nonnegOn_hom (derivGen_isHomogeneous pts W t a F pre) (Nat.mul_pos hvb hb) h
    (mem_sliceRegion hvb hb hy hz)
  change 0 ≤ (sliceGen pts W t a F pre 1 1).run Exact.re _ -
    (sliceGen pts W t a F pre 0 1).run Exact.re _ at h0
  simp only [sliceGen_homEnv, one_pow, one_mul, toFun_polarQ F hC'.ne', Int.cast_one,
    Int.cast_zero, one_smul, zero_smul, zero_add, preQuat_smul, Wit.val_smul_quat] at h0
  change 0 ≤ (F.C : ℝ) ^ 2 * W.val pts t (viewDir a (y 0) (y 1))
      (preQuat (chartQuat F.k F.centre + dirQuat F.k (F.face (z 1) (z 2))) (Exact.rePre pre)) -
    (F.C : ℝ) ^ 2 * W.val pts t (viewDir a (y 0) (y 1))
      (preQuat (dirQuat F.k (F.face (z 1) (z 2))) (Exact.rePre pre)) at h0
  rw [← mul_sub] at h0
  exact nonneg_of_mul_nonneg_right h0 (pow_pos hC' 2)

theorem fullGen_sound
    (h : nonnegOn (fullGen pts W t a F pre) 5 depth (pieceRegion vb b) = true)
    (hC : 0 < F.C) (hvb : 0 < vb.den) (hb : 0 < b.den) {y : Fin 5 → ℝ} (hy : vb.Mem 5 y)
    {z : Fin 3 → ℝ} (hz : b.Mem 3 z) :
    0 ≤ W.val pts t (viewDir a (y 0) (y 1))
      (preQuat (chartQuat F.k F.centre + z 0 • dirQuat F.k (F.face (z 1) (z 2)))
        (Exact.rePre pre)) := by
  have hC' : (0 : ℝ) < F.C := by exact_mod_cast hC
  have h0 := nonnegOn_hom (fullGen_isHomogeneous pts W t a F pre) (Nat.mul_pos hvb hb) h
    (mem_pieceRegion hvb hb hy hz)
  rw [fullGen_homEnv, one_pow, one_mul, toFun_polarQ F hC'.ne', one_smul, preQuat_smul,
    Wit.val_smul_quat] at h0
  exact nonneg_of_mul_nonneg_right h0 (pow_pos hC' 2)

theorem sliceGenAt_sound {U : V3 κ} {l m : ℤ}
    (h : nonnegOn (sliceGenAt pts W t F pre U l m) 2 depth (b.drop 1) = true)
    (hC : 0 < F.C) (hl : 0 < l) (hb : 0 < b.den) {z : Fin 3 → ℝ} (hz : b.Mem 3 z) :
    0 ≤ W.val pts t (Exact.reV U) (preQuat
      (chartQuat F.k F.centre + ((m : ℝ) / l) • dirQuat F.k (F.face (z 1) (z 2)))
      (Exact.rePre pre)) := by
  have hC' : (0 : ℝ) < F.C := by exact_mod_cast hC
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have h0 := nonnegOn_hom (b := b.drop 1) (sliceGenAt_isHomogeneous pts W t F pre U l m) hb h
    (Box.mem_drop_one hz)
  rw [sliceGenAt_homEnv, one_pow, one_mul, toFun_polarQ F hC'.ne'] at h0
  change 0 ≤ W.val pts t (Exact.reV U) (preQuat ((F.C : ℝ) • ((l : ℝ) •
    chartQuat F.k F.centre + (m : ℝ) • dirQuat F.k (F.face (z 1) (z 2)))) (Exact.rePre pre)) at h0
  have hq : (F.C : ℝ) • ((l : ℝ) • chartQuat F.k F.centre +
      (m : ℝ) • dirQuat F.k (F.face (z 1) (z 2))) = ((F.C : ℝ) * l) •
      (chartQuat F.k F.centre + ((m : ℝ) / l) • dirQuat F.k (F.face (z 1) (z 2))) := by
    funext i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    field_simp
  rw [hq, preQuat_smul, Wit.val_smul_quat] at h0
  exact nonneg_of_mul_nonneg_right h0 (pow_pos (mul_pos hC' hl') 2)

theorem derivGenAt_sound {U : V3 κ}
    (h : nonnegOn (derivGenAt pts W t F pre U) 2 depth (b.drop 1) = true)
    (hC : 0 < F.C) (hb : 0 < b.den) {z : Fin 3 → ℝ} (hz : b.Mem 3 z) :
    0 ≤ W.val pts t (Exact.reV U)
        (preQuat (chartQuat F.k F.centre + dirQuat F.k (F.face (z 1) (z 2))) (Exact.rePre pre)) -
      W.val pts t (Exact.reV U)
        (preQuat (dirQuat F.k (F.face (z 1) (z 2))) (Exact.rePre pre)) := by
  have hC' : (0 : ℝ) < F.C := by exact_mod_cast hC
  have h0 := nonnegOn_hom (b := b.drop 1) (derivGenAt_isHomogeneous pts W t F pre U) hb h
    (Box.mem_drop_one hz)
  change 0 ≤ (sliceGenAt pts W t F pre U 1 1).run Exact.re _ -
    (sliceGenAt pts W t F pre U 0 1).run Exact.re _ at h0
  simp only [sliceGenAt_homEnv, one_pow, one_mul, toFun_polarQ F hC'.ne', Int.cast_one,
    Int.cast_zero, one_smul, zero_smul, zero_add, preQuat_smul, Wit.val_smul_quat] at h0
  change 0 ≤ (F.C : ℝ) ^ 2 * W.val pts t (Exact.reV U)
      (preQuat (chartQuat F.k F.centre + dirQuat F.k (F.face (z 1) (z 2))) (Exact.rePre pre)) -
    (F.C : ℝ) ^ 2 * W.val pts t (Exact.reV U)
      (preQuat (dirQuat F.k (F.face (z 1) (z 2))) (Exact.rePre pre)) at h0
  rw [← mul_sub] at h0
  exact nonneg_of_mul_nonneg_right h0 (pow_pos hC' 2)

theorem fullGenAt_sound {U : V3 κ}
    (h : nonnegOn (fullGenAt pts W t F pre U) 3 depth b = true)
    (hC : 0 < F.C) (hb : 0 < b.den) {z : Fin 3 → ℝ} (hz : b.Mem 3 z) :
    0 ≤ W.val pts t (Exact.reV U)
      (preQuat (chartQuat F.k F.centre + z 0 • dirQuat F.k (F.face (z 1) (z 2)))
        (Exact.rePre pre)) := by
  have hC' : (0 : ℝ) < F.C := by exact_mod_cast hC
  have h0 := nonnegOn_hom (fullGenAt_isHomogeneous pts W t F pre U) hb h hz
  rw [fullGenAt_homEnv, one_pow, one_mul, toFun_polarQ F hC'.ne', one_smul, preQuat_smul,
    Wit.val_smul_quat] at h0
  exact nonneg_of_mul_nonneg_right h0 (pow_pos hC' 2)

end Signs

/-- **An affine function along a ray.** If `N` is affine, nonnegative at `δ₀ ≥ 0` and (when
`δ₁ > 0`) at `δ₁`, then `δ N(δ) ≥ 0` on `[δ₀, δ₁]`. -/
theorem nonneg_of_affine {B C δ₀ δ₁ δ : ℝ} (h₀ : 0 ≤ δ₀) (hδ₀ : δ₀ ≤ δ) (hδ₁ : δ ≤ δ₁)
    (hlo : 0 ≤ B + C * δ₀) (hhi : 0 < δ₁ → 0 ≤ B + C * δ₁) : 0 ≤ δ * (B + C * δ) := by
  rcases eq_or_lt_of_le (h₀.trans hδ₀) with h | h
  · rw [← h, zero_mul]
  · have h₁ := hhi (h.trans_le hδ₁)
    have : 0 ≤ B + C * δ := by
      rcases le_total 0 C with hC | hC
      · nlinarith [mul_le_mul_of_nonneg_left hδ₀ hC]
      · nlinarith [mul_le_mul_of_nonpos_left hδ₁ hC]
    exact mul_nonneg h.le this

/-- **Quadratic witnesses that vanish at the centre.** If `g(q₀ + δ q₁)` is quadratic in `δ`
(`Wit.val_add_smul`) and vanishes at `0`, then `g ≥ 0` on `[δ₀, δ₁]` with `δ₀ ≥ 0` follows from:
the derivative `g(q₀ + q₁) - g(q₁) ≥ 0` at `0` if `δ₀ = 0`, or `g(q₀ + δ₀ q₁) ≥ 0` if `δ₀ > 0`;
and `g(q₀ + δ₁ q₁) ≥ 0` if `δ₁ > 0`. -/
theorem nonneg_of_vanishing {g : (Fin 4 → ℝ) → ℝ} {q₀ q₁ : Fin 4 → ℝ}
    (hquad : ∀ δ : ℝ, g (q₀ + δ • q₁) = g q₀ + δ * (g (q₀ + q₁) - g q₀ - g q₁) + δ ^ 2 * g q₁)
    (h0 : g q₀ = 0) {δ₀ δ₁ δ : ℝ} (hδ₀ : 0 ≤ δ₀) (hlo : δ₀ ≤ δ) (hhi : δ ≤ δ₁)
    (hstart : (δ₀ = 0 ∧ 0 ≤ g (q₀ + q₁) - g q₁) ∨ (0 < δ₀ ∧ 0 ≤ g (q₀ + δ₀ • q₁)))
    (hend : 0 < δ₁ → 0 ≤ g (q₀ + δ₁ • q₁)) :
    0 ≤ g (q₀ + δ • q₁) := by
  have hg (δ : ℝ) : g (q₀ + δ • q₁) = δ * ((g (q₀ + q₁) - g q₁) + g q₁ * δ) := by
    rw [hquad, h0]
    ring
  rw [hg]
  refine nonneg_of_affine hδ₀ hlo hhi ?_ fun h ↦ ?_
  · rcases hstart with ⟨rfl, h⟩ | ⟨hpos, h⟩
    · simpa using h
    · rw [hg] at h
      exact nonneg_of_mul_nonneg_right h hpos
  · have h' := hend h
    rw [hg] at h'
    exact nonneg_of_mul_nonneg_right h' h

/-! #### Pieces -/

section Pieces

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The support obstruction `c ⨯₃ (Q(q) v - |q|² a)` vanishes (a zero test of `κ`). -/
def obstZero (q : Q4 κ) (c v a : V3 κ) : Bool :=
  Exact.isZeroV (c.cross ((q.rotate v).sub (V3.smul q.norm2 a)))

/-- Every support obstruction of the witness `W` vanishes at the quaternion `q`
(`ZoomFrame::vanishes` in `zoom.rs`): for balanced supports, at every anchor of every support; for
width pairs and centred supports, at every anchor choice. -/
def vanishes (pts : List (V3 κ)) (q : Q4 κ) : Wit κ → Bool
  | .balanced w => allFin3 fun i ↦ (w.sup i).anchors.all fun j ↦
      obstZero q (w.dir pts i) (pt pts (w.sup i).plug) (pt pts j)
  | .width w => (Wit.width w).choices.all fun t ↦
      obstZero q w.c (w.plugDiff pts) ((pt pts (t.getD 0 0)).sub (pt pts (t.getD 1 0)))
  | .centred w => (Wit.centred w).choices.all fun t ↦
      obstZero q w.c (w.toWidth.plugDiff pts) ((pt pts (t.getD 0 0)).sub (pt pts (t.getD 1 0)))

theorem supportPoly_eq_zero {q : Q4 κ} {c v a : V3 κ} (h : obstZero q c v a = true)
    {C : ℝ} (hC : C ≠ 0) {q₀ : Fin 4 → ℝ} (hq : (q.map Exact.re).toFun = C • q₀)
    (u : Fin 3 → ℝ) : supportPoly u q₀ (Exact.reV c) (Exact.reV v) (Exact.reV a) = 0 := by
  have h0 := Exact.reV_eq_zero_of_isZeroV h
  rw [Exact.reV_cross, Exact.reV_sub, Exact.reV_smul, Exact.reV_rotate, Exact.re_norm2, hq] at h0
  have h1 : supportPoly u (C • q₀) (Exact.reV c) (Exact.reV v) (Exact.reV a) = 0 := by
    rw [supportPoly, h0, dotProduct_zero]
  rw [supportPoly_smul_quat] at h1
  exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero 2 hC)

omit [Add κ] [Sub κ] [Mul κ] [Exact κ] in
theorem mem_choices_balanced {w : Balanced} {t : List ℕ} (ht : t ∈ (Wit.balanced w : Wit κ).choices)
    (i : Fin 3) : t.getD i 0 ∈ (w.sup i).anchors := by
  simp only [Wit.choices, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨i₀, h₀, i₁, h₁, i₂, h₂, rfl⟩ := ht
  fin_cases i
  · exact h₀
  · exact h₁
  · exact h₂

theorem vanishes_sound {pts : List (V3 κ)} {q : Q4 κ} {W : Wit κ} (h : vanishes pts q W = true)
    {C : ℝ} (hC : C ≠ 0) {q₀ : Fin 4 → ℝ} (hq : (q.map Exact.re).toFun = C • q₀) {t : List ℕ}
    (ht : t ∈ W.choices) (u : Fin 3 → ℝ) : W.val pts t u q₀ = 0 := by
  cases W with
  | balanced w =>
    simp only [vanishes, allFin3_eq_true, List.all_eq_true] at h
    have hs (i : Fin 3) := supportPoly_eq_zero (h i _ (mem_choices_balanced ht i)) hC hq u
    simp only [Wit.val, balancedPoly, hs, mul_zero, Finset.sum_const_zero]
  | width w => exact supportPoly_eq_zero (List.all_eq_true.mp h t ht) hC hq u
  | centred w => exact supportPoly_eq_zero (List.all_eq_true.mp h t ht) hC hq u

end Pieces

section Leaves

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The checks of the witness polynomial of the anchor choice `t` of `W`, linear in the view, at
the view `U` on a piece `b` (coordinates `δ, y₁, y₂`) of a face, with the pre-rotation `pre`, if
any; `van` says whether the witness vanishes at the centre. -/
def pieceCornerOk (pts : List (V3 κ)) (W : Wit κ) (t : List ℕ) (U : V3 κ) (F : PolarFrame κ)
    (pre : Option (Q4 κ)) (van : Bool) (depth : ℕ) (b : Box) : Bool :=
  if van then
    (if b.lo.getD 0 0 = 0 then nonnegOn (derivGenAt pts W t F pre U) 2 depth (b.drop 1)
      else nonnegOn (sliceGenAt pts W t F pre U b.den (b.lo.getD 0 0)) 2 depth (b.drop 1)) &&
    (if 0 < b.hi.getD 0 0 then
      nonnegOn (sliceGenAt pts W t F pre U b.den (b.hi.getD 0 0)) 2 depth (b.drop 1)
      else true)
  else nonnegOn (fullGenAt pts W t F pre U) 3 depth b

theorem pieceCornerOk_sound {pts : List (V3 κ)} {W : Wit κ} {t : List ℕ} {U : V3 κ}
    {F : PolarFrame κ} {pre : Option (Q4 κ)} {van : Bool} {depth : ℕ} {b : Box}
    (h : pieceCornerOk pts W t U F pre van depth b = true)
    (hC : 0 < F.C) (hb : 0 < b.den) (hlo : 0 ≤ b.lo.getD 0 0)
    (hvan : van = true →
      ∀ u, W.val pts t u (preQuat (chartQuat F.k F.centre) (Exact.rePre pre)) = 0)
    {z : Fin 3 → ℝ} (hz : b.Mem 3 z) :
    0 ≤ W.val pts t (Exact.reV U)
      (preQuat (chartQuat F.k (F.centre + z 0 • F.face (z 1) (z 2))) (Exact.rePre pre)) := by
  rw [chartQuat_add_smul]
  unfold pieceCornerOk at h
  cases van
  · exact fullGenAt_sound h hC hb hz
  · simp only [↓reduceIte, Bool.and_eq_true] at h
    obtain ⟨h₀, h₁⟩ := h
    have hd : (0 : ℝ) < b.den := by exact_mod_cast hb
    have hbz : (0 : ℤ) < b.den := by exact_mod_cast hb
    rw [preQuat_add, preQuat_smul]
    refine nonneg_of_vanishing (W.val_add_smul pts t _ _ _) (hvan rfl _)
      (δ₀ := (b.lo.getD 0 0 : ℝ) / b.den)
      (δ₁ := (b.hi.getD 0 0 : ℝ) / b.den) (div_nonneg (by exact_mod_cast hlo) hd.le) (hz 0).1
      (hz 0).2 ?_ ?_
    · split_ifs at h₀ with h0
      · have hs := derivGenAt_sound h₀ hC hb hz
        rw [preQuat_add] at hs
        exact Or.inl ⟨by rw [h0]; simp, hs⟩
      · refine Or.inr ⟨div_pos (by exact_mod_cast lt_of_le_of_ne hlo (Ne.symm h0)) hd, ?_⟩
        have hs := sliceGenAt_sound h₀ hC hbz hb hz
        rwa [Int.cast_natCast, preQuat_add, preQuat_smul] at hs
    · intro hpos
      split_ifs at h₁ with h1
      · have hs := sliceGenAt_sound h₁ hC hbz hb hz
        rwa [Int.cast_natCast, preQuat_add, preQuat_smul] at hs
      · have : (b.hi.getD 0 0 : ℝ) / b.den ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast not_lt.mp h1) hd.le
        linarith

/-- The checks of the witness polynomial of the anchor choice `t` of `W` on a piece `b`
(coordinates `δ, y₁, y₂`) of a face, with the view box of `vb` and the pre-rotation `pre`, if any;
`van` says whether the witness vanishes at the centre. A witness linear in the view is checked at
each corner of the view box (`pieceCornerOk`), any other on the whole view box. -/
def pieceTripleOk (pts : List (V3 κ)) (W : Wit κ) (t : List ℕ) (a : Fin 3) (F : PolarFrame κ)
    (pre : Option (Q4 κ)) (van : Bool) (depth : ℕ) (vb b : Box) : Bool :=
  if W.linear then (viewCorners a vb).all fun U ↦ pieceCornerOk pts W t U F pre van depth b
  else if van then
    (if b.lo.getD 0 0 = 0 then nonnegOn (derivGen pts W t a F pre) 4 depth (sliceRegion vb b)
      else nonnegOn (sliceGen pts W t a F pre b.den (b.lo.getD 0 0)) 4 depth
        (sliceRegion vb b)) &&
    (if 0 < b.hi.getD 0 0 then
      nonnegOn (sliceGen pts W t a F pre b.den (b.hi.getD 0 0)) 4 depth (sliceRegion vb b)
      else true)
  else nonnegOn (fullGen pts W t a F pre) 5 depth (pieceRegion vb b)

theorem pieceTripleOk_sound {pts : List (V3 κ)} {W : Wit κ} {t : List ℕ} {a : Fin 3}
    {F : PolarFrame κ} {pre : Option (Q4 κ)} {van : Bool} {depth : ℕ} {vb b : Box}
    (h : pieceTripleOk pts W t a F pre van depth vb b = true)
    (hC : 0 < F.C) (hvb : 0 < vb.den) (hb : 0 < b.den) (hlo : 0 ≤ b.lo.getD 0 0)
    (hvan : van = true →
      ∀ u, W.val pts t u (preQuat (chartQuat F.k F.centre) (Exact.rePre pre)) = 0)
    {y : Fin 5 → ℝ} (hy : vb.Mem 5 y) {z : Fin 3 → ℝ} (hz : b.Mem 3 z) :
    0 ≤ W.val pts t (viewDir a (y 0) (y 1))
      (preQuat (chartQuat F.k (F.centre + z 0 • F.face (z 1) (z 2))) (Exact.rePre pre)) := by
  unfold pieceTripleOk at h
  by_cases hlin : W.linear = true
  · -- the witness is the view dotted with `G`; a corner `U` of the view box bounds it
    rw [ite_eq_left hlin] at h
    obtain ⟨G, hG⟩ := W.exists_dot_of_linear pts hlin t
      (preQuat (chartQuat F.k (F.centre + z 0 • F.face (z 1) (z 2))) (Exact.rePre pre))
    obtain ⟨U, hU, hle⟩ := exists_viewCorner_le (κ := κ) G a hvb hy
    have h0 := pieceCornerOk_sound (List.all_eq_true.mp h U hU) hC hb hlo hvan hz
    rw [hG, dotProduct_comm] at h0
    rw [hG, dotProduct_comm]
    have hd : (0 : ℝ) < vb.den := by exact_mod_cast hvb
    exact nonneg_of_mul_nonneg_right (h0.trans hle) hd
  rw [ite_eq_right hlin] at h
  rw [chartQuat_add_smul]
  cases van
  · exact fullGen_sound h hC hvb hb hy hz
  · simp only [↓reduceIte, Bool.and_eq_true] at h
    obtain ⟨h₀, h₁⟩ := h
    have hd : (0 : ℝ) < b.den := by exact_mod_cast hb
    have hbz : (0 : ℤ) < b.den := by exact_mod_cast hb
    rw [preQuat_add, preQuat_smul]
    refine nonneg_of_vanishing (W.val_add_smul pts t _ _ _) (hvan rfl _)
      (δ₀ := (b.lo.getD 0 0 : ℝ) / b.den)
      (δ₁ := (b.hi.getD 0 0 : ℝ) / b.den) (div_nonneg (by exact_mod_cast hlo) hd.le) (hz 0).1
      (hz 0).2 ?_ ?_
    · split_ifs at h₀ with h0
      · have hs := derivGen_sound h₀ hC hvb hb hy hz
        rw [preQuat_add] at hs
        exact Or.inl ⟨by rw [h0]; simp, hs⟩
      · refine Or.inr ⟨div_pos (by exact_mod_cast lt_of_le_of_ne hlo (Ne.symm h0)) hd, ?_⟩
        have hs := sliceGen_sound h₀ hC hbz hvb hb hy hz
        rwa [Int.cast_natCast, preQuat_add, preQuat_smul] at hs
    · intro hpos
      split_ifs at h₁ with h1
      · have hs := sliceGen_sound h₁ hC hbz hvb hb hy hz
        rwa [Int.cast_natCast, preQuat_add, preQuat_smul] at hs
      · have : (b.hi.getD 0 0 : ℝ) / b.den ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast not_lt.mp h1) hd.le
        linarith

/-- The leaf check of a face tree: the witness `W` on the piece `b` (coordinates `δ, y₁, y₂`, with
`δ ≥ 0`) of the face of `F`, over the view box of `B` pre-rotated by `pre` if any, for every choice
of anchors. -/
def pieceOk (pts : List (V3 κ)) (B : ChartBox) (F : PolarFrame κ) (pre : Option (Q4 κ))
    (depth : ℕ) (b : Box) (W : Wit κ) : Bool :=
  decide (0 < B.box.den) && W.premisesOk pts (viewCorners B.view B.box) && decide (0 < b.den) &&
    decide (0 ≤ b.lo.getD 0 0) &&
    W.choices.all fun t ↦ pieceTripleOk pts W t B.view F pre
      (vanishes pts (preQ id F.centreQuat pre) W) depth B.box b

/-- **Soundness of the leaves of a face tree**: no fit at the poses of `B` whose rotation
coordinates are `x₀ + δ f` for a point `(δ, y₁, y₂)` of the piece, with the pre-rotation `pre`. -/
theorem pieceOk_sound {pts : List (V3 κ)} {B : ChartBox} {F : PolarFrame κ}
    {pre : Option (Q4 κ)}
    {depth : ℕ} {b : Box} {W : Wit κ} (h : pieceOk pts B F pre depth b W = true)
    (hpre : ∀ c ∈ Exact.rePre pre, c ≠ 0) (hk : F.k = B.rot) (hC : 0 < F.C)
    {z : Fin 3 → ℝ} (hz : b.Mem 3 z) {p : ChartPose} (hp : p ∈ B.poses)
    (hx : p.x = F.centre + z 0 • F.face (z 1) (z 2)) :
    ¬ (Polyhedron.ofPoints pts).FitsAlong (viewDir p.view p.s p.t)
      (p.rotation * preRot (Exact.rePre pre)) := by
  simp only [pieceOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hden, hprem⟩, hb⟩, hlo⟩, hall⟩ := h
  intro hfit
  rw [ChartPose.rotation, chartRotation, ← quatRotation_preQuat] at hfit
  obtain ⟨t, ht, hneg⟩ := Wit.exists_neg_val (preQuat_ne_zero (chartQuat_ne_zero _ _) hpre)
    (Wit.premises_of_ok hprem (Balanced.coneBound_of_mem_poses hden hp)) hfit
  have hq : ((preQ id F.centreQuat pre).map Exact.re).toFun =
      (F.C : ℝ) • preQuat (chartQuat F.k F.centre) (Exact.rePre pre) := by
    rw [map_preQ Exact.isArith, Function.comp_id, toFun_preQ, ← preQuat_smul,
      ← toFun_centreQuat F (by exact_mod_cast hC.ne')]
  obtain ⟨hview, hrot, hy⟩ := hp
  have h0 := pieceTripleOk_sound (hall t ht) hC hden hb hlo
    (fun hv u ↦ vanishes_sound hv (by exact_mod_cast hC.ne') hq ht u) hy hz
  rw [hrot, ← hk, hx, hview] at hneg
  exact absurd hneg (not_lt.mpr h0)

end Leaves

/-! #### The faces of a chart box -/

section Faces

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The centre, `centre / den`. -/
noncomputable def x₀ (z : Polar κ) (j : Fin 3) : ℝ :=
  Exact.re (z.centre.get j) / z.den

/-- The bound of rotation coordinate `axis` of the chart box `B` on the face `upper` (upper or
lower), over `B.box.den`. -/
def bound (B : ChartBox) (axis : Fin 3) (upper : Bool) : ℤ :=
  (bif upper then B.box.hi else B.box.lo).getD (2 + axis.val) 0

/-- The frame of the face `(axis, upper)` on the chart box `B`, over the common denominator
`den · B.box.den`. -/
def frame (z : Polar κ) (B : ChartBox) (axis : Fin 3) (upper : Bool) : PolarFrame κ where
  k := B.rot
  axis := axis
  C := z.den * B.box.den
  A := V3.smul (Exact.ofInt B.box.den) z.centre
  E := Exact.ofInt (z.den * bound B axis upper) - Exact.ofInt B.box.den * z.centre.get axis

/-- `B.box.den` times coordinate `j` of the centre, minus `den` times `L`: positive when the
centre lies beyond `L / B.box.den`. -/
def beyond (z : Polar κ) (B : ChartBox) (j : Fin 3) (L : ℤ) : κ :=
  Exact.ofInt B.box.den * z.centre.get j - Exact.ofInt (z.den * L)

/-- The centre lies in the rotation box of `B`. -/
def centreIn (z : Polar κ) (B : ChartBox) : Bool :=
  allFin3 fun j ↦ Exact.nonneg (z.beyond B j (B.box.lo.getD (2 + j.val) 0)) &&
    Exact.nonneg (Exact.ofInt 0 - z.beyond B j (B.box.hi.getD (2 + j.val) 0))

/-- The face `(j, upper)` of the rotation box of `B` contains the centre, so its cone is empty:
an exact sign test. -/
def notRequired (z : Polar κ) (B : ChartBox) (j : Fin 3) (upper : Bool) : Bool :=
  bif upper then Exact.nonneg (z.beyond B j (bound B j true))
  else Exact.nonneg (Exact.ofInt 0 - z.beyond B j (bound B j false))

end Faces

/-- The box of the pieces `(δ, y₁, y₂)` of the faces along `axis`: `δ ∈ [0, 1]`, and the free
coordinates of the face point, in the rotation box of `B`. -/
def faceBox (B : ChartBox) (axis : Fin 3) : Box where
  lo := [0, B.box.lo.getD (2 + (freeAxes axis).1.val) 0,
    B.box.lo.getD (2 + (freeAxes axis).2.val) 0]
  hi := [B.box.den, B.box.hi.getD (2 + (freeAxes axis).1.val) 0,
    B.box.hi.getD (2 + (freeAxes axis).2.val) 0]
  den := B.box.den

/-- The evidence has a tree for the face `(j, upper)`. -/
def hasFace {κ : Type} (z : Polar κ) (j : Fin 3) (upper : Bool) : Bool :=
  z.faces.any fun f ↦ f.axis == j && f.upper == upper

/-- The check of polar zoom evidence on the chart box `B`, pre-rotated by `pre` if any: the centre
lies in the rotation box, every face has a tree or contains the centre (and there is a face), and
every tree checks. -/
def check {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] (pts : List (V3 κ)) (B : ChartBox)
    (depth : ℕ) (z : Polar κ) (pre : Option (Q4 κ) := none) : Bool :=
  decide (0 < z.den) && decide (0 < B.box.den) && Exact.preOk pre && z.centreIn B &&
    !z.faces.isEmpty &&
    allFin3 (fun j ↦ (z.hasFace j false || z.notRequired B j false) &&
      (z.hasFace j true || z.notRequired B j true)) &&
    z.faces.all fun f ↦ f.tree.checkWith (Box.halving 3)
      (pieceOk pts B (z.frame B f.axis f.upper) pre depth) (faceBox B f.axis)

/-! #### Soundness -/

/-- The lower end of rotation coordinate `j` of a chart box. -/
noncomputable def rotLo (B : ChartBox) (j : Fin 3) : ℝ :=
  (B.box.lo.getD (2 + j.val) 0 : ℝ) / B.box.den

/-- The upper end of rotation coordinate `j` of a chart box. -/
noncomputable def rotHi (B : ChartBox) (j : Fin 3) : ℝ :=
  (B.box.hi.getD (2 + j.val) 0 : ℝ) / B.box.den

theorem rot_mem {B : ChartBox} {p : ChartPose} (hp : p ∈ B.poses) (j : Fin 3) :
    rotLo B j ≤ p.x j ∧ p.x j ≤ rotHi B j := by
  have hy := hp.2.2
  fin_cases j
  · exact hy 2
  · exact hy 3
  · exact hy 4

section Sound

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] {z : Polar κ} {B : ChartBox}

theorem frame_C_pos (hz : 0 < z.den) (hb : 0 < B.box.den) (axis : Fin 3) (upper : Bool) :
    0 < (z.frame B axis upper).C := by
  change (0 : ℤ) < z.den * B.box.den
  exact_mod_cast Nat.mul_pos hz hb

theorem frame_centre (hz : 0 < z.den) (hb : 0 < B.box.den) (axis : Fin 3) (upper : Bool) :
    (z.frame B axis upper).centre = z.x₀ := by
  have hz' : (z.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  have hb' : (B.box.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  funext j
  have h : Exact.reV z.centre j = Exact.re (z.centre.get j) := by
    rw [Exact.reV, ← V3.get_eq_toFun]
    fin_cases j <;> rfl
  simp only [PolarFrame.centre, frame, Exact.reV_smul, Exact.re_ofInt, Pi.smul_apply,
    smul_eq_mul, x₀, h]
  push_cast
  field_simp

theorem frame_face (hz : 0 < z.den) (hb : 0 < B.box.den) (axis : Fin 3) (upper : Bool)
    (y₁ y₂ : ℝ) : (z.frame B axis upper).face y₁ y₂ = (placeAxis axis
      ((bif upper then rotHi B axis else rotLo B axis) - z.x₀ axis)
      (y₁ - z.x₀ (freeAxes axis).1) (y₂ - z.x₀ (freeAxes axis).2)).toFun := by
  have hz' : (z.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  have hb' : (B.box.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  have hE : Exact.re (z.frame B axis upper).E / (z.frame B axis upper).C =
      (bif upper then rotHi B axis else rotLo B axis) - z.x₀ axis := by
    cases upper <;>
      simp only [frame, bound, rotLo, rotHi, x₀, Bool.cond_true, Bool.cond_false, Exact.re_sub,
        Exact.re_mul, Exact.re_ofInt] <;> push_cast <;> field_simp
  rw [PolarFrame.face, hE, frame_centre hz hb]
  rfl

theorem mem_faceBox (hb : 0 < B.box.den) {axis : Fin 3} {δ y₁ y₂ : ℝ} (hδ : 0 ≤ δ ∧ δ ≤ 1)
    (h₁ : rotLo B (freeAxes axis).1 ≤ y₁ ∧ y₁ ≤ rotHi B (freeAxes axis).1)
    (h₂ : rotLo B (freeAxes axis).2 ≤ y₂ ∧ y₂ ≤ rotHi B (freeAxes axis).2) :
    (faceBox B axis).Mem 3 ![δ, y₁, y₂] := by
  have hb' : (B.box.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  intro i
  fin_cases i
  · change ((0 : ℤ) : ℝ) / (B.box.den : ℝ) ≤ δ ∧ δ ≤ ((B.box.den : ℤ) : ℝ) / (B.box.den : ℝ)
    rw [Int.cast_zero, zero_div, Int.cast_natCast, div_self hb']
    exact hδ
  · exact h₁
  · exact h₂

theorem re_beyond (hz : 0 < z.den) (hb : 0 < B.box.den) (j : Fin 3) (L : ℤ) :
    Exact.re (z.beyond B j L) = (z.den * B.box.den : ℝ) * (z.x₀ j - L / B.box.den) := by
  have hz' : (z.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  have hb' : (B.box.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  simp only [beyond, x₀, Exact.re_sub, Exact.re_mul, Exact.re_ofInt]
  push_cast
  field_simp

theorem centreIn_sound (hz : 0 < z.den) (hb : 0 < B.box.den) (h : z.centreIn B = true)
    (j : Fin 3) : rotLo B j ≤ z.x₀ j ∧ z.x₀ j ≤ rotHi B j := by
  have hpos : (0 : ℝ) < z.den * B.box.den := by positivity
  have hj := allFin3_eq_true.mp h j
  simp only [Bool.and_eq_true] at hj
  have h₁ := Exact.nonneg_sound _ hj.1
  have h₂ := Exact.nonneg_sound _ hj.2
  rw [re_beyond hz hb] at h₁
  rw [Exact.re_sub, Exact.re_ofInt, re_beyond hz hb] at h₂
  simp only [rotLo, rotHi]
  constructor
  · nlinarith
  · nlinarith

theorem notRequired_sound (hz : 0 < z.den) (hb : 0 < B.box.den) {j : Fin 3} {upper : Bool}
    (h : z.notRequired B j upper = true) :
    bif upper then rotHi B j ≤ z.x₀ j else z.x₀ j ≤ rotLo B j := by
  have hpos : (0 : ℝ) < z.den * B.box.den := by positivity
  cases upper
  · have h₁ := Exact.nonneg_sound _ h
    rw [Exact.re_sub, Exact.re_ofInt, re_beyond hz hb] at h₁
    simp only [bound, Bool.cond_false, Int.cast_zero, zero_sub] at h₁
    simp only [rotLo, Bool.cond_false]
    nlinarith
  · have h₁ := Exact.nonneg_sound _ h
    rw [re_beyond hz hb] at h₁
    simp only [bound, Bool.cond_true] at h₁
    simp only [rotHi, Bool.cond_true]
    nlinarith

omit [Add κ] [Sub κ] [Mul κ] [Exact κ] in
theorem hasFace_sound {j : Fin 3} {upper : Bool} (h : z.hasFace j upper = true) :
    ∃ f ∈ z.faces, f.axis = j ∧ f.upper = upper := by
  simpa [hasFace] using h

end Sound

/-- **Soundness of polar zooms**, on a box pre-rotated by `pre`. -/
theorem check_sound_pre {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] {pts : List (V3 κ)}
    {B : ChartBox} {depth : ℕ} {z : Polar κ} {pre : Option (Q4 κ)}
    (h : z.check pts B depth pre = true) :
    (Polyhedron.ofPoints pts).NoFitRot B.poses (preRot (Exact.rePre pre)) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hz, hb⟩, hpre⟩, hcin⟩, hne⟩, hreq⟩, hfaces⟩ := h
  -- Each face tree covers the poses of its cone.
  have hface : ∀ f ∈ z.faces, ∀ x : Fin 3 → ℝ, (faceBox B f.axis).Mem 3 x → ∀ p ∈ B.poses,
      p.x = (z.frame B f.axis f.upper).centre +
        x 0 • (z.frame B f.axis f.upper).face (x 1) (x 2) →
      ¬ (Polyhedron.ofPoints pts).FitsAlong (viewDir p.view p.s p.t)
        (p.rotation * preRot (Exact.rePre pre)) := fun f hf ↦
    Cover.checkWith_sound (H := Box.halving 3)
      (Q := fun x ↦ ∀ p ∈ B.poses, p.x = (z.frame B f.axis f.upper).centre +
        x 0 • (z.frame B f.axis f.upper).face (x 1) (x 2) →
        ¬ (Polyhedron.ofPoints pts).FitsAlong (viewDir p.view p.s p.t)
          (p.rotation * preRot (Exact.rePre pre)))
      (fun _ _ _ he _ hx _ hp hpx ↦
        pieceOk_sound he (Exact.rePre_ne_zero hpre) rfl (frame_C_pos hz hb _ _) hx hp hpx)
      (List.all_eq_true.mp hfaces f hf)
  intro p hp
  have h₀ := centreIn_sound hz hb hcin
  by_cases hc : p.x = z.x₀
  · -- The centre: any face, at `δ = 0`.
    obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil z.faces (by simpa using hne)
    refine hface f hf ![0, z.x₀ (freeAxes f.axis).1, z.x₀ (freeAxes f.axis).2]
      (mem_faceBox hb ⟨le_rfl, zero_le_one⟩ (h₀ _) (h₀ _)) p hp ?_
    simp [frame_centre hz hb, hc]
  · obtain ⟨j, upper, δ, fv, hδ, hδ1, hreqj, hfj, hfb, hxeq⟩ :=
      exists_polar h₀ (rot_mem hp) hc
    -- The face `(j, upper)` does not contain the centre, so it has a tree.
    have hjf : z.hasFace j upper = true := by
      have h1 := allFin3_eq_true.mp hreq j
      simp only [Bool.and_eq_true, Bool.or_eq_true] at h1
      cases upper
      · exact h1.1.resolve_right fun hn ↦
          absurd (notRequired_sound hz hb hn) (not_le.mpr hreqj)
      · exact h1.2.resolve_right fun hn ↦
          absurd (notRequired_sound hz hb hn) (not_le.mpr hreqj)
    obtain ⟨f, hf, rfl, rfl⟩ := hasFace_sound hjf
    have hP (i : Fin 3) : rotLo B i ≤ z.x₀ i + fv i ∧ z.x₀ i + fv i ≤ rotHi B i := by
      constructor <;> linarith [(hfb i).1, (hfb i).2]
    refine hface f hf ![δ, z.x₀ (freeAxes f.axis).1 + fv (freeAxes f.axis).1,
      z.x₀ (freeAxes f.axis).2 + fv (freeAxes f.axis).2]
      (mem_faceBox hb ⟨hδ.le, hδ1⟩ (hP _) (hP _)) p hp ?_
    change p.x = (z.frame B f.axis f.upper).centre +
      δ • (z.frame B f.axis f.upper).face (z.x₀ (freeAxes f.axis).1 + fv (freeAxes f.axis).1)
        (z.x₀ (freeAxes f.axis).2 + fv (freeAxes f.axis).2)
    rw [frame_centre hz hb, frame_face hz hb, add_sub_cancel_left, add_sub_cancel_left, ← hfj,
      toFun_placeAxis_self]
    exact hxeq

/-- **Soundness of polar zooms.** -/
theorem check_sound {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] {pts : List (V3 κ)}
    {B : ChartBox} {depth : ℕ} {z : Polar κ}
    (h : z.check pts B depth = true) : (Polyhedron.ofPoints pts).NoFit B.poses := by
  have h0 := check_sound_pre h
  rwa [Exact.rePre_none, preRot_none, Polyhedron.noFitRot_one] at h0

end Polar

end Nieuwland.Check
