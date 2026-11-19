import Modules.Root.Slack
import Modules.Rupert.Quat

/-!
# Pose maps

A *pose map* sends the contacts of one chart pose to the contacts of another with the same scale:
an isometry `A ↦ T A + b` on the hole side, an isometry `P ↦ G P + c` on the plug side, and the
induced changes of the view chart, the rotation chart and the translation. It multiplies the real
slack `slackR` of every contact by one nonzero factor (`PoseMap.slackR_map`,
`PoseMap.factor_ne_zero`), and it has an inverse (`PoseMap.inv`, `PoseMap.inv_hole`,
`PoseMap.inv_plug`, `PoseMap.inv_s'`, `PoseMap.inv_t'`, `PoseMap.inv_x'`, `PoseMap.inv_y'`).

* **Isometries.** `T = sT • Q(τ) / |τ|²` and `G = sG • Q(γ) / |γ|²` with `sT, sG = ±1` are
  orthogonal (`PoseMap.T_transpose_mul`, ...).
* **Views.** `T` sends the view direction `u = viewDir a s t` to a multiple of
  `wv = Q(τ) u`; where `wv a' ≠ 0` that is the view direction of chart `a'` at `(s', t')`, so
  `screen a' s' t' (T v) = L (screen a s t v)` for one `2 × 2` matrix `L` (`PoseMap.screen_T`).
* **Rotations.** The new quaternion `qq = τ q γ̄` (times `(0, wv)` when the determinants of `T` and
  `G` differ, `e`) has the rotation `R'` with `R' G = S T R`, `S` the identity or the reflection
  along `wv`; the screen map of the new view does not see `S` (`PoseMap.screen_rot`).
* **Slacks.** Hence the new plug point is `L (l M (R Q) + y) + M' b`, the new hole points are
  `L (M A) + M' b`, and orientations scale by `det L` (`orient_mulVec_add`).

The quaternion product and conjugate are `qmul` and `qconj` of `Nieuwland.Rupert.Quat`.
-/

open Matrix

namespace Nieuwland.Root

/-! ### Quaternions -/

section CommRing

variable {R : Type*} [CommRing R]

/-- `Q(q̄) = Q(q)ᵀ`. -/
theorem quatMatrix_qconj (q : Fin 4 → R) : quatMatrix (qconj q) = (quatMatrix q)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quatMatrix, qconj] <;> ring

/-- `Q(q)ᵀ Q(q) = |q|⁴ 1`. -/
theorem quatMatrix_transpose_mul (q : Fin 4 → R) :
    (quatMatrix q)ᵀ * quatMatrix q = ((q ⬝ᵥ q) ^ 2) • (1 : Matrix (Fin 3) (Fin 3) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatMatrix, mul_apply, Fin.sum_univ_succ, dotProduct, one_apply] <;> ring

/-- The matrix of a pure quaternion: `Q((0, w)) = 2 w wᵀ - |w|² 1`, `|w|²` times the rotation by
a half turn about `w`. -/
theorem quatMatrix_pureQ (w : Fin 3 → R) :
    quatMatrix (pureQ w) = (2 : R) • vecMulVec w w - (w ⬝ᵥ w) • (1 : Matrix (Fin 3) (Fin 3) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatMatrix, pureQ, vecMulVec, dotProduct, Fin.sum_univ_three, one_apply] <;> ring

/-- `Q((0, w)) v = 2 (w ⬝ v) w - |w|² v`. -/
theorem quatMatrix_pureQ_mulVec (w v : Fin 3 → R) :
    quatMatrix (pureQ w) *ᵥ v = (2 * (w ⬝ᵥ v)) • w - (w ⬝ᵥ w) • v := by
  ext i
  fin_cases i <;> simp [quatMatrix, pureQ, mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- The conjugate is an involution. -/
theorem qconj_qconj (q : Fin 4 → R) : qconj (qconj q) = q := by
  funext i
  fin_cases i <;> simp [qconj]

/-- `|q̄|² = |q|²`. -/
theorem qconj_dot_self (q : Fin 4 → R) : qconj q ⬝ᵥ qconj q = q ⬝ᵥ q := by
  simp [qconj, dotProduct, Fin.sum_univ_four]

/-- `|(0, w)|² = |w|²`. -/
theorem pureQ_dot_self (w : Fin 3 → R) : pureQ w ⬝ᵥ pureQ w = w ⬝ᵥ w := by
  simp [pureQ, dotProduct, Fin.sum_univ_four, Fin.sum_univ_three]

/-- The Hamilton product is associative. -/
theorem qmul_assoc (p q r : Fin 4 → R) : qmul (qmul p q) r = qmul p (qmul q r) := by
  funext i
  fin_cases i <;> simp [qmul] <;> ring

/-- `p̄ (p q) = |p|² q`. -/
theorem qconj_qmul_cancel (p q : Fin 4 → R) : qmul (qconj p) (qmul p q) = (p ⬝ᵥ p) • q := by
  funext i
  fin_cases i <;> simp [qmul, qconj, dotProduct, Fin.sum_univ_four] <;> ring

/-- `p (q̄ q) = |q|² p`. -/
theorem qmul_qconj_qmul_self (p q : Fin 4 → R) : qmul p (qmul (qconj q) q) = (q ⬝ᵥ q) • p := by
  funext i
  fin_cases i <;> simp [qmul, qconj, dotProduct, Fin.sum_univ_four] <;> ring

/-- `(0, v) ((0, v) q) = -|v|² q`. -/
theorem pureQ_qmul_pureQ (v : Fin 3 → R) (q : Fin 4 → R) :
    qmul (pureQ v) (qmul (pureQ v) q) = -(v ⬝ᵥ v) • q := by
  funext i
  fin_cases i <;> simp [qmul, pureQ, dotProduct, Fin.sum_univ_three] <;> ring

/-- `τ̄ (0, Q(τ) u) τ = |τ|⁴ (0, u)`. -/
theorem qconj_qmul_pureQ_qmul_self (τ : Fin 4 → R) (u : Fin 3 → R) :
    qmul (qconj τ) (qmul (pureQ (quatMatrix τ *ᵥ u)) τ) = ((τ ⬝ᵥ τ) ^ 2) • pureQ u := by
  funext i
  fin_cases i <;>
    simp [qmul, qconj, pureQ, quatMatrix, mulVec, dotProduct, Fin.sum_univ_four,
      Fin.sum_univ_three] <;> ring

/-- `τ̄ ((0, Q(τ) u) (τ X)) = |τ|⁴ (0, u) X`. -/
theorem qconj_qmul_pureQ_qmul (τ : Fin 4 → R) (u : Fin 3 → R) (X : Fin 4 → R) :
    qmul (qconj τ) (qmul (pureQ (quatMatrix τ *ᵥ u)) (qmul τ X)) =
      ((τ ⬝ᵥ τ) ^ 2) • qmul (pureQ u) X := by
  rw [← qmul_assoc (pureQ _) τ X, ← qmul_assoc (qconj τ), qconj_qmul_pureQ_qmul_self,
    qmul_smul_left]

end CommRing

/-- The conjugate of a nonzero quaternion is nonzero. -/
theorem qconj_ne_zero {q : Fin 4 → ℝ} (hq : q ≠ 0) : qconj q ≠ 0 := fun h ↦
  hq (dotProduct_self_eq_zero.mp (by rw [← qconj_dot_self, h, dotProduct_zero]))

/-- A pure quaternion of a nonzero vector is nonzero. -/
theorem pureQ_ne_zero {w : Fin 3 → ℝ} (hw : w ≠ 0) : pureQ w ≠ 0 := fun h ↦
  hw (dotProduct_self_eq_zero.mp (by rw [← pureQ_dot_self, h, dotProduct_zero]))

/-- The coordinates of rotation chart `k` of a quaternion with `q k ≠ 0`:
`chartQuat k (chartCoords k q) = (q k)⁻¹ • q` (`chartQuat_chartCoords`). -/
noncomputable def chartCoords (k : Fin 4) (q : Fin 4 → ℝ) : Fin 3 → ℝ :=
  fun i ↦ q (k.succAbove i) / q k

/-- The chart quaternion at the chart coordinates of `q` is `q`, scaled. -/
theorem chartQuat_chartCoords {k : Fin 4} {q : Fin 4 → ℝ} (h : q k ≠ 0) :
    chartQuat k (chartCoords k q) = (q k)⁻¹ • q :=
  chartQuat_succAbove h

/-- Chart coordinates do not see scaling. -/
theorem chartCoords_smul {c : ℝ} (hc : c ≠ 0) (k : Fin 4) (q : Fin 4 → ℝ) :
    chartCoords k (c • q) = chartCoords k q := by
  funext i
  simp only [chartCoords, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hc

/-- The chart coordinates of a chart quaternion. -/
theorem chartCoords_chartQuat (k : Fin 4) (x : Fin 3 → ℝ) : chartCoords k (chartQuat k x) = x := by
  funext i
  simp only [chartCoords, chartQuat_self, div_one]
  fin_cases k <;> fin_cases i <;> simp [chartQuat, Fin.succAbove]

/-- The chart rotation is the rotation of the chart quaternion. -/
theorem chartRotation_eq (k : Fin 4) (x : Fin 3 → ℝ) :
    chartRotation k x = quatRotation (chartQuat k x) :=
  rfl

/-! ### Screens -/

/-- The screen map is additive. -/
theorem screen_add (a : Fin 3) (s t : ℝ) (v w : Fin 3 → ℝ) :
    screen a s t (v + w) = screen a s t v + screen a s t w :=
  map_add (screenₗ a s t) v w

/-- The screen map is additive. -/
theorem screen_sub (a : Fin 3) (s t : ℝ) (v w : Fin 3 → ℝ) :
    screen a s t (v - w) = screen a s t v - screen a s t w :=
  map_sub (screenₗ a s t) v w

/-- The screen map is linear. -/
theorem screen_smul (a : Fin 3) (s t c : ℝ) (v : Fin 3 → ℝ) :
    screen a s t (c • v) = c • screen a s t v :=
  map_smul (screenₗ a s t) c v

/-- The screen map is odd. -/
theorem screen_neg (a : Fin 3) (s t : ℝ) (v : Fin 3 → ℝ) : screen a s t (-v) = -screen a s t v :=
  map_neg (screenₗ a s t) v

/-- The screen map vanishes at `0`. -/
theorem screen_zero (a : Fin 3) (s t : ℝ) : screen a s t 0 = 0 :=
  map_zero (screenₗ a s t)

/-- The view direction has `1` at its chart index. -/
theorem viewDir_self (a : Fin 3) (s t : ℝ) : viewDir a s t a = 1 := by
  simp [viewDir]

/-- The view direction has `s` at the chart index plus one. -/
theorem viewDir_add_one (a : Fin 3) (s t : ℝ) : viewDir a s t (a + 1) = s := by
  simp [viewDir]

/-- The view direction has `t` at the chart index plus two. -/
theorem viewDir_add_two (a : Fin 3) (s t : ℝ) : viewDir a s t (a + 2) = t := by
  simp [viewDir]

/-- The screen map of the view through `w` (chart `a`, `w a ≠ 0`) vanishes on `w`. -/
theorem screen_div_self {a : Fin 3} {w : Fin 3 → ℝ} (hw : w a ≠ 0) :
    screen a (w (a + 1) / w a) (w (a + 2) / w a) w = 0 := by
  ext i
  fin_cases i <;> simp [screen, div_mul_cancel₀ _ hw]

/-- The matrix of `screen a' s' t' ∘ T` in the screen coordinates of view chart `a`: its columns
are the images of the unit vectors `e (a + 1)` and `e (a + 2)`. It describes `screen a' s' t' ∘ T`
when `T` sends the view direction of chart `a` into the kernel (`screen_mulVec`). -/
noncomputable def screenMat (T : Matrix (Fin 3) (Fin 3) ℝ) (a a' : Fin 3) (s' t' : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j ↦ screen a' s' t' (T *ᵥ Pi.single (![a + 1, a + 2] j) 1) i

/-- If `T` sends the view direction of chart `a` at `(s, t)` into the kernel of the screen map of
chart `a'` at `(s', t')`, then `screen a' s' t' ∘ T` factors through `screen a s t`. -/
theorem screen_mulVec {T : Matrix (Fin 3) (Fin 3) ℝ} {a a' : Fin 3} {s t s' t' : ℝ}
    (h : screen a' s' t' (T *ᵥ viewDir a s t) = 0) (v : Fin 3 → ℝ) :
    screen a' s' t' (T *ᵥ v) = screenMat T a a' s' t' *ᵥ screen a s t v := by
  have hv : v = v a • viewDir a s t + screen a s t v 0 • Pi.single (a + 1) (1 : ℝ) +
      screen a s t v 1 • Pi.single (a + 2) (1 : ℝ) := by
    funext i
    fin_cases a <;> fin_cases i <;> simp [viewDir, screen] <;> ring
  conv_lhs => rw [hv]
  rw [mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, mulVec_smul, screen_add, screen_add,
    screen_smul, screen_smul, screen_smul, h, smul_zero, zero_add]
  funext i
  simp [screenMat, mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- Orientations of an affine image of the plane scale by the determinant. -/
theorem orient_mulVec_add (L : Matrix (Fin 2) (Fin 2) ℝ) (p q r v : Fin 2 → ℝ) :
    orient (L *ᵥ p + v) (L *ᵥ q + v) (L *ᵥ r + v) = L.det * orient p q r := by
  simp only [orient, Pi.add_apply, mulVec, dotProduct, Fin.sum_univ_two, det_fin_two]
  ring

/-- `σ Q(q) / |q|²` is orthogonal for `σ = ±1`. -/
theorem smul_quatMatrix_transpose_mul {σ : ℝ} {q : Fin 4 → ℝ} (hσ : σ ^ 2 = 1) (hq : q ≠ 0) :
    ((σ / (q ⬝ᵥ q)) • quatMatrix q)ᵀ * ((σ / (q ⬝ᵥ q)) • quatMatrix q) = 1 := by
  have hN : q ⬝ᵥ q ≠ 0 := dotProduct_self_eq_zero.not.mpr hq
  rw [transpose_smul, smul_mul_smul_comm, quatMatrix_transpose_mul, smul_smul]
  convert one_smul ℝ (1 : Matrix (Fin 3) (Fin 3) ℝ) using 2
  field_simp
  linear_combination hσ

/-! ### Real slacks -/

/-- The real slack (the right-hand side of `eval_slackE`): plug vertex `P` at scale `l`, moved by
`y`, against the hole edge `A → B`, in view chart `a` at `(s, t)` and rotation chart `k` at `x`. -/
noncomputable def slackR (a : Fin 3) (k : Fin 4) (s t : ℝ) (x : Fin 3 → ℝ) (y : Fin 2 → ℝ) (l : ℝ)
    (A B P : Fin 3 → ℝ) : ℝ :=
  -((chartQuat k x ⬝ᵥ chartQuat k x) *
    orient (screen a s t A) (screen a s t B)
      (l • screen a s t (quatRotation (chartQuat k x) *ᵥ P) + y))

/-- The slack polynomial evaluates to the real slack. -/
theorem eval_slackE_eq_slackR (z : ℕ → ℝ) (cen : Bool) (a : Fin 3) (k : Fin 4)
    (V : ℕ → Fin 3 → Check.Expr) (va vb vk : ℕ) :
    (slackE cen a k V va vb vk).eval z =
      slackR a k (z 0) (z 1) ![z 2, z 3, z 4] (yOf z cen) ((lE cen).eval z) (vertOf z V va)
        (vertOf z V vb) (vertOf z V vk) := by
  rw [eval_slackE]
  rfl

/-- Reversing the edge negates the slack. -/
theorem slackR_swap (a : Fin 3) (k : Fin 4) (s t : ℝ) (x : Fin 3 → ℝ) (y : Fin 2 → ℝ) (l : ℝ)
    (A B Q : Fin 3 → ℝ) : slackR a k s t x y l B A Q = -slackR a k s t x y l A B Q := by
  rw [slackR, slackR, orient_swap]
  ring

/-- Without translation, the antipodal contact has the same slack. -/
theorem slackR_neg (a : Fin 3) (k : Fin 4) (s t : ℝ) (x : Fin 3 → ℝ) (l : ℝ)
    (A B Q : Fin 3 → ℝ) : slackR a k s t x 0 l (-A) (-B) (-Q) = slackR a k s t x 0 l A B Q := by
  simp only [slackR, orient, screen_neg, mulVec_neg, smul_neg, add_zero, Pi.neg_apply]
  ring

/-! ### Pose maps -/

/-- A pose map from charts `(a, k)` to charts `(a', k')`: hole points `A ↦ T A + b`, plug points
`P ↦ G P + c`, with `T = sT • quatMatrix τ / |τ|²`, `G = sG • quatMatrix γ / |γ|²` (`sT, sG = ±1`;
`e`: the determinants differ, so the new rotation includes the reflection along the new view
direction). -/
structure PoseMap where
  /-- The source view chart. -/
  a : Fin 3
  /-- The source rotation chart. -/
  k : Fin 4
  /-- The target view chart. -/
  a' : Fin 3
  /-- The target rotation chart. -/
  k' : Fin 4
  /-- The quaternion of the hole isometry. -/
  τ : Fin 4 → ℝ
  /-- The sign (determinant) of the hole isometry. -/
  sT : ℝ
  /-- The translation of the hole isometry. -/
  b : Fin 3 → ℝ
  /-- The quaternion of the plug isometry. -/
  γ : Fin 4 → ℝ
  /-- The sign (determinant) of the plug isometry. -/
  sG : ℝ
  /-- The translation of the plug isometry. -/
  c : Fin 3 → ℝ
  /-- Whether the two signs differ. -/
  e : Bool

namespace PoseMap

variable (P : PoseMap)

/-- Nonzero quaternions, signs `±1`, and `e` records whether the signs differ. -/
def Valid : Prop :=
  P.τ ≠ 0 ∧ P.γ ≠ 0 ∧ P.sT ^ 2 = 1 ∧ P.sG ^ 2 = 1 ∧ P.sT * P.sG = (if P.e then -1 else 1)

/-- The linear part of the hole isometry. -/
noncomputable def T : Matrix (Fin 3) (Fin 3) ℝ := (P.sT / (P.τ ⬝ᵥ P.τ)) • quatMatrix P.τ

/-- The linear part of the plug isometry. -/
noncomputable def G : Matrix (Fin 3) (Fin 3) ℝ := (P.sG / (P.γ ⬝ᵥ P.γ)) • quatMatrix P.γ

/-- The new view direction, unnormalised. -/
def wv (s t : ℝ) : Fin 3 → ℝ := quatMatrix P.τ *ᵥ viewDir P.a s t

/-- The first new view coordinate. -/
noncomputable def s' (s t : ℝ) : ℝ := P.wv s t (P.a' + 1) / P.wv s t P.a'

/-- The second new view coordinate. -/
noncomputable def t' (s t : ℝ) : ℝ := P.wv s t (P.a' + 2) / P.wv s t P.a'

/-- The new quaternion, unnormalised: `τ q γ̄`, times `(0, w)` when `e`. -/
def qq (s t : ℝ) (x : Fin 3 → ℝ) : Fin 4 → ℝ :=
  let p := qmul (qmul P.τ (chartQuat P.k x)) (qconj P.γ)
  if P.e then qmul (pureQ (P.wv s t)) p else p

/-- The new rotation coordinates. -/
noncomputable def x' (s t : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ := chartCoords P.k' (P.qq s t x)

/-- `screen a' s' t' ∘ T = L ∘ screen a s t` (`PoseMap.screen_T`): the columns are the images of
`e (a + 1)`, `e (a + 2)`. -/
noncomputable def L (s t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  screenMat P.T P.a P.a' (P.s' s t) (P.t' s t)

/-- The new translation. -/
noncomputable def y' (s t : ℝ) (x : Fin 3 → ℝ) (y : Fin 2 → ℝ) (l : ℝ) : Fin 2 → ℝ :=
  P.L s t *ᵥ y + screen P.a' (P.s' s t) (P.t' s t) P.b
    - l • screen P.a' (P.s' s t) (P.t' s t) (quatRotation (P.qq s t x) *ᵥ P.c)

/-- The factor of the slacks. -/
noncomputable def factor (s t : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  (P.L s t).det * (chartQuat P.k' (P.x' s t x) ⬝ᵥ chartQuat P.k' (P.x' s t x)) /
    (chartQuat P.k x ⬝ᵥ chartQuat P.k x)

/-- The inverse map. -/
noncomputable def inv : PoseMap :=
  ⟨P.a', P.k', P.a, P.k, qconj P.τ, P.sT, -(P.Tᵀ *ᵥ P.b), qconj P.γ, P.sG, -(P.Gᵀ *ᵥ P.c), P.e⟩

@[simp] theorem inv_a : P.inv.a = P.a' := rfl
@[simp] theorem inv_k : P.inv.k = P.k' := rfl
@[simp] theorem inv_a' : P.inv.a' = P.a := rfl
@[simp] theorem inv_k' : P.inv.k' = P.k := rfl
@[simp] theorem inv_τ : P.inv.τ = qconj P.τ := rfl
@[simp] theorem inv_sT : P.inv.sT = P.sT := rfl
@[simp] theorem inv_b : P.inv.b = -(P.Tᵀ *ᵥ P.b) := rfl
@[simp] theorem inv_γ : P.inv.γ = qconj P.γ := rfl
@[simp] theorem inv_sG : P.inv.sG = P.sG := rfl
@[simp] theorem inv_c : P.inv.c = -(P.Gᵀ *ᵥ P.c) := rfl
@[simp] theorem inv_e : P.inv.e = P.e := rfl

/-! #### Isometries -/

variable {P}

/-- The hole isometry is orthogonal. -/
theorem T_transpose_mul (hP : P.Valid) : P.Tᵀ * P.T = 1 :=
  smul_quatMatrix_transpose_mul hP.2.2.1 hP.1

/-- The hole isometry is orthogonal. -/
theorem T_mul_transpose (hP : P.Valid) : P.T * P.Tᵀ = 1 :=
  mul_eq_one_comm.mp (T_transpose_mul hP)

/-- The plug isometry is orthogonal. -/
theorem G_transpose_mul (hP : P.Valid) : P.Gᵀ * P.G = 1 :=
  smul_quatMatrix_transpose_mul hP.2.2.2.1 hP.2.1

/-- The plug isometry is orthogonal. -/
theorem G_mul_transpose (hP : P.Valid) : P.G * P.Gᵀ = 1 :=
  mul_eq_one_comm.mp (G_transpose_mul hP)

variable (P)

/-- The hole isometry of the inverse is the transpose. -/
theorem inv_T : P.inv.T = P.Tᵀ := by
  rw [T, T, inv_τ, inv_sT, quatMatrix_qconj, qconj_dot_self, transpose_smul]

/-- The plug isometry of the inverse is the transpose. -/
theorem inv_G : P.inv.G = P.Gᵀ := by
  rw [G, G, inv_γ, inv_sG, quatMatrix_qconj, qconj_dot_self, transpose_smul]

variable {P}

/-- The inverse of a valid map is valid. -/
theorem inv_valid (hP : P.Valid) : P.inv.Valid := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP
  exact ⟨qconj_ne_zero h1, qconj_ne_zero h2, h3, h4, h5⟩

/-- The inverse undoes the hole isometry. -/
theorem inv_hole (hP : P.Valid) (A : Fin 3 → ℝ) : P.inv.T *ᵥ (P.T *ᵥ A + P.b) + P.inv.b = A := by
  rw [inv_T, inv_b, mulVec_add, mulVec_mulVec, T_transpose_mul hP, one_mulVec,
    add_neg_cancel_right]

/-- The inverse undoes the plug isometry. -/
theorem inv_plug (hP : P.Valid) (Q : Fin 3 → ℝ) : P.inv.G *ᵥ (P.G *ᵥ Q + P.c) + P.inv.c = Q := by
  rw [inv_G, inv_c, mulVec_add, mulVec_mulVec, G_transpose_mul hP, one_mulVec,
    add_neg_cancel_right]

/-! #### Views -/

variable {s t : ℝ} {x : Fin 3 → ℝ}

/-- `T` sends the view direction to a multiple of `wv`. -/
theorem T_mulVec_viewDir : P.T *ᵥ viewDir P.a s t = (P.sT / (P.τ ⬝ᵥ P.τ)) • P.wv s t := by
  rw [T, smul_mulVec]
  rfl

/-- The new screen map vanishes on the new view direction. -/
theorem screen_wv (hw : P.wv s t P.a' ≠ 0) : screen P.a' (P.s' s t) (P.t' s t) (P.wv s t) = 0 :=
  screen_div_self hw

/-- **The screens correspond**: `screen a' s' t' (T v) = L (screen a s t v)`. -/
theorem screen_T (hw : P.wv s t P.a' ≠ 0) (v : Fin 3 → ℝ) :
    screen P.a' (P.s' s t) (P.t' s t) (P.T *ᵥ v) = P.L s t *ᵥ screen P.a s t v :=
  screen_mulVec (by rw [T_mulVec_viewDir, screen_smul, screen_wv hw, smul_zero]) v

/-! #### Rotations -/

/-- The new quaternion is nonzero. -/
theorem qq_ne_zero (hP : P.Valid) (hw : P.wv s t P.a' ≠ 0) : P.qq s t x ≠ 0 := by
  have hp := qmul_ne_zero (qmul_ne_zero hP.1 (chartQuat_ne_zero P.k x)) (qconj_ne_zero hP.2.1)
  have hw0 : P.wv s t ≠ 0 := fun h ↦ hw (by rw [h, Pi.zero_apply])
  unfold qq
  split_ifs
  exacts [qmul_ne_zero (pureQ_ne_zero hw0) hp, hp]

/-- **The rotations correspond**: `R' G = S T R`, where `S` is the identity or the reflection
along the new view direction, which the new screen map does not see. -/
theorem screen_rot (hP : P.Valid) (hw : P.wv s t P.a' ≠ 0) (v : Fin 3 → ℝ) :
    screen P.a' (P.s' s t) (P.t' s t) (quatRotation (P.qq s t x) *ᵥ (P.G *ᵥ v)) =
      screen P.a' (P.s' s t) (P.t' s t) (P.T *ᵥ (quatRotation (chartQuat P.k x) *ᵥ v)) := by
  obtain ⟨hτ, hγ, hsT, -, hTG⟩ := hP
  have hNτ : P.τ ⬝ᵥ P.τ ≠ 0 := dotProduct_self_eq_zero.not.mpr hτ
  have hNγ : P.γ ⬝ᵥ P.γ ≠ 0 := dotProduct_self_eq_zero.not.mpr hγ
  have hNq := (quat_pos P.k x).ne'
  have hγγ : (quatMatrix P.γ)ᵀ *ᵥ (quatMatrix P.γ *ᵥ v) = ((P.γ ⬝ᵥ P.γ) ^ 2) • v := by
    rw [mulVec_mulVec, quatMatrix_transpose_mul, smul_mulVec, one_mulVec]
  have hR : P.T *ᵥ (quatRotation (chartQuat P.k x) *ᵥ v) =
      (P.sT / (P.τ ⬝ᵥ P.τ) * (chartQuat P.k x ⬝ᵥ chartQuat P.k x)⁻¹) •
        (quatMatrix P.τ *ᵥ (quatMatrix (chartQuat P.k x) *ᵥ v)) := by
    rw [T, quatRotation, smul_mulVec, smul_mulVec, mulVec_smul, smul_smul]
  rw [hR]
  cases he : P.e
  · rw [he] at hTG
    simp only [Bool.false_eq_true, ↓reduceIte] at hTG
    have hs : P.sG = P.sT := by linear_combination (-P.sG) * hsT + P.sT * hTG
    simp only [qq, he, Bool.false_eq_true, ↓reduceIte, quatRotation, G, qmul_dot_self,
      qconj_dot_self, quatMatrix_qmul, quatMatrix_qconj, ← mulVec_mulVec, smul_mulVec,
      mulVec_smul, hγγ, smul_smul]
    congr 2
    rw [hs]
    field_simp
  · rw [he] at hTG
    simp only [↓reduceIte] at hTG
    have hs : P.sG = -P.sT := by linear_combination (-P.sG) * hsT + P.sT * hTG
    simp only [qq, he, ↓reduceIte, quatRotation, G, qmul_dot_self, pureQ_dot_self,
      qconj_dot_self, quatMatrix_qmul, quatMatrix_qconj, ← mulVec_mulVec, smul_mulVec,
      mulVec_smul, hγγ, smul_smul]
    have hNw : P.wv s t ⬝ᵥ P.wv s t ≠ 0 :=
      dotProduct_self_eq_zero.not.mpr fun h ↦ hw (by rw [h, Pi.zero_apply])
    rw [quatMatrix_pureQ_mulVec]
    simp only [smul_sub, smul_smul, screen_sub, screen_smul, P.screen_wv hw, smul_zero, zero_sub,
      ← neg_smul]
    congr 1
    rw [hs]
    field_simp

/-- The new chart quaternion is the new quaternion, scaled. -/
theorem chartQuat_x' (hq : P.qq s t x P.k' ≠ 0) :
    chartQuat P.k' (P.x' s t x) = (P.qq s t x P.k')⁻¹ • P.qq s t x :=
  chartQuat_chartCoords hq

/-- The new rotation is the rotation of the new quaternion. -/
theorem rotation_x' (hq : P.qq s t x P.k' ≠ 0) :
    quatRotation (chartQuat P.k' (P.x' s t x)) = quatRotation (P.qq s t x) := by
  rw [chartQuat_x' hq, quatRotation_smul (inv_ne_zero hq)]

/-! #### Slacks -/

/-- **Covariance of slacks**: a pose map multiplies the slack of a contact by `factor`. -/
theorem slackR_map (hP : P.Valid) (hw : P.wv s t P.a' ≠ 0) (hq : P.qq s t x P.k' ≠ 0)
    (A B Q : Fin 3 → ℝ) (y : Fin 2 → ℝ) (l : ℝ) :
    slackR P.a' P.k' (P.s' s t) (P.t' s t) (P.x' s t x) (P.y' s t x y l) l
        (P.T *ᵥ A + P.b) (P.T *ᵥ B + P.b) (P.G *ᵥ Q + P.c) =
      P.factor s t x * slackR P.a P.k s t x y l A B Q := by
  have hplug : l • screen P.a' (P.s' s t) (P.t' s t)
        (quatRotation (chartQuat P.k' (P.x' s t x)) *ᵥ (P.G *ᵥ Q + P.c)) + P.y' s t x y l =
      P.L s t *ᵥ (l • screen P.a s t (quatRotation (chartQuat P.k x) *ᵥ Q) + y) +
        screen P.a' (P.s' s t) (P.t' s t) P.b := by
    rw [rotation_x' hq, mulVec_add, screen_add, screen_rot hP hw, screen_T hw, y', mulVec_add,
      mulVec_smul]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [slackR, slackR, screen_add, screen_add, screen_T hw, screen_T hw, hplug, orient_mulVec_add,
    factor]
  have := (quat_pos P.k x).ne'
  field_simp

/-! #### The inverse -/

/-- The view direction of the inverse at the new view, a multiple of the old view direction. -/
theorem inv_wv (hw : P.wv s t P.a' ≠ 0) :
    P.inv.wv (P.s' s t) (P.t' s t) = ((P.wv s t P.a')⁻¹ * (P.τ ⬝ᵥ P.τ) ^ 2) • viewDir P.a s t := by
  have hv : viewDir P.a' (P.s' s t) (P.t' s t) = (P.wv s t P.a')⁻¹ • P.wv s t := viewDir_div hw
  rw [wv, inv_τ, inv_a, hv, quatMatrix_qconj, mulVec_smul, wv, mulVec_mulVec,
    quatMatrix_transpose_mul, smul_mulVec, one_mulVec, smul_smul]

/-- The inverse's view direction is in its chart. -/
theorem inv_wv_ne (hP : P.Valid) (hw : P.wv s t P.a' ≠ 0) :
    P.inv.wv (P.s' s t) (P.t' s t) P.a ≠ 0 := by
  rw [inv_wv hw, Pi.smul_apply, viewDir_self, smul_eq_mul, mul_one]
  exact mul_ne_zero (inv_ne_zero hw) (pow_ne_zero 2 (dotProduct_self_eq_zero.not.mpr hP.1))

/-- The inverse restores the first view coordinate. -/
theorem inv_s' (hP : P.Valid) (hw : P.wv s t P.a' ≠ 0) : P.inv.s' (P.s' s t) (P.t' s t) = s := by
  have h := inv_wv_ne hP hw
  rw [inv_wv hw, Pi.smul_apply, viewDir_self, smul_eq_mul, mul_one] at h
  rw [s', inv_a', inv_wv hw, Pi.smul_apply, Pi.smul_apply, viewDir_self, viewDir_add_one,
    smul_eq_mul, smul_eq_mul, mul_one, mul_div_cancel_left₀ _ h]

/-- The inverse restores the second view coordinate. -/
theorem inv_t' (hP : P.Valid) (hw : P.wv s t P.a' ≠ 0) : P.inv.t' (P.s' s t) (P.t' s t) = t := by
  have h := inv_wv_ne hP hw
  rw [inv_wv hw, Pi.smul_apply, viewDir_self, smul_eq_mul, mul_one] at h
  rw [t', inv_a', inv_wv hw, Pi.smul_apply, Pi.smul_apply, viewDir_self, viewDir_add_two,
    smul_eq_mul, smul_eq_mul, mul_one, mul_div_cancel_left₀ _ h]

/-- The inverse's new quaternion is a multiple of the old chart quaternion. -/
theorem inv_qq (hP : P.Valid) (hw : P.wv s t P.a' ≠ 0) (hq : P.qq s t x P.k' ≠ 0) :
    ∃ c : ℝ, c ≠ 0 ∧ P.inv.qq (P.s' s t) (P.t' s t) (P.x' s t x) = c • chartQuat P.k x := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, P.inv.qq (P.s' s t) (P.t' s t) (P.x' s t x) = c • chartQuat P.k x := by
    set κ := (P.qq s t x P.k')⁻¹
    have h1 : chartQuat P.k' (P.x' s t x) = κ • P.qq s t x := chartQuat_x' hq
    set c₁ := (P.wv s t P.a')⁻¹ * (P.τ ⬝ᵥ P.τ) ^ 2
    have h2 : P.inv.wv (P.s' s t) (P.t' s t) = c₁ • viewDir P.a s t := inv_wv hw
    cases he : P.e
    · simp only [qq, inv_τ, inv_γ, inv_e, inv_k, h1, he, qconj_qconj, Bool.false_eq_true,
        ↓reduceIte, qmul_smul_left, qmul_smul_right, qmul_assoc, qconj_qmul_cancel,
        qmul_qconj_qmul_self, smul_smul]
      exact ⟨_, rfl⟩
    · have hwv : P.wv s t = quatMatrix P.τ *ᵥ viewDir P.a s t := rfl
      simp only [qq, inv_τ, inv_γ, inv_e, inv_k, h1, h2, hwv, he, qconj_qconj, ↓reduceIte,
        pureQ_smul, qmul_smul_left, qmul_smul_right, qmul_assoc, qconj_qmul_pureQ_qmul,
        qmul_qconj_qmul_self, pureQ_qmul_pureQ, smul_smul]
      exact ⟨_, rfl⟩
  refine ⟨c, fun h0 ↦ ?_, hc⟩
  refine qq_ne_zero (x := P.x' s t x) (inv_valid hP) (inv_wv_ne hP hw) ?_
  rw [hc, h0, zero_smul]

/-- The inverse's new quaternion is in the old chart. -/
theorem inv_qq_ne (hP : P.Valid) (hw : P.wv s t P.a' ≠ 0) (hq : P.qq s t x P.k' ≠ 0) :
    P.inv.qq (P.s' s t) (P.t' s t) (P.x' s t x) P.k ≠ 0 := by
  obtain ⟨c, hc, h⟩ := inv_qq hP hw hq
  rw [h, Pi.smul_apply, chartQuat_self, smul_eq_mul, mul_one]
  exact hc

/-- The inverse restores the rotation coordinates. -/
theorem inv_x' (hP : P.Valid) (hw : P.wv s t P.a' ≠ 0) (hq : P.qq s t x P.k' ≠ 0) :
    P.inv.x' (P.s' s t) (P.t' s t) (P.x' s t x) = x := by
  obtain ⟨c, hc, h⟩ := inv_qq hP hw hq
  rw [x', inv_k', h, chartCoords_smul hc, chartCoords_chartQuat]

/-- The inverse restores the rotation. -/
theorem rotation_inv_qq (hP : P.Valid) (hw : P.wv s t P.a' ≠ 0) (hq : P.qq s t x P.k' ≠ 0) :
    quatRotation (P.inv.qq (P.s' s t) (P.t' s t) (P.x' s t x)) =
      quatRotation (chartQuat P.k x) := by
  obtain ⟨c, hc, h⟩ := inv_qq hP hw hq
  rw [h, quatRotation_smul hc]

/-- The screens correspond under the inverse. -/
theorem screen_inv_T (hP : P.Valid) (hw : P.wv s t P.a' ≠ 0) (v : Fin 3 → ℝ) :
    screen P.a s t (P.Tᵀ *ᵥ v) =
      P.inv.L (P.s' s t) (P.t' s t) *ᵥ screen P.a' (P.s' s t) (P.t' s t) v := by
  have h := P.inv.screen_T (inv_wv_ne hP hw) v
  rwa [inv_a', inv_a, inv_s' hP hw, inv_t' hP hw, inv_T] at h

/-- The rotations correspond under the inverse. -/
theorem screen_inv_rot (hP : P.Valid) (hw : P.wv s t P.a' ≠ 0) (hq : P.qq s t x P.k' ≠ 0)
    (v : Fin 3 → ℝ) :
    screen P.a s t (P.Tᵀ *ᵥ (quatRotation (P.qq s t x) *ᵥ v)) =
      screen P.a s t (quatRotation (chartQuat P.k x) *ᵥ (P.Gᵀ *ᵥ v)) := by
  have h := P.inv.screen_rot (x := P.x' s t x) (inv_valid hP) (inv_wv_ne hP hw) v
  rw [inv_a', inv_k, inv_s' hP hw, inv_t' hP hw, inv_T, inv_G, rotation_inv_qq hP hw hq,
    rotation_x' hq] at h
  exact h.symm

/-- The screen matrices of a map and its inverse are inverse. -/
theorem inv_L_mul (hP : P.Valid) (hw : P.wv s t P.a' ≠ 0) :
    P.inv.L (P.s' s t) (P.t' s t) * P.L s t = 1 := by
  have key : ∀ p, (P.inv.L (P.s' s t) (P.t' s t) * P.L s t) *ᵥ p = p := by
    intro p
    obtain ⟨v, rfl⟩ := screen_surjective P.a s t p
    rw [← mulVec_mulVec, ← screen_T hw, ← screen_inv_T hP hw, mulVec_mulVec, T_transpose_mul hP,
      one_mulVec]
  ext i j
  simpa [one_apply, Pi.single_apply, eq_comm] using congrFun (key (Pi.single j 1)) i

/-- The inverse restores the translation. -/
theorem inv_y' (hP : P.Valid) (hw : P.wv s t P.a' ≠ 0) (hq : P.qq s t x P.k' ≠ 0)
    (y : Fin 2 → ℝ) (l : ℝ) :
    P.inv.y' (P.s' s t) (P.t' s t) (P.x' s t x) (P.y' s t x y l) l = y := by
  rw [y', inv_a', inv_s' hP hw, inv_t' hP hw, rotation_inv_qq hP hw hq, inv_b, inv_c, y',
    mulVec_sub, mulVec_add, mulVec_mulVec, inv_L_mul hP hw, one_mulVec, mulVec_smul,
    ← screen_inv_T hP hw, ← screen_inv_T hP hw, screen_inv_rot hP hw hq, mulVec_neg, screen_neg,
    screen_neg]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

/-- The factors of a map and its inverse are inverse. -/
theorem factor_inv_mul (hP : P.Valid) (hw : P.wv s t P.a' ≠ 0) (hq : P.qq s t x P.k' ≠ 0) :
    P.inv.factor (P.s' s t) (P.t' s t) (P.x' s t x) * P.factor s t x = 1 := by
  have hd : (P.inv.L (P.s' s t) (P.t' s t)).det * (P.L s t).det = 1 := by
    rw [← det_mul, inv_L_mul hP hw, det_one]
  have h1 := (quat_pos P.k x).ne'
  have h2 := (quat_pos P.k' (P.x' s t x)).ne'
  rw [factor, factor, inv_k, inv_k', inv_x' hP hw hq]
  field_simp
  linear_combination hd

/-- **The factor is nonzero.** -/
theorem factor_ne_zero (hP : P.Valid) (hw : P.wv s t P.a' ≠ 0) (hq : P.qq s t x P.k' ≠ 0) :
    P.factor s t x ≠ 0 := fun h ↦ by
  have := factor_inv_mul hP hw hq
  rw [h, mul_zero] at this
  exact zero_ne_one this

/-- A map without translations keeps the zero translation. -/
theorem y'_zero (hb : P.b = 0) (hc : P.c = 0) (l : ℝ) : P.y' s t x 0 l = 0 := by
  simp [y', hb, hc, screen_zero]

end PoseMap

end Nieuwland.Root
