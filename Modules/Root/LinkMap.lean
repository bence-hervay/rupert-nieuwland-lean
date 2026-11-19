import Modules.Root.PoseMap
import Modules.Root.Chain

/-!
# Pose maps as quotients of expressions

The coordinates of a pose map's image (`Modules/Root/PoseMap.lean`) are quotients of polynomials
in the source's variables and the map's real data. Here they are expressions: the variables of
the source system (view `0, 1`, rotation `2, 3, 4`, translation `5, 6` in general mode, the scale
`nx`, the multipliers), and the map's data as variables from an offset `o` on (`τE`, `bE`, …: the
quaternion `τ`, `d_b` times the translation `b`, `d_b`, the quaternion `γ`, `d_c` times `c`, `d_c`).
`Holds D P ζ o` says that the point `ζ` holds the data of `P` there.

* `WE`, `QQE`: the new view direction `wv` and quaternion `qq`, polynomials (`Holds.evalV_WE`,
  `Holds.evalV_QQE`); the new view and rotation coordinates are their ratios.
* `yNE / yDE`: the new translation (`Holds.y'_eq`); `fNE / fDE`: the factor of the slacks
  (`Holds.factor_eq`).
* `coordE`: the numerator and denominator of every coordinate of the image, the multipliers
  `m'_{σ i} = ε_i m_i / factor` included.
-/

open Matrix
open Nieuwland.Check (Expr)

namespace Nieuwland.Root

/-! ### Vectors of expressions -/

/-- The values of a vector of expressions. -/
def evalV {n : ℕ} (z : ℕ → ℝ) (v : Fin n → Expr) : Fin n → ℝ := fun i ↦ (v i).eval z

@[simp] theorem evalV_apply {n : ℕ} (z : ℕ → ℝ) (v : Fin n → Expr) (i : Fin n) :
    evalV z v i = (v i).eval z := rfl

/-- `qmul` on expressions. -/
def qmulE (p q : Fin 4 → Expr) : Fin 4 → Expr :=
  ![p 0 * q 0 - p 1 * q 1 - p 2 * q 2 - p 3 * q 3,
    p 0 * q 1 + p 1 * q 0 + p 2 * q 3 - p 3 * q 2,
    p 0 * q 2 - p 1 * q 3 + p 2 * q 0 + p 3 * q 1,
    p 0 * q 3 + p 1 * q 2 - p 2 * q 1 + p 3 * q 0]

theorem evalV_qmulE (z : ℕ → ℝ) (p q : Fin 4 → Expr) :
    evalV z (qmulE p q) = qmul (evalV z p) (evalV z q) := by
  funext i
  fin_cases i <;> simp [qmulE, qmul]

/-- `qconj` on expressions. -/
def qconjE (q : Fin 4 → Expr) : Fin 4 → Expr :=
  ![q 0, .const 0 - q 1, .const 0 - q 2, .const 0 - q 3]

theorem evalV_qconjE (z : ℕ → ℝ) (q : Fin 4 → Expr) :
    evalV z (qconjE q) = qconj (evalV z q) := by
  funext i
  fin_cases i <;> simp [qconjE, qconj]

/-- `pureQ` on expressions. -/
def pureQE (w : Fin 3 → Expr) : Fin 4 → Expr := ![.const 0, w 0, w 1, w 2]

theorem evalV_pureQE (z : ℕ → ℝ) (w : Fin 3 → Expr) :
    evalV z (pureQE w) = pureQ (evalV z w) := by
  funext i
  fin_cases i <;> simp [pureQE, pureQ]

/-- `quatMatrix q *ᵥ v` on expressions. -/
def qmvE (q : Fin 4 → Expr) (v : Fin 3 → Expr) : Fin 3 → Expr :=
  fun i ↦ quatE q i 0 * v 0 + quatE q i 1 * v 1 + quatE q i 2 * v 2

theorem evalV_qmvE (z : ℕ → ℝ) (q : Fin 4 → Expr) (v : Fin 3 → Expr) :
    evalV z (qmvE q v) = quatMatrix (evalV z q) *ᵥ evalV z v := by
  funext i
  simp [qmvE, eval_quatE, mulVec, dotProduct, Fin.sum_univ_three]
  rfl

/-- The view direction of chart `a` on expressions, `(s, t)` in the variables `0, 1`. -/
def viewDirE (a : Fin 3) : Fin 3 → Expr := fun i ↦ ![.const 1, .var 0, .var 1] (i - a)

theorem evalV_viewDirE (z : ℕ → ℝ) (a : Fin 3) :
    evalV z (viewDirE a) = viewDir a (z 0) (z 1) := by
  funext i
  fin_cases a <;> fin_cases i <;> simp [viewDirE, viewDir]

theorem evalV_qE (z : ℕ → ℝ) (k : Fin 4) : evalV z (qE k) = chartQuat k ![z 2, z 3, z 4] := by
  funext j
  simp [eval_qE]

/-- `w_{a'}` times the screen map of the view through `w` (chart `a'`), on expressions. -/
def sigE (a' : Fin 3) (W v : Fin 3 → Expr) : Fin 2 → Expr :=
  ![W a' * v (a' + 1) - W (a' + 1) * v a', W a' * v (a' + 2) - W (a' + 2) * v a']

/-- `w_{a'}` times the screen map of the view through `w` (chart `a'`). -/
def sigR (a' : Fin 3) (W v : Fin 3 → ℝ) : Fin 2 → ℝ :=
  ![W a' * v (a' + 1) - W (a' + 1) * v a', W a' * v (a' + 2) - W (a' + 2) * v a']

theorem evalV_sigE (z : ℕ → ℝ) (a' : Fin 3) (W v : Fin 3 → Expr) :
    evalV z (sigE a' W v) = sigR a' (evalV z W) (evalV z v) := by
  funext i
  fin_cases i <;> simp [sigE, sigR]

theorem screen_ratio {a' : Fin 3} {W : Fin 3 → ℝ} (hW : W a' ≠ 0) (v : Fin 3 → ℝ) :
    screen a' (W (a' + 1) / W a') (W (a' + 2) / W a') v = (W a')⁻¹ • sigR a' W v := by
  funext i
  fin_cases i <;> simp [screen, sigR] <;> field_simp

theorem sigR_smul (a' : Fin 3) (W v : Fin 3 → ℝ) (r : ℝ) :
    sigR a' W (r • v) = r • sigR a' W v := by
  funext i
  fin_cases i <;> simp [sigR] <;> ring

/-! ### The data of a pose map -/

/-- The discrete data of a pose map: charts, the sign of the hole isometry, whether the signs
differ, and the mode. -/
structure MapD where
  /-- The source view chart. -/
  a : Fin 3
  /-- The source rotation chart. -/
  k : Fin 4
  /-- The target view chart. -/
  a' : Fin 3
  /-- The target rotation chart. -/
  k' : Fin 4
  /-- The sign of the hole isometry. -/
  sT : ℤ
  /-- Whether the signs of the two isometries differ. -/
  e : Bool
  /-- Centred mode. -/
  cen : Bool
  deriving Repr, DecidableEq

/-- The quaternion `τ`. -/
def τE (o : ℕ) : Fin 4 → Expr := fun j ↦ .var (o + j)
/-- `d_b b`. -/
def bE (o : ℕ) : Fin 3 → Expr := fun j ↦ .var (o + (4 + j))
/-- `d_b`. -/
def dbE (o : ℕ) : Expr := .var (o + 7)
/-- The quaternion `γ`. -/
def γE (o : ℕ) : Fin 4 → Expr := fun j ↦ .var (o + (8 + j))
/-- `d_c c`. -/
def cE (o : ℕ) : Fin 3 → Expr := fun j ↦ .var (o + (12 + j))
/-- `d_c`. -/
def dcE (o : ℕ) : Expr := .var (o + 15)

/-- The point `ζ` holds the data of the pose map `P` from `o` on, with charts and signs `D`. -/
structure Holds (D : MapD) (P : PoseMap) (ζ : ℕ → ℝ) (o : ℕ) : Prop where
  a : P.a = D.a
  k : P.k = D.k
  a' : P.a' = D.a'
  k' : P.k' = D.k'
  sT : P.sT = D.sT
  e : P.e = D.e
  τ : evalV ζ (τE o) = P.τ
  b : evalV ζ (bE o) = (dbE o).eval ζ • P.b
  db : (dbE o).eval ζ ≠ 0
  γ : evalV ζ (γE o) = P.γ
  c : evalV ζ (cE o) = (dcE o).eval ζ • P.c
  dc : (dcE o).eval ζ ≠ 0

/-! ### The image as quotients -/

section Image

variable (D : MapD) (o : ℕ)

/-- The new view direction `wv`. -/
def WE : Fin 3 → Expr := qmvE (τE o) (viewDirE D.a)

/-- The new quaternion `qq`. -/
def QQE : Fin 4 → Expr :=
  let p := qmulE (qmulE (τE o) (qE D.k)) (qconjE (γE o))
  if D.e then qmulE (pureQE (WE D o)) p else p

/-- `|τ|² w_{a'}` times the screen matrix `L`, `sT` aside. -/
def LamE (i j : Fin 2) : Expr :=
  sigE D.a' (WE D o) (fun m ↦ quatE (τE o) m (![D.a + 1, D.a + 2] j)) i

/-- The numerator of the new translation. -/
def yNE (c : Fin 2) : Expr :=
  .const D.sT * (LamE D o c 0 * yE D.cen 0 + LamE D o c 1 * yE D.cen 1) * dbE o * dcE o *
      normE (QQE D o) +
    sigE D.a' (WE D o) (bE o) c * normE (τE o) * dcE o * normE (QQE D o) -
    lE D.cen * sigE D.a' (WE D o) (qmvE (QQE D o) (cE o)) c * normE (τE o) * dbE o

/-- The denominator of the new translation. -/
def yDE : Expr := WE D o D.a' * normE (τE o) * dbE o * dcE o * normE (QQE D o)

/-- The numerator of the factor of the slacks. -/
def fNE : Expr :=
  (LamE D o 0 0 * LamE D o 1 1 - LamE D o 0 1 * LamE D o 1 0) * normE (QQE D o)

/-- The denominator of the factor of the slacks. -/
def fDE : Expr :=
  normE (τE o) * normE (τE o) * (WE D o D.a' * WE D o D.a') * (QQE D o D.k' * QQE D o D.k') *
    normE (qE D.k)

end Image

variable {D : MapD} {P : PoseMap} {ζ : ℕ → ℝ} {o : ℕ}

theorem Holds.evalV_WE (h : Holds D P ζ o) : evalV ζ (WE D o) = P.wv (ζ 0) (ζ 1) := by
  simp only [WE, evalV_qmvE, evalV_viewDirE, h.τ, PoseMap.wv, h.a]

theorem Holds.evalV_QQE (h : Holds D P ζ o) :
    evalV ζ (QQE D o) = P.qq (ζ 0) (ζ 1) ![ζ 2, ζ 3, ζ 4] := by
  unfold QQE PoseMap.qq
  rw [h.e, h.k]
  cases D.e <;>
    simp only [Bool.false_eq_true, ↓reduceIte, evalV_qmulE, evalV_qconjE, evalV_pureQE,
      h.evalV_WE, h.γ, h.τ, evalV_qE]

/-- The new view coordinates are the ratios of `wv`. -/
theorem Holds.s'_eq (h : Holds D P ζ o) :
    P.s' (ζ 0) (ζ 1) = (WE D o (D.a' + 1)).eval ζ / (WE D o D.a').eval ζ := by
  rw [← evalV_apply, ← evalV_apply, h.evalV_WE, PoseMap.s', h.a']

theorem Holds.t'_eq (h : Holds D P ζ o) :
    P.t' (ζ 0) (ζ 1) = (WE D o (D.a' + 2)).eval ζ / (WE D o D.a').eval ζ := by
  rw [← evalV_apply, ← evalV_apply, h.evalV_WE, PoseMap.t', h.a']

/-- The new rotation coordinates are the ratios of `qq`. -/
theorem Holds.x'_eq (h : Holds D P ζ o) (i : Fin 3) :
    P.x' (ζ 0) (ζ 1) ![ζ 2, ζ 3, ζ 4] i =
      (QQE D o (D.k'.succAbove i)).eval ζ / (QQE D o D.k').eval ζ := by
  rw [← evalV_apply, ← evalV_apply, h.evalV_QQE, PoseMap.x', chartCoords, h.k']

theorem Holds.L_eq (h : Holds D P ζ o) (hw : P.wv (ζ 0) (ζ 1) P.a' ≠ 0) (i j : Fin 2) :
    P.L (ζ 0) (ζ 1) i j =
      P.sT / (P.τ ⬝ᵥ P.τ) / P.wv (ζ 0) (ζ 1) P.a' * (LamE D o i j).eval ζ := by
  have hcol : evalV ζ (fun m ↦ quatE (τE o) m (![D.a + 1, D.a + 2] j)) =
      quatMatrix P.τ *ᵥ Pi.single (![P.a + 1, P.a + 2] j) 1 := by
    funext m
    simp [eval_quatE, h.a, ← h.τ]
    rfl
  simp only [PoseMap.L, screenMat, of_apply]
  rw [PoseMap.T, smul_mulVec, screen_smul, PoseMap.s', PoseMap.t', screen_ratio hw, ← hcol]
  simp only [LamE, ← evalV_apply ζ (sigE _ _ _), evalV_sigE, h.evalV_WE, h.a', Pi.smul_apply,
    smul_eq_mul]
  ring

theorem Holds.yD_eq (h : Holds D P ζ o) : (yDE D o).eval ζ =
    P.wv (ζ 0) (ζ 1) P.a' * (P.τ ⬝ᵥ P.τ) * (dbE o).eval ζ * (dcE o).eval ζ *
      (P.qq (ζ 0) (ζ 1) ![ζ 2, ζ 3, ζ 4] ⬝ᵥ P.qq (ζ 0) (ζ 1) ![ζ 2, ζ 3, ζ 4]) := by
  simp only [yDE, Expr.eval_mul, eval_normE, ← evalV_apply ζ (WE D o), h.evalV_WE,
    ← evalV_apply ζ (QQE D o), h.evalV_QQE, h.a']
  rw [show (fun i ↦ (τE o i).eval ζ) = P.τ from h.τ]

theorem Holds.yD_ne (h : Holds D P ζ o) (hw : P.wv (ζ 0) (ζ 1) P.a' ≠ 0)
    (hq : P.qq (ζ 0) (ζ 1) ![ζ 2, ζ 3, ζ 4] P.k' ≠ 0) (hτ : P.τ ≠ 0) : (yDE D o).eval ζ ≠ 0 := by
  rw [h.yD_eq]
  have hτ2 : P.τ ⬝ᵥ P.τ ≠ 0 := dotProduct_self_eq_zero.not.mpr hτ
  have hQ2 : P.qq (ζ 0) (ζ 1) ![ζ 2, ζ 3, ζ 4] ⬝ᵥ P.qq (ζ 0) (ζ 1) ![ζ 2, ζ 3, ζ 4] ≠ 0 :=
    dotProduct_self_eq_zero.not.mpr fun h0 ↦ hq (by rw [h0]; rfl)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hw hτ2) h.db) h.dc) hQ2

theorem Holds.fD_eq (h : Holds D P ζ o) : (fDE D o).eval ζ = (P.τ ⬝ᵥ P.τ) * (P.τ ⬝ᵥ P.τ) *
    (P.wv (ζ 0) (ζ 1) P.a' * P.wv (ζ 0) (ζ 1) P.a') *
    (P.qq (ζ 0) (ζ 1) ![ζ 2, ζ 3, ζ 4] P.k' * P.qq (ζ 0) (ζ 1) ![ζ 2, ζ 3, ζ 4] P.k') *
    (chartQuat P.k ![ζ 2, ζ 3, ζ 4] ⬝ᵥ chartQuat P.k ![ζ 2, ζ 3, ζ 4]) := by
  simp only [fDE, Expr.eval_mul, eval_normE, ← evalV_apply ζ (WE D o), h.evalV_WE,
    ← evalV_apply ζ (QQE D o), h.evalV_QQE, h.a', h.k', ← evalV_apply ζ (qE D.k), evalV_qE,
    h.k]
  rw [show (fun i ↦ (τE o i).eval ζ) = P.τ from h.τ]

theorem Holds.fD_ne (h : Holds D P ζ o) (hw : P.wv (ζ 0) (ζ 1) P.a' ≠ 0)
    (hq : P.qq (ζ 0) (ζ 1) ![ζ 2, ζ 3, ζ 4] P.k' ≠ 0) (hτ : P.τ ≠ 0) : (fDE D o).eval ζ ≠ 0 := by
  rw [h.fD_eq]
  have hτ2 : P.τ ⬝ᵥ P.τ ≠ 0 := dotProduct_self_eq_zero.not.mpr hτ
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hτ2 hτ2) (mul_ne_zero hw hw))
    (mul_ne_zero hq hq)) (quat_pos _ _).ne'

theorem Holds.y'_eq (h : Holds D P ζ o) (hw : P.wv (ζ 0) (ζ 1) P.a' ≠ 0)
    (hq : P.qq (ζ 0) (ζ 1) ![ζ 2, ζ 3, ζ 4] P.k' ≠ 0) (hτ : P.τ ≠ 0) (c : Fin 2) :
    P.y' (ζ 0) (ζ 1) ![ζ 2, ζ 3, ζ 4] (yOf ζ D.cen) (ζ (nx D.cen)) c =
      (yNE D o c).eval ζ / (yDE D o).eval ζ := by
  have hτ2 : P.τ ⬝ᵥ P.τ ≠ 0 := dotProduct_self_eq_zero.not.mpr hτ
  have hQ2 : P.qq (ζ 0) (ζ 1) ![ζ 2, ζ 3, ζ 4] ⬝ᵥ P.qq (ζ 0) (ζ 1) ![ζ 2, ζ 3, ζ 4] ≠ 0 :=
    dotProduct_self_eq_zero.not.mpr fun h0 ↦ hq (by rw [h0]; rfl)
  have hb : P.b = ((dbE o).eval ζ)⁻¹ • evalV ζ (bE o) := by
    rw [h.b, smul_smul, inv_mul_cancel₀ h.db, one_smul]
  have hc : P.c = ((dcE o).eval ζ)⁻¹ • evalV ζ (cE o) := by
    rw [h.c, smul_smul, inv_mul_cancel₀ h.dc, one_smul]
  have hs : ∀ v, screen P.a' (P.s' (ζ 0) (ζ 1)) (P.t' (ζ 0) (ζ 1)) v =
      (P.wv (ζ 0) (ζ 1) P.a')⁻¹ • sigR P.a' (P.wv (ζ 0) (ζ 1)) v := fun v ↦ by
    simp only [PoseMap.s', PoseMap.t', screen_ratio hw]
  have eN : (yNE D o c).eval ζ =
      D.sT * ((LamE D o c 0).eval ζ * yOf ζ D.cen 0 + (LamE D o c 1).eval ζ * yOf ζ D.cen 1) *
          (dbE o).eval ζ * (dcE o).eval ζ *
          (P.qq (ζ 0) (ζ 1) ![ζ 2, ζ 3, ζ 4] ⬝ᵥ P.qq (ζ 0) (ζ 1) ![ζ 2, ζ 3, ζ 4]) +
        sigR P.a' (P.wv (ζ 0) (ζ 1)) (evalV ζ (bE o)) c * (P.τ ⬝ᵥ P.τ) * (dcE o).eval ζ *
          (P.qq (ζ 0) (ζ 1) ![ζ 2, ζ 3, ζ 4] ⬝ᵥ P.qq (ζ 0) (ζ 1) ![ζ 2, ζ 3, ζ 4]) -
        ζ (nx D.cen) * sigR P.a' (P.wv (ζ 0) (ζ 1))
            (quatMatrix (P.qq (ζ 0) (ζ 1) ![ζ 2, ζ 3, ζ 4]) *ᵥ evalV ζ (cE o)) c *
          (P.τ ⬝ᵥ P.τ) * (dbE o).eval ζ := by
    simp only [yNE, Expr.eval_add, Expr.eval_sub, Expr.eval_mul, Expr.eval_const, eval_normE,
      ← evalV_apply ζ (sigE _ _ _), evalV_sigE, ← evalV_apply ζ (QQE D o), h.evalV_QQE,
      evalV_qmvE, h.evalV_WE, h.a']
    simp only [yOf, lE, Expr.eval_var]
    rw [show (fun i ↦ (τE o i).eval ζ) = P.τ from h.τ]
  have eD : (yDE D o).eval ζ = P.wv (ζ 0) (ζ 1) P.a' * (P.τ ⬝ᵥ P.τ) * (dbE o).eval ζ *
      (dcE o).eval ζ *
      (P.qq (ζ 0) (ζ 1) ![ζ 2, ζ 3, ζ 4] ⬝ᵥ P.qq (ζ 0) (ζ 1) ![ζ 2, ζ 3, ζ 4]) := by
    simp only [yDE, Expr.eval_mul, eval_normE, ← evalV_apply ζ (WE D o), h.evalV_WE,
      ← evalV_apply ζ (QQE D o), h.evalV_QQE, h.a']
    rw [show (fun i ↦ (τE o i).eval ζ) = P.τ from h.τ]
  have hLy : (P.L (ζ 0) (ζ 1) *ᵥ yOf ζ D.cen) c =
      P.L (ζ 0) (ζ 1) c 0 * yOf ζ D.cen 0 + P.L (ζ 0) (ζ 1) c 1 * yOf ζ D.cen 1 := by
    simp [mulVec, dotProduct, Fin.sum_univ_two]
  rw [eN, eD, PoseMap.y']
  simp only [Pi.add_apply, Pi.sub_apply, hLy, h.L_eq hw, hs, Pi.smul_apply, smul_eq_mul, hb, hc,
    sigR_smul, quatRotation, smul_mulVec, mulVec_smul, h.sT]
  have hdb := h.db
  have hdc := h.dc
  field_simp

theorem Holds.factor_eq (h : Holds D P ζ o) (hP : P.Valid) (hw : P.wv (ζ 0) (ζ 1) P.a' ≠ 0)
    (hq : P.qq (ζ 0) (ζ 1) ![ζ 2, ζ 3, ζ 4] P.k' ≠ 0) :
    P.factor (ζ 0) (ζ 1) ![ζ 2, ζ 3, ζ 4] = (fNE D o).eval ζ / (fDE D o).eval ζ := by
  have hτ2 : P.τ ⬝ᵥ P.τ ≠ 0 := dotProduct_self_eq_zero.not.mpr hP.1
  have hq2 : chartQuat P.k ![ζ 2, ζ 3, ζ 4] ⬝ᵥ chartQuat P.k ![ζ 2, ζ 3, ζ 4] ≠ 0 :=
    (quat_pos _ _).ne'
  have hs2 : P.sT ^ 2 = 1 := hP.2.2.1
  have eN : (fNE D o).eval ζ = ((LamE D o 0 0).eval ζ * (LamE D o 1 1).eval ζ -
      (LamE D o 0 1).eval ζ * (LamE D o 1 0).eval ζ) *
      (P.qq (ζ 0) (ζ 1) ![ζ 2, ζ 3, ζ 4] ⬝ᵥ P.qq (ζ 0) (ζ 1) ![ζ 2, ζ 3, ζ 4]) := by
    simp only [fNE, Expr.eval_mul, Expr.eval_sub, eval_normE, ← evalV_apply ζ (QQE D o),
      h.evalV_QQE]
  have eD : (fDE D o).eval ζ = (P.τ ⬝ᵥ P.τ) * (P.τ ⬝ᵥ P.τ) *
      (P.wv (ζ 0) (ζ 1) P.a' * P.wv (ζ 0) (ζ 1) P.a') *
      (P.qq (ζ 0) (ζ 1) ![ζ 2, ζ 3, ζ 4] P.k' * P.qq (ζ 0) (ζ 1) ![ζ 2, ζ 3, ζ 4] P.k') *
      (chartQuat P.k ![ζ 2, ζ 3, ζ 4] ⬝ᵥ chartQuat P.k ![ζ 2, ζ 3, ζ 4]) := by
    simp only [fDE, Expr.eval_mul, eval_normE, ← evalV_apply ζ (WE D o), h.evalV_WE,
      ← evalV_apply ζ (QQE D o), h.evalV_QQE, h.a', h.k', ← evalV_apply ζ (qE D.k), evalV_qE,
      h.k]
    rw [show (fun i ↦ (τE o i).eval ζ) = P.τ from h.τ]
  rw [eN, eD, PoseMap.factor, det_fin_two, h.L_eq hw, h.L_eq hw, h.L_eq hw, h.L_eq hw,
    PoseMap.chartQuat_x' hq]
  simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul]
  field_simp
  rw [hs2]
  ring

end Nieuwland.Root
