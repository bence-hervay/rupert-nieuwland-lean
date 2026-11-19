import Modules.Check.Sign.Box
import Modules.Check.Leaf.Vec

/-!
# Witness polynomials

The support polynomials of `RESEARCH.md` §3.3 (`regional.rs` in the Rust checker) in the
homogeneous coordinates of a chart box, together with their real meaning.

A chart box has the variables `0, 1` (view coordinates `s, t`), `2, 3, 4` (rotation coordinates
`x`) and `5`, the homogenising variable `D` that stands for the `1` of the charts: the view
direction is `homView a D S T` and the quaternion `homQuat k D X` (`viewVars`, `quatVars`).
Witness polynomials are homogeneous of degree 4 in these six variables
(`Expr.balanced_isHomogeneous`), so the bounds of `Modules/Check/Sign/Box.lean` give their signs at
the poses of a box.

* `supportPoly u q c v w = u ⬝ᵥ (c ⨯₃ (Q(q) v - |q|² w))`. At a chart pose it is
  `|q|² (n ⬝ᵥ R v - n ⬝ᵥ w)` with the normal `n = u ⨯₃ c` and the rotation `R = Q(q) / |q|²`
  (`supportPoly_pose`).
* `balancedPoly`: the combination `∑ λᵢ supportPoly u q cᵢ vᵢ wᵢ` with the weights
  `λᵢ = σ u ⬝ᵥ (c_{i+1} ⨯₃ c_{i+2})`, which balance the normals (`sum_weightPoly_smul_cross`).
* `supportG`, `weightG`, `balancedG`: the same polynomials over any type with `+`, `-` and `*`,
  for exact data (`Modules/Check/Number/Exact.lean`), built with the kernel vectors of
  `Modules/Check/Leaf/Vec.lean`; over the reals with `Exact.re` they are the polynomials above
  (`balancedG_re`). On the variables of a chart box they are generic computations
  (`balancedGen`, homogeneous of degree 4, with their meaning `balancedGen_homEnv`), whose values,
  shapes and norm bounds the kernel computes by runs (`Modules/Check/Sign/Box.lean`). A single support
  polynomial, as in width pairs, has degree 3 (`supportGen`).
-/

open Matrix

namespace Nieuwland.Check

/-! ### Homogeneous chart coordinates -/

section Hom

variable {α β : Type*}

/-- The view direction of view chart `a` in homogeneous coordinates: `u a = D`, `u (a + 1) = S`
and `u (a + 2) = T`. At `D = 1` it is `viewDir a S T` (`toFun_homView`). -/
def homView (a : Fin 3) (D S T : α) : V3 α :=
  match a with
  | 0 => ⟨D, S, T⟩
  | 1 => ⟨T, D, S⟩
  | 2 => ⟨S, T, D⟩

/-- The quaternion of rotation chart `k` in homogeneous coordinates: `q k = D`, and `X` fills the
other places in increasing order. At `D = 1` it is `chartQuat k X` (`toFun_homQuat`). -/
def homQuat (k : Fin 4) (D : α) (X : V3 α) : Q4 α :=
  match k with
  | 0 => ⟨D, X.x, X.y, X.z⟩
  | 1 => ⟨X.x, D, X.y, X.z⟩
  | 2 => ⟨X.x, X.y, D, X.z⟩
  | 3 => ⟨X.x, X.y, X.z, D⟩

theorem map_homView (f : α → β) (a : Fin 3) (D S T : α) :
    (homView a D S T).map f = homView a (f D) (f S) (f T) := by
  fin_cases a <;> rfl

theorem map_homQuat (f : α → β) (k : Fin 4) (D : α) (X : V3 α) :
    (homQuat k D X).map f = homQuat k (f D) (X.map f) := by
  fin_cases k <;> rfl

theorem toFun_homView {R : Type*} [CommRing R] (a : Fin 3) (d s t : R) :
    (homView a d (d * s) (d * t)).toFun = d • viewDir a s t := by
  funext i
  fin_cases a <;> fin_cases i <;> simp [homView, viewDir]

theorem toFun_homQuat {R : Type*} [CommRing R] (k : Fin 4) (d : R) (x : Fin 3 → R) :
    (homQuat k d ⟨d * x 0, d * x 1, d * x 2⟩).toFun = d • chartQuat k x := by
  funext i
  fin_cases k <;> fin_cases i <;> simp [homQuat, chartQuat, Q4.toFun]

end Hom

/-! ### Chart variables -/

/-- The point `(y 2, y 3, y 4)` of the rotation chart, for a point `y` of a chart box. -/
def rotCoords {R : Type*} (y : Fin 5 → R) : Fin 3 → R := ![y 2, y 3, y 4]

/-- The homogeneous view direction of view chart `a` on the variables of a chart box. -/
def viewVars (a : Fin 3) : V3 Expr := homView a (.var 5) (.var 0) (.var 1)

/-- The homogeneous quaternion of rotation chart `k` on the variables of a chart box. -/
def quatVars (k : Fin 4) : Q4 Expr := homQuat k (.var 5) ⟨.var 2, .var 3, .var 4⟩

section Env

variable {R : Type*} [CommRing R] (d : R) (y : Fin 5 → R)

@[simp] theorem homEnv_five_zero : homEnv 5 d y 0 = d * y 0 := rfl
@[simp] theorem homEnv_five_one : homEnv 5 d y 1 = d * y 1 := rfl
@[simp] theorem homEnv_five_two : homEnv 5 d y 2 = d * y 2 := rfl
@[simp] theorem homEnv_five_three : homEnv 5 d y 3 = d * y 3 := rfl
@[simp] theorem homEnv_five_four : homEnv 5 d y 4 = d * y 4 := rfl
@[simp] theorem homEnv_five_five : homEnv 5 d y 5 = d := rfl

theorem toFun_viewVars (a : Fin 3) :
    ((viewVars a).map (Expr.eval (homEnv 5 d y))).toFun = d • viewDir a (y 0) (y 1) := by
  rw [viewVars, map_homView, ← toFun_homView]
  rfl

theorem toFun_quatVars (k : Fin 4) :
    ((quatVars k).map (Expr.eval (homEnv 5 d y))).toFun = d • chartQuat k (rotCoords y) := by
  rw [quatVars, map_homQuat, ← toFun_homQuat]
  rfl

end Env

/-! ### Support polynomials -/

section Poly

variable {R : Type*} [CommRing R]

/-- The support polynomial `u ⬝ᵥ (c ⨯₃ (Q(q) v - |q|² w))` (see `supportPoly_pose`). -/
def supportPoly (u : Fin 3 → R) (q : Fin 4 → R) (c v w : Fin 3 → R) : R :=
  u ⬝ᵥ (c ⨯₃ (quatMatrix q *ᵥ v - (q ⬝ᵥ q) • w))

/-- The balance weight `σ u ⬝ᵥ (c₁ ⨯₃ c₂)`. -/
def weightPoly (σ : R) (u c₁ c₂ : Fin 3 → R) : R :=
  σ * (u ⬝ᵥ (c₁ ⨯₃ c₂))

/-- The balanced combination `∑ᵢ λᵢ supportPoly u q (c i) (v i) (w i)`, with the weights
`λᵢ = σ u ⬝ᵥ (c (i + 1) ⨯₃ c (i + 2))`. -/
def balancedPoly (σ : R) (u : Fin 3 → R) (q : Fin 4 → R) (c v w : Fin 3 → Fin 3 → R) : R :=
  ∑ i, weightPoly σ u (c (i + 1)) (c (i + 2)) * supportPoly u q (c i) (v i) (w i)

theorem quatMatrix_smul (d : R) (q : Fin 4 → R) : quatMatrix (d • q) = d ^ 2 • quatMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quatMatrix] <;> ring

theorem supportPoly_smul (d : R) (u : Fin 3 → R) (q : Fin 4 → R) (c v w : Fin 3 → R) :
    supportPoly (d • u) (d • q) c v w = d ^ 3 * supportPoly u q c v w := by
  simp only [supportPoly, dotProduct, Fin.sum_univ_three, Fin.sum_univ_four, cross_apply, mulVec,
    quatMatrix, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  simp
  ring

theorem weightPoly_smul (σ d : R) (u c₁ c₂ : Fin 3 → R) :
    weightPoly σ (d • u) c₁ c₂ = d * weightPoly σ u c₁ c₂ := by
  simp only [weightPoly, smul_dotProduct, smul_eq_mul]
  ring

theorem balancedPoly_smul (σ d : R) (u : Fin 3 → R) (q : Fin 4 → R) (c v w : Fin 3 → Fin 3 → R) :
    balancedPoly σ (d • u) (d • q) c v w = d ^ 4 * balancedPoly σ u q c v w := by
  simp only [balancedPoly, weightPoly_smul, supportPoly_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

theorem supportPoly_smul_quat (a : R) (u : Fin 3 → R) (q : Fin 4 → R) (c v w : Fin 3 → R) :
    supportPoly u (a • q) c v w = a ^ 2 * supportPoly u q c v w := by
  simp only [supportPoly, dotProduct, Fin.sum_univ_three, Fin.sum_univ_four, cross_apply, mulVec,
    quatMatrix, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  simp
  ring

theorem balancedPoly_smul_quat (σ a : R) (u : Fin 3 → R) (q : Fin 4 → R)
    (c v w : Fin 3 → Fin 3 → R) :
    balancedPoly σ u (a • q) c v w = a ^ 2 * balancedPoly σ u q c v w := by
  simp only [balancedPoly, supportPoly_smul_quat, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-- **Support polynomials along a line** of quaternions are quadratic:
`p(q + δ r) = p(q) + δ (p(q + r) - p(q) - p(r)) + δ² p(r)`. -/
theorem supportPoly_add_smul (u : Fin 3 → R) (q r : Fin 4 → R) (δ : R) (c v w : Fin 3 → R) :
    supportPoly u (q + δ • r) c v w = supportPoly u q c v w +
      δ * (supportPoly u (q + r) c v w - supportPoly u q c v w - supportPoly u r c v w) +
        δ ^ 2 * supportPoly u r c v w := by
  simp only [supportPoly, dotProduct, Fin.sum_univ_three, Fin.sum_univ_four, cross_apply, mulVec,
    quatMatrix, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  simp
  ring

theorem balancedPoly_add_smul (σ : R) (u : Fin 3 → R) (q r : Fin 4 → R) (δ : R)
    (c v w : Fin 3 → Fin 3 → R) :
    balancedPoly σ u (q + δ • r) c v w = balancedPoly σ u q c v w +
      δ * (balancedPoly σ u (q + r) c v w - balancedPoly σ u q c v w -
        balancedPoly σ u r c v w) + δ ^ 2 * balancedPoly σ u r c v w := by
  simp only [balancedPoly, Fin.sum_univ_three, supportPoly_add_smul]
  ring

/-- **The weights balance the normals**: `∑ᵢ λᵢ (u ⨯₃ c i) = 0`, since
`∑ᵢ (u ⬝ᵥ (c (i + 1) ⨯₃ c (i + 2))) c i = det(c) u` (Cramer's rule). -/
theorem sum_weightPoly_smul_cross (σ : R) (u : Fin 3 → R) (c : Fin 3 → Fin 3 → R) :
    ∑ i, weightPoly σ u (c (i + 1)) (c (i + 2)) • (u ⨯₃ c i) = 0 := by
  ext j
  fin_cases j <;>
    simp [Fin.sum_univ_three, weightPoly, cross_apply, dotProduct] <;> ring

/-- `u ⬝ᵥ (c ⨯₃ x) = (u ⨯₃ c) ⬝ᵥ x`. -/
theorem dot_cross_eq_cross_dot (u c x : Fin 3 → R) : u ⬝ᵥ (c ⨯₃ x) = (u ⨯₃ c) ⬝ᵥ x := by
  rw [triple_product_permutation, triple_product_permutation, dotProduct_comm]

end Poly

theorem chartQuat_dot_self_pos (k : Fin 4) (x : Fin 3 → ℝ) :
    0 < chartQuat k x ⬝ᵥ chartQuat k x :=
  lt_of_le_of_ne (Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _)
    (Ne.symm (dotProduct_self_eq_zero.not.mpr (chartQuat_ne_zero k x)))

theorem dotProduct_self_pos {n : ℕ} {q : Fin n → ℝ} (hq : q ≠ 0) : 0 < q ⬝ᵥ q :=
  lt_of_le_of_ne (Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _)
    (Ne.symm (dotProduct_self_eq_zero.not.mpr hq))

/-- **Support polynomials at a representative.** For a quaternion `q ≠ 0` with rotation
`R = Q(q) / |q|²` and `n = u ⨯₃ c`, `supportPoly u q c v w = |q|² (n ⬝ᵥ R v - n ⬝ᵥ w)`. -/
theorem supportPoly_rep {q : Fin 4 → ℝ} (hq : q ≠ 0) (u c v w : Fin 3 → ℝ) :
    supportPoly u q c v w = (q ⬝ᵥ q) * ((u ⨯₃ c) ⬝ᵥ (quatRotation q *ᵥ v) - (u ⨯₃ c) ⬝ᵥ w) := by
  have hd : q ⬝ᵥ q ≠ 0 := dotProduct_self_eq_zero.not.mpr hq
  have hQ : quatMatrix q = (q ⬝ᵥ q) • quatRotation q := by
    rw [quatRotation, smul_smul, mul_inv_cancel₀ hd, one_smul]
  rw [supportPoly, dot_cross_eq_cross_dot, hQ, smul_mulVec, ← smul_sub, dotProduct_smul,
    dotProduct_sub, smul_eq_mul]

/-- **Balanced polynomials at a representative**: `|q|²` times the weighted sum of the support
differences `n i ⬝ᵥ R v i - n i ⬝ᵥ w i`. -/
theorem balancedPoly_rep (σ : ℝ) (u : Fin 3 → ℝ) {q : Fin 4 → ℝ} (hq : q ≠ 0)
    (c v w : Fin 3 → Fin 3 → ℝ) :
    balancedPoly σ u q c v w = (q ⬝ᵥ q) * ∑ i, weightPoly σ u (c (i + 1)) (c (i + 2)) *
      ((u ⨯₃ c i) ⬝ᵥ (quatRotation q *ᵥ v i) - (u ⨯₃ c i) ⬝ᵥ w i) := by
  rw [balancedPoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [supportPoly_rep hq]
  ring

/-- **Support polynomials at a chart pose.** With `q` the chart quaternion, `R` the chart
rotation and `n = u ⨯₃ c` for the view direction `u`,
`supportPoly u q c v w = |q|² (n ⬝ᵥ R v - n ⬝ᵥ w)`. -/
theorem supportPoly_pose (a : Fin 3) (s t : ℝ) (k : Fin 4) (x : Fin 3 → ℝ) (c v w : Fin 3 → ℝ) :
    supportPoly (viewDir a s t) (chartQuat k x) c v w =
      (chartQuat k x ⬝ᵥ chartQuat k x) * ((viewDir a s t ⨯₃ c) ⬝ᵥ (chartRotation k x *ᵥ v) -
        (viewDir a s t ⨯₃ c) ⬝ᵥ w) :=
  supportPoly_rep (chartQuat_ne_zero k x) _ _ _ _

/-- **Balanced polynomials at a chart pose**: `|q|²` times the weighted sum of the support
differences `n i ⬝ᵥ R v i - n i ⬝ᵥ w i`. -/
theorem balancedPoly_pose (σ : ℝ) (a : Fin 3) (s t : ℝ) (k : Fin 4) (x : Fin 3 → ℝ)
    (c v w : Fin 3 → Fin 3 → ℝ) :
    balancedPoly σ (viewDir a s t) (chartQuat k x) c v w =
      (chartQuat k x ⬝ᵥ chartQuat k x) * ∑ i, weightPoly σ (viewDir a s t) (c (i + 1)) (c (i + 2)) *
        ((viewDir a s t ⨯₃ c i) ⬝ᵥ (chartRotation k x *ᵥ v i) - (viewDir a s t ⨯₃ c i) ⬝ᵥ w i) :=
  balancedPoly_rep σ _ (chartQuat_ne_zero k x) _ _ _

/-! ### Witness polynomials, generically -/

section Generic

variable {κ α β : Type} [Add κ] [Sub κ] [Mul κ] [Add α] [Sub α] [Mul α] [Add β] [Sub β] [Mul β]

/-- `U ⬝ᵥ (c ⨯₃ (Q(Q) v - |Q|² w))` in any type with `+`, `-` and `*`, with the exact data
`c`, `v`, `w` embedded by `k`. -/
def supportG (k : κ → α) (U : V3 α) (Q : Q4 α) (c v w : V3 κ) : α :=
  U.dot ((c.map k).cross ((Q.rotate (v.map k)).sub (V3.smul Q.norm2 (w.map k))))

/-- `σ U ⬝ᵥ (c₁ ⨯₃ c₂)`, with the cross product of the exact data computed first. -/
def weightG (k : κ → α) (σ : κ) (U : V3 α) (c₁ c₂ : V3 κ) : α :=
  k σ * U.dot ((c₁.cross c₂).map k)

/-- `∑ᵢ λᵢ supportG k U Q (c i) (v i) (w i)` with the weights
`λᵢ = weightG k σ U (c (i + 1)) (c (i + 2))`. -/
def balancedG (k : κ → α) (σ : κ) (U : V3 α) (Q : Q4 α) (c v w : Fin 3 → V3 κ) : α :=
  weightG k σ U (c 1) (c 2) * supportG k U Q (c 0) (v 0) (w 0) +
    weightG k σ U (c 2) (c 0) * supportG k U Q (c 1) (v 1) (w 1) +
    weightG k σ U (c 0) (c 1) * supportG k U Q (c 2) (v 2) (w 2)

variable {f : α → β}

omit [Add κ] [Sub κ] [Mul κ] in
theorem map_supportG (hf : IsArith f) (k : κ → α) (U : V3 α) (Q : Q4 α) (c v w : V3 κ) :
    f (supportG k U Q c v w) = supportG (f ∘ k) (U.map f) (Q.map f) c v w := by
  rw [supportG, V3.map_dot hf, V3.map_cross hf, V3.map_sub hf, V3.map_smul hf, Q4.map_rotate hf,
    Q4.map_norm2 hf]
  rfl

omit [Add κ] in
theorem map_weightG (hf : IsArith f) (k : κ → α) (σ : κ) (U : V3 α) (c₁ c₂ : V3 κ) :
    f (weightG k σ U c₁ c₂) = weightG (f ∘ k) σ (U.map f) c₁ c₂ := by
  rw [weightG, hf.map_mul, V3.map_dot hf]
  rfl

omit [Add κ] in
theorem map_balancedG (hf : IsArith f) (k : κ → α) (σ : κ) (U : V3 α) (Q : Q4 α)
    (c v w : Fin 3 → V3 κ) :
    f (balancedG k σ U Q c v w) = balancedG (f ∘ k) σ (U.map f) (Q.map f) c v w := by
  simp only [balancedG, hf.map_add, hf.map_mul, map_weightG hf, map_supportG hf]

end Generic

section Meaning

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

theorem supportG_re (U : V3 ℝ) (Q : Q4 ℝ) (c v w : V3 κ) :
    supportG Exact.re U Q c v w =
      supportPoly U.toFun Q.toFun (Exact.reV c) (Exact.reV v) (Exact.reV w) := by
  rw [supportG, V3.dot_eq_dotProduct, V3.toFun_cross, V3.toFun_sub, V3.toFun_smul,
    Q4.toFun_rotate, Q4.norm2_eq_dotProduct]
  rfl

theorem weightG_re (σ : κ) (U : V3 ℝ) (c₁ c₂ : V3 κ) :
    weightG Exact.re σ U c₁ c₂ =
      weightPoly (Exact.re σ) U.toFun (Exact.reV c₁) (Exact.reV c₂) := by
  rw [weightG, V3.dot_eq_dotProduct, weightPoly, V3.map_cross Exact.isArith, V3.toFun_cross]
  rfl

theorem balancedG_re (σ : κ) (U : V3 ℝ) (Q : Q4 ℝ) (c v w : Fin 3 → V3 κ) :
    balancedG Exact.re σ U Q c v w =
      balancedPoly (Exact.re σ) U.toFun Q.toFun (fun i ↦ Exact.reV (c i))
        (fun i ↦ Exact.reV (v i)) (fun i ↦ Exact.reV (w i)) := by
  simp only [balancedG, balancedPoly, Fin.sum_univ_three, weightG_re, supportG_re]
  rfl

end Meaning

/-! ### Pre-rotations -/

section Pre

/-- The real quaternion `q` followed by the pre-rotation `c`, if any: `q c` (`qmul`). -/
def preQuat (q : Fin 4 → ℝ) : Option (Fin 4 → ℝ) → Fin 4 → ℝ
  | none => q
  | some c => qmul q c

/-- The rotation of a pre-rotation: `R(c)`, the identity without one. -/
noncomputable def preRot : Option (Fin 4 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ
  | none => 1
  | some c => quatRotation c

@[simp] theorem preRot_none : preRot none = 1 :=
  rfl

theorem quatRotation_preQuat (q : Fin 4 → ℝ) :
    ∀ pre, quatRotation (preQuat q pre) = quatRotation q * preRot pre
  | none => (mul_one _).symm
  | some c => quatRotation_qmul q c

theorem preQuat_smul (a : ℝ) (q : Fin 4 → ℝ) : ∀ pre, preQuat (a • q) pre = a • preQuat q pre
  | none => rfl
  | some c => qmul_smul_left a q c

theorem preQuat_add (p q : Fin 4 → ℝ) :
    ∀ pre, preQuat (p + q) pre = preQuat p pre + preQuat q pre
  | none => rfl
  | some c => qmul_add_left p q c

theorem preQuat_ne_zero {q : Fin 4 → ℝ} (hq : q ≠ 0) :
    ∀ {pre : Option (Fin 4 → ℝ)}, (∀ c ∈ pre, c ≠ 0) → preQuat q pre ≠ 0
  | none, _ => hq
  | some c, h => qmul_ne_zero hq (h c rfl)

/-- A pre-rotation keeps orthogonal quaternions orthogonal. -/
theorem preQuat_dot_eq_zero {a b : Fin 4 → ℝ} (h : a ⬝ᵥ b = 0) :
    ∀ pre, preQuat a pre ⬝ᵥ preQuat b pre = 0
  | none => h
  | some c => by
    change qmul a c ⬝ᵥ qmul b c = 0
    rw [qmul_dot_qmul, h, zero_mul]

variable {κ α β : Type} [Add α] [Sub α] [Mul α] [Add β] [Sub β] [Mul β]

/-- The quaternion `Q` followed by the pre-rotation `c`, if any: `Q c` (`Q4.mul`), with the exact
`c` embedded by `k`. -/
def preQ (k : κ → α) (Q : Q4 α) : Option (Q4 κ) → Q4 α
  | none => Q
  | some c => Q.mul (c.map k)

theorem map_preQ {f : α → β} (hf : IsArith f) (k : κ → α) (Q : Q4 α) :
    ∀ pre, (preQ k Q pre).map f = preQ (f ∘ k) (Q.map f) pre
  | none => rfl
  | some c => by
    rw [preQ, preQ, Q4.map_mul hf]
    rfl

theorem toFun_preQ [Add κ] [Sub κ] [Mul κ] [Exact κ] (Q : Q4 ℝ) :
    ∀ pre : Option (Q4 κ), (preQ Exact.re Q pre).toFun = preQuat Q.toFun (Exact.rePre pre)
  | none => rfl
  | some c => by
    rw [preQ, Q4.toFun_mul]
    rfl

/-- An exact quaternion followed by an exact pre-rotation, as a quaternion of `ℝ⁴`. -/
theorem reQ_preQ [Add κ] [Sub κ] [Mul κ] [Exact κ] (e : Q4 κ) (pre : Option (Q4 κ)) :
    Exact.reQ (preQ id e pre) = preQuat (Exact.reQ e) (Exact.rePre pre) := by
  rw [Exact.reQ, map_preQ Exact.isArith id e pre]
  exact toFun_preQ (e.map Exact.re) pre

end Pre

/-! ### Witnesses on chart boxes -/

section Chart

variable {κ : Type} [Add κ] [Sub κ] [Mul κ]

/-- The balanced witness on the variables of a chart box (view `S, T` in `0, 1`, rotation `X` in
`2, 3, 4`, `D` in `5`), as a generic computation. -/
def balancedGen (σ : κ) (a : Fin 3) (k : Fin 4) (c v w : Fin 3 → V3 κ)
    (pre : Option (Q4 κ) := none) : GenPoly κ where
  run emb x := balancedG emb σ (homView a (x 5) (x 0) (x 1))
    (preQ emb (homQuat k (x 5) ⟨x 2, x 3, x 4⟩) pre) c v w
  natural f hf emb x := by
    rw [map_balancedG hf, map_homView, map_preQ hf, map_homQuat]
    rfl

/-- A support polynomial on the variables of a chart box, as a generic computation. -/
def supportGen (a : Fin 3) (k : Fin 4) (c v w : V3 κ) (pre : Option (Q4 κ) := none) :
    GenPoly κ where
  run emb x := supportG emb (homView a (x 5) (x 0) (x 1))
    (preQ emb (homQuat k (x 5) ⟨x 2, x 3, x 4⟩) pre) c v w
  natural f hf emb x := by
    rw [map_supportG hf, map_homView, map_preQ hf, map_homQuat]
    rfl

variable [Exact κ]

theorem toFun_homView_homEnv (a : Fin 3) (d : ℝ) (y : Fin 5 → ℝ) :
    (homView a (homEnv 5 d y 5) (homEnv 5 d y 0) (homEnv 5 d y 1)).toFun =
      d • viewDir a (y 0) (y 1) :=
  toFun_homView a d (y 0) (y 1)

theorem toFun_homQuat_homEnv (k : Fin 4) (d : ℝ) (y : Fin 5 → ℝ) :
    (homQuat k (homEnv 5 d y 5) ⟨homEnv 5 d y 2, homEnv 5 d y 3, homEnv 5 d y 4⟩).toFun =
      d • chartQuat k (rotCoords y) :=
  toFun_homQuat k d (rotCoords y)

/-- The balanced witness at a box point `y` with homogenising value `d`. -/
theorem balancedGen_homEnv (σ : κ) (a : Fin 3) (k : Fin 4) (c v w : Fin 3 → V3 κ)
    (pre : Option (Q4 κ)) (d : ℝ) (y : Fin 5 → ℝ) :
    (balancedGen σ a k c v w pre).run Exact.re (homEnv 5 d y) =
      d ^ 4 * balancedPoly (Exact.re σ) (viewDir a (y 0) (y 1))
        (preQuat (chartQuat k (rotCoords y)) (Exact.rePre pre))
        (fun i ↦ Exact.reV (c i)) (fun i ↦ Exact.reV (v i)) (fun i ↦ Exact.reV (w i)) := by
  change balancedG Exact.re σ (homView a (homEnv 5 d y 5) (homEnv 5 d y 0) (homEnv 5 d y 1))
    (preQ Exact.re (homQuat k (homEnv 5 d y 5)
      ⟨homEnv 5 d y 2, homEnv 5 d y 3, homEnv 5 d y 4⟩) pre) c v w = _
  rw [balancedG_re, toFun_homView_homEnv, toFun_preQ, toFun_homQuat_homEnv, preQuat_smul,
    balancedPoly_smul]

theorem balancedGen_isHomogeneous (σ : κ) (a : Fin 3) (k : Fin 4) (c v w : Fin 3 → V3 κ)
    (pre : Option (Q4 κ)) : (balancedGen σ a k c v w pre).IsHomogeneous 5 4 := fun d y ↦ by
  rw [balancedGen_homEnv, balancedGen_homEnv, one_pow, one_mul]

/-- The support polynomial at a box point `y` with homogenising value `d`. -/
theorem supportGen_homEnv (a : Fin 3) (k : Fin 4) (c v w : V3 κ) (pre : Option (Q4 κ)) (d : ℝ)
    (y : Fin 5 → ℝ) : (supportGen a k c v w pre).run Exact.re (homEnv 5 d y) =
      d ^ 3 * supportPoly (viewDir a (y 0) (y 1))
        (preQuat (chartQuat k (rotCoords y)) (Exact.rePre pre)) (Exact.reV c) (Exact.reV v)
        (Exact.reV w) := by
  change supportG Exact.re (homView a (homEnv 5 d y 5) (homEnv 5 d y 0) (homEnv 5 d y 1))
    (preQ Exact.re (homQuat k (homEnv 5 d y 5)
      ⟨homEnv 5 d y 2, homEnv 5 d y 3, homEnv 5 d y 4⟩) pre) c v w = _
  rw [supportG_re, toFun_homView_homEnv, toFun_preQ, toFun_homQuat_homEnv, preQuat_smul,
    supportPoly_smul]

theorem supportGen_isHomogeneous (a : Fin 3) (k : Fin 4) (c v w : V3 κ) (pre : Option (Q4 κ)) :
    (supportGen a k c v w pre).IsHomogeneous 5 3 := fun d y ↦ by
  rw [supportGen_homEnv, supportGen_homEnv, one_pow, one_mul]

end Chart

/-! ### Supports at a fixed view

A support polynomial is linear in the view vector, so on a chart box it is nonnegative if it is at
each corner of the view box for every rotation of the box (`exists_viewCorner_le`): three
variables instead of five, as the Rust check of centred supports does. -/

section Fixed

variable {κ : Type} [Add κ] [Sub κ] [Mul κ]

/-- A support polynomial at the view `U` on the rotation variables of a chart box: inputs
`0, 1, 2` are the rotation coordinates and input `3` the homogenising value. -/
def supportRotGen (U : V3 κ) (k : Fin 4) (c v w : V3 κ) (pre : Option (Q4 κ) := none) :
    GenPoly κ where
  run emb x := supportG emb (U.map emb) (preQ emb (homQuat k (x 3) ⟨x 0, x 1, x 2⟩) pre) c v w
  natural f hf emb x := by
    rw [map_supportG hf, map_preQ hf, map_homQuat]
    rfl

variable [Exact κ]

/-- The support polynomial at the view `U` at a rotation point `y` with homogenising value
`d`. -/
theorem supportRotGen_homEnv (U : V3 κ) (k : Fin 4) (c v w : V3 κ) (pre : Option (Q4 κ))
    (d : ℝ) (y : Fin 3 → ℝ) : (supportRotGen U k c v w pre).run Exact.re (homEnv 3 d y) =
      d ^ 2 * supportPoly (Exact.reV U) (preQuat (chartQuat k y) (Exact.rePre pre))
        (Exact.reV c) (Exact.reV v) (Exact.reV w) := by
  change supportG Exact.re (U.map Exact.re) (preQ Exact.re (homQuat k (homEnv 3 d y 3)
    ⟨homEnv 3 d y 0, homEnv 3 d y 1, homEnv 3 d y 2⟩) pre) c v w = _
  have hq : (homQuat k (homEnv 3 d y 3) ⟨homEnv 3 d y 0, homEnv 3 d y 1, homEnv 3 d y 2⟩).toFun =
      d • chartQuat k y := by
    simpa [homEnv] using toFun_homQuat k d y
  rw [supportG_re, toFun_preQ, hq, preQuat_smul, supportPoly_smul_quat]
  rfl

theorem supportRotGen_isHomogeneous (U : V3 κ) (k : Fin 4) (c v w : V3 κ)
    (pre : Option (Q4 κ)) : (supportRotGen U k c v w pre).IsHomogeneous 3 2 := fun d y ↦ by
  rw [supportRotGen_homEnv, supportRotGen_homEnv, one_pow, one_mul]

end Fixed

end Nieuwland.Check
