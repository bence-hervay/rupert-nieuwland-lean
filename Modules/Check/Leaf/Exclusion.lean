import Modules.Check.Leaf.Symmetry
import Modules.NoFit.Score

/-!
# Excluded leaves

An excluded leaf of a certificate (`Excluded` in `code/src/proof/cert.rs`) is a chart box on
which the pose map of two signed symmetries strictly increases the orbit score
(`Modules/NoFit/Score.lean`); symmetry exclusion then needs no `NoFit` claim there
(`Polyhedron.not_isRupert_of_excluded`).

**The improvement numerator.** For symmetries `g₁ / s₁`, `g₂ / s₂` with signs `σ₁`, `σ₂`, the
score `orbitScore a b w` and a pose `(u, R)` with `R = Q(q) / |q|²`, put `w₁ = g₁ᵀ w` and
`M = g₂ g₁`. Then

  `s₁² s₂ |u|² |w|² |q|² (f(g x) - f(x)) = a s₂ |q|² ((u ⬝ᵥ w₁)² - s₁² (u ⬝ᵥ w)²)`
  `    + b s₁ |w|² (|u|² (tr (M Q(q)) - s₁ s₂ tr Q(q)) - [σ₁ ≠ σ₂] 2 u ⬝ᵥ Q(q) M u)`

(`improvementPoly_eq`), a polynomial of degree `2` in `u` and `2` in `q`, so of degree `4` in
the homogeneous chart variables, with degree at most `2` in each box variable, like the balanced
witnesses. It is defined once, generically (`improvementG`, and `improvementGen` on chart boxes),
and its positivity on a box is certified by `posOn` (`code/src/proof/symmetry.rs` has the same
numerator times `|u|²` for a fold, of degree `(4, 2)`).

* `Improvement κ`: the exact data of the numerator; `Improvement.of` computes it from the score
  and two symmetries.
* `SymmData`: the symmetries and the score of a certificate, with the centre; `SymmData.ok`.
* `Excl.check`, `Excl.check_sound`: an excluded leaf, and every pose of its region is
  `Polyhedron.Excluded`.
-/

open Matrix

namespace Nieuwland.Check

/-! ### Quadratic forms on quaternions -/

/-- A quadratic form `∑_{i ≤ j} c_{ij} q_i q_j` on quaternions, by its coefficients. -/
structure QForm (κ : Type) where
  /-- The coefficient of `w²`. -/
  ww : κ
  /-- The coefficient of `w x`. -/
  wx : κ
  /-- The coefficient of `w y`. -/
  wy : κ
  /-- The coefficient of `w z`. -/
  wz : κ
  /-- The coefficient of `x²`. -/
  xx : κ
  /-- The coefficient of `x y`. -/
  xy : κ
  /-- The coefficient of `x z`. -/
  xz : κ
  /-- The coefficient of `y²`. -/
  yy : κ
  /-- The coefficient of `y z`. -/
  yz : κ
  /-- The coefficient of `z²`. -/
  zz : κ

namespace QForm

variable {κ : Type}

/-- The value at `Q`, in any type with `+` and `*`, with the coefficients embedded by `k`. -/
def evalG {α : Type*} [Add α] [Mul α] (k : κ → α) (K : QForm κ) (Q : Q4 α) : α :=
  Q.w * (k K.ww * Q.w + k K.wx * Q.x + k K.wy * Q.y + k K.wz * Q.z) +
    Q.x * (k K.xx * Q.x + k K.xy * Q.y + k K.xz * Q.z) +
    Q.y * (k K.yy * Q.y + k K.yz * Q.z) + Q.z * (k K.zz * Q.z)

theorem map_evalG {α β : Type*} [Add α] [Sub α] [Mul α] [Add β] [Sub β] [Mul β] {f : α → β}
    (hf : IsArith f) (k : κ → α) (K : QForm κ) (Q : Q4 α) :
    f (K.evalG k Q) = K.evalG (f ∘ k) (Q.map f) := by
  simp [evalG, Q4.map, hf.map_add, hf.map_mul]

variable [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The real value. -/
noncomputable def eval (K : QForm κ) (q : Fin 4 → ℝ) : ℝ :=
  K.evalG Exact.re (Q4.mk (q 0) (q 1) (q 2) (q 3))

theorem evalG_re (K : QForm κ) (Q : Q4 ℝ) : K.evalG Exact.re Q = K.eval Q.toFun := rfl

theorem eval_smul (K : QForm κ) (c : ℝ) (q : Fin 4 → ℝ) :
    K.eval (c • q) = c ^ 2 * K.eval q := by
  simp only [eval, evalG, Pi.smul_apply, smul_eq_mul]
  ring

/-- The form `q ↦ tr (M Q(q)) - e tr Q(q)`, for the quaternion matrix `Q(q)`. -/
def ofTrace (M : M3 κ) (e : κ) : QForm κ where
  ww := M.x.x + M.y.y + M.z.z - Exact.ofInt 3 * e
  wx := Exact.ofInt 2 * (M.y.z - M.z.y)
  wy := Exact.ofInt 2 * (M.z.x - M.x.z)
  wz := Exact.ofInt 2 * (M.x.y - M.y.x)
  xx := M.x.x - M.y.y - M.z.z + e
  xy := Exact.ofInt 2 * (M.x.y + M.y.x)
  xz := Exact.ofInt 2 * (M.x.z + M.z.x)
  yy := M.y.y - M.x.x - M.z.z + e
  yz := Exact.ofInt 2 * (M.y.z + M.z.y)
  zz := M.z.z - M.x.x - M.y.y + e

theorem eval_ofTrace (M : M3 κ) (e : κ) (q : Fin 4 → ℝ) :
    (ofTrace M e).eval q =
      trace (M.toMatrix * quatMatrix q) - Exact.re e * trace (quatMatrix q) := by
  simp [eval, evalG, ofTrace, trace, M3.toMatrix, quatMatrix, mul_apply, Fin.sum_univ_three,
    V3.get, Exact.re_add, Exact.re_sub, Exact.re_mul, Exact.re_ofInt]
  ring

end QForm

/-! ### The improvement numerator -/

/-- The orbit score `orbitScore a b w` with integer parameters. -/
structure Score where
  /-- The weight of the view term. -/
  a : ℤ
  /-- The weight of the rotation term. -/
  b : ℤ
  /-- The direction of the view term. -/
  w : V3 ℤ

/-- The score as a function of poses. -/
noncomputable def Score.f (F : Score) : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ → ℝ :=
  orbitScore F.a F.b (V3.cast ℝ F.w)

/-- The exact data of an improvement numerator (see the module docstring). -/
structure Improvement (κ : Type) where
  /-- `a s₂`. -/
  cv : κ
  /-- `w`. -/
  w : V3 κ
  /-- `w₁ = g₁ᵀ w`. -/
  w₁ : V3 κ
  /-- `s₁²`. -/
  ss : κ
  /-- `b s₁ |w|²`. -/
  cr : κ
  /-- `q ↦ tr (M Q(q)) - s₁ s₂ tr Q(q)`. -/
  K : QForm κ
  /-- Whether the map folds (`σ₁ ≠ σ₂`). -/
  fold : Bool
  /-- `M = g₂ g₁`. -/
  M : M3 κ

/-- The improvement data of the pose map of `S₁` and `S₂` for the score `F`. -/
def Improvement.of {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] (F : Score) (S₁ S₂ : Symm κ) :
    Improvement κ where
  cv := Exact.ofInt (F.a * S₂.den)
  w := F.w.map Exact.ofInt
  w₁ := S₁.g.transpose.mulVec (F.w.map Exact.ofInt)
  ss := Exact.ofInt (S₁.den * S₁.den)
  cr := Exact.ofInt (F.b * S₁.den * F.w.dot F.w)
  K := QForm.ofTrace (S₂.g.mul S₁.g) (Exact.ofInt (S₁.den * S₂.den))
  fold := S₁.sign != S₂.sign
  M := S₂.g.mul S₁.g

section Generic

variable {κ : Type} {α β : Type*} [Add α] [Sub α] [Mul α] [Add β] [Sub β] [Mul β]

/-- The improvement numerator at `(U, Q)`, in any type with `+`, `-` and `*`, with the exact
data embedded by `k`. -/
def improvementG (k : κ → α) (d : Improvement κ) (U : V3 α) (Q : Q4 α) : α :=
  let vw := U.dot (d.w.map k)
  let v₁ := U.dot (d.w₁.map k)
  let r := U.dot U * d.K.evalG k Q
  k d.cv * Q.norm2 * (v₁ * v₁ - k d.ss * (vw * vw)) +
    k d.cr * bif d.fold then
      (let t := U.dot (Q.rotate (d.M.mulVecG k U)); r - (t + t)) else r

theorem map_improvementG {f : α → β} (hf : IsArith f) (k : κ → α) (d : Improvement κ)
    (U : V3 α) (Q : Q4 α) :
    f (improvementG k d U Q) = improvementG (f ∘ k) d (U.map f) (Q.map f) := by
  cases hfold : d.fold <;>
    simp only [improvementG, hfold, Bool.cond_false, Bool.cond_true, hf.map_add, hf.map_sub,
      hf.map_mul,
      V3.map_dot hf, Q4.map_norm2 hf, QForm.map_evalG hf, Q4.map_rotate hf, M3.map_mulVecG hf,
      V3.map_map] <;> rfl

end Generic

section Real

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The improvement numerator as a real function (`improvementG_re`). -/
noncomputable def improvementPoly (d : Improvement κ) (u : Fin 3 → ℝ) (q : Fin 4 → ℝ) : ℝ :=
  Exact.re d.cv * (q ⬝ᵥ q) *
      ((u ⬝ᵥ Exact.reV d.w₁) ^ 2 - Exact.re d.ss * (u ⬝ᵥ Exact.reV d.w) ^ 2) +
    Exact.re d.cr * ((u ⬝ᵥ u) * d.K.eval q -
      bif d.fold then 2 * (u ⬝ᵥ (quatMatrix q *ᵥ (d.M.toMatrix *ᵥ u))) else 0)

theorem improvementG_re (d : Improvement κ) (U : V3 ℝ) (Q : Q4 ℝ) :
    improvementG Exact.re d U Q = improvementPoly d U.toFun Q.toFun := by
  have hU : U.dot U = U.toFun ⬝ᵥ U.toFun := V3.dot_eq_dotProduct U U
  cases hfold : d.fold <;>
    simp only [improvementG, improvementPoly, hfold, Bool.cond_false, Bool.cond_true,
      V3.dot_eq_dotProduct,
      Q4.norm2_eq_dotProduct, QForm.evalG_re, Q4.toFun_rotate, M3.toFun_mulVecG] <;>
    simp only [Exact.reV] <;> ring

theorem improvementPoly_smul (d : Improvement κ) (c : ℝ) (u : Fin 3 → ℝ) (q : Fin 4 → ℝ) :
    improvementPoly d (c • u) (c • q) = c ^ 4 * improvementPoly d u q := by
  cases hfold : d.fold <;>
    simp only [improvementPoly, hfold, Bool.cond_false, Bool.cond_true, QForm.eval_smul,
      smul_dotProduct,
      dotProduct_smul, smul_eq_mul, quatMatrix_smul, mulVec_smul, smul_mulVec] <;> ring

/-- The improvement numerator has degree `2` in the view vector and `2` in the quaternion. -/
theorem improvementPoly_smul₂ (d : Improvement κ) (a b : ℝ) (u : Fin 3 → ℝ) (q : Fin 4 → ℝ) :
    improvementPoly d (a • u) (b • q) = a ^ 2 * b ^ 2 * improvementPoly d u q := by
  cases hfold : d.fold <;>
    simp only [improvementPoly, hfold, Bool.cond_false, Bool.cond_true, QForm.eval_smul,
      smul_dotProduct,
      dotProduct_smul, smul_eq_mul, quatMatrix_smul, mulVec_smul, smul_mulVec] <;> ring

end Real

section Meaning

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]
variable {pts : List (V3 κ)} {C : V3 κ} {m : ℕ} {F : Score} {S₁ S₂ : Symm κ}

/-- **The improvement numerator** is a positive multiple of the improvement of the score. -/
theorem improvementPoly_eq (h₁ : S₁.ok pts C m = true) (h₂ : S₂.ok pts C m = true)
    (hw : F.w.dot F.w ≠ 0) {u : Fin 3 → ℝ} (hu : u ≠ 0) {q : Fin 4 → ℝ} (hq : q ≠ 0) :
    improvementPoly (Improvement.of F S₁ S₂) u q =
      (S₁.den : ℝ) ^ 2 * S₂.den * (u ⬝ᵥ u) * (V3.cast ℝ F.w ⬝ᵥ V3.cast ℝ F.w) * (q ⬝ᵥ q) *
        (F.f (S₁.rot *ᵥ u) (turn (S₁.sign * S₂.sign) (S₁.rot *ᵥ u) * S₁.rot * quatRotation q *
          S₂.rot) - F.f u (quatRotation q)) := by
  set w := V3.cast ℝ F.w with hwdef
  have hw' : w ≠ 0 := fun h0 ↦ hw (by
    have : ((F.w.dot F.w : ℤ) : ℝ) = w ⬝ᵥ w := V3.cast_dot _ _
    rw [h0, dotProduct_zero] at this
    exact_mod_cast this)
  have hA := Symm.transpose_rot_mul_of_ok h₁
  have hs₁ : (S₁.den : ℝ) ≠ 0 := by exact_mod_cast (Symm.den_pos_of_ok h₁).ne'
  have hs₂ : (S₂.den : ℝ) ≠ 0 := by exact_mod_cast (Symm.den_pos_of_ok h₂).ne'
  have hqq : q ⬝ᵥ q ≠ 0 := dotProduct_self_eq_zero.not.mpr hq
  have huu : u ⬝ᵥ u ≠ 0 := dotProduct_self_eq_zero.not.mpr hu
  have hww : w ⬝ᵥ w ≠ 0 := dotProduct_self_eq_zero.not.mpr hw'
  have hAw : u ⬝ᵥ (S₁.rotᵀ *ᵥ w) = (S₁.sign : ℝ) / S₁.den *
      (u ⬝ᵥ Exact.reV (S₁.g.transpose.mulVec (F.w.map (Exact.ofInt : ℤ → κ)))) := by
    rw [Symm.rot, transpose_smul, smul_mulVec, dotProduct_smul, smul_eq_mul, ← M3.toMatrix_mulVec,
      M3.toMatrix_transpose, Exact.reV_map_ofInt]
  have hBA : S₂.rot * S₁.rot =
      ((S₂.sign : ℝ) / S₂.den * (S₁.sign / S₁.den)) • (S₂.g.mul S₁.g).toMatrix := by
    rw [Symm.rot, Symm.rot, smul_mul_smul_comm, M3.toMatrix_mul]
  have hR : quatRotation q = (q ⬝ᵥ q)⁻¹ • quatMatrix q := rfl
  have htr : trace (S₂.rot * S₁.rot * quatRotation q) = (S₂.sign : ℝ) / S₂.den *
      (S₁.sign / S₁.den) * (q ⬝ᵥ q)⁻¹ * trace ((S₂.g.mul S₁.g).toMatrix * quatMatrix q) := by
    rw [hBA, hR, smul_mul_smul_comm, trace_smul, smul_eq_mul]
  have htrR : trace (quatRotation q) = (q ⬝ᵥ q)⁻¹ * trace (quatMatrix q) := by
    rw [hR, trace_smul, smul_eq_mul]
  have hfold : u ⬝ᵥ (quatRotation q *ᵥ ((S₂.rot * S₁.rot) *ᵥ u)) = (S₂.sign : ℝ) / S₂.den *
      (S₁.sign / S₁.den) * (q ⬝ᵥ q)⁻¹ *
        (u ⬝ᵥ (quatMatrix q *ᵥ ((S₂.g.mul S₁.g).toMatrix *ᵥ u))) := by
    rw [hBA, hR, smul_mulVec, smul_mulVec, mulVec_smul, dotProduct_smul, dotProduct_smul,
      smul_eq_mul, smul_eq_mul]
    ring
  have hK := QForm.eval_ofTrace (S₂.g.mul S₁.g) (Exact.ofInt (S₁.den * S₂.den) : κ) q
  have hcase : ((S₁.sign : ℝ) * S₂.sign = 1 ∧ (S₁.sign != S₂.sign) = false) ∨
      ((S₁.sign : ℝ) * S₂.sign = -1 ∧ (S₁.sign != S₂.sign) = true) := by
    rcases S₁.sign_eq with e₁ | e₁ <;> rcases S₂.sign_eq with e₂ | e₂ <;> simp [e₁, e₂]
  have key : (u ⬝ᵥ u) * (w ⬝ᵥ w) * (F.f (S₁.rot *ᵥ u) (turn (S₁.sign * S₂.sign) (S₁.rot *ᵥ u) *
      S₁.rot * quatRotation q * S₂.rot) - F.f u (quatRotation q)) =
      F.a * ((u ⬝ᵥ (S₁.rotᵀ *ᵥ w)) ^ 2 - (u ⬝ᵥ w) ^ 2) + F.b * (w ⬝ᵥ w) *
        ((u ⬝ᵥ u) * (trace (S₂.rot * S₁.rot * quatRotation q) - trace (quatRotation q)) -
          bif S₁.sign != S₂.sign then 2 * ((u ⬝ᵥ u) * trace (S₂.rot * S₁.rot * quatRotation q) -
            u ⬝ᵥ (quatRotation q *ᵥ ((S₂.rot * S₁.rot) *ᵥ u))) else 0) := by
    rcases hcase with ⟨ht, hb⟩ | ⟨ht, hb⟩
    · rw [ht, hb, Bool.cond_false, Score.f, orbitScore_map_sub_one hA _ _ hw' hu]
      ring
    · rw [ht, hb, Bool.cond_true, Score.f, orbitScore_map_sub_neg_one hA _ _ hw' hu]
      ring
  have hrhs : (S₁.den : ℝ) ^ 2 * S₂.den * (u ⬝ᵥ u) * (w ⬝ᵥ w) * (q ⬝ᵥ q) *
      (F.f (S₁.rot *ᵥ u) (turn (S₁.sign * S₂.sign) (S₁.rot *ᵥ u) * S₁.rot * quatRotation q *
        S₂.rot) - F.f u (quatRotation q)) =
      (S₁.den : ℝ) ^ 2 * S₂.den * (q ⬝ᵥ q) * ((u ⬝ᵥ u) * (w ⬝ᵥ w) *
        (F.f (S₁.rot *ᵥ u) (turn (S₁.sign * S₂.sign) (S₁.rot *ᵥ u) * S₁.rot * quatRotation q *
          S₂.rot) - F.f u (quatRotation q))) := by ring
  have hww' : ((F.w.dot F.w : ℤ) : ℝ) = w ⬝ᵥ w := V3.cast_dot _ _
  rw [hrhs, key, hAw, htr, htrR, hfold]
  simp only [improvementPoly, Improvement.of, hK, Exact.re_ofInt, Exact.reV_map_ofInt, ← hwdef]
  push_cast
  rw [hww']
  rcases S₁.sign_eq with e₁ | e₁ <;> rcases S₂.sign_eq with e₂ | e₂ <;>
    simp only [e₁, e₂] <;> norm_num <;> field_simp <;> ring

end Meaning

/-! ### Improvement numerators on chart boxes -/

section Gen

variable {κ : Type} [Add κ] [Sub κ] [Mul κ]

/-- The improvement numerator on the variables of a chart box (view `S, T` in `0, 1`, rotation
`X` in `2, 3, 4`, `D` in `5`), as a generic computation. -/
def improvementGen (d : Improvement κ) (a : Fin 3) (k : Fin 4) : GenPoly κ where
  run emb x := improvementG emb d (homView a (x 5) (x 0) (x 1)) (homQuat k (x 5) ⟨x 2, x 3, x 4⟩)
  natural f hf emb x := by
    rw [map_improvementG hf, map_homView, map_homQuat]
    rfl

variable [Exact κ]

/-- The improvement numerator at a box point `y` with homogenising value `c`. -/
theorem improvementGen_homEnv (d : Improvement κ) (a : Fin 3) (k : Fin 4) (c : ℝ)
    (y : Fin 5 → ℝ) :
    (improvementGen d a k).run Exact.re (homEnv 5 c y) =
      c ^ 4 * improvementPoly d (viewDir a (y 0) (y 1)) (chartQuat k (rotCoords y)) := by
  change improvementG Exact.re d (homView a (homEnv 5 c y 5) (homEnv 5 c y 0) (homEnv 5 c y 1))
    (homQuat k (homEnv 5 c y 5) ⟨homEnv 5 c y 2, homEnv 5 c y 3, homEnv 5 c y 4⟩) = _
  rw [improvementG_re, toFun_homView_homEnv, toFun_homQuat_homEnv, improvementPoly_smul]

theorem improvementGen_isHomogeneous (d : Improvement κ) (a : Fin 3) (k : Fin 4) :
    (improvementGen d a k).IsHomogeneous 5 4 := fun c y ↦ by
  rw [improvementGen_homEnv, improvementGen_homEnv, one_pow, one_mul]

end Gen

/-! ### Excluded leaves -/

/-- The symmetry data of a certificate: signed symmetries about the centre `C / m`, and the
score. -/
structure SymmData (κ : Type) where
  /-- The numerator of the centre. -/
  C : V3 κ
  /-- The denominator of the centre. -/
  m : ℕ
  /-- The symmetries. -/
  syms : List (Symm κ)
  /-- The score. -/
  score : Score

namespace SymmData

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The centre `C / m`. -/
noncomputable def centre (D : SymmData κ) : Fin 3 → ℝ :=
  (D.m : ℝ)⁻¹ • Exact.reV D.C

/-- Every symmetry checks, and the direction of the score is not zero. -/
def ok (pts : List (V3 κ)) (D : SymmData κ) : Bool :=
  D.syms.all (Symm.ok pts D.C D.m) && D.score.w.dot D.score.w != 0

/-- `SymmData.ok` from the checks of the symmetries, which exported data proves one declaration
each (`allCons`), so that the kernel's cache holds one symmetry at a time. -/
theorem ok_of_all {pts : List (V3 κ)} {D : SymmData κ}
    (h : D.syms.all (Symm.ok pts D.C D.m) = true) (hw : (D.score.w.dot D.score.w != 0) = true) :
    D.ok pts = true := by
  simp only [ok, h, hw, Bool.and_self]

end SymmData

/-- `(a :: l).all f` from `f a` and `l.all f`. -/
theorem allCons {α : Type} {f : α → Bool} {a : α} {l : List α} (h₁ : f a = true)
    (h₂ : l.all f = true) : (a :: l).all f = true := by
  simp only [List.all_cons, h₁, h₂, Bool.and_self]

/-- An excluded leaf (`Excluded` in `cert.rs`): on the chart box `region`, the pose map of the
symmetries `i` and `j` increases the score. -/
structure Excl where
  /-- The region. -/
  region : ChartBox
  /-- The index of the first symmetry (acting on the view and from the left). -/
  i : ℕ
  /-- The index of the second symmetry (acting on the inner copy). -/
  j : ℕ

namespace Excl

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The check of an excluded leaf, bisecting at most `depth` times along each branch. -/
def check (D : SymmData κ) (depth : ℕ) (e : Excl) : Bool :=
  match D.syms[e.i]?, D.syms[e.j]? with
  | some S₁, some S₂ => decide (0 < e.region.box.den) &&
      posOn (improvementGen (Improvement.of D.score S₁ S₂) e.region.view e.region.rot) 5 depth
        e.region.box true
  | _, _ => false

/-- **Soundness of excluded leaves.** -/
theorem check_sound {pts : List (V3 κ)} {D : SymmData κ} {depth : ℕ} {e : Excl}
    (hD : D.ok pts = true) (h : e.check D depth = true) :
    ∀ p ∈ e.region.poses, (Polyhedron.ofPoints pts).Excluded D.centre D.score.f p := by
  simp only [SymmData.ok, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at hD
  unfold check at h
  split at h
  next S₁ S₂ hS₁ hS₂ =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hden, hpos⟩ := h
    have h₁ := hD.1 S₁ (List.mem_of_getElem? hS₁)
    have h₂ := hD.1 S₂ (List.mem_of_getElem? hS₂)
    rintro p ⟨hview, hrot, hy⟩
    set y := p.coords
    have hu : viewDir p.view p.s p.t = viewDir e.region.view (y 0) (y 1) := by rw [hview]; rfl
    have hR : p.rotation = quatRotation (chartQuat e.region.rot (rotCoords y)) := by
      rw [ChartPose.rotation, hrot, rotCoords_coords]
      rfl
    have h0 := posOn_hom (improvementGen_isHomogeneous _ _ _) hden hpos hy
    rw [improvementGen_homEnv, one_pow, one_mul,
      improvementPoly_eq h₁ h₂ hD.2 (viewDir_ne_zero _ _ _) (chartQuat_ne_zero _ _)] at h0
    have hdot (v : Fin 3 → ℝ) : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _
    have hlt := pos_of_mul_pos_right h0 (mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (hdot _)) (hdot _)) (Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _))
    exact ⟨S₁.rot, S₁.sign, S₂.rot, S₂.sign, Symm.ok_sound h₁, Symm.ok_sound h₂, by
      rw [hu, hR]
      exact sub_pos.mp hlt⟩
  next => exact absurd h (by simp)

end Excl

end Nieuwland.Check
