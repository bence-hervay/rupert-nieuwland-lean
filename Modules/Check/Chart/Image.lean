import Modules.Check.Leaf.Null
import Modules.NoFit.Pre

/-!
# Images of chart boxes under pose maps

Mapped leaves and chart changes of certificates (`check_image_into` in
`code/src/proof/symmetry.rs`) send every pose of a chart box `src` into a chart box `dst`: with the
pose map of two signed symmetries, or with the identity for a chart change. Both boxes may be
pre-rotated (`Modules/NoFit/Pre.lean`), by `q_c` and `q_c'`.

**Pose maps** (`PMap`, `PoseMap` in `geometry/symmetry.rs`). Symmetries with rotations `A`, `B`
and signs `σ`, `τ` act on representatives by `(u, q) ↦ (A u, [(0, A u)] p₁ q p₂)`, with
quaternions `p₁`, `p₂` of `A` and `B`, and the bracket for a fold, `σ ≠ τ`. The rotation of the
image is `turn (σ τ) (A u) A R(q) B` (`PMap.Acts.quatRotation_imgQ`), the image of `FitsAlong.symm`.
Lean computes `pᵢ` from the matrices of the symmetry data as Rust does (`Symm.quat`) and checks
`den Q(p) = |p|² sign g` exactly (`Symm.quatOk`). The exact data hold a nonzero multiple `M` of
`A`; images only matter up to scale.

**Images on a box.** On the homogeneous variables of `src`, the image view is `V = M u` and the
image quaternion `Q₂` that of `q(x) q_c`; in the charts of `dst`, the chart quaternion is
`Y = Q₂ conj(q_c')`, since `Y q_c' = |q_c'|² Q₂` has the rotation of `Q₂`. The chart coordinates of
the image are ratios: `V (a + 1) / V a`, `V (a + 2) / V a` and `Y (k.succAbove i) / Y k`
(`coordND`). `imgGen` gives `σ (c₁ num - c₂ den)` for a coordinate as a computation, homogeneous of
degree `1`, or `2` for the rotation of a fold.

**The check** (`Image.check`): on `src`, both denominators have a strict sign `σ`, and
`σ (D num - lo den) ≥ 0` and `σ (hi den - D num) ≥ 0` for each coordinate, with the bounds
`lo / D`, `hi / D` of `dst`. Then every pose of `src` has an image pose in `dst`
(`Image.check_sound`, `Image.rotation_eq`), and

* for the pose map of symmetries `i`, `j` of the symmetry data (`SymmData.pmap`), no fit on
  `dst` with its pre-rotation gives no fit on `src` with its pre-rotation
  (`Image.noFitRot_of_check`): mapped leaves;
* for the identity, a settled pose of `dst` gives a settled pose of `src`
  (`Image.settledRot_of_check`): chart changes.
-/

open Matrix

namespace Nieuwland.Check

/-! ### Exact quaternions of symmetries -/

namespace Q4

/-- The pure quaternion `(z, V)`, with `z` standing for `0`. -/
def pure {α : Type} (z : α) (V : V3 α) : Q4 α :=
  ⟨z, V.x, V.y, V.z⟩

theorem map_pure {α β : Type} (f : α → β) (z : α) (V : V3 α) :
    (pure z V).map f = pure (f z) (V.map f) :=
  rfl

variable {α : Type} [Add α] [Sub α] [Mul α]

/-- The matrix `Q(q)` (`quatMatrix`), by rows; twice a value is a sum. -/
def mat (q : Q4 α) : M3 α :=
  ⟨⟨q.w * q.w + q.x * q.x - q.y * q.y - q.z * q.z,
      (q.x * q.y - q.w * q.z) + (q.x * q.y - q.w * q.z),
      (q.x * q.z + q.w * q.y) + (q.x * q.z + q.w * q.y)⟩,
    ⟨(q.x * q.y + q.w * q.z) + (q.x * q.y + q.w * q.z),
      q.w * q.w - q.x * q.x + q.y * q.y - q.z * q.z,
      (q.y * q.z - q.w * q.x) + (q.y * q.z - q.w * q.x)⟩,
    ⟨(q.x * q.z - q.w * q.y) + (q.x * q.z - q.w * q.y),
      (q.y * q.z + q.w * q.x) + (q.y * q.z + q.w * q.x),
      q.w * q.w - q.x * q.x - q.y * q.y + q.z * q.z⟩⟩

end Q4

namespace M3

variable {κ : Type} [Add κ] [Sub κ] [Mul κ]

/-- `c G`. -/
def smul (c : κ) (G : M3 κ) : M3 κ :=
  ⟨V3.smul c G.x, V3.smul c G.y, V3.smul c G.z⟩

variable [Exact κ]

theorem toMatrix_smul (c : κ) (G : M3 κ) : (smul c G).toMatrix = Exact.re c • G.toMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [smul, toMatrix, V3.smul, V3.get, Exact.re_mul]

theorem toMatrix_mat (q : Q4 κ) : q.mat.toMatrix = quatMatrix (Exact.reQ q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Q4.mat, toMatrix, quatMatrix, Exact.reQ, Q4.map, Q4.toFun, V3.get, Exact.re_add,
      Exact.re_sub, Exact.re_mul] <;> ring

end M3

namespace Exact

variable {α : Type} [Add α] [Sub α] [Mul α] [Exact α]

/-- The conjugate `(w, -x, -y, -z)` of an exact quaternion. -/
def conjQ (q : Q4 α) : Q4 α :=
  ⟨q.w, ofInt 0 - q.x, ofInt 0 - q.y, ofInt 0 - q.z⟩

theorem reQ_conjQ (q : Q4 α) : reQ (conjQ q) = qconj (reQ q) := by
  funext i
  fin_cases i <;> simp [reQ, conjQ, qconj, Q4.map, Q4.toFun, re_sub, re_ofInt]

/-- Two pre-rotations are known to be equal: both absent, or equal coordinates by the zero
test. -/
def preEq : Option (Q4 α) → Option (Q4 α) → Bool
  | none, none => true
  | some c, some c' =>
    isZero (c.w - c'.w) && isZero (c.x - c'.x) && isZero (c.y - c'.y) && isZero (c.z - c'.z)
  | _, _ => false

theorem rePre_eq_of_preEq : ∀ {a b : Option (Q4 α)}, preEq a b = true → rePre a = rePre b
  | none, none, _ => rfl
  | some c, some c', h => by
    simp only [preEq, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hw, hx⟩, hy⟩, hz⟩ := h
    have e (a b : α) (h : isZero (a - b) = true) : re a = re b := by
      have := isZero_sound _ h
      rw [re_sub, sub_eq_zero] at this
      exact this
    simp only [rePre, Option.map_some, Option.some.injEq]
    funext i
    fin_cases i
    · exact e _ _ hw
    · exact e _ _ hx
    · exact e _ _ hy
    · exact e _ _ hz
  | none, some _, h => by simp [preEq] at h
  | some _, none, h => by simp [preEq] at h

end Exact

namespace Symm

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The numerator `sign · g` of the rotation `Symm.rot = sign · g / den`. -/
def num (S : Symm κ) : M3 κ :=
  M3.smul (Exact.ofInt S.sign) S.g

/-- A quaternion of the rotation `num / den`: the first of the four rows of the `rotQuat`
formula, scaled by `den`, whose diagonal entry is not zero (`rotation_quat` in
`geometry/symmetry.rs`). `quatOk` checks it. -/
def quat (S : Symm κ) : Q4 κ :=
  let M := S.num
  let D : κ := Exact.ofInt S.den
  let r₀ : Q4 κ := ⟨D + M.x.x + M.y.y + M.z.z, M.z.y - M.y.z, M.x.z - M.z.x, M.y.x - M.x.y⟩
  let r₁ : Q4 κ := ⟨M.z.y - M.y.z, D + M.x.x - M.y.y - M.z.z, M.x.y + M.y.x, M.x.z + M.z.x⟩
  let r₂ : Q4 κ := ⟨M.x.z - M.z.x, M.x.y + M.y.x, D - M.x.x + M.y.y - M.z.z, M.y.z + M.z.y⟩
  let r₃ : Q4 κ := ⟨M.y.x - M.x.y, M.x.z + M.z.x, M.y.z + M.z.y, D - M.x.x - M.y.y + M.z.z⟩
  if Exact.nonzero r₀.w then r₀ else if Exact.nonzero r₁.x then r₁
  else if Exact.nonzero r₂.y then r₂ else r₃

/-- `Q(p) / |p|² = num / den` for the quaternion `p = quat`: `|p|² > 0` and
`den Q(p) = |p|² num`, exactly. -/
def quatOk (S : Symm κ) : Bool :=
  Exact.pos S.quat.norm2 &&
    (M3.smul (Exact.ofInt S.den) S.quat.mat).eqb (M3.smul S.quat.norm2 S.num)

variable {pts : List (V3 κ)} {C : V3 κ} {m : ℕ} {S : Symm κ}

theorem toMatrix_num (h : S.ok pts C m = true) : S.num.toMatrix = (S.den : ℝ) • S.rot := by
  have hd : (S.den : ℝ) ≠ 0 := by exact_mod_cast (den_pos_of_ok h).ne'
  rw [num, M3.toMatrix_smul, Exact.re_ofInt, rot, smul_smul, mul_div_cancel₀ _ hd]

theorem reQ_quat_ne_zero (h : S.quatOk = true) : Exact.reQ S.quat ≠ 0 := by
  simp only [quatOk, Bool.and_eq_true] at h
  intro h0
  have hpos := Exact.pos_sound _ h.1
  rw [Exact.re_norm2, ← Exact.reQ, h0, dotProduct_zero] at hpos
  exact lt_irrefl _ hpos

/-- **The quaternion of a symmetry.** -/
theorem quatRotation_quat (hS : S.ok pts C m = true) (h : S.quatOk = true) :
    quatRotation (Exact.reQ S.quat) = S.rot := by
  have hd : (S.den : ℝ) ≠ 0 := by exact_mod_cast (den_pos_of_ok hS).ne'
  have hne := reQ_quat_ne_zero h
  simp only [quatOk, Bool.and_eq_true] at h
  have he := M3.toMatrix_eq_of_eqb h.2
  rw [M3.toMatrix_smul, M3.toMatrix_smul, M3.toMatrix_mat, Exact.re_ofInt, toMatrix_num hS,
    Exact.re_norm2, ← Exact.reQ, smul_smul] at he
  refine quatRotation_eq_of (dotProduct_self_eq_zero.not.mpr hne) rfl ?_
  simp only [Int.cast_natCast] at he
  have h2 : ((S.den : ℝ)⁻¹ * S.den) • quatMatrix (Exact.reQ S.quat) =
      ((S.den : ℝ)⁻¹ * ((Exact.reQ S.quat ⬝ᵥ Exact.reQ S.quat) * S.den)) • S.rot := by
    rw [← smul_smul, he, smul_smul]
  rwa [inv_mul_cancel₀ hd, one_smul, mul_comm, mul_assoc, mul_inv_cancel₀ hd, mul_one] at h2

end Symm

/-! ### Pose maps -/

/-- The exact data of a pose map `(u, q) ↦ (A u, [(0, A u)] p₁ q p₂)` (`PoseMap` in
`geometry/symmetry.rs`): a nonzero multiple `M` of `A`, the quaternions `p₁`, `p₂`, and whether it
folds (the bracket). -/
structure PMap (κ : Type) where
  /-- A nonzero multiple of the view rotation `A`. -/
  M : M3 κ
  /-- A quaternion of `A`. -/
  p₁ : Q4 κ
  /-- A quaternion of the rotation `B` of the inner copy. -/
  p₂ : Q4 κ
  /-- A half-turn about the image view follows. -/
  fold : Bool

namespace PMap

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The identity, for chart changes. -/
def id : PMap κ :=
  ⟨M3.scalar 1, ⟨Exact.ofInt 1, Exact.ofInt 0, Exact.ofInt 0, Exact.ofInt 0⟩,
    ⟨Exact.ofInt 1, Exact.ofInt 0, Exact.ofInt 0, Exact.ofInt 0⟩, false⟩

/-- The pose map of the signed symmetries `S₁`, `S₂`: it folds when their signs differ. -/
def ofSymm (S₁ S₂ : Symm κ) : PMap κ :=
  ⟨S₁.num, S₁.quat, S₂.quat, S₁.sign != S₂.sign⟩

/-- The image `[(0, M u)] p₁ q p₂` of the representatives `u`, `q`. -/
noncomputable def imgQ (P : PMap κ) (u : Fin 3 → ℝ) (q : Fin 4 → ℝ) : Fin 4 → ℝ :=
  if P.fold then qmul (pureQ (P.M.toMatrix *ᵥ u)) (qmul (qmul (Exact.reQ P.p₁) q) (Exact.reQ P.p₂))
  else qmul (qmul (Exact.reQ P.p₁) q) (Exact.reQ P.p₂)

/-- The degree of the image quaternion in the representatives. -/
def deg (P : PMap κ) : ℕ :=
  if P.fold then 2 else 1

theorem imgQ_smul (P : PMap κ) (d : ℝ) (u : Fin 3 → ℝ) (q : Fin 4 → ℝ) :
    P.imgQ (d • u) (d • q) = d ^ P.deg • P.imgQ u q := by
  unfold imgQ deg
  rw [qmul_smul_right, qmul_smul_left]
  split_ifs
  · rw [mulVec_smul, pureQ_smul, qmul_smul_left, qmul_smul_right, smul_smul, sq]
  · rw [pow_one]

/-- The pose map acts by the rotations `A`, `B` with the signs `σ`, `τ`. -/
structure Acts (P : PMap κ) (A B : Matrix (Fin 3) (Fin 3) ℝ) (σ τ : ℝ) : Prop where
  mul : ∃ μ : ℝ, μ ≠ 0 ∧ P.M.toMatrix = μ • A
  rot₁ : quatRotation (Exact.reQ P.p₁) = A
  rot₂ : quatRotation (Exact.reQ P.p₂) = B
  fold : P.fold = true ↔ σ * τ = -1

theorem Acts.quatRotation_imgQ {P : PMap κ} {A B : Matrix (Fin 3) (Fin 3) ℝ} {σ τ : ℝ}
    (hP : P.Acts A B σ τ) (hA : A ∈ SO(3)) (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1)
    {u : Fin 3 → ℝ} (hu : u ≠ 0) (q : Fin 4 → ℝ) :
    quatRotation (P.imgQ u q) = turn (σ * τ) (A *ᵥ u) * A * quatRotation q * B := by
  obtain ⟨μ, hμ, hM⟩ := hP.mul
  have hprod : quatRotation (qmul (qmul (Exact.reQ P.p₁) q) (Exact.reQ P.p₂)) =
      A * quatRotation q * B := by
    rw [quatRotation_qmul, quatRotation_qmul, hP.rot₁, hP.rot₂]
  unfold imgQ
  split_ifs with hf
  · have hst := hP.fold.mp hf
    have hAu : A *ᵥ u ≠ 0 := Polyhedron.mulVec_ne_zero_of_mem_SO3 hA hu
    rw [quatRotation_qmul, hprod, hM, smul_mulVec, quatRotation_pureQ (smul_ne_zero hμ hAu),
      halfTurn_smul hμ, hst, turn_neg_one, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  · have hst : σ * τ = 1 := by
      rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> norm_num at hf ⊢ <;>
        exact absurd (hP.fold.mpr (by norm_num)) (by simp [hf])
    rw [hprod, hst, turn_one, Matrix.one_mul]

theorem id_acts : (id : PMap κ).Acts 1 1 1 1 := by
  have hq : quatRotation (Exact.reQ (⟨Exact.ofInt 1, Exact.ofInt 0, Exact.ofInt 0,
      Exact.ofInt 0⟩ : Q4 κ)) = 1 := by
    refine quatRotation_eq_of one_ne_zero ?_ ?_
    · simp [Exact.reQ, Q4.map, Q4.toFun, Exact.re_ofInt, dotProduct, Fin.sum_univ_four]
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Exact.reQ, Q4.map, Q4.toFun, Exact.re_ofInt, quatMatrix]
  exact ⟨⟨1, one_ne_zero, by rw [id, M3.toMatrix_scalar]; simp⟩, hq, hq, by norm_num [id]⟩

theorem ofSymm_acts {pts : List (V3 κ)} {C : V3 κ} {m : ℕ} {S₁ S₂ : Symm κ}
    (h₁ : S₁.ok pts C m = true) (h₂ : S₂.ok pts C m = true) (hq₁ : S₁.quatOk = true)
    (hq₂ : S₂.quatOk = true) : (ofSymm S₁ S₂).Acts S₁.rot S₂.rot S₁.sign S₂.sign := by
  refine ⟨⟨S₁.den, by exact_mod_cast (Symm.den_pos_of_ok h₁).ne', Symm.toMatrix_num h₁⟩,
    Symm.quatRotation_quat h₁ hq₁, Symm.quatRotation_quat h₂ hq₂, ?_⟩
  simp only [ofSymm, bne_iff_ne, ne_eq]
  rcases S₁.sign_eq with h | h <;> rcases S₂.sign_eq with h' | h' <;> simp [h, h'] <;> norm_num

/-- **Pose maps send fits to fits**, with pre-rotations: a fit along `u` with the rotation `R(q)`
gives a fit along `A u` with the rotation of the image quaternion. -/
theorem Acts.fitsAlong {pts : List (V3 κ)} {c : Fin 3 → ℝ} {P : PMap κ}
    {A B : Matrix (Fin 3) (Fin 3) ℝ} {σ τ : ℝ} (hP : P.Acts A B σ τ)
    (hA : (Polyhedron.ofPoints pts).IsSignedSymm c A σ)
    (hB : (Polyhedron.ofPoints pts).IsSignedSymm c B τ) {u : Fin 3 → ℝ} (hu : u ≠ 0)
    {q : Fin 4 → ℝ} (h : (Polyhedron.ofPoints pts).FitsAlong u (quatRotation q)) :
    (Polyhedron.ofPoints pts).FitsAlong (A *ᵥ u) (quatRotation (P.imgQ u q)) := by
  rw [hP.quatRotation_imgQ hA.1 hA.2.1 hB.2.1 hu]
  exact h.symm hA hB

end PMap

/-- The pose map of the symmetries `i` and `j` of `D`, whose quaternions check. -/
def SymmData.pmap {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] (D : SymmData κ) (i j : ℕ) :
    Option (PMap κ) :=
  match D.syms[i]?, D.syms[j]? with
  | some S₁, some S₂ => if S₁.quatOk && S₂.quatOk then some (PMap.ofSymm S₁ S₂) else none
  | _, _ => none

theorem SymmData.exists_acts_of_pmap {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]
    {pts : List (V3 κ)} {D : SymmData κ} (hD : D.ok pts = true) {i j : ℕ} {P : PMap κ}
    (h : D.pmap i j = some P) :
    ∃ A σ B τ, P.Acts A B σ τ ∧ (Polyhedron.ofPoints pts).IsSignedSymm D.centre A σ ∧
      (Polyhedron.ofPoints pts).IsSignedSymm D.centre B τ := by
  simp only [SymmData.ok, Bool.and_eq_true, List.all_eq_true] at hD
  unfold pmap at h
  split at h
  next S₁ S₂ hS₁ hS₂ =>
    split_ifs at h with hq
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true] at hq
    have h₁ := hD.1 S₁ (List.mem_of_getElem? hS₁)
    have h₂ := hD.1 S₂ (List.mem_of_getElem? hS₂)
    exact ⟨S₁.rot, S₁.sign, S₂.rot, S₂.sign, PMap.ofSymm_acts h₁ h₂ hq.1 hq.2,
      Symm.ok_sound h₁, Symm.ok_sound h₂⟩
  next => simp at h

/-! ### Images on boxes -/

theorem V3.get_map {α β : Type*} (f : α → β) (v : V3 α) (i : Fin 3) :
    (v.map f).get i = f (v.get i) := by
  fin_cases i <;> rfl

theorem Q4.toFun_map {α β : Type*} (f : α → β) (q : Q4 α) (i : Fin 4) :
    (q.map f).toFun i = f (q.toFun i) := by
  fin_cases i <;> rfl

section Gen

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]
variable {α β : Type} [Add α] [Sub α] [Mul α] [Add β] [Sub β] [Mul β]

/-- The image quaternion `[(0, M U)] p₁ Q p₂` over any type, with the constants embedded by
`k`. -/
def PMap.quatG (P : PMap κ) (k : κ → α) (U : V3 α) (Q : Q4 α) : Q4 α :=
  if P.fold then (Q4.pure (k (Exact.ofInt 0)) (M3.mulVecG k P.M U)).mul
    (((P.p₁.map k).mul Q).mul (P.p₂.map k))
  else ((P.p₁.map k).mul Q).mul (P.p₂.map k)

theorem PMap.map_quatG {f : α → β} (hf : IsArith f) (P : PMap κ) (k : κ → α) (U : V3 α)
    (Q : Q4 α) : (P.quatG k U Q).map f = P.quatG (f ∘ k) (U.map f) (Q.map f) := by
  unfold quatG
  split_ifs
  · rw [Q4.map_mul hf, Q4.map_mul hf, Q4.map_mul hf, Q4.map_pure, M3.map_mulVecG hf]
    rfl
  · rw [Q4.map_mul hf, Q4.map_mul hf]
    rfl

/-- The image view and the chart quaternion of the destination, on the homogeneous variables `x`
of a source box of charts `(a, k)` pre-rotated by `pre`, for a destination pre-rotated by
`pre'`. -/
def imgVQ (P : PMap κ) (a : Fin 3) (k : Fin 4) (pre pre' : Option (Q4 κ)) (emb : κ → α)
    (x : ℕ → α) : V3 α × Q4 α :=
  (M3.mulVecG emb P.M (homView a (x 5) (x 0) (x 1)),
    preQ emb (P.quatG emb (homView a (x 5) (x 0) (x 1))
      (preQ emb (homQuat k (x 5) ⟨x 2, x 3, x 4⟩) pre)) (pre'.map Exact.conjQ))

theorem map_imgVQ {f : α → β} (hf : IsArith f) (P : PMap κ) (a : Fin 3) (k : Fin 4)
    (pre pre' : Option (Q4 κ)) (emb : κ → α) (x : ℕ → α) :
    imgVQ P a k pre pre' (f ∘ emb) (f ∘ x) =
      ((imgVQ P a k pre pre' emb x).1.map f, (imgVQ P a k pre pre' emb x).2.map f) := by
  simp only [imgVQ, M3.map_mulVecG hf, map_preQ hf, PMap.map_quatG hf, map_homView, map_homQuat]
  rfl

omit [Add κ] [Sub κ] [Mul κ] [Exact κ] [Add α] [Sub α] [Mul α] in
/-- Numerator and denominator of chart coordinate `i` (`s, t, x₀, x₁, x₂`) of the view `v` and the
quaternion `y` in the charts `(a, k)`. -/
def coordND {γ : Type*} (a : Fin 3) (k : Fin 4) (v : Fin 3 → γ) (y : Fin 4 → γ) : ℕ → γ × γ
  | 0 => (v (a + 1), v a)
  | 1 => (v (a + 2), v a)
  | 2 => (y (k.succAbove 0), y k)
  | 3 => (y (k.succAbove 1), y k)
  | _ => (y (k.succAbove 2), y k)

omit [Add κ] [Sub κ] [Mul κ] [Exact κ] [Add α] [Sub α] [Mul α] [Add β] [Sub β] [Mul β] in
theorem map_coordND {γ δ : Type*} (f : γ → δ) (a : Fin 3) (k : Fin 4) (v : Fin 3 → γ)
    (y : Fin 4 → γ) : ∀ i, coordND a k (f ∘ v) (f ∘ y) i =
      (f (coordND a k v y i).1, f (coordND a k v y i).2)
  | 0 | 1 | 2 | 3 | _ + 4 => rfl

/-- `σ (c₁ num - c₂ den)` for coordinate `i` of the image in the charts `(a', k')`, on the
variables of a source box of charts `(a, k)` (module docs). -/
def imgGen (P : PMap κ) (a : Fin 3) (k : Fin 4) (pre pre' : Option (Q4 κ)) (a' : Fin 3)
    (k' : Fin 4) (i : ℕ) (σ c₁ c₂ : ℤ) : GenPoly κ where
  run emb x :=
    emb (Exact.ofInt σ) *
      (emb (Exact.ofInt c₁) * (coordND a' k' (imgVQ P a k pre pre' emb x).1.get
        (imgVQ P a k pre pre' emb x).2.toFun i).1 -
      emb (Exact.ofInt c₂) * (coordND a' k' (imgVQ P a k pre pre' emb x).1.get
        (imgVQ P a k pre pre' emb x).2.toFun i).2)
  natural f hf emb x := by
    rw [map_imgVQ hf]
    have hv : ((imgVQ P a k pre pre' emb x).1.map f).get =
        f ∘ (imgVQ P a k pre pre' emb x).1.get := funext fun j ↦ V3.get_map f _ j
    have hq : ((imgVQ P a k pre pre' emb x).2.map f).toFun =
        f ∘ (imgVQ P a k pre pre' emb x).2.toFun := funext fun j ↦ Q4.toFun_map f _ j
    simp only [hv, hq, map_coordND, hf.map_mul, hf.map_sub, Function.comp]

/-- The real image view `M u` at the chart point `y` of view chart `a`. -/
noncomputable def imgV (P : PMap κ) (a : Fin 3) (y : Fin 5 → ℝ) : Fin 3 → ℝ :=
  P.M.toMatrix *ᵥ viewDir a (y 0) (y 1)

/-- The real chart quaternion of the destination at the chart point `y` of a source box of
charts `(a, k)` pre-rotated by `pre`: the image quaternion followed by the conjugate of the
destination's pre-rotation `pre'`. -/
noncomputable def imgY (P : PMap κ) (a : Fin 3) (k : Fin 4) (pre pre' : Option (Q4 κ))
    (y : Fin 5 → ℝ) : Fin 4 → ℝ :=
  preQuat (P.imgQ (viewDir a (y 0) (y 1)) (preQuat (chartQuat k (rotCoords y)) (Exact.rePre pre)))
    (Exact.rePre (pre'.map Exact.conjQ))

theorem PMap.toFun_quatG (P : PMap κ) (U : V3 ℝ) (Q : Q4 ℝ) :
    (P.quatG Exact.re U Q).toFun = P.imgQ U.toFun Q.toFun := by
  have hV := M3.toFun_mulVecG P.M U
  unfold quatG imgQ
  split_ifs
  · rw [Q4.toFun_mul, Q4.toFun_mul, Q4.toFun_mul, ← hV]
    congr 1
    funext i
    fin_cases i <;> simp [Q4.pure, Q4.toFun, pureQ, Exact.re_ofInt, V3.toFun]
  · rw [Q4.toFun_mul, Q4.toFun_mul]
    rfl

theorem imgVQ_homEnv (P : PMap κ) (a : Fin 3) (k : Fin 4) (pre pre' : Option (Q4 κ)) (d : ℝ)
    (y : Fin 5 → ℝ) :
    (imgVQ P a k pre pre' Exact.re (homEnv 5 d y)).1.get = d • imgV P a y ∧
      (imgVQ P a k pre pre' Exact.re (homEnv 5 d y)).2.toFun =
        d ^ P.deg • imgY P a k pre pre' y := by
  constructor
  · funext j
    rw [V3.get_eq_toFun, imgVQ, M3.toFun_mulVecG, toFun_homView_homEnv, mulVec_smul]
    rfl
  · rw [imgVQ, toFun_preQ, PMap.toFun_quatG, toFun_preQ, toFun_homView_homEnv,
      toFun_homQuat_homEnv, preQuat_smul, P.imgQ_smul, preQuat_smul]
    rfl

theorem coordND_smul (a : Fin 3) (k : Fin 4) (d e : ℝ) (v : Fin 3 → ℝ) (y : Fin 4 → ℝ) :
    ∀ i, coordND a k (d • v) (e • y) i =
      ((if i < 2 then d else e) * (coordND a k v y i).1,
        (if i < 2 then d else e) * (coordND a k v y i).2)
  | 0 | 1 | 2 | 3 | _ + 4 => by simp [coordND]

/-- The degree of coordinate `i` of the image. -/
def PMap.degAt (P : PMap κ) (i : ℕ) : ℕ :=
  if i < 2 then 1 else P.deg

theorem imgGen_homEnv (P : PMap κ) (a : Fin 3) (k : Fin 4) (pre pre' : Option (Q4 κ))
    (a' : Fin 3) (k' : Fin 4) (i : ℕ) (σ c₁ c₂ : ℤ) (d : ℝ) (y : Fin 5 → ℝ) :
    (imgGen P a k pre pre' a' k' i σ c₁ c₂).run Exact.re (homEnv 5 d y) =
      d ^ P.degAt i * (σ * (c₁ * (coordND a' k' (imgV P a y) (imgY P a k pre pre' y) i).1 -
        c₂ * (coordND a' k' (imgV P a y) (imgY P a k pre pre' y) i).2)) := by
  obtain ⟨hv, hq⟩ := imgVQ_homEnv P a k pre pre' d y
  change Exact.re (Exact.ofInt σ) * (Exact.re (Exact.ofInt c₁) * (coordND a' k' _ _ i).1 -
    Exact.re (Exact.ofInt c₂) * (coordND a' k' _ _ i).2) = _
  rw [hv, hq, coordND_smul, Exact.re_ofInt, Exact.re_ofInt, Exact.re_ofInt, PMap.degAt]
  split_ifs <;> simp only [pow_one] <;> ring

theorem imgGen_isHomogeneous (P : PMap κ) (a : Fin 3) (k : Fin 4) (pre pre' : Option (Q4 κ))
    (a' : Fin 3) (k' : Fin 4) (i : ℕ) (σ c₁ c₂ : ℤ) :
    (imgGen P a k pre pre' a' k' i σ c₁ c₂).IsHomogeneous 5 (P.degAt i) := fun d y ↦ by
  rw [imgGen_homEnv, imgGen_homEnv, one_pow, one_mul]

end Gen

/-! ### The check -/

namespace Image

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The sign `σ = ± 1` for which the denominator of coordinate `i` (`0`: view, `2`: rotation)
of the image is certified positive on the source box, if any. -/
def denSign (P : PMap κ) (src : ChartBox) (pre : Option (Q4 κ)) (dst : ChartBox)
    (pre' : Option (Q4 κ)) (depth i : ℕ) : Option ℤ :=
  if posOn (imgGen P src.view src.rot pre pre' dst.view dst.rot i 1 0 (-1)) 5 depth src.box true
  then some 1
  else if posOn (imgGen P src.view src.rot pre pre' dst.view dst.rot i (-1) 0 (-1)) 5 depth
    src.box true then some (-1)
  else none

/-- Coordinate `i` of the image lies in the bounds of `dst`, with the sign `σ` of its
denominator. With dominance: an image that touches a face of `dst` makes a bound vanish on a face
of `src`. -/
def coordOk (P : PMap κ) (src : ChartBox) (pre : Option (Q4 κ)) (dst : ChartBox)
    (pre' : Option (Q4 κ)) (depth : ℕ) (σ : ℤ) (i : ℕ) : Bool :=
  nonnegOn (imgGen P src.view src.rot pre pre' dst.view dst.rot i σ dst.box.den
      (dst.box.lo.getD i 0)) 5 depth src.box true &&
    nonnegOn (imgGen P src.view src.rot pre pre' dst.view dst.rot i σ (-(dst.box.den : ℤ))
      (-dst.box.hi.getD i 0)) 5 depth src.box true

/-- **The check of an image**: the pose map `P` sends every pose of the chart box `src`,
pre-rotated by `pre`, into the chart box `dst`, pre-rotated by `pre'` (`check_image_into` in
`proof/symmetry.rs`), bisecting at most `depth` times along each branch. -/
def check (P : PMap κ) (src : ChartBox) (pre : Option (Q4 κ)) (dst : ChartBox)
    (pre' : Option (Q4 κ)) (depth : ℕ) : Bool :=
  decide (0 < src.box.den) && decide (0 < dst.box.den) && Exact.preOk pre && Exact.preOk pre' &&
    match denSign P src pre dst pre' depth 0, denSign P src pre dst pre' depth 2 with
    | some σ, some σ' =>
      coordOk P src pre dst pre' depth σ 0 && coordOk P src pre dst pre' depth σ 1 &&
        coordOk P src pre dst pre' depth σ' 2 && coordOk P src pre dst pre' depth σ' 3 &&
        coordOk P src pre dst pre' depth σ' 4
    | _, _ => false

section Sound

variable {P : PMap κ} {src dst : ChartBox} {pre pre' : Option (Q4 κ)} {depth : ℕ}

theorem denSign_sound {i : ℕ} {σ : ℤ} (hden : 0 < src.box.den)
    (h : denSign P src pre dst pre' depth i = some σ) {y : Fin 5 → ℝ} (hy : src.box.Mem 5 y) :
    0 < σ * (coordND dst.view dst.rot (imgV P src.view y)
      (imgY P src.view src.rot pre pre' y) i).2 := by
  have key (s : ℤ) (hs : posOn (imgGen P src.view src.rot pre pre' dst.view dst.rot i s 0 (-1))
      5 depth src.box true = true) : 0 < s * (coordND dst.view dst.rot (imgV P src.view y)
        (imgY P src.view src.rot pre pre' y) i).2 := by
    have := posOn_hom (imgGen_isHomogeneous _ _ _ _ _ _ _ _ _ _ _) hden hs hy
    rw [imgGen_homEnv, one_pow, one_mul] at this
    simpa using this
  unfold denSign at h
  split_ifs at h with h₁ h₂
  · cases h
    exact key 1 h₁
  · cases h
    exact key (-1) h₂

theorem coordOk_sound {σ : ℤ} {i : ℕ} (hden : 0 < src.box.den)
    (h : coordOk P src pre dst pre' depth σ i = true) {y : Fin 5 → ℝ} (hy : src.box.Mem 5 y)
    (hσ : 0 < σ * (coordND dst.view dst.rot (imgV P src.view y)
      (imgY P src.view src.rot pre pre' y) i).2) (hd : 0 < dst.box.den) :
    (dst.box.lo.getD i 0 : ℝ) / dst.box.den ≤
        (coordND dst.view dst.rot (imgV P src.view y) (imgY P src.view src.rot pre pre' y) i).1 /
          (coordND dst.view dst.rot (imgV P src.view y) (imgY P src.view src.rot pre pre' y) i).2 ∧
      (coordND dst.view dst.rot (imgV P src.view y) (imgY P src.view src.rot pre pre' y) i).1 /
          (coordND dst.view dst.rot (imgV P src.view y) (imgY P src.view src.rot pre pre' y) i).2 ≤
        (dst.box.hi.getD i 0 : ℝ) / dst.box.den := by
  simp only [coordOk, Bool.and_eq_true] at h
  have hlo := nonnegOn_hom (imgGen_isHomogeneous _ _ _ _ _ _ _ _ _ _ _) hden h.1 hy
  have hhi := nonnegOn_hom (imgGen_isHomogeneous _ _ _ _ _ _ _ _ _ _ _) hden h.2 hy
  rw [imgGen_homEnv, one_pow, one_mul] at hlo hhi
  set N := (coordND dst.view dst.rot (imgV P src.view y) (imgY P src.view src.rot pre pre' y) i).1
  set Dn := (coordND dst.view dst.rot (imgV P src.view y) (imgY P src.view src.rot pre pre' y) i).2
  have hdd : (0 : ℝ) < dst.box.den := by exact_mod_cast hd
  have hD : Dn ≠ 0 := fun h0 ↦ by simp [h0] at hσ
  have hσ0 : (σ : ℝ) ≠ 0 := fun h0 ↦ by simp [h0] at hσ
  have hq : N / Dn = (σ * N) / (σ * Dn) := by rw [mul_div_mul_left _ _ hσ0]
  push_cast at hlo hhi
  rw [hq]
  constructor
  · rw [div_le_div_iff₀ hdd hσ]
    nlinarith
  · rw [div_le_div_iff₀ hσ hdd]
    nlinarith

/-- **Soundness of the image check.** Every pose `p` of `src` has an image pose `p'` in `dst`: its
view direction is a nonzero multiple of `M u`, and its chart quaternion one of the image
quaternion of `u` and `q(x) q_c` followed by the conjugate of `q_c'`. -/
theorem check_sound (h : check P src pre dst pre' depth = true) {p : ChartPose}
    (hp : p ∈ src.poses) :
    ∃ p' ∈ dst.poses, ∃ a b : ℝ, a ≠ 0 ∧ b ≠ 0 ∧
      viewDir p'.view p'.s p'.t = a • (P.M.toMatrix *ᵥ viewDir p.view p.s p.t) ∧
      chartQuat p'.rot p'.x = b • preQuat (P.imgQ (viewDir p.view p.s p.t)
        (preQuat (chartQuat p.rot p.x) (Exact.rePre pre)))
        (Exact.rePre (pre'.map Exact.conjQ)) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hden, hden'⟩, -⟩, -⟩, h⟩ := h
  obtain ⟨hv, hr, hy⟩ := hp
  set y := p.coords
  split at h
  next σ σ' hσ hσ' =>
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
    have s0 := denSign_sound hden hσ hy
    have s2 := denSign_sound hden hσ' hy
    set V := imgV P src.view y
    set Y := imgY P src.view src.rot pre pre' y
    have hVa : V dst.view ≠ 0 := fun h0 ↦ by simp [coordND, h0] at s0
    have hYk : Y dst.rot ≠ 0 := fun h0 ↦ by simp [coordND, h0] at s2
    have c0 := coordOk_sound hden h0 hy (by simpa [coordND] using s0) hden'
    have c1 := coordOk_sound hden h1 hy (by simpa [coordND] using s0) hden'
    have c2 := coordOk_sound hden h2 hy s2 hden'
    have c3 := coordOk_sound hden h3 hy (by simpa [coordND] using s2) hden'
    have c4 := coordOk_sound hden h4 hy (by simpa [coordND] using s2) hden'
    simp only [coordND] at c0 c1 c2 c3 c4
    let p' : ChartPose := ⟨dst.view, V (dst.view + 1) / V dst.view,
      V (dst.view + 2) / V dst.view, dst.rot, fun i ↦ Y (dst.rot.succAbove i) / Y dst.rot⟩
    have hu : viewDir p.view p.s p.t = viewDir src.view (y 0) (y 1) := by rw [hv]; rfl
    have hq : chartQuat p.rot p.x = chartQuat src.rot (rotCoords y) := by
      rw [hr, rotCoords_coords]
    refine ⟨p', ⟨rfl, rfl, fun i ↦ ?_⟩, (V dst.view)⁻¹, (Y dst.rot)⁻¹, inv_ne_zero hVa,
      inv_ne_zero hYk, ?_, ?_⟩
    · fin_cases i
      exacts [c0, c1, c2, c3, c4]
    · rw [viewDir_div hVa, hu]
      rfl
    · rw [chartQuat_succAbove hYk, hu, hq]
      rfl
  next => simp at h

/-- **Image poses.** Every pose `p` of `src` has an image pose `p'` in `dst` whose view direction
is a nonzero multiple of `M u` and whose rotation, followed by the pre-rotation of `dst`, is that
of the image quaternion of `u` and `q(x) q_c`. -/
theorem rotation_eq (h : check P src pre dst pre' depth = true) {p : ChartPose}
    (hp : p ∈ src.poses) :
    ∃ p' ∈ dst.poses, ∃ a : ℝ, a ≠ 0 ∧
      viewDir p'.view p'.s p'.t = a • (P.M.toMatrix *ᵥ viewDir p.view p.s p.t) ∧
      p'.rotation * preRot (Exact.rePre pre') = quatRotation (P.imgQ (viewDir p.view p.s p.t)
        (preQuat (chartQuat p.rot p.x) (Exact.rePre pre))) := by
  have hpre' : Exact.preOk pre' = true := by
    simp only [check, Bool.and_eq_true] at h
    exact h.1.2
  obtain ⟨p', hp', a, b, ha, hb, hu, hq⟩ := check_sound h hp
  refine ⟨p', hp', a, ha, hu, ?_⟩
  rw [ChartPose.rotation, chartRotation, hq, quatRotation_smul hb]
  set Q₂ := P.imgQ (viewDir p.view p.s p.t) (preQuat (chartQuat p.rot p.x) (Exact.rePre pre))
  cases pre' with
  | none => rw [Option.map_none, Exact.rePre_none, preQuat, preRot_none, Matrix.mul_one]
  | some c =>
    have hc : Exact.reQ c ≠ 0 := Exact.rePre_ne_zero hpre' _ rfl
    change quatRotation (qmul Q₂ (Exact.reQ (Exact.conjQ c))) * quatRotation (Exact.reQ c) = _
    rw [← quatRotation_qmul, Exact.reQ_conjQ, qmul_qconj_mul,
      quatRotation_smul (dotProduct_self_eq_zero.not.mpr hc)]

/-- **Mapped boxes.** If the pose map of symmetries `i`, `j` of checked symmetry data sends `src`
into `dst`, no fit on `dst` (with its pre-rotation) gives no fit on `src` (with its own). -/
theorem noFitRot_of_check {pts : List (V3 κ)} {D : SymmData κ} (hD : D.ok pts = true)
    {i j : ℕ} (hP : D.pmap i j = some P) (h : check P src pre dst pre' depth = true)
    (hdst : (Polyhedron.ofPoints pts).NoFitRot dst.poses (preRot (Exact.rePre pre'))) :
    (Polyhedron.ofPoints pts).NoFitRot src.poses (preRot (Exact.rePre pre)) := by
  obtain ⟨A, σ, B, τ, hacts, hA, hB⟩ := SymmData.exists_acts_of_pmap hD hP
  have hpre : Exact.preOk pre = true := by
    simp only [check, Bool.and_eq_true] at h
    exact h.1.1.2
  intro p hp hfit
  obtain ⟨p', hp', a, ha, hu, hR⟩ := rotation_eq h hp
  obtain ⟨μ, hμ, hM⟩ := hacts.mul
  rw [ChartPose.rotation, chartRotation, ← quatRotation_preQuat] at hfit
  have h' := hacts.fitsAlong hA hB (viewDir_ne_zero _ _ _) hfit
  rw [← hR] at h'
  refine hdst p' hp' ?_
  rw [hu, hM, smul_mulVec, smul_smul]
  exact h'.smul (mul_ne_zero ha hμ)

/-- **Chart changes.** If the identity sends `src` into `dst`, a settled pose of `dst` (with its
pre-rotation) gives a settled pose of `src` (with its own). -/
theorem settledRot_of_check {pts : List (V3 κ)} {D : SymmData κ}
    (h : check PMap.id src pre dst pre' depth = true)
    (hdst : ∀ p ∈ dst.poses, SettledRot pts D (Exact.rePre pre') p) :
    ∀ p ∈ src.poses, SettledRot pts D (Exact.rePre pre) p := by
  intro p hp
  obtain ⟨p', hp', a, ha, hu, hR⟩ := rotation_eq h hp
  obtain ⟨μ, hμ, hM⟩ := (PMap.id_acts (κ := κ)).mul
  have hs := hdst p' hp'
  unfold SettledRot at hs ⊢
  rw [hu, hR, PMap.id_acts.quatRotation_imgQ (one_mem _) (Or.inl rfl) (Or.inl rfl)
    (viewDir_ne_zero _ _ _), hM, smul_mulVec, smul_smul, one_mulVec] at hs
  simp only [mul_one, turn_one, Matrix.one_mul, quatRotation_preQuat] at hs
  exact hs.of_smul (mul_ne_zero ha hμ)

end Sound

end Image

end Nieuwland.Check
