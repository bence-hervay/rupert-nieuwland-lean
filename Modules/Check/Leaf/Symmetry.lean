import Modules.Check.Leaf.Support
import Modules.NoFit.Symmetry

/-!
# Symmetries from exact data

Certificates give the symmetries of a body as orthogonal matrices `g / den` over its field that
map the points about their centre into themselves (`SymSpec` in `code/src/proof/symmetry.rs`).
This file checks such data exactly, over any type of exact values with a complete zero test, and
turns it into the signed symmetries of `Modules/NoFit/Symmetry.lean`.

* `M3 κ`: matrices by rows over `κ`, with their real matrices `M3.toMatrix`.
* `Symm.ok` checks that `g gᵀ = den² 1`, that `det g = ± den³`, and that `c + g (v - c) / den` is
  one of the points for every point `v`, about the centre `c = C / m`: the point whose index the
  data gives (`Symm.img`, a hint; one comparison per point). Then `Symm.rot`, the rotation
  `± g / den` of determinant `1`, is a signed symmetry with the sign of `det g` (`Symm.ok_sound`).
* `spanOk` checks that three differences of points are linearly independent, so that the points
  span space about any centre (`spanOk_sound`), as symmetry exclusion requires.
-/

open Matrix

namespace Nieuwland.Check

/-- A 3 × 3 matrix by rows. -/
abbrev M3 (κ : Type) := V3 (V3 κ)

namespace M3

variable {κ : Type} [Add κ] [Sub κ] [Mul κ]

/-- `G v`. -/
def mulVec (G : M3 κ) (v : V3 κ) : V3 κ :=
  ⟨G.x.dot v, G.y.dot v, G.z.dot v⟩

/-- `Gᵀ`. -/
def transpose (G : M3 κ) : M3 κ :=
  ⟨⟨G.x.x, G.y.x, G.z.x⟩, ⟨G.x.y, G.y.y, G.z.y⟩, ⟨G.x.z, G.y.z, G.z.z⟩⟩

/-- `G H`. -/
def mul (G H : M3 κ) : M3 κ :=
  ⟨H.transpose.mulVec G.x, H.transpose.mulVec G.y, H.transpose.mulVec G.z⟩

/-- `det G`. -/
def det (G : M3 κ) : κ :=
  G.x.dot (G.y.cross G.z)

/-- `G U` for a vector `U` over any type with `+` and `*`, with the entries embedded by `k`. -/
def mulVecG {α : Type*} [Add α] [Mul α] (k : κ → α) (G : M3 κ) (U : V3 α) : V3 α :=
  ⟨(G.x.map k).dot U, (G.y.map k).dot U, (G.z.map k).dot U⟩

omit [Add κ] [Sub κ] [Mul κ] in
theorem map_mulVecG {α β : Type*} [Add α] [Sub α] [Mul α] [Add β] [Sub β] [Mul β] {f : α → β}
    (hf : IsArith f) (k : κ → α) (G : M3 κ) (U : V3 α) :
    (mulVecG k G U).map f = mulVecG (f ∘ k) G (U.map f) := by
  simp only [mulVecG, V3.map, V3.map_dot hf]
  rfl

variable [Exact κ]

/-- The scalar matrix `c 1`. -/
def scalar (c : ℤ) : M3 κ :=
  ⟨⟨Exact.ofInt c, Exact.ofInt 0, Exact.ofInt 0⟩, ⟨Exact.ofInt 0, Exact.ofInt c, Exact.ofInt 0⟩,
    ⟨Exact.ofInt 0, Exact.ofInt 0, Exact.ofInt c⟩⟩

/-- Equality, by the zero tests of `κ`. -/
def eqb (G H : M3 κ) : Bool :=
  Exact.eqV G.x H.x && Exact.eqV G.y H.y && Exact.eqV G.z H.z

/-- The real matrix. -/
noncomputable def toMatrix (G : M3 κ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j ↦ Exact.re ((G.get i).get j)

theorem toMatrix_eq_of_eqb {G H : M3 κ} (h : G.eqb H = true) : G.toMatrix = H.toMatrix := by
  simp only [eqb, Bool.and_eq_true] at h
  have hx := Exact.reV_eq_of_eqV h.1.1
  have hy := Exact.reV_eq_of_eqV h.1.2
  have hz := Exact.reV_eq_of_eqV h.2
  ext i j
  fin_cases i <;> fin_cases j
  all_goals first
    | exact congrFun hx 0 | exact congrFun hx 1 | exact congrFun hx 2
    | exact congrFun hy 0 | exact congrFun hy 1 | exact congrFun hy 2
    | exact congrFun hz 0 | exact congrFun hz 1 | exact congrFun hz 2

theorem toFun_mulVecG (G : M3 κ) (U : V3 ℝ) :
    (mulVecG Exact.re G U).toFun = G.toMatrix *ᵥ U.toFun := by
  funext i
  fin_cases i <;>
    simp [mulVecG, toMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, V3.dot, V3.get,
      V3.map]

theorem toMatrix_mulVec (G : M3 κ) (v : V3 κ) :
    G.toMatrix *ᵥ Exact.reV v = Exact.reV (G.mulVec v) := by
  funext i
  fin_cases i <;>
    simp [mulVec, toMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, V3.dot, V3.get,
      Exact.reV, V3.map, Exact.re_add, Exact.re_mul]

theorem toMatrix_transpose (G : M3 κ) : G.transpose.toMatrix = G.toMatrixᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem toMatrix_mul (G H : M3 κ) : (G.mul H).toMatrix = G.toMatrix * H.toMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul, mulVec, transpose, toMatrix, mul_apply, Fin.sum_univ_three, V3.dot, V3.get,
      Exact.re_add, Exact.re_mul] <;> ring

theorem det_toMatrix (G : M3 κ) : G.toMatrix.det = Exact.re G.det := by
  rw [det_fin_three]
  simp [det, toMatrix, V3.dot, V3.cross, V3.get, Exact.re_add, Exact.re_sub, Exact.re_mul]
  ring

theorem toMatrix_scalar (c : ℤ) : (scalar c : M3 κ).toMatrix = (c : ℝ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalar, toMatrix, V3.get, Exact.re_ofInt]

end M3

/-! ### Signed symmetries -/

/-- A symmetry of a body as exact data: the orthogonal matrix `g / den`. -/
structure Symm (κ : Type) where
  /-- The numerator. -/
  g : M3 κ
  /-- The denominator. -/
  den : ℕ
  /-- For each point, the index of its image among the points (checked). -/
  img : List ℕ

namespace Symm

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The sign of `det g`, by the positivity test of `κ`. -/
def sign (S : Symm κ) : ℤ :=
  if Exact.pos S.g.det then 1 else -1

/-- The rotation `sign · g / den`. -/
noncomputable def rot (S : Symm κ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ((S.sign : ℝ) / S.den) • S.g.toMatrix

/-- `p` is the image `c + g (v - c) / den` of `v` about the centre `c = C / m`. -/
def maps (C : V3 κ) (m : ℕ) (S : Symm κ) (v p : V3 κ) : Bool :=
  Exact.eqV (V3.smul (Exact.ofInt (m * S.den)) p)
    ((V3.smul (Exact.ofInt S.den) C).add (S.g.mulVec ((V3.smul (Exact.ofInt m) v).sub C)))

/-- Each point of `vs` maps to the point of `pts` whose index is at the same position in `js`. -/
def mapsTo (pts : List (V3 κ)) (C : V3 κ) (m : ℕ) (S : Symm κ) : List (V3 κ) → List ℕ → Bool
  | [], _ => true
  | _ :: _, [] => false
  | v :: vs, j :: js =>
    (match pts[j]? with
      | some p => S.maps C m v p
      | none => false) && mapsTo pts C m S vs js

theorem exists_of_mapsTo {pts : List (V3 κ)} {C : V3 κ} {m : ℕ} {S : Symm κ} :
    ∀ {vs : List (V3 κ)} {js : List ℕ}, mapsTo pts C m S vs js = true →
      ∀ v ∈ vs, ∃ p ∈ pts, S.maps C m v p = true
  | [], _, _, v, hv => by simp at hv
  | _ :: _, [], h, _, _ => by simp [mapsTo] at h
  | w :: vs, j :: js, h, v, hv => by
    simp only [mapsTo, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hv with rfl | hv
    · cases hj : pts[j]? with
      | none => simp [hj] at h
      | some p =>
        simp only [hj] at h
        exact ⟨p, List.mem_of_getElem? hj, h.1⟩
    · exact exists_of_mapsTo h.2 v hv

/-- `g / den` is orthogonal with determinant `± 1`, and maps each point `v` of `pts` to a point,
`c + g (v - c) / den` with the centre `c = C / m`: the point of index `img[k]` if `v` is the
`k`-th. -/
def ok (pts : List (V3 κ)) (C : V3 κ) (m : ℕ) (S : Symm κ) : Bool :=
  decide (0 < S.den) && decide (0 < m) &&
    (S.g.mul S.g.transpose).eqb (M3.scalar (S.den * S.den)) &&
    Exact.isZero (S.g.det - Exact.ofInt (S.sign * (S.den : ℤ) ^ 3)) &&
    S.mapsTo pts C m pts S.img

theorem sign_eq (S : Symm κ) : S.sign = 1 ∨ S.sign = -1 := by
  unfold sign
  split_ifs
  exacts [Or.inl rfl, Or.inr rfl]

theorem sign_mul_self (S : Symm κ) : (S.sign : ℝ) * S.sign = 1 := by
  rcases S.sign_eq with h | h <;> simp [h]

variable {pts : List (V3 κ)} {C : V3 κ} {m : ℕ} {S : Symm κ}

theorem den_pos_of_ok (h : S.ok pts C m = true) : 0 < S.den := by
  simp only [ok, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1

theorem toMatrix_mul_transpose_of_ok (h : S.ok pts C m = true) :
    S.g.toMatrix * S.g.toMatrixᵀ = ((S.den : ℝ) ^ 2) • 1 := by
  simp only [ok, Bool.and_eq_true] at h
  have := M3.toMatrix_eq_of_eqb h.1.1.2
  rw [M3.toMatrix_mul, M3.toMatrix_transpose, M3.toMatrix_scalar] at this
  rw [this]
  push_cast
  ring_nf

theorem det_of_ok (h : S.ok pts C m = true) :
    Exact.re S.g.det = S.sign * (S.den : ℝ) ^ 3 := by
  simp only [ok, Bool.and_eq_true] at h
  have h0 := Exact.isZero_sound _ h.1.2
  rw [Exact.re_sub, Exact.re_ofInt, sub_eq_zero] at h0
  rw [h0]
  push_cast
  ring

theorem rot_mul_transpose_of_ok (h : S.ok pts C m = true) : S.rot * S.rotᵀ = 1 := by
  have hd : (S.den : ℝ) ≠ 0 := by exact_mod_cast (den_pos_of_ok h).ne'
  rw [rot, transpose_smul, smul_mul_smul_comm, toMatrix_mul_transpose_of_ok h, smul_smul]
  have : (S.sign : ℝ) / S.den * (S.sign / S.den) * S.den ^ 2 = 1 := by
    have hs := S.sign_mul_self
    field_simp
    linear_combination hs
  rw [this, one_smul]

theorem transpose_rot_mul_of_ok (h : S.ok pts C m = true) : S.rotᵀ * S.rot = 1 :=
  mul_eq_one_comm.mp (rot_mul_transpose_of_ok h)

theorem rot_mem_of_ok (h : S.ok pts C m = true) : S.rot ∈ SO(3) := by
  have hd : (S.den : ℝ) ≠ 0 := by exact_mod_cast (den_pos_of_ok h).ne'
  rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff]
  refine ⟨by simpa [star_eq_conjTranspose, conjTranspose] using rot_mul_transpose_of_ok h, ?_⟩
  rw [rot, det_smul, M3.det_toMatrix, det_of_ok h, Fintype.card_fin]
  have hs := S.sign_mul_self
  field_simp
  linear_combination ((S.sign : ℝ) * S.sign + 1) * hs

/-- **Symmetry data.** Checked data is a signed symmetry of the polyhedron of `pts` about
`C / m`: the rotation `Symm.rot` with the sign of `det g`. -/
theorem ok_sound (h : S.ok pts C m = true) :
    (Polyhedron.ofPoints pts).IsSignedSymm ((m : ℝ)⁻¹ • Exact.reV C) S.rot S.sign := by
  refine ⟨rot_mem_of_ok h, ?_, fun v hv ↦ ?_⟩
  · rcases S.sign_eq with hs | hs <;> simp [hs]
  have hd : (S.den : ℝ) ≠ 0 := by exact_mod_cast (den_pos_of_ok h).ne'
  simp only [ok, Bool.and_eq_true, decide_eq_true_eq] at h
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast h.1.1.1.2.ne'
  obtain ⟨v', hv', rfl⟩ := Polyhedron.mem_ofPoints.mp hv
  obtain ⟨p, hp, hpv⟩ := exists_of_mapsTo h.2 v' hv'
  refine Polyhedron.mem_ofPoints.mpr ⟨p, hp, ?_⟩
  have hcast := Exact.reV_eq_of_eqV hpv
  rw [Exact.reV_smul, Exact.reV_add, Exact.reV_smul, ← M3.toMatrix_mulVec, Exact.reV_sub,
    Exact.reV_smul, Exact.re_ofInt, Exact.re_ofInt, Exact.re_ofInt] at hcast
  rw [mulVec_sub, mulVec_smul] at hcast
  rw [rot, smul_mulVec, mulVec_sub, mulVec_smul]
  funext i
  have hi := congrFun hcast i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hi ⊢
  push_cast at hi ⊢
  have hs := S.sign_mul_self
  field_simp
  linear_combination hi - ((m : ℝ) * (S.g.toMatrix *ᵥ Exact.reV v') i -
    (S.g.toMatrix *ᵥ Exact.reV C) i) * hs

end Symm

/-! ### Spanning -/

/-- Cramer's rule in space. -/
theorem smul_eq_cramer {R : Type*} [CommRing R] (d₁ d₂ d₃ x : Fin 3 → R) :
    (d₁ ⬝ᵥ (d₂ ⨯₃ d₃)) • x =
      (x ⬝ᵥ (d₂ ⨯₃ d₃)) • d₁ + (x ⬝ᵥ (d₃ ⨯₃ d₁)) • d₂ + (x ⬝ᵥ (d₁ ⨯₃ d₂)) • d₃ := by
  funext i
  fin_cases i <;> simp [cross_apply, dotProduct, Fin.sum_univ_three] <;> ring

section Span

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The differences `p j - p i`, `p k - p i`, `p l - p i` of the points are linearly
independent. -/
def spanOk (pts : List (V3 κ)) (i j k l : ℕ) : Bool :=
  decide (i < pts.length) && decide (j < pts.length) && decide (k < pts.length) &&
    decide (l < pts.length) &&
    Exact.nonzero (((pt pts j).sub (pt pts i)).dot
      (((pt pts k).sub (pt pts i)).cross ((pt pts l).sub (pt pts i))))

/-- **Spanning.** If `spanOk` holds, the points span space about any centre. -/
theorem spanOk_sound {pts : List (V3 κ)} {i j k l : ℕ} (h : spanOk pts i j k l = true)
    (c : Fin 3 → ℝ) :
    Submodule.span ℝ
      ((· - c) '' ((Polyhedron.ofPoints pts).vertices : Set (Fin 3 → ℝ))) = ⊤ := by
  simp only [spanOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hi, hj⟩, hk⟩, hl⟩, hdet⟩ := h
  set S := Submodule.span ℝ
    ((· - c) '' ((Polyhedron.ofPoints pts).vertices : Set (Fin 3 → ℝ)))
  have hmem {r : ℕ} (hr : r < pts.length) : Exact.reV (pt pts r) - c ∈ S :=
    Submodule.subset_span ⟨_, Polyhedron.pt_mem_ofPoints hr, rfl⟩
  have hdiff {r : ℕ} (hr : r < pts.length) :
      Exact.reV (pt pts r) - Exact.reV (pt pts i) ∈ S := by
    rw [← sub_sub_sub_cancel_right _ _ c]
    exact S.sub_mem (hmem hr) (hmem hi)
  set d₁ := Exact.reV (pt pts j) - Exact.reV (pt pts i)
  set d₂ := Exact.reV (pt pts k) - Exact.reV (pt pts i)
  set d₃ := Exact.reV (pt pts l) - Exact.reV (pt pts i)
  have hD : d₁ ⬝ᵥ (d₂ ⨯₃ d₃) ≠ 0 := by
    have h0 := Exact.re_ne_zero_of_nonzero hdet
    rwa [Exact.re_dot, Exact.reV_cross, Exact.reV_sub, Exact.reV_sub, Exact.reV_sub] at h0
  refine eq_top_iff.mpr fun x _ ↦ ?_
  have hx : x = (d₁ ⬝ᵥ (d₂ ⨯₃ d₃))⁻¹ •
      ((x ⬝ᵥ (d₂ ⨯₃ d₃)) • d₁ + (x ⬝ᵥ (d₃ ⨯₃ d₁)) • d₂ + (x ⬝ᵥ (d₁ ⨯₃ d₂)) • d₃) := by
    rw [← smul_eq_cramer, smul_smul, inv_mul_cancel₀ hD, one_smul]
  rw [hx]
  exact S.smul_mem _ (S.add_mem (S.add_mem (S.smul_mem _ (hdiff hj)) (S.smul_mem _ (hdiff hk)))
    (S.smul_mem _ (hdiff hl)))

end Span

end Nieuwland.Check
