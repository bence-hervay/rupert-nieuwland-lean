import Modules.NoFit.Along

/-!
# Symmetry exclusion

`RESEARCH.md` §11.1 and `code/src/proof/symmetry.rs`. A *signed symmetry* of `P` about a centre
`c` is a rotation `A` and a sign `σ = ±1` with `c + σ A (v - c)` a vertex of `P` for every vertex
`v` (`IsSignedSymm`): `A` or `-A` maps the vertices about `c` into themselves. Two signed
symmetries `(A, σ)` and `(B, τ)` act on poses by

  `(u, R) ↦ (A u, H R')`, with `R' = A R B` and `H = turn (σ τ) (A u)`,

where `turn (-1) v` is the half-turn about `v` and `turn 1 v = 1`. This sends fits to fits
(`FitsAlong.symm`): `B` permutes the inner copy up to the sign `τ`, `A` moves the shadow to the
view `A u` up to the sign `σ`, and the half-turn about the view direction, which negates every
shadow, makes up for a sign `σ τ = -1`.

**Exclusion** (`Polyhedron.not_isRupert_of_excluded`). Let `f` be any real function of poses that
does not depend on the length of `u`. If `P` were Rupert, the poses that the signed symmetries
reach from a fit form a finite set of fits (`finite_signedSymm`, using that the vertices span
space about `c`); at one where `f` is largest, no pose map increases `f`
(`FitsAlong.exists_max`). So if every pose of the unit chart boxes either has no fit or is
improved by some pose map, `P` is not Rupert.
-/

open Matrix
open scoped Pointwise

namespace Nieuwland

/-! ### Half-turns -/

/-- The half-turn about `v`: `x ↦ (2 (v ⬝ᵥ x) / (v ⬝ᵥ v)) v - x`. -/
noncomputable def halfTurn (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (2 / (v ⬝ᵥ v)) • vecMulVec v v - 1

theorem halfTurn_mulVec (v x : Fin 3 → ℝ) :
    halfTurn v *ᵥ x = (2 * (v ⬝ᵥ x) / (v ⬝ᵥ v)) • v - x := by
  rw [halfTurn, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul]
  ring_nf

theorem halfTurn_mul_self (v : Fin 3 → ℝ) : halfTurn v * halfTurn v = 1 := by
  have h := householder_mul_self v
  rw [householder] at h
  rw [halfTurn, ← neg_sub, neg_mul_neg, h]

theorem halfTurn_transpose (v : Fin 3 → ℝ) : (halfTurn v)ᵀ = halfTurn v := by
  simp [halfTurn, transpose_sub, transpose_smul]

theorem det_halfTurn {v : Fin 3 → ℝ} (hv : v ≠ 0) : (halfTurn v).det = 1 := by
  have hd : v ⬝ᵥ v ≠ 0 := dotProduct_self_eq_zero.not.mpr hv
  have key (k : ℝ) : (k • vecMulVec v v - 1 : Matrix (Fin 3) (Fin 3) ℝ).det = k * (v ⬝ᵥ v) - 1 := by
    rw [det_fin_three]
    simp [vecMulVec_apply, dotProduct, Fin.sum_univ_three]
    ring
  rw [halfTurn, key, div_mul_cancel₀ 2 hd]
  norm_num

theorem halfTurn_mem {v : Fin 3 → ℝ} (hv : v ≠ 0) : halfTurn v ∈ SO(3) := by
  rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff]
  refine ⟨?_, det_halfTurn hv⟩
  simpa [star_eq_conjTranspose, conjTranspose, halfTurn_transpose] using halfTurn_mul_self v

theorem halfTurn_smul {a : ℝ} (ha : a ≠ 0) (v : Fin 3 → ℝ) : halfTurn (a • v) = halfTurn v := by
  have h : (2 / ((a • v) ⬝ᵥ (a • v))) • vecMulVec (a • v) (a • v) =
      (2 / (v ⬝ᵥ v)) • vecMulVec v v := by
    rw [smul_dotProduct, dotProduct_smul, smul_vecMulVec, vecMulVec_smul, smul_smul, smul_smul,
      smul_eq_mul, smul_eq_mul]
    congr 1
    rcases eq_or_ne (v ⬝ᵥ v) 0 with hv | hv
    · simp [hv]
    · field_simp
  rw [halfTurn, halfTurn, h]

/-- Rotations conjugate half-turns: `A H_v = H_{A v} A`. -/
theorem mul_halfTurn {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A ∈ O(3)) (v : Fin 3 → ℝ) :
    A * halfTurn v = halfTurn (A *ᵥ v) * A := by
  have hAA : Aᵀ * A = 1 := transpose_mul_of_mem_orthogonalGroup hA
  have hdot : (A *ᵥ v) ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ v := by
    rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hAA, one_mulVec]
  have hvv : vecMulVec (A *ᵥ v) (A *ᵥ v) * A = A * vecMulVec v v := by
    rw [vecMulVec_mul, mul_vecMulVec, ← mulVec_transpose, mulVec_mulVec, hAA, one_mulVec]
  rw [halfTurn, halfTurn, hdot, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_smul, Matrix.smul_mul, hvv]

/-- A screen map viewing along `v` negates the half-turn about `v`. -/
theorem map_halfTurn_mulVec {L : (Fin 3 → ℝ) →ₗ[ℝ] Fin 2 → ℝ} {v : Fin 3 → ℝ} (hv : L v = 0)
    (x : Fin 3 → ℝ) : L (halfTurn v *ᵥ x) = -L x := by
  rw [halfTurn_mulVec, map_sub, map_smul, hv, smul_zero, zero_sub]

/-! ### Turns -/

/-- `turn 1 v = 1`, and `turn σ v` is the half-turn about `v` for `σ ≠ 1`. -/
noncomputable def turn (σ : ℝ) (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  if σ = 1 then 1 else halfTurn v

theorem turn_one (v : Fin 3 → ℝ) : turn 1 v = 1 := by
  simp [turn]

theorem turn_neg_one (v : Fin 3 → ℝ) : turn (-1) v = halfTurn v := by
  unfold turn
  norm_num

theorem turn_mem (σ : ℝ) {v : Fin 3 → ℝ} (hv : v ≠ 0) : turn σ v ∈ SO(3) := by
  unfold turn
  split_ifs
  · exact one_mem _
  · exact halfTurn_mem hv

theorem turn_mul_turn {σ τ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) (v : Fin 3 → ℝ) :
    turn σ v * turn τ v = turn (σ * τ) v := by
  rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> norm_num [turn, halfTurn_mul_self]

theorem mul_turn {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A ∈ O(3)) (σ : ℝ) (v : Fin 3 → ℝ) :
    A * turn σ v = turn σ (A *ᵥ v) * A := by
  unfold turn
  split_ifs
  · rw [Matrix.mul_one, Matrix.one_mul]
  · exact mul_halfTurn hA v

theorem turn_smul {a : ℝ} (ha : a ≠ 0) (σ : ℝ) (v : Fin 3 → ℝ) : turn σ (a • v) = turn σ v := by
  rw [turn, turn, halfTurn_smul ha]

theorem map_turn_mulVec {L : (Fin 3 → ℝ) →ₗ[ℝ] Fin 2 → ℝ} {v : Fin 3 → ℝ} (hv : L v = 0)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (x : Fin 3 → ℝ) : L (turn σ v *ᵥ x) = σ • L x := by
  rcases hσ with rfl | rfl
  · simp [turn]
  · rw [turn_neg_one, map_halfTurn_mulVec hv, neg_one_smul]

namespace Polyhedron

variable {P : Polyhedron}

/-! ### Signed symmetries -/

/-- `(A, σ)` is a signed symmetry of `P` about `c`: `A` is a rotation, `σ = ±1`, and
`c + σ A (v - c)` is a vertex for every vertex `v`. -/
def IsSignedSymm (P : Polyhedron) (c : Fin 3 → ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) (σ : ℝ) :
    Prop :=
  A ∈ SO(3) ∧ (σ = 1 ∨ σ = -1) ∧ ∀ v ∈ P.vertices, c + σ • (A *ᵥ (v - c)) ∈ P.vertices

theorem isSignedSymm_one (P : Polyhedron) (c : Fin 3 → ℝ) : P.IsSignedSymm c 1 1 :=
  ⟨one_mem _, Or.inl rfl, fun v hv ↦ by simpa using hv⟩

theorem IsSignedSymm.mul {c : Fin 3 → ℝ} {A B : Matrix (Fin 3) (Fin 3) ℝ} {σ τ : ℝ}
    (hA : P.IsSignedSymm c A σ) (hB : P.IsSignedSymm c B τ) :
    P.IsSignedSymm c (A * B) (σ * τ) := by
  refine ⟨mul_mem hA.1 hB.1, ?_, fun v hv ↦ ?_⟩
  · rcases hA.2.1 with rfl | rfl <;> rcases hB.2.1 with rfl | rfl <;> norm_num
  · have := hA.2.2 _ (hB.2.2 v hv)
    rwa [add_sub_cancel_left, mulVec_smul, smul_smul, mulVec_mulVec] at this

theorem IsSignedSymm.sign_mul {c : Fin 3 → ℝ} {A B : Matrix (Fin 3) (Fin 3) ℝ} {σ τ : ℝ}
    (hA : P.IsSignedSymm c A σ) (hB : P.IsSignedSymm c B τ) : σ * τ = 1 ∨ σ * τ = -1 :=
  (hA.mul hB).2.1

/-! ### Pose maps send fits to fits -/

/-- **Pose maps.** Signed symmetries `(A, σ)` and `(B, τ)` send a fit along `u` with rotation `R`
to a fit along `A u` with rotation `turn (σ τ) (A u) * A * R * B`. -/
theorem FitsAlong.symm {c : Fin 3 → ℝ} {A B : Matrix (Fin 3) (Fin 3) ℝ} {σ τ : ℝ}
    (hA : P.IsSignedSymm c A σ) (hB : P.IsSignedSymm c B τ) {u : Fin 3 → ℝ}
    {R : Matrix (Fin 3) (Fin 3) ℝ} (h : P.FitsAlong u R) :
    P.FitsAlong (A *ᵥ u) (turn (σ * τ) (A *ᵥ u) * A * R * B) := by
  obtain ⟨L, hL, hker, τ₀, hfit⟩ := h
  have hAO : A ∈ O(3) := (mem_specialOrthogonalGroup_iff.mp hA.1).1
  have hAA : Aᵀ * A = 1 := transpose_mul_of_mem_orthogonalGroup hAO
  have hAA' : A * Aᵀ = 1 := mul_transpose_of_mem_orthogonalGroup hAO
  have hσ := hA.2.1
  have hτ := hB.2.1
  -- The new screen map views along `A u`.
  set L' := L ∘ₗ (Aᵀ).mulVecLin with hL'
  have hL'A (y : Fin 3 → ℝ) : L' (A *ᵥ y) = L y := by
    change L (Aᵀ *ᵥ (A *ᵥ y)) = L y
    rw [mulVec_mulVec, hAA, one_mulVec]
  have hLu : L u = 0 := LinearMap.mem_ker.mp (hker ▸ Submodule.mem_span_singleton_self u)
  have hL'u : L' (A *ᵥ u) = 0 := by rw [hL'A, hLu]
  refine ⟨L', fun y ↦ ?_, ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := hL y
    exact ⟨A *ᵥ x, hL'A x⟩
  · ext x
    rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
    change L (Aᵀ *ᵥ x) = 0 ↔ _
    rw [← LinearMap.mem_ker, hker, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, by rw [← mulVec_smul, ha, mulVec_mulVec, hAA', one_mulVec]⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, by rw [mulVec_smul, mulVec_mulVec, hAA, one_mulVec]⟩
  -- Vertices: the new outer polygon contains the old one, moved by `z ↦ K₂ + σ z`.
  have hfit' := (P.image_add_subset_interior_iff (L ∘ₗ R.mulVecLin) L τ₀).mp hfit
  refine ⟨_, (P.image_add_subset_interior_iff
    (L' ∘ₗ (turn (σ * τ) (A *ᵥ u) * A * R * B).mulVecLin) L'
    (L (Aᵀ *ᵥ c) - σ • L c + σ • τ₀ -
      (σ * τ) • (L (R *ᵥ (B *ᵥ c)) - τ • L (R *ᵥ c)))).mpr fun v hv ↦ ?_⟩
  set K₂ := L (Aᵀ *ᵥ c) - σ • L c
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hsub : K₂ +ᵥ σ • {L w | w ∈ P.vertices} ⊆ {L' w | w ∈ P.vertices} := by
    rintro _ ⟨_, ⟨_, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
    refine ⟨c + σ • (A *ᵥ (w - c)), hA.2.2 w hw, ?_⟩
    simp only [hL', LinearMap.comp_apply, mulVecLin_apply, mulVec_mulVec, hAA, one_mulVec,
      map_add, map_smul, map_sub, mulVec_sub, vadd_eq_add, K₂]
    module
  have hint : K₂ +ᵥ σ • interior (convexHull ℝ {L w | w ∈ P.vertices}) ⊆
      interior (convexHull ℝ {L' w | w ∈ P.vertices}) := by
    rw [← interior_smul₀ hσ0, ← interior_vadd, ← convexHull_smul, ← convexHull_vadd]
    exact interior_mono (convexHull_mono hsub)
  -- The vertex `v` of the inner copy is the image of the vertex `v'`.
  set v' := c + τ • (B *ᵥ (v - c))
  have hv' : v' ∈ P.vertices := hB.2.2 v hv
  refine hint ⟨_, ⟨_, hfit' v' hv', rfl⟩, ?_⟩
  simp only [LinearMap.comp_apply, mulVecLin_apply, vadd_eq_add]
  rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, map_turn_mulVec hL'u (hA.sign_mul hB),
    hL'A]
  simp only [v', mulVec_add, mulVec_smul, mulVec_sub, map_add, map_smul, map_sub, K₂]
  rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> module

/-! ### Exclusion -/

/-- If the vertices span space about `c`, `P` has finitely many signed symmetries about `c`: a
signed symmetry is determined by its sign and the vertex map it induces. -/
theorem finite_signedSymm {c : Fin 3 → ℝ}
    (hspan : Submodule.span ℝ ((· - c) '' (P.vertices : Set (Fin 3 → ℝ))) = ⊤) :
    {x : Matrix (Fin 3) (Fin 3) ℝ × ℝ | P.IsSignedSymm c x.1 x.2}.Finite := by
  let F : Matrix (Fin 3) (Fin 3) ℝ × ℝ → ℝ × (P.vertices → Fin 3 → ℝ) :=
    fun x ↦ (x.2, fun v ↦ c + x.2 • (x.1 *ᵥ ((v : Fin 3 → ℝ) - c)))
  refine Set.Finite.of_finite_image (f := F) ?_ ?_
  · refine (((Set.finite_singleton (-1 : ℝ)).insert 1).prod
      (Set.Finite.pi fun _ ↦ P.vertices.finite_toSet)).subset ?_
    rintro _ ⟨x, ⟨-, hσ, hv⟩, rfl⟩
    exact ⟨hσ.imp id id, fun v _ ↦ hv v v.2⟩
  · rintro ⟨A, σ⟩ ⟨-, hσ, -⟩ ⟨B, τ⟩ - hF
    simp only [F, Prod.mk.injEq] at hF
    obtain ⟨rfl, hF⟩ := hF
    have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
    have hAB : A.mulVecLin = B.mulVecLin := LinearMap.ext_on hspan (by
      rintro _ ⟨v, hv, rfl⟩
      have := add_left_cancel (congrFun hF ⟨v, hv⟩)
      exact smul_right_injective _ hσ0 this)
    rw [← toLin'_apply', ← toLin'_apply'] at hAB
    rw [toLin'.injective hAB]

theorem mulVec_ne_zero_of_mem_SO3 {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A ∈ SO(3))
    {u : Fin 3 → ℝ} (hu : u ≠ 0) : A *ᵥ u ≠ 0 := fun h ↦ by
  have hAA : Aᵀ * A = 1 :=
    transpose_mul_of_mem_orthogonalGroup (mem_specialOrthogonalGroup_iff.mp hA).1
  apply hu
  rw [← one_mulVec u, ← hAA, ← mulVec_mulVec, h, mulVec_zero]

/-- **Orbit maximum.** Let `f` be any real function of poses. Among the poses reached from
`(u₀, R₀)` by pose maps of signed symmetries, a finite set (`finite_signedSymm`) closed under pose
maps, one maximises `f`: the pose of a pair `(A₀, σ₀)`, `(B₀, τ₀)` that no pose map improves, and
at least `f (u₀, R₀)`. -/
theorem exists_orbit_max {c : Fin 3 → ℝ}
    (hspan : Submodule.span ℝ ((· - c) '' (P.vertices : Set (Fin 3 → ℝ))) = ⊤)
    (f : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ → ℝ) (u₀ : Fin 3 → ℝ)
    (R₀ : Matrix (Fin 3) (Fin 3) ℝ) :
    ∃ A₀ σ₀ B₀ τ₀, P.IsSignedSymm c A₀ σ₀ ∧ P.IsSignedSymm c B₀ τ₀ ∧
      (∀ A σ B τ, P.IsSignedSymm c A σ → P.IsSignedSymm c B τ →
        f (A *ᵥ (A₀ *ᵥ u₀)) (turn (σ * τ) (A *ᵥ (A₀ *ᵥ u₀)) * A *
          (turn (σ₀ * τ₀) (A₀ *ᵥ u₀) * A₀ * R₀ * B₀) * B) ≤
        f (A₀ *ᵥ u₀) (turn (σ₀ * τ₀) (A₀ *ᵥ u₀) * A₀ * R₀ * B₀)) ∧
      f u₀ R₀ ≤ f (A₀ *ᵥ u₀) (turn (σ₀ * τ₀) (A₀ *ᵥ u₀) * A₀ * R₀ * B₀) := by
  set S := {x : Matrix (Fin 3) (Fin 3) ℝ × ℝ | P.IsSignedSymm c x.1 x.2}
  have hS : S.Finite := finite_signedSymm hspan
  -- The pose reached from `(u₀, R₀)` by the pair `y` of signed symmetries.
  let pose (y : (Matrix (Fin 3) (Fin 3) ℝ × ℝ) × (Matrix (Fin 3) (Fin 3) ℝ × ℝ)) :
      (Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ :=
    (y.1.1 *ᵥ u₀, turn (y.1.2 * y.2.2) (y.1.1 *ᵥ u₀) * y.1.1 * R₀ * y.2.1)
  obtain ⟨⟨⟨A₀, σ₀⟩, ⟨B₀, τ₀⟩⟩, ⟨hA₀, hB₀⟩, hmax⟩ :=
    Set.exists_max_image (S ×ˢ S) (fun y ↦ f (pose y).1 (pose y).2) (hS.prod hS)
      ⟨((1, 1), (1, 1)), isSignedSymm_one P c, isSignedSymm_one P c⟩
  refine ⟨A₀, σ₀, B₀, τ₀, hA₀, hB₀, fun A σ B τ hA hB ↦ ?_, ?_⟩
  swap
  · have h1 := hmax ((1, 1), (1, 1)) ⟨isSignedSymm_one P c, isSignedSymm_one P c⟩
    simpa only [pose, one_mulVec, mul_one, turn_one, Matrix.one_mul, Matrix.mul_one] using h1
  have hle := hmax ((A * A₀, σ * σ₀), (B₀ * B, τ₀ * τ)) ⟨hA.mul hA₀, hB₀.mul hB⟩
  have hAO : A ∈ O(3) := (mem_specialOrthogonalGroup_iff.mp hA.1).1
  have hpose : turn (σ * τ) (A *ᵥ (A₀ *ᵥ u₀)) * A *
      (turn (σ₀ * τ₀) (A₀ *ᵥ u₀) * A₀ * R₀ * B₀) * B =
      turn (σ * σ₀ * (τ₀ * τ)) (A *ᵥ (A₀ *ᵥ u₀)) * (A * A₀) * R₀ * (B₀ * B) := by
    rw [show σ * σ₀ * (τ₀ * τ) = σ * τ * (σ₀ * τ₀) by ring,
      ← turn_mul_turn (hA.sign_mul hB) (hA₀.sign_mul hB₀)]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc A, mul_turn hAO]
    simp only [Matrix.mul_assoc]
  simp only [pose] at hle
  rwa [← mulVec_mulVec, ← hpose] at hle

/-- **Orbit maximum of fits.** If `P` fits along `u₀ ≠ 0` with a rotation `R₀`, it also fits at a
pose `(u, R)` that no pose map of signed symmetries improves (`exists_orbit_max`), with
`f (u₀, R₀) ≤ f (u, R)`. -/
theorem FitsAlong.exists_max_ge {c : Fin 3 → ℝ}
    (hspan : Submodule.span ℝ ((· - c) '' (P.vertices : Set (Fin 3 → ℝ))) = ⊤)
    (f : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ → ℝ) {u₀ : Fin 3 → ℝ}
    {R₀ : Matrix (Fin 3) (Fin 3) ℝ} (h : P.FitsAlong u₀ R₀) (hu₀ : u₀ ≠ 0) (hR₀ : R₀ ∈ SO(3)) :
    ∃ u R, u ≠ 0 ∧ R ∈ SO(3) ∧ P.FitsAlong u R ∧ (∀ A σ B τ, P.IsSignedSymm c A σ →
      P.IsSignedSymm c B τ → f (A *ᵥ u) (turn (σ * τ) (A *ᵥ u) * A * R * B) ≤ f u R) ∧
      f u₀ R₀ ≤ f u R := by
  obtain ⟨A₀, σ₀, B₀, τ₀, hA₀, hB₀, hmax, hge⟩ := exists_orbit_max hspan f u₀ R₀
  have hu : A₀ *ᵥ u₀ ≠ 0 := mulVec_ne_zero_of_mem_SO3 hA₀.1 hu₀
  exact ⟨A₀ *ᵥ u₀, turn (σ₀ * τ₀) (A₀ *ᵥ u₀) * A₀ * R₀ * B₀, hu,
    mul_mem (mul_mem (mul_mem (turn_mem _ hu) hA₀.1) hR₀) hB₀.1, h.symm hA₀ hB₀, hmax, hge⟩

/-- **Orbit maximum of fits.** If `P` fits along `u₀ ≠ 0` with a rotation `R₀`, it also fits at a
pose `(u, R)` that no pose map of signed symmetries improves (`exists_orbit_max`). -/
theorem FitsAlong.exists_max {c : Fin 3 → ℝ}
    (hspan : Submodule.span ℝ ((· - c) '' (P.vertices : Set (Fin 3 → ℝ))) = ⊤)
    (f : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ → ℝ) {u₀ : Fin 3 → ℝ}
    {R₀ : Matrix (Fin 3) (Fin 3) ℝ} (h : P.FitsAlong u₀ R₀) (hu₀ : u₀ ≠ 0) (hR₀ : R₀ ∈ SO(3)) :
    ∃ u R, u ≠ 0 ∧ R ∈ SO(3) ∧ P.FitsAlong u R ∧ ∀ A σ B τ, P.IsSignedSymm c A σ →
      P.IsSignedSymm c B τ → f (A *ᵥ u) (turn (σ * τ) (A *ᵥ u) * A * R * B) ≤ f u R := by
  obtain ⟨u, R, hu, hR, hfit, hmax, -⟩ := h.exists_max_ge hspan f hu₀ hR₀
  exact ⟨u, R, hu, hR, hfit, hmax⟩

/-- At the pose `(u, R)`, some pose map of signed symmetries of `P` about `c` increases `f`. -/
def ExcludedAt (P : Polyhedron) (c : Fin 3 → ℝ) (f : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ → ℝ)
    (u : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∃ A σ B τ, P.IsSignedSymm c A σ ∧ P.IsSignedSymm c B τ ∧
    f u R < f (A *ᵥ u) (turn (σ * τ) (A *ᵥ u) * A * R * B)

/-- Exclusion does not depend on the length of the view direction, for a function `f` that does
not. -/
theorem ExcludedAt.of_smul {c : Fin 3 → ℝ} {f : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ → ℝ}
    (hf : ∀ (a : ℝ) u R, a ≠ 0 → f (a • u) R = f u R) {a : ℝ} (ha : a ≠ 0) {u : Fin 3 → ℝ}
    {R : Matrix (Fin 3) (Fin 3) ℝ} (h : P.ExcludedAt c f (a • u) R) : P.ExcludedAt c f u R := by
  obtain ⟨A, σ, B, τ, hA, hB, hlt⟩ := h
  rw [mulVec_smul, turn_smul ha, hf _ _ _ ha, hf _ _ _ ha] at hlt
  exact ⟨A, σ, B, τ, hA, hB, hlt⟩

/-- At the chart pose `p`, some pose map of signed symmetries of `P` about `c` increases `f`. -/
def Excluded (P : Polyhedron) (c : Fin 3 → ℝ) (f : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ → ℝ)
    (p : ChartPose) : Prop :=
  P.ExcludedAt c f (viewDir p.view p.s p.t) p.rotation

/-- **Symmetry exclusion** (`code/src/proof/symmetry.rs`). Let the vertices of `P` span space
about `c`, and let `f` be a real function of poses that does not depend on the length of the view
direction. If at every pose of the unit chart boxes either `P` has no fit, or some pose map of
signed symmetries increases `f`, then `P` is not Rupert. -/
theorem not_isRupert_of_excluded {c : Fin 3 → ℝ}
    (hspan : Submodule.span ℝ ((· - c) '' (P.vertices : Set (Fin 3 → ℝ))) = ⊤)
    (f : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ → ℝ)
    (hf : ∀ (a : ℝ) u R, a ≠ 0 → f (a • u) R = f u R)
    (h : ∀ p ∈ unitPoses, (∀ τ, ¬ P.FitsAt p τ) ∨ P.Excluded c f p) :
    ¬ P.IsRupert := by
  intro hP
  obtain ⟨p₀, -, τ₀, hp₀⟩ := hP.exists_fitsAt
  obtain ⟨u, R, hu, hR, hfit, hmax⟩ := (fitsAlong_of_fitsAt hp₀).exists_max hspan f
    (viewDir_ne_zero _ _ _) p₀.rotation_mem
  obtain ⟨p, hp, ⟨τ, hτ⟩, ⟨a, ha, hpu⟩, hpR⟩ := hfit.exists_unitPoses hu hR
  rcases h p hp with hno | ⟨A, σ, B, τ', hA, hB, hlt⟩
  · exact hno τ hτ
  · rw [hpu, hpR, mulVec_smul, turn_smul ha, hf _ _ _ ha, hf _ _ _ ha] at hlt
    exact (hmax A σ B τ' hA hB).not_gt hlt

end Polyhedron

end Nieuwland
