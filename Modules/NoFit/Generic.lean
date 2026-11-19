import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.LocallyCompactRegular
import Modules.NoFit.Open
import Modules.NoFit.Symmetry

/-!
# Weak exclusion: generic poses

Part (b) of the density theorem (`lean/DESIGN.md` §8, G3). A certificate whose leaves have
exceptional sets proves, at every pose of the unit chart boxes, that the polyhedron has no fit
there, that some pose map of signed symmetries increases the score, or that the pose lies in a
null set `N`. That suffices (`Polyhedron.not_isRupert_of_excluded_off`) when `N` is meagre in the
space of poses and does not depend on the length of the view direction:

* **Poses** (`poseSpace`): pairs `(u, R)` of a nonzero view direction and a rotation, a Gδ subset
  of `ℝ³ × ℝ³ˣ³` and so a Baire space.
* **Fits** form an open set of poses (`Polyhedron.FitsAlong.eventually`).
* **Pose maps** of signed symmetries are homeomorphisms of the poses (`poseMap`, with the pose map
  of the transposes as inverse), so they pull meagre sets back to meagre sets.
* So a Rupert polyhedron has a fit whose whole orbit avoids `N` (Baire), and the pose of that
  orbit that maximises the score (`Polyhedron.exists_orbit_max`) is a fit that is neither
  excluded nor in `N`: a contradiction.

Null sets come from polynomials: a closed set of poses at whose quaternion representatives a
nonzero polynomial in `(u, q)` vanishes is nowhere dense (`isNowhereDense_of_poly`), by the
identity theorem for polynomials (`eq_zero_of_isOpen`, from `MvPolynomial.funext_set`).
-/

open Matrix Filter Topology

namespace Nieuwland

/-! ### Poses -/

/-- Poses: a nonzero view direction and a rotation. -/
def poseSpace : Set ((Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ) :=
  {x | x.1 ≠ 0 ∧ x.2 ∈ SO(3)}

theorem isClosed_SO3 : IsClosed (SO(3) : Set (Matrix (Fin 3) (Fin 3) ℝ)) := by
  have h : (SO(3) : Set (Matrix (Fin 3) (Fin 3) ℝ)) =
      {A | A * Aᵀ = 1} ∩ {A | A.det = 1} := by
    ext A
    simp [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff]
  rw [h]
  exact (isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_transpose)
    continuous_const).inter (isClosed_eq continuous_id.matrix_det continuous_const)

instance : PerfectlyNormalSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (PerfectlyNormalSpace (Fin 3 → Fin 3 → ℝ))

instance : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → ℝ))

theorem isGδ_poseSpace : IsGδ poseSpace :=
  (isOpen_ne_fun continuous_fst continuous_const).isGδ.inter
    (isClosed_SO3.isGδ.preimage continuous_snd)

instance : BaireSpace poseSpace :=
  isGδ_poseSpace.baireSpace_of_t2Space_locallyCompactSpace

/-- The pose of a chart pose: its view direction and its rotation. -/
noncomputable def ChartPose.pose (p : ChartPose) : (Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ :=
  (viewDir p.view p.s p.t, p.rotation)

theorem ChartPose.pose_mem (p : ChartPose) : p.pose ∈ poseSpace :=
  ⟨viewDir_ne_zero _ _ _, p.rotation_mem⟩

/-! ### Pose maps -/

theorem continuousAt_halfTurn {v : Fin 3 → ℝ} (hv : v ≠ 0) : ContinuousAt halfTurn v := by
  have hd : v ⬝ᵥ v ≠ 0 := dotProduct_self_eq_zero.not.mpr hv
  have h1 : Continuous fun w : Fin 3 → ℝ ↦ w ⬝ᵥ w := continuous_id.dotProduct continuous_id
  have h2 : Continuous fun w : Fin 3 → ℝ ↦ vecMulVec w w := by
    refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    simp only [vecMulVec_apply]
    fun_prop
  exact ((continuousAt_const.div h1.continuousAt hd).smul h2.continuousAt).sub continuousAt_const

theorem continuousAt_turn (σ : ℝ) {v : Fin 3 → ℝ} (hv : v ≠ 0) : ContinuousAt (turn σ) v := by
  change ContinuousAt (fun w ↦ turn σ w) v
  by_cases hσ : σ = 1
  · simp only [turn, hσ, ↓reduceIte]
    exact continuousAt_const
  · simp only [turn, hσ, ↓reduceIte]
    exact continuousAt_halfTurn hv

/-- The pose map of signed symmetries `(A, σ)` and `(B, τ)`, with `s = σ τ`:
`(u, R) ↦ (A u, turn s (A u) A R B)` (`Polyhedron.FitsAlong.symm`). -/
noncomputable def poseMap (A B : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ)
    (x : (Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ) : (Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ :=
  (A *ᵥ x.1, turn s (A *ᵥ x.1) * A * x.2 * B)

section PoseMap

variable {A B : Matrix (Fin 3) (Fin 3) ℝ} {s : ℝ}

theorem poseMap_mem (hA : A ∈ SO(3)) (hB : B ∈ SO(3))
    {x : (Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ} (hx : x ∈ poseSpace) :
    poseMap A B s x ∈ poseSpace := by
  have hu := Polyhedron.mulVec_ne_zero_of_mem_SO3 hA hx.1
  exact ⟨hu, mul_mem (mul_mem (mul_mem (turn_mem s hu) hA) hx.2) hB⟩

theorem continuousOn_poseMap (hA : A ∈ SO(3)) : ContinuousOn (poseMap A B s) poseSpace := by
  intro x hx
  have hu := Polyhedron.mulVec_ne_zero_of_mem_SO3 hA hx.1
  have h1 : ContinuousAt (fun x : (Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ ↦ A *ᵥ x.1) x :=
    (continuous_const.matrix_mulVec continuous_fst).continuousAt
  have h2 : ContinuousAt (fun x : (Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ ↦ turn s (A *ᵥ x.1))
      x :=
    ContinuousAt.comp (g := turn s) (f := fun x : (Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ ↦
      A *ᵥ x.1) (continuousAt_turn s hu) h1
  exact (h1.prodMk (((h2.mul continuousAt_const).mul continuousAt_snd).mul
    continuousAt_const)).continuousWithinAt

/-- The pose map of the transposes undoes a pose map. -/
theorem poseMap_transpose (hA : A ∈ SO(3)) (hB : B ∈ SO(3)) (hs : s = 1 ∨ s = -1)
    (x : (Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ) : poseMap Aᵀ Bᵀ s (poseMap A B s x) = x := by
  obtain ⟨u, R⟩ := x
  have hAt : Aᵀ * A = 1 := transpose_mul_of_mem_orthogonalGroup hA.1
  have hBt : B * Bᵀ = 1 := mul_transpose_of_mem_orthogonalGroup hB.1
  have hu : Aᵀ *ᵥ (A *ᵥ u) = u := by rw [mulVec_mulVec, hAt, one_mulVec]
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  simp only [poseMap, hu, Prod.mk.injEq, true_and]
  calc turn s u * Aᵀ * (turn s (A *ᵥ u) * A * R * B) * Bᵀ
      = turn s u * (Aᵀ * turn s (A *ᵥ u)) * A * R * (B * Bᵀ) := by
        simp only [Matrix.mul_assoc]
    _ = turn s u * turn s u * (Aᵀ * A) * R := by
        rw [mul_turn (transpose_mem_SO3 hA).1, hu, hBt]
        simp only [Matrix.mul_assoc, Matrix.mul_one]
    _ = R := by rw [turn_mul_turn hs hs, hss, turn_one, hAt, Matrix.mul_one, Matrix.one_mul]

/-- **Pose maps pull meagre sets of poses back to meagre sets**: they are homeomorphisms of the
poses. -/
theorem isMeagre_poseMap_preimage (hA : A ∈ SO(3)) (hB : B ∈ SO(3)) (hs : s = 1 ∨ s = -1)
    {N : Set ((Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ)}
    (hN : IsMeagre ((↑) ⁻¹' N : Set poseSpace)) :
    IsMeagre {x : poseSpace | poseMap A B s x ∈ N} := by
  have hA' := transpose_mem_SO3 hA
  have hB' := transpose_mem_SO3 hB
  let g : poseSpace → poseSpace := fun x ↦ ⟨poseMap A B s x, poseMap_mem hA hB x.2⟩
  let g' : poseSpace → poseSpace := fun x ↦ ⟨poseMap Aᵀ Bᵀ s x, poseMap_mem hA' hB' x.2⟩
  have hg : Continuous g :=
    (continuousOn_poseMap hA).domRestrict.subtype_mk _
  have hg' : Continuous g' :=
    (continuousOn_poseMap hA').domRestrict.subtype_mk _
  have hl : Function.LeftInverse g g' := fun x ↦ Subtype.ext (by
    have h := poseMap_transpose hA' hB' hs x.1
    rwa [transpose_transpose, transpose_transpose] at h)
  have hr : Function.RightInverse g g' := fun x ↦ Subtype.ext (poseMap_transpose hA hB hs x.1)
  exact hN.preimage_of_isOpenMap hg (IsOpenMap.of_inverse hg' hl hr)

end PoseMap

/-! ### Polynomials in `(u, q)` -/

/-- The coordinates of `(u, q)` as a point of `ℝ⁷`. -/
def join (u : Fin 3 → ℝ) (q : Fin 4 → ℝ) : Fin 7 → ℝ :=
  ![u 0, u 1, u 2, q 0, q 1, q 2, q 3]

/-- **Identity theorem.** A polynomial in `(u, q)` that vanishes on a nonempty open set is zero. -/
theorem eq_zero_of_isOpen {P : MvPolynomial (Fin 7) ℝ}
    {U : Set ((Fin 3 → ℝ) × (Fin 4 → ℝ))} (hU : IsOpen U) (hne : U.Nonempty)
    (h : ∀ x ∈ U, MvPolynomial.eval (join x.1 x.2) P = 0) : P = 0 := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  set c := join x₀.1 x₀.2
  refine MvPolynomial.funext_set (fun i ↦ Set.Ioo (c i - ε) (c i + ε))
    (fun i ↦ Set.Ioo_infinite (by linarith)) fun y hy ↦ ?_
  have hy' (i : Fin 7) : |y i - c i| < ε := by
    have := hy i (Set.mem_univ i)
    rw [Set.mem_Ioo] at this
    rw [abs_sub_lt_iff]
    constructor <;> linarith [this.1, this.2]
  have hmem : ((![y 0, y 1, y 2], ![y 3, y 4, y 5, y 6]) : (Fin 3 → ℝ) × (Fin 4 → ℝ)) ∈ U := by
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, dist_pi_lt_iff hε, dist_pi_lt_iff hε]
    refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩ <;> rw [Real.dist_eq] <;> fin_cases i
    exacts [hy' 0, hy' 1, hy' 2, hy' 3, hy' 4, hy' 5, hy' 6]
  have hj : join ![y 0, y 1, y 2] ![y 3, y 4, y 5, y 6] = y := by
    funext i
    fin_cases i <;> rfl
  have := h _ hmem
  rw [hj] at this
  rw [this, map_zero]

/-- **Null sets from polynomials.** A closed set of poses is nowhere dense if a nonzero polynomial
in `(u, q)` vanishes at every `(u, q)` with `q ≠ 0` such that `(u, quatRotation q)` is in the
set. -/
theorem isNowhereDense_of_poly {Z : Set poseSpace} (hZ : IsClosed Z)
    {P : MvPolynomial (Fin 7) ℝ} (hP : P ≠ 0)
    (h : ∀ x ∈ Z, ∀ q : Fin 4 → ℝ, q ≠ 0 → quatRotation q = x.1.2 →
      MvPolynomial.eval (join x.1.1 q) P = 0) :
    IsNowhereDense Z := by
  rw [hZ.isNowhereDense_iff, Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨W, hW, hWe⟩ := isOpen_induced_iff.mp (isOpen_interior (s := Z))
  -- The pairs `(u, q)` whose poses lie in the interior of `Z`.
  let θ : (Fin 3 → ℝ) × (Fin 4 → ℝ) → (Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ :=
    fun y ↦ (y.1, quatRotation y.2)
  set X : Set ((Fin 3 → ℝ) × (Fin 4 → ℝ)) := {y | y.1 ≠ 0 ∧ y.2 ≠ 0}
  have hX : IsOpen X :=
    (isOpen_ne_fun continuous_fst continuous_const).inter
      (isOpen_ne_fun continuous_snd continuous_const)
  have hθ : ContinuousOn θ X := fun y hy ↦
    (continuousAt_fst.prodMk ((continuous_quatRotation_at hy.2).comp
      continuousAt_snd)).continuousWithinAt
  have hint (y : (Fin 3 → ℝ) × (Fin 4 → ℝ)) (hy : y ∈ X ∩ θ ⁻¹' W) :
      (⟨θ y, hy.1.1, quatRotation_mem hy.1.2⟩ : poseSpace) ∈ interior Z := by
    rw [← hWe]
    exact hy.2
  refine hP (eq_zero_of_isOpen (hθ.isOpen_inter_preimage hX hW) ?_ fun y hy ↦
    h _ (interior_subset (hint y hy)) y.2 hy.1.2 rfl)
  obtain ⟨⟨u, R⟩, hu, hR⟩ := x
  obtain ⟨q, hq, rfl⟩ := exists_quat_of_mem_SO3 hR
  refine ⟨(u, q), ⟨hu, hq⟩, ?_⟩
  have : (⟨(u, quatRotation q), hu, hR⟩ : poseSpace) ∈ (↑) ⁻¹' W := by
    rw [hWe]
    exact hx
  exact this

/-! ### Weak exclusion -/

namespace Polyhedron

variable {P : Polyhedron}

/-- **Fits form an open set of poses.** -/
theorem isOpen_fitsPose (P : Polyhedron) :
    IsOpen {x : poseSpace | P.FitsAlong x.1.1 x.1.2} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  exact FitsAlong.eventually (υ := fun x : poseSpace ↦ x.1.1) (ρ := fun x : poseSpace ↦ x.1.2)
    (continuous_fst.comp continuous_subtype_val).continuousAt
    (continuous_snd.comp continuous_subtype_val).continuousAt x.2.1 hx

/-- **Weak symmetry exclusion** (part (b) of the density theorem). Let the vertices of `P` span
space about `c`, let `f` be a real function of poses that does not depend on the length of the
view direction, and let `N` be a set of poses, meagre in `poseSpace`, that does not depend on the
length of the view direction either. If at every pose of the unit chart boxes `P` has no fit,
some pose map of signed symmetries increases `f`, or the pose lies in `N`, then `P` is not
Rupert. -/
theorem not_isRupert_of_excluded_off {c : Fin 3 → ℝ}
    (hspan : Submodule.span ℝ ((· - c) '' (P.vertices : Set (Fin 3 → ℝ))) = ⊤)
    (f : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ → ℝ)
    (hf : ∀ (a : ℝ) u R, a ≠ 0 → f (a • u) R = f u R)
    {N : Set ((Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ)}
    (hN : IsMeagre ((↑) ⁻¹' N : Set poseSpace))
    (hNs : ∀ (a : ℝ) u R, a ≠ 0 → (a • u, R) ∈ N → (u, R) ∈ N)
    (h : ∀ p ∈ unitPoses, (∀ τ, ¬ P.FitsAt p τ) ∨ P.Excluded c f p ∨ p.pose ∈ N) :
    ¬ P.IsRupert := by
  intro hP
  obtain ⟨p₀, -, τ₀, hp₀⟩ := hP.exists_fitsAt
  -- The pose maps of signed symmetries, finitely many.
  have hS : ({x : Matrix (Fin 3) (Fin 3) ℝ × ℝ | P.IsSignedSymm c x.1 x.2} ×ˢ
      {x : Matrix (Fin 3) (Fin 3) ℝ × ℝ | P.IsSignedSymm c x.1 x.2}).Countable :=
    ((finite_signedSymm hspan).prod (finite_signedSymm hspan)).countable
  have hbad : IsMeagre (⋃ y ∈ {x : Matrix (Fin 3) (Fin 3) ℝ × ℝ | P.IsSignedSymm c x.1 x.2} ×ˢ
      {x : Matrix (Fin 3) (Fin 3) ℝ × ℝ | P.IsSignedSymm c x.1 x.2},
      {x : poseSpace | poseMap y.1.1 y.2.1 (y.1.2 * y.2.2) x ∈ N}) :=
    isMeagre_biUnion hS fun y hy ↦
      isMeagre_poseMap_preimage hy.1.1 hy.2.1 (hy.1.sign_mul hy.2) hN
  -- A fit whose orbit avoids `N` (the fits are a nonempty open set of poses).
  obtain ⟨x₀, hx₀, hx₀N⟩ : ∃ x : poseSpace, P.FitsAlong x.1.1 x.1.2 ∧ ∀ A σ B τ,
      P.IsSignedSymm c A σ → P.IsSignedSymm c B τ → poseMap A B (σ * τ) x ∉ N := by
    by_contra! H
    refine not_isMeagre_of_isOpen P.isOpen_fitsPose
      ⟨⟨p₀.pose, p₀.pose_mem⟩, fitsAlong_of_fitsAt hp₀⟩ (hbad.mono fun x hx ↦ ?_)
    obtain ⟨A, σ, B, τ, hA, hB, hN'⟩ := H x hx
    exact Set.mem_biUnion (x := ((A, σ), (B, τ))) ⟨hA, hB⟩ hN'
  -- The pose of its orbit that maximises `f`.
  obtain ⟨A₀, σ₀, B₀, τ₀, hA₀, hB₀, hmax, -⟩ := exists_orbit_max hspan f x₀.1.1 x₀.1.2
  have hu : A₀ *ᵥ x₀.1.1 ≠ 0 := mulVec_ne_zero_of_mem_SO3 hA₀.1 x₀.2.1
  have hR : turn (σ₀ * τ₀) (A₀ *ᵥ x₀.1.1) * A₀ * x₀.1.2 * B₀ ∈ SO(3) :=
    mul_mem (mul_mem (mul_mem (turn_mem _ hu) hA₀.1) x₀.2.2) hB₀.1
  obtain ⟨p, hp, ⟨τ, hτ⟩, ⟨a, ha, hpu⟩, hpR⟩ := (hx₀.symm hA₀ hB₀).exists_unitPoses hu hR
  rcases h p hp with hno | ⟨A, σ, B, τ', hA, hB, hlt⟩ | hnull
  · exact hno τ hτ
  · rw [hpu, hpR, mulVec_smul, turn_smul ha, hf _ _ _ ha, hf _ _ _ ha] at hlt
    exact (hmax A σ B τ' hA hB).not_gt hlt
  · refine hx₀N A₀ σ₀ B₀ τ₀ hA₀ hB₀ (hNs a _ _ ha ?_)
    have hpose : p.pose = (a • (A₀ *ᵥ x₀.1.1),
        turn (σ₀ * τ₀) (A₀ *ᵥ x₀.1.1) * A₀ * x₀.1.2 * B₀) := by
      rw [ChartPose.pose, hpu, hpR]
    rw [hpose] at hnull
    exact hnull

end Polyhedron

end Nieuwland
