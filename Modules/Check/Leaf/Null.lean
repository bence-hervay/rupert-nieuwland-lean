import Modules.Check.Chart.ChartBox
import Modules.Check.Leaf.Exclusion
import Modules.NoFit.Generic

/-!
# The null set of a certificate

Leaves with weak conditions (chart trees, `lean/DESIGN.md` §8, G3 part (b)) settle the poses of
their boxes except on exceptional sets. Every exceptional set lies in the null set `null F` of the
certificate's score `F` over `κ`, a fixed countable union of nowhere dense sets of poses:

* `viewNull κ`: view directions orthogonal to a nonzero vector with coordinates in `κ`
  (exceptional vectors of support witnesses, and boundaries of boxes in the view coordinates);
* `quatNull κ`: rotations whose quaternions, as row `k` of `rotQuat`, are orthogonal to a nonzero
  vector with coordinates in `κ` (boundaries of boxes in the rotation coordinates, also of boxes
  pre-rotated by a quaternion over `κ`);
* `tieNull κ F`: ties `F (g x) = F x` of a pose map `g` of two symmetries over `κ`, for the pairs
  whose tie set is nowhere dense (zeros of the improvement numerators of exclusion leaves).

The unions are countable when `κ` is, as the types of exact values are.

Each is nowhere dense by the identity theorem (`isNowhereDense_of_poly`); for a tie set, a point
where the improvement numerator does not vanish shows that the polynomial is not zero
(`isNowhereDense_tieSet`). So `null κ F` is meagre (`isMeagre_null`), and it does not depend on the
length of the view direction (`null_smul`): weak symmetry exclusion
(`Polyhedron.not_isRupert_of_excluded_off`) applies to poses that are `Settled`.
-/

open Matrix

namespace Nieuwland

theorem rotQuat_quatRotation {q : Fin 4 → ℝ} (hq : q ≠ 0) (k : Fin 4) :
    rotQuat (quatRotation q) k = (4 * q k / (q ⬝ᵥ q)) • q := by
  have hd : q ⬝ᵥ q ≠ 0 := dotProduct_self_eq_zero.not.mpr hq
  have hd' : q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 ≠ 0 := by
    simpa [dotProduct, Fin.sum_univ_four, sq] using hd
  funext j
  fin_cases k <;> fin_cases j <;>
    simp [rotQuat, quatRotation, quatMatrix, dotProduct, Fin.sum_univ_four] <;>
    field_simp <;> ring

theorem continuous_rotQuat (k : Fin 4) :
    Continuous fun R : Matrix (Fin 3) (Fin 3) ℝ ↦ rotQuat R k := by
  refine continuous_pi fun j ↦ ?_
  have h (a b : Fin 3) : Continuous fun R : Matrix (Fin 3) (Fin 3) ℝ ↦ R a b :=
    (continuous_apply b).comp (continuous_apply a)
  fin_cases k <;> fin_cases j <;> simp only [rotQuat] <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, cons_val_zero,
      cons_val_one, cons_val] <;>
    fun_prop

theorem continuousOn_orbitScore (a b : ℝ) {w : Fin 3 → ℝ} (hw : w ≠ 0) :
    ContinuousOn (fun x : (Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ ↦ orbitScore a b w x.1 x.2)
      {x | x.1 ≠ 0} := by
  intro x hx
  have hww : w ⬝ᵥ w ≠ 0 := dotProduct_self_eq_zero.not.mpr hw
  have huu : x.1 ⬝ᵥ x.1 ≠ 0 := dotProduct_self_eq_zero.not.mpr hx
  have h1 : Continuous fun x : (Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ ↦ x.1 ⬝ᵥ w :=
    continuous_fst.dotProduct continuous_const
  have h2 : Continuous fun x : (Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ ↦ x.1 ⬝ᵥ x.1 :=
    continuous_fst.dotProduct continuous_fst
  have h3 : Continuous fun x : (Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ ↦ trace x.2 :=
    continuous_snd.matrix_trace
  exact (((continuousAt_const.mul (h1.continuousAt.pow 2)).div
    (h2.continuousAt.mul continuousAt_const) (mul_ne_zero huu hww)).add
      (continuousAt_const.mul h3.continuousAt)).continuousWithinAt

namespace Check

instance {α : Type*} [Countable α] : Countable (V3 α) :=
  Function.Injective.countable (f := fun v : V3 α ↦ (v.x, v.y, v.z)) fun a b h ↦ by
    obtain ⟨_, _, _⟩ := a
    obtain ⟨_, _, _⟩ := b
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl

instance {α : Type*} [Countable α] : Countable (Q4 α) :=
  Function.Injective.countable (f := fun q : Q4 α ↦ (q.w, q.x, q.y, q.z)) fun a b h ↦ by
    obtain ⟨_, _, _, _⟩ := a
    obtain ⟨_, _, _, _⟩ := b
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    rfl

instance {d : ℕ} : Countable (ZSqrt d) :=
  Function.Injective.countable (f := fun x : ZSqrt d ↦ (x.a, x.b)) fun a b h ↦ by
    obtain ⟨_, _⟩ := a
    obtain ⟨_, _⟩ := b
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

instance {κ : Type} [Countable κ] : Countable (Symm κ) :=
  Function.Injective.countable (f := fun S : Symm κ ↦ (S.g, S.den, S.img)) fun a b h ↦ by
    obtain ⟨_, _, _⟩ := a
    obtain ⟨_, _, _⟩ := b
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl

/-! ### The generators -/

section Generators

variable (κ : Type) [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- Poses whose view direction is orthogonal to a nonzero vector with exact coordinates. -/
def viewNull : Set ((Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ) :=
  ⋃ w : {w : V3 κ // Exact.reV w ≠ 0}, {x | Exact.reV w.1 ⬝ᵥ x.1 = 0}

/-- Poses whose rotation has a quaternion row `rotQuat R k` orthogonal to a nonzero vector with
exact coordinates. -/
def quatNull : Set ((Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ) :=
  ⋃ y : Fin 4 × {v : Q4 κ // Exact.reQ v ≠ 0}, {x | Exact.reQ y.2.1 ⬝ᵥ rotQuat x.2 y.1 = 0}

variable {κ}

/-- The tie set of the symmetries `S₁`, `S₂` for the score `F`: the poses whose score their pose
map does not change. -/
def tieSet (F : Score) (S₁ S₂ : Symm κ) : Set ((Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ) :=
  {x | F.f (poseMap S₁.rot S₂.rot (S₁.sign * S₂.sign) x).1
    (poseMap S₁.rot S₂.rot (S₁.sign * S₂.sign) x).2 = F.f x.1 x.2}

variable (κ)

/-- The ties of the pairs of symmetries whose tie sets are nowhere dense. -/
def tieNull (F : Score) : Set ((Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ) :=
  ⋃ y : {y : Symm κ × Symm κ // IsNowhereDense ((↑) ⁻¹' tieSet F y.1 y.2 : Set poseSpace)},
    tieSet F y.1.1 y.1.2

/-- **The null set** of a certificate over `κ` with the score `F`. -/
def null (F : Score) : Set ((Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ) :=
  viewNull κ ∪ quatNull κ ∪ tieNull κ F

end Generators

/-! ### The null set is meagre -/

theorem isNowhereDense_view (w : Fin 3 → ℝ) (hw : w ≠ 0) :
    IsNowhereDense ((↑) ⁻¹' {x : (Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ |
      w ⬝ᵥ x.1 = 0} : Set poseSpace) := by
  set P : MvPolynomial (Fin 7) ℝ := MvPolynomial.C (w 0) * MvPolynomial.X 0 +
    MvPolynomial.C (w 1) * MvPolynomial.X 1 + MvPolynomial.C (w 2) * MvPolynomial.X 2
  have hev (u : Fin 3 → ℝ) (q : Fin 4 → ℝ) : MvPolynomial.eval (join u q) P = w ⬝ᵥ u := by
    simp [P, join, dotProduct, Fin.sum_univ_three]
  refine isNowhereDense_of_poly ?_ (fun h0 ↦ hw ?_) fun x hx q _ _ ↦ by rw [hev]; exact hx
  · exact isClosed_eq ((continuous_const.dotProduct continuous_fst).comp continuous_subtype_val)
      continuous_const
  · have h := hev w 0
    rw [h0, map_zero] at h
    exact dotProduct_self_eq_zero.mp h.symm

theorem isNowhereDense_quat (k : Fin 4) (v : Fin 4 → ℝ) (hv : v ≠ 0) :
    IsNowhereDense ((↑) ⁻¹' {x : (Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ |
      v ⬝ᵥ rotQuat x.2 k = 0} : Set poseSpace) := by
  set lin : MvPolynomial (Fin 7) ℝ := MvPolynomial.C (v 0) * MvPolynomial.X 3 +
    MvPolynomial.C (v 1) * MvPolynomial.X 4 + MvPolynomial.C (v 2) * MvPolynomial.X 5 +
    MvPolynomial.C (v 3) * MvPolynomial.X 6
  have hlin (u : Fin 3 → ℝ) (q : Fin 4 → ℝ) :
      MvPolynomial.eval (join u q) lin = v ⬝ᵥ q := by
    simp [lin, join, dotProduct, Fin.sum_univ_four]
  have hXk (u : Fin 3 → ℝ) (q : Fin 4 → ℝ) :
      MvPolynomial.eval (join u q) (MvPolynomial.X (Fin.natAdd 3 k)) = q k := by
    rw [MvPolynomial.eval_X]
    fin_cases k <;> rfl
  have hlin0 : lin ≠ 0 := fun h0 ↦ hv (by
    have h := hlin 0 v
    rw [h0, map_zero] at h
    exact dotProduct_self_eq_zero.mp h.symm)
  refine isNowhereDense_of_poly (P := MvPolynomial.X (Fin.natAdd 3 k) * lin) ?_
    (mul_ne_zero (MvPolynomial.X_ne_zero _) hlin0) fun x hx q hq hR ↦ ?_
  · exact isClosed_eq ((continuous_const.dotProduct ((continuous_rotQuat k).comp
      continuous_snd)).comp continuous_subtype_val) continuous_const
  · have hd : q ⬝ᵥ q ≠ 0 := dotProduct_self_eq_zero.not.mpr hq
    have h : v ⬝ᵥ rotQuat x.1.2 k = 0 := hx
    rw [← hR, rotQuat_quatRotation hq, dotProduct_smul, smul_eq_mul] at h
    rw [map_mul, hXk, hlin]
    rcases mul_eq_zero.mp h with h | h
    · rw [div_eq_zero_iff, mul_eq_zero] at h
      rcases h with (h | h) | h
      · norm_num at h
      · rw [h, zero_mul]
      · exact absurd h hd
    · rw [h, mul_zero]

section Meagre

variable (κ : Type) [Add κ] [Sub κ] [Mul κ] [Exact κ] [Countable κ]

theorem isMeagre_viewNull : IsMeagre ((↑) ⁻¹' viewNull κ : Set poseSpace) := by
  rw [viewNull, Set.preimage_iUnion]
  exact isMeagre_iUnion fun w ↦ (isNowhereDense_view _ w.2).isMeagre

theorem isMeagre_quatNull : IsMeagre ((↑) ⁻¹' quatNull κ : Set poseSpace) := by
  rw [quatNull, Set.preimage_iUnion]
  exact isMeagre_iUnion fun y ↦ (isNowhereDense_quat y.1 _ y.2.2).isMeagre

theorem isMeagre_tieNull (F : Score) : IsMeagre ((↑) ⁻¹' tieNull κ F : Set poseSpace) := by
  rw [tieNull, Set.preimage_iUnion]
  exact isMeagre_iUnion fun y ↦ y.2.isMeagre

theorem isMeagre_null (F : Score) : IsMeagre ((↑) ⁻¹' null κ F : Set poseSpace) := by
  rw [null, Set.preimage_union, Set.preimage_union]
  exact (isMeagre_viewNull κ |>.union (isMeagre_quatNull κ)).union (isMeagre_tieNull κ F)

end Meagre

/-- The null set does not depend on the length of the view direction. -/
theorem null_smul {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] (F : Score) (a : ℝ)
    (u : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) (ha : a ≠ 0) (h : (a • u, R) ∈ null κ F) :
    (u, R) ∈ null κ F := by
  simp only [null, viewNull, quatNull, tieNull, Set.mem_union, Set.mem_iUnion,
    Set.mem_ofPred_eq] at h ⊢
  rcases h with (⟨w, hw⟩ | ⟨y, hy⟩) | ⟨y, hy⟩
  · refine Or.inl (Or.inl ⟨w, ?_⟩)
    rw [dotProduct_smul, smul_eq_mul] at hw
    exact (mul_eq_zero.mp hw).resolve_left ha
  · exact Or.inl (Or.inr ⟨y, hy⟩)
  · refine Or.inr ⟨y, ?_⟩
    simp only [tieSet, poseMap, Set.mem_ofPred_eq, mulVec_smul, turn_smul ha, Score.f,
      orbitScore_smul _ _ _ ha] at hy ⊢
    exact hy

/-! ### Members of the null set -/

section Members

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

theorem mem_viewNull_of {x : (Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ} {a b : Fin 3}
    (hab : a ≠ b) {d r : ℤ} (hd : d ≠ 0) (h : (d : ℝ) * x.1 b - r * x.1 a = 0) :
    x ∈ viewNull κ := by
  set w : Fin 3 → ℤ := Pi.single b d - Pi.single a r
  set v : V3 κ := (V3.mk (w 0) (w 1) (w 2)).map Exact.ofInt
  have hwi (i : Fin 3) :
      ((w i : ℤ) : ℝ) = (Pi.single b (d : ℝ) - Pi.single a (r : ℝ) : Fin 3 → ℝ) i := by
    simp only [w, Pi.sub_apply, Pi.single_apply, Int.cast_sub]
    split_ifs <;> simp
  have hv : Exact.reV v = Pi.single b (d : ℝ) - Pi.single a (r : ℝ) := by
    funext i
    rw [← hwi]
    fin_cases i <;> simp [v, Exact.reV, V3.map, V3.toFun, Exact.re_ofInt]
  have hw : Exact.reV v ≠ 0 := fun h0 ↦ hd (by
    have := congrFun (hv.symm.trans h0) b
    simpa [Pi.single_apply, hab.symm] using this)
  refine Set.mem_iUnion.mpr ⟨⟨v, hw⟩, ?_⟩
  change Exact.reV v ⬝ᵥ x.1 = 0
  rw [hv, sub_dotProduct, single_dotProduct, single_dotProduct, h]

theorem mem_quatNull_of {x : (Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ} {w : Q4 κ}
    (hw : Exact.reQ w ≠ 0) {q : Fin 4 → ℝ} (hq : q ≠ 0) (hx : x.2 = quatRotation q)
    (h : Exact.reQ w ⬝ᵥ q = 0) : x ∈ quatNull κ := by
  refine Set.mem_iUnion.mpr ⟨(0, ⟨w, hw⟩), ?_⟩
  change Exact.reQ w ⬝ᵥ rotQuat x.2 0 = 0
  rw [hx, rotQuat_quatRotation hq, dotProduct_smul, h, smul_zero]

/-- A rotation `R(q) R(c)` whose quaternion `q` satisfies `d q_j = r q_k` (integers `d ≠ 0`, `r`),
with the pre-rotation `c` over `κ`, if any: its quaternion `q c` is orthogonal to
`(d e_j - r e_k) c` (`qmul_dot_qmul`). -/
theorem mem_quatNull_of_int {x : (Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ} {k j : Fin 4}
    (hkj : k ≠ j) {d r : ℤ} (hd : d ≠ 0) {q : Fin 4 → ℝ} (hq : q ≠ 0) {pre : Option (Q4 κ)}
    (hpre : ∀ c ∈ Exact.rePre pre, c ≠ 0) (hx : x.2 = quatRotation q * preRot (Exact.rePre pre))
    (h : (d : ℝ) * q j - r * q k = 0) : x ∈ quatNull κ := by
  set f : Fin 4 → ℤ := Pi.single j d - Pi.single k r
  set e : Q4 κ := (⟨f 0, f 1, f 2, f 3⟩ : Q4 ℤ).map Exact.ofInt
  have he : Exact.reQ e = Pi.single j (d : ℝ) - Pi.single k (r : ℝ) := by
    have hf : (fun i ↦ (f i : ℝ)) = Pi.single j (d : ℝ) - Pi.single k (r : ℝ) := by
      funext i
      simp only [f, Pi.sub_apply, Pi.single_apply, Int.cast_sub]
      split_ifs <;> simp
    rw [← hf]
    funext i
    fin_cases i <;> simp [e, Exact.reQ, Q4.map, Q4.toFun, Exact.re_ofInt]
  have he0 : Exact.reQ e ≠ 0 := fun h0 ↦ hd (by
    have := congrFun (he.symm.trans h0) j
    simpa [Pi.single_apply, hkj.symm] using this)
  refine mem_quatNull_of (w := preQ id e pre) ?_ (preQuat_ne_zero hq hpre)
    (by rw [hx, quatRotation_preQuat]) ?_
  · rw [reQ_preQ]
    exact preQuat_ne_zero he0 hpre
  · rw [reQ_preQ]
    apply preQuat_dot_eq_zero
    rw [he, sub_dotProduct, single_dotProduct, single_dotProduct, h]

/-- A view direction orthogonal to a vector known to be nonzero is null. -/
theorem mem_null_of_view {F : Score} {x : (Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ} {g : V3 κ}
    (hg : Exact.nonzeroV g = true) (h : Exact.reV g ⬝ᵥ x.1 = 0) : x ∈ null κ F :=
  Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨⟨g, Exact.reV_ne_zero_of_nonzeroV hg⟩, h⟩))

/-- **Chart poses on rational hyperplanes are null**: a chart coordinate `r / d`, with the
rotation followed by a pre-rotation over `κ`, if any. -/
theorem mem_null_of_coord {F : Score} (p : ChartPose) {pre : Option (Q4 κ)}
    (hpre : ∀ c ∈ Exact.rePre pre, c ≠ 0) (i : Fin 5) {r d : ℤ} (hd : d ≠ 0)
    (h : p.coords i = r / d) :
    (viewDir p.view p.s p.t, p.rotation * preRot (Exact.rePre pre)) ∈ null κ F := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have h' : (d : ℝ) * p.coords i - r * 1 = 0 := by rw [h]; field_simp; ring
  obtain ⟨a, s, t, k, x⟩ := p
  have hk (m : Fin 3) : chartQuat k x (k.succAbove m) = x m := by
    fin_cases k <;> fin_cases m <;> rfl
  have hrot (m : Fin 3) (hm : (d : ℝ) * x m - r * 1 = 0) :
      (viewDir a s t, (⟨a, s, t, k, x⟩ : ChartPose).rotation * preRot (Exact.rePre pre)) ∈
        quatNull κ :=
    mem_quatNull_of_int (Fin.succAbove_ne k m).symm hd (chartQuat_ne_zero k x) hpre rfl
      (by rw [hk, chartQuat_self]; exact hm)
  have hab (b : Fin 3) (hb : b = 1 ∨ b = 2) : a ≠ a + b := by
    rcases hb with rfl | rfl <;> fin_cases a <;> decide
  refine Or.inl ?_
  fin_cases i
  · refine Or.inl (mem_viewNull_of (r := r) (hab 1 (Or.inl rfl)) hd ?_)
    simpa [ChartPose.coords, viewDir] using h'
  · refine Or.inl (mem_viewNull_of (r := r) (hab 2 (Or.inr rfl)) hd ?_)
    simpa [ChartPose.coords, viewDir] using h'
  · exact Or.inr (hrot 0 h')
  · exact Or.inr (hrot 1 h')
  · exact Or.inr (hrot 2 h')

end Members

/-! ### Ties of exclusion leaves -/

section Ties

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The improvement numerator as a polynomial in `(u, q)`. -/
noncomputable def improvementMv (d : Improvement κ) : MvPolynomial (Fin 7) ℝ :=
  improvementG (fun z ↦ MvPolynomial.C (Exact.re z)) d
    ⟨MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2⟩
    ⟨MvPolynomial.X 3, MvPolynomial.X 4, MvPolynomial.X 5, MvPolynomial.X 6⟩

theorem isArith_mvEval (y : Fin 7 → ℝ) : IsArith (MvPolynomial.eval y) :=
  ⟨map_add _, map_sub _, map_mul _⟩

theorem eval_improvementMv (d : Improvement κ) (u : Fin 3 → ℝ) (q : Fin 4 → ℝ) :
    MvPolynomial.eval (join u q) (improvementMv d) = improvementPoly d u q := by
  rw [improvementMv, map_improvementG (isArith_mvEval _)]
  have hk : (MvPolynomial.eval (join u q) ∘ fun z : κ ↦ MvPolynomial.C (Exact.re z)) =
      Exact.re := by
    funext z
    simp
  rw [hk, improvementG_re]
  congr 1
  · funext i
    fin_cases i <;> simp [V3.map, V3.toFun, join]
  · funext i
    fin_cases i <;> simp [Q4.map, Q4.toFun, join]

/-- The improvement numerator at an integer point, computed in `κ`. -/
theorem improvementPoly_intPoint (d : Improvement κ) (U : V3 ℤ) (Q : Q4 ℤ) :
    improvementPoly d (V3.cast ℝ U) (Q.map (Int.cast : ℤ → ℝ)).toFun =
      Exact.re (improvementG id d (U.map Exact.ofInt) (Q.map Exact.ofInt)) := by
  rw [map_improvementG Exact.isArith, Function.comp_id]
  have hU : (U.map (Exact.ofInt : ℤ → κ)).map Exact.re = U.map Int.cast := by
    simp only [V3.map, Exact.re_ofInt]
  have hQ : (Q.map (Exact.ofInt : ℤ → κ)).map Exact.re = Q.map Int.cast := by
    simp only [Q4.map, Exact.re_ofInt]
  rw [hU, hQ, improvementG_re]
  rfl

theorem tieSet_iff {pts : List (V3 κ)} {C : V3 κ} {m : ℕ} {F : Score} {S₁ S₂ : Symm κ}
    (h₁ : S₁.ok pts C m = true) (h₂ : S₂.ok pts C m = true) (hw : F.w.dot F.w ≠ 0)
    {u : Fin 3 → ℝ} (hu : u ≠ 0) {q : Fin 4 → ℝ} (hq : q ≠ 0) :
    (u, quatRotation q) ∈ tieSet F S₁ S₂ ↔
      improvementPoly (Improvement.of F S₁ S₂) u q = 0 := by
  have hs₁ : (S₁.den : ℝ) ≠ 0 := by exact_mod_cast (Symm.den_pos_of_ok h₁).ne'
  have hs₂ : (S₂.den : ℝ) ≠ 0 := by exact_mod_cast (Symm.den_pos_of_ok h₂).ne'
  have hw' : V3.cast ℝ F.w ≠ 0 := fun h0 ↦ hw (by
    have : ((F.w.dot F.w : ℤ) : ℝ) = V3.cast ℝ F.w ⬝ᵥ V3.cast ℝ F.w := V3.cast_dot _ _
    rw [h0, dotProduct_zero] at this
    exact_mod_cast this)
  have hpos : (S₁.den : ℝ) ^ 2 * S₂.den * (u ⬝ᵥ u) * (V3.cast ℝ F.w ⬝ᵥ V3.cast ℝ F.w) *
      (q ⬝ᵥ q) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hs₁) hs₂)
      (dotProduct_self_eq_zero.not.mpr hu)) (dotProduct_self_eq_zero.not.mpr hw'))
      (dotProduct_self_eq_zero.not.mpr hq)
  rw [improvementPoly_eq h₁ h₂ hw hu hq, mul_eq_zero, or_iff_right hpos, sub_eq_zero]
  rfl

/-- **Tie sets are nowhere dense** where the improvement numerator does not vanish somewhere:
at the integer point `(U, Q)`, by the nonzero test of `κ`. -/
theorem isNowhereDense_tieSet {pts : List (V3 κ)} {C : V3 κ} {m : ℕ} {F : Score}
    {S₁ S₂ : Symm κ} (h₁ : S₁.ok pts C m = true) (h₂ : S₂.ok pts C m = true)
    (hw : F.w.dot F.w ≠ 0) {U : V3 ℤ} {Q : Q4 ℤ}
    (hUQ : Exact.nonzero (improvementG id (Improvement.of F S₁ S₂) (U.map Exact.ofInt)
      (Q.map Exact.ofInt)) = true) :
    IsNowhereDense ((↑) ⁻¹' tieSet F S₁ S₂ : Set poseSpace) := by
  have hA := Symm.rot_mem_of_ok h₁
  have hB := Symm.rot_mem_of_ok h₂
  have hw' : V3.cast ℝ F.w ≠ 0 := fun h0 ↦ hw (by
    have : ((F.w.dot F.w : ℤ) : ℝ) = V3.cast ℝ F.w ⬝ᵥ V3.cast ℝ F.w := V3.cast_dot _ _
    rw [h0, dotProduct_zero] at this
    exact_mod_cast this)
  have hf := continuousOn_orbitScore F.a F.b hw'
  have hφ : ContinuousOn (fun x ↦ F.f (poseMap S₁.rot S₂.rot (S₁.sign * S₂.sign) x).1
      (poseMap S₁.rot S₂.rot (S₁.sign * S₂.sign) x).2) poseSpace :=
    hf.comp (continuousOn_poseMap hA) fun x hx ↦ (poseMap_mem hA hB hx).1
  have hψ : ContinuousOn (fun x : (Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ ↦ F.f x.1 x.2)
      poseSpace := hf.mono fun x hx ↦ hx.1
  refine isNowhereDense_of_poly (P := improvementMv (Improvement.of F S₁ S₂))
    (isClosed_eq hφ.domRestrict hψ.domRestrict) (fun h0 ↦ Exact.re_ne_zero_of_nonzero hUQ ?_)
    fun x hx q hq hR ↦ ?_
  · have h := eval_improvementMv (Improvement.of F S₁ S₂) (V3.cast ℝ U)
      (Q.map (Int.cast : ℤ → ℝ)).toFun
    rw [h0, map_zero, improvementPoly_intPoint] at h
    exact h.symm
  · rw [eval_improvementMv, ← tieSet_iff h₁ h₂ hw x.2.1 hq, hR]
    exact hx

theorem mem_null_of_tie {F : Score} {S₁ S₂ : Symm κ}
    (hN : IsNowhereDense ((↑) ⁻¹' tieSet F S₁ S₂ : Set poseSpace))
    {x : (Fin 3 → ℝ) × Matrix (Fin 3) (Fin 3) ℝ} (h : x ∈ tieSet F S₁ S₂) : x ∈ null κ F :=
  Or.inr (Set.mem_iUnion.mpr ⟨⟨(S₁, S₂), hN⟩, h⟩)

/-- **Weak exclusion.** Where the improvement numerator of two symmetries of `D` is nonnegative at
`(u, q)`, the pose map of the symmetries increases the score at the pose `(u, R(q))` or ties it. -/
theorem excluded_or_tie {pts : List (V3 κ)} {D : SymmData κ} (hD : D.ok pts = true)
    {S₁ S₂ : Symm κ} (hS₁ : S₁ ∈ D.syms) (hS₂ : S₂ ∈ D.syms) {u : Fin 3 → ℝ} (hu : u ≠ 0)
    {q : Fin 4 → ℝ} (hq : q ≠ 0) (h : 0 ≤ improvementPoly (Improvement.of D.score S₁ S₂) u q) :
    (Polyhedron.ofPoints pts).ExcludedAt D.centre D.score.f u (quatRotation q) ∨
      (u, quatRotation q) ∈ tieSet D.score S₁ S₂ := by
  simp only [SymmData.ok, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at hD
  have h₁ := hD.1 S₁ hS₁
  have h₂ := hD.1 S₂ hS₂
  have hw : V3.cast ℝ D.score.w ≠ 0 := fun h0 ↦ hD.2 (by
    have : ((D.score.w.dot D.score.w : ℤ) : ℝ) = V3.cast ℝ D.score.w ⬝ᵥ V3.cast ℝ D.score.w :=
      V3.cast_dot _ _
    rw [h0, dotProduct_zero] at this
    exact_mod_cast this)
  have hpos {k : ℕ} {v : Fin k → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _)
      (Ne.symm (dotProduct_self_eq_zero.not.mpr hv))
  have hs₁ : (0 : ℝ) < S₁.den := by exact_mod_cast Symm.den_pos_of_ok h₁
  have hs₂ : (0 : ℝ) < S₂.den := by exact_mod_cast Symm.den_pos_of_ok h₂
  rw [improvementPoly_eq h₁ h₂ hD.2 hu hq] at h
  have hd := (mul_nonneg_iff_of_pos_left (mul_pos (mul_pos (mul_pos (mul_pos (pow_pos hs₁ 2)
    hs₂) (hpos hu)) (hpos hw)) (hpos hq))).mp h
  rcases hd.lt_or_eq with hlt | heq
  · exact Or.inl ⟨S₁.rot, S₁.sign, S₂.rot, S₂.sign, Symm.ok_sound h₁, Symm.ok_sound h₂,
      sub_pos.mp hlt⟩
  · exact Or.inr (sub_eq_zero.mp heq.symm)

end Ties

/-! ### Settled poses -/

/-- At the pose `p`, the polyhedron of `pts` has no fit, `p` is excluded by the symmetry data `D`,
or `p` lies in the null set of the score of `D`. -/
def Settled {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] (pts : List (V3 κ)) (D : SymmData κ)
    (p : ChartPose) : Prop :=
  (∀ τ, ¬ (Polyhedron.ofPoints pts).FitsAt p τ) ∨
    (Polyhedron.ofPoints pts).Excluded D.centre D.score.f p ∨ p.pose ∈ null κ D.score

section SettledAt

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- At the pose `(u, R)`, the polyhedron of `pts` has no fit, some pose map of signed symmetries
increases the score of `D`, or the pose is null: `Settled` for any pose. -/
def SettledAt (pts : List (V3 κ)) (D : SymmData κ) (u : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ¬ (Polyhedron.ofPoints pts).FitsAlong u R ∨
    (Polyhedron.ofPoints pts).ExcludedAt D.centre D.score.f u R ∨ (u, R) ∈ null κ D.score

/-- `SettledAt` the pose of `p` with its rotation followed by the pre-rotation `c`, if any. -/
def SettledRot (pts : List (V3 κ)) (D : SymmData κ) (c : Option (Fin 4 → ℝ))
    (p : ChartPose) : Prop :=
  SettledAt pts D (viewDir p.view p.s p.t) (p.rotation * preRot c)

/-- Settled poses do not depend on the length of the view direction. -/
theorem SettledAt.of_smul {pts : List (V3 κ)} {D : SymmData κ} {a : ℝ} (ha : a ≠ 0)
    {u : Fin 3 → ℝ} {R : Matrix (Fin 3) (Fin 3) ℝ} (h : SettledAt pts D (a • u) R) :
    SettledAt pts D u R := by
  rcases h with h | h | h
  · exact Or.inl fun h' ↦ h (h'.smul ha)
  · exact Or.inr (Or.inl (h.of_smul (fun _ u R ha ↦ orbitScore_smul _ _ _ ha u R) ha))
  · exact Or.inr (Or.inr (null_smul D.score a u R ha h))

/-- **Without a pre-rotation**, `SettledRot` is `Settled`. -/
theorem settledRot_none {pts : List (V3 κ)} {D : SymmData κ} {p : ChartPose} :
    SettledRot pts D none p ↔ Settled pts D p := by
  rw [SettledRot, preRot_none, mul_one]
  refine or_congr ⟨fun h τ hfit ↦ h (Polyhedron.fitsAlong_of_fitsAt hfit), fun h hfit ↦ ?_⟩
    Iff.rfl
  obtain ⟨τ, hτ⟩ := hfit.exists_fitsAt (p := p) one_ne_zero (one_smul ℝ _).symm rfl
  exact h τ hτ

end SettledAt

end Check

end Nieuwland
