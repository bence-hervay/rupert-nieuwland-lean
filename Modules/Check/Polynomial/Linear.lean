import Modules.Check.Number.Exact
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Linear algebra by exact tests

Square matrices by rows over exact values (`Exact κ`), checked by zero and sign tests: inverses up
to a determinant (`mulOk`, `mul_inv_apply`), and bounds of linear forms on boxes by their values at
the corners (`corners`, `sum_mem_of_corners`, `coverOk`). Weighted-zoom frames
(`Modules/Check/Leaf/WZoom.lean`) and slot-affine steps of chart trees (`Modules/Check/Chart/Affine.lean`) use
them.
-/

namespace Nieuwland.Check

/-! ### Square matrices by rows -/

theorem sum_map_range_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_map_range_eq f n,
      Finset.sum_range_succ]
    simp

/-- **Inverses up to the determinant.** If `M N = Δ I` with `Δ ≠ 0`, then `M (N v / Δ) = v`. -/
theorem mul_inv_apply {n : ℕ} {M N : ℕ → ℕ → ℝ} {Δ : ℝ}
    (h : ∀ r c, r < n → c < n → ∑ j ∈ Finset.range n, M r j * N j c = if r = c then Δ else 0)
    (hΔ : Δ ≠ 0) (v : ℕ → ℝ) {r : ℕ} (hr : r < n) :
    ∑ c ∈ Finset.range n, M r c * ((∑ j ∈ Finset.range n, N c j * v j) / Δ) = v r := by
  have key : ∑ c ∈ Finset.range n, M r c * (∑ j ∈ Finset.range n, N c j * v j) =
      ∑ j ∈ Finset.range n, (∑ c ∈ Finset.range n, M r c * N c j) * v j := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun c _ ↦ ?_
    ring
  have key2 : ∑ j ∈ Finset.range n, (∑ c ∈ Finset.range n, M r c * N c j) * v j = Δ * v r := by
    rw [Finset.sum_congr rfl fun j hj ↦ by rw [h r j hr (Finset.mem_range.mp hj)]]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_range, hr, ↓reduceIte]
  have hc : ∀ c ∈ Finset.range n, M r c * ((∑ j ∈ Finset.range n, N c j * v j) / Δ) =
      (M r c * (∑ j ∈ Finset.range n, N c j * v j)) * Δ⁻¹ := fun c _ ↦ by ring
  rw [Finset.sum_congr rfl hc, ← Finset.sum_mul, key, key2]
  field_simp

/-- The corners of `n` intervals: the lists of `n` ends, `true` for the upper end. -/
def corners : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (corners n).flatMap fun l ↦ [false :: l, true :: l]

theorem exists_corner : ∀ (n : ℕ) (s : ℕ → Bool), ∃ l ∈ corners n, ∀ j < n, l.getD j false = s j
  | 0, _ => ⟨[], List.mem_singleton_self _, fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩
  | n + 1, s => by
    obtain ⟨l, hl, hs⟩ := exists_corner n fun j ↦ s (j + 1)
    refine ⟨s 0 :: l, List.mem_flatMap.mpr ⟨l, hl, ?_⟩, fun j hj ↦ ?_⟩
    · cases s 0 <;> simp
    · cases j with
      | zero => rfl
      | succ j => simpa using hs j (by omega)

/-- **Linear forms on boxes are bounded by their values at corners.** -/
theorem exists_corner_ge {n : ℕ} (N lo hi v : ℕ → ℝ) (hv : ∀ j < n, lo j ≤ v j ∧ v j ≤ hi j) :
    ∃ l ∈ corners n, ∑ j ∈ Finset.range n, N j * v j ≤
      ∑ j ∈ Finset.range n, N j * bif l.getD j false then hi j else lo j := by
  obtain ⟨l, hl, hs⟩ := exists_corner n fun j ↦ decide (0 ≤ N j)
  refine ⟨l, hl, Finset.sum_le_sum fun j hj ↦ ?_⟩
  have hj' := Finset.mem_range.mp hj
  rw [hs j hj']
  by_cases hN : 0 ≤ N j
  · simp only [hN, decide_true, Bool.cond_true]
    exact mul_le_mul_of_nonneg_left (hv j hj').2 hN
  · simp only [hN, decide_false, Bool.cond_false]
    exact mul_le_mul_of_nonpos_left (hv j hj').1 (not_le.mp hN).le

theorem exists_corner_le {n : ℕ} (N lo hi v : ℕ → ℝ) (hv : ∀ j < n, lo j ≤ v j ∧ v j ≤ hi j) :
    ∃ l ∈ corners n, ∑ j ∈ Finset.range n, N j * (bif l.getD j false then hi j else lo j) ≤
      ∑ j ∈ Finset.range n, N j * v j := by
  obtain ⟨l, hl, hs⟩ := exists_corner_ge (fun j ↦ -N j) lo hi v hv
  refine ⟨l, hl, ?_⟩
  simp only [neg_mul, Finset.sum_neg_distrib, neg_le_neg_iff] at hs
  exact hs

section Matrices

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- Entry `(r, c)` of a matrix given by its rows. -/
def ent (m : List (List κ)) (r c : ℕ) : κ := (m.getD r []).getD c (Exact.ofInt 0)

/-- `m N = Δ I` for `n × n` matrices, by the zero test. -/
def mulOk (n : ℕ) (m N : List (List κ)) (Δ : κ) : Bool :=
  (List.range n).all fun r ↦ (List.range n).all fun c ↦
    Exact.isZero (Exact.sumL ((List.range n).map fun j ↦ ent m r j * ent N j c) -
      if r = c then Δ else Exact.ofInt 0)

theorem mulOk_apply {n : ℕ} {m N : List (List κ)} {Δ : κ} (h : mulOk n m N Δ = true) {r c : ℕ}
    (hr : r < n) (hc : c < n) :
    ∑ j ∈ Finset.range n, Exact.re (ent m r j) * Exact.re (ent N j c) =
      if r = c then Exact.re Δ else 0 := by
  have h1 := Exact.isZero_sound _ (List.all_eq_true.mp (List.all_eq_true.mp h r
    (List.mem_range.mpr hr)) c (List.mem_range.mpr hc))
  rw [Exact.re_sub, Exact.re_sumL, List.map_map, sub_eq_zero, sum_map_range_eq] at h1
  simp only [Function.comp_def, Exact.re_mul] at h1
  rw [h1]
  split_ifs <;> simp [Exact.re_ofInt]

/-- The value `∑_j N_cj e_j` at the corner `l` of the intervals `[A_j, B_j]`. -/
def cornerVal (n : ℕ) (N : List (List κ)) (A B : List κ) (c : ℕ) (l : List Bool) : κ :=
  Exact.sumL ((List.range n).map fun j ↦ ent N c j *
    bif l.getD j false then B.getD j (Exact.ofInt 0) else A.getD j (Exact.ofInt 0))

/-- `|∑_j N_cj v_j| ≤ |D|` for all `v_j ∈ [A_j, B_j]`, at the corners: `D² - S² ≥ 0`. -/
def coverOk (n : ℕ) (N : List (List κ)) (D : κ) (A B : List κ) : Bool :=
  (List.range n).all fun c ↦ (corners n).all fun l ↦
    Exact.nonneg (D * D - cornerVal n N A B c l * cornerVal n N A B c l)

/-- The real value of a corner value. -/
theorem re_cornerVal (n : ℕ) (N : List (List κ)) (A B : List κ) (c : ℕ) (l : List Bool) :
    Exact.re (cornerVal n N A B c l) = ∑ j ∈ Finset.range n, Exact.re (ent N c j) *
      bif l.getD j false then Exact.re (B.getD j (Exact.ofInt 0)) else
        Exact.re (A.getD j (Exact.ofInt 0)) := by
  rw [cornerVal, Exact.re_sumL, List.map_map, sum_map_range_eq]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Function.comp_apply, Exact.re_mul]
  cases l.getD j false <;> rfl

/-- **Bounds at the corners bound the linear form on the box** `[A, B]`. -/
theorem sum_mem_of_corners {n : ℕ} {N : List (List κ)} {A B : List κ} {c : ℕ} {lo hi : ℝ}
    (h : ∀ l ∈ corners n, lo ≤ Exact.re (cornerVal n N A B c l) ∧
      Exact.re (cornerVal n N A B c l) ≤ hi) {v : ℕ → ℝ}
    (hv : ∀ j < n, Exact.re (A.getD j (Exact.ofInt 0)) ≤ v j ∧
      v j ≤ Exact.re (B.getD j (Exact.ofInt 0))) :
    lo ≤ ∑ j ∈ Finset.range n, Exact.re (ent N c j) * v j ∧
      ∑ j ∈ Finset.range n, Exact.re (ent N c j) * v j ≤ hi := by
  obtain ⟨lu, hlu, hu⟩ := exists_corner_ge (fun j ↦ Exact.re (ent N c j)) _ _ v hv
  obtain ⟨ll, hll, hl⟩ := exists_corner_le (fun j ↦ Exact.re (ent N c j)) _ _ v hv
  have h1 := (h ll hll).1
  have h2 := (h lu hlu).2
  rw [re_cornerVal] at h1 h2
  exact ⟨h1.trans hl, hu.trans h2⟩

theorem coverOk_sound {n : ℕ} {N : List (List κ)} {D : κ} {A B : List κ}
    (h : coverOk n N D A B = true) {v : ℕ → ℝ}
    (hv : ∀ j < n, Exact.re (A.getD j (Exact.ofInt 0)) ≤ v j ∧
      v j ≤ Exact.re (B.getD j (Exact.ofInt 0))) {c : ℕ} (hc : c < n) :
    |∑ j ∈ Finset.range n, Exact.re (ent N c j) * v j| ≤ |Exact.re D| := by
  have h1 := List.all_eq_true.mp h c (List.mem_range.mpr hc)
  refine abs_le.mpr (sum_mem_of_corners (fun l hl ↦ ?_) hv)
  have h2 := Exact.nonneg_sound _ (List.all_eq_true.mp h1 l hl)
  rw [Exact.re_sub, Exact.re_mul, Exact.re_mul] at h2
  exact abs_le.mp (sq_le_sq.mp (by rw [sq, sq]; linarith))

end Matrices

end Nieuwland.Check
