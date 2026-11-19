import Modules.System.PolyRootEq
import Modules.System.SystemOps
import Mathlib.Data.List.GetD

/-!
# Systems with auxiliary variables

A system `S'` is a system `S` **with `m` auxiliary variables** (`PolynomialSystem.auxOk S S' m`) when

* its first `n` variables are those of `S` with the same intervals (`n` the length of `S`'s box),
  and it has `m` more, `x n, …, x (n + m - 1)`, each with an interval;
* its first `m` equations define them: the `k`-th is `x (n + k) = D k`, the polynomial `D k` in the
  variables below `n + k`, and the interval of `x (n + k)` holds the interval value of `D k` over
  the intervals of those variables (exact rational interval arithmetic, `RationalPolynomial.ival`);
* its other equations are those of `S` rewritten: the `i`-th, its two sides' difference with every
  auxiliary variable replaced by the expansion of its definition (`fulls`: each definition with the
  earlier expansions substituted), has the difference of the `i`-th equation of `S`, as canonical
  polynomials (`SystemOps.lean`), so the check is `decide` (it succeeds when the sides of `S`'s
  equations are canonical, as the written-out systems are; soundness does not depend on it);
* every variable of its equations has an interval.

Then the roots of `S'` in its box are the roots of `S` with the values of the definitions, so
`S'` has exactly one root when `S` has, with the same scale (`HasUniqueRoot.of_auxOk`), and the shared
scale of systems (`IsRootEq`) passes to their auxiliary forms (`IsRootEq.of_auxsOk`). Nothing here
depends on how the systems arose: it relates two written systems.

## Main statements

* `Nieuwland.RationalPolynomial.eval_substP`, `inI_ival`: substitution and the interval value.
* `Nieuwland.PolynomialSystem.HasUniqueRoot.of_auxOk`, `IsRootEq.of_auxsOk`.
-/

namespace Nieuwland

namespace RationalPolynomial

/-! ### Substitution -/

/-- `p ^ e`. -/
def powP (p : RationalPolynomial) : ℕ → RationalPolynomial
  | 0 => const 1
  | e + 1 => mul p (powP p e)

theorem eval_powP (p : RationalPolynomial) (x : ℕ → ℝ) : ∀ e, (powP p e).eval x = p.eval x ^ e
  | 0 => by simp [powP]
  | e + 1 => by rw [powP, eval_mul, eval_powP p x e, pow_succ, mul_comm]

/-- The monomial of the powers `m` with each variable `i` replaced by `σ i`. -/
def substM (σ : ℕ → RationalPolynomial) : List (ℕ × ℕ) → RationalPolynomial
  | [] => const 1
  | v :: m => mul (powP (σ v.1) v.2) (substM σ m)

theorem eval_substM (σ : ℕ → RationalPolynomial) (x : ℕ → ℝ) :
    ∀ m, (substM σ m).eval x = monomial (fun i ↦ (σ i).eval x) m
  | [] => by simp [substM, monomial_nil]
  | v :: m => by rw [substM, eval_mul, eval_powP, eval_substM σ x m, monomial_cons]

/-- `p` with each variable `i` replaced by the polynomial `σ i`. -/
def substP (σ : ℕ → RationalPolynomial) : RationalPolynomial → RationalPolynomial
  | [] => []
  | t :: p => add (mul (const t.1) (substM σ t.2)) (substP σ p)

theorem eval_substP (σ : ℕ → RationalPolynomial) (x : ℕ → ℝ) :
    ∀ p, (substP σ p).eval x = p.eval fun i ↦ (σ i).eval x
  | [] => by simp [substP]
  | t :: p => by
    rw [substP, eval_add, eval_mul, eval_const, eval_substM, eval_substP σ x p, eval_cons]

/-! ### Interval values -/

/-- `x` lies in the closed interval `I`. -/
def InI (I : ℚ × ℚ) (x : ℝ) : Prop := (I.1 : ℝ) ≤ x ∧ x ≤ I.2

/-- The sum of two intervals. -/
def iadd (I J : ℚ × ℚ) : ℚ × ℚ := (I.1 + J.1, I.2 + J.2)

/-- An interval holding the products of the points of two intervals: the least and the largest
product of their ends. -/
def imul (I J : ℚ × ℚ) : ℚ × ℚ :=
  (min (min (I.1 * J.1) (I.1 * J.2)) (min (I.2 * J.1) (I.2 * J.2)),
    max (max (I.1 * J.1) (I.1 * J.2)) (max (I.2 * J.1) (I.2 * J.2)))

/-- The `e`-th power of an interval, by products. -/
def ipow (I : ℚ × ℚ) : ℕ → ℚ × ℚ
  | 0 => (1, 1)
  | e + 1 => imul I (ipow I e)

/-- The interval value of the monomial of the powers `m`, the variable `i` in the interval
`B.getD i (0, 0)`. -/
def ivalM (B : List (ℚ × ℚ)) : List (ℕ × ℕ) → ℚ × ℚ
  | [] => (1, 1)
  | v :: m => imul (ipow (B.getD v.1 (0, 0)) v.2) (ivalM B m)

/-- The interval value of a polynomial over the intervals `B` of its variables. -/
def ival (B : List (ℚ × ℚ)) : RationalPolynomial → ℚ × ℚ
  | [] => (0, 0)
  | t :: p => iadd (imul (t.1, t.1) (ivalM B t.2)) (ival B p)

theorem inI_add {I J : ℚ × ℚ} {x y : ℝ} (hx : InI I x) (hy : InI J y) : InI (iadd I J) (x + y) := by
  simp only [InI, iadd, Rat.cast_add] at *
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- A product with a point of `[p, q]` lies between the products with its ends. -/
theorem mul_between {p q u : ℝ} (h1 : p ≤ u) (h2 : u ≤ q) (k : ℝ) :
    min (p * k) (q * k) ≤ u * k ∧ u * k ≤ max (p * k) (q * k) := by
  rcases le_total 0 k with hk | hk
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right h1 hk),
      (mul_le_mul_of_nonneg_right h2 hk).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right h2 hk),
      (mul_le_mul_of_nonpos_right h1 hk).trans (le_max_left _ _)⟩

theorem inI_mul {I J : ℚ × ℚ} {x y : ℝ} (hx : InI I x) (hy : InI J y) :
    InI (imul I J) (x * y) := by
  obtain ⟨a, b⟩ := I
  obtain ⟨c, d⟩ := J
  simp only [InI, imul] at *
  push_cast
  obtain ⟨hy1, hy2⟩ := mul_between hy.1 hy.2 x
  obtain ⟨hc1, hc2⟩ := mul_between hx.1 hx.2 (c : ℝ)
  obtain ⟨hd1, hd2⟩ := mul_between hx.1 hx.2 (d : ℝ)
  rw [mul_comm (c : ℝ) x, mul_comm (d : ℝ) x, mul_comm y x] at hy1 hy2
  constructor
  · refine le_trans (le_min (le_trans ?_ hc1) (le_trans ?_ hd1)) hy1
    · exact le_min ((min_le_left _ _).trans (min_le_left _ _))
        ((min_le_right _ _).trans (min_le_left _ _))
    · exact le_min ((min_le_left _ _).trans (min_le_right _ _))
        ((min_le_right _ _).trans (min_le_right _ _))
  · refine le_trans hy2 (max_le (le_trans hc2 ?_) (le_trans hd2 ?_))
    · exact max_le ((le_max_left _ _).trans (le_max_left _ _))
        ((le_max_left _ _).trans (le_max_right _ _))
    · exact max_le ((le_max_right _ _).trans (le_max_left _ _))
        ((le_max_right _ _).trans (le_max_right _ _))

theorem inI_pow {I : ℚ × ℚ} {x : ℝ} (hx : InI I x) : ∀ e, InI (ipow I e) (x ^ e)
  | 0 => by simp [InI, ipow]
  | e + 1 => by rw [ipow, pow_succ, mul_comm]; exact inI_mul hx (inI_pow hx e)

theorem inI_ivalM {B : List (ℚ × ℚ)} {x : ℕ → ℝ}
    (hB : ∀ i < B.length, InI (B.getD i (0, 0)) (x i)) :
    ∀ m, (m.all fun v ↦ decide (v.1 < B.length)) = true → InI (ivalM B m) (monomial x m)
  | [] => fun _ ↦ by simp [InI, ivalM, monomial_nil]
  | v :: m => fun h ↦ by
    rw [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [ivalM, monomial_cons]
    exact inI_mul (inI_pow (hB v.1 h.1) v.2) (inI_ivalM hB m h.2)

/-- **The interval value holds the value** at every point of the intervals. -/
theorem inI_ival {B : List (ℚ × ℚ)} {x : ℕ → ℝ} (hB : ∀ i < B.length, InI (B.getD i (0, 0)) (x i)) :
    ∀ p : RationalPolynomial, p.varsLt B.length = true → InI (ival B p) (p.eval x)
  | [] => fun _ ↦ by simp [InI, ival]
  | t :: p => fun h ↦ by
    rw [varsLt, List.all_cons, Bool.and_eq_true] at h
    rw [ival, eval_cons]
    exact inI_add (inI_mul (I := (t.1, t.1)) ⟨le_rfl, le_rfl⟩ (inI_ivalM hB t.2 h.1))
      (inI_ival hB p h.2)

end RationalPolynomial

namespace PolynomialSystem

open RationalPolynomial

/-! ### The check -/

/-- The polynomial standing for the variable `i`: itself below `n`, and above it the expansion
`F.getD (i - n)` of the auxiliary variable `i`. -/
def sig (n : ℕ) (F : List RationalPolynomial) (i : ℕ) : RationalPolynomial := if i < n then var i else F.getD (i - n) []

/-- One step of `fulls`: the next definition with the earlier expansions substituted. -/
def fullsStep (n : ℕ) (F : List RationalPolynomial) (d : RationalPolynomial) : List RationalPolynomial := F ++ [substP (sig n F) d]

/-- The expansions of the auxiliary variables of the definitions `D`. -/
def fulls (n : ℕ) (D : List RationalPolynomial) : List RationalPolynomial := D.foldl (fullsStep n) []

/-- The definition of the auxiliary variable `k`: the right side of the `k`-th equation. -/
def defn (S' : PolynomialSystem) (k : ℕ) : RationalPolynomial := (S'.eqs.getD k ([], [])).2

/-- **`S'` is `S` with `m` auxiliary variables** (module docs). -/
def auxOk (S S' : PolynomialSystem) (m : ℕ) : Bool :=
  let n := S.box.length
  let F := fulls n ((S'.eqs.take m).map (·.2))
  S'.box.length == n + m && S'.box.take n == S.box && S'.eqs.length == m + S.eqs.length &&
    S'.boxed &&
    ((List.range m).all fun k ↦
      (S'.eqs.getD k ([], [])).1 == var (n + k) && (S'.defn k).varsLt (n + k) &&
        let I := ival (S'.box.take (n + k)) (S'.defn k)
        decide ((S'.box.getD (n + k) (0, 0)).1 ≤ I.1 ∧ I.2 ≤ (S'.box.getD (n + k) (0, 0)).2)) &&
    (List.range S.eqs.length).all fun i ↦
      let e' := S'.eqs.getD (m + i) ([], [])
      let e := S.eqs.getD i ([], [])
      (add (substP (sig n F) (add e'.1 (neg e'.2))) (neg (add e.1 (neg e.2)))).isEmpty

/-! ### The expansions -/

theorem length_foldl_fullsStep (n : ℕ) :
    ∀ (D F : List RationalPolynomial), (D.foldl (fullsStep n) F).length = F.length + D.length
  | [], F => by simp
  | d :: D, F => by
    rw [List.foldl_cons, length_foldl_fullsStep n D]
    simp [fullsStep]
    omega

theorem getD_foldl_fullsStep (n : ℕ) :
    ∀ (D F : List RationalPolynomial) (j : ℕ), j < F.length → (D.foldl (fullsStep n) F).getD j [] = F.getD j []
  | [], F, j, _ => rfl
  | d :: D, F, j, hj => by
    rw [List.foldl_cons, getD_foldl_fullsStep n D _ j (by simp [fullsStep]; omega), fullsStep,
      List.getD_append _ _ _ _ hj]

theorem length_fulls (n : ℕ) (D : List RationalPolynomial) : (fulls n D).length = D.length := by
  simp [fulls, length_foldl_fullsStep]

theorem fulls_eq_foldl (n : ℕ) (D : List RationalPolynomial) (k : ℕ) :
    fulls n D = (D.drop k).foldl (fullsStep n) (fulls n (D.take k)) := by
  conv_lhs => rw [← List.take_append_drop k D]
  rw [fulls, List.foldl_append]
  rfl

/-- The prefix: the expansions of the first `k` definitions are the first `k` expansions. -/
theorem getD_fulls_take (n : ℕ) (D : List RationalPolynomial) {k j : ℕ} (hj : j < k) (hk : k ≤ D.length) :
    (fulls n (D.take k)).getD j [] = (fulls n D).getD j [] := by
  rw [fulls_eq_foldl n D k,
    getD_foldl_fullsStep n _ _ j (by rw [length_fulls, List.length_take]; omega)]

/-- The `k`-th expansion: the `k`-th definition with the first `k` expansions substituted. -/
theorem getD_fulls (n : ℕ) (D : List RationalPolynomial) {k : ℕ} (hk : k < D.length) :
    (fulls n D).getD k [] = substP (sig n (fulls n (D.take k))) (D.getD k []) := by
  have hl : (fulls n (D.take k)).length = k := by rw [length_fulls, List.length_take]; omega
  rw [fulls_eq_foldl n D k, List.drop_eq_getElem_cons hk, List.foldl_cons,
    getD_foldl_fullsStep n _ _ k (by simp [fullsStep, hl]), fullsStep,
    List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self, List.getD_eq_getElem _ _ hk]
  rfl

/-! ### The roots -/

section
variable {S S' : PolynomialSystem} {m : ℕ}

/-- The facts of the check. -/
structure AuxFacts (S S' : PolynomialSystem) (m : ℕ) : Prop where
  len : S'.box.length = S.box.length + m
  take : S'.box.take S.box.length = S.box
  eqlen : S'.eqs.length = m + S.eqs.length
  boxed : S'.boxed = true
  lhs : ∀ k < m, (S'.eqs.getD k ([], [])).1 = var (S.box.length + k)
  vars : ∀ k < m, (S'.defn k).varsLt (S.box.length + k) = true
  ibox : ∀ k < m, ((S'.box.getD (S.box.length + k) (0, 0)).1 ≤
      (ival (S'.box.take (S.box.length + k)) (S'.defn k)).1 ∧
    (ival (S'.box.take (S.box.length + k)) (S'.defn k)).2 ≤
      (S'.box.getD (S.box.length + k) (0, 0)).2)
  rw : ∀ i < S.eqs.length,
    (add (substP (sig S.box.length (fulls S.box.length ((S'.eqs.take m).map (·.2))))
      (add (S'.eqs.getD (m + i) ([], [])).1 (neg (S'.eqs.getD (m + i) ([], [])).2)))
      (neg (add (S.eqs.getD i ([], [])).1 (neg (S.eqs.getD i ([], [])).2)))).isEmpty = true

theorem auxFacts (h : S.auxOk S' m = true) : AuxFacts S S' m := by
  simp only [auxOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hlen, htake⟩, heq⟩, hb⟩, hdefs⟩, hrw⟩ := h
  exact ⟨hlen, htake, heq, hb, fun k hk ↦ (hdefs k hk).1.1, fun k hk ↦ (hdefs k hk).1.2,
    fun k hk ↦ (hdefs k hk).2, hrw⟩

theorem defs_len (A : AuxFacts S S' m) : ((S'.eqs.take m).map (·.2)).length = m := by
  rw [List.length_map, List.length_take, A.eqlen]; omega

theorem getD_defs (A : AuxFacts S S' m) {k : ℕ} (hk : k < m) :
    ((S'.eqs.take m).map (·.2)).getD k [] = S'.defn k := by
  have h1 : k < (S'.eqs.take m).length := by rw [List.length_take, A.eqlen]; omega
  have h2 : k < S'.eqs.length := by rw [A.eqlen]; omega
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact h1), List.getElem_map,
    List.getElem_take, defn, List.getD_eq_getElem _ _ h2]

theorem getD_mem {l : List (RationalPolynomial × RationalPolynomial)} {i : ℕ} (hi : i < l.length) :
    l.getD i ([], []) ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi

theorem exists_getD_of_mem {l : List (RationalPolynomial × RationalPolynomial)} {e : RationalPolynomial × RationalPolynomial} (he : e ∈ l) :
    ∃ i < l.length, l.getD i ([], []) = e := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
  exact ⟨i, hi, List.getD_eq_getElem _ _ hi⟩

/-- The variables of `S'`'s equations are below `n + m`. -/
theorem varsLt_eqs (A : AuxFacts S S' m) {e : RationalPolynomial × RationalPolynomial} (he : e ∈ S'.eqs) :
    e.1.varsLt (S.box.length + m) = true ∧ e.2.varsLt (S.box.length + m) = true := by
  have h := List.all_eq_true.mp A.boxed e he
  rw [Bool.and_eq_true, A.len] at h
  exact h

/-- The point of `S'` of a point `x`: its variables, then the expansions' values at `x`. -/
noncomputable def auxPt (S S' : PolynomialSystem) (m : ℕ) (x : ℕ → ℝ) : ℕ → ℝ :=
  fun j ↦ (sig S.box.length (fulls S.box.length ((S'.eqs.take m).map (·.2))) j).eval x

theorem auxPt_lt (x : ℕ → ℝ) {j : ℕ} (hj : j < S.box.length) : auxPt S S' m x j = x j := by
  simp [auxPt, sig, hj]

theorem auxPt_add (x : ℕ → ℝ) (k : ℕ) :
    auxPt S S' m x (S.box.length + k) =
      ((fulls S.box.length ((S'.eqs.take m).map (·.2))).getD k []).eval x := by
  change (sig S.box.length _ (S.box.length + k)).eval x = _
  have h : ¬ S.box.length + k < S.box.length := by omega
  simp only [sig, h, ↓reduceIte, Nat.add_sub_cancel_left]

theorem getD_take_lt {α : Type*} {l : List α} {d : α} {n i : ℕ} (h : i < n) :
    (l.take n).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, h]

theorem box_getD (A : AuxFacts S S' m) {i : ℕ} (hi : i < S.box.length) :
    S'.box.getD i (0, 0) = S.box.getD i (0, 0) := by
  have h := getD_take_lt (l := S'.box) (d := ((0 : ℚ), (0 : ℚ))) hi
  rw [A.take] at h
  exact h.symm

/-- The `i`-th rewritten equation's value at `auxPt S S' m z` is the `i`-th equation's at `z`. -/
theorem rw_eval (A : AuxFacts S S' m) (z : ℕ → ℝ) {i : ℕ} (hi : i < S.eqs.length) :
    (S.eqs.getD i ([], [])).1.eval z - (S.eqs.getD i ([], [])).2.eval z =
      (S'.eqs.getD (m + i) ([], [])).1.eval (auxPt S S' m z) -
        (S'.eqs.getD (m + i) ([], [])).2.eval (auxPt S S' m z) := by
  have h := congrArg (fun p : RationalPolynomial ↦ p.eval z) (List.isEmpty_iff.mp (A.rw i hi))
  simp only [eval_add, eval_neg, eval_substP, eval_nil] at h
  unfold auxPt
  linarith

/-- **A root of `S'` gives its auxiliary variables the expansions' values.** -/
theorem aux_vals (A : AuxFacts S S' m) {y : ℕ → ℝ} (hy : S'.Solves y) :
    ∀ k < m, y (S.box.length + k) =
      ((fulls S.box.length ((S'.eqs.take m).map (·.2))).getD k []).eval y := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hkD : k < ((S'.eqs.take m).map (·.2)).length := by rw [defs_len A]; exact hk
    have he := hy.2 _ (getD_mem (l := S'.eqs) (i := k) (by rw [A.eqlen]; omega))
    rw [A.lhs k hk, eval_var] at he
    rw [he, getD_fulls _ _ hkD, eval_substP, getD_defs A hk]
    refine eval_congr (fun i hi ↦ ?_) _ (A.vars k hk)
    unfold sig
    split_ifs with h
    · rw [eval_var]
    · have hj : i - S.box.length < k := by omega
      rw [getD_fulls_take _ _ hj hkD.le, ← ih _ hj (by omega)]
      congr 1
      omega

/-- `auxPt` keeps a root of `S'`. -/
theorem auxPt_root (A : AuxFacts S S' m) {y : ℕ → ℝ} (hy : S'.Solves y) :
    ∀ j < S.box.length + m, auxPt S S' m y j = y j := by
  intro j hj
  by_cases h : j < S.box.length
  · exact auxPt_lt y h
  · obtain ⟨k, rfl⟩ : ∃ k, j = S.box.length + k := ⟨j - S.box.length, by omega⟩
    rw [auxPt_add, ← aux_vals A hy k (by omega)]

/-- **A root of `S'` is a root of `S`.** -/
theorem solves_of_aux (A : AuxFacts S S' m) {y : ℕ → ℝ} (hy : S'.Solves y) : S.Solves y := by
  refine ⟨fun i hi ↦ ?_, fun e he ↦ ?_⟩
  · rw [← box_getD A hi]
    exact hy.1 i (by rw [A.len]; omega)
  · obtain ⟨i, hi, rfl⟩ := exists_getD_of_mem he
    have he' := getD_mem (l := S'.eqs) (i := m + i) (by rw [A.eqlen]; omega)
    have h := rw_eval A y hi
    rw [eval_congr (auxPt_root A hy) _ (varsLt_eqs A he').1,
      eval_congr (auxPt_root A hy) _ (varsLt_eqs A he').2, hy.2 _ he', sub_self] at h
    linarith

/-- The auxiliary variables of `auxPt` satisfy their definitions. -/
theorem auxPt_def (A : AuxFacts S S' m) (x : ℕ → ℝ) {k : ℕ} (hk : k < m) :
    auxPt S S' m x (S.box.length + k) = (S'.defn k).eval (auxPt S S' m x) := by
  have hkD : k < ((S'.eqs.take m).map (·.2)).length := by rw [defs_len A]; exact hk
  rw [auxPt_add, getD_fulls _ _ hkD, eval_substP, getD_defs A hk]
  refine eval_congr (fun i hi ↦ ?_) _ (A.vars k hk)
  change _ = (sig _ _ i).eval x
  unfold sig
  split_ifs with h
  · rfl
  · rw [getD_fulls_take _ _ (by omega) hkD.le]

/-- The auxiliary variables of `auxPt` at a root of `S` lie in their intervals. -/
theorem auxPt_box (A : AuxFacts S S' m) {x : ℕ → ℝ} (hx : S.Solves x) :
    ∀ k < m, InI (S'.box.getD (S.box.length + k) (0, 0)) (auxPt S S' m x (S.box.length + k)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hlen : (S'.box.take (S.box.length + k)).length = S.box.length + k := by
      rw [List.length_take, A.len]; omega
    have hB : ∀ i < (S'.box.take (S.box.length + k)).length,
        InI ((S'.box.take (S.box.length + k)).getD i (0, 0)) (auxPt S S' m x i) := by
      intro i hi
      rw [hlen] at hi
      rw [getD_take_lt hi]
      by_cases h : i < S.box.length
      · rw [auxPt_lt x h, box_getD A h]
        exact hx.1 i h
      · have := ih (i - S.box.length) (by omega) (by omega)
        rwa [Nat.add_sub_cancel' (by omega)] at this
    have hI := inI_ival hB _ (by rw [hlen]; exact A.vars k hk)
    rw [auxPt_def A x hk]
    exact ⟨le_trans (by exact_mod_cast (A.ibox k hk).1) hI.1,
      le_trans hI.2 (by exact_mod_cast (A.ibox k hk).2)⟩

/-- **A root of `S` with the expansions' values is a root of `S'`.** -/
theorem auxPt_solves (A : AuxFacts S S' m) {x : ℕ → ℝ} (hx : S.Solves x) :
    S'.Solves (auxPt S S' m x) := by
  refine ⟨fun i hi ↦ ?_, fun e he ↦ ?_⟩
  · rw [A.len] at hi
    by_cases h : i < S.box.length
    · rw [auxPt_lt x h, box_getD A h]
      exact hx.1 i h
    · have := auxPt_box A hx (i - S.box.length) (by omega)
      rwa [Nat.add_sub_cancel' (by omega)] at this
  · obtain ⟨j, hj, rfl⟩ := exists_getD_of_mem he
    by_cases h : j < m
    · rw [A.lhs j h, eval_var, auxPt_def A x h]
      rfl
    · obtain ⟨i, rfl⟩ : ∃ i, j = m + i := ⟨j - m, by omega⟩
      have hi : i < S.eqs.length := by rw [A.eqlen] at hj; omega
      have h1 := rw_eval A x hi
      rw [hx.2 _ (getD_mem hi), sub_self] at h1
      linarith

/-- Two roots of `S'` that agree on `S`'s variables agree on all. -/
theorem aux_unique (A : AuxFacts S S' m) {y z : ℕ → ℝ} (hy : S'.Solves y) (hz : S'.Solves z)
    (h : ∀ i < S.box.length, y i = z i) : ∀ i < S'.box.length, y i = z i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h' : i < S.box.length
    · exact h i h'
    · obtain ⟨k, rfl⟩ : ∃ k, i = S.box.length + k := ⟨i - S.box.length, by omega⟩
      have hk : k < m := by rw [A.len] at hi; omega
      have hmem := getD_mem (l := S'.eqs) (i := k) (by rw [A.eqlen]; omega)
      have ey := hy.2 _ hmem
      have ez := hz.2 _ hmem
      rw [A.lhs k hk, eval_var] at ey ez
      rw [ey, ez]
      exact eval_congr (fun j hj ↦ ih j hj (by omega)) _ (A.vars k hk)

/-- **`S'` has exactly one root when `S` has, with the same scales.** -/
theorem HasUniqueRoot.of_auxOk (h : S.auxOk S' m = true) (hS : S.HasUniqueRoot) :
    S'.HasUniqueRoot ∧ scales [S'] = scales [S] := by
  have A := auxFacts h
  obtain ⟨h0, -, x, hx, hu⟩ := hS
  refine ⟨⟨by rw [A.len]; omega, A.boxed, auxPt S S' m x, auxPt_solves A hx, fun y hy ↦ ?_⟩, ?_⟩
  · refine aux_unique A hy (auxPt_solves A hx) fun i hi ↦ ?_
    rw [auxPt_lt x hi]
    exact hu y (solves_of_aux A hy) i hi
  · ext l
    simp only [scales, Set.mem_ofPred_eq, List.mem_singleton, exists_eq_left]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, solves_of_aux A hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨auxPt S S' m y, auxPt_solves A hy, auxPt_lt y h0⟩

end

/-- Each system of `Ss'` is the system of `Ss` at its place with the number of auxiliary
variables of `ms` at its place; the three lists have one length. (No overlapping patterns: each
equation holds unconditionally.) -/
def auxsOk : List PolynomialSystem → List PolynomialSystem → List ℕ → Bool
  | [], [], [] => true
  | S :: Ss, S' :: Ss', m :: ms => S.auxOk S' m && auxsOk Ss Ss' ms
  | [], _ :: _, _ => false
  | [], [], _ :: _ => false
  | _ :: _, [], _ => false
  | _ :: _, _ :: _, [] => false

theorem auxsOk_nil : auxsOk [] [] [] = true := rfl

/-- The check of a list from its systems' checks, one at a time (each its own declaration in a
generated module, so that the kernel decides one system per declaration). -/
theorem auxsOk_cons {S S' : PolynomialSystem} {m : ℕ} {Ss Ss' : List PolynomialSystem} {ms : List ℕ}
    (h : S.auxOk S' m = true) (hs : auxsOk Ss Ss' ms = true) :
    auxsOk (S :: Ss) (S' :: Ss') (m :: ms) = true := by
  rw [auxsOk, h, hs]; rfl

theorem auxsOk_mem {Ss Ss' : List PolynomialSystem} {ms : List ℕ} (h : auxsOk Ss Ss' ms = true) :
    (Ss' = [] → Ss = []) ∧ ∀ S' ∈ Ss', ∃ S ∈ Ss, ∃ m, S.auxOk S' m = true := by
  induction Ss generalizing Ss' ms with
  | nil => exact ⟨fun _ ↦ rfl, by cases Ss' <;> cases ms <;> simp_all [auxsOk]⟩
  | cons S Ss ih =>
    cases Ss' with
    | nil => cases ms <;> simp [auxsOk] at h
    | cons S' Ss' =>
      cases ms with
      | nil => simp [auxsOk] at h
      | cons m ms =>
        simp only [auxsOk, Bool.and_eq_true] at h
        refine ⟨fun h' ↦ absurd h' (List.cons_ne_nil _ _), fun T hT ↦ ?_⟩
        rcases List.mem_cons.mp hT with rfl | hT
        · exact ⟨S, List.mem_cons_self .., m, h.1⟩
        · obtain ⟨U, hU, k, hk⟩ := (ih h.2).2 T hT
          exact ⟨U, List.mem_cons_of_mem _ hU, k, hk⟩

/-- **The shared scale passes to the auxiliary forms.** -/
theorem IsRootEq.of_auxsOk {Ss Ss' : List PolynomialSystem} {ms : List ℕ} {N : ℝ} (h : IsRootEq Ss N)
    (ha : auxsOk Ss Ss' ms = true) : IsRootEq Ss' N := by
  obtain ⟨hn, hm⟩ := auxsOk_mem ha
  refine ⟨fun h' ↦ h.1 (hn h'), fun S' hS' ↦ ?_⟩
  obtain ⟨S, hS, m, hm'⟩ := hm S' hS'
  have := HasUniqueRoot.of_auxOk hm' (h.2 S hS).1
  exact ⟨this.1, this.2.trans (h.2 S hS).2⟩

end PolynomialSystem

end Nieuwland
