import Modules.Root.Assembly
import Modules.System.SystemRoot

/-!
# A root's system written out

The system of a root record (`Modules/Root/System.lean`: the contacts' slacks and the
stationarity of the scale, in the pose, the translation, the scale and the multipliers, with the
basis values of the solid's field as parameters) as a `PolynomialSystem`
(`Modules/System/System.lean`): rational polynomials in finitely many variables with a box.

**The variables**, in this order: `x 0` the scale; `x 1, …, x nx` the pose `(s, t, x₁, x₂, x₃)`
and, in general mode, the translation; then the multipliers; then, at `x n` (`n` the number of
unknowns of the root's system), a generator of the solid's field when it has one (`ParData`):
`√d` (`x n ^ 2 = d`, `x n ≥ 0`) or the root `α` of the monic integer polynomial `N` of a number
field in its isolating interval; then the coordinates of the vertices that the contacts use,
three per vertex, each fixed by an equation `x = ∑ cⱼ βⱼ` over the field's basis values `βⱼ`
(powers of the generator). The box holds the scale, pose, translation and multipliers in the box
of Krawczyk's test and the generator in its interval; the vertices' coordinates have none.

**The equations**: the slacks over the vertices' coordinate variables (`gc`, the slack of
`Modules/Root/Slack.lean` with the vertices replaced by variables), the stationarity equations of
those slacks (`statc`), the vertices' coordinates (`vertc`) and the generator's equation.

**The statement** (`RootRec.scales_explicit`): the scales of the written-out system are the
scale of the root alone. A solution gives a zero of the root's system in the box of Krawczyk's
test (the generator is the field's, so the coordinate variables are the vertices'
coordinates, and the slacks and their derivatives agree because the root's system is the
written-out one with the vertices' expressions substituted: `substE_slackE`,
`eval_deriv_substE`), which is the only one (`Kraw.IsZero`); the zero gives a solution.

## Main statements

* `Nieuwland.Root.eval_substE`, `eval_deriv_substE`: substitution and derivatives.
* `Nieuwland.Root.substE_slackE`: a slack with the vertices substituted.
* `Nieuwland.Root.RootRec.scales_explicit`: the written-out system of a root record.
* `Nieuwland.Root.ParData.int_spec`, `sqrt_spec`, `theta_spec`: the generators of `ℤ`, `ℤ[√d]`
  and `ℤ[α]`.
-/

open Finset

namespace Nieuwland.Root

open Check (Expr V3 Exact ExactBasis)

/-! ### Substitution -/

/-- `e` with the variable `i` replaced by `σ i`. -/
def substE (σ : ℕ → Expr) : Expr → Expr
  | .const c => .const c
  | .var i => σ i
  | .add a b => .add (substE σ a) (substE σ b)
  | .sub a b => .sub (substE σ a) (substE σ b)
  | .mul a b => .mul (substE σ a) (substE σ b)

section Subst

variable (σ : ℕ → Expr)

@[simp] theorem substE_const (c : ℤ) : substE σ (.const c) = .const c := rfl
@[simp] theorem substE_var (i : ℕ) : substE σ (.var i) = σ i := rfl
@[simp] theorem substE_add (a b : Expr) : substE σ (a + b) = substE σ a + substE σ b := rfl
@[simp] theorem substE_sub (a b : Expr) : substE σ (a - b) = substE σ a - substE σ b := rfl
@[simp] theorem substE_mul (a b : Expr) : substE σ (a * b) = substE σ a * substE σ b := rfl

theorem eval_substE (z : ℕ → ℝ) :
    ∀ e : Expr, (substE σ e).eval z = e.eval fun i ↦ (σ i).eval z
  | .const _ => rfl
  | .var _ => rfl
  | .add a b => by
    simp only [substE, Expr.eval, eval_substE z a, eval_substE z b]
  | .sub a b => by
    simp only [substE, Expr.eval, eval_substE z a, eval_substE z b]
  | .mul a b => by
    simp only [substE, Expr.eval, eval_substE z a, eval_substE z b]

/-- **Derivatives of substitutions**: if every `σ i` has the derivative of the variable `i` in
the variable `v` at `z`, the derivative of `substE σ e` at `z` is that of `e` at the point of the
values of the `σ i`. -/
theorem eval_deriv_substE (z : ℕ → ℝ) (v : ℕ)
    (hσ : ∀ i, (deriv v (σ i)).eval z = ((if i = v then 1 else 0 : ℤ) : ℝ)) :
    ∀ e : Expr, (deriv v (substE σ e)).eval z = (deriv v e).eval fun i ↦ (σ i).eval z
  | .const _ => rfl
  | .var i => by rw [substE, hσ]; rfl
  | .add a b => by
    simp only [substE, deriv, Expr.eval, eval_deriv_substE z v hσ a, eval_deriv_substE z v hσ b]
  | .sub a b => by
    simp only [substE, deriv, Expr.eval, eval_deriv_substE z v hσ a, eval_deriv_substE z v hσ b]
  | .mul a b => by
    simp only [substE, deriv, Expr.eval, eval_deriv_substE z v hσ a, eval_deriv_substE z v hσ b,
      eval_substE]

variable {σ}

theorem substE_qE (hσ : ∀ i < 5, σ i = .var i) (k j : Fin 4) : substE σ (qE k j) = qE k j := by
  fin_cases k <;> fin_cases j <;> simp [qE, hσ]

theorem substE_quatE (q : Fin 4 → Expr) (i j : Fin 3) :
    substE σ (quatE q i j) = quatE (fun m ↦ substE σ (q m)) i j := by
  fin_cases i <;> fin_cases j <;> simp [quatE]

theorem substE_normE (q : Fin 4 → Expr) : substE σ (normE q) = normE fun m ↦ substE σ (q m) := by
  simp [normE]

theorem substE_screenE (h0 : σ 0 = .var 0) (h1 : σ 1 = .var 1) (a : Fin 3) (x : Fin 3 → Expr)
    (c : Fin 2) : substE σ (screenE a x c) = screenE a (fun i ↦ substE σ (x i)) c := by
  fin_cases c <;> simp [screenE, h0, h1]

theorem substE_rotE (hσ : ∀ i < 5, σ i = .var i) (k : Fin 4) (x : Fin 3 → Expr) (i : Fin 3) :
    substE σ (rotE k x i) = rotE k (fun j ↦ substE σ (x j)) i := by
  simp only [rotE, substE_add, substE_mul, substE_quatE, substE_qE hσ]

/-- **A slack with the vertices substituted**: if `σ` fixes the pose, translation and scale
variables, substituting into a slack substitutes into its vertices' expressions. -/
theorem substE_slackE (cen : Bool) (a : Fin 3) (k : Fin 4) (V : ℕ → Fin 3 → Expr)
    (va vb vk : ℕ) (hσ : ∀ i ≤ nx cen, σ i = .var i) :
    substE σ (slackE cen a k V va vb vk) =
      slackE cen a k (fun u c ↦ substE σ (V u c)) va vb vk := by
  have h5 : ∀ i < 5, σ i = .var i := fun i hi ↦ hσ i (by unfold nx; split <;> omega)
  have hl : substE σ (lE cen) = lE cen := hσ _ le_rfl
  have hy : ∀ c, substE σ (yE cen c) = yE cen c := by
    intro c
    unfold yE
    split
    · rfl
    · next h =>
      simp only [substE_var]
      exact hσ _ (by simp [nx, h]; omega)
  simp only [slackE, substE_add, substE_sub, substE_mul, substE_screenE (h5 0 (by norm_num))
    (h5 1 (by norm_num)), substE_rotE h5, substE_normE, substE_qE h5, hl, hy]

theorem slackE_congr {cen : Bool} {a : Fin 3} {k : Fin 4} {V V' : ℕ → Fin 3 → Expr}
    {va vb vk : ℕ} (ha : V va = V' va) (hb : V vb = V' vb) (hk : V vk = V' vk) :
    slackE cen a k V va vb vk = slackE cen a k V' va vb vk := by
  simp only [slackE, ha, hb, hk]

end Subst

/-! ### The vertices' expressions -/

section Verts

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

theorem eval_vertsE_congr {z z' : ℕ → ℝ} (nu : ℕ) (pts : List (V3 κ)) (v : ℕ) (c : Fin 3)
    (h : ∀ j < ExactBasis.dim κ, z (nu + j) = z' (nu + j)) :
    (vertsE nu pts v c).eval z = (vertsE nu pts v c).eval z' := by
  simp only [vertsE, elemE, eval_sumE]
  refine sum_congr rfl fun j hj ↦ ?_
  simp [Expr.eval, h j (mem_range.mp hj)]

theorem eval_deriv_vertsE (z : ℕ → ℝ) {nu v : ℕ} (hv : v < nu) (pts : List (V3 κ)) (u : ℕ)
    (c : Fin 3) : (deriv v (vertsE nu pts u c)).eval z = 0 := by
  simp only [vertsE, elemE, eval_deriv_sumE]
  refine sum_eq_zero fun j _ ↦ ?_
  have : nu + j ≠ v := by omega
  simp [deriv, Expr.eval, this]

end Verts

/-! ### Generators -/

/-- A box condition: `x (G + i)` in the `i`-th interval of `B`. -/
def InBox (B : List (ℚ × ℚ)) (G : ℕ) (x : ℕ → ℝ) : Prop :=
  ∀ i < B.length, ((B.getD i (0, 0)).1 : ℝ) ≤ x (G + i) ∧ x (G + i) ≤ ((B.getD i (0, 0)).2 : ℝ)

/-- The basis values of a field as polynomials in a generator `x G`, with the generator's
equations and the intervals of the variables from `x G` on. -/
structure ParData where
  /-- The basis value `j` as a polynomial, the generator being `x G`. -/
  par : ℕ → ℕ → RationalPolynomial
  /-- The generator's equations. -/
  eqs : ℕ → List RationalPolynomial
  /-- The intervals of `x G, x (G + 1), …`. -/
  box : List (ℚ × ℚ)

/-- `D` describes the basis values of `κ`: where the generator's conditions hold, the polynomials
`par G j` are the basis values (soundness), and they hold at some value of `x G`
(completeness). -/
def ParData.Spec (D : ParData) (κ : Type) [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] : Prop :=
  (∀ (G : ℕ) (x : ℕ → ℝ), InBox D.box G x → (∀ p ∈ D.eqs G, p.eval x = 0) →
    ∀ j, (D.par G j).eval x = basisPar κ j) ∧
  ∃ val : ℝ, ∀ (G : ℕ) (x : ℕ → ℝ), x G = val → InBox D.box G x ∧ ∀ p ∈ D.eqs G, p.eval x = 0

namespace ParData

/-- `ℤ`: the basis value `1`, no generator. -/
def int : ParData where
  par _ j := if j = 0 then RationalPolynomial.const 1 else []
  eqs _ := []
  box := []

theorem int_spec : int.Spec ℤ := by
  refine ⟨fun G x _ _ j ↦ ?_, 0, fun G x _ ↦ ⟨fun i hi ↦ absurd hi (by simp [int]), by simp [int]⟩⟩
  unfold basisPar
  by_cases hj : j = 0
  · subst hj
    have h1 : ExactBasis.basis ℤ 0 = 1 := Erased.out_mk _
    simp [int, h1]
  · have : ¬ j < ExactBasis.dim ℤ := by change ¬ j < 1; omega
    simp [int, hj, this]

/-- `ℤ[√d]`: the basis values `1` and `x G`, with `x G ^ 2 = d` and `x G ∈ [lo, hi]`. -/
def sqrt (d : ℕ) (lo hi : ℚ) : ParData where
  par G j := if j = 0 then RationalPolynomial.const 1 else if j = 1 then RationalPolynomial.var G else []
  eqs G := [[(-(d : ℚ), []), (1, RationalPolynomial.mono G 2)]]
  box := [(lo, hi)]

/-- The test of `sqrt`'s interval: `0 ≤ lo`, `lo² ≤ d ≤ hi²`, `0 ≤ hi`. -/
def sqrtOk (d : ℕ) (lo hi : ℚ) : Bool :=
  decide (0 ≤ lo) && decide (lo * lo ≤ d) && decide ((d : ℚ) ≤ hi * hi) && decide (0 ≤ hi)

theorem sqrt_spec {d : ℕ} {lo hi : ℚ} (h : sqrtOk d lo hi = true) :
    (sqrt d lo hi).Spec (Check.ZSqrt d) := by
  simp only [sqrtOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hlo, hlod⟩, hdhi⟩, hhi⟩ := h
  have hlo' : (0 : ℝ) ≤ lo := by exact_mod_cast hlo
  have hhi' : (0 : ℝ) ≤ hi := by exact_mod_cast hhi
  refine ⟨fun G x hb he j ↦ ?_, √(d : ℝ), fun G x hx ↦ ⟨fun i hi' ↦ ?_, fun p hp ↦ ?_⟩⟩
  · have hx := hb 0 (by simp [sqrt])
    simp only [sqrt, List.getD_cons_zero, add_zero] at hx
    have he' := he _ (List.mem_singleton_self _)
    simp only [RationalPolynomial.eval_cons, RationalPolynomial.monomial_mono, RationalPolynomial.monomial_nil,
      RationalPolynomial.eval_nil] at he'
    have hx0 : 0 ≤ x G := hlo'.trans hx.1
    have hsq : x G = √(d : ℝ) := by
      rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (Nat.cast_nonneg _) hx0]
      push_cast at he'
      nlinarith
    unfold basisPar
    rw [Check.ZSqrt.basis_eq]
    by_cases hj0 : j = 0
    · subst hj0
      simp [sqrt, Check.ZSqrt.basisVal]
    · by_cases hj1 : j = 1
      · subst hj1
        have h12 : 1 < ExactBasis.dim (Check.ZSqrt d) := by change 1 < 2; norm_num
        simp [sqrt, Check.ZSqrt.basisVal, hsq, h12]
      · have : ¬ j < ExactBasis.dim (Check.ZSqrt d) := by change ¬ j < 2; omega
        simp [sqrt, hj0, hj1, this]
  · obtain rfl : i = 0 := by simpa [sqrt] using hi'
    simp only [sqrt, List.getD_cons_zero, add_zero, hx]
    constructor
    · rw [Real.le_sqrt hlo' (Nat.cast_nonneg _)]
      have : ((lo * lo : ℚ) : ℝ) ≤ ((d : ℚ) : ℝ) := by exact_mod_cast hlod
      push_cast at this
      nlinarith
    · rw [Real.sqrt_le_left hhi']
      have : (((d : ℚ)) : ℝ) ≤ ((hi * hi : ℚ) : ℝ) := by exact_mod_cast hdhi
      push_cast at this
      nlinarith
  · simp only [sqrt, List.mem_singleton] at hp
    rw [hp]
    simp only [RationalPolynomial.eval_cons, RationalPolynomial.monomial_mono, RationalPolynomial.monomial_nil, RationalPolynomial.eval_nil,
      hx]
    push_cast
    rw [Real.sq_sqrt (Nat.cast_nonneg _)]
    ring

/-- `ℤ[α]`: the basis values `x G ^ j`, with `N(x G) = 0` and `x G ∈ [A/E, B/E]`, where `α` is
the only root of `N` (`Check.Root.eq_of_root`). -/
def theta (R : Check.Root) : ParData where
  par G j := if j < R.n then [(1, RationalPolynomial.mono G j)] else []
  eqs G := [RationalPolynomial.ofUni G (R.N.map Int.cast)]
  box := [((R.A : ℚ) / R.E, (R.B : ℚ) / R.E)]

theorem evalZ_ofUni (N : List ℤ) (G : ℕ) (x : ℕ → ℝ) :
    (RationalPolynomial.ofUni G (N.map Int.cast)).eval x = Check.evalZ N (x G) := by
  rw [RationalPolynomial.eval_ofUni, List.length_map, Check.evalZ]
  refine sum_congr rfl fun i _ ↦ ?_
  have h := List.getD_map (l := N) (n := i) (d := (0 : ℤ)) (Int.cast : ℤ → ℚ)
  rw [Int.cast_zero] at h
  rw [h]
  push_cast
  rfl

theorem theta_spec (R : Check.Root) : (theta R).Spec (Check.ZTheta R) := by
  refine ⟨fun G x hb he j ↦ ?_, R.α, fun G x hx ↦ ⟨fun i hi ↦ ?_, fun p hp ↦ ?_⟩⟩
  · have hx := hb 0 (by simp [theta])
    simp only [theta, List.getD_cons_zero, add_zero] at hx
    push_cast at hx
    have he' := he _ (List.mem_singleton_self _)
    rw [evalZ_ofUni] at he'
    have hα : R.α = x G := R.eq_of_root hx.1 hx.2 he'
    unfold basisPar
    have hb' : ∀ j, ExactBasis.basis (Check.ZTheta R) j = R.α ^ j := fun _ ↦ Erased.out_mk _
    by_cases hj : j < R.n
    · have : j < ExactBasis.dim (Check.ZTheta R) := hj
      simp only [theta, hj, ↓reduceIte, this, hb', RationalPolynomial.eval_cons, RationalPolynomial.monomial_mono,
        RationalPolynomial.eval_nil, hα]
      push_cast
      ring
    · have : ¬ j < ExactBasis.dim (Check.ZTheta R) := hj
      simp [theta, hj, this]
  · obtain ⟨h1, h2⟩ := R.α_mem_coarse
    obtain rfl : i = 0 := by simpa [theta] using hi
    simp only [theta, List.getD_cons_zero, add_zero, hx]
    push_cast
    exact ⟨h1, h2⟩
  · simp only [theta, List.mem_singleton] at hp
    rw [hp, evalZ_ofUni, hx]
    exact R.spec.2.2

end ParData

/-! ### The written-out system -/

namespace Kraw

/-- The interval of the unknown `i` in the box of the test: `[c - ρ, c + ρ] / 2^s`. -/
def kbox (K : Kraw) (i : ℕ) : ℚ × ℚ :=
  ((((K.c.getD i 0 : ℤ) - ((K.ρ.getD i 0 : ℕ) : ℤ) : ℤ) : ℚ) / 2 ^ K.s,
    (((K.c.getD i 0 : ℤ) + ((K.ρ.getD i 0 : ℕ) : ℤ) : ℤ) : ℚ) / 2 ^ K.s)

theorem mem_kbox_iff (K : Kraw) (i : Fin K.n) (a : ℝ) :
    (((K.kbox i).1 : ℚ) : ℝ) ≤ a ∧ a ≤ (((K.kbox i).2 : ℚ) : ℝ) ↔ |a - K.centre i| ≤ K.radius i := by
  simp only [kbox, centre, radius, rad]
  push_cast
  rw [abs_le, sub_div, add_div]
  constructor
  · rintro ⟨h1, h3⟩
    constructor <;> linarith
  · rintro ⟨h1, h3⟩
    constructor <;> linarith

end Kraw

namespace Sys

variable (S : Sys) (dim : ℕ) (vs : List ℕ)

/-- The coordinate `c` of the vertex `u` as a variable: after the unknowns and the `dim`
parameters, three per vertex of `vs`. -/
def Vc (u : ℕ) (c : Fin 3) : Expr := .var (S.n + dim + 3 * vs.idxOf u + c)

/-- The slack of the contact `i` over the vertices' coordinate variables. -/
def gc (i : ℕ) : Expr :=
  slackE S.cen S.view S.rot (S.Vc dim vs) (S.con i).1 (S.con i).2.1 (S.con i).2.2

/-- The stationarity equation of the unknown `v` over the vertices' coordinate variables. -/
def statc (v : ℕ) : Expr :=
  .sub (sumE S.k fun i ↦ .mul (mE S.cen i) (deriv v (S.gc dim vs i)))
    (.const (if v = nx S.cen then 1 else 0))

/-- The equation of the coordinate variable `i` (the coordinate `i % 3` of the vertex
`vs[i / 3]`). -/
def vertc (i : ℕ) : Expr :=
  .sub (.var (S.n + dim + i)) (S.V (vs.getD (i / 3) 0) ⟨i % 3, Nat.mod_lt _ (by norm_num)⟩)

/-- The vertices' expressions in place of their coordinate variables. -/
def σ (i : ℕ) : Expr :=
  if i < S.n + dim then .var i
  else if i - (S.n + dim) < 3 * vs.length then
    S.V (vs.getD ((i - (S.n + dim)) / 3) 0) ⟨(i - (S.n + dim)) % 3, Nat.mod_lt _ (by norm_num)⟩
  else .const 0

/-- The written-out variables (module docs) of the variables of the root's system: the scale
first, then the pose and translation, the multipliers, the parameters as polynomials `par j` and
the vertices' coordinate variables. -/
def τ (par : ℕ → RationalPolynomial) (i : ℕ) : RationalPolynomial :=
  if i = nx S.cen then RationalPolynomial.var 0
  else if i < nx S.cen then RationalPolynomial.var (i + 1)
  else if i < S.n then RationalPolynomial.var i
  else if i < S.n + dim then par (i - S.n)
  else if i - (S.n + dim) < 3 * vs.length then RationalPolynomial.var (S.n + 1 + (i - (S.n + dim)))
  else []

/-- The written-out system of a root (module docs) as equations `p = 0`, with the parameters
`par`, the generator's equations `geqs` and its intervals `gbox` (`ParData`). -/
def explicitZ (K : Kraw) (par : ℕ → RationalPolynomial) (geqs : List RationalPolynomial) (gbox : List (ℚ × ℚ)) :
    ZSystem where
  eqs := (List.range S.k).map (fun i ↦ RationalPolynomial.ofExpr (S.τ dim vs par) (S.gc dim vs i)) ++
    (List.range S.nv).map (fun v ↦ RationalPolynomial.ofExpr (S.τ dim vs par) (S.statc dim vs v)) ++
    (List.range (3 * vs.length)).map (fun i ↦ RationalPolynomial.ofExpr (S.τ dim vs par) (S.vertc dim vs i)) ++
    geqs
  box := K.kbox (nx S.cen) :: ((List.range (nx S.cen)).map K.kbox ++
    (List.range S.k).map fun i ↦ K.kbox (nx S.cen + 1 + i)) ++ gbox

/-- **The written-out system** of a root, both sides of every equation positive. -/
def explicit (K : Kraw) (par : ℕ → RationalPolynomial) (geqs : List RationalPolynomial) (gbox : List (ℚ × ℚ)) :
    PolynomialSystem :=
  (S.explicitZ dim vs K par geqs gbox).toSystem

theorem n_eq' : S.n = nx S.cen + 1 + S.k := rfl

theorem nx_lt : nx S.cen < S.n := by rw [n_eq']; omega

variable {S dim vs}

theorem σ_lt {i : ℕ} (hi : i < S.n + dim) : S.σ dim vs i = .var i := by simp [σ, hi]

theorem σ_vert {r : ℕ} (hr : r < 3 * vs.length) :
    S.σ dim vs (S.n + dim + r) = S.V (vs.getD (r / 3) 0) ⟨r % 3, Nat.mod_lt _ (by norm_num)⟩ := by
  simp [σ, hr]

theorem σ_Vc {u : ℕ} (hu : u ∈ vs) (c : Fin 3) : substE (S.σ dim vs) (S.Vc dim vs u c) = S.V u c := by
  have hl : vs.idxOf u < vs.length := List.idxOf_lt_length_of_mem hu
  have hr : 3 * vs.idxOf u + c < 3 * vs.length := by omega
  rw [Vc, substE_var, add_assoc (S.n + dim), σ_vert hr]
  have h1 : (3 * vs.idxOf u + c) / 3 = vs.idxOf u := by omega
  have h2 : (⟨(3 * vs.idxOf u + c) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = c := by
    ext; simp only; omega
  rw [h2]
  congr 1
  rw [h1, List.getD_eq_getElem _ _ hl, List.getElem_idxOf hl]

/-- The root's slack is the written-out slack with the vertices' expressions substituted. -/
theorem substE_gc {i : ℕ} (hvs : (S.con i).1 ∈ vs ∧ (S.con i).2.1 ∈ vs ∧ (S.con i).2.2 ∈ vs) :
    substE (S.σ dim vs) (S.gc dim vs i) = S.g i := by
  rw [gc, substE_slackE _ _ _ _ _ _ _ fun j hj ↦ σ_lt (by have := S.nx_lt; omega)]
  exact slackE_congr (funext (σ_Vc hvs.1)) (funext (σ_Vc hvs.2.1)) (funext (σ_Vc hvs.2.2))

section Values

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] {pts : List (V3 κ)}

/-- The values of `σ`'s expressions at `z`. -/
def W (S : Sys) (dim : ℕ) (vs : List ℕ) (z : ℕ → ℝ) (i : ℕ) : ℝ := (S.σ dim vs i).eval z

theorem eval_g (z : ℕ → ℝ) {i : ℕ}
    (hvs : (S.con i).1 ∈ vs ∧ (S.con i).2.1 ∈ vs ∧ (S.con i).2.2 ∈ vs) :
    (S.g i).eval z = (S.gc dim vs i).eval (W S dim vs z) := by
  rw [← substE_gc hvs, eval_substE]
  rfl

theorem eval_deriv_g (hV : S.V = vertsE S.n pts) (z : ℕ → ℝ) {i : ℕ}
    (hvs : (S.con i).1 ∈ vs ∧ (S.con i).2.1 ∈ vs ∧ (S.con i).2.2 ∈ vs) {v : ℕ} (hv : v < S.n) :
    (deriv v (S.g i)).eval z = (deriv v (S.gc dim vs i)).eval (W S dim vs z) := by
  rw [← substE_gc hvs]
  refine eval_deriv_substE _ z v (fun j ↦ ?_) _
  by_cases h1 : j < S.n + dim
  · rw [σ_lt h1]; rfl
  · by_cases h2 : j - (S.n + dim) < 3 * vs.length
    · obtain ⟨r, rfl⟩ : ∃ r, j = S.n + dim + r := ⟨j - (S.n + dim), by omega⟩
      rw [σ_vert (by omega), hV, eval_deriv_vertsE z hv]
      simp [show S.n + dim + r ≠ v by omega]
    · simp only [σ, if_neg h1, if_neg h2, deriv, Expr.eval]
      simp [show j ≠ v by omega]

theorem eval_stat (hV : S.V = vertsE S.n pts) (z : ℕ → ℝ)
    (hvs : ∀ i < S.k, (S.con i).1 ∈ vs ∧ (S.con i).2.1 ∈ vs ∧ (S.con i).2.2 ∈ vs) {v : ℕ}
    (hv : v < S.nv) : (S.stat v).eval z = (S.statc dim vs v).eval (W S dim vs z) := by
  have hvn : v < S.n := by rw [n]; omega
  simp only [stat, statc, Expr.eval, eval_sumE]
  congr 1
  refine sum_congr rfl fun i hi ↦ ?_
  have hi' := mem_range.mp hi
  rw [eval_deriv_g hV z (hvs i hi') hvn]
  congr 1
  simp only [mE, Expr.eval, W]
  rw [σ_lt (by rw [n_eq']; omega)]
  rfl

end Values

end Sys

/-! ### The scales of the written-out system -/

section Main

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The explicit index of the unknown `i` of the root's system: the scale first. -/
def Sys.pos (S : Sys) (i : ℕ) : ℕ := if i = nx S.cen then 0 else if i < nx S.cen then i + 1 else i

theorem Sys.τ_unknown (S : Sys) (dim : ℕ) (vs : List ℕ) (par : ℕ → RationalPolynomial) {i : ℕ}
    (hi : i < S.n) : S.τ dim vs par i = RationalPolynomial.var (S.pos i) := by
  unfold Sys.τ Sys.pos
  split_ifs <;> first | rfl | omega

theorem Sys.box_getD_pos (S : Sys) (dim : ℕ) (vs : List ℕ) (K : Kraw) (par : ℕ → RationalPolynomial)
    (geqs : List RationalPolynomial) (gbox : List (ℚ × ℚ)) {i : ℕ} (hi : i < S.n) :
    (S.explicitZ dim vs K par geqs gbox).box.getD (S.pos i) (0, 0) = K.kbox i := by
  simp only [Sys.explicitZ]
  have hn := S.n_eq'
  unfold Sys.pos
  split_ifs with h1 h2
  · subst h1; rfl
  · rw [List.cons_append, List.getD_cons_succ, List.append_assoc,
      List.getD_append _ _ _ _ (by simpa using h2)]
    simp [List.getD_eq_getElem?_getD, h2]
  · obtain ⟨j, rfl⟩ : ∃ j, i = nx S.cen + 1 + j := ⟨i - (nx S.cen + 1), by omega⟩
    rw [show nx S.cen + 1 + j = (nx S.cen + j) + 1 by omega, List.cons_append,
      List.getD_cons_succ, List.append_assoc, List.getD_append_right _ _ _ _ (by simp),
      List.getD_append _ _ _ _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, show j < S.k by omega]
    congr 1
    omega

theorem Sys.box_getD_gen (S : Sys) (dim : ℕ) (vs : List ℕ) (K : Kraw) (par : ℕ → RationalPolynomial)
    (geqs : List RationalPolynomial) (gbox : List (ℚ × ℚ)) (i : ℕ) :
    (S.explicitZ dim vs K par geqs gbox).box.getD (S.n + i) (0, 0) = gbox.getD i (0, 0) := by
  simp only [Sys.explicitZ]
  rw [List.getD_append_right _ _ _ _ (by simp [S.n_eq']; omega)]
  congr 1
  simp [S.n_eq']
  omega

theorem Sys.box_length (S : Sys) (dim : ℕ) (vs : List ℕ) (K : Kraw) (par : ℕ → RationalPolynomial)
    (geqs : List RationalPolynomial) (gbox : List (ℚ × ℚ)) :
    (S.explicitZ dim vs K par geqs gbox).box.length = S.n + gbox.length := by
  simp [Sys.explicitZ, S.n_eq']
  omega

/-- **The written-out system of a root.** If the root's system has exactly one zero `y` in the
box of the test (`Kraw.IsZero`), with the basis values of the field `κ` as parameters, the only
scale of the written-out system is the scale coordinate of `y`. -/
theorem Sys.scales_explicit {S : Sys} {K : Kraw} (hK : K.eqs = S.eqs) {pts : List (V3 κ)}
    (hV : S.V = vertsE S.n pts) {F : ParData} (hF : F.Spec κ) {vs : List ℕ}
    (hvs : ∀ i < S.k, (S.con i).1 ∈ vs ∧ (S.con i).2.1 ∈ vs ∧ (S.con i).2.2 ∈ vs)
    {y : Fin K.n → ℝ} (hz : K.IsZero (basisPar κ) y) :
    PolynomialSystem.scales [S.explicit (ExactBasis.dim κ) vs K (F.par S.n) (F.eqs S.n) F.box] =
      {K.env (basisPar κ) y (nx S.cen)} := by
  obtain ⟨hsound, val, hcomplete⟩ := hF
  set dim := ExactBasis.dim κ
  set E := S.explicitZ dim vs K (F.par S.n) (F.eqs S.n) F.box with hE
  have hn : K.n = S.n := Sys.n_eq hK
  have hnx := S.nx_lt
  -- the parameters are the basis values where the generator's conditions hold
  have hgen : ∀ x : ℕ → ℝ, E.Solves x → InBox F.box S.n x ∧ ∀ p ∈ F.eqs S.n, p.eval x = 0 := by
    intro x ⟨hb, he⟩
    refine ⟨fun i hi ↦ ?_, fun p hp ↦ he p (List.mem_append_right _ hp)⟩
    have := hb (S.n + i) (by rw [Sys.box_length]; omega)
    rwa [Sys.box_getD_gen] at this
  -- the point of the root's system of a point of the written-out one
  let zX : (ℕ → ℝ) → ℕ → ℝ := fun x i ↦ (S.τ dim vs (F.par S.n) i).eval x
  have hzX_unknown : ∀ x i, i < S.n → zX x i = x (S.pos i) := fun x i hi ↦ by
    simp only [zX, S.τ_unknown dim vs _ hi, RationalPolynomial.eval_var]
  have hzX_par : ∀ x, (∀ j, (F.par S.n j).eval x = basisPar κ j) → ∀ j < dim,
      zX x (S.n + j) = basisPar κ j := fun x hp j hj ↦ by
    simp only [zX, Sys.τ]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    rw [show S.n + j - S.n = j by omega, hp]
  have hzX_vert : ∀ x r, r < 3 * vs.length → zX x (S.n + dim + r) = x (S.n + 1 + r) :=
    fun x r hr ↦ by
      simp only [zX, Sys.τ]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega), RationalPolynomial.eval_var]
      congr 1
      omega
  have hzX_rest : ∀ x i, S.n + dim + 3 * vs.length ≤ i → zX x i = 0 := fun x i hi ↦ by
    simp only [zX, Sys.τ]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
    simp
  -- membership of the equations
  have hmem_g : ∀ i < S.k, RationalPolynomial.ofExpr (S.τ dim vs (F.par S.n)) (S.gc dim vs i) ∈ E.eqs :=
    fun i hi ↦ List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)))
  have hmem_s : ∀ v < S.nv, RationalPolynomial.ofExpr (S.τ dim vs (F.par S.n)) (S.statc dim vs v) ∈ E.eqs :=
    fun v hv ↦ List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨v, List.mem_range.mpr hv, rfl⟩)))
  have hmem_v : ∀ i < 3 * vs.length,
      RationalPolynomial.ofExpr (S.τ dim vs (F.par S.n)) (S.vertc dim vs i) ∈ E.eqs :=
    fun i hi ↦ List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
  -- the values of `σ` agree with the parameters
  have hW_lt : ∀ z i, i < S.n + dim → Sys.W S dim vs z i = z i := fun z i hi ↦ by
    simp only [Sys.W, Sys.σ_lt hi]; rfl
  have hW_vert : ∀ z r, r < 3 * vs.length → Sys.W S dim vs z (S.n + dim + r) =
      (S.V (vs.getD (r / 3) 0) ⟨r % 3, Nat.mod_lt _ (by norm_num)⟩).eval z := fun z r hr ↦ by
    simp only [Sys.W, Sys.σ_vert hr]
  have hW_rest : ∀ z i, S.n + dim + 3 * vs.length ≤ i → Sys.W S dim vs z i = 0 := fun z i hi ↦ by
    simp only [Sys.W, Sys.σ]
    rw [if_neg (by omega), if_neg (by omega)]
    simp [Expr.eval]
  have hV_congr : ∀ (z z' : ℕ → ℝ), (∀ j < dim, z (S.n + j) = z' (S.n + j)) → ∀ u c,
      (S.V u c).eval z = (S.V u c).eval z' := fun z z' h u c ↦ by
    rw [hV]; exact eval_vertsE_congr _ pts u c h
  have henv_par : ∀ (y : Fin K.n → ℝ) j, K.env (basisPar κ) y (S.n + j) = basisPar κ j :=
    fun y j ↦ by simp [Kraw.env, hn]
  -- a point of the written-out system that solves it gives a zero of the root's system
  have hscale : ∀ x : ℕ → ℝ, E.Solves x → x 0 = K.env (basisPar κ) y (nx S.cen) := by
    intro x hx
    obtain ⟨hgb, hge⟩ := hgen x hx
    have hpar := hsound S.n x hgb hge
    let y' : Fin K.n → ℝ := fun i ↦ zX x i
    have hW : Sys.W S dim vs (K.env (basisPar κ) y') = zX x := by
      funext i
      by_cases h1 : i < S.n
      · rw [hW_lt _ _ (by omega)]
        simp [Kraw.env, hn, h1, y']
      by_cases h2 : i < S.n + dim
      · obtain ⟨j, rfl⟩ : ∃ j, i = S.n + j := ⟨i - S.n, by omega⟩
        rw [hW_lt _ _ h2, henv_par, hzX_par x hpar j (by omega)]
      by_cases h3 : i < S.n + dim + 3 * vs.length
      · obtain ⟨r, rfl⟩ : ∃ r, i = S.n + dim + r := ⟨i - (S.n + dim), by omega⟩
        have hr : r < 3 * vs.length := by omega
        rw [hW_vert _ _ hr]
        have heq := hx.2 _ (hmem_v r hr)
        rw [RationalPolynomial.eval_ofExpr] at heq
        simp only [Sys.vertc, Expr.eval] at heq
        change zX x (S.n + dim + r) - (S.V _ _).eval (zX x) = 0 at heq
        rw [sub_eq_zero] at heq
        rw [heq]
        refine hV_congr _ _ (fun j hj ↦ ?_) _ _
        rw [henv_par, hzX_par x hpar j hj]
      · rw [hW_rest _ _ (by omega), hzX_rest _ _ (by omega)]
    have hbox : y' ∈ K.box := by
      rw [Kraw.mem_box]
      intro i
      have hi : (i : ℕ) < S.n := hn ▸ i.2
      rw [← Kraw.mem_kbox_iff]
      have hb := hx.1 (S.pos i) (by
        rw [Sys.box_length]; unfold Sys.pos; split_ifs <;> omega)
      rw [Sys.box_getD_pos _ _ _ _ _ _ _ hi] at hb
      simpa [y', hzX_unknown x i hi] using hb
    have hF : K.F (basisPar κ) y' = 0 := by
      funext k
      have hk : (k : ℕ) < S.n := hn ▸ k.2
      change (K.eqs.getD k (.const 0)).eval (K.env (basisPar κ) y') = 0
      rw [hK]
      by_cases hkk : (k : ℕ) < S.k
      · rw [S.getD_eqs_g hkk, Sys.eval_g _ (hvs k hkk), hW]
        have := hx.2 _ (hmem_g k hkk)
        rwa [RationalPolynomial.eval_ofExpr] at this
      · obtain ⟨v, hv⟩ : ∃ v, (k : ℕ) = S.k + v := ⟨k - S.k, by omega⟩
        have hvn : v < S.nv := by rw [Sys.n] at hk; omega
        rw [hv, S.getD_eqs_stat hvn, Sys.eval_stat hV _ hvs hvn, hW]
        have := hx.2 _ (hmem_s v hvn)
        rwa [RationalPolynomial.eval_ofExpr] at this
    have hy := hz.2 y' ⟨hbox, hF⟩
    have h0 : x 0 = zX x (nx S.cen) := by
      rw [hzX_unknown x _ hnx]; simp [Sys.pos]
    rw [h0, ← hy]
    simp [Kraw.env, hn, hnx, y']
  -- the zero gives a solution
  have hsol : ∃ x : ℕ → ℝ, E.Solves x ∧ x 0 = K.env (basisPar κ) y (nx S.cen) := by
    set w := Sys.W S dim vs (K.env (basisPar κ) y)
    have hw_lt : ∀ i, i < S.n + dim → w i = K.env (basisPar κ) y i := fun i hi ↦ hW_lt _ i hi
    have hw_vert : ∀ r, r < 3 * vs.length → w (S.n + dim + r) =
        (S.V (vs.getD (r / 3) 0) ⟨r % 3, Nat.mod_lt _ (by norm_num)⟩).eval
          (K.env (basisPar κ) y) := fun r hr ↦ hW_vert _ r hr
    have hw_rest : ∀ i, S.n + dim + 3 * vs.length ≤ i → w i = 0 := fun i hi ↦ hW_rest _ i hi
    let x : ℕ → ℝ := fun i ↦
      if i = 0 then w (nx S.cen) else if i ≤ nx S.cen then w (i - 1) else if i < S.n then w i
      else if i = S.n then val else w (S.n + dim + (i - S.n - 1))
    have hxn : x S.n = val := by simp [x, show S.n ≠ 0 by omega, show ¬ S.n ≤ nx S.cen by omega]
    obtain ⟨hgb, hge⟩ := hcomplete S.n x hxn
    have hpar := hsound S.n x hgb hge
    have hz' : zX x = w := by
      funext i
      by_cases h1 : i < S.n
      · rw [hzX_unknown x i h1]
        by_cases hi0 : i = nx S.cen
        · subst hi0; simp only [x, Sys.pos, ↓reduceIte]
        · by_cases hi1 : i < nx S.cen
          · simp only [x, Sys.pos, hi0, hi1, ↓reduceIte, show i + 1 ≠ 0 by omega,
              show i + 1 ≤ nx S.cen by omega, Nat.add_sub_cancel]
          · simp only [x, Sys.pos, hi0, hi1, h1, ↓reduceIte, show i ≠ 0 by omega,
              show ¬ i ≤ nx S.cen by omega]
      by_cases h2 : i < S.n + dim
      · obtain ⟨j, rfl⟩ : ∃ j, i = S.n + j := ⟨i - S.n, by omega⟩
        rw [hzX_par x hpar j (by omega), hw_lt _ h2, henv_par]
      by_cases h3 : i < S.n + dim + 3 * vs.length
      · obtain ⟨r, rfl⟩ : ∃ r, i = S.n + dim + r := ⟨i - (S.n + dim), by omega⟩
        rw [hzX_vert x r (by omega)]
        simp only [x]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        congr 1
        omega
      · rw [hzX_rest _ _ (by omega), hw_rest _ (by omega)]
    refine ⟨x, ⟨fun i hi ↦ ?_, fun p hp ↦ ?_⟩, ?_⟩
    · rw [Sys.box_length] at hi
      by_cases h : i < S.n
      · -- the unknown at the explicit index `i`
        let j := if i = 0 then nx S.cen else if i ≤ nx S.cen then i - 1 else i
        have hj : j < S.n := by simp only [j]; split_ifs <;> omega
        have hpos : S.pos j = i := by simp only [j, Sys.pos]; split_ifs <;> omega
        rw [← hpos, Sys.box_getD_pos _ _ _ _ _ _ _ hj, ← hzX_unknown x j hj, hz', hw_lt _ (by omega)]
        have := (Kraw.mem_box K).mp hz.1.1 ⟨j, hn ▸ hj⟩
        rw [← Kraw.mem_kbox_iff] at this
        simpa [Kraw.env, hn, hj] using this
      · obtain ⟨i', rfl⟩ : ∃ i', i = S.n + i' := ⟨i - S.n, by omega⟩
        rw [Sys.box_getD_gen]
        exact hgb i' (by omega)
    · simp only [hE, Sys.explicitZ, List.mem_append, List.mem_map, List.mem_range] at hp
      rcases hp with ((⟨i, hi, rfl⟩ | ⟨v, hv, rfl⟩) | ⟨r, hr, rfl⟩) | hp
      · rw [RationalPolynomial.eval_ofExpr]
        change (S.gc dim vs i).eval (zX x) = 0
        rw [hz', ← Sys.eval_g _ (hvs i hi)]
        have := congrFun hz.1.2 ⟨i, by rw [hn]; rw [Sys.n] at *; omega⟩
        change (K.eqs.getD i (.const 0)).eval _ = 0 at this
        rwa [hK, S.getD_eqs_g hi] at this
      · rw [RationalPolynomial.eval_ofExpr]
        change (S.statc dim vs v).eval (zX x) = 0
        rw [hz', ← Sys.eval_stat hV _ hvs hv]
        have := congrFun hz.1.2 ⟨S.k + v, by rw [hn, Sys.n]; omega⟩
        change (K.eqs.getD (S.k + v) (.const 0)).eval _ = 0 at this
        rwa [hK, S.getD_eqs_stat hv] at this
      · rw [RationalPolynomial.eval_ofExpr]
        change (S.vertc dim vs r).eval (zX x) = 0
        rw [hz']
        simp only [Sys.vertc, Expr.eval]
        change w (S.n + dim + r) - (S.V _ _).eval w = 0
        rw [hw_vert _ hr, sub_eq_zero]
        refine hV_congr _ _ (fun j hj ↦ ?_) _ _
        rw [hw_lt _ (by omega)]
      · exact hge p hp
    · simp only [x, ↓reduceIte]
      rw [hw_lt _ (by omega)]
  -- the scales
  rw [Sys.explicit, ZSystem.scales_toSystem]
  ext l
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hscale x hx
  · rintro rfl
    exact hsol

end Main

/-- `v` inserted into a sorted list without repeats. -/
def insertSorted (v : ℕ) : List ℕ → List ℕ
  | [] => [v]
  | w :: ws => if v < w then v :: w :: ws else if v = w then w :: ws else w :: insertSorted v ws

theorem mem_insertSorted {u v : ℕ} : ∀ {l : List ℕ}, u ∈ insertSorted v l ↔ u = v ∨ u ∈ l
  | [] => by simp [insertSorted]
  | w :: ws => by
    unfold insertSorted
    split_ifs with h1 h2
    · simp
    · subst h2; simp only [List.mem_cons]; tauto
    · simp only [List.mem_cons, mem_insertSorted (l := ws)]; tauto

/-- The vertices of a root's contacts, sorted, without repeats. -/
def RootRec.vs (R : RootRec) : List ℕ :=
  R.contacts.foldr (fun c acc ↦ insertSorted c.1 (insertSorted c.2.1 (insertSorted c.2.2 acc))) []

theorem RootRec.mem_vs (R : RootRec) {c : ℕ × ℕ × ℕ} (hc : c ∈ R.contacts) :
    c.1 ∈ R.vs ∧ c.2.1 ∈ R.vs ∧ c.2.2 ∈ R.vs := by
  unfold RootRec.vs
  generalize R.contacts = l at hc
  induction l with
  | nil => simp at hc
  | cons d ds ih =>
    simp only [List.foldr_cons, mem_insertSorted]
    rcases List.mem_cons.mp hc with rfl | hc
    · tauto
    · have := ih hc; tauto

/-- **The written-out system of a root record**: the root's system with the parameters, the
generator's equations and intervals of `F`, over the vertices of its contacts. -/
def RootRec.explicit {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] (R : RootRec)
    (pts : List (V3 κ)) (F : ParData) : PolynomialSystem :=
  (R.sys pts).explicit (ExactBasis.dim κ) R.vs (R.kraw pts) (F.par (R.sys pts).n)
    (F.eqs (R.sys pts).n) F.box

/-- **The scales of a root record's written-out system**: the root's scale alone. -/
theorem RootRec.scales_explicit {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]
    (R : RootRec) (pts : List (V3 κ)) {F : ParData} (hF : F.Spec κ)
    {y : Fin (R.kraw pts).n → ℝ} (hz : (R.kraw pts).IsZero (basisPar κ) y) :
    PolynomialSystem.scales [R.explicit pts F] = {(R.kraw pts).env (basisPar κ) y (nx R.cen)} := by
  refine Sys.scales_explicit (R.kraw_eqs pts) (pts := pts) rfl hF (fun i hi ↦ ?_) hz
  have hi' : i < R.contacts.length := hi
  simp only [Sys.con, RootRec.sys, List.getD_eq_getElem _ _ hi']
  exact R.mem_vs (List.getElem_mem hi')

/-! ### The Nieuwland number of a root-form certificate -/

section Top

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The interval of a root's scale: the scale's interval in the root's box. -/
def RootRec.lo (R : RootRec) : ℚ :=
  (((R.c.getD (nx R.cen) 0 : ℤ) - ((R.ρ.getD (nx R.cen) 0 : ℕ) : ℤ) : ℤ) : ℚ) / 2 ^ R.s

/-- The upper end of `RootRec.lo`'s interval. -/
def RootRec.hi (R : RootRec) : ℚ :=
  (((R.c.getD (nx R.cen) 0 : ℤ) + ((R.ρ.getD (nx R.cen) 0 : ℕ) : ℤ) : ℤ) : ℚ) / 2 ^ R.s

theorem RootRec.scale_mem (R : RootRec) (pts : List (V3 κ)) {y : Fin (R.kraw pts).n → ℝ}
    (hz : (R.kraw pts).IsZero (basisPar κ) y) :
    (R.lo : ℝ) ≤ (R.kraw pts).env (basisPar κ) y (nx R.cen) ∧
      (R.kraw pts).env (basisPar κ) y (nx R.cen) ≤ R.hi := by
  have hn : nx R.cen < (R.kraw pts).n := by
    rw [Sys.n_eq (R.kraw_eqs pts)]; exact (R.sys pts).nx_lt
  have henv : (R.kraw pts).env (basisPar κ) y (nx R.cen) = y ⟨nx R.cen, hn⟩ := by
    simp [Kraw.env, hn]
  rw [henv]
  have h := (Kraw.mem_box _).mp hz.1.1 ⟨nx R.cen, hn⟩
  rw [← Kraw.mem_kbox_iff] at h
  exact h

/-- The test that every root of `Rs` is one of the roots `T` (indices into `Rs`) or has its scale's
interval below the interval of one of them. -/
def sepOk (R : RootRec) (Rs : List RootRec) (T : List ℕ) : Bool :=
  (List.range (R :: Rs).length).all fun j ↦
    T.contains j || T.any fun i ↦ decide (((R :: Rs).getD j R).hi ≤ ((R :: Rs).getD i R).lo)

/-- **The Nieuwland number of a root-form certificate as the largest scale of written-out
systems.** `N` is the largest of the scales of the roots `R :: Rs`, every root has the only zero of
its system in its box, and every root is one of the roots `T` (indices into `R :: Rs`) or lies
below one of them (`sepOk`). Then `N` is the largest scale of the written-out systems of the
roots `T`. -/
theorem isGreatest_topScale {pts : List (V3 κ)} {F : ParData} (hF : F.Spec κ) {R : RootRec}
    {Rs : List RootRec} {N : ℝ} (hN : N = topScale pts R Rs)
    (hz : ∀ R' ∈ R :: Rs, ∃ y, (R'.kraw pts).IsZero (basisPar κ) y ∧
      R'.scale pts = (R'.kraw pts).env (basisPar κ) y (nx R'.cen))
    (T : List ℕ) (hT : ∀ i ∈ T, i < (R :: Rs).length) (hsep : sepOk R Rs T = true)
    {Ss : List PolynomialSystem} (hSs : Ss = T.map fun i ↦ ((R :: Rs).getD i R).explicit pts F) :
    IsGreatest (PolynomialSystem.scales Ss) N := by
  set A := R :: Rs
  -- the scales of the systems of `T`
  have hsc : ∀ l, l ∈ PolynomialSystem.scales Ss ↔ ∃ i ∈ T, l = (A.getD i R).scale pts := by
    intro l
    constructor
    · rintro ⟨S, hS, x, hx, rfl⟩
      rw [hSs, List.mem_map] at hS
      obtain ⟨i, hi, rfl⟩ := hS
      have hmem : A.getD i R ∈ A := by
        rw [List.getD_eq_getElem _ _ (hT i hi)]; exact List.getElem_mem _
      obtain ⟨y, hy, hs⟩ := hz _ hmem
      have := (A.getD i R).scales_explicit pts hF hy
      have hl : x 0 ∈ PolynomialSystem.scales [(A.getD i R).explicit pts F] :=
        ⟨_, List.mem_singleton_self _, x, hx, rfl⟩
      rw [this, Set.mem_singleton_iff] at hl
      exact ⟨i, hi, hl.trans hs.symm⟩
    · rintro ⟨i, hi, rfl⟩
      have hmem : A.getD i R ∈ A := by
        rw [List.getD_eq_getElem _ _ (hT i hi)]; exact List.getElem_mem _
      obtain ⟨y, hy, hs⟩ := hz _ hmem
      have := (A.getD i R).scales_explicit pts hF hy
      have hl : (A.getD i R).scale pts ∈ PolynomialSystem.scales [(A.getD i R).explicit pts F]
        := by rw [this, hs]; rfl
      obtain ⟨S, hS, x, hx, h0⟩ := hl
      rw [List.mem_singleton.mp hS] at hx
      exact ⟨_, by rw [hSs]; exact List.mem_map.mpr ⟨i, hi, rfl⟩, x, hx, h0⟩
  -- every root's scale lies in its interval
  have hint : ∀ j < A.length, ((A.getD j R).lo : ℝ) ≤ (A.getD j R).scale pts ∧
      (A.getD j R).scale pts ≤ (A.getD j R).hi := by
    intro j hj
    have hmem : A.getD j R ∈ A := by
      rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
    obtain ⟨y, hy, hs⟩ := hz _ hmem
    rw [hs]
    exact (A.getD j R).scale_mem pts hy
  refine ⟨?_, fun l hl ↦ ?_⟩
  · obtain ⟨R', hR', htop⟩ := topScale_mem pts R Rs
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hR'
    have hjd : A.getD j R = A[j] := List.getD_eq_getElem _ _ hj
    simp only [sepOk, List.all_eq_true, List.mem_range, Bool.or_eq_true, List.contains_iff_mem,
      List.any_eq_true, decide_eq_true_eq] at hsep
    rcases hsep j hj with hjT | ⟨i, hi, hle⟩
    · exact (hsc N).mpr ⟨j, hjT, by rw [hN, htop, hjd]⟩
    · refine (hsc N).mpr ⟨i, hi, le_antisymm ?_ ?_⟩
      · calc N = A[j].scale pts := by rw [hN, htop]
          _ ≤ A[j].hi := hjd ▸ (hint j hj).2
          _ ≤ (A.getD i R).lo := by rw [← hjd]; exact_mod_cast hle
          _ ≤ (A.getD i R).scale pts := (hint i (hT i hi)).1
      · rw [hN]
        refine le_topScale pts R Rs ?_
        rw [List.getD_eq_getElem _ _ (hT i hi)]; exact List.getElem_mem _
  · obtain ⟨i, hi, rfl⟩ := (hsc l).mp hl
    rw [hN]
    refine le_topScale pts R Rs ?_
    rw [List.getD_eq_getElem _ _ (hT i hi)]; exact List.getElem_mem _

/-- **A root-form certificate with one root**: its Nieuwland number is the only scale of the
root's written-out system. -/
theorem isGreatest_one {pts : List (V3 κ)} {F : ParData} (hF : F.Spec κ) {R : RootRec} {N : ℝ}
    (h : ∃ y, (R.kraw pts).IsZero (basisPar κ) y ∧ N = (R.kraw pts).env (basisPar κ) y (nx R.cen))
    {Ss : List PolynomialSystem} (hSs : Ss = [R.explicit pts F]) :
    IsGreatest (PolynomialSystem.scales Ss) N := by
  obtain ⟨y, hy, rfl⟩ := h
  rw [hSs, R.scales_explicit pts hF hy]
  exact isGreatest_singleton

end Top

end Nieuwland.Root
