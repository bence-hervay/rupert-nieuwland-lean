import Modules.Check.Number.Ext
import Modules.Check.Leaf.FitCheck
import Modules.Root.Krawczyk
import Modules.Root.Slack

/-!
# The contact system of a root record

A root record of a D2 certificate (`code/src/proof/d2/`, "Records and what is checked") names
charts, a mode and contacts `A`. Its system, in the unknowns `(x, l, m)` (pose, scale,
multipliers), is `g_i = 0` for the slacks of the contacts and `∑ m_i ∂_v g_i = [v = l]` for every
unknown `v` of `(x, l)`: the scale is stationary on the contact set.

* `deriv`: the formal derivative of an expression (no analysis: the stationarity equations and
  the touch leaf's expansion use the same syntactic operator).
* `Sys`: the record; `Sys.eqs` its equations in the checker's order (slacks, then stationarity),
  ready for `Kraw` (`Modules/Root/Krawczyk.lean`); `Sys.g_zero`, `Sys.stat_zero`: what a zero
  satisfies.
* `vertsE`: the solid's vertex coordinates as expressions in the basis values of its field, the
  parameters of the system (`vertOf_vertsE`); `parOk_of_basis`.
* `bval`: the ball of an expression's value; `Kraw.zballs`: balls of all variables at the zero.
-/

open Nieuwland.Check Finset

namespace Nieuwland.Root

/-- The formal derivative of an expression in the variable `v`. -/
def deriv (v : ℕ) : Expr → Expr
  | .const _ => .const 0
  | .var i => .const (if i = v then 1 else 0)
  | .add a b => .add (deriv v a) (deriv v b)
  | .sub a b => .sub (deriv v a) (deriv v b)
  | .mul a b => .add (.mul (deriv v a) b) (.mul a (deriv v b))

/-- The sum of the expressions `f 0, …, f (n - 1)`. -/
def sumE (n : ℕ) (f : ℕ → Expr) : Expr :=
  (List.range n).foldl (fun acc i ↦ .add acc (f i)) (.const 0)

theorem sumE_succ (n : ℕ) (f : ℕ → Expr) : sumE (n + 1) f = .add (sumE n f) (f n) := by
  simp [sumE, List.range_succ, List.foldl_append]

theorem eval_sumE {R : Type*} [CommRing R] (z : ℕ → R) (n : ℕ) (f : ℕ → Expr) :
    (sumE n f).eval z = ∑ i ∈ range n, (f i).eval z := by
  induction n with
  | zero => simp [sumE]
  | succ n ih => rw [sumE_succ, sum_range_succ, ← ih]; rfl

theorem eval_deriv_sumE {R : Type*} [CommRing R] (z : ℕ → R) (v n : ℕ) (f : ℕ → Expr) :
    (deriv v (sumE n f)).eval z = ∑ i ∈ range n, (deriv v (f i)).eval z := by
  induction n with
  | zero => simp [sumE, deriv]
  | succ n ih => rw [sumE_succ, sum_range_succ, ← ih]; rfl

/-- The ball of an expression's value, from balls of the variables. -/
def bval (Y : ℕ → Ball) : Expr → Ball
  | .const c => Ball.ofInt c
  | .var i => Y i
  | .add a b => bval Y a + bval Y b
  | .sub a b => bval Y a - bval Y b
  | .mul a b => bval Y a * bval Y b

theorem encl_bval {Y : ℕ → Ball} {y : ℕ → ℝ} (hY : ∀ i, (Y i).Encl (y i)) (e : Expr) :
    (bval Y e).Encl (e.eval y) := by
  induction e with
  | const c => exact Ball.encl_ofInt c
  | var i => exact hY i
  | add a b iha ihb => exact Ball.encl_add iha ihb
  | sub a b iha ihb => exact Ball.encl_sub iha ihb
  | mul a b iha ihb => exact Ball.encl_mul iha ihb

/-! ### The solid's vertices as expressions -/

section Field

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- A value of the field with coordinates `cs`: an expression in the basis values, the
variables `nu, nu + 1, …`. -/
def elemE (nu dim : ℕ) (cs : List ℤ) : Expr :=
  sumE dim fun j ↦ .mul (.const (cs.getD j 0)) (.var (nu + j))

theorem eval_elemE (z : ℕ → ℝ) (nu : ℕ)
    (hz : ∀ j < ExactBasis.dim κ, z (nu + j) = ExactBasis.basis κ j) (a : κ) :
    (elemE nu (ExactBasis.dim κ) (ExactBasis.coords a)).eval z = Exact.re a := by
  rw [ExactBasis.re_eq, elemE, eval_sumE, bsum]
  refine sum_congr rfl fun j hj ↦ ?_
  have h := List.getD_map (l := ExactBasis.coords a) (n := j) (d := (0 : ℤ)) (Int.cast : ℤ → ℝ)
  rw [Int.cast_zero] at h
  rw [h, ← hz j (mem_range.mp hj)]
  simp only [Expr.eval]
  ring

/-- The coordinates of the vertices of `pts` as expressions in the basis values. -/
def vertsE (nu : ℕ) (pts : List (V3 κ)) (v : ℕ) (c : Fin 3) : Expr :=
  elemE nu (ExactBasis.dim κ) (ExactBasis.coords ((Exact.pt pts v).get c))

theorem vertOf_vertsE (z : ℕ → ℝ) (nu : ℕ)
    (hz : ∀ j < ExactBasis.dim κ, z (nu + j) = ExactBasis.basis κ j) (pts : List (V3 κ)) (v : ℕ) :
    vertOf z (vertsE nu pts) v = Exact.reV (Exact.pt pts v) := by
  funext c
  simp only [vertOf, vertsE, eval_elemE z nu hz]
  fin_cases c <;> rfl

/-- The parameters of a system over `κ`: the basis values. -/
noncomputable def basisPar (κ : Type) [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] (j : ℕ) : ℝ :=
  if j < ExactBasis.dim κ then ExactBasis.basis κ j else 0

/-- Balls of the basis values are balls of the parameters. -/
theorem parOk_of_basis {K : Kraw} (hlen : K.par.length = ExactBasis.dim κ)
    (hb : ∀ j < ExactBasis.dim κ, (K.par.getD j (Ball.ofInt 0)).Encl (ExactBasis.basis κ j)) :
    K.ParOk (basisPar κ) := by
  intro j
  unfold basisPar
  split_ifs with hj
  · exact hb j hj
  · rw [List.getD_eq_default _ _ (by omega)]
    simpa using Ball.encl_ofInt 0

end Field

/-! ### The system -/

/-- A root record's system: mode, charts, contacts `(a, b, k)` (the plug vertex `k` against the
hole edge `a → b`) and the vertices' coordinates. -/
structure Sys where
  /-- Centred mode: no translation. -/
  cen : Bool
  /-- The view chart. -/
  view : Fin 3
  /-- The rotation chart. -/
  rot : Fin 4
  /-- The contacts. -/
  contacts : List (ℕ × ℕ × ℕ)
  /-- The vertices' coordinates. -/
  V : ℕ → Fin 3 → Expr

namespace Sys

variable (S : Sys)

/-- The number of contacts. -/
def k : ℕ := S.contacts.length

/-- The number of unknowns of `(x, l)`. -/
def nv : ℕ := nx S.cen + 1

/-- The number of unknowns. -/
def n : ℕ := S.nv + S.k

/-- The contact `i`. -/
def con (i : ℕ) : ℕ × ℕ × ℕ := S.contacts.getD i (0, 0, 0)

/-- The slack of a contact. -/
def slack (c : ℕ × ℕ × ℕ) : Expr := slackE S.cen S.view S.rot S.V c.1 c.2.1 c.2.2

/-- The slack of the contact `i`. -/
def g (i : ℕ) : Expr := S.slack (S.con i)

/-- The stationarity equation of the unknown `v` of `(x, l)`: `∑ m_i ∂_v g_i - [v = l]`. -/
def stat (v : ℕ) : Expr :=
  .sub (sumE S.k fun i ↦ .mul (mE S.cen i) (deriv v (S.g i)))
    (.const (if v = nx S.cen then 1 else 0))

/-- The equations: the slacks, then stationarity (the order of `check_root`). -/
def eqs : List Expr := (List.range S.k).map S.g ++ (List.range S.nv).map S.stat

theorem length_eqs : S.eqs.length = S.n := by
  simp [eqs, n, Nat.add_comm]

theorem getD_eqs_g {i : ℕ} (hi : i < S.k) : S.eqs.getD i (.const 0) = S.g i := by
  simp [eqs, List.getD_eq_getElem?_getD, List.getElem?_append_left, hi]

theorem getD_eqs_stat {v : ℕ} (hv : v < S.nv) : S.eqs.getD (S.k + v) (.const 0) = S.stat v := by
  simp [eqs, List.getD_eq_getElem?_getD, hv]

variable {S} {K : Kraw}

theorem n_eq (hK : K.eqs = S.eqs) : K.n = S.n := by rw [Kraw.n, hK, S.length_eqs]

/-- At a zero of the system the slacks of the contacts vanish. -/
theorem g_zero (hK : K.eqs = S.eqs) {p : ℕ → ℝ} {y : Fin K.n → ℝ} (h0 : K.F p y = 0) {i : ℕ}
    (hi : i < S.k) : (S.g i).eval (K.env p y) = 0 := by
  have hn := n_eq hK
  have h := congrFun h0 ⟨i, by rw [hn, n]; omega⟩
  change (K.eqs.getD i (.const 0)).eval (K.env p y) = 0 at h
  rwa [hK, S.getD_eqs_g hi] at h

/-- At a zero of the system the scale is stationary: `∑ m_i ∂_v g_i = [v = l]`. -/
theorem stat_zero (hK : K.eqs = S.eqs) {p : ℕ → ℝ} {y : Fin K.n → ℝ} (h0 : K.F p y = 0) {v : ℕ}
    (hv : v < S.nv) :
    ∑ i ∈ range S.k, (mE S.cen i).eval (K.env p y) * (deriv v (S.g i)).eval (K.env p y) =
      ((if v = nx S.cen then 1 else 0 : ℤ) : ℝ) := by
  have hn := n_eq hK
  have h := congrFun h0 ⟨S.k + v, by rw [hn, n]; omega⟩
  change (K.eqs.getD (S.k + v) (.const 0)).eval (K.env p y) = 0 at h
  rw [hK, S.getD_eqs_stat hv] at h
  have e : (S.stat v).eval (K.env p y) =
      ∑ i ∈ range S.k, (mE S.cen i).eval (K.env p y) * (deriv v (S.g i)).eval (K.env p y) -
        ((if v = nx S.cen then 1 else 0 : ℤ) : ℝ) := by
    rw [stat]
    change (sumE S.k fun i ↦ .mul (mE S.cen i) (deriv v (S.g i))).eval (K.env p y) - _ = _
    rw [eval_sumE]
    rfl
  rw [e] at h
  exact sub_eq_zero.mp h

end Sys

/-! ### Balls of the variables at the zero -/

namespace Kraw

variable (K : Kraw)

/-- Balls of all variables at the zero: the unknowns' enclosures (`Kraw.encl`), then the
parameters'. Computed once. -/
def zballs : List Ball :=
  let Sl := K.slopes
  let Fcs := K.centres
  (List.range K.n).map (fun i ↦ (⟨K.c.getD i 0, 0, K.s⟩ : Ball) + K.W Sl Fcs i) ++ K.par

/-- The ball of the variable `i` at the zero. -/
def zball (Z : List Ball) (i : ℕ) : Ball := Z.getD i (Ball.ofInt 0)

theorem encl_zballs {p : ℕ → ℝ} (hp : K.ParOk p) {y : Fin K.n → ℝ}
    (hy : y ∈ K.box) (h0 : K.F p y = 0) (i : ℕ) :
    (zball K.zballs i).Encl (K.env p y i) := by
  unfold zball zballs
  by_cases hi : i < K.n
  · have h := K.encl_zero hp hy h0 ⟨i, hi⟩
    simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left, hi, Kraw.env, Kraw.encl] using h
  · have h := hp (i - K.n)
    simpa [List.getD_eq_getElem?_getD, List.getElem?_append_right, not_lt.mp hi, Kraw.env, hi]
      using h

theorem env_par (p : ℕ → ℝ) (y : Fin K.n → ℝ) (j : ℕ) : K.env p y (K.n + j) = p j := by
  simp [Kraw.env]

end Kraw

end Nieuwland.Root
