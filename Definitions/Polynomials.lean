import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.List.GetD

/-!
# Polynomials with rational coefficients, as data

A polynomial in the variables `x 0, x 1, …` is written as a list of terms, so that a polynomial
of a statement is data that can be read, printed and computed with.

A system is finitely many polynomial equations with rational coefficients together with a box: a
closed interval with rational end points for each of its variables. A root is a point of the box
at which every equation holds.

The coordinates of some polyhedra lie in a number field `ℚ(θ)`: `θ` is the root of a rational
polynomial in one variable in an interval that isolates it, and a coordinate is a rational
polynomial in `θ` (`polyEval`, `realRoot`).
-/

namespace Nieuwland

/-! ### Polynomials in several variables -/

/-- A polynomial with rational coefficients in the variables `x 0, x 1, …`: a list of terms
`(c, [(i, e), (j, f), …])`, each standing for `c * x i ^ e * x j ^ f * ⋯`. -/
abbrev RationalPolynomial := List (ℚ × List (ℕ × ℕ))

/-- The monomial `x i ^ e * x j ^ f * ⋯` of the powers `m = [(i, e), (j, f), …]`. -/
def monomial (x : ℕ → ℝ) (m : List (ℕ × ℕ)) : ℝ :=
  (m.map fun v ↦ x v.1 ^ v.2).prod

/-- The value of a polynomial at the real point `x`. -/
def RationalPolynomial.eval (p : RationalPolynomial) (x : ℕ → ℝ) : ℝ :=
  (p.map fun t ↦ (t.1 : ℝ) * monomial x t.2).sum

/-- Every variable of `p` is one of `x 0, …, x (n - 1)`. -/
def RationalPolynomial.varsLt (n : ℕ) (p : RationalPolynomial) : Bool :=
  p.all fun t ↦ t.2.all fun v ↦ decide (v.1 < n)

/-! ### Systems in a rational box, and systems with exactly one root -/

/-- A system of polynomial equations with a box. -/
structure PolynomialSystem where
  /-- The equations: each pair `(p, q)` is the equation `p = q`. -/
  eqs : List (RationalPolynomial × RationalPolynomial)
  /-- The box: the closed interval `[lo, hi]` of `x 0`, of `x 1`, and so on. -/
  box : List (ℚ × ℚ)

namespace PolynomialSystem

/-- `x` is a root of `S`: every variable lies in its interval and every equation holds. -/
def Solves (S : PolynomialSystem) (x : ℕ → ℝ) : Prop :=
  (∀ i < S.box.length, ((S.box.getD i (0, 0)).1 : ℝ) ≤ x i ∧ x i ≤ ((S.box.getD i (0, 0)).2 : ℝ)) ∧
    ∀ e ∈ S.eqs, e.1.eval x = e.2.eval x

/-- Every variable of the equations of `S` has an interval. -/
def boxed (S : PolynomialSystem) : Bool :=
  S.eqs.all fun e ↦ e.1.varsLt S.box.length && e.2.varsLt S.box.length

/-- **`S` has exactly one root**: it has a first variable, every variable of its equations has an
interval, and exactly one point of the box solves the equations (any two roots agree on every
variable of the system). -/
def HasUniqueRoot (S : PolynomialSystem) : Prop :=
  0 < S.box.length ∧ S.boxed = true ∧
    ∃ x : ℕ → ℝ, S.Solves x ∧ ∀ y : ℕ → ℝ, S.Solves y → ∀ i < S.box.length, y i = x i

end PolynomialSystem

/-! ### Real roots of polynomials in one variable -/

/-- `∑ᵢ pᵢ xⁱ`, the coefficients listed from the constant one. -/
noncomputable def polyEval (p : List ℚ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range p.length, (p.getD i 0 : ℝ) * x ^ i

/-- The largest root of `p` in `(lo, hi)`: the supremum of the roots there. It is the root when
the interval holds exactly one. -/
noncomputable def realRoot (p : List ℚ) (lo hi : ℚ) : ℝ :=
  sSup {x : ℝ | (lo : ℝ) < x ∧ x < hi ∧ polyEval p x = 0}

end Nieuwland
