import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Bounds.Defs

/-!
# Numbers given by finitely many systems of integer polynomial equations

The shared definition of every solid's headline theorem `<def>_nu`
(`ν <def> ∈ Set.Icc (k / 10 ^ 30) ((k + 1) / 10 ^ 30) ∧ IsPolynomialSystemMax (ν <def>)`):

* `Nieuwland.IntSystem`: finitely many polynomial equations `p = 0` with integer coefficients in the
  real variables `x 0, x 1, …` (Mathlib's `MvPolynomial ℕ ℤ`), and closed rational intervals for
  the first variables;
* `Nieuwland.IntSystem.Solves S x`: the point `x` lies in the intervals of `S` and solves its
  equations;
* `Nieuwland.IntSystem.firstValues S`: the values of the first variable `x 0` at the real solutions
  of `S`;
* `Nieuwland.IsPolynomialSystemMax a`: `a` is the largest value of the first variable `x 0` over the real
  solutions of finitely many such systems, at the solutions of each of which `x 0` has one and the
  same value.

A number with `IsPolynomialSystemMax` is an exact algebraic description: the systems determine it, each
system pins down one value, and the number can be computed from them alone to any precision.
(Such numbers are exactly the real algebraic numbers, a remark that is not used or proved here.)
For each solid the systems are written out in its theorem `<def>_exact`, the witness of
`<def>_nu`, and in the file `fixtures/nieuwland/<family>/<name>.system.json`.
-/

namespace Nieuwland

/-- A system of polynomial equations `p = 0`, each `p` with integer coefficients in the variables
`x 0, x 1, …`, and closed rational intervals `box`: `[lo, hi]` for `x 0`, then for `x 1`, and so
on (the variables after the last interval are unconstrained). -/
structure IntSystem where
  /-- The polynomials, each set to `0`. -/
  eqs : List (MvPolynomial ℕ ℤ)
  /-- The intervals of `x 0, x 1, …` in turn. -/
  box : List (ℚ × ℚ)

/-- The real point `x` solves `S`: each variable with an interval lies in it, and every polynomial
of `S` is `0` at `x`. -/
def IntSystem.Solves (S : IntSystem) (x : ℕ → ℝ) : Prop :=
  (∀ i (h : i < S.box.length), ((S.box[i]).1 : ℝ) ≤ x i ∧ x i ≤ ((S.box[i]).2 : ℝ)) ∧
    ∀ p ∈ S.eqs, MvPolynomial.aeval x p = 0

/-- The values of the first variable `x 0` at the real solutions of `S`. -/
def IntSystem.firstValues (S : IntSystem) : Set ℝ :=
  {l | ∃ x : ℕ → ℝ, S.Solves x ∧ x 0 = l}

/-- `a` is **the largest value of the first variable** `x 0` over the real solutions of finitely
many systems of integer polynomial equations in rational intervals, **each system's solutions
having one and the same value of `x 0`**. -/
def IsPolynomialSystemMax (a : ℝ) : Prop :=
  ∃ Ss : List IntSystem, (∀ S ∈ Ss, ∃ v, S.firstValues = {v}) ∧
    IsGreatest {l : ℝ | ∃ S ∈ Ss, l ∈ S.firstValues} a

end Nieuwland
