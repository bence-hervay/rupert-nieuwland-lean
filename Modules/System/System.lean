import Definitions.Polynomials
import Mathlib.Order.Bounds.Defs
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Polynomial systems with boxes: the form of an exact Nieuwland number

An exact Nieuwland number is stated as **the largest scale among the solutions of fixed systems
of rational polynomial equations inside fixed rational boxes** (Bence Hervay, 2026-11-15). The
systems and the boxes are data written out in the statement; the number can be computed from them
alone, to any precision, without the geometry and without the proof that it is the optimum.

Everything a reader has to know is in this file:

* `Nieuwland.RationalPolynomial`: a polynomial in the variables `x 0, x 1, …` with rational coefficients, a
  list of terms `(c, [(i, e), (j, f), …])` for `c * x i ^ e * x j ^ f * ⋯`;
* `Nieuwland.RationalPolynomial.eval p x`: its value at the real point `x`;
* `Nieuwland.PolynomialSystem`: equations `p = q`, each a pair `(p, q)` of polynomials, and a box, one
  closed rational interval for each of the variables `x 0, x 1, …` in turn (variables past the
  box are unconstrained);
* `Nieuwland.PolynomialSystem.Solves S x`: `x` lies in the box of `S` and every equation of `S` holds;
* `Nieuwland.PolynomialSystem.scales Ss`: the values of `x 0`, **the scale**, at the solutions of the
  systems `Ss`.

The theorem of a solid `P` is `IsGreatest (PolynomialSystem.scales Ss) P.nieuwland`: the Nieuwland
number is the scale of a solution of one of the systems, and no solution of any of them has a
larger scale. (`IsGreatest s a` is Mathlib's `a ∈ s ∧ ∀ b ∈ s, b ≤ a`.)

Variable `0` is always the scale. A system has no more variables than it needs: the scale alone
when the number has a polynomial of its own; otherwise the unknowns of the optimum's contact
equations (the pose, the translation, the scale and the multipliers), a generator of the solid's
number field and the coordinates of the vertices in contact. The generated systems have positive
coefficients on both sides of every equation (a term with a negative coefficient moves to the
other side). A certificate has one system for every optimal pose that its enclosures cannot tell
apart from the optimum.
-/

namespace Nieuwland

namespace PolynomialSystem

/-- The scales of the systems `Ss`: the values of `x 0` at the solutions of any of them. -/
def scales (Ss : List PolynomialSystem) : Set ℝ :=
  {l | ∃ S ∈ Ss, ∃ x : ℕ → ℝ, S.Solves x ∧ x 0 = l}

end PolynomialSystem

end Nieuwland
