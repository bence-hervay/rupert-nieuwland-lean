import Definitions.Polynomials
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Data.List.GetD

/-!
# Real roots of rational polynomials

A body over a number field `ℚ(θ)` is given by a rational polynomial `p` and an interval
`(lo, hi)` isolating the real root `θ` (`FieldSpec::NumberField` in `code/src/math/scalar.rs`);
its coordinates are rational polynomials in `θ`. `realRoot p lo hi` is the largest root of `p` in
`(lo, hi)`, the supremum of the roots there: `θ` when the interval isolates it, and a definite
real number in any case. Checks enclose it and prove that it is a root
(`Modules/Check/Number/Theta.lean`).

The definitions `Nieuwland.polyEval` and `Nieuwland.realRoot` are in `Definitions/Polynomials.lean`.
-/

namespace Nieuwland

theorem continuous_polyEval (p : List ℚ) : Continuous (polyEval p) :=
  continuous_finsetSum _ fun i _ ↦ continuous_const.mul (continuous_pow i)

/-- If some root of `p` in `(lo, hi)` is at least `a` and every one is at most `b`, the largest
root is a root in `[a, b]`. -/
theorem realRoot_mem {p : List ℚ} {lo hi : ℚ} {a b : ℝ}
    (ha : ∃ x, (lo : ℝ) < x ∧ x < hi ∧ polyEval p x = 0 ∧ a ≤ x)
    (hb : ∀ x, (lo : ℝ) < x → x < hi → polyEval p x = 0 → x ≤ b) :
    a ≤ realRoot p lo hi ∧ realRoot p lo hi ≤ b ∧ polyEval p (realRoot p lo hi) = 0 := by
  obtain ⟨x, h₁, h₂, h₃, h₄⟩ := ha
  set S := {x : ℝ | (lo : ℝ) < x ∧ x < hi ∧ polyEval p x = 0}
  have hne : S.Nonempty := ⟨x, h₁, h₂, h₃⟩
  have hbdd : BddAbove S := ⟨b, fun y hy ↦ hb y hy.1 hy.2.1 hy.2.2⟩
  have hcl : closure S ⊆ {x | polyEval p x = 0} :=
    closure_minimal (fun y hy ↦ hy.2.2) (isClosed_eq (continuous_polyEval p) continuous_const)
  exact ⟨h₄.trans (le_csSup hbdd ⟨h₁, h₂, h₃⟩),
    csSup_le hne fun y hy ↦ hb y hy.1 hy.2.1 hy.2.2, hcl (csSup_mem_closure hne hbdd)⟩

end Nieuwland
