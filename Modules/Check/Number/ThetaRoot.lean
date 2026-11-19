import Modules.Check.Number.Theta

/-!
# The root of a number field: what a reader is told

For the data `R : Root` of `θ = realRoot m lo hi` (`Modules/Check/Number/Theta.lean`), `α = c θ`
is a root of the monic integer polynomial `N`, enclosed in `[Xl/D, Xh/D]` (`Root.spec`). Here
the same is said of `θ` itself, with the polynomial `m` of its definition: `θ` is a root of `m`
(`Root.polyEval_theta`), and it lies between the rationals `a` and `b` whenever
`[Xl/D, Xh/D] ⊆ c [a, b]` (`Root.theta_isRoot`, a comparison of rationals). A solid over `ℚ(θ)`
states this in its `Result.lean`.

The certificates' pieces do not import this module.
-/

open Finset

namespace Nieuwland.Check.Root

variable (R : Root)

/-- `N (c x) mₙ = cⁿ m(x)`, for the leading coefficient `mₙ` of `m`. -/
theorem evalZ_mul_lead (x : ℝ) :
    evalZ R.N (R.c * x) * (R.m.getD R.n 0 : ℝ) = (R.c : ℝ) ^ R.n * polyEval R.m x := by
  have h := R.coef
  simp only [coefCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨-, hlen⟩, -⟩, -⟩, -⟩, hcoef⟩ := h
  have hn : R.N.length - 1 = R.n := rfl
  rw [hn] at hcoef
  rw [evalZ, polyEval, sum_mul, mul_sum, hlen]
  refine sum_congr rfl fun i hi ↦ ?_
  have hi' : i ≤ R.n := by have := mem_range.mp hi; rw [R.length_N] at this; omega
  have hr : (R.N.getD i 0 : ℝ) * (R.m.getD R.n 0 : ℝ) =
      (R.m.getD i 0 : ℝ) * (R.c : ℝ) ^ (R.n - i) := by
    exact_mod_cast hcoef i (mem_range.mp hi)
  calc (R.N.getD i 0 : ℝ) * (R.c * x) ^ i * R.m.getD R.n 0
      = ((R.N.getD i 0 : ℝ) * R.m.getD R.n 0) * R.c ^ i * x ^ i := by ring
    _ = R.m.getD i 0 * (R.c ^ (R.n - i) * R.c ^ i) * x ^ i := by rw [hr]; ring
    _ = _ := by rw [pow_sub_mul_pow _ hi']; ring

/-- The scale `c` is positive (as a real). -/
theorem cast_c_pos : (0 : ℝ) < R.c := by
  have h := R.coef
  simp only [coefCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact_mod_cast h.1.2

/-- `θ = realRoot m lo hi` is a root of `m`. -/
theorem polyEval_theta : polyEval R.m (realRoot R.m R.lo R.hi) = 0 := by
  have h := R.evalZ_mul_lead (realRoot R.m R.lo R.hi)
  have h0 : evalZ R.N (R.c * realRoot R.m R.lo R.hi) = 0 := R.spec.2.2
  rw [h0, zero_mul] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ R.cast_c_pos.ne')

/-- **`θ = realRoot m lo hi` is a root of `m` in `[a, b]`**, for rationals `a`, `b` with
`[Xl/D, Xh/D] ⊆ c [a, b]`. -/
theorem theta_isRoot {a b : ℚ}
    (h : decide (a * R.c * R.D ≤ R.Xl ∧ (R.Xh : ℚ) ≤ b * R.c * R.D) = true) :
    polyEval R.m (realRoot R.m R.lo R.hi) = 0 ∧
      (a : ℝ) ≤ realRoot R.m R.lo R.hi ∧ realRoot R.m R.lo R.hi ≤ (b : ℝ) := by
  obtain ⟨ha, hb⟩ := of_decide_eq_true h
  have ha' : (a : ℝ) * R.c * R.D ≤ R.Xl := by exact_mod_cast ha
  have hb' : (R.Xh : ℝ) ≤ b * R.c * R.D := by exact_mod_cast hb
  obtain ⟨hl, hh, -⟩ := R.spec
  have hD : (0 : ℝ) < R.D := by exact_mod_cast R.D_pos
  have hα : R.α = R.c * realRoot R.m R.lo R.hi := rfl
  rw [hα, div_le_iff₀ hD] at hl
  rw [hα, le_div_iff₀ hD] at hh
  have hcD : (0 : ℝ) < R.c * R.D := mul_pos R.cast_c_pos hD
  refine ⟨R.polyEval_theta, ?_, ?_⟩
  · refine le_of_mul_le_mul_right ?_ hcD
    linarith
  · refine le_of_mul_le_mul_right ?_ hcD
    linarith

end Nieuwland.Check.Root
