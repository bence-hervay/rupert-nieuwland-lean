import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Modules.Root.System

/-!
# The chain rule for expressions

The formal derivative `deriv v e` (`Modules/Root/System.lean`) is the derivative of `e` along any
differentiable curve, by the chain rule: along `γ` the value of `e` has the derivative
`∑ u, (deriv u e)(γ t) * γ'ᵤ`, the sum over the variables of `e` (or any finite set of indices
that holds them). Along a coordinate line it is the partial derivative.

* `varsE`: the variables of an expression; `eval_deriv_of_not_mem`: the derivative in another
  variable is zero.
* `hasDerivAt_eval_comp`: the chain rule along a curve; `hasDerivAt_eval_line`: along the line
  `r ↦ z + r eᵥ`.
* `stat_of_pullback`: the stationarity transported by a curve, the core of a pose map's transport
  of a root's zero (`Modules/Root/Link.lean`).
-/

open Nieuwland.Check Finset

namespace Nieuwland.Root

/-- The variables of an expression. -/
def varsE : Expr → Finset ℕ
  | .const _ => ∅
  | .var i => {i}
  | .add a b => varsE a ∪ varsE b
  | .sub a b => varsE a ∪ varsE b
  | .mul a b => varsE a ∪ varsE b

/-- The derivative in a variable the expression does not use is zero. -/
theorem eval_deriv_of_not_mem {R : Type*} [CommRing R] (z : ℕ → R) {v : ℕ} :
    ∀ {e : Expr}, v ∉ varsE e → (deriv v e).eval z = 0
  | .const _, _ => by simp [deriv]
  | .var i, h => by
    have : i ≠ v := fun h' ↦ h (by simp [varsE, h'])
    simp [deriv, this]
  | .add a b, h => by
    simp only [varsE, Finset.mem_union, not_or] at h
    simp only [deriv]
    change (deriv v a).eval z + (deriv v b).eval z = 0
    rw [eval_deriv_of_not_mem z h.1, eval_deriv_of_not_mem z h.2, add_zero]
  | .sub a b, h => by
    simp only [varsE, Finset.mem_union, not_or] at h
    simp only [deriv]
    change (deriv v a).eval z - (deriv v b).eval z = 0
    rw [eval_deriv_of_not_mem z h.1, eval_deriv_of_not_mem z h.2, sub_zero]
  | .mul a b, h => by
    simp only [varsE, Finset.mem_union, not_or] at h
    simp only [deriv]
    change (deriv v a).eval z * b.eval z + a.eval z * (deriv v b).eval z = 0
    rw [eval_deriv_of_not_mem z h.1, eval_deriv_of_not_mem z h.2, zero_mul, mul_zero, add_zero]

/-- The value does not depend on the variables the expression does not use. -/
theorem eval_congr_vars {R : Type*} [CommRing R] {z w : ℕ → R} :
    ∀ {e : Expr}, (∀ u ∈ varsE e, z u = w u) → e.eval z = e.eval w
  | .const _, _ => rfl
  | .var i, h => h i (by simp [varsE])
  | .add a b, h => by
    change a.eval z + b.eval z = a.eval w + b.eval w
    rw [eval_congr_vars fun u hu ↦ h u (by simp [varsE, hu]),
      eval_congr_vars (e := b) fun u hu ↦ h u (by simp [varsE, hu])]
  | .sub a b, h => by
    change a.eval z - b.eval z = a.eval w - b.eval w
    rw [eval_congr_vars fun u hu ↦ h u (by simp [varsE, hu]),
      eval_congr_vars (e := b) fun u hu ↦ h u (by simp [varsE, hu])]
  | .mul a b, h => by
    change a.eval z * b.eval z = a.eval w * b.eval w
    rw [eval_congr_vars fun u hu ↦ h u (by simp [varsE, hu]),
      eval_congr_vars (e := b) fun u hu ↦ h u (by simp [varsE, hu])]

/-- **The chain rule** along a curve `γ` whose coordinates in `S ⊇ varsE e` have the
derivatives `γ'`. -/
theorem hasDerivAt_eval_comp {γ : ℝ → ℕ → ℝ} {γ' : ℕ → ℝ} {t : ℝ} {S : Finset ℕ}
    (h : ∀ u ∈ S, HasDerivAt (fun r ↦ γ r u) (γ' u) t) :
    ∀ {e : Expr}, varsE e ⊆ S →
      HasDerivAt (fun r ↦ e.eval (γ r)) (∑ u ∈ S, (deriv u e).eval (γ t) * γ' u) t
  | .const c, _ => by
    simpa [deriv] using hasDerivAt_const t ((c : ℤ) : ℝ)
  | .var i, hS => by
    have hi : i ∈ S := hS (by simp [varsE])
    have e : ∑ u ∈ S, (deriv u (.var i)).eval (γ t) * γ' u = γ' i := by
      rw [Finset.sum_eq_single_of_mem i hi]
      · simp [deriv]
      · intro u _ hu
        simp [deriv, Ne.symm hu]
    rw [e]
    exact h i hi
  | .add a b, hS => by
    have ha := hasDerivAt_eval_comp h (e := a) (fun u hu ↦ hS (by simp [varsE, hu]))
    have hb := hasDerivAt_eval_comp h (e := b) (fun u hu ↦ hS (by simp [varsE, hu]))
    have e : ∑ u ∈ S, (deriv u (.add a b)).eval (γ t) * γ' u =
        ∑ u ∈ S, (deriv u a).eval (γ t) * γ' u + ∑ u ∈ S, (deriv u b).eval (γ t) * γ' u := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      change ((deriv u a).eval (γ t) + (deriv u b).eval (γ t)) * γ' u = _
      ring
    rw [e]
    exact HasDerivAt.add ha hb
  | .sub a b, hS => by
    have ha := hasDerivAt_eval_comp h (e := a) (fun u hu ↦ hS (by simp [varsE, hu]))
    have hb := hasDerivAt_eval_comp h (e := b) (fun u hu ↦ hS (by simp [varsE, hu]))
    have e : ∑ u ∈ S, (deriv u (.sub a b)).eval (γ t) * γ' u =
        ∑ u ∈ S, (deriv u a).eval (γ t) * γ' u - ∑ u ∈ S, (deriv u b).eval (γ t) * γ' u := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      change ((deriv u a).eval (γ t) - (deriv u b).eval (γ t)) * γ' u = _
      ring
    rw [e]
    exact HasDerivAt.sub ha hb
  | .mul a b, hS => by
    have ha := hasDerivAt_eval_comp h (e := a) (fun u hu ↦ hS (by simp [varsE, hu]))
    have hb := hasDerivAt_eval_comp h (e := b) (fun u hu ↦ hS (by simp [varsE, hu]))
    have e : ∑ u ∈ S, (deriv u (.mul a b)).eval (γ t) * γ' u =
        (∑ u ∈ S, (deriv u a).eval (γ t) * γ' u) * b.eval (γ t) +
          a.eval (γ t) * ∑ u ∈ S, (deriv u b).eval (γ t) * γ' u := by
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      change ((deriv u a).eval (γ t) * b.eval (γ t) + a.eval (γ t) * (deriv u b).eval (γ t)) *
        γ' u = _
      ring
    rw [e]
    exact HasDerivAt.mul ha hb

/-- The line through `z` in the direction of the variable `v`. -/
def line (z : ℕ → ℝ) (v : ℕ) (r : ℝ) : ℕ → ℝ := Function.update z v (z v + r)

theorem line_zero (z : ℕ → ℝ) (v : ℕ) : line z v 0 = z := by
  simp [line]

theorem hasDerivAt_line (z : ℕ → ℝ) (v u : ℕ) :
    HasDerivAt (fun r ↦ line z v r u) (if u = v then 1 else 0) 0 := by
  by_cases h : u = v
  · subst h
    simpa [line] using HasDerivAt.const_add (z u) (hasDerivAt_id (0 : ℝ))
  · simpa [line, h] using hasDerivAt_const (0 : ℝ) (z u)

/-- **Along a coordinate line** the formal derivative is the derivative. -/
theorem hasDerivAt_eval_line (z : ℕ → ℝ) (v : ℕ) (e : Expr) :
    HasDerivAt (fun r ↦ e.eval (line z v r)) ((deriv v e).eval z) 0 := by
  have h := hasDerivAt_eval_comp (S := varsE e) (γ := line z v)
    (fun u _ ↦ hasDerivAt_line z v u) (e := e) subset_rfl
  rw [line_zero] at h
  convert h using 1
  by_cases hv : v ∈ varsE e
  · rw [Finset.sum_eq_single_of_mem v hv]
    · simp
    · intro u _ hu
      simp [hu]
  · rw [eval_deriv_of_not_mem z hv]
    refine (Finset.sum_eq_zero fun u hu ↦ ?_).symm
    have : u ≠ v := fun h' ↦ hv (h' ▸ hu)
    simp [this]

/-- **The stationarity transported by a curve.** At `z`, the multipliers `m` make the scale
`lA` stationary on the slacks `g i`: `∑ m_i ∂ᵤ g_i = [u = lA]` for every `u` where the curve
moves. A curve `γ` through `z` (`γ 0 = z`, derivatives `γ'` in the coordinates `S`, which hold
every slack's variables) pulls back the slacks `g' (σ i)` at `z'`, along the line of `v`, up to
differentiable factors (`g_i(γ r) = c_i r · g'_{σ i}(z' + r eᵥ)` near `0`), and `g'` vanish
at `z'`. Then the multipliers `c_i 0 · m_i` make `∂ᵥ` of the `g' (σ i)` the derivative of the
scale along the curve. -/
theorem stat_of_pullback {k : ℕ} {g g' : ℕ → Expr} {σ : ℕ → ℕ} {m : ℕ → ℝ} {lA : ℕ}
    {S : Finset ℕ} (hS : ∀ i < k, varsE (g i) ⊆ S) {z z' : ℕ → ℝ} {v : ℕ}
    {γ : ℝ → ℕ → ℝ} {γ' : ℕ → ℝ} (hγ0 : γ 0 = z)
    (hγ : ∀ u ∈ S, HasDerivAt (fun r ↦ γ r u) (γ' u) 0)
    (hstat : ∀ u ∈ S, γ' u * ∑ i ∈ range k, m i * (deriv u (g i)).eval z =
      γ' u * (if u = lA then 1 else 0))
    (hlA : lA ∈ S)
    {c : ℕ → ℝ → ℝ} {c' : ℕ → ℝ} (hc : ∀ i < k, HasDerivAt (c i) (c' i) 0)
    (hpull : ∀ i < k, ∀ᶠ r in nhds 0, (g i).eval (γ r) = c i r * (g' (σ i)).eval (line z' v r))
    (hzero : ∀ i < k, (g' (σ i)).eval z' = 0) :
    ∑ i ∈ range k, c i 0 * m i * (deriv v (g' (σ i))).eval z' = γ' lA := by
  have key : ∀ i < k, c i 0 * (deriv v (g' (σ i))).eval z' =
      ∑ u ∈ S, (deriv u (g i)).eval z * γ' u := by
    intro i hi
    have h1 := hasDerivAt_eval_comp hγ (e := g i) (hS i hi)
    rw [hγ0] at h1
    have h2 : HasDerivAt (fun r ↦ c i r * (g' (σ i)).eval (line z' v r))
        (c' i * (g' (σ i)).eval z' + c i 0 * (deriv v (g' (σ i))).eval z') 0 := by
      have := HasDerivAt.mul (hc i hi) (hasDerivAt_eval_line z' v (g' (σ i)))
      rw [line_zero] at this
      exact this
    rw [hzero i hi, mul_zero, zero_add] at h2
    exact (h2.congr_of_eventuallyEq (hpull i hi)).unique h1 |>.symm.symm
  have e1 : ∑ i ∈ range k, c i 0 * m i * (deriv v (g' (σ i))).eval z' =
      ∑ i ∈ range k, m i * ∑ u ∈ S, (deriv u (g i)).eval z * γ' u := by
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [← key i (mem_range.mp hi)]
    ring
  rw [e1]
  have e2 : ∑ i ∈ range k, m i * ∑ u ∈ S, (deriv u (g i)).eval z * γ' u =
      ∑ u ∈ S, γ' u * ∑ i ∈ range k, m i * (deriv u (g i)).eval z := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  rw [e2, Finset.sum_congr rfl hstat, Finset.sum_eq_single_of_mem lA hlA]
  · simp
  · intro u _ hu
    simp [hu]

end Nieuwland.Root
