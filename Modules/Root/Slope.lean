import Modules.Check.Number.Ball
import Modules.Check.Polynomial.Expr

/-!
# Slopes of polynomial expressions, in balls

For a polynomial `e` in the unknowns `0, …, n - 1` (the other variables are parameters) and two
points `y`, `y'` that agree on the parameters,
`e(y) - e(y') = ∑_{k < n} σ_k (y_k - y'_k)` for slopes `σ_k` that are polynomials in `y` and `y'`.
`Expr.slope` computes balls for `e(y)`, `e(y')` and the `σ_k` from balls for the coordinates of
`y` and `y'`, by the product rule `p q - p' q' = (p - p') q + p' (q - q')`: no derivative and no
mean value theorem. `Expr.slope_holds` is its soundness.

These are the enclosures that Krawczyk's test needs (`Modules/Root/Krawczyk.lean`): with `y'` the
centre of a box they bound the image of the box, and with both points in the box they bound the
contraction factor.
-/

open Nieuwland.Check

namespace Nieuwland.Root

/-- Balls for the values of an expression at two points and for its slopes between them. -/
structure SBall where
  /-- The value at `y`. -/
  v : Ball
  /-- The value at `y'`. -/
  v' : Ball
  /-- The slopes in the unknowns. -/
  s : List Ball

namespace SBall

/-- The slope in the unknown `k`. -/
def sl (a : SBall) (k : ℕ) : Ball := a.s.getD k (Ball.ofInt 0)

/-- Values and the slopes `f 0, …, f (n - 1)`. -/
def mk' (n : ℕ) (v v' : Ball) (f : ℕ → Ball) : SBall := ⟨v, v', (List.range n).map f⟩

theorem sl_mk' {n k : ℕ} (hk : k < n) (v v' : Ball) (f : ℕ → Ball) : (mk' n v v' f).sl k = f k := by
  simp [sl, mk', List.getD, hk]

/-- `a` holds the values `p`, `p'` with slopes against the differences `δ`. -/
def Holds (n : ℕ) (a : SBall) (δ : ℕ → ℝ) (p p' : ℝ) : Prop :=
  a.v.Encl p ∧ a.v'.Encl p' ∧
    ∃ σ : ℕ → ℝ, (∀ k < n, (a.sl k).Encl (σ k)) ∧ p - p' = ∑ k ∈ Finset.range n, σ k * δ k

end SBall

/-- The balls of an expression's values at two points (`Y`, `Y'`: balls of their coordinates) and
of its slopes in the unknowns `0, …, n - 1`. -/
def slope (n : ℕ) (Y Y' : ℕ → Ball) : Expr → SBall
  | .const c => SBall.mk' n (Ball.ofInt c) (Ball.ofInt c) fun _ ↦ Ball.ofInt 0
  | .var i => SBall.mk' n (Y i) (Y' i) fun k ↦ Ball.ofInt (if k = i then 1 else 0)
  | .add a b =>
    let (x, z) := (slope n Y Y' a, slope n Y Y' b)
    SBall.mk' n (x.v + z.v) (x.v' + z.v') fun k ↦ x.sl k + z.sl k
  | .sub a b =>
    let (x, z) := (slope n Y Y' a, slope n Y Y' b)
    SBall.mk' n (x.v - z.v) (x.v' - z.v') fun k ↦ x.sl k - z.sl k
  | .mul a b =>
    let (x, z) := (slope n Y Y' a, slope n Y Y' b)
    SBall.mk' n (x.v * z.v) (x.v' * z.v') fun k ↦ x.sl k * z.v + x.v' * z.sl k

/-- Soundness of `slope`: at points `y`, `y'` in the balls that agree on the parameters, the
balls hold the two values and slopes `σ` with `e(y) - e(y') = ∑_{k < n} σ_k (y_k - y'_k)`. -/
theorem slope_holds {n : ℕ} {Y Y' : ℕ → Ball} {y y' : ℕ → ℝ} (hY : ∀ i, (Y i).Encl (y i))
    (hY' : ∀ i, (Y' i).Encl (y' i)) (hpar : ∀ i, n ≤ i → y i = y' i) (e : Expr) :
    (slope n Y Y' e).Holds n (fun k ↦ y k - y' k) (e.eval y) (e.eval y') := by
  induction e with
  | const c =>
    refine ⟨Ball.encl_ofInt c, Ball.encl_ofInt c, fun _ ↦ 0, fun k hk ↦ ?_, by simp [Expr.eval]⟩
    rw [slope, SBall.sl_mk' hk]
    simpa using Ball.encl_ofInt 0
  | var i =>
    refine ⟨hY i, hY' i, fun k ↦ if k = i then 1 else 0, fun k hk ↦ ?_, ?_⟩
    · rw [slope, SBall.sl_mk' hk]
      by_cases h : k = i
      · simpa [h] using Ball.encl_ofInt 1
      · simpa [h] using Ball.encl_ofInt 0
    · simp only [Expr.eval, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range]
      split_ifs with hi
      · rfl
      · rw [hpar i (not_lt.mp hi), sub_self]
  | add a b iha ihb =>
    obtain ⟨ha, ha', σ, hσ, hs⟩ := iha
    obtain ⟨hb, hb', τ, hτ, ht⟩ := ihb
    refine ⟨Ball.encl_add ha hb, Ball.encl_add ha' hb', fun k ↦ σ k + τ k, fun k hk ↦ ?_, ?_⟩
    · rw [slope, SBall.sl_mk' hk]
      exact Ball.encl_add (hσ k hk) (hτ k hk)
    · beta_reduce at hs ht ⊢
      simp only [Expr.eval, add_mul, Finset.sum_add_distrib, ← hs, ← ht]
      ring
  | sub a b iha ihb =>
    obtain ⟨ha, ha', σ, hσ, hs⟩ := iha
    obtain ⟨hb, hb', τ, hτ, ht⟩ := ihb
    refine ⟨Ball.encl_sub ha hb, Ball.encl_sub ha' hb', fun k ↦ σ k - τ k, fun k hk ↦ ?_, ?_⟩
    · rw [slope, SBall.sl_mk' hk]
      exact Ball.encl_sub (hσ k hk) (hτ k hk)
    · beta_reduce at hs ht ⊢
      simp only [Expr.eval, sub_mul, Finset.sum_sub_distrib, ← hs, ← ht]
      ring
  | mul a b iha ihb =>
    obtain ⟨ha, ha', σ, hσ, hs⟩ := iha
    obtain ⟨hb, hb', τ, hτ, ht⟩ := ihb
    refine ⟨Ball.encl_mul ha hb, Ball.encl_mul ha' hb',
      fun k ↦ σ k * b.eval y + a.eval y' * τ k, fun k hk ↦ ?_, ?_⟩
    · rw [slope, SBall.sl_mk' hk]
      exact Ball.encl_add (Ball.encl_mul (hσ k hk) hb) (Ball.encl_mul ha' (hτ k hk))
    · beta_reduce at hs ht ⊢
      have h1 : ∑ k ∈ Finset.range n, (σ k * b.eval y + a.eval y' * τ k) * (y k - y' k) =
          (∑ k ∈ Finset.range n, σ k * (y k - y' k)) * b.eval y +
            a.eval y' * ∑ k ∈ Finset.range n, τ k * (y k - y' k) := by
        rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ ↦ by ring
      rw [h1, ← hs, ← ht]
      simp only [Expr.eval]
      ring

end Nieuwland.Root
