import Modules.Root.Aff

/-!
# Second-order expansions of polynomial expressions, in enclosures

For a polynomial `e`, a point `a` and a displacement `d` of the first `n` variables (the others
are fixed), `e(a + d) = e(a) + ∑ γ_k d_k + ∑ μ_jk d_j d_k`, where `γ_k` is the value at `a` of the
formal derivative (`deriv`, `Modules/Root/System.lean`) and the `μ_jk` are polynomials in `a` and
`d`. `second` computes enclosures (`Enc`: balls, or affine forms, `Modules/Root/Aff.lean`) of
`e(a)`, `e(a + d)`, the `γ_k`, first-order slopes `σ_k` (`e(a + d) - e(a) = ∑ σ_k d_k`) and the
`μ_jk`, from enclosures of the coordinates of `a` and of `a + d`, by the product rules
`γ(fg) = γ(f) g(a) + f(a) γ(g)`, `σ(fg) = σ(f) g(a + d) + f(a) σ(g)` and
`μ(fg)_jk = f(a + d) μ(g)_jk + σ(f)_j γ(g)_k + g(a) μ(f)_jk`.
`second_holds` is its soundness: an identity of polynomials, no derivative and no Taylor theorem.

The touch leaf (`Modules/Root/Leaf.lean`) uses it at the zero of a root's system, where the value
and the first-order term of its function vanish: what remains is the quadratic form of the `μ`.
-/

open Nieuwland.Check Finset

namespace Nieuwland.Root

/-- Enclosures of a second-order expansion (module docs). -/
structure TBall (R : Type) where
  /-- The value at `a`. -/
  va : R
  /-- The value at `a + d`. -/
  vd : R
  /-- The formal gradient at `a`. -/
  gr : List R
  /-- The slopes between `a` and `a + d`. -/
  sl : List R
  /-- The second-order coefficients, row by row. -/
  M : List R

namespace TBall

variable {R : Type} [Enc R]

/-- The derivative in the variable `k`. -/
def g (t : TBall R) (k : ℕ) : R := t.gr.getD k (Enc.ofInt 0)

/-- The slope in the variable `k`. -/
def s (t : TBall R) (k : ℕ) : R := t.sl.getD k (Enc.ofInt 0)

/-- The second-order coefficient of `d_j d_k`. -/
def m (t : TBall R) (n j k : ℕ) : R := t.M.getD (j * n + k) (Enc.ofInt 0)

/-- The enclosures from functions of the indices. -/
def mk' (n : ℕ) (va vd : R) (fg fs : ℕ → R) (fm : ℕ → ℕ → R) : TBall R :=
  ⟨va, vd, (List.range n).map fg, (List.range n).map fs,
    (List.range (n * n)).map fun i ↦ fm (i / n) (i % n)⟩

variable {n : ℕ} {va vd : R} {fg fs : ℕ → R} {fm : ℕ → ℕ → R}

theorem g_mk' {k : ℕ} (hk : k < n) : (mk' n va vd fg fs fm).g k = fg k := by
  simp [g, mk', List.getD, hk]

theorem s_mk' {k : ℕ} (hk : k < n) : (mk' n va vd fg fs fm).s k = fs k := by
  simp [s, mk', List.getD, hk]

theorem m_mk' {j k : ℕ} (hj : j < n) (hk : k < n) : (mk' n va vd fg fs fm).m n j k = fm j k := by
  have h1 : j * n + k < n * n := by
    calc j * n + k < j * n + n := by omega
      _ = (j + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right n hj
  have h2 : (j * n + k) / n = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hk, Nat.zero_add]
  have h3 : (j * n + k) % n = k := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  simp [m, mk', List.getD, h1, h2, h3]

/-- `t` holds, under the enclosure relation `E`, the values `pa`, `py`, the gradient `γ`, slopes
and second-order coefficients against the displacement `d`. -/
structure Holds (E : R → ℝ → Prop) (n : ℕ) (t : TBall R) (d : ℕ → ℝ) (pa py : ℝ) (γ : ℕ → ℝ) :
    Prop where
  va : E t.va pa
  vd : E t.vd py
  gr : ∀ k < n, E (t.g k) (γ k)
  sl : ∃ σ : ℕ → ℝ, (∀ k < n, E (t.s k) (σ k)) ∧ py - pa = ∑ k ∈ range n, σ k * d k
  mat : ∃ μ : ℕ → ℕ → ℝ, (∀ j < n, ∀ k < n, E (t.m n j k) (μ j k)) ∧
    py = pa + ∑ k ∈ range n, γ k * d k + ∑ j ∈ range n, ∑ k ∈ range n, μ j k * d j * d k

end TBall

variable {R : Type} [Enc R]

/-- The enclosures of the second-order expansion of an expression: `A` the enclosures of the
coordinates of `a`, `Z` those of `a + d` (for the variables from `n` on: of `a`). -/
def second (n : ℕ) (A Z : ℕ → R) : Expr → TBall R
  | .const c =>
    TBall.mk' n (Enc.ofInt c) (Enc.ofInt c) (fun _ ↦ Enc.ofInt 0) (fun _ ↦ Enc.ofInt 0)
      fun _ _ ↦ Enc.ofInt 0
  | .var i =>
    TBall.mk' n (A i) (Z i) (fun k ↦ Enc.ofInt (if i = k then 1 else 0))
      (fun k ↦ Enc.ofInt (if i = k then 1 else 0)) fun _ _ ↦ Enc.ofInt 0
  | .add a b =>
    let (x, w) := (second n A Z a, second n A Z b)
    TBall.mk' n (x.va + w.va) (x.vd + w.vd) (fun k ↦ x.g k + w.g k) (fun k ↦ x.s k + w.s k)
      fun j k ↦ x.m n j k + w.m n j k
  | .sub a b =>
    let (x, w) := (second n A Z a, second n A Z b)
    TBall.mk' n (x.va - w.va) (x.vd - w.vd) (fun k ↦ x.g k - w.g k) (fun k ↦ x.s k - w.s k)
      fun j k ↦ x.m n j k - w.m n j k
  | .mul a b =>
    let (x, w) := (second n A Z a, second n A Z b)
    TBall.mk' n (x.va * w.va) (x.vd * w.vd) (fun k ↦ x.g k * w.va + x.va * w.g k)
      (fun k ↦ x.s k * w.vd + x.va * w.s k)
      fun j k ↦ x.vd * w.m n j k + x.s j * w.g k + w.va * x.m n j k

/-- Soundness of `second` (module docs). -/
theorem second_holds {E : R → ℝ → Prop} (hE : Enc.Sound E) {n : ℕ} {A Z : ℕ → R}
    {a y : ℕ → ℝ} (hA : ∀ i, E (A i) (a i)) (hZ : ∀ i, E (Z i) (y i))
    (hfix : ∀ i, n ≤ i → y i = a i) (e : Expr) :
    (second n A Z e).Holds E n (fun k ↦ y k - a k) (e.eval a) (e.eval y)
      (fun k ↦ (deriv k e).eval a) := by
  induction e with
  | const c =>
    refine ⟨hE.ofInt c, hE.ofInt c, fun k hk ↦ ?_, ⟨fun _ ↦ 0, fun k hk ↦ ?_, ?_⟩,
      ⟨fun _ _ ↦ 0, fun j hj k hk ↦ ?_, ?_⟩⟩
    · rw [second, TBall.g_mk' hk]
      simpa [deriv] using hE.ofInt 0
    · rw [second, TBall.s_mk' hk]
      simpa using hE.ofInt 0
    · simp [Expr.eval]
    · rw [second, TBall.m_mk' hj hk]
      simpa using hE.ofInt 0
    · simp [deriv, Expr.eval]
  | var i =>
    have hsum : y i - a i = ∑ k ∈ range n, (if i = k then (1 : ℝ) else 0) * (y k - a k) := by
      simp only [ite_mul, one_mul, zero_mul, sum_ite_eq, mem_range]
      split_ifs with hi
      · rfl
      · rw [hfix i (not_lt.mp hi), sub_self]
    have hite : ∀ k, E (Enc.ofInt (if i = k then 1 else 0)) (if i = k then (1 : ℝ) else 0) :=
      fun k ↦ by
        by_cases h : i = k
        · simpa [h] using hE.ofInt 1
        · simpa [h] using hE.ofInt 0
    have hd : ∀ k, (deriv k (.var i)).eval a = if i = k then (1 : ℝ) else 0 := fun k ↦ by
      by_cases h : i = k <;> simp [deriv, h]
    refine ⟨hA i, hZ i, fun k hk ↦ ?_, ⟨fun k ↦ if i = k then 1 else 0, fun k hk ↦ ?_, hsum⟩,
      ⟨fun _ _ ↦ 0, fun j hj k hk ↦ ?_, ?_⟩⟩
    · rw [second, TBall.g_mk' hk, hd]
      exact hite k
    · rw [second, TBall.s_mk' hk]
      exact hite k
    · rw [second, TBall.m_mk' hj hk]
      simpa using hE.ofInt 0
    · simp only [hd, zero_mul, sum_const_zero, add_zero]
      change y i = a i + _
      linarith
  | add f g ihf ihg =>
    obtain ⟨hfa, hfy, hgf, ⟨σf, hσf, hsf⟩, ⟨μf, hμf, hmf⟩⟩ := ihf
    obtain ⟨hga, hgy, hgg, ⟨σg, hσg, hsg⟩, ⟨μg, hμg, hmg⟩⟩ := ihg
    refine ⟨hE.add hfa hga, hE.add hfy hgy, fun k hk ↦ ?_,
      ⟨fun k ↦ σf k + σg k, fun k hk ↦ ?_, ?_⟩,
      ⟨fun j k ↦ μf j k + μg j k, fun j hj k hk ↦ ?_, ?_⟩⟩
    · rw [second, TBall.g_mk' hk]
      exact hE.add (hgf k hk) (hgg k hk)
    · rw [second, TBall.s_mk' hk]
      exact hE.add (hσf k hk) (hσg k hk)
    · beta_reduce at hsf hsg ⊢
      simp only [Expr.eval, add_mul, sum_add_distrib, ← hsf, ← hsg]
      ring
    · rw [second, TBall.m_mk' hj hk]
      exact hE.add (hμf j hj k hk) (hμg j hj k hk)
    · beta_reduce at hmf hmg ⊢
      simp only [deriv, Expr.eval, add_mul, sum_add_distrib]
      linarith
  | sub f g ihf ihg =>
    obtain ⟨hfa, hfy, hgf, ⟨σf, hσf, hsf⟩, ⟨μf, hμf, hmf⟩⟩ := ihf
    obtain ⟨hga, hgy, hgg, ⟨σg, hσg, hsg⟩, ⟨μg, hμg, hmg⟩⟩ := ihg
    refine ⟨hE.sub hfa hga, hE.sub hfy hgy, fun k hk ↦ ?_,
      ⟨fun k ↦ σf k - σg k, fun k hk ↦ ?_, ?_⟩,
      ⟨fun j k ↦ μf j k - μg j k, fun j hj k hk ↦ ?_, ?_⟩⟩
    · rw [second, TBall.g_mk' hk]
      exact hE.sub (hgf k hk) (hgg k hk)
    · rw [second, TBall.s_mk' hk]
      exact hE.sub (hσf k hk) (hσg k hk)
    · beta_reduce at hsf hsg ⊢
      simp only [Expr.eval, sub_mul, sum_sub_distrib, ← hsf, ← hsg]
      ring
    · rw [second, TBall.m_mk' hj hk]
      exact hE.sub (hμf j hj k hk) (hμg j hj k hk)
    · beta_reduce at hmf hmg ⊢
      simp only [deriv, Expr.eval, sub_mul, sum_sub_distrib]
      linarith
  | mul f g ihf ihg =>
    obtain ⟨hfa, hfy, hgf, ⟨σf, hσf, hsf⟩, ⟨μf, hμf, hmf⟩⟩ := ihf
    obtain ⟨hga, hgy, hgg, ⟨σg, hσg, hsg⟩, ⟨μg, hμg, hmg⟩⟩ := ihg
    refine ⟨hE.mul hfa hga, hE.mul hfy hgy, fun k hk ↦ ?_,
      ⟨fun k ↦ σf k * g.eval y + f.eval a * σg k, fun k hk ↦ ?_, ?_⟩,
      ⟨fun j k ↦ f.eval y * μg j k + σf j * (deriv k g).eval a + g.eval a * μf j k,
        fun j hj k hk ↦ ?_, ?_⟩⟩
    · rw [second, TBall.g_mk' hk]
      exact hE.add (hE.mul (hgf k hk) hga) (hE.mul hfa (hgg k hk))
    · rw [second, TBall.s_mk' hk]
      exact hE.add (hE.mul (hσf k hk) hgy) (hE.mul hfa (hσg k hk))
    · beta_reduce at hsf hsg ⊢
      have h1 : ∑ k ∈ range n, (σf k * g.eval y + f.eval a * σg k) * (y k - a k) =
          (∑ k ∈ range n, σf k * (y k - a k)) * g.eval y +
            f.eval a * ∑ k ∈ range n, σg k * (y k - a k) := by
        rw [sum_mul, mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun k _ ↦ by ring
      rw [h1, ← hsf, ← hsg]
      simp only [Expr.eval]
      ring
    · rw [second, TBall.m_mk' hj hk]
      exact hE.add (hE.add (hE.mul hfy (hμg j hj k hk))
        (hE.mul (hσf j hj) (hgg k hk))) (hE.mul hga (hμf j hj k hk))
    · beta_reduce at hsf hmf hmg ⊢
      have e0 : ∀ k, (deriv k (.mul f g)).eval a =
          (deriv k f).eval a * g.eval a + f.eval a * (deriv k g).eval a := fun _ ↦ rfl
      have h1 : ∑ k ∈ range n, ((deriv k f).eval a * g.eval a + f.eval a * (deriv k g).eval a) *
            (y k - a k) =
          g.eval a * (∑ k ∈ range n, (deriv k f).eval a * (y k - a k)) +
            f.eval a * ∑ k ∈ range n, (deriv k g).eval a * (y k - a k) := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun k _ ↦ by ring
      have e1 : ∑ j ∈ range n, ∑ k ∈ range n, f.eval y * (μg j k * (y j - a j) * (y k - a k)) =
          f.eval y * ∑ j ∈ range n, ∑ k ∈ range n, μg j k * (y j - a j) * (y k - a k) := by
        simp only [mul_sum]
      have e2 : ∑ j ∈ range n, ∑ k ∈ range n,
            σf j * (y j - a j) * ((deriv k g).eval a * (y k - a k)) =
          (∑ j ∈ range n, σf j * (y j - a j)) *
            ∑ k ∈ range n, (deriv k g).eval a * (y k - a k) := by
        rw [sum_mul_sum]
      have e3 : ∑ j ∈ range n, ∑ k ∈ range n, g.eval a * (μf j k * (y j - a j) * (y k - a k)) =
          g.eval a * ∑ j ∈ range n, ∑ k ∈ range n, μf j k * (y j - a j) * (y k - a k) := by
        simp only [mul_sum]
      have e4 : ∀ j k, (f.eval y * μg j k + σf j * (deriv k g).eval a + g.eval a * μf j k) *
            (y j - a j) * (y k - a k) =
          f.eval y * (μg j k * (y j - a j) * (y k - a k)) +
            σf j * (y j - a j) * ((deriv k g).eval a * (y k - a k)) +
            g.eval a * (μf j k * (y j - a j) * (y k - a k)) := fun j k ↦ by ring
      simp only [e0, h1, e4, sum_add_distrib, e1, e2, e3]
      change f.eval y * g.eval y = f.eval a * g.eval a + _ + _
      linear_combination f.eval y * hmg + g.eval a * hmf +
        (∑ k ∈ range n, (deriv k g).eval a * (y k - a k)) * hsf

end Nieuwland.Root
