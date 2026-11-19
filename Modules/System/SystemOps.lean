import Modules.System.System
import Modules.Check.Polynomial.Expr
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Arithmetic of the systems' polynomials

Operations on `RationalPolynomial` (`Modules/System/System.lean`) with their values: sums, negation,
products, univariate polynomials and the expansion of an `Expr` (`Modules/Check/Polynomial/Expr.lean`) with
its variables replaced by polynomials. None of this is part of what a statement means; the proofs
that a written-out system is the system of a certificate use it.

**The canonical form.** A polynomial is canonical when its terms have nonzero coefficients,
powers sorted by their variables with positive exponents, and strictly increasing monomials in
the lexicographic order (`monoLt`). Sums (`add`, a merge) and products (`mul`, merges of the products
by single terms, an order-preserving operation) of canonical polynomials are canonical, so every
polynomial computed from constants and variables is the unique canonical form of its value: the
written-out systems are that form (computed by `code/lean-export`), and a check compares them by
`decide`. Only the values (`eval_add`, `eval_mul`, `eval_ofExpr`) matter for soundness; the order
matters only for the comparison to succeed. All recursion is structural, so the kernel evaluates
it.

## Main statements

* `Nieuwland.RationalPolynomial.eval_add`, `eval_mul`, `eval_ofUni`: the values of sums, products and
  univariate polynomials.
* `Nieuwland.RationalPolynomial.eval_ofExpr`: the expansion of an expression has the expression's value.
-/

namespace Nieuwland

namespace RationalPolynomial

/-! ### Monomials -/

theorem monomial_nil (x : ℕ → ℝ) : monomial x [] = 1 := by simp [monomial]

theorem monomial_cons (x : ℕ → ℝ) (v : ℕ × ℕ) (m : List (ℕ × ℕ)) :
    monomial x (v :: m) = x v.1 ^ v.2 * monomial x m := by simp [monomial]

/-- The product of two monomials: the merge of their powers, those of the same variable
added. -/
def monoMul : List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ)
  | [], b => b
  | a :: as, b => mulAux a as (monoMul as) b
where
  /-- The merge of `a :: as` into a list, `rec` multiplying by `as`. -/
  mulAux (a : ℕ × ℕ) (as : List (ℕ × ℕ)) (rec : List (ℕ × ℕ) → List (ℕ × ℕ)) :
      List (ℕ × ℕ) → List (ℕ × ℕ)
    | [] => a :: as
    | b :: bs =>
      if a.1 = b.1 then (a.1, a.2 + b.2) :: rec bs
      else if a.1 < b.1 then a :: rec (b :: bs)
      else b :: mulAux a as rec bs

theorem monomial_mulAux (a : ℕ × ℕ) (as : List (ℕ × ℕ)) (rec : List (ℕ × ℕ) → List (ℕ × ℕ))
    (x : ℕ → ℝ) (hrec : ∀ r, monomial x (rec r) = monomial x as * monomial x r) :
    ∀ b, monomial x (monoMul.mulAux a as rec b) = monomial x (a :: as) * monomial x b
  | [] => by simp [monoMul.mulAux, monomial_nil]
  | b :: bs => by
    have ih := monomial_mulAux a as rec x hrec bs
    simp only [monoMul.mulAux]
    by_cases h1 : a.1 = b.1
    · simp only [h1, ↓reduceIte, monomial_cons, hrec, pow_add]
      ring
    · by_cases h2 : a.1 < b.1
      · simp only [h1, h2, ↓reduceIte, monomial_cons, hrec]
        ring
      · simp only [h1, h2, ↓reduceIte, monomial_cons, ih]
        ring

theorem monomial_monoMul (a b : List (ℕ × ℕ)) (x : ℕ → ℝ) :
    monomial x (monoMul a b) = monomial x a * monomial x b := by
  induction a generalizing b with
  | nil => simp [monoMul, monomial_nil]
  | cons v as ih => exact monomial_mulAux v as (monoMul as) x ih b

/-- The powers `[(v, j)]` of `x v ^ j` (`[]` for `j = 0`). -/
def mono (v j : ℕ) : List (ℕ × ℕ) := if j = 0 then [] else [(v, j)]

theorem monomial_mono (x : ℕ → ℝ) (v j : ℕ) : monomial x (mono v j) = x v ^ j := by
  unfold mono
  split_ifs with h
  · simp [h, monomial_nil]
  · simp [monomial_cons, monomial_nil]

/-! ### Values -/

@[simp] theorem eval_nil (x : ℕ → ℝ) : eval [] x = 0 := by simp [eval]

theorem eval_cons (t : ℚ × List (ℕ × ℕ)) (p : RationalPolynomial) (x : ℕ → ℝ) :
    eval (t :: p) x = t.1 * monomial x t.2 + eval p x := by simp [eval]

/-- The constant `c`. -/
def const (c : ℚ) : RationalPolynomial := if c = 0 then [] else [(c, [])]

@[simp] theorem eval_const (c : ℚ) (x : ℕ → ℝ) : eval (const c) x = c := by
  unfold const
  split_ifs with h
  · simp [h]
  · simp [eval, monomial_nil]

/-- The variable `x i`. -/
def var (i : ℕ) : RationalPolynomial := [(1, mono i 1)]

@[simp] theorem eval_var (i : ℕ) (x : ℕ → ℝ) : eval (var i) x = x i := by
  simp [var, eval, monomial_mono]

/-- `-p`. -/
def neg (p : RationalPolynomial) : RationalPolynomial := p.map fun t ↦ (-t.1, t.2)

theorem eval_neg (p : RationalPolynomial) (x : ℕ → ℝ) : eval (neg p) x = -eval p x := by
  induction p with
  | nil => simp [neg]
  | cons t p ih =>
    simp only [neg, List.map_cons] at ih ⊢
    rw [eval_cons, eval_cons, ih]
    push_cast
    ring

/-- The lexicographic order of monomials with `x 0 > x 1 > ⋯` (a monomial order), on powers
sorted by their variables with positive exponents: the first variable where the exponents
differ decides. -/
def monoLt : List (ℕ × ℕ) → List (ℕ × ℕ) → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
    if a.1 < b.1 then false else if b.1 < a.1 then true
    else a.2 < b.2 || (a.2 == b.2 && monoLt as bs)

/-- `p + q`: the merge of the terms, those with equal exponents added and dropped if they
cancel. -/
def add : RationalPolynomial → RationalPolynomial → RationalPolynomial
  | [], q => q
  | s :: p, q => addAux s p (add p) q
where
  /-- The merge of `s :: p` into a list, `rec` adding `p` to the rest. -/
  addAux (s : ℚ × List (ℕ × ℕ)) (p : RationalPolynomial) (rec : RationalPolynomial → RationalPolynomial) : RationalPolynomial → RationalPolynomial
    | [] => s :: p
    | t :: q =>
      if s.2 = t.2 then (if s.1 + t.1 = 0 then rec q else (s.1 + t.1, s.2) :: rec q)
      else if monoLt s.2 t.2 then s :: rec (t :: q)
      else t :: addAux s p rec q

theorem eval_addAux (s : ℚ × List (ℕ × ℕ)) (p : RationalPolynomial) (rec : RationalPolynomial → RationalPolynomial) (x : ℕ → ℝ)
    (hrec : ∀ r, eval (rec r) x = eval p x + eval r x) :
    ∀ q, eval (add.addAux s p rec q) x = eval (s :: p) x + eval q x
  | [] => by simp [add.addAux]
  | t :: q => by
    have ih := eval_addAux s p rec x hrec q
    simp only [add.addAux]
    by_cases h1 : s.2 = t.2
    · by_cases h2 : s.1 + t.1 = 0
      · have h2' : (s.1 : ℝ) + t.1 = 0 := by exact_mod_cast h2
        simp only [h1, h2, ite_true, hrec, eval_cons]
        linear_combination (-1 : ℝ) * monomial x t.2 * h2'
      · simp only [h1, h2, ite_true, ite_false, eval_cons, hrec]
        push_cast
        ring
    · by_cases h3 : monoLt s.2 t.2 = true
      · simp only [h1, h3, ite_true, ite_false, eval_cons, hrec]
        ring
      · simp only [h1, h3, ite_false, Bool.false_eq_true, eval_cons, ih]
        ring

theorem eval_add (p q : RationalPolynomial) (x : ℕ → ℝ) : eval (add p q) x = eval p x + eval q x := by
  induction p generalizing q with
  | nil => simp [add]
  | cons s p ih => exact eval_addAux s p (add p) x ih q

/-- The product of a term and a polynomial. -/
def mulT (s : ℚ × List (ℕ × ℕ)) (q : RationalPolynomial) : RationalPolynomial :=
  q.map fun t ↦ (s.1 * t.1, monoMul s.2 t.2)

theorem eval_mulT (s : ℚ × List (ℕ × ℕ)) (q : RationalPolynomial) (x : ℕ → ℝ) :
    eval (mulT s q) x = s.1 * monomial x s.2 * eval q x := by
  induction q with
  | nil => simp [mulT]
  | cons t q ih =>
    simp only [mulT, List.map_cons] at ih ⊢
    rw [eval_cons, eval_cons, ih, monomial_monoMul]
    push_cast
    ring

/-- `p q`: the sum of the products by the terms of `p`. -/
def mul (p q : RationalPolynomial) : RationalPolynomial := p.foldr (fun s acc ↦ add (mulT s q) acc) []

theorem eval_mul (p q : RationalPolynomial) (x : ℕ → ℝ) : eval (mul p q) x = eval p x * eval q x := by
  induction p with
  | nil => simp [mul]
  | cons s p ih =>
    simp only [mul, List.foldr_cons] at ih ⊢
    rw [eval_add, eval_mulT, ih, eval_cons]
    ring

/-- The polynomial `∑ⱼ cⱼ x v ^ (j + k)` of the coefficients `cs = [c₀, c₁, …]` (`ofUni`). -/
def ofUniAux (v : ℕ) : ℕ → List ℚ → RationalPolynomial
  | _, [] => []
  | k, c :: cs => if c = 0 then ofUniAux v (k + 1) cs else (c, mono v k) :: ofUniAux v (k + 1) cs

/-- The polynomial `∑ⱼ cⱼ x v ^ j` in the single variable `x v`, coefficients from the constant
one. -/
def ofUni (v : ℕ) (cs : List ℚ) : RationalPolynomial := ofUniAux v 0 cs

theorem eval_ofUniAux (v : ℕ) (x : ℕ → ℝ) : ∀ (cs : List ℚ) (k : ℕ),
    eval (ofUniAux v k cs) x = ∑ j ∈ Finset.range cs.length, (cs.getD j 0 : ℝ) * x v ^ (j + k)
  | [], k => by simp [ofUniAux]
  | c :: cs, k => by
    have ih := eval_ofUniAux v x cs (k + 1)
    have hu : ofUniAux v k (c :: cs) =
        if c = 0 then ofUniAux v (k + 1) cs else (c, mono v k) :: ofUniAux v (k + 1) cs := rfl
    rw [hu, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, zero_add]
    have e : ∀ j, (cs.getD j 0 : ℝ) * x v ^ (j + 1 + k) = (cs.getD j 0 : ℝ) * x v ^ (j + (k + 1)) :=
      fun j ↦ by ring_nf
    simp only [e, ← ih]
    split_ifs with h
    · simp [h]
    · rw [eval_cons, monomial_mono]
      ring

theorem eval_ofUni (v : ℕ) (cs : List ℚ) (x : ℕ → ℝ) :
    eval (ofUni v cs) x = ∑ j ∈ Finset.range cs.length, (cs.getD j 0 : ℝ) * x v ^ j := by
  simp [ofUni, eval_ofUniAux]

/-! ### Expressions -/

/-- The expansion of an expression whose variable `i` is the polynomial `σ i`. -/
def ofExpr (σ : ℕ → RationalPolynomial) : Check.Expr → RationalPolynomial
  | .const c => const c
  | .var i => σ i
  | .add a b => add (ofExpr σ a) (ofExpr σ b)
  | .sub a b => add (ofExpr σ a) (neg (ofExpr σ b))
  | .mul a b => mul (ofExpr σ a) (ofExpr σ b)

theorem eval_ofExpr (σ : ℕ → RationalPolynomial) (x : ℕ → ℝ) :
    ∀ e : Check.Expr, eval (ofExpr σ e) x = e.eval fun i ↦ eval (σ i) x
  | .const c => by simp [ofExpr, Check.Expr.eval]
  | .var i => rfl
  | .add a b => by
    rw [ofExpr, eval_add, eval_ofExpr σ x a, eval_ofExpr σ x b]; rfl
  | .sub a b => by
    rw [ofExpr, eval_add, eval_neg, eval_ofExpr σ x a, eval_ofExpr σ x b, ← sub_eq_add_neg]; rfl
  | .mul a b => by
    rw [ofExpr, eval_mul, eval_ofExpr σ x a, eval_ofExpr σ x b]; rfl

/-! ### Both sides positive -/

/-- The equation `p = 0` as `p⁺ = p⁻`: the terms with positive coefficients on the left, the
others negated on the right. -/
def split (p : RationalPolynomial) : RationalPolynomial × RationalPolynomial :=
  (p.filter fun t ↦ 0 < t.1, (p.filter fun t ↦ ¬ 0 < t.1).map fun t ↦ (-t.1, t.2))

theorem eval_split (p : RationalPolynomial) (x : ℕ → ℝ) :
    p.eval x = (split p).1.eval x - (split p).2.eval x := by
  induction p with
  | nil => simp [split, eval_nil]
  | cons t p ih =>
    simp only [split] at ih ⊢
    by_cases h : 0 < t.1
    · simp only [List.filter_cons, h, decide_true, ↓reduceIte, not_true_eq_false, decide_false,
        Bool.false_eq_true, eval_cons, ih]
      ring
    · simp only [List.filter_cons, h, decide_false, Bool.false_eq_true, ↓reduceIte,
        not_false_eq_true, decide_true, List.map_cons, eval_cons, ih]
      push_cast
      ring

theorem eval_split_iff (p : RationalPolynomial) (x : ℕ → ℝ) :
    (split p).1.eval x = (split p).2.eval x ↔ p.eval x = 0 := by
  rw [eval_split p x, sub_eq_zero]

/-! ### Lean source -/
/-! ### Lean source -/

/-- A rational number as Lean source. -/
def ratLean (q : ℚ) : String :=
  if q.den = 1 then toString q.num else s!"{q.num}/{q.den}"

/-- A polynomial as Lean source. -/
def toLean (p : RationalPolynomial) : String :=
  "[" ++ ", ".intercalate (p.map fun t ↦ s!"({ratLean t.1}, {t.2})") ++ "]"

end RationalPolynomial

instance : DecidableEq RationalPolynomial := inferInstanceAs (DecidableEq (List (ℚ × List (ℕ × ℕ))))

instance : DecidableEq PolynomialSystem := fun a b ↦
  decidable_of_iff (a.eqs = b.eqs ∧ a.box = b.box) (by cases a; cases b; simp)

/-- A system of equations `p = 0` with a box, the working form of a `PolynomialSystem`. -/
structure ZSystem where
  /-- The polynomials that vanish. -/
  eqs : List RationalPolynomial
  /-- The box, as in `PolynomialSystem`. -/
  box : List (ℚ × ℚ)

namespace ZSystem

/-- `x` solves `S`: `x` lies in the box and every polynomial vanishes at `x`. -/
def Solves (S : ZSystem) (x : ℕ → ℝ) : Prop :=
  (∀ i < S.box.length, ((S.box.getD i (0, 0)).1 : ℝ) ≤ x i ∧ x i ≤ ((S.box.getD i (0, 0)).2 : ℝ)) ∧
    ∀ p ∈ S.eqs, p.eval x = 0

/-- The system with both sides of every equation positive (`RationalPolynomial.split`). -/
def toSystem (S : ZSystem) : PolynomialSystem := ⟨S.eqs.map RationalPolynomial.split, S.box⟩

theorem solves_toSystem (S : ZSystem) (x : ℕ → ℝ) : S.toSystem.Solves x ↔ S.Solves x := by
  simp only [PolynomialSystem.Solves, Solves, toSystem, List.forall_mem_map, RationalPolynomial.eval_split_iff]

theorem scales_toSystem (S : ZSystem) :
    PolynomialSystem.scales [S.toSystem] = {l | ∃ x : ℕ → ℝ, S.Solves x ∧ x 0 = l} := by
  ext l
  simp [PolynomialSystem.scales, solves_toSystem]

end ZSystem

namespace PolynomialSystem

/-- A system as Lean source, one equation a line. -/
def toLean (S : PolynomialSystem) : String :=
  "⟨[" ++ ",\n    ".intercalate
      (S.eqs.map fun e ↦ s!"({RationalPolynomial.toLean e.1},\n     {RationalPolynomial.toLean e.2})") ++ "],\n   [" ++
    ", ".intercalate (S.box.map fun b ↦ s!"({RationalPolynomial.ratLean b.1}, {RationalPolynomial.ratLean b.2})") ++
    "]⟩"

end PolynomialSystem

end Nieuwland
