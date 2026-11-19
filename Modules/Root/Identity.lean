import Modules.Check.Polynomial.Sparse
import Modules.Root.WeakFit

/-!
# Exact identities between slacks

A D2 certificate's weak fit (`code/src/proof/d2/`, "Weak fit") may leave a contact `g` outside
its system `A` whose slack is not negative at the root. The checker then asks for a duplicate
(`g` is an exact positive multiple of a slack of `A`; in centred mode the antipodal contacts) or
a coincidence (an exact identity `D g = ∑ p_i g_i` with the slacks `g_i` of `A`, `D` of one sign
at the root). Both are identities; at the zero every `g_i` vanishes, so `g` does. Here:

* `toSP`: an expression as a sparse polynomial over the field `κ` (`Modules/Check/Polynomial/Sparse.lean`)
  in the system's variables, the parameters read as the basis values of `κ`; its value is the
  expression's (`eval_toSP`).
* `polyE`: a polynomial given as data (terms of exponents and coefficient coordinates) as an
  expression, for the records of a certificate.
* `Sys.dupId`: the identity `a g = b g_i` of a duplicate, `a` and `b` the first coefficients of
  the expansions of `g_i` and `g` (the checker's cross-multiplication by the leading scalars).
* `Sys.idOk`: the identity of an `IdRec` expands to the polynomial without terms, and `D` has a
  sign on the zero's enclosure; `Sys.slack_zero_of_idOk`: then the contact's slack is `0` at the
  zero. `Sys.zeroCons`: the contacts of a weak fit's identities that check, for `Sys.weakOk`.

The identities are data of the check, not of the statement: a wrong or missing one only fails
`Sys.weakOk`.
-/

open Nieuwland.Check Finset

namespace Nieuwland

namespace Root

section Poly

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The coordinates of the `j`-th basis value. -/
def unitCoords (j : ℕ) : List ℤ := List.replicate j 0 ++ [1]

theorem getD_unitCoords (j i : ℕ) :
    ((unitCoords j).map (Int.cast : ℤ → ℝ)).getD i 0 = if i = j then 1 else 0 := by
  simp only [unitCoords, List.map_append, List.map_replicate, List.map_cons, List.map_nil,
    Int.cast_zero, Int.cast_one, List.getD_eq_getElem?_getD, List.getElem?_append,
    List.length_replicate, List.getElem?_replicate]
  split_ifs with h1 h2 h3
  · omega
  · rfl
  · subst h3; simp
  · have : i - j ≠ 0 := by omega
    simp [this]

theorem bsum_unitCoords (j : ℕ) :
    bsum (ExactBasis.basis κ) (ExactBasis.dim κ) ((unitCoords j).map Int.cast) = basisPar κ j := by
  unfold bsum basisPar
  simp only [getD_unitCoords, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_range]

/-- An expression as a sparse polynomial over `κ` in the variables below `nu`; the variable
`nu + j` is the constant `j`-th basis value of `κ`. -/
def toSP (κ : Type) [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] (nu : ℕ) : Expr → SP κ
  | .const c => SP.cst (Exact.ofInt c)
  | .var i => bif Nat.blt i nu then SP.var i else SP.cst (ExactBasis.ofCoords (unitCoords (i - nu)))
  | .add a b => toSP κ nu a + toSP κ nu b
  | .sub a b => toSP κ nu a - toSP κ nu b
  | .mul a b => toSP κ nu a * toSP κ nu b

/-- The polynomial's value is the expression's, at a point whose parameters are the basis
values. -/
theorem eval_toSP (nu : ℕ) (z : ℕ → ℝ) (hz : ∀ j, z (nu + j) = basisPar κ j) :
    ∀ e : Expr, SP.eval z (toSP κ nu e) = e.eval z
  | .const c => by rw [toSP, SP.eval_cst, Exact.re_ofInt]; rfl
  | .var i => by
    unfold toSP
    cases h : Nat.blt i nu
    · have hi : nu ≤ i := by
        by_contra hlt
        rw [Nat.blt_eq.mpr (by omega)] at h
        exact Bool.noConfusion h
      rw [Bool.cond_false, SP.eval_cst, ExactBasis.re_ofCoords, bsum_unitCoords, ← hz (i - nu),
        Nat.add_sub_cancel' hi]
      rfl
    · rw [Bool.cond_true, SP.eval_var]; rfl
  | .add a b => by
    rw [toSP, (SP.isArith_eval z).map_add, eval_toSP nu z hz a, eval_toSP nu z hz b]; rfl
  | .sub a b => by
    rw [toSP, (SP.isArith_eval z).map_sub, eval_toSP nu z hz a, eval_toSP nu z hz b]; rfl
  | .mul a b => by
    rw [toSP, (SP.isArith_eval z).map_mul, eval_toSP nu z hz a, eval_toSP nu z hz b]; rfl

/-- An expression whose polynomial has no terms vanishes. -/
theorem eval_eq_zero_of_toSP (nu : ℕ) (z : ℕ → ℝ) (hz : ∀ j, z (nu + j) = basisPar κ j)
    {e : Expr} (h : (toSP κ nu e).terms.isEmpty = true) : e.eval z = 0 := by
  rw [← eval_toSP nu z hz e, SP.eval, List.isEmpty_iff.mp h, SPoly.run_nil]

/-- The first coefficient of a polynomial's expansion (`0` for the zero polynomial). -/
def lead (p : SP κ) : κ := (p.terms.head?.map (·.1)).getD (Exact.ofInt 0)

/-- `e` times the monomial of the exponents `ks` in the variables from `i` on. -/
def monoE : ℕ → List ℕ → Expr → Expr
  | _, [], e => e
  | i, k :: ks, e => monoE (i + 1) ks (k.repeat (fun a ↦ .mul a (.var i)) e)

/-- A polynomial as an expression: the sum of its terms `(exponents of the variables,
coordinates of the coefficient in the basis values, the variables from `nu` on)`. -/
def polyE (nu dim : ℕ) (ts : List (List ℕ × List ℤ)) : Expr :=
  ts.foldl (fun acc t ↦ .add acc (monoE 0 t.1 (elemE nu dim t.2))) (.const 0)

end Poly

namespace Sys

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] {S : Sys} {K : Kraw}

/-- The expression `D g - ∑ p_i g_i` of an identity. -/
def idE (S : Sys) (r : IdRec) : Expr :=
  .sub (.mul r.D (S.slack r.con)) (sumE S.k fun i ↦ .mul (r.p.getD i (.const 0)) (S.g i))

/-- The check of an identity over `κ`, on the balls `Z` of the variables at the zero: `D` has a
sign there, and `D g - ∑ p_i g_i` expands to the polynomial without terms. -/
def idOk (κ : Type) [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] (S : Sys) (Z : List Ball)
    (r : IdRec) : Bool :=
  ((bval (Kraw.zball Z) r.D).isPos || (bval (Kraw.zball Z) r.D).isNeg) &&
    (toSP κ S.n (S.idE r)).terms.isEmpty

/-- The identity of a duplicate: `a g = b g_i` for the contact `con` and the system's contact
`of`, with the first coefficients `a` of `g_i` and `b` of `g`. -/
def dupId (κ : Type) [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] (S : Sys)
    (d : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) : IdRec :=
  let co (c : ℕ × ℕ × ℕ) : Expr :=
    elemE S.n (ExactBasis.dim κ) (ExactBasis.coords (lead (toSP κ S.n (S.slack c))))
  ⟨d.1, co d.2, S.contacts.map fun c ↦ bif c == d.2 then co d.1 else .const 0⟩

/-- The contacts of a weak fit's duplicates and coincidences whose identities check: their
slacks vanish at the zero. -/
def zeroCons (κ : Type) [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] (S : Sys) (Z : List Ball)
    (W : WeakRec) : List (ℕ × ℕ × ℕ) :=
  ((W.dups.map (dupId κ S) ++ W.ids).filter (idOk κ S Z)).map (·.con)

/-- **Soundness of an identity**: the contact's slack vanishes at the zero. -/
theorem slack_zero_of_idOk (hK : K.eqs = S.eqs) (hp : K.ParOk (basisPar κ))
    {y : Fin K.n → ℝ} (hy : y ∈ K.box)
    (h0 : K.F (basisPar κ) y = 0) {r : IdRec} (h : idOk κ S K.zballs r = true) :
    (S.slack r.con).eval (K.env (basisPar κ) y) = 0 := by
  have hY : ∀ i, (Kraw.zball K.zballs i).Encl (K.env (basisPar κ) y i) := K.encl_zballs hp hy h0
  simp only [idOk, Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨hsign, hemp⟩ := h
  have hz : ∀ j, K.env (basisPar κ) y (S.n + j) = basisPar κ j := fun j ↦ by
    rw [← Sys.n_eq hK, Kraw.env_par]
  have e := eval_eq_zero_of_toSP S.n _ hz hemp
  simp only [idE, Expr.eval, eval_sumE] at e
  rw [sum_eq_zero (fun i hi ↦ by rw [S.g_zero hK h0 (mem_range.mp hi), mul_zero]), sub_zero] at e
  have hD : r.D.eval (K.env (basisPar κ) y) ≠ 0 := by
    rcases hsign with h | h
    · exact (Ball.pos_sound (encl_bval hY r.D) h).ne'
    · exact (Ball.neg_sound (encl_bval hY r.D) h).ne
  exact (mul_eq_zero.mp e).resolve_left hD

/-- The slacks of `zeroCons` vanish at the zero. -/
theorem slack_zero_of_mem_zeroCons (hK : K.eqs = S.eqs) (hp : K.ParOk (basisPar κ))
    {y : Fin K.n → ℝ} (hy : y ∈ K.box)
    (h0 : K.F (basisPar κ) y = 0) {W : WeakRec} {c : ℕ × ℕ × ℕ}
    (hc : c ∈ zeroCons κ S K.zballs W) : (S.slack c).eval (K.env (basisPar κ) y) = 0 := by
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
  exact slack_zero_of_idOk hK hp hy h0 (List.mem_filter.mp hr).2

end Sys

end Root

end Nieuwland
