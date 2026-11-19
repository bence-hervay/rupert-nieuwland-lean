import Modules.Check.Polynomial.Sparse
import Modules.Check.Sign.Trunc

/-!
# Sparse terms

The terms of a sign check computed as rupert computes them (`witness_polys`,
`code/src/proof/tree.rs`): each term's polynomial is run in the ring of sparse polynomials (`SP`)
on the box inputs, so that its numerator in the varying coordinates comes out exactly, with like
terms merged and zero coefficients dropped (`Pull.numerS`). Its monomial `x^e` is divided off
exponentwise (`SPoly.divE`), and its coordinates in the basis of `κ` are integer polynomials
(`SPoly.coordS`), with their shapes and coefficient bounds (`SPoly.shapeS`, `SPoly.normS`): a
`Pull.TermS`. Their values at a packing point come by Horner's rule (`Pull.valS`, `SPoly.evalPk`),
where multiplying by a packing input `Cᵢ + Hᵢ 2^k` is two products by small numbers and a shift.
The checks that use them are in `Modules/Check/Sign/SparseBox.lean` and
`Modules/Check/Sign/SparsePull.lean`.
-/

namespace Nieuwland.Check

open DPoly

/-! ### Exponents and quotients -/

/-- `f - e` exponentwise if `e ≤ f` (a missing exponent is `0`). -/
def subE : List ℕ → List ℕ → Option (List ℕ)
  | [], f => some f
  | a :: e, [] => bif a == 0 then subE e [] else none
  | a :: e, b :: f => bif Nat.ble a b then (subE e f).map ((b - a) :: ·) else none

namespace SPoly

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The quotient of `p` by the monomial `x^e`, if `x^e` divides every term. -/
def divE (e : List ℕ) : SPoly κ → Option (SPoly κ)
  | [] => some []
  | t :: p => (subE e t.2).bind fun f ↦ (divE e p).map ((t.1, f) :: ·)

/-- Every exponent list of `q` has at most `n` entries (`q` is a polynomial in the first `n`
variables). -/
def lenOk (n : ℕ) (q : SPoly ℤ) : Bool := q.all fun t ↦ decide (t.2.length ≤ n)

/-- Per-variable degree bounds of `q` on the box inputs: the largest exponent of each variable, as
the shape of `q` as an expression (`Expr.shape`, `boxShapes`). -/
def shapeS (n : ℕ) (q : SPoly ℤ) : List ℕ :=
  (run (fun _ ↦ (⟨[]⟩ : ShapeL)) (fun i ↦ ⟨(boxShapes n).getD i []⟩) q).val

/-! #### Shapes computed directly -/

/-- `d :: r`, or `[]` when `d = 0` and `r = []`: a shape without trailing zeros. -/
def consZ (d : ℕ) (r : List ℕ) : List ℕ := bif d == 0 && r.isEmpty then [] else d :: r

/-- The shape of the monomial `x^e` on the box inputs: the first `n` entries of `e`, without
trailing zeros. -/
def monoSh : ℕ → List ℕ → List ℕ
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, d :: e => consZ d (monoSh n e)

/-- `shapeS` computed from the exponent lists directly, one pass over each, without the products
of shapes that `run` forms (`powG`, `mono`). Compiled code runs it (`shapeS_eq_shapeD`). -/
def shapeD (n : ℕ) (q : SPoly ℤ) : List ℕ :=
  q.foldr (fun t acc ↦ zipPad max (monoSh n t.2) acc) []

theorem monoSh_replicate_append : ∀ (n i : ℕ) (l : List ℕ), n ≤ i →
    monoSh n (List.replicate i 0 ++ l) = []
  | 0, _, _, _ => by simp [monoSh]
  | n + 1, i + 1, l, h => by
    rw [List.replicate_succ, List.cons_append, monoSh, monoSh_replicate_append n i l (by omega)]
    rfl

theorem monoSh_replicate : ∀ (n i : ℕ), monoSh n (List.replicate i 0) = []
  | 0, _ => by simp [monoSh]
  | _ + 1, 0 => by simp [monoSh]
  | n + 1, i + 1 => by
    rw [List.replicate_succ, monoSh, monoSh_replicate n i]
    rfl

theorem zipPad_add_nil_left (l : List ℕ) : zipPad (· + ·) [] l = l := rfl

theorem isEmpty_zipPad_append (f : ℕ → ℕ → ℕ) (l : List ℕ) (d : ℕ) (bs : List ℕ) :
    (zipPad f (l ++ [d]) bs).isEmpty = false := by
  cases l <;> cases bs <;> rfl

/-- The variable `i < n` to the power `d ≠ 0`, times the monomial of the variables after it. -/
theorem zipPad_monoSh : ∀ (n i d : ℕ) (e : List ℕ), i < n → d ≠ 0 →
    zipPad (· + ·) (List.replicate i 0 ++ [d]) (monoSh n (List.replicate (i + 1) 0 ++ e)) =
      monoSh n (List.replicate i 0 ++ d :: e)
  | n + 1, 0, d, e, _, hd => by
    change zipPad (· + ·) [d] (consZ 0 (monoSh n e)) = consZ d (monoSh n e)
    cases monoSh n e with
    | nil => simp [consZ, zipPad, hd]
    | cons a r => simp [consZ, zipPad]
  | n + 1, i + 1, d, e, hi, hd => by
    have ih := zipPad_monoSh n i d e (by omega) hd
    change zipPad (· + ·) (0 :: (List.replicate i 0 ++ [d]))
        (consZ 0 (monoSh n (List.replicate (i + 1) 0 ++ e))) =
      consZ 0 (monoSh n (List.replicate i 0 ++ d :: e))
    rw [← ih]
    have hne := isEmpty_zipPad_append (· + ·) (List.replicate i 0) d
      (monoSh n (List.replicate (i + 1) 0 ++ e))
    cases h : monoSh n (List.replicate (i + 1) 0 ++ e) with
    | nil =>
      rw [h, zipPad_nil_right] at hne
      simp [consZ, zipPad_nil_right, hne]
    | cons a r =>
      rw [h] at hne
      simp [consZ, zipPad, hne]

theorem zipPad_map_mul_self (a : ℕ) : ∀ l : List ℕ,
    zipPad (· + ·) (l.map (a * ·)) l = l.map ((a + 1) * ·)
  | [] => rfl
  | x :: l => by
    simp only [List.map_cons, zipPad, zipPad_map_mul_self a l]
    congr 1
    ring

theorem powG_shape (l : List ℕ) : ∀ d : ℕ,
    (powG (⟨[]⟩ : ShapeL) ⟨l⟩ (d + 1)).val = l.map ((d + 1) * ·)
  | 0 => by simp [powG]
  | d + 1 => by
    change zipPad (· + ·) (powG (⟨[]⟩ : ShapeL) ⟨l⟩ (d + 1)).val l = _
    rw [powG_shape l d, zipPad_map_mul_self]

theorem mono_shape (n : ℕ) : ∀ (i : ℕ) (e : List ℕ),
    (mono (⟨[]⟩ : ShapeL) (fun j ↦ ⟨(boxShapes n).getD j []⟩) i e).val =
      monoSh n (List.replicate i 0 ++ e)
  | i, [] => by rw [List.append_nil, monoSh_replicate]; rfl
  | i, d :: e => by
    have ih := mono_shape n (i + 1) e
    rw [mono]
    split_ifs with hd
    · rw [ih, hd, List.replicate_succ', List.append_assoc]
      rfl
    · obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
      change zipPad (· + ·) (powG (⟨[]⟩ : ShapeL) ⟨(boxShapes n).getD i []⟩ (d' + 1)).val
        (mono (⟨[]⟩ : ShapeL) (fun j ↦ ⟨(boxShapes n).getD j []⟩) (i + 1) e).val = _
      rw [powG_shape, ih, boxShapes, getD_range_map_append]
      by_cases hi : i < n
      · simp only [hi, ↓reduceIte, List.map_append, List.map_replicate, mul_zero, List.map_cons,
          mul_one, List.map_nil]
        exact zipPad_monoSh n i (d' + 1) e hi hd
      · simp only [hi, ↓reduceIte, ite_self, List.map_nil]
        rw [zipPad_add_nil_left,
          monoSh_replicate_append n (i + 1) e (by omega),
          monoSh_replicate_append n i _ (by omega)]

theorem run_shape (n : ℕ) : ∀ q : SPoly ℤ,
    (run (fun _ ↦ (⟨[]⟩ : ShapeL)) (fun i ↦ ⟨(boxShapes n).getD i []⟩) q).val = shapeD n q
  | [] => rfl
  | t :: q => by
    change zipPad max (zipPad (· + ·) []
        (mono (⟨[]⟩ : ShapeL) (fun j ↦ ⟨(boxShapes n).getD j []⟩) 0 t.2).val)
      (run (fun _ ↦ (⟨[]⟩ : ShapeL)) (fun i ↦ ⟨(boxShapes n).getD i []⟩) q).val = _
    rw [zipPad_add_nil_left, mono_shape, run_shape n q, List.replicate_zero, List.nil_append]
    rfl

/-- **Shapes computed directly.** Compiled code runs `shapeD` for `shapeS`; the kernel and the
proofs keep `shapeS`. -/
@[csimp] theorem shapeS_eq_shapeD : @shapeS = @shapeD := by
  funext n q
  exact run_shape n q

/-- A bound on the absolute coefficient sum of `q` on the box inputs with bounds `b`
(`Expr.normBound`). -/
def normS (b : List ℕ) (q : SPoly ℤ) : ℕ :=
  (run AbsNat.ofInt (fun i ↦ (⟨b.getD i 0⟩ : AbsNat)) q).val

/-! #### Norms computed directly -/

/-- `x ^ d` by squaring (`powB_eq`): compiled `Nat.pow` goes through GMP even for small numbers,
and repeated products cost more on large ones. -/
def powB (x d : ℕ) : ℕ :=
  if d ≤ 1 then bif d == 0 then 1 else x
  else
    let r := powB (x * x) (d / 2)
    bif d % 2 == 1 then r * x else r
termination_by d
decreasing_by omega

theorem powB_eq (x d : ℕ) : powB x d = x ^ d := by
  induction d using Nat.strong_induction_on generalizing x with
  | _ d ih =>
    rw [powB]
    split_ifs with h
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with rfl | rfl
      · rfl
      · exact (pow_one x).symm
    · rw [ih (d / 2) (by omega) (x * x), ← pow_two, ← pow_mul]
      have hd := Nat.div_add_mod d 2
      rcases Nat.mod_two_eq_zero_or_one d with h2 | h2 <;> simp only [h2] at hd ⊢
      · conv_rhs => rw [← hd]
        simp
      · conv_rhs => rw [← hd]
        simp [pow_succ]

/-- The bound `∏ⱼ bⱼ^eⱼ` of the monomial `x^e` on box inputs with the bounds `b` (`mono_norm`). -/
def monoW : List ℕ → List ℕ → ℕ
  | _, [] => 1
  | b, d :: e => bif d == 0 then monoW b.tail e else powB (b.headD 0) d * monoW b.tail e

/-- `normS` computed from the exponent lists directly: `∑ |c| ∏ⱼ bⱼ^eⱼ`, without the products
that `run` forms (`powG`, `mono`). -/
def normD (b : List ℕ) (q : SPoly ℤ) : ℕ :=
  q.foldr (fun t acc ↦ t.1.natAbs * monoW b t.2 + acc) 0

theorem powG_norm (x : ℕ) : ∀ d : ℕ, (powG (⟨1⟩ : AbsNat) ⟨x⟩ d).val = x ^ d
  | 0 => rfl
  | 1 => (pow_one x).symm
  | d + 2 => by
    change (powG (⟨1⟩ : AbsNat) ⟨x⟩ (d + 1)).val * x = _
    rw [powG_norm x (d + 1)]
    ring

theorem headD_drop_getD : ∀ (b : List ℕ) (i : ℕ), (b.drop i).headD 0 = b.getD i 0
  | [], _ => by simp
  | _ :: _, 0 => rfl
  | _ :: b, i + 1 => headD_drop_getD b i

theorem mono_norm (b : List ℕ) : ∀ (i : ℕ) (e : List ℕ),
    (mono (⟨1⟩ : AbsNat) (fun j ↦ ⟨b.getD j 0⟩) i e).val = monoW (b.drop i) e
  | _, [] => rfl
  | i, d :: e => by
    have ih := mono_norm b (i + 1) e
    rw [mono, monoW, List.tail_drop]
    split_ifs with hd
    · rw [ih, hd]
      rfl
    · change (powG (⟨1⟩ : AbsNat) ⟨b.getD i 0⟩ d).val *
        (mono (⟨1⟩ : AbsNat) (fun j ↦ ⟨b.getD j 0⟩) (i + 1) e).val = _
      rw [powG_norm, ih, headD_drop_getD]
      simp [hd, powB_eq]

theorem run_norm (b : List ℕ) : ∀ q : SPoly ℤ,
    (run AbsNat.ofInt (fun i ↦ (⟨b.getD i 0⟩ : AbsNat)) q).val = normD b q
  | [] => rfl
  | t :: q => by
    change t.1.natAbs * (mono (⟨1⟩ : AbsNat) (fun j ↦ ⟨b.getD j 0⟩) 0 t.2).val +
      (run AbsNat.ofInt (fun i ↦ (⟨b.getD i 0⟩ : AbsNat)) q).val = _
    rw [mono_norm, run_norm b q, List.drop_zero]
    rfl

/-- **Norms computed directly.** Compiled code runs `normD` for `normS`; the kernel and the proofs
keep `normS`. -/
@[csimp] theorem normS_eq_normD : @normS = @normD := by
  funext b q
  exact run_norm b q

/-- More than the largest `length + sum` of the exponent lists of `q`: the fuel of `evalPk`. -/
def fuelOf (q : SPoly ℤ) : ℕ := q.foldr (fun t a ↦ max (t.2.length + t.2.sum) a) 0 + 1

/-- The coefficient of a constant term. -/
def cTerm (t : ℤ × List ℕ) : Option ℤ := bif t.2.isEmpty then some t.1 else none

/-- A term of exponent `0` in its first variable, as a term in the variables after it. -/
def zTerm (t : ℤ × List ℕ) : Option (ℤ × List ℕ) :=
  match t.2 with
  | 0 :: f => some (t.1, f)
  | _ => none

/-- A term of positive exponent in its first variable, with that exponent lowered by one. -/
def sTerm (t : ℤ × List ℕ) : Option (ℤ × List ℕ) :=
  match t.2 with
  | (a + 1) :: f => some (t.1, a :: f)
  | _ => none

/-- `a + b`, without the addition (a copy of `b`) when `a = 0`. -/
def addZ (a b : ℤ) : ℤ := bif a == 0 then b else a + b

/-- The value of the terms `ts`, whose exponents are those of the variables `i, i + 1, …`, at
the integer point that `mul` multiplies by (`mul i v = v Zᵢ`), by Horner's rule in variable `i`:
the constant terms, the terms of exponent `0` in `i` from variable `i + 1` on, and `Zᵢ` times the
others with their exponent of `i` lowered (`evalPk_eq`). -/
def evalPk (mul : ℕ → ℤ → ℤ) : ℕ → ℕ → SPoly ℤ → ℤ
  | 0, _, _ => 0
  | fuel + 1, i, ts =>
    let z := ts.filterMap zTerm
    let s := ts.filterMap sTerm
    let v := bif z.isEmpty then 0 else evalPk mul fuel (i + 1) z
    addZ (ts.filterMap cTerm).sum (bif s.isEmpty then v else addZ v (mul i (evalPk mul fuel i s)))

end SPoly

section Coords

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- Coordinate `c` of the coefficients of `p`: an integer polynomial, zero coefficients
dropped. -/
def SPoly.coordS (c : ℕ) (p : SPoly κ) : SPoly ℤ :=
  p.filterMap fun t ↦
    let v := (ExactBasis.coords t.1).getD c 0
    bif v == 0 then none else some (v, t.2)

end Coords

/-! ### Soundness of the sparse operations -/

namespace SPoly

section Generic

variable {R : Type*} [CommRing R]

theorem mono_nilR (x : ℕ → R) (i : ℕ) : mono (1 : R) x i [] = 1 := rfl

theorem mono_consR (x : ℕ → R) (i d : ℕ) (e : List ℕ) :
    mono (1 : R) x i (d :: e) = x i ^ d * mono 1 x (i + 1) e := by
  simp only [mono]
  split_ifs with h
  · rw [h, pow_zero, one_mul]
  · rw [powG_one]

theorem subE_nil (x : ℕ → R) : ∀ (e : List ℕ) (i : ℕ) {f : List ℕ},
    subE e [] = some f → f = [] ∧ mono (1 : R) x i e = 1
  | [], _, f, h => by
    simp only [subE, Option.some.injEq] at h
    exact ⟨h.symm, rfl⟩
  | a :: e, i, f, h => by
    simp only [subE] at h
    cases ha : a == 0
    · rw [ha, Bool.cond_false] at h
      exact absurd h (by simp)
    · rw [ha, Bool.cond_true] at h
      rw [beq_iff_eq] at ha
      subst ha
      obtain ⟨hf, hm⟩ := subE_nil x e (i + 1) h
      exact ⟨hf, by rw [mono_consR, pow_zero, one_mul, hm]⟩

/-- **Exponentwise division.** If `subE e g = some f`, then `x^g = x^e x^f`. -/
theorem mono_subE (x : ℕ → R) : ∀ (e g : List ℕ) (i : ℕ) {f : List ℕ},
    subE e g = some f → mono (1 : R) x i g = mono 1 x i e * mono 1 x i f
  | [], g, i, f, h => by
    simp only [subE, Option.some.injEq] at h
    subst h
    rw [mono_nilR, one_mul]
  | a :: e, [], i, f, h => by
    obtain ⟨rfl, hm⟩ := subE_nil x (a :: e) i h
    rw [hm, mono_nilR, mul_one]
  | a :: e, b :: g, i, f, h => by
    simp only [subE] at h
    cases hab : Nat.ble a b
    · rw [hab, Bool.cond_false] at h
      exact absurd h (by simp)
    · rw [hab, Bool.cond_true] at h
      obtain ⟨f', hf', rfl⟩ := Option.map_eq_some_iff.mp h
      have hle : a ≤ b := Nat.le_of_ble_eq_true hab
      rw [mono_consR, mono_consR, mono_consR, mono_subE x e g (i + 1) hf']
      have : x i ^ b = x i ^ a * x i ^ (b - a) := by rw [← pow_add, Nat.add_sub_cancel' hle]
      rw [this]
      ring

/-- A monomial reads only the variables of its exponents. -/
theorem mono_congr {x x' : ℕ → R} : ∀ (i : ℕ) (e : List ℕ),
    (∀ j, i ≤ j → j < i + e.length → x j = x' j) → mono (1 : R) x i e = mono 1 x' i e
  | _, [], _ => rfl
  | i, d :: e, h => by
    rw [mono_consR, mono_consR, h i le_rfl (by simp),
      mono_congr (i + 1) e fun j h1 h2 ↦ h j (by omega) (by simp only [List.length_cons]; omega)]

/-- A monomial in the first `n` variables as `monoVal`. -/
theorem mono_eq_monoVal : ∀ (n : ℕ) (e : List ℕ) (i : ℕ) (x : ℕ → R), e.length ≤ n →
    mono (1 : R) x i e = DPoly.monoVal n e fun j : Fin n ↦ x (i + j)
  | 0, e, i, x, he => by
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp he)]
    rfl
  | n + 1, [], i, x, _ => by rw [mono_nilR, monoVal_nil]
  | n + 1, d :: e, i, x, he => by
    simp only [List.length_cons] at he
    rw [mono_consR, mono_eq_monoVal n e (i + 1) x (by omega)]
    simp only [DPoly.monoVal, List.headD_cons, List.tail_cons, Fin.val_zero, add_zero]
    congr 2
    funext j
    simp only [Fin.tail, Fin.val_succ]
    congr 1
    omega

/-- The value of an integer sparse polynomial at an integer-valued point as a sum. -/
theorem run_int_eq_sum (x : ℕ → R) : ∀ q : SPoly ℤ,
    run (fun c : ℤ ↦ (c : R)) x q = (q.map fun t ↦ (t.1 : R) * mono 1 x 0 t.2).sum
  | [] => by simp [run, Exact.ofInt]
  | t :: q => by
    rw [run, run_int_eq_sum x q, List.map_cons, List.sum_cons]
    simp [Exact.ofInt]

end Generic

theorem re_int (a : ℤ) : Exact.re a = (a : ℝ) := Erased.out_mk _

theorem run_re_int (x : ℕ → ℝ) (q : SPoly ℤ) :
    run Exact.re x q = run (fun c : ℤ ↦ (c : ℝ)) x q := by
  congr 1
  funext c
  exact re_int c

variable {κ : Type} [Add κ] [Sub κ] [Mul κ]

/-- **Division by a monomial.** If `divE e p = some q`, then `p = x^e q`. -/
theorem run_divE [Exact κ] (x : ℕ → ℝ) (e : List ℕ) : ∀ (p : SPoly κ) {q : SPoly κ},
    divE e p = some q → run Exact.re x p = mono 1 x 0 e * run Exact.re x q
  | [], q, h => by
    simp only [divE, Option.some.injEq] at h
    subst h
    rw [run_nil, mul_zero]
  | t :: p, q, h => by
    simp only [divE] at h
    obtain ⟨f, hf, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
    rw [run_cons, run_cons, run_divE x e p hq', mono_subE x e t.2 0 hf]
    ring

/-- **Coordinates.** A polynomial is the combination of its coordinate polynomials with the
basis values. -/
theorem run_coordS [ExactBasis κ] (x : ℕ → ℝ) : ∀ p : SPoly κ,
    run Exact.re x p = ∑ c ∈ Finset.range (ExactBasis.dim κ),
      ExactBasis.basis κ c * run Exact.re x (coordS c p)
  | [] => by simp [coordS, run_nil]
  | t :: p => by
    rw [run_cons, run_coordS x p, ExactBasis.re_eq, bsum, Finset.sum_mul,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [getD_map_of_eq (z := (0 : ℤ)) Int.cast_zero]
    unfold coordS
    rw [List.filterMap_cons]
    cases hv : (ExactBasis.coords t.1).getD c 0 == 0
    · simp only [hv, Bool.cond_false]
      rw [run_cons, re_int]
      ring
    · rw [beq_iff_eq] at hv
      simp only [hv, beq_self_eq_true, Bool.cond_true, Int.cast_zero, mul_zero, zero_mul,
        zero_add]

/-- Every exponent list of `q` has at most `n` entries. -/
theorem lenOk_iff {n : ℕ} {q : SPoly ℤ} : lenOk n q = true ↔ ∀ t ∈ q, t.2.length ≤ n := by
  simp [lenOk]

/-- **Locality.** A polynomial in the first `n` variables reads only them. -/
theorem run_congr_lenOk {α : Type*} [Add α] [Mul α] (k : ℤ → α) {x x' : ℕ → α} {n : ℕ}
    (h : ∀ j < n, x j = x' j) : ∀ {q : SPoly ℤ}, lenOk n q = true → run k x q = run k x' q
  | [], _ => rfl
  | t :: q, hq => by
    rw [lenOk_iff] at hq
    have ht := hq t List.mem_cons_self
    have ih := run_congr_lenOk k h (q := q)
      (lenOk_iff.mpr fun s hs ↦ hq s (List.mem_cons_of_mem _ hs))
    have hm : mono (k (Exact.ofInt 1)) x 0 t.2 = mono (k (Exact.ofInt 1)) x' 0 t.2 := by
      clear ih hq
      suffices ∀ (i : ℕ) (e : List ℕ), i + e.length ≤ n →
          mono (k (Exact.ofInt 1)) x i e = mono (k (Exact.ofInt 1)) x' i e from
        this 0 t.2 (by omega)
      intro i e
      induction e generalizing i with
      | nil => intro _; rfl
      | cons d e ihe =>
        intro hie
        simp only [List.length_cons] at hie
        simp only [mono]
        rw [h i (by omega), ihe (i + 1) (by omega)]
    simp only [run]
    rw [hm, ih]

/-! #### Horner's rule -/

/-- One term split as `evalPk` splits it: constant, exponent `0` in variable `i`, or `Zᵢ` times
the term with the exponent of `i` lowered. -/
theorem tval_split (Z : ℕ → ℤ) (i : ℕ) (t : ℤ × List ℕ) :
    t.1 * mono 1 Z i t.2 = (cTerm t).getD 0 +
      ((zTerm t).map fun t ↦ t.1 * mono 1 Z (i + 1) t.2).getD 0 +
      Z i * ((sTerm t).map fun t ↦ t.1 * mono 1 Z i t.2).getD 0 := by
  obtain ⟨a, e⟩ := t
  rcases e with _ | ⟨_ | d, f⟩
  · simp [cTerm, zTerm, sTerm, mono_nilR]
  · simp [cTerm, zTerm, sTerm, mono_consR]
  · simp only [cTerm, zTerm, sTerm, List.isEmpty_cons, Bool.cond_false, Option.getD_none,
      Option.map_none, Option.map_some, Option.getD_some, zero_add, mono_consR, pow_succ]
    ring

/-- The terms split as `evalPk` splits them. -/
theorem sum_split (Z : ℕ → ℤ) (i : ℕ) : ∀ ts : SPoly ℤ,
    (ts.map fun t ↦ t.1 * mono 1 Z i t.2).sum =
      (ts.filterMap cTerm).sum +
        ((ts.filterMap zTerm).map fun t ↦ t.1 * mono 1 Z (i + 1) t.2).sum +
        Z i * ((ts.filterMap sTerm).map fun t ↦ t.1 * mono 1 Z i t.2).sum
  | [] => by simp
  | t :: ts => by
    rw [List.map_cons, List.sum_cons, sum_split Z i ts, tval_split Z i t]
    rcases hc : cTerm t with _ | c <;> rcases hz : zTerm t with _ | z <;>
      rcases hs : sTerm t with _ | s <;>
      simp only [List.filterMap_cons, hc, hz, hs, Option.map_none, Option.map_some,
        Option.getD_none, Option.getD_some, List.map_cons, List.sum_cons] <;> ring

theorem le_fuelOf {q : SPoly ℤ} {t : ℤ × List ℕ} (ht : t ∈ q) :
    t.2.length + t.2.sum < fuelOf q := by
  unfold fuelOf
  suffices t.2.length + t.2.sum ≤ q.foldr (fun t a ↦ max (t.2.length + t.2.sum) a) 0 by omega
  induction q with
  | nil => cases ht
  | cons s q ih =>
    rcases List.mem_cons.mp ht with rfl | ht
    · exact le_max_left _ _
    · exact (ih ht).trans (le_max_right _ _)

theorem addZ_eq (a b : ℤ) : addZ a b = a + b := by
  unfold addZ
  cases h : a == 0
  · rfl
  · rw [beq_iff_eq] at h
    simp [h]

/-- **Horner's rule.** With enough fuel, `evalPk` is the value of the terms at the point `Z` that
`mul` multiplies by. -/
theorem evalPk_eq {mul : ℕ → ℤ → ℤ} {Z : ℕ → ℤ} (hmul : ∀ i v, mul i v = v * Z i) :
    ∀ (fuel i : ℕ) (ts : SPoly ℤ), (∀ t ∈ ts, t.2.length + t.2.sum < fuel) →
      evalPk mul fuel i ts = (ts.map fun t ↦ t.1 * mono 1 Z i t.2).sum
  | 0, _, [], _ => rfl
  | 0, _, t :: _, h => absurd (h t List.mem_cons_self) (Nat.not_lt_zero _)
  | fuel + 1, i, ts, h => by
    have hz : ∀ t ∈ ts.filterMap zTerm, t.2.length + t.2.sum < fuel := by
      intro t ht
      obtain ⟨s, hs, hst⟩ := List.mem_filterMap.mp ht
      have := h s hs
      obtain ⟨a, e⟩ := s
      rcases e with _ | ⟨_ | d, f⟩
      · exact absurd hst (by simp [zTerm])
      · simp only [zTerm, Option.some.injEq] at hst
        subst hst
        simp only [List.length_cons, List.sum_cons] at this ⊢
        omega
      · exact absurd hst (by simp [zTerm])
    have hs : ∀ t ∈ ts.filterMap sTerm, t.2.length + t.2.sum < fuel := by
      intro t ht
      obtain ⟨s, hs, hst⟩ := List.mem_filterMap.mp ht
      have := h s hs
      obtain ⟨a, e⟩ := s
      rcases e with _ | ⟨_ | d, f⟩
      · exact absurd hst (by simp [sTerm])
      · exact absurd hst (by simp [sTerm])
      · simp only [sTerm, Option.some.injEq] at hst
        subst hst
        simp only [List.length_cons, List.sum_cons] at this ⊢
        omega
    have ez : (bif (ts.filterMap zTerm).isEmpty then 0 else evalPk mul fuel (i + 1)
        (ts.filterMap zTerm)) =
        ((ts.filterMap zTerm).map fun t ↦ t.1 * mono 1 Z (i + 1) t.2).sum := by
      cases he : (ts.filterMap zTerm).isEmpty
      · rw [Bool.cond_false, evalPk_eq hmul fuel (i + 1) _ hz]
      · rw [Bool.cond_true, List.isEmpty_iff.mp he]
        rfl
    have es : ∀ v : ℤ, (bif (ts.filterMap sTerm).isEmpty then v else
        addZ v (mul i (evalPk mul fuel i (ts.filterMap sTerm)))) =
        v + Z i * ((ts.filterMap sTerm).map fun t ↦ t.1 * mono 1 Z i t.2).sum := by
      intro v
      cases he : (ts.filterMap sTerm).isEmpty
      · rw [Bool.cond_false, addZ_eq, hmul, evalPk_eq hmul fuel i _ hs, mul_comm]
      · rw [Bool.cond_true, List.isEmpty_iff.mp he]
        simp
    simp only [evalPk]
    rw [ez, es, addZ_eq, sum_split Z i ts, add_assoc]

/-! #### Integer sparse polynomials as expressions -/

/-- An integer sparse polynomial as an expression (in proofs). -/
def qE (q : SPoly ℤ) : Expr := run Expr.const Expr.var q

theorem eval_qE {R : Type*} [CommRing R] (x : ℕ → R) (q : SPoly ℤ) :
    (qE q).eval x = run (fun c : ℤ ↦ (c : R)) x q :=
  map_run (Expr.isArith_eval x) Expr.const Expr.var q

theorem evalInt_qE (l : List ℤ) (q : SPoly ℤ) :
    (qE q).evalInt l = run (fun c : ℤ ↦ c) (fun i ↦ l.getD i 0) q :=
  map_run (Expr.isArith_evalInt l) Expr.const Expr.var q

theorem shape_qE (n : ℕ) (q : SPoly ℤ) : (qE q).shape (boxShapes n) = shapeS n q :=
  congrArg ShapeL.val (map_run (Expr.isArith_shape (boxShapes n)) Expr.const Expr.var q)

theorem normBound_qE (b : List ℕ) (q : SPoly ℤ) : (qE q).normBound b = normS b q :=
  congrArg AbsNat.val (map_run (Expr.isArith_normBound b) Expr.const Expr.var q)

theorem run_id_eq_sum (x : ℕ → ℤ) : ∀ q : SPoly ℤ,
    run (fun c : ℤ ↦ c) x q = (q.map fun t ↦ t.1 * mono 1 x 0 t.2).sum
  | [] => rfl
  | t :: q => by
    rw [run, run_id_eq_sum x q, List.map_cons, List.sum_cons]
    rfl

end SPoly

namespace Pull

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-! ### Sparse terms -/

/-- The numerator of a term on the frame `(C, H, D)` as an exact sparse polynomial in the varying
coordinates (`Hᵢ ≠ 0`; the others are the constants `Cᵢ`), over the base `D`. -/
def numerS (t : Term κ) (C H : List ℤ) (D : ℤ) : FV (SP.cst (Exact.ofInt D) : SP κ) :=
  t.G.runFV SP.cst (SP.cst (Exact.ofInt D)) fun i ↦
    boxInput C H (fun c ↦ SP.cst (Exact.ofInt c)) SP.var i

/-- What the sparse check computes once per term on a frame: whether the monomial divides the
numerator (and has at most `n` exponents, at most the denominator's degree, and the quotient is in
the first `n` variables), the coordinates of the quotient, the degree `m` of its denominator, its
shape and a bound on its coefficient sums on the box. -/
structure TermS where
  /-- The monomial divides the numerator and is admissible. -/
  ok : Bool
  /-- The coordinates of the quotient, integer polynomials in the varying coordinates. -/
  q : List (SPoly ℤ)
  /-- The degree `k - |e|` of the quotient's denominator. -/
  m : ℕ
  /-- The shape of the quotient. -/
  sh : List ℕ
  /-- A bound on the absolute coefficient sums of the quotient's coordinates on the box. -/
  nb : ℕ
  deriving Inhabited

/-- The term frame of a sparse term (for `Frame.runTupleW`). -/
def TermS.tf (s : TermS) : TermFrame := ⟨s.ok, s.sh, s.m⟩

/-- The sparse term of the quotient `Q` of a numerator of degree `k` by `x^e` on the frame
`(C, H, D)` of `n` coordinates. -/
def termQ (n : ℕ) (e : List ℕ) (k : ℕ) (C H : List ℤ) (D : ℤ) (Q : SPoly κ) : TermS :=
  let qs := (List.range (ExactBasis.dim κ)).map fun c ↦ SPoly.coordS c Q
  ⟨decide (e.length ≤ n) && decide (e.sum ≤ k) && qs.all (SPoly.lenOk n), qs, k - e.sum,
    shapeMax (qs.map (SPoly.shapeS n)), (qs.map (SPoly.normS (boxNorms n C H D))).foldr max 0⟩

/-- A term on the frame `(C, H, D)` of `n` coordinates, computed sparsely: its numerator divided
by its monomial exponentwise (`default`, which fails, if the monomial does not divide it). -/
def termS (n : ℕ) (t : Term κ) (C H : List ℤ) (D : ℤ) : TermS :=
  let N := numerS t C H D
  match SPoly.divE t.e N.val.terms with
  | none => default
  | some Q => termQ n t.e N.exp C H D Q

/-- `v Zᵢ` at the packing point `Zᵢ = Cᵢ + Hᵢ 2^kᵢ` of the shape `shape` and the digit size `B`
(`Frame.pointW`): two products by small numbers and a shift (`mulPt_eq`). -/
def mulPt (shape : List ℕ) (C H : List ℤ) (B i : ℕ) (v : ℤ) : ℤ :=
  v * C.getD i 0 + (v * H.getD i 0) <<< (B * DPoly.slots (shape.drop (i + 1)))

/-- The values at the packing point of the coordinates of a sparse term. -/
def valS (shape : List ℕ) (C H : List ℤ) (B : ℕ) (s : TermS) : List ℤ :=
  s.q.map fun q ↦ SPoly.evalPk (mulPt shape C H B) (SPoly.fuelOf q) 0 q

section TermSFacts

variable {n : ℕ} {t : Term κ} {C H : List ℤ} {D : ℤ}

theorem termS_ok (h : (termS n t C H D).ok = true) :
    ∃ Q, SPoly.divE t.e (numerS t C H D).val.terms = some Q ∧
      termS n t C H D = termQ n t.e (numerS t C H D).exp C H D Q := by
  revert h
  dsimp only [termS]
  cases SPoly.divE t.e (numerS t C H D).val.terms with
  | none => intro h; exact (Bool.false_ne_true h).elim
  | some Q => intro _; exact ⟨Q, rfl, rfl⟩

theorem getD_mem_or {α : Type*} (l : List α) (c : ℕ) (d : α) : l.getD c d ∈ l ∨ l.getD c d = d := by
  by_cases hc : c < l.length
  · exact Or.inl (by rw [List.getD_eq_getElem _ _ hc]; exact List.getElem_mem hc)
  · exact Or.inr (List.getD_eq_default _ _ (by omega))

/-- The coordinates of a sparse term fit its shape and its bound. -/
theorem termS_bounded (c : ℕ) :
    ShapeLE (SPoly.shapeS n ((termS n t C H D).q.getD c [])) (termS n t C H D).sh ∧
      SPoly.normS (boxNorms n C H D) ((termS n t C H D).q.getD c []) ≤ (termS n t C H D).nb := by
  dsimp only [termS]
  cases SPoly.divE t.e (numerS t C H D).val.terms with
  | none => exact ⟨trivial, Nat.le_refl 0⟩
  | some Q =>
    dsimp only [termQ]
    rcases getD_mem_or ((List.range (ExactBasis.dim κ)).map fun c ↦ SPoly.coordS c Q) c [] with
      h | h
    · exact ⟨shapeLE_shapeMax (List.mem_map_of_mem h), le_foldr_max (List.mem_map_of_mem h)⟩
    · rw [h]
      exact ⟨trivial, Nat.zero_le _⟩

/-- The coordinates of a sparse term that checks are polynomials in the first `n` variables. -/
theorem termS_lenOk (h : (termS n t C H D).ok = true) (c : ℕ) :
    SPoly.lenOk n ((termS n t C H D).q.getD c []) = true := by
  obtain ⟨Q, -, heq⟩ := termS_ok h
  rw [heq] at h ⊢
  dsimp only [termQ] at h ⊢
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  rcases getD_mem_or ((List.range (ExactBasis.dim κ)).map fun c ↦ SPoly.coordS c Q) c [] with
    hm | hm
  · exact h.2 _ hm
  · rw [hm]
    rfl

/-- **The meaning of the sparse numerator**: at a real point `w` of the varying coordinates, over
`D^k`, it is the computation at `x = w / D`, where the constant coordinates are `Cᵢ / D`. -/
theorem eval_numerS (hD : (D : ℝ) ≠ 0) (w : ℕ → ℝ) :
    SP.eval w (numerS t C H D).val / (D : ℝ) ^ (numerS t C H D).exp =
      t.G.run Exact.re fun i ↦ boxInput C H (Int.cast : ℤ → ℝ) w i / D := by
  have h := congrArg FV.val (t.G.map_runFV (SP.isArith_eval (κ := κ) w) SP.cst
    (SP.cst (Exact.ofInt D)) fun i ↦ boxInput C H (fun c ↦ SP.cst (Exact.ofInt c)) SP.var i)
  rw [FV.map_val] at h
  have hk : (SP.eval w ∘ (SP.cst : κ → SP κ)) = Exact.re := funext fun c ↦ SP.eval_cst w c
  have hDD : SP.eval w (SP.cst (Exact.ofInt D : κ)) = (D : ℝ) := by
    rw [SP.eval_cst, Exact.re_ofInt]
  have hxx : (SP.eval w ∘ fun i ↦ boxInput C H (fun c ↦ SP.cst (Exact.ofInt c : κ))
      (SP.var (κ := κ)) i) = fun i ↦ boxInput C H (Int.cast : ℤ → ℝ) w i := by
    funext i
    simp only [Function.comp_apply, boxInput]
    split_ifs
    · rw [SP.eval_cst, Exact.re_ofInt]
    · rw [SP.eval_var]
  have h' : (t.G.runFV (SP.eval w ∘ SP.cst) (SP.eval w (SP.cst (Exact.ofInt D)))
      (SP.eval w ∘ fun i ↦ boxInput C H (fun c ↦ SP.cst (Exact.ofInt c)) SP.var i)).val =
      (t.G.runFV Exact.re (D : ℝ) fun i ↦ boxInput C H (Int.cast : ℤ → ℝ) w i).val :=
    t.G.val_runFV_congr hk hDD hxx
  have h3 := t.G.toVal_runFV hD fun i ↦ boxInput C H (Int.cast : ℤ → ℝ) w i
  rw [FV.toVal, GenPoly.exp_runFV] at h3
  rw [numerS, h, h', GenPoly.exp_runFV, h3]

/-- **The meaning of a sparse term**: at a point `x` of the box (whose constant coordinates are
`Cᵢ / D`), the computation is `x^e` times the combination of the coordinates of the quotient at
`D x`, over `D^m`. -/
theorem termS_run (hok : (termS n t C H D).ok = true) (hH : ∀ i, H.getD i 0 ≠ 0 → i < n)
    (hC : ∀ i, n ≤ i → C.getD i 0 = 0) (hD : (D : ℝ) ≠ 0) (x : Fin n → ℝ)
    (hx : ∀ i : Fin n, H.getD i 0 = 0 → (C.getD i 0 : ℝ) = D * x i) :
    t.G.run Exact.re (ext n x) = ((D : ℝ) ^ (termS n t C H D).m)⁻¹ * monoVal n t.e x *
      ∑ c ∈ Finset.range (ExactBasis.dim κ), ExactBasis.basis κ c *
        SPoly.run Exact.re (fun i ↦ (D : ℝ) * ext n x i) ((termS n t C H D).q.getD c []) := by
  obtain ⟨Q, hQ, heq⟩ := termS_ok hok
  rw [heq] at hok ⊢
  dsimp only [termQ] at hok ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hlen, hsum⟩, -⟩ := hok
  set w : ℕ → ℝ := fun i ↦ (D : ℝ) * ext n x i with hw
  have hin : (fun i ↦ boxInput C H (Int.cast : ℤ → ℝ) w i / (D : ℝ)) = ext n x := by
    funext i
    simp only [boxInput, ext, hw]
    by_cases hi : i < n
    · simp only [hi, ↓reduceDIte]
      split_ifs with h0
      · rw [hx ⟨i, hi⟩ h0]
        field_simp
      · field_simp
    · have h0 : H.getD i 0 = 0 := by_contra fun h ↦ hi (hH i h)
      simp only [h0, ↓reduceIte, hC i (by omega), hi, ↓reduceDIte]
      simp
  have hrun := eval_numerS (t := t) (C := C) (H := H) hD w
  rw [hin] at hrun
  rw [← hrun]
  have hmono : SPoly.mono (1 : ℝ) w 0 t.e = (D : ℝ) ^ t.e.sum * monoVal n t.e x := by
    rw [SPoly.mono_eq_monoVal n t.e 0 w hlen, ← monoVal_smul _ n t.e x hlen]
    congr 1
    funext j
    simp only [hw, ext, zero_add, j.2, ↓reduceDIte]
  have hq : ∀ c ∈ Finset.range (ExactBasis.dim κ),
      ExactBasis.basis κ c * SPoly.run Exact.re w
        (((List.range (ExactBasis.dim κ)).map fun c ↦ SPoly.coordS c Q).getD c []) =
      ExactBasis.basis κ c * SPoly.run Exact.re w (SPoly.coordS c Q) := by
    intro c hc
    rw [Box.getD_range_map _ _ _ (Finset.mem_range.mp hc)]
  rw [Finset.sum_congr rfl hq, ← SPoly.run_coordS w Q]
  change SPoly.run Exact.re w (numerS t C H D).val.terms / _ = _
  rw [SPoly.run_divE w t.e _ hQ, hmono]
  have hexp : (numerS t C H D).exp = t.G.expo := GenPoly.exp_runFV _ _ _ _
  rw [hexp] at hsum ⊢
  have hpow : (D : ℝ) ^ t.G.expo = (D : ℝ) ^ (t.G.expo - t.e.sum) * (D : ℝ) ^ t.e.sum := by
    rw [← pow_add, Nat.sub_add_cancel hsum]
  have h1 : (D : ℝ) ^ t.e.sum ≠ 0 := pow_ne_zero _ hD
  have h2 : (D : ℝ) ^ (t.G.expo - t.e.sum) ≠ 0 := pow_ne_zero _ hD
  rw [hpow]
  field_simp

end TermSFacts

theorem mulPt_eq (shape : List ℕ) (C H : List ℤ) (B i : ℕ) (v : ℤ) :
    mulPt shape C H B i v = v * Frame.pointW shape C H B i := by
  rw [mulPt, Frame.pointW, Int.shiftLeft_eq, packPoint'_eq]
  ring

/-- The values at the packing point by Horner's rule are those of the coordinates there. -/
theorem getD_valS (shape : List ℕ) (C H : List ℤ) (B : ℕ) (s : TermS) (c : ℕ) :
    (valS shape C H B s).getD c 0 =
      SPoly.run (fun c : ℤ ↦ c) (Frame.pointW shape C H B) (s.q.getD c []) := by
  rw [valS, getD_map_of_eq (z := []) (by rfl), SPoly.run_id_eq_sum,
    SPoly.evalPk_eq (mulPt_eq shape C H B) _ 0 _ fun t ht ↦ SPoly.le_fuelOf ht]

end Pull

end Nieuwland.Check
