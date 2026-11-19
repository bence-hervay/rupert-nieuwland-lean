import Modules.Check.Number.Arith
import Modules.Check.Polynomial.Poly

/-!
# Polynomial expressions

An `Expr` is a polynomial expression over `+`, `-`, `*`, integer constants and variables
`0, 1, …`: the polynomials of the checks as objects that proofs reason about. Their
interpretations are related once and for all here:

* `Expr.eval`: the value at a point of any commutative ring, the meaning used in proofs;
* `Expr.evalInt`: the value at an integer point, with direct integer operations;
* `Expr.toDPoly`: the dense polynomial obtained when the variables are themselves polynomials
  (`eval_toDPoly`); it exists only in proofs;
* `Expr.normBound` and `Expr.shape`: bounds on the coefficient sizes and per-variable degrees of
  `toDPoly`, from bounds on the inputs (`absSum_toDPoly_le`, `fits_toDPoly`).

All of these except `toDPoly` commute with `+`, `-` and `*` (`isArith_eval`, …), `normBound` and
`shape` as maps to the types `AbsNat` and `ShapeL`, in which subtraction acts like addition. So the
interpretation of an expression built by generic operations is computed by running those
operations on the interpreted inputs (`Modules/Check/Number/Arith.lean`), and the kernel need not build
the expression at all.
-/

namespace Nieuwland.Check

/-- Polynomial expressions with integer constants. -/
inductive Expr where
  /-- An integer constant. -/
  | const (c : ℤ)
  /-- The variable with index `i`. -/
  | var (i : ℕ)
  /-- A sum. -/
  | add (a b : Expr)
  /-- A difference. -/
  | sub (a b : Expr)
  /-- A product. -/
  | mul (a b : Expr)
  deriving Inhabited

/-- Natural numbers in which subtraction adds: bounds on absolute coefficient sums, which satisfy
`‖p ± q‖ ≤ ‖p‖ + ‖q‖` and `‖p q‖ ≤ ‖p‖ ‖q‖` (`Expr.isArith_normBound`). -/
structure AbsNat where
  /-- The bound. -/
  val : ℕ

instance : Add AbsNat := ⟨fun a b ↦ ⟨Nat.add a.val b.val⟩⟩
instance : Sub AbsNat := ⟨fun a b ↦ ⟨Nat.add a.val b.val⟩⟩
instance : Mul AbsNat := ⟨fun a b ↦ ⟨Nat.mul a.val b.val⟩⟩

/-- The bound `|c|` of an integer constant. -/
def AbsNat.ofInt (c : ℤ) : AbsNat := ⟨c.natAbs⟩

/-- Per-variable degree bounds, with the maximum for sums and differences and the sum for
products (`Expr.isArith_shape`). -/
structure ShapeL where
  /-- The degree bounds. -/
  val : List ℕ

instance : Add ShapeL := ⟨fun a b ↦ ⟨zipPad max a.val b.val⟩⟩
instance : Sub ShapeL := ⟨fun a b ↦ ⟨zipPad max a.val b.val⟩⟩
instance : Mul ShapeL := ⟨fun a b ↦ ⟨zipPad (· + ·) a.val b.val⟩⟩

namespace Expr

instance : Add Expr := ⟨add⟩
instance : Sub Expr := ⟨sub⟩
instance : Mul Expr := ⟨mul⟩

/-- The value at the point `x` of a commutative ring. -/
def eval {R : Type*} [CommRing R] (x : ℕ → R) : Expr → R
  | const c => c
  | var i => x i
  | add a b => eval x a + eval x b
  | sub a b => eval x a - eval x b
  | mul a b => eval x a * eval x b

@[simp] theorem eval_const {R : Type*} [CommRing R] (x : ℕ → R) (c : ℤ) :
    eval x (const c) = c := rfl
@[simp] theorem eval_var {R : Type*} [CommRing R] (x : ℕ → R) (i : ℕ) :
    eval x (var i) = x i := rfl
@[simp] theorem eval_add {R : Type*} [CommRing R] (x : ℕ → R) (a b : Expr) :
    eval x (a + b) = eval x a + eval x b := rfl
@[simp] theorem eval_sub {R : Type*} [CommRing R] (x : ℕ → R) (a b : Expr) :
    eval x (a - b) = eval x a - eval x b := rfl
@[simp] theorem eval_mul {R : Type*} [CommRing R] (x : ℕ → R) (a b : Expr) :
    eval x (a * b) = eval x a * eval x b := rfl

/-- Ring homomorphisms commute with evaluation. -/
theorem map_eval {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : ℕ → R) :
    ∀ e : Expr, f (eval x e) = eval (fun i ↦ f (x i)) e
  | const c => by simp [eval]
  | var i => rfl
  | add a b => by simp [eval, map_eval f x a, map_eval f x b]
  | sub a b => by simp [eval, map_eval f x a, map_eval f x b]
  | mul a b => by simp [eval, map_eval f x a, map_eval f x b]

/-- The value at an integer point, by direct integer operations (for the kernel). -/
def evalInt (x : List ℤ) : Expr → ℤ
  | const c => c
  | var i => x.getD i 0
  | add a b => Int.add (evalInt x a) (evalInt x b)
  | sub a b => Int.sub (evalInt x a) (evalInt x b)
  | mul a b => Int.mul (evalInt x a) (evalInt x b)

theorem evalInt_eq (x : List ℤ) : ∀ e : Expr, evalInt x e = eval (fun i ↦ x.getD i 0) e
  | const _ => rfl
  | var _ => rfl
  | add a b => by simp only [evalInt, eval, evalInt_eq x a, evalInt_eq x b]; rfl
  | sub a b => by simp only [evalInt, eval, evalInt_eq x a, evalInt_eq x b]; rfl
  | mul a b => by simp only [evalInt, eval, evalInt_eq x a, evalInt_eq x b]; rfl

/-- The dense polynomial of `e` when variable `i` is the polynomial `x i`. -/
def toDPoly (n : ℕ) (x : ℕ → DPoly n) : Expr → DPoly n
  | const c => DPoly.const n c
  | var i => x i
  | add a b => DPoly.add n (toDPoly n x a) (toDPoly n x b)
  | sub a b => DPoly.add n (toDPoly n x a) (DPoly.smul n (-1) (toDPoly n x b))
  | mul a b => DPoly.mul n (toDPoly n x a) (toDPoly n x b)

theorem eval_toDPoly {R : Type*} [CommRing R] (n : ℕ) (x : ℕ → DPoly n) (y : Fin n → R) :
    ∀ e : Expr, DPoly.eval n (toDPoly n x e) y = eval (fun i ↦ DPoly.eval n (x i) y) e
  | const c => by simp [toDPoly]
  | var i => rfl
  | add a b => by simp [toDPoly, eval, eval_toDPoly n x y a, eval_toDPoly n x y b]
  | sub a b => by
    simp [toDPoly, eval, eval_toDPoly n x y a, eval_toDPoly n x y b, sub_eq_add_neg]
  | mul a b => by simp [toDPoly, eval, eval_toDPoly n x y a, eval_toDPoly n x y b]

/-- A bound on the sum of the absolute values of the coefficients of `toDPoly`, given such
bounds `b` for the inputs. -/
def normBound (b : List ℕ) : Expr → ℕ
  | const c => c.natAbs
  | var i => b.getD i 0
  | add e e' => normBound b e + normBound b e'
  | sub e e' => normBound b e + normBound b e'
  | mul e e' => normBound b e * normBound b e'

theorem isArith_eval {R : Type*} [CommRing R] (x : ℕ → R) : IsArith (eval x) :=
  ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

theorem isArith_evalInt (x : List ℤ) : IsArith (evalInt x) :=
  ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

theorem isArith_normBound (b : List ℕ) : IsArith fun e ↦ (⟨normBound b e⟩ : AbsNat) :=
  ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

theorem absSum_toDPoly_le (n : ℕ) (x : ℕ → DPoly n) (b : List ℕ)
    (hb : ∀ i, DPoly.absSum n (x i) ≤ b.getD i 0) :
    ∀ e : Expr, DPoly.absSum n (toDPoly n x e) ≤ normBound b e
  | const c => (DPoly.absSum_const n c).le
  | var i => hb i
  | add e e' => (DPoly.absSum_add_le n _ _).trans
      (Nat.add_le_add (absSum_toDPoly_le n x b hb e) (absSum_toDPoly_le n x b hb e'))
  | sub e e' => by
    refine (DPoly.absSum_add_le n _ _).trans (Nat.add_le_add (absSum_toDPoly_le n x b hb e) ?_)
    rw [DPoly.absSum_smul]
    simpa using absSum_toDPoly_le n x b hb e'
  | mul e e' => (DPoly.absSum_mul_le n _ _).trans
      (Nat.mul_le_mul (absSum_toDPoly_le n x b hb e) (absSum_toDPoly_le n x b hb e'))

/-- Per-variable degree bounds of `toDPoly`, given the shapes `s` of the inputs. -/
def shape (s : List (List ℕ)) : Expr → List ℕ
  | const _ => []
  | var i => s.getD i []
  | add e e' => zipPad max (shape s e) (shape s e')
  | sub e e' => zipPad max (shape s e) (shape s e')
  | mul e e' => zipPad (· + ·) (shape s e) (shape s e')

theorem isArith_shape (s : List (List ℕ)) : IsArith fun e ↦ (⟨shape s e⟩ : ShapeL) :=
  ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

theorem fits_toDPoly (n : ℕ) (x : ℕ → DPoly n) (s : List (List ℕ))
    (hs : ∀ i, DPoly.Fits n (x i) (s.getD i [])) :
    ∀ e : Expr, DPoly.Fits n (toDPoly n x e) (shape s e)
  | const c => DPoly.fits_const n c _
  | var i => hs i
  | add e e' => DPoly.fits_add n (fits_toDPoly n x s hs e) (fits_toDPoly n x s hs e')
  | sub e e' => DPoly.fits_add n (fits_toDPoly n x s hs e)
      (DPoly.fits_smul n _ (fits_toDPoly n x s hs e'))
  | mul e e' => DPoly.fits_mul n (fits_toDPoly n x s hs e) (fits_toDPoly n x s hs e')

end Expr

end Nieuwland.Check
