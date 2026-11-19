import Modules.Check.Polynomial.Expr
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Fractions over a fixed base

A pulled-back witness `p ∘ Φ` has exact coefficients and rational parameters: on a parameter box
`∏ [loᵢ, hiᵢ] / den`, write the parameters as `πᵢ = π'ᵢ / D` with `D = 2 den`. A value `v / D ^ k`
is stored as the pair `(v, k)`, an element of `FV D` (`FV.toVal`). Sums pad the smaller exponent by
powers of `D`, products add exponents. A constant `c` enters as `(c, 0)` and a parameter `πᵢ` as
`(π'ᵢ, 1)`, so every value of a computation is a polynomial in the `π'ᵢ` over a power of `D`,
with coefficients in the exact type of the computation's constants.

A generic computation (`GenPoly`, `Modules/Check/Number/Ext.lean`) is run in `FV` over several types
(`FV.isArith_map`): exact values (packed values), `AbsNat` and `ShapeL` over coordinates (norms and
shapes), `Expr` over coordinates (the polynomials themselves, in proofs) and `ℝ` (its meaning,
`FV.isArith_toVal`).
-/

namespace Nieuwland.Check

/-- The fraction `val / D ^ exp` over the base `D`. -/
structure FV {α : Type*} (D : α) where
  /-- The numerator. -/
  val : α
  /-- The exponent of the base in the denominator. -/
  exp : ℕ

namespace FV

section Ops

variable {α : Type*} [Add α] [Sub α] [Mul α]

/-- `a D ^ n`, by repeated multiplication. -/
def pad (D a : α) : ℕ → α
  | 0 => a
  | n + 1 => pad D a n * D

variable {D : α}

/-- The sum, over the larger of the two exponents. -/
def add (x y : FV D) : FV D :=
  if x.exp ≤ y.exp then ⟨pad D x.val (y.exp - x.exp) + y.val, y.exp⟩
  else ⟨x.val + pad D y.val (x.exp - y.exp), x.exp⟩

/-- The difference, over the larger of the two exponents. -/
def sub (x y : FV D) : FV D :=
  if x.exp ≤ y.exp then ⟨pad D x.val (y.exp - x.exp) - y.val, y.exp⟩
  else ⟨x.val - pad D y.val (x.exp - y.exp), x.exp⟩

/-- The product: numerators multiply, exponents add. -/
def mul (x y : FV D) : FV D :=
  ⟨x.val * y.val, x.exp + y.exp⟩

instance : Add (FV D) := ⟨add⟩
instance : Sub (FV D) := ⟨sub⟩
instance : Mul (FV D) := ⟨mul⟩

omit [Sub α] in
theorem add_def (x y : FV D) : x + y = add x y := rfl
omit [Add α] in
theorem sub_def (x y : FV D) : x - y = sub x y := rfl
omit [Add α] [Sub α] in
theorem mul_def (x y : FV D) : x * y = mul x y := rfl

end Ops

/-- The constant `c`, embedded by `k`, with exponent `0`. -/
def const {α κ : Type*} {D : α} (k : κ → α) (c : κ) : FV D := ⟨k c, 0⟩

/-! ### Naturality -/

section Map

variable {α β : Type*} {D : α}

/-- The image under `f`, over the base `f D`. -/
def map (f : α → β) (x : FV D) : FV (f D) := ⟨f x.val, x.exp⟩

@[simp] theorem map_val (f : α → β) (x : FV D) : (map f x).val = f x.val := rfl
@[simp] theorem map_exp (f : α → β) (x : FV D) : (map f x).exp = x.exp := rfl

theorem map_const {κ : Type*} (f : α → β) (k : κ → α) (c : κ) :
    map f (const (D := D) k c) = const (D := f D) (f ∘ k) c := rfl

theorem map_map {γ : Type*} (f : α → β) (g : β → γ) (x : FV D) :
    map g (map f x) = map (g ∘ f) x := rfl

variable [Add α] [Sub α] [Mul α] [Add β] [Sub β] [Mul β]

theorem map_pad {f : α → β} (hf : IsArith f) (a : α) :
    ∀ n, f (pad D a n) = pad (f D) (f a) n
  | 0 => rfl
  | n + 1 => by rw [pad, hf.map_mul, map_pad hf a n]; rfl

/-- Maps that commute with `+`, `-` and `*` commute with them on fractions. -/
theorem isArith_map {f : α → β} (hf : IsArith f) : IsArith (map (D := D) f) where
  map_add x y := by
    simp only [add_def, add, map]
    split_ifs <;> simp [hf.map_add, map_pad hf]
  map_sub x y := by
    simp only [sub_def, sub, map]
    split_ifs <;> simp [hf.map_sub, map_pad hf]
  map_mul x y := by
    simp only [mul_def, mul, map, hf.map_mul]

end Map

/-! ### Meaning -/

theorem pad_eq {R : Type*} [CommRing R] {D a : R} : ∀ n, pad D a n = a * D ^ n
  | 0 => by simp [pad]
  | n + 1 => by rw [pad, pad_eq n, pow_succ, mul_assoc]

section Real

variable {R : Type*} [Field R]

/-- The value of a fraction, `val / D ^ exp`. -/
def toVal {D : R} (x : FV D) : R := x.val / D ^ x.exp

theorem toVal_mk {D : R} (v : R) (k : ℕ) : toVal (⟨v, k⟩ : FV D) = v / D ^ k := rfl

theorem pow_sub_mul {D : R} {i j : ℕ} (h : i ≤ j) : D ^ (j - i) * D ^ i = D ^ j := by
  rw [← pow_add, Nat.sub_add_cancel h]

/-- **The meaning of fractions**: over a nonzero base of a field, `toVal` commutes with `+`, `-`
and `*`. -/
theorem isArith_toVal {D : R} (hD : D ≠ 0) : IsArith (toVal (D := D)) where
  map_add x y := by
    simp only [add_def, add]
    split_ifs with h
    · rw [toVal_mk, pad_eq, toVal, toVal, ← pow_sub_mul h]
      field_simp
    · rw [toVal_mk, pad_eq, toVal, toVal, ← pow_sub_mul (le_of_not_ge h)]
      field_simp
  map_sub x y := by
    simp only [sub_def, sub]
    split_ifs with h
    · rw [toVal_mk, pad_eq, toVal, toVal, ← pow_sub_mul h]
      field_simp
    · rw [toVal_mk, pad_eq, toVal, toVal, ← pow_sub_mul (le_of_not_ge h)]
      field_simp
  map_mul x y := by
    simp only [mul_def, mul, toVal, pow_add]
    field_simp

theorem toVal_const {κ : Type*} {D : R} (k : κ → R) (c : κ) : toVal (const (D := D) k c) = k c := by
  simp [toVal, const]

end Real

end FV

end Nieuwland.Check
