import Mathlib.Algebra.Ring.Int.Defs

/-!
# Interpretations of `+`, `-` and `*`

The checks define each witness polynomial once, as a function over any type with `+`, `-` and `*`,
and interpret it in several such types: expressions (`Expr`) for the proofs, the reals for the
meaning, and, for the kernel, integers (values at packed points), `AbsNat` (coefficient bounds) and
`ShapeL` (degree bounds), the last two in `Modules/Check/Polynomial/Expr.lean`. A map `f` with `IsArith f`
(it commutes with `+`, `-` and `*`) carries one interpretation to another;
`Modules/Check/Leaf/Vec.lean` proves this for the vector operations.
-/

namespace Nieuwland.Check

/-- `f` commutes with `+`, `-` and `*`. -/
structure IsArith {α β : Type*} [Add α] [Sub α] [Mul α] [Add β] [Sub β] [Mul β] (f : α → β) :
    Prop where
  map_add : ∀ a b, f (a + b) = f a + f b
  map_sub : ∀ a b, f (a - b) = f a - f b
  map_mul : ∀ a b, f (a * b) = f a * f b

theorem isArith_intCast (R : Type*) [CommRing R] : IsArith (Int.cast : ℤ → R) :=
  ⟨Int.cast_add, Int.cast_sub, Int.cast_mul⟩

theorem IsArith.comp {α β γ : Type*} [Add α] [Sub α] [Mul α] [Add β] [Sub β] [Mul β] [Add γ]
    [Sub γ] [Mul γ] {f : β → γ} {g : α → β} (hf : IsArith f) (hg : IsArith g) :
    IsArith (f ∘ g) :=
  ⟨fun a b ↦ by simp [hg.map_add, hf.map_add], fun a b ↦ by simp [hg.map_sub, hf.map_sub],
    fun a b ↦ by simp [hg.map_mul, hf.map_mul]⟩

end Nieuwland.Check
