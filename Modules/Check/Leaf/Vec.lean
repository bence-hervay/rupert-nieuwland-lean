import Modules.Check.Number.Arith
import Modules.Rupert.Quat
import Mathlib.LinearAlgebra.CrossProduct

/-!
# Vectors for the kernel

`V3 α` and `Q4 α` are vectors of space and quaternions with named components, the form in which
checks compute with them. Mathlib's vectors `Fin 3 → α`, written `![x, y, z]`, cost the kernel
several unfoldings of `Fin.cases` for every component access (about ten times slower, measured),
so checks use `V3` and `Q4`, and proofs translate with `V3.toFun` and `Q4.toFun`.

The operations are defined once, for any type with `+`, `-` and `*`, and the lemmas come in two
kinds:

* naturality: a map `f` with `IsArith f` commutes with every operation (`V3.map_cross`,
  `Q4.map_rotate`, …), which moves a computation between interpretations;
* meaning: in a commutative ring, the operations are Mathlib's `+`, `-`, `•`, `⬝ᵥ`, `⨯₃`,
  `quatMatrix q *ᵥ` and the Hamilton product `qmul` (`V3.toFun_cross`, `Q4.toFun_rotate`,
  `Q4.toFun_mul`, …).
-/

open Matrix

namespace Nieuwland.Check

/-- A vector of space with components `x`, `y`, `z`. -/
structure V3 (α : Type*) where
  /-- The first component. -/
  x : α
  /-- The second component. -/
  y : α
  /-- The third component. -/
  z : α

/-- A quaternion with components `w`, `x`, `y`, `z`. -/
structure Q4 (α : Type*) where
  /-- The scalar part. -/
  w : α
  /-- The first component of the vector part. -/
  x : α
  /-- The second component of the vector part. -/
  y : α
  /-- The third component of the vector part. -/
  z : α

namespace V3

variable {α β γ R : Type*}

/-- The vector as a function `Fin 3 → α`. -/
def toFun (v : V3 α) : Fin 3 → α := ![v.x, v.y, v.z]

/-- Componentwise image. -/
def map (f : α → β) (v : V3 α) : V3 β := ⟨f v.x, f v.y, f v.z⟩

/-- The vector `v`, cast to a commutative ring. -/
def cast (R : Type*) [CommRing R] (v : V3 ℤ) : Fin 3 → R := (v.map (Int.cast : ℤ → R)).toFun

@[simp] theorem toFun_zero (v : V3 α) : v.toFun 0 = v.x := rfl
@[simp] theorem toFun_one (v : V3 α) : v.toFun 1 = v.y := rfl
@[simp] theorem toFun_two (v : V3 α) : v.toFun 2 = v.z := rfl
@[simp] theorem map_x (f : α → β) (v : V3 α) : (v.map f).x = f v.x := rfl
@[simp] theorem map_y (f : α → β) (v : V3 α) : (v.map f).y = f v.y := rfl
@[simp] theorem map_z (f : α → β) (v : V3 α) : (v.map f).z = f v.z := rfl

theorem map_map (f : β → γ) (g : α → β) (v : V3 α) : (v.map g).map f = v.map (f ∘ g) := rfl

theorem toFun_map (f : α → β) (v : V3 α) : (v.map f).toFun = fun i ↦ f (v.toFun i) := by
  funext i; fin_cases i <;> rfl

section Arith

variable [Add α] [Sub α] [Mul α]

/-- `u + v`. -/
def add (u v : V3 α) : V3 α := ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩

/-- `u - v`. -/
def sub (u v : V3 α) : V3 α := ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩

/-- `a • v`. -/
def smul (a : α) (v : V3 α) : V3 α := ⟨a * v.x, a * v.y, a * v.z⟩

/-- `u ⬝ᵥ v`. -/
def dot (u v : V3 α) : α := u.x * v.x + u.y * v.y + u.z * v.z

/-- `u ⨯₃ v`. -/
def cross (u v : V3 α) : V3 α :=
  ⟨u.y * v.z - u.z * v.y, u.z * v.x - u.x * v.z, u.x * v.y - u.y * v.x⟩

section Natural

variable [Add β] [Sub β] [Mul β] {f : α → β}

theorem map_add (hf : IsArith f) (u v : V3 α) : (u.add v).map f = (u.map f).add (v.map f) := by
  simp [add, map, hf.map_add]

theorem map_sub (hf : IsArith f) (u v : V3 α) : (u.sub v).map f = (u.map f).sub (v.map f) := by
  simp [sub, map, hf.map_sub]

theorem map_smul (hf : IsArith f) (a : α) (v : V3 α) :
    (smul a v).map f = smul (f a) (v.map f) := by
  simp [smul, map, hf.map_mul]

theorem map_dot (hf : IsArith f) (u v : V3 α) : f (u.dot v) = (u.map f).dot (v.map f) := by
  simp [dot, map, hf.map_add, hf.map_mul]

theorem map_cross (hf : IsArith f) (u v : V3 α) :
    (u.cross v).map f = (u.map f).cross (v.map f) := by
  simp [cross, map, hf.map_sub, hf.map_mul]

end Natural

end Arith

section Ring

variable [CommRing R]

theorem toFun_add (u v : V3 R) : (u.add v).toFun = u.toFun + v.toFun := by
  funext i; fin_cases i <;> rfl

theorem toFun_sub (u v : V3 R) : (u.sub v).toFun = u.toFun - v.toFun := by
  funext i; fin_cases i <;> rfl

theorem toFun_smul (a : R) (v : V3 R) : (smul a v).toFun = a • v.toFun := by
  funext i; fin_cases i <;> rfl

theorem dot_eq_dotProduct (u v : V3 R) : u.dot v = u.toFun ⬝ᵥ v.toFun := by
  simp [dot, toFun, dotProduct, Fin.sum_univ_three]

theorem toFun_cross (u v : V3 R) : (u.cross v).toFun = u.toFun ⨯₃ v.toFun := by
  funext i; fin_cases i <;> simp [cross, toFun, cross_apply]

end Ring

/-- Component `i`, for the kernel (`get_eq_toFun`). -/
def get (v : V3 α) (i : Fin 3) : α :=
  match i with
  | 0 => v.x
  | 1 => v.y
  | 2 => v.z

theorem get_eq_toFun (v : V3 α) (i : Fin 3) : v.get i = v.toFun i := by
  fin_cases i <;> rfl

section Cast

variable [CommRing R]

@[simp] theorem cast_apply (v : V3 ℤ) (i : Fin 3) : cast R v i = (v.get i : R) := by
  fin_cases i <;> rfl

@[simp] theorem cast_add (u v : V3 ℤ) : cast R (u.add v) = cast R u + cast R v := by
  rw [cast, map_add (isArith_intCast R), toFun_add]; rfl

@[simp] theorem cast_sub (u v : V3 ℤ) : cast R (u.sub v) = cast R u - cast R v := by
  rw [cast, map_sub (isArith_intCast R), toFun_sub]; rfl

@[simp] theorem cast_smul (a : ℤ) (v : V3 ℤ) : cast R (smul a v) = (a : R) • cast R v := by
  rw [cast, map_smul (isArith_intCast R), toFun_smul]; rfl

@[simp] theorem cast_cross (u v : V3 ℤ) : cast R (u.cross v) = cast R u ⨯₃ cast R v := by
  rw [cast, map_cross (isArith_intCast R), toFun_cross]; rfl

@[simp] theorem cast_dot (u v : V3 ℤ) : ((u.dot v : ℤ) : R) = cast R u ⬝ᵥ cast R v := by
  rw [map_dot (isArith_intCast R), dot_eq_dotProduct]; rfl

/-- Whether every component is zero. -/
def isZero (v : V3 ℤ) : Bool :=
  v.x == 0 && v.y == 0 && v.z == 0

theorem cast_eq_zero_of_isZero {v : V3 ℤ} (h : v.isZero = true) : cast R v = 0 := by
  simp only [isZero, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hx, hy⟩, hz⟩ := h
  funext i
  fin_cases i <;> simp [get, hx, hy, hz]

end Cast

end V3

namespace Q4

variable {α β R : Type*}

/-- The quaternion as a function `Fin 4 → α`. -/
def toFun (q : Q4 α) : Fin 4 → α := ![q.w, q.x, q.y, q.z]

/-- Componentwise image. -/
def map (f : α → β) (q : Q4 α) : Q4 β := ⟨f q.w, f q.x, f q.y, f q.z⟩

/-- The vector part. -/
def vec (q : Q4 α) : V3 α := ⟨q.x, q.y, q.z⟩

section Arith

variable [Add α] [Sub α] [Mul α]

/-- `p + q`. -/
def add (p q : Q4 α) : Q4 α := ⟨p.w + q.w, p.x + q.x, p.y + q.y, p.z + q.z⟩

/-- `a • q`. -/
def smul (a : α) (q : Q4 α) : Q4 α := ⟨a * q.w, a * q.x, a * q.y, a * q.z⟩

/-- `|q|² = q ⬝ᵥ q`. -/
def norm2 (q : Q4 α) : α := q.w * q.w + q.x * q.x + q.y * q.y + q.z * q.z

/-- The Hamilton product `p q` (`qmul`). -/
def mul (p q : Q4 α) : Q4 α :=
  ⟨p.w * q.w - p.x * q.x - p.y * q.y - p.z * q.z, p.w * q.x + p.x * q.w + p.y * q.z - p.z * q.y,
    p.w * q.y - p.x * q.z + p.y * q.w + p.z * q.x, p.w * q.z + p.x * q.y - p.y * q.x + p.z * q.w⟩

/-- `quatMatrix q *ᵥ v`, computed as `(w² - |q⃗|²) v + 2 (q⃗ ⬝ᵥ v) q⃗ + 2 w (q⃗ ⨯₃ v)`, with the
vector part `q⃗` of `q`. -/
def rotate (q : Q4 α) (v : V3 α) : V3 α :=
  let s := q.w * q.w - (q.x * q.x + q.y * q.y + q.z * q.z)
  let d := q.vec.dot v
  let c := q.vec.cross v
  let r : V3 α := ⟨d * q.x + q.w * c.x, d * q.y + q.w * c.y, d * q.z + q.w * c.z⟩
  ⟨s * v.x + (r.x + r.x), s * v.y + (r.y + r.y), s * v.z + (r.z + r.z)⟩

section Natural

variable [Add β] [Sub β] [Mul β] {f : α → β}

theorem map_add (hf : IsArith f) (p q : Q4 α) : (p.add q).map f = (p.map f).add (q.map f) := by
  simp [add, map, hf.map_add]

theorem map_smul (hf : IsArith f) (a : α) (q : Q4 α) :
    (smul a q).map f = smul (f a) (q.map f) := by
  simp [smul, map, hf.map_mul]

theorem map_norm2 (hf : IsArith f) (q : Q4 α) : f q.norm2 = (q.map f).norm2 := by
  simp [norm2, map, hf.map_add, hf.map_mul]

theorem map_mul (hf : IsArith f) (p q : Q4 α) : (p.mul q).map f = (p.map f).mul (q.map f) := by
  simp [mul, map, hf.map_add, hf.map_sub, hf.map_mul]

theorem map_rotate (hf : IsArith f) (q : Q4 α) (v : V3 α) :
    (q.rotate v).map f = (q.map f).rotate (v.map f) := by
  simp [rotate, vec, V3.dot, V3.cross, map, V3.map, hf.map_add, hf.map_sub, hf.map_mul]

end Natural

end Arith

section Ring

variable [CommRing R]

theorem toFun_add (p q : Q4 R) : (p.add q).toFun = p.toFun + q.toFun := by
  funext i; fin_cases i <;> rfl

theorem toFun_smul (a : R) (q : Q4 R) : (smul a q).toFun = a • q.toFun := by
  funext i; fin_cases i <;> rfl

theorem norm2_eq_dotProduct (q : Q4 R) : q.norm2 = q.toFun ⬝ᵥ q.toFun := by
  simp [norm2, toFun, dotProduct, Fin.sum_univ_four]

theorem toFun_mul (p q : Q4 R) : (p.mul q).toFun = qmul p.toFun q.toFun := by
  funext i; fin_cases i <;> rfl

theorem toFun_rotate (q : Q4 R) (v : V3 R) :
    (q.rotate v).toFun = quatMatrix q.toFun *ᵥ v.toFun := by
  funext i
  fin_cases i <;>
    simp [rotate, vec, V3.dot, V3.cross, V3.toFun, toFun, quatMatrix, mulVec, dotProduct,
      Fin.sum_univ_three] <;> ring

theorem cast_rotate (q : Q4 ℤ) (v : V3 ℤ) :
    V3.cast R (q.rotate v) = quatMatrix (q.map (Int.cast : ℤ → R)).toFun *ᵥ V3.cast R v := by
  rw [V3.cast, map_rotate (isArith_intCast R), toFun_rotate]
  rfl

theorem cast_norm2 (q : Q4 ℤ) :
    ((q.norm2 : ℤ) : R) = (q.map (Int.cast : ℤ → R)).toFun ⬝ᵥ (q.map (Int.cast : ℤ → R)).toFun := by
  rw [map_norm2 (isArith_intCast R), norm2_eq_dotProduct]

end Ring

end Q4

end Nieuwland.Check
