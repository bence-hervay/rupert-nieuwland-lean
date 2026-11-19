import Modules.Check.Number.Ball
import Modules.Check.Leaf.Vec
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Erased

/-!
# Exact arithmetic for checks

A body's coordinates lie in a real number field: the rationals, `ℚ(√d)` or `ℚ(θ)` for a root `θ`
of an exact polynomial in an isolating interval (`FieldSpec` in `code/src/math/scalar.rs`). After
scaling to a common denominator they lie in a ring of *exact values*. `Exact α` is what a check
needs from such a ring `α`:

* `+`, `-`, `*` and the integers (`Exact.ofInt`), with which checks compute;
* the value `Exact.re a` of each element, a map into `ℝ` that commutes with the operations
  (`Exact.isArith`), so that a computation over `α` maps to the same computation over `ℝ`
  (`Modules/Check/Number/Arith.lean`);
* sound tests: `pos a = true` only if `0 < re a`, `nonneg a = true` only if `0 ≤ re a`, and
  `isZero a = true` only if `re a = 0`.

A check written once over any `Exact α` is proved sound once, through `re`; a new field needs only
a new instance, with the proof that its tests agree with its values. The ring laws of `α` are never
needed. Instances: the integers (`re` is the cast), `ZSqrt d` for `ℤ[√d]` (exact and complete
tests by integer comparisons), and `ℤ[θ]` with an isolating interval (`Check/Theta.lean`).

The class holds the value as erased data (`Exact.reE`, `Erased ℝ`) and `Exact.re` reads it. No
check computes with it, and erasing it keeps the instances executable over irrational fields
(their values involve `√d` or a root, which Lean cannot compile), so the same checks also run as
compiled code.

## Main definitions

* `Nieuwland.Check.Exact`: the interface.
* `Nieuwland.Check.ZSqrt d`: `a + b √d` with integers `a`, `b`.
* `Nieuwland.Polyhedron.ofPoints`: the polyhedron spanned by points with exact coordinates.
-/

open Matrix

namespace Nieuwland.Check

/-- **Exact values** (module docs): a type with `+`, `-`, `*`, integer constants, a map `re` into
the reals that commutes with them (held as erased data, `reE`), and sound tests of sign and of
zero. -/
class Exact (α : Type) [Add α] [Sub α] [Mul α] where
  /-- The integer `n` as an exact value. -/
  ofInt : ℤ → α
  /-- The real value, erased (module docs); `Exact.re` reads it. -/
  reE : α → Erased ℝ
  /-- A sound test of `0 < re a`. -/
  pos : α → Bool
  /-- A sound test of `0 ≤ re a`. -/
  nonneg : α → Bool
  /-- A sound test of `re a = 0`. -/
  isZero : α → Bool
  /-- An enclosure of the real value (`Ball.Encl`): signs it decides need no exact arithmetic
  (`Modules/Check/Number/Ball.lean`). -/
  ball : α → Ball
  /-- Whether a check with a choice of route decides signs on balls first (`envelopeOk`,
  `Modules/Check/Leaf/Support.lean`): true where a product of exact values costs far more than one of
  integers, as over `ℤ[α]` (`Modules/Check/Number/Theta.lean`). Only speed depends on it. -/
  ballFirst : Bool := false
  /-- Whether compiled code checks the polynomials of balanced and centred supports by the sparse
  sign check first (`Balanced.checkAny`, `Modules/Check/Leaf/SupportSparse.lean`): true over `ℤ[√d]`,
  where it measured faster than `nonnegOn` (`notes/lean-perf.md`, row 6). Only speed depends on
  it. -/
  sparseFirst : Bool := false
  reE_add : ∀ a b, (reE (a + b)).out = (reE a).out + (reE b).out
  reE_sub : ∀ a b, (reE (a - b)).out = (reE a).out - (reE b).out
  reE_mul : ∀ a b, (reE (a * b)).out = (reE a).out * (reE b).out
  reE_ofInt : ∀ n, (reE (ofInt n)).out = n
  pos_sound' : ∀ a, pos a = true → 0 < (reE a).out
  nonneg_sound' : ∀ a, nonneg a = true → 0 ≤ (reE a).out
  isZero_sound' : ∀ a, isZero a = true → (reE a).out = 0
  ball_sound' : ∀ a, (ball a).Encl (reE a).out

namespace Exact

variable {α : Type} [Add α] [Sub α] [Mul α] [Exact α]

/-- The real value of an exact value. -/
noncomputable def re (a : α) : ℝ :=
  (reE a).out

theorem re_add (a b : α) : re (a + b) = re a + re b :=
  reE_add a b

theorem re_sub (a b : α) : re (a - b) = re a - re b :=
  reE_sub a b

theorem re_mul (a b : α) : re (a * b) = re a * re b :=
  reE_mul a b

theorem re_ofInt (n : ℤ) : re (ofInt n : α) = n :=
  reE_ofInt n

theorem pos_sound (a : α) (h : pos a = true) : 0 < re a :=
  pos_sound' a h

theorem nonneg_sound (a : α) (h : nonneg a = true) : 0 ≤ re a :=
  nonneg_sound' a h

theorem isZero_sound (a : α) (h : isZero a = true) : re a = 0 :=
  isZero_sound' a h

theorem ball_sound (a : α) : (ball a).Encl (re a) :=
  ball_sound' a

theorem isArith : IsArith (re : α → ℝ) :=
  ⟨re_add, re_sub, re_mul⟩

/-- A point with exact coordinates, as a point of `ℝ³`. -/
noncomputable def reV (v : V3 α) : Fin 3 → ℝ :=
  (v.map re).toFun

/-- The balls of the coordinates of a point. -/
def ballV (v : V3 α) : V3 Ball := v.map ball

theorem encl_ballV (v : V3 α) : (ballV v).Encl (reV v) :=
  ⟨ball_sound v.x, ball_sound v.y, ball_sound v.z⟩

theorem re_dot (u v : V3 α) : re (u.dot v) = reV u ⬝ᵥ reV v := by
  rw [V3.map_dot isArith, V3.dot_eq_dotProduct]
  rfl

theorem reV_cross (u v : V3 α) : reV (u.cross v) = reV u ⨯₃ reV v := by
  rw [reV, V3.map_cross isArith, V3.toFun_cross]
  rfl

theorem reV_add (u v : V3 α) : reV (u.add v) = reV u + reV v := by
  rw [reV, V3.map_add isArith, V3.toFun_add]
  rfl

theorem reV_sub (u v : V3 α) : reV (u.sub v) = reV u - reV v := by
  rw [reV, V3.map_sub isArith, V3.toFun_sub]
  rfl

theorem reV_smul (a : α) (v : V3 α) : reV (V3.smul a v) = re a • reV v := by
  rw [reV, V3.map_smul isArith, V3.toFun_smul]
  rfl

theorem reV_rotate (q : Q4 α) (v : V3 α) :
    reV (q.rotate v) = quatMatrix (q.map re).toFun *ᵥ reV v := by
  rw [reV, Q4.map_rotate isArith, Q4.toFun_rotate]
  rfl

theorem re_norm2 (q : Q4 α) : re q.norm2 = (q.map re).toFun ⬝ᵥ (q.map re).toFun := by
  rw [Q4.map_norm2 isArith, Q4.norm2_eq_dotProduct]

/-- A quaternion with exact coordinates, as a quaternion of `ℝ⁴`. -/
noncomputable def reQ (q : Q4 α) : Fin 4 → ℝ :=
  (q.map re).toFun

/-- A pre-rotation, if any, as a quaternion of `ℝ⁴`. -/
noncomputable def rePre (pre : Option (Q4 α)) : Option (Fin 4 → ℝ) :=
  pre.map reQ

@[simp] theorem rePre_none : rePre (none : Option (Q4 α)) = none :=
  rfl

/-- A pre-rotation is known not to be zero: its squared norm is known to be positive (`true`
without one). -/
def preOk : Option (Q4 α) → Bool
  | none => true
  | some c => pos c.norm2

theorem rePre_ne_zero {pre : Option (Q4 α)} (h : preOk pre = true) : ∀ c ∈ rePre pre, c ≠ 0 := by
  cases pre with
  | none => simp [rePre]
  | some c =>
    intro c' hc' h0
    simp only [rePre, Option.map_some, Option.mem_def, Option.some.injEq] at hc'
    have hpos := pos_sound _ (show pos c.norm2 = true from h)
    rw [re_norm2, ← reQ, hc', h0, dotProduct_zero] at hpos
    exact lt_irrefl _ hpos

/-- All three coordinates are known to be zero. -/
def isZeroV (v : V3 α) : Bool :=
  isZero v.x && isZero v.y && isZero v.z

theorem reV_eq_zero_of_isZeroV {v : V3 α} (h : isZeroV v = true) : reV v = 0 := by
  simp only [isZeroV, Bool.and_eq_true] at h
  funext i
  fin_cases i <;>
    simp [reV, V3.map, V3.toFun, isZero_sound _ h.1.1, isZero_sound _ h.1.2, isZero_sound _ h.2]

/-- Two points are known to be equal: their difference is known to be zero. -/
def eqV (u v : V3 α) : Bool :=
  isZeroV (u.sub v)

theorem reV_eq_of_eqV {u v : V3 α} (h : eqV u v = true) : reV u = reV v :=
  sub_eq_zero.mp ((reV_sub u v).symm.trans (reV_eq_zero_of_isZeroV h))

/-- A value is known not to be zero: one of `a`, `-a` is known to be positive. -/
def nonzero (a : α) : Bool :=
  pos a || pos (ofInt 0 - a)

theorem re_ne_zero_of_nonzero {a : α} (h : nonzero a = true) : re a ≠ 0 := by
  simp only [nonzero, Bool.or_eq_true] at h
  rcases h with h | h
  · exact (pos_sound a h).ne'
  · have := pos_sound _ h
    rw [re_sub, re_ofInt, Int.cast_zero] at this
    linarith

/-- A vector is known not to be zero: one of its coordinates is. -/
def nonzeroV (v : V3 α) : Bool :=
  nonzero v.x || nonzero v.y || nonzero v.z

theorem reV_ne_zero_of_nonzeroV {v : V3 α} (h : nonzeroV v = true) : reV v ≠ 0 := by
  simp only [nonzeroV, Bool.or_eq_true] at h
  intro h0
  rcases h with (h | h) | h
  · exact re_ne_zero_of_nonzero h (congrFun h0 0)
  · exact re_ne_zero_of_nonzero h (congrFun h0 1)
  · exact re_ne_zero_of_nonzero h (congrFun h0 2)

/-- The sum of a list. -/
def sumL (l : List α) : α := l.foldr (· + ·) (ofInt 0)

theorem re_sumL : ∀ l : List α, re (sumL l) = (l.map re).sum
  | [] => by simp [sumL, re_ofInt]
  | a :: l => by
    have hs : sumL (a :: l) = a + sumL l := rfl
    rw [hs, re_add, re_sumL l, List.map_cons, List.sum_cons]

theorem reV_map_ofInt (v : V3 ℤ) : reV (v.map (ofInt : ℤ → α)) = V3.cast ℝ v := by
  funext i
  fin_cases i <;> simp [reV, V3.map, V3.toFun, V3.cast, re_ofInt]

/-- A scaled point is a given point of `ℝ³` when its three coordinates are: generated files prove
one such identity per point and coordinate, so that no declaration grows with the body. -/
theorem smul_reV_eq {c x y z : ℝ} {v : V3 α} (hx : c * re v.x = x) (hy : c * re v.y = y)
    (hz : c * re v.z = z) : c • reV v = ![x, y, z] := by
  subst hx hy hz
  funext i
  fin_cases i <;> rfl

end Exact

/-! ### The integers -/

/-- `0 < a`, read off the constructor of `a` (a few steps for the kernel). -/
def intPos : ℤ → Bool
  | .ofNat n => Nat.blt 0 n
  | .negSucc _ => false

/-- `0 ≤ a`, read off the constructor of `a`. -/
def intNonneg : ℤ → Bool
  | .ofNat _ => true
  | .negSucc _ => false

/-- `a = 0`, read off the constructor of `a`. -/
def intIsZero : ℤ → Bool
  | .ofNat n => Nat.beq n 0
  | .negSucc _ => false

/-- The integers: the value is the cast, and the tests are exact. -/
instance : Exact ℤ where
  ofInt n := n
  reE n := Erased.mk (n : ℝ)
  pos := intPos
  nonneg := intNonneg
  isZero := intIsZero
  ball := Ball.ofInt
  reE_add a b := by simp only [Erased.out_mk]; exact Int.cast_add a b
  reE_sub a b := by simp only [Erased.out_mk]; exact Int.cast_sub a b
  reE_mul a b := by simp only [Erased.out_mk]; exact Int.cast_mul a b
  reE_ofInt _ := Erased.out_mk _
  pos_sound' a h := by
    rw [Erased.out_mk]
    cases a with
    | ofNat n =>
      have : 0 < n := by simpa only [intPos, Nat.blt_eq] using h
      change (0 : ℝ) < ((Int.ofNat n : ℤ) : ℝ)
      rw [Int.ofNat_eq_natCast, Int.cast_natCast]
      exact_mod_cast this
    | negSucc n => cases h
  nonneg_sound' a h := by
    rw [Erased.out_mk]
    cases a with
    | ofNat n =>
      rw [Int.ofNat_eq_natCast, Int.cast_natCast]
      exact Nat.cast_nonneg n
    | negSucc n => cases h
  isZero_sound' a h := by
    rw [Erased.out_mk]
    cases a with
    | ofNat n =>
      have : n = 0 := Nat.eq_of_beq_eq_true h
      change ((Int.ofNat n : ℤ) : ℝ) = 0
      simp [this]
    | negSucc n => cases h
  ball_sound' a := by rw [Erased.out_mk]; exact Ball.encl_ofInt a

@[simp] theorem Exact.re_int (n : ℤ) : Exact.re n = (n : ℝ) :=
  Erased.out_mk _

theorem Exact.reV_int (v : V3 ℤ) : Exact.reV v = V3.cast ℝ v := by
  funext i
  fin_cases i <;> simp [Exact.reV, V3.map, V3.toFun, V3.cast]

/-! ### Quadratic integers -/

/-- `a + b √d` with integers `a`, `b`: the elements of `ℤ[√d]` (for a body over `ℚ(√d)`, its
coordinates times a common denominator). The value takes the positive square root. -/
structure ZSqrt (d : ℕ) where
  /-- The rational part. -/
  a : ℤ
  /-- The coefficient of `√d`. -/
  b : ℤ

namespace ZSqrt

variable {d : ℕ}

instance : Add (ZSqrt d) := ⟨fun x y ↦ ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Sub (ZSqrt d) := ⟨fun x y ↦ ⟨x.a - y.a, x.b - y.b⟩⟩
instance : Mul (ZSqrt d) := ⟨fun x y ↦ ⟨x.a * y.a + d * (x.b * y.b), x.a * y.b + x.b * y.a⟩⟩

theorem add_def (x y : ZSqrt d) : x + y = ⟨x.a + y.a, x.b + y.b⟩ := rfl
theorem sub_def (x y : ZSqrt d) : x - y = ⟨x.a - y.a, x.b - y.b⟩ := rfl
theorem mul_def (x y : ZSqrt d) : x * y = ⟨x.a * y.a + d * (x.b * y.b), x.a * y.b + x.b * y.a⟩ :=
  rfl

/-- The value `a + b √d`. -/
noncomputable def re (x : ZSqrt d) : ℝ :=
  x.a + x.b * √(d : ℝ)

/-- `0 < a + b √d`, by integer comparisons: with both parts of one sign the sign is clear, and
otherwise the larger of `a²` and `b² d` decides. -/
def pos (x : ZSqrt d) : Bool :=
  if 0 ≤ x.a then
    if 0 ≤ x.b then 0 < x.a || (0 < x.b && 0 < d) else x.b * x.b * d < x.a * x.a
  else 0 < x.b && x.a * x.a < x.b * x.b * d

/-- `0 ≤ a + b √d`, by integer comparisons. -/
def nonneg (x : ZSqrt d) : Bool :=
  if 0 ≤ x.a then 0 ≤ x.b || x.b * x.b * d ≤ x.a * x.a
  else 0 < x.b && x.a * x.a ≤ x.b * x.b * d

theorem sqrt_facts (d : ℕ) : 0 ≤ √(d : ℝ) ∧ √(d : ℝ) * √(d : ℝ) = d :=
  ⟨Real.sqrt_nonneg _, Real.mul_self_sqrt (Nat.cast_nonneg _)⟩

/-- `⌊2^64 √d⌋`. -/
def sqrtApx (d : ℕ) : ℕ := Nat.sqrt (d * 2 ^ 128)

theorem sqrtApx_le (d : ℕ) : (sqrtApx d : ℝ) ≤ 2 ^ 64 * √(d : ℝ) ∧
    2 ^ 64 * √(d : ℝ) < sqrtApx d + 1 := by
  have e : (2 : ℝ) ^ 64 * √(d : ℝ) = √((d * 2 ^ 128 : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul (Nat.cast_nonneg _),
      show ((2 : ℕ) : ℝ) ^ 128 = (2 ^ 64) ^ 2 by norm_num, Real.sqrt_sq (by positivity), mul_comm]
  rw [e]
  constructor
  · refine Real.le_sqrt_of_sq_le ?_
    exact_mod_cast Nat.sqrt_le' (d * 2 ^ 128)
  · rw [Real.sqrt_lt' (by positivity)]
    exact_mod_cast Nat.lt_succ_sqrt' (d * 2 ^ 128)

/-- The ball of `a + b √d` from an approximation `s` of `2^64 √d`: `2^64 a + b s`, with radius
`|b|`, sound for `s = ⌊2^64 √d⌋` (`ballS_sound`). The instance takes `ballS (sqrtApx d)`, so
compiled code computes the square root once, when it builds the instance. -/
def ballS (s : ℤ) (x : ZSqrt d) : Ball := ⟨2 ^ 64 * x.a + x.b * s, x.b.natAbs, 64⟩

theorem ballS_sound (x : ZSqrt d) : (ballS (sqrtApx d : ℤ) x).Encl (re x) := by
  obtain ⟨h1, h2⟩ := sqrtApx_le d
  simp only [ballS, Ball.Encl, re]
  have : (2 : ℝ) ^ 64 * (x.a + x.b * √(d : ℝ)) - ((2 ^ 64 * x.a + x.b * (sqrtApx d : ℤ) : ℤ) : ℝ) =
      x.b * (2 ^ 64 * √(d : ℝ) - sqrtApx d) := by push_cast; ring
  rw [this, abs_mul, Nat.cast_natAbs, Int.cast_abs]
  refine mul_le_of_le_one_right (abs_nonneg _) ?_
  rw [abs_le]
  constructor <;> linarith

theorem pos_sound (x : ZSqrt d) (h : pos x = true) : 0 < re x := by
  obtain ⟨hs, hss⟩ := sqrt_facts d
  obtain ⟨a, b⟩ := x
  simp only [re]
  unfold pos at h
  split_ifs at h with ha hb
  · simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
    rcases h with h | ⟨h, hd⟩
    · have : (0 : ℝ) < a := by exact_mod_cast h
      have : (0 : ℝ) ≤ b := by exact_mod_cast hb
      positivity
    · have hd' : (0 : ℝ) < √(d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
      have : (0 : ℝ) ≤ a := by exact_mod_cast ha
      have : (0 : ℝ) < b := by exact_mod_cast h
      positivity
  · simp only [decide_eq_true_eq] at h
    have h' : (b : ℝ) * b * d < a * a := by exact_mod_cast h
    have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
    have hb' : (b : ℝ) < 0 := by exact_mod_cast not_le.mp hb
    nlinarith [mul_nonneg (neg_nonneg.mpr hb'.le) hs]
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hb, h⟩ := h
    have h' : (a : ℝ) * a < b * b * d := by exact_mod_cast h
    have ha' : (a : ℝ) < 0 := by exact_mod_cast not_le.mp ha
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    nlinarith [mul_nonneg hb'.le hs]

theorem nonneg_sound (x : ZSqrt d) (h : nonneg x = true) : 0 ≤ re x := by
  obtain ⟨hs, hss⟩ := sqrt_facts d
  obtain ⟨a, b⟩ := x
  simp only [re]
  unfold nonneg at h
  split_ifs at h with ha
  · simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
    rcases h with hb | h
    · have : (0 : ℝ) ≤ b := by exact_mod_cast hb
      positivity
    · have h' : (b : ℝ) * b * d ≤ a * a := by exact_mod_cast h
      by_cases hb : (0 : ℝ) ≤ b
      · positivity
      · nlinarith [mul_nonneg (neg_nonneg.mpr (not_le.mp hb).le) hs]
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hb, h⟩ := h
    have h' : (a : ℝ) * a ≤ b * b * d := by exact_mod_cast h
    have ha' : (a : ℝ) < 0 := by exact_mod_cast not_le.mp ha
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    nlinarith [mul_nonneg hb'.le hs]

/-- `ℤ[√d]` as exact values. -/
instance : Exact (ZSqrt d) where
  ofInt n := ⟨n, 0⟩
  reE x := Erased.mk (re x)
  pos := pos
  nonneg := nonneg
  isZero x := x.a == 0 && x.b == 0
  ball := ballS (sqrtApx d : ℤ)
  sparseFirst := true
  reE_add x y := by simp only [Erased.out_mk, re, add_def]; push_cast; ring
  reE_sub x y := by simp only [Erased.out_mk, re, sub_def]; push_cast; ring
  reE_mul x y := by
    simp only [Erased.out_mk, re, mul_def]
    push_cast
    linear_combination (-(x.b : ℝ) * y.b) * (sqrt_facts d).2
  reE_ofInt n := by simp [re]
  pos_sound' x h := by rw [Erased.out_mk]; exact pos_sound x h
  nonneg_sound' x h := by rw [Erased.out_mk]; exact nonneg_sound x h
  isZero_sound' x h := by
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    simp [re, h.1, h.2]
  ball_sound' x := by rw [Erased.out_mk]; exact ballS_sound x

theorem re_eq (x : ZSqrt d) : Exact.re x = re x :=
  Erased.out_mk _

@[simp] theorem re_mk (a b : ℤ) : Exact.re (⟨a, b⟩ : ZSqrt d) = a + b * √(d : ℝ) :=
  Erased.out_mk _

end ZSqrt

end Nieuwland.Check

namespace Nieuwland

open Classical in
/-- The polyhedron spanned by points with exact coordinates. -/
noncomputable def Polyhedron.ofPoints {α : Type} [Add α] [Sub α] [Mul α] [Check.Exact α]
    (pts : List (Check.V3 α)) : Polyhedron where
  vertices := (pts.map Check.Exact.reV).toFinset

theorem Polyhedron.mem_ofPoints {α : Type} [Add α] [Sub α] [Mul α] [Check.Exact α]
    {pts : List (Check.V3 α)} {x : Fin 3 → ℝ} :
    x ∈ (ofPoints pts).vertices ↔ ∃ v ∈ pts, Check.Exact.reV v = x := by
  simp [ofPoints]

end Nieuwland
