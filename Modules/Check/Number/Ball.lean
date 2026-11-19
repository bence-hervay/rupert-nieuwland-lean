import Modules.Check.Leaf.Vec

/-!
# Balls: integer enclosures of real numbers

A ball `⟨m, r, s⟩` encloses the real numbers `x` with `|2^s x - m| ≤ r` (`Ball.Encl`). Sums,
differences and products of balls enclose the sums, differences and products of what they enclose
(`Ball.encl_add`, `Ball.encl_sub`, `Ball.encl_mul`), by integer arithmetic only; a ball with
`r < m` encloses only positive numbers (`Ball.pos_sound`), one with `r ≤ m` only nonnegative ones
(`Ball.nonneg_sound`) and one with `m < -r` only negative ones (`Ball.neg_sound`). Vectors of balls
(`V3 Ball`) use the generic vector operations (`V3.Encl.dot`, `V3.Encl.cross`, `V3.Encl.sub`).

Every exact value has a ball (`Exact.ball`, `Modules/Check/Number/Exact.lean`): its integer itself, or
over a number field its coordinates times approximations `2^64 αʲ` of the powers of the root
(`Modules/Check/Number/Theta.lean`), which decides the sign of every value that is not within about
`2^-58` of `0`, relative to its coordinates, with a few integer products. Checks decide signs by
balls first where the exact values would cost products in the field, as Rust's checker encloses
the points in `f64` intervals once (`regional.rs`, `envelope_valid`), and exactly where a ball
leaves the sign open (`envelopeOk`, `Modules/Check/Leaf/Support.lean`).
-/

open Matrix

namespace Nieuwland.Check

/-- A ball: the real numbers `x` with `|2^s x - m| ≤ r` (`Ball.Encl`). -/
structure Ball where
  /-- The centre, times `2^s`. -/
  m : ℤ
  /-- The radius, times `2^s`. -/
  r : ℕ
  /-- The scale. -/
  s : ℕ

namespace Ball

instance : Inhabited Ball := ⟨⟨0, 0, 0⟩⟩

/-- `b` encloses `x`. -/
def Encl (b : Ball) (x : ℝ) : Prop :=
  |(2 : ℝ) ^ b.s * x - b.m| ≤ b.r

/-- The same ball at the scale `2^(s + k)`. -/
def up (b : Ball) (k : ℕ) : Ball :=
  ⟨b.m * 2 ^ k, b.r * 2 ^ k, b.s + k⟩

/-- The sum, at the larger scale. -/
def add (a b : Ball) : Ball :=
  if a.s = b.s then ⟨a.m + b.m, a.r + b.r, a.s⟩
  else
    let a' := a.up (max a.s b.s - a.s)
    let b' := b.up (max a.s b.s - b.s)
    ⟨a'.m + b'.m, a'.r + b'.r, max a.s b.s⟩

/-- The negation. -/
def neg (a : Ball) : Ball := ⟨-a.m, a.r, a.s⟩

/-- The difference, at the larger scale. -/
def sub (a b : Ball) : Ball := a.add b.neg

/-- The product, at the sum of the scales. -/
def mul (a b : Ball) : Ball :=
  ⟨a.m * b.m, a.m.natAbs * b.r + b.m.natAbs * a.r + a.r * b.r, a.s + b.s⟩

instance : Add Ball := ⟨add⟩
instance : Sub Ball := ⟨sub⟩
instance : Mul Ball := ⟨mul⟩

/-- Only positive numbers lie in the ball. -/
def isPos (b : Ball) : Bool := decide ((b.r : ℤ) < b.m)

/-- Only nonnegative numbers lie in the ball. -/
def isNonneg (b : Ball) : Bool := decide ((b.r : ℤ) ≤ b.m)

/-- Only negative numbers lie in the ball. -/
def isNeg (b : Ball) : Bool := decide (b.m < -(b.r : ℤ))

theorem encl_up {b : Ball} {x : ℝ} (h : b.Encl x) (k : ℕ) : (b.up k).Encl x := by
  unfold Encl up at *
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have : (2 : ℝ) ^ (b.s + k) * x - ((b.m * 2 ^ k : ℤ) : ℝ) = 2 ^ k * (2 ^ b.s * x - b.m) := by
    push_cast; ring
  rw [this, abs_mul, abs_of_pos h2]
  push_cast
  nlinarith

theorem encl_add_same {a b : Ball} {x y : ℝ} (ha : a.Encl x) (hb : b.Encl y) (hs : a.s = b.s) :
    Ball.Encl ⟨a.m + b.m, a.r + b.r, a.s⟩ (x + y) := by
  unfold Encl at *
  rw [← hs] at hb
  have : (2 : ℝ) ^ a.s * (x + y) - ((a.m + b.m : ℤ) : ℝ) =
      (2 ^ a.s * x - a.m) + (2 ^ a.s * y - b.m) := by push_cast; ring
  rw [this]
  push_cast
  exact (abs_add_le _ _).trans (add_le_add ha hb)

theorem encl_add {a b : Ball} {x y : ℝ} (ha : a.Encl x) (hb : b.Encl y) :
    (a + b).Encl (x + y) := by
  change (add a b).Encl (x + y)
  unfold add
  split_ifs with hs
  · exact encl_add_same ha hb hs
  · have ha' := encl_up ha (max a.s b.s - a.s)
    have hb' := encl_up hb (max a.s b.s - b.s)
    have h1 : (a.up (max a.s b.s - a.s)).s = max a.s b.s := by simp only [up]; omega
    have h2 : (b.up (max a.s b.s - b.s)).s = max a.s b.s := by simp only [up]; omega
    have := encl_add_same ha' hb' (h1.trans h2.symm)
    rwa [h1] at this

theorem encl_neg {a : Ball} {x : ℝ} (ha : a.Encl x) : a.neg.Encl (-x) := by
  unfold Encl neg at *
  have : (2 : ℝ) ^ a.s * -x - ((-a.m : ℤ) : ℝ) = -(2 ^ a.s * x - a.m) := by push_cast; ring
  rwa [this, abs_neg]

theorem encl_sub {a b : Ball} {x y : ℝ} (ha : a.Encl x) (hb : b.Encl y) :
    (a - b).Encl (x - y) := by
  change (add a b.neg).Encl (x - y)
  rw [sub_eq_add_neg]
  exact encl_add ha (encl_neg hb)

theorem encl_mul {a b : Ball} {x y : ℝ} (ha : a.Encl x) (hb : b.Encl y) :
    (a * b).Encl (x * y) := by
  change (mul a b).Encl (x * y)
  unfold Encl mul at *
  set X := (2 : ℝ) ^ a.s * x
  set Y := (2 : ℝ) ^ b.s * y
  have key : (2 : ℝ) ^ (a.s + b.s) * (x * y) - ((a.m * b.m : ℤ) : ℝ) =
      (X - a.m) * (Y - b.m) + (a.m : ℝ) * (Y - b.m) + (b.m : ℝ) * (X - a.m) := by
    simp only [X, Y]; push_cast; ring
  rw [key]
  have e1 : |(X - a.m) * (Y - b.m)| ≤ (a.r : ℝ) * b.r := by
    rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) (Nat.cast_nonneg _)
  have e2 : |(a.m : ℝ) * (Y - b.m)| ≤ (a.m.natAbs : ℝ) * b.r := by
    rw [abs_mul, Nat.cast_natAbs, Int.cast_abs]
    exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
  have e3 : |(b.m : ℝ) * (X - a.m)| ≤ (b.m.natAbs : ℝ) * a.r := by
    rw [abs_mul, Nat.cast_natAbs, Int.cast_abs]
    exact mul_le_mul_of_nonneg_left ha (abs_nonneg _)
  push_cast
  calc |(X - a.m) * (Y - b.m) + (a.m : ℝ) * (Y - b.m) + (b.m : ℝ) * (X - a.m)|
      ≤ |(X - a.m) * (Y - b.m)| + |(a.m : ℝ) * (Y - b.m)| + |(b.m : ℝ) * (X - a.m)| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ ≤ _ := by linarith

theorem pos_sound {b : Ball} {x : ℝ} (h : b.Encl x) (hp : b.isPos = true) : 0 < x := by
  unfold Encl at h
  unfold isPos at hp
  have hp' : ((b.r : ℤ) : ℝ) < b.m := by exact_mod_cast of_decide_eq_true hp
  have := (abs_le.mp h).1
  have h2 : (0 : ℝ) < 2 ^ b.s := by positivity
  push_cast at hp'
  have : 0 < (2 : ℝ) ^ b.s * x := by linarith
  exact pos_of_mul_pos_right this h2.le

theorem nonneg_sound {b : Ball} {x : ℝ} (h : b.Encl x) (hp : b.isNonneg = true) : 0 ≤ x := by
  unfold Encl at h
  unfold isNonneg at hp
  have hp' : ((b.r : ℤ) : ℝ) ≤ b.m := by exact_mod_cast of_decide_eq_true hp
  have := (abs_le.mp h).1
  have h2 : (0 : ℝ) < 2 ^ b.s := by positivity
  push_cast at hp'
  have : 0 ≤ (2 : ℝ) ^ b.s * x := by linarith
  exact nonneg_of_mul_nonneg_right (by linarith) h2

theorem neg_sound {b : Ball} {x : ℝ} (h : b.Encl x) (hn : b.isNeg = true) : x < 0 := by
  unfold Encl at h
  unfold isNeg at hn
  have hn' : (b.m : ℝ) < -((b.r : ℤ) : ℝ) := by exact_mod_cast of_decide_eq_true hn
  have := (abs_le.mp h).2
  have h2 : (0 : ℝ) < 2 ^ b.s := by positivity
  push_cast at hn'
  have : (2 : ℝ) ^ b.s * x < 0 := by linarith
  exact neg_of_mul_neg_right this h2.le

/-- The ball of an integer: the integer itself, with radius `0`. -/
def ofInt (a : ℤ) : Ball := ⟨a, 0, 0⟩

theorem encl_ofInt (a : ℤ) : (ofInt a).Encl a := by
  simp [Encl, ofInt]

end Ball

/-! ### Balls of computations -/

/-- A ball of a computation's value (`PBall.Holds`): a centre `m` in `α` at scale `2^s`, with
bounds `r` on the error and `b` on the centre, both at that scale. The centre is a packed integer
in compiled code (`Modules/Check/Sign/Box.lean`), an expression or a real number in proofs. The scale
and the bounds are computed alongside, whatever `α` is (`PBall.map`). -/
structure PBall (α : Type) where
  /-- The centre, times `2^s`. -/
  m : α
  /-- The scale. -/
  s : ℕ
  /-- The error bound, times `2^s`. -/
  r : ℕ
  /-- The bound on the centre. -/
  b : ℕ

namespace PBall

variable {α β : Type} [Add α] [Sub α] [Mul α] [IntCast α] [Add β] [Sub β] [Mul β] [IntCast β]

/-- The same ball at the scale `2^(s + k)`. -/
def up (p : PBall α) (k : ℕ) : PBall α :=
  if k = 0 then p else ⟨((2 ^ k : ℤ) : α) * p.m, p.s + k, p.r * 2 ^ k, p.b * 2 ^ k⟩

/-- The sum, at the larger scale. -/
def add (p q : PBall α) : PBall α :=
  let t := max p.s q.s
  let p' := p.up (t - p.s)
  let q' := q.up (t - q.s)
  ⟨p'.m + q'.m, t, p'.r + q'.r, p'.b + q'.b⟩

/-- The difference, at the larger scale. -/
def sub (p q : PBall α) : PBall α :=
  let t := max p.s q.s
  let p' := p.up (t - p.s)
  let q' := q.up (t - q.s)
  ⟨p'.m - q'.m, t, p'.r + q'.r, p'.b + q'.b⟩

/-- The product, at the sum of the scales. -/
def mul (p q : PBall α) : PBall α :=
  ⟨p.m * q.m, p.s + q.s, (p.b + p.r) * q.r + q.b * p.r, p.b * q.b⟩

instance : Add (PBall α) := ⟨add⟩
instance : Sub (PBall α) := ⟨sub⟩
instance : Mul (PBall α) := ⟨mul⟩

/-- The ball of a constant with the ball `c`; at scale `1` when `c` is an exact integer, so that
integer constants of a number field do not raise the scale. -/
def ofBall (c : Ball) : PBall α :=
  if c.r = 0 ∧ c.m % 2 ^ c.s = 0 then ⟨((c.m / 2 ^ c.s : ℤ) : α), 0, 0, (c.m / 2 ^ c.s).natAbs⟩
  else ⟨(c.m : α), c.s, c.r, c.m.natAbs⟩

/-- An exact input `x`, with the bound `b` on it. -/
def exact (x : α) (b : ℕ) : PBall α := ⟨x, 0, 0, b⟩

/-- The centre mapped by `f`. -/
def map (f : α → β) (p : PBall α) : PBall β := ⟨f p.m, p.s, p.r, p.b⟩

theorem map_up {f : α → β} (hf : IsArith f) (hc : ∀ z : ℤ, f z = z) (p : PBall α) (k : ℕ) :
    (p.up k).map f = (p.map f).up k := by
  unfold up map
  split_ifs
  · rfl
  · simp only [hf.map_mul, hc]

/-- Maps of the centres that commute with the operations and fix the integers commute with the
operations on balls. -/
theorem isArith_map {f : α → β} (hf : IsArith f) (hc : ∀ z : ℤ, f z = z) :
    IsArith (map f : PBall α → PBall β) := by
  refine ⟨fun p q ↦ ?_, fun p q ↦ ?_, fun p q ↦ ?_⟩
  · change (add p q).map f = add (p.map f) (q.map f)
    simp only [add]
    rw [← map_up hf hc p, ← map_up hf hc q]
    simp only [map, hf.map_add]
  · change (sub p q).map f = sub (p.map f) (q.map f)
    simp only [sub]
    rw [← map_up hf hc p, ← map_up hf hc q]
    simp only [map, hf.map_sub]
  · change (mul p q).map f = mul (p.map f) (q.map f)
    simp only [mul, map, hf.map_mul]

omit [Add α] [Sub α] [Mul α] [Add β] [Sub β] [Mul β] in
theorem map_ofBall {f : α → β} (hc : ∀ z : ℤ, f z = z) (c : Ball) :
    (ofBall c : PBall α).map f = ofBall c := by
  unfold ofBall
  split_ifs <;> simp only [map, hc]

omit [Add α] [Sub α] [Add β] [Sub β] [Mul β] [IntCast β] in
theorem up_s (p : PBall α) (k : ℕ) : (p.up k).s = p.s + k := by
  unfold up
  split_ifs with h
  · simp [h]
  · rfl

/-- `p` encloses the real number `v`: `|2^s v - m| ≤ r`, and `|m| ≤ b`. -/
def Holds (v : ℝ) (p : PBall ℝ) : Prop :=
  |2 ^ p.s * v - p.m| ≤ p.r ∧ |p.m| ≤ p.b

theorem holds_up {v : ℝ} {p : PBall ℝ} (h : Holds v p) (k : ℕ) : Holds v (p.up k) := by
  unfold up
  split_ifs
  · exact h
  · obtain ⟨h1, h2⟩ := h
    have hk : (0 : ℝ) < 2 ^ k := by positivity
    refine ⟨?_, ?_⟩
    · have e : (2 : ℝ) ^ (p.s + k) * v - (((2 ^ k : ℤ) : ℝ) * p.m) =
          2 ^ k * (2 ^ p.s * v - p.m) := by push_cast; ring
      simp only [e, abs_mul, abs_of_pos hk]
      push_cast
      nlinarith
    · simp only [abs_mul]
      push_cast
      rw [abs_of_pos hk]
      nlinarith

theorem holds_add {v w : ℝ} {p q : PBall ℝ} (hp : Holds v p) (hq : Holds w q) :
    Holds (v + w) (p + q) := by
  change Holds (v + w) (add p q)
  have hp' := holds_up hp (max p.s q.s - p.s)
  have hq' := holds_up hq (max p.s q.s - q.s)
  have e1 : (p.up (max p.s q.s - p.s)).s = max p.s q.s := by rw [up_s]; omega
  have e2 : (q.up (max p.s q.s - q.s)).s = max p.s q.s := by rw [up_s]; omega
  obtain ⟨a1, a2⟩ := hp'
  obtain ⟨b1, b2⟩ := hq'
  rw [e1] at a1
  rw [e2] at b1
  refine ⟨?_, ?_⟩
  · simp only [add]
    push_cast
    calc |2 ^ max p.s q.s * (v + w) - ((p.up (max p.s q.s - p.s)).m + (q.up (max p.s q.s - q.s)).m)|
        = |(2 ^ max p.s q.s * v - (p.up (max p.s q.s - p.s)).m) +
            (2 ^ max p.s q.s * w - (q.up (max p.s q.s - q.s)).m)| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add a1 b1)
  · simp only [add]
    push_cast
    exact (abs_add_le _ _).trans (add_le_add a2 b2)

theorem holds_sub {v w : ℝ} {p q : PBall ℝ} (hp : Holds v p) (hq : Holds w q) :
    Holds (v - w) (p - q) := by
  change Holds (v - w) (sub p q)
  have hp' := holds_up hp (max p.s q.s - p.s)
  have hq' := holds_up hq (max p.s q.s - q.s)
  have e1 : (p.up (max p.s q.s - p.s)).s = max p.s q.s := by rw [up_s]; omega
  have e2 : (q.up (max p.s q.s - q.s)).s = max p.s q.s := by rw [up_s]; omega
  obtain ⟨a1, a2⟩ := hp'
  obtain ⟨b1, b2⟩ := hq'
  rw [e1] at a1
  rw [e2] at b1
  refine ⟨?_, ?_⟩
  · simp only [sub]
    push_cast
    calc |2 ^ max p.s q.s * (v - w) - ((p.up (max p.s q.s - p.s)).m - (q.up (max p.s q.s - q.s)).m)|
        = |(2 ^ max p.s q.s * v - (p.up (max p.s q.s - p.s)).m) -
            (2 ^ max p.s q.s * w - (q.up (max p.s q.s - q.s)).m)| := by ring_nf
      _ ≤ _ := (abs_sub _ _).trans (add_le_add a1 b1)
  · simp only [sub]
    push_cast
    exact (abs_sub _ _).trans (add_le_add a2 b2)

theorem holds_mul {v w : ℝ} {p q : PBall ℝ} (hp : Holds v p) (hq : Holds w q) :
    Holds (v * w) (p * q) := by
  change Holds (v * w) (mul p q)
  obtain ⟨a1, a2⟩ := hp
  obtain ⟨b1, b2⟩ := hq
  simp only [Holds, mul]
  push_cast
  have hv : |2 ^ p.s * v| ≤ (p.b : ℝ) + p.r := by
    have := abs_sub_abs_le_abs_sub (2 ^ p.s * v) p.m
    linarith
  refine ⟨?_, ?_⟩
  · have e : (2 : ℝ) ^ (p.s + q.s) * (v * w) - p.m * q.m =
        (2 ^ p.s * v) * (2 ^ q.s * w - q.m) + q.m * (2 ^ p.s * v - p.m) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul (2 ^ p.s * v), abs_mul (q.m : ℝ)]
    have t1 := mul_le_mul hv b1 (abs_nonneg _) (by positivity)
    have t2 := mul_le_mul b2 a1 (abs_nonneg _) (by positivity)
    linarith
  · rw [abs_mul]
    exact mul_le_mul a2 b2 (abs_nonneg _) (by positivity)

theorem holds_ofBall {c : Ball} {v : ℝ} (h : c.Encl v) : Holds v (ofBall c) := by
  unfold ofBall
  split_ifs with hc
  · obtain ⟨hr, hm⟩ := hc
    have h0 : (2 : ℝ) ^ c.s * v = c.m := by
      have := h
      rw [Ball.Encl, hr, Nat.cast_zero] at this
      linarith [abs_nonneg ((2 : ℝ) ^ c.s * v - c.m), abs_le.mp this]
    have hq : c.m = 2 ^ c.s * (c.m / 2 ^ c.s) :=
      (Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hm)).symm
    have hv : v = ((c.m / 2 ^ c.s : ℤ) : ℝ) := by
      have h2 : (2 : ℝ) ^ c.s ≠ 0 := by positivity
      apply mul_left_cancel₀ h2
      rw [h0]
      exact_mod_cast hq
    refine ⟨?_, ?_⟩
    · simp [hv]
    · simp [Nat.cast_natAbs]
  · exact ⟨h, by simp [Nat.cast_natAbs]⟩

theorem holds_exact {x : ℝ} {b : ℕ} (h : |x| ≤ b) : Holds x (exact x b) :=
  ⟨by simp [exact], h⟩

end PBall

namespace V3

/-- Each component of the vector of balls `b` encloses that of `v`. -/
def Encl (b : V3 Ball) (v : Fin 3 → ℝ) : Prop :=
  b.x.Encl (v 0) ∧ b.y.Encl (v 1) ∧ b.z.Encl (v 2)

namespace Encl

variable {a b : V3 Ball} {u v : Fin 3 → ℝ}

theorem sub (ha : a.Encl u) (hb : b.Encl v) : (a.sub b).Encl (u - v) :=
  ⟨Ball.encl_sub ha.1 hb.1, Ball.encl_sub ha.2.1 hb.2.1, Ball.encl_sub ha.2.2 hb.2.2⟩

theorem dot (ha : a.Encl u) (hb : b.Encl v) : (a.dot b).Encl (u ⬝ᵥ v) := by
  have := Ball.encl_add (Ball.encl_add (Ball.encl_mul ha.1 hb.1) (Ball.encl_mul ha.2.1 hb.2.1))
    (Ball.encl_mul ha.2.2 hb.2.2)
  have e : u ⬝ᵥ v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
    simp [dotProduct, Fin.sum_univ_three]
  rw [e]
  exact this

theorem cross (ha : a.Encl u) (hb : b.Encl v) : (a.cross b).Encl (u ⨯₃ v) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · exact Ball.encl_sub (Ball.encl_mul ha.2.1 hb.2.2) (Ball.encl_mul ha.2.2 hb.2.1)
  · exact Ball.encl_sub (Ball.encl_mul ha.2.2 hb.1) (Ball.encl_mul ha.1 hb.2.2)
  · exact Ball.encl_sub (Ball.encl_mul ha.1 hb.2.1) (Ball.encl_mul ha.2.1 hb.1)

end Encl

end V3

end Nieuwland.Check
