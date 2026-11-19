import Modules.Root.System

/-!
# Affine forms

A ball evaluation of a polynomial on a box forgets that two occurrences of a variable are the
same number: its width is first order in the box's width with the absolute values of every
term's coefficient, without the cancellations between terms. On the touch leaf of a root
(`Modules/Root/Leaf.lean`) that costs a factor of several in the box's width, in each of five
coordinates.

An affine form `c + ∑ l_k δ_k + e` in `n` variables `δ_k ∈ [-1, 1]` keeps the first-order part
exactly: `c`, the `l_k` and `e` are balls, sums add coefficient by coefficient (so first-order
terms cancel as they do in the polynomial), and a product puts its second-order part into `e`.
Evaluated on the box (`Aff.toBall`), a form's width is first order with the true coefficients,
plus second-order terms: the enclosure of a polynomial expanded about the box's centre, to first
order (the Rust checker expands to every order, `code/src/proof/d2/ivl.rs`).

The balls of a form are kept at a scale of at most `2^p` (`Ball'.trim`: the centre rounded down,
the radius up), `p` a parameter of the type: a ball product adds the scales of its factors, and
the forms of a touch leaf would otherwise carry mantissas of tens of thousands of bits.

`Enc` is the common interface of balls and affine forms (ring operations and an integer), and
`Enc.Sound E` a sound enclosure relation `E r x` for it: the second-order expansions
(`Modules/Root/Second.lean`) and the touch leaf are written once, over `Enc`.
-/

open Nieuwland.Check Finset

namespace Nieuwland.Root

/-- Enclosures of real numbers with ring operations: balls, affine forms. -/
class Enc (R : Type) extends Add R, Sub R, Mul R where
  /-- The enclosure of an integer. -/
  ofInt : ℤ → R

namespace Enc

variable {R : Type} [Enc R]

/-- A sound enclosure relation: `E r x` says that `r` encloses the real number `x`. -/
structure Sound (E : R → ℝ → Prop) : Prop where
  ofInt : ∀ z : ℤ, E (Enc.ofInt z) z
  add : ∀ {a b : R} {x y : ℝ}, E a x → E b y → E (a + b) (x + y)
  sub : ∀ {a b : R} {x y : ℝ}, E a x → E b y → E (a - b) (x - y)
  mul : ∀ {a b : R} {x y : ℝ}, E a x → E b y → E (a * b) (x * y)

/-- The sum of `f 0, …, f (n - 1)`. -/
def sum (n : ℕ) (f : ℕ → R) : R := (List.range n).foldl (fun acc k ↦ acc + f k) (ofInt 0)

theorem Sound.sum {E : R → ℝ → Prop} (hE : Sound E) {n : ℕ} {f : ℕ → R} {x : ℕ → ℝ}
    (h : ∀ k < n, E (f k) (x k)) : E (Enc.sum n f) (∑ k ∈ range n, x k) := by
  induction n with
  | zero => simpa [Enc.sum] using hE.ofInt 0
  | succ n ih =>
    have ih' := ih fun k hk ↦ h k (Nat.lt_succ_of_lt hk)
    rw [sum_range_succ]
    have : Enc.sum (n + 1) f = Enc.sum n f + f n := by simp [Enc.sum, List.range_succ]
    rw [this]
    exact hE.add ih' (h n (Nat.lt_succ_self n))

/-- The enclosure of an expression from enclosures of its variables. -/
def val (Y : ℕ → R) : Expr → R
  | .const c => ofInt c
  | .var i => Y i
  | .add a b => val Y a + val Y b
  | .sub a b => val Y a - val Y b
  | .mul a b => val Y a * val Y b

theorem Sound.val {E : R → ℝ → Prop} (hE : Sound E) {Y : ℕ → R} {y : ℕ → ℝ}
    (hY : ∀ i, E (Y i) (y i)) (e : Expr) : E (Enc.val Y e) (e.eval y) := by
  induction e with
  | const c => exact hE.ofInt c
  | var i => exact hY i
  | add a b iha ihb => exact hE.add iha ihb
  | sub a b iha ihb => exact hE.sub iha ihb
  | mul a b iha ihb => exact hE.mul iha ihb

end Enc

instance : Enc Ball where
  ofInt := Ball.ofInt

/-- Balls are sound enclosures. -/
theorem Ball.sound : Enc.Sound Ball.Encl :=
  ⟨Ball.encl_ofInt, Ball.encl_add, Ball.encl_sub, Ball.encl_mul⟩

/-- The ball at the scale `2^p` when its own is finer: the centre rounded down, the radius up. -/
def Ball'.trim (p : ℕ) (b : Ball) : Ball :=
  if b.s ≤ p then b else ⟨b.m / 2 ^ (b.s - p), b.r / 2 ^ (b.s - p) + 2, p⟩

theorem Ball'.encl_trim {b : Ball} {x : ℝ} (h : b.Encl x) (p : ℕ) : (Ball'.trim p b).Encl x := by
  unfold Ball'.trim
  split_ifs with hs
  · exact h
  · unfold Ball.Encl at *
    have hsk : b.s = p + (b.s - p) := by omega
    generalize b.s - p = k at hsk ⊢
    have hM : (0 : ℝ) < 2 ^ k := by positivity
    have hm1 : ((b.m / 2 ^ k : ℤ) : ℝ) * 2 ^ k ≤ b.m := by
      exact_mod_cast Int.ediv_mul_le b.m (by positivity : (2 : ℤ) ^ k ≠ 0)
    have hm2 : (b.m : ℝ) < (((b.m / 2 ^ k : ℤ) : ℝ) + 1) * 2 ^ k := by
      exact_mod_cast Int.lt_ediv_add_one_mul_self b.m (by positivity : (0 : ℤ) < 2 ^ k)
    have hr2 : (b.r : ℝ) < 2 ^ k * (((b.r / 2 ^ k : ℕ) : ℝ) + 1) := by
      exact_mod_cast Nat.lt_mul_div_succ b.r (by positivity : 0 < 2 ^ k)
    rw [hsk, pow_add] at h
    have h' := _root_.abs_le.mp h
    change |(2 : ℝ) ^ p * x - ((b.m / 2 ^ k : ℤ) : ℝ)| ≤ ((b.r / 2 ^ k + 2 : ℕ) : ℝ)
    push_cast
    rw [_root_.abs_le]
    constructor
    · refine le_of_mul_le_mul_left ?_ hM
      nlinarith
    · refine le_of_mul_le_mul_left ?_ hM
      nlinarith

/-- The entry `k` of a list from a function of the index. -/
theorem getD_map_range {α : Type*} {n i : ℕ} (hi : i < n) (f : ℕ → α) (d : α) :
    ((List.range n).map f).getD i d = f i := by
  simp [List.getD, hi]

/-- An affine form in `n` variables `δ_k ∈ [-1, 1]`: `c + ∑ l_k δ_k + e`, in balls at scales of
at most `2^p` (module docs). -/
structure Aff (n p : ℕ) where
  /-- The constant term. -/
  c : Ball
  /-- The coefficients of the variables. -/
  l : List Ball
  /-- The rest. -/
  e : Ball

namespace Aff

variable {n p : ℕ}

/-- The coefficient of the variable `k`. -/
def lk (f : Aff n p) (k : ℕ) : Ball := f.l.getD k (Ball.ofInt 0)

/-- The ball `[-1, 1]` of a variable. -/
def U : Ball := ⟨0, 1, 0⟩

/-- The ball of the first-order part. -/
def span (f : Aff n p) : Ball := Ball'.sum n fun k ↦ f.lk k * U

/-- The ball of the form on the box. -/
def toBall (f : Aff n p) : Ball := f.c + f.span + f.e

/-- The constant form of a ball. -/
def ofBall (b : Ball) : Aff n p := ⟨Ball'.trim p b, [], Ball.ofInt 0⟩

/-- The form `c + r δ_k` of the variable `k` on its interval, from the ball of the interval. -/
def varOf (b : Ball) (k : ℕ) : Aff n p :=
  ⟨Ball'.trim p ⟨b.m, 0, b.s⟩,
    (List.range n).map fun j ↦ if j = k then Ball'.trim p ⟨b.r, 0, b.s⟩ else Ball.ofInt 0,
    Ball.ofInt 0⟩

/-- The sum of two forms. -/
def add (a b : Aff n p) : Aff n p :=
  ⟨a.c + b.c, (List.range n).map fun k ↦ a.lk k + b.lk k, a.e + b.e⟩

/-- The difference of two forms. -/
def sub (a b : Aff n p) : Aff n p :=
  ⟨a.c - b.c, (List.range n).map fun k ↦ a.lk k - b.lk k, a.e - b.e⟩

/-- The product of two forms: the second-order part goes into the rest. -/
def mul (a b : Aff n p) : Aff n p :=
  let sa := a.span
  let sb := b.span
  ⟨Ball'.trim p (a.c * b.c),
    (List.range n).map fun k ↦ Ball'.trim p (a.c * b.lk k + b.c * a.lk k),
    Ball'.trim p (sa * sb + a.e * (b.c + sb + b.e) + b.e * (a.c + sa))⟩

instance : Enc (Aff n p) where
  add := add
  sub := sub
  mul := mul
  ofInt z := ofBall (Ball.ofInt z)

/-- The form `f` encloses `x` at the point `δ` of the variables. -/
def Encl (δ : ℕ → ℝ) (f : Aff n p) (x : ℝ) : Prop :=
  ∃ (c : ℝ) (l : ℕ → ℝ) (e : ℝ), f.c.Encl c ∧ (∀ k < n, (f.lk k).Encl (l k)) ∧ f.e.Encl e ∧
    x = c + ∑ k ∈ range n, l k * δ k + e

theorem encl_U {t : ℝ} (ht : |t| ≤ 1) : U.Encl t := by
  unfold Ball.Encl U
  simpa using ht

theorem encl_span {δ : ℕ → ℝ} (hδ : ∀ k < n, |δ k| ≤ 1) {f : Aff n p} {l : ℕ → ℝ}
    (hl : ∀ k < n, (f.lk k).Encl (l k)) : f.span.Encl (∑ k ∈ range n, l k * δ k) :=
  Ball'.encl_sum fun k hk ↦ Ball.encl_mul (hl k hk) (encl_U (hδ k hk))

/-- On the box, the form's ball encloses what the form encloses. -/
theorem encl_toBall {δ : ℕ → ℝ} (hδ : ∀ k < n, |δ k| ≤ 1) {f : Aff n p} {x : ℝ}
    (h : f.Encl δ x) : f.toBall.Encl x := by
  obtain ⟨c, l, e, hc, hl, he, rfl⟩ := h
  exact Ball.encl_add (Ball.encl_add hc (encl_span hδ hl)) he

theorem encl_ofBall (δ : ℕ → ℝ) {b : Ball} {x : ℝ} (h : b.Encl x) :
    (ofBall b : Aff n p).Encl δ x := by
  refine ⟨x, fun _ ↦ 0, 0, Ball'.encl_trim h p, fun k _ ↦ ?_, ?_, ?_⟩
  · simpa [lk, ofBall] using Ball.encl_ofInt 0
  · simpa [ofBall] using Ball.encl_ofInt 0
  · simp

/-- What a ball encloses, as a point of its interval: `x = m / 2^s + (r / 2^s) t`, `|t| ≤ 1`. -/
theorem exists_param {b : Ball} {x : ℝ} (h : b.Encl x) :
    ∃ t : ℝ, |t| ≤ 1 ∧ x = (b.m : ℝ) / 2 ^ b.s + (b.r : ℝ) / 2 ^ b.s * t := by
  unfold Ball.Encl at h
  have h2 : (0 : ℝ) < 2 ^ b.s := by positivity
  by_cases hr : (b.r : ℝ) = 0
  · refine ⟨0, by simp, ?_⟩
    rw [hr] at h
    have h0 : (2 : ℝ) ^ b.s * x - b.m = 0 := abs_nonpos_iff.mp h
    rw [hr, zero_div, zero_mul, add_zero, eq_div_iff h2.ne']
    linarith
  · have hr' : (0 : ℝ) < b.r := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hr)
    refine ⟨((2 : ℝ) ^ b.s * x - b.m) / b.r, ?_, ?_⟩
    · rw [abs_div, abs_of_pos hr', div_le_one hr']
      exact h
    · field_simp
      ring

theorem encl_varOf {δ : ℕ → ℝ} {b : Ball} {k : ℕ} (hk : k < n) :
    (varOf b k : Aff n p).Encl δ ((b.m : ℝ) / 2 ^ b.s + (b.r : ℝ) / 2 ^ b.s * δ k) := by
  have h2 : (0 : ℝ) < 2 ^ b.s := by positivity
  refine ⟨(b.m : ℝ) / 2 ^ b.s, fun j ↦ if j = k then (b.r : ℝ) / 2 ^ b.s else 0, 0, ?_,
    fun j hj ↦ ?_, ?_, ?_⟩
  · refine Ball'.encl_trim ?_ p
    change |(2 : ℝ) ^ b.s * ((b.m : ℝ) / 2 ^ b.s) - b.m| ≤ ((0 : ℕ) : ℝ)
    rw [mul_div_cancel₀ _ h2.ne']
    simp
  · rw [lk, varOf, getD_map_range hj]
    by_cases hjk : j = k
    · simp only [hjk, ↓reduceIte]
      refine Ball'.encl_trim ?_ p
      change |(2 : ℝ) ^ b.s * ((b.r : ℝ) / 2 ^ b.s) - ((b.r : ℤ) : ℝ)| ≤ ((0 : ℕ) : ℝ)
      rw [mul_div_cancel₀ _ h2.ne']
      simp
    · simp only [hjk, ↓reduceIte]
      simpa using Ball.encl_ofInt 0
  · simpa [varOf] using Ball.encl_ofInt 0
  · simp only [ite_mul, zero_mul, sum_ite_eq', mem_range, hk, ↓reduceIte, add_zero]

/-- Affine forms are sound enclosures at every point of the box of their variables. -/
theorem sound {δ : ℕ → ℝ} (hδ : ∀ k < n, |δ k| ≤ 1) :
    Enc.Sound (Encl (n := n) (p := p) δ) where
  ofInt z := encl_ofBall δ (Ball.encl_ofInt z)
  add := by
    rintro a b x y ⟨c, l, e, hc, hl, he, rfl⟩ ⟨c', l', e', hc', hl', he', rfl⟩
    refine ⟨c + c', fun k ↦ l k + l' k, e + e', Ball.encl_add hc hc', fun k hk ↦ ?_,
      Ball.encl_add he he', ?_⟩
    · change (lk (add a b) k).Encl _
      rw [lk, add, getD_map_range hk]
      exact Ball.encl_add (hl k hk) (hl' k hk)
    · simp only [add_mul, sum_add_distrib]
      ring
  sub := by
    rintro a b x y ⟨c, l, e, hc, hl, he, rfl⟩ ⟨c', l', e', hc', hl', he', rfl⟩
    refine ⟨c - c', fun k ↦ l k - l' k, e - e', Ball.encl_sub hc hc', fun k hk ↦ ?_,
      Ball.encl_sub he he', ?_⟩
    · change (lk (sub a b) k).Encl _
      rw [lk, sub, getD_map_range hk]
      exact Ball.encl_sub (hl k hk) (hl' k hk)
    · simp only [sub_mul, sum_sub_distrib]
      ring
  mul := by
    rintro a b x y ⟨c, l, e, hc, hl, he, rfl⟩ ⟨c', l', e', hc', hl', he', rfl⟩
    have hsa := encl_span hδ hl
    have hsb := encl_span hδ hl'
    refine ⟨c * c', fun k ↦ c * l' k + c' * l k,
      (∑ k ∈ range n, l k * δ k) * (∑ k ∈ range n, l' k * δ k) +
        e * (c' + ∑ k ∈ range n, l' k * δ k + e') + e' * (c + ∑ k ∈ range n, l k * δ k),
      Ball'.encl_trim (Ball.encl_mul hc hc') p, fun k hk ↦ ?_, ?_, ?_⟩
    · change (lk (mul a b) k).Encl _
      rw [lk, mul, getD_map_range hk]
      exact Ball'.encl_trim
        (Ball.encl_add (Ball.encl_mul hc (hl' k hk)) (Ball.encl_mul hc' (hl k hk))) p
    · exact Ball'.encl_trim (Ball.encl_add (Ball.encl_add (Ball.encl_mul hsa hsb)
        (Ball.encl_mul he (Ball.encl_add (Ball.encl_add hc' hsb) he')))
        (Ball.encl_mul he' (Ball.encl_add hc hsa))) p
    · have h1 : ∑ k ∈ range n, (c * l' k + c' * l k) * δ k =
          c * (∑ k ∈ range n, l' k * δ k) + c' * ∑ k ∈ range n, l k * δ k := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun k _ ↦ by ring
      rw [h1]
      ring

end Aff

end Nieuwland.Root
