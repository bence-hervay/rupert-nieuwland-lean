import Modules.Check.Polynomial.Pack
import Modules.Check.Polynomial.Expr

/-!
# Coefficient tools for quotients by monomials

A pulled-back witness `Q` on a zoom piece vanishes to some order in the radius parameters, and the
range bound is applied to its quotient by a monomial (`wzoom.rs`). The kernel never expands `Q`:
it reads the vanishing pattern off the digits of a packed value (`Nieuwland/Check/Fields.lean`).
This file has the polynomial side of that argument.

* `DPoly.absEval p r = ∑ |p_α| r^α` for natural `r`. It bounds the absolute coefficient sum of
  `p (C + H y)` when `rᵢ = |Cᵢ| + |Hᵢ|`, and `Expr.absEval_toDPoly_le` bounds it by
  `Expr.normBound`.
* `DPoly.toExpr`: the Horner expression of a dense polynomial, so that `Expr.toDPoly` composes
  dense polynomials with the linear inputs of a box (`eval_toExpr`, `normBound_toExpr`,
  `shape_toExpr_le`).
* `DPoly.ZeroOn n P p`: the coefficients of `p` at the exponents `α` with `P α` vanish. With
  `P = below e` this says that the monomial `x^e` divides `p`, and `unshift n e p` is the quotient
  (`eval_unshift`, `absEval_unshift`, `fits_unshift`).
* `toList_unpack_biased`: unpacking a packed value gives back the coefficients, padded with zeros,
  so `absEval` survives packing (`absEval_unpack`), and unpacked polynomials fit their shape
  (`fits_unpack`).
-/

namespace Nieuwland.Check

namespace DPoly

/-! ### Horner sums in the natural numbers -/

section Nat

variable {α : Type*} {f : α → ℕ} {z : ℕ}

theorem horner_zipPad_le {g : α → α → α} (hg : ∀ a b, f (g a b) ≤ f a + f b) :
    ∀ as bs : List α, horner f z (zipPad g as bs) ≤ horner f z as + horner f z bs
  | [], bs => by simp [zipPad]
  | a :: as, [] => by simp [zipPad]
  | a :: as, b :: bs => by
    have h₁ := hg a b
    have h₂ := Nat.mul_le_mul_left z (horner_zipPad_le hg as bs)
    simp only [zipPad, horner_cons]
    nlinarith

theorem horner_map_le {g : α → α} {c : ℕ} (hg : ∀ a, f (g a) ≤ c * f a) :
    ∀ as : List α, horner f z (as.map g) ≤ c * horner f z as
  | [] => by simp
  | a :: as => by
    have h₁ := hg a
    have h₂ := Nat.mul_le_mul_left z (horner_map_le hg as)
    simp only [List.map_cons, horner_cons]
    nlinarith

theorem horner_map_nat {g : α → α} {c : ℕ} (hg : ∀ a, f (g a) = c * f a) :
    ∀ as : List α, horner f z (as.map g) = c * horner f z as
  | [] => by simp
  | a :: as => by
    simp only [List.map_cons, horner_cons, hg, horner_map_nat hg as]
    ring

theorem horner_mulList_le {z₀ : α} {add mul : α → α → α} (h₀ : f z₀ = 0)
    (hadd : ∀ a b, f (add a b) ≤ f a + f b) (hmul : ∀ a b, f (mul a b) ≤ f a * f b) :
    ∀ as bs : List α, horner f z (mulList z₀ add mul as bs) ≤ horner f z as * horner f z bs
  | [], bs => by simp [mulList]
  | a :: as, bs => by
    have h₁ := horner_zipPad_le (z := z) hadd (bs.map (mul a))
      (z₀ :: mulList z₀ add mul as bs)
    have h₂ := horner_map_le (z := z) (hmul a) bs
    have h₃ := Nat.mul_le_mul_left z (horner_mulList_le h₀ hadd hmul as bs)
    simp only [mulList, horner_cons, h₀, zero_add] at h₁ ⊢
    calc _ ≤ _ := h₁
      _ ≤ f a * horner f z bs + z * (horner f z as * horner f z bs) := by nlinarith
      _ = _ := by ring

end Nat

theorem horner_const_mul {α R : Type*} [CommSemiring R] (g : α → R) (c z : R) :
    ∀ as : List α, horner (fun a ↦ c * g a) z as = c * horner g z as
  | [] => by simp
  | a :: as => by rw [horner_cons, horner_cons, horner_const_mul g c z as]; ring

/-! ### Absolute evaluation -/

/-- `∑ |p_α| r^α`, by Horner's scheme in the natural numbers. -/
def absEval : (n : ℕ) → DPoly n → (Fin n → ℕ) → ℕ
  | 0, p, _ => (toInt p).natAbs
  | n + 1, p, r => horner (fun q ↦ absEval n q (Fin.tail r)) (r 0) (toList p)

theorem absEval_zero : ∀ (n : ℕ) (r : Fin n → ℕ), absEval n (zero n) r = 0
  | 0, _ => rfl
  | _ + 1, _ => rfl

theorem absEval_const : ∀ (n : ℕ) (c : ℤ) (r : Fin n → ℕ), absEval n (const n c) r = c.natAbs
  | 0, _, _ => rfl
  | n + 1, c, r => by simp [absEval, const, absEval_const n c]

theorem absEval_add_le : ∀ (n : ℕ) (p q : DPoly n) (r : Fin n → ℕ),
    absEval n (add n p q) r ≤ absEval n p r + absEval n q r
  | 0, p, q, _ => Int.natAbs_add_le (toInt p) (toInt q)
  | n + 1, p, q, r =>
    horner_zipPad_le (f := fun q ↦ absEval n q (Fin.tail r))
      (fun a b ↦ absEval_add_le n a b (Fin.tail r)) (toList p) (toList q)

theorem absEval_smul : ∀ (n : ℕ) (c : ℤ) (p : DPoly n) (r : Fin n → ℕ),
    absEval n (smul n c p) r = c.natAbs * absEval n p r
  | 0, c, p, _ => Int.natAbs_mul c (toInt p)
  | n + 1, c, p, r =>
    horner_map_nat (f := fun q ↦ absEval n q (Fin.tail r))
      (fun a ↦ absEval_smul n c a (Fin.tail r)) (toList p)

theorem absEval_mul_le : ∀ (n : ℕ) (p q : DPoly n) (r : Fin n → ℕ),
    absEval n (mul n p q) r ≤ absEval n p r * absEval n q r
  | 0, p, q, _ => (Int.natAbs_mul (toInt p) (toInt q)).le
  | n + 1, p, q, r =>
    horner_mulList_le (f := fun q ↦ absEval n q (Fin.tail r)) (absEval_zero n _)
      (fun a b ↦ absEval_add_le n a b (Fin.tail r))
      (fun a b ↦ absEval_mul_le n a b (Fin.tail r)) (toList p) (toList q)

theorem absEval_linear : ∀ (n i : ℕ) (C H : ℤ) (r : Fin n → ℕ),
    absEval n (linear n i C H) r ≤ C.natAbs + H.natAbs * (if h : i < n then r ⟨i, h⟩ else 0)
  | 0, _, C, _, _ => by simp [absEval, linear]
  | n + 1, 0, C, H, r => by simp [absEval, linear, absEval_const, Nat.mul_comm]
  | n + 1, i + 1, C, H, r => by
    have := absEval_linear n i C H (Fin.tail r)
    simp only [absEval, linear, toList_ofList, horner_cons, horner_nil, mul_zero, add_zero]
    by_cases h : i < n
    · simpa [h, Fin.tail] using this
    · simpa [h] using this

/-! ### Expressions -/

theorem _root_.Nieuwland.Check.Expr.absEval_toDPoly_le (n : ℕ) (x : ℕ → DPoly n)
    (r : Fin n → ℕ) (b : List ℕ) (hb : ∀ i, absEval n (x i) r ≤ b.getD i 0) :
    ∀ e : Expr, absEval n (e.toDPoly n x) r ≤ e.normBound b
  | .const c => (absEval_const n c r).le
  | .var i => hb i
  | .add e e' => (absEval_add_le n _ _ r).trans
      (Nat.add_le_add (Expr.absEval_toDPoly_le n x r b hb e)
        (Expr.absEval_toDPoly_le n x r b hb e'))
  | .sub e e' => by
    refine (absEval_add_le n _ _ r).trans
      (Nat.add_le_add (Expr.absEval_toDPoly_le n x r b hb e) ?_)
    rw [absEval_smul]
    simpa using Expr.absEval_toDPoly_le n x r b hb e'
  | .mul e e' => (absEval_mul_le n _ _ r).trans
      (Nat.mul_le_mul (Expr.absEval_toDPoly_le n x r b hb e)
        (Expr.absEval_toDPoly_le n x r b hb e'))

/-- Horner's scheme as an expression: `f a₀ + z (f a₁ + z (⋯ + z f aₘ))`. -/
def hornerExpr {α : Type*} (f : α → Expr) (z : Expr) : List α → Expr
  | [] => .const 0
  | [a] => f a
  | a :: b :: as => f a + z * hornerExpr f z (b :: as)

/-- The Horner expression of `p` in the variables `i, i + 1, …, i + n - 1`. -/
def toExpr : (n : ℕ) → ℕ → DPoly n → Expr
  | 0, _, p => .const (toInt p)
  | n + 1, i, p => hornerExpr (toExpr n (i + 1)) (.var i) (toList p)

theorem eval_hornerExpr {α R : Type*} [CommRing R] (x : ℕ → R) (f : α → Expr) (z : Expr) :
    ∀ as : List α, (hornerExpr f z as).eval x = horner (fun a ↦ (f a).eval x) (z.eval x) as
  | [] => by simp [hornerExpr]
  | [a] => by simp [hornerExpr]
  | a :: b :: as => by
    rw [hornerExpr, Expr.eval_add, Expr.eval_mul, eval_hornerExpr x f z (b :: as)]
    rfl

theorem eval_toExpr {R : Type*} [CommRing R] (x : ℕ → R) :
    ∀ (n i : ℕ) (p : DPoly n), (toExpr n i p).eval x = eval n p (fun j ↦ x (i + j))
  | 0, _, p => rfl
  | n + 1, i, p => by
    rw [toExpr, eval_hornerExpr, eval]
    simp only [eval_toExpr x n (i + 1), Expr.eval_var, Fin.val_zero, add_zero]
    congr 1
    funext q
    congr 1
    funext j
    simp only [Fin.tail, Fin.val_succ]
    congr 1
    omega

theorem normBound_hornerExpr {α : Type*} (b : List ℕ) (f : α → Expr) (z : Expr) :
    ∀ as : List α, (hornerExpr f z as).normBound b =
      horner (fun a ↦ (f a).normBound b) (z.normBound b) as
  | [] => by simp [hornerExpr, Expr.normBound]
  | [a] => by simp [hornerExpr]
  | a :: b' :: as => by
    rw [hornerExpr, horner_cons, ← normBound_hornerExpr b f z (b' :: as)]
    rfl

theorem normBound_toExpr (b : List ℕ) :
    ∀ (n i : ℕ) (p : DPoly n),
      (toExpr n i p).normBound b = absEval n p (fun j ↦ b.getD (i + j) 0)
  | 0, _, p => rfl
  | n + 1, i, p => by
    rw [toExpr, normBound_hornerExpr, absEval]
    simp only [normBound_toExpr b n (i + 1), Expr.normBound, Fin.val_zero, add_zero]
    congr 1
    funext q
    congr 1
    funext j
    simp only [Fin.tail, Fin.val_succ]
    congr 1
    omega

/-! ### Shapes of Horner expressions -/

theorem shapeLE_zipPad_max : ∀ {a b c : List ℕ}, ShapeLE a c → ShapeLE b c →
    ShapeLE (zipPad max a b) c
  | [], _, _, _, hb => by simpa [zipPad] using hb
  | _ :: _, [], _, ha, _ => by simpa [zipPad] using ha
  | _ :: _, _ :: _, _, ha, hb => ⟨max_le ha.1 hb.1, shapeLE_zipPad_max ha.2 hb.2⟩

/-- Raising the entry `i` of a bound keeps it a bound. -/
theorem shapeLE_replicate_mono : ∀ (i : ℕ) {a t : List ℕ} {d d' : ℕ}, d ≤ d' →
    ShapeLE a (List.replicate i 0 ++ d :: t) → ShapeLE a (List.replicate i 0 ++ d' :: t)
  | _, [], _, _, _, _, _ => trivial
  | 0, _ :: _, _, _, _, hd, h => ⟨h.1.trans (by simpa using hd), h.2⟩
  | i + 1, _ :: a, t, d, d', hd, h =>
    ⟨h.1, shapeLE_replicate_mono i (a := a) hd h.2⟩

/-- Multiplying by the variable `i` raises the entry `i` of a bound by one. -/
theorem shapeLE_zipPad_var : ∀ (i : ℕ) {a t : List ℕ} {d : ℕ},
    ShapeLE a (List.replicate i 0 ++ d :: t) →
      ShapeLE (zipPad (· + ·) (List.replicate i 0 ++ [1]) a)
        (List.replicate i 0 ++ (d + 1) :: t)
  | 0, [], t, d, _ => ⟨by simp, trivial⟩
  | 0, x :: a, t, d, h => by
    simp only [List.replicate_zero, List.nil_append] at h ⊢
    obtain ⟨h₁, h₂⟩ := h
    simp only [List.headD_cons, List.tail_cons] at h₁ h₂
    simp only [zipPad, ShapeLE, List.headD_cons, List.tail_cons]
    exact ⟨by omega, h₂⟩
  | i + 1, [], t, d, _ => by
    have := shapeLE_zipPad_var i (a := []) (t := t) (d := d) trivial
    rw [zipPad_nil_right] at this
    simp only [List.replicate_succ, List.cons_append, zipPad]
    exact ⟨le_rfl, this⟩
  | i + 1, x :: a, t, d, h => by
    simp only [List.replicate_succ, List.cons_append] at h ⊢
    obtain ⟨h₁, h₂⟩ := h
    simp only [List.headD_cons, List.tail_cons] at h₁ h₂
    simp only [zipPad, ShapeLE, List.headD_cons, List.tail_cons]
    exact ⟨by omega, shapeLE_zipPad_var i h₂⟩

theorem shape_hornerExpr_le {α : Type*} (s : List (List ℕ)) (f : α → Expr) (i : ℕ)
    (hz : s.getD i [] = List.replicate i 0 ++ [1]) (t : List ℕ) (as : List α)
    (hf : ∀ a ∈ as, ShapeLE ((f a).shape s) (List.replicate i 0 ++ 0 :: t)) :
    ShapeLE ((hornerExpr f (.var i) as).shape s)
      (List.replicate i 0 ++ (as.length - 1) :: t) := by
  induction as with
  | nil => trivial
  | cons a as ih =>
    cases as with
    | nil => simpa [hornerExpr] using hf a List.mem_cons_self
    | cons b as =>
      rw [hornerExpr]
      have ih' := ih fun c hc ↦ hf c (List.mem_cons_of_mem _ hc)
      refine shapeLE_zipPad_max
        (shapeLE_replicate_mono i (Nat.zero_le _) (hf a List.mem_cons_self)) ?_
      have := shapeLE_zipPad_var i ih'
      simp only [List.length_cons, Nat.add_sub_cancel] at this ⊢
      change ShapeLE (zipPad (· + ·) (s.getD i []) _) _
      rw [hz]
      exact this

/-- Trailing zeros of a bound do not matter. -/
theorem shapeLE_of_append_zero : ∀ {a c : List ℕ}, ShapeLE a (c ++ [0]) → ShapeLE a c
  | [], _, _ => trivial
  | _ :: _, [], h => ⟨by simpa using h.1, by simpa using h.2⟩
  | _ :: _, _ :: _, h => ⟨h.1, shapeLE_of_append_zero h.2⟩

/-- **Shapes of Horner expressions**: in the variables `i, …, i + n - 1`, with inputs of the
shapes of the variables of a box, the expression of a polynomial that fits `sh` has shape at
most `sh` there. -/
theorem shape_toExpr_le (s : List (List ℕ)) :
    ∀ (n i : ℕ), (∀ j < n, s.getD (i + j) [] = List.replicate (i + j) 0 ++ [1]) →
      ∀ {p : DPoly n} {sh : List ℕ}, Fits n p sh →
        ShapeLE ((toExpr n i p).shape s) (List.replicate i 0 ++ sh)
  | 0, _, _, _, _, _ => trivial
  | n + 1, i, hs, p, sh, ⟨hlen, hp⟩ => by
    rw [toExpr]
    have hz : s.getD i [] = List.replicate i 0 ++ [1] := by simpa using hs 0 (Nat.succ_pos n)
    have hf : ∀ q ∈ toList p, ShapeLE ((toExpr n (i + 1) q).shape s)
        (List.replicate i 0 ++ 0 :: sh.tail) := by
      intro q hq
      have hrep : List.replicate i 0 ++ 0 :: sh.tail =
          List.replicate (i + 1) 0 ++ sh.tail := by
        rw [List.replicate_succ', List.append_assoc]
        rfl
      rw [hrep]
      exact shape_toExpr_le s n (i + 1) (fun j hj ↦ by
        have := hs (j + 1) (by omega)
        rwa [show i + (j + 1) = i + 1 + j by omega] at this) (hp q hq)
    have h := shapeLE_replicate_mono i (d' := sh.headD 0) (by omega)
      (shape_hornerExpr_le s _ i hz _ _ hf)
    cases sh with
    | nil =>
      have h' : ShapeLE ((hornerExpr (toExpr n (i + 1)) (.var i) (toList p)).shape s)
          (List.replicate i 0 ++ [0]) := h
      simpa using shapeLE_of_append_zero h'
    | cons a sh => exact h

/-! ### Zero patterns -/

/-- `ForallIdx f k l`: `f (k + i) (l[i])` for every index `i` of `l`. -/
def ForallIdx {β : Type*} (f : ℕ → β → Prop) : ℕ → List β → Prop
  | _, [] => True
  | k, b :: bs => f k b ∧ ForallIdx f (k + 1) bs

theorem ForallIdx.forall_mem {β : Type*} {f : ℕ → β → Prop} {g : β → Prop} :
    ∀ {k : ℕ} {l : List β}, ForallIdx f k l → (∀ j, k ≤ j → ∀ b, f j b → g b) →
      ∀ b ∈ l, g b
  | _, [], _, _, _, hb => absurd hb List.not_mem_nil
  | k, b :: l, ⟨hb, hl⟩, hfg, c, hc => by
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hfg k le_rfl c hb
    · exact ForallIdx.forall_mem hl (fun j hj ↦ hfg j (by omega)) c hc

theorem ForallIdx.drop {β : Type*} {f : ℕ → β → Prop} :
    ∀ (m k : ℕ) (l : List β), ForallIdx f k l → ForallIdx f (k + m) (l.drop m)
  | 0, k, l, h => by simpa using h
  | _ + 1, _, [], _ => trivial
  | m + 1, k, _ :: l, ⟨_, h⟩ => by
    rw [List.drop_succ_cons, show k + (m + 1) = (k + 1) + m by omega]
    exact ForallIdx.drop m (k + 1) l h

/-- `ZeroOn n P p`: the coefficients of `p` at the exponent lists `α` with `P α` vanish. -/
def ZeroOn : (n : ℕ) → (List ℕ → Bool) → DPoly n → Prop
  | 0, P, p => P [] = true → toInt p = 0
  | n + 1, P, p => ForallIdx (fun k q ↦ ZeroOn n (fun α ↦ P (k :: α)) q) 0 (toList p)

theorem eval_eq_zero_of_zeroOn {R : Type*} [CommRing R] : ∀ (n : ℕ) {P : List ℕ → Bool}
    {p : DPoly n}, (∀ α, P α = true) → ZeroOn n P p → ∀ x : Fin n → R, eval n p x = 0
  | 0, _, p, hP, h, _ => by simp [eval, h (hP [])]
  | n + 1, P, p, hP, h, x => by
    rw [eval]
    have key : ∀ q ∈ toList p, eval n q (Fin.tail x) = 0 :=
      ForallIdx.forall_mem h fun k _ q hq ↦
        eval_eq_zero_of_zeroOn n (fun α ↦ hP (k :: α)) hq _
    rw [horner_congr _ key]
    clear key h
    induction toList p <;> simp_all

theorem absEval_eq_zero_of_zeroOn : ∀ (n : ℕ) {P : List ℕ → Bool} {p : DPoly n},
    (∀ α, P α = true) → ZeroOn n P p → ∀ r : Fin n → ℕ, absEval n p r = 0
  | 0, _, p, hP, h, _ => by simp [absEval, h (hP [])]
  | n + 1, P, p, hP, h, r => by
    rw [absEval]
    have key : ∀ q ∈ toList p, absEval n q (Fin.tail r) = 0 :=
      ForallIdx.forall_mem h fun k _ q hq ↦
        absEval_eq_zero_of_zeroOn n (fun α ↦ hP (k :: α)) hq _
    rw [horner_congr _ key]
    clear key h
    induction toList p <;> simp_all

/-! ### Quotients by monomials -/

/-- The exponent lists below `e` in some variable: `α i < e i` for some `i` (missing entries of
`e` count as `0`). -/
def below : List ℕ → List ℕ → Bool
  | _, [] => false
  | e, a :: α => decide (a < e.headD 0) || below e.tail α

theorem below_cons_of_lt {e : List ℕ} {k : ℕ} (hk : k < e.headD 0) (α : List ℕ) :
    below e (k :: α) = true := by
  simp only [below, Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inl hk

theorem below_cons_of_le {e : List ℕ} {k : ℕ} (hk : e.headD 0 ≤ k) :
    (fun α ↦ below e (k :: α)) = below e.tail := by
  funext α
  have : ¬k < e.headD 0 := Nat.not_lt.mpr hk
  simp only [below, this, decide_false, Bool.false_or]

/-- The quotient by `x^e`: drop the first `e i` coefficients in each variable `i`. -/
def unshift : (n : ℕ) → List ℕ → DPoly n → DPoly n
  | 0, _, p => p
  | n + 1, e, p => ofList (((toList p).drop (e.headD 0)).map (unshift n e.tail))

/-- `∏ᵢ xᵢ ^ eᵢ` over the first `n` variables. -/
def monoVal {R : Type*} [CommMonoid R] : (n : ℕ) → List ℕ → (Fin n → R) → R
  | 0, _, _ => 1
  | n + 1, e, x => x 0 ^ e.headD 0 * monoVal n e.tail (Fin.tail x)

/-- Coefficients that vanish below the index `m` give a factor `z ^ m`. -/
theorem horner_eq_pow_mul_drop {β R : Type*} [CommSemiring R] {f : ℕ → β → Prop} {g : β → R}
    {z : R} {m : ℕ} (hf : ∀ k b, k < m → f k b → g b = 0) :
    ∀ (k : ℕ) (l : List β), k ≤ m → ForallIdx f k l →
      horner g z l = z ^ (m - k) * horner g z (l.drop (m - k))
  | k, [], _, _ => by simp
  | k, b :: l, hk, ⟨hb, hl⟩ => by
    rcases eq_or_lt_of_le hk with rfl | hlt
    · simp
    · rw [horner_cons, hf k b hlt hb, zero_add, horner_eq_pow_mul_drop hf (k + 1) l hlt hl,
        show m - k = (m - (k + 1)) + 1 by omega, List.drop_succ_cons, pow_succ]
      ring

/-- **Quotients by monomials.** If the monomial `x^e` divides `p` coefficientwise,
`p = x^e · unshift e p`. -/
theorem eval_unshift {R : Type*} [CommRing R] : ∀ (n : ℕ) (e : List ℕ) {p : DPoly n},
    ZeroOn n (below e) p → ∀ x : Fin n → R,
      eval n p x = monoVal n e x * eval n (unshift n e p) x
  | 0, _, _, _, _ => by simp [monoVal, unshift]
  | n + 1, e, p, h, x => by
    have hsplit := horner_eq_pow_mul_drop (z := x 0) (g := fun q ↦ eval n q (Fin.tail x))
      (m := e.headD 0) (fun k q hk hq ↦
        eval_eq_zero_of_zeroOn n (fun α ↦ below_cons_of_lt hk α) hq _) 0 (toList p)
      (Nat.zero_le _) h
    have hdrop : ∀ q ∈ (toList p).drop (e.headD 0), ZeroOn n (below e.tail) q :=
      ForallIdx.forall_mem (ForallIdx.drop (e.headD 0) 0 (toList p) h) fun k hk q hq ↦ by
        rwa [← below_cons_of_le (k := k) (by omega)]
    rw [eval, hsplit, Nat.sub_zero,
      horner_congr _ fun q hq ↦ eval_unshift n e.tail (hdrop q hq) (Fin.tail x),
      horner_const_mul]
    simp only [unshift, eval_ofList, monoVal, horner_map']
    ring

theorem absEval_unshift : ∀ (n : ℕ) (e : List ℕ) {p : DPoly n},
    ZeroOn n (below e) p → ∀ r : Fin n → ℕ,
      absEval n p r = monoVal n e r * absEval n (unshift n e p) r
  | 0, _, _, _, _ => by simp [monoVal, unshift]
  | n + 1, e, p, h, r => by
    have hsplit := horner_eq_pow_mul_drop (z := r 0) (g := fun q ↦ absEval n q (Fin.tail r))
      (m := e.headD 0) (fun k q hk hq ↦
        absEval_eq_zero_of_zeroOn n (fun α ↦ below_cons_of_lt hk α) hq _) 0 (toList p)
      (Nat.zero_le _) h
    have hdrop : ∀ q ∈ (toList p).drop (e.headD 0), ZeroOn n (below e.tail) q :=
      ForallIdx.forall_mem (ForallIdx.drop (e.headD 0) 0 (toList p) h) fun k hk q hq ↦ by
        rwa [← below_cons_of_le (k := k) (by omega)]
    rw [absEval, hsplit, Nat.sub_zero,
      horner_congr _ fun q hq ↦ absEval_unshift n e.tail (hdrop q hq) (Fin.tail r),
      horner_const_mul]
    simp only [unshift, absEval, toList_ofList, monoVal, horner_map']
    ring

/-- The shape `sh - e`, entry by entry (truncated). -/
def shapeSub : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | a :: sh, e => (a - e.headD 0) :: shapeSub sh e.tail

theorem fits_unshift : ∀ (n : ℕ) (e : List ℕ) {p : DPoly n} {sh : List ℕ}, Fits n p sh →
    Fits n (unshift n e p) (shapeSub sh e)
  | 0, _, _, _, _ => trivial
  | n + 1, e, p, sh, ⟨hlen, hp⟩ => by
    refine ⟨?_, fun q hq ↦ ?_⟩
    · simp only [unshift, toList_ofList, List.length_map, List.length_drop]
      cases sh <;> simp [shapeSub] at hlen ⊢ <;> omega
    · simp only [unshift, toList_ofList, List.mem_map] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      have := fits_unshift n e.tail (hp q' (List.mem_of_mem_drop hq'))
      cases sh <;> simpa [shapeSub] using this

/-! ### Unpacking keeps the coefficients -/

theorem length_unpackL {α : Type*} (f : ℕ → α) (w : ℕ) :
    ∀ (m N : ℕ), (unpackL f w m N).length = m
  | 0, _ => rfl
  | m + 1, N => by simp [unpackL, length_unpackL f w m]

theorem mem_unpackL {α : Type*} {f : ℕ → α} {w : ℕ} :
    ∀ {m N : ℕ} {a : α}, a ∈ unpackL f w m N → ∃ k, a = f k
  | 0, _, _, h => absurd h List.not_mem_nil
  | m + 1, N, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, rfl⟩
    · exact mem_unpackL h

theorem fits_unpack : ∀ (n : ℕ) (sh : List ℕ) (B N : ℕ), Fits n (unpack n sh B N) sh
  | 0, _, _, _ => trivial
  | n + 1, sh, B, N => by
    refine ⟨by simp [unpack, length_unpackL], fun q hq ↦ ?_⟩
    simp only [unpack, toList_ofList] at hq
    obtain ⟨k, rfl⟩ := mem_unpackL hq
    exact fits_unpack n sh.tail B k

theorem toList_unpack_biased {n : ℕ} {e : List ℕ} {B : ℕ} {p : DPoly (n + 1)} (hB : 0 < B)
    (hfit : Fits (n + 1) p e) (hsmall : Small (n + 1) B p) :
    toList (unpack (n + 1) e B (biased (n + 1) e B p).toNat) =
      (padTo (e.headD 0 + 1) (zero n) (toList p)).map fun q ↦
        unpack n e.tail B (biased n e.tail B q).toNat := by
  obtain ⟨hlen, hfit'⟩ := hfit
  have hblock : ∀ q ∈ padTo (e.headD 0 + 1) (zero n) (toList p),
      0 ≤ biased n e.tail B q ∧ biased n e.tail B q < 2 ^ (B * slots e.tail) := by
    intro q hq
    rcases mem_padTo hq with hq | rfl
    · exact biased_range n hB (hfit' q hq) (hsmall q hq)
    · exact biased_range n hB (fits_zero n _) (small_zero B n)
  have hN : (biased (n + 1) e B p).toNat = horner id (2 ^ (B * slots e.tail))
      ((padTo (e.headD 0 + 1) (zero n) (toList p)).map fun q ↦
        (biased n e.tail B q).toNat) := by
    rw [biased_succ n e B p hlen, horner_toNat _ _ _ fun q hq ↦ (hblock q hq).1,
      Int.toNat_natCast, horner_map']
    rfl
  have := unpackL_horner (unpack n e.tail B) (B * slots e.tail)
    ((padTo (e.headD 0 + 1) (zero n) (toList p)).map fun q ↦ (biased n e.tail B q).toNat) (by
      intro b hb
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
      exact toNat_lt_two_pow (hblock q hq).2)
  rw [List.length_map, length_padTo _ hlen, List.map_map] at this
  rw [unpack, toList_ofList, hN]
  exact this

/-- **Unpacking keeps absolute evaluations.** -/
theorem absEval_unpack : ∀ (n : ℕ) {e : List ℕ} {B : ℕ} {p : DPoly n}, 0 < B → Fits n p e →
    Small n B p → ∀ r : Fin n → ℕ,
      absEval n (unpack n e B (biased n e B p).toNat) r = absEval n p r
  | 0, e, B, p, hB, _, hc, r => by
    have hc' : |toInt p| < 2 ^ (B - 1) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast (hc : (toInt p).natAbs < 2 ^ (B - 1))
    have h2 : (2 : ℤ) ^ B = 2 * 2 ^ (B - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hb : biased 0 e B p = toInt p + 2 ^ (B - 1) := by
      simp [biased, eval, offset]
    have h0 : 0 ≤ biased 0 e B p := by rw [hb]; linarith [neg_abs_le (toInt p)]
    have hlt : (biased 0 e B p).toNat < 2 ^ B :=
      toNat_lt_two_pow (by rw [hb]; linarith [le_abs_self (toInt p)])
    have hval : (((biased 0 e B p).toNat % 2 ^ B : ℕ) : ℤ) - 2 ^ (B - 1) = toInt p := by
      rw [Nat.mod_eq_of_lt hlt, Int.toNat_of_nonneg h0, hb]
      ring
    simp only [unpack, absEval, toInt_ofInt, hval]
  | n + 1, e, B, p, hB, hfit, hsmall, r => by
    rw [absEval, toList_unpack_biased hB hfit hsmall, horner_map', absEval,
      ← horner_padTo (a := zero n) (absEval_zero n _) (e.headD 0 + 1) (toList p)]
    refine horner_congr _ fun q hq ↦ ?_
    rcases mem_padTo hq with hq | rfl
    · exact absEval_unpack n hB (hfit.2 q hq) (hsmall q hq) _
    · exact absEval_unpack n hB (fits_zero n _) (small_zero B n) _

end DPoly

end Nieuwland.Check
