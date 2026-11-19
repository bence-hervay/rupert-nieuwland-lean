import Modules.Check.Polynomial.Expr
import Modules.Check.Polynomial.Pack
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity

/-!
# Range bounds on boxes

The centred-form lower bound of `RESEARCH.md` §7.3 (`range_on` in `code/src/math/smallpoly.rs`):
on `y ∈ [-1, 1]^n`, a polynomial `∑ b_α y^α` is at least
`b₀ + ∑_{α ≠ 0 even} min(0, b_α) − ∑_{α not even} |b_α|`, because `y^α ∈ [0, 1]` for even `α`
and `y^α ∈ [-1, 1]` otherwise (`DPoly.lower_le`).

For the polynomial `y ↦ e(C₀ + H₀ y₀, …, C_{n-1} + H_{n-1} y_{n-1}, D)` of an expression `e`,
the kernel computes this bound without expanding the polynomial: it evaluates `e` once at the
packing point (`Modules/Check/Polynomial/Pack.lean`, `box_packing_lt`) and reads the bound off the digits
with natural-number arithmetic only (`DPoly.penalty`, equal to `DPoly.lower` of the unpacked
polynomial by `DPoly.lower_unpack`). Polynomials with coefficients in a number field are packed one
coordinate per numeral and read in lockstep (`ExactBasis.lowerOf`, `Modules/Check/Number/Ext.lean`); the
packed engine (`Modules/Check/Sign/Engine.lean`) uses this bound where its approximate one may not
decide.
-/

namespace Nieuwland.Check

namespace DPoly

/-- `lower n ev zr p` bounds `m * p(y)` from below for `y ∈ [-1, 1]^n`, where `m` is the value of
the monomial in the variables already read: `m = 1` if `zr` (all exponents so far zero),
`m ∈ [0, 1]` if `ev` (all exponents so far even), and `m ∈ [-1, 1]` otherwise. -/
def lower : (n : ℕ) → Bool → Bool → DPoly n → ℤ
  | 0, ev, zr, p => if zr then toInt p else if ev then min 0 (toInt p) else -|toInt p|
  | n + 1, ev, zr, p => lowerL (lower n) ev zr 0 (toList p)
where
  /-- `lower` along a coefficient list whose first entry has exponent `k`. -/
  lowerL {α : Type} (f : Bool → Bool → α → ℤ) (ev zr : Bool) : ℕ → List α → ℤ
    | _, [] => 0
    | k, a :: as => f (ev && k % 2 == 0) (zr && k == 0) a + lowerL f ev zr (k + 1) as

theorem lower_le : ∀ (n : ℕ) (ev zr : Bool) (p : DPoly n) (y : Fin n → ℝ) (m : ℝ),
    (∀ i, |y i| ≤ 1) → (zr = true → m = 1) → (ev = true → 0 ≤ m) → |m| ≤ 1 →
    (lower n ev zr p : ℝ) ≤ m * eval n p y
  | 0, ev, zr, p, y, m, _, hzr, hev, hm => by
    simp only [lower, eval]
    split_ifs with h₁ h₂
    · simp [hzr h₁]
    · push_cast
      rcases le_or_gt 0 (toInt p : ℝ) with hp | hp
      · rw [min_eq_left hp]; exact mul_nonneg (hev h₂) hp
      · rw [min_eq_right hp.le]
        have := abs_le.mp hm
        nlinarith
    · push_cast
      have h₃ : |m * (toInt p : ℝ)| ≤ |(toInt p : ℝ)| := by
        rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hm
      linarith [neg_abs_le (m * (toInt p : ℝ))]
  | n + 1, ev, zr, p, y, m, hy, hzr, hev, hm => by
    have key : ∀ (k : ℕ) (ps : List (DPoly n)),
        (lower.lowerL (lower n) ev zr k ps : ℝ) ≤
          m * y 0 ^ k * horner (fun q ↦ eval n q (Fin.tail y)) (y 0) ps := by
      intro k ps
      induction ps generalizing k with
      | nil => simp [lower.lowerL]
      | cons a as ih =>
        have h₀ : |y 0| ≤ 1 := hy 0
        have hmk : |m * y 0 ^ k| ≤ 1 := by
          rw [abs_mul, abs_pow]
          calc |m| * |y 0| ^ k ≤ 1 * 1 :=
                mul_le_mul hm (pow_le_one₀ (abs_nonneg _) h₀) (by positivity) zero_le_one
            _ = 1 := one_mul 1
        have ha := lower_le n (ev && k % 2 == 0) (zr && k == 0) a (Fin.tail y) (m * y 0 ^ k)
          (fun i ↦ hy i.succ) (by
            intro h
            simp only [Bool.and_eq_true, beq_iff_eq] at h
            rw [hzr h.1, h.2, pow_zero, mul_one])
          (by
            intro h
            simp only [Bool.and_eq_true, beq_iff_eq] at h
            have hk : Even k := Nat.even_iff.mpr h.2
            exact mul_nonneg (hev h.1) (hk.pow_nonneg _)) hmk
        simp only [lower.lowerL, horner_cons, Int.cast_add]
        have := ih (k + 1)
        rw [pow_succ] at this
        nlinarith [ha, this]
    have := key 0 (toList p)
    simpa [lower, eval] using this

/-! ### Reading the bound off the digits -/

/-- The penalty of the coefficient `d - h`, stored as the digit `d` with bias `h`: `|d - h|` if
`odd`, else `max 0 (h - d)` (truncated subtraction). -/
def digitPenalty (h : ℕ) (odd : Bool) (d : ℕ) : ℕ :=
  match odd with
  | true => Nat.add (Nat.sub d h) (Nat.sub h d)
  | false => Nat.sub h d

/-- The penalties of `m` blocks of `N` of modulus `P`, each read by `f`: block `k` is
`N / P ^ k % P`, read with the flag `odd` for even `k` and `true` for odd `k`. -/
def penaltyL (f : Bool → ℕ → ℕ) (P : ℕ) (odd : Bool) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | 1, N => f odd (Nat.mod N P)
  | m + 2, N => Nat.add (Nat.add (f odd (Nat.mod N P)) (f true (Nat.mod (Nat.div N P) P)))
      (penaltyL f P odd m (Nat.div (Nat.div N P) P))

/-- `penaltyL` with shifts and masks where `P` is a power of two (`divP2`, `modP2`). -/
def penaltyLS (f : Bool → ℕ → ℕ) (P : ℕ) (odd : Bool) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | 1, N => f odd (modP2 N P)
  | m + 2, N =>
    let N₁ := divP2 N P
    Nat.add (Nat.add (f odd (modP2 N P)) (f true (modP2 N₁ P))) (penaltyLS f P odd m (divP2 N₁ P))

theorem penaltyL_eq (f : Bool → ℕ → ℕ) (P : ℕ) (odd : Bool) :
    ∀ m N, penaltyL f P odd m N = penaltyLS f P odd m N
  | 0, _ => rfl
  | 1, N => by rw [penaltyL, penaltyLS, modP2_eq]; rfl
  | m + 2, N => by
    rw [penaltyL, penaltyLS, ← penaltyL_eq f P odd m]
    simp only [modP2_eq, divP2_eq]
    rfl

@[csimp] theorem penaltyL_eq_penaltyLS : @penaltyL = @penaltyLS := by
  funext f P odd m N
  exact penaltyL_eq f P odd m N

/-- The layout of the slots of the shape `e` in `n` variables with digits of `B` bits: for each
variable, the number of blocks and the block modulus. -/
def layout (B : ℕ) : ℕ → List ℕ → List (ℕ × ℕ)
  | 0, _ => []
  | n + 1, e => (e.headD 0 + 1, 1 <<< (B * slots e.tail)) :: layout B n e.tail

theorem layout_zero (B : ℕ) (e : List ℕ) : layout B 0 e = [] := rfl

theorem layout_succ (B n : ℕ) (e : List ℕ) :
    layout B (n + 1) e = (e.headD 0 + 1, 2 ^ (B * slots e.tail)) :: layout B n e.tail := by
  rw [layout, Nat.one_shiftLeft]

/-- The sum of the penalties of the digits of `N` in the layout `ls`, with digit modulus `P₀` and
bias `h`; `odd` says whether the exponents read so far include an odd one. -/
def penalty (h P₀ : ℕ) : List (ℕ × ℕ) → Bool → ℕ → ℕ
  | [], odd, N => digitPenalty h odd (Nat.mod N P₀)
  | (m, P) :: ls, odd, N => penaltyL (penalty h P₀ ls) P odd m N

private theorem nat_mod (a b : ℕ) : Nat.mod a b = a % b := rfl
private theorem nat_div (a b : ℕ) : Nat.div a b = a / b := rfl

/-- **The penalty form of `lower`**: on the polynomial with the `B`-bit digits of `N`, `lower` is
the constant coefficient (if `zr` and positive) minus the penalties. -/
theorem lower_unpack {B : ℕ} (hB : 0 < B) : ∀ (n : ℕ) (e : List ℕ) (ev zr : Bool) (N : ℕ),
    (zr = true → ev = true) →
    lower n ev zr (unpack n e B N) =
      (if zr then ((N % 2 ^ B - 2 ^ (B - 1) : ℕ) : ℤ) else 0) -
        penalty (2 ^ (B - 1)) (2 ^ B) (layout B n e) (!ev) N
  | 0, e, ev, zr, N, hzr => by
    simp only [unpack, lower, toInt_ofInt, layout, penalty, digitPenalty, nat_mod]
    have h2 : ((2 : ℤ) ^ (B - 1)) = ((2 ^ (B - 1) : ℕ) : ℤ) := by push_cast; rfl
    rw [h2]
    generalize N % 2 ^ B = d
    generalize 2 ^ (B - 1) = h
    cases zr <;> cases ev <;> simp_all [abs_eq_max_neg] <;> omega
  | n + 1, e, ev, zr, N, hzr => by
    have ih := lower_unpack hB n e.tail
    set w := B * slots e.tail
    set f := penalty (2 ^ (B - 1)) (2 ^ B) (layout B n e.tail)
    have key : ∀ m N k, k % 2 = 0 →
        lower.lowerL (lower n) ev zr k (unpackL (unpack n e.tail B) w m N) =
          (if zr = true ∧ k = 0 ∧ m ≠ 0 then ((N % 2 ^ w % 2 ^ B - 2 ^ (B - 1) : ℕ) : ℤ)
            else 0) - (penaltyL f (2 ^ w) (!ev) m N : ℤ) := by
      intro m
      induction m using Nat.twoStepInduction with
      | zero => intro N k _; simp [unpackL, lower.lowerL, penaltyL]
      | one =>
        intro N k hk
        simp only [unpackL, lower.lowerL, penaltyL, nat_mod, hk]
        rw [ih _ _ _ (by intro h; simp at h; simp [hzr h.1])]
        by_cases hz : zr = true <;> by_cases hk0 : k = 0 <;> simp [hz, hk0]
      | more m ihm _ =>
        intro N k hk
        have hk1 : (k + 1) % 2 = 1 := by omega
        have hk2 : (k + 2) % 2 = 0 := by omega
        simp only [unpackL, lower.lowerL, penaltyL, nat_mod, nat_div, Nat.add_eq, hk, hk1]
        rw [ih _ _ _ (by intro h; simp at h; simp [hzr h.1]), ih _ _ _ (by simp),
          show k + 1 + 1 = k + 2 by ring, ihm _ _ hk2]
        by_cases hz : zr = true <;> by_cases hk0 : k = 0 <;> simp [hz, hk0] <;> ring
    simp only [unpack, lower, toList_ofList, layout_succ, penalty]
    rw [key _ _ 0 rfl]
    have hw : 2 ^ B ∣ 2 ^ w :=
      Nat.pow_dvd_pow 2 (Nat.le_mul_of_pos_right B (one_le_slots _))
    rw [Nat.mod_mod_of_dvd _ hw]
    by_cases hz : zr = true <;> simp [hz] <;> rfl

end DPoly

/-! ### Boxes in packed form -/

/-- The shapes of the box inputs: variable `i < n` has degree `1` in `yᵢ`; variable `n` is a
constant. -/
def boxShapes (n : ℕ) : List (List ℕ) :=
  (List.range n).map (fun i ↦ List.replicate i 0 ++ [1]) ++ [[]]

/-- Bounds on the absolute coefficient sums of the box inputs. -/
def boxNorms (n : ℕ) (C H : List ℤ) (D : ℤ) : List ℕ :=
  (List.range n).map (fun i ↦ (C.getD i 0).natAbs + (H.getD i 0).natAbs) ++ [D.natAbs]

/-- The box inputs at the packing point. -/
def boxPacked (n : ℕ) (sh : List ℕ) (B : ℕ) (C H : List ℤ) (D : ℤ) : List ℤ :=
  (List.range n).map (fun i ↦ C.getD i 0 + H.getD i 0 * DPoly.packPoint' sh B i) ++ [D]

/-- A number `k` with `N < 2 ^ k`: the first of `64, 128, 256, …` that works (`fuel` doublings),
else `N + 1`. -/
def bitsAbove (N : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => N + 1
  | fuel + 1, k => if N < 2 ^ k then k else bitsAbove N fuel (2 * k)

theorem lt_two_pow_bitsAbove (N : ℕ) : ∀ fuel k : ℕ, N < 2 ^ bitsAbove N fuel k
  | 0, _ => Nat.lt_two_pow_self.trans (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self N))
  | fuel + 1, k => by
    unfold bitsAbove
    split_ifs with h
    · exact h
    · exact lt_two_pow_bitsAbove N fuel (2 * k)

/-- The digit size used for an expression with absolute coefficient sum at most `N`: digits of
`B` bits hold coefficients below `2 ^ (B - 1)` in absolute value. -/
def digitBits (N : ℕ) : ℕ := bitsAbove N 16 64 + 1

theorem lt_two_pow_digitBits (N : ℕ) : N < 2 ^ (digitBits N - 1) := by
  simpa [digitBits] using lt_two_pow_bitsAbove N 16 64

theorem getD_range_map_append {α : Type*} (n : ℕ) (f : ℕ → α) (a d : α) (i : ℕ) :
    ((List.range n).map f ++ [a]).getD i d = if i < n then f i else if i = n then a else d := by
  rw [List.getD_eq_getElem?_getD]
  rcases lt_trichotomy i n with h | rfl | h
  · rw [List.getElem?_append_left (by simpa using h)]
    simp [h]
  · rw [List.getElem?_append_right (by simp)]
    simp
  · rw [List.getElem?_append_right (by simp; omega)]
    have h₁ : ¬i < n := by omega
    have h₂ : i ≠ n := by omega
    simp only [List.length_map, List.length_range, h₁, h₂, ite_false]
    rw [List.getElem?_eq_none (by simp; omega)]
    rfl

/-- The box inputs as polynomials in `y`: `Cᵢ + Hᵢ yᵢ` for `i < n`, then the constant `D`. -/
def boxInputs (n : ℕ) (C H : List ℤ) (D : ℤ) (i : ℕ) : DPoly n :=
  if i < n then DPoly.linear n i (C.getD i 0) (H.getD i 0)
  else if i = n then DPoly.const n D else DPoly.zero n

/-- The point at which a box bound holds: `Cᵢ + Hᵢ yᵢ` for `i < n`, then `D`. -/
def boxEnv {R : Type*} [CommRing R] (n : ℕ) (C H : List ℤ) (D : ℤ) (y : Fin n → R) (i : ℕ) :
    R :=
  if h : i < n then C.getD i 0 + H.getD i 0 * y ⟨i, h⟩ else if i = n then (D : R) else 0

theorem eval_boxInputs {R : Type*} [CommRing R] (n : ℕ) (C H : List ℤ) (D : ℤ) (y : Fin n → R)
    (i : ℕ) : DPoly.eval n (boxInputs n C H D i) y = boxEnv n C H D y i := by
  unfold boxInputs boxEnv
  split_ifs with h₁ h₂ <;> simp [DPoly.eval_linear, h₁]

/-- **Packing an expression on a box.** If the shape of `e` on the box inputs is at most `sh`
and its norm bound at most `nb`, its polynomial in `y` fits `sh`, has absolute coefficient sum at
most `nb`, and its biased packed value (any digit size `B`) is `e` at the packed inputs plus the
offset. -/
theorem box_packing_lt {n : ℕ} (e : Expr) {sh : List ℕ}
    (hsh : DPoly.ShapeLE (e.shape (boxShapes n)) sh) (C H : List ℤ) (D : ℤ) {nb : ℕ}
    (hnb : e.normBound (boxNorms n C H D) ≤ nb) (B : ℕ) :
    DPoly.Fits n (e.toDPoly n (boxInputs n C H D)) sh ∧
      DPoly.absSum n (e.toDPoly n (boxInputs n C H D)) ≤ nb ∧
      e.evalInt (boxPacked n sh B C H D) + DPoly.offset n sh B =
        DPoly.biased n sh B (e.toDPoly n (boxInputs n C H D)) := by
  set T := e.toDPoly n (boxInputs n C H D)
  refine ⟨?_, ?_, ?_⟩
  · refine DPoly.fits_mono n hsh (Expr.fits_toDPoly n _ _ (fun i ↦ ?_) e)
    rw [boxShapes, getD_range_map_append]
    unfold boxInputs
    split_ifs with h₁ h₂
    · exact DPoly.fits_linear n i _ _
    · exact DPoly.fits_const n D _
    · exact DPoly.fits_zero n _
  · refine (Expr.absSum_toDPoly_le n _ _ (fun i ↦ ?_) e).trans hnb
    rw [boxNorms, getD_range_map_append]
    unfold boxInputs
    split_ifs with h₁ h₂
    · exact DPoly.absSum_linear_le n i _ _
    · exact (DPoly.absSum_const n D).le
    · rw [DPoly.absSum_zero]
  · rw [DPoly.biased, Expr.evalInt_eq, Expr.eval_toDPoly]
    congr 2
    funext i
    rw [eval_boxInputs, boxPacked, getD_range_map_append, boxEnv]
    split_ifs with h₁ h₂ <;> simp [DPoly.packPoint]

/-- `box_packing_lt` with the digit size `digitBits nb`, whose digits hold the coefficients. -/
theorem box_packing {n : ℕ} (e : Expr) {sh : List ℕ}
    (hsh : DPoly.ShapeLE (e.shape (boxShapes n)) sh) (C H : List ℤ) (D : ℤ) {nb : ℕ}
    (hnb : e.normBound (boxNorms n C H D) ≤ nb) :
    DPoly.Fits n (e.toDPoly n (boxInputs n C H D)) sh ∧
      DPoly.Small n (digitBits nb) (e.toDPoly n (boxInputs n C H D)) ∧
      e.evalInt (boxPacked n sh (digitBits nb) C H D) + DPoly.offset n sh (digitBits nb) =
        DPoly.biased n sh (digitBits nb) (e.toDPoly n (boxInputs n C H D)) := by
  obtain ⟨hfit, hnorm, hv⟩ := box_packing_lt e hsh C H D hnb (digitBits nb)
  exact ⟨hfit, DPoly.allCoeff_mono n (fun c hc ↦ lt_of_le_of_lt (hc.trans hnorm)
    (lt_two_pow_digitBits nb)) (DPoly.allCoeff_absSum_le n _), hv⟩

end Nieuwland.Check
