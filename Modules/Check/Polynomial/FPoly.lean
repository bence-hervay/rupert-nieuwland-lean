import Modules.Check.Polynomial.SparseTerm

/-!
# Packed polynomials at bounded precision

rupert shifts a polynomial to a box in `f64` intervals (`proof/tree.rs`, `proof/regional.rs`):
the coefficients in the box variables are enclosed with a few significant bits each and never
computed exactly. Here the same shift runs on packed numerals of a small digit size `B`. Horner's
rule on a sparse integer polynomial (`fE`, as `SPoly.evalPk`) multiplies by the box inputs
`Cᵢ + Hᵢ yᵢ` (`mulZ`) and, wherever the digits' absolute sum outgrows `2^p`, floors every digit
by a power of two (`down`: a bias, a shift and a mask, `downN_eq`). An `FP` carries the
numeral, its scale `2^σ`, a bound `m` on its digits' absolute sum, the slot `S` from which its
digits vanish (so that a product by `yᵢ` never reaches the next variable's slots) and the error
`r`: on the cube, the polynomial it stands for is within `r 2^σ` of `2^σ` times the numeral's
polynomial (`Inv`, `fE_inv`). The truncated tests read their digits from it (`trunc`,
`trunc_spec`), as `Lay.truncL` reads the exact values' digits.
-/

open Finset

namespace Nieuwland.Check

open DPoly Num Lay

namespace Num

/-- **A digitwise shift**: shifting right by `k ≤ B` bits and keeping the low `B - k` bits of each
digit divides every digit by `2^k`. -/
theorem num_shr_land {B k L : ℕ} {a : ℕ → ℕ} (hB : 0 < B) (hk : k ≤ B) (ha : Digits B a L) :
    (num B a L >>> k) &&& num B (fun _ ↦ 2 ^ (B - k) - 1) L = num B (fun p ↦ a p >>> k) L := by
  have hm : Digits B (fun _ ↦ 2 ^ (B - k) - 1) L := fun _ _ ↦
    lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)
      (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le B k))
  refine num_eq_of_testBit hB (fun p hp ↦ lt_of_le_of_lt (Nat.shiftRight_le _ _) (ha p hp))
    fun j ↦ ?_
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_num hB ha, testBit_num hB hm,
    Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  have hj := Nat.div_add_mod j B
  have hr := Nat.mod_lt j hB
  set u := j / B
  set v := j % B
  by_cases hv : v < B - k
  · have h₁ : (k + j) / B = u := by
      rw [show k + j = (v + k) + B * u by omega, Nat.add_mul_div_left _ _ hB,
        Nat.div_eq_of_lt (by omega), zero_add]
    have h₂ : (k + j) % B = k + v := by
      rw [show k + j = (v + k) + B * u by omega, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by omega)]
      omega
    rw [h₁, h₂]
    by_cases hu : u < L <;> simp [hv, hu]
  · simp only [hv, decide_false, Bool.and_false]
    by_cases hu : u < L
    · have : (a u).testBit (k + v) = false := testBit_of_digit (ha u hu) (by omega)
      simp [this]
    · simp [hu]

end Num

/-! ### Packed polynomials at bounded precision -/

namespace FPoly

/-- A packed polynomial at bounded precision: the signed numeral `N` (digit size `B` of the
context), standing for `2^σ` times its polynomial, within `r 2^σ` on the cube, with absolute digit
sum at most `m` and digits zero from slot `S` on (`Inv`). -/
structure FP where
  /-- The signed numeral of the digits. -/
  N : ℤ
  /-- The scale: the numeral stands for `2^σ` times its polynomial. -/
  σ : ℕ
  /-- The error in units of `2^σ`, on the cube. -/
  r : ℕ
  /-- A bound on the digits' absolute sum. -/
  m : ℕ
  /-- The slot from which the digits vanish. -/
  S : ℕ
deriving Inhabited

/-- The context: the shape `sh` of the layout, the box inputs `Cᵢ + Hᵢ yᵢ`, the digit size `B`
and the precision `p` (about `p` bits of every value are kept). -/
structure Ctx where
  /-- The shape of the layout. -/
  sh : List ℕ
  /-- The box inputs' constants `Cᵢ`. -/
  C : List ℤ
  /-- The box inputs' half-widths `Hᵢ`. -/
  H : List ℤ
  /-- The digit size. -/
  B : ℕ
  /-- The precision: about `p` bits of every value are kept. -/
  p : ℕ

/-- The zero polynomial, exactly. -/
def zero : FP := ⟨0, 0, 0, 0, 0⟩

/-- `⌈x / 2^k⌉`. -/
def cdiv (x k : ℕ) : ℕ := bif x == 0 then 0 else ((x - 1) >>> k) + 1

/-- The digit `1` in the slots `q < S` (digit size `B`): `(2^(B S) - 1) / (2^B - 1)`. -/
def onesS (B S : ℕ) : ℕ := ((1 <<< (B * S)) - 1) / ((1 <<< B) - 1)

/-- The numeral of the digits `⌊d_q / 2^k⌋` of a signed numeral of `S` digits `d_q` (`downN_eq`):
biased by `2^(B-1)` in every digit, shifted right by `k` bits, masked to the low `B - k` bits of
every digit, unbiased by `2^(B-1-k)`. -/
def downN (B k S : ℕ) (N : ℤ) : ℤ :=
  let o := onesS B S
  ((((N + ((o <<< (B - 1) : ℕ) : ℤ)).toNat >>> k) &&& ((o <<< (B - k)) - o) : ℕ) : ℤ) -
    ((o <<< (B - 1 - k) : ℕ) : ℤ)

/-- The scale raised by `2^k`: every digit floored by `2^k` (`downN`), or zero where the digits'
absolute sum is below `2^k`. -/
def down (B k : ℕ) (x : FP) : FP :=
  bif k == 0 then x
  else bif x.m >>> k == 0 || decide (B ≤ k + 1) then ⟨0, x.σ + k, cdiv (x.r + x.m) k, 0, 0⟩
  else ⟨downN B k x.S x.N, x.σ + k, cdiv x.r k + x.S, cdiv x.m k + x.S, x.S⟩

/-- At most `p` bits: the scale raised until the absolute digit sum is below about `2^p`. -/
def norm (c : Ctx) (x : FP) : FP := down c.B (Nat.log2 x.m + 1 - c.p) x

/-- Whether `x` is exactly zero. -/
def isZero (x : FP) : Bool := x.m == 0 && x.r == 0

/-- The sum, at the larger scale; `none` if the digits could leave their range. -/
def add (c : Ctx) (x y : FP) : Option FP :=
  bif isZero x then some y else
  bif isZero y then some x else
  let σ := max x.σ y.σ
  let x' := down c.B (σ - x.σ) x
  let y' := down c.B (σ - y.σ) y
  bif decide (x'.m + y'.m < 2 ^ (c.B - 1)) then
    some (norm c ⟨x'.N + y'.N, σ, x'.r + y'.r, x'.m + y'.m, max x'.S y'.S⟩)
  else none

/-- The product by the box input `Cᵢ + Hᵢ yᵢ`: the digits times `Cᵢ`, plus those times `Hᵢ`
moved up one power of `yᵢ`; `none` if `x` could have a term of the top degree in `yᵢ` or the
digits could leave their range. -/
def mulZ (c : Ctx) (i : ℕ) (x : FP) : Option FP :=
  let a := c.C.getD i 0
  let b := c.H.getD i 0
  let g := a.natAbs + b.natAbs
  bif b == 0 then
    bif decide (x.m * g < 2 ^ (c.B - 1)) then
      some (norm c ⟨x.N * a, x.σ, x.r * g, x.m * g, x.S⟩)
    else none
  else
    let st := Lay.stride c.sh i
    bif decide (x.S ≤ Lay.deg c.sh i * st) && decide (x.m * g < 2 ^ (c.B - 1)) then
      some (norm c ⟨x.N * a + Lay.shl (x.N * b) (c.B * st), x.σ, x.r * g, x.m * g, x.S + st⟩)
    else none

/-- The constant `k` at the precision `p`. -/
def const (c : Ctx) (k : ℤ) : FP :=
  let σ := Nat.log2 k.natAbs + 1 - c.p
  let N := k >>> σ
  ⟨N, σ, bif σ == 0 then 0 else 1, N.natAbs, 1⟩

/-- `x` plus the constant `k`. -/
def addC (c : Ctx) (k : ℤ) (x : FP) : Option FP :=
  bif k == 0 then some x else
  bif decide ((const c k).m < 2 ^ (c.B - 1)) then add c (const c k) x else none

/-- **Horner's rule at bounded precision** (`SPoly.evalPk`; `fE_inv`): the terms `ts` (exponents
of the variables `i, i + 1, …`) at the box inputs, as a packed polynomial in the `yᵢ`. -/
def fE (c : Ctx) : ℕ → ℕ → SPoly ℤ → Option FP
  | 0, _, ts => bif ts.isEmpty then some zero else none
  | fuel + 1, i, ts =>
    let z := ts.filterMap SPoly.zTerm
    let s := ts.filterMap SPoly.sTerm
    (bif z.isEmpty then some zero else fE c fuel (i + 1) z).bind fun v ↦
    (bif s.isEmpty then some zero else (fE c fuel i s).bind (mulZ c i)).bind fun w ↦
    (add c v w).bind (addC c (ts.filterMap SPoly.cTerm).sum)

/-- **A truncation from a packed polynomial at bounded precision** (`trunc_spec`): the signed
numeral of digit size `B'` of the digits `⌊d_q m 2^e / 2^k⌋` (`e = σ - s`, `k = s - σ`; `truncL`)
with their absolute sum, and the error in units of `2^s`: `m` times the value of `x` is within it
of `2^s` times the truncated polynomial on the cube. -/
def trunc (c : Ctx) (B' s : ℕ) (m : ℤ) (x : FP) : (ℤ × ℕ) × ℕ :=
  let e := x.σ - s
  let k := s - x.σ
  (Lay.truncL c.B B' k (2 ^ (c.B - 1)) (m * 2 ^ e) (slots c.sh)
      (x.N + (Lay.offN c.B c.sh : ℤ)).toNat,
    slots c.sh + cdiv (m.natAbs * x.r * 2 ^ e) k)


/-! ### Numerals -/

theorem le_cdiv_mul (x k : ℕ) : x ≤ cdiv x k * 2 ^ k := by
  unfold cdiv
  cases h : x == 0
  · have hx : x ≠ 0 := by simpa using h
    simp only [Bool.cond_false, Nat.shiftRight_eq_div_pow]
    have := Nat.lt_div_mul_add (a := x - 1) (Nat.two_pow_pos k)
    rw [Nat.add_mul, one_mul]
    omega
  · rw [beq_iff_eq] at h
    simp [h]

theorem num_ones_mul (B : ℕ) : ∀ S, num B (fun _ ↦ 1) S * (2 ^ B - 1) = 2 ^ (B * S) - 1
  | 0 => by simp [num_zero]
  | S + 1 => by
    rw [num_succ, Nat.add_mul, num_ones_mul B S, one_mul, show B * (S + 1) = B * S + B by ring,
      pow_add, Nat.mul_sub, mul_one]
    have h₁ : 1 ≤ 2 ^ (B * S) := Nat.one_le_two_pow
    have h₂ : 2 ^ (B * S) ≤ 2 ^ (B * S) * 2 ^ B := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos B)
    omega

theorem onesS_eq {B : ℕ} (hB : 0 < B) (S : ℕ) : onesS B S = num B (fun _ ↦ 1) S := by
  unfold onesS
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, one_mul, one_mul, ← num_ones_mul B S]
  have : 1 < 2 ^ B := Nat.one_lt_two_pow (by omega)
  exact Nat.mul_div_cancel _ (by omega)

theorem ones_shiftLeft (B S t : ℕ) :
    num B (fun _ ↦ 1) S <<< t = num B (fun _ ↦ 2 ^ t) S := by
  rw [Nat.shiftLeft_eq, mul_comm, num_mul]
  simp

/-- **Flooring every digit** (`downN`): for digits in range and `k < B`, the digits
`⌊d_q / 2^k⌋`. -/
theorem downN_eq {B k S : ℕ} (hk : k + 1 ≤ B) {d : ℕ → ℤ}
    (hd : ∀ q < S, -2 ^ (B - 1) ≤ d q ∧ d q < 2 ^ (B - 1)) :
    downN B k S (snum B d S) = snum B (fun q ↦ d q / 2 ^ k) S := by
  have hB : 0 < B := by omega
  obtain ⟨hbias, hdig⟩ := snum_add_bias hB hd
  have hm : (num B (fun _ ↦ 1) S <<< (B - k)) - num B (fun _ ↦ 1) S =
      num B (fun _ ↦ 2 ^ (B - k) - 1) S := by
    rw [ones_shiftLeft]
    refine Nat.sub_eq_of_eq_add ?_
    rw [num_add]
    exact num_congr fun q _ ↦ (Nat.sub_add_cancel Nat.one_le_two_pow).symm
  unfold downN
  dsimp only
  rw [onesS_eq hB, ones_shiftLeft, hbias, Int.toNat_natCast, hm, num_shr_land hB (by omega) hdig,
    ones_shiftLeft, snum_natCast, snum_natCast, snum_sub]
  refine snum_congr fun q hq ↦ ?_
  have h₀ : 0 ≤ d q + 2 ^ (B - 1) := by linarith [(hd q hq).1]
  have hp : (2 : ℤ) ^ (B - 1) = 2 ^ k * 2 ^ (B - 1 - k) := by
    rw [← pow_add]; congr 1; omega
  rw [Nat.shiftRight_eq_div_pow]
  push_cast
  rw [Int.toNat_of_nonneg h₀, hp, Int.add_mul_ediv_left _ _ (by positivity)]
  ring


/-! ### Digit sums -/

/-- A sum of absolute values of digits that vanish from slot `S` on. -/
theorem l1_eq_of_vanish {sh : List ℕ} {d : ℕ → ℤ} {S : ℕ} (hS : S ≤ slots sh)
    (h0 : ∀ q, S ≤ q → d q = 0) : l1 sh d = ∑ q ∈ range S, (d q).natAbs := by
  unfold l1
  rw [Lay.natAbs_sum_split _ hS]
  simp [h0]

theorem l1_le_of_vanish {sh : List ℕ} {e : ℕ → ℤ} {S M : ℕ} (hS : S ≤ slots sh)
    (h0 : ∀ q, S ≤ q → e q = 0) (hM : ∀ q, (e q).natAbs ≤ M) : l1 sh e ≤ S * M := by
  rw [l1_eq_of_vanish hS h0]
  calc ∑ q ∈ range S, (e q).natAbs ≤ ∑ _q ∈ range S, M := sum_le_sum fun q _ ↦ hM q
    _ = S * M := by rw [sum_const, card_range, smul_eq_mul]

/-- Every digit is at most the digits' absolute sum. -/
theorem natAbs_le_l1 {sh : List ℕ} {d : ℕ → ℤ} {S : ℕ} (hS : S ≤ slots sh)
    (h0 : ∀ q, S ≤ q → d q = 0) (q : ℕ) : (d q).natAbs ≤ l1 sh d := by
  by_cases hq : q < slots sh
  · have := abs_coeff_le_l1 (sh := sh) d hq
    exact_mod_cast this
  · rw [h0 q (by omega)]
    exact Nat.zero_le _

theorem natAbs_ediv_le (a : ℤ) {K : ℕ} (_hK : 0 < K) :
    (a / (K : ℤ)).natAbs ≤ a.natAbs / K + 1 := by
  rw [Int.natAbs_ediv, Int.natAbs_natCast]
  split_ifs <;> omega

/-- The digits' absolute sum after flooring by `2^k`. -/
theorem l1_ediv_le {sh : List ℕ} {d : ℕ → ℤ} {S m : ℕ} (hS : S ≤ slots sh)
    (h0 : ∀ q, S ≤ q → d q = 0) (hm : l1 sh d ≤ m) (k : ℕ) :
    l1 sh (fun q ↦ d q / 2 ^ k) ≤ cdiv m k + S := by
  have hK : 0 < 2 ^ k := Nat.two_pow_pos k
  rw [l1_eq_of_vanish hS (d := fun q ↦ d q / 2 ^ k) fun q hq ↦ by simp [h0 q hq]]
  rw [l1_eq_of_vanish hS h0] at hm
  have h₁ : ∀ q ∈ range S, (d q / 2 ^ k).natAbs ≤ (d q).natAbs / 2 ^ k + 1 := fun q _ ↦ by
    have := natAbs_ediv_le (d q) hK
    push_cast at this
    exact this
  have h₂ : ∑ q ∈ range S, (d q).natAbs / 2 ^ k ≤ m / 2 ^ k := by
    rw [Nat.le_div_iff_mul_le hK, sum_mul]
    exact (sum_le_sum fun q _ ↦ Nat.div_mul_le_self _ _).trans hm
  have h₃ : m / 2 ^ k ≤ cdiv m k := Nat.div_le_of_le_mul (by
    have := le_cdiv_mul m k
    rwa [Nat.mul_comm] at this)
  calc ∑ q ∈ range S, (d q / 2 ^ k).natAbs
      ≤ ∑ q ∈ range S, ((d q).natAbs / 2 ^ k + 1) := sum_le_sum h₁
    _ = ∑ q ∈ range S, (d q).natAbs / 2 ^ k + S := by rw [sum_add_distrib]; simp
    _ ≤ cdiv m k + S := by omega

/-- A signed numeral of digits that vanish from slot `S` on has any length from `S`. -/
theorem snum_extend {B S T : ℕ} {d : ℕ → ℤ} (h0 : ∀ q, S ≤ q → d q = 0) (hST : S ≤ T) :
    snum B d S = snum B d T := by
  rw [Lay.snum_split B d hST]
  have : snum B (fun q ↦ d (S + q)) (T - S) = 0 := by
    unfold snum
    exact sum_eq_zero fun q _ ↦ by simp [h0 (S + q) (by omega)]
  rw [this, zero_mul, add_zero]

/-! ### The invariant -/

/-- The box inputs `Cᵢ + Hᵢ yᵢ` at `y`. -/
noncomputable def X (c : Ctx) (y : ℕ → ℝ) (i : ℕ) : ℝ :=
  (c.C.getD i 0 : ℝ) + (c.H.getD i 0 : ℝ) * y i

/-- **`x` stands for `V` on the cube**: its numeral has digits `d` below `2^(B-1)` in absolute
value, zero from slot `S ≤ slots` on, with absolute sum at most `m`, and `2^σ` times their
polynomial is within `r 2^σ` of `V` on the cube. -/
def Inv (c : Ctx) (V : (ℕ → ℝ) → ℝ) (x : FP) : Prop :=
  x.S ≤ slots c.sh ∧ ∃ d : ℕ → ℤ, x.N = snum c.B d x.S ∧ (∀ q, x.S ≤ q → d q = 0) ∧
    (∀ q, (d q).natAbs < 2 ^ (c.B - 1)) ∧ l1 c.sh d ≤ x.m ∧
    ∀ y : ℕ → ℝ, (∀ i, |y i| ≤ 1) → |V y - 2 ^ x.σ * pv c.sh d y| ≤ x.r * 2 ^ x.σ

variable {c : Ctx}

theorem inv_zero (c : Ctx) : Inv c (fun _ ↦ 0) zero :=
  ⟨Nat.zero_le _, fun _ ↦ 0, by simp [zero, snum], fun _ _ ↦ rfl,
    fun _ ↦ by simp, by simp [l1, zero], fun y _ ↦ by simp [zero, pv_zero]⟩

theorem Inv.congr {V W : (ℕ → ℝ) → ℝ} {x : FP} (hx : Inv c V x)
    (h : ∀ y : ℕ → ℝ, (∀ i, |y i| ≤ 1) → V y = W y) : Inv c W x := by
  obtain ⟨hS, d, hN, h0, hr, hl, he⟩ := hx
  exact ⟨hS, d, hN, h0, hr, hl, fun y hy ↦ by rw [← h y hy]; exact he y hy⟩

/-- An exact zero stands for `0`. -/
theorem Inv.eq_zero {V : (ℕ → ℝ) → ℝ} {x : FP} (hx : Inv c V x) (h : isZero x = true)
    {y : ℕ → ℝ} (hy : ∀ i, |y i| ≤ 1) : V y = 0 := by
  obtain ⟨hS, d, -, h0, -, hl, he⟩ := hx
  simp only [isZero, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hm, hr⟩ := h
  have hd : ∀ q < slots c.sh, d q = 0 := fun q _ ↦ by
    have := natAbs_le_l1 hS h0 q
    omega
  have := he y hy
  rw [pv_congr hd, pv_zero, hr] at this
  simpa using this

theorem down_σ (B k : ℕ) (x : FP) : (down B k x).σ = x.σ + k := by
  unfold down
  cases hk : k == 0
  · simp only [Bool.cond_false]
    cases x.m >>> k == 0 || decide (B ≤ k + 1) <;> rfl
  · rw [beq_iff_eq] at hk
    simp [hk]

/-- **Flooring keeps the invariant.** -/
theorem inv_down {V : (ℕ → ℝ) → ℝ} {x : FP} (hx : Inv c V x) (k : ℕ) :
    Inv c V (down c.B k x) := by
  obtain ⟨hS, d, hN, h0, hr, hl, he⟩ := hx
  have hK : (0 : ℝ) < 2 ^ k := by positivity
  unfold down
  cases hk : k == 0
  · simp only [Bool.cond_false]
    cases hz : x.m >>> k == 0 || decide (c.B ≤ k + 1)
    · -- every digit floored
      simp only [Bool.cond_false]
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_le] at hz
      have hrange : ∀ q < x.S, -2 ^ (c.B - 1) ≤ d q ∧ d q < 2 ^ (c.B - 1) := fun q _ ↦ by
        have := hr q
        have h' : |d q| < 2 ^ (c.B - 1) := by
          rw [Int.abs_eq_natAbs]; exact_mod_cast this
        exact ⟨by linarith [(abs_lt.mp h').1], (abs_lt.mp h').2⟩
      refine ⟨hS, fun q ↦ d q / 2 ^ k, ?_, fun q hq ↦ by simp [h0 q hq], fun q ↦ ?_,
        l1_ediv_le hS h0 hl k, fun y hy ↦ ?_⟩
      · rw [hN]
        exact downN_eq (by omega) hrange
      · exact lt_of_le_of_lt (Int.natAbs_ediv_le_natAbs _ _) (hr q)
      · -- the error: `r 2^σ` and at most `2^k` in each of `S` digits
        have hpv : pv c.sh d y - 2 ^ k * pv c.sh (fun q ↦ d q / 2 ^ k) y =
            pv c.sh (fun q ↦ d q % 2 ^ k) y := by
          unfold pv
          rw [mul_sum, ← sum_sub_distrib]
          refine sum_congr rfl fun q _ ↦ ?_
          have := congrArg (fun z : ℤ ↦ (z : ℝ)) (Int.mul_ediv_add_emod (d q) (2 ^ k))
          have h' : ((d q : ℤ) : ℝ) =
              ((d q % 2 ^ k : ℤ) : ℝ) + 2 ^ k * ((d q / 2 ^ k : ℤ) : ℝ) := by
            push_cast at this ⊢; linarith
          rw [h']
          ring
        have hmod : |pv c.sh (fun q ↦ d q % 2 ^ k) y| ≤ x.S * 2 ^ k := by
          refine (abs_pv_le_l1 c.sh _ hy).trans ?_
          have := l1_le_of_vanish (sh := c.sh) (e := fun q ↦ d q % 2 ^ k) (M := 2 ^ k) hS
            (fun q hq ↦ by simp [h0 q hq]) (fun q ↦ by
              have h₁ := Int.emod_nonneg (d q) (b := 2 ^ k) (by positivity)
              have h₂ := Int.emod_lt_of_pos (d q) (b := 2 ^ k) (by positivity)
              have h₃ : ((d q % 2 ^ k).natAbs : ℤ) = d q % 2 ^ k := Int.natAbs_of_nonneg h₁
              have : ((d q % 2 ^ k).natAbs : ℤ) ≤ ((2 ^ k : ℕ) : ℤ) := by
                rw [h₃]; push_cast; exact h₂.le
              exact_mod_cast this)
          exact_mod_cast this
        have hc := le_cdiv_mul x.r k
        have hc' : (x.r : ℝ) ≤ cdiv x.r k * 2 ^ k := by exact_mod_cast hc
        have h₁ := he y hy
        have e₁ : V y - 2 ^ (x.σ + k) * pv c.sh (fun q ↦ d q / 2 ^ k) y =
            (V y - 2 ^ x.σ * pv c.sh d y) + 2 ^ x.σ * pv c.sh (fun q ↦ d q % 2 ^ k) y := by
          rw [← hpv, pow_add]; ring
        simp only
        rw [e₁]
        calc |(V y - 2 ^ x.σ * pv c.sh d y) + 2 ^ x.σ * pv c.sh (fun q ↦ d q % 2 ^ k) y|
            ≤ |V y - 2 ^ x.σ * pv c.sh d y| + 2 ^ x.σ * |pv c.sh (fun q ↦ d q % 2 ^ k) y| := by
              refine (abs_add_le _ _).trans ?_
              rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ x.σ)]
          _ ≤ x.r * 2 ^ x.σ + 2 ^ x.σ * (x.S * 2 ^ k) := by gcongr
          _ ≤ (cdiv x.r k * 2 ^ k) * 2 ^ x.σ + 2 ^ x.σ * (x.S * 2 ^ k) := by gcongr
          _ = ((cdiv x.r k + x.S : ℕ) : ℝ) * 2 ^ (x.σ + k) := by push_cast; rw [pow_add]; ring
    · -- zero
      simp only [Bool.cond_true]
      refine ⟨Nat.zero_le _, fun _ ↦ 0, by simp [snum], fun _ _ ↦ rfl, fun _ ↦ by simp,
        by simp [l1], fun y hy ↦ ?_⟩
      have h₁ := he y hy
      have h₂ := abs_pv_le_l1 c.sh d hy
      have h₃ : (l1 c.sh d : ℝ) ≤ x.m := by exact_mod_cast hl
      have hc : ((x.r + x.m : ℕ) : ℝ) ≤ cdiv (x.r + x.m) k * 2 ^ k := by
        exact_mod_cast le_cdiv_mul (x.r + x.m) k
      have hσ : (0 : ℝ) < 2 ^ x.σ := by positivity
      simp only [pv_zero, mul_zero, sub_zero]
      calc |V y| ≤ |V y - 2 ^ x.σ * pv c.sh d y| + 2 ^ x.σ * |pv c.sh d y| := by
            have := abs_sub_abs_le_abs_sub (V y) (2 ^ x.σ * pv c.sh d y)
            rw [abs_mul, abs_of_pos hσ] at this
            linarith
        _ ≤ x.r * 2 ^ x.σ + 2 ^ x.σ * x.m := by gcongr; exact h₂.trans h₃
        _ = ((x.r + x.m : ℕ) : ℝ) * 2 ^ x.σ := by push_cast; ring
        _ ≤ (cdiv (x.r + x.m) k * 2 ^ k) * 2 ^ x.σ := by gcongr
        _ = (cdiv (x.r + x.m) k : ℝ) * 2 ^ (x.σ + k) := by rw [pow_add]; ring
  · rw [beq_iff_eq] at hk
    subst hk
    exact ⟨hS, d, hN, h0, hr, hl, he⟩

theorem inv_norm {V : (ℕ → ℝ) → ℝ} {x : FP} (hx : Inv c V x) : Inv c V (norm c x) :=
  inv_down hx _


/-- **Sums keep the invariant.** -/
theorem inv_add {V W : (ℕ → ℝ) → ℝ} {x y z : FP} (hx : Inv c V x) (hy : Inv c W y)
    (h : add c x y = some z) : Inv c (fun t ↦ V t + W t) z := by
  unfold add at h
  cases hzx : isZero x
  · cases hzy : isZero y
    · simp only [hzx, hzy, Bool.cond_false] at h
      have hx' := inv_down hx (max x.σ y.σ - x.σ)
      have hy' := inv_down hy (max x.σ y.σ - y.σ)
      have hσx : (down c.B (max x.σ y.σ - x.σ) x).σ = max x.σ y.σ := by rw [down_σ]; omega
      have hσy : (down c.B (max x.σ y.σ - y.σ) y).σ = max x.σ y.σ := by rw [down_σ]; omega
      set σ := max x.σ y.σ
      set x' := down c.B (σ - x.σ) x
      set y' := down c.B (σ - y.σ) y
      cases hm : decide (x'.m + y'.m < 2 ^ (c.B - 1))
      · simp [hm] at h
      · simp only [hm, Bool.cond_true, Option.some.injEq] at h
        subst h
        refine inv_norm ?_
        obtain ⟨hS1, d1, hN1, h01, hr1, hl1, he1⟩ := hx'
        obtain ⟨hS2, d2, hN2, h02, hr2, hl2, he2⟩ := hy'
        have hm' : x'.m + y'.m < 2 ^ (c.B - 1) := of_decide_eq_true hm
        refine ⟨max_le hS1 hS2, fun q ↦ d1 q + d2 q, ?_, fun q hq ↦ ?_, fun q ↦ ?_, ?_,
          fun t ht ↦ ?_⟩
        · simp only
          rw [hN1, hN2, snum_extend h01 (le_max_left x'.S y'.S),
            snum_extend h02 (le_max_right x'.S y'.S), snum_add]
        · simp only at hq
          change d1 q + d2 q = 0
          rw [h01 q (le_of_max_le_left hq), h02 q (le_of_max_le_right hq), add_zero]
        · change (d1 q + d2 q).natAbs < _
          have h₁ := natAbs_le_l1 hS1 h01 q
          have h₂ := natAbs_le_l1 hS2 h02 q
          have h₃ := Int.natAbs_add_le (d1 q) (d2 q)
          omega
        · exact (l1_add_le c.sh d1 d2).trans (Nat.add_le_add hl1 hl2)
        · have e1 := he1 t ht
          have e2 := he2 t ht
          rw [hσx] at e1
          rw [hσy] at e2
          simp only
          rw [pv_add]
          have : V t + W t - 2 ^ σ * (pv c.sh d1 t + pv c.sh d2 t) =
              (V t - 2 ^ σ * pv c.sh d1 t) + (W t - 2 ^ σ * pv c.sh d2 t) := by ring
          rw [this]
          calc _ ≤ |V t - 2 ^ σ * pv c.sh d1 t| + |W t - 2 ^ σ * pv c.sh d2 t| := abs_add_le _ _
            _ ≤ x'.r * 2 ^ σ + y'.r * 2 ^ σ := add_le_add e1 e2
            _ = ((x'.r + y'.r : ℕ) : ℝ) * 2 ^ σ := by push_cast; ring
    · simp only [hzx, hzy, Bool.cond_false, Bool.cond_true, Option.some.injEq] at h
      subst h
      exact hx.congr fun t ht ↦ by rw [hy.eq_zero hzy ht, add_zero]
  · simp only [hzx, Bool.cond_true, Option.some.injEq] at h
    subst h
    exact hy.congr fun t ht ↦ by rw [hx.eq_zero hzx ht, zero_add]

/-- The absolute sum of a product by `a + b yᵢ`. -/
theorem l1_mulL_le (sh : List ℕ) (i : ℕ) (a b : ℤ) (d : ℕ → ℤ) :
    l1 sh (mulL sh i a b d) ≤ (a.natAbs + b.natAbs) * l1 sh d := by
  set L := slots sh
  set st := stride sh i
  have hst : st ≤ L := Nat.le_of_dvd (slots_pos sh) (stride_dvd sh i)
  have h₁ : ∀ q, (mulL sh i a b d q).natAbs ≤
      a.natAbs * (d q).natAbs + (if st ≤ q then b.natAbs * (d (q - st)).natAbs else 0) := by
    intro q
    unfold mulL
    split_ifs with h0 hq hq
    · simp [Int.natAbs_mul]
    · simp [Int.natAbs_mul]
    · rw [← Int.natAbs_mul, ← Int.natAbs_mul]
      exact Int.natAbs_add_le _ _
    · exfalso
      apply h0
      unfold ex
      rw [Nat.div_eq_of_lt (by omega)]
      simp
  have h₂ : ∑ q ∈ range L, (if st ≤ q then b.natAbs * (d (q - st)).natAbs else 0) ≤
      b.natAbs * ∑ q ∈ range L, (d q).natAbs := by
    have e : ∑ q ∈ range L, (if st ≤ q then b.natAbs * (d (q - st)).natAbs else 0) =
        ∑ q ∈ range (L - st), b.natAbs * (d q).natAbs := by
      conv_lhs => rw [show L = st + (L - st) by omega]
      rw [sum_range_add]
      have : ∑ q ∈ range st, (if st ≤ q then b.natAbs * (d (q - st)).natAbs else 0) = 0 :=
        sum_eq_zero fun q hq ↦ by simp [show ¬ st ≤ q by simpa using hq]
      rw [this, zero_add]
      exact sum_congr rfl fun q _ ↦ by simp
    rw [e, ← mul_sum]
    exact Nat.mul_le_mul_left _ (sum_le_sum_of_subset (range_subset_range.mpr (Nat.sub_le L st)))
  unfold l1
  calc ∑ q ∈ range L, (mulL sh i a b d q).natAbs
      ≤ ∑ q ∈ range L, (a.natAbs * (d q).natAbs +
          (if st ≤ q then b.natAbs * (d (q - st)).natAbs else 0)) := sum_le_sum fun q _ ↦ h₁ q
    _ = a.natAbs * ∑ q ∈ range L, (d q).natAbs +
          ∑ q ∈ range L, (if st ≤ q then b.natAbs * (d (q - st)).natAbs else 0) := by
        rw [sum_add_distrib, mul_sum]
    _ ≤ a.natAbs * ∑ q ∈ range L, (d q).natAbs + b.natAbs * ∑ q ∈ range L, (d q).natAbs :=
        Nat.add_le_add_left h₂ _
    _ = (a.natAbs + b.natAbs) * ∑ q ∈ range L, (d q).natAbs := by ring

theorem abs_X_le (c : Ctx) {t : ℕ → ℝ} (ht : ∀ i, |t i| ≤ 1) (i : ℕ) :
    |X c t i| ≤ ((c.C.getD i 0).natAbs + (c.H.getD i 0).natAbs : ℕ) := by
  unfold X
  push_cast
  rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
  calc |(c.C.getD i 0 : ℝ) + (c.H.getD i 0 : ℝ) * t i|
      ≤ |(c.C.getD i 0 : ℝ)| + |(c.H.getD i 0 : ℝ)| * |t i| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul]
    _ ≤ |(c.C.getD i 0 : ℝ)| + |(c.H.getD i 0 : ℝ)| * 1 := by gcongr; exact ht i
    _ = _ := by ring

/-- **Products by a box input keep the invariant.** -/
theorem inv_mulZ {V : (ℕ → ℝ) → ℝ} {x z : FP} (hx : Inv c V x) {i : ℕ}
    (h : mulZ c i x = some z) : Inv c (fun t ↦ X c t i * V t) z := by
  obtain ⟨hS, d, hN, h0, hr, hl, he⟩ := hx
  unfold mulZ at h
  dsimp only at h
  have hg : ∀ t : ℕ → ℝ, (∀ j, |t j| ≤ 1) →
      |X c t i| ≤ ((c.C.getD i 0).natAbs + (c.H.getD i 0).natAbs : ℕ) :=
    fun t ht ↦ abs_X_le c ht i
  set a := c.C.getD i 0 with ha
  set b := c.H.getD i 0 with hb'
  set g := a.natAbs + b.natAbs with hgdef
  have herr : ∀ (P : (ℕ → ℝ) → ℝ), (∀ t, (∀ j, |t j| ≤ 1) → P t = X c t i * pv c.sh d t) →
      ∀ t, (∀ j, |t j| ≤ 1) →
        |X c t i * V t - 2 ^ x.σ * P t| ≤ ((x.r * g : ℕ) : ℝ) * 2 ^ x.σ := by
    intro P hP t ht
    rw [hP t ht]
    have : X c t i * V t - 2 ^ x.σ * (X c t i * pv c.sh d t) =
        X c t i * (V t - 2 ^ x.σ * pv c.sh d t) := by ring
    rw [this, abs_mul]
    calc |X c t i| * |V t - 2 ^ x.σ * pv c.sh d t| ≤ (g : ℝ) * (x.r * 2 ^ x.σ) :=
          mul_le_mul (hg t ht) (he t ht) (abs_nonneg _) (by positivity)
      _ = ((x.r * g : ℕ) : ℝ) * 2 ^ x.σ := by push_cast; ring
  have hM : ∀ q, (d q).natAbs ≤ l1 c.sh d := natAbs_le_l1 hS h0
  cases hb : b == 0
  · -- a product with a shift
    simp only [hb, Bool.cond_false] at h
    have hb0 : b ≠ 0 := by simpa using hb
    cases hc : decide (x.S ≤ Lay.deg c.sh i * Lay.stride c.sh i) &&
      decide (x.m * g < 2 ^ (c.B - 1))
    · simp [hc] at h
    · simp only [hc, Bool.cond_true, Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hdeg, hmg⟩ := hc
      refine inv_norm ?_
      set st := Lay.stride c.sh i
      have hst : 0 < st := stride_pos c.sh i
      have htop : ∀ q < slots c.sh, ex c.sh i q = deg c.sh i → d q = 0 := by
        intro q _ hq
        apply h0
        have h₁ : deg c.sh i ≤ q / st := by rw [← hq]; exact Nat.mod_le _ _
        have h₂ : deg c.sh i * st ≤ q :=
          (Nat.mul_le_mul_right st h₁).trans (Nat.div_mul_le_self q st)
        omega
      have hL : x.S + st ≤ slots c.sh := by
        have h₁ : st * (deg c.sh i + 1) ≤ slots c.sh :=
          Nat.le_of_dvd (slots_pos c.sh) (stride_mul_dvd c.sh i)
        have h₂ : st * (deg c.sh i + 1) = deg c.sh i * st + st := by ring
        omega
      have h0' : ∀ q, x.S + st ≤ q → mulL c.sh i a b d q = 0 := by
        intro q hq
        unfold mulL
        rw [h0 q (by omega)]
        split_ifs
        · simp
        · rw [h0 (q - st) (by omega)]
          simp
      refine ⟨hL, mulL c.sh i a b d, ?_, h0', fun q ↦ ?_, ?_, fun t ht ↦ ?_⟩
      · simp only
        rw [snum_extend h0' hL, ← pv_pack, pv_mulL c.sh i a b htop, pv_pack,
          ← snum_extend h0 hS, ← hN, Lay.shl_eq, packY]
        simp only [Int.cast_id]
        rw [show stride c.sh i = st from rfl]
        ring
      · by_cases hq : q < slots c.sh
        · have h₁ := natAbs_mulL_le c.sh i a b (fun q _ ↦ hM q) hq
          have h₂ : g * l1 c.sh d ≤ x.m * g := by
            rw [Nat.mul_comm x.m]; exact Nat.mul_le_mul_left _ hl
          exact lt_of_le_of_lt (h₁.trans h₂) hmg
        · rw [h0' q (by omega)]
          simp
      · refine (l1_mulL_le c.sh i a b d).trans ?_
        rw [Nat.mul_comm x.m]
        exact Nat.mul_le_mul_left _ hl
      · exact herr _ (fun t _ ↦ by rw [pv_mulL c.sh i a b htop]; unfold X; ring) t ht
  · -- a product with `Cᵢ` only
    rw [beq_iff_eq] at hb
    simp only [hb, beq_self_eq_true, Bool.cond_true] at h
    cases hc : decide (x.m * g < 2 ^ (c.B - 1))
    · simp [hc] at h
    · simp only [hc, Bool.cond_true, Option.some.injEq] at h
      subst h
      have hmg : x.m * g < 2 ^ (c.B - 1) := of_decide_eq_true hc
      refine inv_norm ⟨hS, fun q ↦ a * d q, ?_, fun q hq ↦ by simp [h0 q hq], fun q ↦ ?_, ?_,
        fun t ht ↦ ?_⟩
      · simp only
        rw [hN, mul_comm, snum_mul]
      · rw [Int.natAbs_mul]
        have h₁ : a.natAbs * (d q).natAbs ≤ g * l1 c.sh d :=
          Nat.mul_le_mul (Nat.le_add_right _ _) (hM q)
        have h₂ : g * l1 c.sh d ≤ x.m * g := by
          rw [Nat.mul_comm x.m]; exact Nat.mul_le_mul_left _ hl
        omega
      · rw [l1_smul, Nat.mul_comm x.m]
        exact Nat.mul_le_mul (Nat.le_add_right _ _) hl
      · exact herr _ (fun t _ ↦ by rw [pv_smul]; unfold X; rw [← hb', hb]; push_cast; ring) t ht

/-- **A constant at the precision `p`.** -/
theorem inv_const {k : ℤ} (h : (const c k).m < 2 ^ (c.B - 1)) :
    Inv c (fun _ ↦ (k : ℝ)) (const c k) := by
  set σ := Nat.log2 k.natAbs + 1 - c.p with hσ
  have hN : (const c k).N = k / 2 ^ σ := by
    simp only [const, ← hσ, Int.shiftRight_eq_div_pow, Nat.cast_pow, Nat.cast_ofNat]
  have hm : (const c k).m = (k / 2 ^ σ).natAbs := by
    simp only [const, ← hσ, Int.shiftRight_eq_div_pow, Nat.cast_pow, Nat.cast_ofNat]
  have hS : (const c k).S = 1 := rfl
  have hσ' : (const c k).σ = σ := rfl
  refine ⟨by rw [hS]; exact slots_pos c.sh, fun q ↦ if q = 0 then k / 2 ^ σ else 0, ?_,
    fun q hq ↦ ?_, fun q ↦ ?_, ?_, fun t _ ↦ ?_⟩
  · rw [hN, hS, snum_single _ _ one_pos]
  · rw [hS] at hq
    simp [show q ≠ 0 by omega]
  · change (if q = 0 then k / 2 ^ σ else 0).natAbs < _
    split_ifs
    · rw [← hm]; exact h
    · simp
  · rw [l1_single, hm]
  · rw [pv_single, hσ']
    have hP : (0 : ℤ) < 2 ^ σ := by positivity
    have e := congrArg (fun z : ℤ ↦ (z : ℝ)) (Int.mul_ediv_add_emod k (2 ^ σ))
    push_cast at e
    have h₁ := Int.emod_nonneg k hP.ne'
    have h₂ := Int.emod_lt_of_pos k hP
    have h₃ : ((k % 2 ^ σ : ℤ) : ℝ) < 2 ^ σ := by exact_mod_cast h₂
    have h₄ : (0 : ℝ) ≤ ((k % 2 ^ σ : ℤ) : ℝ) := by exact_mod_cast h₁
    have h₅ : (k : ℝ) - 2 ^ σ * ((k / 2 ^ σ : ℤ) : ℝ) = ((k % 2 ^ σ : ℤ) : ℝ) := by linarith
    rw [h₅, abs_of_nonneg h₄]
    simp only [const, ← hσ]
    cases hz : σ == 0
    · simp only [Bool.cond_false, Nat.cast_one, one_mul]
      exact h₃.le
    · rw [beq_iff_eq] at hz
      have : k % 2 ^ σ = 0 := by rw [hz, pow_zero, Int.emod_one]
      simp [this]

/-- **Adding a constant keeps the invariant.** -/
theorem inv_addC {V : (ℕ → ℝ) → ℝ} {x z : FP} (hx : Inv c V x) {k : ℤ}
    (h : addC c k x = some z) : Inv c (fun t ↦ (k : ℝ) + V t) z := by
  unfold addC at h
  cases hk : k == 0
  · simp only [hk, Bool.cond_false] at h
    cases hm : decide ((const c k).m < 2 ^ (c.B - 1))
    · simp [hm] at h
    · simp only [hm, Bool.cond_true] at h
      exact inv_add (inv_const (of_decide_eq_true hm)) hx h
  · simp only [hk, Bool.cond_true, Option.some.injEq] at h
    subst h
    rw [beq_iff_eq] at hk
    subst hk
    exact hx.congr fun t _ ↦ by simp


/-! ### Horner's rule -/

/-- One term split as `fE` splits it (`SPoly.tval_split` over the reals). -/
theorem tval_splitR (Z : ℕ → ℝ) (i : ℕ) (t : ℤ × List ℕ) :
    (t.1 : ℝ) * SPoly.mono 1 Z i t.2 = (((SPoly.cTerm t).getD 0 : ℤ) : ℝ) +
      ((SPoly.zTerm t).map fun t ↦ (t.1 : ℝ) * SPoly.mono 1 Z (i + 1) t.2).getD 0 +
      Z i * ((SPoly.sTerm t).map fun t ↦ (t.1 : ℝ) * SPoly.mono 1 Z i t.2).getD 0 := by
  obtain ⟨a, e⟩ := t
  rcases e with _ | ⟨_ | d, f⟩
  · simp [SPoly.cTerm, SPoly.zTerm, SPoly.sTerm, SPoly.mono_nilR]
  · simp [SPoly.cTerm, SPoly.zTerm, SPoly.sTerm, SPoly.mono_consR]
  · simp only [SPoly.cTerm, SPoly.zTerm, SPoly.sTerm, List.isEmpty_cons, Bool.cond_false,
      Option.getD_none, Option.map_none, Option.map_some, Option.getD_some, Int.cast_zero, zero_add,
      SPoly.mono_consR, pow_succ]
    ring

/-- The terms split as `fE` splits them (`SPoly.sum_split` over the reals). -/
theorem sum_splitR (Z : ℕ → ℝ) (i : ℕ) : ∀ ts : SPoly ℤ,
    (ts.map fun t ↦ (t.1 : ℝ) * SPoly.mono 1 Z i t.2).sum =
      (((ts.filterMap SPoly.cTerm).sum : ℤ) : ℝ) +
        ((ts.filterMap SPoly.zTerm).map fun t ↦ (t.1 : ℝ) * SPoly.mono 1 Z (i + 1) t.2).sum +
        Z i * ((ts.filterMap SPoly.sTerm).map fun t ↦ (t.1 : ℝ) * SPoly.mono 1 Z i t.2).sum
  | [] => by simp
  | t :: ts => by
    rw [List.map_cons, List.sum_cons, sum_splitR Z i ts, tval_splitR Z i t]
    rcases hc : SPoly.cTerm t with _ | c <;> rcases hz : SPoly.zTerm t with _ | z <;>
      rcases hs : SPoly.sTerm t with _ | s <;>
      simp only [List.filterMap_cons, hc, hz, hs, Option.map_none, Option.map_some,
        Option.getD_none, Option.getD_some, List.map_cons, List.sum_cons, Int.cast_add,
        Int.cast_zero] <;> ring

/-- **Horner's rule at bounded precision** (`fE`): with enough fuel, its packed polynomial stands
for the terms' value at the box inputs. -/
theorem fE_inv : ∀ (fuel i : ℕ) (ts : SPoly ℤ), (∀ t ∈ ts, t.2.length + t.2.sum < fuel) →
    ∀ {x : FP}, fE c fuel i ts = some x →
      Inv c (fun y ↦ (ts.map fun t ↦ (t.1 : ℝ) * SPoly.mono 1 (X c y) i t.2).sum) x
  | 0, _, [], _, x, h => by
    simp only [fE, List.isEmpty_nil, Bool.cond_true, Option.some.injEq] at h
    subst h
    exact (inv_zero c).congr fun y _ ↦ by simp
  | 0, _, t :: _, h, _, _ => absurd (h t List.mem_cons_self) (Nat.not_lt_zero _)
  | fuel + 1, i, ts, h, x, hx => by
    have hz : ∀ t ∈ ts.filterMap SPoly.zTerm, t.2.length + t.2.sum < fuel := by
      intro t ht
      obtain ⟨s, hs, hst⟩ := List.mem_filterMap.mp ht
      have := h s hs
      obtain ⟨a, e⟩ := s
      rcases e with _ | ⟨_ | d, f⟩
      · exact absurd hst (by simp [SPoly.zTerm])
      · simp only [SPoly.zTerm, Option.some.injEq] at hst
        subst hst
        simp only [List.length_cons, List.sum_cons] at this ⊢
        omega
      · exact absurd hst (by simp [SPoly.zTerm])
    have hs : ∀ t ∈ ts.filterMap SPoly.sTerm, t.2.length + t.2.sum < fuel := by
      intro t ht
      obtain ⟨s, hs, hst⟩ := List.mem_filterMap.mp ht
      have := h s hs
      obtain ⟨a, e⟩ := s
      rcases e with _ | ⟨_ | d, f⟩
      · exact absurd hst (by simp [SPoly.sTerm])
      · exact absurd hst (by simp [SPoly.sTerm])
      · simp only [SPoly.sTerm, Option.some.injEq] at hst
        subst hst
        simp only [List.length_cons, List.sum_cons] at this ⊢
        omega
    simp only [fE] at hx
    obtain ⟨v, hv, hx⟩ := Option.bind_eq_some_iff.mp hx
    obtain ⟨w, hw, hx⟩ := Option.bind_eq_some_iff.mp hx
    obtain ⟨vw, hvw, hx⟩ := Option.bind_eq_some_iff.mp hx
    have iv : Inv c (fun y ↦ ((ts.filterMap SPoly.zTerm).map fun t ↦
        (t.1 : ℝ) * SPoly.mono 1 (X c y) (i + 1) t.2).sum) v := by
      cases he : (ts.filterMap SPoly.zTerm).isEmpty
      · rw [he, Bool.cond_false] at hv
        exact fE_inv fuel (i + 1) _ hz hv
      · rw [he, Bool.cond_true, Option.some.injEq] at hv
        subst hv
        rw [List.isEmpty_iff.mp he]
        exact (inv_zero c).congr fun y _ ↦ by simp
    have iw : Inv c (fun y ↦ X c y i * ((ts.filterMap SPoly.sTerm).map fun t ↦
        (t.1 : ℝ) * SPoly.mono 1 (X c y) i t.2).sum) w := by
      cases he : (ts.filterMap SPoly.sTerm).isEmpty
      · rw [he, Bool.cond_false] at hw
        obtain ⟨u, hu, hw⟩ := Option.bind_eq_some_iff.mp hw
        exact inv_mulZ (fE_inv fuel i _ hs hu) hw
      · rw [he, Bool.cond_true, Option.some.injEq] at hw
        subst hw
        rw [List.isEmpty_iff.mp he]
        exact (inv_zero c).congr fun y _ ↦ by simp
    exact (inv_addC (inv_add iv iw hvw) hx).congr fun y _ ↦ by rw [sum_splitR (X c y) i ts]; ring

/-- **The value of a sparse polynomial at the box inputs, at bounded precision.** -/
theorem fE_spec {q : SPoly ℤ} {x : FP} (h : fE c (SPoly.fuelOf q) 0 q = some x) :
    Inv c (fun y ↦ SPoly.run (fun a : ℤ ↦ (a : ℝ)) (X c y) q) x :=
  (fE_inv _ 0 q (fun _ ht ↦ SPoly.le_fuelOf ht) h).congr fun y _ ↦ by
    rw [SPoly.run_int_eq_sum]

/-! ### Truncations -/

/-- **A truncation from a packed polynomial at bounded precision** (`trunc`): the signed numeral
of digit size `B'` of digits `td` with absolute sum `tl`, such that `m` times the value stands
within `ρ 2^s` of `2^s` times their polynomial on the cube. -/
theorem trunc_spec {V : (ℕ → ℝ) → ℝ} {x : FP} (hx : Inv c V x) (hB : 0 < c.B) (B' s : ℕ)
    (m : ℤ) :
    ∃ td : ℕ → ℤ, (trunc c B' s m x).1.1 = snum B' td (slots c.sh) ∧
      l1 c.sh td = (trunc c B' s m x).1.2 ∧
      ∀ y : ℕ → ℝ, (∀ i, |y i| ≤ 1) →
        |(m : ℝ) * V y - 2 ^ s * pv c.sh td y| ≤ ((trunc c B' s m x).2 : ℝ) * 2 ^ s := by
  obtain ⟨hS, d, hN, h0, hr, hl, he⟩ := hx
  have hrange : ∀ q < slots c.sh, -2 ^ (c.B - 1) ≤ d q ∧ d q < 2 ^ (c.B - 1) := fun q _ ↦ by
    have h' : |d q| < 2 ^ (c.B - 1) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hr q
    exact ⟨by linarith [(abs_lt.mp h').1], (abs_lt.mp h').2⟩
  obtain ⟨hbias, hdig⟩ := snum_add_bias hB hrange
  have hU : (x.N + (offN c.B c.sh : ℤ)).toNat =
      num c.B (fun q ↦ (d q + 2 ^ (c.B - 1)).toNat) (slots c.sh) := by
    rw [hN, snum_extend h0 hS, offN_eq, hbias, Int.toNat_natCast]
  have hdq : ∀ q < slots c.sh,
      ((dig c.B (num c.B (fun q ↦ (d q + 2 ^ (c.B - 1)).toNat) (slots c.sh)) q : ℕ) : ℤ) -
        ((2 ^ (c.B - 1) : ℕ) : ℤ) = d q := by
    intro q hq
    rw [dig_num hB hdig hq, Int.toNat_of_nonneg (by linarith [(hrange q hq).1])]
    push_cast
    ring
  have htr := Lay.truncL_eq c.B B' (s - x.σ) (2 ^ (c.B - 1)) (m * 2 ^ (x.σ - s)) (slots c.sh) _
    (num_lt hdig)
  refine ⟨fun q ↦ d q * (m * 2 ^ (x.σ - s)) / 2 ^ (s - x.σ), ?_, ?_, fun y hy ↦ ?_⟩
  · simp only [trunc]
    rw [hU, htr]
    exact snum_congr fun q hq ↦ by rw [hdq q hq]
  · simp only [trunc]
    rw [hU, htr]
    unfold l1
    exact sum_congr rfl fun q hq ↦ by rw [hdq q (mem_range.mp hq)]
  · simp only [trunc]
    set e := x.σ - s
    set k := s - x.σ
    set m' := m * 2 ^ e
    set td : ℕ → ℤ := fun q ↦ d q * m' / 2 ^ k
    have hσk : (2 : ℝ) ^ x.σ * 2 ^ k = 2 ^ s * 2 ^ e := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    have h₁ := he y hy
    have h₂ := Lay.abs_pv_trunc_le c.sh d m' k hy
    have hc : ((m.natAbs * x.r * 2 ^ e : ℕ) : ℝ) ≤ cdiv (m.natAbs * x.r * 2 ^ e) k * 2 ^ k := by
      exact_mod_cast le_cdiv_mul _ _
    have hm' : (m' : ℝ) = m * 2 ^ e := by simp [m']
    have key : (2 : ℝ) ^ k * ((m : ℝ) * V y - 2 ^ s * pv c.sh td y) =
        2 ^ k * (m : ℝ) * (V y - 2 ^ x.σ * pv c.sh d y) +
          2 ^ s * ((m' : ℝ) * pv c.sh d y - 2 ^ k * pv c.sh td y) := by
      rw [hm']
      linear_combination ((m : ℝ) * pv c.sh d y) * hσk
    have hk : (0 : ℝ) < 2 ^ k := by positivity
    have hs : (0 : ℝ) < 2 ^ s := by positivity
    have hmabs : |(m : ℝ)| = (m.natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    have hbound : (2 : ℝ) ^ k * |(m : ℝ) * V y - 2 ^ s * pv c.sh td y| ≤
        2 ^ k * (((slots c.sh + cdiv (m.natAbs * x.r * 2 ^ e) k : ℕ) : ℝ) * 2 ^ s) := by
      rw [← abs_of_pos hk, ← abs_mul, key, abs_of_pos hk]
      calc |2 ^ k * (m : ℝ) * (V y - 2 ^ x.σ * pv c.sh d y) +
            2 ^ s * ((m' : ℝ) * pv c.sh d y - 2 ^ k * pv c.sh td y)|
          ≤ 2 ^ k * |(m : ℝ)| * |V y - 2 ^ x.σ * pv c.sh d y| +
            2 ^ s * |(m' : ℝ) * pv c.sh d y - 2 ^ k * pv c.sh td y| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_mul, abs_of_pos hk, abs_of_pos hs]
        _ ≤ 2 ^ k * (m.natAbs : ℝ) * (x.r * 2 ^ x.σ) + 2 ^ s * ((slots c.sh : ℝ) * 2 ^ k) := by
            rw [hmabs]
            gcongr
        _ = (((m.natAbs * x.r * 2 ^ e : ℕ) : ℝ)) * 2 ^ s + 2 ^ s * ((slots c.sh : ℝ) * 2 ^ k) := by
            push_cast
            linear_combination ((m.natAbs : ℝ) * x.r) * hσk
        _ ≤ (cdiv (m.natAbs * x.r * 2 ^ e) k * 2 ^ k) * 2 ^ s +
            2 ^ s * ((slots c.sh : ℝ) * 2 ^ k) := by gcongr
        _ = 2 ^ k * (((slots c.sh + cdiv (m.natAbs * x.r * 2 ^ e) k : ℕ) : ℝ) * 2 ^ s) := by
            push_cast; ring
    exact le_of_mul_le_mul_left hbound hk

end FPoly

end Nieuwland.Check
