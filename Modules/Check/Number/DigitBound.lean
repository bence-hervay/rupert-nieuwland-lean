import Modules.Check.Polynomial.Layout
import Modules.Check.Number.Ext

/-!
# The centred form of packed numerals

A polynomial in the slots of a shape `sh` (`Modules/Check/Polynomial/Layout.lean`) is packed in a numeral `N`
of `B`-bit digits, coefficient `c_q` in digit `q` with the bias `h = 2^(B-1)`. On `[-1, 1]^n` a
monomial with an odd exponent lies in `[-1, 1]` and one with only even exponents in `[0, 1]`, so

  `c₀ - ∑_{q odd} |c_q| - ∑_{q even, q ≠ 0} max(-c_q, 0)`

is a lower bound (`sum_ge_pen`). The kernel reads it off `N` with a few operations on whole
numerals (`lowerN`, sound by `lowerN_le`):

* the sign bits of all digits by one shift and one mask (`signN`), the positive and negative parts
  of all coefficients by masks (`posN`, `negN`) and their sum (`absN`);
* digit sums by one remainder modulo `2^B - 1` (`maskSum`, by `num_mod_mersenne_of_lt`), after
  masking the slots with an odd exponent (`oddM`) or with even ones (`even0M`); the masks are
  product indicators (`Lay.ind`).

The absolute coefficient sum is `absN % (2^B - 1)` (`l1N`), exact while it is below `2^(B-1)`.

Over a field with basis values `β₀, β₁, …` (`ExactBasis`) the polynomial is `∑ⱼ βⱼ pⱼ` with integer
polynomials `pⱼ` in numerals `Nⱼ`. With integer approximations `aⱼ` of `2^k βⱼ`, error at most
`εⱼ` (`ExactBasis.apx`), the penalties are read off the single numeral of `∑ⱼ aⱼ pⱼ`, plus
`∑ⱼ εⱼ ‖pⱼ‖₁` for the errors; the constant coefficient is exact. The kernel then decides one sign
in `κ` (`apxOk`, sound by `apxOk_sound`).
-/

open Finset

namespace Nieuwland.Check

/-- `0 < v` if `strict`, else `0 ≤ v`. -/
def Sign (strict : Bool) (v : ℝ) : Prop := if strict then 0 < v else 0 ≤ v

theorem sign_of_le {strict : Bool} {u v : ℝ} (h : Sign strict u) (huv : u ≤ v) : Sign strict v := by
  cases strict
  · exact (show 0 ≤ u from h).trans huv
  · exact (show 0 < u from h).trans_le huv

theorem sign_of_mul {strict : Bool} {t v : ℝ} (ht : 0 < t) (h : Sign strict (t * v)) :
    Sign strict v := by
  cases strict
  · exact nonneg_of_mul_nonneg_right (show 0 ≤ t * v from h) ht
  · exact pos_of_mul_pos_right (show 0 < t * v from h) ht.le

/-- A sound test of `Sign strict (re a)`. -/
def signTest {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] (strict : Bool) (a : κ) : Bool :=
  bif strict then Exact.pos a else Exact.nonneg a

theorem sign_of_signTest {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] {strict : Bool} {a : κ}
    (h : signTest strict a = true) : Sign strict (Exact.re a) := by
  cases strict
  · exact Exact.nonneg_sound a h
  · exact Exact.pos_sound a h

namespace Lay

open DPoly Num

/-! ### Digits -/

theorem num_sub {B L : ℕ} {a b : ℕ → ℕ} (h : ∀ p < L, b p ≤ a p) :
    num B a L - num B b L = num B (fun p ↦ a p - b p) L := by
  have h₁ := num_add B (fun p ↦ a p - b p) b L
  rw [num_congr (B := B) (a := fun p ↦ a p - b p + b p) (b := a)
    fun p hp ↦ Nat.sub_add_cancel (h p hp)] at h₁
  omega

/-- The top bit of a digit is its comparison with the bias. -/
theorem testBit_top {B d : ℕ} (hB : 0 < B) (hd : d < 2 ^ B) :
    d.testBit (B - 1) = decide (2 ^ (B - 1) ≤ d) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h2 : 2 ^ B = 2 ^ (B - 1) * 2 := by rw [← pow_succ]; congr 1; omega
  have hq : d / 2 ^ (B - 1) < 2 := Nat.div_lt_of_lt_mul (h2 ▸ hd)
  by_cases h : 2 ^ (B - 1) ≤ d
  · have : 1 ≤ d / 2 ^ (B - 1) := (Nat.one_le_div_iff (Nat.two_pow_pos _)).mpr h
    have : d / 2 ^ (B - 1) = 1 := by omega
    simp [this, h]
  · have : d / 2 ^ (B - 1) = 0 := Nat.div_eq_of_lt (by omega)
    simp [this, h]

theorem cf_zero (B N : ℕ) : cf B N 0 = ((N % 2 ^ B : ℕ) : ℤ) - 2 ^ (B - 1) := by
  simp [cf, dig]

theorem cf_eq (B N q : ℕ) : cf B N q = (dig B N q : ℤ) - ((2 ^ (B - 1) : ℕ) : ℤ) := by
  simp [cf]

/-! ### Masks -/

/-- The digit `1` in every slot. -/
def onesN (B : ℕ) (sh : List ℕ) : ℕ := ind B sh fun _ _ ↦ true

/-- The digit `1` in the slots whose exponents are all even. -/
def evenN (B : ℕ) (sh : List ℕ) : ℕ := ind B sh fun _ x ↦ x % 2 == 0

/-- `1` if slot `q` has only even exponents, else `0`. -/
def ev (sh : List ℕ) (q : ℕ) : ℕ := if AllT sh (fun _ x ↦ x % 2 == 0) q then 1 else 0

/-- The digit `1` in the slots with an odd exponent. -/
def oddM (B : ℕ) (sh : List ℕ) : ℕ := onesN B sh - evenN B sh

/-- The digit `1` in the slots other than `0` with only even exponents. -/
def even0M (B : ℕ) (sh : List ℕ) : ℕ := evenN B sh - 1

theorem ev_le_one (sh : List ℕ) (q : ℕ) : ev sh q ≤ 1 := by unfold ev; split_ifs <;> omega

theorem ev_zero (sh : List ℕ) : ev sh 0 = 1 := by
  simp [ev, AllT, ex]

theorem one_lt_two_pow {B : ℕ} (hB : 0 < B) : 1 < 2 ^ B := Nat.one_lt_two_pow (by omega)

theorem onesN_eq (B : ℕ) (sh : List ℕ) : onesN B sh = num B (fun _ ↦ 1) (slots sh) := by
  rw [onesN, ind_eq]
  exact num_congr fun q _ ↦ by simp [allT_true]

theorem evenN_eq (B : ℕ) (sh : List ℕ) : evenN B sh = num B (ev sh) (slots sh) := ind_eq B sh _

theorem oddM_eq (B : ℕ) (sh : List ℕ) : oddM B sh = num B (fun q ↦ 1 - ev sh q) (slots sh) := by
  rw [oddM, onesN_eq, evenN_eq, num_sub fun q _ ↦ ev_le_one sh q]

theorem num_sub_one {B L : ℕ} {a : ℕ → ℕ} (hL : 0 < L) (h0 : 1 ≤ a 0) :
    num B a L - 1 = num B (fun q ↦ if q = 0 then a 0 - 1 else a q) L := by
  obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  simp only [num, sum_range_succ']
  simp only [mul_zero, pow_zero, mul_one, ite_true, Nat.succ_ne_zero, ite_false]
  omega

theorem even0M_eq (B : ℕ) (sh : List ℕ) :
    even0M B sh = num B (fun q ↦ if q = 0 then 0 else ev sh q) (slots sh) := by
  rw [even0M, evenN_eq, num_sub_one (slots_pos sh) (by rw [ev_zero])]
  refine num_congr fun q _ ↦ ?_
  split_ifs with h
  · simp [ev_zero]
  · rfl

/-! ### Signs and parts of the coefficients -/

/-- `1` if digit `q` of `N` is at least the bias, i.e. the coefficient is nonnegative. -/
def sgn (B N q : ℕ) : ℕ := if 2 ^ (B - 1) ≤ dig B N q then 1 else 0

/-- The sign bits of all digits, by one shift and one mask (`signN_eq`). -/
def signN (B : ℕ) (sh : List ℕ) (N : ℕ) : ℕ := (N >>> (B - 1)) &&& onesN B sh

/-- The positive parts `max(c_q, 0)` (`posN_eq`). -/
def posN (B : ℕ) (sh : List ℕ) (N : ℕ) : ℕ :=
  (N &&& (2 ^ B - 1) * signN B sh N) - 2 ^ (B - 1) * signN B sh N

/-- The negative parts `max(-c_q, 0)` (`negN_eq`). -/
def negN (B : ℕ) (sh : List ℕ) (N : ℕ) : ℕ :=
  2 ^ (B - 1) * (onesN B sh - signN B sh N) - (N &&& (2 ^ B - 1) * (onesN B sh - signN B sh N))

/-- The absolute values `|c_q|` (`absN_eq`). -/
def absN (B : ℕ) (sh : List ℕ) (N : ℕ) : ℕ := posN B sh N + negN B sh N

/-- `posN` by shifts. -/
def posNS (B : ℕ) (sh : List ℕ) (N : ℕ) : ℕ :=
  let s := signN B sh N
  (N &&& ((s <<< B) - s)) - (s <<< (B - 1))

@[csimp] theorem posN_eq_posNS : @posN = @posNS := by
  funext B sh N
  simp only [posN, posNS, two_pow_sub_one_mul_eq, two_pow_mul_eq_shiftLeft]

/-- `negN` by shifts. -/
def negNS (B : ℕ) (sh : List ℕ) (N : ℕ) : ℕ :=
  let t := onesN B sh - signN B sh N
  (t <<< (B - 1)) - (N &&& ((t <<< B) - t))

@[csimp] theorem negN_eq_negNS : @negN = @negNS := by
  funext B sh N
  simp only [negN, negNS, two_pow_sub_one_mul_eq, two_pow_mul_eq_shiftLeft]

/-- `absN` by shifts, with the sign bits and the ones computed once. -/
def absNS (B : ℕ) (sh : List ℕ) (N : ℕ) : ℕ :=
  let o := onesN B sh
  let s := (N >>> (B - 1)) &&& o
  let t := o - s
  ((N &&& ((s <<< B) - s)) - (s <<< (B - 1))) + ((t <<< (B - 1)) - (N &&& ((t <<< B) - t)))

@[csimp] theorem absN_eq_absNS : @absN = @absNS := by
  funext B sh N
  simp only [absN, absNS, posN, negN, signN, two_pow_sub_one_mul_eq, two_pow_mul_eq_shiftLeft]

theorem sgn_le_one (B N q : ℕ) : sgn B N q ≤ 1 := by unfold sgn; split_ifs <;> omega

theorem num_and_mask {B : ℕ} (hB : 0 < B) {x m : ℕ → ℕ} {L : ℕ} (hx : Digits B x L)
    (hm : ∀ p < L, m p ≤ 1) :
    num B x L &&& (2 ^ B - 1) * num B m L = num B (fun p ↦ m p * x p) L := by
  rw [num_mul, num_land hB hx fun p hp ↦ ?_]
  · refine num_congr fun p hp ↦ ?_
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hm p hp) with h | h <;> rw [h]
    · simp
    · rw [mul_one, one_mul]
      exact Nat.and_two_pow_sub_one_of_lt_two_pow (hx p hp)
  · have := hm p hp
    calc (2 ^ B - 1) * m p ≤ (2 ^ B - 1) * 1 := Nat.mul_le_mul_left _ this
      _ < 2 ^ B := by have := Nat.two_pow_pos B; omega
section Parts

variable {B : ℕ} (hB : 0 < B) (sh : List ℕ) {N : ℕ} (hN : N < 2 ^ (B * slots sh))
include hB hN

theorem signN_eq : signN B sh N = num B (sgn B N) (slots sh) := by
  have h1 := one_lt_two_pow hB
  have hs : Digits B (sgn B N) (slots sh) := fun q _ ↦ (sgn_le_one B N q).trans_lt h1
  refine num_eq_of_testBit hB hs fun j ↦ ?_
  rw [signN, Nat.testBit_and, Nat.testBit_shiftRight, onesN_eq, testBit_num hB (fun _ _ ↦ h1) j]
  conv_lhs => rw [← num_dig hB hN]
  rw [testBit_num hB (digits_dig B N _)]
  obtain ⟨p, r, hr, rfl⟩ : ∃ p r, r < B ∧ j = B * p + r :=
    ⟨j / B, j % B, Nat.mod_lt _ hB, (Nat.div_add_mod j B).symm⟩
  have hjB : (B * p + r) / B = p := by rw [Nat.mul_add_div hB, Nat.div_eq_of_lt hr, add_zero]
  have hjr : (B * p + r) % B = r := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  rw [hjB, hjr]
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · have h₁ : (B - 1 + (B * p + 0)) / B = p := by
      rw [add_zero, add_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt (by omega), add_zero]
    have h₂ : (B - 1 + (B * p + 0)) % B = B - 1 := by
      rw [add_zero, add_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    rw [h₁, h₂, testBit_top hB (dig_lt B N p)]
    unfold sgn
    by_cases hp : p < slots sh <;> split_ifs with hd <;> simp [hp, hd]
  · have h₁ : (1 : ℕ).testBit r = false := Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))
    have h₂ : (sgn B N p).testBit r = false :=
      Nat.testBit_lt_two_pow ((sgn_le_one B N p).trans_lt (Nat.one_lt_two_pow (by omega)))
    simp [h₁, h₂]


theorem posN_eq : posN B sh N = num B (fun q ↦ dig B N q - 2 ^ (B - 1)) (slots sh) := by
  rw [posN, signN_eq hB sh hN]
  conv_lhs => arg 1; arg 1; rw [← num_dig hB hN]
  rw [num_and_mask hB (digits_dig B N _) fun q _ ↦ sgn_le_one B N q, num_mul,
    num_sub fun q _ ↦ ?_]
  · refine num_congr fun q _ ↦ ?_
    unfold sgn
    split_ifs
    · simp
    · simp; omega
  · unfold sgn
    split_ifs
    · simp; omega
    · simp

theorem negN_eq : negN B sh N = num B (fun q ↦ 2 ^ (B - 1) - dig B N q) (slots sh) := by
  have hS : onesN B sh - signN B sh N = num B (fun q ↦ 1 - sgn B N q) (slots sh) := by
    rw [onesN_eq, signN_eq hB sh hN, num_sub fun q _ ↦ sgn_le_one B N q]
  rw [negN, hS]
  conv_lhs => arg 2; arg 1; rw [← num_dig hB hN]
  rw [num_and_mask hB (digits_dig B N _) fun q _ ↦ Nat.sub_le 1 _, num_mul,
    num_sub fun q _ ↦ ?_]
  · refine num_congr fun q _ ↦ ?_
    unfold sgn
    split_ifs
    · simp; omega
    · simp
  · unfold sgn
    split_ifs
    · simp
    · simp; omega

theorem absN_eq : absN B sh N = num B (fun q ↦ (cf B N q).natAbs) (slots sh) := by
  rw [absN, posN_eq hB sh hN, negN_eq hB sh hN, num_add]
  refine num_congr fun q _ ↦ ?_
  rw [cf_eq]
  generalize 2 ^ (B - 1) = h
  omega

end Parts

/-! ### Digit sums -/

/-- The sum of the digits of `X` in the slots where the digit of `M` (`0` or `1`) is `1`: one mask
and one remainder (`maskSum_eq`). -/
def maskSum (B X M : ℕ) : ℕ := (X &&& (2 ^ B - 1) * M) % (2 ^ B - 1)

/-- `maskSum` with the mask by a shift. -/
def maskSumS (B X M : ℕ) : ℕ := (X &&& ((M <<< B) - M)) % (2 ^ B - 1)

@[csimp] theorem maskSum_eq_maskSumS : @maskSum = @maskSumS := by
  funext B X M
  rw [maskSum, maskSumS, two_pow_sub_one_mul_eq]

theorem maskSum_eq {B L : ℕ} (hB : 0 < B) {x m : ℕ → ℕ} (hx : Digits B x L)
    (hm : ∀ p < L, m p ≤ 1) (hs : ∑ p ∈ range L, x p < 2 ^ B - 1) :
    maskSum B (num B x L) (num B m L) = ∑ p ∈ range L, m p * x p := by
  rw [maskSum, num_and_mask hB hx hm, num_mod_mersenne_of_lt]
  refine (sum_le_sum fun p hp ↦ ?_).trans_lt hs
  have := hm p (mem_range.mp hp)
  calc m p * x p ≤ 1 * x p := Nat.mul_le_mul_right _ this
    _ = x p := one_mul _

/-- The absolute coefficient sum, exact below `2^B - 1` (`l1N_eq`). -/
def l1N (B : ℕ) (sh : List ℕ) (N : ℕ) : ℕ := absN B sh N % (2 ^ B - 1)

/-- `∑_{q odd} |c_q|`. -/
def oddAbs (B : ℕ) (sh : List ℕ) (N : ℕ) : ℕ := maskSum B (absN B sh N) (oddM B sh)

/-- `∑_{q ≠ 0 even} max(-c_q, 0)`. -/
def evenNeg (B : ℕ) (sh : List ℕ) (N : ℕ) : ℕ := maskSum B (negN B sh N) (even0M B sh)

/-- **The centred-form bound of a numeral** on `[-1, 1]^n` (`lowerN_le`). -/
def lowerN (B : ℕ) (sh : List ℕ) (N : ℕ) : ℤ :=
  ((N % 2 ^ B : ℕ) : ℤ) - 2 ^ (B - 1) - oddAbs B sh N - evenNeg B sh N

theorem negD_le (B N q : ℕ) : 2 ^ (B - 1) - dig B N q ≤ (cf B N q).natAbs := by
  rw [cf_eq]
  generalize 2 ^ (B - 1) = h
  omega

section Sums

variable {B : ℕ} (hB : 0 < B) {sh : List ℕ} {N : ℕ} (hN : N < 2 ^ (B * slots sh))
  (hl : l1 sh (cf B N) < 2 ^ B - 1)
include hB hN hl

theorem l1N_eq : l1N B sh N = l1 sh (cf B N) := by
  rw [l1N, absN_eq hB sh hN, num_mod_mersenne_of_lt hl]
  rfl

theorem oddAbs_eq : oddAbs B sh N = ∑ q ∈ range (slots sh), (1 - ev sh q) * (cf B N q).natAbs := by
  rw [oddAbs, absN_eq hB sh hN, oddM_eq]
  refine maskSum_eq hB (fun q hq ↦ ?_) (fun q _ ↦ Nat.sub_le 1 _) hl
  have := (abs_coeff_le_l1 (cf B N) hq).trans_lt hl
  have : 2 ^ B - 1 < 2 ^ B := Nat.sub_lt (Nat.two_pow_pos B) one_pos
  omega

theorem evenNeg_eq : evenNeg B sh N = ∑ q ∈ range (slots sh),
    (if q = 0 then 0 else ev sh q) * (2 ^ (B - 1) - dig B N q) := by
  rw [evenNeg, negN_eq hB sh hN, even0M_eq]
  refine maskSum_eq hB (fun q _ ↦ ?_) (fun q _ ↦ ?_) ?_
  · exact (Nat.sub_le _ _).trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  · split_ifs
    · exact Nat.zero_le 1
    · exact ev_le_one sh q
  · exact (sum_le_sum fun q _ ↦ negD_le B N q).trans_lt hl

end Sums

/-! ### Bounds on the cube -/

section Cube

variable {R : Type*} [CommRing R]

theorem mono_zero (sh : List ℕ) (y : ℕ → R) : mono sh 0 y = 1 := by
  simp [mono, ex]

variable {sh : List ℕ} {y : ℕ → ℝ}

theorem abs_mono_le (hy : ∀ i, |y i| ≤ 1) (q : ℕ) : |mono sh q y| ≤ 1 := by
  rw [mono, abs_prod]
  exact prod_le_one₀ (fun i _ ↦ abs_nonneg _) fun i _ ↦ by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hy i)

theorem mono_nonneg {q : ℕ} (h : ev sh q = 1) : 0 ≤ mono sh q y := by
  unfold ev at h
  split_ifs at h with hq
  · refine prod_nonneg fun i hi ↦ Even.pow_nonneg ?_ _
    have := hq i (mem_range.mp hi)
    simp only [beq_iff_eq] at this
    exact Nat.even_iff.mpr this

/-- The penalty of slot `q` in the centred form. -/
noncomputable def pen (sh : List ℕ) (C : ℕ → ℝ) (q : ℕ) : ℝ :=
  if q = 0 then 0 else if ev sh q = 1 then max (-C q) 0 else |C q|

/-- **The centred form on the cube.** -/
theorem sum_ge_pen (C : ℕ → ℝ) (hy : ∀ i, |y i| ≤ 1) :
    C 0 - ∑ q ∈ range (slots sh), pen sh C q ≤ ∑ q ∈ range (slots sh), C q * mono sh q y := by
  have h0 : C 0 = ∑ q ∈ range (slots sh), if q = 0 then C q else 0 := by
    rw [sum_ite_eq' (range (slots sh)) 0 C]
    simp [slots_pos sh]
  rw [h0, ← sum_sub_distrib]
  refine sum_le_sum fun q _ ↦ ?_
  unfold pen
  by_cases hq : q = 0
  · subst hq; simp [mono_zero]
  · simp only [hq, ite_false, zero_sub]
    have hm := abs_le.mp (abs_mono_le (sh := sh) hy q)
    split_ifs with he
    · have h₀ := mono_nonneg (y := y) he
      rcases le_or_gt 0 (C q) with hc | hc
      · rw [max_eq_right (by linarith)]; simp only [neg_zero]; positivity
      · rw [max_eq_left (by linarith)]; nlinarith
    · have := neg_abs_le (C q * mono sh q y)
      rw [abs_mul] at this
      have := mul_le_of_le_one_right (abs_nonneg (C q)) (abs_mono_le (sh := sh) hy q)
      linarith

theorem pen_smul {C : ℕ → ℝ} {t : ℝ} (ht : 0 ≤ t) (q : ℕ) :
    pen sh (fun p ↦ t * C p) q = t * pen sh C q := by
  unfold pen
  dsimp only
  split_ifs
  · ring
  · rw [mul_max_of_nonneg _ _ ht, mul_zero, mul_neg]
  · rw [abs_mul, abs_of_nonneg ht]

theorem pen_le_add {C C' : ℕ → ℝ} (q : ℕ) :
    pen sh C q ≤ pen sh C' q + if q = 0 then 0 else |C q - C' q| := by
  unfold pen
  split_ifs
  · simp
  · refine max_le ?_ (add_nonneg (le_max_right _ _) (abs_nonneg _))
    have h₁ := neg_abs_le (C q - C' q)
    have h₂ := le_max_left (-C' q) 0
    linarith
  · have := abs_sub_abs_le_abs_sub (C q) (C' q)
    linarith

end Cube

theorem pv_eq_sum (sh : List ℕ) (c : ℕ → ℤ) (y : ℕ → ℝ) :
    pv sh c y = ∑ q ∈ range (slots sh), ((c q : ℤ) : ℝ) * mono sh q y := rfl

/-- The penalties of a numeral, as its digit sums. -/
theorem sum_pen_eq {B : ℕ} (hB : 0 < B) {sh : List ℕ} {N : ℕ} (hN : N < 2 ^ (B * slots sh))
    (hl : l1 sh (cf B N) < 2 ^ B - 1) :
    ∑ q ∈ range (slots sh), pen sh (fun p ↦ (cf B N p : ℝ)) q =
      (oddAbs B sh N : ℝ) + (evenNeg B sh N : ℝ) := by
  rw [oddAbs_eq hB hN hl, evenNeg_eq hB hN hl, Nat.cast_sum, Nat.cast_sum, ← sum_add_distrib]
  refine sum_congr rfl fun q _ ↦ ?_
  rw [Nat.cast_mul, Nat.cast_mul]
  unfold pen
  by_cases hq : q = 0
  · subst hq; simp [ev_zero]
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (ev_le_one sh q) with h | h
    · simp only [hq, h, ite_false, zero_ne_one, Nat.sub_zero, Nat.cast_one, one_mul,
        Nat.cast_zero, zero_mul, add_zero]
      rw [Nat.cast_natAbs, Int.cast_abs]
    · simp only [hq, h, ite_false, ite_true, Nat.sub_self, Nat.cast_zero, zero_mul,
        Nat.cast_one, one_mul, zero_add]
      unfold cf
      rcases le_or_gt (2 ^ (B - 1)) (dig B N q) with h' | h'
      · rw [Nat.sub_eq_zero_of_le h', Nat.cast_zero, max_eq_right]
        push_cast
        have : ((2 : ℝ) ^ (B - 1)) ≤ (dig B N q : ℝ) := by exact_mod_cast h'
        linarith
      · rw [max_eq_left, Nat.cast_sub h'.le]
        · push_cast; ring
        · push_cast
          have : (dig B N q : ℝ) < (2 : ℝ) ^ (B - 1) := by exact_mod_cast h'
          linarith

/-- **Soundness of `lowerN`.** -/
theorem lowerN_le {B : ℕ} (hB : 0 < B) {sh : List ℕ} {N : ℕ} (hN : N < 2 ^ (B * slots sh))
    (hl : l1 sh (cf B N) < 2 ^ B - 1) {y : ℕ → ℝ} (hy : ∀ i, |y i| ≤ 1) :
    (lowerN B sh N : ℝ) ≤ pv sh (cf B N) y := by
  have h := sum_ge_pen (sh := sh) (fun p ↦ (cf B N p : ℝ)) hy
  rw [sum_pen_eq hB hN hl] at h
  calc (lowerN B sh N : ℝ) = (cf B N 0 : ℝ) - ((oddAbs B sh N : ℝ) + (evenNeg B sh N : ℝ)) := by
        rw [lowerN, cf_zero]; push_cast; ring
    _ ≤ pv sh (cf B N) y := h

/-! ### Over a field -/

/-- `∑_{j < n} f j`, by recursion (for the kernel). -/
def sumZ (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => sumZ f n + f n

/-- `∑_{j < n} f j`, by recursion (for the kernel). -/
def sumN (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumN f n + f n

theorem sumZ_eq (f : ℕ → ℤ) (n : ℕ) : sumZ f n = ∑ j ∈ range n, f j := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumZ, ih, sum_range_succ]

theorem sumN_eq (f : ℕ → ℕ) (n : ℕ) : sumN f n = ∑ j ∈ range n, f j := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumN, ih, sum_range_succ]

/-- The invariant of the numerals of the engine: `slots sh` digits, and an absolute coefficient
sum below the bias. -/
def Inv (B : ℕ) (sh : List ℕ) (N : ℕ) : Prop :=
  N < 2 ^ (B * slots sh) ∧ l1 sh (cf B N) < 2 ^ (B - 1)

theorem two_pow_pred_le {B : ℕ} (hB : 0 < B) : 2 ^ (B - 1) ≤ 2 ^ B - 1 := by
  have : 2 ^ B = 2 * 2 ^ (B - 1) := by rw [← pow_succ']; congr 1; omega
  have := Nat.one_le_two_pow (n := B - 1)
  omega

theorem l1N_eq_of_inv {B : ℕ} (hB : 0 < B) {sh : List ℕ} {N : ℕ} (h : Inv B sh N) :
    l1N B sh N = l1 sh (cf B N) :=
  l1N_eq hB h.1 (h.2.trans_le (two_pow_pred_le hB))

/-- A numeral less the offset is the signed numeral of its coefficients. -/
theorem sub_offN {B : ℕ} (hB : 0 < B) {sh : List ℕ} {N : ℕ} (hN : N < 2 ^ (B * slots sh)) :
    (N : ℤ) - offN B sh = snum B (cf B N) (slots sh) := by
  conv_lhs => rw [← num_dig hB hN]
  rw [offN_eq, snum_natCast, snum_natCast, snum_sub]
  exact snum_congr fun q _ ↦ by rw [cf]; push_cast; ring

theorem sum_snum (B L : ℕ) (s : Finset ℕ) (f : ℕ → ℤ) (c : ℕ → ℕ → ℤ) :
    ∑ j ∈ s, f j * snum B (c j) L = snum B (fun p ↦ ∑ j ∈ s, f j * c j p) L := by
  simp only [snum, mul_sum, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun p _ ↦ sum_congr rfl fun j _ ↦ by ring

section Field

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

variable (κ) in
/-- The approximation `aⱼ` of `2^k βⱼ` (`ExactBasis.apx`). -/
def apxA (j : ℕ) : ℤ := ((ExactBasis.apx κ).getD j (0, 0)).1

variable (κ) in
/-- The error bound `εⱼ` of `aⱼ`. -/
def apxE (j : ℕ) : ℕ := ((ExactBasis.apx κ).getD j (0, 0)).2

variable (κ) in
/-- The numeral of `∑ⱼ aⱼ pⱼ`: `∑ⱼ aⱼ (Nⱼ - off) + off`. -/
def apxNum (B : ℕ) (sh : List ℕ) (Ns : List ℕ) : ℕ :=
  (sumZ (fun j ↦ apxA κ j * ((Ns.getD j 0 : ℤ) - offN B sh)) (ExactBasis.dim κ) +
    offN B sh).toNat

variable (κ) in
/-- The bound of the penalties: those of `∑ⱼ aⱼ pⱼ`, plus `∑ⱼ εⱼ ‖pⱼ‖₁` for the errors. -/
def apxPen (B : ℕ) (sh : List ℕ) (Ns : List ℕ) : ℕ :=
  oddAbs B sh (apxNum κ B sh Ns) + evenNeg B sh (apxNum κ B sh Ns) +
    sumN (fun j ↦ apxE κ j * l1N B sh (Ns.getD j 0)) (ExactBasis.dim κ)

variable (κ) in
/-- **The approximate centred form over a field**: decides the sign of `∑ⱼ βⱼ pⱼ` on the cube by
one sign in `κ`, of `2^k c₀ - apxPen` (`apxOk_sound`). The first test keeps the coefficients of
`∑ⱼ aⱼ pⱼ` below the bias. -/
def apxOk (strict : Bool) (B : ℕ) (sh : List ℕ) (Ns : List ℕ) : Bool :=
  decide (sumN (fun j ↦ (apxA κ j).natAbs * l1N B sh (Ns.getD j 0)) (ExactBasis.dim κ) <
      2 ^ (B - 1)) &&
    signTest strict (Exact.ofInt (2 ^ ExactBasis.apxK κ) *
        ExactBasis.ofCoords ((List.range (ExactBasis.dim κ)).map fun j ↦ cf B (Ns.getD j 0) 0) -
      Exact.ofInt (apxPen κ B sh Ns : ℤ) : κ)

theorem abs_apx_le (j : ℕ) (hj : j < ExactBasis.dim κ) :
    |(2 : ℝ) ^ ExactBasis.apxK κ * ExactBasis.basis κ j - (apxA κ j : ℝ)| ≤ (apxE κ j : ℝ) :=
  ExactBasis.apx_sound j hj

/-- The value of the polynomials `∑ⱼ βⱼ pⱼ`, slot by slot. -/
theorem sum_pv_eq (sh : List ℕ) (c : ℕ → ℕ → ℤ) (y : ℕ → ℝ) :
    ∑ j ∈ range (ExactBasis.dim κ), ExactBasis.basis κ j * pv sh (c j) y =
      ∑ q ∈ range (slots sh),
        (∑ j ∈ range (ExactBasis.dim κ), ExactBasis.basis κ j * (c j q : ℝ)) * mono sh q y := by
  simp only [pv, mul_sum, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun q _ ↦ sum_congr rfl fun j _ ↦ by ring

theorem apxOk_sound {strict : Bool} {B : ℕ} (hB : 0 < B) {sh : List ℕ} {Ns : List ℕ}
    (hinv : ∀ j < ExactBasis.dim κ, Inv B sh (Ns.getD j 0))
    (h : apxOk κ strict B sh Ns = true) {y : ℕ → ℝ} (hy : ∀ i, |y i| ≤ 1) :
    Sign strict (∑ j ∈ range (ExactBasis.dim κ),
      ExactBasis.basis κ j * pv sh (cf B (Ns.getD j 0)) y) := by
  simp only [apxOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hsum, hsign⟩ := h
  set d := ExactBasis.dim κ with hd
  set c : ℕ → ℕ → ℤ := fun j ↦ cf B (Ns.getD j 0) with hc
  set k := ExactBasis.apxK κ with hk
  have hl : ∀ j < d, l1N B sh (Ns.getD j 0) = l1 sh (c j) := fun j hj ↦
    l1N_eq_of_inv hB (hinv j hj)
  -- The combination `a = ∑ⱼ aⱼ cⱼ` and its numeral.
  set a : ℕ → ℤ := fun q ↦ ∑ j ∈ range d, apxA κ j * c j q with ha
  have hsum' : ∑ j ∈ range d, (apxA κ j).natAbs * l1 sh (c j) < 2 ^ (B - 1) := by
    rw [sumN_eq] at hsum
    rwa [sum_congr rfl fun j hj ↦ by rw [hl j (mem_range.mp hj)]] at hsum
  have hal1 : l1 sh a ≤ ∑ j ∈ range d, (apxA κ j).natAbs * l1 sh (c j) := by
    unfold l1
    calc ∑ q ∈ range (slots sh), (a q).natAbs
        ≤ ∑ q ∈ range (slots sh), ∑ j ∈ range d, (apxA κ j).natAbs * (c j q).natAbs :=
          sum_le_sum fun q _ ↦ (natAbs_sum_le _ _).trans (le_of_eq (sum_congr rfl fun j _ ↦
            Int.natAbs_mul _ _))
      _ = ∑ j ∈ range d, (apxA κ j).natAbs * ∑ q ∈ range (slots sh), (c j q).natAbs := by
          rw [sum_comm]
          exact sum_congr rfl fun j _ ↦ (mul_sum _ _ _).symm
  have haq : ∀ q < (slots sh), -2 ^ (B - 1) ≤ a q ∧ a q < 2 ^ (B - 1) := by
    intro q hq
    have h₁ := ((abs_coeff_le_l1 a hq).trans hal1).trans_lt hsum'
    have h₂ : |a q| < 2 ^ (B - 1) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h₁
    constructor <;> linarith [abs_lt.mp h₂]
  obtain ⟨hbias, hdig⟩ := snum_add_bias hB haq
  have hA : apxNum κ B sh Ns = num B (fun q ↦ (a q + 2 ^ (B - 1)).toNat) (slots sh) := by
    have h₁ : ∑ j ∈ range d, apxA κ j * ((Ns.getD j 0 : ℤ) - offN B sh) = snum B a (slots sh) := by
      rw [sum_congr rfl fun j hj ↦ by rw [sub_offN hB (hinv j (mem_range.mp hj)).1], sum_snum]
    rw [apxNum, sumZ_eq, ← hd, h₁, offN_eq, hbias, Int.toNat_natCast]
  have hAlt : apxNum κ B sh Ns < 2 ^ (B * (slots sh)) := hA ▸ num_lt hdig
  have hcfA : ∀ q < (slots sh), cf B (apxNum κ B sh Ns) q = a q := by
    intro q hq
    rw [hA, cf, dig_num hB hdig hq, Int.toNat_of_nonneg (by linarith [(haq q hq).1])]
    ring
  have hl1A : l1 sh (cf B (apxNum κ B sh Ns)) < 2 ^ B - 1 := by
    rw [l1_congr hcfA]
    exact (hal1.trans_lt hsum').trans_le (two_pow_pred_le hB)
  have hpenA := sum_pen_eq hB hAlt hl1A
  rw [sum_congr rfl fun q hq ↦ by
    rw [show pen sh (fun p ↦ (cf B (apxNum κ B sh Ns) p : ℝ)) q = pen sh (fun p ↦ (a p : ℝ)) q by
      unfold pen; dsimp only; rw [hcfA q (mem_range.mp hq)]]] at hpenA
  -- The real coefficients `C q = ∑ⱼ βⱼ cⱼ q` and the centred form.
  set C : ℕ → ℝ := fun q ↦ ∑ j ∈ range d, ExactBasis.basis κ j * (c j q : ℝ) with hC
  have hV : ∑ j ∈ range d, ExactBasis.basis κ j * pv sh (c j) y =
      ∑ q ∈ range (slots sh), C q * mono sh q y := sum_pv_eq (κ := κ) sh c y
  have hsm : ∑ q ∈ range (slots sh), pen sh (fun p ↦ (2 : ℝ) ^ k * C p) q =
      (2 : ℝ) ^ k * ∑ q ∈ range (slots sh), pen sh C q := by
    rw [mul_sum]
    exact sum_congr rfl fun q _ ↦ pen_smul (by positivity) q
  have hcf := sum_ge_pen (sh := sh) C hy
  -- The errors.
  have herr : ∀ q, |(2 : ℝ) ^ k * C q - (a q : ℝ)| ≤
      ∑ j ∈ range d, (apxE κ j : ℝ) * |(c j q : ℝ)| := by
    intro q
    have : (2 : ℝ) ^ k * C q - (a q : ℝ) =
        ∑ j ∈ range d, ((2 : ℝ) ^ k * ExactBasis.basis κ j - (apxA κ j : ℝ)) * (c j q : ℝ) := by
      simp only [hC, ha]
      push_cast
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun j _ ↦ by ring
    rw [this]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj ↦ ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_apx_le j (mem_range.mp hj)) (abs_nonneg _)
  have hpen :
      ∑ q ∈ range (slots sh), pen sh (fun p ↦ (2 : ℝ) ^ k * C p) q ≤ (apxPen κ B sh Ns : ℝ) := by
    calc ∑ q ∈ range (slots sh), pen sh (fun p ↦ (2 : ℝ) ^ k * C p) q
        ≤ ∑ q ∈ range (slots sh), (pen sh (fun p ↦ (a p : ℝ)) q +
            ∑ j ∈ range d, (apxE κ j : ℝ) * |(c j q : ℝ)|) := by
          refine sum_le_sum fun q _ ↦ (pen_le_add (C' := fun p ↦ (a p : ℝ)) q).trans ?_
          gcongr
          split_ifs
          · exact sum_nonneg fun j _ ↦ by positivity
          · exact herr q
      _ = (oddAbs B sh (apxNum κ B sh Ns) : ℝ) + (evenNeg B sh (apxNum κ B sh Ns) : ℝ) +
            ∑ j ∈ range d, (apxE κ j : ℝ) * (l1 sh (c j) : ℝ) := by
          rw [sum_add_distrib, hpenA, sum_comm]
          congr 1
          refine sum_congr rfl fun j _ ↦ ?_
          rw [← mul_sum, l1, Nat.cast_sum]
          congr 1
          exact sum_congr rfl fun q _ ↦ by rw [Nat.cast_natAbs, Int.cast_abs]
      _ = (apxPen κ B sh Ns : ℝ) := by
          rw [apxPen, sumN_eq]
          push_cast
          congr 1
          exact sum_congr rfl fun j hj ↦ by rw [hl j (mem_range.mp hj)]
  -- The value tested in `κ`.
  have hre : Exact.re (Exact.ofInt (2 ^ k) * ExactBasis.ofCoords ((List.range d).map fun j ↦
      cf B (Ns.getD j 0) 0) - Exact.ofInt (apxPen κ B sh Ns : ℤ) : κ) =
      (2 : ℝ) ^ k * C 0 - (apxPen κ B sh Ns : ℝ) := by
    rw [Exact.re_sub, Exact.re_mul, Exact.re_ofInt, Exact.re_ofInt, ExactBasis.re_ofCoords, bsum]
    push_cast
    congr 2
    refine sum_congr rfl fun j hj ↦ ?_
    rw [List.getD_eq_getElem _ _ (by simpa using mem_range.mp hj), List.getElem_map,
      List.getElem_map, List.getElem_range]
  have hs := sign_of_signTest hsign
  rw [hre] at hs
  refine sign_of_mul (t := (2 : ℝ) ^ k) (by positivity) (sign_of_le hs ?_)
  rw [hV]
  have h₁ := mul_le_mul_of_nonneg_left hcf (by positivity : (0 : ℝ) ≤ 2 ^ k)
  rw [mul_sub] at h₁
  linarith

end Field

end Lay

end Nieuwland.Check
