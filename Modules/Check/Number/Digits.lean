import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Numerals with `B`-bit digits

A packed polynomial is a natural number whose digits in base `2^B` are its coefficients plus a
bias (`Modules/Check/Polynomial/Pack.lean`). The kernel computes with such numerals by a few bitwise and
arithmetic operations on whole numerals, each one call into its big-integer library, instead of
digit by digit. This file has the facts about digits that make those operations sound.

* `num B a L = ∑_{p < L} a p 2^(B p)`: the numeral with the digits `a 0, …, a (L-1)`
  (each below `2^B`: `Digits B a L`).
* `testBit_num`: bit `j` is bit `j % B` of digit `j / B`; hence `num_land` (`&&&` acts digitwise),
  `num_shiftRight` (shifting by `B t` bits drops `t` digits) and `num_div_mod` (reading a digit).
* `num_mod_mersenne`: modulo `2^B - 1`, a numeral is congruent to its digit sum, which it equals
  when the sum is smaller (`num_mod_mersenne_of_lt`). One `%` thus sums all digits.
* `dig B N p = N / 2^(B p) % 2^B`, with `num_dig`: a numeral below `2^(B L)` is the numeral of its
  digits.
* `snum B c L = ∑_{p < L} c p 2^(B p)` for integer digits, and `snum_add_bias`: adding the bias
  `h = 2^(B-1)` to every digit of `c` with `-h ≤ c p < h` gives a numeral.
-/

open Finset

namespace Nieuwland.Check

/-- The numeral `∑_{p < L} a p 2^(B p)` with the digits `a 0, …, a (L - 1)`. -/
def num (B : ℕ) (a : ℕ → ℕ) (L : ℕ) : ℕ := ∑ p ∈ range L, a p * 2 ^ (B * p)

/-- The digits `a 0, …, a (L - 1)` are below `2^B`. -/
def Digits (B : ℕ) (a : ℕ → ℕ) (L : ℕ) : Prop := ∀ p < L, a p < 2 ^ B

/-- Digit `p` of `N` in base `2^B`. -/
def dig (B N p : ℕ) : ℕ := N / 2 ^ (B * p) % 2 ^ B

/-- `dig` by masks and shifts (compiled code divides by general division;
`Modules/Check/Polynomial/Pack.lean`, `divP2`), reading at most about half of `N`: the low `B (p + 1)` bits
then a shift where they are at most half of its bits, else a shift then a mask. -/
def digS (B N p : ℕ) : ℕ :=
  bif Nat.ble (2 * (B * p)) N.log2 then (N &&& ((1 <<< (B * (p + 1))) - 1)) >>> (B * p)
  else (N >>> (B * p)) &&& (2 ^ B - 1)

@[csimp] theorem dig_eq_digS : @dig = @digS := by
  funext B N p
  unfold dig digS
  cases Nat.ble (2 * (B * p)) N.log2
  · rw [Bool.cond_false, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]
  · rw [Bool.cond_true, Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod,
      Nat.shiftRight_eq_div_pow, Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mod_mul_right_div_self]

/-- A product with a power of two is a shift (for the `@[csimp]` versions of the digit
operations: compiled code multiplies by general multiplication). -/
theorem two_pow_mul_eq_shiftLeft (k x : ℕ) : 2 ^ k * x = x <<< k := by
  rw [Nat.shiftLeft_eq, Nat.mul_comm]

/-- A product with `2^B - 1` is a shift and a subtraction. -/
theorem two_pow_sub_one_mul_eq (B x : ℕ) : (2 ^ B - 1) * x = (x <<< B) - x := by
  rw [Nat.sub_mul, Nat.one_mul, two_pow_mul_eq_shiftLeft]

namespace Num

variable {B L : ℕ} {a b : ℕ → ℕ}

theorem num_zero (B : ℕ) (a : ℕ → ℕ) : num B a 0 = 0 := by simp [num]

theorem num_succ (B : ℕ) (a : ℕ → ℕ) (L : ℕ) :
    num B a (L + 1) = num B a L + a L * 2 ^ (B * L) := by
  simp [num, sum_range_succ]

theorem num_congr {L : ℕ} (h : ∀ p < L, a p = b p) : num B a L = num B b L :=
  sum_congr rfl fun p hp ↦ by rw [h p (mem_range.mp hp)]

theorem num_add (B : ℕ) (a b : ℕ → ℕ) (L : ℕ) :
    num B a L + num B b L = num B (fun p ↦ a p + b p) L := by
  simp only [num, ← sum_add_distrib, add_mul]

theorem num_mul (B : ℕ) (m : ℕ) (a : ℕ → ℕ) (L : ℕ) :
    m * num B a L = num B (fun p ↦ m * a p) L := by
  simp only [num, mul_sum, mul_assoc]

theorem digits_of_le (hb : Digits B b L) (h : ∀ p < L, a p ≤ b p) : Digits B a L :=
  fun p hp ↦ (h p hp).trans_lt (hb p hp)

theorem num_lt (ha : Digits B a L) : num B a L < 2 ^ (B * L) := by
  induction L with
  | zero => simp [num]
  | succ L ih =>
    have h₁ := ih fun p hp ↦ ha p (by omega)
    have h₂ : a L + 1 ≤ 2 ^ B := ha L (by omega)
    rw [num_succ]
    calc num B a L + a L * 2 ^ (B * L) < 2 ^ (B * L) + a L * 2 ^ (B * L) := by omega
      _ = (a L + 1) * 2 ^ (B * L) := by ring
      _ ≤ 2 ^ B * 2 ^ (B * L) := Nat.mul_le_mul_right _ h₂
      _ = 2 ^ (B * (L + 1)) := by rw [← pow_add]; ring_nf

/-- **Bits of a numeral**: bit `j` is bit `j % B` of digit `j / B`. -/
theorem testBit_num (hB : 0 < B) (ha : Digits B a L) (j : ℕ) :
    (num B a L).testBit j = (decide (j / B < L) && (a (j / B)).testBit (j % B)) := by
  induction L with
  | zero => simp [num]
  | succ L ih =>
    have hlt := num_lt fun p (hp : p < L) ↦ ha p (by omega)
    rw [num_succ, add_comm, mul_comm, Nat.testBit_two_pow_mul_add _ hlt,
      ih fun p hp ↦ ha p (by omega)]
    have hj := Nat.div_add_mod j B
    have hjm := Nat.mod_lt j hB
    split_ifs with h
    · have : j / B < L := by
        by_contra hc
        have : B * L ≤ B * (j / B) := Nat.mul_le_mul_left B (by omega)
        omega
      simp [this, show j / B < L + 1 by omega]
    · rcases Nat.lt_or_ge (j / B) (L + 1) with h₁ | h₁
      · have hjL : j / B = L := by
          by_contra hc
          have : B * (j / B) + B ≤ B * L := by
            have : j / B + 1 ≤ L := by omega
            nlinarith
          omega
        have : j - B * L = j % B := by rw [← hjL]; omega
        simp [hjL, this]
      · have hge : B ≤ j - B * L := by
          have : B * (L + 1) ≤ B * (j / B) := Nat.mul_le_mul_left B h₁
          have : B * (L + 1) = B * L + B := by ring
          omega
        have : (a L).testBit (j - B * L) = false :=
          Nat.testBit_lt_two_pow
            ((ha L (by omega)).trans_le (Nat.pow_le_pow_right (by norm_num) hge))
        simp [this, show ¬ j / B < L + 1 by omega]

theorem testBit_of_digit {d : ℕ} (hd : d < 2 ^ B) {i : ℕ} (hi : B ≤ i) : d.testBit i = false :=
  Nat.testBit_lt_two_pow (hd.trans_le (Nat.pow_le_pow_right (by norm_num) hi))

/-- Two numerals with the same digits are equal; with `testBit_num`, the way to compute
bitwise operations digitwise. -/
theorem num_eq_of_testBit {N : ℕ} (hB : 0 < B) (ha : Digits B a L)
    (h : ∀ j, N.testBit j = (decide (j / B < L) && (a (j / B)).testBit (j % B))) :
    N = num B a L :=
  Nat.eq_of_testBit_eq fun j ↦ by rw [h, testBit_num hB ha]

/-- **`&&&` acts digitwise.** -/
theorem num_land (hB : 0 < B) (ha : Digits B a L) (hb : Digits B b L) :
    num B a L &&& num B b L = num B (fun p ↦ a p &&& b p) L := by
  refine num_eq_of_testBit hB (fun p hp ↦ Nat.and_lt_two_pow _ (hb p hp)) fun j ↦ ?_
  rw [Nat.testBit_and, testBit_num hB ha, testBit_num hB hb, Nat.testBit_and]
  cases decide (j / B < L) <;> simp

/-- **Shifting right by `B t` bits drops `t` digits.** -/
theorem num_shiftRight (hB : 0 < B) (ha : Digits B a L) (t : ℕ) :
    num B a L >>> (B * t) = num B (fun p ↦ if p + t < L then a (p + t) else 0) L := by
  refine num_eq_of_testBit hB (fun p hp ↦ ?_) fun j ↦ ?_
  · split_ifs with h
    · exact ha _ h
    · exact Nat.two_pow_pos B
  · rw [Nat.testBit_shiftRight, testBit_num hB ha]
    have e₁ : (B * t + j) / B = j / B + t := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hB]
    have e₂ : (B * t + j) % B = j % B := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left]
    rw [e₁, e₂]
    by_cases h : j / B + t < L
    · simp [h, show j / B < L by omega]
    · simp [h]

theorem digit_eq (hB : 0 < B) (ha : Digits B a L) {p : ℕ} (hp : p < L) :
    num B a L / 2 ^ (B * p) % 2 ^ B = a p := by
  refine Nat.eq_of_testBit_eq fun i ↦ ?_
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, testBit_num hB ha]
  by_cases hi : i < B
  · have e₁ : (i + B * p) / B = p := by
      rw [Nat.add_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt hi, add_zero]
    have e₂ : (i + B * p) % B = i := by
      rw [Nat.add_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
    simp [hi, e₁, e₂, hp]
  · simp [hi, testBit_of_digit (ha p hp) (show B ≤ i by omega)]

/-- **Reading a digit.** -/
theorem dig_num (hB : 0 < B) (ha : Digits B a L) {p : ℕ} (hp : p < L) : dig B (num B a L) p = a p :=
  digit_eq hB ha hp

theorem dig_lt (B N p : ℕ) : dig B N p < 2 ^ B := Nat.mod_lt _ (Nat.two_pow_pos B)

theorem digits_dig (B N L : ℕ) : Digits B (dig B N) L := fun p _ ↦ dig_lt B N p

/-- Digits beyond a numeral's length vanish. -/
theorem dig_eq_zero {N : ℕ} (hN : N < 2 ^ (B * L)) {p : ℕ} (hp : L ≤ p) : dig B N p = 0 := by
  have : N < 2 ^ (B * p) := hN.trans_le (Nat.pow_le_pow_right (by norm_num) (by
    exact Nat.mul_le_mul_left B hp))
  simp [dig, Nat.div_eq_of_lt this]

/-- **A numeral is the numeral of its digits.** -/
theorem num_dig (hB : 0 < B) {N : ℕ} (hN : N < 2 ^ (B * L)) : num B (dig B N) L = N := by
  symm
  refine num_eq_of_testBit hB (digits_dig B N L) fun j ↦ ?_
  have hj := Nat.div_add_mod j B
  have hjm := Nat.mod_lt j hB
  rw [dig, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  have e : j % B + B * (j / B) = j := by omega
  rw [e]
  by_cases h : j / B < L
  · simp [h, hjm]
  · have h₁ : B * L ≤ B * (j / B) := Nat.mul_le_mul_left B (by omega)
    have : N.testBit j = false := Nat.testBit_lt_two_pow (hN.trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [h, this]

/-! ### Digit sums -/

theorem two_pow_modEq_one (B : ℕ) : Nat.ModEq (2 ^ B - 1) (2 ^ B) 1 := by
  have h : 2 ^ B = (2 ^ B - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_two_pow)).symm
  calc 2 ^ B = (2 ^ B - 1) + 1 := h
    _ ≡ 0 + 1 [MOD 2 ^ B - 1] := Nat.ModEq.add_right 1 (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)
    _ = 1 := zero_add 1

/-- **Modulo `2^B - 1`, a numeral is its digit sum.** -/
theorem num_modEq_sum (B : ℕ) (a : ℕ → ℕ) (L : ℕ) :
    Nat.ModEq (2 ^ B - 1) (num B a L) (∑ p ∈ range L, a p) := by
  induction L with
  | zero => simp [num_zero]; rfl
  | succ L ih =>
    rw [num_succ, sum_range_succ]
    refine Nat.ModEq.add ih ?_
    have : Nat.ModEq (2 ^ B - 1) (2 ^ (B * L)) 1 := by
      rw [pow_mul]
      simpa using (two_pow_modEq_one B).pow L
    simpa using Nat.ModEq.mul_left (a L) this

theorem num_mod_mersenne (B : ℕ) (a : ℕ → ℕ) (L : ℕ) :
    num B a L % (2 ^ B - 1) = (∑ p ∈ range L, a p) % (2 ^ B - 1) := num_modEq_sum B a L

/-- **One `%` sums the digits**, when their sum is below `2^B - 1`. -/
theorem num_mod_mersenne_of_lt (h : ∑ p ∈ range L, a p < 2 ^ B - 1) :
    num B a L % (2 ^ B - 1) = ∑ p ∈ range L, a p := by
  rw [num_mod_mersenne, Nat.mod_eq_of_lt h]

/-! ### Integer digits -/

/-- `∑_{p < L} c p 2^(B p)` for integer digits `c`. -/
def snum (B : ℕ) (c : ℕ → ℤ) (L : ℕ) : ℤ := ∑ p ∈ range L, c p * 2 ^ (B * p)

theorem snum_natCast (B : ℕ) (a : ℕ → ℕ) (L : ℕ) :
    ((num B a L : ℕ) : ℤ) = snum B (fun p ↦ (a p : ℤ)) L := by
  simp [num, snum]

theorem snum_add (B : ℕ) (c d : ℕ → ℤ) (L : ℕ) :
    snum B c L + snum B d L = snum B (fun p ↦ c p + d p) L := by
  simp only [snum, ← sum_add_distrib, add_mul]

theorem snum_sub (B : ℕ) (c d : ℕ → ℤ) (L : ℕ) :
    snum B c L - snum B d L = snum B (fun p ↦ c p - d p) L := by
  simp only [snum, ← sum_sub_distrib, sub_mul]

theorem snum_mul (B : ℕ) (m : ℤ) (c : ℕ → ℤ) (L : ℕ) :
    m * snum B c L = snum B (fun p ↦ m * c p) L := by
  simp only [snum, mul_sum, mul_assoc]

theorem snum_congr {c d : ℕ → ℤ} (h : ∀ p < L, c p = d p) : snum B c L = snum B d L :=
  sum_congr rfl fun p hp ↦ by rw [h p (mem_range.mp hp)]

/-- **Biased digits.** If `-h ≤ c p < h` for `h = 2^(B-1)`, then `c` plus the bias in every
digit is a numeral with the digits `c p + h`. -/
theorem snum_add_bias (hB : 0 < B) {c : ℕ → ℤ}
    (hc : ∀ p < L, -2 ^ (B - 1) ≤ c p ∧ c p < 2 ^ (B - 1)) :
    snum B c L + ((num B (fun _ ↦ 2 ^ (B - 1)) L : ℕ) : ℤ) =
      ((num B (fun p ↦ (c p + 2 ^ (B - 1)).toNat) L : ℕ) : ℤ) ∧
    Digits B (fun p ↦ (c p + 2 ^ (B - 1)).toNat) L := by
  have h2 : (2 : ℤ) ^ B = 2 * 2 ^ (B - 1) := by
    rw [← pow_succ']; congr 1; omega
  refine ⟨?_, fun p hp ↦ ?_⟩
  · rw [snum_natCast, snum_natCast, snum_add]
    refine snum_congr fun p hp ↦ ?_
    rw [Int.toNat_of_nonneg (by linarith [(hc p hp).1])]
    push_cast
    ring
  · have := hc p hp
    have : (c p + 2 ^ (B - 1)).toNat < ((2 ^ B : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg (by linarith)]
      push_cast
      linarith
    exact_mod_cast this

end Num

end Nieuwland.Check
