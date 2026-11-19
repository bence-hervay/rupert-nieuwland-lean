import Modules.Check.Number.Digits
import Modules.Check.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Sum

/-!
# Polynomials laid out in slots

A polynomial whose degree in `yᵢ` is at most `eᵢ` (a *shape* `sh = [e₀, e₁, …]`) has one slot per
exponent vector, `slots sh = ∏ (eᵢ + 1)` in all, in mixed radix with `y₀` outermost: slot `q` holds
the coefficient of `∏ yᵢ ^ ex sh i q`, where `ex sh i q = q / stride sh i % (eᵢ + 1)` and
`stride sh i = ∏_{j > i} (eⱼ + 1)`. This is the order of `DPoly.unpack` (`eval_unpack_eq_pv`), and
at the packing point `Yᵢ = 2^(B strideᵢ)` the monomial of slot `q` is `2^(B q)` (`mono_pack`), so
the packed value of a polynomial is the numeral of its coefficients (`pv_pack`).

Here the polynomial with coefficients `c : ℕ → ℤ` is `pv sh c y = ∑_{q < slots sh} c q mono sh q y`,
and `l1 sh c` is its absolute coefficient sum. The operations of the packed engine
(`Modules/Check/Sign/Engine.lean`) act on the coefficient functions:

* `slc sh i k c`: the coefficients of `yᵢ^k`, a polynomial without `yᵢ`, with
  `pv sh c y = ∑_k yᵢ^k pv sh (slc sh i k c) y` (`pv_slc`, `l1_slc`);
* `sub sh i w a b c`: the coefficients of `∑_k w_k (a + b yᵢ)^k pv sh (slc sh i k c) y`
  (`pv_sub`), with `l1_sub_le` bounding their absolute sum;
* `ind B sh T`: the numeral with the digit `1` in the slots whose exponents satisfy `T`
  variable by variable (`ind_eq`), from which the kernel builds digit masks.
-/

open Finset

namespace Nieuwland.Check

namespace Lay

open DPoly Num

/-- The degree bound of variable `i`. -/
def deg (sh : List ℕ) (i : ℕ) : ℕ := sh.getD i 0

/-- The stride of variable `i`: the number of slots of the variables after it. -/
def stride (sh : List ℕ) (i : ℕ) : ℕ := slots (sh.drop (i + 1))

/-- The exponent of variable `i` in slot `q`. -/
def ex (sh : List ℕ) (i q : ℕ) : ℕ := q / stride sh i % (deg sh i + 1)

/-- The monomial of slot `q`. -/
def mono {R : Type*} [CommMonoid R] (sh : List ℕ) (q : ℕ) (y : ℕ → R) : R :=
  ∏ i ∈ range sh.length, y i ^ ex sh i q

/-- The polynomial with the coefficients `c q` in the slots of `sh`. -/
def pv {R : Type*} [CommRing R] (sh : List ℕ) (c : ℕ → ℤ) (y : ℕ → R) : R :=
  ∑ q ∈ range (slots sh), (c q : R) * mono sh q y

/-- The absolute coefficient sum. -/
def l1 (sh : List ℕ) (c : ℕ → ℤ) : ℕ := ∑ q ∈ range (slots sh), (c q).natAbs

/-! ### Recursive structure -/

section Cons

variable {e : ℕ} {t : List ℕ}

@[simp] theorem deg_cons_zero : deg (e :: t) 0 = e := rfl
@[simp] theorem deg_cons_succ (i : ℕ) : deg (e :: t) (i + 1) = deg t i := rfl
@[simp] theorem stride_cons_zero : stride (e :: t) 0 = slots t := rfl
@[simp] theorem stride_cons_succ (i : ℕ) : stride (e :: t) (i + 1) = stride t i := rfl

theorem deg_of_le {sh : List ℕ} {i : ℕ} (h : sh.length ≤ i) : deg sh i = 0 :=
  List.getD_eq_default _ _ h

theorem stride_of_le {sh : List ℕ} {i : ℕ} (h : sh.length ≤ i) : stride sh i = 1 := by
  rw [stride, List.drop_eq_nil_of_le (by omega)]
  rfl

theorem ex_of_le {sh : List ℕ} {i : ℕ} (h : sh.length ≤ i) (q : ℕ) : ex sh i q = 0 := by
  rw [ex, deg_of_le h, Nat.mod_one]

theorem slots_pos (sh : List ℕ) : 0 < slots sh := one_le_slots sh

theorem stride_pos (sh : List ℕ) (i : ℕ) : 0 < stride sh i := slots_pos _

/-- The block of variable `i` divides the slots. -/
theorem stride_mul_dvd : ∀ (sh : List ℕ) (i : ℕ), stride sh i * (deg sh i + 1) ∣ slots sh
  | [], i => by simp [stride, deg, slots]
  | e :: t, 0 => ⟨1, by simp [slots]; ring⟩
  | e :: t, i + 1 => by
    simp only [stride_cons_succ, deg_cons_succ, slots]
    exact (stride_mul_dvd t i).trans (Dvd.intro_left _ rfl)

theorem stride_dvd (sh : List ℕ) (i : ℕ) : stride sh i ∣ slots sh :=
  (Dvd.intro _ rfl).trans (stride_mul_dvd sh i)

theorem ex_cons_zero {k r : ℕ} (hk : k ≤ e) (hr : r < slots t) :
    ex (e :: t) 0 (k * slots t + r) = k := by
  rw [ex, stride_cons_zero, deg_cons_zero, add_comm, Nat.add_mul_div_right _ _ (slots_pos t),
    Nat.div_eq_of_lt hr, zero_add, Nat.mod_eq_of_lt (by omega)]

theorem ex_cons_succ (k : ℕ) {r : ℕ} (i : ℕ) (_hr : r < slots t) :
    ex (e :: t) (i + 1) (k * slots t + r) = ex t i r := by
  rw [ex, ex, stride_cons_succ, deg_cons_succ]
  obtain ⟨m, hm⟩ := stride_mul_dvd t i
  have hs := stride_pos t i
  have e₁ : (k * slots t + r) / stride t i = k * (deg t i + 1) * m + r / stride t i := by
    rw [hm, show k * (stride t i * (deg t i + 1) * m) = k * (deg t i + 1) * m * stride t i by ring,
      Nat.add_comm, Nat.add_mul_div_right _ _ hs, Nat.add_comm]
  rw [e₁, show k * (deg t i + 1) * m = (deg t i + 1) * (k * m) by ring, Nat.mul_add_mod]

theorem mono_cons {R : Type*} [CommMonoid R] {k r : ℕ} (hk : k ≤ e) (hr : r < slots t)
    (y : ℕ → R) : mono (e :: t) (k * slots t + r) y = y 0 ^ k * mono t r fun i ↦ y (i + 1) := by
  rw [mono, List.length_cons, prod_range_succ', ex_cons_zero hk hr, mul_comm, mono]
  congr 1
  exact prod_congr rfl fun i _ ↦ by rw [ex_cons_succ k i hr]

/-- A sum over the slots of `e :: t`, block by block. -/
theorem sum_range_mul {M : Type*} [AddCommMonoid M] (S : ℕ) (f : ℕ → M) :
    ∀ m : ℕ, ∑ q ∈ range (m * S), f q = ∑ k ∈ range m, ∑ r ∈ range S, f (k * S + r)
  | 0 => by simp
  | m + 1 => by
    rw [show (m + 1) * S = m * S + S by ring, sum_range_add, sum_range_mul S f m, sum_range_succ]

theorem pv_cons {R : Type*} [CommRing R] (c : ℕ → ℤ) (y : ℕ → R) :
    pv (e :: t) c y = ∑ k ∈ range (e + 1),
      y 0 ^ k * pv t (fun r ↦ c (k * slots t + r)) fun i ↦ y (i + 1) := by
  rw [pv, slots, sum_range_mul]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [pv, mul_sum]
  refine sum_congr rfl fun r hr ↦ ?_
  rw [mono_cons (Nat.lt_succ_iff.mp (mem_range.mp hk)) (mem_range.mp hr)]
  ring

theorem l1_cons (c : ℕ → ℤ) :
    l1 (e :: t) c = ∑ k ∈ range (e + 1), l1 t fun r ↦ c (k * slots t + r) := by
  rw [l1, slots, sum_range_mul]
  rfl

end Cons

theorem pv_nil {R : Type*} [CommRing R] (c : ℕ → ℤ) (y : ℕ → R) : pv [] c y = c 0 := by
  simp [pv, mono, slots]

theorem l1_nil (c : ℕ → ℤ) : l1 [] c = (c 0).natAbs := by
  simp [l1, slots]

/-! ### Basic properties -/

theorem pv_congr {R : Type*} [CommRing R] {sh : List ℕ} {c d : ℕ → ℤ}
    (h : ∀ q < slots sh, c q = d q) (y : ℕ → R) : pv sh c y = pv sh d y :=
  sum_congr rfl fun q hq ↦ by rw [h q (mem_range.mp hq)]

theorem l1_congr {sh : List ℕ} {c d : ℕ → ℤ} (h : ∀ q < slots sh, c q = d q) : l1 sh c = l1 sh d :=
  sum_congr rfl fun q hq ↦ by rw [h q (mem_range.mp hq)]

theorem pv_zero {R : Type*} [CommRing R] (sh : List ℕ) (y : ℕ → R) : pv sh (fun _ ↦ 0) y = 0 := by
  simp [pv]

theorem pv_add {R : Type*} [CommRing R] (sh : List ℕ) (c d : ℕ → ℤ) (y : ℕ → R) :
    pv sh (fun q ↦ c q + d q) y = pv sh c y + pv sh d y := by
  simp only [pv, ← sum_add_distrib, Int.cast_add, add_mul]

theorem pv_smul {R : Type*} [CommRing R] (sh : List ℕ) (m : ℤ) (c : ℕ → ℤ) (y : ℕ → R) :
    pv sh (fun q ↦ m * c q) y = m * pv sh c y := by
  simp only [pv, mul_sum, Int.cast_mul, mul_assoc]

theorem pv_sum {R : Type*} [CommRing R] (sh : List ℕ) {ι : Type*} (s : Finset ι)
    (c : ι → ℕ → ℤ) (y : ℕ → R) :
    pv sh (fun q ↦ ∑ k ∈ s, c k q) y = ∑ k ∈ s, pv sh (c k) y := by
  simp only [pv, Int.cast_sum, sum_mul]
  exact sum_comm

theorem pv_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (sh : List ℕ) (c : ℕ → ℤ)
    (y : ℕ → R) : f (pv sh c y) = pv sh c fun i ↦ f (y i) := by
  simp [pv, mono, map_sum, map_prod]

/-- The absolute coefficient sum is the polynomial of the absolute values at `1`. -/
theorem l1_eq_pv (sh : List ℕ) (c : ℕ → ℤ) :
    (l1 sh c : ℤ) = pv sh (fun q ↦ |c q|) fun _ ↦ (1 : ℤ) := by
  simp [l1, pv, mono]

theorem abs_coeff_le_l1 {sh : List ℕ} (c : ℕ → ℤ) {q : ℕ} (hq : q < slots sh) :
    (c q).natAbs ≤ l1 sh c :=
  single_le_sum (f := fun q ↦ (c q).natAbs) (fun _ _ ↦ Nat.zero_le _) (mem_range.mpr hq)

/-! ### The packing point -/

/-- **Mixed radix**: a slot is the sum of its exponents times the strides. -/
theorem sum_ex_mul_stride : ∀ (sh : List ℕ) {q : ℕ}, q < slots sh →
    ∑ i ∈ range sh.length, ex sh i q * stride sh i = q
  | [], q, hq => by simp [slots] at hq; simp [hq]
  | e :: t, q, hq => by
    have hS := slots_pos t
    have hk : q / slots t ≤ e := by
      rw [slots] at hq
      exact Nat.lt_succ_iff.mp (Nat.div_lt_of_lt_mul (by linarith))
    have hr : q % slots t < slots t := Nat.mod_lt _ hS
    have hq' : q = q / slots t * slots t + q % slots t := (Nat.div_add_mod' q (slots t)).symm
    rw [List.length_cons, sum_range_succ']
    conv_lhs => rw [hq']
    simp only [stride_cons_succ, stride_cons_zero, ex_cons_succ _ _ hr, ex_cons_zero hk hr]
    rw [sum_ex_mul_stride t hr]
    omega

/-- The packing point `Yᵢ = 2^(B strideᵢ)`. -/
def packY (B : ℕ) (sh : List ℕ) (i : ℕ) : ℤ := 2 ^ (B * stride sh i)

theorem mono_pack (B : ℕ) {sh : List ℕ} {q : ℕ} (hq : q < slots sh) :
    mono sh q (packY B sh) = 2 ^ (B * q) := by
  conv_rhs => rw [← sum_ex_mul_stride sh hq, mul_sum, ← prod_pow_eq_pow_sum]
  rw [mono]
  refine prod_congr rfl fun i _ ↦ ?_
  rw [packY, ← pow_mul]
  ring_nf

/-- **The packed value is the numeral of the coefficients.** -/
theorem pv_pack (B : ℕ) (sh : List ℕ) (c : ℕ → ℤ) : pv sh c (packY B sh) = snum B c (slots sh) :=
  sum_congr rfl fun q hq ↦ by rw [mono_pack B (mem_range.mp hq)]; rfl

/-! ### Slices -/

/-- The coefficients of `yᵢ^k`: `c (q + k strideᵢ)` in the slots `q` of exponent `0` in `yᵢ`. -/
def slc (sh : List ℕ) (i k : ℕ) (c : ℕ → ℤ) (q : ℕ) : ℤ :=
  if ex sh i q = 0 then c (q + k * stride sh i) else 0

theorem slc_cons_zero {e : ℕ} {t : List ℕ} {k k' r : ℕ} (_hk : k ≤ e) (hk' : k' ≤ e)
    (hr : r < slots t) (c : ℕ → ℤ) :
    slc (e :: t) 0 k c (k' * slots t + r) = if k' = 0 then c (k * slots t + r) else 0 := by
  rw [slc, ex_cons_zero hk' hr, stride_cons_zero]
  split_ifs with h
  · subst h; ring_nf
  · rfl

theorem slc_cons_succ {e : ℕ} {t : List ℕ} (i k k' : ℕ) {r : ℕ} (hr : r < slots t)
    (c : ℕ → ℤ) :
    slc (e :: t) (i + 1) k c (k' * slots t + r) = slc t i k (fun r ↦ c (k' * slots t + r)) r := by
  rw [slc, slc, ex_cons_succ k' i hr, stride_cons_succ, add_assoc]

/-- **Decomposition by the powers of `yᵢ`.** -/
theorem pv_slc {R : Type*} [CommRing R] : ∀ (sh : List ℕ) (i : ℕ) (c : ℕ → ℤ) (y : ℕ → R),
    pv sh c y = ∑ k ∈ range (deg sh i + 1), y i ^ k * pv sh (slc sh i k c) y
  | [], i, c, y => by
    simp [deg, slc, ex, stride, slots, pv_nil]
  | e :: t, 0, c, y => by
    rw [pv_cons, deg_cons_zero]
    refine sum_congr rfl fun k hk ↦ ?_
    have hk' := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [pv_cons, sum_eq_single 0]
    · rw [pow_zero, one_mul]
      congr 1
      exact pv_congr (fun r hr ↦ by
        rw [slc_cons_zero hk' (Nat.zero_le e) hr, ite_eq_left_iff.mpr (fun h ↦ absurd rfl h)]) _
    · intro k' hk'' hne
      rw [pv_congr (d := fun _ ↦ 0) (fun r hr ↦ by
        rw [slc_cons_zero hk' (Nat.lt_succ_iff.mp (mem_range.mp hk'')) hr]; simp [hne]), pv_zero,
        mul_zero]
    · exact fun h ↦ absurd (mem_range.mpr (Nat.succ_pos e)) h
  | e :: t, i + 1, c, y => by
    rw [pv_cons, deg_cons_succ]
    have h₁ : ∀ k0 ∈ range (e + 1),
        y 0 ^ k0 * pv t (fun r ↦ c (k0 * slots t + r)) (fun i ↦ y (i + 1)) =
          ∑ k ∈ range (deg t i + 1), y 0 ^ k0 * (y (i + 1) ^ k *
            pv t (slc t i k fun r ↦ c (k0 * slots t + r)) fun i ↦ y (i + 1)) := by
      intro k0 _
      rw [pv_slc t i _ (fun i ↦ y (i + 1)), mul_sum]
    refine (sum_congr rfl h₁).trans ?_
    rw [sum_comm]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [pv_cons, mul_sum]
    refine sum_congr rfl fun k' _ ↦ ?_
    rw [pv_congr (fun r hr ↦ slc_cons_succ i k k' hr c)]
    ring

theorem slc_abs (sh : List ℕ) (i k : ℕ) (c : ℕ → ℤ) (q : ℕ) :
    slc sh i k (fun q ↦ |c q|) q = |slc sh i k c q| := by
  unfold slc
  split_ifs <;> simp

theorem l1_slc (sh : List ℕ) (i : ℕ) (c : ℕ → ℤ) :
    l1 sh c = ∑ k ∈ range (deg sh i + 1), l1 sh (slc sh i k c) := by
  have h := pv_slc sh i (fun q ↦ |c q|) fun _ ↦ (1 : ℤ)
  simp only [one_pow, one_mul] at h
  rw [← l1_eq_pv] at h
  have h' : ∀ k, pv sh (slc sh i k fun q ↦ |c q|) (fun _ ↦ (1 : ℤ)) = (l1 sh (slc sh i k c) : ℤ) :=
    fun k ↦ by rw [l1_eq_pv]; exact pv_congr (fun q _ ↦ slc_abs sh i k c q) _
  simp only [h'] at h
  exact_mod_cast h

/-- A slot of exponent `0` in `yᵢ`, moved up by `k ≤ eᵢ` strides, has exponent `k`. -/
theorem ex_add_stride {sh : List ℕ} {i q k : ℕ} (h : ex sh i q = 0) (hk : k ≤ deg sh i) :
    ex sh i (q + k * stride sh i) = k := by
  rw [ex] at h ⊢
  rw [Nat.add_mul_div_right _ _ (stride_pos sh i), Nat.add_mod, h, zero_add,
    Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]

theorem ex_lt (sh : List ℕ) (i q : ℕ) : ex sh i q ≤ deg sh i :=
  Nat.lt_succ_iff.mp (Nat.mod_lt _ (Nat.succ_pos _))

/-! ### Substitution -/

/-- The coefficients of `∑_k w_k (a + b yᵢ)^k pv sh (slc sh i k c) y` (`pv_sub`). -/
def sub (sh : List ℕ) (i : ℕ) (w : ℕ → ℤ) (a b : ℤ) (c : ℕ → ℤ) (q : ℕ) : ℤ :=
  ∑ k ∈ Ico (ex sh i q) (deg sh i + 1), w k * ((k.choose (ex sh i q) : ℕ) : ℤ) *
    a ^ (k - ex sh i q) * b ^ ex sh i q * c (q + (k - ex sh i q) * stride sh i)

theorem slc_sub (sh : List ℕ) (i : ℕ) (w : ℕ → ℤ) (a b : ℤ) (c : ℕ → ℤ) {j : ℕ}
    (hj : j ≤ deg sh i) (q : ℕ) :
    slc sh i j (sub sh i w a b c) q = ∑ k ∈ Ico j (deg sh i + 1),
      w k * ((k.choose j : ℕ) : ℤ) * a ^ (k - j) * b ^ j * slc sh i k c q := by
  unfold slc
  split_ifs with h
  · rw [sub, ex_add_stride h hj]
    refine sum_congr rfl fun k hk ↦ ?_
    have hjk := (mem_Ico.mp hk).1
    rw [add_assoc, ← add_mul, Nat.add_sub_cancel' hjk]
  · simp

/-- **The meaning of substitution.** -/
theorem pv_sub {R : Type*} [CommRing R] (sh : List ℕ) (i : ℕ) (w : ℕ → ℤ) (a b : ℤ)
    (c : ℕ → ℤ) (y : ℕ → R) :
    pv sh (sub sh i w a b c) y =
      ∑ k ∈ range (deg sh i + 1), (w k : R) * (a + b * y i) ^ k * pv sh (slc sh i k c) y := by
  rw [pv_slc sh i (sub sh i w a b c) y]
  have h₁ : ∀ j ∈ range (deg sh i + 1), y i ^ j * pv sh (slc sh i j (sub sh i w a b c)) y =
      ∑ k ∈ Ico j (deg sh i + 1), y i ^ j * ((w k * ((k.choose j : ℕ) : ℤ) * a ^ (k - j) *
        b ^ j : ℤ) : R) * pv sh (slc sh i k c) y := by
    intro j hj
    rw [pv_congr (fun q _ ↦ slc_sub sh i w a b c (Nat.lt_succ_iff.mp (mem_range.mp hj)) q),
      pv_sum, mul_sum]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [pv_smul (c := slc sh i k c)]
    ring
  refine (sum_congr rfl h₁).trans ?_
  rw [range_eq_Ico, sum_Ico_Ico_comm]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [Nat.Ico_zero_eq_range, add_comm (a : R), add_pow, mul_sum, sum_mul]
  refine sum_congr rfl fun j _ ↦ ?_
  push_cast
  ring

theorem natAbs_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    (∑ k ∈ s, f k).natAbs ≤ ∑ k ∈ s, (f k).natAbs := by
  have : |∑ k ∈ s, f k| ≤ ∑ k ∈ s, |f k| := abs_sum_le_sum_abs _ _
  have h' : ((∑ k ∈ s, f k).natAbs : ℤ) ≤ ((∑ k ∈ s, (f k).natAbs : ℕ) : ℤ) := by
    push_cast
    simpa [Int.natCast_natAbs] using this
  exact_mod_cast h'

/-- **The absolute coefficient sum after substitution**, if `|w_k| (|a| + |b|)^k ≤ W` for every
`k ≤ eᵢ`. -/
theorem l1_sub_le (sh : List ℕ) (i : ℕ) (w : ℕ → ℤ) (a b : ℤ) (c : ℕ → ℤ) {W : ℕ}
    (hW : ∀ k ≤ deg sh i, (w k).natAbs * (a.natAbs + b.natAbs) ^ k ≤ W) :
    l1 sh (sub sh i w a b c) ≤ W * l1 sh c := by
  rw [l1_slc sh i (sub sh i w a b c), l1_slc sh i c, mul_sum]
  have h₁ : ∀ j ∈ range (deg sh i + 1), l1 sh (slc sh i j (sub sh i w a b c)) ≤
      ∑ k ∈ Ico j (deg sh i + 1), (w k).natAbs * k.choose j * a.natAbs ^ (k - j) *
        b.natAbs ^ j * l1 sh (slc sh i k c) := by
    intro j hj
    rw [l1_congr (fun q _ ↦ slc_sub sh i w a b c (Nat.lt_succ_iff.mp (mem_range.mp hj)) q)]
    unfold l1
    calc ∑ q ∈ range (slots sh), (∑ k ∈ Ico j (deg sh i + 1),
          w k * ((k.choose j : ℕ) : ℤ) * a ^ (k - j) * b ^ j * slc sh i k c q).natAbs
        ≤ ∑ q ∈ range (slots sh), ∑ k ∈ Ico j (deg sh i + 1), (w k).natAbs * k.choose j *
            a.natAbs ^ (k - j) * b.natAbs ^ j * (slc sh i k c q).natAbs :=
          sum_le_sum fun q _ ↦ (natAbs_sum_le _ _).trans (le_of_eq (sum_congr rfl fun k _ ↦ by
            simp [Int.natAbs_mul, Int.natAbs_pow]))
      _ = _ := by
          rw [sum_comm]
          refine sum_congr rfl fun k _ ↦ ?_
          rw [mul_sum]
  refine (sum_le_sum h₁).trans ?_
  rw [range_eq_Ico, sum_Ico_Ico_comm]
  refine sum_le_sum fun k hk ↦ ?_
  have hk' : k ≤ deg sh i := Nat.lt_succ_iff.mp (mem_Ico.mp hk).2
  calc ∑ j ∈ Ico 0 (k + 1), (w k).natAbs * k.choose j * a.natAbs ^ (k - j) * b.natAbs ^ j *
        l1 sh (slc sh i k c)
      = (w k).natAbs * (a.natAbs + b.natAbs) ^ k * l1 sh (slc sh i k c) := by
        rw [add_comm a.natAbs, add_pow, mul_sum, sum_mul, ← Nat.Ico_zero_eq_range]
        refine sum_congr rfl fun j _ ↦ ?_
        simp only [Nat.cast_id]
        ring
    _ ≤ W * l1 sh (slc sh i k c) := Nat.mul_le_mul_right _ (hW k hk')

/-- Substitution at a point: if `Σ_k w_k (a + b z)^k Sₖ = λ Σ_k z'^k Sₖ`, i.e. for weights
`w_k = t^(e - k)` and `a + b z = t z'`. -/
theorem pv_update {R : Type*} [CommRing R] (sh : List ℕ) (i : ℕ) (c : ℕ → ℤ) (y : ℕ → R)
    (z : R) : pv sh c (Function.update y i z) =
      ∑ k ∈ range (deg sh i + 1), z ^ k * pv sh (slc sh i k c) y := by
  rw [pv_slc sh i c (Function.update y i z), Function.update_self]
  refine sum_congr rfl fun k _ ↦ ?_
  congr 1
  refine sum_congr rfl fun q _ ↦ ?_
  unfold slc
  split_ifs with h
  · congr 1
    refine prod_congr rfl fun j _ ↦ ?_
    by_cases hj : j = i
    · subst hj; rw [h, pow_zero, pow_zero]
    · rw [Function.update_of_ne hj]
  · simp

/-! ### Product indicators -/

/-- `∑_{j < m} [T₀ (k + j)] inner 2^(P (k + j))`, by shifts. -/
def indRep (inner P : ℕ) (T0 : ℕ → Bool) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | k, m + 1 => (bif T0 k then inner <<< (P * k) else 0) + indRep inner P T0 (k + 1) m

/-- The numeral with the digit `1` in the slots `q` of `sh` whose exponents satisfy `T` variable
by variable (`ind_eq`), and `0` elsewhere. -/
def ind (B : ℕ) : List ℕ → (ℕ → ℕ → Bool) → ℕ
  | [], _ => 1
  | e :: t, T => indRep (ind B t fun i ↦ T (i + 1)) (B * slots t) (T 0) 0 (e + 1)

/-- Every variable's exponent in slot `q` satisfies `T`. -/
def AllT (sh : List ℕ) (T : ℕ → ℕ → Bool) (q : ℕ) : Prop := ∀ i < sh.length, T i (ex sh i q) = true

instance (sh : List ℕ) (T : ℕ → ℕ → Bool) : DecidablePred (AllT sh T) :=
  fun q ↦ inferInstanceAs (Decidable (∀ i < sh.length, T i (ex sh i q) = true))

theorem indRep_eq (inner P : ℕ) (T0 : ℕ → Bool) : ∀ k m : ℕ,
    indRep inner P T0 k m = ∑ j ∈ range m, if T0 (k + j) then inner * 2 ^ (P * (k + j)) else 0
  | k, 0 => by simp [indRep]
  | k, m + 1 => by
    rw [indRep, indRep_eq inner P T0 (k + 1) m, sum_range_succ']
    simp only [add_zero, Nat.shiftLeft_eq, cond_eq_ite]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun j _ ↦ ?_
    rw [show k + 1 + j = k + (j + 1) by ring]

/-- A numeral over the slots of `m` blocks of `S` slots, block by block. -/
theorem num_mul_split (B : ℕ) (a : ℕ → ℕ) (S m : ℕ) :
    num B a (m * S) = ∑ k ∈ range m, num B (fun r ↦ a (k * S + r)) S * 2 ^ (B * (k * S)) := by
  rw [num, sum_range_mul]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [num, sum_mul]
  refine sum_congr rfl fun r _ ↦ ?_
  rw [mul_assoc, ← pow_add]
  ring_nf

theorem allT_cons {e : ℕ} {t : List ℕ} {T : ℕ → ℕ → Bool} {k r : ℕ} (hk : k ≤ e)
    (hr : r < slots t) :
    AllT (e :: t) T (k * slots t + r) ↔ T 0 k = true ∧ AllT t (fun i ↦ T (i + 1)) r := by
  unfold AllT
  rw [List.length_cons]
  constructor
  · intro h
    refine ⟨by simpa [ex_cons_zero hk hr] using h 0 (by omega), fun i hi ↦ ?_⟩
    simpa [ex_cons_succ k i hr] using h (i + 1) (by omega)
  · rintro ⟨h₀, h⟩ i hi
    cases i with
    | zero => simpa [ex_cons_zero hk hr] using h₀
    | succ i => simpa [ex_cons_succ k i hr] using h i (by omega)

/-- **The digits of product indicators.** -/
theorem ind_eq (B : ℕ) : ∀ (sh : List ℕ) (T : ℕ → ℕ → Bool),
    ind B sh T = num B (fun q ↦ if AllT sh T q then 1 else 0) (slots sh)
  | [], T => by simp [ind, num, slots, AllT]
  | e :: t, T => by
    rw [ind, indRep_eq, ind_eq B t, slots, num_mul_split]
    refine sum_congr rfl fun k hk ↦ ?_
    have hk' := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [zero_add, show B * slots t * k = B * (k * slots t) by ring]
    split_ifs with h
    · congr 1
      exact num_congr fun r hr ↦ by simp only [allT_cons hk' hr, h, true_and]
    · rw [num_congr (b := fun _ ↦ 0) fun r hr ↦ by simp [allT_cons hk' hr, h]]
      simp [num]

theorem digits_ind (B : ℕ) (hB : 0 < B) (sh : List ℕ) (T : ℕ → ℕ → Bool) :
    Digits B (fun q ↦ if AllT sh T q then 1 else 0) (slots sh) := fun q _ ↦ by
  dsimp only
  split_ifs
  · exact Nat.one_lt_two_pow (by omega)
  · exact Nat.two_pow_pos B

/-! ### Numerals and coefficient functions -/

/-- The coefficients of the numeral `N`: digit `q` minus the bias `2^(B-1)`. -/
def cf (B N q : ℕ) : ℤ := (dig B N q : ℤ) - 2 ^ (B - 1)

theorem horner_unpackL {α : Type*} {R : Type*} [CommSemiring R] (f : α → R) (g : ℕ → α) (z : R)
    (w : ℕ) : ∀ (m N : ℕ),
    horner f z (DPoly.unpackL g w m N) = ∑ k ∈ range m, z ^ k * f (g (N / 2 ^ (w * k) % 2 ^ w))
  | 0, N => by simp [DPoly.unpackL]
  | m + 1, N => by
    rw [DPoly.unpackL, horner_cons, horner_unpackL f g z w m, sum_range_succ', mul_sum]
    simp only [pow_zero, one_mul, mul_zero, Nat.div_one, add_comm]
    congr 1
    refine sum_congr rfl fun k _ ↦ ?_
    rw [Nat.div_div_eq_div_mul, ← pow_add, pow_succ]
    ring_nf

/-- Digit `r` of block `k` is digit `k S + r`. -/
theorem dig_block {B S r : ℕ} (k N : ℕ) (hr : r < S) :
    dig B (N / 2 ^ (B * S * k) % 2 ^ (B * S)) r = dig B N (k * S + r) := by
  refine Nat.eq_of_testBit_eq fun i ↦ ?_
  simp only [dig, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < B
  · have h₁ : i + B * r < B * S := by
      have : B * (r + 1) ≤ B * S := Nat.mul_le_mul_left B hr
      nlinarith
    simp only [hi, h₁, decide_true, Bool.true_and]
    congr 1
    ring
  · simp [hi]

/-- `pv` by the first variable, also for the empty shape. -/
theorem pv_eq_head {R : Type*} [CommRing R] (sh : List ℕ) (c : ℕ → ℤ) (y : ℕ → R) :
    pv sh c y = ∑ k ∈ range (sh.headD 0 + 1),
      y 0 ^ k * pv sh.tail (fun r ↦ c (k * slots sh.tail + r)) fun i ↦ y (i + 1) := by
  cases sh with
  | nil => simp [pv_nil, slots]
  | cons e t => exact pv_cons c y

theorem l1_eq_head (sh : List ℕ) (c : ℕ → ℤ) :
    l1 sh c = ∑ k ∈ range (sh.headD 0 + 1), l1 sh.tail fun r ↦ c (k * slots sh.tail + r) := by
  cases sh with
  | nil => simp [l1_nil, slots]
  | cons e t => exact l1_cons c

/-- **Unpacking in slot order**: the polynomial `DPoly.unpack` reads off a numeral is `pv` of its
coefficients. -/
theorem eval_unpack_eq_pv {R : Type*} [CommRing R] (B : ℕ) : ∀ (n : ℕ) (sh : List ℕ),
    sh.length ≤ n → ∀ (N : ℕ) (y : ℕ → R),
      DPoly.eval n (DPoly.unpack n sh B N) (fun i : Fin n ↦ y i) = pv sh (cf B N) y
  | 0, sh, hsh, N, y => by
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hsh), pv_nil]
    simp [DPoly.unpack, DPoly.eval, cf, dig]
  | n + 1, sh, hsh, N, y => by
    rw [DPoly.unpack, DPoly.eval_ofList, horner_unpackL, pv_eq_head]
    refine sum_congr rfl fun k _ ↦ ?_
    congr 1
    have ht : sh.tail.length ≤ n := by simp; omega
    rw [show (Fin.tail fun i : Fin (n + 1) ↦ y i) = fun i : Fin n ↦ y (i + 1) from rfl]
    exact (eval_unpack_eq_pv B n sh.tail ht _ fun j ↦ y (j + 1)).trans
      (pv_congr (fun r hr ↦ by rw [cf, cf, dig_block k N hr]) _)

/-- **Absolute sums in slot order.** -/
theorem absEval_unpack_eq_l1 (B : ℕ) : ∀ (n : ℕ) (sh : List ℕ), sh.length ≤ n → ∀ N : ℕ,
    DPoly.absEval n (DPoly.unpack n sh B N) (fun _ ↦ 1) = l1 sh (cf B N)
  | 0, sh, hsh, N => by
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hsh), l1_nil]
    simp [DPoly.unpack, DPoly.absEval, cf, dig]
  | n + 1, sh, hsh, N => by
    rw [DPoly.unpack, DPoly.absEval, DPoly.toList_ofList, horner_unpackL, l1_eq_head]
    refine sum_congr rfl fun k _ ↦ ?_
    have ht : sh.tail.length ≤ n := by simp; omega
    rw [one_pow, one_mul,
      show (Fin.tail fun _ : Fin (n + 1) ↦ (1 : ℕ)) = fun _ : Fin n ↦ 1 from rfl,
      absEval_unpack_eq_l1 B n sh.tail ht]
    exact l1_congr fun r hr ↦ by rw [cf, cf, dig_block k N hr]

/-! ### Slices of numerals -/

/-- Exponent `0` in variable `i`, any exponent elsewhere. -/
def zeroAt (i j x : ℕ) : Bool := !(j == i) || x == 0

theorem allT_zeroAt {sh : List ℕ} {i q : ℕ} : AllT sh (zeroAt i) q ↔ ex sh i q = 0 := by
  unfold AllT zeroAt
  constructor
  · intro h
    by_cases hi : i < sh.length
    · simpa using h i hi
    · exact ex_of_le (by omega) q
  · intro h j _
    by_cases hj : j = i
    · subst hj; simp [h]
    · simp [hj]

theorem allT_true {sh : List ℕ} {q : ℕ} : AllT sh (fun _ _ ↦ true) q := fun _ _ ↦ rfl

/-- **Slices of a numeral**: the digits of `yᵢ^k`, by one shift and one mask. -/
theorem slice_eq {B : ℕ} (hB : 0 < B) {sh : List ℕ} {N : ℕ} (hN : N < 2 ^ (B * slots sh))
    (i k : ℕ) :
    (N >>> (B * (k * stride sh i))) &&& ((2 ^ B - 1) * ind B sh (zeroAt i)) =
      num B (fun q ↦ if ex sh i q = 0 then dig B N (q + k * stride sh i) else 0) (slots sh) := by
  rw [ind_eq, num_mul]
  conv_lhs => rw [← num_dig hB hN]
  rw [num_shiftRight hB (digits_dig B N _),
    num_land hB (fun p hp ↦ by split_ifs <;> simp [dig_lt])
      (fun p hp ↦ by split_ifs <;> simp)]
  refine num_congr fun q hq ↦ ?_
  simp only [allT_zeroAt]
  split_ifs with h₁ h₂ h₂
  · rw [mul_one]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (dig_lt B N _)
  · simp
  · rw [dig_eq_zero hN (by omega)]
    simp
  · simp

/-- The signed slice: the packed value of the coefficients of `yᵢ^k`. -/
theorem slice_signed {B : ℕ} (hB : 0 < B) {sh : List ℕ} {N : ℕ} (hN : N < 2 ^ (B * slots sh))
    (i k : ℕ) :
    (((N >>> (B * (k * stride sh i))) &&& ((2 ^ B - 1) * ind B sh (zeroAt i)) : ℕ) : ℤ) -
      ((2 ^ (B - 1) * ind B sh (zeroAt i) : ℕ) : ℤ) =
        snum B (slc sh i k (cf B N)) (slots sh) := by
  rw [slice_eq hB hN, ind_eq, num_mul, snum_natCast, snum_natCast, snum_sub]
  refine snum_congr fun q _ ↦ ?_
  simp only [allT_zeroAt, slc, cf]
  split_ifs <;> push_cast <;> ring

/-! ### Substitution in numerals -/

/-- Shift left of an integer. -/
def shl (x : ℤ) (P : ℕ) : ℤ :=
  match x with
  | .ofNat m => .ofNat (m <<< P)
  | .negSucc m => -(.ofNat ((m + 1) <<< P))

theorem shl_eq (x : ℤ) (P : ℕ) : shl x P = x * 2 ^ P := by
  cases x with
  | ofNat m => simp [shl, Nat.shiftLeft_eq]
  | negSucc m =>
    simp only [shl, Nat.shiftLeft_eq, Int.ofNat_eq_natCast, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, Int.negSucc_eq]
    push_cast
    ring

/-- `∑_{j < m} w (k + j) (a + b 2^P)^j S (k + j)` by Horner's scheme, multiplying by `2^P` by
shifts. -/
def hsub (P : ℕ) (a b : ℤ) (w S : ℕ → ℤ) : ℕ → ℕ → ℤ
  | _, 0 => 0
  | k, m + 1 =>
    let acc := hsub P a b w S (k + 1) m
    w k * S k + (a * acc + shl (b * acc) P)

theorem hsub_succ (P : ℕ) (a b : ℤ) (w S : ℕ → ℤ) (k m : ℕ) :
    hsub P a b w S k (m + 1) = w k * S k + (a + b * 2 ^ P) * hsub P a b w S (k + 1) m := by
  simp only [hsub, shl_eq]
  ring

theorem hsub_eq (P : ℕ) (a b : ℤ) (w S : ℕ → ℤ) : ∀ k m : ℕ,
    hsub P a b w S k m = ∑ j ∈ range m, w (k + j) * (a + b * 2 ^ P) ^ j * S (k + j)
  | k, 0 => by simp [hsub]
  | k, m + 1 => by
    rw [hsub_succ, hsub_eq P a b w S (k + 1) m, sum_range_succ', mul_sum]
    simp only [add_zero, pow_zero, mul_one]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun j _ ↦ ?_
    rw [show k + 1 + j = k + (j + 1) by ring, pow_succ]
    ring

/-- The offset: the bias `2^(B-1)` in every slot. -/
def offN (B : ℕ) (sh : List ℕ) : ℕ := 2 ^ (B - 1) * ind B sh fun _ _ ↦ true

/-- `offN` by a shift. -/
def offNS (B : ℕ) (sh : List ℕ) : ℕ := (ind B sh fun _ _ ↦ true) <<< (B - 1)

@[csimp] theorem offN_eq_offNS : @offN = @offNS := by
  funext B sh
  rw [offN, offNS, two_pow_mul_eq_shiftLeft]

theorem offN_eq (B : ℕ) (sh : List ℕ) : offN B sh = num B (fun _ ↦ 2 ^ (B - 1)) (slots sh) := by
  rw [offN, ind_eq, num_mul]
  exact num_congr fun q _ ↦ by simp [allT_true]

/-- **Substitution in a numeral**: the numeral of `∑_k w_k (a + b yᵢ)^k Sₖ`, where `Sₖ` are the
slices of `N` (`subN_spec`). -/
def subN (B : ℕ) (sh : List ℕ) (i : ℕ) (w : ℕ → ℤ) (a b : ℤ) (N : ℕ) : ℕ :=
  let s := stride sh i
  let I := ind B sh (zeroAt i)
  let M := (2 ^ B - 1) * I
  let hI : ℤ := ((2 ^ (B - 1) * I : ℕ) : ℤ)
  (hsub (B * s) a b w (fun k ↦ (((N >>> (B * (k * s))) &&& M : ℕ) : ℤ) - hI) 0 (deg sh i + 1) +
    (offN B sh : ℤ)).toNat

/-- `subN` with the masks by shifts. -/
def subNS (B : ℕ) (sh : List ℕ) (i : ℕ) (w : ℕ → ℤ) (a b : ℤ) (N : ℕ) : ℕ :=
  let s := stride sh i
  let I := ind B sh (zeroAt i)
  let M := (I <<< B) - I
  let hI : ℤ := ((I <<< (B - 1) : ℕ) : ℤ)
  (hsub (B * s) a b w (fun k ↦ (((N >>> (B * (k * s))) &&& M : ℕ) : ℤ) - hI) 0 (deg sh i + 1) +
    (offN B sh : ℤ)).toNat

@[csimp] theorem subN_eq_subNS : @subN = @subNS := by
  funext B sh i w a b N
  simp only [subN, subNS, two_pow_sub_one_mul_eq, two_pow_mul_eq_shiftLeft]

/-- **Soundness of substitution in numerals.** If `N` has `slots sh` digits and the bound
`W ≥ |w_k| (|a| + |b|)^k` keeps `W` times the absolute coefficient sum below the bias, the
result has `slots sh` digits and its coefficients are those of `sub`. -/
theorem subN_spec {B : ℕ} (hB : 0 < B) {sh : List ℕ} {N : ℕ} (hN : N < 2 ^ (B * slots sh))
    (i : ℕ) (w : ℕ → ℤ) (a b : ℤ) {W : ℕ}
    (hW : ∀ k ≤ deg sh i, (w k).natAbs * (a.natAbs + b.natAbs) ^ k ≤ W)
    (hl : W * l1 sh (cf B N) < 2 ^ (B - 1)) :
    subN B sh i w a b N < 2 ^ (B * slots sh) ∧
      ∀ q < slots sh, cf B (subN B sh i w a b N) q = sub sh i w a b (cf B N) q := by
  set r := sub sh i w a b (cf B N)
  have hr : l1 sh r < 2 ^ (B - 1) := (l1_sub_le sh i w a b (cf B N) hW).trans_lt hl
  have hrq : ∀ q < slots sh, -2 ^ (B - 1) ≤ r q ∧ r q < 2 ^ (B - 1) := by
    intro q hq
    have h₁ := (abs_coeff_le_l1 r hq).trans_lt hr
    have h₂ : |r q| < 2 ^ (B - 1) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast h₁
    constructor <;> linarith [abs_lt.mp h₂]
  obtain ⟨hbias, hdig⟩ := snum_add_bias hB hrq
  have hval : hsub (B * stride sh i) a b w (fun k ↦ (((N >>> (B * (k * stride sh i))) &&&
      ((2 ^ B - 1) * ind B sh (zeroAt i)) : ℕ) : ℤ) -
        ((2 ^ (B - 1) * ind B sh (zeroAt i) : ℕ) : ℤ)) 0 (deg sh i + 1) = snum B r (slots sh) := by
    rw [hsub_eq]
    simp only [zero_add, slice_signed hB hN]
    rw [← pv_pack, pv_sub]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [pv_pack, packY]
    simp only [Int.cast_id]
  have heq : subN B sh i w a b N = num B (fun q ↦ (r q + 2 ^ (B - 1)).toNat) (slots sh) := by
    simp only [subN]
    rw [hval, offN_eq, hbias, Int.toNat_natCast]
  refine ⟨heq ▸ num_lt hdig, fun q hq ↦ ?_⟩
  rw [heq, cf, dig_num hB hdig hq, Int.toNat_of_nonneg (by linarith [(hrq q hq).1])]
  ring

end Lay

end Nieuwland.Check
