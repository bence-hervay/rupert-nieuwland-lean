import Modules.Check.Sign.Engine

/-!
# Exact division by linear factors

Rust's chart-tree checker certifies a weak sign `p ≥ 0` on a node box for the quotient of `p` by
its largest monomial in the signed slots (`Node::divided` in `code/src/proof/tree.rs`), and it
divides every tuple's combination sum once more (`weak_nonneg`). A sum that vanishes on a face of
the box, such as a blow-up radius at `0`, has no certificate by centred bounds; its quotient may
have one.

The packed engine does the same here. A coordinate `xᵢ = (cᵢ + hᵢ yᵢ) / D` of a box with
`|hᵢ| ≤ |cᵢ|` has the linear factor `a + b yᵢ` (`cᵢ + hᵢ yᵢ` over `gcd(cᵢ, hᵢ)`, with the sign of
`cᵢ`; `|b| ≤ a`), which is nonnegative on the cube. So `p ≥ 0` follows from `t ≥ 0` where
`p = (a + b yᵢ) t`. One division of a numeral `N` with the coefficients of `p` (`divN`, sound by
`divN_spec`):

1. divides the packed value `v = p(Y)` by `f = a + b Yᵢ` at the packing point
   `Yᵢ = 2^(B strideᵢ)`; one big-integer remainder decides most failures;
2. reads the quotient's digits with the bias `2^e` and checks them by one mask (`divMask`): the
   digits of degree `deg i` in `yᵢ` are `0`, and the others have no bit from `e + 1` on, so the
   quotient `t` has coefficients in `[-2^e, 2^e)`;
3. then `(a + b yᵢ) t` (`mulL`, `pv_mulL`) has coefficients below `2^(B-1)` in absolute value, as
   `p` has, and both have the packed value `v`; so they are equal (`snum_inj`), and
   `p = (a + b yᵢ) t` as polynomials.

The bounds `(|a| + |b|) 2^e < 2^(B-1)` and `slots 2^e < 2^(B-1)` make the quotient a numeral of
the engine (`Inv`). `runDiv` (sound by `runDiv_sound`) is the engine for weak signs with this
division: if the box test of the numerals fails and some division by the factors `fs` is exact,
it runs the engine on the quotients, each factor divided out as often as the division is exact
(`divAll`); it then falls back to bisecting the undivided numerals (`split`), so it certifies
everything `run` certifies.
-/

open Finset

namespace Nieuwland.Check

namespace Lay

open DPoly Num

/-! ### Products with a linear factor -/

/-- The coefficients of `(a + b yᵢ) p` for the coefficients `c` of `p`: `a c q`, plus `b` times
the coefficient one power of `yᵢ` lower (`pv_mulL`, where `p` has no term of degree `deg i` in
`yᵢ`). -/
def mulL (sh : List ℕ) (i : ℕ) (a b : ℤ) (c : ℕ → ℤ) (q : ℕ) : ℤ :=
  a * c q + if ex sh i q = 0 then 0 else b * c (q - stride sh i)

/-- A slot of exponent `0` in `yᵢ`, moved up by `k ≤ deg i` strides, is still a slot. -/
theorem add_stride_lt {sh : List ℕ} {i q k : ℕ} (hq : q < slots sh) (h0 : ex sh i q = 0)
    (hk : k ≤ deg sh i) : q + k * stride sh i < slots sh := by
  obtain ⟨m, hm⟩ := stride_mul_dvd sh i
  have hs := stride_pos sh i
  set s := stride sh i
  set e := deg sh i
  have hu : q / s % (e + 1) = 0 := h0
  obtain ⟨w, hw⟩ : (e + 1) ∣ q / s := Nat.dvd_of_mod_eq_zero hu
  have hq' : s * (q / s) + q % s = q := Nat.div_add_mod q s
  have hr := Nat.mod_lt q hs
  rw [hw] at hq'
  have hwm : w + 1 ≤ m := by
    by_contra hc
    have h₁ : m ≤ w := by omega
    have : s * (e + 1) * m ≤ s * ((e + 1) * w) := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left s (Nat.mul_le_mul_left (e + 1) h₁)
    omega
  have h₂ : s * ((e + 1) * w) + k * s + q % s < s * ((e + 1) * (w + 1)) := by
    have : k * s + q % s < (e + 1) * s := by
      have : k * s + s ≤ (e + 1) * s := by
        have := Nat.mul_le_mul_right s hk
        rw [Nat.add_mul, one_mul]
        omega
      omega
    nlinarith
  have h₃ : s * ((e + 1) * (w + 1)) ≤ s * (e + 1) * m := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left s (Nat.mul_le_mul_left (e + 1) hwm)
  omega

theorem slc_mulL (sh : List ℕ) (i : ℕ) (a b : ℤ) (c : ℕ → ℤ) {k : ℕ} (hk : k ≤ deg sh i)
    (q : ℕ) : slc sh i k (mulL sh i a b c) q =
      a * slc sh i k c q + if k = 0 then 0 else b * slc sh i (k - 1) c q := by
  unfold slc mulL
  by_cases h₀ : ex sh i q = 0
  · simp only [h₀, ↓reduceIte, ex_add_stride h₀ hk]
    by_cases h₁ : k = 0
    · simp [h₁]
    · simp only [h₁, ↓reduceIte]
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [Nat.add_sub_cancel, Nat.add_mul, one_mul,
        show q + (k * stride sh i + stride sh i) - stride sh i = q + k * stride sh i by omega]
  · simp [h₀]

/-- **The meaning of `mulL`**: if `p` has no term of degree `deg i` in `yᵢ`, then `mulL` has the
coefficients of `(a + b yᵢ) p`. -/
theorem pv_mulL {R : Type*} [CommRing R] (sh : List ℕ) (i : ℕ) (a b : ℤ) {c : ℕ → ℤ}
    (htop : ∀ q < slots sh, ex sh i q = deg sh i → c q = 0) (y : ℕ → R) :
    pv sh (mulL sh i a b c) y = (a + b * y i) * pv sh c y := by
  set e := deg sh i
  set T : ℕ → R := fun k ↦ y i ^ k * pv sh (slc sh i k c) y
  have hT : T e = 0 := by
    have : pv sh (slc sh i e c) y = 0 := by
      rw [pv_congr (d := fun _ ↦ 0) (fun q hq ↦ ?_), pv_zero]
      unfold slc
      split_ifs with h
      · exact htop _ (add_stride_lt hq h le_rfl) (ex_add_stride h le_rfl)
      · rfl
    simp [T, this]
  have h₁ : ∀ k ∈ range (e + 1), y i ^ k * pv sh (slc sh i k (mulL sh i a b c)) y =
      a * T k + if k = 0 then 0 else b * y i * T (k - 1) := by
    intro k hk
    have hk' := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [pv_congr (fun q _ ↦ slc_mulL sh i a b c hk' q)]
    split_ifs with h0
    · subst h0
      simp only [add_zero, pv_smul (c := slc sh i 0 c), T]
      ring
    · rw [pv_add, pv_smul (c := slc sh i k c), pv_smul (c := slc sh i (k - 1) c)]
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [T, Nat.add_sub_cancel, pow_succ]
      ring
  rw [pv_slc sh i (mulL sh i a b c) y, pv_slc sh i c y, sum_congr rfl h₁, sum_add_distrib,
    ← mul_sum, sum_range_succ' (fun k ↦ if k = 0 then (0 : R) else b * y i * T (k - 1))]
  simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, ↓reduceIte, add_zero]
  rw [← mul_sum]
  have hs : ∑ k ∈ range e, T k = ∑ k ∈ range (e + 1), T k := by
    rw [sum_range_succ, hT, add_zero]
  rw [hs]
  ring

theorem natAbs_mulL_le (sh : List ℕ) (i : ℕ) (a b : ℤ) {c : ℕ → ℤ} {L M : ℕ}
    (hc : ∀ q < L, (c q).natAbs ≤ M) {q : ℕ} (hq : q < L) :
    (mulL sh i a b c q).natAbs ≤ (a.natAbs + b.natAbs) * M := by
  unfold mulL
  have h₁ : (a * c q).natAbs ≤ a.natAbs * M := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul_left _ (hc q hq)
  split_ifs
  · rw [add_zero, Nat.add_mul]
    exact h₁.trans (Nat.le_add_right _ _)
  · have h₂ : (b * c (q - stride sh i)).natAbs ≤ b.natAbs * M := by
      rw [Int.natAbs_mul]; exact Nat.mul_le_mul_left _ (hc _ (by omega))
    rw [Nat.add_mul]
    exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add h₁ h₂)

/-! ### Small coefficients are determined by the packed value -/

/-- **Injectivity of packing**: integer digits in `[-2^(B-1), 2^(B-1))` are determined by their
signed numeral. -/
theorem snum_inj {B L : ℕ} (hB : 0 < B) {c d : ℕ → ℤ}
    (hc : ∀ p < L, -2 ^ (B - 1) ≤ c p ∧ c p < 2 ^ (B - 1))
    (hd : ∀ p < L, -2 ^ (B - 1) ≤ d p ∧ d p < 2 ^ (B - 1))
    (h : snum B c L = snum B d L) {p : ℕ} (hp : p < L) : c p = d p := by
  obtain ⟨hc₁, hc₂⟩ := snum_add_bias hB hc
  obtain ⟨hd₁, hd₂⟩ := snum_add_bias hB hd
  have hn : num B (fun p ↦ (c p + 2 ^ (B - 1)).toNat) L =
      num B (fun p ↦ (d p + 2 ^ (B - 1)).toNat) L := by
    have := hc₁.symm.trans (h ▸ hd₁)
    exact_mod_cast this
  have h' := congrArg (fun N ↦ dig B N p) hn
  simp only [dig_num hB hc₂ hp, dig_num hB hd₂ hp] at h'
  have h₁ := (hc p hp).1
  have h₂ := (hd p hp).1
  have h₃ : (0 : ℤ) ≤ 2 ^ (B - 1) := by positivity
  omega

theorem cf_bounds {B : ℕ} (hB : 0 < B) (N q : ℕ) :
    -2 ^ (B - 1) ≤ cf B N q ∧ cf B N q < 2 ^ (B - 1) := by
  have h2 : (2 : ℤ) ^ B = 2 * 2 ^ (B - 1) := by rw [← pow_succ']; congr 1; omega
  have := dig_lt B N q
  have : ((dig B N q : ℕ) : ℤ) < 2 ^ B := by exact_mod_cast this
  unfold cf
  constructor <;> omega

/-! ### Masks of divisions -/

/-- Exponent `e` in variable `i`, any exponent elsewhere. -/
def topAt (i e j x : ℕ) : Bool := !(j == i) || x == e

theorem allT_topAt {sh : List ℕ} {i q : ℕ} :
    AllT sh (topAt i (deg sh i)) q ↔ ex sh i q = deg sh i := by
  unfold AllT topAt
  constructor
  · intro h
    by_cases hi : i < sh.length
    · simpa using h i hi
    · rw [ex_of_le (by omega), deg_of_le (by omega)]
  · intro h j _
    by_cases hj : j = i
    · subst hj; simp [h]
    · simp [hj]

/-- The mask of a division along `i` for quotient digits below `2^(e+1)` with the bias `2^e`: all
bits of the digits of degree `deg i` in `yᵢ` (which must be the bias), the bits from `e + 1` on
of the others (which must be `0`). -/
def divMask (B : ℕ) (sh : List ℕ) (i e : ℕ) : ℕ :=
  (2 ^ B - 2 ^ (e + 1)) * onesN B sh + (2 ^ (e + 1) - 1) * ind B sh (topAt i (deg sh i))

/-- A digit with no bit from `k` to `B` is below `2^k`. -/
theorem lt_of_and_eq_zero {B k d : ℕ} (hd : d < 2 ^ B) (h : d &&& (2 ^ B - 2 ^ k) = 0) :
    d < 2 ^ k := by
  refine Nat.lt_pow_two_of_testBit d fun j hj ↦ ?_
  by_cases hjB : j < B
  · have hm : (2 ^ B - 2 ^ k).testBit j = true := by
      have hkB : k ≤ B := by omega
      have : 2 ^ B - 2 ^ k = 2 ^ k * (2 ^ (B - k) - 1) := by
        rw [Nat.mul_sub, ← pow_add, Nat.add_sub_cancel' hkB, mul_one]
      rw [this, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one]
      simp only [ge_iff_le, hj, decide_true, Bool.true_and, decide_eq_true_eq]
      omega
    have := congrArg (·.testBit j) h
    simp only [Nat.testBit_and, hm, Bool.and_true, Nat.zero_testBit] at this
    exact this
  · exact Nat.testBit_lt_two_pow (hd.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-- The mask as a numeral. -/
theorem divMask_eq (B : ℕ) (sh : List ℕ) (i e : ℕ) :
    divMask B sh i e = num B (fun q ↦ (2 ^ B - 2 ^ (e + 1)) * 1 +
      (2 ^ (e + 1) - 1) * if ex sh i q = deg sh i then 1 else 0) (slots sh) := by
  rw [divMask, onesN_eq, ind_eq, num_mul, num_mul, num_add]
  exact num_congr fun q _ ↦ by simp only [allT_topAt]

/-! ### Exact division of a numeral -/

/-- **Exact division of a numeral by `a + b yᵢ`** (`divN_spec`), with the quotient's coefficients
in `[-2^e, 2^e)` and the bias numeral `O = offN B sh`: the packed value `v = N - O` divided by
`a + b Yᵢ` at the packing point, if the remainder is `0`, the quotient's digits with the bias
`2^e` pass the mask `divMask` and fit the slots; then the numeral of the quotient. -/
def divN (B : ℕ) (sh : List ℕ) (i : ℕ) (a b : ℤ) (e O N : ℕ) : Option ℕ :=
  let v : ℤ := (N : ℤ) - O
  let f : ℤ := a + b * 2 ^ (B * stride sh i)
  bif v % f != 0 then none
  else
    let X : ℤ := v / f + ((onesN B sh * 2 ^ e : ℕ) : ℤ)
    bif decide (X < 0) || X.toNat >>> (B * slots sh) != 0 ||
        X.toNat &&& divMask B sh i e != ind B sh (topAt i (deg sh i)) * 2 ^ e then none
    else some (v / f + O).toNat

/-- **Soundness of the division of a numeral**: the quotient is a numeral of the engine, and the
polynomial of `N` is `a + b yᵢ` times the quotient's. -/
theorem divN_spec {B : ℕ} (hB : 0 < B) {sh : List ℕ} {i : ℕ} {a b : ℤ} {e N N' : ℕ}
    (he₁ : (a.natAbs + b.natAbs) * 2 ^ e < 2 ^ (B - 1)) (he₂ : slots sh * 2 ^ e < 2 ^ (B - 1))
    (hN : N < 2 ^ (B * slots sh)) (h : divN B sh i a b e (offN B sh) N = some N') :
    Inv B sh N' ∧ ∀ y : ℕ → ℝ, pv sh (cf B N) y = (a + b * y i) * pv sh (cf B N') y := by
  simp only [divN, Bool.cond_eq_ite, bne_iff_ne, ne_eq, Bool.or_eq_true,
    decide_eq_true_eq] at h
  split_ifs at h with h₁ h₂
  rw [Option.some.injEq] at h
  rw [not_or, not_or, not_lt, not_not, not_not] at h₂
  obtain ⟨⟨hX0, hXs⟩, hXm⟩ := h₂
  set L := slots sh
  set v : ℤ := (N : ℤ) - offN B sh
  set f : ℤ := a + b * 2 ^ (B * stride sh i)
  set X : ℤ := v / f + ((onesN B sh * 2 ^ e : ℕ) : ℤ) with hXdef
  have hr : v % f = 0 := h₁
  -- The digit bounds.
  have hL : 1 ≤ L := one_le_slots sh
  have heB : 2 ^ e < 2 ^ (B - 1) := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hL) he₂
  have heB' : e + 1 ≤ B - 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp heB
  have hpe : 2 ^ (e + 1) ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) (by omega)
  set Xn := X.toNat
  have hXlt : Xn < 2 ^ (B * L) := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] at hXs
    rcases hXs with h0 | h0
    · exact absurd h0 (Nat.two_pow_pos _).ne'
    · exact h0
  have hdig : ∀ q < L, dig B Xn q < 2 ^ (e + 1) ∧ (ex sh i q = deg sh i → dig B Xn q = 2 ^ e) := by
    have hm : Digits B (fun q ↦ (2 ^ B - 2 ^ (e + 1)) * 1 +
        (2 ^ (e + 1) - 1) * if ex sh i q = deg sh i then 1 else 0) L := fun q _ ↦ by
      have := Nat.one_le_two_pow (n := e + 1)
      dsimp only
      split_ifs <;> omega
    have ht : Digits B (fun q ↦ (if ex sh i q = deg sh i then 1 else 0) * 2 ^ e) L := fun q _ ↦ by
      have : 2 ^ e < 2 ^ B := heB.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
      have := Nat.two_pow_pos B
      dsimp only
      split_ifs <;> omega
    have hR : ind B sh (topAt i (deg sh i)) * 2 ^ e =
        num B (fun q ↦ (if ex sh i q = deg sh i then 1 else 0) * 2 ^ e) L := by
      rw [ind_eq, Nat.mul_comm, num_mul]
      exact num_congr fun q _ ↦ by simp only [allT_topAt]; split_ifs <;> simp
    rw [divMask_eq, ← num_dig hB hXlt, num_land hB (digits_dig B Xn L) hm, hR] at hXm
    intro q hq
    have hq' := congrArg (fun N ↦ dig B N q) hXm
    rw [dig_num hB (fun p hp ↦ Nat.and_lt_two_pow _ (hm p hp)) hq, dig_num hB ht hq] at hq'
    have hd := dig_lt B Xn q
    by_cases htop : ex sh i q = deg sh i
    · simp only [htop, ↓reduceIte, mul_one, one_mul] at hq'
      have : 2 ^ B - 2 ^ (e + 1) + (2 ^ (e + 1) - 1) = 2 ^ B - 1 := by
        have := Nat.one_le_two_pow (n := e + 1)
        omega
      rw [this, Nat.and_two_pow_sub_one_of_lt_two_pow hd] at hq'
      exact ⟨hq' ▸ Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self e), fun _ ↦ hq'⟩
    · simp only [htop, ↓reduceIte, mul_one, mul_zero, add_zero, zero_mul] at hq'
      exact ⟨lt_of_and_eq_zero hd hq', fun h ↦ absurd h htop⟩
  -- The quotient's coefficients.
  set t : ℕ → ℤ := fun q ↦ (dig B Xn q : ℤ) - 2 ^ e
  have ht : ∀ q < L, -2 ^ e ≤ t q ∧ t q < 2 ^ e := fun q hq ↦ by
    have := (hdig q hq).1
    have : ((dig B Xn q : ℕ) : ℤ) < 2 ^ (e + 1) := by exact_mod_cast this
    have : (2 : ℤ) ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ']
    simp only [t]
    constructor <;> omega
  have ht' : ∀ q < L, -2 ^ (B - 1) ≤ t q ∧ t q < 2 ^ (B - 1) := fun q hq ↦ by
    have : (2 : ℤ) ^ e ≤ 2 ^ (B - 1) := by exact_mod_cast heB.le
    have := ht q hq
    constructor <;> omega
  have hsnum : snum B t L = v / f := by
    have hG : ((onesN B sh * 2 ^ e : ℕ) : ℤ) = snum B (fun _ ↦ (2 : ℤ) ^ e) L := by
      rw [onesN_eq, mul_comm, num_mul, snum_natCast]
      exact snum_congr fun q _ ↦ by push_cast; ring
    have hXv : (Xn : ℤ) = snum B (fun q ↦ (dig B Xn q : ℤ)) L := by
      rw [← snum_natCast, num_dig hB hXlt]
    have : (Xn : ℤ) = X := Int.toNat_of_nonneg hX0
    rw [← snum_sub]
    simp only [X] at this
    rw [← hXv, this, hG]
    ring
  -- The quotient numeral.
  obtain ⟨hbias, hdigs⟩ := snum_add_bias hB ht'
  have hN'eq : N' = num B (fun q ↦ (t q + 2 ^ (B - 1)).toNat) L := by
    rw [← h, ← hsnum, offN_eq]
    exact (congrArg Int.toNat hbias).trans (Int.toNat_natCast _)
  have hN'lt : N' < 2 ^ (B * L) := hN'eq ▸ num_lt hdigs
  have hcf : ∀ q < L, cf B N' q = t q := fun q hq ↦ by
    rw [cf, hN'eq, dig_num hB hdigs hq, Int.toNat_of_nonneg (by linarith [(ht' q hq).1])]
    ring
  have hl1 : l1 sh (cf B N') < 2 ^ (B - 1) := by
    calc l1 sh (cf B N') ≤ ∑ q ∈ range L, 2 ^ e := sum_le_sum fun q hq ↦ by
          rw [hcf q (mem_range.mp hq)]
          have := ht q (mem_range.mp hq)
          have : |t q| ≤ 2 ^ e := abs_le.mpr ⟨this.1, this.2.le⟩
          rw [Int.abs_eq_natAbs] at this
          exact_mod_cast this
      _ = L * 2 ^ e := by rw [sum_const, card_range, smul_eq_mul]
      _ < 2 ^ (B - 1) := he₂
  refine ⟨⟨hN'lt, hl1⟩, ?_⟩
  -- The product with the factor: its coefficients are those of `N`.
  have htop : ∀ q < L, ex sh i q = deg sh i → cf B N' q = 0 := fun q hq hx ↦ by
    rw [hcf q hq]
    simp [t, (hdig q hq).2 hx]
  have hcfle : ∀ q < L, (cf B N' q).natAbs ≤ 2 ^ e := fun q hq ↦ by
    rw [hcf q hq]
    have := ht q hq
    have : |t q| ≤ 2 ^ e := abs_le.mpr ⟨this.1, this.2.le⟩
    rw [Int.abs_eq_natAbs] at this
    exact_mod_cast this
  have hp : ∀ q < L, -2 ^ (B - 1) ≤ mulL sh i a b (cf B N') q ∧
      mulL sh i a b (cf B N') q < 2 ^ (B - 1) := fun q hq ↦ by
    have h₁ := (natAbs_mulL_le sh i a b hcfle hq).trans_lt he₁
    have h₂ : |mulL sh i a b (cf B N') q| < 2 ^ (B - 1) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast h₁
    exact ⟨by linarith [(abs_lt.mp h₂).1], (abs_lt.mp h₂).2⟩
  have hpack : snum B (mulL sh i a b (cf B N')) L = snum B (cf B N) L := by
    rw [← pv_pack, pv_mulL sh i a b htop, pv_pack, snum_congr hcf, hsnum, packY, ← sub_offN hB hN]
    exact Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hr)
  intro y
  rw [← pv_mulL sh i a b htop y]
  exact pv_congr (fun q hq ↦ (snum_inj hB (fun q _ ↦ cf_bounds hB N q) hp hpack.symm hq)) y

/-! ### Division of the numerals of a polynomial over a field -/

/-- `divN` on every numeral, `none` at the first failure (`divL_spec`). -/
def divL (B : ℕ) (sh : List ℕ) (i : ℕ) (a b : ℤ) (e O : ℕ) : List ℕ → Option (List ℕ)
  | [] => some []
  | N :: Ns =>
    match divN B sh i a b e O N with
    | none => none
    | some N' => (divL B sh i a b e O Ns).map (N' :: ·)

theorem divL_spec {B : ℕ} (hB : 0 < B) {sh : List ℕ} {i : ℕ} {a b : ℤ} {e : ℕ}
    (he₁ : (a.natAbs + b.natAbs) * 2 ^ e < 2 ^ (B - 1)) (he₂ : slots sh * 2 ^ e < 2 ^ (B - 1)) :
    ∀ {Ns Ts : List ℕ}, (∀ N ∈ Ns, N < 2 ^ (B * slots sh)) →
      divL B sh i a b e (offN B sh) Ns = some Ts →
      (∀ T ∈ Ts, Inv B sh T) ∧ Ts.length = Ns.length ∧ ∀ j < Ns.length, ∀ y : ℕ → ℝ,
        pv sh (cf B (Ns.getD j 0)) y = (a + b * y i) * pv sh (cf B (Ts.getD j 0)) y
  | [], Ts, _, h => by
    simp only [divL, Option.some.injEq] at h
    subst h
    exact ⟨fun _ h ↦ absurd h List.not_mem_nil, rfl, fun j hj ↦ absurd hj (Nat.not_lt_zero _)⟩
  | N :: Ns, Ts, hNs, h => by
    simp only [divL] at h
    split at h
    · exact absurd h (by simp)
    · rename_i N' hN'
      cases hL : divL B sh i a b e (offN B sh) Ns with
      | none => rw [hL] at h; exact absurd h (by simp)
      | some Ts' =>
        rw [hL, Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨hinv, hpv⟩ := divN_spec hB he₁ he₂ (hNs N List.mem_cons_self) hN'
        obtain ⟨hinv', hlen', hpv'⟩ :=
          divL_spec hB he₁ he₂ (fun M hM ↦ hNs M (List.mem_cons_of_mem _ hM)) hL
        refine ⟨fun T hT ↦ ?_, by simp [hlen'], fun j hj y ↦ ?_⟩
        · rcases List.mem_cons.mp hT with rfl | hT
          · exact hinv
          · exact hinv' T hT
        · cases j with
          | zero => exact hpv y
          | succ j => exact hpv' j (by simpa using hj) y

/-- The quotient digit bound `2^e` of a division by `a + b yᵢ`: `max (|a| + |b|) slots < 2^g` and
`e + g = B - 1`, where `B` is large enough. -/
def divE (B : ℕ) (sh : List ℕ) (a b : ℤ) : ℕ :=
  B - 2 - Nat.log2 (max (a.natAbs + b.natAbs) (slots sh))

/-- The factor `a + b yᵢ` divided out of the numerals `Ns` as often as the division is exact, at
most `k` times (`divRep_spec`); `none` if the first division is not exact. -/
def divRep (B : ℕ) (sh : List ℕ) (i : ℕ) (a b : ℤ) (O : ℕ) : ℕ → List ℕ → Option (List ℕ)
  | 0, _ => none
  | k + 1, Ns =>
    let e := divE B sh a b
    bif decide ((a.natAbs + b.natAbs) * 2 ^ e < 2 ^ (B - 1)) &&
        decide (slots sh * 2 ^ e < 2 ^ (B - 1)) then
      match divL B sh i a b e O Ns with
      | none => none
      | some Ns' => some ((divRep B sh i a b O k Ns').getD Ns')
    else none

theorem divRep_spec {B : ℕ} (hB : 0 < B) {sh : List ℕ} {i : ℕ} {a b : ℤ} :
    ∀ (k : ℕ) {Ns Ts : List ℕ}, (∀ N ∈ Ns, N < 2 ^ (B * slots sh)) →
      divRep B sh i a b (offN B sh) k Ns = some Ts →
      (∀ T ∈ Ts, Inv B sh T) ∧ Ts.length = Ns.length ∧ ∃ m : ℕ, ∀ j < Ns.length, ∀ y : ℕ → ℝ,
        pv sh (cf B (Ns.getD j 0)) y = (a + b * y i) ^ m * pv sh (cf B (Ts.getD j 0)) y
  | 0, _, _, _, h => absurd h (by simp [divRep])
  | k + 1, Ns, Ts, hNs, h => by
    simp only [divRep] at h
    cases hc : (decide ((a.natAbs + b.natAbs) * 2 ^ divE B sh a b < 2 ^ (B - 1)) &&
        decide (slots sh * 2 ^ divE B sh a b < 2 ^ (B - 1)))
    · rw [hc] at h; exact absurd h (by simp)
    rw [hc, Bool.cond_true] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    split at h
    · exact absurd h (by simp)
    rename_i Ns' hNs'
    rw [Option.some.injEq] at h
    obtain ⟨hinv', hlen', hpv'⟩ := divL_spec hB hc.1 hc.2 hNs hNs'
    cases hR : divRep B sh i a b (offN B sh) k Ns' with
    | none =>
      rw [hR, Option.getD_none] at h
      subst h
      exact ⟨hinv', hlen', 1, fun j hj y ↦ by rw [pow_one]; exact hpv' j hj y⟩
    | some Us =>
      rw [hR, Option.getD_some] at h
      subst h
      obtain ⟨hinv, hlen, m, hpv⟩ := divRep_spec hB k (fun N hN ↦ (hinv' N hN).1) hR
      refine ⟨hinv, hlen.trans hlen', m + 1, fun j hj y ↦ ?_⟩
      rw [hpv' j hj y, hpv j (hlen' ▸ hj) y]
      ring

/-- The numerals `Ns` divided by the factors `fs` in turn, each `(i, a, b)` the factor
`a + b yᵢ` with `|b| ≤ a`, as often as the division is exact and at most `deg i` times
(`divAll_spec`); `none` if no division is exact. -/
def divAll (B : ℕ) (sh : List ℕ) (O : ℕ) : List (ℕ × ℤ × ℤ) → List ℕ → Option (List ℕ)
  | [], _ => none
  | (i, a, b) :: fs, Ns =>
    match bif decide ((b.natAbs : ℤ) ≤ a) then divRep B sh i a b O (deg sh i) Ns else none with
    | none => divAll B sh O fs Ns
    | some Ts => some ((divAll B sh O fs Ts).getD Ts)

/-- **Soundness of the divisions**: the quotients are numerals of the engine, and the polynomials
of `Ns` are those of the quotients times one function, nonnegative on the cube. -/
theorem divAll_spec {B : ℕ} (hB : 0 < B) {sh : List ℕ} :
    ∀ (fs : List (ℕ × ℤ × ℤ)) {Ns Ts : List ℕ}, (∀ N ∈ Ns, Inv B sh N) →
      divAll B sh (offN B sh) fs Ns = some Ts →
      (∀ T ∈ Ts, Inv B sh T) ∧ Ts.length = Ns.length ∧ ∃ φ : (ℕ → ℝ) → ℝ,
        (∀ y : ℕ → ℝ, (∀ i, |y i| ≤ 1) → 0 ≤ φ y) ∧ ∀ j < Ns.length, ∀ y : ℕ → ℝ,
          pv sh (cf B (Ns.getD j 0)) y = φ y * pv sh (cf B (Ts.getD j 0)) y
  | [], _, _, _, h => absurd h (by simp [divAll])
  | (i, a, b) :: fs, Ns, Ts, hNs, h => by
    simp only [divAll] at h
    split at h
    · exact divAll_spec hB fs hNs h
    rename_i Ts' hTs'
    cases hb : decide ((b.natAbs : ℤ) ≤ a)
    · rw [hb] at hTs'; exact absurd hTs' (by simp)
    rw [hb, Bool.cond_true] at hTs'
    have hab : (b.natAbs : ℤ) ≤ a := of_decide_eq_true hb
    obtain ⟨hinv', hlen', m, hpv'⟩ := divRep_spec hB _ (fun N hN ↦ (hNs N hN).1) hTs'
    have hφ : ∀ y : ℕ → ℝ, (∀ i, |y i| ≤ 1) → 0 ≤ ((a : ℝ) + b * y i) ^ m := fun y hy ↦ by
      refine pow_nonneg ?_ m
      have h₁ : |(b : ℝ) * y i| ≤ |(b : ℝ)| := by
        rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hy i)
      have h₂ : |(b : ℝ)| ≤ a := by
        rw [← Int.cast_abs, Int.abs_eq_natAbs]; exact_mod_cast hab
      linarith [neg_abs_le ((b : ℝ) * y i)]
    cases hR : divAll B sh (offN B sh) fs Ts' with
    | none =>
      rw [hR, Option.getD_none, Option.some.injEq] at h
      subst h
      exact ⟨hinv', hlen', fun y ↦ ((a : ℝ) + b * y i) ^ m, hφ, hpv'⟩
    | some Us =>
      rw [hR, Option.getD_some, Option.some.injEq] at h
      subst h
      obtain ⟨hinv, hlen, φ, hφ', hpv⟩ := divAll_spec hB fs hinv' hR
      refine ⟨hinv, hlen.trans hlen', fun y ↦ ((a : ℝ) + b * y i) ^ m * φ y,
        fun y hy ↦ mul_nonneg (hφ y hy) (hφ' y hy), fun j hj y ↦ ?_⟩
      rw [hpv' j hj y, hpv j (hlen' ▸ hj) y]
      ring

/-! ### The engine with divisions -/

section Field

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

variable (κ) in
/-- The bisection step of `run`: `run` is the box test or this (`run_eq_or_split`). -/
def split (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom last : Bool) : ℕ → List ℤ → List ℕ → Bool
  | 0, _, _ => false
  | d + 1, W, Ns =>
    let i := pickW last n W
    let W' := halveW W i
    bif deg sh i == 0 then run κ n sh B strict dom last d W' Ns
    else
      match subAll B sh i (halfW sh i) (-1) 1 (2 ^ deg sh i) Ns,
        subAll B sh i (halfW sh i) 1 1 (2 ^ deg sh i) Ns with
      | some Lo, some Hi =>
        run κ n sh B strict dom last d W' Lo && run κ n sh B strict dom last d W' Hi
      | _, _ => false

theorem run_eq_or_split (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom last : Bool) (d : ℕ)
    (W : List ℤ) (Ns : List ℕ) :
    run κ n sh B strict dom last d W Ns =
      (boxOk κ n sh B strict dom Ns || split κ n sh B strict dom last d W Ns) := by
  cases d with
  | zero => simp [run, split]
  | succ d => rfl

variable (κ) in
/-- **The engine with divisions** (`runDiv_sound`): for a weak sign, the box test of the numerals,
then the engine on their quotients by the factors `fs` (`divAll`) if a division is exact, then the
bisection of the numerals; for a strict sign, `run`. -/
def runDiv (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom last : Bool) (depth : ℕ) (W : List ℤ)
    (fs : List (ℕ × ℤ × ℤ)) (Ns : List ℕ) : Bool :=
  bif strict then run κ n sh B strict dom last depth W Ns
  else
    boxOk κ n sh B strict dom Ns ||
      (match divAll B sh (offN B sh) fs Ns with
        | some Ts => run κ n sh B strict dom last depth W Ts
        | none => false) ||
      split κ n sh B strict dom last depth W Ns

/-- **Soundness of the engine with divisions.** -/
theorem runDiv_sound {n : ℕ} {sh : List ℕ} {B : ℕ} {strict dom last : Bool} (hB : 0 < B)
    (hsh : sh.length ≤ n) (depth : ℕ) (W : List ℤ) (fs : List (ℕ × ℤ × ℤ)) {Ns : List ℕ}
    (hNs : ∀ N ∈ Ns, Inv B sh N) (hlen : ExactBasis.dim κ ≤ Ns.length)
    (h : runDiv κ n sh B strict dom last depth W fs Ns = true) (y : ℕ → ℝ)
    (hy : ∀ i, |y i| ≤ 1) : Sign strict (val (κ := κ) sh B Ns y) := by
  cases strict
  · simp only [runDiv, Bool.cond_false, Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · exact boxOk_sound hB hsh hNs hlen h hy
    · split at h
      · rename_i Ts hTs
        obtain ⟨hinv, hlenT, φ, hφ, hpv⟩ := divAll_spec hB fs hNs hTs
        have hs := run_sound hB hsh depth W hinv (hlenT ▸ hlen) h y hy
        have : val (κ := κ) sh B Ns y = φ y * val (κ := κ) sh B Ts y := by
          unfold val
          rw [mul_sum]
          refine sum_congr rfl fun j hj ↦ ?_
          rw [hpv j ((mem_range.mp hj).trans_le hlen) y]
          ring
        rw [this]
        exact mul_nonneg (hφ y hy) hs
      · exact absurd h (by simp)
    · have h' : run κ n sh B false dom last depth W Ns = true := by
        rw [run_eq_or_split, h, Bool.or_true]
      exact run_sound hB hsh depth W hNs hlen h' y hy
  · simp only [runDiv, Bool.cond_true] at h
    exact run_sound hB hsh depth W hNs hlen h y hy

end Field

end Lay

end Nieuwland.Check
