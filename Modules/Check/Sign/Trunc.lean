import Modules.Check.Sign.EngineCache

/-!
# Sign checks at bounded precision

The packed engine (`Lay.run`) decides the sign of `∑_c β_c p_c` on the cube from numerals whose
digits hold the coefficients of the polynomials `p_c` exactly, so its digit size grows with them. A
sum that is far from zero needs far fewer bits, as rupert's range check bounds with intervals before
it computes exactly. Here a tuple's terms are truncated, and the engine runs on the truncated sums
at a small digit size, with a bound on the truncation errors subtracted from their constant:

* `truncL`: the digits `c_q` of a term's numeral (digit size `B`), each scaled by an integer `m`
  and floored to a multiple of `2^s`, as a signed numeral of the digit size `B'`, with the sum of
  their absolute values (`truncL_eq`). It works by halves: a few passes over the numeral per level,
  `log₂` of the slots levels.
* The truncated polynomial `t` (`t_q = ⌊c_q m / 2^s⌋`) has `2^s pv t` within `L 2^s` of `m pv c`
  on the cube (`L` slots; `abs_pv_trunc_le`).
* `tPass`: the sums `∑ w_j t_{j c}` of a tuple's truncated terms, less `M = tErr (∑ |w_j| ρ_j)` in
  the constant of each coordinate `c` (`M` bounds `∑_c |β_c| ∑ |w_j| ρ_j` with the approximations
  of the basis, `apxSum`), checked by the engine at the digit size `B'`. `tPass_sound`: if it
  passes, `∑_c β_c ∑_j w_j P_{j c}` has the sign on the cube, for any values `P_{j c}` within
  `ρ_j 2^s` of the truncations `2^s pv t_{j c}`. Its sums (`tSums`) are a lower bound of the
  tuple's polynomial on the cube (`tSums_spec`), which `Pull.fTop` (`SparseTop.lean`) also tests by
  the top box's vertex test.

The exact engine stays the fallback where this test fails (`Pull.Frame.runTupleXT`).
-/

open Finset

namespace Nieuwland.Check

namespace Lay

open DPoly Num

/-! ### Truncated digits -/

/-- The signed numeral of digit size `B'` whose `L` digits are `⌊(d_q - h) m / 2^s⌋`, for the
digits `d_q` of `N` of digit size `B`, and the sum of their absolute values (`truncL_eq`): by
halves. -/
def truncL (B B' s h : ℕ) (m : ℤ) (L N : ℕ) : ℤ × ℕ :=
  if _hL : L ≤ 1 then
    bif L == 0 then (0, 0) else
      let d := (((N : ℤ) - h) * m) >>> s
      (d, d.natAbs)
  else
    let lo := truncL B B' s h m (L / 2) (N - ((N >>> (B * (L / 2))) <<< (B * (L / 2))))
    let hi := truncL B B' s h m (L - L / 2) (N >>> (B * (L / 2)))
    (lo.1 + shl hi.1 (B' * (L / 2)), lo.2 + hi.2)
termination_by L
decreasing_by all_goals omega

/-- The digits of the low part of a numeral. -/
theorem dig_mod_two_pow {B k q : ℕ} (N : ℕ) (hq : q < k) :
    dig B (N % 2 ^ (B * k)) q = dig B N q := by
  have := dig_block (B := B) (S := k) 0 N hq
  simpa using this

/-- The digits of the high part of a numeral. -/
theorem dig_div_two_pow (B k q N : ℕ) : dig B (N / 2 ^ (B * k)) q = dig B N (k + q) := by
  rw [dig, dig, Nat.div_div_eq_div_mul, ← pow_add, Nat.mul_add]

/-- A signed numeral in two parts. -/
theorem snum_split (B : ℕ) (f : ℕ → ℤ) {k L : ℕ} (hk : k ≤ L) :
    snum B f L = snum B f k + snum B (fun q ↦ f (k + q)) (L - k) * 2 ^ (B * k) := by
  conv_lhs => rw [show L = k + (L - k) by omega]
  rw [snum, sum_range_add, snum, snum, sum_mul]
  congr 1
  refine sum_congr rfl fun q _ ↦ ?_
  rw [mul_assoc, ← pow_add]
  congr 2
  ring

/-- A sum of absolute values in two parts. -/
theorem natAbs_sum_split (f : ℕ → ℤ) {k L : ℕ} (hk : k ≤ L) :
    ∑ q ∈ range L, (f q).natAbs =
      ∑ q ∈ range k, (f q).natAbs + ∑ q ∈ range (L - k), (f (k + q)).natAbs := by
  conv_lhs => rw [show L = k + (L - k) by omega]
  rw [sum_range_add]

/-- **`truncL` is the signed numeral of the truncated digits, with the sum of their absolute
values.** -/
theorem truncL_eq (B B' s h : ℕ) (m : ℤ) : ∀ (L N : ℕ), N < 2 ^ (B * L) →
    truncL B B' s h m L N = (snum B' (fun q ↦ ((dig B N q : ℤ) - h) * m / 2 ^ s) L,
      ∑ q ∈ range L, (((dig B N q : ℤ) - h) * m / 2 ^ s).natAbs) := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro N hN
    rw [truncL]
    split_ifs with hL
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hL with rfl | rfl
      · simp [snum]
      · have h1 : N < 2 ^ B := by simpa using hN
        have h0 : dig B N 0 = N := by simp [dig, Nat.mod_eq_of_lt h1]
        simp [snum, Int.shiftRight_eq_div_pow, h0]
    · have hk0 : 0 < L / 2 := by omega
      have hkL : L / 2 < L := by omega
      have hP : 0 < 2 ^ (B * (L / 2)) := Nat.two_pow_pos _
      have hlo : N - N / 2 ^ (B * (L / 2)) * 2 ^ (B * (L / 2)) = N % 2 ^ (B * (L / 2)) := by
        rw [Nat.mod_eq_sub_mul_div, Nat.mul_comm]
      have hhi : N / 2 ^ (B * (L / 2)) < 2 ^ (B * (L - L / 2)) := by
        rw [Nat.div_lt_iff_lt_mul hP, ← pow_add, ← Nat.mul_add, Nat.sub_add_cancel hkL.le]
        exact hN
      simp only []
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, hlo, shl_eq,
        ih (L / 2) hkL _ (Nat.mod_lt _ hP), ih (L - L / 2) (by omega) _ hhi,
        snum_split B' _ hkL.le, natAbs_sum_split _ hkL.le]
      refine Prod.ext ?_ ?_
      · dsimp only
        congr 1
        · exact snum_congr fun q hq ↦ by rw [dig_mod_two_pow N hq]
        · congr 1
          exact snum_congr fun q _ ↦ by rw [dig_div_two_pow]
      · dsimp only
        congr 1
        · exact sum_congr rfl fun q hq ↦ by rw [dig_mod_two_pow N (mem_range.mp hq)]
        · exact sum_congr rfl fun q _ ↦ by rw [dig_div_two_pow]

/-! ### Truncation errors -/

/-- A polynomial on the cube is at most its absolute coefficient sum. -/
theorem abs_pv_le_l1 (sh : List ℕ) (c : ℕ → ℤ) {y : ℕ → ℝ} (hy : ∀ i, |y i| ≤ 1) :
    |pv sh c y| ≤ (l1 sh c : ℝ) := by
  unfold pv l1
  push_cast
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun q _ ↦ ?_)
  rw [abs_mul, Nat.cast_natAbs, Int.cast_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_mono_le hy q)

/-- **The error of a truncation**: `m pv c` is within `L 2^s` of `2^s pv t` on the cube. -/
theorem abs_pv_trunc_le (sh : List ℕ) (c : ℕ → ℤ) (m : ℤ) (s : ℕ) {y : ℕ → ℝ}
    (hy : ∀ i, |y i| ≤ 1) :
    |(m : ℝ) * pv sh c y - 2 ^ s * pv sh (fun q ↦ c q * m / 2 ^ s) y| ≤
      (slots sh : ℝ) * 2 ^ s := by
  have hP : (0 : ℤ) < 2 ^ s := by positivity
  have he : (m : ℝ) * pv sh c y - 2 ^ s * pv sh (fun q ↦ c q * m / 2 ^ s) y =
      pv sh (fun q ↦ c q * m % 2 ^ s) y := by
    unfold pv
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun q _ ↦ ?_
    change (m : ℝ) * ((c q : ℝ) * mono sh q y) -
        2 ^ s * (((c q * m / 2 ^ s : ℤ) : ℝ) * mono sh q y) =
      ((c q * m % 2 ^ s : ℤ) : ℝ) * mono sh q y
    rw [Int.emod_def]
    push_cast
    ring
  rw [he]
  refine (abs_pv_le_l1 sh _ hy).trans ?_
  unfold l1
  push_cast
  calc ∑ q ∈ range (slots sh), (((c q * m % 2 ^ s).natAbs : ℤ) : ℝ)
      ≤ ∑ _q ∈ range (slots sh), ((2 : ℝ) ^ s) := by
        refine sum_le_sum fun q _ ↦ ?_
        have h₁ := Int.emod_nonneg (c q * m) hP.ne'
        have h₂ := Int.emod_lt_of_pos (c q * m) hP
        rw [Int.natAbs_of_nonneg h₁]
        exact_mod_cast h₂.le
    _ = (slots sh : ℝ) * 2 ^ s := by rw [sum_const, card_range, nsmul_eq_mul]

/-! ### The truncated test of a tuple -/

section Field

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

variable (κ) in
/-- `∑ⱼ (|aⱼ| + εⱼ)`, at least `2^apxK ∑ⱼ |βⱼ|` (`sum_abs_basis_le`). -/
def apxSum : ℕ := sumN (fun j ↦ (apxA κ j).natAbs + apxE κ j) (ExactBasis.dim κ)

theorem sum_abs_basis_le :
    (2 : ℝ) ^ ExactBasis.apxK κ * ∑ c ∈ range (ExactBasis.dim κ), |ExactBasis.basis κ c| ≤
      (apxSum κ : ℝ) := by
  rw [apxSum, sumN_eq, mul_sum]
  push_cast
  refine sum_le_sum fun c hc ↦ ?_
  have h := abs_apx_le (κ := κ) c (mem_range.mp hc)
  have h₂ : |(2 : ℝ) ^ ExactBasis.apxK κ * ExactBasis.basis κ c| ≤
      |(apxA κ c : ℝ)| + (apxE κ c : ℝ) := by
    have := abs_sub_abs_le_abs_sub ((2 : ℝ) ^ ExactBasis.apxK κ * ExactBasis.basis κ c)
      (apxA κ c : ℝ)
    linarith
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ ExactBasis.apxK κ)] at h₂
  rw [Nat.cast_natAbs, Int.cast_abs]
  exact h₂

variable (κ) in
/-- The bound on the truncation errors of a tuple in units of `2^s`, from `E = ∑ |w_j| ρ_j`: at
least `∑_c |β_c| E` (`le_tErr`). -/
def tErr (E : ℕ) : ℕ := (apxSum κ * E) >>> ExactBasis.apxK κ + 1

theorem le_tErr (E : ℕ) :
    (∑ c ∈ range (ExactBasis.dim κ), |ExactBasis.basis κ c|) * E ≤ (tErr κ E : ℝ) := by
  have hk : (0 : ℝ) < 2 ^ ExactBasis.apxK κ := by positivity
  have h₁ : (2 : ℝ) ^ ExactBasis.apxK κ *
      ((∑ c ∈ range (ExactBasis.dim κ), |ExactBasis.basis κ c|) * E) ≤ (apxSum κ * E : ℕ) := by
    rw [← mul_assoc]
    push_cast
    exact mul_le_mul_of_nonneg_right sum_abs_basis_le (Nat.cast_nonneg _)
  have h₂ : apxSum κ * E < 2 ^ ExactBasis.apxK κ * tErr κ E := by
    rw [tErr, Nat.shiftRight_eq_div_pow, Nat.mul_add, Nat.mul_one,
      Nat.mul_comm (2 ^ ExactBasis.apxK κ)]
    exact Nat.lt_div_mul_add (Nat.two_pow_pos _)
  have h₃ : ((apxSum κ * E : ℕ) : ℝ) ≤ (2 : ℝ) ^ ExactBasis.apxK κ * (tErr κ E : ℝ) := by
    exact_mod_cast h₂.le
  exact le_of_mul_le_mul_left (h₁.trans h₃) hk

variable (κ) in
/-- **The truncated test of a tuple** `τ` (`tPass_sound`): with the terms' truncated coordinates
`tv j c` (signed numerals of digit size `B'`), bounds `tl j c` on their absolute coefficient sums
and error bounds `ρ j` in units of `2^s`. Each coordinate's sum `∑ w tv` less
`M = tErr (∑ |w| ρ)` times the coordinates `u` of `1` must have its absolute coefficient sum
below the bias; then the engine runs on the numerals of the sums. -/
def tPass (n : ℕ) (sh : List ℕ) (B' : ℕ) (strict dom last : Bool) (depth : ℕ) (W : List ℤ)
    (tv : ℕ → ℕ → ℤ) (tl : ℕ → ℕ → ℕ) (ρ : ℕ → ℕ) (τ : List (ℕ × ℤ)) : Bool :=
  let M := tErr κ (τ.map fun jw ↦ jw.2.natAbs * ρ jw.1).sum
  let u := ExactBasis.coords (Exact.ofInt 1 : κ)
  (List.range (ExactBasis.dim κ)).all (fun c ↦
    decide ((τ.map fun jw ↦ jw.2.natAbs * tl jw.1 c).sum + M * (u.getD c 0).natAbs <
      2 ^ (B' - 1))) &&
    run κ n sh B' strict dom last depth W ((List.range (ExactBasis.dim κ)).map fun c ↦
      ((τ.map fun jw ↦ jw.2 * tv jw.1 c).sum - M * u.getD c 0 + offN B' sh).toNat)

variable (κ) in
/-- `tPass` with the engine's masks at the digit size `B'` given (`tPassM_masks`). -/
def tPassM (m : Masks) (n : ℕ) (sh : List ℕ) (B' : ℕ) (strict dom last : Bool) (depth : ℕ)
    (W : List ℤ) (tv : ℕ → ℕ → ℤ) (tl : ℕ → ℕ → ℕ) (ρ : ℕ → ℕ) (τ : List (ℕ × ℤ)) : Bool :=
  let M := tErr κ (τ.map fun jw ↦ jw.2.natAbs * ρ jw.1).sum
  let u := ExactBasis.coords (Exact.ofInt 1 : κ)
  (List.range (ExactBasis.dim κ)).all (fun c ↦
    decide ((τ.map fun jw ↦ jw.2.natAbs * tl jw.1 c).sum + M * (u.getD c 0).natAbs <
      2 ^ (B' - 1))) &&
    runM κ m n sh B' strict dom last depth W ((List.range (ExactBasis.dim κ)).map fun c ↦
      ((τ.map fun jw ↦ jw.2 * tv jw.1 c).sum - M * u.getD c 0 + m.off).toNat)

theorem tPassM_masks (n : ℕ) (sh : List ℕ) (B' : ℕ) (strict dom last : Bool) (depth : ℕ)
    (W : List ℤ) (tv : ℕ → ℕ → ℤ) (tl : ℕ → ℕ → ℕ) (ρ : ℕ → ℕ) (τ : List (ℕ × ℤ)) :
    tPassM κ (masks B' sh) n sh B' strict dom last depth W tv tl ρ τ =
      tPass κ n sh B' strict dom last depth W tv tl ρ τ := by
  simp only [tPassM, tPass, masks_off, runM_masks]

variable (κ) in
/-- The numerals of a tuple's truncated sums as `tPass` builds them (`tSums_spec`): each
coordinate's sum `∑ w tv` less `M = tErr (∑ |w| ρ)` times the coordinates `u` of `1`, biased. -/
def tSums (sh : List ℕ) (B' : ℕ) (tv : ℕ → ℕ → ℤ) (ρ : ℕ → ℕ) (τ : List (ℕ × ℤ)) : List ℕ :=
  (List.range (ExactBasis.dim κ)).map fun c ↦
    ((τ.map fun jw ↦ jw.2 * tv jw.1 c).sum -
      tErr κ (τ.map fun jw ↦ jw.2.natAbs * ρ jw.1).sum *
        (ExactBasis.coords (Exact.ofInt 1 : κ)).getD c 0 + offN B' sh).toNat

variable (κ) in
/-- The bound on the absolute coefficient sum of coordinate `c` of `tSums`, which `tPass` tests
against the bias. -/
def tL1 (tl : ℕ → ℕ → ℕ) (ρ : ℕ → ℕ) (τ : List (ℕ × ℤ)) (c : ℕ) : ℕ :=
  (τ.map fun jw ↦ jw.2.natAbs * tl jw.1 c).sum +
    tErr κ (τ.map fun jw ↦ jw.2.natAbs * ρ jw.1).sum *
      ((ExactBasis.coords (Exact.ofInt 1 : κ)).getD c 0).natAbs

/-- `tPass` is the room test of `tL1` and the engine on `tSums`. -/
theorem tPass_eq (n : ℕ) (sh : List ℕ) (B' : ℕ) (strict dom last : Bool) (depth : ℕ)
    (W : List ℤ) (tv : ℕ → ℕ → ℤ) (tl : ℕ → ℕ → ℕ) (ρ : ℕ → ℕ) (τ : List (ℕ × ℤ)) :
    tPass κ n sh B' strict dom last depth W tv tl ρ τ =
      ((List.range (ExactBasis.dim κ)).all (fun c ↦ decide (tL1 κ tl ρ τ c < 2 ^ (B' - 1))) &&
        run κ n sh B' strict dom last depth W (tSums κ sh B' tv ρ τ)) := rfl

/-- Lists related elementwise by `R` have equal images under a map that `R` preserves. -/
theorem map_eq_of_forall₂ {α β : Type*} {R : α → α → Prop} {f : α → β}
    (hf : ∀ a b, R a b → f a = f b) : ∀ {l' l : List α}, List.Forall₂ R l' l → l'.map f = l.map f
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h t => by
    rw [List.map_cons, List.map_cons, hf _ _ h, map_eq_of_forall₂ hf t]

/-- `tPass` reads a tuple's terms only through their weights and data. -/
theorem tPass_congr (n : ℕ) (sh : List ℕ) (B' : ℕ) (strict dom last : Bool) (depth : ℕ)
    (W : List ℤ) (tv : ℕ → ℕ → ℤ) (tl : ℕ → ℕ → ℕ) (ρ : ℕ → ℕ) {τ' τ : List (ℕ × ℤ)}
    (h : List.Forall₂ (fun x' x ↦ x'.2 = x.2 ∧ tv x'.1 = tv x.1 ∧ tl x'.1 = tl x.1 ∧
      ρ x'.1 = ρ x.1) τ' τ) :
    tPass κ n sh B' strict dom last depth W tv tl ρ τ' =
      tPass κ n sh B' strict dom last depth W tv tl ρ τ := by
  have h₁ : (τ'.map fun jw ↦ jw.2.natAbs * ρ jw.1) = τ.map fun jw ↦ jw.2.natAbs * ρ jw.1 :=
    map_eq_of_forall₂ (fun _ _ h ↦ by rw [h.1, h.2.2.2]) h
  have h₂ : ∀ c, (τ'.map fun jw ↦ jw.2.natAbs * tl jw.1 c) =
      τ.map fun jw ↦ jw.2.natAbs * tl jw.1 c :=
    fun c ↦ map_eq_of_forall₂ (fun _ _ h ↦ by rw [h.1, h.2.2.1]) h
  have h₃ : ∀ c, (τ'.map fun jw ↦ jw.2 * tv jw.1 c) = τ.map fun jw ↦ jw.2 * tv jw.1 c :=
    fun c ↦ map_eq_of_forall₂ (fun _ _ h ↦ by rw [h.1, h.2.1]) h
  simp only [tPass, h₁, h₂, h₃]

/-! #### Sums over a tuple -/

theorem snum_listSum (B L : ℕ) (f : ℕ → ℕ → ℤ) : ∀ τ : List (ℕ × ℤ),
    (τ.map fun jw ↦ jw.2 * snum B (f jw.1) L).sum =
      snum B (fun q ↦ (τ.map fun jw ↦ jw.2 * f jw.1 q).sum) L
  | [] => by simp [snum]
  | jw :: τ => by
    rw [List.map_cons, List.sum_cons, snum_listSum B L f τ, snum_mul, snum_add]
    simp only [List.map_cons, List.sum_cons]

theorem pv_listSum (sh : List ℕ) (f : ℕ → ℕ → ℤ) (y : ℕ → ℝ) : ∀ τ : List (ℕ × ℤ),
    pv sh (fun q ↦ (τ.map fun jw ↦ jw.2 * f jw.1 q).sum) y =
      (τ.map fun jw ↦ (jw.2 : ℝ) * pv sh (f jw.1) y).sum
  | [] => by simp [pv_zero]
  | jw :: τ => by
    simp only [List.map_cons, List.sum_cons]
    rw [pv_add, pv_smul, pv_listSum sh f y τ]

theorem l1_add_le (sh : List ℕ) (c d : ℕ → ℤ) :
    l1 sh (fun q ↦ c q + d q) ≤ l1 sh c + l1 sh d := by
  unfold l1
  rw [← sum_add_distrib]
  exact sum_le_sum fun q _ ↦ Int.natAbs_add_le _ _

theorem l1_smul (sh : List ℕ) (w : ℤ) (c : ℕ → ℤ) :
    l1 sh (fun q ↦ w * c q) = w.natAbs * l1 sh c := by
  simp only [l1, Int.natAbs_mul, mul_sum]

theorem l1_listSum_le (sh : List ℕ) (f : ℕ → ℕ → ℤ) : ∀ τ : List (ℕ × ℤ),
    l1 sh (fun q ↦ (τ.map fun jw ↦ jw.2 * f jw.1 q).sum) ≤
      (τ.map fun jw ↦ jw.2.natAbs * l1 sh (f jw.1)).sum
  | [] => by simp [l1]
  | jw :: τ => by
    simp only [List.map_cons, List.sum_cons]
    refine (l1_add_le sh _ _).trans ?_
    rw [l1_smul]
    exact Nat.add_le_add_left (l1_listSum_le sh f τ) _

/-- The polynomial with the single coefficient `x` in slot `0` (the constant). -/
theorem pv_single (sh : List ℕ) (x : ℤ) (y : ℕ → ℝ) :
    pv sh (fun q ↦ if q = 0 then x else 0) y = x := by
  unfold pv
  rw [sum_eq_single 0 (fun q _ hq ↦ by simp [hq]) (fun h ↦ absurd (mem_range.mpr (slots_pos sh)) h)]
  simp [mono_zero]

theorem l1_single (sh : List ℕ) (x : ℤ) : l1 sh (fun q ↦ if q = 0 then x else 0) = x.natAbs := by
  unfold l1
  rw [sum_eq_single 0 (fun q _ hq ↦ by simp [hq]) (fun h ↦ absurd (mem_range.mpr (slots_pos sh)) h)]
  simp

theorem snum_single (B L : ℕ) (hL : 0 < L) (x : ℤ) :
    snum B (fun q ↦ if q = 0 then x else 0) L = x := by
  unfold snum
  rw [sum_eq_single 0 (fun q _ hq ↦ by simp [hq]) (fun h ↦ absurd (mem_range.mpr hL) h)]
  simp

theorem abs_listSum_le {ι : Type*} (l : List ι) (f b : ι → ℝ) (h : ∀ x ∈ l, |f x| ≤ b x) :
    |(l.map f).sum| ≤ (l.map b).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add (h a List.mem_cons_self)
      (ih fun x hx ↦ h x (List.mem_cons_of_mem _ hx)))

theorem listSum_sub {ι : Type*} (l : List ι) (f g : ι → ℝ) :
    (l.map f).sum - (l.map g).sum = (l.map fun x ↦ f x - g x).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih]
    ring

theorem listSum_mul {ι : Type*} (l : List ι) (f : ι → ℝ) (t : ℝ) :
    t * (l.map f).sum = (l.map fun x ↦ t * f x).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih]
    ring

/-- The coordinates of `1` against the basis sum to `1`. -/
theorem sum_basis_coords_one :
    ∑ c ∈ range (ExactBasis.dim κ), ExactBasis.basis κ c *
      ((ExactBasis.coords (Exact.ofInt 1 : κ)).getD c 0 : ℝ) = 1 := by
  have h := ExactBasis.re_eq (Exact.ofInt 1 : κ)
  rw [Exact.re_ofInt, bsum] at h
  push_cast at h
  rw [h]
  refine sum_congr rfl fun c _ ↦ ?_
  rw [getD_map_of_eq (z := (0 : ℤ)) Int.cast_zero]

/-- **The truncated sums of a tuple** (`tSums`). For each term `j` of nonzero weight and each
coordinate `c`, let `tv j c` be the signed numeral of digits `td j c`, with absolute sum at most
`tl j c`, whose polynomial times `2^s` is within `ρ j 2^s` of `P j c` on the cube. Where the bounds
`tL1` are below the bias, the sums are numerals of the digit size `B'`, and `2^s` times the
combination of their polynomials is at most `∑_c β_c ∑_j w_j P j c` on the cube. -/
theorem tSums_spec {sh : List ℕ} {B' : ℕ} {tv : ℕ → ℕ → ℤ} {tl : ℕ → ℕ → ℕ} {ρ : ℕ → ℕ}
    {τ : List (ℕ × ℤ)} (hB' : 0 < B') (s : ℕ) (td : ℕ → ℕ → ℕ → ℤ)
    (P : ℕ → ℕ → (ℕ → ℝ) → ℝ)
    (ht : ∀ jw ∈ τ, jw.2 ≠ 0 → ∀ c < ExactBasis.dim κ,
      tv jw.1 c = snum B' (td jw.1 c) (slots sh) ∧ l1 sh (td jw.1 c) ≤ tl jw.1 c ∧
      ∀ y : ℕ → ℝ, (∀ i, |y i| ≤ 1) →
        |P jw.1 c y - 2 ^ s * pv sh (td jw.1 c) y| ≤ (ρ jw.1 : ℝ) * 2 ^ s)
    (hb : ∀ c < ExactBasis.dim κ, tL1 κ tl ρ τ c < 2 ^ (B' - 1)) :
    (∀ N ∈ tSums κ sh B' tv ρ τ, Inv B' sh N) ∧
      (tSums κ sh B' tv ρ τ).length = ExactBasis.dim κ ∧
      ∀ y : ℕ → ℝ, (∀ i, |y i| ≤ 1) →
        2 ^ s * ∑ c ∈ range (ExactBasis.dim κ),
            ExactBasis.basis κ c * pv sh (cf B' ((tSums κ sh B' tv ρ τ).getD c 0)) y ≤
          ∑ c ∈ range (ExactBasis.dim κ),
            ExactBasis.basis κ c * (τ.map fun jw ↦ (jw.2 : ℝ) * P jw.1 c y).sum := by
  unfold tSums
  unfold tL1 at hb
  set d := ExactBasis.dim κ with hd
  set E := (τ.map fun jw ↦ jw.2.natAbs * ρ jw.1).sum with hE
  set M := tErr κ E with hM
  set u := ExactBasis.coords (Exact.ofInt 1 : κ) with hu
  set L := slots sh with hL
  -- The digits of the sums.
  set g : ℕ → ℕ → ℤ := fun c q ↦
    (τ.map fun jw ↦ jw.2 * td jw.1 c q).sum + (if q = 0 then -(M * u.getD c 0) else 0) with hg
  have hzero : ∀ (c : ℕ) (f : ℕ × ℤ → ℤ) (f' : ℕ × ℤ → ℤ),
      (∀ jw ∈ τ, jw.2 ≠ 0 → f jw = f' jw) →
      (τ.map fun jw ↦ jw.2 * f jw).sum = (τ.map fun jw ↦ jw.2 * f' jw).sum := by
    intro c f f' hff
    congr 1
    refine List.map_congr_left fun jw hjw ↦ ?_
    by_cases hw : jw.2 = 0
    · rw [hw, zero_mul, zero_mul]
    · rw [hff jw hjw hw]
  have hsum : ∀ c < d, (τ.map fun jw ↦ jw.2 * tv jw.1 c).sum - M * u.getD c 0 =
      snum B' (g c) L := by
    intro c hc
    have hl := snum_listSum B' L (fun j ↦ td j c) τ
    rw [hzero c (fun jw ↦ tv jw.1 c) (fun jw ↦ snum B' (td jw.1 c) L)
      (fun jw hjw hw ↦ (ht jw hjw hw c hc).1), hl, sub_eq_add_neg,
      ← snum_single B' L (slots_pos sh) (-(M * u.getD c 0)), snum_add]
  have hl1 : ∀ c < d, l1 sh (g c) < 2 ^ (B' - 1) := by
    intro c hc
    refine lt_of_le_of_lt ?_ (hb c hc)
    refine (l1_add_le sh _ _).trans (Nat.add_le_add ?_ ?_)
    · refine (l1_listSum_le sh (fun j ↦ td j c) τ).trans (List.sum_le_sum fun jw hjw ↦ ?_)
      by_cases hw : jw.2 = 0
      · simp [hw]
      · exact Nat.mul_le_mul_left _ (ht jw hjw hw c hc).2.1
    · rw [l1_single, Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_natCast]
  -- The numerals of the sums.
  have hdig : ∀ c < d, ∀ q < L, -2 ^ (B' - 1) ≤ g c q ∧ g c q < 2 ^ (B' - 1) := by
    intro c hc q hq
    have h₁ := (abs_coeff_le_l1 (g c) hq).trans_lt (hl1 c hc)
    have h₂ : |g c q| < 2 ^ (B' - 1) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h₁
    constructor <;> linarith [abs_lt.mp h₂]
  set Ns := (List.range d).map fun c ↦
    ((τ.map fun jw ↦ jw.2 * tv jw.1 c).sum - M * u.getD c 0 + offN B' sh).toNat with hNs
  have hNc : ∀ c < d, Ns.getD c 0 = num B' (fun q ↦ (g c q + 2 ^ (B' - 1)).toNat) L := by
    intro c hc
    obtain ⟨hbias, -⟩ := snum_add_bias hB' (hdig c hc)
    rw [hNs, getD_map_of_lt _ 0 _ (by simpa using hc), List.getD_eq_getElem _ _ (by simpa using hc),
      List.getElem_range, hsum c hc, offN_eq, hbias, Int.toNat_natCast]
  have hcf : ∀ c < d, ∀ q < L, cf B' (Ns.getD c 0) q = g c q := by
    intro c hc q hq
    obtain ⟨-, hdg⟩ := snum_add_bias hB' (hdig c hc)
    rw [hNc c hc, cf, dig_num hB' hdg hq, Int.toNat_of_nonneg (by linarith [(hdig c hc q hq).1])]
    ring
  have hinv : ∀ N ∈ Ns, Inv B' sh N := by
    intro N hN
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hN
    have hc' : c < d := List.mem_range.mp hc
    have hget := hNc c hc'
    rw [hNs, getD_map_of_lt _ 0 _ (by simpa using hc'),
      List.getD_eq_getElem _ _ (by simpa using hc'), List.getElem_range] at hget
    rw [hget]
    obtain ⟨-, hdg⟩ := snum_add_bias hB' (hdig c hc')
    refine ⟨num_lt hdg, ?_⟩
    have := hcf c hc'
    rw [hNc c hc'] at this
    rw [l1_congr this]
    exact hl1 c hc'
  refine ⟨hinv, by simp [hNs, hd], fun y hy ↦ ?_⟩
  -- The value of the sums: `∑_c β_c (∑_j w_j pv t_{j c} - M u_c)`.
  have hval : ∑ c ∈ range d, ExactBasis.basis κ c * pv sh (cf B' (Ns.getD c 0)) y =
      ∑ c ∈ range d, ExactBasis.basis κ c *
        (τ.map fun jw ↦ (jw.2 : ℝ) * pv sh (td jw.1 c) y).sum - M := by
    have hpv : ∀ c < d, pv sh (cf B' (Ns.getD c 0)) y =
        (τ.map fun jw ↦ (jw.2 : ℝ) * pv sh (td jw.1 c) y).sum - M * (u.getD c 0 : ℝ) := by
      intro c hc
      have hl := pv_listSum sh (fun j ↦ td j c) y τ
      rw [pv_congr (hcf c hc), hg]
      simp only
      rw [pv_add (c := fun q ↦ (τ.map fun jw ↦ jw.2 * td jw.1 c q).sum), hl, pv_single]
      push_cast
      ring
    rw [sum_congr rfl fun c hc ↦ by rw [hpv c (mem_range.mp hc)]]
    simp only [mul_sub, sum_sub_distrib]
    congr 1
    conv_rhs => rw [← mul_one (M : ℝ), ← sum_basis_coords_one (κ := κ), ← hu, mul_sum]
    exact sum_congr rfl fun c _ ↦ by ring
  -- The errors.
  have herr : ∀ c < d, |(τ.map fun jw ↦ (jw.2 : ℝ) * P jw.1 c y).sum -
      2 ^ s * (τ.map fun jw ↦ (jw.2 : ℝ) * pv sh (td jw.1 c) y).sum| ≤ (E : ℝ) * 2 ^ s := by
    intro c hc
    rw [listSum_mul, listSum_sub]
    have hE' : (E : ℝ) * 2 ^ s = (τ.map fun jw ↦ ((jw.2.natAbs * ρ jw.1 : ℕ) : ℝ) * 2 ^ s).sum := by
      rw [hE, Nat.cast_list_sum, List.map_map, mul_comm, listSum_mul]
      congr 1
      exact List.map_congr_left fun jw _ ↦ by simp only [Function.comp]; ring
    rw [hE']
    refine abs_listSum_le _ _ _ fun jw hjw ↦ ?_
    by_cases hw : jw.2 = 0
    · simp [hw]
    · have := (ht jw hjw hw c hc).2.2 y hy
      rw [show (jw.2 : ℝ) * P jw.1 c y - 2 ^ s * ((jw.2 : ℝ) * pv sh (td jw.1 c) y) =
        (jw.2 : ℝ) * (P jw.1 c y - 2 ^ s * pv sh (td jw.1 c) y) by ring, abs_mul]
      push_cast
      rw [Nat.cast_natAbs, Int.cast_abs, mul_assoc]
      exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
  have hbound : ∑ c ∈ range d, ExactBasis.basis κ c *
        (τ.map fun jw ↦ (jw.2 : ℝ) * P jw.1 c y).sum ≥
      2 ^ s * (∑ c ∈ range d, ExactBasis.basis κ c *
        (τ.map fun jw ↦ (jw.2 : ℝ) * pv sh (td jw.1 c) y).sum - M) := by
    have h₁ : |∑ c ∈ range d, ExactBasis.basis κ c *
        (τ.map fun jw ↦ (jw.2 : ℝ) * P jw.1 c y).sum -
        2 ^ s * ∑ c ∈ range d, ExactBasis.basis κ c *
          (τ.map fun jw ↦ (jw.2 : ℝ) * pv sh (td jw.1 c) y).sum| ≤
        (∑ c ∈ range d, |ExactBasis.basis κ c|) * E * 2 ^ s := by
      rw [mul_sum, ← sum_sub_distrib, mul_assoc, sum_mul]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun c hc ↦ ?_)
      rw [show ExactBasis.basis κ c * (τ.map fun jw ↦ (jw.2 : ℝ) * P jw.1 c y).sum -
          2 ^ s * (ExactBasis.basis κ c *
            (τ.map fun jw ↦ (jw.2 : ℝ) * pv sh (td jw.1 c) y).sum) =
          ExactBasis.basis κ c * ((τ.map fun jw ↦ (jw.2 : ℝ) * P jw.1 c y).sum -
            2 ^ s * (τ.map fun jw ↦ (jw.2 : ℝ) * pv sh (td jw.1 c) y).sum) by ring, abs_mul]
      exact mul_le_mul_of_nonneg_left (herr c (mem_range.mp hc)) (abs_nonneg _)
    have h₂ : (∑ c ∈ range d, |ExactBasis.basis κ c|) * E * 2 ^ s ≤ (M : ℝ) * 2 ^ s :=
      mul_le_mul_of_nonneg_right (le_tErr E) (by positivity)
    have h₃ := (abs_le.mp (h₁.trans h₂)).1
    nlinarith
  rw [hval]
  linarith

/-- **Soundness of the truncated test.** For each term `j` of nonzero weight and each coordinate
`c`, let `tv j c` be the signed numeral of digits `td j c`, with absolute sum at most `tl j c`,
whose polynomial times `2^s` is within `ρ j 2^s` of `P j c` on the cube. If `tPass` passes, then
`∑_c β_c ∑_j w_j P j c` has the sign on the cube. -/
theorem tPass_sound {n : ℕ} {sh : List ℕ} {B' : ℕ} {strict dom last : Bool} {depth : ℕ}
    {W : List ℤ} {tv : ℕ → ℕ → ℤ} {tl : ℕ → ℕ → ℕ} {ρ : ℕ → ℕ} {τ : List (ℕ × ℤ)}
    (hB' : 0 < B') (hsh : sh.length ≤ n) (s : ℕ) (td : ℕ → ℕ → ℕ → ℤ)
    (P : ℕ → ℕ → (ℕ → ℝ) → ℝ)
    (ht : ∀ jw ∈ τ, jw.2 ≠ 0 → ∀ c < ExactBasis.dim κ,
      tv jw.1 c = snum B' (td jw.1 c) (slots sh) ∧ l1 sh (td jw.1 c) ≤ tl jw.1 c ∧
      ∀ y : ℕ → ℝ, (∀ i, |y i| ≤ 1) →
        |P jw.1 c y - 2 ^ s * pv sh (td jw.1 c) y| ≤ (ρ jw.1 : ℝ) * 2 ^ s)
    (h : tPass κ n sh B' strict dom last depth W tv tl ρ τ = true)
    {y : ℕ → ℝ} (hy : ∀ i, |y i| ≤ 1) :
    Sign strict (∑ c ∈ range (ExactBasis.dim κ),
      ExactBasis.basis κ c * (τ.map fun jw ↦ (jw.2 : ℝ) * P jw.1 c y).sum) := by
  simp only [tPass_eq, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨hb, hrun⟩ := h
  obtain ⟨hinv, hlen, hle⟩ := tSums_spec (κ := κ) hB' s td P ht hb
  have hs := run_sound hB' hsh depth W hinv hlen.ge hrun y hy
  unfold val at hs
  refine sign_of_le ?_ (hle y hy)
  cases strict
  · exact mul_nonneg (by positivity) hs
  · exact mul_pos (by positivity) hs

end Field

end Lay

end Nieuwland.Check
