import Modules.Check.Sign.SparseBnd

/-!
# The top box at bounded precision

rupert tests the top box of a tuple with a zero on its box (`nonneg_exact_rec`,
`code/src/proof/regional.rs`) on `f64` interval shifts of one dense enclosure of the tuple's
polynomial, with the exact value at the vertex where the centred linear part is smallest. `procA`
(`SparseBnd.lean`) tests it on the exact vertex frame, computed from the tuple's sparse terms at the
full digit size, which was most of the time of the heavy leaves. `procB` tests it first on one
integer enclosure on the leaf's box `y ∈ [-1, 1]^n`, made at bounded precision from the tuple's
centred numerals (those of the centred test) and the exact value at the vertex `σ`:

* each slot's coefficient `p_q = 2^K ∑_c β_c d_{c,q}` lies in `[m_q, m_q + 2 e_q]` for the lower
  bound `m_q` and the approximation error `e_q` of `Lay.lowD`. Floored at `2^s` it is
  `p_q = 2^s t_q + δ_q` with `0 ≤ δ_q ≤ 2^s ε_q` for the count `ε_q = Lay.errS s e_q`
  (`Lay.truncIE`: the floors `t_q` of `Lay.truncI`, and `ε = ∑_q ε_q`);
* `2^K P(y) = 2^K P(σ) + 2^s (T(y) - T(σ)) + ∑_q δ_q (y^q - σ^q)`, and on `[-1, 1]^n`
  `|y^q - σ^q| ≤ ∑ᵢ qᵢ |yᵢ - σᵢ| = ∑ᵢ qᵢ (1 - σᵢ yᵢ)` (`Lay.abs_mono_sub_le`), so the rounding
  errors are charged to the distances from the vertex, where they vanish;
* with the exact value `v` at the vertex (`valsAt` at the point `Cₓ + σ Hₓ`) and its lower bound
  `lowZ v ≤ 2^K P(σ)`, `encY = ⌊lowZ v / 2^s⌋ + T(y) - T(σ) - ε ∑ᵢ dᵢ (1 - σᵢ yᵢ)` (`dᵢ` the
  shape's degree in `yᵢ`) satisfies `2^s encY ≤ 2^K P` on `[-1, 1]^n` (`encY_le`);
* the top box's tests run on the enclosure over `ℤ` (`topTM`: the centred form, then the vertex
  test at the enclosure's own vertex). Where they fail, `procA` tests the box exactly and bisects:
  an enclosure whose errors grow linearly from the vertex cannot follow a tuple that vanishes there
  to second order.

The scale `2^s` is `bPrecY` bits below the largest coordinate of the exact value at the vertex
(`vMax`). That value is at most the numerals' absolute coefficient sums, which the centred test
computes, and on K_{√3/3}'s failing tuples within 4 bits of them. So `procB` needs neither those
sums nor the centred test, and after a failing truncated test compiled code tests the centred form
last (`runTupleNP`). The field's approximations limit the precision to about `2^-K` of the
coefficients. Soundness (`procB_sound`): the tuple's combination has the sign on the leaf's box.
Neither the precision nor the vertex needs correctness. `runTupleNW` runs `procB` before the exact
vertex frame where the numerals have at least `bMin` bits (`useB`).

`fTop` tests the top box from the truncations of the terms' values at bounded precision
(`FPoly`), so that a tuple it closes needs no exact values: their sums as the truncated test builds
them (`Lay.tSums`, the errors of the truncations and of the values subtracted from the constant;
`Lay.tSums_spec`), the enclosure `encP` on the cube (the floors of `Lay.truncIE`, their error
count charged as one constant, `encP_le`), and `cubeZ`'s tests on it: the centred form, then, where
the enclosure has the sign at the vertex, `procA` over `ℤ` on it (the vertex test on its exact
vertex frame, then rupert's bisection on that frame's integer enclosure), as rupert bisects the
enclosure of a tuple whose top box fails. The values' errors bound them on the whole cube, not at
a vertex, so this enclosure has no vertex and needs no exact value there; the margin it needs is
the tuple's vertex value, which on K_{√3/3}'s failing tuples is within 6 bits of their largest
term, against errors about 120 bits below it. Where the tuple vanishes at the vertex, the
enclosure is negative there and the tuple goes on to the exact tests, as rupert shifts exactly
there. Soundness (`fTop_sound`): the conclusion of `Lay.tPass_sound`.
-/

open Finset

namespace Nieuwland.Check

open DPoly

namespace Lay

open Num

/-! ### Two-sided truncation -/

/-- The approximation errors `∑_c E_c |d_c|` of the digits `d_c = N_c - h` of the numerals `Ns`
(`c < D`), with the error bounds `E_c` of `A` (as `lowD`). -/
def errD (D : ℕ) (A : List (ℤ × ℕ)) (h : ℕ) (Ns : List ℕ) : ℕ :=
  ((List.range D).map fun c ↦ (A.getD c (0, 0)).2 * ((Ns.getD c 0 : ℤ) - h).natAbs).sum

/-- `errD` with the digits read by a function (in proofs). -/
def errF (D : ℕ) (A : List (ℤ × ℕ)) (h : ℕ) (d : ℕ → ℕ) : ℕ :=
  ∑ c ∈ range D, (A.getD c (0, 0)).2 * ((d c : ℤ) - h).natAbs

theorem errD_eq (D : ℕ) (A : List (ℤ × ℕ)) (h : ℕ) (Ns : List ℕ) :
    errD D A h Ns = errF D A h fun c ↦ Ns.getD c 0 := by
  unfold errD errF
  induction D with
  | zero => simp
  | succ D ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

/-- A slot's error count at the scale `2^s`: one for the floor, and twice the approximation
errors `e` over `2^s`, rounded up. -/
def errS (s e : ℕ) : ℕ := (2 * e + 2 ^ s - 1) / 2 ^ s + 1

/-- `errS` by shifts (`errS_eq_errSS`): compiled `Nat.pow` builds a GMP number even for small
powers, and dividing by `2^s` is a shift. -/
def errSS (s e : ℕ) : ℕ := ((2 * e + (1 <<< s) - 1) >>> s) + 1

@[csimp] theorem errS_eq_errSS : @errS = @errSS := by
  funext s e
  rw [errS, errSS, Nat.shiftLeft_eq, Nat.one_mul, Nat.shiftRight_eq_div_pow]

theorem two_mul_le_errS (s e : ℕ) : 2 * e + 2 ^ s ≤ 2 ^ s * errS s e := by
  have hp : 0 < 2 ^ s := Nat.two_pow_pos s
  have h := Nat.div_add_mod (2 * e + 2 ^ s - 1) (2 ^ s)
  have hm := Nat.mod_lt (2 * e + 2 ^ s - 1) hp
  rw [errS, Nat.mul_add, Nat.mul_one]
  omega

/-- `truncI` with the slots' error counts (`errS`) summed: the terms of `truncI` (`truncIE_fst`)
and `∑_q errS s (errF …)` (`truncIE_snd`). -/
def truncIE (B s h D : ℕ) (A : List (ℤ × ℕ)) (sh : List ℕ) (q₀ L : ℕ) (Ns : List ℕ) :
    SPoly ℤ × ℕ :=
  if _hL : L ≤ 1 then
    bif L == 0 then ([], 0) else
      let t := lowD D A h Ns >>> s
      (bif t == 0 then [] else [(t, exps sh q₀)], errS s (errD D A h Ns))
  else
    let lo := truncIE B s h D A sh q₀ (L / 2)
      (Ns.map fun N ↦ N - ((N >>> (B * (L / 2))) <<< (B * (L / 2))))
    let hi := truncIE B s h D A sh (q₀ + L / 2) (L - L / 2) (Ns.map fun N ↦ N >>> (B * (L / 2)))
    (lo.1 ++ hi.1, lo.2 + hi.2)
termination_by L
decreasing_by all_goals omega

theorem truncIE_fst (B s h D : ℕ) (A : List (ℤ × ℕ)) (sh : List ℕ) :
    ∀ (L q₀ : ℕ) (Ns : List ℕ), (truncIE B s h D A sh q₀ L Ns).1 = truncI B s h D A sh q₀ L Ns := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro q₀ Ns
    rw [truncIE, truncI]
    split_ifs with hL
    · cases L == 0 <;> rfl
    · simp only
      rw [ih (L / 2) (by omega), ih (L - L / 2) (by omega)]

theorem truncIE_snd (B s h D : ℕ) (A : List (ℤ × ℕ)) (sh : List ℕ) :
    ∀ (L q₀ : ℕ) (Ns : List ℕ), (∀ c, Ns.getD c 0 < 2 ^ (B * L)) →
      (truncIE B s h D A sh q₀ L Ns).2 =
        ∑ q ∈ range L, errS s (errF D A h fun c ↦ dig B (Ns.getD c 0) q) := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro q₀ Ns hN
    rw [truncIE]
    split_ifs with hL
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hL with rfl | rfl
      · rfl
      · have h0 : ∀ c, dig B (Ns.getD c 0) 0 = Ns.getD c 0 := fun c ↦ by
          have h1 : Ns.getD c 0 < 2 ^ B := by simpa using hN c
          rw [dig, Nat.mul_zero, pow_zero, Nat.div_one, Nat.mod_eq_of_lt h1]
        simp only [show ((1 : ℕ) == 0) = false from rfl, Bool.cond_false, sum_range_one, h0,
          errD_eq]
    · have hkL : L / 2 < L := by omega
      have hP : 0 < 2 ^ (B * (L / 2)) := Nat.two_pow_pos _
      have hlo : ∀ c, (Ns.map fun N ↦ N - (N >>> (B * (L / 2))) <<< (B * (L / 2))).getD c 0 =
          Ns.getD c 0 % 2 ^ (B * (L / 2)) := fun c ↦ by
        rw [getD_map_of_eq (z := 0) (by simp), Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
          Nat.mod_eq_sub_mul_div, Nat.mul_comm]
      have hhi : ∀ c, (Ns.map fun N ↦ N >>> (B * (L / 2))).getD c 0 =
          Ns.getD c 0 / 2 ^ (B * (L / 2)) := fun c ↦ by
        rw [getD_map_of_eq (z := 0) (by simp), Nat.shiftRight_eq_div_pow]
      have hhi' : ∀ c, Ns.getD c 0 / 2 ^ (B * (L / 2)) < 2 ^ (B * (L - L / 2)) := fun c ↦ by
        rw [Nat.div_lt_iff_lt_mul hP, ← pow_add, ← Nat.mul_add, Nat.sub_add_cancel hkL.le]
        exact hN c
      simp only
      rw [ih (L / 2) hkL _ _ (fun c ↦ by rw [hlo]; exact Nat.mod_lt _ hP),
        ih (L - L / 2) (by omega) _ _ (fun c ↦ by rw [hhi]; exact hhi' c)]
      conv_rhs => rw [show L = L / 2 + (L - L / 2) by omega, sum_range_add]
      congr 1
      · refine sum_congr rfl fun q hq ↦ ?_
        simp only [hlo, dig_mod_two_pow _ (mem_range.mp hq)]
      · refine sum_congr rfl fun q _ ↦ ?_
        simp only [hhi, dig_div_two_pow]

section Field

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- **The upper bound of a slot**: `2^K ∑_c β_c d_c ≤ m + 2 ∑_c E_c |d_c|` for the lower bound `m`
of `lowF_le`. -/
theorem le_lowF_add (h : ℕ) (d : ℕ → ℕ) :
    2 ^ ExactBasis.apxK κ * ∑ c ∈ range (ExactBasis.dim κ),
        ExactBasis.basis κ c * (((d c : ℤ) - h : ℤ) : ℝ) ≤
      (lowF (ExactBasis.dim κ) (ExactBasis.apx κ) h d : ℝ) +
        2 * (errF (ExactBasis.dim κ) (ExactBasis.apx κ) h d : ℝ) := by
  unfold lowF errF
  push_cast
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun c hc ↦ ?_
  have ha := ExactBasis.apx_sound (κ := κ) c (mem_range.mp hc)
  set A := (((ExactBasis.apx κ).getD c (0, 0)).1 : ℝ)
  set E := (((ExactBasis.apx κ).getD c (0, 0)).2 : ℝ)
  set x : ℝ := (d c : ℝ) - h
  have hb : |(2 ^ ExactBasis.apxK κ * ExactBasis.basis κ c - A) * x| ≤ E * |x| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right ha (abs_nonneg _)
  have := le_abs_self ((2 ^ ExactBasis.apxK κ * ExactBasis.basis κ c - A) * x)
  have hx : ((((d c : ℤ) - h).natAbs : ℕ) : ℝ) = |x| := by
    rw [Nat.cast_natAbs]
    push_cast
    rfl
  rw [hx]
  nlinarith

end Field

/-! ### Exact values -/

/-- The integer lower bound `∑_c (A_c v_c - E_c |v_c|)` of `2^K ∑_c β_c v_c` (`lowZ_le`). -/
def lowZ (D : ℕ) (A : List (ℤ × ℕ)) (v : List ℤ) : ℤ :=
  ((List.range D).map fun c ↦
    (A.getD c (0, 0)).1 * v.getD c 0 - ((A.getD c (0, 0)).2 : ℤ) * ((v.getD c 0).natAbs : ℤ)).sum

section Field

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

theorem lowZ_le (v : List ℤ) :
    (lowZ (ExactBasis.dim κ) (ExactBasis.apx κ) v : ℝ) ≤
      2 ^ ExactBasis.apxK κ * ∑ c ∈ range (ExactBasis.dim κ),
        ExactBasis.basis κ c * (v.getD c 0 : ℝ) := by
  have hL : lowZ (ExactBasis.dim κ) (ExactBasis.apx κ) v = ∑ c ∈ range (ExactBasis.dim κ),
      (((ExactBasis.apx κ).getD c (0, 0)).1 * v.getD c 0 -
        (((ExactBasis.apx κ).getD c (0, 0)).2 : ℤ) * ((v.getD c 0).natAbs : ℤ)) := by
    unfold lowZ
    generalize ExactBasis.dim κ = D
    induction D with
    | zero => simp
    | succ D ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp
  rw [hL]
  push_cast
  rw [mul_sum]
  refine sum_le_sum fun c hc ↦ ?_
  have ha := ExactBasis.apx_sound (κ := κ) c (mem_range.mp hc)
  set A := (((ExactBasis.apx κ).getD c (0, 0)).1 : ℝ)
  set E := (((ExactBasis.apx κ).getD c (0, 0)).2 : ℝ)
  set x : ℝ := (v.getD c 0 : ℝ)
  have hb : |(2 ^ ExactBasis.apxK κ * ExactBasis.basis κ c - A) * x| ≤ E * |x| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right ha (abs_nonneg _)
  have := neg_abs_le ((2 ^ ExactBasis.apxK κ * ExactBasis.basis κ c - A) * x)
  nlinarith

end Field

/-! ### Monomials near a vertex -/

theorem abs_pow_sub_pow_le {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    ∀ e : ℕ, |a ^ e - b ^ e| ≤ e * |a - b|
  | 0 => by simp
  | e + 1 => by
    have ih := abs_pow_sub_pow_le ha hb e
    have h1 : a ^ (e + 1) - b ^ (e + 1) = (a - b) * a ^ e + b * (a ^ e - b ^ e) := by ring
    have hae : |a ^ e| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) ha
    rw [h1]
    calc |(a - b) * a ^ e + b * (a ^ e - b ^ e)|
        ≤ |a - b| * |a ^ e| + |b| * |a ^ e - b ^ e| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
      _ ≤ |a - b| * 1 + 1 * (e * |a - b|) := by
          gcongr
      _ = ((e + 1 : ℕ) : ℝ) * |a - b| := by push_cast; ring

theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) {a b : ι → ℝ} (e : ι → ℕ)
    (ha : ∀ i ∈ s, |a i| ≤ 1) (hb : ∀ i ∈ s, |b i| ≤ 1) :
    |∏ i ∈ s, a i ^ e i - ∏ i ∈ s, b i ^ e i| ≤ ∑ i ∈ s, (e i : ℝ) * |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [prod_insert hj, prod_insert hj, sum_insert hj]
    have ih := ih (fun i hi ↦ ha i (mem_insert_of_mem hi)) (fun i hi ↦ hb i (mem_insert_of_mem hi))
    have hP : |∏ i ∈ s, a i ^ e i| ≤ 1 := by
      rw [abs_prod]
      exact prod_le_one₀ (fun _ _ ↦ abs_nonneg _) fun i hi ↦ by
        rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (ha i (mem_insert_of_mem hi))
    have hbj : |b j ^ e j| ≤ 1 := by
      rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hb j (mem_insert_self j s))
    have hj' := abs_pow_sub_pow_le (ha j (mem_insert_self j s)) (hb j (mem_insert_self j s)) (e j)
    have h1 : a j ^ e j * ∏ i ∈ s, a i ^ e i - b j ^ e j * ∏ i ∈ s, b i ^ e i =
        (a j ^ e j - b j ^ e j) * ∏ i ∈ s, a i ^ e i +
          b j ^ e j * (∏ i ∈ s, a i ^ e i - ∏ i ∈ s, b i ^ e i) := by ring
    rw [h1]
    calc _ ≤ |a j ^ e j - b j ^ e j| * |∏ i ∈ s, a i ^ e i| +
          |b j ^ e j| * |∏ i ∈ s, a i ^ e i - ∏ i ∈ s, b i ^ e i| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
      _ ≤ (e j : ℝ) * |a j - b j| * 1 + 1 * ∑ i ∈ s, (e i : ℝ) * |a i - b i| := by gcongr
      _ = _ := by ring

/-- **A monomial near a vertex**: on `[-1, 1]^n`, a slot's monomial moves by at most the degrees
times the distances. -/
theorem abs_mono_sub_le (sh : List ℕ) (q : ℕ) {y σ : ℕ → ℝ} (hy : ∀ i, |y i| ≤ 1)
    (hσ : ∀ i, |σ i| ≤ 1) :
    |mono sh q y - mono sh q σ| ≤ ∑ i ∈ range sh.length, (deg sh i : ℝ) * |y i - σ i| := by
  refine (abs_prod_sub_prod_le _ _ (fun i _ ↦ hy i) fun i _ ↦ hσ i).trans
    (sum_le_sum fun i _ ↦ ?_)
  gcongr
  exact_mod_cast ex_lt sh i q

end Lay

namespace Pull

open WTerms

/-- The exponent list of the variable `i`. -/
def linE (i : ℕ) : List ℕ := List.replicate i 0 ++ [1]

theorem mono_linE (u : ℕ → ℝ) (i : ℕ) : SPoly.mono (1 : ℝ) u 0 (linE i) = u i := by
  rw [Lay.mono_list, linE, List.length_append, List.length_replicate, List.length_singleton,
    prod_range_succ]
  have h1 : (List.replicate i 0 ++ [1]).getD i 0 = 1 := by
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have h0 : ∀ j ∈ range i, u (0 + j) ^ (List.replicate i 0 ++ [1]).getD j 0 = 1 := by
    intro j hj
    have hj := mem_range.mp hj
    rw [List.getD_append _ _ _ _ (show j < (List.replicate i 0).length by simpa using hj)]
    simp
  rw [prod_eq_one h0, h1, one_mul, pow_one, zero_add]

/-- The linear terms `cᵢ yᵢ` of the variables `i < m` with `cᵢ ≠ 0`. -/
def linT (c : ℕ → ℤ) (m : ℕ) : SPoly ℤ :=
  (List.range m).filterMap fun i ↦ bif c i == 0 then none else some (c i, linE i)

theorem run_linT (c : ℕ → ℤ) (u : ℕ → ℝ) (m : ℕ) :
    SPoly.run (fun a : ℤ ↦ (a : ℝ)) u (linT c m) = ∑ i ∈ range m, (c i : ℝ) * u i := by
  induction m with
  | zero => simp [linT, SPoly.run, Exact.ofInt]
  | succ m ih =>
    rw [linT, List.range_succ, List.filterMap_append, ← linT, SPoly.run_int_eq_sum,
      List.map_append, List.sum_append, ← SPoly.run_int_eq_sum, ih, sum_range_succ]
    congr 1
    by_cases h : c m = 0
    · simp [h]
    · simp [h, mono_linE]

section Field

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

variable (κ) in
/-- **A tuple's enclosure on the leaf's box at bounded precision** (`encY_le`), from its numerals
`Ns` (digit size `B`, shape `shape`) and the exact value `v` at the vertex `σ`: the floored lower
bounds `T` of its coefficients at the scale `2^s` with their error count `e` (`Lay.truncIE`), and
`⌊lowZ v / 2^s⌋ + T(y) - T(σ) - e ∑ᵢ dᵢ (1 - σᵢ yᵢ)` on `[-1, 1]^n`: the floors' errors are
charged to the distances from the vertex, where they vanish. -/
def encY (shape : List ℕ) (B s : ℕ) (σ : ℕ → ℤ) (Ns : List ℕ) (v : List ℤ) : SPoly ℤ :=
  let Te := Lay.truncIE B s (2 ^ (B - 1)) (ExactBasis.dim κ) (ExactBasis.apx κ) shape 0
    (slots shape) Ns
  let c0 := Lay.lowZ (ExactBasis.dim κ) (ExactBasis.apx κ) v / 2 ^ s -
    SPoly.run (fun c : ℤ ↦ c) σ Te.1 -
      Te.2 * ((List.range shape.length).map fun i ↦ (Lay.deg shape i : ℤ)).sum
  (c0, []) :: (Te.1 ++ linT (fun i ↦ Te.2 * Lay.deg shape i * σ i) shape.length)

theorem sum_range_map_int (f : ℕ → ℤ) (m : ℕ) :
    ((List.range m).map f).sum = ∑ i ∈ range m, f i := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

/-- The value of `encY`. -/
theorem run_encY (shape : List ℕ) (B s : ℕ) (σ : ℕ → ℤ) (Ns : List ℕ) (v : List ℤ)
    (y : ℕ → ℝ) :
    SPoly.run (fun a : ℤ ↦ (a : ℝ)) y (encY κ shape B s σ Ns v) =
      ((Lay.lowZ (ExactBasis.dim κ) (ExactBasis.apx κ) v / 2 ^ s : ℤ) : ℝ) -
        ((SPoly.run (fun c : ℤ ↦ c) σ (Lay.truncIE B s (2 ^ (B - 1)) (ExactBasis.dim κ)
          (ExactBasis.apx κ) shape 0 (slots shape) Ns).1 : ℤ) : ℝ) -
        ((Lay.truncIE B s (2 ^ (B - 1)) (ExactBasis.dim κ) (ExactBasis.apx κ) shape 0
          (slots shape) Ns).2 : ℝ) * ∑ i ∈ range shape.length, (Lay.deg shape i : ℝ) +
        SPoly.run (fun a : ℤ ↦ (a : ℝ)) y (Lay.truncIE B s (2 ^ (B - 1)) (ExactBasis.dim κ)
          (ExactBasis.apx κ) shape 0 (slots shape) Ns).1 +
        ∑ i ∈ range shape.length, ((Lay.truncIE B s (2 ^ (B - 1)) (ExactBasis.dim κ)
          (ExactBasis.apx κ) shape 0 (slots shape) Ns).2 : ℝ) * Lay.deg shape i * σ i * y i := by
  rw [encY, SPoly.run_int_eq_sum, List.map_cons, List.sum_cons, List.map_append,
    List.sum_append, ← SPoly.run_int_eq_sum, ← SPoly.run_int_eq_sum, run_linT, sum_range_map_int]
  simp only [SPoly.mono, mul_one]
  push_cast
  rw [mul_sum]
  ring

/-- **A slot's floor** (`Lay.truncIE`): slot `q` of `2^K ∑_c β_c` of the numerals `Ns` (digit size
`B`) less `2^s` times its floored lower bound lies in `[0, 2^s ε_q]`, `ε_q` the slot's error count
(`Lay.errS`). -/
theorem slot_floor (B s : ℕ) (Ns : List ℕ) (q : ℕ) :
    0 ≤ 2 ^ ExactBasis.apxK κ * ∑ c ∈ range (ExactBasis.dim κ),
        ExactBasis.basis κ c * ((Lay.cf B (Ns.getD c 0) q : ℤ) : ℝ) -
      2 ^ s * ((Lay.lowF (ExactBasis.dim κ) (ExactBasis.apx κ) (2 ^ (B - 1))
        (fun c ↦ dig B (Ns.getD c 0) q) / 2 ^ s : ℤ) : ℝ) ∧
    2 ^ ExactBasis.apxK κ * ∑ c ∈ range (ExactBasis.dim κ),
        ExactBasis.basis κ c * ((Lay.cf B (Ns.getD c 0) q : ℤ) : ℝ) -
      2 ^ s * ((Lay.lowF (ExactBasis.dim κ) (ExactBasis.apx κ) (2 ^ (B - 1))
        (fun c ↦ dig B (Ns.getD c 0) q) / 2 ^ s : ℤ) : ℝ) ≤
      2 ^ s * (Lay.errS s (Lay.errF (ExactBasis.dim κ) (ExactBasis.apx κ) (2 ^ (B - 1))
        fun c ↦ dig B (Ns.getD c 0) q) : ℝ) := by
  have hcf : ∀ c, ((Lay.cf B (Ns.getD c 0) q : ℤ) : ℝ) =
      (((dig B (Ns.getD c 0) q : ℤ) - ((2 ^ (B - 1) : ℕ) : ℤ) : ℤ) : ℝ) := by
    intro c
    simp [Lay.cf]
  have h1 := Lay.lowF_le (κ := κ) (2 ^ (B - 1)) fun c ↦ dig B (Ns.getD c 0) q
  have h2 := Lay.le_lowF_add (κ := κ) (2 ^ (B - 1)) fun c ↦ dig B (Ns.getD c 0) q
  set lo := Lay.lowF (ExactBasis.dim κ) (ExactBasis.apx κ) (2 ^ (B - 1))
    (fun c ↦ dig B (Ns.getD c 0) q) with hlo
  have hpq : 2 ^ ExactBasis.apxK κ * ∑ c ∈ range (ExactBasis.dim κ),
      ExactBasis.basis κ c * ((Lay.cf B (Ns.getD c 0) q : ℤ) : ℝ) =
      2 ^ ExactBasis.apxK κ * ∑ c ∈ range (ExactBasis.dim κ),
        ExactBasis.basis κ c *
          (((dig B (Ns.getD c 0) q : ℤ) - ((2 ^ (B - 1) : ℕ) : ℤ) : ℤ) : ℝ) := by
    simp only [hcf]
  have hf1 : lo / 2 ^ s * 2 ^ s ≤ lo := Int.ediv_mul_le _ (by positivity)
  have hf2 : lo < lo / 2 ^ s * 2 ^ s + 2 ^ s := by
    have := Int.emod_lt_of_pos lo (show (0 : ℤ) < 2 ^ s by positivity)
    have := Int.emod_add_ediv_mul lo (2 ^ s)
    linarith
  have hf1' : (2 : ℝ) ^ s * ((lo / 2 ^ s : ℤ) : ℝ) ≤ lo := by
    have := (Int.cast_le (R := ℝ)).mpr hf1
    push_cast at this
    linarith
  have hf2' : (lo : ℝ) < 2 ^ s * ((lo / 2 ^ s : ℤ) : ℝ) + 2 ^ s := by
    have := (Int.cast_lt (R := ℝ)).mpr hf2
    push_cast at this
    linarith
  have he2 := Lay.two_mul_le_errS s (Lay.errF (ExactBasis.dim κ) (ExactBasis.apx κ)
    (2 ^ (B - 1)) fun c ↦ dig B (Ns.getD c 0) q)
  have he2' : 2 * (Lay.errF (ExactBasis.dim κ) (ExactBasis.apx κ) (2 ^ (B - 1))
      (fun c ↦ dig B (Ns.getD c 0) q) : ℝ) + 2 ^ s ≤
      2 ^ s * (Lay.errS s (Lay.errF (ExactBasis.dim κ) (ExactBasis.apx κ) (2 ^ (B - 1))
        fun c ↦ dig B (Ns.getD c 0) q) : ℝ) := by
    exact_mod_cast he2
  rw [hpq]
  constructor <;> [linarith; linarith]

/-- **The enclosure on the leaf's box is below**: on `[-1, 1]^n`, `2^s` times the enclosure is at
most `2^K` times the combination of the numerals' polynomials, where `lowZ v` is at most `2^K`
times the combination's value at the vertex `σ`. -/
theorem encY_le {shape : List ℕ} {B s : ℕ} {σ : ℕ → ℤ} (hσ : ∀ i, σ i = 1 ∨ σ i = -1)
    {Ns : List ℕ} (hN : ∀ c, Ns.getD c 0 < 2 ^ (B * slots shape)) {v : List ℤ}
    (hv : (Lay.lowZ (ExactBasis.dim κ) (ExactBasis.apx κ) v : ℝ) ≤
      2 ^ ExactBasis.apxK κ * ∑ c ∈ range (ExactBasis.dim κ),
        ExactBasis.basis κ c * Lay.pv shape (Lay.cf B (Ns.getD c 0)) fun i ↦ (σ i : ℝ))
    {y : ℕ → ℝ} (hy : ∀ i, |y i| ≤ 1) :
    2 ^ s * SPoly.run (fun a : ℤ ↦ (a : ℝ)) y (encY κ shape B s σ Ns v) ≤
      2 ^ ExactBasis.apxK κ * ∑ c ∈ range (ExactBasis.dim κ),
        ExactBasis.basis κ c * Lay.pv shape (Lay.cf B (Ns.getD c 0)) y := by
  rw [run_encY]
  -- the floored lower bounds `t q`, the errors `p q - 2^s t q` and their counts `eq q`
  set t : ℕ → ℤ := fun q ↦ Lay.lowF (ExactBasis.dim κ) (ExactBasis.apx κ) (2 ^ (B - 1))
    (fun c ↦ dig B (Ns.getD c 0) q) / 2 ^ s with ht
  set p : ℕ → ℝ := fun q ↦ 2 ^ ExactBasis.apxK κ * ∑ c ∈ range (ExactBasis.dim κ),
    ExactBasis.basis κ c * ((Lay.cf B (Ns.getD c 0) q : ℤ) : ℝ) with hp
  set eq : ℕ → ℕ := fun q ↦ Lay.errS s (Lay.errF (ExactBasis.dim κ) (ExactBasis.apx κ)
    (2 ^ (B - 1)) fun c ↦ dig B (Ns.getD c 0) q) with heqd
  set σr : ℕ → ℝ := fun i ↦ (σ i : ℝ) with hσr
  have hrunT : ∀ u : ℕ → ℝ, SPoly.run (fun a : ℤ ↦ (a : ℝ)) u (Lay.truncIE B s (2 ^ (B - 1))
      (ExactBasis.dim κ) (ExactBasis.apx κ) shape 0 (slots shape) Ns).1 =
        ∑ q ∈ range (slots shape), (t q : ℝ) * Lay.mono shape q u := by
    intro u
    rw [Lay.truncIE_fst, Lay.run_truncI _ _ _ _ _ _ _ _ _ _ hN]
    simp only [zero_add, t]
  have he : ((Lay.truncIE B s (2 ^ (B - 1)) (ExactBasis.dim κ) (ExactBasis.apx κ) shape 0
      (slots shape) Ns).2 : ℝ) = ∑ q ∈ range (slots shape), (eq q : ℝ) := by
    rw [Lay.truncIE_snd _ _ _ _ _ _ _ _ _ hN]
    push_cast
    rfl
  have hTσ : ((SPoly.run (fun c : ℤ ↦ c) σ (Lay.truncIE B s (2 ^ (B - 1)) (ExactBasis.dim κ)
      (ExactBasis.apx κ) shape 0 (slots shape) Ns).1 : ℤ) : ℝ) =
        ∑ q ∈ range (slots shape), (t q : ℝ) * Lay.mono shape q σr := by
    rw [SPoly.map_run (isArith_intCast ℝ), ← hrunT]
    rfl
  rw [hTσ, hrunT, he]
  generalize (Lay.truncIE B s (2 ^ (B - 1)) (ExactBasis.dim κ) (ExactBasis.apx κ) shape 0
    (slots shape) Ns) = Te
  have hδ : ∀ q, 0 ≤ p q - 2 ^ s * t q ∧ p q - 2 ^ s * t q ≤ 2 ^ s * eq q :=
    fun q ↦ slot_floor (κ := κ) B s Ns q
  -- the combination as a slot polynomial
  have hP : ∀ u : ℕ → ℝ, 2 ^ ExactBasis.apxK κ * ∑ c ∈ range (ExactBasis.dim κ),
      ExactBasis.basis κ c * Lay.pv shape (Lay.cf B (Ns.getD c 0)) u =
        ∑ q ∈ range (slots shape), p q * Lay.mono shape q u := by
    intro u
    unfold Lay.pv
    simp only [mul_sum, sum_mul, p]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring
  have hσ1 : ∀ i, |σr i| ≤ 1 := fun i ↦ by rcases hσ i with h | h <;> simp [σr, h]
  have hdist : ∀ i, |y i - σr i| = 1 - σr i * y i := by
    intro i
    have := abs_le.mp (hy i)
    rcases hσ i with h | h <;> simp only [σr, h] <;> push_cast
    · rw [abs_sub_comm, abs_of_nonneg (by linarith)]; ring
    · rw [show y i - -1 = y i + 1 by ring, abs_of_nonneg (by linarith)]
      ring
  set W := ∑ i ∈ range shape.length, (Lay.deg shape i : ℝ) * (1 - σr i * y i) with hW
  have hmono : ∀ q, |Lay.mono shape q y - Lay.mono shape q σr| ≤ W := by
    intro q
    refine (Lay.abs_mono_sub_le shape q hy hσ1).trans (le_of_eq ?_)
    exact sum_congr rfl fun i _ ↦ by rw [hdist]
  have herr : -(2 ^ s * (∑ q ∈ range (slots shape), (eq q : ℝ)) * W) ≤
      ∑ q ∈ range (slots shape), (p q - 2 ^ s * t q) *
        (Lay.mono shape q y - Lay.mono shape q σr) := by
    have hsum : ∑ q ∈ range (slots shape), 2 ^ s * (eq q : ℝ) * W =
        2 ^ s * (∑ q ∈ range (slots shape), (eq q : ℝ)) * W := by
      rw [← sum_mul, ← mul_sum]
    have : |∑ q ∈ range (slots shape), (p q - 2 ^ s * t q) *
        (Lay.mono shape q y - Lay.mono shape q σr)| ≤
          2 ^ s * (∑ q ∈ range (slots shape), (eq q : ℝ)) * W := by
      refine (abs_sum_le_sum_abs _ _).trans (le_of_le_of_eq (sum_le_sum fun q _ ↦ ?_) hsum)
      rw [abs_mul, abs_of_nonneg (hδ q).1]
      exact mul_le_mul (hδ q).2 (hmono q) (abs_nonneg _) (by positivity)
    linarith [neg_abs_le (∑ q ∈ range (slots shape), (p q - 2 ^ s * t q) *
      (Lay.mono shape q y - Lay.mono shape q σr))]
  have hfl : (2 : ℝ) ^ s * ((Lay.lowZ (ExactBasis.dim κ) (ExactBasis.apx κ) v / 2 ^ s : ℤ) : ℝ) ≤
      Lay.lowZ (ExactBasis.dim κ) (ExactBasis.apx κ) v := by
    have := (Int.cast_le (R := ℝ)).mpr (Int.ediv_mul_le (Lay.lowZ (ExactBasis.dim κ)
      (ExactBasis.apx κ) v) (show (2 : ℤ) ^ s ≠ 0 by positivity))
    push_cast at this
    linarith
  rw [hP]
  rw [hP] at hv
  have hlin : ∑ i ∈ range shape.length, (∑ q ∈ range (slots shape), (eq q : ℝ)) *
      Lay.deg shape i * σr i * y i =
        (∑ q ∈ range (slots shape), (eq q : ℝ)) * ∑ i ∈ range shape.length, (Lay.deg shape i : ℝ) -
          (∑ q ∈ range (slots shape), (eq q : ℝ)) * W := by
    simp only [W, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ ↦ by ring
  have hsplit : ∑ q ∈ range (slots shape), p q * Lay.mono shape q y =
      ∑ q ∈ range (slots shape), p q * Lay.mono shape q σr +
        ∑ q ∈ range (slots shape), (p q - 2 ^ s * t q) *
          (Lay.mono shape q y - Lay.mono shape q σr) +
        2 ^ s * (∑ q ∈ range (slots shape), (t q : ℝ) * Lay.mono shape q y -
          ∑ q ∈ range (slots shape), (t q : ℝ) * Lay.mono shape q σr) := by
    rw [mul_sub, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun q _ ↦ by ring
  simp only [σr] at hlin hsplit herr ⊢
  rw [hlin, hsplit]
  nlinarith

/-- Weighted terms at an integer point: `valsAt` with no widths is their value there. -/
theorem valsAt_point (shape : List ℕ) (C : List ℤ) (c : ℕ) : ∀ w : WTerms,
    (valsAt shape C [] 0 c w : ℝ) = valAt c (fun i ↦ (C.getD i 0 : ℝ)) w
  | [] => by simp [valsAt, valAt]
  | x :: w => by
    rw [valsAt, valAt, evalPk_eq_run]
    push_cast
    rw [valsAt_point shape C c w, SPoly.map_run (isArith_intCast ℝ)]
    congr 2
    congr 1
    funext i
    simp [Frame.pointW]

/-- The list of `n` zeros. -/
def zerosL (n : ℕ) : List ℤ := (List.range n).map fun _ ↦ 0

/-- The precision of `procB`'s enclosure: bits below the bound `lb` it is given (`vMax`). With
fewer bits the floors' errors, spread by the shift to the vertex, give the vertex frame positive
terms that its exact form does not have, and monomial dominance pays for them quadratically
(K_{√3/3}'s leaves 7384 and 8764, a failing tuple each: 12,720 and 10,772 at 96 bits, 1,156 and
176 from 160 bits, against 1,156 and 153 exactly). -/
def bPrecY : ℕ := 160

/-- The least size `B · slots` (bits) of a tuple's numerals at which `procB` runs before the exact
vertex frame (`procA`): on smaller numerals the exact frame costs less than the enclosure. On
K_{√3/3}'s leaves the exact frame took 0.30 s and `procB` 0.54 s at 17 Mbit (6049), and 11.6 s
against 4.4 s at 339 Mbit (8764). Any gate is sound. -/
def bMin : ℕ := 2 ^ 26

/-- Whether `procB` runs before the exact vertex frame (`bMin`). -/
def useB (B : ℕ) (shape : List ℕ) : Bool := Nat.ble bMin (B * slots shape)

/-- **The top box's tests over `ℤ`** (`topZ_sound`) on an integer polynomial `T` on the cube
`[-1, 1]^n`: `topTM` (the centred form, then the vertex test) on its numerals at the digit size of
its bound. -/
def topZ (n : ℕ) (strict : Bool) (T : SPoly ℤ) : Bool :=
  let shT := shapeMax ([T].map (SPoly.shapeS n))
  let wT : WTerms := [(1, [T])]
  let BT := Lay.digitsFor (normsAt ℤ n (zerosL n) (onesL n) wT) (Lay.apxBits ℤ)
  let m := Lay.masks BT shT
  let NT := numsAt ℤ n shT (zerosL n) (onesL n) BT wT
  decide (shT.length ≤ n) && SPoly.lenOk n T &&
    topTM ℤ m n shT BT strict wT (zerosL n) (onesL n) (NT.map (Lay.l1O BT m.ones)) NT

/-- **Soundness of the top box's tests over `ℤ`**: where `topZ` passes, `T` has the sign on the
cube. -/
theorem topZ_sound {n : ℕ} {strict : Bool} {T : SPoly ℤ} (h : topZ n strict T = true)
    {y : ℕ → ℝ} (hy : ∀ i, |y i| ≤ 1) : Sign strict (SPoly.run (fun a : ℤ ↦ (a : ℝ)) y T) := by
  simp only [topZ, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hshT, hlenT⟩, h⟩ := h
  have hfitT := fit_one (n := n) (T := [T]) (by simp [hlenT])
  rw [Lay.masks_ones, topTM_eq] at h
  have hs := topT_sound (κ := ℤ) (Lay.digitsFor_pos _ _) hshT hfitT (by simp [numsAt])
    (numsAt_spec (κ := ℤ) (Lay.digitsFor_pos _ _) hshT hfitT fun c hc ↦
      normW_lt_digitsFor hc _) h hy
  have hagree : ∀ i < n, ((zerosL n).getD i 0 : ℝ) + (onesL n).getD i 0 * y i = y i := by
    intro i hi
    simp only [zerosL, onesL, Box.getD_range_map _ _ _ hi]
    simp
  rwa [comb_congr hfitT hagree, comb_int_one] at hs

/-- The sign `∏ᵢ sᵢ^eᵢ` of the monomial with the exponents `e` at the vertex with the signs `s`
(`±1`, read alongside the exponents; `1` past the end of `s`). -/
def sgnE : List ℤ → List ℕ → ℤ
  | s :: ss, d :: e => bif d % 2 == 1 then s * sgnE ss e else sgnE ss e
  | _, _ => 1

/-- The value of an integer polynomial at the vertex with the signs `s`: `cubeZ`'s gate. -/
def atSign (s : List ℤ) (T : SPoly ℤ) : ℤ := T.foldl (fun a t ↦ a + t.1 * sgnE s t.2) 0

/-- **The top box's tests and rupert's bisection over `ℤ`** (`cubeZ_sound`) on an integer
polynomial `T` on the cube `[-1, 1]^n`, as rupert tests the enclosure of a tuple: the centred form
on `T`'s numerals (as `topZ`); where it fails and `T` has the sign at the vertex `Lay.lowSign`
where the centred linear part is smallest (`atSign`, a gate: elsewhere no test of the cube can
pass), rupert's procedure over `ℤ` on `T` (`procAW`): the vertex test on `T`'s exact vertex frame
(as `topZ`), then rupert's bisection on that frame's integer enclosure (`encI`, `Lay.bPrec` bits)
without its terms `-1` (`dropM1`: `T`'s own floors make slightly negative the coefficients that
are zero in the tuple's vertex frame), along the widths `W`, at most `depth` levels deep, and
without exact shifts (a zero of the enclosure is not one of the tuple). The vertex's signs are
read once (each reads a digit of the numerals). The tuple `i` of `nτ` labels the beat lines. -/
def cubeZ (i nτ n : ℕ) (strict : Bool) (depth : ℕ) (W : List ℤ) (T : SPoly ℤ) : Bool :=
  let shT := shapeMax ([T].map (SPoly.shapeS n))
  let wT : WTerms := [(1, [T])]
  let BT := Lay.digitsFor (normsAt ℤ n (zerosL n) (onesL n) wT) (Lay.apxBits ℤ)
  let m := Lay.masks BT shT
  let NT := numsAt ℤ n shT (zerosL n) (onesL n) BT wT
  decide (shT.length ≤ n) && SPoly.lenOk n T &&
    (Lay.boxOkM ℤ m n shT BT strict false (NT.map (Lay.l1O BT m.ones)) NT ||
      (let sL := (List.range n).map (Lay.lowSign ℤ shT BT NT)
       let v := atSign sL T
       bif strict then decide (0 < v) else decide (0 ≤ v)) &&
        procAW ℤ i nτ n shT strict depth wT (zerosL n) (onesL n) W BT NT 0 true)

/-- The labels of `cubeZ`'s beat lines change nothing. -/
theorem cubeZ_tag (i nτ n : ℕ) (strict : Bool) (depth : ℕ) (W : List ℤ) (T : SPoly ℤ) :
    cubeZ i nτ n strict depth W T = cubeZ 0 0 n strict depth W T := by
  simp only [cubeZ, procAW_tag (κ := ℤ) i nτ]

/-- **Soundness of the top box's tests and rupert's bisection over `ℤ`**: where `cubeZ` passes,
`T` has the sign on the cube (as `topZ_sound`). -/
theorem cubeZ_sound {i nτ n : ℕ} {strict : Bool} {depth : ℕ} {W : List ℤ} {T : SPoly ℤ}
    (h : cubeZ i nτ n strict depth W T = true) {y : ℕ → ℝ} (hy : ∀ i, |y i| ≤ 1) :
    Sign strict (SPoly.run (fun a : ℤ ↦ (a : ℝ)) y T) := by
  simp only [cubeZ, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hshT, hlenT⟩, h⟩ := h
  have hfitT := fit_one (n := n) (T := [T]) (by simp [hlenT])
  have hagree : ∀ i < n, ((zerosL n).getD i 0 : ℝ) + (onesL n).getD i 0 * y i = y i := by
    intro i hi
    simp only [zerosL, onesL, Box.getD_range_map _ _ _ hi]
    simp
  rw [← comb_int_one, ← comb_congr hfitT hagree]
  rcases h with h | ⟨-, h⟩
  · -- the centred form, as `topZ`
    rw [Lay.masks_ones, Lay.boxOkM_masks] at h
    exact topT_sound (κ := ℤ) (Lay.digitsFor_pos _ _) hshT hfitT (by simp [numsAt])
      (numsAt_spec (κ := ℤ) (Lay.digitsFor_pos _ _) hshT hfitT fun c hc ↦
        normW_lt_digitsFor hc _) (by rw [topT, h, Bool.true_or]) hy
  · -- the vertex test and the bisection
    exact procAW_sound hshT hfitT h hy

variable (κ) in
/-- The top box's tests (`topTM` over `ℤ`: the centred form, the vertex test) on the integer
enclosure `encY` of the numerals `Ns` (digit size `B`) on the leaf's box `[-1, 1]^n`, at `bPrecY`
bits below the bound `lb`, with the values `v` at the vertex `σ`. -/
def encTop (n : ℕ) (shape : List ℕ) (strict : Bool) (B : ℕ) (Ns : List ℕ) (lb : ℕ) (σ : ℕ → ℤ)
    (v : List ℤ) : Bool :=
  topZ n strict (encY κ shape B (ExactBasis.apxK κ + (Nat.log2 lb + 1 - bPrecY)) σ Ns v)

/-- The largest absolute coordinate of the values `v`: `procB`'s bound for its precision. -/
def vMax (v : List ℤ) : ℕ := (v.map Int.natAbs).foldr max 0

variable (κ) in
/-- **The top box at bounded precision** (`procB_sound`), as rupert tests it where the tuple's
exact value at the vertex is not `0`: that value `v` of the tuple's terms `wt` at the vertex
`Lay.lowSign` where the centred linear part is smallest (`valsAt`; the signs read once, as each
reads a digit of the numerals), then the top box's tests on the integer enclosure of the tuple's
numerals `Ns` at `bPrecY` bits below `v`'s largest coordinate (`encTop`, `vMax`). Where `v` is `0`,
rupert shifts exactly (here `procA`'s exact vertex frame). The tuple `i` of `nτ` labels the beat
line (`btop`). -/
def procB (i nτ n : ℕ) (shape : List ℕ) (strict : Bool) (wt : WTerms) (CX HX : List ℤ) (B : ℕ)
    (Ns : List ℕ) : Bool :=
  let sL := (List.range shape.length).map (Lay.lowSign κ shape B Ns)
  let σ : ℕ → ℤ := fun i ↦ sL.getD i (-1)
  let v := (List.range (ExactBasis.dim κ)).map fun c ↦ valsAt shape (vertC n CX HX σ) [] 0 c wt
  beat "btop" (fun r ↦ s!" i={i} n={nτ} ok={r}")
    (v.any (· != 0) && encTop κ n shape strict B Ns (vMax v) σ v)

/-- The labels of `procB`'s beat line change nothing. -/
theorem procB_tag (i nτ n : ℕ) (shape : List ℕ) (strict : Bool) (wt : WTerms) (CX HX : List ℤ)
    (B : ℕ) (Ns : List ℕ) :
    procB κ i nτ n shape strict wt CX HX B Ns = procB κ 0 0 n shape strict wt CX HX B Ns := by
  simp only [procB, beat_eq]

/-- **Soundness of the top box at bounded precision**: where `procB` passes on the numerals of the
tuple's terms on the leaf's frame, the tuple's combination has the sign there. -/
theorem procB_sound {i nτ n : ℕ} {shape : List ℕ} {strict : Bool} {wt : WTerms}
    {CX HX : List ℤ} {B : ℕ} {Ns : List ℕ} (hfit : Fit n shape wt)
    (hlen : Ns.length = ExactBasis.dim κ)
    (hNs : ∀ c < ExactBasis.dim κ, Lay.Inv B shape (Ns.getD c 0) ∧
      ∀ y : ℕ → ℝ, Lay.pv shape (Lay.cf B (Ns.getD c 0)) y =
        valAt c (fun i ↦ (CX.getD i 0 : ℝ) + HX.getD i 0 * y i) wt)
    (h : procB κ i nτ n shape strict wt CX HX B Ns = true) {y : ℕ → ℝ}
    (hy : ∀ i, |y i| ≤ 1) :
    Sign strict (comb (κ := κ) wt fun i ↦ (CX.getD i 0 : ℝ) + HX.getD i 0 * y i) := by
  simp only [procB, encTop, Bool.and_eq_true, beat_eq] at h
  set σ : ℕ → ℤ := fun i ↦ ((List.range shape.length).map (Lay.lowSign κ shape B Ns)).getD i (-1)
    with hσdef
  have hσ : ∀ i, σ i = 1 ∨ σ i = -1 := by
    intro i
    by_cases hi : i < shape.length
    · simp only [σ, Box.getD_range_map _ _ _ hi]
      exact Lay.lowSign_cases shape B Ns i
    · right
      simp only [σ]
      exact List.getD_eq_default _ _ (by simpa using hi)
  set v := (List.range (ExactBasis.dim κ)).map fun c ↦ valsAt shape (vertC n CX HX σ) [] 0 c wt
    with hvdef
  set s := ExactBasis.apxK κ + (Nat.log2 (vMax v) + 1 - bPrecY)
  obtain ⟨-, h⟩ := h
  have hN : ∀ c, Ns.getD c 0 < 2 ^ (B * slots shape) := by
    intro c
    by_cases hc : c < ExactBasis.dim κ
    · exact (hNs c hc).1.1
    · rw [List.getD_eq_default _ _ (by omega)]
      positivity
  -- the exact value at the vertex
  have hv : (Lay.lowZ (ExactBasis.dim κ) (ExactBasis.apx κ) v : ℝ) ≤
      2 ^ ExactBasis.apxK κ * ∑ c ∈ range (ExactBasis.dim κ),
        ExactBasis.basis κ c * Lay.pv shape (Lay.cf B (Ns.getD c 0)) fun i ↦ (σ i : ℝ) := by
    refine (Lay.lowZ_le (κ := κ) v).trans (le_of_eq ?_)
    congr 1
    refine sum_congr rfl fun c hc ↦ ?_
    have hc := mem_range.mp hc
    rw [(hNs c hc).2, show v.getD c 0 = valsAt shape (vertC n CX HX σ) [] 0 c wt by
      rw [hvdef, Box.getD_range_map _ _ _ hc], valsAt_point]
    congr 1
    exact valAt_congr (fun j hj ↦ by
      simp only [vertC, Box.getD_range_map _ _ _ hj]
      push_cast
      ring) hfit
  -- the enclosure's tests at the top box, and its sign implies the tuple's on `[-1, 1]^n`
  have hs := topZ_sound h hy
  have hle := encY_le (κ := κ) (s := s) hσ hN hv hy
  have heq : ∑ c ∈ range (ExactBasis.dim κ),
      ExactBasis.basis κ c * Lay.pv shape (Lay.cf B (Ns.getD c 0)) y =
        comb (κ := κ) wt fun i ↦ (CX.getD i 0 : ℝ) + HX.getD i 0 * y i := by
    unfold comb
    exact sum_congr rfl fun c hc ↦ by rw [(hNs c (mem_range.mp hc)).2]
  rw [heq] at hle
  exact sign_of_mul (by positivity) (sign_of_le (sign_mul_of_pos (by positivity) hs) hle)

/-! ### The top box from truncations at bounded precision -/

variable (κ) in
/-- **A polynomial's enclosure on the cube at bounded precision** (`encP_le`): from numerals `Ns`
(digit size `B`), the floored lower bounds `T` of the coefficients of `2^K ∑_c β_c` of their
polynomials at the scale `2^s` with their error count `ε` (`Lay.truncIE`), as `T(y) - ε`. Unlike
`encY` it has no vertex: its error is one constant on the cube. -/
def encP (shape : List ℕ) (B s : ℕ) (Ns : List ℕ) : SPoly ℤ :=
  let Te := Lay.truncIE B s (2 ^ (B - 1)) (ExactBasis.dim κ) (ExactBasis.apx κ) shape 0
    (slots shape) Ns
  (-(Te.2 : ℤ), []) :: Te.1

/-- **The enclosure on the cube is below**: on `[-1, 1]^n`, `2^s` times `encP` is at most `2^K`
times the combination of the numerals' polynomials. -/
theorem encP_le {shape : List ℕ} {B s : ℕ} {Ns : List ℕ}
    (hN : ∀ c, Ns.getD c 0 < 2 ^ (B * slots shape)) {y : ℕ → ℝ} (hy : ∀ i, |y i| ≤ 1) :
    2 ^ s * SPoly.run (fun a : ℤ ↦ (a : ℝ)) y (encP κ shape B s Ns) ≤
      2 ^ ExactBasis.apxK κ * ∑ c ∈ range (ExactBasis.dim κ),
        ExactBasis.basis κ c * Lay.pv shape (Lay.cf B (Ns.getD c 0)) y := by
  set t : ℕ → ℤ := fun q ↦ Lay.lowF (ExactBasis.dim κ) (ExactBasis.apx κ) (2 ^ (B - 1))
    (fun c ↦ dig B (Ns.getD c 0) q) / 2 ^ s with ht
  set p : ℕ → ℝ := fun q ↦ 2 ^ ExactBasis.apxK κ * ∑ c ∈ range (ExactBasis.dim κ),
    ExactBasis.basis κ c * ((Lay.cf B (Ns.getD c 0) q : ℤ) : ℝ) with hp
  set eq : ℕ → ℕ := fun q ↦ Lay.errS s (Lay.errF (ExactBasis.dim κ) (ExactBasis.apx κ)
    (2 ^ (B - 1)) fun c ↦ dig B (Ns.getD c 0) q) with heqd
  have hrunT : SPoly.run (fun a : ℤ ↦ (a : ℝ)) y (Lay.truncIE B s (2 ^ (B - 1))
      (ExactBasis.dim κ) (ExactBasis.apx κ) shape 0 (slots shape) Ns).1 =
        ∑ q ∈ range (slots shape), (t q : ℝ) * Lay.mono shape q y := by
    rw [Lay.truncIE_fst, Lay.run_truncI _ _ _ _ _ _ _ _ _ _ hN]
    simp only [zero_add, t]
  have he : ((Lay.truncIE B s (2 ^ (B - 1)) (ExactBasis.dim κ) (ExactBasis.apx κ) shape 0
      (slots shape) Ns).2 : ℝ) = ∑ q ∈ range (slots shape), (eq q : ℝ) := by
    rw [Lay.truncIE_snd _ _ _ _ _ _ _ _ _ hN]
    push_cast
    rfl
  have hrun : SPoly.run (fun a : ℤ ↦ (a : ℝ)) y (encP κ shape B s Ns) =
      -((Lay.truncIE B s (2 ^ (B - 1)) (ExactBasis.dim κ) (ExactBasis.apx κ) shape 0
        (slots shape) Ns).2 : ℝ) + SPoly.run (fun a : ℤ ↦ (a : ℝ)) y (Lay.truncIE B s
          (2 ^ (B - 1)) (ExactBasis.dim κ) (ExactBasis.apx κ) shape 0 (slots shape) Ns).1 := by
    rw [encP, SPoly.run_int_eq_sum, List.map_cons, List.sum_cons, ← SPoly.run_int_eq_sum]
    simp only [SPoly.mono, mul_one]
    push_cast
    rfl
  have hP : 2 ^ ExactBasis.apxK κ * ∑ c ∈ range (ExactBasis.dim κ),
      ExactBasis.basis κ c * Lay.pv shape (Lay.cf B (Ns.getD c 0)) y =
        ∑ q ∈ range (slots shape), p q * Lay.mono shape q y := by
    unfold Lay.pv
    simp only [mul_sum, sum_mul, p]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring
  have hterm : ∀ q, 0 ≤ (p q - 2 ^ s * t q) * Lay.mono shape q y + 2 ^ s * eq q := by
    intro q
    obtain ⟨h0, h1⟩ := slot_floor (κ := κ) B s Ns q
    have hm := abs_le.mp (Lay.abs_mono_le (sh := shape) hy q)
    have h3 : -(p q - 2 ^ s * t q) ≤ (p q - 2 ^ s * t q) * Lay.mono shape q y := by nlinarith
    have h4 : p q - 2 ^ s * t q ≤ 2 ^ s * eq q := h1
    linarith
  have hsum := sum_nonneg fun q (_ : q ∈ range (slots shape)) ↦ hterm q
  have key : ∑ q ∈ range (slots shape), ((p q - 2 ^ s * t q) * Lay.mono shape q y +
      2 ^ s * eq q) = ∑ q ∈ range (slots shape), p q * Lay.mono shape q y -
        2 ^ s * (-(∑ q ∈ range (slots shape), (eq q : ℝ)) +
          ∑ q ∈ range (slots shape), (t q : ℝ) * Lay.mono shape q y) := by
    rw [mul_add, mul_neg, mul_sum, mul_sum, ← sum_neg_distrib, ← sum_add_distrib,
      ← sum_sub_distrib]
    exact sum_congr rfl fun q _ ↦ by ring
  rw [hrun, hrunT, he, hP]
  linarith

variable (κ) in
/-- **The top box from truncations at bounded precision** (`fTop_sound`): the sums of a tuple's
truncated terms as the truncated test builds them (`Lay.tSums`, with its room test `Lay.tL1`),
their enclosure on the cube (`encP`) at `bPrecY` bits below the largest bound of the sums, and the
top box's tests and rupert's bisection on it over `ℤ` (`cubeZ`, along the leaf's widths `W`, at
most `depth` levels deep). The tuple `i` of `nτ` labels the beat lines. -/
def fTop (i nτ n : ℕ) (shape : List ℕ) (strict : Bool) (depth : ℕ) (W : List ℤ) (B : ℕ)
    (tv : ℕ → ℕ → ℤ) (tl : ℕ → ℕ → ℕ) (ρ : ℕ → ℕ) (τ : List (ℕ × ℤ)) : Bool :=
  let ls := (List.range (ExactBasis.dim κ)).map (Lay.tL1 κ tl ρ τ)
  ls.all (fun l ↦ decide (l < 2 ^ (B - 1))) &&
    cubeZ i nτ n strict depth W (encP κ shape B
      (ExactBasis.apxK κ + (Nat.log2 (ls.foldr max 0) + 1 - bPrecY)) (Lay.tSums κ shape B tv ρ τ))

/-- The labels of `fTop`'s beat lines change nothing. -/
theorem fTop_tag (i nτ n : ℕ) (shape : List ℕ) (strict : Bool) (depth : ℕ) (W : List ℤ) (B : ℕ)
    (tv : ℕ → ℕ → ℤ) (tl : ℕ → ℕ → ℕ) (ρ : ℕ → ℕ) (τ : List (ℕ × ℤ)) :
    fTop κ i nτ n shape strict depth W B tv tl ρ τ =
      fTop κ 0 0 n shape strict depth W B tv tl ρ τ := by
  simp only [fTop, cubeZ_tag i nτ]

theorem fTop_congr (i nτ n : ℕ) (shape : List ℕ) (strict : Bool) (depth : ℕ) (W : List ℤ) (B : ℕ)
    (tv : ℕ → ℕ → ℤ) (tl : ℕ → ℕ → ℕ) (ρ : ℕ → ℕ) {τ' τ : List (ℕ × ℤ)}
    (h : List.Forall₂ (fun x' x ↦ x'.2 = x.2 ∧ tv x'.1 = tv x.1 ∧ tl x'.1 = tl x.1 ∧
      ρ x'.1 = ρ x.1) τ' τ) :
    fTop κ i nτ n shape strict depth W B tv tl ρ τ' =
      fTop κ i nτ n shape strict depth W B tv tl ρ τ := by
  have h₁ : (τ'.map fun jw ↦ jw.2.natAbs * ρ jw.1) = τ.map fun jw ↦ jw.2.natAbs * ρ jw.1 :=
    Lay.map_eq_of_forall₂ (fun _ _ h ↦ by rw [h.1, h.2.2.2]) h
  have h₂ : ∀ c, (τ'.map fun jw ↦ jw.2.natAbs * tl jw.1 c) =
      τ.map fun jw ↦ jw.2.natAbs * tl jw.1 c :=
    fun c ↦ Lay.map_eq_of_forall₂ (fun _ _ h ↦ by rw [h.1, h.2.2.1]) h
  have h₃ : ∀ c, (τ'.map fun jw ↦ jw.2 * tv jw.1 c) = τ.map fun jw ↦ jw.2 * tv jw.1 c :=
    fun c ↦ Lay.map_eq_of_forall₂ (fun _ _ h ↦ by rw [h.1, h.2.1]) h
  have h₄ : Lay.tL1 κ tl ρ τ' = Lay.tL1 κ tl ρ τ := funext fun c ↦ by simp only [Lay.tL1, h₁, h₂]
  simp only [fTop, h₄, Lay.tSums, h₁, h₃]

/-- **Soundness of the top box from truncations.** For each term `j` of nonzero weight and each
coordinate `c`, let `tv j c` be the signed numeral of digits `td j c`, with absolute sum at most
`tl j c`, whose polynomial times `2^s` is within `ρ j 2^s` of `P j c` on the cube. If `fTop` passes,
then `∑_c β_c ∑_j w_j P j c` has the sign on the cube. -/
theorem fTop_sound {i nτ n : ℕ} {shape : List ℕ} {strict : Bool} {depth : ℕ} {W : List ℤ}
    {B : ℕ} {tv : ℕ → ℕ → ℤ} {tl : ℕ → ℕ → ℕ} {ρ : ℕ → ℕ} {τ : List (ℕ × ℤ)} (hB : 0 < B) (s : ℕ)
    (td : ℕ → ℕ → ℕ → ℤ) (P : ℕ → ℕ → (ℕ → ℝ) → ℝ)
    (ht : ∀ jw ∈ τ, jw.2 ≠ 0 → ∀ c < ExactBasis.dim κ,
      tv jw.1 c = Num.snum B (td jw.1 c) (slots shape) ∧ Lay.l1 shape (td jw.1 c) ≤ tl jw.1 c ∧
      ∀ y : ℕ → ℝ, (∀ i, |y i| ≤ 1) →
        |P jw.1 c y - 2 ^ s * Lay.pv shape (td jw.1 c) y| ≤ (ρ jw.1 : ℝ) * 2 ^ s)
    (h : fTop κ i nτ n shape strict depth W B tv tl ρ τ = true) {y : ℕ → ℝ}
    (hy : ∀ i, |y i| ≤ 1) :
    Sign strict (∑ c ∈ range (ExactBasis.dim κ),
      ExactBasis.basis κ c * (τ.map fun jw ↦ (jw.2 : ℝ) * P jw.1 c y).sum) := by
  simp only [fTop, Bool.and_eq_true, List.all_eq_true, List.mem_map, List.mem_range,
    decide_eq_true_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h
  obtain ⟨hb, h⟩ := h
  obtain ⟨hinv, hlen, hle⟩ := Lay.tSums_spec (κ := κ) hB s td P ht hb
  have hN : ∀ c, (Lay.tSums κ shape B tv ρ τ).getD c 0 < 2 ^ (B * slots shape) := by
    intro c
    by_cases hc : c < (Lay.tSums κ shape B tv ρ τ).length
    · exact (hinv _ (Lay.getD_mem hc)).1
    · rw [List.getD_eq_default _ _ (by omega)]
      positivity
  have h₁ := sign_of_le (sign_mul_of_pos (by positivity) (cubeZ_sound h hy))
    (encP_le (κ := κ) hN hy)
  exact sign_of_le (sign_mul_of_pos (by positivity) (sign_of_mul (by positivity) h₁)) (hle y hy)

end Field

end Pull

end Nieuwland.Check
