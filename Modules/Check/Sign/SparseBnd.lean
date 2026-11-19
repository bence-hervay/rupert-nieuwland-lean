import Modules.Check.Sign.SparseBox

/-!
# rupert's procedure on a one-sided enclosure

rupert's exact check of a box (`nonneg_exact_rec`, `code/src/proof/regional.rs`) shifts one dense
interval enclosure of the tuple's polynomial to every box of its bisection, in `f64`, and computes
exactly only the value at a vertex, and the shifted polynomial where that value is `0` (within a
work budget, `EXACT_SHIFT_WORK`). Here the enclosure is one-sided and has integer coefficients, and
exact arithmetic runs on its small numbers (`procA`):

* the leaf's exact vertex frame at the vertex `σ` where the centred linear part is smallest
  (`X = Cₓ + σ Hₓ - 2 σ Hₓ u`, `u ∈ [0, 1]^n`; `vertC`, `vertH`), from the tuple's sparse terms,
  and its vertex test (`Lay.vdTest`, as `vertT`);
* its coefficients `p_q = ∑_c β_c a_{c,q}` bounded below by the integers
  `m_q = ∑_c (A_c a_{c,q} - E_c |a_{c,q}|) ≤ 2^K p_q`, from the field's approximations `A_c` of
  `2^K β_c` with error bounds `E_c` (`ExactBasis.apx`), and floored to multiples of `2^s`, `s` some
  `Lay.bPrec` bits below the largest absolute coefficient sum (`Lay.truncI`): on `[0, 1]^n`, where
  every monomial is nonnegative, `2^s` times the integer polynomial of the quotients is at most
  `2^K` times the tuple's (`Lay.truncI_le`). Coefficients that are `0` stay `0`: a face of zeros
  through the vertex is a face of zeros of the enclosure;
* rupert's bisection (`bisect`) of `[0, 1]^n` with the enclosure's box tests (`boxA`: `topT` over
  `ℤ` on each box's frame by Horner's rule from the enclosure's terms, exact on its numbers, whose
  digits grow by its degree per level);
* where they fail on a box and the tuple's exact value at the box's vertex is `0`, the exact vertex
  frame of the box from the tuple's sparse terms (`vertT`), as rupert's exact shift, each charged
  rupert's work bound (`xCost`) against rupert's budget per tuple (`xWork`).

Soundness (`procA_sound`): the tuple's combination has the sign on the leaf's box, as `vertT_sound`
concludes. Neither the budget nor the choices of vertices and of the precision need correctness.
-/

open Finset

namespace Nieuwland.Check

open DPoly

namespace Lay

open Num

/-! ### Directed truncation into sparse terms -/

/-- The exponents of slot `q` of the shape `sh`, as an exponent list. -/
def exps (sh : List ℕ) (q : ℕ) : List ℕ := (List.range sh.length).map fun i ↦ ex sh i q

/-- The exponents of slot `q` in the shape `sh` with the slots of `sh`, from the last variable
(`exps_eq_expsS`). -/
def expsG (q : ℕ) : List ℕ → List ℕ × ℕ
  | [] => ([], 1)
  | a :: sh =>
    let r := expsG q sh
    ((q / r.2 % (a + 1)) :: r.1, (a + 1) * r.2)

/-- `exps` as compiled code runs it (`exps_eq_expsS`): each stride once, not once a variable. -/
def expsS (sh : List ℕ) (q : ℕ) : List ℕ := (expsG q sh).1

theorem expsG_snd (q : ℕ) : ∀ sh : List ℕ, (expsG q sh).2 = slots sh
  | [] => rfl
  | a :: sh => by simp only [expsG, slots, expsG_snd q sh]

theorem exps_cons (a : ℕ) (sh : List ℕ) (q : ℕ) :
    exps (a :: sh) q = (q / slots sh % (a + 1)) :: exps sh q := by
  rw [exps, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, exps]
  rfl

/-- **Exponents computed directly.** -/
@[csimp] theorem exps_eq_expsS : @exps = @expsS := by
  funext sh q
  induction sh with
  | nil => rfl
  | cons a sh ih => simp only [exps_cons, ih, expsS, expsG, expsG_snd]

/-- The integer lower bound `∑_c (A_c d_c - E_c |d_c|)` of `2^K ∑_c β_c d_c` for the digits
`d_c = N_c - h` of the numerals `Ns` (`c < D`), given approximations `A_c` of `2^K β_c` with error
bounds `E_c` as pairs `(A_c, E_c)` (as `ExactBasis.apx`; `lowF_le`). -/
def lowD (D : ℕ) (A : List (ℤ × ℕ)) (h : ℕ) (Ns : List ℕ) : ℤ :=
  ((List.range D).map fun c ↦
    let d : ℤ := (Ns.getD c 0 : ℤ) - h
    (A.getD c (0, 0)).1 * d - ((A.getD c (0, 0)).2 : ℤ) * (d.natAbs : ℤ)).sum

/-- The sparse terms of the slots `q₀, …, q₀ + L - 1` of the numerals `Ns` (digit size `B`, their
digits `0` the slot `q₀`): each slot's lower bound `lowD` of its digits, floored to a multiple of
`2^s` and divided by it, where not `0`, with the exponents of its slot in the shape `sh`
(`run_truncI`); by halves. -/
def truncI (B s h D : ℕ) (A : List (ℤ × ℕ)) (sh : List ℕ) (q₀ L : ℕ) (Ns : List ℕ) : SPoly ℤ :=
  if _hL : L ≤ 1 then
    bif L == 0 then [] else
      let t := lowD D A h Ns >>> s
      bif t == 0 then [] else [(t, exps sh q₀)]
  else
    truncI B s h D A sh q₀ (L / 2)
        (Ns.map fun N ↦ N - ((N >>> (B * (L / 2))) <<< (B * (L / 2)))) ++
      truncI B s h D A sh (q₀ + L / 2) (L - L / 2) (Ns.map fun N ↦ N >>> (B * (L / 2)))
termination_by L
decreasing_by all_goals omega

/-- The precision of the enclosure: bits below the largest absolute coefficient sum of the exact
vertex frame. -/
def bPrec : ℕ := 64

theorem mono_list (u : ℕ → ℝ) : ∀ (e : List ℕ) (j : ℕ),
    SPoly.mono (1 : ℝ) u j e = ∏ i ∈ range e.length, u (j + i) ^ e.getD i 0
  | [], j => by simp [SPoly.mono]
  | d :: e, j => by
    rw [SPoly.mono_consR, mono_list u e (j + 1), List.length_cons, prod_range_succ', mul_comm]
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    congr 1
    refine prod_congr rfl fun i _ ↦ ?_
    rw [show j + (i + 1) = j + 1 + i by omega]

/-- The monomial of the exponent list of a slot is the slot's monomial. -/
theorem mono_exps (sh : List ℕ) (q : ℕ) (u : ℕ → ℝ) :
    SPoly.mono (1 : ℝ) u 0 (exps sh q) = mono sh q u := by
  rw [mono_list, exps, List.length_map, List.length_range, mono]
  refine prod_congr rfl fun i hi ↦ ?_
  rw [zero_add, Box.getD_range_map _ _ _ (mem_range.mp hi)]

theorem run_append_int (u : ℕ → ℝ) (p q : SPoly ℤ) :
    SPoly.run (fun c : ℤ ↦ (c : ℝ)) u (p ++ q) =
      SPoly.run (fun c : ℤ ↦ (c : ℝ)) u p + SPoly.run (fun c : ℤ ↦ (c : ℝ)) u q := by
  rw [SPoly.run_int_eq_sum, SPoly.run_int_eq_sum, SPoly.run_int_eq_sum, List.map_append,
    List.sum_append]

/-- `lowD` with the digits read by a function (in proofs). -/
def lowF (D : ℕ) (A : List (ℤ × ℕ)) (h : ℕ) (d : ℕ → ℕ) : ℤ :=
  ∑ c ∈ range D, ((A.getD c (0, 0)).1 * ((d c : ℤ) - h) -
    ((A.getD c (0, 0)).2 : ℤ) * ((((d c : ℤ) - h).natAbs : ℕ) : ℤ))

theorem lowD_eq (D : ℕ) (A : List (ℤ × ℕ)) (h : ℕ) (Ns : List ℕ) :
    lowD D A h Ns = lowF D A h fun c ↦ Ns.getD c 0 := by
  unfold lowD lowF
  induction D with
  | zero => simp
  | succ D ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]
    simp

/-- **The terms of `truncI`** are the floored lower bounds of the digits on the monomials of their
slots. -/
theorem run_truncI (B s h D : ℕ) (A : List (ℤ × ℕ)) (sh : List ℕ) (u : ℕ → ℝ) :
    ∀ (L q₀ : ℕ) (Ns : List ℕ), (∀ c, Ns.getD c 0 < 2 ^ (B * L)) →
      SPoly.run (fun c : ℤ ↦ (c : ℝ)) u (truncI B s h D A sh q₀ L Ns) =
        ∑ q ∈ range L, ((lowF D A h (fun c ↦ dig B (Ns.getD c 0) q) / 2 ^ s : ℤ) : ℝ) *
          mono sh (q₀ + q) u := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro q₀ Ns hN
    rw [truncI]
    split_ifs with hL
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hL with rfl | rfl
      · simp [SPoly.run, Exact.ofInt]
      · have h0 : ∀ c, dig B (Ns.getD c 0) 0 = Ns.getD c 0 := fun c ↦ by
          have h1 : Ns.getD c 0 < 2 ^ B := by simpa using hN c
          rw [dig, Nat.mul_zero, pow_zero, Nat.div_one, Nat.mod_eq_of_lt h1]
        simp only [show ((1 : ℕ) == 0) = false from rfl, Bool.cond_false,
          Int.shiftRight_eq_div_pow, Nat.cast_pow, Nat.cast_ofNat, sum_range_one, h0, add_zero,
          lowD_eq]
        by_cases hd : lowF D A h (fun c ↦ Ns.getD c 0) / 2 ^ s = 0
        · have hd' : (lowF D A h (fun c ↦ Ns.getD c 0) / 2 ^ s == 0) = true := by rw [hd]; rfl
          rw [hd', Bool.cond_true, hd]
          simp [SPoly.run, Exact.ofInt]
        · have hd' : (lowF D A h (fun c ↦ Ns.getD c 0) / 2 ^ s == 0) = false := beq_false_of_ne hd
          rw [hd', Bool.cond_false]
          simp only [SPoly.run, Exact.ofInt, Int.cast_one, Int.cast_zero, add_zero]
          rw [mono_exps]
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
      rw [run_append_int, ih (L / 2) hkL _ _ (fun c ↦ by rw [hlo]; exact Nat.mod_lt _ hP),
        ih (L - L / 2) (by omega) _ _ (fun c ↦ by rw [hhi]; exact hhi' c)]
      conv_rhs => rw [show L = L / 2 + (L - L / 2) by omega, sum_range_add]
      congr 1
      · refine sum_congr rfl fun q hq ↦ ?_
        simp only [hlo, dig_mod_two_pow _ (mem_range.mp hq)]
      · refine sum_congr rfl fun q _ ↦ ?_
        simp only [hhi, dig_div_two_pow, add_assoc]

section Field

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- **The lower bound of a slot**: `m = ∑_c (A_c d_c - E_c |d_c|) ≤ 2^K ∑_c β_c d_c`. -/
theorem lowF_le (h : ℕ) (d : ℕ → ℕ) :
    (lowF (ExactBasis.dim κ) (ExactBasis.apx κ) h d : ℝ) ≤
      2 ^ ExactBasis.apxK κ * ∑ c ∈ range (ExactBasis.dim κ),
        ExactBasis.basis κ c * (((d c : ℤ) - h : ℤ) : ℝ) := by
  unfold lowF
  push_cast
  rw [mul_sum]
  refine sum_le_sum fun c hc ↦ ?_
  have ha := ExactBasis.apx_sound (κ := κ) c (mem_range.mp hc)
  set A := (((ExactBasis.apx κ).getD c (0, 0)).1 : ℝ)
  set E := (((ExactBasis.apx κ).getD c (0, 0)).2 : ℝ)
  set x : ℝ := (d c : ℝ) - h
  have hb : |(2 ^ ExactBasis.apxK κ * ExactBasis.basis κ c - A) * x| ≤ E * |x| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right ha (abs_nonneg _)
  have := neg_abs_le ((2 ^ ExactBasis.apxK κ * ExactBasis.basis κ c - A) * x)
  nlinarith

/-- **The integer enclosure is below**: on `[0, 1]^n`, `2^s` times the polynomial of the floored
lower bounds of the digits is at most `2^K` times the combination of the numerals' polynomials. -/
theorem truncI_le (sh : List ℕ) (B s : ℕ) (Vs : List ℕ) {u : ℕ → ℝ}
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1) :
    2 ^ s * ∑ q ∈ range (slots sh), ((lowF (ExactBasis.dim κ) (ExactBasis.apx κ) (2 ^ (B - 1))
        (fun c ↦ dig B (Vs.getD c 0) q) / 2 ^ s : ℤ) : ℝ) * mono sh q u ≤
      2 ^ ExactBasis.apxK κ * ∑ c ∈ range (ExactBasis.dim κ),
        ExactBasis.basis κ c * pv sh (cf B (Vs.getD c 0)) u := by
  have hR : 2 ^ ExactBasis.apxK κ * ∑ c ∈ range (ExactBasis.dim κ),
        ExactBasis.basis κ c * pv sh (cf B (Vs.getD c 0)) u =
      ∑ q ∈ range (slots sh), (2 ^ ExactBasis.apxK κ * ∑ c ∈ range (ExactBasis.dim κ),
        ExactBasis.basis κ c * ((cf B (Vs.getD c 0) q : ℤ) : ℝ)) * mono sh q u := by
    unfold pv
    simp only [mul_sum, sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring
  rw [hR, mul_sum]
  refine sum_le_sum fun q _ ↦ ?_
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (mono_nonneg_unit sh q hu)
  set m := lowF (ExactBasis.dim κ) (ExactBasis.apx κ) (2 ^ (B - 1)) fun c ↦ dig B (Vs.getD c 0) q
  have h1 : m / 2 ^ s * 2 ^ s ≤ m := Int.ediv_mul_le m (by positivity)
  have h1' : (2 : ℝ) ^ s * ((m / 2 ^ s : ℤ) : ℝ) ≤ m := by
    have := (Int.cast_le (R := ℝ)).mpr h1
    push_cast at this
    linarith
  refine h1'.trans ((lowF_le (κ := κ) _ _).trans (le_of_eq ?_))
  congr 1

end Field

end Lay

theorem sign_mul_of_pos {strict : Bool} {t v : ℝ} (ht : 0 < t) (h : Sign strict v) :
    Sign strict (t * v) := by
  cases strict
  · exact mul_nonneg ht.le (show 0 ≤ v from h)
  · exact mul_pos ht (show 0 < v from h)

namespace Pull

open WTerms

section Field

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-! ### The procedure -/

/-- The centres `2^k Cₓ + Hₓ C` (over `2^k`) of the box `(C, H)` over `2^k` of the frame
`X = Cₓ + Hₓ u` in the variables `X`. -/
def frameC (n : ℕ) (CX HX C : List ℤ) (k : ℕ) : List ℤ :=
  (List.range n).map fun i ↦ 2 ^ k * CX.getD i 0 + HX.getD i 0 * C.getD i 0

/-- The half-widths `Hₓ H` (over `2^k`) of the box `(C, H)` over `2^k` of the frame `Cₓ + Hₓ u`. -/
def frameH (n : ℕ) (HX H : List ℤ) : List ℤ :=
  (List.range n).map fun i ↦ HX.getD i 0 * H.getD i 0

variable (κ) in
/-- **The one-sided integer enclosure** of the numerals `Vs` (digit size `B`, shape `shape`): each
slot's lower bound of `2^K` times its coefficient from the field's approximations, floored to a
multiple of `2^s` (`Lay.truncI`), as a sparse integer polynomial (`encI_le`). -/
def encI (shape : List ℕ) (B s : ℕ) (Vs : List ℕ) : SPoly ℤ :=
  Lay.truncI B s (2 ^ (B - 1)) (ExactBasis.dim κ) (ExactBasis.apx κ) shape 0 (slots shape) Vs

/-- rupert's work bound of an exact shift (`exact_dominance`): the slots times the sum of the
degrees plus one. -/
def xCost (n : ℕ) (shape : List ℕ) : ℕ :=
  slots shape * ((List.range n).map fun i ↦ Lay.deg shape i + 1).sum

/-- rupert's work budget of the exact shifts of one tuple (`EXACT_SHIFT_WORK`). -/
def xWork : ℕ := 2 ^ 21

variable (κ) in
/-- **The tests of a box** `(C, H)` over `2^k` of the enclosure's frame `[0, 1]^n`, with the work
`b` left (`boxA_sound`): `topT` over `ℤ` on the box's frame of the enclosure's integer terms `wT`
(shape `shT`, scaled to degree `MT`); where it fails, the tuple's terms `wt` (shape `shape`, in the
variables `X = Cₓ + Hₓ u`) have the exact value `0` at the box's vertex and the work `cost` is
left, their exact vertex frame (`vertT`, scaled to degree `M`). -/
def boxA (n : ℕ) (shT shape : List ℕ) (strict : Bool) (MT : ℕ) (wT : WTerms) (M : ℕ)
    (wt : WTerms) (CX HX : List ℤ) (cost : ℕ) (C H : List ℤ) (k b : ℕ) : Bool × ℕ :=
  let w := WTerms.scale k MT wT
  let B := Lay.digitsFor (normsAt ℤ n C H w) (Lay.apxBits ℤ)
  let m := Lay.masks B shT
  let Ns := numsAt ℤ n shT C H B w
  bif topTM ℤ m n shT B strict w C H (Ns.map (Lay.l1O B m.ones)) Ns then (true, b)
  else
    let σ := Lay.lowSign ℤ shT B Ns
    let wk := WTerms.scale k M wt
    bif Nat.ble cost b && (List.range (ExactBasis.dim κ)).all (fun c ↦
        valsAt shape (frameC n CX HX (vertC n C H σ) k) [] 0 c wk == 0) then
      (vertTM κ n shape strict wk (frameC n CX HX C k) (frameH n HX H) σ, b - cost)
    else (false, b)

/-- One box of `bisect`: its test `t` with the work left (if `test`), with a beat line (`boxa`: the
label `lbl` of the box's level, the boxes tested and the result), and the count of boxes tested. -/
def stepA (lbl : ℕ → ℕ → Bool → String) (t : List ℤ → List ℤ → ℕ → ℕ → Bool × ℕ) (lvl : ℕ)
    (test : Bool) (C H : List ℤ) (k : ℕ) (st : ℕ × ℕ) : Bool × ℕ × ℕ :=
  bif test then
    let r := beat "boxa" (fun r : Bool × ℕ ↦ lbl lvl (st.2 + 1) r.1) (t C H k st.1)
    (r.1, r.2, st.2 + 1)
  else (false, st)

/-- **rupert's bisection** with the box test `t` (`bisect_sound`), as `boxRec`: the box `(C, H)`
over `2^k` (if `test`), else a split along the coordinate `Lay.pickW true` of the widths `W` (none
where the shape has degree `0` in it), at most `fuel` levels deep; the state is the work left for
the tests and the count of boxes tested. -/
def bisect (lbl : ℕ → ℕ → Bool → String) (t : List ℤ → List ℤ → ℕ → ℕ → Bool × ℕ) (n : ℕ)
    (shape : List ℕ) : ℕ → ℕ → Bool → List ℤ → List ℤ → ℕ → List ℤ → ℕ × ℕ → Bool × ℕ × ℕ
  | 0, lvl, test, C, H, k, _, st => stepA lbl t lvl test C H k st
  | d + 1, lvl, test, C, H, k, W, st =>
    let r := stepA lbl t lvl test C H k st
    bif r.1 then r
    else
      let j := Lay.pickW true n W
      let W' := Lay.halveW W j
      bif Lay.deg shape j == 0 then bisect lbl t n shape d lvl false C H k W' r.2
      else
        let lo := bisect lbl t n shape d (lvl + 1) true (halfC n C H j (-1)) (halfH n H j) (k + 1)
          W' r.2
        bif lo.1 then
          bisect lbl t n shape d (lvl + 1) true (halfC n C H j 1) (halfH n H j) (k + 1) W' lo.2
        else lo

/-- The list of `n` ones. -/
def onesL (n : ℕ) : List ℤ := (List.range n).map fun _ ↦ 1

/-- An integer polynomial's terms other than `-1`, and the count of its terms `-1`. -/
def dropM1G : SPoly ℤ → SPoly ℤ × ℕ
  | [] => ([], 0)
  | t :: E =>
    let r := dropM1G E
    bif t.1 == -1 then (r.1, r.2 + 1) else (t :: r.1, r.2)

/-- **An integer polynomial without its terms `-1`**, their count charged to its constant
(`dropM1_le`: below it on `[0, 1]^n`). The floors of an enclosure (`encI`) turn every slightly
negative coefficient into a term `-1`; without them its boxes' numerals are smaller. -/
def dropM1 (E : SPoly ℤ) : SPoly ℤ :=
  let r := dropM1G E
  (-(r.2 : ℤ), []) :: r.1

variable (κ) in
/-- **rupert's bisection on an integer enclosure** `E` (`bisE_sound`) of a tuple's terms `wt`
(shape `shape`) on the vertex frame `X = vC + vH u`, `u ∈ [0, 1]^n`: rupert's bisection (`bisect`,
`boxA`) of `[0, 1]^n` = `(1 + w) / 2`, `w ∈ [-1, 1]^n`, along the widths `W`, at most `depth` levels
deep, with exact shifts of the tuple's terms within the work `xw`. The tuple `i` of `nτ` labels the
beat lines (`boxa`, and `arec` after the bisection). -/
def bisE (i nτ n : ℕ) (shape : List ℕ) (strict : Bool) (depth : ℕ) (wt : WTerms)
    (vC vH W : List ℤ) (xw : ℕ) (E : SPoly ℤ) : Bool :=
  let shE := shapeMax ([E].map (SPoly.shapeS n))
  let wE : WTerms := [(1, [E])]
  decide (shE.length ≤ n) && SPoly.lenOk n E &&
    (beat "arec" (fun r ↦ s!" i={i} n={nτ} boxes={r.2.2} ok={r.1}")
      (bisect (fun lvl cnt r ↦ s!" i={i} n={nτ} boxes={cnt} depth={lvl} ok={r}")
        (boxA κ n shE shape strict (WTerms.deg wE) wE (WTerms.deg wt) wt vC vH (xCost n shape))
        n shape depth 0 false (onesL n) (onesL n) 1 W (xw, 0))).1

variable (κ) in
/-- **rupert's procedure on a one-sided enclosure** of a tuple's terms `wt` (shape `shape`) on the
leaf's frame `X = Cₓ + Hₓ y`, `y ∈ [-1, 1]^n`, with the leaf's numerals `Ns` (digit size `B`;
`procAW_sound`): the exact vertex frame at the vertex `Lay.lowSign` of `Ns` and its vertex test (as
`vertTM`), then its integer enclosure (`encI`; without its terms `-1` where `dr`, `dropM1`) and
rupert's bisection on it (`bisE`, exact shifts within the work `xw`), below the leaf's box. The
tuple `i` of `nτ` labels the beat lines. -/
def procAW (i nτ n : ℕ) (shape : List ℕ) (strict : Bool) (depth : ℕ) (wt : WTerms)
    (CX HX W : List ℤ) (B : ℕ) (Ns : List ℕ) (xw : ℕ) (dr : Bool) : Bool :=
  let σ := Lay.lowSign κ shape B Ns
  let vC := vertC n CX HX σ
  let vH := vertH n HX σ
  let Bv := Lay.digitsFor (normsAt κ n vC vH wt) 0
  let Vs := numsAt κ n shape vC vH Bv wt
  let lmax := (Vs.map (Lay.l1O Bv (Lay.onesN Bv shape))).foldr max 0
  Lay.vdTest κ n shape Bv strict lmax Vs ||
    let T := encI κ shape Bv (ExactBasis.apxK κ + (Nat.log2 lmax + 1 - Lay.bPrec)) Vs
    bisE κ i nτ n shape strict depth wt vC vH W xw (bif dr then dropM1 T else T)

variable (κ) in
/-- **rupert's procedure on a one-sided enclosure** (`procA_sound`): `procAW` with rupert's work
for exact shifts (`xWork`) and the enclosure's floors as they are. -/
def procA (i nτ n : ℕ) (shape : List ℕ) (strict : Bool) (depth : ℕ) (wt : WTerms)
    (CX HX W : List ℤ) (B : ℕ) (Ns : List ℕ) : Bool :=
  procAW κ i nτ n shape strict depth wt CX HX W B Ns xWork false

/-! #### Labels -/

theorem stepA_lbl (lbl₁ lbl₂ : ℕ → ℕ → Bool → String) (t : List ℤ → List ℤ → ℕ → ℕ → Bool × ℕ)
    (lvl : ℕ) (test : Bool) (C H : List ℤ) (k : ℕ) (st : ℕ × ℕ) :
    stepA lbl₁ t lvl test C H k st = stepA lbl₂ t lvl test C H k st := by
  cases test <;> simp [stepA, beat_eq]

/-- The labels of the beat lines change nothing. -/
theorem bisect_lbl (lbl₁ lbl₂ : ℕ → ℕ → Bool → String) (t : List ℤ → List ℤ → ℕ → ℕ → Bool × ℕ)
    (n : ℕ) (shape : List ℕ) : ∀ (fuel lvl : ℕ) (test : Bool) (C H : List ℤ) (k : ℕ)
      (W : List ℤ) (st : ℕ × ℕ),
      bisect lbl₁ t n shape fuel lvl test C H k W st =
        bisect lbl₂ t n shape fuel lvl test C H k W st
  | 0, _, _, _, _, _, _, _ => by simp only [bisect, stepA_lbl lbl₁ lbl₂]
  | d + 1, _, _, _, _, _, _, _ => by
    simp only [bisect, stepA_lbl lbl₁ lbl₂, bisect_lbl lbl₁ lbl₂ t n shape d]

theorem bisE_tag (i nτ n : ℕ) (shape : List ℕ) (strict : Bool) (depth : ℕ) (wt : WTerms)
    (vC vH W : List ℤ) (xw : ℕ) (E : SPoly ℤ) :
    bisE κ i nτ n shape strict depth wt vC vH W xw E =
      bisE κ 0 0 n shape strict depth wt vC vH W xw E := by
  simp only [bisE, beat_eq]
  rw [bisect_lbl _ (fun _ _ _ ↦ ""), bisect_lbl (fun lvl cnt r ↦
    s!" i={0} n={0} boxes={cnt} depth={lvl} ok={r}") (fun _ _ _ ↦ "")]

theorem procAW_tag (i nτ n : ℕ) (shape : List ℕ) (strict : Bool) (depth : ℕ) (wt : WTerms)
    (CX HX W : List ℤ) (B : ℕ) (Ns : List ℕ) (xw : ℕ) (dr : Bool) :
    procAW κ i nτ n shape strict depth wt CX HX W B Ns xw dr =
      procAW κ 0 0 n shape strict depth wt CX HX W B Ns xw dr := by
  simp only [procAW, bisE_tag (κ := κ) i nτ]

/-- The labels of the beat lines change nothing. -/
theorem procA_tag (i nτ n : ℕ) (shape : List ℕ) (strict : Bool) (depth : ℕ) (wt : WTerms)
    (CX HX W : List ℤ) (B : ℕ) (Ns : List ℕ) :
    procA κ i nτ n shape strict depth wt CX HX W B Ns =
      procA κ 0 0 n shape strict depth wt CX HX W B Ns := by
  simp only [procA, procAW_tag (κ := κ) i nτ]

/-! #### Soundness -/

theorem comb_scale {wt : WTerms} {M : ℕ}
    (hdeg : ∀ x ∈ wt, ∀ c, ∀ t ∈ x.2.getD c [], t.2.sum ≤ M) (k : ℕ) (X : ℕ → ℝ) :
    comb (κ := κ) (WTerms.scale k M wt) X =
      2 ^ (k * M) * comb (κ := κ) wt (fun j ↦ X j / 2 ^ k) := by
  unfold comb
  rw [mul_sum]
  refine sum_congr rfl fun c _ ↦ ?_
  rw [valAt_scale _ k M c fun x hx t ht ↦ hdeg x hx c t ht]
  ring

/-- **Soundness of the tests of a box**: where `boxA` passes and the enclosure's sign implies the
tuple's on `[0, 1]^n` (`henc`), the tuple's combination has the sign at the points of the box that
lie in `[0, 1]^n`. -/
theorem boxA_sound {n : ℕ} {shT shape : List ℕ} {strict : Bool} {MT M : ℕ} {wT wt : WTerms}
    {CX HX : List ℤ} {cost : ℕ} (hshT : shT.length ≤ n) (hfitT : Fit n shT wT)
    (hdegT : ∀ x ∈ wT, ∀ c, ∀ t ∈ x.2.getD c [], t.2.sum ≤ MT)
    (hsh : shape.length ≤ n) (hfit : Fit n shape wt)
    (hdeg : ∀ x ∈ wt, ∀ c, ∀ t ∈ x.2.getD c [], t.2.sum ≤ M)
    (henc : ∀ u : ℕ → ℝ, (∀ i < n, 0 ≤ u i ∧ u i ≤ 1) → Sign strict (comb (κ := ℤ) wT u) →
      Sign strict (comb (κ := κ) wt fun i ↦ (CX.getD i 0 : ℝ) + HX.getD i 0 * u i))
    {C H : List ℤ} {k b : ℕ}
    (h : (boxA κ n shT shape strict MT wT M wt CX HX cost C H k b).1 = true)
    {y : ℕ → ℝ} (hy : ∀ i, |y i| ≤ 1) (hu : ∀ i < n, 0 ≤ envK C H k y i ∧ envK C H k y i ≤ 1) :
    Sign strict (comb (κ := κ) wt fun i ↦ (CX.getD i 0 : ℝ) + HX.getD i 0 * envK C H k y i) := by
  simp only [boxA, Bool.cond_eq_ite] at h
  split_ifs at h with h₁ h₂
  · -- the enclosure's tests
    rw [Lay.masks_ones, topTM_eq] at h₁
    have hfit' := hfitT.scale k MT
    have hs := topT_sound (κ := ℤ) (Lay.digitsFor_pos _ _) hshT hfit' (by simp [numsAt])
      (numsAt_spec (κ := ℤ) (Lay.digitsFor_pos _ _) hshT hfit' fun c hc ↦
        normW_lt_digitsFor hc _) h₁ hy
    rw [comb_scale (κ := ℤ) hdegT] at hs
    exact henc _ hu (sign_of_mul (by positivity) hs)
  · -- the exact shift
    rw [vertTM_eq] at h
    have hs := vertT_sound hsh (hfit.scale k M) (Lay.lowSign_cases _ _ _) h hy
    rw [comb_scale hdeg] at hs
    refine (congrArg (Sign strict) (comb_congr hfit fun j hj ↦ ?_)).mp
      (sign_of_mul (by positivity) hs)
    simp only [frameC, frameH, Box.getD_range_map _ _ _ hj, envK]
    push_cast
    field_simp
    ring

theorem stepA_fst (lbl : ℕ → ℕ → Bool → String) (t : List ℤ → List ℤ → ℕ → ℕ → Bool × ℕ)
    (lvl : ℕ) (test : Bool) (C H : List ℤ) (k : ℕ) (st : ℕ × ℕ) :
    (stepA lbl t lvl test C H k st).1 = (test && (t C H k st.1).1) := by
  cases test <;> simp [stepA, beat_eq]

/-- **Soundness of rupert's bisection** for a property `R` of the points of `[0, 1]^n` that reads
their first `n` coordinates: where `bisect` passes with a test that implies `R` on its boxes, `R`
holds on the box. -/
theorem bisect_sound {n : ℕ} {shape : List ℕ} {lbl : ℕ → ℕ → Bool → String}
    {t : List ℤ → List ℤ → ℕ → ℕ → Bool × ℕ} {R : (ℕ → ℝ) → Prop}
    (hR : ∀ u u' : ℕ → ℝ, (∀ i < n, u i = u' i) → R u → R u')
    (ht : ∀ C H k b, (t C H k b).1 = true → ∀ y : ℕ → ℝ, (∀ i, |y i| ≤ 1) → R (envK C H k y)) :
    ∀ (fuel lvl : ℕ) (test : Bool) (C H : List ℤ) (k : ℕ) (W : List ℤ) (st : ℕ × ℕ),
      (bisect lbl t n shape fuel lvl test C H k W st).1 = true →
      ∀ y : ℕ → ℝ, (∀ i, |y i| ≤ 1) → R (envK C H k y)
  | 0, lvl, test, C, H, k, W, st, h, y, hy => by
    rw [bisect, stepA_fst, Bool.and_eq_true] at h
    exact ht C H k st.1 h.2 y hy
  | d + 1, lvl, test, C, H, k, W, st, h, y, hy => by
    simp only [bisect] at h
    cases hr : (stepA lbl t lvl test C H k st).1
    · rw [hr, Bool.cond_false] at h
      cases hdg : Lay.deg shape (Lay.pickW true n W) == 0
      · rw [hdg, Bool.cond_false] at h
        set i := Lay.pickW true n W
        set lo := bisect lbl t n shape d (lvl + 1) true (halfC n C H i (-1)) (halfH n H i) (k + 1)
          (Lay.halveW W i) (stepA lbl t lvl test C H k st).2 with hlo_def
        cases hlo : lo.1
        · rw [hlo, Bool.cond_false] at h
          exact absurd h (by rw [hlo]; decide)
        · rw [hlo, Bool.cond_true] at h
          have half : ∀ s : ℤ, (s = 1 ∨ s = -1) → 0 ≤ s * y i →
              (∀ st', (bisect lbl t n shape d (lvl + 1) true (halfC n C H i s) (halfH n H i)
                (k + 1) (Lay.halveW W i) st').1 = true → R (envK C H k y)) := by
            intro s hs hside st' hrec
            have hy' : ∀ j, |Function.update y i (2 * y i - s) j| ≤ 1 := by
              intro j
              by_cases hj : j = i
              · subst hj
                rw [Function.update_self]
                exact abs_half_le hs (hy _) hside
              · rw [Function.update_of_ne hj]
                exact hy j
            have := bisect_sound hR ht d (lvl + 1) true _ _ (k + 1) _ st' hrec _ hy'
            exact hR _ _ (envK_half C H k i s y) this
          by_cases hyi : y i ≤ 0
          · exact half (-1) (Or.inr rfl) (by push_cast; linarith) _ hlo
          · exact half 1 (Or.inl rfl) (by push_cast; linarith) _ h
      · rw [hdg, Bool.cond_true] at h
        exact bisect_sound hR ht d lvl false C H k _ _ h y hy
    · rw [stepA_fst, Bool.and_eq_true] at hr
      exact ht C H k st.1 hr.2 y hy

/-- The enclosure as weighted terms reads the enclosure's polynomials. -/
theorem valAt_one (c : ℕ) (X : ℕ → ℝ) (T : List (SPoly ℤ)) :
    valAt c X [(1, T)] = SPoly.run (fun a : ℤ ↦ (a : ℝ)) X (T.getD c []) := by
  simp [valAt]

theorem fit_one {n : ℕ} {T : List (SPoly ℤ)} (hlen : T.all (SPoly.lenOk n) = true) :
    Fit n (shapeMax (T.map (SPoly.shapeS n))) [(1, T)] := by
  intro x hx c
  rw [List.mem_singleton] at hx
  subst hx
  rcases getD_mem_or T c [] with h | h
  · exact ⟨shapeLE_shapeMax (List.mem_map_of_mem h), List.all_eq_true.mp hlen _ h⟩
  · rw [h]
    exact ⟨trivial, rfl⟩

/-- The combination over `ℤ` of one integer polynomial is its value. -/
theorem comb_int_one (T : SPoly ℤ) (X : ℕ → ℝ) :
    comb (κ := ℤ) [(1, [T])] X = SPoly.run (fun a : ℤ ↦ (a : ℝ)) X T := by
  change ∑ c ∈ range 1, (Erased.mk (1 : ℝ)).out * valAt c X [(1, [T])] = _
  simp [valAt, Erased.out_mk]

/-- **The integer enclosure is below**: on `[0, 1]^n`, `2^s` times the enclosure is at most `2^K`
times the combination of the numerals' polynomials. -/
theorem encI_le {shape : List ℕ} {B s : ℕ} {Vs : List ℕ}
    (hV : ∀ c, Vs.getD c 0 < 2 ^ (B * slots shape)) {u : ℕ → ℝ}
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1) :
    2 ^ s * SPoly.run (fun a : ℤ ↦ (a : ℝ)) u (encI κ shape B s Vs) ≤
      2 ^ ExactBasis.apxK κ * ∑ c ∈ range (ExactBasis.dim κ),
        ExactBasis.basis κ c * Lay.pv shape (Lay.cf B (Vs.getD c 0)) u := by
  rw [encI, Lay.run_truncI _ _ _ _ _ _ _ _ _ _ hV]
  simp only [zero_add]
  exact Lay.truncI_le shape B s Vs hu

/-- A monomial on `[0, 1]^n` is in `[0, 1]`. -/
theorem mono_unit {u : ℕ → ℝ} (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1) : ∀ (i : ℕ) (e : List ℕ),
    0 ≤ SPoly.mono (1 : ℝ) u i e ∧ SPoly.mono (1 : ℝ) u i e ≤ 1
  | _, [] => by simp [SPoly.mono]
  | i, d :: e => by
    obtain ⟨h0, h1⟩ := mono_unit hu (i + 1) e
    simp only [SPoly.mono]
    split_ifs
    · exact ⟨h0, h1⟩
    · rw [powG_one]
      have hp0 := pow_nonneg (hu i).1 d
      have hp1 : u i ^ d ≤ 1 := pow_le_one₀ (hu i).1 (hu i).2
      exact ⟨mul_nonneg hp0 h0, by nlinarith⟩

theorem dropM1G_le {u : ℕ → ℝ} (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1) : ∀ E : SPoly ℤ,
    SPoly.run (fun a : ℤ ↦ (a : ℝ)) u (dropM1G E).1 - (dropM1G E).2 ≤
      SPoly.run (fun a : ℤ ↦ (a : ℝ)) u E
  | [] => by simp [dropM1G, SPoly.run_int_eq_sum]
  | t :: E => by
    have ih := dropM1G_le hu E
    have hm := (mono_unit hu 0 t.2).2
    simp only [SPoly.run_int_eq_sum] at ih ⊢
    rw [dropM1G]
    cases h : t.1 == -1
    · simp only [Bool.cond_false, List.map_cons, List.sum_cons]
      linarith
    · have ht : t.1 = -1 := by simpa using h
      simp only [Bool.cond_true, List.map_cons, List.sum_cons, ht]
      push_cast
      linarith

/-- **Without its terms `-1`, an integer polynomial stays below** on `[0, 1]^n`: each such term is
at least `-1` there. -/
theorem dropM1_le {u : ℕ → ℝ} (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1) (E : SPoly ℤ) :
    SPoly.run (fun a : ℤ ↦ (a : ℝ)) u (dropM1 E) ≤ SPoly.run (fun a : ℤ ↦ (a : ℝ)) u E := by
  have h := dropM1G_le hu E
  rw [dropM1, SPoly.run_int_eq_sum, List.map_cons, List.sum_cons, ← SPoly.run_int_eq_sum]
  simp only [SPoly.mono, mul_one]
  push_cast
  linarith

/-- **Soundness of rupert's bisection on an integer enclosure**: where `bisE` passes on an
enclosure `E` whose sign on `[0, 1]^n` implies the tuple's on the vertex frame (`henc`), the
tuple's combination has the sign there. -/
theorem bisE_sound {i nτ n : ℕ} {shape : List ℕ} {strict : Bool} {depth : ℕ} {wt : WTerms}
    {vC vH W : List ℤ} {xw : ℕ} {E : SPoly ℤ} (hsh : shape.length ≤ n) (hfit : Fit n shape wt)
    (henc : ∀ u : ℕ → ℝ, (∀ i, 0 ≤ u i ∧ u i ≤ 1) →
      Sign strict (SPoly.run (fun a : ℤ ↦ (a : ℝ)) u E) →
        Sign strict (comb (κ := κ) wt fun i ↦ (vC.getD i 0 : ℝ) + vH.getD i 0 * u i))
    (h : bisE κ i nτ n shape strict depth wt vC vH W xw E = true) {u : ℕ → ℝ}
    (hu : ∀ i < n, 0 ≤ u i ∧ u i ≤ 1) :
    Sign strict (comb (κ := κ) wt fun i ↦ (vC.getD i 0 : ℝ) + vH.getD i 0 * u i) := by
  simp only [bisE, Bool.and_eq_true, beat_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hshE, hlen⟩, h⟩ := h
  have hfitE := fit_one (n := n) (T := [E]) (by simp [hlen])
  -- The enclosure's sign implies the tuple's on `[0, 1]^n`, read on the first `n` coordinates.
  have henc' : ∀ u : ℕ → ℝ, (∀ i < n, 0 ≤ u i ∧ u i ≤ 1) →
      Sign strict (comb (κ := ℤ) [(1, [E])] u) →
        Sign strict (comb (κ := κ) wt fun i ↦ (vC.getD i 0 : ℝ) + vH.getD i 0 * u i) := by
    intro u hu hs
    set u' : ℕ → ℝ := fun i ↦ if i < n then u i else 0
    have hu' : ∀ i, 0 ≤ u' i ∧ u' i ≤ 1 := by
      intro i
      by_cases hi : i < n
      · simpa [u', hi] using hu i hi
      · simp [u', hi]
    have hagree : ∀ i < n, u i = u' i := fun i hi ↦ by simp [u', hi]
    rw [comb_congr hfitE hagree, comb_int_one] at hs
    have hX := comb_congr (κ := κ) hfit
      (X := fun i ↦ (vC.getD i 0 : ℝ) + vH.getD i 0 * u i)
      (X' := fun i ↦ (vC.getD i 0 : ℝ) + vH.getD i 0 * u' i) fun i hi ↦ by
        simp only [hagree i hi]
    rw [hX]
    exact henc u' hu' hs
  -- The bisection of `[0, 1]^n`.
  have hb := bisect_sound (n := n) (shape := shape)
    (R := fun u ↦ (∀ i < n, 0 ≤ u i ∧ u i ≤ 1) →
      Sign strict (comb (κ := κ) wt fun i ↦ (vC.getD i 0 : ℝ) + vH.getD i 0 * u i))
    (fun u u' hu R hu' ↦ by
      have hX := comb_congr (κ := κ) hfit
        (X := fun i ↦ (vC.getD i 0 : ℝ) + vH.getD i 0 * u i)
        (X' := fun i ↦ (vC.getD i 0 : ℝ) + vH.getD i 0 * u' i) fun i hi ↦ by
          simp only [hu i hi]
      rw [← hX]
      exact R fun i hi ↦ hu i hi ▸ hu' i hi)
    (fun C H k b hb y hy hu ↦ boxA_sound hshE hfitE (fun x hx c t ht ↦ WTerms.le_deg hx c ht)
      hsh hfit (fun x hx c t ht ↦ WTerms.le_deg hx c ht) henc' hb hy hu)
    _ _ _ _ _ _ _ _ h
  -- The point `u` is the point `w = 2 u - 1` of `[-1, 1]^n`.
  set w : ℕ → ℝ := fun i ↦ if i < n then 2 * u i - 1 else 0
  have hw : ∀ i, |w i| ≤ 1 := by
    intro i
    by_cases hi : i < n
    · have := hu i hi
      simp only [w, hi, ↓reduceIte, abs_le]
      constructor <;> linarith
    · simp [w, hi]
  have hE : ∀ j < n, envK (onesL n) (onesL n) 1 w j = u j := by
    intro j hj
    simp only [envK, onesL, Box.getD_range_map _ _ _ hj, w, hj, ↓reduceIte]
    push_cast
    ring
  have hs := hb w hw fun j hj ↦ by rw [hE j hj]; exact hu j hj
  refine (congrArg (Sign strict) (comb_congr hfit fun j hj ↦ ?_)).mp hs
  rw [hE j hj]

/-- **Soundness of rupert's procedure on a one-sided enclosure**: where `procAW` passes, the
tuple's combination has the sign on the leaf's frame. -/
theorem procAW_sound {i nτ n : ℕ} {shape : List ℕ} {strict : Bool} {depth : ℕ} {wt : WTerms}
    {CX HX W : List ℤ} {B : ℕ} {Ns : List ℕ} {xw : ℕ} {dr : Bool} (hsh : shape.length ≤ n)
    (hfit : Fit n shape wt) (h : procAW κ i nτ n shape strict depth wt CX HX W B Ns xw dr = true)
    {y : ℕ → ℝ} (hy : ∀ i, |y i| ≤ 1) :
    Sign strict (comb (κ := κ) wt fun i ↦ (CX.getD i 0 : ℝ) + HX.getD i 0 * y i) := by
  set σ := Lay.lowSign κ shape B Ns with hσdef
  have hσ : ∀ i, σ i = 1 ∨ σ i = -1 := Lay.lowSign_cases shape B Ns
  simp only [procAW, Bool.or_eq_true] at h
  rcases h with h | h
  · have hv : vertTM κ n shape strict wt CX HX σ = true := h
    exact vertT_sound hsh hfit hσ (by rw [← vertTM_eq]; exact hv) hy
  · set vC := vertC n CX HX σ
    set vH := vertH n HX σ
    set Bv := Lay.digitsFor (normsAt κ n vC vH wt) 0
    set Vs := numsAt κ n shape vC vH Bv wt
    set S := ExactBasis.apxK κ +
      (Nat.log2 ((Vs.map (Lay.l1O Bv (Lay.onesN Bv shape))).foldr max 0) + 1 - Lay.bPrec)
    set T := encI κ shape Bv S Vs
    have hspec := numsAt_spec (κ := κ) (C := vC) (H := vH) (B := Bv) (Lay.digitsFor_pos _ _)
      hsh hfit fun c hc ↦ normW_lt_digitsFor hc 0
    have hV : ∀ c, Vs.getD c 0 < 2 ^ (Bv * slots shape) := by
      intro c
      by_cases hc : c < ExactBasis.dim κ
      · exact (hspec c hc).1.1
      · rw [List.getD_eq_default _ _ (by simp [Vs, numsAt]; omega)]
        positivity
    -- The enclosure's sign on `[0, 1]^n` implies the tuple's (`encI_le`, `dropM1_le`).
    have henc : ∀ u : ℕ → ℝ, (∀ i, 0 ≤ u i ∧ u i ≤ 1) →
        Sign strict (SPoly.run (fun a : ℤ ↦ (a : ℝ)) u (bif dr then dropM1 T else T)) →
          Sign strict (comb (κ := κ) wt fun i ↦ (vC.getD i 0 : ℝ) + vH.getD i 0 * u i) := by
      intro u hu hs
      have hd : SPoly.run (fun a : ℤ ↦ (a : ℝ)) u (bif dr then dropM1 T else T) ≤
          SPoly.run (fun a : ℤ ↦ (a : ℝ)) u T := by
        cases dr
        · exact le_rfl
        · exact dropM1_le hu T
      have hle := encI_le (κ := κ) (s := S) hV hu
      have heq : ∑ c ∈ range (ExactBasis.dim κ),
          ExactBasis.basis κ c * Lay.pv shape (Lay.cf Bv (Vs.getD c 0)) u =
            comb (κ := κ) wt fun i ↦ (vC.getD i 0 : ℝ) + vH.getD i 0 * u i := by
        unfold comb
        exact sum_congr rfl fun c hc ↦ by rw [(hspec c (mem_range.mp hc)).2]
      rw [heq] at hle
      exact sign_of_mul (by positivity)
        (sign_of_le (sign_mul_of_pos (by positivity) (sign_of_le hs hd)) hle)
    -- The leaf's point `y` is the point `u = (1 - σ y) / 2` of the vertex frame.
    have hs := bisE_sound hsh hfit henc h (u := fun j ↦ (1 - σ j * y j) / 2)
      fun j _ ↦ vert_mem hσ hy j
    have e := envK_vert (n := n) CX HX 0 hσ y
    simp only [envK, pow_zero, div_one] at e
    exact (congrArg (Sign strict) (comb_congr hfit fun j hj ↦ e j hj)).mp hs

/-- **Soundness of rupert's procedure on a one-sided enclosure**: where `procA` passes, the tuple's
combination has the sign on the leaf's frame. -/
theorem procA_sound {i nτ n : ℕ} {shape : List ℕ} {strict : Bool} {depth : ℕ} {wt : WTerms}
    {CX HX W : List ℤ} {B : ℕ} {Ns : List ℕ} (hsh : shape.length ≤ n) (hfit : Fit n shape wt)
    (h : procA κ i nτ n shape strict depth wt CX HX W B Ns = true) {y : ℕ → ℝ}
    (hy : ∀ i, |y i| ≤ 1) :
    Sign strict (comb (κ := κ) wt fun i ↦ (CX.getD i 0 : ℝ) + HX.getD i 0 * y i) :=
  procAW_sound hsh hfit h hy

end Field

end Pull

end Nieuwland.Check
