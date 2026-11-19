import Modules.Check.Number.DigitBound
import Modules.Check.Sign.Dominance
import Modules.Check.Leaf.Progress

/-!
# The packed engine

The sign of `∑ⱼ βⱼ pⱼ` on the cube `[-1, 1]^n`, where `βⱼ` are the basis values of an exact type
(`ExactBasis κ`) and the integer polynomials `pⱼ` are packed in numerals
(`Modules/Check/Polynomial/Layout.lean`, one numeral per coordinate). This is the computation of every box
check: the polynomial is evaluated once on the whole box, and every smaller box is reached by
substitutions in the numerals.
On each box `run` (sound by `run_sound`) tries

1. the approximate centred form (`apxOk`): a few operations on whole numerals and one sign in `κ`;
2. the exact centred form (`ExactBasis.lowerOf`), only where the approximation errors might hide a
   pass (`apxGate`);
3. if `dom`: dominance (`domOf`) at the vertex where the linear part is smallest (`lowSign`), after
   the expansion `yᵢ = σᵢ (1 - 2 uᵢ)` in the numerals (`vertAll`);
4. else it bisects the widest coordinate `i` (`pickW`): the halves `yᵢ = (∓1 + y'ᵢ) / 2`, as
   `2^(deg i) p((∓1 + y'ᵢ) / 2)` (`halfW`), by substitution in the numerals (`subAll`).

The widths `W` only choose the coordinate. A substitution multiplies the absolute coefficient sums
by at most a known factor and is done only while they stay below the bias (`Inv`); the digit size
leaves room for the growth along the bisections (`growth`), the vertex expansion and the
approximations (`digitsFor`).
-/

open Finset

namespace Nieuwland.Check

namespace Lay

open DPoly Num

/-! ### Substitutions in numerals -/

theorem pv_slc_update {R : Type*} [CommRing R] (sh : List ℕ) (i k : ℕ) (c : ℕ → ℤ)
    (y : ℕ → R) (z : R) :
    pv sh (slc sh i k c) (Function.update y i z) = pv sh (slc sh i k c) y := by
  refine sum_congr rfl fun q _ ↦ ?_
  unfold slc
  split_ifs with h
  · congr 1
    refine prod_congr rfl fun j _ ↦ ?_
    by_cases hj : j = i
    · subst hj; rw [h, pow_zero, pow_zero]
    · rw [Function.update_of_ne hj]
  · simp

/-- **Substitution keeps the invariant** when the factor `W` keeps the coefficient sum below the
bias. -/
theorem subN_inv {B : ℕ} (hB : 0 < B) {sh : List ℕ} {N : ℕ} (hN : Inv B sh N) (i : ℕ)
    (w : ℕ → ℤ) (a b : ℤ) {W : ℕ}
    (hW : ∀ k ≤ deg sh i, (w k).natAbs * (a.natAbs + b.natAbs) ^ k ≤ W)
    (hl : W * l1N B sh N < 2 ^ (B - 1)) :
    Inv B sh (subN B sh i w a b N) ∧ ∀ y : ℕ → ℝ, pv sh (cf B (subN B sh i w a b N)) y =
      ∑ k ∈ range (deg sh i + 1),
        (w k : ℝ) * (a + b * y i) ^ k * pv sh (slc sh i k (cf B N)) y := by
  rw [l1N_eq_of_inv hB hN] at hl
  obtain ⟨hlt, hcf⟩ := subN_spec hB hN.1 i w a b hW hl
  refine ⟨⟨hlt, ?_⟩, fun y ↦ ?_⟩
  · rw [l1_congr hcf]
    exact (l1_sub_le sh i w a b _ hW).trans_lt hl
  · rw [pv_congr hcf, pv_sub]

/-- Substitution in every numeral, if the factor `W` keeps their coefficient sums below the bias
(`subAll_spec`). -/
def subAll (B : ℕ) (sh : List ℕ) (i : ℕ) (w : ℕ → ℤ) (a b : ℤ) (W : ℕ) (Ns : List ℕ) :
    Option (List ℕ) :=
  bif Ns.all fun N ↦ decide (W * l1N B sh N < 2 ^ (B - 1)) then some (Ns.map (subN B sh i w a b))
  else none

theorem getD_mem {Ns : List ℕ} {j : ℕ} (hj : j < Ns.length) : Ns.getD j 0 ∈ Ns := by
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

theorem subAll_spec {B : ℕ} (hB : 0 < B) {sh : List ℕ} {i : ℕ} {w : ℕ → ℤ} {a b : ℤ} {W : ℕ}
    (hW : ∀ k ≤ deg sh i, (w k).natAbs * (a.natAbs + b.natAbs) ^ k ≤ W) {Ns Ns' : List ℕ}
    (hNs : ∀ N ∈ Ns, Inv B sh N) (h : subAll B sh i w a b W Ns = some Ns') :
    (∀ N ∈ Ns', Inv B sh N) ∧ Ns'.length = Ns.length ∧ ∀ j < Ns.length, ∀ y : ℕ → ℝ,
      pv sh (cf B (Ns'.getD j 0)) y = ∑ k ∈ range (deg sh i + 1),
        (w k : ℝ) * (a + b * y i) ^ k * pv sh (slc sh i k (cf B (Ns.getD j 0))) y := by
  unfold subAll at h
  cases hall : Ns.all fun N ↦ decide (W * l1N B sh N < 2 ^ (B - 1))
  · rw [hall] at h
    exact absurd h (by simp)
  · rw [hall, Bool.cond_true, Option.some.injEq] at h
    subst h
    have hl : ∀ N ∈ Ns, W * l1N B sh N < 2 ^ (B - 1) := fun N hN ↦
      of_decide_eq_true (List.all_eq_true.mp hall N hN)
    refine ⟨fun N' hN' ↦ ?_, List.length_map _, fun j hj y ↦ ?_⟩
    · obtain ⟨N, hN, rfl⟩ := List.mem_map.mp hN'
      exact (subN_inv hB (hNs N hN) i w a b hW (hl N hN)).1
    · have hmem := getD_mem hj
      rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
        ← List.getD_eq_getElem _ 0 hj]
      exact (subN_inv hB (hNs _ hmem) i w a b hW (hl _ hmem)).2 y

/-! ### Bisection -/

/-- The weights of a bisection along `i`: `2^(deg i) p((s + yᵢ) / 2)` is
`∑ₖ 2^(deg i - k) (s + yᵢ)^k Sₖ` (`pv_half`). -/
def halfW (sh : List ℕ) (i k : ℕ) : ℤ := 2 ^ (deg sh i - k)

theorem halfW_bound (sh : List ℕ) (i : ℕ) {s : ℤ} (hs : s.natAbs = 1) :
    ∀ k ≤ deg sh i, (halfW sh i k).natAbs * (s.natAbs + (1 : ℤ).natAbs) ^ k ≤ 2 ^ deg sh i := by
  intro k hk
  rw [halfW, hs, Int.natAbs_pow]
  norm_num
  rw [← pow_add, Nat.sub_add_cancel hk]

theorem pv_half (sh : List ℕ) (i : ℕ) (s : ℤ) (c : ℕ → ℤ) (y : ℕ → ℝ) :
    ∑ k ∈ range (deg sh i + 1), ((halfW sh i k : ℤ) : ℝ) *
        ((s : ℝ) + ((1 : ℤ) : ℝ) * Function.update y i (2 * y i - s) i) ^ k *
        pv sh (slc sh i k c) (Function.update y i (2 * y i - s)) =
      2 ^ deg sh i * pv sh c y := by
  rw [pv_slc sh i c y, mul_sum]
  refine sum_congr rfl fun k hk ↦ ?_
  have hk' : k ≤ deg sh i := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [Function.update_self, pv_slc_update, halfW]
  have : (2 : ℝ) ^ deg sh i = 2 ^ (deg sh i - k) * 2 ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk']
  rw [this]
  push_cast
  ring

/-- The coordinate to bisect: the widest of the first `n` widths, the first such or, if `last`,
the last (`max_by` in the Rust check). -/
def pickW (last : Bool) (n : ℕ) (W : List ℤ) : ℕ :=
  ((List.range n).foldl (fun (acc : ℕ × ℤ) i ↦
    bif (bif last then decide (acc.2 ≤ W.getD i 0) else decide (acc.2 < W.getD i 0))
    then (i, W.getD i 0) else acc) (0, -1)).1

/-- The widths of both halves along `i`, over the doubled denominator. -/
def halveW (W : List ℤ) (i : ℕ) : List ℤ := W.mapIdx fun j w ↦ if j = i then w else 2 * w

/-- The growth of the coefficient sums (in bits) along `depth` bisections from the widths `W`:
a bisection along `i` multiplies them by at most `2^(deg i)`. All boxes at one depth have the same
widths, so this is the growth along every branch. -/
def growth (last : Bool) (n : ℕ) (sh : List ℕ) : ℕ → List ℤ → ℕ
  | 0, _ => 0
  | d + 1, W => deg sh (pickW last n W) + growth last n sh d (halveW W (pickW last n W))

/-! ### Vertex expansion -/

/-- The expansion at the vertex `σ` (`σᵢ = ±1`) of the first `m` coordinates: `yᵢ = σᵢ (1 - 2 uᵢ)`
with `uᵢ ∈ [0, 1]`, one coordinate after another (`vertAll_spec`). -/
def vertAll (B : ℕ) (sh : List ℕ) (σ : ℕ → ℤ) : ℕ → List ℕ → Option (List ℕ)
  | 0, Ns => some Ns
  | m + 1, Ns =>
    match vertAll B sh σ m Ns with
    | none => none
    | some Ns' =>
      bif deg sh m == 0 then some Ns'
      else subAll B sh m (fun _ ↦ 1) (σ m) (-2 * σ m) (3 ^ deg sh m) Ns'

/-- The point of the expansion: `uᵢ = (1 - σᵢ yᵢ) / 2` for `i < m`, `yᵢ` beyond. -/
noncomputable def vertPt (σ : ℕ → ℤ) (m : ℕ) (y : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i < m then (1 - σ i * y i) / 2 else y i

theorem vertPt_succ (σ : ℕ → ℤ) (m : ℕ) (y : ℕ → ℝ) :
    vertPt σ (m + 1) y = Function.update (vertPt σ m y) m ((1 - σ m * y m) / 2) := by
  funext i
  unfold vertPt
  by_cases h : i = m
  · subst h; simp
  · rw [Function.update_of_ne h]
    by_cases h' : i < m
    · simp [h', show i < m + 1 by omega]
    · simp [h', show ¬i < m + 1 by omega]

theorem vertPt_self (σ : ℕ → ℤ) (m : ℕ) (y : ℕ → ℝ) : vertPt σ m y m = y m := by
  simp [vertPt]

theorem vertPt_mem {σ : ℕ → ℤ} (hσ : ∀ i, σ i = 1 ∨ σ i = -1) {m : ℕ} {y : ℕ → ℝ}
    (hy : ∀ i, |y i| ≤ 1) {i : ℕ} (hi : i < m) : 0 ≤ vertPt σ m y i ∧ vertPt σ m y i ≤ 1 := by
  simp only [vertPt, hi, ite_true]
  have := abs_le.mp (hy i)
  rcases hσ i with h | h <;> rw [h] <;> push_cast <;> constructor <;> linarith

theorem vertW_bound (sh : List ℕ) (m : ℕ) {s : ℤ} (hs : s.natAbs = 1) :
    ∀ k ≤ deg sh m, ((fun _ ↦ (1 : ℤ)) k).natAbs * (s.natAbs + (-2 * s).natAbs) ^ k ≤
      3 ^ deg sh m := by
  intro k hk
  rw [Int.natAbs_mul, hs]
  norm_num
  exact Nat.pow_le_pow_right (by norm_num) hk

theorem vertAll_spec {B : ℕ} (hB : 0 < B) {sh : List ℕ} {σ : ℕ → ℤ}
    (hσ : ∀ i, σ i = 1 ∨ σ i = -1) :
    ∀ (m : ℕ) {Ns Vs : List ℕ}, (∀ N ∈ Ns, Inv B sh N) → vertAll B sh σ m Ns = some Vs →
      (∀ N ∈ Vs, Inv B sh N) ∧ Vs.length = Ns.length ∧ ∀ j < Ns.length, ∀ y : ℕ → ℝ,
        pv sh (cf B (Vs.getD j 0)) (vertPt σ m y) = pv sh (cf B (Ns.getD j 0)) y
  | 0, Ns, Vs, hNs, h => by
    simp only [vertAll, Option.some.injEq] at h
    subst h
    refine ⟨hNs, rfl, fun j _ y ↦ ?_⟩
    have : vertPt σ 0 y = y := by funext i; simp [vertPt]
    rw [this]
  | m + 1, Ns, Vs, hNs, h => by
    simp only [vertAll] at h
    cases hm : vertAll B sh σ m Ns with
    | none => rw [hm] at h; exact absurd h (by simp)
    | some Ns' =>
      rw [hm] at h
      obtain ⟨hinv', hlen', hpv'⟩ := vertAll_spec hB hσ m hNs hm
      have hs : (σ m).natAbs = 1 := by rcases hσ m with h' | h' <;> rw [h'] <;> rfl
      cases hd : deg sh m == 0
      · simp only [hd, Bool.cond_false] at h
        obtain ⟨hinv, hlen, hpv⟩ := subAll_spec hB (vertW_bound sh m hs) hinv' h
        refine ⟨hinv, hlen.trans hlen', fun j hj y ↦ ?_⟩
        rw [hpv j (hlen' ▸ hj), ← hpv' j hj y, pv_slc sh m _ (vertPt σ m y)]
        have hσ2 : (σ m : ℝ) * σ m = 1 := by
          rcases hσ m with h' | h' <;> rw [h'] <;> norm_num
        have hbase : ((σ m : ℤ) : ℝ) + ((-2 * σ m : ℤ) : ℝ) * ((1 - (σ m : ℝ) * y m) / 2) =
            y m := by
          push_cast
          linear_combination (y m) * hσ2
        refine sum_congr rfl fun k _ ↦ ?_
        rw [vertPt_succ, Function.update_self, pv_slc_update, vertPt_self, hbase, Int.cast_one,
          one_mul]
      · simp only [hd, Bool.cond_true, Option.some.injEq] at h
        subst h
        have hd' : deg sh m = 0 := by simpa using hd
        refine ⟨hinv', hlen', fun j hj y ↦ ?_⟩
        rw [← hpv' j hj y, vertPt_succ, pv_update, pv_slc sh m _ (vertPt σ m y), hd']
        simp

/-! ### Box tests -/

section Field

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

variable (κ) in
/-- The vertex where the linear part is smallest: the upper end (`σᵢ = 1`) where the coefficient
of `yᵢ` (slot `stride i`) is not known to be nonnegative (`nonneg_exact_rec` in `regional.rs`).
Any vertex is sound. -/
def lowSign (sh : List ℕ) (B : ℕ) (Ns : List ℕ) (i : ℕ) : ℤ :=
  bif (deg sh i != 0) &&
      !Exact.nonneg (ExactBasis.ofCoords (Ns.map fun N ↦ cf B N (stride sh i)) : κ) then 1
  else -1

theorem lowSign_cases (sh : List ℕ) (B : ℕ) (Ns : List ℕ) (i : ℕ) :
    lowSign κ sh B Ns i = 1 ∨ lowSign κ sh B Ns i = -1 := by
  unfold lowSign
  cases (deg sh i != 0) && !Exact.nonneg (ExactBasis.ofCoords (Ns.map fun N ↦
    cf B N (stride sh i)) : κ) <;> simp

variable (κ) in
/-- Dominance at the vertex `lowSign` (`domOk_sound`). -/
def domOk (n : ℕ) (sh : List ℕ) (B : ℕ) (strict : Bool) (Ns : List ℕ) : Bool :=
  match vertAll B sh (lowSign κ sh B Ns) n Ns with
  | none => false
  | some Vs => (domOf (κ := κ) n sh B Vs).2 && signTest strict (domOf (κ := κ) n sh B Vs).1

variable (κ) in
/-- The error term of `apxPen`: `∑ⱼ εⱼ ‖pⱼ‖₁`. -/
def apxErr (B : ℕ) (sh : List ℕ) (Ns : List ℕ) : ℕ :=
  sumN (fun j ↦ apxE κ j * l1N B sh (Ns.getD j 0)) (ExactBasis.dim κ)

variable (κ) in
/-- Whether the exact centred form might pass where the approximate one failed: the range test of
`apxOk` failed, or the errors are not `0` and the approximate bound plus twice the errors passes
(the exact penalties are at least the approximate ones less the errors). A heuristic. -/
def apxGate (strict : Bool) (B : ℕ) (sh : List ℕ) (Ns : List ℕ) : Bool :=
  !decide (sumN (fun j ↦ (apxA κ j).natAbs * l1N B sh (Ns.getD j 0)) (ExactBasis.dim κ) <
      2 ^ (B - 1)) ||
    decide (0 < apxErr κ B sh Ns) &&
      signTest strict (Exact.ofInt (2 ^ ExactBasis.apxK κ) *
          ExactBasis.ofCoords ((List.range (ExactBasis.dim κ)).map fun j ↦ cf B (Ns.getD j 0) 0) -
        Exact.ofInt (apxPen κ B sh Ns : ℤ) + Exact.ofInt (2 * apxErr κ B sh Ns : ℤ) : κ)

variable (κ) in
/-- The exact centred form, behind `apxGate` (`exactOk_sound`). -/
def exactOk (n : ℕ) (sh : List ℕ) (B : ℕ) (strict : Bool) (Ns : List ℕ) : Bool :=
  apxGate κ strict B sh Ns && (ExactBasis.lowerOf (κ := κ) n sh B Ns).2 &&
    signTest strict (ExactBasis.lowerOf (κ := κ) n sh B Ns).1

variable (κ) in
/-- The tests of one box. -/
def boxOk (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom : Bool) (Ns : List ℕ) : Bool :=
  apxOk κ strict B sh Ns || exactOk κ n sh B strict Ns || (dom && domOk κ n sh B strict Ns)

variable (κ) in
/-- `boxOk` as compiled code runs it (`boxOk_eq_boxOkP`): with a beat line after the dominance
(`Modules/Check/Leaf/Progress.lean`). -/
def boxOkP (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom : Bool) (Ns : List ℕ) : Bool :=
  apxOk κ strict B sh Ns || exactOk κ n sh B strict Ns ||
    (dom && beat "dom" (fun r ↦ s!" ok={r}") (domOk κ n sh B strict Ns))

@[csimp] theorem boxOk_eq_boxOkP : @boxOk = @boxOkP := by
  funext κ _ _ _ _ n sh B strict dom Ns
  simp only [boxOk, boxOkP, beat_eq]

variable (κ) in
/-- **The engine** (`run_sound`): certifies `0 < ∑ⱼ βⱼ pⱼ` (`strict`) or `0 ≤` on `[-1, 1]^n`, with
at most `depth` bisections along each branch. -/
def run (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom last : Bool) : ℕ → List ℤ → List ℕ → Bool
  | 0, _, Ns => boxOk κ n sh B strict dom Ns
  | d + 1, W, Ns =>
    boxOk κ n sh B strict dom Ns ||
      let i := pickW last n W
      let W' := halveW W i
      bif deg sh i == 0 then run n sh B strict dom last d W' Ns
      else
        match subAll B sh i (halfW sh i) (-1) 1 (2 ^ deg sh i) Ns,
          subAll B sh i (halfW sh i) 1 1 (2 ^ deg sh i) Ns with
        | some Lo, some Hi =>
          run n sh B strict dom last d W' Lo && run n sh B strict dom last d W' Hi
        | _, _ => false

/-! #### Soundness -/

variable {n : ℕ} {sh : List ℕ} {B : ℕ} {strict : Bool} {Ns : List ℕ}

/-- The value certified on the cube. -/
noncomputable def val (sh : List ℕ) (B : ℕ) (Ns : List ℕ) (y : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range (ExactBasis.dim κ), ExactBasis.basis κ j * pv sh (cf B (Ns.getD j 0)) y

theorem sum_eval_unpack (hsh : sh.length ≤ n) (Ns : List ℕ) (y : ℕ → ℝ) :
    ∑ j ∈ range (ExactBasis.dim κ),
        ExactBasis.basis κ j * DPoly.eval n (DPoly.unpack n sh B (Ns.getD j 0)) (fun i ↦ y i) =
      val (κ := κ) sh B Ns y :=
  sum_congr rfl fun j _ ↦ by rw [eval_unpack_eq_pv B n sh hsh]

theorem exactOk_sound (hB : 0 < B) (hsh : sh.length ≤ n) (hlen : ExactBasis.dim κ ≤ Ns.length)
    (h : exactOk κ n sh B strict Ns = true) {y : ℕ → ℝ} (hy : ∀ i, |y i| ≤ 1) :
    Sign strict (val (κ := κ) sh B Ns y) := by
  simp only [exactOk, Bool.and_eq_true] at h
  refine sign_of_le (sign_of_signTest h.2) ?_
  rw [← sum_eval_unpack hsh]
  exact ExactBasis.lowerOf_le n sh B Ns _ hB hlen (fun i ↦ hy i) h.1.2

theorem domOk_sound (hB : 0 < B) (hsh : sh.length ≤ n) (hNs : ∀ N ∈ Ns, Inv B sh N)
    (hlen : ExactBasis.dim κ ≤ Ns.length) (h : domOk κ n sh B strict Ns = true) {y : ℕ → ℝ}
    (hy : ∀ i, |y i| ≤ 1) : Sign strict (val (κ := κ) sh B Ns y) := by
  unfold domOk at h
  split at h
  · exact absurd h (by simp)
  · rename_i Vs hV
    simp only [Bool.and_eq_true] at h
    obtain ⟨-, hlenV, hpv⟩ := vertAll_spec hB (lowSign_cases sh B Ns) n hNs hV
    refine sign_of_le (sign_of_signTest h.2) ?_
    have hd := domOf_le (κ := κ) n sh B Vs (fun i ↦ vertPt (lowSign κ sh B Ns) n y i)
      (hlenV ▸ hlen) (fun i ↦ vertPt_mem (lowSign_cases sh B Ns) hy i.2) h.1
    refine hd.trans (le_of_eq ?_)
    rw [sum_eval_unpack hsh]
    exact sum_congr rfl fun j hj ↦ by
      rw [hpv j ((mem_range.mp hj).trans_le hlen)]

theorem boxOk_sound {dom : Bool} (hB : 0 < B) (hsh : sh.length ≤ n)
    (hNs : ∀ N ∈ Ns, Inv B sh N) (hlen : ExactBasis.dim κ ≤ Ns.length)
    (h : boxOk κ n sh B strict dom Ns = true) {y : ℕ → ℝ} (hy : ∀ i, |y i| ≤ 1) :
    Sign strict (val (κ := κ) sh B Ns y) := by
  simp only [boxOk, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with (h | h) | ⟨-, h⟩
  · exact apxOk_sound hB (fun j hj ↦ hNs _ (getD_mem ((hj.trans_le hlen)))) h hy
  · exact exactOk_sound hB hsh hlen h hy
  · exact domOk_sound hB hsh hNs hlen h hy

/-- A bisection along `i`: the half containing `y` gives the sign at `y`. -/
theorem half_sound {i : ℕ} {Lo Hi : List ℕ} (hB : 0 < B) (hNs : ∀ N ∈ Ns, Inv B sh N)
    (hlen : ExactBasis.dim κ ≤ Ns.length)
    (hLo : subAll B sh i (halfW sh i) (-1) 1 (2 ^ deg sh i) Ns = some Lo)
    (hHi : subAll B sh i (halfW sh i) 1 1 (2 ^ deg sh i) Ns = some Hi)
    (hsLo : ∀ y : ℕ → ℝ, (∀ i, |y i| ≤ 1) → Sign strict (val (κ := κ) sh B Lo y))
    (hsHi : ∀ y : ℕ → ℝ, (∀ i, |y i| ≤ 1) → Sign strict (val (κ := κ) sh B Hi y))
    {y : ℕ → ℝ} (hy : ∀ i, |y i| ≤ 1) : Sign strict (val (κ := κ) sh B Ns y) := by
  have key : ∀ {s : ℤ} {Ns' : List ℕ}, s.natAbs = 1 →
      subAll B sh i (halfW sh i) s 1 (2 ^ deg sh i) Ns = some Ns' →
      (∀ y : ℕ → ℝ, (∀ i, |y i| ≤ 1) → Sign strict (val (κ := κ) sh B Ns' y)) →
      |2 * y i - s| ≤ 1 → Sign strict (val (κ := κ) sh B Ns y) := by
    intro s Ns' hs h hs' hyi
    obtain ⟨-, -, hpv⟩ := subAll_spec hB (halfW_bound sh i hs) hNs h
    have hy' : ∀ k, |Function.update y i (2 * y i - s) k| ≤ 1 := by
      intro k
      by_cases hk : k = i
      · subst hk; rw [Function.update_self]; exact hyi
      · rw [Function.update_of_ne hk]; exact hy k
    refine sign_of_mul (t := (2 : ℝ) ^ deg sh i) (by positivity) ?_
    have := hs' _ hy'
    unfold val at this ⊢
    rw [mul_sum]
    refine (congrArg (Sign strict) (sum_congr rfl fun j hj ↦ ?_)).mp this
    rw [hpv j ((mem_range.mp hj).trans_le hlen), pv_half]
    ring
  have hyi := abs_le.mp (hy i)
  rcases le_or_gt (y i) 0 with h | h
  · exact key (s := -1) rfl hLo hsLo (by rw [abs_le]; push_cast; constructor <;> linarith)
  · exact key (s := 1) rfl hHi hsHi (by rw [abs_le]; push_cast; constructor <;> linarith)

/-- **Soundness of the engine.** -/
theorem run_sound {dom last : Bool} (hB : 0 < B) (hsh : sh.length ≤ n) :
    ∀ (depth : ℕ) (W : List ℤ) {Ns : List ℕ}, (∀ N ∈ Ns, Inv B sh N) →
      ExactBasis.dim κ ≤ Ns.length → run κ n sh B strict dom last depth W Ns = true →
      ∀ y : ℕ → ℝ, (∀ i, |y i| ≤ 1) → Sign strict (val (κ := κ) sh B Ns y)
  | 0, W, Ns, hNs, hlen, h, y, hy => boxOk_sound hB hsh hNs hlen h hy
  | d + 1, W, Ns, hNs, hlen, h, y, hy => by
    simp only [run, Bool.or_eq_true] at h
    rcases h with h | h
    · exact boxOk_sound hB hsh hNs hlen h hy
    cases hd : deg sh (pickW last n W) == 0
    · rw [hd, Bool.cond_false] at h
      split at h
      · rename_i Lo Hi hLo hHi
        simp only [Bool.and_eq_true] at h
        have hLo' := hLo
        have hHi' := hHi
        obtain ⟨hiLo, hlLo, -⟩ := subAll_spec hB (halfW_bound sh _ (s := -1) rfl) hNs hLo'
        obtain ⟨hiHi, hlHi, -⟩ := subAll_spec hB (halfW_bound sh _ (s := 1) rfl) hNs hHi'
        exact half_sound hB hNs hlen hLo hHi
          (run_sound hB hsh d _ hiLo (hlLo ▸ hlen) h.1)
          (run_sound hB hsh d _ hiHi (hlHi ▸ hlen) h.2) hy
      · exact absurd h (by simp)
    · rw [hd, Bool.cond_true] at h
      exact run_sound hB hsh d _ hNs hlen h y hy

end Field

/-! ### Digit sizes -/

/-- A digit size for absolute coefficient sums up to `nb` with `h` bits of room:
`nb 2^h < 2^(B - 1)` (`lt_digitsFor`). -/
def digitsFor (nb h : ℕ) : ℕ := Nat.log2 (nb * 2 ^ h) + 2

theorem lt_digitsFor (nb h : ℕ) : nb * 2 ^ h < 2 ^ (digitsFor nb h - 1) := by
  simpa [digitsFor] using Nat.lt_log2_self

theorem digitsFor_pos (nb h : ℕ) : 0 < digitsFor nb h := Nat.succ_pos _

theorem le_digitsFor (nb h : ℕ) : nb < 2 ^ (digitsFor nb h - 1) :=
  lt_of_le_of_lt (Nat.le_mul_of_pos_right nb (Nat.two_pow_pos h)) (lt_digitsFor nb h)

variable (κ : Type) [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] in
/-- Bits for the approximations: `∑ⱼ |aⱼ| < 2^apxBits`. -/
def apxBits : ℕ := Nat.log2 (sumN (fun j ↦ (apxA κ j).natAbs) (ExactBasis.dim κ)) + 1

/-- The room for a run: the growth along the bisections, the vertex expansion (`3^e ≤ 4^e`) if
`dom`, and the approximations. -/
def room (apx : ℕ) (n : ℕ) (sh : List ℕ) (dom last : Bool) (depth : ℕ) (W : List ℤ) : ℕ :=
  growth last n sh depth W + (bif dom then 2 * sh.sum else 0) + apx

/-! ### Packed inputs -/

theorem absEval_one : ∀ (n : ℕ) (p : DPoly n), absEval n p (fun _ ↦ 1) = absSum n p
  | 0, _ => rfl
  | n + 1, p => by
    rw [absEval, absSum]
    have h : ∀ l : List (DPoly n), horner (fun q ↦ absEval n q (Fin.tail fun _ ↦ 1)) 1 l =
        (l.map (absSum n)).sum := by
      intro l
      induction l with
      | nil => rfl
      | cons a l ih =>
        rw [horner_cons, ih, List.map_cons, List.sum_cons, one_mul]
        exact congrArg (· + _) (absEval_one n a)
    exact h _

/-- **The invariant of packed inputs**: the biased packed value of a polynomial of shape `sh`
with coefficient sum at most `nb < 2^(B - 1)` satisfies `Inv`, and its slot polynomial is the
polynomial. -/
theorem inv_biased {n : ℕ} {sh : List ℕ} (hsh : sh.length ≤ n) {B : ℕ} (hB : 0 < B)
    {p : DPoly n} (hfit : Fits n p sh) {nb : ℕ} (hnb : absSum n p ≤ nb) (hlt : nb < 2 ^ (B - 1)) :
    Inv B sh (biased n sh B p).toNat ∧
      ∀ y : ℕ → ℝ, pv sh (cf B (biased n sh B p).toNat) y = eval n p fun i ↦ y i := by
  have hsmall : Small n B p :=
    allCoeff_mono n (fun c hc ↦ lt_of_le_of_lt (hc.trans hnb) hlt) (allCoeff_absSum_le n p)
  obtain ⟨h0, h1⟩ := biased_range n hB hfit hsmall
  refine ⟨⟨toNat_lt_two_pow h1, ?_⟩, fun y ↦ ?_⟩
  · rw [← absEval_unpack_eq_l1 B n sh hsh, absEval_unpack n hB hfit hsmall, absEval_one]
    exact lt_of_le_of_lt hnb hlt
  · rw [← eval_unpack_eq_pv B n sh hsh, eval_unpack n hB hfit hsmall]

end Lay

end Nieuwland.Check
