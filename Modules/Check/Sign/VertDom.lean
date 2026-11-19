import Modules.Check.Sign.Trunc
import Modules.Check.Sign.Box

/-!
# Dominance at a vertex at bounded precision

rupert's exact check of a box (`nonneg_exact_rec`, `code/src/proof/regional.rs`) bounds the
polynomial at the vertex where its centred linear part is smallest by vertex, then monomial,
dominance (`vertBound`, `monoBound`) of the vertex frame enclosed in intervals, with the exact
value at the vertex as its constant. Here the vertex frame comes exactly (numerals of digit size
`B`; from the sparse terms by Horner's rule, `Modules/Check/Sign/SparseBox.lean`), and `vdTest`
truncates it to `vdPrec` bits below a given bound of its absolute coefficient sums: each
coordinate `c` of each coefficient is floored in the direction of the sign `sg_c` of the basis
value `β_c` (`basisSg`), so that `β_c (a - 2^s t) ≥ 0` for every coefficient `a` and its
truncation `t`. On `[0, 1]^n`, where every monomial is in `[0, 1]`, the polynomial is then at
least `v + 2^s (P_t - t₀)`, with its exact constant `v` and the truncated polynomial `P_t` less
its constant `t₀`, and the dominance bounds of `P_t` read small numerals only (`vdTest_sound`).
Any bound and any shift are sound; the truncation's digits are checked to fit.

The truncation is uniform: `vdPrec` bits below the largest absolute sum, whatever the size of a
coefficient; rupert's enclosure is relative to each coefficient (`f64` intervals), and where the
vertex value is exactly zero rupert bounds the vertex frame computed exactly (`exact_dominance`,
`v.is_zero()`). At a pose of margin zero at the exact scale, or in a box next to one, the bound
rests on the smallest coefficients, which the uniform truncation rounds below zero. So `vdTest`
is a ladder of precisions (`vdLadder`): the test at `vdPrec` bits (`vdTestAt`, sound at any
precision, `vdTestAt_sound`), and while it fails by no more than the truncation can take from the
bound (`vdStage`: the bound plus `2^s` for every coefficient and coordinate has the sign) or the
vertex value is zero (`vertZero`), again at four times the precision, until nothing is truncated.
A failure by more than the truncation's error ends the ladder: the cost of the boxes that the
bisection must split stays that of one test. The choice of when to go on is not a premise.
-/

open Finset

namespace Nieuwland.Check

namespace Lay

open DPoly Num

section Field

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

variable (κ) in
/-- The basis value `β_c` as an exact value: the coordinates `0, …, 1, …, 0`. -/
def basisElt (c : ℕ) : κ :=
  ExactBasis.ofCoords ((List.range (ExactBasis.dim κ)).map fun c' ↦ bif c' == c then 1 else 0)

theorem re_basisElt {c : ℕ} (hc : c < ExactBasis.dim κ) :
    Exact.re (basisElt κ c) = ExactBasis.basis κ c := by
  rw [basisElt, ExactBasis.re_ofCoords, bsum,
    sum_eq_single c (fun c' hc' hne ↦ ?_) (fun h ↦ absurd (mem_range.mpr hc) h)]
  · rw [getD_map_of_eq (z := (0 : ℤ)) Int.cast_zero, Box.getD_range_map _ _ _ hc]
    simp
  · rw [getD_map_of_eq (z := (0 : ℤ)) Int.cast_zero, Box.getD_range_map _ _ _ (mem_range.mp hc')]
    simp [hne]

variable (κ) in
/-- The sign `sg_c` of the basis value `β_c`: `1` where it is decided nonnegative, `-1` where
decided nonpositive, else `0` (and `vdTest` fails). -/
def basisSg (c : ℕ) : ℤ :=
  bif Exact.nonneg (basisElt κ c) then 1
  else bif Exact.nonneg (Exact.ofInt 0 - basisElt κ c : κ) then -1 else 0

theorem basisSg_spec {c : ℕ} (hc : c < ExactBasis.dim κ) (h : basisSg κ c ≠ 0) :
    (basisSg κ c = 1 ∨ basisSg κ c = -1) ∧ 0 ≤ ExactBasis.basis κ c * (basisSg κ c : ℝ) := by
  unfold basisSg at h ⊢
  cases h₁ : Exact.nonneg (basisElt κ c)
  · cases h₂ : Exact.nonneg (Exact.ofInt 0 - basisElt κ c : κ)
    · simp [h₁, h₂] at h
    · have := Exact.nonneg_sound _ h₂
      rw [Exact.re_sub, Exact.re_ofInt, re_basisElt hc, Int.cast_zero] at this
      change ((-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1) ∧ 0 ≤ ExactBasis.basis κ c * ((-1 : ℤ) : ℝ)
      refine ⟨Or.inr rfl, ?_⟩
      push_cast
      linarith
  · have := Exact.nonneg_sound _ h₁
    rw [re_basisElt hc] at this
    change ((1 : ℤ) = 1 ∨ (1 : ℤ) = -1) ∧ 0 ≤ ExactBasis.basis κ c * ((1 : ℤ) : ℝ)
    refine ⟨Or.inl rfl, ?_⟩
    push_cast
    linarith

/-- The first precision of the truncated vertex frame: bits below the bound of its absolute
sums. -/
def vdPrec : ℕ := 64

variable (κ) in
/-- **Dominance of an exact vertex frame at the precision `prec`** (`vdTestAt_sound`): the
numerals `Vs` (digit size `B`, shape `sh`) of the coordinates of a polynomial on `[0, 1]^n`, given
a bound `lmax` of their absolute coefficient sums (any is sound). The coordinates are truncated
(`truncL`, `basisSg`) `prec` bits below `lmax` into numerals of digit size `B'` whose digit
sums must fit; then vertex dominance, and where it fails monomial dominance, bounds the truncated
polynomial, and the bound with the exact constant `v` must have the sign. Where `prec` is more
than the bits of `lmax`, nothing is truncated. -/
def vdTestAt (prec n : ℕ) (sh : List ℕ) (B : ℕ) (strict : Bool) (lmax : ℕ) (Vs : List ℕ) : Bool :=
  let d := ExactBasis.dim κ
  let L := slots sh
  let s := Nat.log2 lmax + 1 - prec
  let B' := prec + Nat.log2 L + 3
  let T := (List.range d).map fun c ↦ truncL B B' s (2 ^ (B - 1)) (basisSg κ c) L (Vs.getD c 0)
  let Ns := (List.range d).map fun c ↦ (basisSg κ c * (T.getD c (0, 0)).1 + offN B' sh).toNat
  let v : κ := ExactBasis.ofCoords ((List.range d).map fun c ↦ cf0 B (Vs.getD c 0))
  let t0 : κ := ExactBasis.ofCoords ((List.range d).map fun c ↦ cf0 B' (Ns.getD c 0))
  let ms := monosP (κ := κ) (2 ^ (B' - 1)) (2 ^ B') (DPoly.layout B' (nEff n sh) sh) 1 0 Ns []
  let ok := fun lb : κ × Bool ↦ lb.2 && signTest strict (v + Exact.ofInt (2 ^ s) * (lb.1 - t0))
  (List.range d).all (fun c ↦ basisSg κ c != 0 && decide ((T.getD c (0, 0)).2 < 2 ^ (B' - 1))) &&
    (DPoly.layout B' n sh).all (fun l ↦ Nat.ble l.1 65536) &&
    (ok (vertBound n ms) || ok (monoBound n ms))

/-- The dominance terms read off packed coordinates are the polynomial `∑ⱼ βⱼ Tⱼ` of the
unpacked numerals (as in `domOf_le`). -/
theorem psum_monos_layout {n : ℕ} (sh : List ℕ) (B : ℕ) (Ns : List ℕ) (y : Fin n → ℝ)
    (hlen : ExactBasis.dim κ ≤ Ns.length)
    (hc : ∀ l ∈ DPoly.layout B n sh, Nat.ble l.1 65536 = true) :
    psum n (monosP (κ := κ) (2 ^ (B - 1)) (2 ^ B) (DPoly.layout B (nEff n sh) sh) 1 0 Ns []) y =
      ∑ j ∈ range (ExactBasis.dim κ),
        ExactBasis.basis κ j * DPoly.eval n (DPoly.unpack n sh B (Ns.getD j 0)) y := by
  rw [← monoSumK_monosK n sh Ns y hlen, ← psum_monosP _ _ _ _
    fun l hl ↦ le_of_le_of_eq (Nat.le_of_ble_eq_true (hc l hl)) (by norm_num),
    layout_trim B n sh, monosP_trim]

/-- A monomial on `[0, 1]^n` is nonnegative. -/
theorem mono_nonneg_unit (sh : List ℕ) (q : ℕ) {u : ℕ → ℝ} (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1) :
    0 ≤ mono sh q u :=
  prod_nonneg fun i _ ↦ pow_nonneg (hu i).1 _

/-- **The directed truncation of one coordinate**: with `g = ±1` of the sign of `β`
(`0 ≤ β g`), the digits `τ_q = g ⌊a_q g / 2^s⌋` satisfy
`β pv a ≥ β (a₀ - 2^s τ₀) + 2^s β pv τ` on `[0, 1]^n`. -/
theorem trunc_coord_le (sh : List ℕ) (a : ℕ → ℤ) {g : ℤ} (hg : g = 1 ∨ g = -1) {β : ℝ}
    (hβ : 0 ≤ β * g) (s : ℕ) {u : ℕ → ℝ} (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1) :
    β * ((a 0 : ℝ) - 2 ^ s * (g * (a 0 * g / 2 ^ s) : ℤ)) +
        2 ^ s * (β * pv sh (fun q ↦ g * (a q * g / 2 ^ s)) u) ≤
      β * pv sh a u := by
  have hP : (0 : ℤ) < 2 ^ s := by positivity
  have hg2 : g * g = 1 := by rcases hg with rfl | rfl <;> rfl
  -- `a - 2^s τ = g r` with `r = (a g) mod 2^s ≥ 0`.
  have hr : ∀ q, a q - 2 ^ s * (g * (a q * g / 2 ^ s)) = g * (a q * g % 2 ^ s) := by
    intro q
    have := Int.emod_def (a q * g) (2 ^ s)
    linear_combination (-g) * this - a q * hg2
  have hdiff : β * pv sh a u - 2 ^ s * (β * pv sh (fun q ↦ g * (a q * g / 2 ^ s)) u) =
      ∑ q ∈ range (slots sh), β * ((g * (a q * g % 2 ^ s) : ℤ) : ℝ) * mono sh q u := by
    unfold pv
    rw [mul_sum, mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun q _ ↦ ?_
    rw [← hr q]
    push_cast
    ring
  have hterm : ∀ q ∈ range (slots sh), 0 ≤ β * ((g * (a q * g % 2 ^ s) : ℤ) : ℝ) * mono sh q u := by
    intro q _
    refine mul_nonneg ?_ (mono_nonneg_unit sh q hu)
    have h₁ : (0 : ℝ) ≤ ((a q * g % 2 ^ s : ℤ) : ℝ) := by
      exact_mod_cast Int.emod_nonneg _ hP.ne'
    push_cast
    rw [← mul_assoc]
    exact mul_nonneg hβ h₁
  have h0 := single_le_sum hterm (mem_range.mpr (slots_pos sh))
  rw [mono_zero, mul_one, ← hdiff] at h0
  have h₂ : ((g * (a 0 * g % 2 ^ s) : ℤ) : ℝ) =
      (a 0 : ℝ) - 2 ^ s * (g * (a 0 * g / 2 ^ s) : ℤ) := by
    rw [← hr 0]
    push_cast
    ring
  rw [h₂] at h0
  linarith

/-- **Soundness of `vdTestAt`**, at any precision: if it passes on numerals `Vs` that fit their
slots, the polynomial `∑_c β_c pv_c` of their coordinates has the sign on `[0, 1]^n`. -/
theorem vdTestAt_sound {prec n : ℕ} {sh : List ℕ} {B : ℕ} {strict : Bool} {lmax : ℕ}
    {Vs : List ℕ} (hsh : sh.length ≤ n)
    (hV : ∀ c < ExactBasis.dim κ, Vs.getD c 0 < 2 ^ (B * slots sh))
    (h : vdTestAt κ prec n sh B strict lmax Vs = true) {u : ℕ → ℝ}
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1) :
    Sign strict (∑ c ∈ range (ExactBasis.dim κ),
      ExactBasis.basis κ c * pv sh (cf B (Vs.getD c 0)) u) := by
  simp only [vdTestAt, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, List.mem_range,
    bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hfit, hlay⟩, hok⟩ := h
  set d := ExactBasis.dim κ with hd
  set L := slots sh with hL
  set s := Nat.log2 lmax + 1 - prec with hs
  set B' := prec + Nat.log2 L + 3 with hB'
  have hB'0 : 0 < B' := by omega
  set g : ℕ → ℤ := fun c ↦ basisSg κ c with hgdef
  set a : ℕ → ℕ → ℤ := fun c ↦ cf B (Vs.getD c 0) with ha
  set τ : ℕ → ℕ → ℤ := fun c q ↦ g c * (a c q * g c / 2 ^ s) with hτ
  set T := (List.range d).map fun c ↦ truncL B B' s (2 ^ (B - 1)) (g c) L (Vs.getD c 0) with hT
  set Ns := (List.range d).map fun c ↦ (g c * (T.getD c (0, 0)).1 + offN B' sh).toNat with hNs
  -- The truncations.
  have hTc : ∀ c < d, T.getD c (0, 0) = (snum B' (fun q ↦ a c q * g c / 2 ^ s) L,
      ∑ q ∈ range L, (a c q * g c / 2 ^ s).natAbs) := by
    intro c hc
    rw [hT, Box.getD_range_map _ _ _ hc, truncL_eq _ _ _ _ _ _ _ (hV c hc)]
    have hdq : ∀ q, ((dig B (Vs.getD c 0) q : ℤ) - ((2 ^ (B - 1) : ℕ) : ℤ)) * g c / 2 ^ s =
        a c q * g c / 2 ^ s := fun q ↦ by
      simp only [ha, cf]
      push_cast
      ring
    simp only [hdq]
  have hgc : ∀ c < d, (g c = 1 ∨ g c = -1) ∧ 0 ≤ ExactBasis.basis κ c * (g c : ℝ) :=
    fun c hc ↦ basisSg_spec hc (hfit c hc).1
  have hl1 : ∀ c < d, l1 sh (τ c) < 2 ^ (B' - 1) := by
    intro c hc
    have h₁ := (hfit c hc).2
    rw [hTc c hc] at h₁
    refine lt_of_le_of_lt (le_of_eq ?_) h₁
    unfold l1
    refine sum_congr rfl fun q _ ↦ ?_
    rw [hτ, Int.natAbs_mul]
    rcases (hgc c hc).1 with h₂ | h₂ <;> simp [h₂]
  have hdig : ∀ c < d, ∀ q < L, -2 ^ (B' - 1) ≤ τ c q ∧ τ c q < 2 ^ (B' - 1) := by
    intro c hc q hq
    have h₁ := (abs_coeff_le_l1 (τ c) hq).trans_lt (hl1 c hc)
    have h₂ : |τ c q| < 2 ^ (B' - 1) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h₁
    constructor <;> linarith [abs_lt.mp h₂]
  have hNc : ∀ c < d, Ns.getD c 0 = num B' (fun q ↦ (τ c q + 2 ^ (B' - 1)).toNat) L := by
    intro c hc
    obtain ⟨hbias, -⟩ := snum_add_bias hB'0 (hdig c hc)
    rw [hNs, Box.getD_range_map _ _ _ hc, hTc c hc, snum_mul, offN_eq]
    simp only [hτ] at hbias
    rw [hbias, Int.toNat_natCast]
  have hcf : ∀ c < d, ∀ q < L, cf B' (Ns.getD c 0) q = τ c q := by
    intro c hc q hq
    obtain ⟨-, hdg⟩ := snum_add_bias hB'0 (hdig c hc)
    rw [hNc c hc, cf, dig_num hB'0 hdg hq, Int.toNat_of_nonneg (by linarith [(hdig c hc q hq).1])]
    ring
  -- The dominance bound of the truncated polynomial.
  have hlenN : d ≤ Ns.length := by simp [hNs]
  have hdom : ∀ lb : κ × Bool, (lb = vertBound n (monosP (κ := κ) (2 ^ (B' - 1)) (2 ^ B')
        (DPoly.layout B' (nEff n sh) sh) 1 0 Ns []) ∨ lb = monoBound n (monosP (κ := κ)
        (2 ^ (B' - 1)) (2 ^ B') (DPoly.layout B' (nEff n sh) sh) 1 0 Ns [])) → lb.2 = true →
      Exact.re lb.1 ≤ ∑ c ∈ range d, ExactBasis.basis κ c * pv sh (τ c) u := by
    intro lb hlb h2
    have hy : ∀ i : Fin n, 0 ≤ u i ∧ u i ≤ 1 := fun i ↦ hu i
    have hp := psum_monos_layout (κ := κ) sh B' Ns (fun i : Fin n ↦ u i) hlenN hlay
    have hle : Exact.re lb.1 ≤ psum n (monosP (κ := κ) (2 ^ (B' - 1)) (2 ^ B')
        (DPoly.layout B' (nEff n sh) sh) 1 0 Ns []) (fun i : Fin n ↦ u i) := by
      rcases hlb with rfl | rfl
      · exact vertBound_le hy _ h2
      · exact monoBound_le hy _ h2
    rw [hp] at hle
    refine hle.trans (le_of_eq (sum_congr rfl fun c hc ↦ ?_))
    rw [eval_unpack_eq_pv B' n sh hsh, pv_congr (hcf c (mem_range.mp hc))]
  -- The exact constant and the truncated one.
  have hv : Exact.re (ExactBasis.ofCoords ((List.range d).map fun c ↦ cf0 B (Vs.getD c 0)) : κ) =
      ∑ c ∈ range d, ExactBasis.basis κ c * (a c 0 : ℝ) := by
    rw [ExactBasis.re_ofCoords, bsum]
    refine sum_congr rfl fun c hc ↦ ?_
    rw [getD_map_of_eq (z := (0 : ℤ)) Int.cast_zero, Box.getD_range_map _ _ _ (mem_range.mp hc),
      cf0_eq]
  have ht0 : Exact.re (ExactBasis.ofCoords ((List.range d).map fun c ↦ cf0 B' (Ns.getD c 0)) : κ) =
      ∑ c ∈ range d, ExactBasis.basis κ c * (τ c 0 : ℝ) := by
    rw [ExactBasis.re_ofCoords, bsum]
    refine sum_congr rfl fun c hc ↦ ?_
    rw [getD_map_of_eq (z := (0 : ℤ)) Int.cast_zero, Box.getD_range_map _ _ _ (mem_range.mp hc),
      cf0_eq, hcf c (mem_range.mp hc) 0 (slots_pos sh)]
  -- The truncation errors are nonnegative on the cube.
  have htr : ∑ c ∈ range d, ExactBasis.basis κ c * ((a c 0 : ℝ) - 2 ^ s * (τ c 0 : ℝ)) +
      2 ^ s * ∑ c ∈ range d, ExactBasis.basis κ c * pv sh (τ c) u ≤
      ∑ c ∈ range d, ExactBasis.basis κ c * pv sh (a c) u := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun c hc ↦ ?_
    have hc' := mem_range.mp hc
    have := trunc_coord_le sh (a c) (hgc c hc').1 (hgc c hc').2 s hu
    simpa [hτ] using this
  rcases hok with h' | h'
  all_goals
    obtain ⟨h2, hsg⟩ := h'
    refine sign_of_le (sign_of_signTest hsg) ?_
    rw [Exact.re_add, Exact.re_mul, Exact.re_ofInt, Exact.re_sub, hv, ht0]
  · have hb := hdom _ (Or.inl rfl) h2
    have e : ∑ c ∈ range d, ExactBasis.basis κ c * ((a c 0 : ℝ) - 2 ^ s * (τ c 0 : ℝ)) =
        ∑ c ∈ range d, ExactBasis.basis κ c * (a c 0 : ℝ) -
          2 ^ s * ∑ c ∈ range d, ExactBasis.basis κ c * (τ c 0 : ℝ) := by
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun c _ ↦ by ring
    rw [e] at htr
    push_cast
    have h2s : (0 : ℝ) ≤ 2 ^ s := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hb h2s]
  · have hb := hdom _ (Or.inr rfl) h2
    have e : ∑ c ∈ range d, ExactBasis.basis κ c * ((a c 0 : ℝ) - 2 ^ s * (τ c 0 : ℝ)) =
        ∑ c ∈ range d, ExactBasis.basis κ c * (a c 0 : ℝ) -
          2 ^ s * ∑ c ∈ range d, ExactBasis.basis κ c * (τ c 0 : ℝ) := by
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun c _ ↦ by ring
    rw [e] at htr
    push_cast
    have h2s : (0 : ℝ) ≤ 2 ^ s := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hb h2s]

variable (κ) in
/-- The vertex value of the numerals `Vs` is zero: every coordinate of the constant is. -/
def vertZero (B : ℕ) (Vs : List ℕ) : Bool :=
  (List.range (ExactBasis.dim κ)).all fun c ↦ cf0 B (Vs.getD c 0) == 0

/-- The outcome of a stage from its parts: whether it passes (`fit`, and one of the bounds `vb`,
`mb` is `ok`: `stageOf_fst`), and where it fails with `fit`, whether one of the bounds is `near`.
The second bound is computed only where the first is not `ok`. -/
def stageOf {β : Type} (fit : Bool) (vb mb : Unit → β) (ok near : β → Bool) : Bool × Bool :=
  bif fit then
    let x := vb ()
    bif ok x then (true, true) else
      let y := mb ()
      bif ok y then (true, true) else (false, near x || near y)
  else (false, false)

theorem stageOf_fst {β : Type} (fit : Bool) (vb mb : Unit → β) (ok near : β → Bool) :
    (stageOf fit vb mb ok near).1 = (fit && (ok (vb ()) || ok (mb ()))) := by
  simp only [stageOf]
  cases fit <;> cases ok (vb ()) <;> cases ok (mb ()) <;> rfl

variable (κ) in
/-- **One stage of the ladder**: `vdTestAt` at the precision `prec` (`vdStage_fst`), and where it
fails with digits that fit, whether it is near: one of the two bounds with the truncation's
error added (`2^s` for each of the `slots sh` coefficients, times the sum of the absolute basis
values) has the sign. -/
def vdStage (prec n : ℕ) (sh : List ℕ) (B : ℕ) (strict : Bool) (lmax : ℕ) (Vs : List ℕ) :
    Bool × Bool :=
  let d := ExactBasis.dim κ
  let L := slots sh
  let s := Nat.log2 lmax + 1 - prec
  let B' := prec + Nat.log2 L + 3
  let T := (List.range d).map fun c ↦ truncL B B' s (2 ^ (B - 1)) (basisSg κ c) L (Vs.getD c 0)
  let Ns := (List.range d).map fun c ↦ (basisSg κ c * (T.getD c (0, 0)).1 + offN B' sh).toNat
  let v : κ := ExactBasis.ofCoords ((List.range d).map fun c ↦ cf0 B (Vs.getD c 0))
  let t0 : κ := ExactBasis.ofCoords ((List.range d).map fun c ↦ cf0 B' (Ns.getD c 0))
  let ms := monosP (κ := κ) (2 ^ (B' - 1)) (2 ^ B') (DPoly.layout B' (nEff n sh) sh) 1 0 Ns []
  stageOf ((List.range d).all (fun c ↦ basisSg κ c != 0 &&
        decide ((T.getD c (0, 0)).2 < 2 ^ (B' - 1))) &&
      (DPoly.layout B' n sh).all (fun l ↦ Nat.ble l.1 65536))
    (fun _ ↦ vertBound n ms) (fun _ ↦ monoBound n ms)
    (fun lb : κ × Bool ↦ lb.2 && signTest strict (v + Exact.ofInt (2 ^ s) * (lb.1 - t0)))
    (fun lb : κ × Bool ↦ lb.2 && signTest strict (v + Exact.ofInt (2 ^ s) * (lb.1 - t0) +
      Exact.ofInt (2 ^ s * L) * ExactBasis.ofCoords ((List.range d).map (basisSg κ))))

theorem vdStage_fst (prec n : ℕ) (sh : List ℕ) (B : ℕ) (strict : Bool) (lmax : ℕ) (Vs : List ℕ) :
    (vdStage κ prec n sh B strict lmax Vs).1 = vdTestAt κ prec n sh B strict lmax Vs := by
  simp only [vdStage, stageOf_fst, vdTestAt]

variable (κ) in
/-- **The ladder of precisions** from `p`: the stage at `p` (`vdStage`); where it fails near, or
at a vertex value of zero (`vertZero`), and still truncates (`p` is less than the bits of `lmax`),
the ladder from `4 p`; at most `fuel` stages. -/
def vdLadder (n : ℕ) (sh : List ℕ) (B : ℕ) (strict : Bool) (lmax : ℕ) (Vs : List ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, p =>
    let r := vdStage κ p n sh B strict lmax Vs
    r.1 || ((r.2 || vertZero κ B Vs) && !Nat.ble (Nat.log2 lmax + 1) p &&
      vdLadder n sh B strict lmax Vs fuel (4 * p))

variable (κ) in
/-- **Dominance of an exact vertex frame** (`vdTest_sound`): the ladder of precisions from
`vdPrec` (`vdLadder`), up to the frame as it is. rupert's order (`nonneg_exact_rec`) is the
enclosed frame, then the exact one at a zero (`exact_dominance`); the ladder passes wherever
either does on the same buckets. -/
def vdTest (n : ℕ) (sh : List ℕ) (B : ℕ) (strict : Bool) (lmax : ℕ) (Vs : List ℕ) : Bool :=
  vdLadder κ n sh B strict lmax Vs (Nat.log2 lmax + 2) vdPrec

/-- **Soundness of `vdTest`**: if it passes on numerals `Vs` that fit their slots, the polynomial
`∑_c β_c pv_c` of their coordinates has the sign on `[0, 1]^n`. -/
theorem vdTest_sound {n : ℕ} {sh : List ℕ} {B : ℕ} {strict : Bool} {lmax : ℕ} {Vs : List ℕ}
    (hsh : sh.length ≤ n) (hV : ∀ c < ExactBasis.dim κ, Vs.getD c 0 < 2 ^ (B * slots sh))
    (h : vdTest κ n sh B strict lmax Vs = true) {u : ℕ → ℝ} (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1) :
    Sign strict (∑ c ∈ range (ExactBasis.dim κ),
      ExactBasis.basis κ c * pv sh (cf B (Vs.getD c 0)) u) := by
  have key : ∀ fuel p, vdLadder κ n sh B strict lmax Vs fuel p = true →
      Sign strict (∑ c ∈ range (ExactBasis.dim κ),
        ExactBasis.basis κ c * pv sh (cf B (Vs.getD c 0)) u) := by
    intro fuel
    induction fuel with
    | zero => intro p h; simp [vdLadder] at h
    | succ fuel ih =>
      intro p h
      rw [vdLadder, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with h | ⟨-, h⟩
      · rw [vdStage_fst] at h
        exact vdTestAt_sound hsh hV h hu
      · exact ih _ h
  exact key _ _ h

end Field

end Lay

end Nieuwland.Check
