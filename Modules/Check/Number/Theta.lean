import Modules.Check.Number.Ext
import Modules.System.RealRoot
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Logic.Equiv.List

/-!
# Exact values over a number field

A body over `ℚ(θ)`, for the root `θ = realRoot m lo hi` of a rational polynomial `m` in an
isolating interval (`Modules/System/RealRoot.lean`), has rational polynomials in `θ` as coordinates. For
an integer `c > 0` with `α = c θ` a root of a monic integer polynomial `N` of degree `n`, they are,
times a common denominator, integer polynomials of degree `< n` in `α`: the elements of `ℤ[α]`.
`ZTheta R` represents them by their coordinates in the basis `1, α, …, α^(n-1)`.

`Root` holds the data of `θ` with a kernel check (`Root.ok`) that
* `Nᵢ mₙ = mᵢ c^(n-i)` for every `i`, so that `N (c x) mₙ = cⁿ m(x)` (`coefCheck`);
* `N` is injective on a coarse enclosure `[A/E, B/E] ⊆ [c lo, c hi]`, its derivative having a sign
  there (`lipPos`), and has no root in `[B/E, Yh/E] ⊇ [B/E, c hi]` (`excl`: pieces `[x, x + w]` on
  which the constant coefficient of the Taylor shift `P(x + T)` of `P(y) = E^n N(y/E)` exceeds the
  others' bound, the width doubling after a piece and halving after a failure) (`coarseCheck`);
* `N` changes sign on a fine enclosure `[Xl/D, Xh/D] ⊆ [A/E, B/E]` (`fineCheck`).
Then `α = c θ` lies in `[Xl/D, Xh/D]` and `N(α) = 0` (`Root.spec`): `m` has a root in
`c⁻¹ [Xl/D, Xh/D]` and none above it in the interval, so the largest root `θ` lies there. Nothing is
assumed about `m`: `θ` is a definite real number whatever the interval holds.

Values multiply by reduction modulo `N` (`mulG`, Horner's scheme over the shorter factor). Signs
are read off a ball first (`ZTheta.ballWith`, `Exact.ball`): the coordinates against
approximations of `2^64 αⁱ` (`apxList`, computed once with the instance), a few integer products
that decide every value not within about `2^-58` of `0` relative to its coordinates. Otherwise the
sign of `a(α)` is decided on the enclosure: `a(α) > 0` if `a(Xl/D)` exceeds a Lipschitz bound of
`a` times the width of the enclosure (`lipPos`, `sgnAt`); the exporter takes `D = 2^512`, which
decides all but nearly cancelling values. Those are decided on enclosures refined by bisection,
each half checked like the fine enclosure (`Root.sgnRef`), as Rust's exact sign refines its
isolating interval; the number of bisections (`Root.refineFuel`) suffices for every nonzero value
if `N` is irreducible. `isZero` tests the coordinates. All arithmetic is over the integers, with
`D` cleared (`hv`, `hb`, `hl`, computed in one pass each by `hvP` and `hblP`).

## Main definitions

* `Nieuwland.Check.evalZ`: integer polynomials at real points.
* `Nieuwland.Check.lipPos`, `Nieuwland.Check.sgnAt`, `Nieuwland.Check.excl`: signs and root exclusion
  on intervals.
* `Nieuwland.Check.tshift`, `Nieuwland.Check.scl`: Taylor shifts and scaled polynomials.
* `Nieuwland.Check.Root`: the data of `θ` with its check; `Root.spec`, `Root.enclose`; refined signs
  `Root.sgnRef`.
* `Nieuwland.Check.ZTheta R`: `ℤ[c θ]`, with `Exact` and `ExactBasis` instances.
-/

open Finset

namespace Nieuwland.Check

/-! ### Integer polynomials at real points -/

/-- `∑ᵢ pᵢ xⁱ` for integer coefficients listed from the constant one. -/
noncomputable def evalZ (p : List ℤ) (x : ℝ) : ℝ :=
  ∑ i ∈ range p.length, (p.getD i 0 : ℝ) * x ^ i

theorem evalZ_nil (x : ℝ) : evalZ [] x = 0 := by
  simp [evalZ]

theorem evalZ_cons (a : ℤ) (q : List ℤ) (x : ℝ) : evalZ (a :: q) x = a + x * evalZ q x := by
  rw [evalZ, evalZ, List.length_cons, sum_range_succ', mul_sum, add_comm]
  simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one]
  congr 1
  exact sum_congr rfl fun i _ ↦ by ring

/-- The sum may run over any range containing the coefficients. -/
theorem evalZ_eq_sum {p : List ℤ} {m : ℕ} (h : p.length ≤ m) (x : ℝ) :
    evalZ p x = ∑ i ∈ range m, (p.getD i 0 : ℝ) * x ^ i := by
  refine sum_subset (range_subset_range.mpr h) fun i _ hi ↦ ?_
  rw [List.getD_eq_default _ _ (by simpa using hi), Int.cast_zero, zero_mul]

theorem continuous_evalZ (p : List ℤ) : Continuous (evalZ p) :=
  continuous_finsetSum _ fun i _ ↦ continuous_const.mul (continuous_pow i)

/-! ### Scaled Horner schemes -/

/-- `D^(L-1) p(X/D)` for `p` of length `L ≥ 1` (`hv_mul`), by Horner's scheme over the integers. -/
def hv (D X : ℤ) : List ℤ → ℤ
  | [] => 0
  | a :: q => a * D ^ q.length + X * hv D X q

/-- `D^(L-1)` times a bound of `|p|` on `[-M/D, M/D]` (`hb_bound`). -/
def hb (D M : ℤ) : List ℤ → ℤ
  | [] => 0
  | a :: q => |a| * D ^ q.length + M * hb D M q

/-- `D^(L-2)` times a Lipschitz constant of `p` on `[-M/D, M/D]` (`hl_bound`). -/
def hl (D M : ℤ) : List ℤ → ℤ
  | [] => 0
  | _ :: q => hb D M q + M * hl D M q

/-- `(hv D X p, D^L)` in one pass (`hvP_eq`): how checks compute `hv`. -/
def hvP (D X : ℤ) : List ℤ → ℤ × ℤ
  | [] => (0, 1)
  | a :: q => let (v, d) := hvP D X q; (a * d + X * v, D * d)

/-- `(hb D M p, hl D M p, D^L)` in one pass (`hblP_eq`): how checks compute `hb` and `hl`. -/
def hblP (D M : ℤ) : List ℤ → ℤ × ℤ × ℤ
  | [] => (0, 0, 1)
  | a :: q => let (b, l, d) := hblP D M q; (|a| * d + M * b, b + M * l, D * d)

theorem hvP_eq (D X : ℤ) : ∀ p : List ℤ, hvP D X p = (hv D X p, D ^ p.length)
  | [] => by simp [hvP, hv]
  | a :: q => by simp only [hvP, hvP_eq D X q, hv, List.length_cons, pow_succ']

theorem hblP_eq (D M : ℤ) : ∀ p : List ℤ, hblP D M p = (hb D M p, hl D M p, D ^ p.length)
  | [] => by simp [hblP, hb, hl]
  | a :: q => by simp only [hblP, hblP_eq D M q, hb, hl, List.length_cons, pow_succ']

section Horner

variable {D M : ℤ}

theorem hv_mul (hD : 0 < D) (X : ℤ) : ∀ p : List ℤ,
    (hv D X p : ℝ) * D = (D : ℝ) ^ p.length * evalZ p (X / D)
  | [] => by simp [hv, evalZ_nil]
  | a :: q => by
    have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    rw [hv, evalZ_cons, List.length_cons]
    push_cast
    rw [add_mul, mul_assoc (X : ℝ), hv_mul hD X q]
    field_simp
    ring

theorem hb_nonneg (hD : 0 < D) (hM : 0 ≤ M) : ∀ p : List ℤ, 0 ≤ hb D M p
  | [] => le_rfl
  | a :: q => add_nonneg (mul_nonneg (abs_nonneg a) (pow_nonneg hD.le _))
      (mul_nonneg hM (hb_nonneg hD hM q))

theorem hl_nonneg (hD : 0 < D) (hM : 0 ≤ M) : ∀ p : List ℤ, 0 ≤ hl D M p
  | [] => le_rfl
  | _ :: q => add_nonneg (hb_nonneg hD hM q) (mul_nonneg hM (hl_nonneg hD hM q))

theorem hb_bound (hD : 0 < D) (hM : 0 ≤ M) {x : ℝ} (hx : |x| * D ≤ M) : ∀ p : List ℤ,
    |evalZ p x| * (D : ℝ) ^ p.length ≤ (hb D M p : ℝ) * D
  | [] => by simp [evalZ_nil, hb]
  | a :: q => by
    have ih := hb_bound hD hM hx q
    have hDr : (0 : ℝ) < D := by exact_mod_cast hD
    have hM' : (0 : ℝ) ≤ M := by exact_mod_cast hM
    rw [evalZ_cons, hb, List.length_cons, pow_succ]
    push_cast
    calc |(a : ℝ) + x * evalZ q x| * ((D : ℝ) ^ q.length * D)
        ≤ (|(a : ℝ)| + |x| * |evalZ q x|) * ((D : ℝ) ^ q.length * D) := by
          refine mul_le_mul_of_nonneg_right ((abs_add_le _ _).trans ?_) (by positivity)
          rw [abs_mul]
      _ = |(a : ℝ)| * D ^ q.length * D + |x| * D * (|evalZ q x| * D ^ q.length) := by ring
      _ ≤ |(a : ℝ)| * D ^ q.length * D + M * (hb D M q * D) :=
          add_le_add le_rfl (mul_le_mul hx ih (by positivity) hM')
      _ = (|(a : ℝ)| * D ^ q.length + M * hb D M q) * D := by ring

theorem hl_bound (hD : 0 < D) (hM : 0 ≤ M) {x y : ℝ} (hx : |x| * D ≤ M) (hy : |y| * D ≤ M) :
    ∀ p : List ℤ,
      |evalZ p x - evalZ p y| * (D : ℝ) ^ p.length ≤ (hl D M p : ℝ) * D * D * |x - y|
  | [] => by simp [evalZ_nil, hl]
  | a :: q => by
    have ih := hl_bound hD hM hx hy q
    have hbq := hb_bound hD hM hx q
    have hDr : (0 : ℝ) < D := by exact_mod_cast hD
    have hM' : (0 : ℝ) ≤ M := by exact_mod_cast hM
    rw [evalZ_cons, evalZ_cons, hl, List.length_cons, pow_succ]
    push_cast
    have e : (a : ℝ) + x * evalZ q x - (a + y * evalZ q y) =
        (x - y) * evalZ q x + y * (evalZ q x - evalZ q y) := by ring
    rw [e]
    calc |(x - y) * evalZ q x + y * (evalZ q x - evalZ q y)| * ((D : ℝ) ^ q.length * D)
        ≤ (|x - y| * |evalZ q x| + |y| * |evalZ q x - evalZ q y|) *
            ((D : ℝ) ^ q.length * D) := by
          refine mul_le_mul_of_nonneg_right ((abs_add_le _ _).trans ?_) (by positivity)
          rw [abs_mul, abs_mul]
      _ = |x - y| * D * (|evalZ q x| * D ^ q.length) +
            |y| * D * (|evalZ q x - evalZ q y| * D ^ q.length) := by ring
      _ ≤ |x - y| * D * (hb D M q * D) + M * (hl D M q * D * D * |x - y|) :=
          add_le_add (mul_le_mul_of_nonneg_left hbq (by positivity))
            (mul_le_mul hy ih (by positivity) hM')
      _ = (hb D M q + M * hl D M q) * D * D * |x - y| := by ring

/-- `|y| D ≤ M` on `[X₁/D, X₂/D]` when `|X₁|, |X₂| ≤ M`. -/
theorem abs_mul_le_of_mem (hD : 0 < D) {X₁ X₂ : ℤ} (h₁ : |X₁| ≤ M) (h₂ : |X₂| ≤ M) {y : ℝ}
    (hy₁ : (X₁ : ℝ) / D ≤ y) (hy₂ : y ≤ X₂ / D) : |y| * D ≤ M := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have k₁ : (X₁ : ℝ) ≤ y * D := by rwa [div_le_iff₀ hDr] at hy₁
  have k₂ : y * D ≤ X₂ := by rwa [le_div_iff₀ hDr] at hy₂
  have := abs_le_max_abs_abs k₁ k₂
  rw [abs_mul, abs_of_pos hDr] at this
  exact this.trans (max_le (by exact_mod_cast h₁) (by exact_mod_cast h₂))

/-- On `[X/D, (X + w)/D]`, `p` moves by at most `hl D M p w / D^(L-1)`. -/
theorem evalZ_sub_le (hD : 0 < D) {X w : ℤ} (h₁ : |X| ≤ M) (h₂ : |X + w| ≤ M) (p : List ℤ)
    {y : ℝ} (hy₁ : (X : ℝ) / D ≤ y) (hy₂ : y ≤ (X + w : ℤ) / D) :
    |evalZ p y - evalZ p (X / D)| * (D : ℝ) ^ p.length ≤ hl D M p * D * w := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hM : 0 ≤ M := (abs_nonneg _).trans h₁
  have hx : |(X : ℝ) / D| * D ≤ M := by
    rw [abs_div, abs_of_pos hDr, div_mul_cancel₀ _ hDr.ne']
    exact_mod_cast h₁
  have hb := hl_bound hD hM (abs_mul_le_of_mem hD h₁ h₂ hy₁ hy₂) hx p
  have hw : |y - X / D| * D ≤ w := by
    rw [abs_of_nonneg (sub_nonneg.mpr hy₁), sub_mul, div_mul_cancel₀ _ hDr.ne']
    have := (le_div_iff₀ hDr).mp hy₂
    push_cast at this
    linarith
  have hl0 : (0 : ℝ) ≤ hl D M p := by exact_mod_cast hl_nonneg hD hM p
  calc |evalZ p y - evalZ p (X / D)| * (D : ℝ) ^ p.length
      ≤ hl D M p * D * D * |y - X / D| := hb
    _ = (hl D M p * D) * (|y - X / D| * D) := by ring
    _ ≤ (hl D M p * D) * w := mul_le_mul_of_nonneg_left hw (by positivity)

end Horner

/-! ### Signs and roots on intervals -/

/-- `p` is positive on `[Xl/D, Xh/D]`, for `M ≥ |Xl|, |Xh|`: its value at `Xl/D` exceeds the
Lipschitz bound times the width. -/
def lipPos (D M Xl Xh : ℤ) (p : List ℤ) : Bool :=
  decide ((hblP D M p).2.1 * (Xh - Xl) < (hvP D Xl p).1)

theorem lipPos_sound {D M Xl Xh : ℤ} (hD : 0 < D) (h₁ : |Xl| ≤ M) (h₂ : |Xh| ≤ M) {p : List ℤ}
    (h : lipPos D M Xl Xh p = true) {y : ℝ} (hy₁ : (Xl : ℝ) / D ≤ y) (hy₂ : y ≤ Xh / D) :
    0 < evalZ p y := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hw : Xl + (Xh - Xl) = Xh := by ring
  have k := evalZ_sub_le hD h₁ (hw ▸ h₂) p hy₁ (by rwa [hw])
  have hv' := hv_mul hD Xl p
  simp only [lipPos, decide_eq_true_eq, hblP_eq, hvP_eq] at h
  have h' : ((hl D M p * (Xh - Xl) : ℤ) : ℝ) < hv D Xl p := by exact_mod_cast h
  push_cast at h' k
  have hL : (0 : ℝ) < D ^ p.length := by positivity
  have k₂ : (evalZ p (Xl / D) - evalZ p y) * D ^ p.length ≤ hl D M p * D * (Xh - Xl) := by
    refine le_trans ?_ k
    rw [abs_sub_comm]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hL.le
  have : 0 < evalZ p y * D ^ p.length := by nlinarith [mul_pos hDr (sub_pos.mpr h')]
  exact pos_of_mul_pos_left this hL.le

/-- The coefficients of `p(X + T)` in `T`. -/
def tshift (X : ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: q => let s := tshift X q; zipD 0 (· + ·) (s.map (X * ·)) (a :: s)

/-- The coefficients `pᵢ D^(L-1-i)` of `D^(L-1) p(y/D)` in `y` (`evalZ_scl`). -/
def scl (D : ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: q => a * D ^ q.length :: scl D q

theorem evalZ_zipD_add (x : ℝ) : ∀ a b : List ℤ,
    evalZ (zipD 0 (· + ·) a b) x = evalZ a x + evalZ b x
  | [], b => by simp [zipD, evalZ_nil]
  | a :: as, [] => by simp [zipD, evalZ_nil]
  | a :: as, b :: bs => by
    rw [zipD, evalZ_cons, evalZ_cons, evalZ_cons, evalZ_zipD_add x as bs]
    push_cast
    ring

theorem evalZ_map_mul (X : ℤ) (x : ℝ) : ∀ p : List ℤ, evalZ (p.map (X * ·)) x = X * evalZ p x
  | [] => by simp [evalZ_nil]
  | a :: q => by
    rw [List.map_cons, evalZ_cons, evalZ_cons, evalZ_map_mul X x q]
    push_cast
    ring

theorem evalZ_tshift (X : ℤ) (t : ℝ) : ∀ p : List ℤ, evalZ (tshift X p) t = evalZ p (X + t)
  | [] => by simp [tshift, evalZ_nil]
  | a :: q => by
    simp only [tshift]
    rw [evalZ_zipD_add, evalZ_map_mul, evalZ_cons, evalZ_cons, evalZ_tshift X t q]
    ring

theorem evalZ_scl {D : ℤ} (hD : D ≠ 0) (y : ℝ) : ∀ p : List ℤ,
    evalZ (scl D p) y * D = (D : ℝ) ^ p.length * evalZ p (y / D)
  | [] => by simp [scl, evalZ_nil]
  | a :: q => by
    have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD
    rw [scl, evalZ_cons, evalZ_cons, List.length_cons]
    push_cast
    rw [add_mul, mul_assoc y, evalZ_scl hD y q]
    field_simp
    ring

theorem evalZ_headD_tail (p : List ℤ) (x : ℝ) : evalZ p x = p.headD 0 + x * evalZ p.tail x := by
  cases p <;> simp [evalZ_cons, evalZ_nil]

/-- `P` has no root in `[x, b]`: pieces `[x, x + w]` on which the constant coefficient `c₀` of
`P(x + T) = ∑ cⱼ Tʲ` exceeds `∑_{j ≥ 1} |cⱼ| wʲ`, the width doubling after a piece and halving
after a failure; `false` when the fuel runs out or the width reaches `0`. -/
def excl (b : ℤ) (P : List ℤ) : ℕ → ℤ → ℤ → Bool
  | 0, _, _ => false
  | fuel + 1, x, w =>
    if b < x then true
    else if w ≤ 0 then false
    else if w * (hblP 1 w (tshift x P).tail).1 < |(tshift x P).headD 0| then
      excl b P fuel (x + w) (2 * w)
    else excl b P fuel x (w / 2)

theorem excl_sound {b : ℤ} {P : List ℤ} : ∀ (fuel : ℕ) (x w : ℤ),
    excl b P fuel x w = true → ∀ u : ℝ, (x : ℝ) ≤ u → u ≤ b → evalZ P u ≠ 0
  | 0, _, _, h => by simp [excl] at h
  | fuel + 1, x, w, h => by
    intro u hu₁ hu₂
    unfold excl at h
    split_ifs at h with hbx hw hcut
    · exact absurd (by exact_mod_cast hu₁.trans hu₂ : x ≤ b) (not_le.mpr hbx)
    · by_cases huw : u ≤ ((x + w : ℤ) : ℝ)
      · have hw0 : (0 : ℤ) ≤ w := (not_le.mp hw).le
        have ht₀ : 0 ≤ u - x := sub_nonneg.mpr hu₁
        have ht₁ : |u - x| ≤ w := by
          push_cast at huw
          rw [abs_of_nonneg ht₀]
          linarith
        have hbd := hb_bound one_pos hw0 (x := u - x) (by simpa using ht₁) (tshift x P).tail
        simp only [Int.cast_one, one_pow, mul_one] at hbd
        rw [hblP_eq] at hcut
        have hc : (w : ℝ) * hb 1 w (tshift x P).tail < |((tshift x P).headD 0 : ℝ)| := by
          exact_mod_cast hcut
        have e := evalZ_headD_tail (tshift x P) (u - x)
        rw [evalZ_tshift, add_sub_cancel] at e
        have hle : |u - x| * |evalZ (tshift x P).tail (u - x)| ≤ w * hb 1 w (tshift x P).tail :=
          mul_le_mul ht₁ hbd (abs_nonneg _) (by exact_mod_cast hw0)
        intro h0
        rw [h0, eq_comm, add_eq_zero_iff_eq_neg] at e
        rw [e, abs_neg, abs_mul] at hc
        linarith
      · exact excl_sound fuel (x + w) (2 * w) h u (not_le.mp huw).le hu₂
    · exact excl_sound fuel x (w / 2) h u hu₁ hu₂

/-- `excl` on the scaled polynomial: `p` has no root in `[x/D, b/D]`. -/
theorem excl_scl_sound {D b : ℤ} (hD : 0 < D) {p : List ℤ} {fuel : ℕ} {x w : ℤ}
    (h : excl b (scl D p) fuel x w = true) (y : ℝ) (hy₁ : (x : ℝ) / D ≤ y) (hy₂ : y ≤ b / D) :
    evalZ p y ≠ 0 := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  intro h0
  have e := evalZ_scl hD.ne' (y * D) p
  rw [mul_div_cancel_right₀ _ hDr.ne', h0, mul_zero] at e
  refine excl_sound fuel x w h (y * D) ?_ ?_ ((mul_eq_zero.mp e).resolve_right hDr.ne')
  · rwa [div_le_iff₀ hDr] at hy₁
  · rwa [le_div_iff₀ hDr] at hy₂

/-- The coefficients of the derivative. -/
def dlist (p : List ℤ) : List ℤ :=
  (List.range (p.length - 1)).map fun j : ℕ ↦ ((j : ℤ) + 1) * p.getD (j + 1) 0

theorem getD_map_range {γ : Type*} {n : ℕ} {g : ℕ → γ} {z : γ} {i : ℕ} (hi : i < n) :
    ((List.range n).map g).getD i z = g i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]

theorem hasDerivAt_evalZ (p : List ℤ) (x : ℝ) : HasDerivAt (evalZ p) (evalZ (dlist p) x) x := by
  have h := HasDerivAt.fun_sum (u := range p.length) (A := fun i y ↦ (p.getD i 0 : ℝ) * y ^ i)
    (x := x) fun i _ ↦ (hasDerivAt_pow i x).const_mul _
  have e : (fun y ↦ ∑ i ∈ range p.length, (p.getD i 0 : ℝ) * y ^ i) = evalZ p := rfl
  rw [e] at h
  convert h using 1
  rw [evalZ, dlist, List.length_map, List.length_range]
  obtain ⟨L, hL⟩ | hL : (∃ L, p.length = L + 1) ∨ p.length = 0 := by
    cases p.length <;> simp
  · rw [hL, Nat.add_sub_cancel, sum_range_succ']
    simp only [CharP.cast_eq_zero, zero_mul, mul_zero, add_zero]
    refine sum_congr rfl fun j hj ↦ ?_
    rw [getD_map_range (mem_range.mp hj)]
    push_cast
    ring_nf
  · simp [hL]

theorem evalZ_map_neg (p : List ℤ) (x : ℝ) : evalZ (p.map Neg.neg) x = -evalZ p x := by
  rw [evalZ, evalZ, List.length_map, ← sum_neg_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [getD_map_of_eq (z := (0 : ℤ)) neg_zero]
  push_cast
  ring

/-- `p` is injective on `[A/E, B/E]` if its derivative is positive or negative there. -/
theorem injOn_of_lipPos {E M A B : ℤ} (hE : 0 < E) (h₁ : |A| ≤ M) (h₂ : |B| ≤ M) {p : List ℤ}
    (h : (lipPos E M A B (dlist p) || lipPos E M A B ((dlist p).map Neg.neg)) = true) :
    Set.InjOn (evalZ p) (Set.Icc ((A : ℝ) / E) (B / E)) := by
  have hc := (continuous_evalZ p).continuousOn (s := Set.Icc ((A : ℝ) / E) (B / E))
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · refine (strictMonoOn_of_deriv_pos (convex_Icc _ _) hc fun x hx ↦ ?_).injOn
    have hx' := interior_subset hx
    rw [(hasDerivAt_evalZ p x).deriv]
    exact lipPos_sound hE h₁ h₂ h hx'.1 hx'.2
  · refine (strictAntiOn_of_deriv_neg (convex_Icc _ _) hc fun x hx ↦ ?_).injOn
    have hx' := interior_subset hx
    rw [(hasDerivAt_evalZ p x).deriv]
    have := lipPos_sound hE h₁ h₂ h hx'.1 hx'.2
    rw [evalZ_map_neg] at this
    linarith

theorem hv_map_neg (D X : ℤ) : ∀ p : List ℤ, hv D X (p.map Neg.neg) = -hv D X p
  | [] => by simp [hv]
  | a :: q => by simp only [List.map_cons, hv, List.length_map, hv_map_neg D X q]; ring

theorem hb_map_neg (D M : ℤ) : ∀ p : List ℤ, hb D M (p.map Neg.neg) = hb D M p
  | [] => rfl
  | a :: q => by simp only [List.map_cons, hb, List.length_map, abs_neg, hb_map_neg D M q]

theorem hl_map_neg (D M : ℤ) : ∀ p : List ℤ, hl D M (p.map Neg.neg) = hl D M p
  | [] => rfl
  | _ :: q => by simp only [List.map_cons, hl, hb_map_neg, hl_map_neg D M q]

/-- The sign of `p` on `[Xl/D, Xh/D]`, for `M ≥ |Xl|, |Xh|`, if its value at `Xl/D` exceeds the
Lipschitz bound times the width in absolute value (`lipPos` of `p` or of `-p`, from one value and
one bound): `some true` if positive, `some false` if negative, `none` if undecided. -/
def sgnAt (D M Xl Xh : ℤ) (p : List ℤ) : Option Bool :=
  let v := (hvP D Xl p).1
  let L := (hblP D M p).2.1 * (Xh - Xl)
  if L < v then some true else if L < -v then some false else none

theorem sgnAt_sound {D M Xl Xh : ℤ} (hD : 0 < D) (h₁ : |Xl| ≤ M) (h₂ : |Xh| ≤ M) {p : List ℤ}
    {b : Bool} (h : sgnAt D M Xl Xh p = some b) {y : ℝ} (hy₁ : (Xl : ℝ) / D ≤ y)
    (hy₂ : y ≤ Xh / D) : bif b then 0 < evalZ p y else evalZ p y < 0 := by
  simp only [sgnAt] at h
  split_ifs at h with hp hn
  · obtain rfl := Option.some.inj h
    exact lipPos_sound hD h₁ h₂ (decide_eq_true hp) hy₁ hy₂
  · obtain rfl := Option.some.inj h
    have hn' : lipPos D M Xl Xh (p.map Neg.neg) = true := by
      simp only [lipPos, hblP_eq, hvP_eq, hl_map_neg, hv_map_neg] at hn ⊢
      exact decide_eq_true hn
    have := lipPos_sound hD h₁ h₂ hn' hy₁ hy₂
    rw [evalZ_map_neg] at this
    exact neg_pos.mp this

/-! ### The root -/

/-- The coefficients: `N` is monic of degree `n ≥ 1` and `Nᵢ mₙ = mᵢ c^(n-i)`. -/
def coefCheck (m : List ℚ) (c : ℕ) (N : List ℤ) : Bool :=
  decide (2 ≤ N.length) && decide (m.length = N.length) &&
    decide (N.getD (N.length - 1) 0 = 1) && decide (m.getD (N.length - 1) 0 ≠ 0) &&
    decide (0 < c) && (List.range N.length).all fun i ↦
      decide ((N.getD i 0 : ℚ) * m.getD (N.length - 1) 0 =
        m.getD i 0 * (c : ℚ) ^ (N.length - 1 - i))

/-- The coarse enclosure: `N` is injective on `[A/E, B/E] ⊆ c [lo, hi]` and has no root in
`[B/E, Yh/E] ⊇ [B/E, c hi]`. -/
def coarseCheck (lo hi : ℚ) (c : ℕ) (N : List ℤ) (E : ℕ) (A B Yh : ℤ) (fuel : ℕ) : Bool :=
  decide (0 < E) && decide (A < B) && decide (lo * c * E ≤ A) && decide ((B : ℚ) ≤ hi * c * E) &&
    decide (hi * c * E ≤ Yh) &&
    (lipPos E (max |A| |B|) A B (dlist N) || lipPos E (max |A| |B|) A B ((dlist N).map Neg.neg)) &&
    excl Yh (scl E N) fuel B 1

/-- The fine enclosure: `N` changes sign on `[Xl/D, Xh/D] ⊆ [A/E, B/E]`. -/
def fineCheck (N : List ℤ) (E : ℕ) (A B : ℤ) (D : ℕ) (Xl Xh : ℤ) : Bool :=
  decide (0 < D) && decide (Xl < Xh) && decide (A * D ≤ Xl * E) && decide (Xh * E ≤ B * D) &&
    decide ((hvP D Xl N).1 * (hvP D Xh N).1 < 0)

/-- **The data of a root** `θ = realRoot m lo hi` (module docs): `α = c θ` is a root of the monic
integer polynomial `N`; `N` is injective on `[A/E, B/E]`, has no root in `[B/E, Yh/E]` (`fuel`
bounds the search of `excl`) and changes sign on `[Xl/D, Xh/D] ⊆ [A/E, B/E]`. -/
structure Root where
  /-- The polynomial of `θ`, from the constant coefficient. -/
  m : List ℚ
  /-- The lower end of the interval of `θ`. -/
  lo : ℚ
  /-- The upper end of the interval of `θ`. -/
  hi : ℚ
  /-- The scale: `α = c θ`. -/
  c : ℕ
  /-- The monic integer polynomial of `α`, from the constant coefficient. -/
  N : List ℤ
  /-- The denominator of the coarse enclosure. -/
  E : ℕ
  /-- The lower end of the coarse enclosure, times `E`. -/
  A : ℤ
  /-- The upper end of the coarse enclosure, times `E`. -/
  B : ℤ
  /-- `N` has no root in `[B/E, Yh/E]`. -/
  Yh : ℤ
  /-- The fuel of `excl`. -/
  fuel : ℕ
  /-- The denominator of the enclosure of `α`. -/
  D : ℕ
  /-- The lower end of the enclosure of `α`, times `D`. -/
  Xl : ℤ
  /-- The upper end of the enclosure of `α`, times `D`. -/
  Xh : ℤ
  /-- The check. -/
  ok : (coefCheck m c N && coarseCheck lo hi c N E A B Yh fuel && fineCheck N E A B D Xl Xh) =
    true

namespace Root

variable (R : Root)

/-- The degree of `N`: the number of coordinates. -/
def n : ℕ := R.N.length - 1

/-- `α = c θ` for `θ = realRoot m lo hi`. -/
noncomputable def α : ℝ := R.c * realRoot R.m R.lo R.hi

theorem coef : coefCheck R.m R.c R.N = true := by
  have h := R.ok
  simp only [Bool.and_eq_true] at h
  exact h.1.1

theorem coarse : coarseCheck R.lo R.hi R.c R.N R.E R.A R.B R.Yh R.fuel = true := by
  have h := R.ok
  simp only [Bool.and_eq_true] at h
  exact h.1.2

theorem fine : fineCheck R.N R.E R.A R.B R.D R.Xl R.Xh = true := by
  have h := R.ok
  simp only [Bool.and_eq_true] at h
  exact h.2

theorem length_N : R.N.length = R.n + 1 := by
  have h := R.coef
  simp only [coefCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold n
  omega

theorem n_pos : 0 < R.n := by
  have h := R.coef
  simp only [coefCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold n
  omega

theorem getD_N_n : R.N.getD R.n 0 = 1 := by
  have h := R.coef
  simp only [coefCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2

theorem D_pos : 0 < R.D := by
  have h := R.fine
  simp only [fineCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1

/-- **Enclosures of `α`**: `α` lies in every interval `[Xl/D, Xh/D] ⊆ [A/E, B/E]` on which `N`
changes sign (`fineCheck`), and `N(α) = 0`. -/
theorem enclose {D : ℕ} {Xl Xh : ℤ} (h₃ : fineCheck R.N R.E R.A R.B D Xl Xh = true) :
    (Xl : ℝ) / D ≤ R.α ∧ R.α ≤ (Xh : ℝ) / D ∧ evalZ R.N R.α = 0 := by
  have h₁ := R.coef
  have h₂ := R.coarse
  simp only [coefCheck, coarseCheck, fineCheck, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, hvP_eq] at h₁ h₂ h₃
  obtain ⟨⟨⟨⟨⟨-, hlen⟩, -⟩, hmn⟩, hc⟩, hcoef⟩ := h₁
  obtain ⟨⟨⟨⟨⟨⟨hE, hAB⟩, hlo⟩, hhi⟩, hYh⟩, hmono⟩, hexcl⟩ := h₂
  obtain ⟨⟨⟨⟨hD, hXlh⟩, hAX⟩, hXB⟩, hsign⟩ := h₃
  have hn : R.N.length - 1 = R.n := rfl
  rw [hn] at hmn hcoef
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hDz : (0 : ℤ) < D := by exact_mod_cast hD
  have hEr : (0 : ℝ) < R.E := by exact_mod_cast hE
  have hEz : (0 : ℤ) < R.E := by exact_mod_cast hE
  have hcR : (0 : ℝ) < R.c := by exact_mod_cast hc
  have hmn' : (R.m.getD R.n 0 : ℝ) ≠ 0 := by exact_mod_cast hmn
  -- `N (c x) mₙ = cⁿ m(x)`
  have hrel : ∀ x : ℝ, evalZ R.N (R.c * x) * (R.m.getD R.n 0 : ℝ) =
      (R.c : ℝ) ^ R.n * polyEval R.m x := by
    intro x
    rw [evalZ, polyEval, sum_mul, mul_sum, hlen]
    refine sum_congr rfl fun i hi ↦ ?_
    have hi' : i ≤ R.n := by have := mem_range.mp hi; rw [R.length_N] at this; omega
    have hr : (R.N.getD i 0 : ℝ) * (R.m.getD R.n 0 : ℝ) =
        (R.m.getD i 0 : ℝ) * (R.c : ℝ) ^ (R.n - i) := by
      exact_mod_cast hcoef i (mem_range.mp hi)
    calc (R.N.getD i 0 : ℝ) * (R.c * x) ^ i * R.m.getD R.n 0
        = ((R.N.getD i 0 : ℝ) * R.m.getD R.n 0) * R.c ^ i * x ^ i := by ring
      _ = R.m.getD i 0 * (R.c ^ (R.n - i) * R.c ^ i) * x ^ i := by rw [hr]; ring
      _ = _ := by rw [pow_sub_mul_pow _ hi']; ring
  have hroot : ∀ x : ℝ, polyEval R.m x = 0 ↔ evalZ R.N (R.c * x) = 0 := by
    intro x
    have := hrel x
    constructor
    · intro h0
      rw [h0, mul_zero] at this
      exact (mul_eq_zero.mp this).resolve_right hmn'
    · intro h0
      rw [h0, zero_mul] at this
      exact (mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero _ hcR.ne')
  -- a root `y₀` of `N` in `(Xl/D, Xh/D)`
  have hv_l := hv_mul hDz Xl R.N
  have hv_h := hv_mul hDz Xh R.N
  simp only [Int.cast_natCast] at hv_l hv_h
  have hab : (Xl : ℝ) / D ≤ Xh / D :=
    div_le_div_of_nonneg_right (by exact_mod_cast hXlh.le) hDr.le
  have hsc : evalZ R.N (Xl / D) * evalZ R.N (Xh / D) < 0 := by
    have hs : ((hv D Xl R.N * hv D Xh R.N : ℤ) : ℝ) < 0 := by exact_mod_cast hsign
    push_cast at hs
    have hDL : (0 : ℝ) < (D : ℝ) ^ R.N.length * (D : ℝ) ^ R.N.length := by positivity
    have : ((D : ℝ) ^ R.N.length * (D : ℝ) ^ R.N.length) *
        (evalZ R.N (Xl / D) * evalZ R.N (Xh / D)) < 0 := by
      calc _ = ((hv D Xl R.N : ℝ) * D) * ((hv D Xh R.N : ℝ) * D) := by
            rw [hv_l, hv_h]
            ring
        _ < 0 := by nlinarith [mul_pos hDr hDr]
    exact neg_of_mul_neg_right this hDL.le
  obtain ⟨y₀, ⟨hy₀l, hy₀h⟩, hy₀⟩ : ∃ y ∈ Set.Ioo ((Xl : ℝ) / D) (Xh / D),
      evalZ R.N y = 0 := by
    have hcont := (continuous_evalZ R.N).continuousOn
      (s := Set.Icc ((Xl : ℝ) / D) ((Xh : ℝ) / D))
    rcases lt_or_gt_of_ne (mul_ne_zero_iff.mp hsc.ne).1 with hneg | hpos
    · exact intermediate_value_Ioo hab hcont ⟨hneg, by nlinarith⟩
    · exact intermediate_value_Ioo' hab hcont ⟨by nlinarith, hpos⟩
  -- the enclosures in real numbers
  have hlo' : (R.lo : ℝ) * R.c * R.E ≤ R.A := by exact_mod_cast hlo
  have hhi' : (R.B : ℝ) ≤ R.hi * R.c * R.E := by exact_mod_cast hhi
  have hYh' : (R.hi : ℝ) * R.c * R.E ≤ R.Yh := by exact_mod_cast hYh
  have hAX' : (R.A : ℝ) * D ≤ Xl * R.E := by exact_mod_cast hAX
  have hXB' : (Xh : ℝ) * R.E ≤ R.B * D := by exact_mod_cast hXB
  have k₁ : (Xl : ℝ) < y₀ * D := by rwa [div_lt_iff₀ hDr] at hy₀l
  have k₂ : y₀ * D < Xh := by rwa [lt_div_iff₀ hDr] at hy₀h
  have kA : (R.A : ℝ) < y₀ * R.E := by
    have := mul_lt_mul_of_pos_right k₁ hEr
    exact lt_of_mul_lt_mul_right (by linarith : (R.A : ℝ) * D < y₀ * R.E * D) hDr.le
  have kB : y₀ * R.E < R.B := by
    have := mul_lt_mul_of_pos_right k₂ hEr
    exact lt_of_mul_lt_mul_right (by linarith : y₀ * R.E * D < R.B * D) hDr.le
  have hinj := injOn_of_lipPos hEz (le_max_left |R.A| |R.B|) (le_max_right |R.A| |R.B|) hmono
  simp only [Int.cast_natCast] at hinj
  have hx₀ : (R.c : ℝ) * (y₀ / R.c) = y₀ := by field_simp
  obtain ⟨hθl, hθh, hθ⟩ := realRoot_mem (p := R.m) (lo := R.lo) (hi := R.hi)
    (a := y₀ / R.c) (b := Xh / (R.c * D)) ⟨y₀ / R.c, by
      refine ⟨?_, ?_, (hroot _).mpr (by rw [hx₀]; exact hy₀), le_rfl⟩
      · rw [lt_div_iff₀ hcR]
        exact lt_of_mul_lt_mul_right (by linarith : (R.lo : ℝ) * R.c * R.E < y₀ * R.E) hEr.le
      · rw [div_lt_iff₀ hcR]
        exact lt_of_mul_lt_mul_right (by linarith : y₀ * R.E < R.hi * R.c * R.E) hEr.le⟩ (by
      intro x hx₁ hx₂ hx
      by_contra hgt
      rw [not_le, div_lt_iff₀ (by positivity)] at hgt
      have hy : evalZ R.N (R.c * x) = 0 := (hroot x).mp hx
      have hxy : y₀ < R.c * x := lt_of_mul_lt_mul_right
        (by linarith [show x * (R.c * D) = R.c * x * D by ring] : y₀ * D < R.c * x * D)
        hDr.le
      have hxE := mul_lt_mul_of_pos_right hxy hEr
      by_cases hxB : R.c * x ≤ R.B / R.E
      · have := hinj ⟨by rw [div_le_iff₀ hEr]; linarith, hxB⟩
          ⟨by rw [div_le_iff₀ hEr]; linarith, by rw [le_div_iff₀ hEr]; linarith⟩
          (hy.trans hy₀.symm)
        linarith
      · have hex := excl_scl_sound hEz hexcl (R.c * x)
        simp only [Int.cast_natCast] at hex
        refine hex (not_le.mp hxB).le ?_ hy
        rw [le_div_iff₀ hEr]
        have := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hx₂ hcR) hEr
        linarith)
  refine ⟨?_, ?_, (hroot _).mp hθ⟩
  · calc (Xl : ℝ) / D ≤ y₀ := hy₀l.le
      _ = R.c * (y₀ / R.c) := hx₀.symm
      _ ≤ R.α := mul_le_mul_of_nonneg_left hθl hcR.le
  · calc R.α ≤ R.c * (Xh / (R.c * D)) := mul_le_mul_of_nonneg_left hθh hcR.le
      _ = Xh / D := by field_simp

/-- **The enclosure of `α`**: `α ∈ [Xl/D, Xh/D]` and `N(α) = 0`. -/
theorem spec : (R.Xl : ℝ) / R.D ≤ R.α ∧ R.α ≤ (R.Xh : ℝ) / R.D ∧ evalZ R.N R.α = 0 :=
  R.enclose R.fine

/-- `α` is the only root of `N` in `[A/E, B/E]`. -/
theorem eq_of_root {y : ℝ} (hy₁ : (R.A : ℝ) / R.E ≤ y) (hy₂ : y ≤ (R.B : ℝ) / R.E)
    (hy : evalZ R.N y = 0) : R.α = y := by
  have h₂ := R.coarse
  have h₃ := R.fine
  simp only [coarseCheck, fineCheck, Bool.and_eq_true, decide_eq_true_eq] at h₂ h₃
  obtain ⟨⟨⟨⟨⟨⟨hE, -⟩, -⟩, -⟩, -⟩, hmono⟩, -⟩ := h₂
  obtain ⟨⟨⟨⟨hD, -⟩, hAX⟩, hXB⟩, -⟩ := h₃
  obtain ⟨hl, hh, h0⟩ := R.spec
  have hEz : (0 : ℤ) < R.E := by exact_mod_cast hE
  have hEr : (0 : ℝ) < R.E := by exact_mod_cast hE
  have hDr : (0 : ℝ) < R.D := by exact_mod_cast hD
  have hAX' : (R.A : ℝ) * R.D ≤ R.Xl * R.E := by exact_mod_cast hAX
  have hXB' : (R.Xh : ℝ) * R.E ≤ R.B * R.D := by exact_mod_cast hXB
  have hinj := injOn_of_lipPos hEz (le_max_left |R.A| |R.B|) (le_max_right |R.A| |R.B|) hmono
  simp only [Int.cast_natCast] at hinj
  refine hinj ⟨?_, ?_⟩ ⟨hy₁, hy₂⟩ (h0.trans hy.symm)
  · calc (R.A : ℝ) / R.E ≤ R.Xl / R.D := by rw [div_le_div_iff₀ hEr hDr]; linarith
      _ ≤ R.α := hl
  · calc R.α ≤ R.Xh / R.D := hh
      _ ≤ R.B / R.E := by rw [div_le_div_iff₀ hDr hEr]; linarith

/-! ### Refined signs

Values too close to zero for the enclosure `[Xl/D, Xh/D]` are decided on enclosures refined by
bisection (`sgnRef`), as Rust's exact sign refines its isolating interval: each half is checked
like the fine enclosure (`fineCheck`), so nothing about the bisection is trusted, and a midpoint
where `N` vanishes is `α` (`eq_of_root`). -/

/-- The sign of `p(α)` if `N` vanishes at `Z/G ∈ [A/E, B/E]`, which is then `α`. -/
def sgnExact (G : ℕ) (Z : ℤ) (p : List ℤ) : Option Bool :=
  if 0 < G ∧ (hvP G Z R.N).1 = 0 ∧ R.A * G ≤ Z * R.E ∧ Z * R.E ≤ R.B * G then
    let v := (hvP G Z p).1
    if 0 < v then some true else if v < 0 then some false else none
  else none

/-- The half of `[Yl/F, Yh/F]`, over `2F`, on which `N` changes sign: the upper one if the signs
of `N` at the midpoint and at `Yh/F` differ. -/
def half (F : ℕ) (Yl Yh : ℤ) : ℤ × ℤ :=
  if (hvP (2 * F : ℕ) (Yl + Yh) R.N).1 * (hvP (2 * F : ℕ) (2 * Yh) R.N).1 < 0 then
    (Yl + Yh, 2 * Yh)
  else (2 * Yl, Yl + Yh)

/-- The sign of `p(α)` on enclosures of `α` refined from `[Yl/F, Yh/F]` by at most `k`
bisections: the midpoint if `N` vanishes there (`sgnExact`), else the half on which `N` changes
sign, if it passes `fineCheck`, until `sgnAt` decides. `none` if undecided. -/
def sgnRef (p : List ℤ) : ℕ → ℕ → ℤ → ℤ → Option Bool
  | 0, _, _, _ => none
  | k + 1, F, Yl, Yh =>
    if (hvP (2 * F : ℕ) (Yl + Yh) R.N).1 = 0 then R.sgnExact (2 * F) (Yl + Yh) p
    else
      let Y := R.half F Yl Yh
      if fineCheck R.N R.E R.A R.B (2 * F) Y.1 Y.2 then
        (sgnAt (2 * F : ℕ) (max |Y.1| |Y.2|) Y.1 Y.2 p).orElse
          fun _ ↦ sgnRef p k (2 * F) Y.1 Y.2
      else none

/-- Bisections that decide the sign of every nonzero `p(α)` with `deg p < n` from the enclosure
`[Xl/D, Xh/D]`, if `N` is irreducible (as the fixtures' polynomials are certified to be by Rust;
the bound only affects completeness): with `C = 1 + max |Nᵢ|` bounding the roots `αⱼ` of `N` and
`P = ∑ |pᵢ|`, the norm `∏ p(αⱼ)` is a nonzero integer and `|p(αⱼ)| ≤ P C^(n-1)`, so
`|p(α)| ≥ (P C^(n-1))^(-(n-1))`; the test decides once the width `w ≤ 2C` halved `k` times times the
Lipschitz bound `L ≤ n P (C + 1)^n` is below `|p(α)| / 2`. -/
def refineFuel (p : List ℤ) : ℕ :=
  let P := (p.map Int.natAbs).sum
  let C := (R.N.map Int.natAbs).foldl max 0 + 1
  (R.n + 1) * (Nat.log2 P + 1) + (R.n + 1) ^ 2 * (Nat.log2 (C + 1) + 1) + R.n + 4

theorem sgnExact_sound {G : ℕ} {Z : ℤ} {p : List ℤ} {b : Bool} (h : R.sgnExact G Z p = some b) :
    bif b then 0 < evalZ p R.α else evalZ p R.α < 0 := by
  unfold sgnExact at h
  by_cases hc : 0 < G ∧ (hvP G Z R.N).1 = 0 ∧ R.A * G ≤ Z * R.E ∧ Z * R.E ≤ R.B * G
  swap
  · rw [ite_eq_right hc] at h
    exact absurd h (by simp)
  rw [ite_eq_left hc] at h
  obtain ⟨hG, hs, hA, hB⟩ := hc
  have hGz : (0 : ℤ) < G := by exact_mod_cast hG
  have hGr : (0 : ℝ) < G := by exact_mod_cast hG
  have hEr : (0 : ℝ) < R.E := by
    have h₂ := R.coarse
    simp only [coarseCheck, Bool.and_eq_true, decide_eq_true_eq] at h₂
    exact_mod_cast h₂.1.1.1.1.1.1
  have hN := hv_mul hGz Z R.N
  have hp := hv_mul hGz Z p
  simp only [hvP_eq] at hs
  simp only [Int.cast_natCast, hs, Int.cast_zero, zero_mul] at hN hp
  have hN0 : evalZ R.N (Z / G) = 0 :=
    (mul_eq_zero.mp hN.symm).resolve_left (pow_ne_zero _ hGr.ne')
  have hA' : (R.A : ℝ) * G ≤ Z * R.E := by exact_mod_cast hA
  have hB' : (Z : ℝ) * R.E ≤ R.B * G := by exact_mod_cast hB
  have hα := R.eq_of_root (by rw [div_le_div_iff₀ hEr hGr]; linarith)
    (by rw [div_le_div_iff₀ hGr hEr]; linarith) hN0
  have key : (hv G Z p : ℝ) * G = (G : ℝ) ^ p.length * evalZ p R.α := by rw [hα]; exact hp
  have hL : (0 : ℝ) ≤ (G : ℝ) ^ p.length := by positivity
  simp only [hvP_eq] at h
  split_ifs at h with hpos hneg
  · obtain rfl := Option.some.inj h
    have : (0 : ℝ) < (hv G Z p : ℝ) * G := mul_pos (by exact_mod_cast hpos) hGr
    rw [key] at this
    exact pos_of_mul_pos_right this hL
  · obtain rfl := Option.some.inj h
    have : (hv G Z p : ℝ) * G < 0 := mul_neg_of_neg_of_pos (by exact_mod_cast hneg) hGr
    rw [key] at this
    exact neg_of_mul_neg_right this hL

theorem sgnRef_sound (p : List ℤ) : ∀ (k F : ℕ) (Yl Yh : ℤ) {b : Bool},
    R.sgnRef p k F Yl Yh = some b → bif b then 0 < evalZ p R.α else evalZ p R.α < 0
  | 0, _, _, _, _, h => by simp [sgnRef] at h
  | k + 1, F, Yl, Yh, b, h => by
    simp only [sgnRef] at h
    split_ifs at h with hs hf
    · exact R.sgnExact_sound h
    · obtain ⟨hl, hh, -⟩ := R.enclose hf
      have hF : (0 : ℤ) < (2 * F : ℕ) := by
        simp only [fineCheck, Bool.and_eq_true, decide_eq_true_eq] at hf
        exact_mod_cast hf.1.1.1.1
      cases ha : sgnAt (2 * F : ℕ) (max |(R.half F Yl Yh).1| |(R.half F Yl Yh).2|)
        (R.half F Yl Yh).1 (R.half F Yl Yh).2 p with
      | some b' =>
        rw [ha] at h
        simp only [Option.orElse, Option.some.injEq] at h
        subst h
        exact sgnAt_sound hF (le_max_left _ _) (le_max_right _ _) ha
          (by exact_mod_cast hl) (by exact_mod_cast hh)
      | none =>
        rw [ha] at h
        simp only [Option.orElse] at h
        exact sgnRef_sound p k (2 * F) _ _ h

/-- Integer approximations of `2^64 αʲ` from the enclosure, with error bounds: `⌊2^64 Xlʲ / Dʲ⌋`,
and `⌊2^64 j (Xh - Xl) M^(j-1) / Dʲ⌋ + 2` for `M = max |Xl| |Xh|` (the mean value bound of
`|αʲ - (Xl/D)ʲ|`, plus the two roundings). -/
def apx (j : ℕ) : ℤ × ℕ :=
  ((2 ^ 64 * R.Xl ^ j) / ((R.D ^ j : ℕ) : ℤ),
    2 ^ 64 * j * (R.Xh - R.Xl).toNat * max R.Xl.natAbs R.Xh.natAbs ^ (j - 1) / R.D ^ j + 2)

theorem apx_sound (j : ℕ) :
    |(2 : ℝ) ^ 64 * R.α ^ j - ((R.apx j).1 : ℝ)| ≤ ((R.apx j).2 : ℝ) := by
  obtain ⟨hl, hh, -⟩ := R.spec
  have hD : (0 : ℝ) < R.D := by exact_mod_cast R.D_pos
  have hDj : 0 < R.D ^ j := pow_pos R.D_pos j
  set a : ℝ := (R.Xl : ℝ) / R.D with ha_def
  set M : ℕ := max R.Xl.natAbs R.Xh.natAbs with hM
  have hXlh : (R.Xl : ℝ) ≤ R.Xh := by
    have := hl.trans hh
    rwa [div_le_div_iff_of_pos_right hD] at this
  have hXl : |(R.Xl : ℝ)| ≤ M := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]; exact_mod_cast le_max_left _ _
  have hXh : |(R.Xh : ℝ)| ≤ M := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]; exact_mod_cast le_max_right _ _
  have hα : |R.α| ≤ (M : ℝ) / R.D := by
    rw [abs_le]
    constructor
    · calc -((M : ℝ) / R.D) = -(M : ℝ) / R.D := by ring
        _ ≤ R.Xl / R.D := div_le_div_of_nonneg_right (by linarith [neg_abs_le (R.Xl : ℝ)]) hD.le
        _ ≤ R.α := hl
    · exact hh.trans (div_le_div_of_nonneg_right ((le_abs_self _).trans hXh) hD.le)
  have ha : |a| ≤ (M : ℝ) / R.D := by
    rw [ha_def, abs_div, abs_of_pos hD]
    exact div_le_div_of_nonneg_right hXl hD.le
  -- The rounding of `2^64 aʲ`.
  have hq : |(2 : ℝ) ^ 64 * a ^ j - ((R.apx j).1 : ℝ)| ≤ 1 := by
    have hDj' : (0 : ℤ) < ((R.D ^ j : ℕ) : ℤ) := by exact_mod_cast hDj
    have h₁ := Int.emod_add_ediv_mul (2 ^ 64 * R.Xl ^ j) ((R.D ^ j : ℕ) : ℤ)
    have h₂ := Int.emod_nonneg (2 ^ 64 * R.Xl ^ j) hDj'.ne'
    have h₃ := Int.emod_lt_of_pos (2 ^ 64 * R.Xl ^ j) hDj'
    set q := (2 ^ 64 * R.Xl ^ j) / ((R.D ^ j : ℕ) : ℤ)
    set r := (2 ^ 64 * R.Xl ^ j) % ((R.D ^ j : ℕ) : ℤ)
    have hval : (2 : ℝ) ^ 64 * a ^ j = q + (r : ℝ) / (R.D ^ j : ℕ) := by
      have h₁' : (r : ℝ) + q * ((R.D : ℝ) ^ j) = 2 ^ 64 * (R.Xl : ℝ) ^ j := by
        exact_mod_cast h₁
      have hDne : ((R.D : ℝ) ^ j) ≠ 0 := by positivity
      rw [ha_def, div_pow, mul_div_assoc', ← h₁']
      push_cast
      rw [add_div, mul_div_cancel_right₀ _ hDne]
      ring
    have hr₀ : (0 : ℝ) ≤ (r : ℝ) / (R.D ^ j : ℕ) :=
      div_nonneg (by exact_mod_cast h₂) (by positivity)
    have hr₁ : (r : ℝ) / (R.D ^ j : ℕ) < 1 := by
      rw [div_lt_one (by exact_mod_cast hDj)]
      exact_mod_cast h₃
    change |(2 : ℝ) ^ 64 * a ^ j - (q : ℝ)| ≤ 1
    rw [hval, abs_le]
    constructor <;> linarith
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [pow_zero] at hq ⊢
    exact hq.trans (by simp [apx])
  -- The mean value bound.
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hmv := abs_pow_sub_pow_le (a := R.α) (b := a) (n := m + 1)
  have hda : |R.α - a| ≤ ((R.Xh : ℝ) - R.Xl) / R.D := by
    rw [abs_of_nonneg (by linarith), sub_div]
    linarith
  have hmax : max |R.α| |a| ^ (m + 1 - 1) ≤ ((M : ℝ) / R.D) ^ m := by
    rw [Nat.add_sub_cancel]
    exact pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) (max_le hα ha) m
  have hT : |R.α ^ (m + 1) - a ^ (m + 1)| ≤
      ((R.Xh : ℝ) - R.Xl) * (m + 1) * (M : ℝ) ^ m / (R.D : ℝ) ^ (m + 1) := by
    refine hmv.trans ?_
    calc |R.α - a| * ((m + 1 : ℕ) : ℝ) * max |R.α| |a| ^ (m + 1 - 1)
        ≤ ((R.Xh : ℝ) - R.Xl) / R.D * ((m + 1 : ℕ) : ℝ) * ((M : ℝ) / R.D) ^ m := by
          gcongr
      _ = ((R.Xh : ℝ) - R.Xl) * (m + 1) * (M : ℝ) ^ m / (R.D : ℝ) ^ (m + 1) := by
          rw [div_pow]
          field_simp
          push_cast
          ring
  -- The floor of the error bound.
  set X : ℕ := 2 ^ 64 * (m + 1) * (R.Xh - R.Xl).toNat * M ^ (m + 1 - 1)
  have hX : (X : ℝ) = 2 ^ 64 * (((R.Xh : ℝ) - R.Xl) * (m + 1) * (M : ℝ) ^ m) := by
    have : (((R.Xh - R.Xl).toNat : ℕ) : ℝ) = (R.Xh : ℝ) - R.Xl := by
      rw [show (((R.Xh - R.Xl).toNat : ℕ) : ℝ) = (((R.Xh - R.Xl).toNat : ℤ) : ℝ) by push_cast; rfl,
        Int.toNat_of_nonneg (by exact_mod_cast sub_nonneg.mpr hXlh)]
      push_cast
      ring
    simp only [X, Nat.add_sub_cancel]
    push_cast
    rw [this]
    ring
  have hfl : (X : ℝ) / (R.D : ℝ) ^ (m + 1) < ((X / R.D ^ (m + 1) : ℕ) : ℝ) + 1 := by
    have h₁ := Nat.lt_div_mul_add (a := X) hDj
    have hDr : (0 : ℝ) < (R.D : ℝ) ^ (m + 1) := by positivity
    rw [div_lt_iff₀ hDr]
    have : (X : ℝ) < ((X / R.D ^ (m + 1) : ℕ) : ℝ) * ((R.D ^ (m + 1) : ℕ) : ℝ) +
        ((R.D ^ (m + 1) : ℕ) : ℝ) := by exact_mod_cast h₁
    push_cast at this
    linarith
  have hε : ((R.apx (m + 1)).2 : ℝ) = ((X / R.D ^ (m + 1) : ℕ) : ℝ) + 2 := by
    simp only [apx, X]
    push_cast
    ring
  rw [hε]
  calc |(2 : ℝ) ^ 64 * R.α ^ (m + 1) - ((R.apx (m + 1)).1 : ℝ)|
      ≤ (2 : ℝ) ^ 64 * |R.α ^ (m + 1) - a ^ (m + 1)| +
          |(2 : ℝ) ^ 64 * a ^ (m + 1) - ((R.apx (m + 1)).1 : ℝ)| := by
        have h₁ := abs_sub_le ((2 : ℝ) ^ 64 * R.α ^ (m + 1)) ((2 : ℝ) ^ 64 * a ^ (m + 1))
          ((R.apx (m + 1)).1 : ℝ)
        have h₂ : |(2 : ℝ) ^ 64 * R.α ^ (m + 1) - (2 : ℝ) ^ 64 * a ^ (m + 1)| =
            (2 : ℝ) ^ 64 * |R.α ^ (m + 1) - a ^ (m + 1)| := by
          rw [← mul_sub, abs_mul, abs_of_pos (by positivity)]
        linarith
    _ ≤ (2 : ℝ) ^ 64 * (((R.Xh : ℝ) - R.Xl) * (m + 1) * (M : ℝ) ^ m / (R.D : ℝ) ^ (m + 1)) + 1 := by
        gcongr
    _ = (X : ℝ) / (R.D : ℝ) ^ (m + 1) + 1 := by rw [hX]; ring
    _ ≤ ((X / R.D ^ (m + 1) : ℕ) : ℝ) + 2 := by linarith

end Root

/-! ### `ℤ[α]` -/

/-- `∑ᵢ aᵢ αⁱ` with integers `aᵢ`: the elements of `ℤ[α]` for `α = c θ` (`Root`); for a body over
`ℚ(θ)`, its coordinates times a common denominator. -/
structure ZTheta (R : Root) where
  /-- The coordinates in the basis `1, α, …, α^(n-1)`. -/
  c : List ℤ

namespace ZTheta

section Gen

variable {γ : Type} [Add γ] [Sub γ] [Mul γ] (k : ℤ → γ) (N : List ℤ) (n : ℕ)

/-- `cᵢ - t Nᵢ` along `Ns`, with `c` padded by `k 0`. -/
def redG (t : γ) : List γ → List ℤ → List γ
  | _, [] => []
  | [], a :: Ns => (k 0 - t * k a) :: redG t [] Ns
  | x :: c, a :: Ns => (x - t * k a) :: redG t c Ns

/-- `α` times coordinates `c`, reduced by `αⁿ = -∑_{i<n} Nᵢ αⁱ`: a generic computation over `γ`
with integer constants embedded by `k`. -/
def shiftG (c : List γ) : List γ :=
  redG k (c.getD (n - 1) (k 0)) (k 0 :: c) (N.take n)

omit [Add γ] in
theorem getD_redG {z : γ} (t : γ) : ∀ (c : List γ) (Ns : List ℤ) (i : ℕ), i < Ns.length →
    (redG k t c Ns).getD i z = c.getD i (k 0) - t * k (Ns.getD i 0)
  | _, [], _, h => absurd h (Nat.not_lt_zero _)
  | [], _ :: _, 0, _ => rfl
  | [], _ :: Ns, i + 1, h => by
    simp only [redG, List.getD_cons_succ, List.getD_nil]
    exact getD_redG t [] Ns i (by simpa using h)
  | _ :: _, _ :: _, 0, _ => rfl
  | _ :: c, _ :: Ns, i + 1, h => by
    simp only [redG, List.getD_cons_succ]
    exact getD_redG t c Ns i (by simpa using h)

/-- `a b` for the coordinates `a` of a value, by Horner's scheme in `α`. -/
def hornerG (b : List γ) : List γ → List γ
  | [] => []
  | [a] => b.map (a * ·)
  | a :: a' :: as => zipD (k 0) (· + ·) (b.map (a * ·)) (shiftG k N n (hornerG b (a' :: as)))

/-- The product of coordinate lists, by Horner's scheme over the shorter of the first `n`
coordinates of `a` and of `b`. -/
def mulG (a b : List γ) : List γ :=
  let a := a.take n
  let b := b.take n
  if a.length ≤ b.length then hornerG k N n b a else hornerG k N n a b

end Gen

section Natural

variable {γ δ : Type} [Add γ] [Sub γ] [Mul γ] [Add δ] [Sub δ] [Mul δ] {f : γ → δ}
  (hf : IsArith f) (k : ℤ → γ) (N : List ℤ) (n : ℕ)
include hf

theorem redG_natural (t : γ) : ∀ (c : List γ) (Ns : List ℤ),
    (redG k t c Ns).map f = redG (f ∘ k) (f t) (c.map f) Ns
  | _, [] => by simp [redG]
  | [], a :: Ns => by
    simp only [redG, List.map_cons, hf.map_sub, hf.map_mul, Function.comp_apply, List.map_nil]
    rw [redG_natural t [] Ns, List.map_nil]
  | x :: c, a :: Ns => by
    simp only [redG, List.map_cons, hf.map_sub, hf.map_mul, Function.comp_apply]
    rw [redG_natural t c Ns]

theorem shiftG_natural (c : List γ) : (shiftG k N n c).map f = shiftG (f ∘ k) N n (c.map f) := by
  rw [shiftG, shiftG, redG_natural hf, List.map_cons, Function.comp_apply, List.getD_map]

theorem hornerG_natural (b : List γ) : ∀ a : List γ,
    (hornerG k N n b a).map f = hornerG (f ∘ k) N n (b.map f) (a.map f)
  | [] => rfl
  | [a] => by simp [hornerG, hf.map_mul]
  | a :: a' :: as => by
    rw [List.map_cons, List.map_cons, hornerG, hornerG, map_zipD hf.map_add, shiftG_natural hf,
      ← List.map_cons, hornerG_natural b (a' :: as), List.map_map, List.map_map]
    congr 1
    exact List.map_congr_left fun x _ ↦ hf.map_mul a x

theorem mulG_natural (a b : List γ) :
    (mulG k N n a b).map f = mulG (f ∘ k) N n (a.map f) (b.map f) := by
  simp only [mulG, ← List.map_take, List.length_map]
  split_ifs <;> exact hornerG_natural hf k N n _ _

end Natural

section Real

variable {α : ℝ} {N : List ℤ} {n : ℕ}

theorem bsum_shiftG (hN : N.length = n + 1) (h₁ : N.getD n 0 = 1) (h₀ : evalZ N α = 0)
    (c : List ℝ) : bsum (α ^ ·) n (shiftG Int.cast N n c) = α * bsum (α ^ ·) n c := by
  obtain _ | n := n
  · simp [bsum]
  have hsumN : ∑ i ∈ range (n + 1), (N.getD i 0 : ℝ) * α ^ i = -α ^ (n + 1) := by
    have := h₀
    rw [evalZ, hN, sum_range_succ, h₁] at this
    push_cast at this
    linarith
  have hget : ∀ i ∈ range (n + 1), α ^ i * (shiftG Int.cast N (n + 1) c).getD i 0 =
      α ^ i * (if i = 0 then 0 else c.getD (i - 1) 0) -
        c.getD n 0 * ((N.getD i 0 : ℝ) * α ^ i) := by
    intro i hi
    have hi' := mem_range.mp hi
    have hNt : (N.take (n + 1)).getD i 0 = N.getD i 0 := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi']
    rw [shiftG, getD_redG _ _ _ _ _ (by simp; omega), hNt]
    rcases i with _ | i
    · simp
    · simp only [Int.cast_zero, Nat.add_sub_cancel, List.getD_cons_succ, Nat.add_one_ne_zero,
        ↓reduceIte]
      ring
  have e₁ : ∑ i ∈ range (n + 1), α ^ i * (if i = 0 then (0 : ℝ) else c.getD (i - 1) 0) =
      ∑ i ∈ range n, α ^ (i + 1) * c.getD i 0 := by
    rw [sum_range_succ']
    simp
  have e₂ : α * ∑ i ∈ range (n + 1), α ^ i * c.getD i 0 =
      ∑ i ∈ range n, α ^ (i + 1) * c.getD i 0 + α ^ (n + 1) * c.getD n 0 := by
    rw [sum_range_succ, mul_add, mul_sum]
    congr 1
    · exact sum_congr rfl fun i _ ↦ by ring
    · ring
  simp only [bsum]
  rw [sum_congr rfl hget, sum_sub_distrib, ← mul_sum, hsumN, e₁, e₂]
  ring

theorem bsum_cons (a : ℝ) {l : List ℝ} (hl : l.length < n) :
    bsum (α ^ ·) n (a :: l) = a + α * bsum (α ^ ·) n l := by
  obtain _ | n := n
  · omega
  simp only [bsum]
  rw [sum_range_succ', sum_range_succ (fun i ↦ α ^ i * l.getD i 0),
    List.getD_eq_default _ _ (by omega : l.length ≤ n), mul_add, mul_sum]
  simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, one_mul, mul_zero, add_zero]
  rw [add_comm]
  congr 1
  exact sum_congr rfl fun i _ ↦ by ring

theorem bsum_map_mul (a : ℝ) (b : List ℝ) :
    bsum (α ^ ·) n (b.map (a * ·)) = a * bsum (α ^ ·) n b := by
  simp only [bsum, mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [getD_map_of_eq (z := (0 : ℝ)) (mul_zero a)]
  ring

theorem bsum_hornerG (hN : N.length = n + 1) (h₁ : N.getD n 0 = 1) (h₀ : evalZ N α = 0)
    (b : List ℝ) : ∀ l : List ℝ, l.length ≤ n →
      bsum (α ^ ·) n (hornerG Int.cast N n b l) = bsum (α ^ ·) n l * bsum (α ^ ·) n b
  | [], _ => by simp [hornerG, bsum]
  | [a], hl => by
    rw [hornerG, bsum_map_mul, bsum_cons a (by simp at hl ⊢; omega)]
    simp [bsum]
  | a :: a' :: as, hl => by
    simp only [List.length_cons] at hl
    rw [hornerG, Int.cast_zero, bsum_zipD_add, bsum_map_mul, bsum_shiftG hN h₁ h₀,
      bsum_hornerG hN h₁ h₀ b (a' :: as) (by simp; omega), bsum_cons a (by simp; omega)]
    ring

theorem bsum_take (l : List ℝ) : bsum (α ^ ·) n (l.take n) = bsum (α ^ ·) n l := by
  simp only [bsum]
  refine sum_congr rfl fun i hi ↦ ?_
  simp [List.getD_eq_getElem?_getD, mem_range.mp hi]

theorem bsum_mulG (hN : N.length = n + 1) (h₁ : N.getD n 0 = 1) (h₀ : evalZ N α = 0)
    (a b : List ℝ) :
    bsum (α ^ ·) n (mulG Int.cast N n a b) = bsum (α ^ ·) n a * bsum (α ^ ·) n b := by
  simp only [mulG]
  split_ifs
  · rw [bsum_hornerG hN h₁ h₀ _ _ (by simp), bsum_take, bsum_take]
  · rw [bsum_hornerG hN h₁ h₀ _ _ (by simp), bsum_take, bsum_take, mul_comm]

end Real

variable {R : Root}

instance : Add (ZTheta R) := ⟨fun a b ↦ ⟨zipD 0 (· + ·) a.c b.c⟩⟩
instance : Sub (ZTheta R) := ⟨fun a b ↦ ⟨zipD 0 (· - ·) a.c b.c⟩⟩
instance : Mul (ZTheta R) := ⟨fun a b ↦ ⟨mulG id R.N R.n a.c b.c⟩⟩

theorem add_c (a b : ZTheta R) : (a + b).c = zipD 0 (· + ·) a.c b.c := rfl
theorem sub_c (a b : ZTheta R) : (a - b).c = zipD 0 (· - ·) a.c b.c := rfl
theorem mul_c (a b : ZTheta R) : (a * b).c = mulG id R.N R.n a.c b.c := rfl

/-- The value `∑ᵢ aᵢ αⁱ`. -/
noncomputable def re (a : ZTheta R) : ℝ :=
  bsum (R.α ^ ·) R.n (a.c.map Int.cast)

/-- `0 < a(α)`, decided on the enclosure of `α` (`sgnAt`), else on enclosures refined by
bisection (`Root.sgnRef`, at most `Root.refineFuel` times) unless every coordinate is `0`. -/
def pos (a : ZTheta R) : Bool :=
  let p := a.c.take R.n
  match sgnAt R.D (max |R.Xl| |R.Xh|) R.Xl R.Xh p with
  | some b => b
  | none => p.any (· != 0) && (R.sgnRef p (R.refineFuel p) R.D R.Xl R.Xh).getD false

/-- All coordinates are `0`. -/
def isZero (a : ZTheta R) : Bool :=
  a.c.all (· == 0)

theorem re_eq_evalZ (a : ZTheta R) : re a = evalZ (a.c.take R.n) R.α := by
  rw [re, bsum, evalZ_eq_sum (m := R.n) (by simp)]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [getD_map_of_eq (z := (0 : ℤ)) Int.cast_zero, mul_comm]
  simp [List.getD_eq_getElem?_getD, mem_range.mp hi]

theorem re_mul (a b : ZTheta R) : re (a * b) = re a * re b := by
  obtain ⟨-, -, h₀⟩ := R.spec
  rw [re, re, re, mul_c, mulG_natural (isArith_intCast ℝ), Function.comp_id,
    bsum_mulG R.length_N R.getD_N_n h₀]

theorem pos_sound (a : ZTheta R) (h : pos a = true) : 0 < re a := by
  obtain ⟨hl, hh, -⟩ := R.spec
  rw [re_eq_evalZ]
  dsimp only [pos] at h
  split at h
  next b hb =>
    subst h
    exact sgnAt_sound (by exact_mod_cast R.D_pos) (le_max_left _ _) (le_max_right _ _) hb
      (by exact_mod_cast hl) (by exact_mod_cast hh)
  next =>
    simp only [Bool.and_eq_true] at h
    obtain ⟨-, h⟩ := h
    revert h
    cases hr : R.sgnRef (a.c.take R.n) (R.refineFuel (a.c.take R.n)) R.D R.Xl R.Xh with
    | none => simp
    | some b =>
      intro h
      simp only [Option.getD_some] at h
      subst h
      exact R.sgnRef_sound _ _ _ _ _ hr

theorem isZero_sound (a : ZTheta R) (h : isZero a = true) : re a = 0 := by
  simp only [isZero, List.all_eq_true, beq_iff_eq] at h
  simp only [re, bsum]
  refine sum_eq_zero fun i _ ↦ ?_
  rw [getD_map_of_eq (z := (0 : ℤ)) Int.cast_zero]
  rcases lt_or_ge i a.c.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi, h _ (List.getElem_mem hi)]
    simp
  · rw [List.getD_eq_default _ _ hi]
    simp

/-- The ball sum `(∑ⱼ cⱼ aⱼ, ∑ⱼ |cⱼ| εⱼ)` of coordinates `c` against approximations `(aⱼ, εⱼ)` of
`2^64 βⱼ` (`ballSum_sound`). -/
def ballSum : List (ℤ × ℕ) → List ℤ → ℤ × ℕ
  | (a, e) :: ap, c :: cs =>
    let t := ballSum ap cs
    (c * a + t.1, c.natAbs * e + t.2)
  | _, _ => (0, 0)

theorem ballSum_sound (β : ℕ → ℝ) : ∀ (ap : List (ℤ × ℕ)) (c : List ℤ),
    (∀ j < ap.length, |(2 : ℝ) ^ 64 * β j - ((ap.getD j (0, 0)).1 : ℝ)| ≤
      ((ap.getD j (0, 0)).2 : ℝ)) →
    |(2 : ℝ) ^ 64 * ∑ j ∈ range ap.length, β j * (c.getD j 0 : ℝ) - ((ballSum ap c).1 : ℝ)| ≤
      ((ballSum ap c).2 : ℝ)
  | [], c, _ => by simp [ballSum]
  | (a, e) :: ap, [], _ => by simp [ballSum]
  | (a, e) :: ap, c :: cs, h => by
    have ih := ballSum_sound (fun j ↦ β (j + 1)) ap cs fun j hj ↦ by
      simpa using h (j + 1) (by simp only [List.length_cons]; omega)
    have h0 : |(2 : ℝ) ^ 64 * β 0 - (a : ℝ)| ≤ (e : ℝ) := by simpa using h 0 (by simp)
    simp only [ballSum, List.length_cons, Finset.sum_range_succ', List.getD_cons_succ,
      List.getD_cons_zero]
    push_cast
    have key : (2 : ℝ) ^ 64 * (∑ j ∈ range ap.length, β (j + 1) * (cs.getD j 0 : ℝ) +
        β 0 * c) - (c * a + (ballSum ap cs).1) =
        ((2 : ℝ) ^ 64 * ∑ j ∈ range ap.length, β (j + 1) * (cs.getD j 0 : ℝ) -
          (ballSum ap cs).1) + c * ((2 : ℝ) ^ 64 * β 0 - a) := by ring
    rw [key]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, Nat.cast_natAbs, Int.cast_abs]
    have := mul_le_mul_of_nonneg_left h0 (abs_nonneg (c : ℝ))
    linarith

/-- The approximations `2^64 αⁱ` of the powers of the root, with their errors (`Root.apx`). -/
def apxList (R : Root) : List (ℤ × ℕ) := (List.range R.n).map R.apx

/-- The ball of `∑ᵢ aᵢ αⁱ` from approximations `ap` of `2^64 αⁱ`: sound for `apxList R`
(`ballWith_sound`). The instances take `ballWith (apxList R)`, so compiled code computes the
approximations once, when it builds the instance: a definition `fun a ↦ …` under a `let` is
compiled at its full arity and would compute them at every call. -/
def ballWith (ap : List (ℤ × ℕ)) (a : ZTheta R) : Ball :=
  let t := ballSum ap a.c
  ⟨t.1, t.2, 64⟩

theorem ballWith_sound (a : ZTheta R) : (ballWith (apxList R) a).Encl (re a) := by
  have h := ballSum_sound (R.α ^ ·) (apxList R) a.c fun j hj ↦ by
    simp only [apxList, List.length_map, List.length_range] at hj
    rw [apxList, getD_map_of_lt R.apx 0 (0, 0) (by simpa using hj), List.getD_eq_getElem _ _
      (by simpa using hj), List.getElem_range]
    exact R.apx_sound j
  simp only [apxList, List.length_map, List.length_range] at h
  have e : re a = ∑ j ∈ range R.n, R.α ^ j * ((a.c.getD j 0 : ℤ) : ℝ) := by
    rw [re, bsum]
    exact sum_congr rfl fun j _ ↦ by rw [getD_map_of_eq (z := (0 : ℤ)) Int.cast_zero]
  simp only [ballWith, Ball.Encl]
  rw [e]
  exact h

/-- `0 < a(α)`: by the ball (`ballWith`) where it decides, else by `pos`. -/
def posWith (ap : List (ℤ × ℕ)) (a : ZTheta R) : Bool :=
  let b := ballWith ap a
  b.isPos || (!b.isNeg && pos a)

/-- `0 ≤ a(α)`: by the ball (`ballWith`) where it decides, else by `isZero` and `pos`. -/
def nonnegWith (ap : List (ℤ × ℕ)) (a : ZTheta R) : Bool :=
  let b := ballWith ap a
  b.isNonneg || (!b.isNeg && (isZero a || pos a))

theorem posWith_sound (a : ZTheta R) (h : posWith (apxList R) a = true) : 0 < re a := by
  simp only [posWith, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with h | ⟨-, h⟩
  · exact Ball.pos_sound (ballWith_sound a) h
  · exact pos_sound a h

theorem nonnegWith_sound (a : ZTheta R) (h : nonnegWith (apxList R) a = true) : 0 ≤ re a := by
  simp only [nonnegWith, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with h | ⟨-, h | h⟩
  · exact Ball.nonneg_sound (ballWith_sound a) h
  · exact (isZero_sound a h).ge
  · exact (pos_sound a h).le

/-- `ℤ[α]` as exact values. -/
instance : Exact (ZTheta R) where
  ofInt z := ⟨[z]⟩
  reE a := Erased.mk (re a)
  pos := posWith (apxList R)
  nonneg := nonnegWith (apxList R)
  isZero := isZero
  ball := ballWith (apxList R)
  ballFirst := true
  reE_add a b := by
    rw [Erased.out_mk, Erased.out_mk, Erased.out_mk, re, re, re, add_c,
      map_zipD (Int.cast_add (R := ℝ)), Int.cast_zero, bsum_zipD_add]
  reE_sub a b := by
    rw [Erased.out_mk, Erased.out_mk, Erased.out_mk, re, re, re, sub_c,
      map_zipD (Int.cast_sub (R := ℝ)), Int.cast_zero, bsum_zipD_sub]
  reE_mul a b := by simp only [Erased.out_mk]; exact re_mul a b
  reE_ofInt z := by
    rw [Erased.out_mk, re, List.map_singleton, bsum_cons _ (by simpa using R.n_pos)]
    simp [bsum]
  pos_sound' a h := by rw [Erased.out_mk]; exact posWith_sound a h
  nonneg_sound' a h := by rw [Erased.out_mk]; exact nonnegWith_sound a h
  isZero_sound' a h := by rw [Erased.out_mk]; exact isZero_sound a h
  ball_sound' a := by rw [Erased.out_mk]; exact ballWith_sound a

theorem re_eq (a : ZTheta R) : Exact.re a = re a :=
  Erased.out_mk _

theorem re_ofCoords (l : List ℤ) :
    Exact.re (⟨l⟩ : ZTheta R) = ∑ j ∈ range R.n, R.α ^ j * (l.getD j 0 : ℝ) := by
  rw [re_eq, re, bsum]
  exact sum_congr rfl fun j _ ↦ by rw [getD_map_of_eq (z := (0 : ℤ)) Int.cast_zero]

/-- The real value of a constant. -/
theorem re_const (c : ℤ) : Exact.re (⟨[c]⟩ : ZTheta R) = c := by
  rw [re_ofCoords, Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp
  · intro h
    exact absurd (Finset.mem_range.mpr R.n_pos) h

/-- `n` coordinates; bounds are read in lockstep (`readK`). -/
instance : ExactBasis (ZTheta R) where
  dim := R.n
  basisE i := Erased.mk (R.α ^ i)
  coords a := a.c
  ofCoords l := ⟨l⟩
  mulG k a b := mulG k R.N R.n a b
  lowerOf n sh B Ns :=
    readK (fun l ↦ (⟨l⟩ : ZTheta R)) (2 ^ (B - 1)) (2 ^ B) (DPoly.layout B n sh) true true Ns
  apxK := 64
  apx := apxList R
  mulG_natural f hf k a b := mulG_natural hf k R.N R.n a b
  bsum_mulG' a b := by
    simp only [Erased.out_mk]
    exact bsum_mulG R.length_N R.getD_N_n R.spec.2.2 a b
  re_eq' a := by
    simp only [Erased.out_mk]
    exact (re_eq a).trans rfl
  coords_add _ _ := rfl
  coords_sub _ _ := rfl
  coords_mul _ _ := rfl
  coords_ofInt c := by simp [Exact.ofInt]
  coords_ofCoords _ _ _ := rfl
  lowerOf_le' n sh B Ns y hB hl hy h := by
    change Exact.re _ ≤ _
    simpa using readK_le (fun l ↦ (⟨l⟩ : ZTheta R)) (R.α ^ ·) R.n
      (fun l _ ↦ re_ofCoords l) hB n sh true true Ns y 1 hl hy (fun _ ↦ rfl)
      (fun _ ↦ zero_le_one) (by simp) h
  apx_sound' j hj := by
    rw [Erased.out_mk, apxList, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
      List.getElem_range]
    exact R.apx_sound j

instance : Countable (ZTheta R) :=
  Function.Injective.countable (f := ZTheta.c) fun a b h ↦ by
    cases a
    cases b
    simp_all

@[simp] theorem re_mk (l : List ℤ) :
    Exact.re (⟨l⟩ : ZTheta R) = ∑ j ∈ range R.n, R.α ^ j * (l.getD j 0 : ℝ) :=
  re_ofCoords l

/-- `q` lists the coefficients in powers of `θ` of the value with coordinates `l` (in powers of
`α = c θ`) divided by `S`: `qⱼ S = lⱼ cʲ` for `j < n`, and `q` has at most `n` entries. -/
def scaleOk (R : Root) (S : ℕ) (l : List ℤ) (q : List ℚ) : Bool :=
  decide (q.length ≤ R.n) && (List.range R.n).all fun j ↦
    decide (q.getD j 0 * S = l.getD j 0 * (R.c : ℚ) ^ j)

/-- **Coordinates to coefficients in `θ`.** A value of `ZTheta R` divided by `S` is the rational
polynomial `q` at `θ = realRoot m lo hi` (the coordinates of a fixture). -/
theorem smul_re_eq {R : Root} {s : ℝ} {S : ℕ} (hs : s * S = 1) {l : List ℤ} {q : List ℚ}
    (h : scaleOk R S l q = true) :
    s * Exact.re (⟨l⟩ : ZTheta R) = polyEval q (realRoot R.m R.lo R.hi) := by
  simp only [scaleOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hlen, hq⟩ := h
  rw [re_mk, Finset.mul_sum, polyEval, Finset.sum_subset (Finset.range_subset_range.mpr hlen)
    fun j _ hj ↦ by rw [List.getD_eq_default _ _ (by simpa using hj)]; simp]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have h' : ((q.getD j 0 : ℚ) : ℝ) * S = (l.getD j 0 : ℝ) * (R.c : ℝ) ^ j := by
    exact_mod_cast hq j (Finset.mem_range.mp hj)
  rw [Root.α, mul_pow]
  calc s * ((R.c : ℝ) ^ j * realRoot R.m R.lo R.hi ^ j * (l.getD j 0 : ℝ))
      = s * ((l.getD j 0 : ℝ) * (R.c : ℝ) ^ j) * realRoot R.m R.lo R.hi ^ j := by ring
    _ = (q.getD j 0 : ℝ) * (s * S) * realRoot R.m R.lo R.hi ^ j := by rw [← h']; ring
    _ = (q.getD j 0 : ℝ) * realRoot R.m R.lo R.hi ^ j := by rw [hs, mul_one]

end ZTheta

end Nieuwland.Check
