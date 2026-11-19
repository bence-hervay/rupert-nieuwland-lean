import Modules.System.SystemOps
import Modules.Nieuwland.Settled
import Modules.Check.Number.Theta

/-!
# Closed forms as systems in the scale alone

The statement of `Modules/System/System.lean` for a Nieuwland number with a polynomial of its
own: one system, one equation `P(x 0) = 0` in the scale alone (written `L = Rt` with positive
coefficients on both sides, `RationalPolynomial.split`) and one box `[a, b]`, together with an enclosure
`[u, v]` of the number between two rationals.

* A Nopert: the equation `x 0 = 1` and no box (`isGreatest_scales_one`).
* A closed form `N = realRoot m lo hi` (the largest root of `m` in `(lo, hi)`) with the checked
  data of that root (`Check.Root`: an enclosure, and that it is a root): `P` is a nonzero multiple
  of `m` (`isGreatest_scales_of_realRoot`).
* A closed form `N = Θ.re`, `Θ` an exact value (an element of the solid's field over a common
  denominator), and `P` an integer polynomial with `P(Θ) = 0`, checked in exact arithmetic
  (`homEval`, `Exact.isZero`), with the checked data of the root of `P` near `Θ`
  (`isGreatest_scales_of_exact`): the number is the largest root of `P` in an interval because
  `Θ` lies in that root's isolating interval (`Exact.nonneg`).

## Main statements

* `Nieuwland.Check.Root.polyEval_eq_zero_iff`: `m(x) = 0` exactly when `N(c x) = 0`.
* `Nieuwland.isGreatest_scales_one`, `Nieuwland.isGreatest_scales_of_realRoot`,
  `Nieuwland.isGreatest_scales_of_exact`.
-/

open Finset

namespace Nieuwland

namespace Check.Root

variable (R : Root)

theorem c_pos : 0 < R.c := by
  have h := R.coef
  simp only [coefCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

/-- `m` and the monic integer polynomial `N` of `α = c θ` have the same roots, up to the factor
`c`. -/
theorem polyEval_eq_zero_iff (x : ℝ) : polyEval R.m x = 0 ↔ evalZ R.N (R.c * x) = 0 := by
  have h₁ := R.coef
  simp only [coefCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    at h₁
  obtain ⟨⟨⟨⟨⟨-, hlen⟩, -⟩, hmn⟩, hc⟩, hcoef⟩ := h₁
  have hn : R.N.length - 1 = R.n := rfl
  rw [hn] at hmn hcoef
  have hcR : (0 : ℝ) < R.c := by exact_mod_cast hc
  have hmn' : (R.m.getD R.n 0 : ℝ) ≠ 0 := by exact_mod_cast hmn
  have hrel : evalZ R.N (R.c * x) * (R.m.getD R.n 0 : ℝ) = (R.c : ℝ) ^ R.n * polyEval R.m x := by
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
  constructor
  · intro h0
    rw [h0, mul_zero] at hrel
    exact (mul_eq_zero.mp hrel).resolve_right hmn'
  · intro h0
    rw [h0, zero_mul] at hrel
    exact (mul_eq_zero.mp hrel.symm).resolve_left (pow_ne_zero _ hcR.ne')

/-- `A/E ≤ α ≤ B/E`: the fine enclosure lies in the coarse one. -/
theorem α_mem_coarse : (R.A : ℝ) / R.E ≤ R.α ∧ R.α ≤ (R.B : ℝ) / R.E := by
  have h₃ := R.fine
  simp only [fineCheck, Bool.and_eq_true, decide_eq_true_eq] at h₃
  obtain ⟨⟨⟨⟨hD, -⟩, hAX⟩, hXB⟩, -⟩ := h₃
  have h₂ := R.coarse
  simp only [coarseCheck, Bool.and_eq_true, decide_eq_true_eq] at h₂
  have hE : (0 : ℝ) < R.E := by exact_mod_cast h₂.1.1.1.1.1.1
  have hDr : (0 : ℝ) < R.D := by exact_mod_cast hD
  have hAX' : (R.A : ℝ) * R.D ≤ R.Xl * R.E := by exact_mod_cast hAX
  have hXB' : (R.Xh : ℝ) * R.E ≤ R.B * R.D := by exact_mod_cast hXB
  obtain ⟨hl, hh, -⟩ := R.spec
  constructor
  · calc (R.A : ℝ) / R.E ≤ R.Xl / R.D := by
          rw [div_le_div_iff₀ hE hDr]; linarith
      _ ≤ R.α := hl
  · calc R.α ≤ R.Xh / R.D := hh
      _ ≤ R.B / R.E := by rw [div_le_div_iff₀ hDr hE]; linarith

end Check.Root

theorem eval_ofUni_map_mul (k : ℚ) (m : List ℚ) (x : ℕ → ℝ) :
    (RationalPolynomial.ofUni 0 (m.map (k * ·))).eval x = k * polyEval m (x 0) := by
  rw [RationalPolynomial.eval_ofUni, polyEval, mul_sum, List.length_map]
  refine sum_congr rfl fun j _ ↦ ?_
  have h := List.getD_map (l := m) (n := j) (d := (0 : ℚ)) (k * ·)
  simp only [mul_zero] at h
  rw [h]
  push_cast
  ring

/-- **A closed form as a system in the scale alone.** `R` is the checked data of the root
`realRoot R.m R.lo R.hi`, and `N` is that root. `P` is `k ≠ 0` times `R.m` in the variable `x 0`,
written `L = Rt` with both sides positive (`RationalPolynomial.split`). The box `[a, b]` lies inside
`(R.lo, R.hi)` and holds `[u, v]`, which holds the enclosure of the root. Then `N` is the largest
scale of the system `L = Rt` in the box `[a, b]`, and `u ≤ N ≤ v`. -/
theorem isGreatest_scales_of_realRoot (R : Check.Root) {N : ℝ}
    (hN : N = realRoot R.m R.lo R.hi) {k : ℚ} (hk : k ≠ 0) {L Rt : RationalPolynomial}
    (hP : RationalPolynomial.split (RationalPolynomial.ofUni 0 (R.m.map (k * ·))) = (L, Rt)) {a b u v : ℚ}
    (hlo : R.lo < a) (hhi : b < R.hi) (hau : a ≤ u) (hvb : v ≤ b)
    (hu : u * (R.c * R.D) ≤ R.Xl) (hv : (R.Xh : ℚ) ≤ v * (R.c * R.D)) :
    IsGreatest (PolynomialSystem.scales [⟨[(L, Rt)], [(a, b)]⟩]) N ∧ N ∈ Set.Icc (u : ℝ) (v : ℝ) := by
  set P := RationalPolynomial.ofUni 0 (R.m.map (k * ·)) with hPdef
  have hS : (⟨[(L, Rt)], [(a, b)]⟩ : PolynomialSystem) = (⟨[P], [(a, b)]⟩ : ZSystem).toSystem := by
    simp [ZSystem.toSystem, hP]
  rw [hS, ZSystem.scales_toSystem]
  have hp : ∀ x : ℕ → ℝ, P.eval x = k * polyEval R.m (x 0) := fun x ↦ by
    rw [hPdef, eval_ofUni_map_mul]
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  obtain ⟨hl, hh, h0⟩ := R.spec
  have hc : (0 : ℝ) < R.c := by exact_mod_cast R.c_pos
  have hD : (0 : ℝ) < R.D := by exact_mod_cast R.D_pos
  have hα : R.α = R.c * N := by rw [hN]; rfl
  rw [hα] at hl hh h0
  have hroot : polyEval R.m N = 0 := (R.polyEval_eq_zero_iff N).mpr h0
  have hu' : (u : ℝ) * (R.c * R.D) ≤ R.Xl := by exact_mod_cast hu
  have hv' : (R.Xh : ℝ) ≤ v * (R.c * R.D) := by exact_mod_cast hv
  have huN : (u : ℝ) ≤ N := by
    rw [div_le_iff₀ hD] at hl
    have : (u : ℝ) * (R.c * R.D) ≤ N * (R.c * R.D) := by nlinarith
    exact le_of_mul_le_mul_right this (mul_pos hc hD)
  have hNv : N ≤ (v : ℝ) := by
    rw [le_div_iff₀ hD] at hh
    have : N * (R.c * R.D) ≤ (v : ℝ) * (R.c * R.D) := by nlinarith
    exact le_of_mul_le_mul_right this (mul_pos hc hD)
  have hau' : (a : ℝ) ≤ u := by exact_mod_cast hau
  have hvb' : (v : ℝ) ≤ b := by exact_mod_cast hvb
  refine ⟨⟨?_, ?_⟩, huN, hNv⟩
  · refine ⟨fun _ ↦ N, ⟨?_, ?_⟩, rfl⟩
    · intro i hi
      have hi0 : i = 0 := by simpa using hi
      subst hi0
      exact ⟨hau'.trans huN, hNv.trans hvb'⟩
    · intro q hq
      rw [List.mem_singleton.mp hq, hp, hroot, mul_zero]
  · rintro l ⟨x, ⟨hbox, heq⟩, rfl⟩
    obtain ⟨hxa, hxb⟩ := hbox 0 (by simp)
    simp only [List.getD_cons_zero] at hxa hxb
    have hx0 : polyEval R.m (x 0) = 0 := by
      have := heq P (List.mem_singleton_self _)
      rw [hp] at this
      exact (mul_eq_zero.mp this).resolve_left hk'
    have hlo' : (R.lo : ℝ) < a := by exact_mod_cast hlo
    have hhi' : (b : ℝ) < R.hi := by exact_mod_cast hhi
    rw [hN]
    exact le_csSup ⟨R.hi, fun y hy ↦ hy.2.1.le⟩ ⟨hlo'.trans_le hxa, hxb.trans_lt hhi', hx0⟩

/-- **A Nopert as a system in the scale alone**: `x 0 = 1`, no box. -/
theorem isGreatest_scales_one {N : ℝ} (hN : N = 1) :
    IsGreatest (PolynomialSystem.scales [⟨[([(1, [(0, 1)])], [(1, [])])], []⟩]) N ∧
      N ∈ Set.Icc (1 : ℝ) 1 := by
  have hev : ∀ x : ℕ → ℝ, RationalPolynomial.eval [(1, [(0, 1)])] x = x 0 := fun x ↦ by
    simp [RationalPolynomial.eval, monomial]
  have hev1 : ∀ x : ℕ → ℝ, RationalPolynomial.eval [(1, [])] x = 1 := fun x ↦ by
    simp [RationalPolynomial.eval, monomial]
  subst hN
  refine ⟨⟨⟨_, List.mem_singleton_self _, fun _ ↦ 1, ⟨fun i hi ↦ absurd hi (by simp), ?_⟩, rfl⟩,
    ?_⟩, le_refl _, le_refl _⟩
  · intro e he
    rw [List.mem_singleton.mp he, hev, hev1]
  · rintro l ⟨S, hS, x, ⟨-, heq⟩, rfl⟩
    rw [List.mem_singleton.mp hS] at heq
    have := heq _ (List.mem_singleton_self _)
    rw [hev, hev1] at this
    exact this.le

/-! ### A polynomial of an exact value -/

section Exact

open Check

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- `∑ pᵢ aⁱ dⁿ⁻ⁱ` (`n + 1` the length of `p`, `pᵢ` from the constant coefficient), by Horner's
scheme: `dⁿ p(a/d)` in exact arithmetic. -/
def homEval (a : κ) (d : ℤ) : List ℤ → κ
  | [] => Exact.ofInt 0
  | c :: cs => Exact.ofInt (c * d ^ cs.length) + a * homEval a d cs

theorem re_homEval (a : κ) {d : ℤ} (hd : d ≠ 0) :
    ∀ p : List ℤ, Exact.re (homEval a d p) = (d : ℝ) ^ (p.length - 1) * evalZ p (Exact.re a / d)
  | [] => by simp [homEval, Exact.re_ofInt, evalZ_nil]
  | [c] => by simp [homEval, Exact.re_add, Exact.re_mul, Exact.re_ofInt, evalZ_cons, evalZ_nil]
  | c :: c' :: cs => by
    have ih := re_homEval a hd (c' :: cs)
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
    rw [homEval, Exact.re_add, Exact.re_mul, Exact.re_ofInt, ih]
    simp only [evalZ_cons, List.length_cons, Nat.add_sub_cancel]
    push_cast
    rw [pow_succ]
    field_simp

/-- `Θ` is a root of `p` if `homEval` of its numerator and denominator is zero. -/
theorem evalZ_re_eq_zero (Θ : Scale κ) (hden : 0 < Θ.den) (p : List ℤ)
    (h : Exact.isZero (homEval Θ.num (Θ.den : ℤ) p) = true) : evalZ p Θ.re = 0 := by
  have hd : (Θ.den : ℤ) ≠ 0 := by exact_mod_cast hden.ne'
  have h0 := Exact.isZero_sound _ h
  rw [re_homEval _ hd] at h0
  have hd' : ((Θ.den : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hd
  rw [Scale.re]
  push_cast at h0
  exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ (by exact_mod_cast hden.ne'))

end Exact

/-- **A closed form `N = Θ.re` as a system in the scale alone.** `p` is an integer polynomial
with `p(Θ) = 0` (`homEval`, in exact arithmetic), `R` the checked data of the largest root of `p`
in `(R.lo, R.hi)` (`R.m = p`), and `Θ` lies in that root's isolating interval: `A ≤ E c Θ ≤ B`
(`Exact.nonneg`). Then `N` is that root, and the statement of `isGreatest_scales_of_realRoot`
holds with `P = p` in the variable `x 0`. -/
theorem isGreatest_scales_of_exact {κ : Type} [Add κ] [Sub κ] [Mul κ] [Check.Exact κ]
    (R : Check.Root) (Θ : Check.Scale κ) {N : ℝ} (hN : N = Θ.re) (p : List ℤ)
    (hm : R.m = p.map (Int.cast)) (hden : 0 < Θ.den)
    (hz : Check.Exact.isZero (homEval Θ.num (Θ.den : ℤ) p) = true)
    (hA : Check.Exact.nonneg (Check.Exact.ofInt ((R.E : ℤ) * R.c) * Θ.num -
      Check.Exact.ofInt (R.A * Θ.den)) = true)
    (hB : Check.Exact.nonneg (Check.Exact.ofInt (R.B * Θ.den) -
      Check.Exact.ofInt ((R.E : ℤ) * R.c) * Θ.num) = true)
    {L Rt : RationalPolynomial} (hP : RationalPolynomial.split (RationalPolynomial.ofUni 0 (p.map Int.cast)) = (L, Rt))
    {a b u v : ℚ} (hlo : R.lo < a) (hhi : b < R.hi) (hau : a ≤ u) (hvb : v ≤ b)
    (hu : u * (R.c * R.D) ≤ R.Xl) (hv : (R.Xh : ℚ) ≤ v * (R.c * R.D)) :
    IsGreatest (PolynomialSystem.scales [⟨[(L, Rt)], [(a, b)]⟩]) N ∧ N ∈ Set.Icc (u : ℝ) (v : ℝ) := by
  have hden' : (0 : ℝ) < Θ.den := by exact_mod_cast hden
  have hE : (0 : ℝ) < R.E := by
    have h₂ := R.coarse
    simp only [Check.coarseCheck, Bool.and_eq_true, decide_eq_true_eq] at h₂
    exact_mod_cast h₂.1.1.1.1.1.1
  have hc : (0 : ℝ) < R.c := by exact_mod_cast R.c_pos
  have hre : Check.Exact.re Θ.num = N * Θ.den := by
    rw [hN, Check.Scale.re]; field_simp
  -- `N` is a root of `R.m`
  have hp0 : Check.evalZ p N = 0 := hN ▸ evalZ_re_eq_zero Θ hden p hz
  have hm0 : polyEval R.m N = 0 := by
    rw [hm, polyEval, List.length_map]
    rw [Check.evalZ] at hp0
    rw [← hp0]
    refine sum_congr rfl fun j _ ↦ ?_
    have h := List.getD_map (l := p) (n := j) (d := (0 : ℤ)) (Int.cast : ℤ → ℚ)
    rw [Int.cast_zero] at h
    rw [h]
    push_cast
    rfl
  -- `c N` lies in the coarse enclosure, so it is `α`
  have hA' := Check.Exact.nonneg_sound _ hA
  have hB' := Check.Exact.nonneg_sound _ hB
  simp only [Check.Exact.re_sub, Check.Exact.re_mul, Check.Exact.re_ofInt, hre] at hA' hB'
  push_cast at hA' hB'
  have h1 : (R.A : ℝ) / R.E ≤ R.c * N := by
    rw [div_le_iff₀ hE]
    nlinarith
  have h2 : R.c * N ≤ (R.B : ℝ) / R.E := by
    rw [le_div_iff₀ hE]
    nlinarith
  have hα : R.α = R.c * N := R.eq_of_root h1 h2 ((R.polyEval_eq_zero_iff N).mp hm0)
  have hN' : N = realRoot R.m R.lo R.hi := by
    have : (R.c : ℝ) * realRoot R.m R.lo R.hi = R.c * N := hα
    exact (mul_left_cancel₀ hc.ne' this).symm
  have hP' : RationalPolynomial.split (RationalPolynomial.ofUni 0 (R.m.map ((1 : ℚ) * ·))) = (L, Rt) := by
    rw [← hP, hm, List.map_map]
    congr 3
    funext x
    simp
  exact isGreatest_scales_of_realRoot R hN' one_ne_zero hP' hlo hhi hau hvb hu hv

/-- `isGreatest_scales_of_exact` with the enclosure as decimals: `[U, V] / 10^k`, `U` and `V`
natural numbers (as the literals of a statement are). -/
theorem isGreatest_scales_of_exact_dec {κ : Type} [Add κ] [Sub κ] [Mul κ] [Check.Exact κ]
    (R : Check.Root) (Θ : Check.Scale κ) {N : ℝ} (hN : N = Θ.re) (p : List ℤ)
    (hm : R.m = p.map (Int.cast)) (hden : 0 < Θ.den)
    (hz : Check.Exact.isZero (homEval Θ.num (Θ.den : ℤ) p) = true)
    (hA : Check.Exact.nonneg (Check.Exact.ofInt ((R.E : ℤ) * R.c) * Θ.num -
      Check.Exact.ofInt (R.A * Θ.den)) = true)
    (hB : Check.Exact.nonneg (Check.Exact.ofInt (R.B * Θ.den) -
      Check.Exact.ofInt ((R.E : ℤ) * R.c) * Θ.num) = true)
    {L Rt : RationalPolynomial} (hP : RationalPolynomial.split (RationalPolynomial.ofUni 0 (p.map Int.cast)) = (L, Rt))
    {a b : ℚ} {U V : ℕ} (k : ℕ) (hlo : R.lo < a) (hhi : b < R.hi) (hau : a ≤ (U : ℚ) / 10 ^ k)
    (hvb : (V : ℚ) / 10 ^ k ≤ b) (hu : (U : ℚ) / 10 ^ k * (R.c * R.D) ≤ R.Xl)
    (hv : (R.Xh : ℚ) ≤ (V : ℚ) / 10 ^ k * (R.c * R.D)) :
    IsGreatest (PolynomialSystem.scales [⟨[(L, Rt)], [(a, b)]⟩]) N ∧
      N ∈ Set.Icc ((U : ℝ) / 10 ^ k) ((V : ℝ) / 10 ^ k) := by
  obtain ⟨h, h1, h2⟩ := isGreatest_scales_of_exact R Θ hN p hm hden hz hA hB hP hlo hhi hau hvb hu hv
  push_cast at h1 h2
  exact ⟨h, h1, h2⟩

end Nieuwland
