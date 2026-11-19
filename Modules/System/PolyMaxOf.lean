import Mathlib.Tactic.Linarith
import Modules.System.PolyMax
import Modules.System.System

/-!
# The headline theorems from the list form

The certificates' exact theorems state `PolynomialSystem.IsMaxSingle Ss N` for systems `Ss` in the
list form of `Modules/System/System.lean`: `N` is their largest scale, and each has one scale
(`Modules/System/Single.lean`). This file turns that into the two parts of a
solid's headline theorem `<def>_nu`:

* `Nieuwland.PolynomialSystem.isPolynomialSystemMax`: if `N` is the largest scale of `Ss` and each system has
  one scale (`PolynomialSystem.IsMaxSingle`, the list form's statement), and every coefficient of `Ss`
  is an integer (`PolynomialSystem.intSides`, decided by the kernel), `N` is `IsPolynomialSystemMax`, the same
  systems as Mathlib polynomials (`RationalPolynomial.toMv`);
* `Nieuwland.PolynomialSystem.mem_Icc_dec`: `N` is the scale of a solution of one of the systems, so it
  lies in the interval of the scale of that system; when each system's interval misses an
  interval `[U, V] / 10 ^ e` known to hold `N`, or its overlap with it lies in `[a, b] / 10 ^ e`
  (`PolynomialSystem.boxIn`, decided by the kernel), `N` lies in `[a, b] / 10 ^ e`. The scale's
  intervals of the root forms are about `10⁻⁶⁰` wide, so this narrows the decimals of `N` to one
  unit of `10⁻³⁰`.
-/

namespace Nieuwland

open MvPolynomial

namespace RationalPolynomial

/-- Every coefficient of `p` is an integer. -/
def intCoeffs (p : RationalPolynomial) : Bool :=
  p.all fun t ↦ t.1.den == 1

/-- The monomial of the powers `m` as a Mathlib polynomial. -/
noncomputable def mvMonomial (m : List (ℕ × ℕ)) : MvPolynomial ℕ ℤ :=
  (m.map fun v ↦ X v.1 ^ v.2).prod

/-- The polynomial `p` with the numerators of its coefficients, as a Mathlib polynomial. -/
noncomputable def toMv (p : RationalPolynomial) : MvPolynomial ℕ ℤ :=
  (p.map fun t ↦ C t.1.num * mvMonomial t.2).sum

theorem aeval_mvMonomial (x : ℕ → ℝ) (m : List (ℕ × ℕ)) :
    aeval x (mvMonomial m) = monomial x m := by
  induction m with
  | nil => simp [mvMonomial, monomial]
  | cons v m ih =>
    simp only [mvMonomial, monomial, List.map_cons, List.prod_cons, map_mul, map_pow,
      aeval_X] at ih ⊢
    rw [ih]

theorem aeval_toMv (x : ℕ → ℝ) (p : RationalPolynomial) (h : p.intCoeffs = true) :
    aeval x (toMv p) = p.eval x := by
  induction p with
  | nil => simp [toMv, RationalPolynomial.eval]
  | cons t p ih =>
    rw [intCoeffs, List.all_cons, Bool.and_eq_true] at h
    have hc : ((t.1.num : ℤ) : ℝ) = (t.1 : ℝ) := by
      have hd : t.1.den = 1 := by simpa using h.1
      exact_mod_cast (Rat.coe_int_num_of_den_eq_one hd)
    simp only [toMv, RationalPolynomial.eval, List.map_cons, List.sum_cons, map_add, map_mul, eq_intCast,
      map_intCast] at ih ⊢
    rw [aeval_mvMonomial, hc, ih h.2]

end RationalPolynomial

namespace PolynomialSystem

theorem getD_box (l : List (ℚ × ℚ)) {i : ℕ} (hi : i < l.length) : l.getD i (0, 0) = l[i] := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- Both sides of every equation of `S` have integer coefficients. -/
def intSides (S : PolynomialSystem) : Bool :=
  S.eqs.all fun e ↦ e.1.intCoeffs && e.2.intCoeffs

/-- `S` as a system of Mathlib polynomials: `p - q = 0` for each equation `p = q`. -/
noncomputable def toInt (S : PolynomialSystem) : IntSystem :=
  ⟨S.eqs.map fun e ↦ e.1.toMv - e.2.toMv, S.box⟩

theorem solves_toInt (S : PolynomialSystem) (h : S.intSides = true) (x : ℕ → ℝ) :
    S.toInt.Solves x ↔ S.Solves x := by
  unfold IntSystem.Solves Solves toInt
  refine and_congr ?_ ?_
  · refine forall_congr' fun i ↦ ⟨fun H hi ↦ ?_, fun H hi ↦ ?_⟩
    · have := H hi
      rwa [getD_box _ hi]
    · have := H hi
      rwa [getD_box _ hi] at this
  · rw [intSides, List.all_eq_true] at h
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    refine forall₂_congr fun e he ↦ ?_
    have he' := h e he
    rw [Bool.and_eq_true] at he'
    rw [map_sub, RationalPolynomial.aeval_toMv x _ he'.1, RationalPolynomial.aeval_toMv x _ he'.2, sub_eq_zero]

/-- `N` is the largest scale of the systems `Ss`, and each system has one scale: the list form
of `IsPolynomialSystemMax`, which the exact theorems' `<def>_exact_list` state. -/
def IsMaxSingle (Ss : List PolynomialSystem) (N : ℝ) : Prop :=
  IsGreatest (scales Ss) N ∧ ∀ S ∈ Ss, ∃ v, scales [S] = {v}

theorem firstValues_toInt (S : PolynomialSystem) (h : S.intSides = true) :
    S.toInt.firstValues = scales [S] := by
  ext l
  simp only [IntSystem.firstValues, scales, Set.mem_ofPred_eq, List.mem_singleton, exists_eq_left,
    solves_toInt S h]

/-- **The list form gives `IsPolynomialSystemMax`**: if `N` is the largest scale of the systems `Ss`,
each of one scale and all of whose coefficients are integers, then `N` is the largest first
coordinate of the real solutions of the same systems as Mathlib polynomials. -/
theorem isPolynomialSystemMax {Ss : List PolynomialSystem} (h : Ss.all intSides = true) {N : ℝ}
    (hN : IsMaxSingle Ss N) : IsPolynomialSystemMax N := by
  have hi : ∀ S ∈ Ss, S.toInt.firstValues = scales [S] := fun S hS ↦
    firstValues_toInt S (List.all_eq_true.mp h S hS)
  refine ⟨Ss.map toInt, ?_, ?_⟩
  · simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro S hS
    rw [hi S hS]
    exact hN.2 S hS
  · have hset : {l : ℝ | ∃ S ∈ Ss.map toInt, l ∈ S.firstValues} = scales Ss := by
      ext l
      simp only [Set.mem_ofPred_eq, List.mem_map]
      constructor
      · rintro ⟨_, ⟨S, hS, rfl⟩, hl⟩
        rw [hi S hS] at hl
        obtain ⟨_, hT, x, hx, rfl⟩ := hl
        rw [List.mem_singleton.mp hT] at hx
        exact ⟨S, hS, x, hx, rfl⟩
      · rintro ⟨S, hS, x, hx, rfl⟩
        refine ⟨_, ⟨S, hS, rfl⟩, ?_⟩
        rw [hi S hS]
        exact ⟨S, List.mem_singleton_self _, x, hx, rfl⟩
    rw [hset]
    exact hN.1

/-- A scale of `S` in `[U, V]` lies in `[a, b]`: the interval `[lo, hi]` of the scale misses
`[U, V]`, or its overlap with `[U, V]` lies in `[a, b]`; without an interval, `[U, V]` lies in
`[a, b]`. -/
def boxIn (S : PolynomialSystem) (U V a b : ℚ) : Bool :=
  match S.box with
  | [] => decide (a ≤ U) && decide (V ≤ b)
  | lh :: _ => decide (lh.2 < U) || decide (V < lh.1) ||
      (decide (a ≤ max lh.1 U) && decide (min lh.2 V ≤ b))

theorem mem_Icc_of_boxIn {S : PolynomialSystem} {x : ℕ → ℝ} (hx : S.Solves x) {U V a b : ℚ}
    (hN : x 0 ∈ Set.Icc (U : ℝ) V) (hc : S.boxIn U V a b = true) : x 0 ∈ Set.Icc (a : ℝ) b := by
  unfold boxIn at hc
  match hbox : S.box, hc with
  | [], hc =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    have ha : (a : ℝ) ≤ U := by exact_mod_cast hc.1
    have hb : (V : ℝ) ≤ b := by exact_mod_cast hc.2
    exact ⟨ha.trans hN.1, hN.2.trans hb⟩
  | lh :: rest, hc =>
    have h0 : 0 < S.box.length := by simp [hbox]
    have hx0 := hx.1 0 h0
    rw [getD_box _ h0] at hx0
    simp only [hbox, List.getElem_cons_zero] at hx0
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hc with (hc | hc) | ⟨ha, hb⟩
    · have : (lh.2 : ℝ) < U := by exact_mod_cast hc
      linarith [hN.1, hx0.2]
    · have : (V : ℝ) < lh.1 := by exact_mod_cast hc
      linarith [hN.2, hx0.1]
    · have ha' : (a : ℝ) ≤ max (lh.1 : ℝ) U := by exact_mod_cast ha
      have hb' : min (lh.2 : ℝ) V ≤ b := by exact_mod_cast hb
      exact ⟨ha'.trans (max_le hx0.1 hN.1), (le_min hx0.2 hN.2).trans hb'⟩

/-- **Decimals from the scale's intervals**: if `N` is the largest scale of the systems `Ss` and
lies in `[U, V] / 10 ^ e`, and a scale of each system in `[U, V] / 10 ^ e` lies in
`[a, b] / 10 ^ e` (`boxIn`, decided), then `N` lies in `[a, b] / 10 ^ e`. The scale's intervals of
the root forms are about `10⁻⁶⁰` wide, so this narrows the decimals of `N` to one unit. -/
theorem mem_Icc_dec (U V a b e : ℕ) {Ss : List PolynomialSystem} {N : ℝ}
    (h : IsGreatest (scales Ss) N ∧ N ∈ Set.Icc ((U : ℝ) / 10 ^ e) ((V : ℝ) / 10 ^ e))
    (hc : (Ss.all fun S ↦ S.boxIn ((U : ℚ) / 10 ^ e) ((V : ℚ) / 10 ^ e) ((a : ℚ) / 10 ^ e)
      ((b : ℚ) / 10 ^ e)) = true) :
    N ∈ Set.Icc ((a : ℝ) / 10 ^ e) ((b : ℝ) / 10 ^ e) := by
  obtain ⟨S, hS, x, hx, rfl⟩ := h.1.1
  have hN : x 0 ∈ Set.Icc (((U : ℚ) / 10 ^ e : ℚ) : ℝ) (((V : ℚ) / 10 ^ e : ℚ) : ℝ) := by
    push_cast; exact h.2
  have := mem_Icc_of_boxIn hx hN (List.all_eq_true.mp hc S hS)
  push_cast at this
  exact this

end PolynomialSystem

end Nieuwland
