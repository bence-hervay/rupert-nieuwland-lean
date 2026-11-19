import Modules.System.PolyRoot
import Modules.System.PolyMaxOf

/-!
# One root per system, from the list form

The list form of `IsPolyRootMax` (`Modules/System/PolyRoot.lean`) for the systems of
`Modules/System/System.lean`:

* `Nieuwland.PolynomialSystem.boxed`: every variable of the equations has an interval (decided by the
  kernel);
* `Nieuwland.PolynomialSystem.HasUniqueRoot S`: `S` has a first variable, every variable an interval, and
  **exactly one point of the box solves the equations** (a point is its values of the variables
  with an interval, `x 0, …, x (n - 1)`);
* `Nieuwland.PolynomialSystem.HasUniqueRoot.existsUnique`: such a system with integer coefficients has, as a
  system of Mathlib polynomials in its `n` variables, exactly one root in its box (`∃!` over
  `Fin n → ℝ`); a solid's theorems `<def>_nu_system_<j>_oneRoot` state `HasUniqueRoot` of each of its
  systems `<def>_nu_system_<j>`, one system at a time;
* `Nieuwland.PolynomialSystem.IsRootMax Ss N`: `N` is the largest scale of the systems `Ss`, each of which
  has exactly one root: what a solid's `<def>_nu_roots_list` states;
* `Nieuwland.PolynomialSystem.IsRootMax.isMaxSingle`: it implies the statement of `<def>_exact_list`
  (`PolynomialSystem.IsMaxSingle`) for the same systems;
* `Nieuwland.PolynomialSystem.isPolyRootMax`: with integer coefficients (`PolynomialSystem.intSides`), it gives
  `IsPolyRootMax N`, the same systems as Mathlib polynomials in `n` variables (`RationalPolynomial.toMvFin`).

No certificate is involved here: the systems' roots are counted in
`Modules/System/HasUniqueRoot.lean` and `Modules/Root/HasUniqueRoot.lean`.
-/

namespace Nieuwland

open MvPolynomial

/-- The point of `ℕ → ℝ` with the coordinates `r` first and `0` after them. -/
def ofFin {n : ℕ} (r : Fin (n + 1) → ℝ) (i : ℕ) : ℝ := if h : i < n + 1 then r ⟨i, h⟩ else 0

theorem ofFin_lt {n : ℕ} (r : Fin (n + 1) → ℝ) {i : ℕ} (h : i < n + 1) : ofFin r i = r ⟨i, h⟩ := by
  simp [ofFin, h]

namespace RationalPolynomial

theorem monomial_congr {x y : ℕ → ℝ} {n : ℕ} (hxy : ∀ i < n, x i = y i) (m : List (ℕ × ℕ))
    (h : (m.all fun v ↦ decide (v.1 < n)) = true) : monomial x m = monomial y m := by
  induction m with
  | nil => rfl
  | cons v m ih =>
    rw [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [monomial, List.map_cons, List.prod_cons] at ih ⊢
    rw [hxy _ h.1, ih h.2]

/-- A polynomial in the variables below `n` has the same value at points that agree there. -/
theorem eval_congr {x y : ℕ → ℝ} {n : ℕ} (hxy : ∀ i < n, x i = y i) (p : RationalPolynomial)
    (h : p.varsLt n = true) : p.eval x = p.eval y := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rw [varsLt, List.all_cons, Bool.and_eq_true] at h
    simp only [RationalPolynomial.eval, List.map_cons, List.sum_cons] at ih ⊢
    rw [monomial_congr hxy _ h.1, ih h.2]

/-- The monomial of the powers `m` as a Mathlib polynomial in `n + 1` variables (a variable out of
range is `0`, as in `ofFin`). -/
noncomputable def mvMonomialFin (n : ℕ) (m : List (ℕ × ℕ)) : MvPolynomial (Fin (n + 1)) ℤ :=
  (m.map fun v ↦ (if h : v.1 < n + 1 then X ⟨v.1, h⟩ else 0) ^ v.2).prod

/-- The polynomial `p` with the numerators of its coefficients, as a Mathlib polynomial in
`n + 1` variables. -/
noncomputable def toMvFin (n : ℕ) (p : RationalPolynomial) : MvPolynomial (Fin (n + 1)) ℤ :=
  (p.map fun t ↦ C t.1.num * mvMonomialFin n t.2).sum

theorem aeval_mvMonomialFin {n : ℕ} (r : Fin (n + 1) → ℝ) (m : List (ℕ × ℕ)) :
    aeval r (mvMonomialFin n m) = monomial (ofFin r) m := by
  induction m with
  | nil => simp [mvMonomialFin, monomial]
  | cons v m ih =>
    simp only [mvMonomialFin, monomial, List.map_cons, List.prod_cons, map_mul, map_pow] at ih ⊢
    rw [ih]
    congr 2
    by_cases h : v.1 < n + 1 <;> simp [ofFin, h]

theorem aeval_toMvFin {n : ℕ} (r : Fin (n + 1) → ℝ) (p : RationalPolynomial) (h : p.intCoeffs = true) :
    aeval r (toMvFin n p) = p.eval (ofFin r) := by
  induction p with
  | nil => simp [toMvFin, RationalPolynomial.eval]
  | cons t p ih =>
    rw [intCoeffs, List.all_cons, Bool.and_eq_true] at h
    have hc : ((t.1.num : ℤ) : ℝ) = (t.1 : ℝ) := by
      have hd : t.1.den = 1 := by simpa using h.1
      exact_mod_cast (Rat.coe_int_num_of_den_eq_one hd)
    simp only [toMvFin, RationalPolynomial.eval, List.map_cons, List.sum_cons, map_add, map_mul, eq_intCast,
      map_intCast] at ih ⊢
    rw [aeval_mvMonomialFin, hc, ih h.2]

end RationalPolynomial

namespace PolynomialSystem

/-- Points that agree on the variables with an interval solve a boxed system together. -/
theorem solves_congr {S : PolynomialSystem} (h : S.boxed = true) {x y : ℕ → ℝ}
    (hxy : ∀ i < S.box.length, x i = y i) (hx : S.Solves x) : S.Solves y := by
  rw [boxed, List.all_eq_true] at h
  refine ⟨fun i hi ↦ ?_, fun e he ↦ ?_⟩
  · rw [← hxy i hi]; exact hx.1 i hi
  · have he' := h e he
    rw [Bool.and_eq_true] at he'
    rw [← RationalPolynomial.eval_congr hxy _ he'.1, ← RationalPolynomial.eval_congr hxy _ he'.2]
    exact hx.2 e he

/-- `N` is the largest scale of the systems `Ss`, **each of which has exactly one root**: the list
form of `IsPolyRootMax`, which the theorems `<def>_nu_roots_list` state. -/
def IsRootMax (Ss : List PolynomialSystem) (N : ℝ) : Prop :=
  IsGreatest (scales Ss) N ∧ ∀ S ∈ Ss, S.HasUniqueRoot

/-- A system with exactly one root has one scale. -/
theorem HasUniqueRoot.scales_eq {S : PolynomialSystem} (h : S.HasUniqueRoot) : ∃ v, scales [S] = {v} := by
  obtain ⟨h0, -, x, hx, hu⟩ := h
  refine ⟨x 0, ?_⟩
  ext l
  simp only [scales, Set.mem_ofPred_eq, List.mem_singleton, exists_eq_left, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hu y hy 0 h0
  · rintro rfl
    exact ⟨x, hx, rfl⟩

/-- **One root per system implies one scale per system**: the statement of `<def>_nu_roots_list`
gives that of `<def>_exact_list` for the same systems. -/
theorem IsRootMax.isMaxSingle {Ss : List PolynomialSystem} {N : ℝ} (h : IsRootMax Ss N) :
    IsMaxSingle Ss N :=
  ⟨h.1, fun S hS ↦ (h.2 S hS).scales_eq⟩

/-- `S` as a system of Mathlib polynomials in `n + 1` variables: `p - q = 0` for each equation
`p = q`, the intervals of `S`. -/
noncomputable def toBox (S : PolynomialSystem) (n : ℕ) : BoxSystem n where
  eqs := S.eqs.map fun e ↦ e.1.toMvFin n - e.2.toMvFin n
  box := fun i ↦ S.box.getD i (0, 0)

theorem isRoot_toBox (S : PolynomialSystem) (h : S.intSides = true) {n : ℕ}
    (hn : S.box.length = n + 1) (r : Fin (n + 1) → ℝ) :
    (S.toBox n).IsRoot r ↔ S.Solves (ofFin r) := by
  unfold BoxSystem.IsRoot Solves toBox
  refine and_congr ?_ ?_
  · constructor
    · intro H i hi
      have := H ⟨i, by omega⟩
      rwa [ofFin_lt r (by omega)]
    · intro H i
      have := H i (by have := i.2; omega)
      rwa [ofFin_lt r i.2] at this
  · rw [intSides, List.all_eq_true] at h
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    refine forall₂_congr fun e he ↦ ?_
    have he' := h e he
    rw [Bool.and_eq_true] at he'
    rw [map_sub, RationalPolynomial.aeval_toMvFin r _ he'.1, RationalPolynomial.aeval_toMvFin r _ he'.2, sub_eq_zero]

/-- **Exactly one root in `ℝⁿ⁺¹`**: a system with integer coefficients that has exactly one root
(`HasUniqueRoot`) has, as a system of Mathlib polynomials in its `n + 1` variables, exactly one root in
its box. -/
theorem HasUniqueRoot.existsUnique {S : PolynomialSystem} (h : S.HasUniqueRoot) (hint : S.intSides = true) :
    ∃! r : Fin (S.box.length - 1 + 1) → ℝ, (S.toBox (S.box.length - 1)).IsRoot r := by
  obtain ⟨h0, hb, x, hx, hu⟩ := h
  have hlen : S.box.length = (S.box.length - 1) + 1 := by omega
  refine ⟨fun i ↦ x i, ?_, fun r hr ↦ ?_⟩
  · change (S.toBox (S.box.length - 1)).IsRoot fun i ↦ x i
    rw [isRoot_toBox S hint hlen]
    refine solves_congr hb (fun i hi ↦ ?_) hx
    rw [ofFin_lt _ (by omega)]
  · funext i
    have := hu _ ((isRoot_toBox S hint hlen r).mp hr) i (by have := i.2; omega)
    rwa [ofFin_lt r i.2] at this

/-- **The list form gives `IsPolyRootMax`**: if `N` is the largest scale of the systems `Ss`, each
with exactly one root and all of whose coefficients are integers, then `N` is the largest first
coordinate of the roots of the same systems as Mathlib polynomials, each with exactly one root in
its box. -/
theorem isPolyRootMax {Ss : List PolynomialSystem} (h : Ss.all intSides = true) {N : ℝ}
    (hN : IsRootMax Ss N) : IsPolyRootMax N := by
  have hint : ∀ S ∈ Ss, S.intSides = true := fun S hS ↦ List.all_eq_true.mp h S hS
  have hlen : ∀ S ∈ Ss, S.box.length = (S.box.length - 1) + 1 := fun S hS ↦ by
    have := (hN.2 S hS).1; omega
  -- a solution of `S` restricted to the variables with an interval is a root of its box system
  have hres : ∀ S ∈ Ss, ∀ x : ℕ → ℝ, S.Solves x →
      (S.toBox (S.box.length - 1)).IsRoot fun i ↦ x i := fun S hS x hx ↦ by
    rw [isRoot_toBox S (hint S hS) (hlen S hS)]
    refine solves_congr (hN.2 S hS).2.1 (fun i hi ↦ ?_) hx
    rw [ofFin_lt _ (by have := hlen S hS; omega)]
  refine ⟨Ss.map fun S ↦ ⟨S.box.length - 1, S.toBox (S.box.length - 1)⟩, ?_, ?_⟩
  · intro T hT
    obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hT
    obtain ⟨-, -, x, hx, hu⟩ := hN.2 S hS
    change ∃! r : Fin (S.box.length - 1 + 1) → ℝ, (S.toBox (S.box.length - 1)).IsRoot r
    refine ⟨fun i ↦ x i, hres S hS x hx, fun r hr ↦ ?_⟩
    funext i
    have := hu _ ((isRoot_toBox S (hint S hS) (hlen S hS) r).mp hr) i
      (by have := hlen S hS; have := i.2; omega)
    rwa [ofFin_lt r i.2] at this
  · have hset : {l : ℝ | ∃ T ∈ Ss.map fun S ↦ (⟨S.box.length - 1, S.toBox (S.box.length - 1)⟩ :
        Σ n, BoxSystem n), ∃ x, T.2.IsRoot x ∧ x 0 = l} = scales Ss := by
      ext l
      simp only [Set.mem_ofPred_eq, List.mem_map]
      constructor
      · rintro ⟨_, ⟨S, hS, rfl⟩, r, hr, rfl⟩
        refine ⟨S, hS, ofFin r, (isRoot_toBox S (hint S hS) (hlen S hS) r).mp hr, ?_⟩
        rw [ofFin_lt r (Nat.succ_pos _)]
        rfl
      · rintro ⟨S, hS, x, hx, rfl⟩
        exact ⟨_, ⟨S, hS, rfl⟩, fun i ↦ x i, hres S hS x hx, rfl⟩
    rw [hset]
    exact hN.1

end PolynomialSystem

end Nieuwland
