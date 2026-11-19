import Mathlib.Algebra.MvPolynomial.Rename
import Modules.System.PolyMax

/-!
# Numbers given by polynomial systems with exactly one root

The shared definition of every solid's theorem `<def>_nu_roots`
(`ν <def> ∈ Set.Icc (k / 10 ^ 30) ((k + 1) / 10 ^ 30) ∧ IsPolyRootMax (ν <def>)`), a stronger
form of the headline `<def>_nu` (`Modules/System/PolyMax.lean`; `IsPolyRootMax.isPolynomialSystemMax`
below):

* `Nieuwland.BoxSystem n`: finitely many polynomial equations `p = 0` with integer coefficients in
  the `n + 1` real variables `x 0, …, x n` (Mathlib's `MvPolynomial (Fin (n + 1)) ℤ`), and a
  closed rational interval for **every** variable: a rational box in `ℝⁿ⁺¹`;
* `Nieuwland.BoxSystem.IsRoot S x`: the point `x` lies in the box of `S` and solves its equations;
* `Nieuwland.IsPolyRootMax a`: there are finitely many such systems, **each with exactly one root in
  its box**, and `a` is the largest value of the first variable `x 0` among those roots.

(Bence Hervay, 2026-11-17.) A system with one root in a rational box is an exact description of
that root: the root can be computed from the system alone to any precision. For each solid the
systems are the definitions `<def>_nu_system_<j>`, each with its theorem
`<def>_nu_system_<j>_oneRoot`, and `<def>_nu_roots_list` states the maximum.
-/

namespace Nieuwland

open MvPolynomial

/-- A system of polynomial equations `p = 0`, each `p` with integer coefficients in the `n + 1`
variables `x 0, …, x n`, and a closed rational interval `box i` for each variable `x i`. -/
structure BoxSystem (n : ℕ) where
  /-- The polynomials, each set to `0`. -/
  eqs : List (MvPolynomial (Fin (n + 1)) ℤ)
  /-- The interval `[lo, hi]` of each variable. -/
  box : Fin (n + 1) → ℚ × ℚ

/-- The real point `x` is a root of `S`: every coordinate lies in its interval, and every
polynomial of `S` is `0` at `x`. -/
def BoxSystem.IsRoot {n : ℕ} (S : BoxSystem n) (x : Fin (n + 1) → ℝ) : Prop :=
  (∀ i, ((S.box i).1 : ℝ) ≤ x i ∧ x i ≤ ((S.box i).2 : ℝ)) ∧ ∀ p ∈ S.eqs, aeval x p = 0

/-- `a` is **the largest first coordinate of the roots** of finitely many systems of integer
polynomial equations, each in a rational box of all its variables and **each with exactly one
root in its box**. -/
def IsPolyRootMax (a : ℝ) : Prop :=
  ∃ Ss : List (Σ n, BoxSystem n), (∀ S ∈ Ss, ∃! x, S.2.IsRoot x) ∧
    IsGreatest {l : ℝ | ∃ S ∈ Ss, ∃ x, S.2.IsRoot x ∧ x 0 = l} a

/-- The system `S` over the variables `x 0, x 1, …` of `IntSystem`: the same polynomials and
intervals. -/
noncomputable def BoxSystem.toInt {n : ℕ} (S : BoxSystem n) : IntSystem where
  eqs := S.eqs.map (rename Fin.val)
  box := List.ofFn S.box

theorem BoxSystem.solves_toInt {n : ℕ} (S : BoxSystem n) (x : ℕ → ℝ) :
    S.toInt.Solves x ↔ S.IsRoot fun i ↦ x i := by
  simp only [IntSystem.Solves, toInt, IsRoot, List.length_ofFn, List.getElem_ofFn,
    List.forall_mem_map, aeval_rename]
  refine and_congr ⟨fun h i ↦ h i i.2, fun h i hi ↦ h ⟨i, hi⟩⟩ Iff.rfl

/-- **The stronger form implies the headline's**: a number with `IsPolyRootMax` has
`IsPolynomialSystemMax`, by the same systems. -/
theorem IsPolyRootMax.isPolynomialSystemMax {a : ℝ} (h : IsPolyRootMax a) : IsPolynomialSystemMax a := by
  obtain ⟨Ss, h1, h2⟩ := h
  have hfv : ∀ S : Σ n, BoxSystem n, S.2.toInt.firstValues = {l | ∃ x, S.2.IsRoot x ∧ x 0 = l} := by
    intro S
    ext l
    simp only [IntSystem.firstValues, Set.mem_ofPred_eq, BoxSystem.solves_toInt]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨fun i ↦ if h : i < S.1 + 1 then x ⟨i, h⟩ else 0, ?_, by simp⟩
      convert hx using 1
      funext i
      simp
  refine ⟨Ss.map fun S ↦ S.2.toInt, ?_, ?_⟩
  · intro T hT
    obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hT
    obtain ⟨x, hx, hu⟩ := h1 S hS
    refine ⟨x 0, ?_⟩
    rw [hfv]
    ext l
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hu y hy]
    · rintro rfl
      exact ⟨x, hx, rfl⟩
  · convert h2 using 1
    ext l
    simp only [List.mem_map, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨T, ⟨S, hS, rfl⟩, hl⟩
      rw [hfv] at hl
      exact ⟨S, hS, hl⟩
    · rintro ⟨S, hS, hl⟩
      exact ⟨_, ⟨S, hS, rfl⟩, by rw [hfv]; exact hl⟩

end Nieuwland
