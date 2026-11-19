import Definitions.Optimum
import Modules.System.PolyAux

/-!
# Enclosures of a system's roots by narrowing

A check that every root of a polynomial system lies in a smaller box, from the system alone:
no certificate, no uniqueness, no existence. It gives the rational enclosures of an optimum
(`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`) at any precision.

A **narrowing step** names a variable `v` and an equation `e`, and is accepted from a box `B`:

* `Narrow.eval v e`, when the equation is `x v = D`: every root in `B` has `v` in the interval
  value of `D` over `B` (`RationalPolynomial.ival`, exact rational interval arithmetic), and the
  step leaves the part of `v`'s interval inside it;
* `Narrow.cut v e a b`, when on each side either the interval of `v` in `B` already ends inside
  `[a, b]` (`a ≤ lo`, `hi ≤ b`), or the equation has no solution in `B` with `v` in the part cut
  off (`[lo, a]`, `[b, hi]`: the interval values of its two sides there are disjoint). Every
  root in `B` has `v` in `[a, b]`, the interval the step leaves (so a cut can also round an
  interval's ends outwards).

The next step starts from `B` with the interval the step left. The steps of an optimum follow
its system's definitions: each variable is narrowed by the equation that defines it.

## Main definitions

* `PolynomialSystem.Narrow`, `narrow`: the steps and the box they lead to.
* `PolynomialSystem.encloseOk`: the check of an enclosure of the optimum's variables.

## Main statements

* `PolynomialSystem.narrow_sound`: every root in the first box lies in the last.
* `PolynomialSystem.enclosedBy_of_encloseOk`: the check proves `EnclosedBy`.
-/

namespace Nieuwland

namespace PolynomialSystem

open RationalPolynomial

/-- A narrowing step. -/
inductive Narrow where
  /-- By the equation `e`, the variable `v` lies in `[a, b]`. -/
  | cut (v e : ℕ) (a b : ℚ)
  /-- The equation `e` is `x v = D`: the variable `v` lies in the interval value of `D`. -/
  | eval (v e : ℕ)

/-- The variable of a step. -/
def Narrow.v : Narrow → ℕ
  | .cut v _ _ _ => v
  | .eval v _ => v

/-- The common part of two intervals. -/
def inter (I J : ℚ × ℚ) : ℚ × ℚ := (max I.1 J.1, min I.2 J.2)

theorem inI_inter {I J : ℚ × ℚ} {x : ℝ} (hI : InI I x) (hJ : InI J x) : InI (inter I J) x := by
  constructor
  · show ((max I.1 J.1 : ℚ) : ℝ) ≤ x
    rw [Rat.cast_max]
    exact max_le hI.1 hJ.1
  · show x ≤ ((min I.2 J.2 : ℚ) : ℝ)
    rw [Rat.cast_min]
    exact le_min hI.2 hJ.2

theorem eval_var (x : ℕ → ℝ) (v : ℕ) : RationalPolynomial.eval [(1, [(v, 1)])] x = x v := by
  simp [RationalPolynomial.eval, monomial]

/-- The equation `p = q` has no solution in the box `B`: the interval values of its sides are
disjoint. -/
def noRoot (B : List (ℚ × ℚ)) (e : RationalPolynomial × RationalPolynomial) : Bool :=
  decide ((ival B e.1).2 < (ival B e.2).1) || decide ((ival B e.2).2 < (ival B e.1).1)

theorem ne_of_noRoot {B : List (ℚ × ℚ)} {e : RationalPolynomial × RationalPolynomial} {x : ℕ → ℝ}
    (h : noRoot B e = true) (hB : ∀ i < B.length, InI (B.getD i (0, 0)) (x i))
    (h1 : e.1.varsLt B.length = true) (h2 : e.2.varsLt B.length = true) :
    e.1.eval x ≠ e.2.eval x := by
  have hp := inI_ival hB e.1 h1
  have hq := inI_ival hB e.2 h2
  rw [noRoot, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  intro heq
  rcases h with h | h
  · have hlt : (((ival B e.1).2 : ℚ) : ℝ) < (((ival B e.2).1 : ℚ) : ℝ) := by exact_mod_cast h
    linarith [hp.2, hq.1]
  · have hlt : (((ival B e.2).2 : ℚ) : ℝ) < (((ival B e.1).1 : ℚ) : ℝ) := by exact_mod_cast h
    linarith [hp.1, hq.2]

/-- The step `s` is accepted from the box `B`. -/
def stepOk (S : PolynomialSystem) (B : List (ℚ × ℚ)) : Narrow → Bool
  | .cut v e a b =>
    decide (v < B.length) && decide (e < S.eqs.length) &&
      (decide (a ≤ (B.getD v (0, 0)).1) ||
        noRoot (B.set v ((B.getD v (0, 0)).1, a)) (S.eqs.getD e ([], []))) &&
      (decide ((B.getD v (0, 0)).2 ≤ b) ||
        noRoot (B.set v (b, (B.getD v (0, 0)).2)) (S.eqs.getD e ([], [])))
  | .eval v e =>
    decide (v < B.length) && decide (e < S.eqs.length) &&
      decide ((S.eqs.getD e ([], [])).1 = [(1, [(v, 1)])])

/-- The interval the step `s` leaves its variable, from the box `B`. -/
def stepInterval (S : PolynomialSystem) (B : List (ℚ × ℚ)) : Narrow → ℚ × ℚ
  | .cut _ _ a b => (a, b)
  | .eval v e => inter (B.getD v (0, 0)) (ival B (S.eqs.getD e ([], [])).2)

/-- The box after the steps, each accepted from the box before it; `none` when one is refused. -/
def narrow (S : PolynomialSystem) : List (ℚ × ℚ) → List Narrow → Option (List (ℚ × ℚ))
  | B, [] => some B
  | B, s :: ss => if stepOk S B s then narrow S (B.set s.v (stepInterval S B s)) ss else none

theorem getD_set_self {α : Type*} (l : List α) {i : ℕ} (a d : α) (h : i < l.length) :
    (l.set i a).getD i d = a := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_set_of_ne {α : Type*} (l : List α) {i j : ℕ} (a d : α) (h : i ≠ j) :
    (l.set i a).getD j d = l.getD j d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

/-- A point of the box `B` with `v` in `I` is a point of `B` with `I` for `v`. -/
theorem inBox_set {B : List (ℚ × ℚ)} {x : ℕ → ℝ} (hB : ∀ i < B.length, InI (B.getD i (0, 0)) (x i))
    {v : ℕ} (hv : v < B.length) {I : ℚ × ℚ} (hI : InI I (x v)) :
    ∀ i < (B.set v I).length, InI ((B.set v I).getD i (0, 0)) (x i) := by
  intro i hi
  rw [List.length_set] at hi
  by_cases h : v = i
  · subst h
    rw [getD_set_self B I (0, 0) hv]
    exact hI
  · rw [getD_set_of_ne B I (0, 0) h]
    exact hB i hi

/-- **One step is sound**: a point of `B` that solves the equations of `S` has the step's
variable in the interval the step leaves. -/
theorem stepOk_sound {S : PolynomialSystem} {B : List (ℚ × ℚ)} {s : Narrow} {x : ℕ → ℝ}
    (hb : S.boxed = true) (hlen : B.length = S.box.length) (h : stepOk S B s = true)
    (hB : ∀ i < B.length, InI (B.getD i (0, 0)) (x i))
    (hx : ∀ e ∈ S.eqs, e.1.eval x = e.2.eval x) :
    ∀ i < (B.set s.v (stepInterval S B s)).length,
      InI ((B.set s.v (stepInterval S B s)).getD i (0, 0)) (x i) := by
  cases s with
  | cut v e a b =>
    simp only [stepOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hv, he⟩, hlo⟩, hhi⟩ := h
    have hmem : S.eqs.getD e ([], []) ∈ S.eqs := getD_mem he
    have hvars := List.all_eq_true.mp hb _ hmem
    rw [Bool.and_eq_true] at hvars
    have hin := hB v hv
    refine inBox_set hB hv ⟨?_, ?_⟩
    · rcases hlo with hlo | hlo
      · exact le_trans (by exact_mod_cast hlo) hin.1
      · by_contra hcon
        have hI : InI ((B.getD v (0, 0)).1, a) (x v) := ⟨hin.1, (not_le.mp hcon).le⟩
        refine ne_of_noRoot hlo (inBox_set hB hv hI) ?_ ?_ (hx _ hmem)
        · rw [List.length_set, hlen]; exact hvars.1
        · rw [List.length_set, hlen]; exact hvars.2
    · rcases hhi with hhi | hhi
      · exact le_trans hin.2 (by exact_mod_cast hhi)
      · by_contra hcon
        have hI : InI (b, (B.getD v (0, 0)).2) (x v) := ⟨(not_le.mp hcon).le, hin.2⟩
        refine ne_of_noRoot hhi (inBox_set hB hv hI) ?_ ?_ (hx _ hmem)
        · rw [List.length_set, hlen]; exact hvars.1
        · rw [List.length_set, hlen]; exact hvars.2
  | eval v e =>
    simp only [stepOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hv, he⟩, hdef⟩ := h
    have hmem : S.eqs.getD e ([], []) ∈ S.eqs := getD_mem he
    have hvars := List.all_eq_true.mp hb _ hmem
    rw [Bool.and_eq_true] at hvars
    have heq := hx _ hmem
    rw [hdef, eval_var] at heq
    refine inBox_set hB hv (inI_inter (hB v hv) ?_)
    rw [heq]
    exact inI_ival hB _ (by rw [hlen]; exact hvars.2)

/-- **Narrowing is sound**: a point of the first box that solves the equations of `S` lies in
the last box. -/
theorem narrow_sound {S : PolynomialSystem} (hb : S.boxed = true) {x : ℕ → ℝ}
    (hx : ∀ e ∈ S.eqs, e.1.eval x = e.2.eval x) :
    ∀ (steps : List Narrow) (B B' : List (ℚ × ℚ)), B.length = S.box.length →
      narrow S B steps = some B' → (∀ i < B.length, InI (B.getD i (0, 0)) (x i)) →
      ∀ i < B'.length, InI (B'.getD i (0, 0)) (x i)
  | [], B, B', _, h, hB => by
    rw [narrow, Option.some.injEq] at h
    rw [← h]
    exact hB
  | s :: ss, B, B', hlen, h, hB => by
    rw [narrow] at h
    split at h
    · rename_i hs
      exact narrow_sound hb hx ss _ B' (by rw [List.length_set, hlen]) h
        (stepOk_sound hb hlen hs hB hx)
    · exact absurd h (by simp)

/-- The check of an enclosure: every variable of the equations has an interval; the steps are
accepted in turn from the box of `S`; `E` has an interval for each of the optimum's variables,
which holds that variable's interval after the steps; and no interval of `E` is wider than `w`. -/
def encloseOk (S : PolynomialSystem) (L : PoseLayout) (steps : List Narrow) (E : List (ℚ × ℚ))
    (w : ℚ) : Bool :=
  S.boxed && match narrow S S.box steps with
    | none => false
    | some B =>
      decide (L.variables.length = E.length) &&
        ((L.variables.zip E).all fun p ↦ decide (p.1 < B.length) &&
          decide (p.2.1 ≤ (B.getD p.1 (0, 0)).1) && decide ((B.getD p.1 (0, 0)).2 ≤ p.2.2)) &&
        E.all fun I ↦ decide (I.2 - I.1 ≤ w)

/-- **The check proves the enclosure.** -/
theorem enclosedBy_of_encloseOk {S : PolynomialSystem} {L : PoseLayout} {steps : List Narrow}
    {E : List (ℚ × ℚ)} {w : ℚ} (h : encloseOk S L steps E w = true) : S.EnclosedBy L E w := by
  rw [encloseOk, Bool.and_eq_true] at h
  obtain ⟨hb, h⟩ := h
  split at h
  · exact absurd h (by simp)
  · rename_i B hB
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨hlen, hin⟩, hw⟩ := h
    refine ⟨List.forall₂_iff_zip.mpr ⟨hlen, fun {i I} hmem x hx ↦ ?_⟩, fun I hI ↦ hw I hI⟩
    obtain ⟨⟨hi, hlo⟩, hhi⟩ := hin (i, I) hmem
    have hbox := narrow_sound hb hx.2 steps S.box B rfl hB hx.1 i hi
    exact ⟨le_trans (by exact_mod_cast hlo) hbox.1, le_trans hbox.2 (by exact_mod_cast hhi)⟩

end PolynomialSystem

end Nieuwland
