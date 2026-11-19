import Modules.Nieuwland.Defs
import Modules.System.SystemOps

/-!
# The readable form of a polynomial system

The exact statement of a solid's Nieuwland number is written with free variables, as ordinary
polynomial equations with integer coefficients:

  `IsGreatest {ℓ : ℝ | ∃ s t … : ℝ, ℓ ∈ Set.Icc a b ∧ s ∈ Set.Icc c d ∧ … ∧`
  `  2 * ℓ ^ 2 * s - 3 * t + 1 = 0 ∧ …} N`,

one existential conjunction for each system, joined by `∨`. The proofs work with the list form of
`Modules/System/System.lean` (`PolynomialSystem`, each equation `l = r` with positive coefficients),
whose `decide`-checked comparisons with a certificate's systems are the hot path; this file proves
that the written statement is the list form's (`isGreatest`), so nothing on the hot path changes.

**How a system is written** (`readable`). The variables are `x 0, x 1, …` of the list form, the
statement's `ℓ, s, t, …` in this order: `ℓ` is `x 0`, the scale. First the box, `x i ∈ Set.Icc ↑lo
↑hi` for every interval in the order of the variables, the bounds rationals cast to the reals. Then
each equation `l = r` as the single polynomial `p = l - r` (`RationalPolynomial.add l (RationalPolynomial.neg r)`, the
canonical form of `SystemOps.lean`), written `p = 0` with its terms in decreasing lexicographic
order (`x 0` the highest variable): `t₁ ± t₂ ± ⋯`. A term is `c * x i ^ e * x j ^ f * ⋯`
(left-associated, the variables increasing), without the coefficient when it is `1` and without the
exponent when it is `1`; a constant term is its numeral; the first term carries its sign as `-c * ⋯`
(or `-x i ^ e * ⋯`). Every coefficient must be a nonzero integer (`ok`, checked by `decide`).

## Main statements

* `Nieuwland.Readable.readable_iff`: the written conjunction of a system is its `Solves`.
* `Nieuwland.Readable.isGreatest`: the written statement of a list of systems is its `scales`'.

## Notation

* `ν P`: the Nieuwland number of `P` (`Polyhedron.nieuwland`), in the exact statements
  (`open scoped Nieuwland.Notation`).
* With it, `v ^ n` for a name `v` and a numeral `n` is the natural-number power at once
  (`HPow.hPow v (n : ℕ)`, the term Mathlib's default instance gives later): thousands of
  exponents left to the default instances at the end of a statement run out of recursion depth.
-/

namespace Nieuwland.Notation

/-- The exponent of `v ^ n` (a name and a numeral) is a natural number at once. -/
scoped macro_rules | `($a:ident ^ $n:num) => `(HPow.hPow $a ($n : ℕ))

end Nieuwland.Notation

namespace Nieuwland.Readable

open RationalPolynomial

/-! ### The written form -/

/-- `x i ^ e`, written `x i` when `e = 1`. -/
def pw (x : ℕ → ℝ) (i e : ℕ) : ℝ := if e = 1 then x i else x i ^ e

/-- A positive integer coefficient as written: `1`, or the numeral. -/
def cst (c : ℚ) : ℝ := if c = 1 then 1 else ((c.num.toNat : ℕ) : ℝ)

/-- `a * x i ^ e * x j ^ f * ⋯` (left-associated) for the powers `m`. -/
def mono (x : ℕ → ℝ) (a : ℝ) : List (ℕ × ℕ) → ℝ
  | [] => a
  | (i, e) :: m => mono x (a * pw x i e) m

/-- The term `c * x i ^ e * ⋯` for a positive coefficient `c`. -/
def term (x : ℕ → ℝ) (c : ℚ) : List (ℕ × ℕ) → ℝ
  | [] => cst c
  | (i, e) :: m => mono x (if c = 1 then pw x i e else cst c * pw x i e) m

/-- The term `-c * x i ^ e * ⋯` for a positive coefficient `c`, its minus sign in front. -/
def negTerm (x : ℕ → ℝ) (c : ℚ) : List (ℕ × ℕ) → ℝ
  | [] => -cst c
  | (i, e) :: m => mono x (if c = 1 then -pw x i e else -cst c * pw x i e) m

/-- The leading term, with its sign. -/
def lead (x : ℕ → ℝ) (t : ℚ × List (ℕ × ℕ)) : ℝ :=
  if 0 < t.1 then term x t.1 t.2 else negTerm x (-t.1) t.2

/-- The polynomial `p` (terms increasing) as written: its last term first, then the others added
or subtracted from the last to the first. -/
def written (x : ℕ → ℝ) : RationalPolynomial → ℝ
  | [] => 0
  | [t] => lead x t
  | t :: p => if 0 < t.1 then written x p + term x t.1 t.2 else written x p - term x (-t.1) t.2

/-- The polynomial `l - r` of the equation `l = r`. -/
def diff (e : RationalPolynomial × RationalPolynomial) : RationalPolynomial := add e.1 (neg e.2)

/-- The equations as written: `p₁ = 0 ∧ p₂ = 0 ∧ ⋯ ∧ p_k = 0`. -/
def eqs (x : ℕ → ℝ) : List (RationalPolynomial × RationalPolynomial) → Prop
  | [] => True
  | [e] => written x (diff e) = 0
  | e :: es => written x (diff e) = 0 ∧ eqs x es

/-- The box as written, before `P`: `x i ∈ Set.Icc ↑lo ↑hi ∧ ⋯ ∧ P` from the variable `i` on. -/
def boxed (x : ℕ → ℝ) (i : ℕ) : List (ℚ × ℚ) → Prop → Prop
  | [], P => P
  | b :: bs, P => x i ∈ Set.Icc (b.1 : ℝ) (b.2 : ℝ) ∧ boxed x (i + 1) bs P

/-- The system `S` at `x` as the statement writes it. -/
def readable (S : PolynomialSystem) (x : ℕ → ℝ) : Prop := boxed x 0 S.box (eqs x S.eqs)

/-- `a, x 0, x 1, …`. -/
def cons (a : ℝ) (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => a
  | i + 1 => x i

/-- `∃ a₁ … aₙ : ℝ, P (a₁, …, aₙ, 0, 0, …)`. -/
def ex : ℕ → ((ℕ → ℝ) → Prop) → Prop
  | 0, P => P fun _ ↦ 0
  | n + 1, P => ∃ a : ℝ, ex n fun y ↦ P (cons a y)

/-- `p₁ ∨ p₂ ∨ ⋯ ∨ p_k`. -/
def ors : List Prop → Prop
  | [] => False
  | [p] => p
  | p :: ps => p ∨ ors ps

/-- The systems `Ss` at the scale `ℓ` as the statement writes them, with `n` further variables
for each (`∃ s t …`). -/
def readables (ns : List ℕ) (Ss : List PolynomialSystem) (ℓ : ℝ) : Prop :=
  ors ((ns.zip Ss).map fun nS ↦ ex nS.1 fun y ↦ readable nS.2 (cons ℓ y))

/-! ### The conditions -/

/-- The variables of `p` are below `n`. -/
def varsLt (p : RationalPolynomial) (n : ℕ) : Bool := p.all fun t ↦ t.2.all fun v ↦ decide (v.1 < n)

/-- The coefficients of `p` are nonzero integers. -/
def intCoeffs (p : RationalPolynomial) : Bool := p.all fun t ↦ t.1.den == 1 && t.1 != 0

/-- The conditions of the written form: as many counts as systems, each system's variables below
its count plus one (`ℓ`) and its polynomials with nonzero integer coefficients. -/
def ok (ns : List ℕ) (Ss : List PolynomialSystem) : Bool :=
  ns.length == Ss.length && (ns.zip Ss).all fun nS ↦
    decide (nS.2.box.length ≤ nS.1 + 1) &&
      nS.2.eqs.all fun e ↦ varsLt e.1 (nS.1 + 1) && varsLt e.2 (nS.1 + 1) && intCoeffs (diff e)

/-! ### Values -/

theorem pw_eq (x : ℕ → ℝ) (i e : ℕ) : pw x i e = x i ^ e := by
  unfold pw; split_ifs with h <;> simp [h]

theorem cst_eq {c : ℚ} (h1 : c.den = 1) (h0 : 0 < c) : cst c = c := by
  unfold cst
  split_ifs with h
  · simp [h]
  · have hn : (0 : ℤ) ≤ c.num := (Rat.num_pos.2 h0).le
    have e1 : ((c.num.toNat : ℕ) : ℝ) = ((c.num : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hn
    have e2 : ((c.num : ℤ) : ℝ) = (c : ℝ) := by exact_mod_cast Rat.coe_int_num_of_den_eq_one h1
    rw [e1, e2]

theorem mono_eq (x : ℕ → ℝ) : ∀ (a : ℝ) (m : List (ℕ × ℕ)), mono x a m = a * monomial x m
  | a, [] => by simp [mono, monomial_nil]
  | a, (i, e) :: m => by
    rw [mono, mono_eq x _ m, monomial_cons, pw_eq]; ring

theorem term_eq (x : ℕ → ℝ) {c : ℚ} (h1 : c.den = 1) (h0 : 0 < c) :
    ∀ m : List (ℕ × ℕ), term x c m = c * monomial x m
  | [] => by simp [term, cst_eq h1 h0, monomial_nil]
  | (i, e) :: m => by
    rw [term, mono_eq, monomial_cons, pw_eq]
    split_ifs with h
    · simp [h]
    · rw [cst_eq h1 h0]; ring

theorem negTerm_eq (x : ℕ → ℝ) {c : ℚ} (h1 : c.den = 1) (h0 : 0 < c) :
    ∀ m : List (ℕ × ℕ), negTerm x c m = -(c * monomial x m)
  | [] => by simp [negTerm, cst_eq h1 h0, monomial_nil]
  | (i, e) :: m => by
    rw [negTerm, mono_eq, monomial_cons, pw_eq]
    split_ifs with h
    · simp [h]
    · rw [cst_eq h1 h0]; ring

/-- A coefficient of `intCoeffs`: an integer, and its absolute value a positive one. -/
theorem coeff_cases {c : ℚ} (h : (c.den == 1 && c != 0) = true) :
    (0 < c ∧ c.den = 1) ∨ (¬ 0 < c ∧ 0 < -c ∧ (-c).den = 1) := by
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  by_cases hc : 0 < c
  · exact Or.inl ⟨hc, h.1⟩
  · refine Or.inr ⟨hc, by
      have := lt_of_le_of_ne (not_lt.1 hc) h.2; linarith, by rw [Rat.den_neg_eq_den]; exact h.1⟩

theorem lead_eq (x : ℕ → ℝ) (t : ℚ × List (ℕ × ℕ)) (h : (t.1.den == 1 && t.1 != 0) = true) :
    lead x t = t.1 * monomial x t.2 := by
  unfold lead
  rcases coeff_cases h with ⟨hp, h1⟩ | ⟨hn, hp, h1⟩
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hp), term_eq x h1 hp]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hn), negTerm_eq x h1 hp]; push_cast; ring

theorem written_eq (x : ℕ → ℝ) : ∀ p : RationalPolynomial, intCoeffs p = true → written x p = p.eval x
  | [], _ => by simp [written]
  | [t], h => by
    rw [intCoeffs, List.all_cons, List.all_nil, Bool.and_true] at h
    simp [written, eval_cons, lead_eq x t h]
  | t :: u :: p, h => by
    rw [intCoeffs, List.all_cons, Bool.and_eq_true] at h
    have ih := written_eq x (u :: p) h.2
    change (if 0 < t.1 then written x (u :: p) + term x t.1 t.2 else
      written x (u :: p) - term x (-t.1) t.2) = _
    rw [eval_cons, ih]
    rcases coeff_cases h.1 with ⟨hp, h1⟩ | ⟨hn, hp, h1⟩
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hp), term_eq x h1 hp]; ring
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hn), term_eq x h1 hp]; push_cast; ring

theorem eqs_iff (x : ℕ → ℝ) :
    ∀ es : List (RationalPolynomial × RationalPolynomial), (∀ e ∈ es, intCoeffs (diff e) = true) →
      (eqs x es ↔ ∀ e ∈ es, e.1.eval x = e.2.eval x)
  | [], _ => by simp [eqs]
  | [e], h => by
    change written x (diff e) = 0 ↔ _
    rw [written_eq x _ (h e (by simp)), diff, eval_add, eval_neg, add_neg_eq_zero]
    simp
  | e :: f :: es, h => by
    change (written x (diff e) = 0 ∧ eqs x (f :: es)) ↔ _
    rw [eqs_iff x (f :: es) (fun g hg ↦ h g (List.mem_cons_of_mem _ hg)),
      written_eq x _ (h e (by simp)), diff, eval_add, eval_neg, add_neg_eq_zero]
    simp only [List.forall_mem_cons]

theorem boxed_iff (x : ℕ → ℝ) (P : Prop) : ∀ (B : List (ℚ × ℚ)) (i : ℕ),
    boxed x i B P ↔ (∀ j < B.length, ((B.getD j (0, 0)).1 : ℝ) ≤ x (i + j) ∧
      x (i + j) ≤ ((B.getD j (0, 0)).2 : ℝ)) ∧ P
  | [], i => by simp [boxed]
  | b :: B, i => by
    rw [boxed, boxed_iff x P B (i + 1), Set.mem_Icc]
    constructor
    · rintro ⟨hb, hB, hP⟩
      refine ⟨fun j hj ↦ ?_, hP⟩
      cases j with
      | zero => simpa using hb
      | succ j =>
        have := hB j (by simp at hj; omega)
        rw [show i + (j + 1) = i + 1 + j by omega]
        simpa using this
    · rintro ⟨hB, hP⟩
      refine ⟨by simpa using hB 0 (by simp), fun j hj ↦ ?_, hP⟩
      have := hB (j + 1) (by simp; omega)
      rw [show i + 1 + j = i + (j + 1) by omega]
      simpa using this

/-- **The written form of a system is its list form**, for nonzero integer coefficients. -/
theorem readable_iff (S : PolynomialSystem) (h : ∀ e ∈ S.eqs, intCoeffs (diff e) = true)
    (x : ℕ → ℝ) : readable S x ↔ S.Solves x := by
  rw [readable, boxed_iff, eqs_iff x _ h, PolynomialSystem.Solves]
  simp

/-! ### Variables -/

theorem monomial_congr {x y : ℕ → ℝ} {n : ℕ} (hxy : ∀ i < n, x i = y i) :
    ∀ m : List (ℕ × ℕ), (m.all fun v ↦ decide (v.1 < n)) = true → monomial x m = monomial y m
  | [], _ => by simp [monomial_nil]
  | v :: m, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [monomial_cons, monomial_cons, hxy _ h.1, monomial_congr hxy m h.2]

theorem eval_congr {x y : ℕ → ℝ} {n : ℕ} (hxy : ∀ i < n, x i = y i) :
    ∀ p : RationalPolynomial, varsLt p n = true → p.eval x = p.eval y
  | [], _ => by simp
  | t :: p, h => by
    simp only [varsLt, List.all_cons, Bool.and_eq_true] at h
    rw [eval_cons, eval_cons, monomial_congr hxy _ h.1, eval_congr hxy p h.2]

theorem solves_congr {S : PolynomialSystem} {n : ℕ} (hb : S.box.length ≤ n)
    (he : ∀ e ∈ S.eqs, varsLt e.1 n = true ∧ varsLt e.2 n = true) {x y : ℕ → ℝ}
    (hxy : ∀ i < n, x i = y i) : S.Solves x ↔ S.Solves y := by
  unfold PolynomialSystem.Solves
  refine and_congr (forall_congr' fun i ↦ imp_congr_right fun hi ↦ ?_)
    (forall_congr' fun e ↦ imp_congr_right fun hm ↦ ?_)
  · rw [hxy i (by omega)]
  · rw [eval_congr hxy _ (he e hm).1, eval_congr hxy _ (he e hm).2]

theorem ex_iff : ∀ (n : ℕ) (P : (ℕ → ℝ) → Prop),
    (∀ x y : ℕ → ℝ, (∀ i < n, x i = y i) → (P x ↔ P y)) → (ex n P ↔ ∃ x, P x)
  | 0, P, h => ⟨fun hP ↦ ⟨_, hP⟩,
      fun ⟨x, hx⟩ ↦ (h _ _ fun i hi ↦ absurd hi (Nat.not_lt_zero i)).2 hx⟩
  | n + 1, P, h => by
    have hc : ∀ a, (ex n fun y ↦ P (cons a y)) ↔ ∃ y, P (cons a y) := fun a ↦
      ex_iff n _ fun x y hxy ↦ h _ _ fun i hi ↦ by
        cases i with
        | zero => rfl
        | succ i => exact hxy i (by omega)
    simp only [ex, hc]
    constructor
    · rintro ⟨a, y, hy⟩; exact ⟨_, hy⟩
    · rintro ⟨x, hx⟩
      refine ⟨x 0, fun i ↦ x (i + 1), (h _ _ fun i _ ↦ ?_).2 hx⟩
      cases i <;> rfl

theorem ors_map {α : Type} (f : α → Prop) : ∀ L : List α, ors (L.map f) ↔ ∃ a ∈ L, f a
  | [] => by simp [ors]
  | [a] => by simp [ors]
  | a :: b :: L => by
    change (f a ∨ ors ((b :: L).map f)) ↔ _
    rw [ors_map f (b :: L)]
    simp

/-- **The written systems are the list form's**: under `ok`, the scales of the written statement
are `PolynomialSystem.scales Ss`. -/
theorem readables_iff {ns : List ℕ} {Ss : List PolynomialSystem} (h : ok ns Ss = true) (ℓ : ℝ) :
    readables ns Ss ℓ ↔ ℓ ∈ PolynomialSystem.scales Ss := by
  simp only [ok, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlen, h⟩ := h
  rw [readables, ors_map, PolynomialSystem.scales, Set.mem_ofPred_eq]
  simp only [Prod.exists]
  constructor
  · rintro ⟨n, S, hm, hS⟩
    obtain ⟨hb, he⟩ := h _ hm
    have hS' := (ex_iff n _ fun x y hxy ↦ by
      rw [readable_iff S (fun e he' ↦ (he e he').2) _, readable_iff S (fun e he' ↦ (he e he').2) _]
      exact solves_congr (n := n + 1) hb (fun e he' ↦ ⟨(he e he').1.1, (he e he').1.2⟩)
        fun i hi ↦ by cases i with
          | zero => rfl
          | succ i => exact hxy i (by omega)).1 hS
    obtain ⟨y, hy⟩ := hS'
    exact ⟨S, List.of_mem_zip hm |>.2, _, (readable_iff S (fun e he' ↦ (he e he').2) _).1 hy, rfl⟩
  · rintro ⟨S, hS, x, hx, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hS
    have hi' : i < ns.length := hlen ▸ hi
    have hm : (ns[i], Ss[i]) ∈ ns.zip Ss := by
      rw [List.mem_iff_getElem]
      exact ⟨i, by simp [hi, hi'], by simp⟩
    obtain ⟨hb, he⟩ := h _ hm
    refine ⟨ns[i], Ss[i], hm, ?_⟩
    refine (ex_iff _ _ fun x y hxy ↦ ?_).2 ⟨fun j ↦ x (j + 1), ?_⟩
    · rw [readable_iff _ (fun e he' ↦ (he e he').2) _, readable_iff _ (fun e he' ↦ (he e he').2) _]
      exact solves_congr (n := ns[i] + 1) hb (fun e he' ↦ ⟨(he e he').1.1, (he e he').1.2⟩)
        fun j hj ↦ by cases j with
          | zero => rfl
          | succ j => exact hxy j (by omega)
    · rw [readable_iff _ (fun e he' ↦ (he e he').2) _]
      have : cons (x 0) (fun j ↦ x (j + 1)) = x := funext fun j ↦ by cases j <;> rfl
      rw [this]; exact hx

/-- **The written statement**: a solid's Nieuwland number is the largest scale of the written
systems when it is the largest of `PolynomialSystem.scales Ss`. -/
theorem isGreatest (ns : List ℕ) {Ss : List PolynomialSystem} (h : ok ns Ss = true) {N : ℝ}
    (hN : IsGreatest (PolynomialSystem.scales Ss) N) : IsGreatest {ℓ | readables ns Ss ℓ} N := by
  have : {ℓ | readables ns Ss ℓ} = PolynomialSystem.scales Ss := Set.ext (readables_iff h)
  rw [this]; exact hN

end Nieuwland.Readable
