import Modules.Check.Chart.TreeLeaf

/-!
# Re-charts of chart trees

The re-chart step S2b of chart trees (`Node::rechart` in `code/src/proof/tree.rs`) replaces the
family `(Y, Φ)` of a node by a family `(Z, Φ')` with the same poses. Its data: an affine map
`Φ'(z) = A z + b / L` of `k` new slots (rows `u₀, u₁, u₂, q₀, …, q₃`; the constants are multiples
of the unit `1 / L`), a box `Z`, and polynomials `Ψ_c` (`c < k`), `D`, `λ_u`, `λ_q` in the seven
outputs with coefficients in `κ` (`SPoly κ`). The checks (`Rechart.ok`):

1. the identity `L ∑_c A_rc Ψ_c + b_r D = λ_r x_r` in `κ[x₀, …, x₆]` for every row `r`, with
   `λ_r = λ_u` for `r < 3` and `λ_q` otherwise: the coefficients of every monomial cancel, by the
   zero test of `κ` (`SPoly.zeroOk`);
2. `D`, `λ_u` and `λ_q` at the outputs of the parent map have the declared strict signs on the
   parent box (`posAll`);
3. the image `Ψ / D` lies in `Z`: `δ (hi_c D - den Ψ_c) ≥ 0` and `δ (den Ψ_c - lo_c D) ≥ 0`, with
   `δ` the sign of `D`, each divided by a monomial (bound contract, `weakOk`).

At a point of the parent box with outputs `P`, the point `z = Ψ(P) / D(P)` of `Z` has the outputs
`(λ_u(P) P_u, λ_q(P) P_q) / (L D(P))`: the same pose (`Rechart.step_sound`). Rust's fourth check
(the outputs of the child do not vanish) is not needed: `PoseSim` carries nonzero factors.
-/

namespace Nieuwland.Check

open Pull

/-! ### Sparse polynomials -/

/-- A sparse polynomial with coefficients in `κ`: terms `(c, e)`, the coefficient `c` and the
exponents `e` of the variables `0, 1, …`. -/
abbrev SPoly (κ : Type) := List (κ × List ℕ)

namespace SPoly

/-- The monomial with the exponents `e` of the variables `i, i + 1, …` (`one` if there are
none). -/
def mono {α : Type*} [Mul α] (one : α) (x : ℕ → α) : ℕ → List ℕ → α
  | _, [] => one
  | i, d :: e => if d = 0 then mono one x (i + 1) e else powG one (x i) d * mono one x (i + 1) e

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The value at `x`: the sum of `k c * x^e` over the terms, then `k 0`. -/
def run {α : Type*} [Add α] [Mul α] (k : κ → α) (x : ℕ → α) : SPoly κ → α
  | [] => k (Exact.ofInt 0)
  | t :: p => k t.1 * mono (k (Exact.ofInt 1)) x 0 t.2 + run k x p

section Natural

variable {α β : Type*} [Add α] [Sub α] [Mul α] [Add β] [Sub β] [Mul β] {f : α → β}

omit [Add κ] [Sub κ] [Mul κ] [Exact κ] in
theorem map_mono (hf : IsArith f) (one : α) (x : ℕ → α) :
    ∀ (i : ℕ) (e : List ℕ), f (mono one x i e) = mono (f one) (f ∘ x) i e
  | _, [] => rfl
  | i, d :: e => by
    simp only [mono]
    split_ifs
    · exact map_mono hf one x (i + 1) e
    · rw [hf.map_mul, map_powG hf.map_mul, map_mono hf one x (i + 1) e]
      rfl

theorem map_run (hf : IsArith f) (k : κ → α) (x : ℕ → α) :
    ∀ p : SPoly κ, f (run k x p) = run (f ∘ k) (f ∘ x) p
  | [] => rfl
  | t :: p => by
    simp only [run]
    rw [hf.map_add, hf.map_mul, map_mono hf _ x 0 t.2, map_run hf k x p]
    rfl

end Natural

/-- The polynomial as a computation. -/
def gen (p : SPoly κ) : GenPoly κ where
  run k x := SPoly.run k x p
  natural _ hf k x := map_run hf k x p

/-- `a p`. -/
def scale (a : κ) (p : SPoly κ) : SPoly κ := p.map fun t ↦ (a * t.1, t.2)

/-- The exponents `e` with the exponent of variable `r` (counted from the first) raised by one. -/
def incr : ℕ → List ℕ → List ℕ
  | 0, [] => [1]
  | 0, d :: e => (d + 1) :: e
  | r + 1, [] => 0 :: incr r []
  | r + 1, d :: e => d :: incr r e

/-- `x_r p`. -/
def mulVar (r : ℕ) (p : SPoly κ) : SPoly κ := p.map fun t ↦ (t.1, incr r t.2)

/-- The coefficient of the monomial `e`: the sum of the coefficients of the terms with the
exponents `e`. -/
def coeff (p : SPoly κ) (e : List ℕ) : κ := Exact.sumL ((p.filter fun t ↦ t.2 == e).map Prod.fst)

/-- Every monomial has the coefficient `0` by the zero test of `κ`, so the polynomial is `0`
(`run_eq_zero`). -/
def zeroOk (p : SPoly κ) : Bool := p.all fun t ↦ Exact.isZero (coeff p t.2)

section Eval

omit [Add κ] [Sub κ] [Mul κ] [Exact κ] in
theorem mono_nil (x : ℕ → ℝ) (i : ℕ) : mono (1 : ℝ) x i [] = 1 := rfl

omit [Add κ] [Sub κ] [Mul κ] [Exact κ] in
theorem mono_cons (x : ℕ → ℝ) (i d : ℕ) (e : List ℕ) :
    mono (1 : ℝ) x i (d :: e) = x i ^ d * mono 1 x (i + 1) e := by
  simp only [mono]
  split_ifs with h
  · rw [h, pow_zero, one_mul]
  · rw [powG_one]

theorem re_one : Exact.re (Exact.ofInt 1 : κ) = 1 := by
  rw [Exact.re_ofInt, Int.cast_one]

/-- The value of a term. -/
noncomputable def tval (x : ℕ → ℝ) (t : κ × List ℕ) : ℝ := Exact.re t.1 * mono 1 x 0 t.2

theorem run_eq_sum (x : ℕ → ℝ) : ∀ p : SPoly κ, run Exact.re x p = (p.map (tval x)).sum
  | [] => by simp [run, Exact.re_ofInt]
  | t :: p => by
    rw [run, run_eq_sum x p, List.map_cons, List.sum_cons, re_one]
    rfl

theorem run_append (x : ℕ → ℝ) (p q : SPoly κ) :
    run Exact.re x (p ++ q) = run Exact.re x p + run Exact.re x q := by
  rw [run_eq_sum, run_eq_sum, run_eq_sum, List.map_append, List.sum_append]

theorem run_scale (x : ℕ → ℝ) (a : κ) :
    ∀ p : SPoly κ, run Exact.re x (scale a p) = Exact.re a * run Exact.re x p
  | [] => by simp [scale, run, Exact.re_ofInt]
  | t :: p => by
    have ih := run_scale x a p
    simp only [scale] at ih ⊢
    simp only [List.map_cons, run, ih, Exact.re_mul]
    ring

omit [Add κ] [Sub κ] [Mul κ] [Exact κ] in
theorem mono_incr (x : ℕ → ℝ) : ∀ (r i : ℕ) (e : List ℕ),
    mono (1 : ℝ) x i (incr r e) = x (i + r) * mono 1 x i e
  | 0, i, [] => by simp [incr, mono_cons, mono_nil]
  | 0, i, d :: e => by
    rw [incr, mono_cons, mono_cons, add_zero, pow_succ]
    ring
  | r + 1, i, [] => by
    rw [incr, mono_cons, mono_incr x r (i + 1) [], mono_nil, mono_nil,
      show i + 1 + r = i + (r + 1) by omega]
    ring
  | r + 1, i, d :: e => by
    rw [incr, mono_cons, mono_incr x r (i + 1) e, mono_cons,
      show i + 1 + r = i + (r + 1) by omega]
    ring

theorem run_mulVar (x : ℕ → ℝ) (r : ℕ) :
    ∀ p : SPoly κ, run Exact.re x (mulVar r p) = x r * run Exact.re x p
  | [] => by simp [mulVar, run, Exact.re_ofInt]
  | t :: p => by
    have ih := run_mulVar x r p
    simp only [mulVar] at ih ⊢
    simp only [List.map_cons, run, ih, re_one, mono_incr, zero_add]
    ring

omit [Add κ] [Sub κ] [Mul κ] [Exact κ] in
theorem sum_map_filter_add {γ : Type*} (g : γ → ℝ) (P : γ → Bool) : ∀ l : List γ,
    (l.map g).sum = ((l.filter P).map g).sum + ((l.filter fun a ↦ !P a).map g).sum
  | [] => by simp
  | a :: l => by
    have ih := sum_map_filter_add g P l
    cases h : P a <;> simp [h, ih] <;> ring

theorem sum_filter_eq (x : ℕ → ℝ) (e : List ℕ) : ∀ p : SPoly κ,
    ((p.filter fun t ↦ t.2 == e).map (tval x)).sum = Exact.re (coeff p e) * mono 1 x 0 e
  | [] => by simp [coeff, Exact.re_sumL]
  | t :: p => by
    have ih := sum_filter_eq x e p
    unfold coeff at ih ⊢
    rw [List.filter_cons]
    split_ifs with h
    · have he : t.2 = e := beq_iff_eq.mp h
      have hs (a : κ) (l : List κ) : Exact.sumL (a :: l) = a + Exact.sumL l := rfl
      rw [List.map_cons, List.sum_cons, ih, List.map_cons, hs, Exact.re_add, tval, he]
      ring
    · exact ih

theorem sum_eq_zero (x : ℕ → ℝ) : ∀ (m : ℕ) (p : SPoly κ), p.length ≤ m → zeroOk p = true →
    (p.map (tval x)).sum = 0
  | 0, p, hp, _ => by
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hp)]
    simp
  | _ + 1, [], _, _ => by simp
  | m + 1, t :: q, hp, h => by
    have hall : ∀ s ∈ t :: q, Exact.isZero (coeff (t :: q) s.2) = true := fun s hs ↦
      (List.all_eq_true.mp h) s hs
    rw [sum_map_filter_add (tval x) (fun s ↦ s.2 == t.2) (t :: q), sum_filter_eq x t.2 (t :: q),
      Exact.isZero_sound _ (hall t List.mem_cons_self), zero_mul, zero_add]
    refine sum_eq_zero x m _ ?_ ?_
    · rw [List.filter_cons]
      simp only [beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact (List.length_filter_le _ _).trans (Nat.le_of_succ_le_succ hp)
    · unfold zeroOk
      rw [List.all_eq_true]
      intro s hs
      have hs' := List.mem_filter.mp hs
      have hne : s.2 ≠ t.2 := by simpa using hs'.2
      have hco : coeff ((t :: q).filter fun u ↦ !(u.2 == t.2)) s.2 = coeff (t :: q) s.2 := by
        unfold coeff
        rw [List.filter_filter]
        congr 2
        apply List.filter_congr
        intro u _
        by_cases hu : u.2 = s.2
        · simp [hu, hne]
        · simp [hu]
      rw [hco]
      exact hall s hs'.1

/-- **Zero polynomials.** If every monomial has the coefficient `0`, the value is `0`. -/
theorem run_eq_zero {p : SPoly κ} (h : zeroOk p = true) (x : ℕ → ℝ) :
    run Exact.re x p = 0 := by
  rw [run_eq_sum]
  exact sum_eq_zero x p.length p le_rfl h

end Eval

end SPoly

/-! ### Signs on boxes -/

section Signs

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- Each computation, divided by its monomial (whose sign on the box is not `0`), is nonnegative on
the box `b` of `n` slots (bound contract). -/
def weakOk (n : ℕ) (b : Box) (depth : ℕ) (ts : List (Term κ)) : Bool :=
  ts.all (fun t ↦ monoSign n b t.e != 0) &&
    Pull.check n ts false depth b
      ((List.range ts.length).map fun i ↦ [(i, monoSign n b (ts.getD i default).e)])

theorem weakOk_sound {n : ℕ} {b : Box} {depth : ℕ} {ts : List (Term κ)}
    (h : weakOk n b depth ts = true) {z : Fin n → ℝ} (hz : b.Mem n z) :
    ∀ t ∈ ts, 0 ≤ t.G.run Exact.re (ext n z) := by
  simp only [weakOk, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨hsg, hc⟩ := h
  have hden : 0 < b.den := Pull.den_pos_of_check hc
  intro t ht
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
  have hti : ts.getD i default = ts[i] := List.getD_eq_getElem _ _ hi
  have hmem : [(i, monoSign n b (ts.getD i default).e)] ∈
      (List.range ts.length).map fun i ↦ [(i, monoSign n b (ts.getD i default).e)] :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  obtain ⟨c, hc0, s, heq, hsign⟩ := Pull.check_sound hc _ hmem z hz
  have he := heq _ List.mem_cons_self
  rw [hti] at he
  simp only [Sign, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, hti] at hsign
  have hs0 : monoSign n b ts[i].e ≠ 0 := hsg _ (List.getElem_mem hi)
  exact nonneg_of_signed hc0 (monoSign_eq hs0) (monoSign_mul_nonneg hs0 hden hz) he hsign

/-- Each computation is positive on the box `b` of `n` slots (undivided). -/
def posAll (n : ℕ) (b : Box) (depth : ℕ) (gs : List (GenPoly κ)) : Bool :=
  Pull.check n (gs.map fun G ↦ ⟨G, []⟩) true depth b
    ((List.range gs.length).map fun i ↦ [(i, 1)])

omit [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] in
theorem monoVal_nil {R : Type*} [CommMonoid R] :
    ∀ (n : ℕ) (x : Fin n → R), DPoly.monoVal n [] x = 1
  | 0, _ => rfl
  | n + 1, x => by simp [DPoly.monoVal, monoVal_nil n]

theorem posAll_sound {n : ℕ} {b : Box} {depth : ℕ} {gs : List (GenPoly κ)}
    (h : posAll n b depth gs = true) {z : Fin n → ℝ} (hz : b.Mem n z) :
    ∀ G ∈ gs, 0 < G.run Exact.re (ext n z) := by
  intro G hG
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hG
  have hmem : [(i, (1 : ℤ))] ∈ (List.range gs.length).map fun i ↦ [(i, (1 : ℤ))] :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  obtain ⟨c, hc0, s, heq, hsign⟩ := Pull.check_sound h _ hmem z hz
  have he := heq _ List.mem_cons_self
  rw [getD_map_of_lt _ default _ hi] at he
  simp only [List.getD_eq_getElem _ _ hi, monoVal_nil, mul_one] at he
  simp only [Sign, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, Int.cast_one, one_mul] at hsign
  rw [he]
  exact mul_pos hc0 hsign

end Signs

/-! ### Re-charts -/

/-- `1` for `true`, `-1` for `false`. -/
def sgnOf (s : Bool) : ℤ := bif s then 1 else -1

theorem sgnOf_mul_self (s : Bool) : (sgnOf s : ℝ) * sgnOf s = 1 := by
  cases s <;> simp [sgnOf]

/-- A re-chart step (S2b) to `k` new slots (see the module doc). The polynomials are in the seven
outputs of the parent map, the exponents of the bound contract in the parent's slots. -/
structure Rechart (κ : Type) where
  /-- The number of new slots. -/
  k : ℕ
  /-- The rows `u₀, u₁, u₂, q₀, …, q₃` of `A`, one entry per new slot. -/
  a : List (List κ)
  /-- The constants of the rows, in multiples of the unit `1 / L`. -/
  b : List κ
  /-- The numerators `Ψ_c` of the new slots. -/
  psi : List (SPoly κ)
  /-- The denominator `D`. -/
  d : SPoly κ
  /-- The factor `λ_u` of the view. -/
  lu : SPoly κ
  /-- The factor `λ_q` of the quaternion. -/
  lq : SPoly κ
  /-- The signs of `D`, `λ_u` and `λ_q` on the parent box (`true`: positive). -/
  sgns : Bool × Bool × Bool
  /-- The numerators of the lower ends of the new slots, over `den`. -/
  lo : List ℤ
  /-- The numerators of the upper ends of the new slots, over `den`. -/
  hi : List ℤ
  /-- The denominator of the new box. -/
  den : ℕ
  /-- For each new slot, the exponents of the monomials dividing its upper and its lower range
  condition. -/
  exps : List (List ℕ × List ℕ)
  /-- The bisection depth of the sign checks. -/
  depth : ℕ

namespace Rechart

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] (R : Rechart κ)

/-- `λ_u` for the rows `0, 1, 2`, `λ_q` for the others. -/
def lam (r : ℕ) : SPoly κ := if r < 3 then R.lu else R.lq

/-- The integer `a` in `κ`. -/
abbrev ki (a : ℤ) : κ := Exact.ofInt a

/-- `L ∑_{c < m} A_rc Ψ_c`. -/
def linS (L r : ℕ) : ℕ → SPoly κ
  | 0 => []
  | c + 1 => linS L r c ++
      SPoly.scale (ki L * (R.a.getD r []).getD c (ki 0)) (R.psi.getD c [])

/-- The identity of row `r`, a polynomial that must vanish: `L ∑_c A_rc Ψ_c + b_r D - λ_r x_r`. -/
def row (L r : ℕ) : SPoly κ :=
  R.linS L r R.k ++ SPoly.scale (R.b.getD r (ki 0)) R.d ++
    SPoly.scale (ki (-1)) (SPoly.mulVar r (R.lam r))

/-- The upper range condition of new slot `c`: `δ (hi_c D - den Ψ_c)`. -/
def upper (c : ℕ) : SPoly κ :=
  SPoly.scale (ki (sgnOf R.sgns.1))
    (SPoly.scale (ki (R.hi.getD c 0)) R.d ++ SPoly.scale (ki (-R.den)) (R.psi.getD c []))

/-- The lower range condition of new slot `c`: `δ (den Ψ_c - lo_c D)`. -/
def lower (c : ℕ) : SPoly κ :=
  SPoly.scale (ki (sgnOf R.sgns.1))
    (SPoly.scale (ki R.den) (R.psi.getD c []) ++ SPoly.scale (ki (-R.lo.getD c 0)) R.d)

/-- The strict conditions: `D`, `λ_u` and `λ_q` times their signs. -/
def strict : List (SPoly κ) :=
  [SPoly.scale (ki (sgnOf R.sgns.1)) R.d, SPoly.scale (ki (sgnOf R.sgns.2.1)) R.lu,
    SPoly.scale (ki (sgnOf R.sgns.2.2)) R.lq]

/-- The range conditions at the outputs of `Ψ`, upper then lower for each new slot, with their
monomials. -/
def ranges (Ψ : GenMap κ) : List (Term κ) :=
  (List.range R.k).flatMap fun c ↦
    [⟨(SPoly.gen (R.upper c)).comp Ψ, (R.exps.getD c ([], [])).1⟩,
      ⟨(SPoly.gen (R.lower c)).comp Ψ, (R.exps.getD c ([], [])).2⟩]

/-- **The check of a re-chart** of the family with map `Ψ` on the box `b` of `n` slots, with the
unit `1 / L`. -/
def ok (n L : ℕ) (Ψ : GenMap κ) (b : Box) : Bool :=
  decide (R.k < n) && decide (0 < R.den) && decide (0 < L) && decide (R.den % L = 0) &&
    (List.range 7).all (fun r ↦ SPoly.zeroOk (R.row L r)) &&
    posAll n b R.depth (R.strict.map fun p ↦ (SPoly.gen p).comp Ψ) &&
    weakOk n b R.depth (R.ranges Ψ)

/-- `∑_{c < m} k (row_c) x_c`, after `k 0`, without the entries that are zero
(`Exact.isZero`): they add nothing, and without them the formal shapes of the outputs
(`Term.shapeOf`) have only the slots that the row uses, so that the packings of the terms below
the re-chart are not larger than their degrees need. -/
def lin {α : Type*} [Add α] [Mul α] (kk : κ → α) (x : ℕ → α) (row : List κ) : ℕ → α
  | 0 => kk (ki 0)
  | c + 1 => bif Exact.isZero (row.getD c (ki 0)) then lin kk x row c
      else lin kk x row c + kk (row.getD c (ki 0)) * x c

omit R in
theorem map_lin {α β : Type*} [Add α] [Sub α] [Mul α] [Add β] [Sub β] [Mul β] {f : α → β}
    (hf : IsArith f) (kk : κ → α) (x : ℕ → α) (row : List κ) :
    ∀ m, f (lin kk x row m) = lin (f ∘ kk) (f ∘ x) row m
  | 0 => rfl
  | m + 1 => by
    simp only [lin]
    cases Exact.isZero (row.getD m (ki 0))
    · rw [Bool.cond_false, Bool.cond_false, hf.map_add, hf.map_mul, map_lin hf kk x row m]
      rfl
    · rw [Bool.cond_true, Bool.cond_true, map_lin hf kk x row m]

/-- The child map with the unit slot `U`: output `r < 7` is `∑_c A_rc x_c + b_r x_U`. -/
def cmap (U : ℕ) : GenMap κ where
  run kk x i := if i < 7 then lin kk x (R.a.getD i []) R.k + kk (R.b.getD i (ki 0)) * x U
    else kk (ki 0)
  natural f hf kk x := by
    funext i
    simp only [Function.comp_apply]
    split_ifs
    · rw [hf.map_add, map_lin hf, hf.map_mul]
    · rfl

/-- The child box of `n` slots with the unit `1 / L`: the new slots in `[lo_c, hi_c] / den`, the
unit slot `n - 1` at `1 / L`, the others at `0`. -/
def cbox (n L : ℕ) : Box where
  lo := (List.range n).map fun i ↦
    if i < R.k then R.lo.getD i 0 else if i = n - 1 then ((R.den / L : ℕ) : ℤ) else 0
  hi := (List.range n).map fun i ↦
    if i < R.k then R.hi.getD i 0 else if i = n - 1 then ((R.den / L : ℕ) : ℤ) else 0
  den := R.den

/-- **The re-chart step** of a chart tree with `n` slots and the unit `1 / L`. -/
def step (n L : ℕ) : StepFn κ (Rechart κ) := fun R Φ σ b ↦
  if R.ok n L (Φ.comp σ) b then some (R.cmap (n - 1), GenMap.id, R.cbox n L) else none

theorem run_linS (L r : ℕ) (P : ℕ → ℝ) : ∀ m,
    SPoly.run Exact.re P (R.linS L r m) = ∑ c ∈ Finset.range m,
      (L : ℝ) * Exact.re ((R.a.getD r []).getD c (ki 0)) *
        SPoly.run Exact.re P (R.psi.getD c [])
  | 0 => by simp [linS, SPoly.run, Exact.re_ofInt]
  | m + 1 => by
    rw [linS, SPoly.run_append, run_linS L r P m, SPoly.run_scale, Finset.sum_range_succ,
      Exact.re_mul, ki, Exact.re_ofInt]
    push_cast
    ring

omit R in
theorem lin_re (x : ℕ → ℝ) (row : List κ) : ∀ m,
    lin Exact.re x row m = ∑ c ∈ Finset.range m, Exact.re (row.getD c (ki 0)) * x c
  | 0 => by simp [lin, Exact.re_ofInt]
  | m + 1 => by
    rw [lin, Finset.sum_range_succ, ← lin_re x row m]
    cases h : Exact.isZero (row.getD m (ki 0))
    · rw [Bool.cond_false]
    · rw [Bool.cond_true, Exact.isZero_sound _ h, zero_mul, add_zero]

variable {R}

/-- **Re-charts are sound**: every point of the parent box is covered by a point of the child
box with the same pose. -/
theorem step_sound (n L : ℕ) : StepSound ⟨n, n - 1, []⟩ (step (κ := κ) n L) := by
  intro R Φ σ b Φ' σ' b' h y hy
  simp only [step] at h
  split_ifs at h with hok
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  simp only [ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨⟨hk, hden⟩, hL⟩, hLd⟩, hid⟩, hpos⟩, hweak⟩ := hok
  -- The values at the parent's outputs `P`.
  set P := (Φ.comp σ).run Exact.re (ext n y) with hP
  have hcomp (p : SPoly κ) : ((SPoly.gen p).comp (Φ.comp σ)).run Exact.re (ext n y) =
      SPoly.run Exact.re P p := rfl
  have hpos' := posAll_sound hpos hy
  have hsd : 0 < (sgnOf R.sgns.1 : ℝ) * SPoly.run Exact.re P R.d := by
    have := hpos' _
      (List.mem_map.mpr ⟨SPoly.scale (ki (sgnOf R.sgns.1)) R.d, by simp [strict], rfl⟩)
    rwa [hcomp, SPoly.run_scale, ki, Exact.re_ofInt] at this
  have hsu : 0 < (sgnOf R.sgns.2.1 : ℝ) * SPoly.run Exact.re P R.lu := by
    have := hpos' _ (List.mem_map.mpr ⟨SPoly.scale (ki (sgnOf R.sgns.2.1)) R.lu, by simp [strict],
      rfl⟩)
    rwa [hcomp, SPoly.run_scale, ki, Exact.re_ofInt] at this
  have hsq : 0 < (sgnOf R.sgns.2.2 : ℝ) * SPoly.run Exact.re P R.lq := by
    have := hpos' _ (List.mem_map.mpr ⟨SPoly.scale (ki (sgnOf R.sgns.2.2)) R.lq, by simp [strict],
      rfl⟩)
    rwa [hcomp, SPoly.run_scale, ki, Exact.re_ofInt] at this
  have hD : SPoly.run Exact.re P R.d ≠ 0 := fun h0 ↦ by
    rw [h0, mul_zero] at hsd
    exact lt_irrefl _ hsd
  have hU : SPoly.run Exact.re P R.lu ≠ 0 := fun h0 ↦ by
    rw [h0, mul_zero] at hsu
    exact lt_irrefl _ hsu
  have hQ : SPoly.run Exact.re P R.lq ≠ 0 := fun h0 ↦ by
    rw [h0, mul_zero] at hsq
    exact lt_irrefl _ hsq
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hden' : (0 : ℝ) < R.den := by exact_mod_cast hden
  -- The new slots lie in their ranges.
  have hweak' := weakOk_sound hweak hy
  have hrange (c : ℕ) (hc : c < R.k) :
      (R.lo.getD c 0 : ℝ) / R.den ≤ SPoly.run Exact.re P (R.psi.getD c []) /
          SPoly.run Exact.re P R.d ∧
        SPoly.run Exact.re P (R.psi.getD c []) / SPoly.run Exact.re P R.d ≤
          (R.hi.getD c 0 : ℝ) / R.den := by
    have hu := hweak' ⟨(SPoly.gen (R.upper c)).comp (Φ.comp σ), (R.exps.getD c ([], [])).1⟩
      (List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, by simp⟩)
    have hl := hweak' ⟨(SPoly.gen (R.lower c)).comp (Φ.comp σ), (R.exps.getD c ([], [])).2⟩
      (List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, by simp⟩)
    simp only [hcomp, upper, lower, SPoly.run_scale, SPoly.run_append, ki, Exact.re_ofInt] at hu hl
    have hδ := sgnOf_mul_self R.sgns.1
    have hq : SPoly.run Exact.re P (R.psi.getD c []) / SPoly.run Exact.re P R.d =
        ((sgnOf R.sgns.1 : ℝ) * SPoly.run Exact.re P (R.psi.getD c [])) /
          ((sgnOf R.sgns.1 : ℝ) * SPoly.run Exact.re P R.d) := by
      rw [mul_div_mul_left _ _ (fun h0 ↦ by rw [h0, zero_mul] at hδ; exact zero_ne_one hδ)]
    rw [hq, div_le_div_iff₀ hden' hsd, div_le_div_iff₀ hsd hden']
    push_cast at hu hl
    constructor <;> nlinarith
  -- The child point.
  set z : Fin n → ℝ := fun i ↦ if (i : ℕ) < R.k then
      SPoly.run Exact.re P (R.psi.getD i []) / SPoly.run Exact.re P R.d
    else if (i : ℕ) = n - 1 then (L : ℝ)⁻¹ else 0 with hz
  have hext (c : ℕ) (hc : c < R.k) :
      ext n z c = SPoly.run Exact.re P (R.psi.getD c []) / SPoly.run Exact.re P R.d := by
    simp [Pull.ext, show c < n by omega, hz, hc]
  have hextU : ext n z (n - 1) = (L : ℝ)⁻¹ := by
    simp [Pull.ext, show n - 1 < n by omega, hz, show ¬ n - 1 < R.k by omega]
  refine ⟨z, ?_, fun i hi ↦ by simp at hi, ?_⟩
  · -- `z` is in the child box.
    intro i
    simp only [cbox, Box.getD_range_map _ _ _ i.isLt, hz]
    split_ifs with h1 h2
    · exact hrange i h1
    · have hdvd : L ∣ R.den := Nat.dvd_of_mod_eq_zero hLd
      rw [Int.cast_natCast, Nat.cast_div hdvd hL'.ne', div_div_cancel_left' hden'.ne']
      exact ⟨le_refl _, le_refl _⟩
    · simp
  · -- The same pose.
    set o := ((R.cmap (n - 1)).comp GenMap.id).run Exact.re (ext n z) with ho
    have hrow (r : ℕ) (hr : r < 7) :
        o r * (L * SPoly.run Exact.re P R.d) = SPoly.run Exact.re P (R.lam r) * P r := by
      have h0 := SPoly.run_eq_zero (hid r hr) P
      simp only [row, SPoly.run_append, SPoly.run_scale, SPoly.run_mulVar, run_linS, ki,
        Exact.re_ofInt] at h0
      have hlin : lin Exact.re (ext n z) (R.a.getD r []) R.k *
          (L * SPoly.run Exact.re P R.d) = ∑ c ∈ Finset.range R.k,
            (L : ℝ) * Exact.re ((R.a.getD r []).getD c (ki 0)) *
              SPoly.run Exact.re P (R.psi.getD c []) := by
        rw [lin_re, Finset.sum_mul]
        refine Finset.sum_congr rfl fun c hc ↦ ?_
        rw [hext c (Finset.mem_range.mp hc)]
        field_simp
      simp only [ho, GenMap.comp, GenMap.id, cmap, hr, ↓reduceIte, hextU]
      rw [add_mul, hlin]
      field_simp
      linear_combination h0
    have hlamU (i : Fin 3) : R.lam i = R.lu := by simp [lam, i.isLt]
    have hlamQ (i : Fin 4) : R.lam (i + 3) = R.lq := by simp [lam]
    refine ⟨L * SPoly.run Exact.re P R.d / SPoly.run Exact.re P R.lu,
      L * SPoly.run Exact.re P R.d / SPoly.run Exact.re P R.lq, ?_, ?_, ?_, ?_⟩
    · exact div_ne_zero (mul_ne_zero hL'.ne' hD) hU
    · exact div_ne_zero (mul_ne_zero hL'.ne' hD) hQ
    · funext i
      have := hrow i (by omega)
      rw [hlamU] at this
      simp only [outU, Pi.smul_apply, smul_eq_mul]
      rw [div_mul_eq_mul_div, eq_div_iff hU]
      linear_combination -1 * this
    · funext i
      have := hrow (i + 3) (by omega)
      rw [hlamQ] at this
      simp only [outQ, Pi.smul_apply, smul_eq_mul]
      rw [div_mul_eq_mul_div, eq_div_iff hQ]
      linear_combination -1 * this

end Rechart

end Nieuwland.Check
