import Modules.Check.Chart.Rechart

/-!
# Sparse polynomials as a ring: exact leaf maps

`SP κ` holds sparse polynomials with coefficients in `κ` (`SPoly κ`) as a type with `+`, `-` and
`*`, so that generic computations run in it exactly: the outputs of a pose map `Φ` become the
sparse polynomials of its outputs in its inputs (`GenMap.polys`), with like terms merged and zero
coefficients (`Exact.isZero`) dropped, as rupert composes the maps of chart-tree nodes
(`Node::map_all`, `code/src/proof/tree.rs`). The terms are kept sorted by their exponents
(`cmpE`), so that sums merge sorted lists.

Evaluation at a real point commutes with the operations whatever the order of the terms
(`SP.isArith_eval`), so by naturality the map of the polynomials (`GenMap.ofPolys`) has the
outputs of `Φ` at every real point (`GenMap.ofPolys_polys`). Its formal shapes and norms
(`Pull.Term.shapeOf`, `Pull.Term.norm`) are those of the polynomials themselves: a slot whose
coefficients cancel in `Φ` no longer counts.
-/

namespace Nieuwland.Check

/-! ### Exponents -/

/-- The lexicographic order of exponent lists, a missing exponent read as `0`. -/
def cmpE : List ℕ → List ℕ → Ordering
  | [], [] => .eq
  | [], b :: f => bif b == 0 then cmpE [] f else .lt
  | a :: e, [] => bif a == 0 then cmpE e [] else .gt
  | a :: e, b :: f => bif Nat.blt a b then .lt else bif Nat.blt b a then .gt else cmpE e f

/-- The exponents of the product of two monomials. -/
def addE : List ℕ → List ℕ → List ℕ
  | [], f => f
  | a :: e, [] => a :: e
  | a :: e, b :: f => (a + b) :: addE e f

namespace SPoly

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The sum of the term lists `p` and `q`, reversed onto `acc` (tail-recursive): for sorted lists,
their sorted sum reversed, with like terms merged and zero coefficients dropped (`merge`). -/
def mergeR (p q acc : SPoly κ) : SPoly κ :=
  match p, q with
  | [], q => q.reverseAux acc
  | t :: p, [] => p.reverseAux (t :: acc)
  | t :: p', s :: q' =>
    match cmpE t.2 s.2 with
    | .lt => mergeR p' (s :: q') (t :: acc)
    | .gt => mergeR (t :: p') q' (s :: acc)
    | .eq => mergeR p' q' (bif Exact.isZero (t.1 + s.1) then acc else (t.1 + s.1, t.2) :: acc)
termination_by p.length + q.length

/-- The sum of two term lists: for sorted lists, sorted, with like terms merged and zero
coefficients dropped. -/
def merge (p q : SPoly κ) : SPoly κ := (mergeR p q []).reverse

/-- `-p`. -/
def neg (p : SPoly κ) : SPoly κ := p.map fun t ↦ (Exact.ofInt 0 - t.1, t.2)

/-- `c x^e q`, without the terms whose coefficients are zero. -/
def mulTerm (c : κ) (e : List ℕ) (q : SPoly κ) : SPoly κ :=
  q.filterMap fun s ↦ bif Exact.isZero (c * s.1) then none else some (c * s.1, addE e s.2)

/-- The products of the terms of `p` with those of `q`, unsorted, without zero coefficients. -/
def prods (p q : SPoly κ) : SPoly κ := p.flatMap fun t ↦ mulTerm t.1 t.2 q

/-- `t` onto `acc`, unless its coefficient is zero. -/
def push (t : κ × List ℕ) (acc : SPoly κ) : SPoly κ := bif Exact.isZero t.1 then acc else t :: acc

/-- The pending term `t` and the terms `p`, adjacent like terms merged, reversed onto `acc`
(tail-recursive). -/
def combR (t : κ × List ℕ) : SPoly κ → SPoly κ → SPoly κ
  | [], acc => push t acc
  | s :: p, acc =>
    match cmpE t.2 s.2 with
    | .eq => combR (t.1 + s.1, t.2) p acc
    | _ => combR s p (push t acc)

/-- The terms sorted by their exponents (`cmpE`), like terms merged, zero coefficients
dropped. -/
def normal (p : SPoly κ) : SPoly κ :=
  match p.mergeSort fun a b ↦ cmpE a.2 b.2 != .gt with
  | [] => []
  | t :: q => (combR t q []).reverse

/-- `p q`: all products of terms, sorted and merged (`normal`). -/
def mul (p q : SPoly κ) : SPoly κ := normal (prods p q)

end SPoly

/-! ### The ring -/

/-- Sparse polynomials with coefficients in `κ`, with `+`, `-` and `*` (`SPoly.merge`,
`SPoly.mul`). -/
structure SP (κ : Type) where
  /-- The terms. -/
  terms : SPoly κ

namespace SP

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

instance : Add (SP κ) := ⟨fun p q ↦ ⟨SPoly.merge p.terms q.terms⟩⟩
instance : Sub (SP κ) := ⟨fun p q ↦ ⟨SPoly.merge p.terms (SPoly.neg q.terms)⟩⟩
instance : Mul (SP κ) := ⟨fun p q ↦ ⟨SPoly.mul p.terms q.terms⟩⟩

/-- The constant `c`. -/
def cst (c : κ) : SP κ := ⟨bif Exact.isZero c then [] else [(c, [])]⟩

/-- The variable `x_i`. -/
def var (i : ℕ) : SP κ := ⟨[(Exact.ofInt 1, List.replicate i 0 ++ [1])]⟩

end SP

/-! ### Evaluation at real points -/

namespace SPoly

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

omit [Add κ] [Sub κ] [Mul κ] [Exact κ] in
theorem mono_zero_cons (x : ℕ → ℝ) (i : ℕ) (e : List ℕ) :
    mono (1 : ℝ) x i (0 :: e) = mono 1 x (i + 1) e := by
  simp only [mono, ↓reduceIte]

omit [Add κ] [Sub κ] [Mul κ] [Exact κ] in
/-- Exponent lists equal in `cmpE` give the same monomial. -/
theorem mono_eq_of_cmpE (x : ℕ → ℝ) : ∀ (e f : List ℕ) (i : ℕ), cmpE e f = .eq →
    mono (1 : ℝ) x i e = mono 1 x i f
  | [], [], _, _ => rfl
  | [], b :: f, i, h => by
    unfold cmpE at h
    cases hb : b == 0
    · simp [hb] at h
    · rw [hb, Bool.cond_true] at h
      rw [beq_iff_eq] at hb
      subst hb
      rw [mono_zero_cons, ← mono_eq_of_cmpE x [] f (i + 1) h, mono_nil, mono_nil]
  | a :: e, [], i, h => by
    unfold cmpE at h
    cases ha : a == 0
    · simp [ha] at h
    · rw [ha, Bool.cond_true] at h
      rw [beq_iff_eq] at ha
      subst ha
      rw [mono_zero_cons, mono_eq_of_cmpE x e [] (i + 1) h, mono_nil, mono_nil]
  | a :: e, b :: f, i, h => by
    unfold cmpE at h
    cases h1 : Nat.blt a b
    · cases h2 : Nat.blt b a
      · rw [h1, h2, Bool.cond_false, Bool.cond_false] at h
        have hab : a = b := by
          have h1' : ¬a < b := by rw [← Nat.blt_eq, h1]; decide
          have h2' : ¬b < a := by rw [← Nat.blt_eq, h2]; decide
          omega
        subst hab
        rw [mono_cons, mono_cons, mono_eq_of_cmpE x e f (i + 1) h]
      · simp [h1, h2] at h
    · simp [h1] at h

omit [Add κ] [Sub κ] [Mul κ] [Exact κ] in
/-- The monomial of `addE e f` is the product of the monomials. -/
theorem mono_addE (x : ℕ → ℝ) : ∀ (e f : List ℕ) (i : ℕ),
    mono (1 : ℝ) x i (addE e f) = mono 1 x i e * mono 1 x i f
  | [], f, i => by rw [addE, mono_nil, one_mul]
  | a :: e, [], i => by rw [addE, mono_nil, mul_one]
  | a :: e, b :: f, i => by
    rw [addE, mono_cons, mono_cons, mono_cons, mono_addE x e f (i + 1), pow_add]
    ring

omit [Add κ] [Sub κ] [Mul κ] [Exact κ] in
theorem mono_var (x : ℕ → ℝ) : ∀ i j : ℕ, mono (1 : ℝ) x j (List.replicate i 0 ++ [1]) = x (j + i)
  | 0, j => by rw [List.replicate_zero, List.nil_append, mono_cons, mono_nil, pow_one, mul_one,
      add_zero]
  | i + 1, j => by
    rw [List.replicate_succ, List.cons_append, mono_zero_cons, mono_var x i (j + 1),
      Nat.add_right_comm, Nat.add_assoc]

theorem run_nil (x : ℕ → ℝ) : run Exact.re x ([] : SPoly κ) = 0 := by
  rw [run, Exact.re_ofInt, Int.cast_zero]

theorem run_cons (x : ℕ → ℝ) (t : κ × List ℕ) (p : SPoly κ) :
    run Exact.re x (t :: p) = Exact.re t.1 * mono 1 x 0 t.2 + run Exact.re x p := by
  rw [run, re_one]

theorem sum_tval_reverseAux (x : ℕ → ℝ) (p acc : SPoly κ) :
    ((p.reverseAux acc).map (tval x)).sum = (p.map (tval x)).sum + (acc.map (tval x)).sum := by
  rw [List.reverseAux_eq, List.map_append, List.sum_append, List.map_reverse, List.sum_reverse]

theorem tval_add (x : ℕ → ℝ) {t s : κ × List ℕ} (h : cmpE t.2 s.2 = .eq) :
    tval x (t.1 + s.1, t.2) = tval x t + tval x s := by
  simp only [tval, Exact.re_add, mono_eq_of_cmpE x t.2 s.2 0 h]
  ring

theorem tval_eq_zero (x : ℕ → ℝ) {t : κ × List ℕ} (h : Exact.isZero t.1 = true) :
    tval x t = 0 := by
  simp only [tval, Exact.isZero_sound _ h, zero_mul]

theorem sum_tval_mergeR (x : ℕ → ℝ) (p q acc : SPoly κ) :
    ((mergeR p q acc).map (tval x)).sum =
      (p.map (tval x)).sum + (q.map (tval x)).sum + (acc.map (tval x)).sum := by
  induction p, q, acc using mergeR.induct with
  | case1 acc q =>
    rw [mergeR, sum_tval_reverseAux, List.map_nil, List.sum_nil, zero_add]
  | case2 acc t p =>
    rw [mergeR, sum_tval_reverseAux]
    simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
    ring
  | case3 acc t p s q h ih =>
    rw [mergeR, h, ih]
    simp only [List.map_cons, List.sum_cons]
    ring
  | case4 acc t p s q h ih =>
    rw [mergeR, h, ih]
    simp only [List.map_cons, List.sum_cons]
    ring
  | case5 acc t p s q h ih =>
    rw [mergeR, h, ih]
    have ha := tval_add x h
    cases hz : Exact.isZero (t.1 + s.1)
    · simp only [Bool.cond_false, List.map_cons, List.sum_cons, ha]
      ring
    · have h0 := tval_eq_zero x (t := (t.1 + s.1, t.2)) hz
      rw [ha] at h0
      simp only [Bool.cond_true, List.map_cons, List.sum_cons]
      linear_combination (-1 : ℝ) * h0

/-- **Sums.** The value of `merge p q` is the sum of the values. -/
theorem run_merge (x : ℕ → ℝ) (p q : SPoly κ) :
    run Exact.re x (merge p q) = run Exact.re x p + run Exact.re x q := by
  rw [run_eq_sum, run_eq_sum, run_eq_sum, merge, List.map_reverse, List.sum_reverse,
    sum_tval_mergeR, List.map_nil, List.sum_nil, add_zero]

theorem run_neg (x : ℕ → ℝ) : ∀ p : SPoly κ, run Exact.re x (neg p) = -run Exact.re x p
  | [] => by rw [neg, List.map_nil, run_nil, neg_zero]
  | t :: p => by
    have ih := run_neg x p
    simp only [neg] at ih ⊢
    rw [List.map_cons, run_cons, run_cons, ih, Exact.re_sub, Exact.re_ofInt, Int.cast_zero]
    ring

theorem run_mulTerm (x : ℕ → ℝ) (c : κ) (e : List ℕ) : ∀ q : SPoly κ,
    run Exact.re x (mulTerm c e q) = Exact.re c * mono 1 x 0 e * run Exact.re x q
  | [] => by rw [mulTerm, List.filterMap_nil, run_nil, mul_zero]
  | s :: q => by
    have ih := run_mulTerm x c e q
    unfold mulTerm at ih ⊢
    rw [List.filterMap_cons]
    cases hz : Exact.isZero (c * s.1)
    · simp only [Bool.cond_false]
      rw [run_cons, ih, run_cons, Exact.re_mul, mono_addE]
      ring
    · have h0 := Exact.isZero_sound _ hz
      rw [Exact.re_mul] at h0
      simp only [Bool.cond_true]
      rw [ih, run_cons]
      linear_combination (-(mono 1 x 0 e * mono 1 x 0 s.2)) * h0

theorem run_prods (x : ℕ → ℝ) (q : SPoly κ) : ∀ p : SPoly κ,
    run Exact.re x (prods p q) = run Exact.re x p * run Exact.re x q
  | [] => by rw [prods, List.flatMap_nil, run_nil, zero_mul]
  | t :: p => by
    have ih := run_prods x q p
    rw [prods] at ih ⊢
    rw [List.flatMap_cons, run_append, run_mulTerm, ih, run_cons]
    ring

theorem sum_tval_push (x : ℕ → ℝ) (t : κ × List ℕ) (acc : SPoly κ) :
    ((push t acc).map (tval x)).sum = tval x t + (acc.map (tval x)).sum := by
  unfold push
  cases hz : Exact.isZero t.1
  · simp only [Bool.cond_false, List.map_cons, List.sum_cons]
  · simp only [Bool.cond_true, tval_eq_zero x hz, zero_add]

theorem sum_tval_combR (x : ℕ → ℝ) : ∀ (p : SPoly κ) (t : κ × List ℕ) (acc : SPoly κ),
    ((combR t p acc).map (tval x)).sum =
      tval x t + (p.map (tval x)).sum + (acc.map (tval x)).sum
  | [], t, acc => by rw [combR, sum_tval_push, List.map_nil, List.sum_nil, add_zero]
  | s :: p, t, acc => by
    rw [combR]
    split
    · rename_i h
      rw [sum_tval_combR x p, tval_add x h]
      simp only [List.map_cons, List.sum_cons]
      ring
    · rw [sum_tval_combR x p, sum_tval_push]
      simp only [List.map_cons, List.sum_cons]
      ring

theorem run_normal (x : ℕ → ℝ) (p : SPoly κ) : run Exact.re x (normal p) = run Exact.re x p := by
  have hp := ((List.mergeSort_perm p fun a b ↦ cmpE a.2 b.2 != .gt).map (tval x)).sum_eq
  rw [run_eq_sum, run_eq_sum, ← hp, normal]
  split
  · rename_i h
    rw [h]
  · rename_i t q h
    rw [h, List.map_reverse, List.sum_reverse, sum_tval_combR, List.map_nil, List.sum_nil,
      add_zero, List.map_cons, List.sum_cons]

/-- **Products.** The value of `mul p q` is the product of the values. -/
theorem run_mul (x : ℕ → ℝ) (q p : SPoly κ) :
    run Exact.re x (mul p q) = run Exact.re x p * run Exact.re x q := by
  rw [mul, run_normal, run_prods]

end SPoly

namespace SP

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The value at the real point `x`. -/
noncomputable def eval (x : ℕ → ℝ) (p : SP κ) : ℝ := SPoly.run Exact.re x p.terms

/-- **Evaluation commutes with the operations**, whatever the order of the terms. -/
theorem isArith_eval (x : ℕ → ℝ) : IsArith (eval (κ := κ) x) where
  map_add p q := SPoly.run_merge x p.terms q.terms
  map_sub p q := by
    change SPoly.run Exact.re x (SPoly.merge p.terms (SPoly.neg q.terms)) = _
    rw [SPoly.run_merge, SPoly.run_neg]
    rfl
  map_mul p q := SPoly.run_mul x q.terms p.terms

theorem eval_cst (x : ℕ → ℝ) (c : κ) : eval x (cst c) = Exact.re c := by
  unfold eval cst
  cases hz : Exact.isZero c
  · rw [Bool.cond_false, SPoly.run_cons, SPoly.run_nil, SPoly.mono_nil, mul_one, add_zero]
  · rw [Bool.cond_true, SPoly.run_nil, Exact.isZero_sound c hz]

theorem eval_var (x : ℕ → ℝ) (i : ℕ) : eval (κ := κ) x (var i) = x i := by
  unfold eval var
  rw [SPoly.run_cons, SPoly.run_nil, SPoly.re_one, SPoly.mono_var, one_mul, add_zero, zero_add]

end SP

/-! ### Exact maps -/

namespace GenMap

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The outputs `0, …, 6` of `Φ` (a view and a quaternion) as exact sparse polynomials in its
inputs. -/
def polys (Φ : GenMap κ) : List (SPoly κ) :=
  (List.range 7).map fun i ↦ (look (Φ.all SP.cst SP.var) (Φ.run SP.cst SP.var) i).terms

/-- The map whose output `i` is the sparse polynomial `ps i` (`0` beyond the list). -/
def ofPolys (ps : List (SPoly κ)) : GenMap κ where
  run k x i := SPoly.run k x (ps.getD i [])
  natural f hf k x := by
    funext i
    exact SPoly.map_run hf k x _

/-- **Exact maps.** At every real point, the map of the polynomials of `Φ` has the outputs
`0, …, 6` of `Φ`. -/
theorem ofPolys_polys (Φ : GenMap κ) (x : ℕ → ℝ) {i : ℕ} (hi : i < 7) :
    (ofPolys Φ.polys).run Exact.re x i = Φ.run Exact.re x i := by
  have hl : i < Φ.polys.length := by simpa [polys] using hi
  have h := congrFun (Φ.natural (SP.eval x) (SP.isArith_eval x) SP.cst SP.var) i
  simp only [Function.comp_apply] at h
  change SPoly.run Exact.re x (Φ.polys.getD i []) = _
  rw [List.getD_eq_getElem _ _ hl]
  simp only [polys, List.getElem_map, List.getElem_range, look_all]
  change SP.eval x (Φ.run SP.cst SP.var i) = _
  rw [h]
  congr 1
  · funext c
    exact SP.eval_cst x c
  · funext j
    exact SP.eval_var x j

/-- The exact map represents the poses of `Φ`. -/
theorem sim_ofPolys (Φ : GenMap κ) (x : ℕ → ℝ) :
    PoseSim ((ofPolys Φ.polys).run Exact.re x) (Φ.run Exact.re x) := by
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_, ?_⟩
  · funext i
    rw [Pi.smul_apply, one_smul]
    exact (ofPolys_polys Φ x (i := (i : ℕ)) (by have := i.isLt; omega)).symm
  · funext i
    rw [Pi.smul_apply, one_smul]
    exact (ofPolys_polys Φ x (i := (i : ℕ) + 3) (by have := i.isLt; omega)).symm

end GenMap

end Nieuwland.Check
