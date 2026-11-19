import Modules.Check.Polynomial.SparseTerm
import Modules.Check.Sign.VertDom

/-!
# Box checks of sparse terms in rupert's order

rupert's exact check of a tuple's polynomial on a box (`nonneg_exact_rec`,
`code/src/proof/regional.rs`) runs, on each box of its bisection: the centred range; then the
vertex where the centred linear part is smallest, with the exact value there and vertex, then
monomial, dominance of the vertex frame; then a split of the widest coordinate, the last of equal
ones, at its midpoint. Each box's frame comes from the polynomial itself. Here the polynomial is a
tuple's weighted sparse terms (`WTerms`: integer weights and the coordinates of the quotients, in
the variables `X = D x` of the leaf), and every frame is computed from them by Horner's rule
(`valsAt`, as `Pull.valS`), so that no frame is derived from another one:

* the box `(C, H)` over `2^k` (the points `X = (C + H y) / 2^k`, `y ∈ [-1, 1]^n`) halves into
  the boxes `halfC`, `halfH` over `2^(k + 1)`; its terms are scaled to integers
  (`SPoly.scaleD`: `2^(k M) q(X / 2^k)` for degrees at most `M`), so its numerals are those of
  `2^(k M)` times the tuple's polynomial;
* every frame's numerals have the digit size of its own bound (`normsAt`, `Lay.digitsFor`), so
  they fit by construction and grow only as far as the bisection goes;
* `boxT`: the centred form (`Lay.boxOk` without dominance) passes, or the vertex frame
  (`vertC`, `vertH`: `X = (C + σ H - 2 σ H u) / 2^k`, `u ∈ [0, 1]^n`) at the vertex
  `Lay.lowSign` passes `Lay.vdTest` (dominance at bounded precision with the exact vertex value);
* `origT`: the vertex frame at the origin of the coordinates passes `Lay.vdTest`, on a box that
  has the origin as a vertex (`origOn`: `C = H` or `C = -H` in every coordinate of positive
  degree). This is the origin vertex of rupert's `nonneg_on_fbox_exact`: below an exact frame at a
  pose with margin zero the terms vanish there, and `Lay.lowSign` need not find that vertex;
* `boxRec`: `boxT` (unless the caller has tested the box), then `origT`, else a split
  (`Lay.pickW`), at most `fuel` levels deep;
* `topT`: the tests of the leaf's own box on numerals given (shared with the other tuples);
* `boxRecP`: `boxRec` as compiled code runs it, with the engine's masks, a beat line per box
  (`box`: tuple, boxes tested, level) and the count of boxes tested (`boxRecP_fst`).

Soundness (`boxRec_sound`, `topT_sound`; the vertex test is sound at any vertex, `vertT_sound`,
so `origT_sound` uses nothing about the origin): the combination `∑_c β_c ∑ w q_c` has the sign at
every point of the box.
-/

open Finset

namespace Nieuwland.Check

open DPoly

namespace SPoly

/-! ### Scaled polynomials -/

/-- The largest total degree of the terms of `q`. -/
def degT (q : SPoly ℤ) : ℕ := (q.map fun t ↦ t.2.sum).foldr max 0

theorem le_degT {q : SPoly ℤ} {t : ℤ × List ℕ} (ht : t ∈ q) : t.2.sum ≤ degT q :=
  le_foldr_max (List.mem_map_of_mem ht)

/-- Each coefficient times `2^(k (M - |e|))`: `2^(k M) q(X / 2^k)` where every total degree is at
most `M` (`run_scaleD`). -/
def scaleD (k M : ℕ) (q : SPoly ℤ) : SPoly ℤ := q.map fun t ↦ (t.1 * 2 ^ (k * (M - t.2.sum)), t.2)

theorem run_map_fst {α : Type*} [Add α] [Mul α] (k : ℤ → α) (x : ℕ → α)
    (f : ℤ × List ℕ → ℤ) (hf : ∀ t, k (f t) = k t.1) :
    ∀ q : SPoly ℤ, run k x (q.map fun t ↦ (f t, t.2)) = run k x q
  | [] => rfl
  | t :: q => by simp only [List.map_cons, run, hf t, run_map_fst k x f hf q]

theorem shapeS_scaleD (n k M : ℕ) (q : SPoly ℤ) : shapeS n (scaleD k M q) = shapeS n q := by
  unfold shapeS scaleD
  exact congrArg _ (run_map_fst _ _ (fun t ↦ t.1 * 2 ^ (k * (M - t.2.sum))) (fun _ ↦ rfl) q)

theorem lenOk_scaleD (n k M : ℕ) (q : SPoly ℤ) : lenOk n (scaleD k M q) = lenOk n q := by
  unfold lenOk scaleD
  rw [List.all_map]
  rfl

theorem mono_div (x : ℕ → ℝ) {a : ℝ} (ha : a ≠ 0) : ∀ (i : ℕ) (e : List ℕ),
    mono (1 : ℝ) (fun j ↦ x j / a) i e = mono 1 x i e / a ^ e.sum
  | i, [] => by simp [mono_nilR]
  | i, d :: e => by
    rw [mono_consR, mono_consR, mono_div x ha (i + 1) e, List.sum_cons, pow_add, div_pow]
    field_simp

/-- **Scaling.** `scaleD k M q` is `2^(k M) q(X / 2^k)` where every total degree is at most
`M`. -/
theorem run_scaleD (X : ℕ → ℝ) (k M : ℕ) {q : SPoly ℤ} (hq : ∀ t ∈ q, t.2.sum ≤ M) :
    run (fun c : ℤ ↦ (c : ℝ)) X (scaleD k M q) =
      2 ^ (k * M) * run (fun c : ℤ ↦ (c : ℝ)) (fun j ↦ X j / 2 ^ k) q := by
  rw [run_int_eq_sum, run_int_eq_sum, scaleD, List.map_map, Lay.listSum_mul]
  congr 1
  refine List.map_congr_left fun t ht ↦ ?_
  simp only [Function.comp_apply]
  rw [mono_div X (by positivity) 0 t.2]
  have hM := hq t ht
  have hp : (2 : ℝ) ^ (k * M) = 2 ^ (k * (M - t.2.sum)) * (2 ^ k) ^ t.2.sum := by
    rw [← pow_mul, ← pow_add, ← Nat.mul_add, Nat.sub_add_cancel hM]
  rw [hp]
  push_cast
  field_simp

end SPoly

namespace Pull

/-! ### Weighted terms -/

/-- A tuple's terms as integer weights and the coordinates of their quotients, in the variables
`X = D x` of the leaf's frame. -/
abbrev WTerms := List (ℤ × List (SPoly ℤ))

namespace WTerms

/-- The terms of the box over `2^k`: each coordinate scaled by `SPoly.scaleD k M`. -/
def scale (k M : ℕ) (wt : WTerms) : WTerms := wt.map fun x ↦ (x.1, x.2.map (SPoly.scaleD k M))

/-- The largest total degree of the coordinates. -/
def deg (wt : WTerms) : ℕ := (wt.map fun x ↦ (x.2.map SPoly.degT).foldr max 0).foldr max 0

theorem le_deg {wt : WTerms} {x : ℤ × List (SPoly ℤ)} (hx : x ∈ wt) (c : ℕ)
    {t : ℤ × List ℕ} (ht : t ∈ x.2.getD c []) : t.2.sum ≤ wt.deg := by
  rcases getD_mem_or x.2 c [] with h | h
  · exact (SPoly.le_degT ht).trans ((le_foldr_max (List.mem_map_of_mem h)).trans
      (le_foldr_max (List.mem_map_of_mem hx)))
  · rw [h] at ht
    cases ht

theorem getD_scale (k M : ℕ) (x : ℤ × List (SPoly ℤ)) (c : ℕ) :
    (x.2.map (SPoly.scaleD k M)).getD c [] = SPoly.scaleD k M (x.2.getD c []) :=
  getD_map_of_eq (f := SPoly.scaleD k M) (z := []) (z' := []) rfl x.2 c

/-- Coordinate `c` of the weighted sum at a real point (in proofs). -/
noncomputable def valAt (c : ℕ) (X : ℕ → ℝ) : WTerms → ℝ
  | [] => 0
  | x :: wt => (x.1 : ℝ) * SPoly.run (fun a : ℤ ↦ (a : ℝ)) X (x.2.getD c []) + valAt c X wt

/-- Coordinate `c` of the weighted sum at the packing point `Cᵢ + Hᵢ 2^(B stride)` of the shape
`shape` and the digit size `B`, by Horner's rule (`evalInt_sumExprW`). -/
def valsAt (shape : List ℕ) (C H : List ℤ) (B c : ℕ) : WTerms → ℤ
  | [] => 0
  | x :: wt => x.1 * SPoly.evalPk (mulPt shape C H B) (SPoly.fuelOf (x.2.getD c [])) 0
      (x.2.getD c []) + valsAt shape C H B c wt

/-- A bound on the absolute coefficient sums of coordinate `c` of the weighted sum on the box
inputs with bounds `bs`. -/
def normW (bs : List ℕ) (c : ℕ) : WTerms → ℕ
  | [] => 0
  | x :: wt => x.1.natAbs * SPoly.normS bs (x.2.getD c []) + normW bs c wt

/-- Coordinate `c` of the weighted sum as an expression (in proofs). -/
def sumExprW (c : ℕ) : WTerms → Expr
  | [] => .const 0
  | x :: wt => .const x.1 * SPoly.qE (x.2.getD c []) + sumExprW c wt

/-- Every coordinate fits the shape and is a polynomial in the first `n` variables. -/
def Fit (n : ℕ) (shape : List ℕ) (wt : WTerms) : Prop :=
  ∀ x ∈ wt, ∀ c, ShapeLE (SPoly.shapeS n (x.2.getD c [])) shape ∧
    SPoly.lenOk n (x.2.getD c []) = true

theorem Fit.scale {n : ℕ} {shape : List ℕ} {wt : WTerms} (h : Fit n shape wt) (k M : ℕ) :
    Fit n shape (WTerms.scale k M wt) := by
  intro x hx c
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  rw [getD_scale, SPoly.shapeS_scaleD, SPoly.lenOk_scaleD]
  exact h y hy c

theorem shape_sumExprW {n : ℕ} {shape : List ℕ} (c : ℕ) : ∀ {wt : WTerms}, Fit n shape wt →
    ShapeLE ((sumExprW c wt).shape (boxShapes n)) shape
  | [], _ => trivial
  | x :: wt, h => by
    refine shapeLE_zipPad_max ?_ (shape_sumExprW c fun y hy ↦ h y (List.mem_cons_of_mem _ hy))
    change ShapeLE ((SPoly.qE (x.2.getD c [])).shape (boxShapes n)) shape
    rw [SPoly.shape_qE]
    exact (h x List.mem_cons_self c).1

theorem normBound_sumExprW (bs : List ℕ) (c : ℕ) :
    ∀ wt : WTerms, (sumExprW c wt).normBound bs ≤ normW bs c wt
  | [] => Nat.le_refl 0
  | x :: wt => by
    change x.1.natAbs * (SPoly.qE (x.2.getD c [])).normBound bs +
        (sumExprW c wt).normBound bs ≤ x.1.natAbs * SPoly.normS bs (x.2.getD c []) + normW bs c wt
    rw [SPoly.normBound_qE]
    exact Nat.add_le_add_left (normBound_sumExprW bs c wt) _

theorem evalPk_eq_run (shape : List ℕ) (C H : List ℤ) (B : ℕ) (q : SPoly ℤ) :
    SPoly.evalPk (mulPt shape C H B) (SPoly.fuelOf q) 0 q =
      SPoly.run (fun c : ℤ ↦ c) (Frame.pointW shape C H B) q := by
  rw [SPoly.run_id_eq_sum,
    SPoly.evalPk_eq (mulPt_eq shape C H B) _ 0 _ fun t ht ↦ SPoly.le_fuelOf ht]

theorem evalInt_sumExprW {n : ℕ} {shape : List ℕ} {C H : List ℤ} {D : ℤ} {B c : ℕ} :
    ∀ {wt : WTerms}, Fit n shape wt →
      (sumExprW c wt).evalInt (boxPacked n shape B C H D) = valsAt shape C H B c wt
  | [], _ => rfl
  | x :: wt, h => by
    change x.1 * (SPoly.qE (x.2.getD c [])).evalInt (boxPacked n shape B C H D) +
        (sumExprW c wt).evalInt (boxPacked n shape B C H D) = _
    rw [evalInt_sumExprW fun y hy ↦ h y (List.mem_cons_of_mem _ hy), SPoly.evalInt_qE,
      SPoly.run_congr_lenOk (fun c : ℤ ↦ c) (x' := Frame.pointW shape C H B) (fun i hi ↦ ?_)
        (h x List.mem_cons_self c).2, valsAt, evalPk_eq_run]
    simp only [boxPacked, getD_range_map_append, hi, ↓reduceIte, Frame.pointW]

theorem eval_sumExprW (y : ℕ → ℝ) (c : ℕ) :
    ∀ wt : WTerms, (sumExprW c wt).eval y = valAt c y wt
  | [] => by simp [sumExprW, valAt]
  | x :: wt => by
    rw [sumExprW, Expr.eval_add, Expr.eval_mul, Expr.eval_const, SPoly.eval_qE,
      eval_sumExprW y c wt, valAt]

/-- **The numerals of weighted terms on a frame**: coordinate `c` of the weighted sum at the
packing point of digit size `B`, biased, satisfies the invariant of the engine where its bound
fits, and its slot polynomial is the weighted sum at the box inputs. -/
theorem nums_spec {n : ℕ} {shape : List ℕ} {C H : List ℤ} {D : ℤ} {B c : ℕ} {wt : WTerms}
    (hB : 0 < B) (hsh : shape.length ≤ n) (hfit : Fit n shape wt)
    (hnb : normW (boxNorms n C H D) c wt < 2 ^ (B - 1)) :
    Lay.Inv B shape ((valsAt shape C H B c wt + offset n shape B).toNat) ∧
      ∀ y : ℕ → ℝ, Lay.pv shape (Lay.cf B ((valsAt shape C H B c wt + offset n shape B).toNat)) y =
        valAt c (fun i ↦ boxEnv n C H D (fun i ↦ y i) i) wt := by
  obtain ⟨hf, hnorm, hv⟩ := box_packing_lt (sumExprW c wt) (shape_sumExprW c hfit) C H D
    (normBound_sumExprW (boxNorms n C H D) c wt) B
  rw [← evalInt_sumExprW hfit, hv]
  obtain ⟨hinv, hpv⟩ := Lay.inv_biased hsh hB hf hnorm hnb
  refine ⟨hinv, fun y ↦ ?_⟩
  rw [hpv, Expr.eval_toDPoly, eval_sumExprW]
  simp only [eval_boxInputs]

/-- `valAt` reads only the first `n` coordinates. -/
theorem valAt_congr {n : ℕ} {shape : List ℕ} {c : ℕ} {X X' : ℕ → ℝ} (h : ∀ i < n, X i = X' i) :
    ∀ {wt : WTerms}, Fit n shape wt → valAt c X wt = valAt c X' wt
  | [], _ => rfl
  | x :: wt, hf => by
    rw [valAt, valAt, SPoly.run_congr_lenOk _ h (hf x List.mem_cons_self c).2,
      valAt_congr h fun y hy ↦ hf y (List.mem_cons_of_mem _ hy)]

/-- The weighted sum of the scaled terms is `2^(k M)` times the sum at `X / 2^k`. -/
theorem valAt_scale (X : ℕ → ℝ) (k M c : ℕ) : ∀ {wt : WTerms},
    (∀ x ∈ wt, ∀ t ∈ x.2.getD c [], t.2.sum ≤ M) →
      valAt c X (WTerms.scale k M wt) = 2 ^ (k * M) * valAt c (fun j ↦ X j / 2 ^ k) wt
  | [], _ => by simp [scale, valAt]
  | x :: wt, h => by
    change (x.1 : ℝ) * SPoly.run (fun a : ℤ ↦ (a : ℝ)) X ((x.2.map (SPoly.scaleD k M)).getD c []) +
        valAt c X (WTerms.scale k M wt) = _
    rw [getD_scale, SPoly.run_scaleD X k M (h x List.mem_cons_self),
      valAt_scale X k M c fun y hy ↦ h y (List.mem_cons_of_mem _ hy), valAt]
    ring

end WTerms

open WTerms

/-! ### Frames -/

/-- The half of the box `(C, H)` along `i` on the side `s = ±1`, over twice the denominator:
the centres. -/
def halfC (n : ℕ) (C H : List ℤ) (i : ℕ) (s : ℤ) : List ℤ :=
  (List.range n).map fun j ↦ 2 * C.getD j 0 + bif j == i then s * H.getD j 0 else 0

/-- The half-widths of the halves along `i`. -/
def halfH (n : ℕ) (H : List ℤ) (i : ℕ) : List ℤ :=
  (List.range n).map fun j ↦ bif j == i then H.getD j 0 else 2 * H.getD j 0

/-- The vertex `C + σ H` of the box `(C, H)`. -/
def vertC (n : ℕ) (C H : List ℤ) (σ : ℕ → ℤ) : List ℤ :=
  (List.range n).map fun j ↦ C.getD j 0 + σ j * H.getD j 0

/-- The edges `-2 σ H` from the vertex `C + σ H` into the box. -/
def vertH (n : ℕ) (H : List ℤ) (σ : ℕ → ℤ) : List ℤ :=
  (List.range n).map fun j ↦ -2 * σ j * H.getD j 0

/-- The point `(C + H y) / 2^k` of the box `(C, H)` over `2^k` (in proofs). -/
noncomputable def envK (C H : List ℤ) (k : ℕ) (y : ℕ → ℝ) (i : ℕ) : ℝ :=
  ((C.getD i 0 : ℝ) + (H.getD i 0 : ℝ) * y i) / 2 ^ k

/-- Each point of the box is a point of the half on its side. -/
theorem envK_half {n : ℕ} (C H : List ℤ) (k i : ℕ) (s : ℤ) (y : ℕ → ℝ) :
    ∀ j < n, envK (halfC n C H i s) (halfH n H i) (k + 1)
      (Function.update y i (2 * y i - s)) j = envK C H k y j := by
  intro j hj
  simp only [envK, halfC, halfH, Box.getD_range_map _ _ _ hj]
  by_cases hji : j = i
  · subst hji
    simp only [beq_self_eq_true, Bool.cond_true, Function.update_self, pow_succ]
    push_cast
    field_simp
    ring
  · have : (j == i) = false := by simpa using hji
    simp only [this, Bool.cond_false, Function.update_of_ne hji, pow_succ]
    push_cast
    field_simp
    ring

theorem abs_half_le {y : ℝ} {s : ℤ} (hs : s = 1 ∨ s = -1) (hy : |y| ≤ 1)
    (hside : 0 ≤ s * y) : |2 * y - s| ≤ 1 := by
  rw [abs_le] at hy ⊢
  rcases hs with rfl | rfl <;> push_cast at hside ⊢ <;> constructor <;> linarith

/-- Each point of the box is a point of the vertex frame. -/
theorem envK_vert {n : ℕ} (C H : List ℤ) (k : ℕ) {σ : ℕ → ℤ} (hσ : ∀ i, σ i = 1 ∨ σ i = -1)
    (y : ℕ → ℝ) : ∀ j < n, envK (vertC n C H σ) (vertH n H σ) k
      (fun i ↦ (1 - σ i * y i) / 2) j = envK C H k y j := by
  intro j hj
  simp only [envK, vertC, vertH, Box.getD_range_map _ _ _ hj]
  have h2 : (σ j : ℝ) * σ j = 1 := by rcases hσ j with h | h <;> rw [h] <;> norm_num
  push_cast
  congr 1
  linear_combination ((H.getD j 0 : ℝ) * y j) * h2

theorem vert_mem {σ : ℕ → ℤ} (hσ : ∀ i, σ i = 1 ∨ σ i = -1) {y : ℕ → ℝ}
    (hy : ∀ i, |y i| ≤ 1) (i : ℕ) : 0 ≤ (1 - σ i * y i) / 2 ∧ (1 - σ i * y i) / 2 ≤ 1 := by
  have := abs_le.mp (hy i)
  rcases hσ i with h | h <;> rw [h] <;> push_cast <;> constructor <;> linarith

/-! ### The tests of a box -/

section Field

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

variable (κ) in
/-- The numerals of the coordinates of weighted terms on the frame `(C, H)` at digit size `B`. -/
def numsAt (n : ℕ) (shape : List ℕ) (C H : List ℤ) (B : ℕ) (w : WTerms) : List ℕ :=
  (List.range (ExactBasis.dim κ)).map fun c ↦ (valsAt shape C H B c w + offset n shape B).toNat

variable (κ) in
/-- The largest bound of the coordinates of weighted terms on the frame `(C, H)`: their numerals
fit the digit size `Lay.digitsFor (normsAt κ n C H w) h` for every `h` (`normW_lt_digitsFor`). -/
def normsAt (n : ℕ) (C H : List ℤ) (w : WTerms) : ℕ :=
  ((List.range (ExactBasis.dim κ)).map fun c ↦ normW (boxNorms n C H 0) c w).foldr max 0

/-- The largest absolute coefficient sum of numerals (the bound of `Lay.vdTest`). -/
def lmaxOf (B : ℕ) (shape : List ℕ) (Vs : List ℕ) : ℕ := (Vs.map (Lay.l1N B shape)).foldr max 0

variable (κ) in
/-- **The vertex test** of the frame `(C, H)` at the vertex `σ`, with the terms `w`: the vertex
frame's numerals at the digit size of their bound (`normsAt`), and `Lay.vdTest` on them
(`vertT_sound`). -/
def vertT (n : ℕ) (shape : List ℕ) (strict : Bool) (w : WTerms) (C H : List ℤ) (σ : ℕ → ℤ) :
    Bool :=
  let vC := vertC n C H σ
  let vH := vertH n H σ
  let B := Lay.digitsFor (normsAt κ n vC vH w) 0
  let Vs := numsAt κ n shape vC vH B w
  Lay.vdTest κ n shape B strict (lmaxOf B shape Vs) Vs

variable (κ) in
/-- **The tests of a box with its numerals `Ns` of digit size `B` given** (`topT_sound`): the
centred form without dominance, then the vertex test at the vertex where the centred linear part is
smallest. -/
def topT (n : ℕ) (shape : List ℕ) (B : ℕ) (strict : Bool) (w : WTerms) (C H : List ℤ)
    (Ns : List ℕ) : Bool :=
  Lay.boxOk κ n shape B strict false Ns || vertT κ n shape strict w C H (Lay.lowSign κ shape B Ns)

variable (κ) in
/-- **The tests of the box `(C, H)` over `2^k`** (`boxT_sound`): `topT` on the scaled terms'
numerals at the digit size of their bound with room for the approximate centred form
(`Lay.apxBits`). -/
def boxT (n : ℕ) (shape : List ℕ) (strict : Bool) (M : ℕ) (wt : WTerms) (C H : List ℤ) (k : ℕ) :
    Bool :=
  let w := WTerms.scale k M wt
  let B := Lay.digitsFor (normsAt κ n C H w) (Lay.apxBits κ)
  topT κ n shape B strict w C H (numsAt κ n shape C H B w)

/-- The vertex at the origin of the coordinates, for a box `(C, H)` that has it as a vertex: the
lower end (`-1`) where `C = H`, else the upper end. -/
def origV (C H : List ℤ) (i : ℕ) : ℤ := bif C.getD i 0 == H.getD i 0 then -1 else 1

theorem origV_cases (C H : List ℤ) (i : ℕ) : origV C H i = 1 ∨ origV C H i = -1 := by
  unfold origV
  cases C.getD i 0 == H.getD i 0 <;> simp

/-- Whether the box `(C, H)` has the origin of the coordinates as a vertex: in every coordinate of
positive degree one end is `0` (`C = H` or `C = -H`). -/
def origOn (n : ℕ) (shape : List ℕ) (C H : List ℤ) : Bool :=
  (List.range n).all fun i ↦
    Lay.deg shape i == 0 || C.getD i 0 == H.getD i 0 || C.getD i 0 + H.getD i 0 == 0

variable (κ) in
/-- **The vertex test at the origin** of the box `(C, H)` over `2^k`, where the box has it as a
vertex (`origT_sound`): the origin vertex of `nonneg_on_fbox_exact` in rupert's bound contract
(`code/src/proof/regional.rs`). An exact frame at a pose with margin zero puts the zero of the
terms there, and the centred linear part need not decrease towards it. -/
def origT (n : ℕ) (shape : List ℕ) (strict : Bool) (M : ℕ) (wt : WTerms) (C H : List ℤ)
    (k : ℕ) : Bool :=
  origOn n shape C H && vertT κ n shape strict (WTerms.scale k M wt) C H (origV C H)

variable (κ) in
/-- The tests of one box of `boxRec` (`boxS_sound`): `boxT` (if `test`), then the vertex test at
the origin. -/
def boxS (n : ℕ) (shape : List ℕ) (strict : Bool) (M : ℕ) (wt : WTerms) (test : Bool)
    (C H : List ℤ) (k : ℕ) : Bool :=
  (test && boxT κ n shape strict M wt C H k) || origT κ n shape strict M wt C H k

variable (κ) in
/-- **rupert's bisection** of the box `(C, H)` over `2^k` (`boxRec_sound`): the box's tests
(`boxS`), else a split along the coordinate `Lay.pickW true` of the widths `W` (none where the
terms have degree `0` in it), at most `fuel` levels deep. -/
def boxRec (n : ℕ) (shape : List ℕ) (strict : Bool) (M : ℕ) (wt : WTerms) :
    ℕ → Bool → List ℤ → List ℤ → ℕ → List ℤ → Bool
  | 0, test, C, H, k, _ => boxS κ n shape strict M wt test C H k
  | d + 1, test, C, H, k, W =>
    boxS κ n shape strict M wt test C H k ||
      let i := Lay.pickW true n W
      let W' := Lay.halveW W i
      bif Lay.deg shape i == 0 then boxRec n shape strict M wt d false C H k W'
      else boxRec n shape strict M wt d true (halfC n C H i (-1)) (halfH n H i) (k + 1) W' &&
        boxRec n shape strict M wt d true (halfC n C H i 1) (halfH n H i) (k + 1) W'

/-! #### Compiled copies -/

variable (κ) in
/-- `vertT` with the absolute sums from the ones of the digit size (`vertTM_eq`). -/
def vertTM (n : ℕ) (shape : List ℕ) (strict : Bool) (w : WTerms) (C H : List ℤ) (σ : ℕ → ℤ) :
    Bool :=
  let vC := vertC n C H σ
  let vH := vertH n H σ
  let B := Lay.digitsFor (normsAt κ n vC vH w) 0
  let Vs := numsAt κ n shape vC vH B w
  Lay.vdTest κ n shape B strict ((Vs.map (Lay.l1O B (Lay.onesN B shape))).foldr max 0) Vs

theorem vertTM_eq (n : ℕ) (shape : List ℕ) (strict : Bool) (w : WTerms) (C H : List ℤ)
    (σ : ℕ → ℤ) : vertTM κ n shape strict w C H σ = vertT κ n shape strict w C H σ := by
  have h : ∀ B, Lay.l1O B (Lay.onesN B shape) = Lay.l1N B shape := fun B ↦
    funext (Lay.l1O_onesN B shape)
  simp only [vertTM, vertT, lmaxOf, h]

variable (κ) in
/-- `topT` with the engine's masks `m` and the absolute sums `ls` of the numerals given
(`topTM_eq`). -/
def topTM (m : Lay.Masks) (n : ℕ) (shape : List ℕ) (B : ℕ) (strict : Bool) (w : WTerms)
    (C H : List ℤ) (ls Ns : List ℕ) : Bool :=
  Lay.boxOkM κ m n shape B strict false ls Ns ||
    vertTM κ n shape strict w C H (Lay.lowSign κ shape B Ns)

theorem topTM_eq (n : ℕ) (shape : List ℕ) (B : ℕ) (strict : Bool) (w : WTerms) (C H : List ℤ)
    (Ns : List ℕ) :
    topTM κ (Lay.masks B shape) n shape B strict w C H (Ns.map (Lay.l1O B (Lay.onesN B shape))) Ns =
      topT κ n shape B strict w C H Ns := by
  simp only [topTM, topT, Lay.boxOkM_masks, vertTM_eq]

variable (κ) in
/-- `boxT` with the masks of its digit size (`boxTM_eq`). -/
def boxTM (n : ℕ) (shape : List ℕ) (strict : Bool) (M : ℕ) (wt : WTerms) (C H : List ℤ)
    (k : ℕ) : Bool :=
  let w := WTerms.scale k M wt
  let B := Lay.digitsFor (normsAt κ n C H w) (Lay.apxBits κ)
  let m := Lay.masks B shape
  let Ns := numsAt κ n shape C H B w
  topTM κ m n shape B strict w C H (Ns.map (Lay.l1O B m.ones)) Ns

theorem boxTM_eq (n : ℕ) (shape : List ℕ) (strict : Bool) (M : ℕ) (wt : WTerms) (C H : List ℤ)
    (k : ℕ) : boxTM κ n shape strict M wt C H k = boxT κ n shape strict M wt C H k := by
  simp only [boxTM, boxT, Lay.masks_ones, topTM_eq]

variable (κ) in
/-- One box's tests in `boxRecP`: `boxTM` (if `test`) with a beat line (`box`: the tuple `i` of
`nτ`, the boxes tested, the box's level, the result), and the count of boxes tested. -/
def boxStepP (i nτ n : ℕ) (shape : List ℕ) (strict : Bool) (M : ℕ) (wt : WTerms) (lvl : ℕ)
    (test : Bool) (C H : List ℤ) (k cnt : ℕ) : Bool × ℕ :=
  bif test then
    (beat "box" (fun r ↦ s!" i={i} n={nτ} boxes={cnt + 1} depth={lvl} ok={r}")
      (boxTM κ n shape strict M wt C H k || origT κ n shape strict M wt C H k), cnt + 1)
  else (origT κ n shape strict M wt C H k, cnt)

theorem boxStepP_fst (i nτ n : ℕ) (shape : List ℕ) (strict : Bool) (M : ℕ) (wt : WTerms)
    (lvl : ℕ) (test : Bool) (C H : List ℤ) (k cnt : ℕ) :
    (boxStepP κ i nτ n shape strict M wt lvl test C H k cnt).1 =
      boxS κ n shape strict M wt test C H k := by
  cases test <;> simp [boxStepP, boxS, beat_eq, boxTM_eq]

variable (κ) in
/-- `boxRec` as compiled code runs it (`boxRecP_fst`): the boxes' tests by `boxStepP`, which
counts them (the second component), at the level `lvl` of the bisection. -/
def boxRecP (i nτ n : ℕ) (shape : List ℕ) (strict : Bool) (M : ℕ) (wt : WTerms) :
    ℕ → ℕ → Bool → List ℤ → List ℤ → ℕ → List ℤ → ℕ → Bool × ℕ
  | 0, lvl, test, C, H, k, _, cnt => boxStepP κ i nτ n shape strict M wt lvl test C H k cnt
  | d + 1, lvl, test, C, H, k, W, cnt =>
    let r := boxStepP κ i nτ n shape strict M wt lvl test C H k cnt
    bif r.1 then r
    else
      let j := Lay.pickW true n W
      let W' := Lay.halveW W j
      bif Lay.deg shape j == 0 then boxRecP i nτ n shape strict M wt d lvl false C H k W' r.2
      else
        let lo := boxRecP i nτ n shape strict M wt d (lvl + 1) true (halfC n C H j (-1))
          (halfH n H j) (k + 1) W' r.2
        bif lo.1 then
          boxRecP i nτ n shape strict M wt d (lvl + 1) true (halfC n C H j 1) (halfH n H j) (k + 1)
            W' lo.2
        else lo

theorem boxRecP_fst (i nτ n : ℕ) (shape : List ℕ) (strict : Bool) (M : ℕ) (wt : WTerms)
    (fuel : ℕ) : ∀ (lvl : ℕ) (test : Bool) (C H : List ℤ) (k : ℕ) (W : List ℤ) (cnt : ℕ),
      (boxRecP κ i nτ n shape strict M wt fuel lvl test C H k W cnt).1 =
        boxRec κ n shape strict M wt fuel test C H k W := by
  induction fuel with
  | zero =>
    intro lvl test C H k W cnt
    rw [boxRecP, boxRec, boxStepP_fst]
  | succ d ih =>
    intro lvl test C H k W cnt
    have hc : ∀ (c : Bool) (a b : Bool × ℕ), (bif c then a else b).1 = bif c then a.1 else b.1 :=
      fun c a b ↦ by cases c <;> rfl
    have ha : ∀ a b : Bool, (bif a then b else a) = (a && b) := fun a b ↦ by cases a <;> rfl
    simp only [boxRecP, boxRec, hc, ih, boxStepP_fst, ha]
    cases boxS κ n shape strict M wt test C H k <;> rfl

/-! #### Soundness -/

/-- The combination of the weighted terms at a real point (in proofs). -/
noncomputable def comb (wt : WTerms) (X : ℕ → ℝ) : ℝ :=
  ∑ c ∈ range (ExactBasis.dim κ), ExactBasis.basis κ c * valAt c X wt

theorem normW_lt_digitsFor {n : ℕ} {C H : List ℤ} {w : WTerms} {c : ℕ}
    (hc : c < ExactBasis.dim κ) (h : ℕ) :
    normW (boxNorms n C H 0) c w < 2 ^ (Lay.digitsFor (normsAt κ n C H w) h - 1) :=
  (le_foldr_max (List.mem_map_of_mem (f := fun c ↦ normW (boxNorms n C H 0) c w)
    (List.mem_range.mpr hc))).trans_lt (Lay.le_digitsFor _ _)

theorem numsAt_spec {n : ℕ} {shape : List ℕ} {C H : List ℤ} {B : ℕ} {w : WTerms} (hB : 0 < B)
    (hsh : shape.length ≤ n) (hfit : Fit n shape w)
    (hnb : ∀ c < ExactBasis.dim κ, normW (boxNorms n C H 0) c w < 2 ^ (B - 1)) :
    ∀ c < ExactBasis.dim κ, Lay.Inv B shape ((numsAt κ n shape C H B w).getD c 0) ∧
      ∀ y : ℕ → ℝ, Lay.pv shape (Lay.cf B ((numsAt κ n shape C H B w).getD c 0)) y =
        valAt c (fun i ↦ (C.getD i 0 : ℝ) + H.getD i 0 * y i) w := by
  intro c hc
  obtain ⟨hinv, hpv⟩ := nums_spec (D := 0) hB hsh hfit (hnb c hc)
  rw [numsAt, Box.getD_range_map _ _ _ hc]
  refine ⟨hinv, fun y ↦ ?_⟩
  rw [hpv y]
  exact valAt_congr (fun i hi ↦ by simp [boxEnv, hi]) hfit

theorem vertT_sound {n : ℕ} {shape : List ℕ} {strict : Bool} {w : WTerms}
    {C H : List ℤ} {σ : ℕ → ℤ} (hsh : shape.length ≤ n) (hfit : Fit n shape w)
    (hσ : ∀ i, σ i = 1 ∨ σ i = -1) (h : vertT κ n shape strict w C H σ = true) {y : ℕ → ℝ}
    (hy : ∀ i, |y i| ≤ 1) :
    Sign strict (comb (κ := κ) w fun i ↦ (C.getD i 0 : ℝ) + H.getD i 0 * y i) := by
  simp only [vertT] at h
  have hspec := numsAt_spec (κ := κ) (C := vertC n C H σ) (H := vertH n H σ)
    (B := Lay.digitsFor (normsAt κ n (vertC n C H σ) (vertH n H σ) w) 0) (Lay.digitsFor_pos _ _)
    hsh hfit fun c hc ↦ normW_lt_digitsFor hc 0
  have hs := Lay.vdTest_sound hsh (fun c hc ↦ (hspec c hc).1.1) h (vert_mem hσ hy)
  refine (congrArg (Sign strict) (sum_congr rfl fun c hc ↦ ?_)).mp hs
  rw [(hspec c (mem_range.mp hc)).2]
  congr 1
  have e := envK_vert (n := n) C H 0 hσ y
  simp only [envK, pow_zero, div_one] at e
  exact valAt_congr e hfit

theorem topT_sound {n : ℕ} {shape : List ℕ} {B : ℕ} {strict : Bool} {w : WTerms}
    {C H : List ℤ} {Ns : List ℕ} (hB : 0 < B) (hsh : shape.length ≤ n) (hfit : Fit n shape w)
    (hlen : Ns.length = ExactBasis.dim κ)
    (hNs : ∀ c < ExactBasis.dim κ, Lay.Inv B shape (Ns.getD c 0) ∧
      ∀ y : ℕ → ℝ, Lay.pv shape (Lay.cf B (Ns.getD c 0)) y =
        valAt c (fun i ↦ (C.getD i 0 : ℝ) + H.getD i 0 * y i) w)
    (h : topT κ n shape B strict w C H Ns = true) {y : ℕ → ℝ} (hy : ∀ i, |y i| ≤ 1) :
    Sign strict (comb (κ := κ) w fun i ↦ (C.getD i 0 : ℝ) + H.getD i 0 * y i) := by
  simp only [topT, Bool.or_eq_true] at h
  rcases h with h | h
  · have hinv : ∀ N ∈ Ns, Lay.Inv B shape N := by
      intro N hN
      obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hN
      have := (hNs c (hlen ▸ hc)).1
      rwa [List.getD_eq_getElem _ _ hc] at this
    have hs := Lay.boxOk_sound hB hsh hinv hlen.ge h hy
    unfold Lay.val at hs
    unfold comb
    refine (congrArg (Sign strict) (sum_congr rfl fun c hc ↦ ?_)).mp hs
    rw [(hNs c (mem_range.mp hc)).2 y]
  · exact vertT_sound hsh hfit (Lay.lowSign_cases shape B Ns) h hy

theorem comb_congr {n : ℕ} {shape : List ℕ} {wt : WTerms} (hfit : Fit n shape wt)
    {X X' : ℕ → ℝ} (h : ∀ i < n, X i = X' i) : comb (κ := κ) wt X = comb (κ := κ) wt X' := by
  unfold comb
  exact sum_congr rfl fun c _ ↦ by rw [valAt_congr h hfit]

theorem boxT_sound {n : ℕ} {shape : List ℕ} {strict : Bool} {M : ℕ} {wt : WTerms}
    {C H : List ℤ} {k : ℕ} (hsh : shape.length ≤ n) (hfit : Fit n shape wt)
    (hdeg : ∀ x ∈ wt, ∀ c, ∀ t ∈ x.2.getD c [], t.2.sum ≤ M)
    (h : boxT κ n shape strict M wt C H k = true) {y : ℕ → ℝ} (hy : ∀ i, |y i| ≤ 1) :
    Sign strict (comb (κ := κ) wt (envK C H k y)) := by
  simp only [boxT] at h
  have hfit' := hfit.scale k M
  have hs := topT_sound (Lay.digitsFor_pos _ _) hsh hfit' (by simp [numsAt])
    (numsAt_spec (κ := κ) (C := C) (H := H)
      (B := Lay.digitsFor (normsAt κ n C H (WTerms.scale k M wt)) (Lay.apxBits κ))
      (Lay.digitsFor_pos _ _) hsh hfit' fun c hc ↦ normW_lt_digitsFor hc _) h hy
  have e : comb (κ := κ) (WTerms.scale k M wt) (fun i ↦ (C.getD i 0 : ℝ) + H.getD i 0 * y i) =
      2 ^ (k * M) * comb (κ := κ) wt (envK C H k y) := by
    unfold comb
    rw [mul_sum]
    refine sum_congr rfl fun c _ ↦ ?_
    rw [valAt_scale _ k M c fun x hx t ht ↦ hdeg x hx c t ht]
    unfold envK
    ring
  rw [e] at hs
  exact sign_of_mul (by positivity) hs

/-- The vertex test at the origin gives the sign on the box (any vertex does: `vertT_sound`). -/
theorem origT_sound {n : ℕ} {shape : List ℕ} {strict : Bool} {M : ℕ} {wt : WTerms}
    {C H : List ℤ} {k : ℕ} (hsh : shape.length ≤ n) (hfit : Fit n shape wt)
    (hdeg : ∀ x ∈ wt, ∀ c, ∀ t ∈ x.2.getD c [], t.2.sum ≤ M)
    (h : origT κ n shape strict M wt C H k = true) {y : ℕ → ℝ} (hy : ∀ i, |y i| ≤ 1) :
    Sign strict (comb (κ := κ) wt (envK C H k y)) := by
  simp only [origT, Bool.and_eq_true] at h
  have hs := vertT_sound hsh (hfit.scale k M) (origV_cases C H) h.2 hy
  have e : comb (κ := κ) (WTerms.scale k M wt) (fun i ↦ (C.getD i 0 : ℝ) + H.getD i 0 * y i) =
      2 ^ (k * M) * comb (κ := κ) wt (envK C H k y) := by
    unfold comb
    rw [mul_sum]
    refine sum_congr rfl fun c _ ↦ ?_
    rw [valAt_scale _ k M c fun x hx t ht ↦ hdeg x hx c t ht]
    unfold envK
    ring
  rw [e] at hs
  exact sign_of_mul (by positivity) hs

theorem boxS_sound {n : ℕ} {shape : List ℕ} {strict : Bool} {M : ℕ} {wt : WTerms} {test : Bool}
    {C H : List ℤ} {k : ℕ} (hsh : shape.length ≤ n) (hfit : Fit n shape wt)
    (hdeg : ∀ x ∈ wt, ∀ c, ∀ t ∈ x.2.getD c [], t.2.sum ≤ M)
    (h : boxS κ n shape strict M wt test C H k = true) {y : ℕ → ℝ} (hy : ∀ i, |y i| ≤ 1) :
    Sign strict (comb (κ := κ) wt (envK C H k y)) := by
  simp only [boxS, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨-, h⟩ | h
  · exact boxT_sound hsh hfit hdeg h hy
  · exact origT_sound hsh hfit hdeg h hy

/-- **Soundness of rupert's bisection**: where `boxRec` passes, the combination of the weighted
terms has the sign at every point of the box. -/
theorem boxRec_sound {n : ℕ} {shape : List ℕ} {strict : Bool} {M : ℕ} {wt : WTerms}
    (hsh : shape.length ≤ n) (hfit : Fit n shape wt)
    (hdeg : ∀ x ∈ wt, ∀ c, ∀ t ∈ x.2.getD c [], t.2.sum ≤ M) :
    ∀ (fuel : ℕ) (test : Bool) (C H : List ℤ) (k : ℕ) (W : List ℤ),
      boxRec κ n shape strict M wt fuel test C H k W = true →
      ∀ y : ℕ → ℝ, (∀ i, |y i| ≤ 1) → Sign strict (comb (κ := κ) wt (envK C H k y))
  | 0, test, C, H, k, W, h, y, hy => by
    simp only [boxRec] at h
    exact boxS_sound hsh hfit hdeg h hy
  | d + 1, test, C, H, k, W, h, y, hy => by
    simp only [boxRec, Bool.or_eq_true] at h
    rcases h with h | h
    · exact boxS_sound hsh hfit hdeg h hy
    · cases hdg : Lay.deg shape (Lay.pickW true n W) == 0
      · rw [hdg, Bool.cond_false, Bool.and_eq_true] at h
        obtain ⟨hlo, hhi⟩ := h
        have half : ∀ s : ℤ, (s = 1 ∨ s = -1) → 0 ≤ s * y (Lay.pickW true n W) →
            boxRec κ n shape strict M wt d true (halfC n C H (Lay.pickW true n W) s)
              (halfH n H (Lay.pickW true n W)) (k + 1) (Lay.halveW W (Lay.pickW true n W)) =
              true → Sign strict (comb (κ := κ) wt (envK C H k y)) := by
          intro s hs hside hrec
          set i := Lay.pickW true n W
          have hy' : ∀ j, |Function.update y i (2 * y i - s) j| ≤ 1 := by
            intro j
            by_cases hj : j = i
            · subst hj
              rw [Function.update_self]
              exact abs_half_le hs (hy _) hside
            · rw [Function.update_of_ne hj]
              exact hy j
          have := boxRec_sound hsh hfit hdeg d true _ _ (k + 1) _ hrec _ hy'
          rwa [comb_congr hfit (envK_half C H k i s y)] at this
        by_cases hyi : y (Lay.pickW true n W) ≤ 0
        · exact half (-1) (Or.inr rfl) (by push_cast; linarith) hlo
        · exact half 1 (Or.inl rfl) (by push_cast; linarith) hhi
      · rw [hdg, Bool.cond_true] at h
        exact boxRec_sound hsh hfit hdeg d false C H k _ h y hy

end Field

end Pull

end Nieuwland.Check
