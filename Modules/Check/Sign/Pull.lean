import Modules.Check.Number.Frac
import Modules.Check.Polynomial.Mask
import Modules.Check.Sign.Box
import Modules.Check.Sign.Dominance
import Modules.Check.Polynomial.Divide
import Modules.Check.Sign.EngineCache
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.GetD
import Mathlib.Tactic.LinearCombination

/-!
# Signs of pulled-back polynomials on boxes

A witness polynomial pulled back along an exact map of parameter boxes (a zoom) is a polynomial
`Q` in the box variables with exact coefficients, vanishing to some order where radius parameters
vanish. As in `nonneg_on_fbox_exact` (`code/src/proof/regional.rs`), the sign is certified for the
quotient `Q / x^e` by the largest monomial in the radii that divides it. This file is the sign
routine for such quotients and for positive combinations of them.

The polynomial is a generic computation (`GenPoly κ`) with constants in an exact type with
coordinates (`ExactBasis κ`), run in fractions over the base `D = 2 den` of a box
`∏ [loᵢ, hiᵢ] / den` (`GenPoly.runFV`): a box coordinate is `xᵢ = zᵢ / D` with `zᵢ = Cᵢ + Hᵢ yᵢ`,
`Cᵢ = loᵢ + hiᵢ`, `Hᵢ = hiᵢ - loᵢ`, `|yᵢ| ≤ 1`, and the value is `∑ₖ βₖ Vₖ(z) / D^m` with integer
polynomials `Vₖ`, one per coordinate of `κ`. The frame is the box itself (`D = 2 den`); on it the
kernel

1. packs each `Vₖ` in the variables `z` and checks that the digits of the monomials not divisible
   by `z^e` equal the bias (`DPoly.maskOk`), so `Vₖ = z^e Nₖ` with integer polynomials `Nₖ`;
2. packs the quotients `Tₖ(y) = Nₖ(C + H y)`, whose values at the packing point are the
   coordinates of `V(Z) / Z^e` at the packed inputs `Z = C + H Y`: one evaluation of the
   computation in `κ` and one exact division per coordinate;
3. runs the packed engine (`Lay.run`, `Modules/Check/Sign/Engine.lean`) on the numerals of
   `∑ₖ βₖ Tₖ`, or of a positive combination of such quotients: the centred form, vertex dominance,
   and bisection of the last widest coordinate (as `nonneg_on_fbox_exact` does) by substitutions
   in the numerals. The halves of the Rust check have their own packings; theirs are positive
   multiples of the engine's polynomials, so the decisions are the same. For a weak sign the
   engine also divides the combination by the linear factors `Cᵢ + Hᵢ yᵢ` of the coordinates where
   the box has one sign, as often as the division is exact (`Lay.runDiv`,
   `Modules/Check/Polynomial/Divide.lean`), as Rust's `weak_nonneg` divides a tuple's sum again by its largest
   monomial in the signed slots.

Coordinates where the box is a point (`Hᵢ = 0`) enter as constants, so the packings have no slots
for them. The conclusion (`Pull.check_sound`): at every box point `x`, for every checked
combination `∑ wⱼ Qⱼ`, there are `c > 0` and numbers `sⱼ` with `Qⱼ(x) = c x^eⱼ sⱼ` and
`∑ wⱼ sⱼ ≥ 0` (or `> 0`).
-/

namespace Nieuwland.Check

/-! ### Runs in fractions -/

namespace GenPoly

variable {κ : Type}

/-- The computation in fractions over the base `D`: the inputs `x i` over `D` (exponent `1`),
the constants embedded by `k` (exponent `0`). -/
def runFV {α : Type} [Add α] [Sub α] [Mul α] (G : GenPoly κ) (k : κ → α) (D : α) (x : ℕ → α) :
    FV D :=
  G.run (FV.const k) fun i ↦ ⟨x i, 1⟩

theorem map_runFV {α β : Type} [Add α] [Sub α] [Mul α] [Add β] [Sub β] [Mul β] (G : GenPoly κ)
    {f : α → β} (hf : IsArith f) (k : κ → α) (D : α) (x : ℕ → α) :
    FV.map f (G.runFV k D x) = G.runFV (f ∘ k) (f D) (f ∘ x) := by
  rw [runFV, G.natural _ (FV.isArith_map hf)]
  rfl

theorem val_runFV_congr {α : Type} [Add α] [Sub α] [Mul α] (G : GenPoly κ) {k k' : κ → α}
    {D D' : α} {x x' : ℕ → α} (hk : k = k') (hD : D = D') (hx : x = x') :
    (G.runFV k D x).val = (G.runFV k' D' x').val := by
  subst hk hD hx
  rfl

/-- The exponent of the denominator of a run, which depends only on the computation. -/
def expo (G : GenPoly κ) : ℕ :=
  (G.runFV (α := PUnit) (fun _ ↦ PUnit.unit) PUnit.unit fun _ ↦ PUnit.unit).exp

theorem exp_runFV {α : Type} [Add α] [Sub α] [Mul α] (G : GenPoly κ) (k : κ → α) (D : α)
    (x : ℕ → α) : (G.runFV k D x).exp = G.expo := by
  have hf : IsArith fun _ : α ↦ PUnit.unit := ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  have := congrArg FV.exp (G.map_runFV hf k D x)
  rw [FV.map_exp] at this
  rw [this]
  rfl

/-- **The meaning of runs**: over a nonzero real base `D`, a run with inputs `w i` has the value
of the computation at `w i / D`. -/
theorem toVal_runFV [Add κ] [Sub κ] [Mul κ] [Exact κ] (G : GenPoly κ) {D : ℝ} (hD : D ≠ 0)
    (w : ℕ → ℝ) : FV.toVal (G.runFV Exact.re D w) = G.run Exact.re fun i ↦ w i / D := by
  rw [runFV, G.natural _ (FV.isArith_toVal hD)]
  congr 1
  · funext c
    simp [Function.comp, FV.const, FV.toVal]
  · funext i
    simp [Function.comp, FV.toVal]

end GenPoly

/-! ### Box inputs -/

/-- The input `i` of a box: the variable `v i` where the box varies in coordinate `i`
(`Hᵢ ≠ 0`), else the constant `Cᵢ`, embedded by `k`. -/
def boxInput {α : Type*} (C H : List ℤ) (k : ℤ → α) (v : ℕ → α) (i : ℕ) : α :=
  if H.getD i 0 = 0 then k (C.getD i 0) else v i

theorem map_boxInput {α β : Type*} (f : α → β) (C H : List ℤ) (k : ℤ → α) (v : ℕ → α) :
    f ∘ boxInput C H k v = boxInput C H (f ∘ k) (f ∘ v) := by
  funext i
  simp only [Function.comp, boxInput]
  split_ifs <;> rfl

/-- A term of a sign check: a polynomial, as a generic computation in the box variables, and
the exponents of the monomial it is divided by. -/
structure Term (κ : Type) where
  /-- The polynomial. -/
  G : GenPoly κ
  /-- The exponents of the monomial. -/
  e : List ℕ

/-- The default computation: the constant `0`. -/
instance {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] : Inhabited (GenPoly κ) :=
  ⟨⟨fun k _ ↦ k (Exact.ofInt 0), fun _ _ _ _ ↦ rfl⟩⟩

instance {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] : Inhabited (Term κ) := ⟨⟨default, []⟩⟩

namespace Term

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] (t : Term κ)

/-- The run as coordinate polynomials in the varying coordinates, over the base `D` (in
proofs). -/
def expr (C H : List ℤ) (D : ℤ) : FV (Ext.var (.const D) : Ext κ Expr) :=
  t.G.runFV Ext.const (Ext.var (.const D)) fun i ↦ Ext.var (boxInput C H Expr.const Expr.var i)

/-- Coordinate `c` of the run's numerator (in proofs). -/
def coordE (C H : List ℤ) (D : ℤ) (c : ℕ) : Expr := (t.expr C H D).val.coord c

/-- A bound on the shapes of the coordinates of the run's numerator in the varying coordinates. -/
def shapeOf (C H : List ℤ) : List ℕ :=
  DPoly.shapeMax ((t.G.runFV (Ext.const : κ → Ext κ ShapeL) (Ext.var ⟨[]⟩) fun i ↦
    Ext.var (boxInput C H (fun _ ↦ ⟨[]⟩) (fun i ↦ ⟨List.replicate i 0 ++ [1]⟩) i)).val.c.map
      ShapeL.val)

/-- A bound on the absolute coefficient sums of the coordinates of the run's numerator in the
varying coordinates, where varying coordinate `i` is bounded by `r i`. -/
def norm (C H : List ℤ) (D : ℤ) (r : ℕ → ℕ) : ℕ :=
  ((t.G.runFV (Ext.const : κ → Ext κ AbsNat) (Ext.var ⟨D.natAbs⟩) fun i ↦
    Ext.var (boxInput C H AbsNat.ofInt (fun i ↦ ⟨r i⟩) i)).val.c.map AbsNat.val).foldr max 0

/-- The numerator of the run at the integer inputs `z` of the varying coordinates, in `κ`. -/
def value (C H : List ℤ) (D : ℤ) (z : ℕ → ℤ) : κ :=
  (t.G.runFV id (Exact.ofInt D) fun i ↦ Exact.ofInt (boxInput C H id z i)).val

theorem exp_expr (C H : List ℤ) (D : ℤ) : (t.expr C H D).exp = t.G.expo :=
  t.G.exp_runFV _ _ _

/-- The coordinate polynomials under an interpretation `f` are a run over `f`. -/
theorem map_val_expr {γ : Type} [Add γ] [Sub γ] [Mul γ] [IntCast γ] {f : Expr → γ}
    (hf : IsArith f) (hk : ∀ n : ℤ, f n = n) {C H : List ℤ} {D : ℤ} {Dγ : Ext κ γ}
    (hD : Ext.var (f (.const D)) = Dγ) {xγ : ℕ → Ext κ γ}
    (hx : ∀ i, Ext.var (f (boxInput C H Expr.const Expr.var i)) = xγ i) :
    (t.expr C H D).val.map f = (t.G.runFV Ext.const Dγ xγ).val := by
  have h := congrArg FV.val (t.G.map_runFV (Ext.isArith_map (κ := κ) hf hk) Ext.const
    (Ext.var (.const D)) fun i ↦ Ext.var (boxInput C H Expr.const Expr.var i))
  rw [FV.map_val] at h
  rw [expr, h]
  exact t.G.val_runFV_congr (funext fun a ↦ Ext.map_const hk a)
    ((Ext.map_var hf.map_mul hk _).trans hD)
    (funext fun i ↦ (Ext.map_var hf.map_mul hk _).trans (hx i))

theorem shapeOf_eq {C H : List ℤ} (D : ℤ) {s : List (List ℕ)}
    (hs : ∀ i, H.getD i 0 ≠ 0 → s.getD i [] = List.replicate i 0 ++ [1]) :
    t.shapeOf C H = DPoly.shapeMax ((t.expr C H D).val.c.map fun e ↦ e.shape s) := by
  have h := t.map_val_expr (Expr.isArith_shape s) (fun _ ↦ rfl) (C := C) (H := H) (D := D)
    (Dγ := Ext.var ⟨[]⟩) rfl
    (xγ := fun i ↦ Ext.var (boxInput C H (fun _ ↦ ⟨[]⟩) (fun i ↦ ⟨List.replicate i 0 ++ [1]⟩) i))
    fun i ↦ by
      simp only [boxInput]
      split_ifs with h0
      · rfl
      · simp only [Expr.shape, hs i h0]
  rw [shapeOf, ← h, Ext.map_c, List.map_map]
  rfl

theorem shapeLE_coordE {C H : List ℤ} (D : ℤ) {s : List (List ℕ)}
    (hs : ∀ i, H.getD i 0 ≠ 0 → s.getD i [] = List.replicate i 0 ++ [1]) (c : ℕ) :
    DPoly.ShapeLE ((t.coordE C H D c).shape s) (t.shapeOf C H) := by
  rw [t.shapeOf_eq D hs]
  exact (t.expr C H D).val.shapeLE_coord s c

theorem norm_eq {C H : List ℤ} {D : ℤ} {b : List ℕ} {r : ℕ → ℕ}
    (hb : ∀ i, H.getD i 0 ≠ 0 → b.getD i 0 = r i) :
    t.norm C H D r = ((t.expr C H D).val.c.map fun e ↦ e.normBound b).foldr max 0 := by
  have h := t.map_val_expr (Expr.isArith_normBound b) (fun _ ↦ rfl) (C := C) (H := H) (D := D)
    (Dγ := Ext.var ⟨D.natAbs⟩) rfl
    (xγ := fun i ↦ Ext.var (boxInput C H AbsNat.ofInt (fun i ↦ ⟨r i⟩) i)) fun i ↦ by
      simp only [boxInput]
      split_ifs with h0
      · rfl
      · simp only [Expr.normBound, hb i h0]
  rw [norm, ← h, Ext.map_c, List.map_map]
  rfl

theorem normBound_le_norm {C H : List ℤ} {D : ℤ} {b : List ℕ} {r : ℕ → ℕ}
    (hb : ∀ i, H.getD i 0 ≠ 0 → b.getD i 0 = r i) (c : ℕ) :
    (t.coordE C H D c).normBound b ≤ t.norm C H D r := by
  rw [t.norm_eq hb]
  exact (t.expr C H D).val.normBound_le_coord b c

theorem coords_value {C H : List ℤ} {D : ℤ} {zl : List ℤ} {z : ℕ → ℤ}
    (hz : ∀ i, H.getD i 0 ≠ 0 → zl.getD i 0 = z i) :
    ExactBasis.coords (t.value C H D z) = (t.expr C H D).val.c.map (Expr.evalInt zl) := by
  have h := t.map_val_expr (Expr.isArith_evalInt zl) (fun _ ↦ rfl) (C := C) (H := H) (D := D)
    (Dγ := Ext.var D) rfl
    (xγ := fun i ↦ Ext.var (boxInput C H id z i)) fun i ↦ by
      simp only [boxInput]
      split_ifs with h0
      · rfl
      · simp only [Expr.evalInt, hz i h0]
  have h' := congrArg FV.val (t.G.map_runFV (Ext.isArith_ofExact (κ := κ)) id (Exact.ofInt D)
    fun i ↦ Exact.ofInt (boxInput C H id z i))
  rw [FV.map_val] at h'
  rw [← Ext.map_c, h, value]
  change (Ext.ofExact _).c = _
  rw [h']
  congr 1
  exact t.G.val_runFV_congr (funext fun a ↦ Ext.ofExact_eq_const a) (Ext.ofExact_ofInt D)
    (funext fun i ↦ Ext.ofExact_ofInt _)

theorem getD_coords_value {C H : List ℤ} {D : ℤ} {zl : List ℤ} {z : ℕ → ℤ}
    (hz : ∀ i, H.getD i 0 ≠ 0 → zl.getD i 0 = z i) (c : ℕ) :
    (ExactBasis.coords (t.value C H D z)).getD c 0 = (t.coordE C H D c).evalInt zl := by
  rw [t.coords_value hz, coordE, Ext.evalInt_coord]

/-- **The meaning of the coordinates**: at a real point `w` of the varying coordinates, divided by
`D^k`, their combination is the computation at `x = w / D`, where the constant coordinates are
`Cᵢ / D`. -/
theorem eval_expr {C H : List ℤ} {D : ℤ} (hD : (D : ℝ) ≠ 0) (w : ℕ → ℝ) :
    (∑ c ∈ Finset.range (ExactBasis.dim κ), ExactBasis.basis κ c * (t.coordE C H D c).eval w) /
        (D : ℝ) ^ t.G.expo = t.G.run Exact.re fun i ↦ boxInput C H (Int.cast : ℤ → ℝ) w i / D := by
  have h := t.map_val_expr (Expr.isArith_eval w) (fun _ ↦ rfl) (C := C) (H := H) (D := D)
    (Dγ := Ext.var (D : ℝ))
    rfl (xγ := fun i ↦ Ext.var (boxInput C H Int.cast w i)) fun i ↦ by
      simp only [boxInput]
      split_ifs <;> rfl
  have h' := congrArg FV.val (t.G.map_runFV (Ext.isArith_re (κ := κ)) Ext.const
    (Ext.var (D : ℝ)) fun i ↦ Ext.var (boxInput C H Int.cast w i))
  rw [FV.map_val] at h'
  have e : (∑ c ∈ Finset.range (ExactBasis.dim κ),
      ExactBasis.basis κ c * (t.coordE C H D c).eval w) =
        Ext.re ((t.expr C H D).val.map (Expr.eval w)) := (Ext.re_map_eval _ w).symm
  rw [e, h, h', ← t.G.toVal_runFV hD, FV.toVal, GenPoly.exp_runFV]
  congr 1
  exact t.G.val_runFV_congr (funext fun a ↦ Ext.re_const a) (Ext.re_var _)
    (funext fun i ↦ Ext.re_var _)

theorem shapeOf_default (C H : List ℤ) : (default : Term κ).shapeOf C H = [] := by
  change DPoly.shapeMax (((ExactBasis.coords (Exact.ofInt 0 : κ)).map
    (Int.cast : ℤ → ShapeL)).map ShapeL.val) = []
  rw [List.map_map]
  induction ExactBasis.coords (Exact.ofInt 0 : κ) with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, DPoly.shapeMax, ih]
    rfl

theorem shapeOf_congr {C H C' H' : List ℤ} (h : ∀ i, H.getD i 0 = 0 ↔ H'.getD i 0 = 0) :
    t.shapeOf C H = t.shapeOf C' H' := by
  unfold shapeOf
  congr 5
  funext i
  simp only [boxInput, h i]

end Term

namespace DPoly

theorem zeroOn_of_false : ∀ (n : ℕ) {P : List ℕ → Bool} (p : DPoly n), (∀ α, P α = false) →
    ZeroOn n P p
  | 0, _, _, hP => fun h ↦ absurd h (by simp [hP])
  | n + 1, P, p, hP => by
    have key : ∀ (k : ℕ) (l : List (DPoly n)),
        ForallIdx (fun k q ↦ ZeroOn n (fun α ↦ P (k :: α)) q) k l := by
      intro k l
      induction l generalizing k with
      | nil => trivial
      | cons q l ih => exact ⟨zeroOn_of_false n q fun α ↦ hP _, ih (k + 1)⟩
    exact key 0 _

theorem below_eq_false {e : List ℕ} (he : e.all (· == 0) = true) : ∀ α, below e α = false
  | [] => rfl
  | a :: α => by
    have h0 : e.headD 0 = 0 := by
      cases e with
      | nil => rfl
      | cons b e => simpa using (List.all_eq_true.mp he b List.mem_cons_self)
    have ht : e.tail.all (· == 0) = true := by
      cases e with
      | nil => rfl
      | cons b e => simp only [List.all_cons, Bool.and_eq_true] at he; exact he.2
    change (decide (a < e.headD 0) || below e.tail α) = false
    rw [h0, below_eq_false ht α]
    simp

theorem monoVal_smul {R : Type*} [CommMonoid R] (c : R) : ∀ (n : ℕ) (e : List ℕ)
    (x : Fin n → R), e.length ≤ n → monoVal n e (fun i ↦ c * x i) = c ^ e.sum * monoVal n e x
  | 0, e, _, he => by simp [monoVal, List.length_eq_zero_iff.mp (Nat.le_zero.mp he)]
  | n + 1, e, x, he => by
    have ht : e.tail.length ≤ n := by simp; omega
    have hs : e.sum = e.headD 0 + e.tail.sum := by cases e <;> simp
    have := monoVal_smul c n e.tail (Fin.tail x) ht
    have h' : (Fin.tail fun i ↦ c * x i) = fun i ↦ c * Fin.tail x i := rfl
    rw [monoVal, monoVal, h', this, hs, mul_pow, pow_add, mul_mul_mul_comm]

theorem monoVal_cast {R : Type*} [CommRing R] : ∀ (n : ℕ) (e : List ℕ) (z : Fin n → ℤ),
    ((monoVal n e z : ℤ) : R) = monoVal n e fun i ↦ (z i : R)
  | 0, _, _ => by simp [monoVal]
  | n + 1, e, z => by
    simp only [monoVal, Int.cast_mul, Int.cast_pow, monoVal_cast n e.tail]
    rfl

end DPoly

namespace Pull

open DPoly

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

theorem digitBits_pos (N : ℕ) : 0 < digitBits N := Nat.succ_pos _

/-- The bounds `|Cᵢ| + |Hᵢ|` of the box inputs. -/
def radii (C H : List ℤ) (i : ℕ) : ℕ := (C.getD i 0).natAbs + (H.getD i 0).natAbs

/-! ### Terms on a frame

A frame `(C, H, D)` fixes the base `D` and the coordinates where the box is a point (`Hᵢ = 0`,
the constant `Cᵢ / D`). A term's quotients by its monomial, one per coordinate, depend only on the
frame: they are read once from the packed numerators, after the mask checks. -/

/-- The digit size of the mask checks of a term on the frame `(C, H, D)`. -/
def maskBits (t : Term κ) (C H : List ℤ) (D : ℤ) : ℕ := digitBits (t.norm C H D fun _ ↦ 1)

theorem maskBits_pos (t : Term κ) (C H : List ℤ) (D : ℤ) : 0 < maskBits t C H D :=
  digitBits_pos _

/-- The mask checks of a term on the frame `(C, H, D)`: in each packed coordinate of the
numerator, the digits of the monomials that `z^e` does not divide equal the bias. -/
def maskAt (n : ℕ) (t : Term κ) (C H : List ℤ) (D : ℤ) : Bool :=
  let shz := t.shapeOf C H
  let B := maskBits t C H D
  let v := ExactBasis.coords (t.value C H D fun i ↦ packPoint' shz B i)
  (List.range (ExactBasis.dim κ)).all fun c ↦
    maskOk n (below t.e) shz B (v.getD c 0 + offset n shz B).toNat

/-- `maskAt` with the mask and the offset, numerals as large as the packed coordinates, built once
for all coordinates (`maskAt_eq_maskAtS`). -/
def maskAtS (n : ℕ) (t : Term κ) (C H : List ℤ) (D : ℤ) : Bool :=
  let shz := t.shapeOf C H
  let B := maskBits t C H D
  let v := ExactBasis.coords (t.value C H D fun i ↦ packPoint' shz B i)
  let M := mask n (below t.e) shz B
  let O := offset n shz B
  let OM := O &&& M
  (List.range (ExactBasis.dim κ)).all fun c ↦ (v.getD c 0 + O).toNat &&& M == OM

@[csimp] theorem maskAt_eq_maskAtS : @maskAt = @maskAtS := by
  funext κ _ _ _ _ n t C H D
  simp only [maskAt, maskAtS, maskOk]

/-- What the check computes once per term on a frame. -/
structure TermFrame where
  /-- The mask checks passed and the monomial is admissible. -/
  ok : Bool
  /-- A bound on the shapes of the quotients. -/
  sh : List ℕ
  /-- The degree `k - |e|` of the quotients' denominator. -/
  m : ℕ
  deriving Inhabited

/-- A term on the frame `(C, H, D)`. -/
def termFrame (n : ℕ) (t : Term κ) (C H : List ℤ) (D : ℤ) : TermFrame :=
  ⟨(t.e.all (· == 0) || maskAt n t C H D) && decide (t.e.length ≤ n) &&
      decide (t.e.sum ≤ t.G.expo),
    shapeSub (t.shapeOf C H) t.e, t.G.expo - t.e.sum⟩

/-- The variables of a box, as dense polynomials. -/
def zVars (n : ℕ) (D : ℤ) : ℕ → DPoly n := boxInputs n [] (List.replicate n 1) D

/-- Coordinate `c` of the numerator of a term on a frame, as a dense polynomial in the varying
coordinates (in proofs). -/
def numer (n : ℕ) (t : Term κ) (C H : List ℤ) (D : ℤ) (c : ℕ) : DPoly n :=
  (t.coordE C H D c).toDPoly n (zVars n D)

/-- Coordinate `c` of the quotient of a term on a frame by its monomial, read from the packed
numerator (in proofs). -/
def quot (n : ℕ) (t : Term κ) (C H : List ℤ) (D : ℤ) (c : ℕ) : DPoly n :=
  let shz := t.shapeOf C H
  let B := maskBits t C H D
  unshift n t.e (unpack n shz B (biased n shz B (numer n t C H D c)).toNat)

/-- Bounds `r` of the varying coordinates, then `|D|`. -/
def normList (n : ℕ) (r : ℕ → ℕ) (D : ℤ) : List ℕ := (List.range n).map r ++ [D.natAbs]

/-- A box point as an input to computations: its coordinates, then zeros. -/
def ext (n : ℕ) (x : Fin n → ℝ) (i : ℕ) : ℝ := if h : i < n then x ⟨i, h⟩ else 0

theorem getD_replicate_one {n i : ℕ} (hi : i < n) : (List.replicate n (1 : ℤ)).getD i 0 = 1 := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem eval_zVars {n : ℕ} {D : ℤ} {R : Type*} [CommRing R] (w : Fin n → R) (i : ℕ) :
    eval n (zVars n D i) w = if h : i < n then w ⟨i, h⟩ else if i = n then (D : R) else 0 := by
  rw [zVars, eval_boxInputs, boxEnv]
  split_ifs with h₁
  · rw [getD_replicate_one h₁]
    simp
  · rfl
  · rfl

theorem absEval_zVars_le {n : ℕ} {D : ℤ} (r : ℕ → ℕ) (i : ℕ) :
    absEval n (zVars n D i) (fun j ↦ r j) ≤ (normList n r D).getD i 0 := by
  rw [normList, getD_range_map_append, zVars, boxInputs]
  split_ifs with h₁ h₂
  · refine (absEval_linear n i _ _ _).trans ?_
    rw [getD_replicate_one h₁]
    simp [h₁]
  · exact (absEval_const n D _).le
  · rw [absEval_zero]

section TermFacts

variable {n : ℕ} {t : Term κ} {C H : List ℤ} {D : ℤ}

variable (hH : ∀ i, H.getD i 0 ≠ 0 → i < n)
include hH

/-- The packing of coordinate `c` of the numerator: it fits its shape, its coefficients are
small, and its biased packed value is computed from the run. -/
theorem numer_packing (c : ℕ) :
    Fits n (numer n t C H D c) (t.shapeOf C H) ∧
      Small n (maskBits t C H D) (numer n t C H D c) ∧
      (ExactBasis.coords (t.value C H D fun i ↦
          packPoint' (t.shapeOf C H) (maskBits t C H D) i)).getD c 0 +
          offset n (t.shapeOf C H) (maskBits t C H D) =
        biased n (t.shapeOf C H) (maskBits t C H D) (numer n t C H D c) := by
  have hsh : ShapeLE ((t.coordE C H D c).shape (boxShapes n)) (t.shapeOf C H) :=
    t.shapeLE_coordE D (fun i hi ↦ by
      simp only [boxShapes, getD_range_map_append, hH i hi, ↓reduceIte]) c
  have hnb : (t.coordE C H D c).normBound (boxNorms n [] (List.replicate n 1) D) ≤
      t.norm C H D fun _ ↦ 1 :=
    t.normBound_le_norm (fun i hi ↦ by
      simp only [boxNorms, getD_range_map_append, hH i hi, ↓reduceIte,
        getD_replicate_one (hH i hi)]
      simp) c
  obtain ⟨h₁, h₂, h₃⟩ := box_packing (t.coordE C H D c) hsh [] (List.replicate n 1) D hnb
  rw [maskBits]
  refine ⟨h₁, h₂, ?_⟩
  rw [t.getD_coords_value (zl := boxPacked n (t.shapeOf C H) (digitBits (t.norm C H D fun _ ↦ 1))
    [] (List.replicate n 1) D) (fun i hi ↦ ?_)]
  · exact h₃
  · simp only [boxPacked, getD_range_map_append, hH i hi, ↓reduceIte,
      getD_replicate_one (hH i hi)]
    simp

variable (hok : (termFrame n t C H D).ok = true)
include hok

omit hH in
theorem termFrame_ok_iff : (t.e.all (· == 0) = true ∨ maskAt n t C H D = true) ∧
    t.e.length ≤ n ∧ t.e.sum ≤ t.G.expo := by
  simpa [termFrame, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, and_assoc] using hok

/-- The mask checks give the zero patterns of the packed coordinates of the numerator. -/
theorem zeroOn_packed {c : ℕ} (hc : c < ExactBasis.dim κ) :
    ZeroOn n (below t.e) (unpack n (t.shapeOf C H) (maskBits t C H D)
      (biased n (t.shapeOf C H) (maskBits t C H D) (numer n t C H D c)).toNat) := by
  rcases (termFrame_ok_iff hok).1 with he | hm
  · exact zeroOn_of_false n _ (below_eq_false he)
  · simp only [maskAt, List.all_eq_true, List.mem_range] at hm
    have := hm c hc
    rw [(numer_packing hH c).2.2] at this
    exact zeroOn_unpack_of_maskOk (maskBits_pos t C H D) this

omit hH hok in
theorem fits_quot (c : ℕ) : Fits n (quot n t C H D c) (termFrame n t C H D).sh :=
  fits_unshift n t.e (fits_unpack n _ _ _)

/-- The absolute coefficient sum of coordinate `c` of the quotient at bounds `r` of the varying
coordinates. -/
theorem absEval_quot_le {c : ℕ} (hc : c < ExactBasis.dim κ) (r : ℕ → ℕ)
    (hr : 0 < monoVal n t.e fun j : Fin n ↦ r j) :
    absEval n (quot n t C H D c) (fun j ↦ r j) ≤
      t.norm C H D r / monoVal n t.e fun j : Fin n ↦ r j := by
  obtain ⟨hfit, hsmall, -⟩ := numer_packing (t := t) (D := D) hH c
  have h₁ := absEval_unshift n t.e (zeroOn_packed hH hok hc) (fun j ↦ r j)
  have h₂ := absEval_unpack n (maskBits_pos t C H D) hfit hsmall (fun j ↦ r j)
  have h₃ : absEval n (numer n t C H D c) (fun j ↦ r j) ≤ t.norm C H D r :=
    (Expr.absEval_toDPoly_le n (zVars n D) _ (normList n r D) (absEval_zVars_le r) _).trans
      (t.normBound_le_norm (fun i hi ↦ by
        simp only [normList, getD_range_map_append, hH i hi, ↓reduceIte]) c)
  rw [Nat.le_div_iff_mul_le hr, mul_comm]
  have : monoVal n t.e (fun j : Fin n ↦ r j) * absEval n (quot n t C H D c) (fun j ↦ r j) =
      absEval n (numer n t C H D c) (fun j ↦ r j) := by
    rw [← h₂, h₁]
    rfl
  rw [this]
  exact h₃

/-- Coordinate `c` of the value of the run at integer inputs is the monomial times the
quotient. -/
theorem value_eq {c : ℕ} (hc : c < ExactBasis.dim κ) (z : ℕ → ℤ) :
    (ExactBasis.coords (t.value C H D z)).getD c 0 =
      monoVal n t.e (fun j : Fin n ↦ z j) * eval n (quot n t C H D c) (fun j ↦ z j) := by
  obtain ⟨hfit, hsmall, -⟩ := numer_packing (t := t) (D := D) hH c
  have h₁ : (ExactBasis.coords (t.value C H D z)).getD c 0 =
      eval n (numer n t C H D c) (fun j ↦ z j) := by
    rw [t.getD_coords_value (zl := (List.range n).map z ++ [D]) (fun i hi ↦ ?_)]
    · rw [numer, Expr.evalInt_eq, Expr.eval_toDPoly]
      congr 1
      funext i
      rw [eval_zVars, getD_range_map_append]
      split_ifs <;> rfl
    · simp only [getD_range_map_append, hH i hi, ↓reduceIte]
  rw [h₁, ← eval_unpack n (maskBits_pos t C H D) hfit hsmall,
    eval_unshift n t.e (zeroOn_packed hH hok hc)]
  rfl

/-- **The meaning of the quotients**: at a point `x` of the box (whose constant coordinates are
`Cᵢ / D`), the computation is `x^e` times the combination of the quotients at `D x`, over
`D^m`. -/
theorem run_eq (hC : ∀ i, n ≤ i → C.getD i 0 = 0) (hD : (D : ℝ) ≠ 0)
    (x : Fin n → ℝ) (hx : ∀ i : Fin n, H.getD i 0 = 0 → (C.getD i 0 : ℝ) = D * x i) :
    t.G.run Exact.re (ext n x) = ((D : ℝ) ^ (termFrame n t C H D).m)⁻¹ * monoVal n t.e x *
      ∑ c ∈ Finset.range (ExactBasis.dim κ),
        ExactBasis.basis κ c * eval n (quot n t C H D c) (fun i ↦ (D : ℝ) * x i) := by
  obtain ⟨-, hlen, hsum⟩ := termFrame_ok_iff hok
  set w : Fin n → ℝ := fun i ↦ D * x i
  have hin : (fun i ↦ boxInput C H (Int.cast : ℤ → ℝ)
      (fun i ↦ eval n (zVars n D i) w) i / (D : ℝ)) = ext n x := by
    funext i
    simp only [boxInput, ext]
    by_cases hi : i < n
    · simp only [hi, ↓reduceDIte]
      split_ifs with h0
      · rw [hx ⟨i, hi⟩ h0]; field_simp
      · rw [eval_zVars]
        simp only [hi, ↓reduceDIte, w]
        field_simp
    · have h0 : H.getD i 0 = 0 := by_contra fun h ↦ hi (hH i h)
      simp only [h0, ↓reduceIte, hC i (by omega), hi, ↓reduceDIte]
      simp
  have hrun := t.eval_expr (C := C) (H := H) hD fun i ↦ eval n (zVars n D i) w
  have hcoord : ∀ c ∈ Finset.range (ExactBasis.dim κ),
      ExactBasis.basis κ c * (t.coordE C H D c).eval (fun i ↦ eval n (zVars n D i) w) =
        monoVal n t.e w * (ExactBasis.basis κ c * eval n (quot n t C H D c) w) := by
    intro c hc
    obtain ⟨hfit, hsmall, -⟩ := numer_packing (t := t) (D := D) hH c
    rw [← Expr.eval_toDPoly, ← numer, ← eval_unpack n (maskBits_pos t C H D) hfit hsmall,
      eval_unshift n t.e (zeroOn_packed hH hok (Finset.mem_range.mp hc))]
    change ExactBasis.basis κ c * (monoVal n t.e w * eval n (quot n t C H D c) w) = _
    ring
  rw [hin, Finset.sum_congr rfl hcoord, ← Finset.mul_sum] at hrun
  have hw : monoVal n t.e w = (D : ℝ) ^ t.e.sum * monoVal n t.e x := monoVal_smul _ n t.e x hlen
  rw [← hrun, hw]
  set S := ∑ c ∈ Finset.range (ExactBasis.dim κ),
    ExactBasis.basis κ c * eval n (quot n t C H D c) w
  change (D : ℝ) ^ t.e.sum * monoVal n t.e x * S / (D : ℝ) ^ t.G.expo =
    ((D : ℝ) ^ (t.G.expo - t.e.sum))⁻¹ * monoVal n t.e x * S
  have hpow : (D : ℝ) ^ t.G.expo = (D : ℝ) ^ (t.G.expo - t.e.sum) * (D : ℝ) ^ t.e.sum := by
    rw [← pow_add, Nat.sub_add_cancel hsum]
  have h1 : (D : ℝ) ^ t.e.sum ≠ 0 := pow_ne_zero _ hD
  have h2 : (D : ℝ) ^ (t.G.expo - t.e.sum) ≠ 0 := pow_ne_zero _ hD
  rw [hpow]
  field_simp

end TermFacts

/-! ### Weighted combinations on boxes -/

/-- A weighted combination of terms: pairs of a term index and an integer weight. -/
abbrev Tuple := List (ℕ × ℤ)

/-- The terms of a check and the frame on which their quotients are computed: `C / D` and
`H / D` are the centres and half-widths of the frame box. -/
structure Frame (κ : Type) where
  /-- The number of box coordinates. -/
  n : ℕ
  /-- The terms. -/
  ts : List (Term κ)
  /-- Numerators of the centres of the frame box, over `D`. -/
  C : List ℤ
  /-- Numerators of the half-widths of the frame box, over `D`. -/
  H : List ℤ
  /-- The base. -/
  D : ℤ
  /-- The widths by which the engine picks the coordinate to bisect (`Lay.pickW`): the
  half-widths `H`, or another order (`bisW`). Any widths are sound (`Lay.run_sound`). -/
  W : List ℤ

namespace Frame

variable (F : Frame κ)

/-- Term `j` (the default term beyond the list). -/
def term (j : ℕ) : Term κ := F.ts.getD j default

/-- Term `j` on the frame. -/
def tf (j : ℕ) : TermFrame := termFrame F.n (F.term j) F.C F.H F.D

/-- Coordinate `c` of the quotient of term `j` (in proofs). -/
def q (j c : ℕ) : DPoly F.n := quot F.n (F.term j) F.C F.H F.D c

/-- The packing shape: a bound on the shapes of all quotients. -/
def shape : List ℕ := shapeMax (F.ts.map fun t ↦ (termFrame F.n t F.C F.H F.D).sh)

/-- The monomial of term `j` is positive at the radii of the box `(C, H)`. -/
def rmOk (C H : List ℤ) (j : ℕ) : Bool :=
  decide (0 < monoVal F.n (F.term j).e fun i : Fin F.n ↦ radii C H i)

/-- A bound on the absolute coefficient sums of the quotient of term `j` on the box `(C, H)`. -/
def nb (C H : List ℤ) (j : ℕ) : ℕ :=
  (F.term j).norm F.C F.H F.D (radii C H) / monoVal F.n (F.term j).e fun i : Fin F.n ↦ radii C H i

/-- The monomial of term `j` is nonzero at the integer point `Z`. -/
def mzOk (Z : ℕ → ℤ) (j : ℕ) : Bool :=
  monoVal F.n (F.term j).e (fun i : Fin F.n ↦ Z i) != 0

/-- The coordinates of the quotient of term `j` at the integer point `Z`: those of the numerator
there, divided exactly by the monomial. -/
def val (Z : ℕ → ℤ) (j : ℕ) : List ℤ :=
  let m := monoVal F.n (F.term j).e fun i : Fin F.n ↦ Z i
  (ExactBasis.coords ((F.term j).value F.C F.H F.D Z)).map (· / m)

/-- The largest denominator degree of the terms of a tuple. -/
def tupleK (τ : Tuple) : ℕ := τ.foldr (fun jw K ↦ max (F.tf jw.1).m K) 0

/-- A bound on the absolute coefficient sums of `∑ w D^(K - mⱼ) qⱼ` on the box `(C, H)`. -/
def normSum (C H : List ℤ) (K : ℕ) : Tuple → ℕ
  | [] => 0
  | (j, w) :: τ => w.natAbs * F.D.natAbs ^ (K - (F.tf j).m) * F.nb C H j + normSum C H K τ

/-- The coordinates of `∑ w D^(K - mⱼ) qⱼ` at the integer point `Z`. -/
def valueSum (Z : ℕ → ℤ) (K : ℕ) : Tuple → List ℤ
  | [] => []
  | (j, w) :: τ =>
    zipD 0 (· + ·) ((F.val Z j).map ((w * F.D ^ (K - (F.tf j).m)) * ·)) (valueSum Z K τ)

/-- The packing point `Cᵢ + Hᵢ Yᵢ` of the box `(C, H)` for digits of `B` bits. -/
def point (C H : List ℤ) (B i : ℕ) : ℤ := C.getD i 0 + H.getD i 0 * packPoint' F.shape B i

/-- The numerals of the packed coordinates `v` with digits of `B` bits. -/
def numerals (B : ℕ) (v : List ℤ) : List ℕ :=
  (List.range (ExactBasis.dim κ)).map fun c ↦ (v.getD c 0 + offset F.n F.shape B).toNat

/-- The largest coefficient bound of the tuples on the box `(C, H)`: one digit size for all. -/
def maxNorm (C H : List ℤ) (τs : List Tuple) : ℕ :=
  τs.foldr (fun τ a ↦ max (F.normSum C H (F.tupleK τ) τ) a) 0

/-- The digit size of the tuples `τs` with at most `depth` bisections: one for all, so that the
values of the terms at the packing point are shared, with room for the growth along the
bisections, the vertex expansion and the approximations (`Lay.room`). -/
def bits (depth : ℕ) (τs : List Tuple) : ℕ :=
  Lay.digitsFor (F.maxNorm F.C F.H τs) (Lay.room (Lay.apxBits κ) F.n F.shape true true depth F.W)

/-- The linear factors of the coordinates where the frame box has one sign (`0 < |Hᵢ| ≤ |Cᵢ|`):
`Cᵢ + Hᵢ yᵢ` over `gcd(Cᵢ, Hᵢ)`, with the sign of `Cᵢ`, as `(i, a, b)` for `a + b yᵢ`. The weak
checks divide the combinations by them where the division is exact (`Lay.runDiv`); any list is
sound. -/
def divisors : List (ℕ × ℤ × ℤ) :=
  (List.range F.n).filterMap fun i ↦
    let c := F.C.getD i 0
    let h := F.H.getD i 0
    let g : ℤ := (Nat.gcd c.natAbs h.natAbs : ℤ)
    bif h != 0 && decide (h.natAbs ≤ c.natAbs) then some (i, (c.natAbs : ℤ) / g, c.sign * h / g)
    else none

/-- Certifies the tuple `τ` on the frame box at digit size `B`, with at most `depth` bisections
along each branch: the monomial checks of its terms, then the packed engine on the numerals of its
coordinates (`Lay.run` with vertex dominance and the last widest coordinate; for a weak sign with
the divisions by the factors `divisors`, `Lay.runDiv`). -/
def runTuple (strict : Bool) (depth B : ℕ) (τ : Tuple) : Bool :=
  τ.all (fun jw ↦ F.rmOk F.C F.H jw.1 && F.mzOk (F.point F.C F.H B) jw.1) &&
    Lay.runDiv κ F.n F.shape B strict true true depth F.W F.divisors
      (F.numerals B (F.valueSum (F.point F.C F.H B) (F.tupleK τ) τ))

/-! #### Soundness -/

/-- Coordinate `c` of the polynomial `∑ w D^(K - mⱼ) qⱼ` of a tuple as an expression in the box
variables (in proofs). -/
def sumExpr (K c : ℕ) : Tuple → Expr
  | [] => .const 0
  | (j, w) :: τ => .const (w * F.D ^ (K - (F.tf j).m)) * toExpr F.n 0 (F.q j c) + sumExpr K c τ

/-- Coordinate `c` of the polynomial `∑ w D^(K - mⱼ) qⱼ` of a tuple at a point of a commutative
ring (in proofs). -/
def sumAt {R : Type*} [CommRing R] (z : Fin F.n → R) (K c : ℕ) : Tuple → R
  | [] => 0
  | (j, w) :: τ =>
    ((w * F.D ^ (K - (F.tf j).m) : ℤ) : R) * eval F.n (F.q j c) z + sumAt z K c τ

/-- The frame's varying coordinates are among the first `n`. -/
def Valid : Prop := ∀ i, F.H.getD i 0 ≠ 0 → i < F.n

theorem le_tupleK {τ : Tuple} {jw : ℕ × ℤ} (h : jw ∈ τ) : (F.tf jw.1).m ≤ F.tupleK τ := by
  induction τ with
  | nil => simp at h
  | cons a τ ih =>
    rw [tupleK, List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem le_maxNorm {C H : List ℤ} {τs : List Tuple} {τ : Tuple} (h : τ ∈ τs) :
    F.normSum C H (F.tupleK τ) τ ≤ F.maxNorm C H τs := by
  induction τs with
  | nil => simp at h
  | cons a τs ih =>
    rw [maxNorm, List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem shapeLE_shape (j : ℕ) : ShapeLE (F.tf j).sh F.shape := by
  by_cases hj : j < F.ts.length
  · refine shapeLE_shapeMax (List.mem_map.mpr ⟨F.term j, ?_, rfl⟩)
    rw [term, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  · rw [tf, term, List.getD_eq_default _ _ (by omega), termFrame, Term.shapeOf_default]
    trivial

theorem shape_sumExpr (K c : ℕ) :
    ∀ τ : Tuple, ShapeLE ((F.sumExpr K c τ).shape (boxShapes F.n)) F.shape
  | [] => trivial
  | (j, w) :: τ => by
    refine shapeLE_zipPad_max ?_ (shape_sumExpr K c τ)
    change ShapeLE ((toExpr F.n 0 (F.q j c)).shape (boxShapes F.n)) F.shape
    refine (shape_toExpr_le (boxShapes F.n) F.n 0 (fun i hi ↦ ?_) (fits_quot c)).trans
      (F.shapeLE_shape j)
    simp only [Nat.zero_add, boxShapes, getD_range_map_append, hi, ↓reduceIte]

theorem eval_sumExpr {R : Type*} [CommRing R] (x : ℕ → R) (K c : ℕ) :
    ∀ τ : Tuple, (F.sumExpr K c τ).eval x = F.sumAt (fun i ↦ x i) K c τ
  | [] => by simp [sumExpr, sumAt]
  | (j, w) :: τ => by
    rw [sumExpr, Expr.eval_add, Expr.eval_mul, Expr.eval_const, eval_toExpr,
      eval_sumExpr x K c τ, sumAt]
    simp only [Nat.zero_add]

theorem length_numerals (B : ℕ) (v : List ℤ) :
    ExactBasis.dim κ ≤ (F.numerals B v).length := by
  simp [numerals]

section Sound

variable {F} (hF : F.Valid)
include hF

theorem normBound_sumExpr (C H : List ℤ) (K : ℕ) {c : ℕ} (hc : c < ExactBasis.dim κ) :
    ∀ τ : Tuple, (∀ jw ∈ τ, (F.tf jw.1).ok = true ∧ F.rmOk C H jw.1 = true) →
      (F.sumExpr K c τ).normBound (boxNorms F.n C H F.D) ≤ F.normSum C H K τ
  | [] => fun _ ↦ le_rfl
  | (j, w) :: τ => fun h ↦ by
    obtain ⟨hok, hrm⟩ := h (j, w) List.mem_cons_self
    have ih := normBound_sumExpr C H K hc τ fun jw hjw ↦ h jw (List.mem_cons_of_mem _ hjw)
    change (w * F.D ^ (K - (F.tf j).m)).natAbs *
        (toExpr F.n 0 (F.q j c)).normBound (boxNorms F.n C H F.D) +
        (F.sumExpr K c τ).normBound (boxNorms F.n C H F.D) ≤
      w.natAbs * F.D.natAbs ^ (K - (F.tf j).m) * F.nb C H j + F.normSum C H K τ
    rw [normBound_toExpr, Int.natAbs_mul, Int.natAbs_pow]
    refine Nat.add_le_add (Nat.mul_le_mul_left _ ?_) ih
    have hr : (fun i : Fin F.n ↦ (boxNorms F.n C H F.D).getD (0 + i) 0) =
        fun i : Fin F.n ↦ radii C H i := by
      funext i
      simp only [Nat.zero_add, boxNorms, getD_range_map_append, i.2, ↓reduceIte, radii]
    rw [hr]
    exact absEval_quot_le hF hok hc (radii C H) (by simpa [rmOk] using hrm)

theorem val_eq {j : ℕ} (hok : (F.tf j).ok = true) {Z : ℕ → ℤ} (hmz : F.mzOk Z j = true)
    {c : ℕ} (hc : c < ExactBasis.dim κ) :
    (F.val Z j).getD c 0 = eval F.n (F.q j c) (fun i ↦ Z i) := by
  rw [val, getD_map_of_eq (f := fun v : ℤ ↦ v / monoVal F.n (F.term j).e fun i : Fin F.n ↦ Z i)
    (z := 0) (Int.zero_ediv _), value_eq hF hok hc,
    Int.mul_ediv_cancel_left]
  · rfl
  · simpa [mzOk] using hmz

theorem valueSum_eq (Z : ℕ → ℤ) (K : ℕ) {c : ℕ} (hc : c < ExactBasis.dim κ) : ∀ τ : Tuple,
    (∀ jw ∈ τ, (F.tf jw.1).ok = true ∧ F.mzOk Z jw.1 = true) →
      (F.valueSum Z K τ).getD c 0 = F.sumAt (fun i ↦ Z i) K c τ
  | [] => fun _ ↦ by simp [valueSum, sumAt]
  | (j, w) :: τ => fun h ↦ by
    obtain ⟨hok, hmz⟩ := h (j, w) List.mem_cons_self
    rw [valueSum, getD_zipD (z := (0 : ℤ)) (f := (· + ·)) (by simp),
      getD_map_of_eq (f := fun v : ℤ ↦ w * F.D ^ (K - (F.tf j).m) * v) (z := 0) (mul_zero _),
      val_eq hF hok hmz hc,
      valueSum_eq Z K hc τ fun jw hjw ↦ h jw (List.mem_cons_of_mem _ hjw), sumAt, Int.cast_id]

/-- The packed numeral of coordinate `c` of a tuple on the box `(C, H)` at digit size `B`
satisfies the invariant of the engine, and its slot polynomial is the tuple's polynomial at the
box inputs. -/
theorem numerals_spec {C H : List ℤ} {K B c : ℕ} {τ : Tuple} (hB : 0 < B)
    (hsh : F.shape.length ≤ F.n) (hc : c < ExactBasis.dim κ)
    (hok : ∀ jw ∈ τ, (F.tf jw.1).ok = true ∧ F.rmOk C H jw.1 = true ∧
      F.mzOk (F.point C H B) jw.1 = true)
    (hnb : F.normSum C H K τ < 2 ^ (B - 1)) :
    Lay.Inv B F.shape ((F.numerals B (F.valueSum (F.point C H B) K τ)).getD c 0) ∧
      ∀ y : ℕ → ℝ, Lay.pv F.shape (Lay.cf B ((F.numerals B
          (F.valueSum (F.point C H B) K τ)).getD c 0)) y =
        F.sumAt (fun i ↦ boxEnv F.n C H F.D (fun i ↦ y i) i) K c τ := by
  obtain ⟨hfit, hnorm, hv⟩ := box_packing_lt (F.sumExpr K c τ) (F.shape_sumExpr K c τ) C H F.D
    (normBound_sumExpr hF C H K hc τ fun jw hjw ↦ ⟨(hok jw hjw).1, (hok jw hjw).2.1⟩) B
  have hZ : (F.valueSum (F.point C H B) K τ).getD c 0 =
      (F.sumExpr K c τ).evalInt (boxPacked F.n F.shape B C H F.D) := by
    rw [valueSum_eq hF _ _ hc τ fun jw hjw ↦ ⟨(hok jw hjw).1, (hok jw hjw).2.2⟩,
      Expr.evalInt_eq, eval_sumExpr]
    congr 1
    funext i
    simp only [boxPacked, getD_range_map_append, i.2, ↓reduceIte, point]
  rw [numerals, Box.getD_range_map _ _ _ hc, hZ, hv]
  obtain ⟨hinv, hpv⟩ := Lay.inv_biased hsh hB hfit hnorm hnb
  refine ⟨hinv, fun y ↦ ?_⟩
  rw [hpv, Expr.eval_toDPoly, eval_sumExpr]
  simp only [eval_boxInputs]

/-- **Soundness of a tuple**: a tuple that the engine certifies on the frame box `b` has a
polynomial of the right sign at `D x` for every point `x` of the box. -/
theorem runTuple_sound {strict : Bool} {depth B : ℕ} {b : Box} (hden : 0 < b.den)
    (hC : F.C = b.centres F.n) (hH : F.H = b.widths F.n) (hD : F.D = 2 * b.den)
    (hsh : F.shape.length ≤ F.n) (hB : 0 < B) {τ : Tuple}
    (hok : ∀ jw ∈ τ, (F.tf jw.1).ok = true)
    (hnb : F.normSum F.C F.H (F.tupleK τ) τ < 2 ^ (B - 1))
    (h : F.runTuple strict depth B τ = true) {x : Fin F.n → ℝ} (hx : b.Mem F.n x) :
    Sign strict (∑ c ∈ Finset.range (ExactBasis.dim κ),
      ExactBasis.basis κ c * F.sumAt (fun i ↦ (F.D : ℝ) * x i) (F.tupleK τ) c τ) := by
  simp only [runTuple, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hall, hrun⟩ := h
  have hspec : ∀ c < ExactBasis.dim κ, _ := fun c hc ↦ numerals_spec hF hB hsh hc
    (fun jw hjw ↦ ⟨hok jw hjw, (hall jw hjw).1, (hall jw hjw).2⟩) hnb
  have hinv : ∀ N ∈ F.numerals B (F.valueSum (F.point F.C F.H B) (F.tupleK τ) τ),
      Lay.Inv B F.shape N := by
    intro N hN
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hN
    have := (hspec c (List.mem_range.mp hc)).1
    rwa [numerals, Box.getD_range_map _ _ _ (List.mem_range.mp hc)] at this
  choose y hy hyx using fun i : Fin F.n ↦ Box.exists_centred hden (hx i)
  set y' : ℕ → ℝ := fun k ↦ if h : k < F.n then y ⟨k, h⟩ else 0
  have hy' : ∀ k, |y' k| ≤ 1 := fun k ↦ by
    simp only [y']
    split_ifs
    · exact hy _
    · simp
  have hE : (fun i : Fin F.n ↦ boxEnv F.n F.C F.H F.D (fun i ↦ y' i) i) =
      fun i ↦ (F.D : ℝ) * x i := by
    funext i
    simp only [boxEnv, i.2, ↓reduceDIte, y', hC, hH, hD, Box.centres, Box.widths,
      Box.getD_range_map _ _ _ i.2]
    have := hyx i
    push_cast at this ⊢
    linear_combination this
  have hs := Lay.runDiv_sound hB hsh depth F.W F.divisors hinv (F.length_numerals _ _) hrun y' hy'
  unfold Lay.val at hs
  refine (congrArg (Sign strict) (Finset.sum_congr rfl fun c hc ↦ ?_)).mp hs
  rw [(hspec c (Finset.mem_range.mp hc)).2 y', hE]

end Sound

theorem sumAt_eq_sum (z : Fin F.n → ℝ) (K : ℕ) (τ : Tuple) :
    ∑ c ∈ Finset.range (ExactBasis.dim κ), ExactBasis.basis κ c * F.sumAt z K c τ =
      (τ.map fun jw ↦ (jw.2 : ℝ) * ((F.D : ℝ) ^ (K - (F.tf jw.1).m) *
        ∑ c ∈ Finset.range (ExactBasis.dim κ),
          ExactBasis.basis κ c * eval F.n (F.q jw.1 c) z)).sum := by
  induction τ with
  | nil => simp [sumAt]
  | cons a τ ih =>
    obtain ⟨j, w⟩ := a
    rw [List.map_cons, List.sum_cons, ← ih]
    simp only [sumAt, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    push_cast
    ring

/-! #### Compiled checks

The parts of `runTuple` and `bits` with the term frames, the shape, the bounds, the monomial
checks and the values given as arguments, so that compiled code computes them once
(`Pull.checkMemo`). -/

/-- `normSum` with the term frames `tf` and the bounds `nb` given. -/
def normSumW (tf : ℕ → TermFrame) (nb : ℕ → ℕ) (K : ℕ) : Tuple → ℕ
  | [] => 0
  | (j, w) :: τ => w.natAbs * F.D.natAbs ^ (K - (tf j).m) * nb j + normSumW tf nb K τ

theorem normSumW_eq (C H : List ℤ) (K : ℕ) :
    ∀ τ, F.normSumW F.tf (F.nb C H) K τ = F.normSum C H K τ
  | [] => rfl
  | (j, w) :: τ => by rw [normSumW, normSum, normSumW_eq C H K τ]

/-- `tupleK` with the term frames `tf` given. -/
def tupleKW (tf : ℕ → TermFrame) (τ : Tuple) : ℕ := τ.foldr (fun jw K ↦ max (tf jw.1).m K) 0

/-- `bits` with the shape, the term frames and the bounds given. -/
def bitsW (shape : List ℕ) (tf : ℕ → TermFrame) (nb : ℕ → ℕ) (depth : ℕ) (τs : List Tuple) : ℕ :=
  Lay.digitsFor (τs.foldr (fun τ a ↦ max (F.normSumW tf nb (tupleKW tf τ) τ) a) 0)
    (Lay.room (Lay.apxBits κ) F.n shape true true depth F.W)

theorem bitsW_eq (depth : ℕ) (τs : List Tuple) :
    F.bitsW F.shape F.tf (F.nb F.C F.H) depth τs = F.bits depth τs := by
  simp only [bitsW, normSumW_eq]
  rfl

/-- `valueSum` with the term frames `tf` and the values `val` given. -/
def valueSumW (tf : ℕ → TermFrame) (val : ℕ → List ℤ) (K : ℕ) : Tuple → List ℤ
  | [] => []
  | (j, w) :: τ =>
    zipD 0 (· + ·) ((val j).map ((w * F.D ^ (K - (tf j).m)) * ·)) (valueSumW tf val K τ)

theorem valueSumW_eq (Z : ℕ → ℤ) (K : ℕ) :
    ∀ τ, F.valueSumW F.tf (F.val Z) K τ = F.valueSum Z K τ
  | [] => rfl
  | (j, w) :: τ => by rw [valueSumW, valueSum, valueSumW_eq Z K τ]

/-- `point` with the shape given. -/
def pointW (shape : List ℕ) (C H : List ℤ) (B i : ℕ) : ℤ :=
  C.getD i 0 + H.getD i 0 * packPoint' shape B i

/-- `runTuple` with the shape, the term frames, the monomial checks and the values given. -/
def runTupleW (shape : List ℕ) (tf : ℕ → TermFrame) (rm mz : ℕ → Bool) (val : ℕ → List ℤ)
    (strict : Bool) (depth B : ℕ) (τ : Tuple) : Bool :=
  τ.all (fun jw ↦ rm jw.1 && mz jw.1) &&
    Lay.runDiv κ F.n shape B strict true true depth F.W F.divisors
      ((List.range (ExactBasis.dim κ)).map fun c ↦
        ((F.valueSumW tf val (tupleKW tf τ) τ).getD c 0 + offset F.n shape B).toNat)

theorem runTupleW_eq (strict : Bool) (depth B : ℕ) :
    F.runTupleW F.shape F.tf (F.rmOk F.C F.H) (F.mzOk (F.point F.C F.H B))
      (F.val (F.point F.C F.H B)) strict depth B = F.runTuple strict depth B := by
  funext τ
  simp only [runTupleW, valueSumW_eq]
  rfl

/-- The term frames of all terms, as data. -/
def termFrames : Array TermFrame := (F.ts.map fun t ↦ termFrame F.n t F.C F.H F.D).toArray

theorem look_termFrames : look F.termFrames F.tf = F.tf := by
  refine look_eq fun j hj ↦ ?_
  simp only [termFrames, List.getElem_toArray, List.getElem_map, tf, term]
  rw [List.getD_eq_getElem]

theorem shapeMax_termFrames : shapeMax (F.termFrames.toList.map (·.sh)) = F.shape := by
  simp only [termFrames, List.toList_toArray, List.map_map, shape]
  rfl

/-- **`check` on the frame `F` as compiled code runs it** (`checkMemo_eq`): the term frames, the
shape, the quotient bounds, the packing point, and each term's monomial check and value at it,
are each computed once and passed on as data. -/
def checkMemo (den : ℕ) (strict : Bool) (depth : ℕ) (τs : List Tuple) : Bool :=
  let tfa := F.termFrames
  let shape := shapeMax (tfa.toList.map (·.sh))
  decide (0 < den) && decide (shape.length ≤ F.n) &&
    τs.all (fun τ ↦ τ.all fun jw ↦ (look tfa F.tf jw.1).ok) &&
    let nba := thunks F.ts.length (F.nb F.C F.H)
    let B := F.bitsW shape (look tfa F.tf) (lookT nba (F.nb F.C F.H)) depth τs
    let Za := Array.ofFn (n := F.n) fun i ↦ pointW shape F.C F.H B i
    let Z := look Za (F.point F.C F.H B)
    let mza := thunks F.ts.length (F.mzOk Z)
    let vala := thunks F.ts.length (F.val Z)
    τs.all (F.runTupleW shape (look tfa F.tf) (F.rmOk F.C F.H) (lookT mza (F.mzOk Z))
      (lookT vala (F.val Z)) strict depth B)

theorem checkMemo_eq (den : ℕ) (strict : Bool) (depth : ℕ) (τs : List Tuple) :
    F.checkMemo den strict depth τs = (decide (0 < den) && decide (F.shape.length ≤ F.n) &&
      τs.all (fun τ ↦ τ.all fun jw ↦ (F.tf jw.1).ok) &&
      τs.all (F.runTuple strict depth (F.bits depth τs))) := by
  have hZ (B : ℕ) : (Array.ofFn (n := F.n) fun i ↦ pointW F.shape F.C F.H B i) =
      Array.ofFn (n := F.n) fun i ↦ F.point F.C F.H B i := rfl
  simp only [checkMemo, shapeMax_termFrames, look_termFrames, lookT_thunks, bitsW_eq, hZ,
    look_ofFn, runTupleW_eq]

end Frame

/-- The frame of the box `b`: base `D = 2 b.den`, the engine widths `W`. -/
def frameOf (n : ℕ) (ts : List (Term κ)) (b : Box) (W : List ℤ) : Frame κ :=
  ⟨n, ts, b.centres n, b.widths n, 2 * b.den, W⟩

/-- **The engine widths of a bisection order** (rupert's `nonneg_exact_rec`: bisect the widest
coordinate, the last of equal ones, in rupert's coordinates). The order `o` lists rupert's
coordinates of positive width in rupert's order, each as `(i, w)`: the coordinate `i` of the box
and its width `w` over a common denominator. With these widths, `Lay.pickW true` picks the
coordinates rupert picks along `depth` bisections: the width `w` is scaled by `2^((depth + 1) m)`
for the `m` coordinates of the order, and the `r`-th coordinate of the order adds
`2^((depth + 1) r)`, which breaks ties towards the later coordinate and never reverses an
inequality between widths. Coordinates outside the order get width `0`, and the empty order keeps
the widths `H`. -/
def bisW (n depth : ℕ) (H : List ℤ) (o : List (ℕ × ℕ)) : List ℤ :=
  bif o.isEmpty then H else
    o.zipIdx.foldl (fun W x ↦ W.set x.1.1
      (x.1.2 * 2 ^ ((depth + 1) * o.length) + 2 ^ ((depth + 1) * x.2))) (List.replicate n 0)

/-- **The sign check of weighted combinations of pulled-back polynomials** on the box `b`, with
at most `depth` bisections along each branch, in the bisection order `o` (`bisW`; `check_sound`). -/
def check (n : ℕ) (ts : List (Term κ)) (strict : Bool) (depth : ℕ) (b : Box) (τs : List Tuple)
    (o : List (ℕ × ℕ) := []) : Bool :=
  let F := frameOf n ts b (bisW n depth (b.widths n) o)
  decide (0 < b.den) && decide (F.shape.length ≤ n) &&
    τs.all (fun τ ↦ τ.all fun jw ↦ (F.tf jw.1).ok) &&
    τs.all (F.runTuple strict depth (F.bits depth τs))

theorem den_pos_of_check {n : ℕ} {ts : List (Term κ)} {strict : Bool} {depth : ℕ} {b : Box}
    {τs : List Tuple} {o : List (ℕ × ℕ)} (h : check n ts strict depth b τs o = true) :
    0 < b.den := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

/-- **Soundness of the sign check.** At every point `x` of the box and for every checked tuple,
each term's polynomial is `c x^eⱼ sⱼ` with one `c > 0`, and `∑ wⱼ sⱼ` is positive (`strict`) or
nonnegative. -/
theorem check_sound {n : ℕ} {ts : List (Term κ)} {strict : Bool} {depth : ℕ} {b : Box}
    {τs : List Tuple} {o : List (ℕ × ℕ)} (h : check n ts strict depth b τs o = true) :
    ∀ τ ∈ τs, ∀ x : Fin n → ℝ, b.Mem n x → ∃ c : ℝ, 0 < c ∧ ∃ s : ℕ → ℝ,
      (∀ jw ∈ τ, (ts.getD jw.1 default).G.run Exact.re (ext n x) =
        c * monoVal n (ts.getD jw.1 default).e x * s jw.1) ∧
      Sign strict (τ.map fun jw ↦ (jw.2 : ℝ) * s jw.1).sum := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hden, hsh⟩, hok⟩, hc⟩ := h
  set F := frameOf n ts b (bisW n depth (b.widths n) o) with hFdef
  have hC : ∀ i, F.C.getD i 0 = if i < n then b.lo.getD i 0 + b.hi.getD i 0 else 0 := by
    intro i
    split_ifs with hi
    · exact Box.getD_range_map _ _ _ hi
    · exact List.getD_eq_default _ _ (by simp [F, frameOf, Box.centres]; omega)
  have hH : ∀ i, F.H.getD i 0 = if i < n then b.hi.getD i 0 - b.lo.getD i 0 else 0 := by
    intro i
    split_ifs with hi
    · exact Box.getD_range_map _ _ _ hi
    · exact List.getD_eq_default _ _ (by simp [F, frameOf, Box.widths]; omega)
  have hF : F.Valid := fun i hi ↦ by
    rw [hH] at hi
    split_ifs at hi with h₁
    · exact h₁
    · exact absurd rfl hi
  have hD : F.D = 2 * b.den := rfl
  have hD0 : (F.D : ℝ) ≠ 0 := by
    rw [hD]
    push_cast
    positivity
  intro τ hτ x hx
  have hsign := Frame.runTuple_sound hF hden rfl rfl hD hsh (Lay.digitsFor_pos _ _) (hok τ hτ)
    ((F.le_maxNorm hτ).trans_lt (Lay.le_digitsFor _ _)) (hc τ hτ) hx
  have hDpos : (0 : ℝ) < F.D := by
    rw [hD]
    push_cast
    positivity
  have hx' : ∀ i : Fin n, F.H.getD i 0 = 0 → (F.C.getD i 0 : ℝ) = F.D * x i := by
    intro i h0
    simp only [hH, i.2, ↓reduceIte] at h0
    simp only [hC, i.2, ↓reduceIte, hD]
    have hlh : b.hi.getD i 0 = b.lo.getD i 0 := by omega
    have hd : (0 : ℝ) < b.den := by exact_mod_cast hden
    obtain ⟨h₁, h₂⟩ := hx i
    rw [hlh] at h₂
    have hxi : x i = (b.lo.getD i 0 : ℝ) / b.den := le_antisymm h₂ h₁
    rw [hxi, hlh]
    push_cast
    field_simp
    ring
  refine ⟨((F.D : ℝ) ^ F.tupleK τ)⁻¹, by positivity,
    fun j ↦ (F.D : ℝ) ^ (F.tupleK τ - (F.tf j).m) * ∑ c ∈ Finset.range (ExactBasis.dim κ),
      ExactBasis.basis κ c * eval n (F.q j c) fun i ↦ (F.D : ℝ) * x i,
    fun jw hjw ↦ ?_, ?_⟩
  · have hrun := run_eq hF (hok τ hτ jw hjw)
      (fun i hi ↦ by
        have hn : F.n = n := rfl
        simp only [hC, show ¬i < n by omega, ↓reduceIte]) hD0 x hx'
    change (F.term jw.1).G.run Exact.re (ext F.n x) = _
    rw [hrun]
    change ((F.D : ℝ) ^ (F.tf jw.1).m)⁻¹ * monoVal n (F.term jw.1).e x *
      ∑ c ∈ Finset.range (ExactBasis.dim κ), ExactBasis.basis κ c * eval n (F.q jw.1 c) _ = _
    have hm := F.le_tupleK hjw
    have hpow : (F.D : ℝ) ^ F.tupleK τ =
        (F.D : ℝ) ^ (F.tupleK τ - (F.tf jw.1).m) * (F.D : ℝ) ^ (F.tf jw.1).m := by
      rw [← pow_add, Nat.sub_add_cancel hm]
    have h1 : (F.D : ℝ) ^ (F.tf jw.1).m ≠ 0 := pow_ne_zero _ hD0
    have h2 : (F.D : ℝ) ^ (F.tupleK τ - (F.tf jw.1).m) ≠ 0 := pow_ne_zero _ hD0
    rw [hpow]
    field_simp
    rfl
  · rw [Frame.sumAt_eq_sum] at hsign
    exact hsign

/-- `check` as compiled code runs it (`check_eq_checkMemo`): what the kernel shares between calls,
computed once (`Frame.checkMemo`). -/
def checkMemo (n : ℕ) (ts : List (Term κ)) (strict : Bool) (depth : ℕ) (b : Box)
    (τs : List Tuple) (o : List (ℕ × ℕ) := []) : Bool :=
  (frameOf n ts b (bisW n depth (b.widths n) o)).checkMemo b.den strict depth τs

@[csimp] theorem check_eq_checkMemo : @check = @checkMemo := by
  funext κ _ _ _ _ n ts strict depth b τs o
  rw [checkMemo, Frame.checkMemo_eq]
  rfl

/-! ### Combinations

The tuples of a combination are the choices of one term from every part (`combL`): their number
is the product of the parts' numbers of choices, up to millions on leaves of chart trees and
weighted zooms. Many choices of a part have the same quotient on the box (witness polynomials are
linear in each anchor), and tuples whose entries have the same weights and data on the frame give
the same run. `checkComb` is `check` on `combL` as compiled code runs it (`check_combL`): the
digit size from the choice of largest bound for each denominator degree of each part (the largest
bound over all tuples), and the engine once per tuple of representatives of the classes of choices
with equal weights, frames, monomial checks and values at the packing point. -/

/-- The weighted tuples of the parts `(i, js, c)`: one choice `j ∈ js` of every part, as the term
`i K + j` with weight `c σ i j` (`mem_combL`). -/
def combL (K : ℕ) (σ : ℕ → ℕ → ℤ) : List (ℕ × List ℕ × ℤ) → List Tuple
  | [] => [[]]
  | (i, js, c) :: ps => js.flatMap fun j ↦ (combL K σ ps).map fun τ ↦ (i * K + j, c * σ i j) :: τ

theorem mem_combL {K : ℕ} {σ : ℕ → ℕ → ℤ} : ∀ {ps : List (ℕ × List ℕ × ℤ)} {τ : Tuple},
    τ ∈ combL K σ ps ↔
      List.Forall₂ (fun p x ↦ ∃ j ∈ p.2.1, x = (p.1 * K + j, p.2.2 * σ p.1 j)) ps τ
  | [], τ => by simp [combL]
  | (i, js, c) :: ps, τ => by
    rw [combL, List.forall₂_cons_left_iff]
    simp only [List.mem_flatMap, List.mem_map, mem_combL]
    constructor
    · rintro ⟨j, hj, τ', hτ', rfl⟩
      exact ⟨_, τ', ⟨j, hj, rfl⟩, hτ', rfl⟩
    · rintro ⟨x, τ', ⟨j, hj, rfl⟩, hτ', rfl⟩
      exact ⟨j, hj, τ', hτ', rfl⟩

/-- The first element of every class: `j` is kept unless `r j' j` for a kept `j'` before it
(`firstReps_spec`). -/
def firstReps (r : ℕ → ℕ → Bool) : List ℕ → List ℕ → List ℕ
  | acc, [] => acc.reverse
  | acc, j :: l => bif acc.any (r · j) then firstReps r acc l else firstReps r (j :: acc) l

theorem mem_firstReps (r : ℕ → ℕ → Bool) :
    ∀ (acc l : List ℕ) {j : ℕ}, j ∈ firstReps r acc l → j ∈ acc ∨ j ∈ l
  | acc, [], j, h => Or.inl (List.mem_reverse.mp h)
  | acc, a :: l, j, h => by
    rw [firstReps] at h
    cases hc : acc.any (r · a)
    · rw [hc, Bool.cond_false] at h
      rcases mem_firstReps r (a :: acc) l h with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr List.mem_cons_self
        · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rw [hc, Bool.cond_true] at h
      rcases mem_firstReps r acc l h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem firstReps_spec (r : ℕ → ℕ → Bool) : ∀ (acc l : List ℕ),
    (∀ j ∈ acc, j ∈ firstReps r acc l) ∧
      ∀ j ∈ l, ∃ j' ∈ firstReps r acc l, j' = j ∨ r j' j = true
  | acc, [] => ⟨fun _ hj ↦ List.mem_reverse.mpr hj, fun _ h ↦ absurd h List.not_mem_nil⟩
  | acc, a :: l => by
    rw [firstReps]
    cases hc : acc.any (r · a)
    · rw [Bool.cond_false]
      obtain ⟨h₁, h₂⟩ := firstReps_spec r (a :: acc) l
      refine ⟨fun j hj ↦ h₁ j (List.mem_cons_of_mem _ hj), fun j hj ↦ ?_⟩
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ⟨j, h₁ j List.mem_cons_self, Or.inl rfl⟩
      · exact h₂ j hj
    · rw [Bool.cond_true]
      obtain ⟨h₁, h₂⟩ := firstReps_spec r acc l
      refine ⟨h₁, fun j hj ↦ ?_⟩
      rcases List.mem_cons.mp hj with rfl | hj
      · obtain ⟨j', hj', hr⟩ := List.any_eq_true.mp hc
        exact ⟨j', h₁ j' hj', Or.inr hr⟩
      · exact h₂ j hj

/-- Entry `x'` of a tuple is entry `x` with choice `j` of part `i` replaced by `j'`, where
`R i j' j`. -/
def RepEntry (K : ℕ) (σ : ℕ → ℕ → ℤ) (R : ℕ → ℕ → ℕ → Prop) (x' x : ℕ × ℤ) : Prop :=
  ∃ i j' j c, R i j' j ∧ x' = (i * K + j', c * σ i j') ∧ x = (i * K + j, c * σ i j)

section Reps

variable {K : ℕ} {σ : ℕ → ℕ → ℤ} (f : ℕ → List ℕ → List ℕ)

/-- The parts with the choices `f i js` instead of `js`. -/
def repParts (ps : List (ℕ × List ℕ × ℤ)) : List (ℕ × List ℕ × ℤ) :=
  ps.map fun p ↦ (p.1, f p.1 p.2.1, p.2.2)

theorem mem_combL_of_repParts (hf : ∀ i js, ∀ j ∈ f i js, j ∈ js) {ps : List (ℕ × List ℕ × ℤ)}
    {τ : Tuple} (h : τ ∈ combL K σ (repParts f ps)) : τ ∈ combL K σ ps := by
  rw [mem_combL, repParts, List.forall₂_map_left_iff] at h
  rw [mem_combL]
  exact h.imp fun p x ⟨j, hj, hx⟩ ↦ ⟨j, hf _ _ j hj, hx⟩

theorem exists_combL_repParts (R : ℕ → ℕ → ℕ → Prop)
    (hf : ∀ i js, ∀ j ∈ js, ∃ j' ∈ f i js, R i j' j) :
    ∀ {ps : List (ℕ × List ℕ × ℤ)} {τ : Tuple}, τ ∈ combL K σ ps →
      ∃ τ' ∈ combL K σ (repParts f ps), List.Forall₂ (RepEntry K σ R) τ' τ
  | [], τ, h => by
    rw [mem_combL, List.forall₂_nil_left_iff] at h
    subst h
    exact ⟨[], by simp [repParts, combL], List.Forall₂.nil⟩
  | (i, js, c) :: ps, τ, h => by
    rw [mem_combL, List.forall₂_cons_left_iff] at h
    obtain ⟨x, τ₀, ⟨j, hj, rfl⟩, hτ₀, rfl⟩ := h
    obtain ⟨τ₀', hτ₀', hrel⟩ := exists_combL_repParts R hf (mem_combL.mpr hτ₀)
    obtain ⟨j', hj', hR⟩ := hf i js j hj
    refine ⟨(i * K + j', c * σ i j') :: τ₀', ?_, List.Forall₂.cons ⟨i, j', j, c, hR, rfl, rfl⟩ hrel⟩
    rw [repParts, List.map_cons, mem_combL, List.forall₂_cons_left_iff]
    exact ⟨_, τ₀', ⟨j', hj', rfl⟩, mem_combL.mp hτ₀', rfl⟩

theorem all_combL_repParts (R : ℕ → ℕ → ℕ → Prop) (hsub : ∀ i js, ∀ j ∈ f i js, j ∈ js)
    (hf : ∀ i js, ∀ j ∈ js, ∃ j' ∈ f i js, R i j' j) (P : Tuple → Bool)
    (hP : ∀ τ' τ, List.Forall₂ (RepEntry K σ R) τ' τ → P τ' = P τ) (ps : List (ℕ × List ℕ × ℤ)) :
    (combL K σ ps).all P = (combL K σ (repParts f ps)).all P := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  refine ⟨fun h τ' hτ' ↦ h τ' (mem_combL_of_repParts f hsub hτ'), fun h τ hτ ↦ ?_⟩
  obtain ⟨τ', hτ', hrel⟩ := exists_combL_repParts f R hf hτ
  rw [← hP τ' τ hrel]
  exact h τ' hτ'

theorem le_foldr_max_of_mem (g : Tuple → ℕ) {L : List Tuple} {τ : Tuple} (h : τ ∈ L) :
    g τ ≤ L.foldr (fun τ a ↦ max (g τ) a) 0 := by
  induction L with
  | nil => cases h
  | cons b L ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem foldr_max_le (g : Tuple → ℕ) {L : List Tuple} {M : ℕ} (h : ∀ τ ∈ L, g τ ≤ M) :
    L.foldr (fun τ a ↦ max (g τ) a) 0 ≤ M := by
  induction L with
  | nil => exact Nat.zero_le _
  | cons b L ih =>
    exact max_le (h b List.mem_cons_self) (ih fun τ hτ ↦ h τ (List.mem_cons_of_mem _ hτ))

theorem foldr_max_combL_repParts (R : ℕ → ℕ → ℕ → Prop) (hsub : ∀ i js, ∀ j ∈ f i js, j ∈ js)
    (hf : ∀ i js, ∀ j ∈ js, ∃ j' ∈ f i js, R i j' j) (g : Tuple → ℕ)
    (hg : ∀ τ' τ, List.Forall₂ (RepEntry K σ R) τ' τ → g τ ≤ g τ') (ps : List (ℕ × List ℕ × ℤ)) :
    (combL K σ ps).foldr (fun τ a ↦ max (g τ) a) 0 =
      (combL K σ (repParts f ps)).foldr (fun τ a ↦ max (g τ) a) 0 := by
  refine le_antisymm (foldr_max_le g fun τ hτ ↦ ?_) (foldr_max_le g fun τ' hτ' ↦
    le_foldr_max_of_mem g (mem_combL_of_repParts f hsub hτ'))
  obtain ⟨τ', hτ', hrel⟩ := exists_combL_repParts f R hf hτ
  exact (hg τ' τ hrel).trans (le_foldr_max_of_mem g hτ')

theorem all_combL_firstReps (r : ℕ → ℕ → ℕ → Bool) (P : Tuple → Bool)
    (hP : ∀ τ' τ, List.Forall₂ (RepEntry K σ fun i j' j ↦ j' = j ∨ r i j' j = true) τ' τ →
      P τ' = P τ) (ps : List (ℕ × List ℕ × ℤ)) :
    (combL K σ ps).all P =
      (combL K σ (repParts (fun i js ↦ firstReps (r i) [] js) ps)).all P :=
  all_combL_repParts (fun i js ↦ firstReps (r i) [] js) (fun i j' j ↦ j' = j ∨ r i j' j = true)
    (fun _ _ _ hj ↦ (mem_firstReps _ [] _ hj).resolve_left List.not_mem_nil)
    (fun _ _ j hj ↦ (firstReps_spec _ [] _).2 j hj) P hP ps

end Reps

theorem all_congr_forall₂ {α β : Type*} {g : α → Bool} {g' : β → Bool} {l : List α}
    {l' : List β} (h : List.Forall₂ (fun a b ↦ g a = g' b) l l') : l.all g = l'.all g' := by
  induction h with
  | nil => rfl
  | cons h _ ih => rw [List.all_cons, List.all_cons, h, ih]

namespace Frame

variable (F : Frame κ)

theorem tupleK_congr {τ' τ : Tuple}
    (h : List.Forall₂ (fun x' x ↦ (F.tf x'.1).m = (F.tf x.1).m) τ' τ) :
    F.tupleK τ' = F.tupleK τ := by
  induction h with
  | nil => rfl
  | cons h _ ih =>
    simp only [tupleK, List.foldr_cons] at ih ⊢
    rw [h, ih]

theorem valueSum_congr (Z : ℕ → ℤ) (K : ℕ) {τ' τ : Tuple}
    (h : List.Forall₂ (fun x' x ↦ x'.2 = x.2 ∧ F.val Z x'.1 = F.val Z x.1 ∧
      (F.tf x'.1).m = (F.tf x.1).m) τ' τ) :
    F.valueSum Z K τ' = F.valueSum Z K τ := by
  induction h with
  | nil => rfl
  | @cons x' x τ' τ h _ ih =>
    obtain ⟨j', w'⟩ := x'
    obtain ⟨j, w⟩ := x
    obtain ⟨hw, hv, hm⟩ := h
    simp only at hw hv hm
    rw [valueSum, valueSum, hw, hv, hm, ih]

theorem normSum_le_congr (C H : List ℤ) (K : ℕ) {τ' τ : Tuple}
    (h : List.Forall₂ (fun x' x ↦ (F.tf x'.1).m = (F.tf x.1).m ∧
      x.2.natAbs * F.nb C H x.1 ≤ x'.2.natAbs * F.nb C H x'.1) τ' τ) :
    F.normSum C H K τ ≤ F.normSum C H K τ' := by
  induction h with
  | nil => exact le_rfl
  | @cons x' x τ' τ h _ ih =>
    obtain ⟨j', w'⟩ := x'
    obtain ⟨j, w⟩ := x
    obtain ⟨hm, hle⟩ := h
    simp only at hm hle
    rw [normSum, normSum, hm]
    have : w.natAbs * F.D.natAbs ^ (K - (F.tf j).m) * F.nb C H j ≤
        w'.natAbs * F.D.natAbs ^ (K - (F.tf j).m) * F.nb C H j' := by
      rw [Nat.mul_right_comm w.natAbs, Nat.mul_right_comm w'.natAbs]
      exact Nat.mul_le_mul_right _ hle
    exact Nat.add_le_add this ih

theorem runTuple_congr (strict : Bool) (depth B : ℕ) {τ' τ : Tuple}
    (h : List.Forall₂ (fun x' x ↦ x'.2 = x.2 ∧ F.rmOk F.C F.H x'.1 = F.rmOk F.C F.H x.1 ∧
      F.mzOk (F.point F.C F.H B) x'.1 = F.mzOk (F.point F.C F.H B) x.1 ∧
      F.val (F.point F.C F.H B) x'.1 = F.val (F.point F.C F.H B) x.1 ∧
      (F.tf x'.1).m = (F.tf x.1).m) τ' τ) :
    F.runTuple strict depth B τ' = F.runTuple strict depth B τ := by
  rw [runTuple, runTuple, tupleK_congr F (h.imp fun _ _ h ↦ h.2.2.2.2),
    valueSum_congr F (F.point F.C F.H B) (F.tupleK τ)
      (h.imp fun _ _ h ↦ ⟨h.1, h.2.2.2.1, h.2.2.2.2⟩),
    all_congr_forall₂ (g := fun jw ↦ F.rmOk F.C F.H jw.1 && F.mzOk (F.point F.C F.H B) jw.1)
      (g' := fun jw ↦ F.rmOk F.C F.H jw.1 && F.mzOk (F.point F.C F.H B) jw.1)
      (h.imp fun _ _ h ↦ by simp only [h.2.1, h.2.2.1])]

/-- Choices `j'` and `j` of part `i` have the same weight factor, frame, monomial checks and
values (the term data `tf`, `rm`, `mz`, `val`). -/
def sameData (K : ℕ) (σ : ℕ → ℕ → ℤ) (tf : ℕ → TermFrame) (rm mz : ℕ → Bool)
    (val : ℕ → List ℤ) (i j' j : ℕ) : Bool :=
  σ i j' == σ i j && (tf (i * K + j')).ok == (tf (i * K + j)).ok &&
    (tf (i * K + j')).m == (tf (i * K + j)).m && rm (i * K + j') == rm (i * K + j) &&
    mz (i * K + j') == mz (i * K + j) && val (i * K + j') == val (i * K + j)

/-- Choice `j'` of part `i` has the denominator degree of choice `j` and at least its bound
`|σ i j| nb (i K + j)`. -/
def bigger (K : ℕ) (σ : ℕ → ℕ → ℤ) (tf : ℕ → TermFrame) (nb : ℕ → ℕ) (i j' j : ℕ) : Bool :=
  (tf (i * K + j')).m == (tf (i * K + j)).m &&
    decide ((σ i j).natAbs * nb (i * K + j) ≤ (σ i j').natAbs * nb (i * K + j'))

/-- The choices `js` of part `i` sorted by decreasing bound `|σ i j| nb (i K + j)`. -/
def byBound (K : ℕ) (σ : ℕ → ℕ → ℤ) (nb : ℕ → ℕ) (i : ℕ) (js : List ℕ) : List ℕ :=
  js.mergeSort fun j j' ↦ decide ((σ i j').natAbs * nb (i * K + j') ≤
    (σ i j).natAbs * nb (i * K + j))

/-- **`check` on the tuples `combL K σ ps` as compiled code runs it** (`checkComb_eq`): as
`checkMemo`, with the digit size from the tuples of the choices of largest bound for each
denominator degree of each part, and the tuples of the first choices of each part's classes of
equal data (`sameData`) only. -/
def checkComb (den : ℕ) (strict : Bool) (depth K : ℕ) (σ : ℕ → ℕ → ℤ)
    (ps : List (ℕ × List ℕ × ℤ)) : Bool :=
  let tfa := F.termFrames
  let shape := shapeMax (tfa.toList.map (·.sh))
  let tf := look tfa F.tf
  let nba := thunks F.ts.length (F.nb F.C F.H)
  let nb := lookT nba (F.nb F.C F.H)
  let B := F.bitsW shape tf nb depth (combL K σ (repParts (fun i js ↦
    firstReps (bigger K σ tf nb i) [] (byBound K σ nb i js)) ps))
  let Za := Array.ofFn (n := F.n) fun i ↦ pointW shape F.C F.H B i
  let Z := look Za (F.point F.C F.H B)
  let mza := thunks F.ts.length (F.mzOk Z)
  let vala := thunks F.ts.length (F.val Z)
  let mz := lookT mza (F.mzOk Z)
  let val := lookT vala (F.val Z)
  let τs := combL K σ (repParts (fun i js ↦
    firstReps (sameData K σ tf (F.rmOk F.C F.H) mz val i) [] js) ps)
  decide (0 < den) && decide (shape.length ≤ F.n) &&
    τs.all (fun τ ↦ τ.all fun jw ↦ (tf jw.1).ok) &&
    τs.all (F.runTupleW shape tf (F.rmOk F.C F.H) mz val strict depth B)

theorem sameData_rep {K : ℕ} {σ : ℕ → ℕ → ℤ} {tf : ℕ → TermFrame} {rm mz : ℕ → Bool}
    {val : ℕ → List ℤ} {x' x : ℕ × ℤ}
    (h : RepEntry K σ (fun i j' j ↦ j' = j ∨ sameData K σ tf rm mz val i j' j = true) x' x) :
    x'.2 = x.2 ∧ (tf x'.1).ok = (tf x.1).ok ∧ (tf x'.1).m = (tf x.1).m ∧ rm x'.1 = rm x.1 ∧
      mz x'.1 = mz x.1 ∧ val x'.1 = val x.1 := by
  obtain ⟨i, j', j, c, hR, rfl, rfl⟩ := h
  rcases hR with rfl | hR
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [sameData, Bool.and_eq_true, beq_iff_eq] at hR
    obtain ⟨⟨⟨⟨⟨hσ, hok⟩, hm⟩, hrm⟩, hmz⟩, hv⟩ := hR
    exact ⟨by rw [hσ], hok, hm, hrm, hmz, hv⟩

theorem bigger_rep {K : ℕ} {σ : ℕ → ℕ → ℤ} {tf : ℕ → TermFrame} {nb : ℕ → ℕ} {x' x : ℕ × ℤ}
    (h : RepEntry K σ (fun i j' j ↦ j' = j ∨ bigger K σ tf nb i j' j = true) x' x) :
    (tf x'.1).m = (tf x.1).m ∧ x.2.natAbs * nb x.1 ≤ x'.2.natAbs * nb x'.1 := by
  obtain ⟨i, j', j, c, hR, rfl, rfl⟩ := h
  rcases hR with rfl | hR
  · exact ⟨rfl, le_rfl⟩
  · simp only [bigger, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hR
    refine ⟨hR.1, ?_⟩
    simp only [Int.natAbs_mul, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ hR.2

theorem checkComb_eq (den : ℕ) (strict : Bool) (depth K : ℕ) (σ : ℕ → ℕ → ℤ)
    (ps : List (ℕ × List ℕ × ℤ)) :
    F.checkComb den strict depth K σ ps = (decide (0 < den) && decide (F.shape.length ≤ F.n) &&
      (combL K σ ps).all (fun τ ↦ τ.all fun jw ↦ (F.tf jw.1).ok) &&
      (combL K σ ps).all (F.runTuple strict depth (F.bits depth (combL K σ ps)))) := by
  have hZ (B : ℕ) : (Array.ofFn (n := F.n) fun i ↦ pointW F.shape F.C F.H B i) =
      Array.ofFn (n := F.n) fun i ↦ F.point F.C F.H B i := rfl
  simp only [checkComb, shapeMax_termFrames, look_termFrames, lookT_thunks, bitsW_eq, hZ,
    look_ofFn, runTupleW_eq]
  -- The digit size: the largest bound is that of the tuples of the largest choices.
  have hB : F.bits depth (combL K σ (repParts (fun i js ↦
      firstReps (bigger K σ F.tf (F.nb F.C F.H) i) [] (byBound K σ (F.nb F.C F.H) i js)) ps)) =
      F.bits depth (combL K σ ps) := by
    simp only [bits, maxNorm]
    congr 1
    refine (foldr_max_combL_repParts (fun i js ↦
      firstReps (bigger K σ F.tf (F.nb F.C F.H) i) [] (byBound K σ (F.nb F.C F.H) i js))
      (fun i j' j ↦ j' = j ∨ bigger K σ F.tf (F.nb F.C F.H) i j' j = true)
      (fun i js j hj ↦ List.mem_mergeSort.mp
        ((mem_firstReps _ [] _ hj).resolve_left List.not_mem_nil))
      (fun i js j hj ↦ (firstReps_spec _ [] _).2 j (List.mem_mergeSort.mpr hj))
      (fun τ ↦ F.normSum F.C F.H (F.tupleK τ) τ) (fun τ' τ h ↦ ?_) ps).symm
    rw [F.tupleK_congr (h.imp fun _ _ h ↦ (bigger_rep h).1)]
    exact F.normSum_le_congr _ _ _ (h.imp fun _ _ h ↦ bigger_rep h)
  rw [hB]
  -- The runs: tuples of representatives have the same data.
  rw [← all_combL_firstReps (sameData K σ F.tf (F.rmOk F.C F.H)
      (F.mzOk (F.point F.C F.H (F.bits depth (combL K σ ps))))
      (F.val (F.point F.C F.H (F.bits depth (combL K σ ps)))))
      (fun τ ↦ τ.all fun jw ↦ (F.tf jw.1).ok)
      (fun τ' τ h ↦ all_congr_forall₂ (h.imp fun _ _ h ↦ (sameData_rep h).2.1)) ps,
    ← all_combL_firstReps (sameData K σ F.tf (F.rmOk F.C F.H)
      (F.mzOk (F.point F.C F.H (F.bits depth (combL K σ ps))))
      (F.val (F.point F.C F.H (F.bits depth (combL K σ ps)))))
      (F.runTuple strict depth (F.bits depth (combL K σ ps)))
      (fun τ' τ h ↦ F.runTuple_congr strict depth _ (h.imp fun _ _ h ↦
        have h := sameData_rep h
        ⟨h.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, h.2.2.1⟩)) ps]

/-- `runTupleW` with the engine's masks `m` and the offset `O` given, built once per leaf
(`Lay.masks`, `runTupleWP_eq`), and beat lines (`Modules/Check/Leaf/Progress.lean`): after the tuple's
numerals (`vals`), after each dominance test (`dom`, with the tuple and the boxes tested,
`Lay.runDivMC`) and after its sign check (`engine`). -/
def runTupleWP (m : Lay.Masks) (O : ℕ) (shape : List ℕ) (tf : ℕ → TermFrame) (rm mz : ℕ → Bool)
    (val : ℕ → List ℤ) (strict : Bool) (depth B i n : ℕ) (τ : Tuple) : Bool :=
  τ.all (fun jw ↦ rm jw.1 && mz jw.1) &&
    beat "engine" (fun r ↦ s!" i={i} n={n} ok={r}") (Lay.runDivMC κ i m F.n shape B strict true
      true depth F.W F.divisors (beat "vals" (fun _ ↦ s!" i={i} n={n}")
        ((List.range (ExactBasis.dim κ)).map fun c ↦
          ((F.valueSumW tf val (tupleKW tf τ) τ).getD c 0 + O).toNat)))

theorem runTupleWP_eq (shape : List ℕ) (tf : ℕ → TermFrame) (rm mz : ℕ → Bool)
    (val : ℕ → List ℤ) (strict : Bool) (depth B i n : ℕ) :
    F.runTupleWP (Lay.masks B shape) (offset F.n shape B) shape tf rm mz val strict depth B i n =
      F.runTupleW shape tf rm mz val strict depth B := by
  funext τ
  simp only [runTupleWP, runTupleW, beat_eq, Lay.runDivMC_eq, Lay.runDivM_masks]

/-- A list of naturals as `a,b,…` (a key of a progress line). -/
def csv (l : List ℕ) : String := ",".intercalate (l.map toString)

/-- `checkComb` as compiled code runs it (`checkComb_eq_checkCombP`): with stage lines
(`Modules/Check/Leaf/Progress.lean`) after the term frames (`masks`), the packing (`bits`) and the
tuples (`tuples`), a beat after each term's frame (`mask`) and value (`val`), and the beats of
each tuple (`runTupleWP`, with the engine's masks and the offset built once). -/
def checkCombP (den : ℕ) (strict : Bool) (depth K : ℕ) (σ : ℕ → ℕ → ℤ)
    (ps : List (ℕ × List ℕ × ℤ)) : Bool :=
  let tfa := stage "masks" (fun a ↦ s!" terms={a.size}") (mapIdxP (fun j t ↦
    beat "mask" (fun f ↦ s!" i={j} n={F.ts.length} shape={csv f.sh}")
      (termFrame F.n t F.C F.H F.D)) 0 F.ts).toArray
  let shape := shapeMax (tfa.toList.map (·.sh))
  let tf := look tfa F.tf
  let nba := thunks F.ts.length (F.nb F.C F.H)
  let nb := lookT nba (F.nb F.C F.H)
  let B := stage "bits" (fun B ↦ s!" slots={DPoly.slots shape} B={B} " ++
      s!"bits={B * DPoly.slots shape} terms={F.ts.length} shape={csv shape}")
    (F.bitsW shape tf nb depth (combL K σ (repParts (fun i js ↦
      firstReps (bigger K σ tf nb i) [] (byBound K σ nb i js)) ps)))
  let Za := Array.ofFn (n := F.n) fun i ↦ pointW shape F.C F.H B i
  let Z := look Za (F.point F.C F.H B)
  let mza := thunks F.ts.length (F.mzOk Z)
  let vala := thunks F.ts.length fun j ↦ beat "val" (fun _ ↦ s!" i={j} n={F.ts.length}") (F.val Z j)
  let mz := lookT mza (F.mzOk Z)
  let val := lookT vala (F.val Z)
  let τs := stage "tuples" (fun τs ↦ s!" tuples={τs.length}") (combL K σ (repParts (fun i js ↦
    firstReps (sameData K σ tf (F.rmOk F.C F.H) mz val i) [] js) ps))
  let mT := Thunk.mk fun _ ↦ Lay.masks B shape
  let OT := Thunk.mk fun _ ↦ offset F.n shape B
  decide (0 < den) && decide (shape.length ≤ F.n) &&
    τs.all (fun τ ↦ τ.all fun jw ↦ (tf jw.1).ok) &&
    allIdx (fun i ↦ F.runTupleWP mT.get OT.get shape tf (F.rmOk F.C F.H) mz val strict depth B i
      τs.length) 0 τs

@[csimp] theorem checkComb_eq_checkCombP : @checkComb = @checkCombP := by
  funext κ _ _ _ _ F den strict depth K σ ps
  simp only [checkComb, checkCombP, stage_eq, beat_eq, Lay.thunk_get_mk, runTupleWP_eq, allIdx_eq,
    mapIdxP_eq]
  rfl

end Frame

/-- `check` on the tuples `combL K σ ps` as compiled code runs it (`check_combL`). -/
def checkComb (n : ℕ) (ts : List (Term κ)) (strict : Bool) (depth : ℕ) (b : Box) (K : ℕ)
    (σ : ℕ → ℕ → ℤ) (ps : List (ℕ × List ℕ × ℤ)) (o : List (ℕ × ℕ) := []) : Bool :=
  (frameOf n ts b (bisW n depth (b.widths n) o)).checkComb b.den strict depth K σ ps

theorem check_combL (n : ℕ) (ts : List (Term κ)) (strict : Bool) (depth : ℕ) (b : Box) (K : ℕ)
    (σ : ℕ → ℕ → ℤ) (ps : List (ℕ × List ℕ × ℤ)) (o : List (ℕ × ℕ)) :
    check n ts strict depth b (combL K σ ps) o = checkComb n ts strict depth b K σ ps o := by
  rw [checkComb, Frame.checkComb_eq]
  rfl

end Pull

end Nieuwland.Check
