import Modules.Check.Sign.Engine
import Mathlib.Tactic.FieldSimp

/-!
# Signs on boxes, with bisection

`nonnegOn G n depth b` certifies that a computation `G` with constants in an exact type `κ`
(`GenPoly κ`) is nonnegative on the box `b` in its first `n` variables, with variable `n` as the
homogenising variable: it applies the centred-form bound and, where that fails, bisects the widest
coordinate, at most `depth` times along each branch. This is `nonneg_on_fbox` of
`code/src/proof/regional.rs`, in exact arithmetic. `posOn` is the strict version (`pos_on_fbox` of
`wzoom.rs`). Both are `signOn`; with `dom` they also try dominance at a vertex before bisecting
(`nonneg_on_fbox_exact`).

`G` is evaluated once in `κ`, at the packing point of the box inputs (`boxNumerals`): each
coordinate of the value is one numeral holding the coefficients of `y ↦ G(C + H y, D)` on
`[-1, 1]^n` in its digits. The packed engine (`Lay.run`, `Modules/Check/Sign/Engine.lean`) takes it
from there: bounds by digit operations, smaller boxes by substitutions in the numerals. The shape
and digit size come from runs of `G` in `ShapeL` and `AbsNat` over the coordinate ring
(`GenPoly.shapeOn`, `GenPoly.normOn`), with room for the growth along the bisections
(`Lay.room`); the kernel never builds the polynomial.

Boxes have integer endpoints over a common positive denominator. The conclusion is about `G` at
`(2 den x, 2 den)`, the scaled point of the whole box. For a computation homogeneous of some degree
in its `n + 1` variables (all witness polynomials are), this is the sign of `G` at `(x, 1)`
(`nonnegOn_hom`, `posOn_hom`); the bisections then decide as those of the Rust check, whose halves
have their own scaled points.
-/

namespace Nieuwland.Check

/-- A box `∏ᵢ [loᵢ / den, hiᵢ / den]` with integer endpoints over a common denominator. -/
structure Box where
  /-- Numerators of the lower ends. -/
  lo : List ℤ
  /-- Numerators of the upper ends. -/
  hi : List ℤ
  /-- The common denominator, positive. -/
  den : ℕ

/-- The homogeneous point `(d x, d)`: variable `i < n` is `d xᵢ`, variable `n` is `d`. -/
def homEnv {R : Type*} [CommRing R] (n : ℕ) (d : R) (x : Fin n → R) (i : ℕ) : R :=
  if h : i < n then d * x ⟨i, h⟩ else if i = n then d else 0

namespace Box

/-- `x` lies in the closed box (in its first `n` coordinates). -/
def Mem (b : Box) (n : ℕ) (x : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, (b.lo.getD i 0 : ℝ) / b.den ≤ x i ∧ x i ≤ (b.hi.getD i 0 : ℝ) / b.den

/-- The box of the coordinates from `k` on: the rotation coordinates of a chart box (`k = 2`), the
face coordinates of a polar piece (`k = 1`). -/
def drop (b : Box) (k : ℕ) : Box := ⟨b.lo.drop k, b.hi.drop k, b.den⟩

theorem mem_drop_two {b : Box} {y : Fin 5 → ℝ} (hy : b.Mem 5 y) :
    (b.drop 2).Mem 3 ![y 2, y 3, y 4] := by
  intro i
  have h := hy ⟨i + 2, by omega⟩
  simp only [drop, List.getD_eq_getElem?_getD, List.getElem?_drop] at h ⊢
  fin_cases i <;> simpa [add_comm] using h

theorem mem_drop_one {b : Box} {z : Fin 3 → ℝ} (hz : b.Mem 3 z) :
    (b.drop 1).Mem 2 ![z 1, z 2] := by
  intro i
  have h := hz ⟨i + 1, by omega⟩
  simp only [drop, List.getD_eq_getElem?_getD, List.getElem?_drop] at h ⊢
  fin_cases i <;> simpa [add_comm] using h

/-- Numerators of twice the centres. -/
def centres (b : Box) (n : ℕ) : List ℤ :=
  (List.range n).map fun i ↦ b.lo.getD i 0 + b.hi.getD i 0

/-- Numerators of the widths. -/
def widths (b : Box) (n : ℕ) : List ℤ :=
  (List.range n).map fun i ↦ b.hi.getD i 0 - b.lo.getD i 0

/-- The lower half along coordinate `k`, over the doubled denominator. -/
def lowerHalf (b : Box) (n k : ℕ) : Box where
  lo := (List.range n).map fun i ↦ 2 * b.lo.getD i 0
  hi := (List.range n).map fun i ↦
    if i = k then b.lo.getD i 0 + b.hi.getD i 0 else 2 * b.hi.getD i 0
  den := 2 * b.den

/-- The upper half along coordinate `k`, over the doubled denominator. -/
def upperHalf (b : Box) (n k : ℕ) : Box where
  lo := (List.range n).map fun i ↦
    if i = k then b.lo.getD i 0 + b.hi.getD i 0 else 2 * b.lo.getD i 0
  hi := (List.range n).map fun i ↦ 2 * b.hi.getD i 0
  den := 2 * b.den

theorem getD_range_map {α : Type*} (n : ℕ) (f : ℕ → α) (d : α) {i : ℕ} (h : i < n) :
    ((List.range n).map f).getD i d = f i := by
  simp [List.getD_eq_getElem?_getD, h]

theorem mem_lowerHalf_or_upperHalf {b : Box} {n : ℕ} (k : ℕ) (hden : 0 < b.den)
    {x : Fin n → ℝ} (hx : b.Mem n x) : (b.lowerHalf n k).Mem n x ∨ (b.upperHalf n k).Mem n x := by
  have hd : (0 : ℝ) < b.den := by exact_mod_cast hden
  have hd2 : ((2 * b.den : ℕ) : ℝ) = 2 * b.den := by push_cast; ring
  -- Away from coordinate `k`, both halves are the box itself.
  have hsame : ∀ (i : Fin n) (a : ℤ), ((2 * a : ℤ) : ℝ) / ((2 * b.den : ℕ) : ℝ) = (a : ℝ) / b.den :=
    fun i a ↦ by rw [hd2]; push_cast; field_simp
  by_cases hk : ∃ hk : k < n, x ⟨k, hk⟩ ≤ ((b.lo.getD k 0 + b.hi.getD k 0 : ℤ) : ℝ) / (2 * b.den)
  · left
    obtain ⟨hk, hxk⟩ := hk
    intro i
    simp only [lowerHalf, getD_range_map n _ _ i.2]
    refine ⟨by rw [hsame i]; exact (hx i).1, ?_⟩
    split_ifs with hi
    · have : i = ⟨k, hk⟩ := Fin.ext hi
      subst this
      rw [hd2]; exact hxk
    · rw [hsame i]; exact (hx i).2
  · right
    intro i
    simp only [upperHalf, getD_range_map n _ _ i.2]
    refine ⟨?_, by rw [hsame i]; exact (hx i).2⟩
    split_ifs with hi
    · simp only [not_exists, not_le] at hk
      have := hk (hi ▸ i.2)
      have hi' : (⟨k, hi ▸ i.2⟩ : Fin n) = i := Fin.ext hi.symm
      rw [hi'] at this
      rw [hd2, hi]; exact this.le
    · rw [hsame i]; exact (hx i).1

/-- A point of the box in centred coordinates: `(loᵢ + hiᵢ) + (hiᵢ - loᵢ) yᵢ = 2 den xᵢ` with
`|yᵢ| ≤ 1`. -/
theorem exists_centred {lo hi : ℤ} {den : ℕ} (hden : 0 < den) {x : ℝ}
    (hx : (lo : ℝ) / den ≤ x ∧ x ≤ (hi : ℝ) / den) :
    ∃ y : ℝ, |y| ≤ 1 ∧ ((lo + hi : ℤ) : ℝ) + ((hi - lo : ℤ) : ℝ) * y = 2 * den * x := by
  have hd : (0 : ℝ) < den := by exact_mod_cast hden
  have h₁ : (lo : ℝ) ≤ den * x := by rw [div_le_iff₀ hd] at hx; linarith [hx.1]
  have h₂ : den * x ≤ (hi : ℝ) := by rw [le_div_iff₀ hd] at hx; linarith [hx.2]
  rcases eq_or_lt_of_le (h₁.trans h₂) with heq | hlt
  · refine ⟨0, by simp, ?_⟩
    push_cast
    linarith
  · refine ⟨(2 * den * x - lo - hi) / (hi - lo), ?_, ?_⟩
    · rw [abs_le]
      have hpos : (0 : ℝ) < hi - lo := by linarith
      constructor
      · rw [le_div_iff₀ hpos]; linarith
      · rw [div_le_iff₀ hpos]; linarith
    · have hne : (hi : ℝ) - lo ≠ 0 := by linarith
      push_cast
      field_simp
      ring

/-- `b ⊆ c` in the first `n` coordinates, with positive denominators. -/
def subset (n : ℕ) (b c : Box) : Bool :=
  decide (0 < b.den) && decide (0 < c.den) &&
    (List.range n).all fun i ↦
      decide (c.lo.getD i 0 * b.den ≤ b.lo.getD i 0 * c.den) &&
        decide (b.hi.getD i 0 * c.den ≤ c.hi.getD i 0 * b.den)

theorem mem_of_subset {n : ℕ} {b c : Box} (h : b.subset n c = true) {x : Fin n → ℝ}
    (hx : b.Mem n x) : c.Mem n x := by
  simp only [subset, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    at h
  obtain ⟨⟨hb, hc⟩, h⟩ := h
  have hb' : (0 : ℝ) < b.den := by exact_mod_cast hb
  have hc' : (0 : ℝ) < c.den := by exact_mod_cast hc
  intro i
  obtain ⟨hlo, hhi⟩ := h i i.2
  have hlo' : (c.lo.getD i 0 : ℝ) / c.den ≤ (b.lo.getD i 0 : ℝ) / b.den := by
    rw [div_le_div_iff₀ hc' hb']
    exact_mod_cast hlo
  have hhi' : (b.hi.getD i 0 : ℝ) / b.den ≤ (c.hi.getD i 0 : ℝ) / c.den := by
    rw [div_le_div_iff₀ hb' hc']
    exact_mod_cast hhi
  exact ⟨hlo'.trans (hx i).1, (hx i).2.trans hhi'⟩

end Box

/-! ### Bounds of generic computations -/

namespace DPoly

theorem ShapeLE.trans : ∀ {a b c : List ℕ}, ShapeLE a b → ShapeLE b c → ShapeLE a c
  | [], _, _, _, _ => trivial
  | _ :: _, _, _, hab, hbc => ⟨hab.1.trans hbc.headD_le, ShapeLE.trans hab.2 hbc.tail⟩

/-- A bound on all shapes of a list. -/
def shapeMax : List (List ℕ) → List ℕ
  | [] => []
  | s :: ss => zipPad max s (shapeMax ss)

theorem shapeLE_shapeMax : ∀ {ss : List (List ℕ)} {s : List ℕ}, s ∈ ss → ShapeLE s (shapeMax ss)
  | _ :: _, _, .head _ => ShapeLE.zipPad_max_left _ _
  | _ :: _, _, .tail _ h => (shapeLE_shapeMax h).trans (ShapeLE.zipPad_max_right _ _)

end DPoly

theorem le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

namespace Ext

omit [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] in
theorem shapeLE_coord (a : Ext κ Expr) (s : List (List ℕ)) (j : ℕ) :
    DPoly.ShapeLE ((a.coord j).shape s) (DPoly.shapeMax (a.c.map fun e ↦ e.shape s)) := by
  by_cases hj : j < a.c.length
  · refine DPoly.shapeLE_shapeMax (List.mem_map.mpr ⟨a.coord j, ?_, rfl⟩)
    rw [coord, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  · rw [coord, List.getD_eq_default _ _ (by omega)]
    trivial

omit [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] in
theorem normBound_le_coord (a : Ext κ Expr) (b : List ℕ) (j : ℕ) :
    (a.coord j).normBound b ≤ (a.c.map fun e ↦ e.normBound b).foldr max 0 := by
  by_cases hj : j < a.c.length
  · refine le_foldr_max (List.mem_map.mpr ⟨a.coord j, ?_, rfl⟩)
    rw [coord, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  · rw [coord, List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

end Ext

namespace GenPoly

/-- A bound on the shapes of the coordinate polynomials on the box inputs of `n` variables, by a
run in `ShapeL`. -/
def shapeOn (G : GenPoly κ) (n : ℕ) : List ℕ :=
  DPoly.shapeMax ((G.run Ext.const fun i ↦ Ext.var ⟨(boxShapes n).getD i []⟩ : Ext κ ShapeL).c.map
    ShapeL.val)

/-- A bound on the absolute coefficient sums of the coordinate polynomials, given bounds `b` for
the inputs, by a run in `AbsNat`. -/
def normOn (G : GenPoly κ) (b : List ℕ) : ℕ :=
  ((G.run Ext.const fun i ↦ Ext.var ⟨b.getD i 0⟩ : Ext κ AbsNat).c.map AbsNat.val).foldr max 0

/-- The value at integer inputs, in `κ`. -/
def valueAt (G : GenPoly κ) (x : List ℤ) : κ := G.run id fun i ↦ Exact.ofInt (x.getD i 0)

theorem shapeLE_shapeOn (G : GenPoly κ) (n j : ℕ) :
    DPoly.ShapeLE ((G.coord j).shape (boxShapes n)) (G.shapeOn n) := by
  rw [shapeOn, shapes_run, List.map_map]
  exact G.ext.shapeLE_coord _ j

theorem normBound_le_normOn (G : GenPoly κ) (b : List ℕ) (j : ℕ) :
    (G.coord j).normBound b ≤ G.normOn b := by
  rw [normOn, norms_run, List.map_map]
  exact G.ext.normBound_le_coord _ j

end GenPoly

/-- The packed numerals of `G` on the box inputs (centres `C`, widths `H`, scale `D`) at digit size
`B`: coordinate `j` of the value at the packing point, plus the offset. -/
def boxNumerals (G : GenPoly κ) (n : ℕ) (sh : List ℕ) (B : ℕ) (C H : List ℤ) (D : ℤ) :
    List ℕ :=
  let v := G.valueAt (boxPacked n sh B C H D)
  (List.range (ExactBasis.dim κ)).map fun j ↦
    ((ExactBasis.coords v).getD j 0 + DPoly.offset n sh B).toNat

/-- The numerals of `boxNumerals` satisfy the invariant of the engine, and their value at `y` is
`G` at the box point of `y`. -/
theorem boxNumerals_spec (G : GenPoly κ) {n : ℕ} (hsh : (G.shapeOn n).length ≤ n) {B : ℕ}
    (hB : 0 < B) (C H : List ℤ) (D : ℤ) (hnb : G.normOn (boxNorms n C H D) < 2 ^ (B - 1)) :
    (∀ N ∈ boxNumerals G n (G.shapeOn n) B C H D, Lay.Inv B (G.shapeOn n) N) ∧
      ExactBasis.dim κ ≤ (boxNumerals G n (G.shapeOn n) B C H D).length ∧
      ∀ y : Fin n → ℝ, Lay.val (κ := κ) (G.shapeOn n) B (boxNumerals G n (G.shapeOn n) B C H D)
          (fun i ↦ if h : i < n then y ⟨i, h⟩ else 0) = G.run Exact.re (boxEnv n C H D y) := by
  have key : ∀ j, (boxNumerals G n (G.shapeOn n) B C H D).getD j 0 =
      if j < ExactBasis.dim κ then (DPoly.biased n (G.shapeOn n) B
        ((G.coord j).toDPoly n (boxInputs n C H D))).toNat else 0 := by
    intro j
    split_ifs with hj
    · rw [boxNumerals, Box.getD_range_map _ _ _ hj, GenPoly.valueAt, GenPoly.getD_coords_run,
        (box_packing_lt (G.coord j) (G.shapeLE_shapeOn n j) C H D
          (G.normBound_le_normOn _ j) B).2.2]
    · rw [boxNumerals, List.getD_eq_default _ _ (by simp; omega)]
  have hinv : ∀ j < ExactBasis.dim κ, Lay.Inv B (G.shapeOn n)
        ((boxNumerals G n (G.shapeOn n) B C H D).getD j 0) ∧
      ∀ y : ℕ → ℝ, Lay.pv (G.shapeOn n) (Lay.cf B ((boxNumerals G n (G.shapeOn n) B C H D).getD
        j 0)) y = DPoly.eval n ((G.coord j).toDPoly n (boxInputs n C H D)) fun i ↦ y i := by
    intro j hj
    obtain ⟨hfit, hnorm, -⟩ := box_packing_lt (G.coord j) (G.shapeLE_shapeOn n j) C H D
      (G.normBound_le_normOn _ j) B
    rw [key]
    simp only [hj, ↓reduceIte]
    exact Lay.inv_biased hsh hB hfit hnorm hnb
  refine ⟨fun N hN ↦ ?_, by simp [boxNumerals], fun y ↦ ?_⟩
  · obtain ⟨j, hj, rfl⟩ : ∃ j < ExactBasis.dim κ,
        (boxNumerals G n (G.shapeOn n) B C H D).getD j 0 = N := by
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hN
      refine ⟨j, by simpa [boxNumerals] using hj, ?_⟩
      rw [List.getD_eq_getElem _ _ hj]
    exact (hinv j hj).1
  · rw [Lay.val, GenPoly.run_re_eq_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [(hinv j (Finset.mem_range.mp hj)).2, Expr.eval_toDPoly]
    congr 1
    refine congrArg (G.coord j).eval (funext fun i ↦ ?_)
    rw [eval_boxInputs]
    congr 1
    funext i
    simp

/-- The exact route of `signOn`: the engine on the coordinates of `G`'s value in `κ` at the packing
point, one numeral per coordinate. -/
def signOnX (G : GenPoly κ) (n : ℕ) (strict : Bool) (depth : ℕ) (b : Box) (dom : Bool := false) :
    Bool :=
  let C := b.centres n
  let H := b.widths n
  let D : ℤ := ((2 * b.den : ℕ) : ℤ)
  let sh := G.shapeOn n
  let B := Lay.digitsFor (G.normOn (boxNorms n C H D))
    (Lay.room (Lay.apxBits κ) n sh dom false depth H)
  decide (sh.length ≤ n) && Lay.run κ n sh B strict dom false depth H (boxNumerals G n sh B C H D)

/-- Soundness of `signOnX`, at the scaled point `(2 den x, 2 den)` of the box. -/
theorem signOnX_sound (G : GenPoly κ) {n : ℕ} {strict : Bool} {depth : ℕ} {b : Box} {dom : Bool}
    (hden : 0 < b.den) (h : signOnX G n strict depth b dom = true) {x : Fin n → ℝ}
    (hx : b.Mem n x) : Sign strict (G.run Exact.re (homEnv n (2 * b.den : ℝ) x)) := by
  simp only [signOnX, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hsh, h⟩ := h
  have hB := Lay.digitsFor_pos (G.normOn (boxNorms n (b.centres n) (b.widths n) (2 * b.den : ℕ)))
    (Lay.room (Lay.apxBits κ) n (G.shapeOn n) dom false depth (b.widths n))
  obtain ⟨hinv, hlen, hval⟩ := boxNumerals_spec G hsh hB (b.centres n) (b.widths n)
    (2 * b.den : ℕ) (Lay.le_digitsFor _ _)
  choose y hy hyx using fun i : Fin n ↦ Box.exists_centred hden (hx i)
  have henv : boxEnv n (b.centres n) (b.widths n) (2 * b.den : ℕ) y =
      homEnv n (2 * b.den : ℝ) x := by
    funext i
    unfold boxEnv homEnv
    split_ifs with h₁ h₂
    · rw [Box.centres, Box.widths, Box.getD_range_map n _ _ h₁, Box.getD_range_map n _ _ h₁,
        hyx ⟨i, h₁⟩]
    · push_cast; ring
    · rfl
  have hs := Lay.run_sound (Lay.digitsFor_pos _ _) hsh depth _ hinv hlen h
    (fun i ↦ if h : i < n then y ⟨i, h⟩ else 0) (fun i ↦ by
      split_ifs
      · exact hy _
      · simp)
  rwa [hval, henv] at hs

/-- `G` run on balls (`PBall`): its constants on their balls (`Exact.ball`), its inputs exact with
the bounds `bnd`; the centre less the error bound. A computation over `ℤ`: compiled code runs it on
packed integers, one numeral and one product a product, where `κ` takes `(dim κ)²` (row 2 of
`notes/lean-perf.md`). -/
def GenPoly.ballPoly (G : GenPoly κ) (bnd : List ℕ) : GenPoly ℤ where
  run k x :=
    letI := IntCast.mk k
    let P := G.run (fun c ↦ PBall.ofBall (Exact.ball c)) fun i ↦ PBall.exact (x i) (bnd.getD i 0)
    P.m - k P.r
  natural f hf k x := by
    let _ := IntCast.mk k
    let _ := IntCast.mk (f ∘ k)
    have h := G.natural _ (PBall.isArith_map (f := f) hf fun _ ↦ rfl)
      (fun c ↦ PBall.ofBall (Exact.ball c)) fun i ↦ PBall.exact (x i) (bnd.getD i 0)
    have e1 : (PBall.map f ∘ fun c : κ ↦ (PBall.ofBall (Exact.ball c) : PBall _)) =
        fun c : κ ↦ PBall.ofBall (Exact.ball c) :=
      funext fun c ↦ PBall.map_ofBall (f := f) (fun _ ↦ rfl) _
    rw [e1] at h
    simp only [hf.map_sub]
    exact congrArg₂ (· - ·) (congrArg PBall.m h) (congrArg (fun P ↦ f (k P.r)) h)

/-- **The real value is in the ball** of the run on balls, when the inputs are within their
bounds: by naturality, on pairs of a value and a ball that holds it. -/
theorem GenPoly.holds_run (G : GenPoly κ) (bnd : List ℕ) (x : ℕ → ℝ)
    (hx : ∀ i, |x i| ≤ bnd.getD i 0) :
    PBall.Holds (G.run Exact.re x)
      (G.run (fun c ↦ PBall.ofBall (Exact.ball c)) fun i ↦ PBall.exact (x i) (bnd.getD i 0)) := by
  let HB := {q : ℝ × PBall ℝ // PBall.Holds q.1 q.2}
  let _ : Add HB := ⟨fun p q ↦ ⟨(p.1.1 + q.1.1, p.1.2 + q.1.2), PBall.holds_add p.2 q.2⟩⟩
  let _ : Sub HB := ⟨fun p q ↦ ⟨(p.1.1 - q.1.1, p.1.2 - q.1.2), PBall.holds_sub p.2 q.2⟩⟩
  let _ : Mul HB := ⟨fun p q ↦ ⟨(p.1.1 * q.1.1, p.1.2 * q.1.2), PBall.holds_mul p.2 q.2⟩⟩
  let k : κ → HB := fun c ↦
    ⟨(Exact.re c, PBall.ofBall (Exact.ball c)), PBall.holds_ofBall (Exact.ball_sound c)⟩
  let y : ℕ → HB := fun i ↦
    ⟨(x i, PBall.exact (x i) (bnd.getD i 0)), PBall.holds_exact (hx i)⟩
  have h1 : (G.run k y).1.1 = G.run Exact.re x :=
    G.natural (fun q : HB ↦ q.1.1) ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩ k y
  have h2 : (G.run k y).1.2 = G.run (fun c ↦ PBall.ofBall (Exact.ball c))
      (fun i ↦ PBall.exact (x i) (bnd.getD i 0)) :=
    G.natural (fun q : HB ↦ q.1.2) ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩ k y
  have h3 := (G.run k y).2
  rw [h1, h2] at h3
  exact h3

/-- The real run of `ballPoly` is the centre of the run on real balls less the error bound. -/
theorem GenPoly.ballPoly_run_re (G : GenPoly κ) (bnd : List ℕ) (x : ℕ → ℝ) :
    (G.ballPoly bnd).run Exact.re x =
      (G.run (fun c ↦ PBall.ofBall (Exact.ball c)) fun i ↦ PBall.exact (x i) (bnd.getD i 0)).m -
      (G.run (fun c ↦ PBall.ofBall (Exact.ball c)) fun i ↦ PBall.exact (x i) (bnd.getD i 0)).r := by
  have hre : ∀ z : ℤ, Exact.re z = (z : ℝ) := fun z ↦ by
    change (Erased.mk (z : ℝ)).out = _
    rw [Erased.out_mk]
  have hi : (IntCast.mk Exact.re : IntCast ℝ) = Real.instIntCast := by
    rw [show (Exact.re : ℤ → ℝ) = Int.cast from funext hre]
  simp only [GenPoly.ballPoly]
  rw [hi, hre, Int.cast_natCast]

theorem GenPoly.abs_homEnv_le {b : Box} {n : ℕ} (hden : 0 < b.den) {x : Fin n → ℝ}
    (hx : b.Mem n x) (i : ℕ) :
    |homEnv n (2 * b.den : ℝ) x i| ≤
      (boxNorms n (b.centres n) (b.widths n) ((2 * b.den : ℕ) : ℤ)).getD i 0 := by
  unfold homEnv boxNorms
  split_ifs with h₁ h₂
  · obtain ⟨y, hy, hyx⟩ := Box.exists_centred hden (hx ⟨i, h₁⟩)
    rw [List.getD_append _ _ _ _ (by simpa using h₁), Box.getD_range_map _ _ _ h₁,
      Box.centres, Box.widths, Box.getD_range_map _ _ _ h₁, Box.getD_range_map _ _ _ h₁, ← hyx]
    push_cast
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, Nat.cast_natAbs, Nat.cast_natAbs]
    push_cast
    have := abs_nonneg (((b.hi.getD i 0 - b.lo.getD i 0 : ℤ)) : ℝ)
    push_cast at this
    nlinarith [abs_nonneg y]
  · subst h₂
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp [abs_of_nonneg]
  · simp

/-- Certifies `0 ≤ G` on the box `b`, or `0 < G` if `strict` (module docs). Over a number field
(`1 < dim κ`) the run on balls goes first (`ballPoly`), as Rust ranges support witnesses on
enclosures; the exact route only where it fails (an exact zero, a sign the balls leave open). With
`dom`, a box where the centred form fails is also tried by dominance at the vertex where the linear
part is smallest (`Lay.run`), before it is bisected: this certifies polynomials that vanish at a
vertex or on a face of the box with the right slopes, which no centred bound can
(`nonneg_on_fbox_exact` of `regional.rs`; images of mapped leaves that touch the face of their
claim's region). -/
def signOn (G : GenPoly κ) (n : ℕ) (strict : Bool) (depth : ℕ) (b : Box) (dom : Bool := false) :
    Bool :=
  (decide (1 < ExactBasis.dim κ) &&
      signOnX (G.ballPoly (boxNorms n (b.centres n) (b.widths n) ((2 * b.den : ℕ) : ℤ))) n strict
        depth b dom) ||
    signOnX G n strict depth b dom

/-- **Soundness of `signOn`**, at the scaled point `(2 den x, 2 den)` of the box. -/
theorem signOn_sound (G : GenPoly κ) {n : ℕ} {strict : Bool} {depth : ℕ} {b : Box} {dom : Bool}
    (hden : 0 < b.den) (h : signOn G n strict depth b dom = true) {x : Fin n → ℝ} (hx : b.Mem n x) :
    Sign strict (G.run Exact.re (homEnv n (2 * b.den : ℝ) x)) := by
  simp only [signOn, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨-, h⟩ | h
  · have hs := signOnX_sound _ hden h hx
    rw [GenPoly.ballPoly_run_re] at hs
    obtain ⟨hr, -⟩ := G.holds_run _ _ (GenPoly.abs_homEnv_le hden hx)
    set P := G.run (fun c ↦ PBall.ofBall (Exact.ball c)) fun i ↦
      PBall.exact (homEnv n (2 * b.den : ℝ) x i)
        ((boxNorms n (b.centres n) (b.widths n) ((2 * b.den : ℕ) : ℤ)).getD i 0)
    have hle : P.m - P.r ≤ 2 ^ P.s * G.run Exact.re (homEnv n (2 * b.den : ℝ) x) := by
      linarith [(abs_le.mp hr).1]
    have h2 : (0 : ℝ) < 2 ^ P.s := by positivity
    have hs' := sign_of_le hs hle
    unfold Sign at hs' ⊢
    split_ifs at hs' ⊢
    · exact pos_of_mul_pos_right hs' h2.le
    · exact nonneg_of_mul_nonneg_right hs' h2
  · exact signOnX_sound G hden h hx

/-- Certifies `G ≥ 0` on the box `b` (module docs). -/
def nonnegOn (G : GenPoly κ) (n depth : ℕ) (b : Box) (dom : Bool := false) : Bool :=
  signOn G n false depth b dom

/-- Certifies `G > 0` on the box `b` (module docs). -/
def posOn (G : GenPoly κ) (n depth : ℕ) (b : Box) (dom : Bool := false) : Bool :=
  signOn G n true depth b dom

theorem nonnegOn_sound (G : GenPoly κ) (n : ℕ) (depth : ℕ) {b : Box} {dom : Bool}
    (hden : 0 < b.den) (h : nonnegOn G n depth b dom = true) (x : Fin n → ℝ) (hx : b.Mem n x) :
    ∃ d : ℝ, 0 < d ∧ 0 ≤ G.run Exact.re (homEnv n d x) :=
  ⟨2 * b.den, by positivity, by simpa [Sign] using signOn_sound G hden h hx⟩

theorem posOn_sound (G : GenPoly κ) (n : ℕ) (depth : ℕ) {b : Box} {dom : Bool}
    (hden : 0 < b.den) (h : posOn G n depth b dom = true) (x : Fin n → ℝ) (hx : b.Mem n x) :
    ∃ d : ℝ, 0 < d ∧ 0 < G.run Exact.re (homEnv n d x) :=
  ⟨2 * b.den, by positivity, by simpa [Sign] using signOn_sound G hden h hx⟩

/-- `G` is homogeneous of degree `k` in its first `n + 1` variables. -/
def GenPoly.IsHomogeneous {ν : Type} [Add ν] [Sub ν] [Mul ν] [Exact ν] (G : GenPoly ν)
    (n k : ℕ) : Prop :=
  ∀ (d : ℝ) (x : Fin n → ℝ), G.run Exact.re (homEnv n d x) = d ^ k * G.run Exact.re (homEnv n 1 x)

theorem nonnegOn_hom {n k : ℕ} {G : GenPoly κ} (he : G.IsHomogeneous n k) {depth : ℕ}
    {b : Box} {dom : Bool} (hden : 0 < b.den) (h : nonnegOn G n depth b dom = true) {x : Fin n → ℝ}
    (hx : b.Mem n x) : 0 ≤ G.run Exact.re (homEnv n 1 x) := by
  obtain ⟨d, hd, hpos⟩ := nonnegOn_sound G n depth hden h x hx
  rw [he d x] at hpos
  exact nonneg_of_mul_nonneg_right hpos (pow_pos hd k)

theorem posOn_hom {n k : ℕ} {G : GenPoly κ} (he : G.IsHomogeneous n k) {depth : ℕ}
    {b : Box} {dom : Bool} (hden : 0 < b.den) (h : posOn G n depth b dom = true) {x : Fin n → ℝ}
    (hx : b.Mem n x) : 0 < G.run Exact.re (homEnv n 1 x) := by
  obtain ⟨d, hd, hpos⟩ := posOn_sound G n depth hden h x hx
  rw [he d x] at hpos
  exact pos_of_mul_pos_right hpos (pow_pos hd k).le

end Nieuwland.Check
