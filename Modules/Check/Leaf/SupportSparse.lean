import Modules.Check.Leaf.Centred
import Modules.Check.Sign.SparsePull

/-!
# Support witnesses by the sparse sign check

`Balanced.check` and `Centred.check` decide the sign of each witness polynomial on its box by
`nonnegOn` (`Modules/Check/Sign/Box.lean`): on balls first where `Exact.ballFirst`, then exactly (the
polynomial's numerals at a packing point, the engine). Here the same polynomials go to the sparse
sign check (`Pull.checkX`, `Modules/Check/Sign/SparsePull.lean`), which the obstruction leaves of
weighted zooms and chart trees use: each polynomial expanded exactly as a sparse polynomial in the
box variables, its values at bounded precision and the truncated test, rupert's procedure, the
engine as the fallback.

A balanced witness polynomial is linear in its plugs and anchors together (`supportPoly`), so the
polynomial of the anchors `t` is the sum of an anchor-free part `P` (the plugs, anchors `0`) and
one part `Nᵢ(t i)` per support (its anchor alone, plugs `0`; `balancedPoly_split`). With three or
more triples of anchors, `Balanced.checkS` expands `P` and each `Nᵢ(a)` once and sums them per
triple (`splitTerms`); with one or two, it expands each triple's polynomial (`wholeTerms`), which
measured faster there. A centred support has one term per pair and corner of the view box
(`Centred.terms`), as in `Centred.check`.

`checkAny` accepts a claim that either check accepts (`Evidence.check`). The kernel tests `check`
first, so a kernel check costs what it did; compiled code tests `checkS` first where
`Exact.sparseFirst` (over `ℤ[√d]`, where it measured faster; `notes/lean-perf.md`, row 6), and
`check` first elsewhere (`checkAny_eq_checkAnyF`). The kernel does not reduce the sparse check (its
merges of sparse polynomials are well-founded recursions), so kernel tests of refused claims test
`check`, and native tests (`Nieuwland/Examples/Native.lean`) test `checkS` and `checkAny`.
-/

open Matrix

namespace Nieuwland.Check

/-- The inputs of a homogeneous computation at the point `(x, 1)`: the box variables, with the
homogenising variable `m` set to `1` (`dehom_run`). -/
def dehom {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] (m : ℕ) : GenMap κ where
  run k x i := if i = m then k (Exact.ofInt 1) else x i
  natural f hf k x := by
    funext i
    simp only [Function.comp_apply]
    split <;> rfl

theorem dehom_run {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] (n : ℕ) (x : Fin n → ℝ) :
    (dehom (κ := κ) n).run Exact.re (Pull.ext n x) = homEnv n 1 x := by
  funext i
  simp only [dehom, Pull.ext, homEnv, Exact.re_ofInt, Int.cast_one, one_mul]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- The exact point `0`. -/
def zeroV {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] : V3 κ :=
  ⟨Exact.ofInt 0, Exact.ofInt 0, Exact.ofInt 0⟩

theorem reV_zeroV {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] :
    Exact.reV (zeroV : V3 κ) = 0 := by
  funext i
  fin_cases i <;> simp [Exact.reV, zeroV, V3.map, V3.toFun, Exact.re_ofInt]

namespace Pull

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

theorem getD_e_nil {ts : List (Term κ)} (he : ∀ t ∈ ts, t.e = []) (j : ℕ) :
    (ts.getD j default).e = [] := by
  rw [List.getD_eq_getElem?_getD]
  cases h : ts[j]? with
  | none => rfl
  | some t => exact he t (List.mem_of_getElem? h)

/-- **The sparse sign check of undivided terms** (`checkX_sound` with every monomial `1`): at every
point of the box, every checked weighted sum of the terms' polynomials has the sign. -/
theorem checkX_sum {n : ℕ} {ts : List (Term κ)} {strict : Bool} {depth : ℕ} {b : Box}
    {τs : List Tuple} {o : List (ℕ × ℕ)} (h : checkX n ts strict depth b τs o = true)
    (he : ∀ t ∈ ts, t.e = []) {τ : Tuple} (hτ : τ ∈ τs) {x : Fin n → ℝ} (hx : b.Mem n x) :
    Sign strict
      (τ.map fun jw ↦ (jw.2 : ℝ) * (ts.getD jw.1 default).G.run Exact.re (ext n x)).sum := by
  obtain ⟨c, hc, s, heq, hsign⟩ := checkX_sound h τ hτ x hx
  have hmap : (τ.map fun jw ↦ (jw.2 : ℝ) * (ts.getD jw.1 default).G.run Exact.re (ext n x)) =
      τ.map fun jw ↦ c * ((jw.2 : ℝ) * s jw.1) := by
    refine List.map_congr_left fun jw hjw ↦ ?_
    rw [heq jw hjw, getD_e_nil he, monoVal_nil, mul_one]
    ring
  rw [hmap, List.sum_map_mul_left]
  unfold Sign at hsign ⊢
  split_ifs at hsign ⊢
  · exact mul_pos hc hsign
  · exact mul_nonneg hc.le hsign

/-- **The sparse sign check of undivided terms, one tuple per term**: every term's polynomial has
the sign on the box. -/
theorem checkX_each {n : ℕ} {ts : List (Term κ)} {strict : Bool} {depth : ℕ} {b : Box}
    (h : checkX n ts strict depth b ((List.range ts.length).map fun j ↦ [(j, 1)]) = true)
    (he : ∀ t ∈ ts, t.e = []) {t : Term κ} (ht : t ∈ ts) {x : Fin n → ℝ} (hx : b.Mem n x) :
    Sign strict (t.G.run Exact.re (ext n x)) := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
  have hs := checkX_sum h he (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩) hx
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Int.cast_one,
    one_mul] at hs
  rwa [List.getD_eq_getElem _ _ hj] at hs

end Pull

/-! ### The split of balanced witness polynomials -/

section Split

variable {R : Type*} [CommRing R]

/-- A support polynomial is linear in the plug and the anchor together. -/
theorem supportPoly_split (u : Fin 3 → R) (q : Fin 4 → R) (c v w : Fin 3 → R) :
    supportPoly u q c v w = supportPoly u q c v 0 + supportPoly u q c 0 w := by
  simp only [supportPoly, mulVec_zero, smul_zero, sub_zero, zero_sub, map_sub, map_neg,
    dotProduct_sub, dotProduct_neg]
  ring

theorem supportPoly_zero (u : Fin 3 → R) (q : Fin 4 → R) (c : Fin 3 → R) :
    supportPoly u q c 0 0 = 0 := by
  simp [supportPoly]

/-- **The split of a balanced witness polynomial**: the anchor-free part plus one part per
support's anchor. -/
theorem balancedPoly_split (σ : R) (u : Fin 3 → R) (q : Fin 4 → R) (c v w : Fin 3 → Fin 3 → R) :
    balancedPoly σ u q c v w = balancedPoly σ u q c v (fun _ ↦ 0) +
      (balancedPoly σ u q c (fun _ ↦ 0) (fun l ↦ if l = 0 then w 0 else 0) +
        (balancedPoly σ u q c (fun _ ↦ 0) (fun l ↦ if l = 1 then w 1 else 0) +
          balancedPoly σ u q c (fun _ ↦ 0) (fun l ↦ if l = 2 then w 2 else 0))) := by
  simp only [balancedPoly, Fin.sum_univ_three, ↓reduceIte,
    show ¬((1 : Fin 3) = 0) by decide, show ¬((2 : Fin 3) = 0) by decide,
    show ¬((0 : Fin 3) = 1) by decide, show ¬((2 : Fin 3) = 1) by decide,
    show ¬((0 : Fin 3) = 2) by decide, show ¬((1 : Fin 3) = 2) by decide]
  rw [supportPoly_split u q (c 0) (v 0) (w 0), supportPoly_split u q (c 1) (v 1) (w 1),
    supportPoly_split u q (c 2) (v 2) (w 2)]
  simp only [supportPoly_zero]
  ring

end Split

namespace Balanced

section Basis

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The witness polynomial of the anchors `t` on the chart box `B` (as in `check`). -/
def gen (pts : List (V3 κ)) (B : ChartBox) (w : Balanced) (pre : Option (Q4 κ))
    (t : Fin 3 → ℕ) : GenPoly κ :=
  balancedGen (Exact.ofInt w.sigma) B.view B.rot (w.dir pts) (fun i ↦ pt pts (w.sup i).plug)
    (fun i ↦ pt pts (t i)) pre

/-- The anchor-free part of the witness polynomials: the plugs, anchors `0`. -/
def genP (pts : List (V3 κ)) (B : ChartBox) (w : Balanced) (pre : Option (Q4 κ)) : GenPoly κ :=
  balancedGen (Exact.ofInt w.sigma) B.view B.rot (w.dir pts) (fun i ↦ pt pts (w.sup i).plug)
    (fun _ ↦ zeroV) pre

/-- The part of the anchor `a` of support `i`: anchor `a` for support `i`, the other anchors and
the plugs `0`. -/
def genN (pts : List (V3 κ)) (B : ChartBox) (w : Balanced) (pre : Option (Q4 κ)) (i : Fin 3)
    (a : ℕ) : GenPoly κ :=
  balancedGen (Exact.ofInt w.sigma) B.view B.rot (w.dir pts) (fun _ ↦ zeroV)
    (fun l ↦ if l = i then pt pts a else zeroV) pre

theorem gen_split (pts : List (V3 κ)) (B : ChartBox) (w : Balanced) (pre : Option (Q4 κ))
    (t : Fin 3 → ℕ) (y : Fin 5 → ℝ) :
    (w.gen pts B pre t).run Exact.re (homEnv 5 1 y) =
      (w.genP pts B pre).run Exact.re (homEnv 5 1 y) +
        ((w.genN pts B pre 0 (t 0)).run Exact.re (homEnv 5 1 y) +
          ((w.genN pts B pre 1 (t 1)).run Exact.re (homEnv 5 1 y) +
            (w.genN pts B pre 2 (t 2)).run Exact.re (homEnv 5 1 y))) := by
  have hz : (fun _ : Fin 3 ↦ Exact.reV (zeroV : V3 κ)) = fun _ ↦ 0 :=
    funext fun _ ↦ reV_zeroV (κ := κ)
  have hN (i : Fin 3) (a : ℕ) : (fun l ↦ Exact.reV (if l = i then pt pts a else zeroV)) =
      fun l ↦ if l = i then Exact.reV (pt pts a) else 0 := by
    funext l
    split_ifs
    · rfl
    · exact reV_zeroV (κ := κ)
  simp only [gen, genP, genN, balancedGen_homEnv, one_pow, one_mul, hz, hN]
  exact balancedPoly_split _ _ _ _ _ _

/-- The triples of anchors of the supports. -/
def triples (A : Fin 3 → List ℕ) : List (Fin 3 → ℕ) :=
  (A 0).flatMap fun i₀ ↦ (A 1).flatMap fun i₁ ↦ (A 2).map fun i₂ ↦ ![i₀, i₁, i₂]

theorem mem_triples {A : Fin 3 → List ℕ} {t : Fin 3 → ℕ} (ht : ∀ i, t i ∈ A i) :
    t ∈ triples A := by
  have hte : t = ![t 0, t 1, t 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hte]
  simp only [triples, List.mem_flatMap, List.mem_map]
  exact ⟨t 0, ht 0, t 1, ht 1, t 2, ht 2, rfl⟩

/-- The number of triples of anchors. -/
def nTriples (w : Balanced) : ℕ :=
  (w.sup 0).anchors.length * (w.sup 1).anchors.length * (w.sup 2).anchors.length

/-- The terms of `checkS` with few triples: each triple's polynomial at `D = 1`. -/
def wholeTerms (pts : List (V3 κ)) (B : ChartBox) (w : Balanced) (pre : Option (Q4 κ)) :
    List (Term κ) :=
  (triples fun i ↦ (w.sup i).anchors).map fun t ↦ ⟨(w.gen pts B pre t).comp (dehom 5), []⟩

/-- The parts of the anchors of support `i`, at `D = 1`. -/
def partTerms (pts : List (V3 κ)) (B : ChartBox) (w : Balanced) (pre : Option (Q4 κ))
    (i : Fin 3) : List (Term κ) :=
  (w.sup i).anchors.map fun a ↦ ⟨(w.genN pts B pre i a).comp (dehom 5), []⟩

/-- The terms of `checkS` with many triples: the anchor-free part, then the parts of the anchors
of supports `0`, `1` and `2`. -/
def splitTerms (pts : List (V3 κ)) (B : ChartBox) (w : Balanced) (pre : Option (Q4 κ)) :
    List (Term κ) :=
  ⟨(w.genP pts B pre).comp (dehom 5), []⟩ ::
    (w.partTerms pts B pre 0 ++ w.partTerms pts B pre 1 ++ w.partTerms pts B pre 2)

/-- The tuples of `splitTerms`: per triple of anchors, the anchor-free part and the part of each
anchor. -/
def splitTuples (w : Balanced) : List Pull.Tuple :=
  let n₀ := (w.sup 0).anchors.length
  let n₁ := (w.sup 1).anchors.length
  (List.range n₀).flatMap fun k₀ ↦ (List.range n₁).flatMap fun k₁ ↦
    (List.range (w.sup 2).anchors.length).map fun k₂ ↦
      [(0, 1), (k₀ + 1, 1), (n₀ + k₁ + 1, 1), (n₀ + n₁ + k₂ + 1, 1)]

/-- **The sparse check of a balanced-support claim** on the chart box `B`, pre-rotated by `pre` if
any, bisecting at most `depth` times along each branch: the premises of `check`, then the witness
polynomials by the sparse sign check, split into parts with three or more triples of anchors. -/
def checkS (pts : List (V3 κ)) (B : ChartBox) (depth : ℕ) (w : Balanced)
    (pre : Option (Q4 κ) := none) : Bool :=
  decide (0 < B.box.den) && Exact.preOk pre && w.premisesOk pts (viewCorners B.view B.box) &&
    if 3 ≤ w.nTriples then
      Pull.checkX 5 (w.splitTerms pts B pre) false depth B.box w.splitTuples
    else
      Pull.checkX 5 (w.wholeTerms pts B pre) false depth B.box
        ((List.range (w.wholeTerms pts B pre).length).map fun j ↦ [(j, 1)])

theorem getD_splitTerms {α : Type*} (d p : α) (L₀ L₁ L₂ : List α) :
    (∀ k < L₀.length, (p :: (L₀ ++ L₁ ++ L₂)).getD (k + 1) d = L₀.getD k d) ∧
      (∀ k < L₁.length, (p :: (L₀ ++ L₁ ++ L₂)).getD (L₀.length + k + 1) d = L₁.getD k d) ∧
      ∀ k, (p :: (L₀ ++ L₁ ++ L₂)).getD (L₀.length + L₁.length + k + 1) d = L₂.getD k d := by
  refine ⟨fun k hk ↦ ?_, fun k hk ↦ ?_, fun k ↦ ?_⟩
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.append_assoc]
    rw [List.getElem?_append_left hk]
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.append_assoc]
    rw [List.getElem?_append_right (by omega), List.getElem?_append_left (by omega)]
    congr 2
    omega
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.append_assoc]
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    congr 2
    omega

theorem splitTerms_e (pts : List (V3 κ)) (B : ChartBox) (w : Balanced) (pre : Option (Q4 κ)) :
    ∀ t ∈ w.splitTerms pts B pre, t.e = [] := by
  intro t ht
  simp only [splitTerms, partTerms, List.mem_cons, List.mem_append, List.mem_map] at ht
  rcases ht with rfl | ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) <;> rfl

theorem getD_partTerms {pts : List (V3 κ)} {B : ChartBox} {w : Balanced} {pre : Option (Q4 κ)}
    {i : Fin 3} {k : ℕ} (hk : k < (w.sup i).anchors.length) :
    (w.partTerms pts B pre i).getD k default =
      ⟨(w.genN pts B pre i (w.sup i).anchors[k]).comp (dehom 5), []⟩ := by
  rw [partTerms, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk]
  rfl

/-- The split check gives each triple's polynomial its sign. -/
theorem split_nonneg {pts : List (V3 κ)} {B : ChartBox} {depth : ℕ} {w : Balanced}
    {pre : Option (Q4 κ)}
    (h : Pull.checkX 5 (w.splitTerms pts B pre) false depth B.box w.splitTuples = true)
    {t : Fin 3 → ℕ} (ht : ∀ i, t i ∈ (w.sup i).anchors) {y : Fin 5 → ℝ} (hy : B.box.Mem 5 y) :
    0 ≤ (w.gen pts B pre t).run Exact.re (homEnv 5 1 y) := by
  obtain ⟨k₀, hk₀, e₀⟩ := List.getElem_of_mem (ht 0)
  obtain ⟨k₁, hk₁, e₁⟩ := List.getElem_of_mem (ht 1)
  obtain ⟨k₂, hk₂, e₂⟩ := List.getElem_of_mem (ht 2)
  set n₀ := (w.sup 0).anchors.length
  set n₁ := (w.sup 1).anchors.length
  have hτ : [(0, (1 : ℤ)), (k₀ + 1, 1), (n₀ + k₁ + 1, 1), (n₀ + n₁ + k₂ + 1, 1)] ∈
      w.splitTuples := by
    simp only [splitTuples, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨k₀, hk₀, k₁, hk₁, k₂, hk₂, rfl⟩
  have hs := Pull.checkX_sum h (splitTerms_e pts B w pre) hτ hy
  have hl₀ : (w.partTerms pts B pre 0).length = n₀ := List.length_map _
  have hl₁ : (w.partTerms pts B pre 1).length = n₁ := List.length_map _
  obtain ⟨g₀, g₁, g₂⟩ := getD_splitTerms (default : Term κ)
    (⟨(w.genP pts B pre).comp (dehom 5), []⟩ : Term κ) (w.partTerms pts B pre 0)
    (w.partTerms pts B pre 1) (w.partTerms pts B pre 2)
  rw [hl₀, hl₁] at g₁ g₂
  simp only [Sign, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, Int.cast_one, one_mul] at hs
  rw [splitTerms, g₀ k₀ (hl₀ ▸ hk₀), g₁ k₁ (hl₁ ▸ hk₁), g₂ k₂, getD_partTerms hk₀,
    getD_partTerms hk₁, getD_partTerms hk₂, e₀, e₁, e₂] at hs
  change 0 ≤ (w.genP pts B pre).run Exact.re ((dehom 5).run Exact.re (Pull.ext 5 y)) +
    ((w.genN pts B pre 0 (t 0)).run Exact.re ((dehom 5).run Exact.re (Pull.ext 5 y)) +
      ((w.genN pts B pre 1 (t 1)).run Exact.re ((dehom 5).run Exact.re (Pull.ext 5 y)) +
        (w.genN pts B pre 2 (t 2)).run Exact.re ((dehom 5).run Exact.re (Pull.ext 5 y)))) at hs
  rw [dehom_run] at hs
  rw [gen_split]
  exact hs

/-- The check of each triple's polynomial gives it its sign. -/
theorem whole_nonneg {pts : List (V3 κ)} {B : ChartBox} {depth : ℕ} {w : Balanced}
    {pre : Option (Q4 κ)}
    (h : Pull.checkX 5 (w.wholeTerms pts B pre) false depth B.box
      ((List.range (w.wholeTerms pts B pre).length).map fun j ↦ [(j, 1)]) = true)
    {t : Fin 3 → ℕ} (ht : ∀ i, t i ∈ (w.sup i).anchors) {y : Fin 5 → ℝ} (hy : B.box.Mem 5 y) :
    0 ≤ (w.gen pts B pre t).run Exact.re (homEnv 5 1 y) := by
  have he : ∀ t ∈ w.wholeTerms pts B pre, t.e = [] := by
    intro t ht
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp ht
    rfl
  have hs := Pull.checkX_each h he (List.mem_map.mpr ⟨t, mem_triples ht, rfl⟩) hy
  simp only [Sign, Bool.false_eq_true, ↓reduceIte] at hs
  change 0 ≤ (w.gen pts B pre t).run Exact.re ((dehom 5).run Exact.re (Pull.ext 5 y)) at hs
  rwa [dehom_run] at hs

/-- **Soundness of the sparse check of balanced-support claims**, on a box pre-rotated by `pre`,
with the conclusion of `check_sound_pre`. -/
theorem checkS_sound_pre {pts : List (V3 κ)} {B : ChartBox} {depth : ℕ} {ev : Balanced}
    {pre : Option (Q4 κ)} (h : ev.checkS pts B depth pre = true) :
    (Polyhedron.ofPoints pts).NoFitRot B.poses (preRot (Exact.rePre pre)) := by
  simp only [checkS, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hden, hpre⟩, hprem⟩, hpoly⟩ := h
  refine sound_of_nonneg hden hpre hprem fun t ht y hy ↦ ?_
  split_ifs at hpoly
  · exact split_nonneg hpoly ht hy
  · exact whole_nonneg hpoly ht hy

/-- **The check of a balanced-support claim** (`Evidence.check`): `check` or `checkS` (module
docs). -/
def checkAny (pts : List (V3 κ)) (B : ChartBox) (depth : ℕ) (w : Balanced)
    (pre : Option (Q4 κ) := none) : Bool :=
  w.check pts B depth pre || w.checkS pts B depth pre

/-- `checkAny` as compiled code runs it (`checkAny_eq_checkAnyF`): `checkS` first where
`Exact.sparseFirst`. -/
def checkAnyF (pts : List (V3 κ)) (B : ChartBox) (depth : ℕ) (w : Balanced)
    (pre : Option (Q4 κ) := none) : Bool :=
  if Exact.sparseFirst (α := κ) then w.checkS pts B depth pre || w.check pts B depth pre
  else w.check pts B depth pre || w.checkS pts B depth pre

@[csimp] theorem checkAny_eq_checkAnyF : @checkAny = @checkAnyF := by
  funext κ _ _ _ _ pts B depth w pre
  rw [checkAny, checkAnyF]
  split
  · exact Bool.or_comm _ _
  · rfl

/-- **Soundness of balanced-support claims** by either check, on a box pre-rotated by `pre`. -/
theorem checkAny_sound_pre {pts : List (V3 κ)} {B : ChartBox} {depth : ℕ} {ev : Balanced}
    {pre : Option (Q4 κ)} (h : ev.checkAny pts B depth pre = true) :
    (Polyhedron.ofPoints pts).NoFitRot B.poses (preRot (Exact.rePre pre)) := by
  simp only [checkAny, Bool.or_eq_true] at h
  rcases h with h | h
  · exact check_sound_pre h
  · exact checkS_sound_pre h

end Basis

end Balanced

namespace Centred

section Basis

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The terms of `checkS`: the witness polynomial of each pair at each corner of the view box, on
the rotation variables at `D = 1` (as in `check`). -/
def terms (pts : List (V3 κ)) (B : ChartBox) (w : Centred κ) (pre : Option (Q4 κ)) :
    List (Term κ) :=
  w.pairs.flatMap fun p ↦ (viewCorners B.view B.box).map fun U ↦
    ⟨(supportRotGen U B.rot w.c (w.toWidth.plugDiff pts) ((pt pts p.1).sub (pt pts p.2))
      pre).comp (dehom 3), []⟩

/-- **The sparse check of a centred-support claim** on the chart box `B`, pre-rotated by `pre` if
any, bisecting at most `depth` times along each branch: the premises of `check`, then the witness
polynomials by the sparse sign check. -/
def checkS (pts : List (V3 κ)) (B : ChartBox) (depth : ℕ) (w : Centred κ)
    (pre : Option (Q4 κ) := none) : Bool :=
  decide (0 < B.box.den) && Exact.preOk pre && w.premisesOk pts (viewCorners B.view B.box) &&
    Pull.checkX 3 (w.terms pts B pre) false depth (B.box.drop 2)
      ((List.range (w.terms pts B pre).length).map fun j ↦ [(j, 1)])

/-- **Soundness of the sparse check of centred-support claims**, on a box pre-rotated by `pre`,
with the conclusion of `check_sound_pre`. -/
theorem checkS_sound_pre {pts : List (V3 κ)} {B : ChartBox} {depth : ℕ} {w : Centred κ}
    {pre : Option (Q4 κ)} (h : w.checkS pts B depth pre = true) :
    (Polyhedron.ofPoints pts).NoFitRot B.poses (preRot (Exact.rePre pre)) := by
  simp only [checkS, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hden, hpre⟩, hprem⟩, hpoly⟩ := h
  have he : ∀ t ∈ w.terms pts B pre, t.e = [] := by
    intro t ht
    obtain ⟨_, _, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp ht
    rfl
  refine sound_of_nonneg hden hpre hprem fun r hr U hU x hx ↦ ?_
  have hs := Pull.checkX_each hpoly he
    (List.mem_flatMap.mpr ⟨r, hr, List.mem_map.mpr ⟨U, hU, rfl⟩⟩) hx
  simp only [Sign, Bool.false_eq_true, ↓reduceIte] at hs
  change 0 ≤ (supportRotGen U B.rot w.c (w.toWidth.plugDiff pts) ((pt pts r.1).sub (pt pts r.2))
    pre).run Exact.re ((dehom 3).run Exact.re (Pull.ext 3 x)) at hs
  rwa [dehom_run] at hs

/-- **The check of a centred-support claim** (`Evidence.check`): `check` or `checkS` (module
docs). -/
def checkAny (pts : List (V3 κ)) (B : ChartBox) (depth : ℕ) (w : Centred κ)
    (pre : Option (Q4 κ) := none) : Bool :=
  w.check pts B depth pre || w.checkS pts B depth pre

/-- `checkAny` as compiled code runs it (`checkAny_eq_checkAnyF`): `checkS` first where
`Exact.sparseFirst`. -/
def checkAnyF (pts : List (V3 κ)) (B : ChartBox) (depth : ℕ) (w : Centred κ)
    (pre : Option (Q4 κ) := none) : Bool :=
  if Exact.sparseFirst (α := κ) then w.checkS pts B depth pre || w.check pts B depth pre
  else w.check pts B depth pre || w.checkS pts B depth pre

@[csimp] theorem checkAny_eq_checkAnyF : @checkAny = @checkAnyF := by
  funext κ _ _ _ _ pts B depth w pre
  rw [checkAny, checkAnyF]
  split
  · exact Bool.or_comm _ _
  · rfl

/-- **Soundness of centred-support claims** by either check, on a box pre-rotated by `pre`. -/
theorem checkAny_sound_pre {pts : List (V3 κ)} {B : ChartBox} {depth : ℕ} {w : Centred κ}
    {pre : Option (Q4 κ)} (h : w.checkAny pts B depth pre = true) :
    (Polyhedron.ofPoints pts).NoFitRot B.poses (preRot (Exact.rePre pre)) := by
  simp only [checkAny, Bool.or_eq_true] at h
  rcases h with h | h
  · exact check_sound_pre h
  · exact checkS_sound_pre h

end Basis

end Centred

end Nieuwland.Check
