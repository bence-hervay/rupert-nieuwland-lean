import Modules.Check.Chart.Affine
import Modules.Check.Chart.Rechart
import Modules.Check.Sign.SparsePull
import Modules.Check.Leaf.WZoom
import Modules.NoFit.Dense

/-!
# Chart trees

A chart tree (`ChartTree` evidence, `code/src/proof/tree.rs`) proves `NoFit` on its claim box
with a family tree (`FTree`, the G1 core of `lean/DESIGN.md` §8) whose leaves certify weak
conditions on closed boxes (`Modules/Check/Chart/TreeLeaf.lean`).

* **Root.** Slots `0, …, 4` hold the chart coordinates `(s, t, x₀, x₁, x₂)` of the claim box, the
  last slot `n - 1` is the unit slot, fixed at `1 / L`, and the slots between them, the radius
  slots of blow-ups, are fixed at `0` (`rootBox`). The root map is the chart map, the view
  `homView a 1 s t` and the quaternion `homQuat k 1 (x₀, x₁, x₂)` (`rootMap`,
  `TreeChecker::root`).
* **Steps.** Splits (S1), weighted blow-ups (S3), whose centres are multiples of `1 / L`,
  slot-affine changes (S2a, `Modules/Check/Chart/Affine.lean`) and re-charts (S2b,
  `Modules/Check/Chart/Rechart.lean`).
* **Leaves.** Obstruction and combination leaves (L1, L2; `TObst`), outside leaves (L3;
  `TOut`) and, in trees with symmetry data, exclusion leaves (L4; `TExcl`).
* **Soundness.** A pose strictly inside the claim box whose view direction is off the
  exceptional set of the leaves (zero sets of nonzero linear forms of the view direction) is
  covered by a leaf (`ChartTree.concl_interior`). An obstruction or combination leaf proves no fit
  there; an outside leaf cannot cover it; an exclusion leaf excludes it or puts it in the null set.
  - Without symmetry data (`ChartTree.check_sound`), part (a) of the density theorem
    (`Polyhedron.noFit_box_of_interior`) extends `NoFit` to the closed box.
  - With symmetry data (`ChartTree.check_settled_pre`), every pose of the closed box is settled:
    the poses on the boundary of the box and on the exceptional set are null (part (b),
    `Modules/Check/Leaf/Null.lean`).

Large trees are checked in parts (`ChartTree.check_of_parts`), as weighted zooms are.

**Pre-rotated boxes.** On a claim box pre-rotated by `q_c`, the root map, the steps and outside
leaves are unchanged (chart-coordinate statements), obstruction and exclusion leaves take their
polynomials at `q q_c` (`PosePoly.pre`), and every leaf checks that `q_c ≠ 0`. The density
argument holds for fits with the rotation followed by `R(q_c)`
(`Polyhedron.noFitRot_box_of_interior`, `ChartTree.check_sound_pre`), and settles the poses
`(u, R R(q_c))`: on the boundary of the box, `q` lies on a rational hyperplane, so `q q_c` lies on
a hyperplane over the field (`mem_null_of_coord`).
-/

open Matrix

namespace Nieuwland

theorem chartPose_coords (p : ChartPose) : chartPose p.view p.rot p.coords = p := by
  obtain ⟨a, s, t, k, x⟩ := p
  simp only [chartPose, ChartPose.coords, ChartPose.mk.injEq, true_and]
  refine ⟨rfl, rfl, ?_⟩
  funext i
  fin_cases i <;> rfl

theorem coords_chartPose (a : Fin 3) (k : Fin 4) (y : Fin 5 → ℝ) :
    (chartPose a k y).coords = y := by
  funext i
  fin_cases i <;> rfl

namespace Check

open Pull

/-! ### The root -/

section Root

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The root map of a chart tree in the view chart `a` and the rotation chart `k`: the view
`homView a 1 x₀ x₁` and the quaternion `homQuat k 1 (x₂, x₃, x₄)`. -/
def rootMap (a : Fin 3) (k : Fin 4) : GenMap κ where
  run kk x := outOf (homView a (kk (Exact.ofInt 1)) (x 0) (x 1))
    (homQuat k (kk (Exact.ofInt 1)) ⟨x 2, x 3, x 4⟩)
  natural f hf kk x := by
    funext i
    rw [Function.comp_apply, map_outOf f, map_homView, map_homQuat]
    rfl
  all kk x := outAll (homView a (kk (Exact.ofInt 1)) (x 0) (x 1))
    (homQuat k (kk (Exact.ofInt 1)) ⟨x 2, x 3, x 4⟩)
  all_get _ _ := outAll_get _ _

/-- The root box of a chart tree with `n` slots and unit `1 / L` on the claim box `B`, over the
denominator of `B` times `L`: slots `0, …, 4` the ranges of `B`, the unit slot `n - 1` fixed at
`1 / L`, the others fixed at `0`. -/
def rootBox (B : ChartBox) (n L : ℕ) : Box where
  lo := (List.range n).map fun i ↦
    if i < 5 then L * B.box.lo.getD i 0 else if i = n - 1 then (B.box.den : ℤ) else 0
  hi := (List.range n).map fun i ↦
    if i < 5 then L * B.box.hi.getD i 0 else if i = n - 1 then (B.box.den : ℤ) else 0
  den := B.box.den * L

/-- The point of the root box at the chart coordinates `y`. -/
noncomputable def rootPt (n L : ℕ) (y : Fin 5 → ℝ) : Fin n → ℝ := fun i ↦
  if h : (i : ℕ) < 5 then y ⟨i, h⟩ else if (i : ℕ) = n - 1 then (L : ℝ)⁻¹ else 0

theorem mem_rootBox {B : ChartBox} {n L : ℕ} (hL : 0 < L) (hden : 0 < B.box.den)
    {y : Fin 5 → ℝ} (hy : B.box.Mem 5 y) : (rootBox B n L).Mem n (rootPt n L y) := by
  intro i
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hd' : (B.box.den : ℝ) ≠ 0 := by exact_mod_cast hden.ne'
  simp only [rootBox, Box.getD_range_map _ _ _ i.isLt, rootPt]
  split_ifs with h5 hU
  · obtain ⟨h1, h2⟩ := hy ⟨i, h5⟩
    push_cast
    rw [mul_comm (B.box.den : ℝ), mul_div_mul_left _ _ hL', mul_div_mul_left _ _ hL']
    exact ⟨h1, h2⟩
  · push_cast
    rw [div_mul_cancel_left₀ hd']
    exact ⟨le_refl _, le_refl _⟩
  · simp

theorem ext_rootPt {n L : ℕ} (hn : 5 ≤ n) (y : Fin 5 → ℝ) {j : ℕ} (hj : j < 5) :
    ext n (rootPt n L y) j = y ⟨j, hj⟩ := by
  simp [Pull.ext, rootPt, show j < n by omega, hj]

theorem outU_rootMap (a : Fin 3) (k : Fin 4) (x : ℕ → ℝ) :
    outU ((rootMap (κ := κ) a k).run Exact.re x) = viewDir a (x 0) (x 1) := by
  simp only [rootMap, WFrame.outU_outOf, Exact.re_ofInt, Int.cast_one]
  simpa using toFun_homView a (1 : ℝ) (x 0) (x 1)

theorem outQ_rootMap (a : Fin 3) (k : Fin 4) (x : ℕ → ℝ) :
    outQ ((rootMap (κ := κ) a k).run Exact.re x) = chartQuat k ![x 2, x 3, x 4] := by
  simp only [rootMap, WFrame.outQ_outOf, Exact.re_ofInt, Int.cast_one]
  simpa using toFun_homQuat k (1 : ℝ) ![x 2, x 3, x 4]

theorem outQ_rootMap_ne (a : Fin 3) (k : Fin 4) (x : ℕ → ℝ) :
    outQ ((rootMap (κ := κ) a k).run Exact.re x) ≠ 0 := fun h ↦ by
  have h1 := congrFun h k
  rw [outQ_rootMap, chartQuat_self] at h1
  exact one_ne_zero h1

/-- **The root map represents the chart pose** of its chart coordinates. -/
theorem represents_rootPt {n L : ℕ} (hn : 5 ≤ n) (a : Fin 3) (k : Fin 4) (y : Fin 5 → ℝ) :
    Represents (chartPose a k y)
      ((rootMap (κ := κ) a k).run Exact.re (ext n (rootPt n L y))) := by
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_, ?_⟩
  · rw [outU_rootMap, one_smul, ext_rootPt hn y (by norm_num : 0 < 5),
      ext_rootPt hn y (by norm_num : 1 < 5)]
    rfl
  · rw [outQ_rootMap, one_smul, ext_rootPt hn y (by norm_num : 2 < 5),
      ext_rootPt hn y (by norm_num : 3 < 5), ext_rootPt hn y (by norm_num : 4 < 5)]
    rfl

end Root

/-! ### Trees -/

/-- A leaf of a chart tree. -/
inductive TLeaf (κ : Type) where
  /-- An obstruction or combination leaf (L1, L2). -/
  | obst (t : TObst κ)
  /-- An outside leaf (L3). -/
  | out (o : TOut)
  /-- An exclusion leaf (L4). -/
  | excl (x : TExcl)
  /-- An obstruction or combination leaf checked in rupert's bisection order `o`
  (`Pull.bisW`). -/
  | obstB (o : List (ℕ × ℕ)) (t : TObst κ)
  /-- An outside leaf checked in rupert's bisection order `o`. -/
  | outB (o : List (ℕ × ℕ)) (x : TOut)
  /-- An exclusion leaf checked in rupert's bisection order `o`. -/
  | exclB (o : List (ℕ × ℕ)) (x : TExcl)
  /-- An obstruction or combination leaf checked in rupert's bisection order `o` (`[]`: the
  engine's own), with the positive factors `f` of its anchor choices' weights, per part and
  choice (`Obst.polyOkS`). Below a slot-affine step Lean's slots hold rupert's values over scales
  `q`, so a choice's quotient by its monomial `x^e` is `q^e` times rupert's; the factors
  `q^(M - e)` make every combination a positive multiple of rupert's. -/
  | obstF (o : List (ℕ × ℕ)) (f : List (List ℤ)) (t : TObst κ)
  /-- The leaf `l` checked on its exact map (`GenMap.ofPolys`: the outputs of the leaf's map as
  sparse polynomials in the slots with exact coefficients, as rupert composes them,
  `Node::map_all`), with the sparse sign checks (`Modules/Check/Sign/SparsePull.lean`). -/
  | exact (l : TLeaf κ)

instance {κ : Type} : Inhabited (TLeaf κ) := ⟨.out ⟨0, false, [], 0⟩⟩

/-- The leaf without its bisection order and its checking mode. -/
def TLeaf.base {κ : Type} : TLeaf κ → TLeaf κ
  | .obstB _ t | .obstF _ _ t => .obst t
  | .outB _ x => .out x
  | .exclB _ x => .excl x
  | .exact l => l.base
  | l => l

/-- The bisection order of a leaf (`[]`: the engine's own, by the box widths). -/
def TLeaf.ord {κ : Type} : TLeaf κ → List (ℕ × ℕ)
  | .obstB o _ | .outB o _ | .exclB o _ | .obstF o _ _ => o
  | .exact l => l.ord
  | _ => []

/-- The factors of the anchor choices' weights of a leaf (`[]`: all `1`). -/
def TLeaf.facs {κ : Type} : TLeaf κ → List (List ℤ)
  | .obstF _ f _ => f
  | .exact l => l.facs
  | _ => []

/-- The leaf is checked on its exact map, with the sparse sign checks. -/
def TLeaf.isExact {κ : Type} : TLeaf κ → Bool
  | .exact _ => true
  | _ => false

/-- An instance step of a chart tree. -/
inductive TStep (κ : Type) where
  /-- A slot-affine change (S2a). -/
  | affine (A : Affine κ)
  /-- A re-chart (S2b). -/
  | rechart (R : Rechart κ)

section Steps

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The instance steps of a chart tree with `n` slots and the unit `1 / L`. -/
def tstep (n L : ℕ) : StepFn κ (TStep κ)
  | .affine A => Affine.step n A
  | .rechart R => Rechart.step n L R

theorem tstep_sound (n L : ℕ) : StepSound ⟨n, n - 1, []⟩ (tstep (κ := κ) n L) := by
  intro s
  cases s with
  | affine A => exact Affine.step_sound n A
  | rechart R => exact Rechart.step_sound n L R

end Steps

/-- Chart-tree evidence (`ChartTree` in `regional.rs`): the number of slots `n` (the chart
coordinates, the radius slots and the unit slot `n - 1`), the denominator `L` of the unit slot,
in which blow-up centres are integers, and the family tree. -/
structure ChartTree (κ : Type) where
  /-- The number of slots. -/
  n : ℕ
  /-- The unit slot is fixed at `1 / L`. -/
  L : ℕ
  /-- The tree. -/
  tree : FTree (TLeaf κ) (TStep κ)

namespace ChartTree

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The slots: `n`, the unit slot `n - 1`, none protected. -/
def slots (T : ChartTree κ) : Slots := ⟨T.n, T.n - 1, []⟩

/-- The leaves of the tree on the claim box `B`. -/
def leaves (B : ChartBox) (T : ChartTree κ) : Option (List (FLeaf κ (TLeaf κ))) :=
  T.tree.cover T.slots (tstep T.n T.L) (rootMap B.view B.rot) GenMap.id (rootBox B T.n T.L)

/-- The map a leaf is checked on: for `exact` leaves the outputs of its map as sparse polynomials
(`GenMap.ofPolys`), which agree with the map at every real point (`sim_leafMap`). -/
def leafMap (x : FLeaf κ (TLeaf κ)) : GenMap κ :=
  bif x.data.isExact then GenMap.ofPolys x.map.polys else x.map

theorem sim_leafMap (x : FLeaf κ (TLeaf κ)) (z : ℕ → ℝ) :
    PoseSim ((leafMap x).run Exact.re z) (x.map.run Exact.re z) := by
  unfold leafMap
  cases x.data.isExact
  · exact PoseSim.refl _
  · exact GenMap.sim_ofPolys x.map z

/-- **The check of a leaf** of a chart tree with `n` slots on the claim box `B` pre-rotated by `pre`
if any, with the symmetry data `D?` of exclusion leaves, in the leaf's bisection order, on the
leaf's map (`leafMap`). Every leaf checks that the pre-rotation is not zero. Leaves checked on
their exact maps use the sparse sign checks (`TObst.checkX`, `TOut.checkX`, `TExcl.checkX`). -/
def leafOk (pts : List (V3 κ)) (D? : Option (SymmData κ)) (pre : Option (Q4 κ)) (B : ChartBox)
    (n : ℕ) (x : FLeaf κ (TLeaf κ)) : Bool :=
  Exact.preOk pre && match x.data.base with
  | .obst t => bif x.data.isExact then t.checkX pts n (leafMap x) x.box pre x.data.ord x.data.facs
      else t.check pts n (leafMap x) x.box pre x.data.ord x.data.facs
  | .out o => bif x.data.isExact then o.checkX B n (leafMap x) x.box x.data.ord
      else o.check B n (leafMap x) x.box x.data.ord
  | .excl e => match D? with
    | some D => bif x.data.isExact then e.checkX D n (leafMap x) x.box pre x.data.ord
        else e.check D n (leafMap x) x.box pre x.data.ord
    | none => false
  | _ => false

theorem preOk_of_leafOk {pts : List (V3 κ)} {D? : Option (SymmData κ)} {pre : Option (Q4 κ)}
    {B : ChartBox} {n : ℕ} {x : FLeaf κ (TLeaf κ)} (h : leafOk pts D? pre B n x = true) :
    Exact.preOk pre = true := by
  unfold leafOk at h
  simp only [Bool.and_eq_true] at h
  exact h.1

/-- The exceptional vectors of a leaf. -/
def leafExcs (pts : List (V3 κ)) (x : FLeaf κ (TLeaf κ)) : List (V3 κ) :=
  match x.data.base with
  | .obst t => t.excs pts
  | _ => []

/-- The claim box has positive widths and a positive denominator, there are slots for the chart
coordinates and the unit, and `L > 0`. -/
def boxOk (B : ChartBox) (T : ChartTree κ) : Bool :=
  decide (6 ≤ T.n) && decide (0 < T.L) && decide (0 < B.box.den) &&
    (List.range 5).all fun i ↦ decide (B.box.lo.getD i 0 < B.box.hi.getD i 0)

/-- **The check of a chart tree** on the claim box `B` pre-rotated by `pre` if any, with the
symmetry data `D?` of exclusion leaves: the box, the steps and the leaves. -/
def check (pts : List (V3 κ)) (D? : Option (SymmData κ)) (B : ChartBox) (T : ChartTree κ)
    (pre : Option (Q4 κ) := none) : Bool :=
  T.boxOk B && match T.leaves B with
    | some ls => ls.all (leafOk pts D? pre B T.n)
    | none => false

/-! #### The check in parts (as `WZoom.check_of_parts`) -/

/-- The check of a chart tree without the checks of its leaves: the box and the steps, with `m`
leaves. -/
def head (B : ChartBox) (T : ChartTree κ) (m : ℕ) : Bool :=
  T.boxOk B && match T.leaves B with
    | some ls => ls.length == m
    | none => false

/-- The checks of the leaves `a, …, b - 1`, with the pre-rotation `pre`. -/
def leavesOk (pts : List (V3 κ)) (D? : Option (SymmData κ)) (B : ChartBox) (T : ChartTree κ)
    (a b : ℕ) (pre : Option (Q4 κ) := none) : Bool :=
  decide (a ≤ b) && match T.leaves B with
    | some ls => ((ls.drop a).take (b - a)).all (leafOk pts D? pre B T.n)
    | none => false

/-- `leavesOk` with a progress line after each leaf (`Modules/Check/Leaf/Progress.lean`): what compiled
code runs (`leavesOk_eq_leavesOkP`). -/
def leavesOkP (pts : List (V3 κ)) (D? : Option (SymmData κ)) (B : ChartBox) (T : ChartTree κ)
    (a b : ℕ) (pre : Option (Q4 κ) := none) : Bool :=
  withLeaves (b - a) fun around ↦ decide (a ≤ b) && match T.leaves B with
    | some ls => allP (leafOk pts D? pre B T.n) around a 0 ((ls.drop a).take (b - a))
    | none => false

@[csimp] theorem leavesOk_eq_leavesOkP : @leavesOk = @leavesOkP := by
  funext κ _ _ _ _ pts D? B T a b pre
  simp only [leavesOk, leavesOkP, withLeaves_eq, allP_eq]

theorem leavesOk_trans {pts : List (V3 κ)} {D? : Option (SymmData κ)} {B : ChartBox}
    {T : ChartTree κ} {a b c : ℕ} {pre : Option (Q4 κ)} (h₁ : T.leavesOk pts D? B a b pre = true)
    (h₂ : T.leavesOk pts D? B b c pre = true) :
    T.leavesOk pts D? B a c pre = true := by
  unfold leavesOk at *
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂ ⊢
  obtain ⟨hab, h₁⟩ := h₁
  obtain ⟨hbc, h₂⟩ := h₂
  refine ⟨hab.trans hbc, ?_⟩
  cases hls : T.leaves B with
  | none => simp [hls] at h₁
  | some ls =>
    simp only [hls] at h₁ h₂ ⊢
    rw [show c - a = (b - a) + (c - b) by omega, List.take_add, List.all_append, h₁,
      Bool.true_and, List.drop_drop, show a + (b - a) = b by omega]
    exact h₂

/-- **The check from its parts.** -/
theorem check_of_parts {pts : List (V3 κ)} {D? : Option (SymmData κ)} {B : ChartBox}
    {T : ChartTree κ} {m : ℕ} {pre : Option (Q4 κ)} (h : T.head B m = true)
    (hl : T.leavesOk pts D? B 0 m pre = true) : T.check pts D? B pre = true := by
  unfold head at h
  unfold leavesOk at hl
  unfold check
  cases hls : T.leaves B with
  | none => simp [hls] at h
  | some ls =>
    simp only [hls, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h hl ⊢
    obtain ⟨hok, hm⟩ := h
    rw [List.drop_zero, Nat.sub_zero, ← hm, List.take_length] at hl
    exact ⟨hok, hl.2⟩

/-! #### Soundness -/

theorem excs_ne_of_check {pts : List (V3 κ)} {n : ℕ} {Ψ : GenMap κ} {b : Box} {t : TObst κ}
    {pre : Option (Q4 κ)} {o : List (ℕ × ℕ)} {f : List (List ℤ)}
    (h : t.check pts n Ψ b pre o f = true) :
    ∀ g ∈ t.excs pts, Exact.nonzeroV g = true := by
  simp only [TObst.check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Option.isSome_iff_exists] at h
  obtain ⟨⟨⟨-, hparts⟩, -⟩, -⟩ := h
  intro g hg
  obtain ⟨p, hp, hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨-, gs, hgs⟩ := hparts p hp
  rw [hgs, Option.getD_some] at hg
  exact Wit.excs_ne hgs g hg

/-- The exceptional vectors of the leaves are not zero. -/
theorem excs_ne {pts : List (V3 κ)} {D? : Option (SymmData κ)} {pre : Option (Q4 κ)}
    {B : ChartBox} {n : ℕ} {ls : List (FLeaf κ (TLeaf κ))}
    (h : ∀ x ∈ ls, leafOk pts D? pre B n x = true) :
    ∀ g ∈ ls.flatMap (leafExcs pts), Exact.nonzeroV g = true := by
  intro g hg
  obtain ⟨x, hx, hgx⟩ := List.mem_flatMap.mp hg
  have hok := h x hx
  unfold leafExcs at hgx
  unfold leafOk at hok
  cases hxd : x.data.base with
  | obst t =>
    rw [hxd] at hgx hok
    simp only [Bool.and_eq_true] at hok
    cases hxe : x.data.isExact
    · rw [hxe, Bool.cond_false] at hok
      exact excs_ne_of_check hok.2 g hgx
    · rw [hxe, Bool.cond_true] at hok
      exact TObst.excs_ne_of_checkX hok.2 g hgx
  | _ =>
    rw [hxd] at hgx
    simp at hgx

/-- The conclusion of a chart tree at a pose, with the rotation followed by the pre-rotation `c`:
no fit, or, with symmetry data `D` that checks, exclusion or a null pose. -/
def Concl (pts : List (V3 κ)) (D? : Option (SymmData κ)) (c : Option (Fin 4 → ℝ))
    (p : ChartPose) : Prop :=
  ¬ (Polyhedron.ofPoints pts).FitsAlong (viewDir p.view p.s p.t) (p.rotation * preRot c) ∨
    ∃ D, D? = some D ∧ (D.ok pts = true →
      (Polyhedron.ofPoints pts).ExcludedAt D.centre D.score.f (viewDir p.view p.s p.t)
          (p.rotation * preRot c) ∨
        (viewDir p.view p.s p.t, p.rotation * preRot c) ∈ null κ D.score)

/-- **Interior poses.** At a pose strictly inside the claim box, off the exceptional set of the
leaves, the leaf that covers it concludes. -/
theorem concl_interior {pts : List (V3 κ)} {D? : Option (SymmData κ)} {pre : Option (Q4 κ)}
    {B : ChartBox} {T : ChartTree κ} (hok : T.boxOk B = true) {ls : List (FLeaf κ (TLeaf κ))}
    (hls : T.leaves B = some ls)
    (h : ∀ x ∈ ls, leafOk pts D? pre B T.n x = true) {y : Fin 5 → ℝ}
    (hy : ∀ i : Fin 5, (B.box.lo.getD i 0 : ℝ) / B.box.den < y i ∧
      y i < (B.box.hi.getD i 0 : ℝ) / B.box.den)
    (hg : ∀ g ∈ ls.flatMap (leafExcs pts), Exact.reV g ⬝ᵥ viewDir B.view (y 0) (y 1) ≠ 0) :
    Concl pts D? (Exact.rePre pre) (chartPose B.view B.rot y) := by
  simp only [boxOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hn, hL⟩, hden⟩, -⟩ := hok
  have hY : (rootBox B T.n T.L).Mem T.n (rootPt T.n T.L y) :=
    mem_rootBox hL hden fun i ↦ ⟨(hy i).1.le, (hy i).2.le⟩
  obtain ⟨x, hx, z, hz, -, hsim⟩ : ∃ x ∈ ls, ∃ z : Fin T.n → ℝ, x.box.Mem T.n z ∧
      ProtEq T.slots (ext T.n z) (ext T.n (rootPt T.n T.L y)) ∧
      PoseSim (x.map.run Exact.re (ext T.n z))
        ((rootMap B.view B.rot).run Exact.re (ext T.n (rootPt T.n T.L y))) :=
    FTree.cover_sound (tstep_sound T.n T.L) T.tree hls _ hY
  replace hsim := (sim_leafMap x (ext T.n z)).trans hsim
  have hrep : Represents (chartPose B.view B.rot y) ((leafMap x).run Exact.re (ext T.n z)) :=
    (represents_rootPt (by omega) B.view B.rot y).of_sim hsim.symm
  have hok := h x hx
  unfold leafOk at hok
  cases hxd : x.data.base with
  | obst t =>
    rw [hxd] at hok
    simp only [Bool.and_eq_true] at hok
    obtain ⟨a', b', -, -, hu', hq'⟩ := hsim
    have hroot : outU ((rootMap (κ := κ) B.view B.rot).run Exact.re
        (ext T.n (rootPt T.n T.L y))) = viewDir B.view (y 0) (y 1) := by
      rw [outU_rootMap, ext_rootPt (by omega) y (by norm_num : 0 < 5),
        ext_rootPt (by omega) y (by norm_num : 1 < 5)]
      rfl
    have hexc : ∀ g ∈ t.excs pts,
        Exact.reV g ⬝ᵥ outU ((leafMap x).run Exact.re (ext T.n z)) ≠ 0 := by
      intro g hg' h0
      apply hg g (List.mem_flatMap.mpr ⟨x, hx, by simpa [leafExcs, hxd] using hg'⟩)
      rw [← hroot, hu', dotProduct_smul, h0, smul_zero]
    have hq : outQ ((leafMap x).run Exact.re (ext T.n z)) ≠ 0 := fun h0 ↦ by
      rw [h0, smul_zero] at hq'
      exact outQ_rootMap_ne B.view B.rot _ hq'
    have hpre := Exact.rePre_ne_zero hok.1
    cases hxe : x.data.isExact
    · rw [hxe, Bool.cond_false] at hok
      exact Or.inl ((TObst.check_sound hok.2 hpre hz hexc hq).noFit hrep)
    · rw [hxe, Bool.cond_true] at hok
      exact Or.inl ((TObst.checkX_sound hok.2 hpre hz hexc hq).noFit hrep)
  | out o =>
    rw [hxd] at hok
    simp only [Bool.and_eq_true] at hok
    have hout : bif o.upper then (B.box.hi.getD o.coord 0 : ℝ) / B.box.den ≤
          (chartPose B.view B.rot y).coords o.coord
        else (chartPose B.view B.rot y).coords o.coord ≤
          (B.box.lo.getD o.coord 0 : ℝ) / B.box.den := by
      cases hxe : x.data.isExact
      · rw [hxe, Bool.cond_false] at hok
        exact TOut.check_sound hok.2 hz rfl rfl hrep
      · rw [hxe, Bool.cond_true] at hok
        exact TOut.checkX_sound hok.2 hz rfl rfl hrep
    rw [coords_chartPose] at hout
    have hc := hy o.coord
    exfalso
    cases hup : o.upper <;> simp only [hup, Bool.cond_true, Bool.cond_false] at hout <;>
      linarith [hc.1, hc.2]
  | excl e =>
    rw [hxd] at hok
    cases hD? : D? with
    | none => simp [hD?] at hok
    | some D =>
      simp only [hD?, Bool.and_eq_true] at hok
      cases hxe : x.data.isExact
      · rw [hxe, Bool.cond_false] at hok
        exact Or.inr ⟨D, rfl, fun hD ↦
          TExcl.check_sound hD hok.2 (Exact.rePre_ne_zero hok.1) hz hrep⟩
      · rw [hxe, Bool.cond_true] at hok
        exact Or.inr ⟨D, rfl, fun hD ↦
          TExcl.checkX_sound hD hok.2 (Exact.rePre_ne_zero hok.1) hz hrep⟩
  | _ =>
    rw [hxd] at hok
    simp at hok

/-- **Soundness of chart trees** without symmetry data, on a box pre-rotated by `pre` if any. No
pose of the claim box fits with its rotation followed by the pre-rotation. -/
theorem check_sound_pre {pts : List (V3 κ)} {B : ChartBox} {T : ChartTree κ}
    {pre : Option (Q4 κ)} (h : T.check pts none B pre = true) :
    (Polyhedron.ofPoints pts).NoFitRot B.poses (preRot (Exact.rePre pre)) := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨hok, h⟩ := h
  have hok' := hok
  simp only [boxOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hok'
  obtain ⟨⟨⟨-, -⟩, hden⟩, hlt⟩ := hok'
  cases hls : T.leaves B with
  | none => simp [hls] at h
  | some ls =>
  simp only [hls, List.all_eq_true] at h
  have hd : (0 : ℝ) < B.box.den := by exact_mod_cast hden
  rintro p ⟨hv, hr, hp⟩ hfit
  rw [← chartPose_coords p, hv, hr] at hfit
  refine Polyhedron.noFitRot_box_of_interior _ B.view B.rot (preRot (Exact.rePre pre))
    (lo := fun i ↦ (B.box.lo.getD i 0 : ℝ) / B.box.den)
    (hi := fun i ↦ (B.box.hi.getD i 0 : ℝ) / B.box.den)
    (fun i ↦ div_lt_div_of_pos_right (by exact_mod_cast hlt i i.isLt) hd)
    ((ls.flatMap (leafExcs pts)).map Exact.reV) ?_ ?_ hp hfit
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact Exact.reV_ne_zero_of_nonzeroV (excs_ne h g' hg')
  · intro y hy hg
    rcases concl_interior hok hls h hy fun g hg' ↦ hg _ (List.mem_map_of_mem hg') with
      hno | ⟨D, hD, -⟩
    · exact hno
    · simp at hD

/-- **Soundness of chart trees** without symmetry data. No pose of the claim box fits. -/
theorem check_sound {pts : List (V3 κ)} {B : ChartBox} {T : ChartTree κ}
    (h : T.check pts none B = true) : (Polyhedron.ofPoints pts).NoFit B.poses := by
  have h0 := check_sound_pre h
  rwa [Exact.rePre_none, preRot_none, Polyhedron.noFitRot_one] at h0

/-- **Soundness of chart trees with symmetry data `D`** (part (b) of the density theorem), on a
box pre-rotated by `pre` if any. Every pose of the claim box is settled with its rotation followed
by the pre-rotation. -/
theorem check_settled_pre {pts : List (V3 κ)} {D : SymmData κ} {B : ChartBox} {T : ChartTree κ}
    {pre : Option (Q4 κ)} (hD : D.ok pts = true) (h : T.check pts (some D) B pre = true) :
    ∀ p ∈ B.poses, SettledRot pts D (Exact.rePre pre) p := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨hok, h⟩ := h
  have hok' := hok
  simp only [boxOk, Bool.and_eq_true, decide_eq_true_eq] at hok'
  obtain ⟨⟨⟨-, hL⟩, hden⟩, -⟩ := hok'
  have hd : ((B.box.den : ℤ) : ℝ) = B.box.den := Int.cast_natCast _
  cases hls : T.leaves B with
  | none => simp [hls] at h
  | some ls =>
  simp only [hls, List.all_eq_true] at h
  rintro p ⟨hv, hr, hp⟩
  -- The leaf over `p` checks that the pre-rotation is not zero.
  obtain ⟨x, hx, -⟩ := FTree.cover_sound (tstep_sound T.n T.L) T.tree hls _
    (mem_rootBox hL hden hp)
  have hpre := Exact.rePre_ne_zero (preOk_of_leafOk (h x hx))
  -- Poses on the boundary of the box are null.
  by_cases hb : ∃ i : Fin 5, p.coords i = (B.box.lo.getD i 0 : ℝ) / B.box.den ∨
      p.coords i = (B.box.hi.getD i 0 : ℝ) / B.box.den
  · obtain ⟨i, hi⟩ := hb
    have hd0 : (B.box.den : ℤ) ≠ 0 := by exact_mod_cast hden.ne'
    rcases hi with hi | hi
    · exact Or.inr (Or.inr (mem_null_of_coord (r := B.box.lo.getD i 0) p hpre i hd0
        (by rw [hi, hd])))
    · exact Or.inr (Or.inr (mem_null_of_coord (r := B.box.hi.getD i 0) p hpre i hd0
        (by rw [hi, hd])))
  push Not at hb
  -- Poses on the exceptional set are null.
  by_cases he : ∃ g ∈ ls.flatMap (leafExcs pts), Exact.reV g ⬝ᵥ viewDir p.view p.s p.t = 0
  · obtain ⟨g, hg, h0⟩ := he
    exact Or.inr (Or.inr (mem_null_of_view (excs_ne h g hg) h0))
  push Not at he
  -- Interior poses.
  have hc := concl_interior hok hls h (y := p.coords)
    (fun i ↦ ⟨lt_of_le_of_ne (hp i).1 (hb i).1.symm, lt_of_le_of_ne (hp i).2 (hb i).2⟩)
    (fun g hg ↦ by rw [← hv]; exact he g hg)
  rw [← hv, ← hr, chartPose_coords] at hc
  rcases hc with hno | ⟨D', hD', hc⟩
  · exact Or.inl hno
  · cases hD'
    exact Or.inr (hc hD)

end ChartTree

end Check

end Nieuwland
