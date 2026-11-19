import Modules.Check.Leaf.FamilyLeaf
import Modules.Check.Sign.SparsePull
import Modules.Check.Polynomial.Linear
import Modules.Check.Leaf.LocalExcl
import Modules.Check.Leaf.Progress

/-!
# Weighted zooms

Weighted-zoom evidence (`WeightedZoom` in `code/src/proof/regional/wzoom.rs`) proves that every
pose of a chart box `B` has no fit or is excluded, around an exact centre `P₀` where touch sheets
cross. It is an instance of the pose families of `Modules/Check/Leaf/Family.lean`.

**The frame.** With the block-diagonal frame `M = diag(Mv, Mr)` and the weights `k`, every point
`y` of `B` is `P₀ + M z` with `z ∈ [-1, 1]⁵` (`WFrame.ok`: `M⁻¹` up to the determinants, and
`coverOk`, bounds of the linear forms `z = M⁻¹ (y - P₀)` by their values at the corners of `B`),
and `z_i = δ^{k_i} f_i` with `δ ∈ [0, 1]` and `f` on a face `f_j = ±1` of a coordinate with
`k_j > 0` (`exists_gauge`); a weight-`0` coordinate is a free slot. The centre and the frame are
exact values (`κ`, with zero and sign tests): `P₀ = p0 / L` and `M = m / L`, and the chart
coordinates `y_r` times `L` are the polynomials `WFrame.chartY` of the slots
(`WFrame.exists_top`).

**Slots.** `0` is `δ`, `1, …, 5` are `f₀, …, f₄`, `6, …, 9` the radii of nested zooms, and `10`
the unit slot, fixed at `1 / E`, where `E` is a common denominator of the centres of nested
zooms. The map of the top-level faces (`WFrame.top`) has outputs `(L u, L q)`, the view direction
and the chart quaternion of `y` times `L`. `δ` and the weight-`0` coordinate are protected.

**Faces.** Each top-level face `(j, upper)` has a family tree (`FTree`) with splits and nested
zooms (weighted blow-ups); its leaves are obstruction or combination leaves (`Obst`), excluded
leaves and outside leaves (`Modules/Check/Leaf/FamilyLeaf.lean`). Obstruction premises are checked at
the images of the vertices of the leaf box under the view outputs (`hullPts`), with the blow-up
at the centre view where the view weights are equal (`WFrame.blowDir`, `WFrame.top_blow`): the
view is `U₀ + δ^k w`, and premises that fail at `U₀` hold where `δ > 0`.

**The centre set.** At `δ = 0` the top map depends only on the weight-`0` slot
(`WFrame.top_centre`), so the image is the point `P₀` or a segment. It must be covered by
obstruction leaves whose premises hold at all views, with `δ = 0` in their boxes and, for a
segment, ranges of the free slot that chain across `[-1, 1]` (`WFrame.centreOk`).

The conclusion (`WZoom.check_sound`): at every pose of `B` there is no fit, or (with symmetry
data) the pose is excluded. On a box pre-rotated by `q_c` (`WZoom.check_sound_pre`), obstruction
leaves take their witnesses at `q q_c` (`PosePoly.pre`) and prove no fit with the rotation
followed by `R(q_c)`; the frame, the maps and outside leaves are chart-coordinate statements and do
not change, and excluded leaves are refused, as in Rust.

**Local exclusion** (`check … (loc := true)`, `WZoom.check_sound_loc`): a local exclusion leaf
(`WLeaf.loc`, `LocLeaf.check` in `Modules/Check/Leaf/LocalExcl.lean`) maps the poses it represents by a
pose map of the symmetry data to poses of `B` whose rotation chart coordinates are strictly closer
to those of the frame centre (`WFrame.locCentre`). Every pose of `B` then has no fit or is locally
excluded, and `noFitRot_of_local` gives `NoFit` on `B` with no global premise
(`Evidence.wzoomLoc`). As in Rust, local exclusion leaves and excluded leaves are not mixed: the
flag `loc` admits the former and refuses the latter.
-/

open Matrix

namespace Nieuwland.Check

open Pull

/-! ### Frames -/

/-- The exact data of a weighted zoom (`WFrame` in `wzoom.rs`) over a common denominator `L`: the
centre `P₀ = p0 / L`, the blocks `Mv = mv / L` (view) and `Mr = mr / L` (rotation) of the frame,
the weights, the inverses of the blocks up to their determinants (`mv nv = dv I`, `mr nr = dr I`),
and the denominator `E` of the unit slot. The centre, the blocks and their inverses are exact
values in `κ`. -/
structure WFrame (κ : Type) where
  /-- The common denominator of the centre and the frame. -/
  L : ℕ
  /-- The centre, times `L`. -/
  p0 : List κ
  /-- The view block of the frame, times `L`, by rows. -/
  mv : List (List κ)
  /-- The rotation block of the frame, times `L`, by rows. -/
  mr : List (List κ)
  /-- The weights of `f₀, …, f₄`. -/
  w : List ℕ
  /-- The inverse of `mv` times `dv`. -/
  nv : List (List κ)
  /-- The determinant of `mv` (or any nonzero multiple). -/
  dv : κ
  /-- The inverse of `mr` times `dr`. -/
  nr : List (List κ)
  /-- The determinant of `mr` (or any nonzero multiple). -/
  dr : κ
  /-- The denominator of the unit slot. -/
  E : ℕ

namespace WFrame

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] (F : WFrame κ)

/-- Coordinate `r` of the centre, times `L`. -/
def cen (r : ℕ) : κ := F.p0.getD r (Exact.ofInt 0)

section Generic

variable {α β : Type*} [Add α] [Sub α] [Mul α] [Add β] [Sub β] [Mul β]

/-- The term `M_rj δ^{k_j} f_j` of a chart coordinate, with the entry `mrow = L M_rj` and the
column `j` (slot `j + 1`). -/
def term (kk : κ → α) (x : ℕ → α) (mrow : κ) (j : ℕ) : α :=
  kk mrow * powG (kk (Exact.ofInt 1)) (x 0) (F.w.getD j 0) * x (j + 1)

/-- The numerator `L y_r` of chart coordinate `r` at the slots `x`: `p0_r + ∑_j L M_rj δ^{k_j} f_j`
over the block of `r` (`top_node` in `wzoom.rs`). -/
def chartY (kk : κ → α) (x : ℕ → α) (r : ℕ) : α :=
  if r < 2 then
    kk (F.cen r) + (F.term kk x (ent F.mv r 0) 0 + F.term kk x (ent F.mv r 1) 1)
  else
    kk (F.cen r) + (F.term kk x (ent F.mr (r - 2) 0) 2 +
      (F.term kk x (ent F.mr (r - 2) 1) 3 + F.term kk x (ent F.mr (r - 2) 2) 4))

theorem map_chartY {f : α → β} (hf : IsArith f) (kk : κ → α) (x : ℕ → α) (r : ℕ) :
    f (F.chartY kk x r) = F.chartY (f ∘ kk) (f ∘ x) r := by
  unfold chartY term
  split_ifs <;> simp only [hf.map_add, hf.map_mul, map_powG hf.map_mul, Function.comp_apply]

end Generic

/-- **The map of the top-level faces**: outputs `0, 1, 2` are `homView a L (L y₀) (L y₁)`, outputs
`3, …, 6` are `homQuat k L (L y₂, L y₃, L y₄)`. -/
def top (a : Fin 3) (k : Fin 4) : GenMap κ where
  run kk x := outOf (homView a (kk (Exact.ofInt (F.L : ℤ))) (F.chartY kk x 0) (F.chartY kk x 1))
    (homQuat k (kk (Exact.ofInt (F.L : ℤ))) ⟨F.chartY kk x 2, F.chartY kk x 3, F.chartY kk x 4⟩)
  natural f hf kk x := by
    funext i
    rw [Function.comp_apply, map_outOf f, map_homView, map_homQuat]
    simp only [V3.map, F.map_chartY hf]
    rfl
  all kk x := outAll (homView a (kk (Exact.ofInt (F.L : ℤ))) (F.chartY kk x 0) (F.chartY kk x 1))
    (homQuat k (kk (Exact.ofInt (F.L : ℤ))) ⟨F.chartY kk x 2, F.chartY kk x 3, F.chartY kk x 4⟩)
  all_get _ _ := outAll_get _ _

/-- **The direction of the blown-up view**, for equal view weights: the view of the top map is
`U₀ + δ^{k₀} w` with `w = homView a 0 (∑_j L Mv_0j f_j) (∑_j L Mv_1j f_j)` (`blowup_points` in
`wzoom.rs`, `top_blow`). -/
def blowDir (a : Fin 3) : GenMap κ where
  run kk x := outOf (homView a (kk (Exact.ofInt 0))
    (kk (ent F.mv 0 0) * x 1 + kk (ent F.mv 0 1) * x 2)
    (kk (ent F.mv 1 0) * x 1 + kk (ent F.mv 1 1) * x 2))
    ⟨kk (Exact.ofInt 0), kk (Exact.ofInt 0), kk (Exact.ofInt 0), kk (Exact.ofInt 0)⟩
  natural f hf kk x := by
    funext i
    rw [Function.comp_apply, map_outOf f, map_homView]
    simp only [Q4.map, hf.map_add, hf.map_mul]
    rfl
  all kk x := outAll (homView a (kk (Exact.ofInt 0))
    (kk (ent F.mv 0 0) * x 1 + kk (ent F.mv 0 1) * x 2)
    (kk (ent F.mv 1 0) * x 1 + kk (ent F.mv 1 1) * x 2))
    ⟨kk (Exact.ofInt 0), kk (Exact.ofInt 0), kk (Exact.ofInt 0), kk (Exact.ofInt 0)⟩
  all_get _ _ := outAll_get _ _

/-- The centre view `U₀ = homView a L p0₀ p0₁`. -/
def centreView (a : Fin 3) : V3 κ :=
  homView a (Exact.ofInt (F.L : ℤ)) (F.cen 0) (F.cen 1)

/-- The weight-`0` coordinates. -/
def flats : List ℕ := (List.range 5).filter fun j ↦ F.w.getD j 0 = 0

/-- The slots: `11` of them, the unit slot `10`, and `δ` and the weight-`0` slots protected. -/
def slots : Slots := ⟨11, 10, 0 :: F.flats.map (· + 1)⟩

/-- The box of the top-level face `(j, upper)` over the denominator `E`: `δ ∈ [0, 1]`,
`f ∈ [-1, 1]⁵` with `f_j = 1` (`upper`) or `-1`, the nested radii `0` and the unit slot
`1 / E`. -/
def topBox (j : ℕ) (upper : Bool) : Box where
  lo := (List.range 11).map fun i ↦
    if i = 0 then 0 else if i ≤ 5 then
      (if i = j + 1 then (bif upper then (F.E : ℤ) else -F.E) else -F.E)
    else if i = 10 then 1 else 0
  hi := (List.range 11).map fun i ↦
    if i = 0 then F.E else if i ≤ 5 then
      (if i = j + 1 then (bif upper then (F.E : ℤ) else -F.E) else F.E)
    else if i = 10 then 1 else 0
  den := F.E

/-- The ends of `v_j = d (L y_j - p0_j)` over the box `b` of chart coordinates, for the
coordinates `r₀ + j`, `j < n`. -/
def ends (b : Box) (r₀ n : ℕ) (upper : Bool) : List κ :=
  (List.range n).map fun j ↦
    Exact.ofInt (F.L * (bif upper then b.hi else b.lo).getD (r₀ + j) 0) -
      Exact.ofInt (b.den : ℤ) * F.cen (r₀ + j)

/-- **The frame is valid and covers the chart box `B`**: positive denominators, a positive
weight, at most one weight `0`, invertible blocks, and `|M⁻¹ (y - P₀)| ≤ 1` on `B`. -/
def ok (B : ChartBox) : Bool :=
  decide (0 < F.L) && decide (0 < F.E) && decide (0 < B.box.den) &&
    (List.range 5).any (fun j ↦ decide (0 < F.w.getD j 0)) && decide (F.flats.length ≤ 1) &&
    Exact.nonzero F.dv && Exact.nonzero F.dr && mulOk 2 F.mv F.nv F.dv &&
    mulOk 3 F.mr F.nr F.dr &&
    coverOk 2 F.nv (Exact.ofInt (B.box.den : ℤ) * F.dv) (F.ends B.box 0 2 false)
      (F.ends B.box 0 2 true) &&
    coverOk 3 F.nr (Exact.ofInt (B.box.den : ℤ) * F.dr) (F.ends B.box 2 3 false)
      (F.ends B.box 2 3 true)

/-! #### Meaning -/

theorem outU_outOf (U : V3 ℝ) (Q : Q4 ℝ) : outU (outOf U Q) = U.toFun := by
  funext i
  fin_cases i <;> rfl

theorem outQ_outOf (U : V3 ℝ) (Q : Q4 ℝ) : outQ (outOf U Q) = Q.toFun := by
  funext i
  fin_cases i <;> rfl

theorem homView_self {R : Type*} (a : Fin 3) (D S T : R) : (homView a D S T).toFun a = D := by
  fin_cases a <;> rfl

theorem homQuat_self {R : Type*} (k : Fin 4) (D : R) (X : V3 R) : (homQuat k D X).toFun k = D := by
  fin_cases k <;> rfl

variable {F}

theorem top_view_ne (hL : 0 < F.L) (a : Fin 3) (k : Fin 4) (x : ℕ → ℝ) :
    outU ((F.top a k).run Exact.re x) ≠ 0 := fun h ↦ by
  have h1 := congrFun h a
  simp only [top, outU_outOf, homView_self, Pi.zero_apply, Exact.re_ofInt, Int.cast_natCast] at h1
  exact (Nat.cast_pos.mpr hL).ne' h1

theorem top_quat_ne (hL : 0 < F.L) (a : Fin 3) (k : Fin 4) (x : ℕ → ℝ) :
    outQ ((F.top a k).run Exact.re x) ≠ 0 := fun h ↦ by
  have h1 := congrFun h k
  simp only [top, outQ_outOf, homQuat_self, Pi.zero_apply, Exact.re_ofInt, Int.cast_natCast] at h1
  exact (Nat.cast_pos.mpr hL).ne' h1

/-- **The top map represents the pose** whose chart coordinates `y_r` are `chartY / L`. -/
theorem represents_top (hL : 0 < F.L) {p : ChartPose} {x : ℕ → ℝ}
    (hy : ∀ r : Fin 5, F.chartY Exact.re x r = F.L * p.coords r) :
    Represents p ((F.top p.view p.rot).run Exact.re x) := by
  have hL' : (F.L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have h0 : F.chartY Exact.re x 0 = F.L * p.s := hy 0
  have h1 : F.chartY Exact.re x 1 = F.L * p.t := hy 1
  have h2 : F.chartY Exact.re x 2 = F.L * p.x 0 := hy 2
  have h3 : F.chartY Exact.re x 3 = F.L * p.x 1 := hy 3
  have h4 : F.chartY Exact.re x 4 = F.L * p.x 2 := hy 4
  refine ⟨F.L, F.L, hL', hL', ?_, ?_⟩
  · simp only [top, outU_outOf, Exact.re_ofInt, Int.cast_natCast]
    rw [h0, h1, toFun_homView]
  · simp only [top, outQ_outOf, Exact.re_ofInt, Int.cast_natCast]
    rw [h2, h3, h4, toFun_homQuat]

theorem term_re (x : ℕ → ℝ) (m : κ) (j : ℕ) :
    F.term Exact.re x m j = Exact.re m * (x 0 ^ F.w.getD j 0 * x (j + 1)) := by
  simp only [term, Exact.re_ofInt, Int.cast_one, powG_one]
  ring

theorem term_centre {x x' : ℕ → ℝ} (h0 : x 0 = 0) (h0' : x' 0 = 0)
    (hflat : ∀ j < 5, F.w.getD j 0 = 0 → x (j + 1) = x' (j + 1)) (m : κ) {j : ℕ} (hj : j < 5) :
    F.term Exact.re x m j = F.term Exact.re x' m j := by
  simp only [term_re, h0, h0']
  rcases Nat.eq_zero_or_pos (F.w.getD j 0) with hw | hw
  · rw [hw, hflat j hj hw]
  · rw [zero_pow hw.ne']
    ring

/-- **At the centre**, the top map depends only on the weight-`0` slots. -/
theorem top_centre {x x' : ℕ → ℝ} (h0 : x 0 = 0) (h0' : x' 0 = 0)
    (hflat : ∀ j < 5, F.w.getD j 0 = 0 → x (j + 1) = x' (j + 1)) (a : Fin 3) (k : Fin 4) :
    (F.top a k).run Exact.re x = (F.top a k).run Exact.re x' := by
  have hc : ∀ r, F.chartY Exact.re x r = F.chartY Exact.re x' r := by
    intro r
    unfold chartY
    split_ifs <;> simp only [term_centre h0 h0' hflat _ (by norm_num : (0 : ℕ) < 5),
      term_centre h0 h0' hflat _ (by norm_num : (1 : ℕ) < 5),
      term_centre h0 h0' hflat _ (by norm_num : (2 : ℕ) < 5),
      term_centre h0 h0' hflat _ (by norm_num : (3 : ℕ) < 5),
      term_centre h0 h0' hflat _ (by norm_num : (4 : ℕ) < 5)]
  simp only [top, hc]

/-- **The blown-up view**: with equal view weights, the view of the top map is the centre view
plus `δ^{k₀}` times the blow-up direction. -/
theorem top_blow (hw : F.w.getD 0 0 = F.w.getD 1 0) (a : Fin 3) (k : Fin 4) (x : ℕ → ℝ) :
    outU ((F.top a k).run Exact.re x) = Exact.reV (F.centreView a) +
      x 0 ^ F.w.getD 0 0 • outU ((F.blowDir a).run Exact.re x) := by
  simp only [top, blowDir, outU_outOf, centreView, chartY, term_re, ← hw, Exact.reV,
    map_homView, Nat.ofNat_pos, ↓reduceIte, Nat.one_lt_ofNat, Exact.re_ofInt, Int.cast_zero]
  funext i
  fin_cases a <;> fin_cases i <;>
    simp [homView, V3.toFun] <;> ring

/-! #### The frame covers the claim box -/

variable (F) in
/-- The frame coordinates `z = M⁻¹ (y - P₀)` of the chart coordinates `y`: `z_c` for `c < 2` from
the view block, `z_{2 + c}` from the rotation block. -/
noncomputable def frameZ (y : Fin 5 → ℝ) (c : ℕ) : ℝ :=
  if c < 2 then
    (∑ j ∈ Finset.range 2, Exact.re (ent F.nv c j) *
      (F.L * ext 5 y j - Exact.re (F.cen j))) / Exact.re F.dv
  else
    (∑ j ∈ Finset.range 3, Exact.re (ent F.nr (c - 2) j) *
      (F.L * ext 5 y (2 + j) - Exact.re (F.cen (2 + j)))) / Exact.re F.dr

theorem ends_le {B : ChartBox} {y : Fin 5 → ℝ} (hy : B.box.Mem 5 y) (hden : 0 < B.box.den)
    {r₀ n j : ℕ} (hj : j < n) (hr : r₀ + j < 5) :
    Exact.re ((F.ends B.box r₀ n false).getD j (Exact.ofInt 0)) ≤
        B.box.den * (F.L * ext 5 y (r₀ + j) - Exact.re (F.cen (r₀ + j))) ∧
      B.box.den * (F.L * ext 5 y (r₀ + j) - Exact.re (F.cen (r₀ + j))) ≤
        Exact.re ((F.ends B.box r₀ n true).getD j (Exact.ofInt 0)) := by
  have hd : (0 : ℝ) < B.box.den := by exact_mod_cast hden
  obtain ⟨h1, h2⟩ := hy ⟨r₀ + j, hr⟩
  rw [div_le_iff₀ hd] at h1
  rw [le_div_iff₀ hd] at h2
  have hL : (0 : ℝ) ≤ F.L := Nat.cast_nonneg _
  simp only [ends, Box.getD_range_map _ _ _ hj, Bool.cond_false, Bool.cond_true, Exact.re_sub,
    Exact.re_mul, Exact.re_ofInt]
  push_cast
  simp only [Pull.ext, hr, ↓reduceDIte]
  constructor <;> nlinarith

/-- **The frame coordinates of the claim box lie in `[-1, 1]`.** -/
theorem frameZ_abs {B : ChartBox} (h : F.ok B = true) {y : Fin 5 → ℝ} (hy : B.box.Mem 5 y)
    {c : ℕ} (hc : c < 5) : |F.frameZ y c| ≤ 1 := by
  simp only [ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, hden⟩, -⟩, -⟩, hdv⟩, hdr⟩, -⟩, -⟩, hcv⟩, hcr⟩ := h
  have hd : (0 : ℝ) < B.box.den := by exact_mod_cast hden
  have key (S Δ : ℝ) (hΔ : Δ ≠ 0) (hS : |B.box.den * S| ≤ |B.box.den * Δ|) : |S / Δ| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_of_pos hd] at hS
    rw [abs_div, div_le_one (abs_pos.mpr hΔ)]
    exact le_of_mul_le_mul_left hS hd
  have hsum (N : ℕ → ℝ) (v : ℕ → ℝ) (n : ℕ) : ∑ j ∈ Finset.range n, N j * (B.box.den * v j) =
      B.box.den * ∑ j ∈ Finset.range n, N j * v j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  unfold frameZ
  split_ifs with h2
  · have := coverOk_sound hcv (v := fun j ↦ B.box.den *
      (F.L * ext 5 y (0 + j) - Exact.re (F.cen (0 + j))))
      (fun j hj ↦ F.ends_le hy hden hj (by omega)) h2
    simp only [zero_add, Exact.re_mul, Exact.re_ofInt, Int.cast_natCast] at this
    rw [hsum (fun j ↦ Exact.re (ent F.nv c j))] at this
    exact key _ _ (Exact.re_ne_zero_of_nonzero hdv) this
  · have := coverOk_sound hcr (v := fun j ↦ B.box.den *
      (F.L * ext 5 y (2 + j) - Exact.re (F.cen (2 + j))))
      (fun j hj ↦ F.ends_le hy hden hj (by omega)) (by omega : c - 2 < 3)
    simp only [Exact.re_mul, Exact.re_ofInt, Int.cast_natCast] at this
    rw [hsum (fun j ↦ Exact.re (ent F.nr (c - 2) j))] at this
    exact key _ _ (Exact.re_ne_zero_of_nonzero hdr) this

/-- **The frame coordinates give back the chart coordinates** (view block). -/
theorem frameZ_view {B : ChartBox} (h : F.ok B = true) (y : Fin 5 → ℝ) {r : ℕ} (hr : r < 2) :
    ∑ c ∈ Finset.range 2, Exact.re (ent F.mv r c) * F.frameZ y c =
      F.L * ext 5 y r - Exact.re (F.cen r) := by
  simp only [ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hdv⟩, -⟩, hmv⟩, -⟩, -⟩, -⟩ := h
  have := mul_inv_apply (fun r c hr hc ↦ mulOk_apply hmv hr hc) (Exact.re_ne_zero_of_nonzero hdv)
    (fun j ↦ F.L * ext 5 y j - Exact.re (F.cen j)) hr
  rw [← this]
  refine Finset.sum_congr rfl fun c hc ↦ ?_
  simp only [frameZ, Finset.mem_range.mp hc, ↓reduceIte]

/-- **The frame coordinates give back the chart coordinates** (rotation block). -/
theorem frameZ_rot {B : ChartBox} (h : F.ok B = true) (y : Fin 5 → ℝ) {r : ℕ} (hr : r < 3) :
    ∑ c ∈ Finset.range 3, Exact.re (ent F.mr r c) * F.frameZ y (2 + c) =
      F.L * ext 5 y (2 + r) - Exact.re (F.cen (2 + r)) := by
  simp only [ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, hdr⟩, -⟩, hmr⟩, -⟩, -⟩ := h
  have := mul_inv_apply (fun r c hr hc ↦ mulOk_apply hmr hr hc) (Exact.re_ne_zero_of_nonzero hdr)
    (fun j ↦ F.L * ext 5 y (2 + j) - Exact.re (F.cen (2 + j))) hr
  rw [← this]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  simp only [frameZ, show ¬ 2 + c < 2 by omega, ↓reduceIte, Nat.add_sub_cancel_left]

/-- **Every pose of the claim box is represented at a point of a top-level face** `(j, upper)`
with `k_j > 0`. -/
theorem exists_top {B : ChartBox} (h : F.ok B = true) {p : ChartPose} (hp : p ∈ B.poses) :
    ∃ j upper, j < 5 ∧ 0 < F.w.getD j 0 ∧ ∃ z : Fin 11 → ℝ, (F.topBox j upper).Mem 11 z ∧
      Represents p ((F.top B.view B.rot).run Exact.re (ext 11 z)) := by
  classical
  obtain ⟨hpv, hpr, hy⟩ := hp
  have hok := h
  simp only [ok, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hL, hE⟩, -⟩, ⟨j₀, hj₀, hw₀⟩⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  have hG1 (c : ℕ) (hc : c < 5) : -1 ≤ F.frameZ p.coords c ∧ F.frameZ p.coords c ≤ 1 :=
    abs_le.mp (F.frameZ_abs hok hy hc)
  obtain ⟨j, upper, ρ, g, hjS, hρ0, hρ1, -, hgj, hall⟩ :=
    exists_gauge ((Finset.range 5).filter fun j ↦ 0 < F.w.getD j 0) (fun j ↦ F.w.getD j 0)
      (fun i hi ↦ (Finset.mem_filter.mp hi).2.ne') (lo := fun _ ↦ -1) (hi := fun _ ↦ 1)
      (c := fun _ ↦ 0) (x := F.frameZ p.coords) (fun _ _ ↦ by norm_num)
      (fun i hi ↦ hG1 i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1))
      ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj₀, hw₀⟩, by norm_num⟩
  obtain ⟨hj5, hwj⟩ := Finset.mem_filter.mp hjS
  rw [Finset.mem_range] at hj5
  have hall' (c : ℕ) (hc : c < 5) (hwc : 0 < F.w.getD c 0) :
      -1 ≤ g c ∧ g c ≤ 1 ∧ F.frameZ p.coords c = ρ ^ F.w.getD c 0 * g c := by
    have := hall c (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hc, hwc⟩)
    simp only [sub_zero, zero_add] at this
    exact this
  -- The point of the face.
  let z : Fin 11 → ℝ := fun i ↦ if (i : ℕ) = 0 then ρ else if (i : ℕ) ≤ 5 then
    (if 0 < F.w.getD (i - 1) 0 then g (i - 1) else F.frameZ p.coords (i - 1))
    else if (i : ℕ) = 10 then (F.E : ℝ)⁻¹ else 0
  have hzf (c : ℕ) (hc : c < 5) :
      ext 11 z 0 ^ F.w.getD c 0 * ext 11 z (c + 1) = F.frameZ p.coords c := by
    simp only [Pull.ext, show c + 1 < 11 by omega, show (0 : ℕ) < 11 by omega, ↓reduceDIte, z,
      ↓reduceIte, Nat.add_one_ne_zero, show c + 1 ≤ 5 by omega, Nat.add_sub_cancel]
    split_ifs with hwc
    · exact (hall' c hc hwc).2.2.symm
    · rw [Nat.eq_zero_of_not_pos hwc, pow_zero, one_mul]
  refine ⟨j, upper, hj5, hwj, z, ?_, ?_⟩
  · intro ⟨i, hi⟩
    have hE' : (0 : ℝ) < F.E := by exact_mod_cast hE
    have e1 : ((F.E : ℤ) : ℝ) / F.E = 1 := by push_cast; exact div_self hE'.ne'
    have e2 : ((-(F.E : ℤ) : ℤ) : ℝ) / F.E = -1 := by push_cast; rw [neg_div, div_self hE'.ne']
    simp only [topBox, Box.getD_range_map _ _ _ hi, z]
    by_cases h0 : i = 0
    · subst h0
      simp only [↓reduceIte, Int.cast_zero, zero_div, e1]
      exact ⟨hρ0, hρ1⟩
    by_cases h5 : i ≤ 5
    · by_cases hij : i = j + 1
      · subst hij
        simp only [Nat.add_one_ne_zero, ↓reduceIte, h5, Nat.add_sub_cancel, hwj]
        have hgj' : g j = bif upper then 1 else -1 := by simpa using hgj
        cases upper <;> simp only [Bool.cond_false, Bool.cond_true] at hgj' ⊢ <;>
          simp only [e1, e2, hgj', le_refl, and_self]
      · simp only [h0, ↓reduceIte, h5, hij, e1, e2]
        split_ifs with hwi
        · exact ⟨(hall' (i - 1) (by omega) hwi).1, (hall' (i - 1) (by omega) hwi).2.1⟩
        · exact hG1 (i - 1) (by omega)
    · by_cases h10 : i = 10
      · subst h10
        simp only [show (10 : ℕ) ≠ 0 by omega, show ¬ (10 : ℕ) ≤ 5 by omega, ↓reduceIte,
          Int.cast_one, one_div, le_refl, and_self]
      · simp only [h0, h5, h10, ↓reduceIte, Int.cast_zero, zero_div, le_refl, and_self]
  · rw [← hpv, ← hpr]
    have hterm (m : κ) (c : ℕ) (hc : c < 5) :
        F.term Exact.re (ext 11 z) m c = Exact.re m * F.frameZ p.coords c := by
      rw [term_re, hzf c hc]
    have hchart (r : ℕ) (hr : r < 5) :
        F.chartY Exact.re (ext 11 z) r = F.L * ext 5 p.coords r := by
      simp only [chartY]
      split_ifs with h2
      · rw [hterm _ 0 (by norm_num), hterm _ 1 (by norm_num)]
        have := F.frameZ_view hok p.coords h2
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at this
        linarith
      · rw [hterm _ 2 (by norm_num), hterm _ 3 (by norm_num), hterm _ 4 (by norm_num)]
        have := F.frameZ_rot hok p.coords (show r - 2 < 3 by omega)
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceAdd,
          show 2 + (r - 2) = r by omega] at this
        linarith
    refine F.represents_top hL fun r ↦ ?_
    rw [hchart r r.isLt]
    simp [Pull.ext]

omit [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] in
theorem mem_flats {j : ℕ} : j ∈ F.flats ↔ j < 5 ∧ F.w.getD j 0 = 0 := by
  simp [flats, List.mem_filter, List.mem_range]

omit [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] in
theorem zero_mem_prot : 0 ∈ F.slots.prot := List.mem_cons_self

omit [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] in
theorem flat_mem_prot {f : ℕ} (hf : f ∈ F.flats) : f + 1 ∈ F.slots.prot :=
  List.mem_cons_of_mem _ (List.mem_map_of_mem hf)

end WFrame

/-! ### Leaves -/

/-- A leaf of a weighted zoom. -/
inductive WLeaf (κ : Type) where
  /-- An obstruction or combination leaf. -/
  | obst (ob : Obst κ)
  /-- An excluded leaf. -/
  | excl (e : ExclLeaf)
  /-- An outside leaf. -/
  | out (o : OutLeaf)
  /-- A local exclusion leaf. -/
  | loc (l : LocLeaf)

instance {κ : Type} : Inhabited (WLeaf κ) := ⟨.out ⟨0, false, 0, 0⟩⟩

section Leaves

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- Weighted zooms have no instance steps. -/
def noStep : StepFn κ Empty := fun s ↦ s.elim

theorem noStep_sound (S : Slots) : StepSound S (noStep (κ := κ)) := fun s ↦ s.elim

theorem noStep_keeps (S : Slots) : StepKeeps S (noStep (κ := κ)) := fun s ↦ s.elim

/-- The ranges `[l / e, h / e]` cover `[a / d, 1]`: each starts at or below the end reached so
far, and one reaches `1`. -/
def chainOk (a : ℤ) (d : ℕ) : List (ℤ × ℤ × ℕ) → Bool
  | [] => false
  | (l, h, e) :: rest =>
    decide (0 < e) && decide (l * d ≤ a * e) && (decide (e ≤ h) || chainOk h e rest)

theorem chainOk_sound : ∀ (rs : List (ℤ × ℤ × ℕ)) {a : ℤ} {d : ℕ}, 0 < d →
    chainOk a d rs = true → ∀ t : ℝ, (a : ℝ) / d ≤ t → t ≤ 1 →
      ∃ r ∈ rs, (r.1 : ℝ) / r.2.2 ≤ t ∧ t ≤ (r.2.1 : ℝ) / r.2.2
  | [], _, _, _, h, _, _, _ => by simp [chainOk] at h
  | (l, hh, e) :: rest, a, d, hd, h, t, hat, ht1 => by
    simp only [chainOk, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
    obtain ⟨⟨he, hle⟩, hnext⟩ := h
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have he' : (0 : ℝ) < e := by exact_mod_cast he
    have hle' : (l : ℝ) / e ≤ a / d := by
      rw [div_le_div_iff₀ he' hd']
      exact_mod_cast hle
    by_cases hth : t ≤ (hh : ℝ) / e
    · exact ⟨(l, hh, e), List.mem_cons_self, hle'.trans hat, hth⟩
    · rw [not_le] at hth
      rcases hnext with hend | hrest
      · exfalso
        have h1 : (e : ℝ) ≤ hh := by exact_mod_cast hend
        have : (1 : ℝ) ≤ hh / e := by rwa [le_div_iff₀ he', one_mul]
        linarith
      · obtain ⟨r, hr, hr'⟩ := chainOk_sound rest he hrest t hth.le ht1
        exact ⟨r, List.mem_cons_of_mem _ hr, hr'⟩

/-- The default leaf, which is no centre leaf. -/
def dfltLeaf : FLeaf κ (WLeaf κ) := ⟨GenMap.id, GenMap.id, ⟨[], [], 0⟩, default⟩

/-- A centre leaf: an obstruction leaf whose premises hold at all views, on a box that is not
empty and contains points with `δ = 0`. -/
def centreLeaf (x : FLeaf κ (WLeaf κ)) : Bool :=
  (match x.data with
    | .obst ob => ob.strong
    | _ => false) &&
    decide (0 < x.box.den) && decide (x.box.lo.getD 0 0 ≤ 0) && decide (0 ≤ x.box.hi.getD 0 0) &&
    (List.range 11).all fun i ↦ decide (x.box.lo.getD i 0 ≤ x.box.hi.getD i 0)

omit [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] in
theorem mem_of_centreLeaf {ls : List (FLeaf κ (WLeaf κ))} {i : ℕ}
    (h : centreLeaf (ls.getD i dfltLeaf) = true) : ls.getD i dfltLeaf ∈ ls := by
  by_cases hi : i < ls.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  · rw [List.getD_eq_default _ _ (by omega)] at h
    simp [centreLeaf, dfltLeaf] at h

omit [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] in
/-- **Centre leaves have points with `δ = 0`**, with any value of slot `s > 0` in its range. -/
theorem exists_centre_point {x : FLeaf κ (WLeaf κ)} (h : centreLeaf x = true) {s : ℕ}
    (hs : 0 < s) {t : ℝ}
    (ht : (x.box.lo.getD s 0 : ℝ) / x.box.den ≤ t ∧ t ≤ (x.box.hi.getD s 0 : ℝ) / x.box.den) :
    ∃ z : Fin 11 → ℝ, x.box.Mem 11 z ∧ ext 11 z 0 = 0 ∧ (s < 11 → ext 11 z s = t) := by
  simp only [centreLeaf, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨-, hden⟩, hlo⟩, hhi⟩, hne⟩ := h
  have hd : (0 : ℝ) < x.box.den := by exact_mod_cast hden
  refine ⟨fun i ↦ if (i : ℕ) = 0 then 0 else if (i : ℕ) = s then t
    else (x.box.lo.getD i 0 : ℝ) / x.box.den, fun ⟨i, hi⟩ ↦ ?_, by simp [Pull.ext],
    fun hs' ↦ by simp [Pull.ext, hs', hs.ne']⟩
  simp only
  by_cases h0 : i = 0
  · subst h0
    simp only [↓reduceIte]
    constructor
    · exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hlo) hd.le
    · exact div_nonneg (by exact_mod_cast hhi) hd.le
  by_cases his : i = s
  · subst his
    simp only [h0, ↓reduceIte]
    exact ht
  · simp only [h0, his, ↓reduceIte, le_refl, true_and]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hne i hi) hd.le

end Leaves

namespace WFrame

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] (F : WFrame κ)

/-- The views of a leaf: the hull points of its view outputs, with the blow-up at the centre view
where the view weights are equal. -/
def views (a : Fin 3) (x : FLeaf κ (WLeaf κ)) : Option (Views κ) :=
  (hullPts x.map 11 x.box).map fun us ↦ ⟨us, if F.w.getD 0 0 = F.w.getD 1 0 then
    (hullPts ((F.blowDir a).comp x.slots) 11 x.box).map fun ws ↦ (F.centreView a, ws) else none⟩

/-- The rotation chart coordinates of the frame centre, about which local exclusion leaves
improve. -/
noncomputable def locCentre (r : Fin 3) : ℝ :=
  Exact.re (F.cen (2 + r.1)) / F.L

/-- **The check of a leaf** of the claim box `B` pre-rotated by `pre` if any, with the symmetry data
`sym` if any: excluded leaves only without a pre-rotation and without local exclusion (`loc`),
local exclusion leaves only with it. -/
def leafOk (pts : List (V3 κ)) (sym : Option (SymmData κ)) (pre : Option (Q4 κ)) (B : ChartBox)
    (loc : Bool) (x : FLeaf κ (WLeaf κ)) : Bool :=
  decide (0 < x.box.den) && match x.data with
    | .obst ob => match F.views B.view x with
      | some V => Exact.preOk pre && ob.checkS pts 11 x.map x.box V pre
      | none => false
    | .excl e => match sym, pre with
      | some D, none => !loc && e.checkAny D 11 x.map x.box
      | _, _ => false
    | .out o => o.checkAny B 11 x.map x.box
    | .loc l => match sym with
      | some D => loc && l.check D B pre F.L (fun r ↦ F.cen (2 + r.1)) 11 x.map x.box
      | none => false

/-- **The centre set is covered** by the leaves `centre` (indices into the leaves `ls`): centre
leaves, at least one, and for a weight-`0` coordinate `f` their ranges of slot `f + 1` chain across
`[-1, 1]`. -/
def centreOk (ls : List (FLeaf κ (WLeaf κ))) (centre : List ℕ) : Bool :=
  (centre.map fun i ↦ ls.getD i dfltLeaf).all centreLeaf && match F.flats with
    | [] => !centre.isEmpty
    | [f] => chainOk (-1) 1 ((centre.map fun i ↦ ls.getD i dfltLeaf).map fun x ↦
        (x.box.lo.getD (f + 1) 0, x.box.hi.getD (f + 1) 0, x.box.den))
    | _ => false

variable {F}

/-- The slot maps of leaves keep `δ`. -/
theorem slot0 {x : FLeaf κ (WLeaf κ)} (hd : Descends F.slots GenMap.id x.slots) (v : ℕ → ℝ) :
    x.slots.run Exact.re v 0 = v 0 := by
  obtain ⟨y, hpy, hy⟩ := hd v
  rw [hy]
  exact (hpy 0 F.zero_mem_prot).symm

theorem map_run {x : FLeaf κ (WLeaf κ)} {a : Fin 3} {k : Fin 4} (hb : x.base = F.top a k)
    (v : ℕ → ℝ) :
    x.map.run Exact.re v = (F.top a k).run Exact.re (x.slots.run Exact.re v) := by
  rw [FLeaf.map, hb]
  rfl

/-- **The views of a leaf contain its view directions.** -/
theorem views_mem {a : Fin 3} {k : Fin 4} {x : FLeaf κ (WLeaf κ)} {V : Views κ}
    (hV : F.views a x = some V) (hb : x.base = F.top a k)
    (hd : Descends F.slots GenMap.id x.slots) (hden : 0 < x.box.den) {z : Fin 11 → ℝ}
    (hz : x.box.Mem 11 z) :
    V.Mem (outU (x.map.run Exact.re (ext 11 z))) (ext 11 z 0 ^ F.w.getD 0 0) := by
  unfold views at hV
  obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hV
  refine ⟨coneBound_hullPts hus hden hz, fun U₀ ws hb' ↦ ?_⟩
  split_ifs at hb' with hw
  · obtain ⟨ws', hws, hpair⟩ := Option.map_eq_some_iff.mp hb'
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    refine ⟨1, one_pos, _, coneBound_hullPts hws hden hz, ?_⟩
    rw [one_smul, map_run hb, top_blow hw, slot0 hd]
    rfl

omit [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] in
theorem topBox_delta {j : ℕ} {upper : Bool} {z : Fin 11 → ℝ}
    (hz : (F.topBox j upper).Mem 11 z) : 0 ≤ ext 11 z 0 := by
  have h := (hz ⟨0, by norm_num⟩).1
  simp only [topBox, Box.getD_range_map _ _ _ (show 0 < 11 by norm_num), ↓reduceIte,
    Int.cast_zero, zero_div] at h
  simpa [Pull.ext] using h

omit [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] in
theorem topBox_free (hE : 0 < F.E) {j : ℕ} {upper : Bool} {z : Fin 11 → ℝ}
    (hz : (F.topBox j upper).Mem 11 z) {i : ℕ} (hi : i < 5) (hij : i ≠ j) :
    -1 ≤ ext 11 z (i + 1) ∧ ext 11 z (i + 1) ≤ 1 := by
  have hE' : (0 : ℝ) < F.E := by exact_mod_cast hE
  have h := hz ⟨i + 1, by omega⟩
  simp only [topBox, Box.getD_range_map _ _ _ (show i + 1 < 11 by omega),
    Nat.add_one_ne_zero, ↓reduceIte, show i + 1 ≤ 5 by omega,
    show i + 1 ≠ j + 1 by omega] at h
  simp only [Pull.ext, show i + 1 < 11 by omega, ↓reduceDIte]
  push_cast at h
  rwa [neg_div, div_self hE'.ne'] at h

/-- **Leaves where `δ > 0`**: no fit (with the pre-rotation), excluded, or locally excluded, at the
poses they represent. -/
theorem leafOk_pos {pts : List (V3 κ)} {sym : Option (SymmData κ)} {pre : Option (Q4 κ)}
    {loc : Bool} (hD : ∀ D, sym = some D → D.ok pts = true) {B : ChartBox}
    {x : FLeaf κ (WLeaf κ)} (h : F.leafOk pts sym pre B loc x = true)
    (hb : x.base = F.top B.view B.rot) (hd : Descends F.slots GenMap.id x.slots) (hL : 0 < F.L)
    {z : Fin 11 → ℝ} (hz : x.box.Mem 11 z) (hz0 : 0 < ext 11 z 0) {p : ChartPose}
    (hp : p ∈ B.poses) (hrep : Represents p (x.map.run Exact.re (ext 11 z))) :
    ¬ (Polyhedron.ofPoints pts).FitsAlong (viewDir p.view p.s p.t)
        (p.rotation * preRot (Exact.rePre pre)) ∨
      (∃ D, sym = some D ∧ pre = none ∧ loc = false ∧
        (Polyhedron.ofPoints pts).Excluded D.centre D.score.f p) ∨
      ∃ D, sym = some D ∧ loc = true ∧ LocalExcl D B pre F.locCentre p := by
  simp only [leafOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hden, h⟩ := h
  have hq : outQ (x.map.run Exact.re (ext 11 z)) ≠ 0 := by
    rw [map_run hb]
    exact top_quat_ne hL _ _ _
  have hu : outU (x.map.run Exact.re (ext 11 z)) ≠ 0 := by
    rw [map_run hb]
    exact top_view_ne hL _ _ _
  cases hx : x.data with
  | obst ob =>
    simp only [hx] at h
    cases hV : F.views B.view x with
    | none => simp [hV] at h
    | some V =>
      simp only [hV, Bool.and_eq_true] at h
      exact Or.inl ((Obst.checkS_sound h.2 (Exact.rePre_ne_zero h.1) hz
        (F.views_mem hV hb hd hden hz) (Or.inr (pow_pos hz0 _)) hq).noFit hrep)
  | excl e =>
    simp only [hx] at h
    cases hs : sym with
    | none => simp [hs] at h
    | some D =>
      cases hpr : pre with
      | some c => simp [hs, hpr] at h
      | none =>
        simp only [hs, hpr, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
        exact Or.inr (Or.inl ⟨D, rfl, rfl, h.1,
          (ExclLeaf.checkAny_sound (hD D hs) h.2 hz hz0 hu hq).excluded hrep⟩)
  | out o =>
    simp only [hx] at h
    exact (OutLeaf.checkAny_sound h hz hz0 hp hrep).elim
  | loc l =>
    simp only [hx] at h
    cases hs : sym with
    | none => simp [hs] at h
    | some D =>
      simp only [hs, Bool.and_eq_true] at h
      exact Or.inr (Or.inr ⟨D, rfl, h.1, LocLeaf.check_sound h.2 hz hz0 hp hrep⟩)

/-- **Centre leaves** prove no fit (with the pre-rotation) at all their points. -/
theorem leafOk_centre {pts : List (V3 κ)} {sym : Option (SymmData κ)} {pre : Option (Q4 κ)}
    {loc : Bool} {B : ChartBox} {x : FLeaf κ (WLeaf κ)} (h : F.leafOk pts sym pre B loc x = true)
    (hc : centreLeaf x = true) (hb : x.base = F.top B.view B.rot)
    (hd : Descends F.slots GenMap.id x.slots) (hL : 0 < F.L) {z : Fin 11 → ℝ}
    (hz : x.box.Mem 11 z) : NoFitRep pts (Exact.rePre pre) (x.map.run Exact.re (ext 11 z)) := by
  simp only [leafOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hden, h⟩ := h
  have hq : outQ (x.map.run Exact.re (ext 11 z)) ≠ 0 := by
    rw [map_run hb]
    exact top_quat_ne hL _ _ _
  simp only [centreLeaf, Bool.and_eq_true] at hc
  cases hx : x.data with
  | obst ob =>
    simp only [hx] at h hc
    cases hV : F.views B.view x with
    | none => simp [hV] at h
    | some V =>
      simp only [hV, Bool.and_eq_true] at h
      exact Obst.checkS_sound h.2 (Exact.rePre_ne_zero h.1) hz (F.views_mem hV hb hd hden hz)
        (Or.inl hc.1.1.1.1) hq
  | excl e => simp [hx] at hc
  | out o => simp [hx] at hc
  | loc l => simp [hx] at hc

end WFrame

/-! ### Weighted zooms -/

section Zooms

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The leaves of the top-level faces `(j, upper, tree)` of a family with base map `Φ` and face
boxes `bx`. -/
def facesCover (S : Slots) (Φ : GenMap κ) (bx : ℕ → Bool → Box) :
    List (ℕ × Bool × FTree (WLeaf κ) Empty) → Option (List (FLeaf κ (WLeaf κ)))
  | [] => some []
  | (j, u, T) :: rest =>
    optAppend (T.cover S noStep Φ GenMap.id (bx j u)) (facesCover S Φ bx rest)

theorem facesCover_face {S : Slots} {Φ : GenMap κ} {bx : ℕ → Bool → Box} :
    ∀ {fs : List (ℕ × Bool × FTree (WLeaf κ) Empty)} {ls : List (FLeaf κ (WLeaf κ))},
      facesCover S Φ bx fs = some ls → ∀ f ∈ fs, ∃ ls',
        f.2.2.cover S noStep Φ GenMap.id (bx f.1 f.2.1) = some ls' ∧ ∀ x ∈ ls', x ∈ ls
  | [], _, _, f, hf => by simp at hf
  | (j, u, T) :: rest, ls, h, f, hf => by
    simp only [facesCover] at h
    obtain ⟨a, c, ha, hc, rfl⟩ := optAppend_eq_some h
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨a, ha, fun x hx ↦ List.mem_append_left _ hx⟩
    · obtain ⟨ls', h', hsub⟩ := facesCover_face hc f hf
      exact ⟨ls', h', fun x hx ↦ List.mem_append_right _ (hsub x hx)⟩

theorem facesCover_leaf {S : Slots} {Φ : GenMap κ} {bx : ℕ → Bool → Box} :
    ∀ {fs : List (ℕ × Bool × FTree (WLeaf κ) Empty)} {ls : List (FLeaf κ (WLeaf κ))},
      facesCover S Φ bx fs = some ls → ∀ x ∈ ls, x.base = Φ ∧ Descends S GenMap.id x.slots
  | [], _, h, x, hx => by
    simp only [facesCover, Option.some.injEq] at h
    subst h
    simp at hx
  | (j, u, T) :: rest, ls, h, x, hx => by
    simp only [facesCover] at h
    obtain ⟨a, c, ha, hc, rfl⟩ := optAppend_eq_some h
    rcases List.mem_append.mp hx with hx | hx
    · exact FTree.descends_of_cover (noStep_keeps S) T ha x hx
    · exact facesCover_leaf hc x hx

/-- Weighted-zoom evidence (`WeightedZoom` in `wzoom.rs`): the frame, a family tree for each
top-level face `(j, upper)`, and the indices of the centre leaves among the leaves of all faces,
in order. -/
structure WZoom (κ : Type) where
  /-- The frame. -/
  frame : WFrame κ
  /-- The top-level faces with their trees. -/
  faces : List (ℕ × Bool × FTree (WLeaf κ) Empty)
  /-- The centre leaves. -/
  centre : List ℕ

end Zooms

namespace WZoom

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The face `(j, upper)` is present. -/
def hasFace (Z : WZoom κ) (j : ℕ) (upper : Bool) : Bool :=
  Z.faces.any fun f ↦ f.1 == j && f.2.1 == upper

/-- The leaves of all faces on the claim box `B`. -/
def leaves (Z : WZoom κ) (B : ChartBox) : Option (List (FLeaf κ (WLeaf κ))) :=
  facesCover Z.frame.slots (Z.frame.top B.view B.rot) Z.frame.topBox Z.faces

/-- **The check of a weighted zoom** on the claim box `B` pre-rotated by `pre` if any, with the
symmetry data `sym` if any, with local exclusion (`loc`) or not: the frame covers `B`, every face
`f_j = ±1` with `k_j > 0` has a tree, the trees check, the centre set is covered, and the leaves
check (in this order, cheap checks first). -/
def check (pts : List (V3 κ)) (sym : Option (SymmData κ)) (B : ChartBox) (Z : WZoom κ)
    (pre : Option (Q4 κ) := none) (loc : Bool := false) : Bool :=
  Z.frame.ok B &&
    (List.range 5).all (fun j ↦ decide (Z.frame.w.getD j 0 = 0) ||
      (Z.hasFace j true && Z.hasFace j false)) &&
    match Z.leaves B with
    | some ls => Z.frame.centreOk ls Z.centre && ls.all (Z.frame.leafOk pts sym pre B loc)
    | none => false

/-! #### The check in parts

The kernel keeps every intermediate value of a declaration until it is checked, so one `check`
of a weighted zoom with many leaves needs memory for all of them. `check_of_parts` assembles
`check` from `head` and the checks of runs of leaves (`leavesOk`), each its own declaration. The
runs are given by their ends, so that adjacent runs compose (`leavesOk_trans`) without
arithmetic. -/

/-- The check of a weighted zoom without the checks of its leaves: the frame, the faces, the
trees with `n` leaves in all, and the centre set. -/
def head (B : ChartBox) (Z : WZoom κ) (n : ℕ) : Bool :=
  Z.frame.ok B &&
    (List.range 5).all (fun j ↦ decide (Z.frame.w.getD j 0 = 0) ||
      (Z.hasFace j true && Z.hasFace j false)) &&
    match Z.leaves B with
    | some ls => ls.length == n && Z.frame.centreOk ls Z.centre
    | none => false

/-- The checks of the leaves `a, …, b - 1`, with the pre-rotation `pre` and local exclusion
`loc`. -/
def leavesOk (pts : List (V3 κ)) (sym : Option (SymmData κ)) (B : ChartBox) (Z : WZoom κ)
    (a b : ℕ) (pre : Option (Q4 κ) := none) (loc : Bool := false) : Bool :=
  decide (a ≤ b) && match Z.leaves B with
    | some ls => ((ls.drop a).take (b - a)).all (Z.frame.leafOk pts sym pre B loc)
    | none => false

/-- `leavesOk` with a progress line after each leaf (`Modules/Check/Leaf/Progress.lean`): what compiled
code runs (`leavesOk_eq_leavesOkP`). -/
def leavesOkP (pts : List (V3 κ)) (sym : Option (SymmData κ)) (B : ChartBox) (Z : WZoom κ)
    (a b : ℕ) (pre : Option (Q4 κ) := none) (loc : Bool := false) : Bool :=
  withLeaves (b - a) fun around ↦ decide (a ≤ b) && match Z.leaves B with
    | some ls => allP (Z.frame.leafOk pts sym pre B loc) around a 0 ((ls.drop a).take (b - a))
    | none => false

@[csimp] theorem leavesOk_eq_leavesOkP : @leavesOk = @leavesOkP := by
  funext κ _ _ _ _ pts sym B Z a b pre loc
  simp only [leavesOk, leavesOkP, withLeaves_eq, allP_eq]

theorem leavesOk_trans {pts : List (V3 κ)} {sym : Option (SymmData κ)} {B : ChartBox}
    {Z : WZoom κ} {a b c : ℕ} {pre : Option (Q4 κ)} {loc : Bool}
    (h₁ : Z.leavesOk pts sym B a b pre loc = true) (h₂ : Z.leavesOk pts sym B b c pre loc = true) :
    Z.leavesOk pts sym B a c pre loc = true := by
  unfold leavesOk at *
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂ ⊢
  obtain ⟨hab, h₁⟩ := h₁
  obtain ⟨hbc, h₂⟩ := h₂
  refine ⟨hab.trans hbc, ?_⟩
  cases hls : Z.leaves B with
  | none => simp [hls] at h₁
  | some ls =>
    simp only [hls] at h₁ h₂ ⊢
    rw [show c - a = (b - a) + (c - b) by omega, List.take_add, List.all_append, h₁,
      Bool.true_and, List.drop_drop, show a + (b - a) = b by omega]
    exact h₂

/-- **The check from its parts.** -/
theorem check_of_parts {pts : List (V3 κ)} {sym : Option (SymmData κ)} {B : ChartBox}
    {Z : WZoom κ} {n : ℕ} {pre : Option (Q4 κ)} {loc : Bool} (h : Z.head B n = true)
    (hl : Z.leavesOk pts sym B 0 n pre loc = true) : Z.check pts sym B pre loc = true := by
  unfold head at h
  unfold leavesOk at hl
  unfold check
  cases hls : Z.leaves B with
  | none => simp [hls] at h
  | some ls =>
    simp only [hls, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h hl ⊢
    obtain ⟨⟨hok, hfaces⟩, hn, hc⟩ := h
    rw [List.drop_zero, Nat.sub_zero, ← hn, List.take_length] at hl
    exact ⟨⟨hok, hfaces⟩, hc, hl.2⟩

omit [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] in
theorem centre_range {x : FLeaf κ (WLeaf κ)} (h : centreLeaf x = true) {i : ℕ} (hi : i < 11) :
    (x.box.lo.getD i 0 : ℝ) / x.box.den ≤ (x.box.hi.getD i 0 : ℝ) / x.box.den := by
  simp only [centreLeaf, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  exact div_le_div_of_nonneg_right (by exact_mod_cast h.2 i hi) (Nat.cast_nonneg _)

/-- **Soundness of weighted zooms**, on a box pre-rotated by `pre` if any, with local exclusion
`loc` or not. At every pose of the claim box there is no fit with the rotation followed by the
pre-rotation, or the pose is excluded by the symmetry data (no pre-rotation, no local exclusion),
or it is locally excluded (with local exclusion). -/
theorem check_sound_gen {pts : List (V3 κ)} {sym : Option (SymmData κ)}
    (hD : ∀ D, sym = some D → D.ok pts = true) {B : ChartBox} {Z : WZoom κ} {pre : Option (Q4 κ)}
    {loc : Bool} (h : Z.check pts sym B pre loc = true) {p : ChartPose} (hp : p ∈ B.poses) :
    ¬ (Polyhedron.ofPoints pts).FitsAlong (viewDir p.view p.s p.t)
        (p.rotation * preRot (Exact.rePre pre)) ∨
      (∃ D, sym = some D ∧ pre = none ∧ loc = false ∧
        (Polyhedron.ofPoints pts).Excluded D.centre D.score.f p) ∨
      ∃ D, sym = some D ∧ loc = true ∧ LocalExcl D B pre Z.frame.locCentre p := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨hok, hfaces⟩, h⟩ := h
  have hLE := hok
  simp only [WFrame.ok, Bool.and_eq_true, decide_eq_true_eq] at hLE
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hL, hE⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hLE
  cases hls : Z.leaves B with
  | none => simp [hls] at h
  | some ls =>
  simp only [hls, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hcen, hall⟩ := h
  obtain ⟨j, upper, hj5, hwj, z, hz, hrep⟩ := Z.frame.exists_top hok hp
  have hface : Z.hasFace j upper = true := by
    rcases hfaces j hj5 with h0 | ⟨ht, hf⟩
    · omega
    · cases upper
      · exact hf
      · exact ht
  obtain ⟨f, hf, hfj⟩ := List.any_eq_true.mp hface
  simp only [Bool.and_eq_true, beq_iff_eq] at hfj
  obtain ⟨ls', hcov, hsub⟩ := facesCover_face hls f hf
  rw [hfj.1, hfj.2] at hcov
  obtain ⟨x, hx, z', hz', hprot, hsim⟩ := FTree.cover_sound (noStep_sound _) f.2.2 hcov z hz
  have hxl := hsub x hx
  obtain ⟨hb, hd⟩ := facesCover_leaf hls x hxl
  rcases (Z.frame.topBox_delta hz).lt_or_eq with hpos | hzero
  · -- `δ > 0`: the leaf.
    have h0 : ext 11 z' 0 = ext 11 z 0 := hprot 0 Z.frame.zero_mem_prot
    exact Z.frame.leafOk_pos hD (hall x hxl) hb hd hL hz' (h0 ▸ hpos) hp (hrep.of_sim hsim.symm)
  · -- `δ = 0`: the centre set.
    left
    -- A centre leaf `c` with a point `w` at `δ = 0` whose weight-`0` slot agrees with `z`.
    have key : ∃ c ∈ ls, centreLeaf c = true ∧ ∃ w : Fin 11 → ℝ, c.box.Mem 11 w ∧
        ext 11 w 0 = 0 ∧ ∀ g ∈ Z.frame.flats, ext 11 w (g + 1) = ext 11 z (g + 1) := by
      simp only [WFrame.centreOk, Bool.and_eq_true, List.all_eq_true, List.mem_map] at hcen
      obtain ⟨hcl, hch⟩ := hcen
      have hcl' : ∀ i ∈ Z.centre, centreLeaf (ls.getD i dfltLeaf) = true :=
        fun i hi ↦ hcl _ ⟨i, hi, rfl⟩
      split at hch
      next hfl =>
        obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil Z.centre (by simpa using hch)
        have hc := hcl' i hi
        obtain ⟨w, hw, hw0, -⟩ := exists_centre_point hc (s := 1) one_pos
          ⟨le_refl _, centre_range hc (by norm_num)⟩
        exact ⟨_, mem_of_centreLeaf hc, hc, w, hw, hw0, by simp [hfl]⟩
      next g hfl =>
        have hg : g ∈ Z.frame.flats := by simp [hfl]
        obtain ⟨hg5, hgw⟩ := Z.frame.mem_flats.mp hg
        have hgj : g ≠ j := by
          rintro rfl
          omega
        obtain ⟨ht1, ht2⟩ := Z.frame.topBox_free hE hz hg5 hgj
        obtain ⟨r, hr, hrt⟩ := chainOk_sound _ one_pos hch (ext 11 z (g + 1)) (by simpa using ht1)
          ht2
        simp only [List.mem_map] at hr
        obtain ⟨c, ⟨i, hi, rfl⟩, rfl⟩ := hr
        have hc := hcl' i hi
        obtain ⟨w, hw, hw0, hwg⟩ := exists_centre_point hc (s := g + 1) (by omega) hrt
        refine ⟨_, mem_of_centreLeaf hc, hc, w, hw, hw0, fun g' hg' ↦ ?_⟩
        rw [hfl, List.mem_singleton] at hg'
        subst hg'
        exact hwg (by omega)
      next => simp at hch
    obtain ⟨c, hcl, hc, w, hw, hw0, hwf⟩ := key
    obtain ⟨hcb, hcd⟩ := facesCover_leaf hls c hcl
    have hno := Z.frame.leafOk_centre (hall c hcl) hc hcb hcd hL hw
    obtain ⟨y, hpy, hy⟩ := hcd (ext 11 w)
    have hsame : c.map.run Exact.re (ext 11 w) =
        (Z.frame.top B.view B.rot).run Exact.re (ext 11 z) := by
      rw [WFrame.map_run hcb, hy]
      change (Z.frame.top B.view B.rot).run Exact.re y = _
      refine WFrame.top_centre (by rw [← hpy 0 Z.frame.zero_mem_prot, hw0]) hzero.symm
        (fun g hg5 hgw ↦ ?_) _ _
      have hg : g ∈ Z.frame.flats := Z.frame.mem_flats.mpr ⟨hg5, hgw⟩
      rw [← hpy (g + 1) (Z.frame.flat_mem_prot hg), hwf g hg]
    exact (hno.of_sim (PoseSim.of_eq hsame)).noFit hrep

/-- **Soundness of weighted zooms**, on a box pre-rotated by `pre` if any. At every pose of the
claim box there is no fit with the rotation followed by the pre-rotation, or there is no
pre-rotation and the pose is excluded by the symmetry data. -/
theorem check_sound_pre {pts : List (V3 κ)} {sym : Option (SymmData κ)}
    (hD : ∀ D, sym = some D → D.ok pts = true) {B : ChartBox} {Z : WZoom κ} {pre : Option (Q4 κ)}
    (h : Z.check pts sym B pre = true) {p : ChartPose} (hp : p ∈ B.poses) :
    ¬ (Polyhedron.ofPoints pts).FitsAlong (viewDir p.view p.s p.t)
        (p.rotation * preRot (Exact.rePre pre)) ∨
      ∃ D, sym = some D ∧ pre = none ∧
        (Polyhedron.ofPoints pts).Excluded D.centre D.score.f p := by
  rcases check_sound_gen hD h hp with h' | ⟨D, hs, hpr, -, hex⟩ | ⟨-, -, hl, -⟩
  · exact Or.inl h'
  · exact Or.inr ⟨D, hs, hpr, hex⟩
  · cases hl

/-- **Soundness of weighted zooms with local exclusion**, on a box pre-rotated by `pre` if any. At
every pose of the claim box there is no fit with the rotation followed by the pre-rotation, or
the pose is locally excluded about the frame centre. -/
theorem check_sound_loc {pts : List (V3 κ)} {D : SymmData κ} (hD : D.ok pts = true)
    {B : ChartBox} {Z : WZoom κ} {pre : Option (Q4 κ)} (h : Z.check pts (some D) B pre true = true)
    {p : ChartPose} (hp : p ∈ B.poses) :
    ¬ (Polyhedron.ofPoints pts).FitsAlong (viewDir p.view p.s p.t)
        (p.rotation * preRot (Exact.rePre pre)) ∨ LocalExcl D B pre Z.frame.locCentre p := by
  rcases check_sound_gen (fun _ h ↦ by cases h; exact hD) h hp with
    h' | ⟨-, -, -, hl, -⟩ | ⟨D', hs, -, hex⟩
  · exact Or.inl h'
  · cases hl
  · obtain rfl := Option.some.inj hs
    exact Or.inr hex

/-- **Soundness of weighted zooms.** At every pose of the claim box there is no fit, or the pose
is excluded by the symmetry data. -/
theorem check_sound {pts : List (V3 κ)} {sym : Option (SymmData κ)}
    (hD : ∀ D, sym = some D → D.ok pts = true) {B : ChartBox} {Z : WZoom κ}
    (h : Z.check pts sym B = true) {p : ChartPose} (hp : p ∈ B.poses) :
    (∀ τ, ¬ (Polyhedron.ofPoints pts).FitsAt p τ) ∨
      ∃ D, sym = some D ∧ (Polyhedron.ofPoints pts).Excluded D.centre D.score.f p := by
  rcases check_sound_pre hD h hp with h' | ⟨D, hs, -, hex⟩
  · left
    intro τ hfit
    rw [Exact.rePre_none, preRot_none, mul_one] at h'
    exact h' (Polyhedron.fitsAlong_of_fitsAt hfit)
  · exact Or.inr ⟨D, hs, hex⟩

end WZoom

end Nieuwland.Check
