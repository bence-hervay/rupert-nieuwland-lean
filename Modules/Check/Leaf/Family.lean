import Modules.Check.Leaf.Gauge
import Modules.Check.Chart.Map
import Modules.Check.Sign.Vertex

/-!
# Pose families

The parameter walks of weighted zooms (`code/src/proof/regional/wzoom.rs`) and chart trees
(`code/src/proof/tree.rs`) share one core, G1 of `lean/DESIGN.md` §8. A *family* is a box `b` of
`n` slots with a map `Φ` (a `GenMap`) whose outputs at a slot point are a representative `(u, q)`
of a pose: outputs `0, 1, 2` are the view direction `u` (its line is the view) and outputs
`3, …, 6` the quaternion `q` (the rotation `R(q)`). Nonzero multiples of `u` and of `q` represent
the same pose (`PoseSim`). A *family tree* (`FTree`) refines a family by steps:

* **split** at a rational point of a slot; both parts keep `Φ`;
* **weighted blow-up** (`Blow`) of slots `J` around a centre `c` with weights `w` and a radius
  slot `ρ`, fixed at `0` before: every point of the box is `y_j = c_j + ρ^{w_j} g_j` on `J` with
  `ρ ∈ [0, 1]` and `g` on a face of `∏ [lo_j - c_j, hi_j - c_j]` that does not contain `0`
  (`exists_gauge`). Each such face has a subtree, whose map is `Φ` after the blow-up map;
* **instance steps** of a type `St`, checked by the instance and sound in the sense of
  `FTree.cover_sound`: a new family with the same poses (re-charts and slot-affine changes of
  chart trees).

Leaves carry data of a type `L` that the instance checks on the leaf's family.

**Units.** Maps compute with constants in a type `κ` of exact values (`GenMap κ`), read as reals
by `Exact.re`. A rational constant of a slot map is an integer multiple of the value of the *unit
slot* (`Slots.unit`), a slot fixed on every box.
**Protected slots** (`Slots.prot`) are never changed by a step: the top-level radius `δ` of a
weighted zoom and its flat coordinate, whose values decide what a leaf proves.

`FTree.cover` checks the steps and returns the leaves with their families. Soundness:

* `FTree.cover_sound`: every point of the box is covered by a point of some leaf, with the same
  protected slots and the same pose;
* `FTree.descends_of_cover`: if instance steps keep the protected slots, so does every leaf: its
  map is `Φ` after a map of slots that keeps them.
-/

namespace Nieuwland.Check

open Pull

/-! ### Representatives -/

/-- The view direction of the outputs `o` of a pose map: outputs `0, 1, 2`. -/
def outU (o : ℕ → ℝ) : Fin 3 → ℝ := fun i ↦ o i

/-- The quaternion of the outputs `o` of a pose map: outputs `3, 4, 5, 6`. -/
def outQ (o : ℕ → ℝ) : Fin 4 → ℝ := fun i ↦ o (i + 3)

/-- The outputs `o` and `o'` represent the same pose: the views and the quaternions are nonzero
multiples. -/
def PoseSim (o o' : ℕ → ℝ) : Prop :=
  ∃ a b : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ outU o' = a • outU o ∧ outQ o' = b • outQ o

namespace PoseSim

theorem refl (o : ℕ → ℝ) : PoseSim o o :=
  ⟨1, 1, one_ne_zero, one_ne_zero, by simp, by simp⟩

theorem of_eq {o o' : ℕ → ℝ} (h : o = o') : PoseSim o o' := h ▸ refl o

theorem symm {o o' : ℕ → ℝ} (h : PoseSim o o') : PoseSim o' o := by
  obtain ⟨a, b, ha, hb, hu, hq⟩ := h
  refine ⟨a⁻¹, b⁻¹, inv_ne_zero ha, inv_ne_zero hb, ?_, ?_⟩
  · rw [hu, smul_smul, inv_mul_cancel₀ ha, one_smul]
  · rw [hq, smul_smul, inv_mul_cancel₀ hb, one_smul]

theorem trans {o o' o'' : ℕ → ℝ} (h : PoseSim o o') (h' : PoseSim o' o'') : PoseSim o o'' := by
  obtain ⟨a, b, ha, hb, hu, hq⟩ := h
  obtain ⟨a', b', ha', hb', hu', hq'⟩ := h'
  exact ⟨a' * a, b' * b, mul_ne_zero ha' ha, mul_ne_zero hb' hb, by rw [hu', hu, smul_smul],
    by rw [hq', hq, smul_smul]⟩

end PoseSim

/-! ### Slots -/

/-- The slot layout of a family tree. -/
structure Slots where
  /-- The number of slots. -/
  n : ℕ
  /-- The unit slot, fixed on every box: rational constants of slot maps are integer multiples
  of its value. -/
  unit : ℕ
  /-- The protected slots, which no step changes. -/
  prot : List ℕ

/-- The protected slots of `z` and `y` agree. -/
def ProtEq (S : Slots) (z y : ℕ → ℝ) : Prop :=
  ∀ i ∈ S.prot, z i = y i

theorem ProtEq.trans {S : Slots} {x y z : ℕ → ℝ} (h : ProtEq S x y) (h' : ProtEq S y z) :
    ProtEq S x z :=
  fun i hi ↦ (h i hi).trans (h' i hi)

/-! ### Boxes -/

namespace Box

/-- The numerators and the denominator times `e`: the same box when `e > 0`. -/
def scale (b : Box) (e : ℕ) : Box :=
  ⟨b.lo.map (· * e), b.hi.map (· * e), b.den * e⟩

/-- The range of slot `k` replaced by `[l, h]` (numerators), on `n` slots. -/
def setRange (b : Box) (n k : ℕ) (l h : ℤ) : Box where
  lo := (List.range n).map fun i ↦ if i = k then l else b.lo.getD i 0
  hi := (List.range n).map fun i ↦ if i = k then h else b.hi.getD i 0
  den := b.den

/-- The part `≤ m / (den e)` of slot `k`, over the denominator `den e`. -/
def splitLo (b : Box) (n k e : ℕ) (m : ℤ) : Box :=
  (b.scale e).setRange n k (b.lo.getD k 0 * e) m

/-- The part `≥ m / (den e)` of slot `k`, over the denominator `den e`. -/
def splitHi (b : Box) (n k e : ℕ) (m : ℤ) : Box :=
  (b.scale e).setRange n k m (b.hi.getD k 0 * e)

theorem getD_map_mul (l : List ℤ) (e : ℕ) (i : ℕ) :
    (l.map (· * (e : ℤ))).getD i 0 = l.getD i 0 * e := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases l[i]? <;> simp

theorem cast_div_scale (a : ℤ) (d : ℕ) {e : ℕ} (he : 0 < e) :
    ((a * e : ℤ) : ℝ) / ((d * e : ℕ) : ℝ) = (a : ℝ) / d := by
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  push_cast
  rw [mul_div_mul_right _ _ he']

/-- **Splits cover.** Every point of the box lies in one of the two parts. -/
theorem mem_split {b : Box} {n k e : ℕ} (he : 0 < e) (m : ℤ) {y : Fin n → ℝ} (hy : b.Mem n y) :
    (b.splitLo n k e m).Mem n y ∨ (b.splitHi n k e m).Mem n y := by
  have hlo (i : ℕ) : ((b.lo.getD i 0 * e : ℤ) : ℝ) / ((b.den * e : ℕ) : ℝ) =
      (b.lo.getD i 0 : ℝ) / b.den := cast_div_scale _ _ he
  have hhi (i : ℕ) : ((b.hi.getD i 0 * e : ℤ) : ℝ) / ((b.den * e : ℕ) : ℝ) =
      (b.hi.getD i 0 : ℝ) / b.den := cast_div_scale _ _ he
  by_cases hk : ∃ hk : k < n, y ⟨k, hk⟩ ≤ (m : ℝ) / ((b.den * e : ℕ) : ℝ)
  · left
    obtain ⟨hk, hyk⟩ := hk
    intro i
    simp only [splitLo, setRange, scale, getD_range_map n _ _ i.2, getD_map_mul]
    split_ifs with hik
    · subst hik
      rw [hlo]
      exact ⟨(hy i).1, hyk⟩
    · rw [hlo, hhi]
      exact hy i
  · right
    intro i
    simp only [splitHi, setRange, scale, getD_range_map n _ _ i.2, getD_map_mul]
    split_ifs with hik
    · subst hik
      simp only [not_exists, not_le] at hk
      rw [hhi]
      exact ⟨(hk i.2).le, (hy i).2⟩
    · rw [hlo, hhi]
      exact hy i

end Box

/-! ### Weighted blow-ups -/

/-- A weighted blow-up: the slots `j` with their centres `c_j` (numerators over the box's
denominator, in multiples of the unit slot's numerator) and weights `w_j`, and the radius slot.
A slot listed twice counts with its first entry. -/
structure Blow where
  /-- The slots, centres and weights. -/
  zs : List (ℕ × ℤ × ℕ)
  /-- The radius slot. -/
  rho : ℕ

namespace Blow

/-- The centre and weight of slot `i`, if it is a slot of the blow-up. -/
def find (bl : Blow) (i : ℕ) : Option (ℤ × ℕ) :=
  (bl.zs.find? fun z ↦ z.1 == i).map (·.2)

/-- The centre of slot `i`, in units (`0` off the blow-up). -/
def cen (bl : Blow) (i : ℕ) : ℤ :=
  ((bl.find i).map (·.1)).getD 0

/-- The weight of slot `i` (`1` off the blow-up). -/
def wt (bl : Blow) (i : ℕ) : ℕ :=
  ((bl.find i).map (·.2)).getD 1

theorem find_isSome {bl : Blow} {i : ℕ} : (bl.find i).isSome = true ↔ ∃ z ∈ bl.zs, z.1 = i := by
  simp only [find, Option.isSome_map, List.find?_isSome, beq_iff_eq]

/-- The blow-up map of slots, with unit slot `U`: `x_j ↦ c_j x_U + x_ρ^{w_j} x_j` on the slots of
the blow-up, `x_ρ ↦ 0`, other slots unchanged. -/
def map {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] (U : ℕ) (bl : Blow) : GenMap κ where
  run k x i :=
    if (bl.find i).isSome then
      k (Exact.ofInt (bl.cen i)) * x U + powG (k (Exact.ofInt 1)) (x bl.rho) (bl.wt i) * x i
    else if i = bl.rho then k (Exact.ofInt 0) else x i
  natural f hf k x := by
    funext i
    simp only [Function.comp_apply]
    split_ifs
    · rw [hf.map_add, hf.map_mul, hf.map_mul, map_powG hf.map_mul]
    · rfl
    · rfl

/-- The box of the face `(j, upper)` of the blow-up of `b`: the slots of the blow-up hold
`g_i = y_i - c_i`, with slot `j` fixed at its upper (or lower) end, and the radius slot ranges
over `[0, 1]`. -/
def face (S : Slots) (bl : Blow) (b : Box) (j : ℕ) (upper : Bool) : Box where
  lo := (List.range S.n).map fun i ↦
    if (bl.find i).isSome then
      (if i = j then (bif upper then b.hi.getD i 0 else b.lo.getD i 0) else b.lo.getD i 0) -
        bl.cen i * b.lo.getD S.unit 0
    else if i = bl.rho then 0 else b.lo.getD i 0
  hi := (List.range S.n).map fun i ↦
    if (bl.find i).isSome then
      (if i = j then (bif upper then b.hi.getD i 0 else b.lo.getD i 0) else b.hi.getD i 0) -
        bl.cen i * b.lo.getD S.unit 0
    else if i = bl.rho then (b.den : ℤ) else b.hi.getD i 0
  den := b.den

/-- The faces that the blow-up of `b` needs: `(j, false)` where `lo_j < c_j`, and `(j, true)`
where `c_j < hi_j`. -/
def required (S : Slots) (bl : Blow) (b : Box) : List (ℕ × Bool) :=
  bl.zs.flatMap fun z ↦
    (if b.lo.getD z.1 0 < bl.cen z.1 * b.lo.getD S.unit 0 then [(z.1, false)] else []) ++
      (if bl.cen z.1 * b.lo.getD S.unit 0 < b.hi.getD z.1 0 then [(z.1, true)] else [])

/-- The blow-up of `b` is valid: the unit slot is fixed and the radius slot is fixed at `0`, both
off the blow-up and distinct; no protected slot changes; the slots of the blow-up are slots, with
positive weights and centres in their ranges, and one of their ranges is not a point. -/
def ok (S : Slots) (bl : Blow) (b : Box) : Bool :=
  decide (0 < b.den) && decide (S.unit < S.n) && decide (bl.rho < S.n) &&
    decide (bl.rho ≠ S.unit) && !(bl.find bl.rho).isSome && !(bl.find S.unit).isSome &&
    decide (b.hi.getD S.unit 0 = b.lo.getD S.unit 0) && decide (b.lo.getD bl.rho 0 = 0) &&
    decide (b.hi.getD bl.rho 0 = 0) &&
    S.prot.all (fun p ↦ decide (p ≠ bl.rho) && !(bl.find p).isSome) &&
    bl.zs.all (fun z ↦ decide (z.1 < S.n) && decide (0 < bl.wt z.1) &&
      decide (b.lo.getD z.1 0 ≤ bl.cen z.1 * b.lo.getD S.unit 0) &&
      decide (bl.cen z.1 * b.lo.getD S.unit 0 ≤ b.hi.getD z.1 0)) &&
    bl.zs.any (fun z ↦ decide (b.lo.getD z.1 0 < b.hi.getD z.1 0))

/-- The blow-up map keeps the slots off the blow-up other than the radius slot. -/
theorem map_run_of_not {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] {U : ℕ} {bl : Blow} {i : ℕ}
    (hi : (bl.find i).isSome = false) (hρ : i ≠ bl.rho) (k : κ → ℝ) (x : ℕ → ℝ) :
    (bl.map U).run k x i = x i := by
  simp [map, hi, hρ]

/-- **Blow-ups cover.** Every point `y` of a box with a valid blow-up is the image of a point `z`
of the box of a required face, with the same protected slots. -/
theorem exists_face {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] {S : Slots} {bl : Blow}
    {b : Box} (h : bl.ok S b = true) {y : Fin S.n → ℝ}
    (hy : b.Mem S.n y) : ∃ f ∈ bl.required S b, ∃ z : Fin S.n → ℝ,
      (bl.face S b f.1 f.2).Mem S.n z ∧ ProtEq S (ext S.n z) (ext S.n y) ∧
      (bl.map S.unit : GenMap κ).run Exact.re (ext S.n z) = ext S.n y := by
  classical
  simp only [ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.all_eq_true, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hden, hU⟩, hρn⟩, hρU⟩, hρbl⟩, hUbl⟩, hUfix⟩, hρlo⟩, hρhi⟩, hprot⟩, hzs⟩,
    hS⟩ := h
  have hd0 : (0 : ℝ) < b.den := Nat.cast_pos.mpr hden
  -- The slots of the blow-up.
  set T : Finset ℕ := (bl.zs.map Prod.fst).toFinset with hT
  have hTiff (i : ℕ) : i ∈ T ↔ (bl.find i).isSome = true := by
    simp only [hT, List.mem_toFinset, List.mem_map, find_isSome]
  have hTn (i : ℕ) (hi : i ∈ T) : i < S.n := by
    obtain ⟨z, hz, rfl⟩ := find_isSome.mp ((hTiff i).mp hi)
    exact (hzs z hz).1.1.1
  have hTdata (i : ℕ) (hi : i ∈ T) : 0 < bl.wt i ∧
      b.lo.getD i 0 ≤ bl.cen i * b.lo.getD S.unit 0 ∧
      bl.cen i * b.lo.getD S.unit 0 ≤ b.hi.getD i 0 := by
    obtain ⟨z, hz, rfl⟩ := find_isSome.mp ((hTiff i).mp hi)
    exact ⟨(hzs z hz).1.1.2, (hzs z hz).1.2, (hzs z hz).2⟩
  have hnotT (i : ℕ) (hi : i ∉ T) : (bl.find i).isSome = false := by
    rw [← Bool.not_eq_true, ← hTiff]
    exact hi
  -- The point `y` at the unit and radius slots.
  have hyU : ext S.n y S.unit = (b.lo.getD S.unit 0 : ℝ) / b.den := by
    have h1 := (hy ⟨S.unit, hU⟩).1
    have h2 := (hy ⟨S.unit, hU⟩).2
    rw [hUfix] at h2
    simp only [ext, hU, ↓reduceDIte]
    exact le_antisymm h2 h1
  have hyρ : ext S.n y bl.rho = 0 := by
    have h1 := (hy ⟨bl.rho, hρn⟩).1
    have h2 := (hy ⟨bl.rho, hρn⟩).2
    rw [hρlo] at h1
    rw [hρhi] at h2
    simp only [ext, hρn, ↓reduceDIte]
    simp only [Int.cast_zero, zero_div] at h1 h2
    exact le_antisymm h2 h1
  have hS' : ∃ j ∈ T, (b.lo.getD j 0 : ℝ) / b.den < (b.hi.getD j 0 : ℝ) / b.den := by
    obtain ⟨z, hz, hlt⟩ := hS
    refine ⟨z.1, ?_, div_lt_div_of_pos_right (by exact_mod_cast hlt) hd0⟩
    exact (hTiff _).mpr (find_isSome.mpr ⟨z, hz, rfl⟩)
  obtain ⟨j, upper, ρ, g, hjT, hρ0, hρ1, hside, hgj, hg⟩ :=
    exists_gauge T bl.wt (fun i hi' ↦ (hTdata i hi').1.ne')
      (lo := fun i ↦ (b.lo.getD i 0 : ℝ) / b.den) (hi := fun i ↦ (b.hi.getD i 0 : ℝ) / b.den)
      (c := fun i ↦ ((bl.cen i * b.lo.getD S.unit 0 : ℤ) : ℝ) / b.den) (x := ext S.n y)
      (fun i hi' ↦ ⟨div_le_div_of_nonneg_right (by exact_mod_cast (hTdata i hi').2.1) hd0.le,
        div_le_div_of_nonneg_right (by exact_mod_cast (hTdata i hi').2.2) hd0.le⟩)
      (fun i hi' ↦ by
        have hin := hTn i hi'
        simp only [ext, hin, ↓reduceDIte]
        exact hy ⟨i, hin⟩) hS'
  -- The required face.
  have hreq : (j, upper) ∈ bl.required S b := by
    obtain ⟨z, hz, hzj⟩ := find_isSome.mp ((hTiff j).mp hjT)
    simp only [required, List.mem_flatMap, List.mem_append]
    refine ⟨z, hz, ?_⟩
    subst hzj
    cases upper with
    | false =>
      left
      have hlt' : b.lo.getD z.1 0 < bl.cen z.1 * b.lo.getD S.unit 0 := by
        exact_mod_cast (div_lt_div_iff_of_pos_right hd0).mp hside
      simp only [hlt', ↓reduceIte, List.mem_singleton]
    | true =>
      right
      have hlt' : bl.cen z.1 * b.lo.getD S.unit 0 < b.hi.getD z.1 0 := by
        exact_mod_cast (div_lt_div_iff_of_pos_right hd0).mp hside
      simp only [hlt', ↓reduceIte, List.mem_singleton]
  -- The point of the face.
  set z : Fin S.n → ℝ := fun i ↦ if (i : ℕ) ∈ T then g i else if (i : ℕ) = bl.rho then ρ
    else y i with hzdef
  have hρT : bl.rho ∉ T := fun h ↦ by rw [hTiff] at h; simp_all
  have hUT : S.unit ∉ T := fun h ↦ by rw [hTiff] at h; simp_all
  have hzU : ext S.n z S.unit = ext S.n y S.unit := by
    simp only [ext, hU, ↓reduceDIte, hzdef, hUT, ↓reduceIte, Ne.symm hρU]
  have hcast (a c : ℤ) : ((a - c : ℤ) : ℝ) / b.den = (a : ℝ) / b.den - (c : ℝ) / b.den := by
    push_cast
    ring
  refine ⟨(j, upper), hreq, z, fun i ↦ ?_, fun p hp ↦ ?_, ?_⟩
  · -- `z` lies in the face box.
    simp only [face, Box.getD_range_map S.n _ _ i.2]
    by_cases hiT : (i : ℕ) ∈ T
    · have hsome := (hTiff i).mp hiT
      simp only [hsome, ↓reduceIte, hzdef, hiT, hcast]
      obtain ⟨hg1, hg2, -⟩ := hg i hiT
      by_cases hij : (i : ℕ) = j
      · subst hij
        cases upper <;> simp only [↓reduceIte, Bool.cond_false, Bool.cond_true] at hgj ⊢ <;>
          exact ⟨hgj.ge, hgj.le⟩
      · simp only [hij, ↓reduceIte]
        exact ⟨hg1, hg2⟩
    · simp only [hnotT i hiT, Bool.false_eq_true, ↓reduceIte, hzdef, hiT]
      by_cases hiρ : (i : ℕ) = bl.rho
      · simp only [hiρ, ↓reduceIte, Int.cast_zero, zero_div, Int.cast_natCast]
        exact ⟨hρ0, by rw [div_self hd0.ne']; exact hρ1⟩
      · simp only [hiρ, ↓reduceIte]
        exact hy i
  · -- Protected slots are kept.
    have hpρ : p ≠ bl.rho := (hprot p hp).1
    have hpT : p ∉ T := fun h' ↦ by
      have := (hprot p hp).2
      rw [hTiff] at h'
      simp_all
    by_cases hpn : p < S.n
    · simp only [ext, hpn, ↓reduceDIte, hzdef, hpT, ↓reduceIte, hpρ]
    · simp only [ext, hpn, ↓reduceDIte]
  · -- The image of `z` is `y`.
    funext i
    by_cases hiT : i ∈ T
    · have hsome := (hTiff i).mp hiT
      have hin := hTn i hiT
      have hzi : ext S.n z i = g i := by
        simp only [ext, hin, ↓reduceDIte, hzdef, hiT, ↓reduceIte]
      have hzρ : ext S.n z bl.rho = ρ := by
        simp only [ext, hρn, ↓reduceDIte, hzdef, hρT, ↓reduceIte]
      have hrun : (bl.map S.unit : GenMap κ).run Exact.re (ext S.n z) i =
          (bl.cen i : ℝ) * ext S.n z S.unit + powG 1 (ext S.n z bl.rho) (bl.wt i) *
            ext S.n z i := by
        simp only [map, hsome, ↓reduceIte, Exact.re_ofInt, Int.cast_one]
      rw [hrun, hzi, hzρ, hzU, hyU, powG_one, (hg i hiT).2.2]
      push_cast
      ring
    · by_cases hiρ : i = bl.rho
      · rw [hiρ, hyρ]
        simp only [map, hρbl, Bool.false_eq_true, ↓reduceIte, Exact.re_ofInt, Int.cast_zero]
      · rw [map_run_of_not (hnotT i hiT) hiρ]
        by_cases hin : i < S.n
        · simp only [ext, hin, ↓reduceDIte, hzdef, hiT, ↓reduceIte, hiρ]
        · simp only [ext, hin, ↓reduceDIte]

/-- The blow-up map keeps the protected slots of a valid blow-up, at every point. -/
theorem protEq_map {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] {S : Slots} {bl : Blow} {b : Box}
    (h : bl.ok S b = true) (z : ℕ → ℝ) :
    ProtEq S z ((bl.map S.unit : GenMap κ).run Exact.re z) := by
  simp only [ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.all_eq_true] at h
  intro p hp
  have hp' := h.1.1.2 p hp
  rw [map_run_of_not hp'.2 hp'.1]

end Blow

/-! ### Family trees -/

mutual

/-- A family tree with leaf data `L` and instance steps `St`. -/
inductive FTree (L St : Type) where
  /-- A leaf. -/
  | leaf (l : L)
  /-- Split slot `k` at `m / (den e)`, where `den` is the box's denominator. -/
  | split (k e : ℕ) (m : ℤ) (lo hi : FTree L St)
  /-- A weighted blow-up, with the subtrees of its faces. -/
  | blow (bl : Blow) (faces : FFaces L St)
  /-- An instance step. -/
  | step (s : St) (child : FTree L St)

/-- The faces of a weighted blow-up, `(j, upper)`, with their subtrees. -/
inductive FFaces (L St : Type) where
  /-- No more faces. -/
  | nil
  /-- The face `(j, upper)` and its subtree, then the other faces. -/
  | cons (j : ℕ) (upper : Bool) (t : FTree L St) (rest : FFaces L St)

end

/-- Both lists, appended, if both are there. -/
def optAppend {α : Type*} : Option (List α) → Option (List α) → Option (List α)
  | some a, some c => some (a ++ c)
  | _, _ => none

theorem optAppend_eq_some {α : Type*} {x y : Option (List α)} {l : List α}
    (h : optAppend x y = some l) : ∃ a c, x = some a ∧ y = some c ∧ l = a ++ c := by
  rcases x with _ | a <;> rcases y with _ | c <;> simp only [optAppend, reduceCtorEq] at h
  exact ⟨a, c, rfl, rfl, (Option.some.inj h).symm⟩

namespace FFaces

variable {L St : Type}

/-- The faces present. -/
def keys : FFaces L St → List (ℕ × Bool)
  | nil => []
  | cons j upper _ rest => (j, upper) :: keys rest

end FFaces

/-- A leaf with its family: the base map `Φ` and the slot map `σ`, so that the leaf's map is
`Φ ∘ σ`, the box and the data. -/
structure FLeaf (κ L : Type) where
  /-- The base map, from the slots of the base family to representatives. -/
  base : GenMap κ
  /-- The map from the leaf's slots to the slots of the base family. -/
  slots : GenMap κ
  /-- The box. -/
  box : Box
  /-- The data. -/
  data : L

/-- The map of a leaf, from its slots to representatives. -/
def FLeaf.map {κ L : Type} (x : FLeaf κ L) : GenMap κ := x.base.comp x.slots

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] {L St : Type}

/-- Instance steps: the child family `(Φ', σ', b')` of the family `(Φ, σ, b)`, or `none`. -/
abbrev StepFn (κ St : Type) :=
  St → GenMap κ → GenMap κ → Box → Option (GenMap κ × GenMap κ × Box)

mutual

/-- Check the steps of a tree on the family `(Φ, σ, b)`, with map `Φ ∘ σ`, and return the leaves
with their families. -/
def FTree.cover (S : Slots) (step : StepFn κ St) :
    GenMap κ → GenMap κ → Box → FTree L St → Option (List (FLeaf κ L))
  | Φ, σ, b, .leaf l => some [⟨Φ, σ, b, l⟩]
  | Φ, σ, b, .split k e m lo hi =>
    if 0 < e then
      optAppend (FTree.cover S step Φ σ (b.splitLo S.n k e m) lo)
        (FTree.cover S step Φ σ (b.splitHi S.n k e m) hi)
    else none
  | Φ, σ, b, .blow bl fs =>
    if bl.ok S b && (bl.required S b).all (fun f ↦ decide (f ∈ fs.keys)) then
      FFaces.cover S step bl Φ σ b fs
    else none
  | Φ, σ, b, .step s t =>
    match step s Φ σ b with
    | some (Φ', σ', b') => FTree.cover S step Φ' σ' b' t
    | none => none

/-- `FTree.cover` on the faces of the blow-up `bl` of the family `(Φ, σ, b)`. -/
def FFaces.cover (S : Slots) (step : StepFn κ St) (bl : Blow) (Φ σ : GenMap κ) (b : Box) :
    FFaces L St → Option (List (FLeaf κ L))
  | .nil => some []
  | .cons j upper t rest =>
    optAppend (FTree.cover S step Φ (σ.comp (bl.map S.unit)) (bl.face S b j upper) t)
      (FFaces.cover S step bl Φ σ b rest)

end

/-- The leaf `x` covers the point `y` of the family with map `Ψ`: a point `z` of its box has the
same protected slots and the same pose. -/
def Covers (S : Slots) (Ψ : GenMap κ) (y : Fin S.n → ℝ) (x : FLeaf κ L) : Prop :=
  ∃ z : Fin S.n → ℝ, x.box.Mem S.n z ∧ ProtEq S (ext S.n z) (ext S.n y) ∧
    PoseSim (x.map.run Exact.re (ext S.n z)) (Ψ.run Exact.re (ext S.n y))

theorem Covers.of_sim {S : Slots} {Ψ Ψ' : GenMap κ} {y w : Fin S.n → ℝ} {x : FLeaf κ L}
    (h : Covers S Ψ' w x) (hp : ProtEq S (ext S.n w) (ext S.n y))
    (hΨ : PoseSim (Ψ'.run Exact.re (ext S.n w)) (Ψ.run Exact.re (ext S.n y))) :
    Covers S Ψ y x := by
  obtain ⟨z, hz, hzp, hzs⟩ := h
  exact ⟨z, hz, hzp.trans hp, hzs.trans hΨ⟩

/-- Instance steps are sound: every point of the parent family is covered by a point of the
child family with the same protected slots and the same pose. -/
def StepSound (S : Slots) (step : StepFn κ St) : Prop :=
  ∀ s Φ σ b Φ' σ' b', step s Φ σ b = some (Φ', σ', b') → ∀ y : Fin S.n → ℝ, b.Mem S.n y →
    ∃ z : Fin S.n → ℝ, b'.Mem S.n z ∧ ProtEq S (ext S.n z) (ext S.n y) ∧
      PoseSim ((Φ'.comp σ').run Exact.re (ext S.n z))
        ((Φ.comp σ).run Exact.re (ext S.n y))

mutual

/-- **Soundness of family trees.** Every point of the box is covered by a leaf. -/
theorem FTree.cover_sound {S : Slots} {step : StepFn κ St} (hstep : StepSound S step) :
    ∀ (T : FTree L St) {Φ σ : GenMap κ} {b : Box} {ls : List (FLeaf κ L)},
      FTree.cover S step Φ σ b T = some ls → ∀ y : Fin S.n → ℝ, b.Mem S.n y →
        ∃ x ∈ ls, Covers S (Φ.comp σ) y x
  | .leaf l, Φ, σ, b, ls, h, y, hy => by
    simp only [FTree.cover, Option.some.injEq] at h
    subst h
    exact ⟨_, List.mem_singleton_self _, y, hy, fun _ _ ↦ rfl, PoseSim.refl _⟩
  | .split k e m lo hi, Φ, σ, b, ls, h, y, hy => by
    simp only [FTree.cover] at h
    split_ifs at h with he
    obtain ⟨a, c, ha, hc, rfl⟩ := optAppend_eq_some h
    rcases Box.mem_split he m hy with hy' | hy'
    · obtain ⟨x, hx, hcov⟩ := FTree.cover_sound hstep lo ha y hy'
      exact ⟨x, List.mem_append_left _ hx, hcov⟩
    · obtain ⟨x, hx, hcov⟩ := FTree.cover_sound hstep hi hc y hy'
      exact ⟨x, List.mem_append_right _ hx, hcov⟩
  | .blow bl fs, Φ, σ, b, ls, h, y, hy => by
    simp only [FTree.cover, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    split_ifs at h with hok
    obtain ⟨f, hf, z, hz, hzp, hzy⟩ := Blow.exists_face (κ := κ) hok.1 hy
    obtain ⟨x, hx, hcov⟩ := FFaces.cover_sound hstep fs h f (hok.2 f hf) z hz
    refine ⟨x, hx, hcov.of_sim hzp (PoseSim.of_eq ?_)⟩
    change Φ.run Exact.re (σ.run Exact.re ((bl.map S.unit).run Exact.re (ext S.n z))) = _
    rw [hzy]
    rfl
  | .step s t, Φ, σ, b, ls, h, y, hy => by
    simp only [FTree.cover] at h
    split at h
    next Φ' σ' b' hs =>
      obtain ⟨z, hz, hzp, hzs⟩ := hstep s Φ σ b Φ' σ' b' hs y hy
      obtain ⟨x, hx, hcov⟩ := FTree.cover_sound hstep t h z hz
      exact ⟨x, hx, hcov.of_sim hzp hzs⟩
    next => exact absurd h (by simp)

/-- **Soundness of the faces of a blow-up.** Every point of the box of a present face is covered
by a leaf of its subtree. -/
theorem FFaces.cover_sound {S : Slots} {step : StepFn κ St} (hstep : StepSound S step) :
    ∀ (fs : FFaces L St) {bl : Blow} {Φ σ : GenMap κ} {b : Box} {ls : List (FLeaf κ L)},
      FFaces.cover S step bl Φ σ b fs = some ls → ∀ f ∈ fs.keys, ∀ z : Fin S.n → ℝ,
        (bl.face S b f.1 f.2).Mem S.n z → ∃ x ∈ ls, Covers S (Φ.comp (σ.comp (bl.map S.unit))) z x
  | .nil, _, _, _, _, _, _, f, hf, _, _ => by simp [FFaces.keys] at hf
  | .cons j upper t rest, bl, Φ, σ, b, ls, h, f, hf, z, hz => by
    simp only [FFaces.cover] at h
    obtain ⟨a, c, ha, hc, rfl⟩ := optAppend_eq_some h
    simp only [FFaces.keys, List.mem_cons] at hf
    rcases hf with rfl | hf
    · obtain ⟨x, hx, hcov⟩ := FTree.cover_sound hstep t ha z hz
      exact ⟨x, List.mem_append_left _ hx, hcov⟩
    · obtain ⟨x, hx, hcov⟩ := FFaces.cover_sound hstep rest hc f hf z hz
      exact ⟨x, List.mem_append_right _ hx, hcov⟩

end

/-- `σ'` is `σ` after a map of slots that keeps the protected slots. -/
def Descends (S : Slots) (σ σ' : GenMap κ) : Prop :=
  ∀ z : ℕ → ℝ, ∃ y : ℕ → ℝ, ProtEq S z y ∧ σ'.run Exact.re z = σ.run Exact.re y

theorem Descends.refl (S : Slots) (σ : GenMap κ) : Descends S σ σ :=
  fun z ↦ ⟨z, fun _ _ ↦ rfl, rfl⟩

theorem Descends.trans {S : Slots} {σ σ' σ'' : GenMap κ} (h : Descends S σ σ')
    (h' : Descends S σ' σ'') : Descends S σ σ'' := fun z ↦ by
  obtain ⟨y, hy, hyz⟩ := h' z
  obtain ⟨x, hx, hxy⟩ := h y
  exact ⟨x, hy.trans hx, hyz.trans hxy⟩

/-- Instance steps keep the base map, and change slots by maps that keep the protected slots. -/
def StepKeeps (S : Slots) (step : StepFn κ St) : Prop :=
  ∀ s Φ σ b Φ' σ' b', step s Φ σ b = some (Φ', σ', b') → Φ' = Φ ∧ Descends S σ σ'

mutual

/-- **Leaves descend.** If instance steps keep the base map and the protected slots, every leaf
has the base map of the family and a slot map that is `σ` after a map keeping the protected
slots. -/
theorem FTree.descends_of_cover {S : Slots} {step : StepFn κ St} (hstep : StepKeeps S step) :
    ∀ (T : FTree L St) {Φ σ : GenMap κ} {b : Box} {ls : List (FLeaf κ L)},
      FTree.cover S step Φ σ b T = some ls → ∀ x ∈ ls, x.base = Φ ∧ Descends S σ x.slots
  | .leaf l, Φ, σ, b, ls, h, x, hx => by
    simp only [FTree.cover, Option.some.injEq] at h
    subst h
    rw [List.mem_singleton.mp hx]
    exact ⟨rfl, Descends.refl S σ⟩
  | .split k e m lo hi, Φ, σ, b, ls, h, x, hx => by
    simp only [FTree.cover] at h
    split_ifs at h with he
    obtain ⟨a, c, ha, hc, rfl⟩ := optAppend_eq_some h
    rcases List.mem_append.mp hx with hx | hx
    · exact FTree.descends_of_cover hstep lo ha x hx
    · exact FTree.descends_of_cover hstep hi hc x hx
  | .blow bl fs, Φ, σ, b, ls, h, x, hx => by
    simp only [FTree.cover, Bool.and_eq_true] at h
    split_ifs at h with hok
    obtain ⟨hb, hd⟩ := FFaces.descends_of_cover hstep fs h x hx
    exact ⟨hb, Descends.trans (fun z ↦ ⟨_, Blow.protEq_map hok.1 z, rfl⟩) hd⟩
  | .step s t, Φ, σ, b, ls, h, x, hx => by
    simp only [FTree.cover] at h
    split at h
    next Φ' σ' b' hs =>
      obtain ⟨rfl, hd⟩ := hstep s Φ σ b Φ' σ' b' hs
      obtain ⟨hb, hd'⟩ := FTree.descends_of_cover hstep t h x hx
      exact ⟨hb, hd.trans hd'⟩
    next => exact absurd h (by simp)

/-- **Leaves of faces descend.** -/
theorem FFaces.descends_of_cover {S : Slots} {step : StepFn κ St} (hstep : StepKeeps S step) :
    ∀ (fs : FFaces L St) {bl : Blow} {Φ σ : GenMap κ} {b : Box} {ls : List (FLeaf κ L)},
      FFaces.cover S step bl Φ σ b fs = some ls → ∀ x ∈ ls,
        x.base = Φ ∧ Descends S (σ.comp (bl.map S.unit)) x.slots
  | .nil, _, _, _, _, ls, h, x, hx => by
    simp only [FFaces.cover, Option.some.injEq] at h
    subst h
    simp at hx
  | .cons j upper t rest, bl, Φ, σ, b, ls, h, x, hx => by
    simp only [FFaces.cover] at h
    obtain ⟨a, c, ha, hc, rfl⟩ := optAppend_eq_some h
    rcases List.mem_append.mp hx with hx | hx
    · exact FTree.descends_of_cover hstep t ha x hx
    · exact FFaces.descends_of_cover hstep rest hc x hx

end

end Nieuwland.Check
