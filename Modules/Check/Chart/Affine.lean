import Modules.Check.Leaf.Family
import Modules.Check.Polynomial.Linear

/-!
# Slot-affine steps (S2a)

A slot-affine step of a chart tree (`Tree::Affine` in `code/src/proof/tree.rs`, `Node::affine`)
changes the slots `J` of a family: the old slots are `y_J = M z + κ` with `M` invertible over the
field and `z` in a new rational box `Z`, and the other slots are kept. Since the step is affine,
`z = M⁻¹ (y - κ)` lies in `Z` for every point `y` of the parent box when it does at the corners
of the parent box (`sum_mem_of_corners`), so every point of the parent box is the image of a
point of the child box (`Affine.step_sound`).

In exact values (`Affine`): the matrix `m` and the constants `c` lie in `κ`, the constants in
multiples of the unit slot `U` (fixed on the parent box), and an inverse `inv` of `m` up to a
positive factor `e` (`m inv = e I`) is given. The new ranges are rational, over the parent's
denominator times `s`. The exporter scales rupert's new slots so that `m` is integral in `κ`
(`code/lean-export`).
-/

namespace Nieuwland.Check

open Pull

/-! ### Sums by repeated addition -/

section Sum

variable {α β : Type*} [Add α] [Add β]

/-- `z + f 0 + ⋯ + f (k - 1)` by repeated addition. -/
def sumG (z : α) (f : ℕ → α) : ℕ → α
  | 0 => z
  | k + 1 => sumG z f k + f k

theorem map_sumG {f : α → β} (hf : ∀ a b, f (a + b) = f a + f b) (z : α) (g : ℕ → α) :
    ∀ k, f (sumG z g k) = sumG (f z) (f ∘ g) k
  | 0 => rfl
  | k + 1 => by rw [sumG, hf, map_sumG hf z g k]; rfl

theorem sumG_zero (g : ℕ → ℝ) : ∀ k, sumG 0 g k = ∑ c ∈ Finset.range k, g c
  | 0 => by simp [sumG]
  | k + 1 => by rw [sumG, sumG_zero g k, Finset.sum_range_succ]

/-- `sumG` with only the summands `f c` where `nz c` holds. -/
def sumGZ (z : α) (nz : ℕ → Bool) (f : ℕ → α) : ℕ → α
  | 0 => z
  | k + 1 => bif nz k then sumGZ z nz f k + f k else sumGZ z nz f k

theorem map_sumGZ {f : α → β} (hf : ∀ a b, f (a + b) = f a + f b) (z : α) (nz : ℕ → Bool)
    (g : ℕ → α) : ∀ k, f (sumGZ z nz g k) = sumGZ (f z) nz (f ∘ g) k
  | 0 => rfl
  | k + 1 => by
    simp only [sumGZ]
    cases nz k
    · rw [Bool.cond_false, Bool.cond_false, map_sumGZ hf z nz g k]
    · rw [Bool.cond_true, Bool.cond_true, hf, map_sumGZ hf z nz g k]
      rfl

theorem sumGZ_zero (nz : ℕ → Bool) (g : ℕ → ℝ) (hg : ∀ c, nz c = false → g c = 0) :
    ∀ k, sumGZ 0 nz g k = ∑ c ∈ Finset.range k, g c
  | 0 => by simp [sumGZ]
  | k + 1 => by
    rw [sumGZ, Finset.sum_range_succ, ← sumGZ_zero nz g hg k]
    cases h : nz k
    · rw [Bool.cond_false, hg k h, add_zero]
    · rw [Bool.cond_true]

end Sum

/-! ### The step -/

/-- A slot-affine step (S2a): the slots `J` (`slots`), the matrix `m` by rows and the constants
`c` (in multiples of the unit slot), one row and one constant per slot of `J`, an inverse `inv`
of `m` up to the factor `e`, and the new ranges of the slots of `J` over the parent's denominator
times `s`. -/
structure Affine (κ : Type) where
  /-- The slots `J`. -/
  slots : List ℕ
  /-- The matrix, by rows. -/
  m : List (List κ)
  /-- The constants, in multiples of the unit slot. -/
  c : List κ
  /-- An inverse of `m` times `e`, by rows. -/
  inv : List (List κ)
  /-- The factor of the inverse. -/
  e : κ
  /-- The new denominator is the parent's times `s`. -/
  s : ℕ
  /-- The numerators of the lower ends of the new ranges. -/
  lo : List ℤ
  /-- The numerators of the upper ends of the new ranges. -/
  hi : List ℤ

namespace Affine

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] (A : Affine κ)

/-- The number of changed slots. -/
abbrev k : ℕ := A.slots.length

/-- The slot map with unit slot `U`: slot `J_r` holds `∑_c m_rc x_{J_c} + c_r x_U`, the other
slots are kept. The sum leaves out the entries that are zero (`Exact.isZero`): they add nothing,
and without them the formal shapes of the outputs (`Term.shapeOf`) have only the slots that the
row uses. -/
def map (U : ℕ) : GenMap κ where
  run kk x i :=
    if i ∈ A.slots then
      sumGZ (kk (Exact.ofInt 0)) (fun c ↦ !Exact.isZero (ent A.m (A.slots.idxOf i) c))
          (fun c ↦ kk (ent A.m (A.slots.idxOf i) c) * x (A.slots.getD c 0)) A.k +
        kk (A.c.getD (A.slots.idxOf i) (Exact.ofInt 0)) * x U
    else x i
  natural f hf kk x := by
    funext i
    simp only [Function.comp_apply]
    split_ifs
    · rw [hf.map_add, hf.map_mul, map_sumGZ hf.map_add]
      simp only [Function.comp_def, hf.map_mul]
    · rfl

/-- The child box of `n` slots: the parent's over its denominator times `s`, with the new ranges
in the slots of `J`. -/
def box (n : ℕ) (b : Box) : Box where
  lo := (List.range n).map fun i ↦
    if i ∈ A.slots then A.lo.getD (A.slots.idxOf i) 0 else A.s * b.lo.getD i 0
  hi := (List.range n).map fun i ↦
    if i ∈ A.slots then A.hi.getD (A.slots.idxOf i) 0 else A.s * b.hi.getD i 0
  den := b.den * A.s

/-- The ends of `v_c = den y_{J_c} - c_c (den y_U)` over the parent box `b`, with the unit slot
`U` fixed at `b.lo_U / den`. -/
def ends (b : Box) (U : ℕ) (upper : Bool) : List κ :=
  (List.range A.k).map fun c ↦
    Exact.ofInt ((bif upper then b.hi else b.lo).getD (A.slots.getD c 0) 0) -
      A.c.getD c (Exact.ofInt 0) * Exact.ofInt (b.lo.getD U 0)

/-- The value of `s (inv v)_r` at the corner `l` of the ends. -/
def cval (b : Box) (U r : ℕ) (l : List Bool) : κ :=
  Exact.ofInt A.s * cornerVal A.k A.inv (A.ends b U false) (A.ends b U true) r l

/-- **The check of a slot-affine step** on the parent box `b` of `n` slots with the unit slot
`n - 1`: distinct slots of `J` below the unit slot, the unit slot fixed, `m inv = e I` with
`e > 0`, and `inv (y - c u) / e` in the new ranges at the corners of the parent box. -/
def ok (n : ℕ) (b : Box) : Bool :=
  decide (0 < A.k) && decide A.slots.Nodup && A.slots.all (fun j ↦ decide (j + 1 < n)) &&
    decide (0 < A.s) && decide (0 < b.den) &&
    decide (b.lo.getD (n - 1) 0 = b.hi.getD (n - 1) 0) && Exact.pos A.e &&
    mulOk A.k A.m A.inv A.e &&
    (List.range A.k).all fun r ↦ (corners A.k).all fun l ↦
      Exact.nonneg (A.cval b (n - 1) r l - Exact.ofInt (A.lo.getD r 0) * A.e) &&
        Exact.nonneg (Exact.ofInt (A.hi.getD r 0) * A.e - A.cval b (n - 1) r l)

/-- The step: the child family keeps the base map and composes the slot map with `map`. -/
def step (n : ℕ) : StepFn κ (Affine κ) := fun A Φ σ b ↦
  if A.ok n b then some (Φ, σ.comp (A.map (n - 1)), A.box n b) else none

/-! #### Soundness -/

variable {A}

theorem run_map_re (U : ℕ) (x : ℕ → ℝ) (i : ℕ) :
    (A.map U).run Exact.re x i = if i ∈ A.slots then
      ∑ c ∈ Finset.range A.k, Exact.re (ent A.m (A.slots.idxOf i) c) * x (A.slots.getD c 0) +
        Exact.re (A.c.getD (A.slots.idxOf i) (Exact.ofInt 0)) * x U
    else x i := by
  simp only [map]
  split_ifs
  · rw [Exact.re_ofInt, Int.cast_zero, sumGZ_zero _ _ fun c hc ↦ by
      simp only [Bool.not_eq_false'] at hc
      simp only [Exact.isZero_sound _ hc, zero_mul]]
  · rfl

/-- The preimage point: `z_{J_r} = (inv (y_J - c y_U))_r / e`, the other slots of `y`. -/
noncomputable def pre (n : ℕ) (y : Fin n → ℝ) : Fin n → ℝ := fun i ↦
  if (i : ℕ) ∈ A.slots then
    (∑ j ∈ Finset.range A.k, Exact.re (ent A.inv (A.slots.idxOf (i : ℕ)) j) *
      (ext n y (A.slots.getD j 0) -
        Exact.re (A.c.getD j (Exact.ofInt 0)) * ext n y (n - 1))) / Exact.re A.e
  else y i

omit [Add κ] [Sub κ] [Mul κ] [Exact κ] in
theorem idxOf_getD (hnd : A.slots.Nodup) {c : ℕ} (hc : c < A.k) :
    A.slots.idxOf (A.slots.getD c 0) = c := by
  rw [List.getD_eq_getElem _ _ hc]
  exact List.Nodup.idxOf_getElem hnd c hc

omit [Add κ] [Sub κ] [Mul κ] [Exact κ] in
theorem getD_mem {c : ℕ} (hc : c < A.k) : A.slots.getD c 0 ∈ A.slots := by
  rw [List.getD_eq_getElem _ _ hc]
  exact List.getElem_mem hc

omit [Add κ] [Sub κ] [Mul κ] [Exact κ] in
theorem getD_idxOf {i : ℕ} (hi : i ∈ A.slots) : A.slots.getD (A.slots.idxOf i) 0 = i := by
  rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hi)]
  exact List.getElem_idxOf (List.idxOf_lt_length_of_mem hi)

/-- **The slot map takes the preimage point to the point.** -/
theorem map_pre {n : ℕ} {b : Box} (h : A.ok n b = true) (y : Fin n → ℝ) :
    (A.map (n - 1)).run Exact.re (ext n (A.pre n y)) = ext n y := by
  simp only [ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hk, hnd⟩, hlt⟩, -⟩, -⟩, -⟩, hpos⟩, hmul⟩, -⟩ := h
  have he : Exact.re A.e ≠ 0 := (Exact.pos_sound _ hpos).ne'
  have hn : 0 < n := by
    obtain ⟨j, hj⟩ := List.exists_mem_of_length_pos (by omega : 0 < A.k)
    have := hlt j hj
    omega
  -- The unit slot is kept.
  have hU : ext n (A.pre n y) (n - 1) = ext n y (n - 1) := by
    have hU' : n - 1 ∉ A.slots := fun hm ↦ by have := hlt _ hm; omega
    simp only [Pull.ext, show n - 1 < n by omega, ↓reduceDIte, pre, hU', ↓reduceIte]
  funext i
  rw [run_map_re]
  split_ifs with hi
  · have hin : i < n := by have := hlt i hi; omega
    set r := A.slots.idxOf i with hr
    have hrk : r < A.k := List.idxOf_lt_length_of_mem hi
    have hz (c : ℕ) (hc : c < A.k) : ext n (A.pre n y) (A.slots.getD c 0) =
        (∑ j ∈ Finset.range A.k, Exact.re (ent A.inv c j) *
          (ext n y (A.slots.getD j 0) -
            Exact.re (A.c.getD j (Exact.ofInt 0)) * ext n y (n - 1))) / Exact.re A.e := by
      have hm := getD_mem hc
      have hcn : A.slots.getD c 0 < n := by have := hlt _ hm; omega
      simp only [Pull.ext, hcn, ↓reduceDIte, pre, hm, ↓reduceIte, idxOf_getD hnd hc]
    rw [Finset.sum_congr rfl fun c hc ↦ by rw [hz c (Finset.mem_range.mp hc)], hU,
      mul_inv_apply (fun r c hr hc ↦ mulOk_apply hmul hr hc) he _ hrk, getD_idxOf hi]
    ring
  · simp only [Pull.ext]
    split_ifs with hin
    · simp only [pre, hi, ↓reduceIte]
    · rfl

/-- **The preimage point lies in the child box.** -/
theorem pre_mem {n : ℕ} {b : Box} (h : A.ok n b = true) {y : Fin n → ℝ} (hy : b.Mem n y) :
    (A.box n b).Mem n (A.pre n y) := by
  simp only [ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hk, hnd⟩, hlt⟩, hs⟩, hden⟩, hfix⟩, hpos⟩, -⟩, hcor⟩ := h
  have he : 0 < Exact.re A.e := Exact.pos_sound _ hpos
  have hd : (0 : ℝ) < b.den := by exact_mod_cast hden
  have hs' : (0 : ℝ) < A.s := by exact_mod_cast hs
  have hn : 0 < n := by
    obtain ⟨j, hj⟩ := List.exists_mem_of_length_pos (by omega : 0 < A.k)
    have := hlt j hj
    omega
  -- The unit slot is fixed at `lo_U / den`.
  have hyU : ext n y (n - 1) = (b.lo.getD (n - 1) 0 : ℝ) / b.den := by
    obtain ⟨h1, h2⟩ := hy ⟨n - 1, by omega⟩
    simp only [Pull.ext, show n - 1 < n by omega, ↓reduceDIte]
    rw [hfix] at h1 ⊢
    exact le_antisymm (by rwa [← hfix] at h2 ⊢) h1
  intro ⟨i, hi⟩
  simp only [box, Box.getD_range_map _ _ _ hi, pre]
  split_ifs with hJ
  · set r := A.slots.idxOf i
    have hrk : r < A.k := List.idxOf_lt_length_of_mem hJ
    -- The numerators `v_c = den y_{J_c} - c_c lo_U` lie between the ends.
    have hv : ∀ c < A.k, Exact.re ((A.ends b (n - 1) false).getD c (Exact.ofInt 0)) ≤
        b.den * ext n y (A.slots.getD c 0) -
          Exact.re (A.c.getD c (Exact.ofInt 0)) * b.lo.getD (n - 1) 0 ∧
        b.den * ext n y (A.slots.getD c 0) -
          Exact.re (A.c.getD c (Exact.ofInt 0)) * b.lo.getD (n - 1) 0 ≤
        Exact.re ((A.ends b (n - 1) true).getD c (Exact.ofInt 0)) := by
      intro c hc
      have hm := getD_mem hc
      have hcn : A.slots.getD c 0 < n := by have := hlt _ hm; omega
      obtain ⟨h1, h2⟩ := hy ⟨_, hcn⟩
      rw [div_le_iff₀ hd] at h1
      rw [le_div_iff₀ hd] at h2
      simp only [ends, Box.getD_range_map _ _ _ hc, Bool.cond_false, Bool.cond_true,
        Exact.re_sub, Exact.re_mul, Exact.re_ofInt, Pull.ext, hcn, ↓reduceDIte]
      constructor <;> linarith
    have hb := sum_mem_of_corners (N := A.inv) (c := r)
      (lo := (A.lo.getD r 0 : ℝ) * Exact.re A.e / A.s)
      (hi := (A.hi.getD r 0 : ℝ) * Exact.re A.e / A.s) (fun l hl ↦ ?_) hv
    · -- The preimage coordinate is the sum over `den e`.
      have hsum : ∑ j ∈ Finset.range A.k, Exact.re (ent A.inv r j) *
          (ext n y (A.slots.getD j 0) -
            Exact.re (A.c.getD j (Exact.ofInt 0)) * ext n y (n - 1)) =
          (∑ j ∈ Finset.range A.k, Exact.re (ent A.inv r j) *
            (b.den * ext n y (A.slots.getD j 0) -
              Exact.re (A.c.getD j (Exact.ofInt 0)) * b.lo.getD (n - 1) 0)) / b.den := by
        rw [eq_div_iff hd.ne', Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [hyU]
        field_simp
      rw [hsum]
      obtain ⟨h1, h2⟩ := hb
      rw [div_le_iff₀ hs'] at h1
      rw [le_div_iff₀ hs'] at h2
      push_cast
      constructor
      · rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      · rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
    · have h1 := hcor r hrk l hl
      have ha := Exact.nonneg_sound _ h1.1
      have hb := Exact.nonneg_sound _ h1.2
      simp only [cval, Exact.re_sub, Exact.re_mul, Exact.re_ofInt, Int.cast_natCast] at ha hb
      constructor
      · rw [div_le_iff₀ hs']
        linarith
      · rw [le_div_iff₀ hs']
        linarith
  · obtain ⟨h1, h2⟩ := hy ⟨i, hi⟩
    push_cast
    rw [mul_comm (b.den : ℝ), mul_div_mul_left _ _ hs'.ne', mul_div_mul_left _ _ hs'.ne']
    exact ⟨h1, h2⟩

/-- **Slot-affine steps are sound**: every point of the parent box is the image of a point of
the child box under the slot map, so it has the same pose. -/
theorem step_sound (n : ℕ) : StepSound ⟨n, n - 1, []⟩ (step (κ := κ) n) := by
  intro A Φ σ b Φ' σ' b' h y hy
  simp only [step] at h
  split_ifs at h with hok
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  refine ⟨A.pre n y, pre_mem hok hy, fun _ h ↦ absurd h List.not_mem_nil, PoseSim.of_eq ?_⟩
  change Φ.run Exact.re (σ.run Exact.re ((A.map (n - 1)).run Exact.re (ext n (A.pre n y)))) = _
  rw [map_pre hok]
  rfl

end Affine

end Nieuwland.Check
