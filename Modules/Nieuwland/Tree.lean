import Modules.Check.Chart.Tree
import Modules.Nieuwland.Supports

/-!
# Chart trees at a plug scale

The claims of an exact Nieuwland certificate are chart trees at the plug scale `Θ = λ*`
(`chart_tree` evidence with a claim scale, `code/src/proof/scale.rs`): the tree, its steps and its
outside leaves are those of `Modules/Check/Chart/Tree.lean`, and an obstruction or combination leaf
takes the witness polynomials of the plug `θ P` in the hole `P`, `θ = ν / d` (`Scale`): the plugs
times `ν` and the anchors times `d > 0`, as `Balanced.checkScaled` and `Width.checkScaled` do it
for the supports of boxes (`Modules/Nieuwland/Supports.lean`). The premises of the witnesses are
statements about the hole and do not change.

* `Wit.polyS`, `Wit.exists_negS`: the witness polynomials at a scale; at a fit of
  `θ • R(q) R(q_c)` with the premises, some anchor choice is negative.
* `Obst.polyOkSS`: `Obst.polyOkS` (`x = false`) and `Obst.polyOkSX` (`x = true`, the sparse sign
  check) on the scaled terms.
* `TObst.checkS`: the check of an obstruction or combination leaf at a scale.
* `ChartTree.checkS`, `ChartTree.checkS_sound_pre`: the check of a chart tree at a scale (no
  symmetry data: exclusion leaves fail), sound for `NoFitRot B.poses (θ • preRot c)`. In parts:
  `ChartTree.checkS_of_parts`.

The unscaled checks are unchanged; at `ν / d = 1 / 1` the scaled polynomials are theirs up to the
products by `1`.
-/

open Matrix

namespace Nieuwland.Check

open Pull

/-- **No fit at a chart pose, at a scale**: `NoFitRep.noFit` for the matrix
`θ • (R(q) R(q_c))`. -/
theorem not_fitsAlong_smul_of_represents {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]
    {pts : List (V3 κ)} {θ : ℝ} {c : Option (Fin 4 → ℝ)} {o : ℕ → ℝ} {p : ChartPose}
    (h : ¬ (Polyhedron.ofPoints pts).FitsAlong (outU o)
      (θ • (quatRotation (outQ o) * preRot c)))
    (hp : Represents p o) :
    ¬ (Polyhedron.ofPoints pts).FitsAlong (viewDir p.view p.s p.t)
      (θ • (p.rotation * preRot c)) := by
  intro h'
  obtain ⟨a, b, ha, hb, hu, hq⟩ := hp
  have hR : p.rotation = quatRotation (outQ o) := by
    rw [hq, quatRotation_smul hb]
    rfl
  rw [hR] at h'
  refine h ?_
  rw [hu]
  exact Polyhedron.FitsAlong.of_smul (inv_ne_zero ha) (by rwa [smul_smul, inv_mul_cancel₀ ha,
    one_smul])

/-! ### Witness polynomials at a scale -/

namespace Wit

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The witness polynomial of the anchor choice `t` at the plug scale `s`: `Wit.poly` with the
plugs times `s.num` and the anchors times `s.den`. -/
def polyS (s : Scale κ) (pts : List (V3 κ)) : Wit κ → List ℕ → PosePoly κ
  | balanced w, t => ⟨fun k U Q ↦ balancedG k (Exact.ofInt w.sigma) U Q (w.dir pts)
      (fun i ↦ V3.smul s.num (pt pts (w.sup i).plug))
      (fun i ↦ V3.smul (Exact.ofInt (s.den : ℤ)) (pt pts (t.getD i 0))),
      fun _ hf k U Q ↦ map_balancedG hf k _ U Q _ _ _⟩
  | width w, t => ⟨fun k U Q ↦ supportG k U Q w.c (V3.smul s.num (w.plugDiff pts))
      (V3.smul (Exact.ofInt (s.den : ℤ)) ((pt pts (t.getD 0 0)).sub (pt pts (t.getD 1 0)))),
      fun _ hf k U Q ↦ map_supportG hf k U Q _ _ _⟩
  | centred w, t => ⟨fun k U Q ↦ supportG k U Q w.c (V3.smul s.num (w.toWidth.plugDiff pts))
      (V3.smul (Exact.ofInt (s.den : ℤ)) ((pt pts (t.getD 0 0)).sub (pt pts (t.getD 1 0)))),
      fun _ hf k U Q ↦ map_supportG hf k U Q _ _ _⟩

/-- The real value of the witness polynomial of the anchor choice `t` at the plug scale `s`. -/
noncomputable def valS (s : Scale κ) (pts : List (V3 κ)) :
    Wit κ → List ℕ → (Fin 3 → ℝ) → (Fin 4 → ℝ) → ℝ
  | balanced w, t, u, q => balancedPoly (w.sigma : ℝ) u q (fun i ↦ Exact.reV (w.dir pts i))
      (fun i ↦ Exact.re s.num • Exact.reV (pt pts (w.sup i).plug))
      (fun i ↦ (s.den : ℝ) • Exact.reV (pt pts (t.getD i 0)))
  | width w, t, u, q => supportPoly u q (Exact.reV w.c)
      (Exact.re s.num • Exact.reV (w.plugDiff pts))
      ((s.den : ℝ) • Exact.reV ((pt pts (t.getD 0 0)).sub (pt pts (t.getD 1 0))))
  | centred w, t, u, q => supportPoly u q (Exact.reV w.c)
      (Exact.re s.num • Exact.reV (w.toWidth.plugDiff pts))
      ((s.den : ℝ) • Exact.reV ((pt pts (t.getD 0 0)).sub (pt pts (t.getD 1 0))))

theorem run_reS (s : Scale κ) (pts : List (V3 κ)) (W : Wit κ) (t : List ℕ) (U : V3 ℝ)
    (Q : Q4 ℝ) : (W.polyS s pts t).run Exact.re U Q = W.valS s pts t U.toFun Q.toFun := by
  cases W with
  | balanced w =>
    simp only [polyS, valS, balancedG_re, Exact.re_ofInt, Exact.reV_smul, Int.cast_natCast]
  | width w =>
    simp only [polyS, valS, supportG_re, Exact.re_ofInt, Exact.reV_smul, Int.cast_natCast]
  | centred w =>
    simp only [polyS, valS, supportG_re, Exact.re_ofInt, Exact.reV_smul, Int.cast_natCast]

theorem eval_preS (s : Scale κ) (pts : List (V3 κ)) (W : Wit κ) (t : List ℕ)
    (c : Option (Q4 κ)) (o : ℕ → ℝ) : ((W.polyS s pts t).pre c).eval o =
      W.valS s pts t (outU o) (preQuat (outQ o) (Exact.rePre c)) := by
  change (W.polyS s pts t).run Exact.re (viewOf o) (preQ Exact.re (quatOf o) c) = _
  rw [run_reS, toFun_viewOf, toFun_preQ, toFun_quatOf]

/-- **At a fit of the scaled plug with the premises, some anchor choice is negative.** -/
theorem exists_neg_valS {pts : List (V3 κ)} {W : Wit κ} {s : Scale κ} {u : Fin 3 → ℝ}
    {q : Fin 4 → ℝ} (hq : q ≠ 0) (hs : 0 < s.den) (h : W.Premises pts u)
    (hfit : (Polyhedron.ofPoints pts).FitsAlong u (s.re • quatRotation q)) :
    ∃ t ∈ W.choices, W.valS s pts t u q < 0 := by
  by_contra hno
  have hall : ∀ t ∈ W.choices, 0 ≤ W.valS s pts t u q := fun t ht ↦
    not_lt.mp fun hlt ↦ hno ⟨t, ht, hlt⟩
  have hb : (0 : ℝ) < s.den := by exact_mod_cast hs
  have hfit' : (Polyhedron.ofPoints pts).FitsAlong u
      ((Exact.re s.num / (s.den : ℝ)) • quatRotation q) := hfit
  cases W with
  | balanced w =>
    refine Balanced.not_fitsAlong_smul_of_premises hq h hb (fun t ht ↦ ?_) hfit'
    have h0 := hall [t 0, t 1, t 2] (by
      simp only [choices, List.mem_flatMap, List.mem_map]
      exact ⟨t 0, ht 0, t 1, ht 1, t 2, ht 2, rfl⟩)
    have hl : (fun i : Fin 3 ↦ (s.den : ℝ) • Exact.reV (pt pts ([t 0, t 1, t 2].getD i 0))) =
        fun i ↦ (s.den : ℝ) • Exact.reV (pt pts (t i)) := by
      funext i
      fin_cases i <;> rfl
    simp only [valS] at h0
    rw [hl] at h0
    exact h0
  | width w =>
    refine Width.not_fitsAlong_smul_of_premises hq h hb (fun i hi j hj ↦ ?_) hfit'
    exact hall [i, j] (by
      simp only [choices, List.mem_flatMap, List.mem_map]
      exact ⟨i, hi, j, hj, rfl⟩)
  | centred w =>
    refine Centred.not_fitsAlong_smul_of_premises hq h hb (fun p hp ↦ ?_) hfit'
    exact hall [p.1, p.2] (List.mem_map.mpr ⟨p, hp, rfl⟩)

/-- **At a fit of the scaled plug with the premises, some anchor choice is negative**, at the
outputs `o` followed by the pre-rotation `pre`, if any. -/
theorem exists_negS {pts : List (V3 κ)} {W : Wit κ} {s : Scale κ} {o : ℕ → ℝ}
    {pre : Option (Q4 κ)} (hq : outQ o ≠ 0) (hpre : ∀ c ∈ Exact.rePre pre, c ≠ 0)
    (hs : 0 < s.den) (h : W.Premises pts (outU o))
    (hfit : (Polyhedron.ofPoints pts).FitsAlong (outU o)
      (s.re • (quatRotation (outQ o) * preRot (Exact.rePre pre)))) :
    ∃ t ∈ W.choices, ((W.polyS s pts t).pre pre).eval o < 0 := by
  rw [← quatRotation_preQuat] at hfit
  obtain ⟨t, ht, hneg⟩ := exists_neg_valS (preQuat_ne_zero hq hpre) hs h hfit
  exact ⟨t, ht, by rwa [eval_preS]⟩

end Wit

/-! ### Signed combinations at a scale -/

namespace Obst

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]
variable (s : Scale κ) (pts : List (V3 κ)) (n : ℕ) (Ψ : GenMap κ) (b : Box) (ob : Obst κ)
  (pre : Option (Q4 κ))

/-- The term of choice `j` of part `i` at the plug scale `s`, with the pre-rotation `pre`. -/
def termS (i j : ℕ) : Term κ :=
  ⟨(((ob.part i).1.polyS s pts ((ob.part i).1.choices.getD j [])).pre pre).comp Ψ,
    (ob.exps.getD i []).getD j []⟩

/-- The terms at the plug scale `s`: choice `j` of part `i` at index `i K + j`. -/
def termsS : List (Term κ) :=
  (List.range (ob.parts.length * ob.K)).map fun idx ↦
    ob.termS s pts Ψ pre (idx / ob.K) (idx % ob.K)

/-- **The polynomial check with signed monomials at the plug scale `s`**: `polyOkS` (`x = false`)
or `polyOkSX` (`x = true`, the sparse sign check) on the scaled terms. -/
def polyOkSS (x : Bool) (o : List (ℕ × ℕ) := []) (f : List (List ℤ) := []) : Bool :=
  (List.range ob.parts.length).all (fun i ↦
    (List.range (ob.part i).1.choices.length).all fun j ↦
      ob.sgn n b i j != 0 && decide (0 < fac f i j)) &&
    bif x then Pull.checkX n (ob.termsS s pts Ψ pre) false ob.depth b
        (combTuplesS ob.K (ob.sgnF n b f) ob.specs) o
      else Pull.check n (ob.termsS s pts Ψ pre) false ob.depth b
        (combTuplesS ob.K (ob.sgnF n b f) ob.specs) o

/-- `polyOkSS` as compiled code runs it (`polyOkSS_eq_polyOkSSF`): the sign checks by
`Pull.checkXComb` and `Pull.checkComb`, once per tuple of representatives of the anchor choices
with equal data. -/
def polyOkSSF (x : Bool) (o : List (ℕ × ℕ) := []) (f : List (List ℤ) := []) : Bool :=
  (List.range ob.parts.length).all (fun i ↦
    (List.range (ob.part i).1.choices.length).all fun j ↦
      ob.sgn n b i j != 0 && decide (0 < fac f i j)) &&
    bif x then Pull.checkXComb n (ob.termsS s pts Ψ pre) false ob.depth b ob.K (ob.sgnF n b f)
        (ob.specs.map fun p ↦ (p.1, List.range p.2.1, p.2.2)) o
      else Pull.checkComb n (ob.termsS s pts Ψ pre) false ob.depth b ob.K (ob.sgnF n b f)
        (ob.specs.map fun p ↦ (p.1, List.range p.2.1, p.2.2)) o

@[csimp] theorem polyOkSS_eq_polyOkSSF : @polyOkSS = @polyOkSSF := by
  funext κ _ _ _ _ s pts n Ψ b ob pre x o f
  cases x <;>
    simp only [polyOkSS, polyOkSSF, Bool.cond_true, Bool.cond_false, combTuplesS_eq_combL,
      Pull.check_combL, Pull.checkX_combL]

variable {s pts n Ψ b ob pre}

theorem getD_termsS {i j : ℕ} (hi : i < ob.parts.length) (hj : j < ob.K) :
    (ob.termsS s pts Ψ pre).getD (i * ob.K + j) default = ob.termS s pts Ψ pre i j := by
  have hK : 0 < ob.K := lt_of_le_of_lt (Nat.zero_le j) hj
  have hlt : i * ob.K + j < ob.parts.length * ob.K := by
    have : (i + 1) * ob.K ≤ ob.parts.length * ob.K := Nat.mul_le_mul_right _ hi
    rw [Nat.succ_mul] at this
    omega
  rw [termsS, Box.getD_range_map _ _ _ hlt, Nat.add_comm, Nat.add_mul_div_right _ _ hK,
    Nat.div_eq_of_lt hj, zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

/-- **Soundness of signed combinations at a scale** (`polyOkS_sound`, `polyOkSX_sound`). If every
part has positive weight and an anchor choice whose scaled polynomial is negative at a point of
the box, the check fails. -/
theorem polyOkSS_sound {x : Bool} {o : List (ℕ × ℕ)} {f : List (List ℤ)}
    (h : ob.polyOkSS s pts n Ψ b pre x o f = true) {z : Fin n → ℝ} (hz : b.Mem n z)
    (hne : ob.parts ≠ []) (hw : ∀ p ∈ ob.parts, 0 < p.2)
    (hneg : ∀ i, i < ob.parts.length → ∃ j, j < (ob.part i).1.choices.length ∧
      (((ob.part i).1.polyS s pts ((ob.part i).1.choices.getD j [])).pre pre).eval
        (Ψ.run Exact.re (ext n z)) < 0) : False := by
  simp only [polyOkSS, Bool.and_eq_true, List.all_eq_true, List.mem_range, bne_iff_ne,
    ne_eq, decide_eq_true_eq] at h
  obtain ⟨hmono, hcheck⟩ := h
  have hden : 0 < b.den := by
    cases x
    · exact Pull.den_pos_of_check hcheck
    · exact Pull.den_pos_of_checkX hcheck
  choose! g hg hgneg using hneg
  set τ := ob.specs.map fun p ↦ (p.1 * ob.K + g p.1, p.2.2 * ob.sgnF n b f p.1 (g p.1)) with hτ
  have hmem : τ ∈ combTuplesS ob.K (ob.sgnF n b f) ob.specs :=
    mem_combTuplesS _ _ g _ fun p hp ↦ by
    simp only [specs, List.mem_map, List.mem_range] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    exact hg i hi
  obtain ⟨c, hc, r, heq, hsign⟩ : ∃ c : ℝ, 0 < c ∧ ∃ r : ℕ → ℝ,
      (∀ jw ∈ τ, ((ob.termsS s pts Ψ pre).getD jw.1 default).G.run Exact.re (ext n z) =
        c * DPoly.monoVal n ((ob.termsS s pts Ψ pre).getD jw.1 default).e z * r jw.1) ∧
      Sign false (τ.map fun jw ↦ (jw.2 : ℝ) * r jw.1).sum := by
    cases x
    · exact Pull.check_sound hcheck τ hmem z hz
    · exact Pull.checkX_sound hcheck τ hmem z hz
  have hall : ∀ jw ∈ τ, (jw.2 : ℝ) * r jw.1 < 0 := by
    intro jw hjw
    simp only [hτ, specs, List.map_map, List.mem_map, List.mem_range, Function.comp] at hjw
    obtain ⟨i, hi, rfl⟩ := hjw
    have hgi := hg i hi
    have hgK := lt_of_lt_of_le hgi (le_K hi)
    have he := heq _ (List.mem_map.mpr ⟨(i, (ob.part i).1.choices.length, ((ob.part i).2 : ℤ)),
      List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, rfl⟩)
    simp only [getD_termsS hi hgK, termS, PosePoly.comp_run] at he
    have hs0 : ob.sgn n b i (g i) ≠ 0 := (hmono i hi (g i) hgi).1
    have hf0 : (0 : ℝ) < (fac f i (g i) : ℝ) := by exact_mod_cast (hmono i hi (g i) hgi).2
    have hσs := neg_of_signed hc (monoSign_eq hs0) (monoSign_mul_nonneg hs0 hden hz) he
      (hgneg i hi)
    have hwi : (0 : ℝ) < ((ob.part i).2 : ℝ) := by exact_mod_cast hw _ (part_mem hi)
    simp only [sgnF, sgn] at hσs ⊢
    push_cast
    have : ((ob.part i).2 : ℝ) * ((monoSign n b ((ob.exps.getD i []).getD (g i) []) : ℝ) *
        (fac f i (g i) : ℝ)) * r (i * ob.K + g i) = ((ob.part i).2 : ℝ) * (fac f i (g i) : ℝ) *
        ((monoSign n b ((ob.exps.getD i []).getD (g i) []) : ℝ) * r (i * ob.K + g i)) := by ring
    rw [this]
    exact mul_neg_of_pos_of_neg (mul_pos hwi hf0) hσs
  have hτne : τ ≠ [] := by
    simp only [hτ, specs, ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
    exact fun h0 ↦ hne (List.length_eq_zero_iff.mp h0)
  have hsum := sum_neg_of_mul_neg τ hτne hall
  simp only [Sign, Bool.false_eq_true, ↓reduceIte] at hsign
  linarith

end Obst

/-! ### Obstruction and combination leaves at a scale -/

namespace TObst

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]
variable (s : Scale κ) (pts : List (V3 κ)) (n : ℕ) (Ψ : GenMap κ) (b : Box) (t : TObst κ)
  (pre : Option (Q4 κ))

/-- **The check of an obstruction or combination leaf at the plug scale `s`**: `check`
(`x = false`) or `checkX` (`x = true`, the sparse sign checks) with the witness polynomials of the
plugs times `s.num` and the anchors times `s.den`. The premises are those of the unscaled
leaf. -/
def checkS (x : Bool) (o : List (ℕ × ℕ) := []) (f : List (List ℤ) := []) : Bool :=
  !t.parts.isEmpty &&
    t.parts.all (fun p ↦
      decide (0 < p.weight) && p.wit.domOk pts p.dom && (p.wit.excs pts).isSome) &&
    (bif x then formsOkX n Ψ b t.depth (t.forms pts) o
      else formsOk n Ψ b t.depth (t.forms pts) o) &&
    t.obst.polyOkSS s pts n Ψ b pre x o f

variable {s pts n Ψ b t pre}

/-- **Soundness of tree obstruction leaves at a scale.** At a point of the box whose view output
is not orthogonal to the exceptional vectors, the plug scaled by `s` has no fit at the outputs
with the pre-rotation. -/
theorem checkS_sound {x : Bool} {o : List (ℕ × ℕ)} {f : List (List ℤ)}
    (h : t.checkS s pts n Ψ b pre x o f = true) (hs : 0 < s.den)
    (hpre : ∀ c ∈ Exact.rePre pre, c ≠ 0) {z : Fin n → ℝ} (hz : b.Mem n z)
    (hexc : ∀ g ∈ t.excs pts, Exact.reV g ⬝ᵥ outU (Ψ.run Exact.re (ext n z)) ≠ 0)
    (hq : outQ (Ψ.run Exact.re (ext n z)) ≠ 0) :
    ¬ (Polyhedron.ofPoints pts).FitsAlong (outU (Ψ.run Exact.re (ext n z)))
      (s.re • (quatRotation (outQ (Ψ.run Exact.re (ext n z))) *
        preRot (Exact.rePre pre))) := by
  simp only [checkS, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.isEmpty_eq_false_iff, List.all_eq_true, decide_eq_true_eq, Option.isSome_iff_exists]
    at h
  obtain ⟨⟨⟨hne, hparts⟩, hforms⟩, hpoly⟩ := h
  have hf : ∀ ge ∈ t.forms pts,
      0 ≤ Exact.reV ge.1 ⬝ᵥ outU (Ψ.run Exact.re (ext n z)) := by
    cases x
    · exact formsOk_sound hforms hz
    · exact formsOkX_sound hforms hz
  intro hfit
  refine Obst.polyOkSS_sound hpoly hz (by simpa [obst] using hne) (fun q hq' ↦ ?_) fun i hi ↦ ?_
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq'
    exact (hparts p hp).1.1
  · have hi' : i < t.parts.length := by simpa [obst] using hi
    rw [obst_part hi']
    set p := t.parts[i] with hpdef
    have hp : p ∈ t.parts := List.getElem_mem hi'
    obtain ⟨⟨-, hd⟩, gs, hgs⟩ := hparts p hp
    have hprem := Wit.premises_of_weak hd hgs (fun g hg ↦ by
      obtain ⟨e, he⟩ := mem_forms hp hg
      exact hf _ he) fun g hg ↦ hexc g (List.mem_flatMap.mpr ⟨p, hp, by rw [hgs]; exact hg⟩)
    obtain ⟨tt, ht, hlt⟩ := Wit.exists_negS hq hpre hs hprem hfit
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
    exact ⟨j, hj, by rwa [List.getD_eq_getElem _ _ hj]⟩

theorem excs_ne_of_checkS {x : Bool} {o : List (ℕ × ℕ)} {f : List (List ℤ)}
    (h : t.checkS s pts n Ψ b pre x o f = true) :
    ∀ g ∈ t.excs pts, Exact.nonzeroV g = true := by
  simp only [checkS, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Option.isSome_iff_exists] at h
  obtain ⟨⟨⟨-, hparts⟩, -⟩, -⟩ := h
  intro g hg
  obtain ⟨p, hp, hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨-, gs, hgs⟩ := hparts p hp
  rw [hgs, Option.getD_some] at hg
  exact Wit.excs_ne hgs g hg

end TObst

/-! ### Chart trees at a scale -/

namespace ChartTree

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- **The check of a leaf of a chart tree at the plug scale `s`** (`leafOk` without symmetry
data): obstruction and combination leaves at the scale, outside leaves as they are; an exclusion
leaf fails. -/
def leafOkS (s : Scale κ) (pts : List (V3 κ)) (pre : Option (Q4 κ)) (B : ChartBox) (n : ℕ)
    (x : FLeaf κ (TLeaf κ)) : Bool :=
  Exact.preOk pre && match x.data.base with
  | .obst t => t.checkS s pts n (leafMap x) x.box pre x.data.isExact x.data.ord x.data.facs
  | .out o => bif x.data.isExact then o.checkX B n (leafMap x) x.box x.data.ord
      else o.check B n (leafMap x) x.box x.data.ord
  | _ => false

/-- **The check of a chart tree at the plug scale `s`** on the claim box `B` pre-rotated by `pre`
if any: the scale's denominator, the box, the steps and the leaves. -/
def checkS (s : Scale κ) (pts : List (V3 κ)) (B : ChartBox) (T : ChartTree κ)
    (pre : Option (Q4 κ) := none) : Bool :=
  decide (0 < s.den) && T.boxOk B && match T.leaves B with
    | some ls => ls.all (leafOkS s pts pre B T.n)
    | none => false

/-- The checks of the leaves `a, …, b - 1` at the plug scale `s`, with the pre-rotation `pre`. -/
def leavesOkS (s : Scale κ) (pts : List (V3 κ)) (B : ChartBox) (T : ChartTree κ) (a b : ℕ)
    (pre : Option (Q4 κ) := none) : Bool :=
  decide (a ≤ b) && match T.leaves B with
    | some ls => ((ls.drop a).take (b - a)).all (leafOkS s pts pre B T.n)
    | none => false

theorem leavesOkS_trans {s : Scale κ} {pts : List (V3 κ)} {B : ChartBox} {T : ChartTree κ}
    {a b c : ℕ} {pre : Option (Q4 κ)} (h₁ : T.leavesOkS s pts B a b pre = true)
    (h₂ : T.leavesOkS s pts B b c pre = true) : T.leavesOkS s pts B a c pre = true := by
  unfold leavesOkS at *
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

/-- **The check at a scale from its parts**: the head of the unscaled check (`head`) and the
leaves. -/
theorem checkS_of_parts {s : Scale κ} {pts : List (V3 κ)} {B : ChartBox} {T : ChartTree κ}
    {m : ℕ} {pre : Option (Q4 κ)} (hs : 0 < s.den) (h : T.head B m = true)
    (hl : T.leavesOkS s pts B 0 m pre = true) : T.checkS s pts B pre = true := by
  unfold head at h
  unfold leavesOkS at hl
  unfold checkS
  cases hls : T.leaves B with
  | none => simp [hls] at h
  | some ls =>
    simp only [hls, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h hl ⊢
    obtain ⟨hok, hm⟩ := h
    rw [List.drop_zero, Nat.sub_zero, ← hm, List.take_length] at hl
    exact ⟨⟨hs, hok⟩, hl.2⟩

/-- The exceptional vectors of the leaves are not zero. -/
theorem excs_neS {s : Scale κ} {pts : List (V3 κ)} {pre : Option (Q4 κ)} {B : ChartBox} {n : ℕ}
    {ls : List (FLeaf κ (TLeaf κ))} (h : ∀ x ∈ ls, leafOkS s pts pre B n x = true) :
    ∀ g ∈ ls.flatMap (leafExcs pts), Exact.nonzeroV g = true := by
  intro g hg
  obtain ⟨x, hx, hgx⟩ := List.mem_flatMap.mp hg
  have hok := h x hx
  unfold leafExcs at hgx
  unfold leafOkS at hok
  cases hxd : x.data.base with
  | obst t =>
    rw [hxd] at hgx hok
    simp only [Bool.and_eq_true] at hok
    exact TObst.excs_ne_of_checkS hok.2 g hgx
  | _ =>
    rw [hxd] at hgx
    simp at hgx

/-- **Interior poses at a scale.** At a pose strictly inside the claim box, off the exceptional
set of the leaves, the plug scaled by `s` has no fit. -/
theorem not_fitsAlong_interiorS {s : Scale κ} {pts : List (V3 κ)} {pre : Option (Q4 κ)}
    {B : ChartBox} {T : ChartTree κ} (hs : 0 < s.den) (hok : T.boxOk B = true)
    {ls : List (FLeaf κ (TLeaf κ))} (hls : T.leaves B = some ls)
    (h : ∀ x ∈ ls, leafOkS s pts pre B T.n x = true) {y : Fin 5 → ℝ}
    (hy : ∀ i : Fin 5, (B.box.lo.getD i 0 : ℝ) / B.box.den < y i ∧
      y i < (B.box.hi.getD i 0 : ℝ) / B.box.den)
    (hg : ∀ g ∈ ls.flatMap (leafExcs pts), Exact.reV g ⬝ᵥ viewDir B.view (y 0) (y 1) ≠ 0) :
    ¬ (Polyhedron.ofPoints pts).FitsAlong (viewDir B.view (y 0) (y 1))
      (s.re • ((chartPose B.view B.rot y).rotation * preRot (Exact.rePre pre))) := by
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
  unfold leafOkS at hok
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
    have hno := TObst.checkS_sound hok.2 hs hpre hz hexc hq
    exact not_fitsAlong_smul_of_represents (p := chartPose B.view B.rot y) hno hrep
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
  | _ =>
    rw [hxd] at hok
    simp at hok

/-- **Soundness of chart trees at a plug scale**, on a box pre-rotated by `pre` if any. No pose
of the claim box fits the plug scaled by `s`, with its rotation followed by the pre-rotation. -/
theorem checkS_sound_pre {s : Scale κ} {pts : List (V3 κ)} {B : ChartBox} {T : ChartTree κ}
    {pre : Option (Q4 κ)} (h : T.checkS s pts B pre = true) :
    (Polyhedron.ofPoints pts).NoFitRot B.poses (s.re • preRot (Exact.rePre pre)) := by
  simp only [checkS, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hs, hok⟩, h⟩ := h
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
  refine Polyhedron.noFitRot_box_of_interior _ B.view B.rot (s.re • preRot (Exact.rePre pre))
    (lo := fun i ↦ (B.box.lo.getD i 0 : ℝ) / B.box.den)
    (hi := fun i ↦ (B.box.hi.getD i 0 : ℝ) / B.box.den)
    (fun i ↦ div_lt_div_of_pos_right (by exact_mod_cast hlt i i.isLt) hd)
    ((ls.flatMap (leafExcs pts)).map Exact.reV) ?_ ?_ hp hfit
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact Exact.reV_ne_zero_of_nonzeroV (excs_neS h g' hg')
  · intro y hy hg
    rw [Matrix.mul_smul]
    exact not_fitsAlong_interiorS hs hok hls h hy fun g hg' ↦ hg _ (List.mem_map_of_mem hg')

/-- **Soundness of chart trees at a plug scale.** No pose of the claim box fits the plug scaled
by `s`. -/
theorem checkS_sound {s : Scale κ} {pts : List (V3 κ)} {B : ChartBox} {T : ChartTree κ}
    (h : T.checkS s pts B = true) :
    (Polyhedron.ofPoints pts).NoFitRot B.poses (s.re • 1) := by
  have h0 := checkS_sound_pre h
  rwa [Exact.rePre_none, preRot_none] at h0

end ChartTree

end Nieuwland.Check
