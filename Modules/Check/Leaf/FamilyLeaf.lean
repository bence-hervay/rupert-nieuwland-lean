import Modules.Check.Leaf.Family
import Modules.Check.Leaf.Exclusion
import Modules.Check.Leaf.Centred

/-!
# Leaves of pose families

The leaves of weighted zooms and chart trees (`Modules/Check/Leaf/Family.lean`) prove facts about the
pose represented by the outputs `o` of their map at the points of their box: the view direction
`outU o` and the rotation `quatRotation (outQ o)`. The facts are stated at any representative and
survive `PoseSim`:

* `NoFitRep`: no fit along the view, with any translation (and with the rotation followed by a
  pre-rotation, if any);
* `ExclRep`: a pose map of signed symmetries increases the orbit score (symmetry exclusion);
* `coordOf`: a chart coordinate of the pose, for outside leaves.

At a chart pose they give `NoFit` and `Polyhedron.Excluded` (`NoFitRep.noFit`,
`ExclRep.excluded`).

**Pre-rotated boxes.** On a claim box pre-rotated by `q_c` the outputs stay the view direction and
the chart quaternion `q` of the pose, so maps, steps and outside leaves are unchanged, and the
witness polynomials of obstruction leaves are taken at `q q_c` (`PosePoly.pre`), as Rust takes
them at the rotated plug points.

**Pose polynomials** (`PosePoly`) are polynomials in a view vector and a quaternion, natural like
`GenPoly`; at the outputs of a pose map they are computations in the slots (`PosePoly.comp`), whose
signs `Pull.check` certifies on boxes, each divided by a monomial in the slots.

* `Obst`: support witnesses with positive weights, one (an obstruction leaf) or several (a
  nonnegative combination, `RESEARCH.md` §7.2). Every polynomial of every anchor choice, divided by
  its monomial, and every weighted sum of one choice per witness is nonnegative on the box, and the
  monomials are nonnegative there (`monoOk`). At a fit with the premises, every witness has a
  negative choice (`Wit.exists_neg`), so some checked sum is negative: `Obst.check_sound`.
* `ExclLeaf`: the improvement numerator of two symmetries, divided by a power of slot `0`, is
  positive on the box; so it is positive where slot `0` is (`ExclLeaf.check_sound`).
* `OutLeaf`: a chart coordinate minus a bound of the claim box, times the square of its
  denominator, divided by a power of slot `0`, is positive on the box (`OutLeaf.check_sound`).
-/

open Matrix

namespace Nieuwland

/-- **Fits along multiples.** A fit along `a • u` with `a ≠ 0` is a fit along `u`. -/
theorem Polyhedron.FitsAlong.of_smul {P : Polyhedron} {u : Fin 3 → ℝ}
    {R : Matrix (Fin 3) (Fin 3) ℝ} {a : ℝ} (ha : a ≠ 0) (h : P.FitsAlong (a • u) R) :
    P.FitsAlong u R := by
  obtain ⟨L, hL, hker, τ, hτ⟩ := h
  exact ⟨L, hL, by rw [hker, Submodule.span_singleton_smul_eq (IsUnit.mk0 a ha)], τ, hτ⟩

namespace Check

open Pull

/-! ### Outputs and pose polynomials -/

section Outputs

variable {α β : Type*}

/-- The view vector of the outputs `o`: outputs `0, 1, 2`. -/
def viewOf (o : ℕ → α) : V3 α := ⟨o 0, o 1, o 2⟩

/-- The quaternion of the outputs `o`: outputs `3, …, 6`. -/
def quatOf (o : ℕ → α) : Q4 α := ⟨o 3, o 4, o 5, o 6⟩

/-- Output `i` of a view vector and a quaternion: `U` at `0, 1, 2`, `Q` at `3, …, 6`. -/
def outOf (U : V3 α) (Q : Q4 α) : ℕ → α
  | 0 => U.x
  | 1 => U.y
  | 2 => U.z
  | 3 => Q.w
  | 4 => Q.x
  | 5 => Q.y
  | _ => Q.z

theorem map_viewOf (f : α → β) (o : ℕ → α) : (viewOf o).map f = viewOf (f ∘ o) := rfl

theorem map_quatOf (f : α → β) (o : ℕ → α) : (quatOf o).map f = quatOf (f ∘ o) := rfl

theorem map_outOf (f : α → β) (U : V3 α) (Q : Q4 α) (i : ℕ) :
    f (outOf U Q i) = outOf (U.map f) (Q.map f) i := by
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | _ + 6 => rfl

theorem outOf_of {o : ℕ → α} {i : ℕ} (hi : i < 7) : outOf (viewOf o) (quatOf o) i = o i := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => rfl

/-- The outputs `0, …, 6` of a view vector and a quaternion, as data (`GenMap.all`). -/
def outAll (U : V3 α) (Q : Q4 α) : Array α := #[U.x, U.y, U.z, Q.w, Q.x, Q.y, Q.z]

theorem outAll_get (U : V3 α) (Q : Q4 α) (i : ℕ) (h : i < (outAll U Q).size) :
    (outAll U Q)[i] = outOf U Q i := by
  match i, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => rfl

end Outputs

theorem toFun_viewOf (o : ℕ → ℝ) : (viewOf o).toFun = outU o := by
  funext i
  fin_cases i <;> rfl

theorem toFun_quatOf (o : ℕ → ℝ) : (quatOf o).toFun = outQ o := by
  funext i
  fin_cases i <;> rfl

/-- A polynomial in a view vector and a quaternion, computed in any type with `+`, `-` and `*`
from constants in `κ` embedded by `k`, and natural in maps that commute with the operations. -/
structure PosePoly (κ : Type) where
  /-- The computation. -/
  run : {α : Type} → [Add α] → [Sub α] → [Mul α] → (κ → α) → V3 α → Q4 α → α
  /-- Naturality. -/
  natural : ∀ {α β : Type} [Add α] [Sub α] [Mul α] [Add β] [Sub β] [Mul β] (f : α → β),
    IsArith f → ∀ (k : κ → α) (U : V3 α) (Q : Q4 α),
      f (run k U Q) = run (f ∘ k) (U.map f) (Q.map f)

namespace PosePoly

variable {κ : Type}

/-- The polynomial at the outputs of the map `Ψ`: a computation in the slots. -/
def comp (P : PosePoly κ) (Ψ : GenMap κ) : GenPoly κ where
  run k x := P.run k (viewOf (Ψ.run k x)) (quatOf (Ψ.run k x))
  natural f hf k x := by
    rw [P.natural f hf, map_viewOf, map_quatOf, Ψ.natural f hf]

/-- `comp` with the outputs of `Ψ` computed once, as data: what compiled code runs
(`comp_eq_compM`). -/
def compM (P : PosePoly κ) (Ψ : GenMap κ) : GenPoly κ where
  run k x :=
    let a := Ψ.all k x
    P.run k (viewOf (look a (Ψ.run k x))) (quatOf (look a (Ψ.run k x)))
  natural f hf k x := by
    simp only [GenMap.look_all]
    exact (P.comp Ψ).natural f hf k x

@[csimp] theorem comp_eq_compM : @comp = @compM := by
  funext κ P Ψ
  simp only [comp, compM, GenMap.look_all]

/-- The polynomial at the quaternion followed by the pre-rotation `c`, if any (`preQ`). -/
def pre (P : PosePoly κ) (c : Option (Q4 κ)) : PosePoly κ where
  run k U Q := P.run k U (preQ k Q c)
  natural f hf k U Q := by
    rw [P.natural f hf, map_preQ hf]

variable [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The real value at the outputs `o`. -/
noncomputable def eval (P : PosePoly κ) (o : ℕ → ℝ) : ℝ :=
  P.run Exact.re (viewOf o) (quatOf o)

theorem comp_run (P : PosePoly κ) (Ψ : GenMap κ) (x : ℕ → ℝ) :
    (P.comp Ψ).run Exact.re x = P.eval (Ψ.run Exact.re x) := rfl

end PosePoly

variable {κ : Type} [Add κ] [Sub κ] [Mul κ]

/-! ### Facts at representatives -/

section Facts

variable [Exact κ]

/-- No fit along the view and with the rotation of the outputs `o` followed by the pre-rotation
`c`, if any, with any translation. -/
def NoFitRep (pts : List (V3 κ)) (c : Option (Fin 4 → ℝ)) (o : ℕ → ℝ) : Prop :=
  ¬ (Polyhedron.ofPoints pts).FitsAlong (outU o) (quatRotation (outQ o) * preRot c)

/-- At the view and the rotation of the outputs `o`, a pose map of signed symmetries about the
centre of `D` increases the score of `D` (`Polyhedron.Excluded`). -/
def ExclRep (pts : List (V3 κ)) (D : SymmData κ) (o : ℕ → ℝ) : Prop :=
  ∃ A σ B τ, (Polyhedron.ofPoints pts).IsSignedSymm D.centre A σ ∧
    (Polyhedron.ofPoints pts).IsSignedSymm D.centre B τ ∧
    D.score.f (outU o) (quatRotation (outQ o)) <
      D.score.f (A *ᵥ outU o) (turn (σ * τ) (A *ᵥ outU o) * A * quatRotation (outQ o) * B)

/-- The outputs `o` represent the chart pose `p`: its view direction and chart quaternion, up to
nonzero factors. -/
def Represents (p : ChartPose) (o : ℕ → ℝ) : Prop :=
  ∃ a b : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ outU o = a • viewDir p.view p.s p.t ∧
    outQ o = b • chartQuat p.rot p.x

theorem Represents.of_sim {p : ChartPose} {o o' : ℕ → ℝ} (h : Represents p o)
    (hs : PoseSim o o') : Represents p o' := by
  obtain ⟨a, b, ha, hb, hu, hq⟩ := h
  obtain ⟨a', b', ha', hb', hu', hq'⟩ := hs
  exact ⟨a' * a, b' * b, mul_ne_zero ha' ha, mul_ne_zero hb' hb, by rw [hu', hu, smul_smul],
    by rw [hq', hq, smul_smul]⟩

theorem NoFitRep.of_sim {pts : List (V3 κ)} {c : Option (Fin 4 → ℝ)} {o o' : ℕ → ℝ}
    (h : NoFitRep pts c o) (hs : PoseSim o o') : NoFitRep pts c o' := by
  obtain ⟨a, b, ha, hb, hu, hq⟩ := hs
  intro hfit
  rw [hu, hq, quatRotation_smul hb] at hfit
  exact h (hfit.of_smul ha)

theorem ExclRep.of_sim {pts : List (V3 κ)} {D : SymmData κ} {o o' : ℕ → ℝ} (h : ExclRep pts D o)
    (hs : PoseSim o o') : ExclRep pts D o' := by
  obtain ⟨a, b, ha, hb, hu, hq⟩ := hs
  obtain ⟨A, σ, B, τ, hA, hB, hlt⟩ := h
  refine ⟨A, σ, B, τ, hA, hB, ?_⟩
  rw [hu, hq, quatRotation_smul hb, mulVec_smul, turn_smul ha]
  simp only [Score.f, orbitScore_smul _ _ _ ha]
  exact hlt

/-- **No fit at a chart pose**, with its rotation followed by the pre-rotation `c`, if any. -/
theorem NoFitRep.noFit {pts : List (V3 κ)} {c : Option (Fin 4 → ℝ)} {o : ℕ → ℝ} {p : ChartPose}
    (h : NoFitRep pts c o) (hp : Represents p o) :
    ¬ (Polyhedron.ofPoints pts).FitsAlong (viewDir p.view p.s p.t) (p.rotation * preRot c) := by
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

/-- **No fit at a chart pose**, without a pre-rotation. -/
theorem NoFitRep.not_fitsAt {pts : List (V3 κ)} {o : ℕ → ℝ} {p : ChartPose}
    (h : NoFitRep pts none o) (hp : Represents p o) (τ : Fin 2 → ℝ) :
    ¬ (Polyhedron.ofPoints pts).FitsAt p τ := fun hfit ↦
  h.noFit hp (by rw [preRot_none, mul_one]; exact Polyhedron.fitsAlong_of_fitsAt hfit)

/-- **Exclusion at a chart pose.** -/
theorem ExclRep.excluded {pts : List (V3 κ)} {D : SymmData κ} {o : ℕ → ℝ} {p : ChartPose}
    (h : ExclRep pts D o) (hp : Represents p o) :
    (Polyhedron.ofPoints pts).Excluded D.centre D.score.f p := by
  obtain ⟨a, b, ha, hb, hu, hq⟩ := hp
  obtain ⟨A, σ, B, τ, hA, hB, hlt⟩ := h
  refine ⟨A, σ, B, τ, hA, hB, ?_⟩
  have hR : p.rotation = quatRotation (outQ o) := by
    rw [hq, quatRotation_smul hb]
    rfl
  rw [hR]
  rw [hu, mulVec_smul, turn_smul ha] at hlt
  simp only [Score.f, orbitScore_smul _ _ _ ha] at hlt
  exact hlt

end Facts

/-! ### Support witnesses -/

/-- A support witness of a family leaf or a polar zoom: balanced supports, a width pair or a
centred support. -/
inductive Wit (κ : Type) where
  /-- Balanced supports. -/
  | balanced (w : Balanced)
  /-- A width pair. -/
  | width (w : Width κ)
  /-- A centred support. -/
  | centred (w : Centred κ)

instance [Exact κ] : Inhabited (Wit κ) :=
  ⟨.width ⟨⟨Exact.ofInt 0, Exact.ofInt 0, Exact.ofInt 0⟩, ⟨[], 0⟩, ⟨[], 0⟩⟩⟩

namespace Wit

/-- The anchor choices, in the order of `evidence_polynomials` (`regional.rs`): triples for
balanced supports, pairs (along `c`, along `-c`) for width pairs, and the anchor pairs of a centred
support (rupert's anchors, each with its antipode). -/
def choices : Wit κ → List (List ℕ)
  | balanced w => w.s₀.anchors.flatMap fun i ↦ w.s₁.anchors.flatMap fun j ↦
      w.s₂.anchors.map fun l ↦ [i, j, l]
  | width w => w.pos.anchors.flatMap fun i ↦ w.neg.anchors.map fun j ↦ [i, j]
  | centred w => w.pairs.map fun p ↦ [p.1, p.2]

/-- The degree of the witness polynomials (jointly in the view vector and the quaternion; they
are quadratic in the quaternion). -/
def deg : Wit κ → ℕ
  | balanced _ => 4
  | width _ => 3
  | centred _ => 3

variable [Exact κ]

/-- The witness polynomial of a width pair with direction `c`, plug difference `v` and the anchor
choice `t` (along `c`, along `-c`). -/
def supportP (pts : List (V3 κ)) (c v : V3 κ) (t : List ℕ) : PosePoly κ :=
  ⟨fun k U Q ↦ supportG k U Q c v ((pt pts (t.getD 0 0)).sub (pt pts (t.getD 1 0))),
    fun _ hf k U Q ↦ map_supportG hf k U Q _ _ _⟩

/-- The witness polynomial of the anchor choice `t`. -/
def poly (pts : List (V3 κ)) : Wit κ → List ℕ → PosePoly κ
  | balanced w, t => ⟨fun k U Q ↦ balancedG k (Exact.ofInt w.sigma) U Q (w.dir pts)
      (fun i ↦ pt pts (w.sup i).plug) (fun i ↦ pt pts (t.getD i 0)),
      fun _ hf k U Q ↦ map_balancedG hf k _ U Q _ _ _⟩
  | width w, t => supportP pts w.c (w.plugDiff pts) t
  | centred w, t => supportP pts w.c (w.toWidth.plugDiff pts) t

/-- The real value of the witness polynomial of the anchor choice `t` at the view direction `u`
and the quaternion `q`. -/
noncomputable def val (pts : List (V3 κ)) : Wit κ → List ℕ → (Fin 3 → ℝ) → (Fin 4 → ℝ) → ℝ
  | balanced w, t, u, q => balancedPoly (w.sigma : ℝ) u q (fun i ↦ Exact.reV (w.dir pts i))
      (fun i ↦ Exact.reV (pt pts (w.sup i).plug)) (fun i ↦ Exact.reV (pt pts (t.getD i 0)))
  | width w, t, u, q => supportPoly u q (Exact.reV w.c) (Exact.reV (w.plugDiff pts))
      (Exact.reV ((pt pts (t.getD 0 0)).sub (pt pts (t.getD 1 0))))
  | centred w, t, u, q => supportPoly u q (Exact.reV w.c) (Exact.reV (w.toWidth.plugDiff pts))
      (Exact.reV ((pt pts (t.getD 0 0)).sub (pt pts (t.getD 1 0))))

theorem run_re (pts : List (V3 κ)) (W : Wit κ) (t : List ℕ) (U : V3 ℝ) (Q : Q4 ℝ) :
    (W.poly pts t).run Exact.re U Q = W.val pts t U.toFun Q.toFun := by
  cases W with
  | balanced w => simp only [poly, val, balancedG_re, Exact.re_ofInt]
  | width w => simp only [poly, supportP, val, supportG_re]
  | centred w => simp only [poly, supportP, val, supportG_re]

theorem eval_eq (pts : List (V3 κ)) (W : Wit κ) (t : List ℕ) (o : ℕ → ℝ) :
    (W.poly pts t).eval o = W.val pts t (outU o) (outQ o) := by
  rw [PosePoly.eval, run_re, toFun_viewOf, toFun_quatOf]

theorem eval_pre (pts : List (V3 κ)) (W : Wit κ) (t : List ℕ) (c : Option (Q4 κ)) (o : ℕ → ℝ) :
    ((W.poly pts t).pre c).eval o =
      W.val pts t (outU o) (preQuat (outQ o) (Exact.rePre c)) := by
  change (W.poly pts t).run Exact.re (viewOf o) (preQ Exact.re (quatOf o) c) = _
  rw [run_re, toFun_viewOf, toFun_preQ, toFun_quatOf]

theorem val_smul (pts : List (V3 κ)) (W : Wit κ) (t : List ℕ) (d : ℝ) (u : Fin 3 → ℝ)
    (q : Fin 4 → ℝ) : W.val pts t (d • u) (d • q) = d ^ W.deg * W.val pts t u q := by
  cases W with
  | balanced w => simp only [val, deg, balancedPoly_smul]
  | width w => simp only [val, deg, supportPoly_smul]
  | centred w => simp only [val, deg, supportPoly_smul]

theorem val_smul_quat (pts : List (V3 κ)) (W : Wit κ) (t : List ℕ) (a : ℝ) (u : Fin 3 → ℝ)
    (q : Fin 4 → ℝ) : W.val pts t u (a • q) = a ^ 2 * W.val pts t u q := by
  cases W with
  | balanced w => simp only [val, balancedPoly_smul_quat]
  | width w => simp only [val, supportPoly_smul_quat]
  | centred w => simp only [val, supportPoly_smul_quat]

/-- **Witness polynomials along a line** of quaternions are quadratic. -/
theorem val_add_smul (pts : List (V3 κ)) (W : Wit κ) (t : List ℕ) (u : Fin 3 → ℝ)
    (q r : Fin 4 → ℝ) (δ : ℝ) : W.val pts t u (q + δ • r) = W.val pts t u q +
      δ * (W.val pts t u (q + r) - W.val pts t u q - W.val pts t u r) +
        δ ^ 2 * W.val pts t u r := by
  cases W with
  | balanced w => simp only [val]; exact balancedPoly_add_smul _ _ _ _ _ _ _ _
  | width w => simp only [val]; exact supportPoly_add_smul _ _ _ _ _ _ _
  | centred w => simp only [val]; exact supportPoly_add_smul _ _ _ _ _ _ _

/-- Whether the witness polynomials are linear in the view vector: width pairs and centred
supports. -/
def linear : Wit κ → Bool
  | balanced _ => false
  | width _ => true
  | centred _ => true

/-- **Linear witnesses** are the view vector dotted with a vector that depends on the quaternion
only. -/
theorem exists_dot_of_linear (pts : List (V3 κ)) {W : Wit κ} (h : W.linear = true) (t : List ℕ)
    (q : Fin 4 → ℝ) : ∃ G : Fin 3 → ℝ, ∀ u, W.val pts t u q = u ⬝ᵥ G := by
  cases W with
  | balanced w => exact absurd h (by simp [linear])
  | width w => exact ⟨_, fun u ↦ rfl⟩
  | centred w => exact ⟨_, fun u ↦ rfl⟩

/-- The premises at the view directions of the cone over `us`. -/
def premisesOk (pts us : List (V3 κ)) : Wit κ → Bool
  | balanced w => w.premisesOk pts us
  | width w => w.premisesOk pts us
  | centred w => w.premisesOk pts us

/-- The premises on the views `V` (`Balanced.premisesOkV`, `Width.premisesOkV`,
`Centred.premisesOkV`). -/
def premisesOkV (pts : List (V3 κ)) (V : Views κ) (strong : Bool) : Wit κ → Bool
  | balanced w => w.premisesOkV pts V strong
  | width w => w.premisesOkV pts V strong
  | centred w => w.premisesOkV pts V strong

/-- The premises at the view direction `u`. -/
def Premises (pts : List (V3 κ)) : Wit κ → (Fin 3 → ℝ) → Prop
  | balanced w, u => w.Premises pts u
  | width w, u => w.Premises pts u
  | centred w, u => w.Premises pts u

theorem premises_of_ok {pts us : List (V3 κ)} {W : Wit κ} (h : W.premisesOk pts us = true)
    {u : Fin 3 → ℝ} (hu : ConeBound us u) : W.Premises pts u := by
  cases W with
  | balanced w => exact Balanced.premises_of_ok h hu
  | width w => exact Width.premises_of_ok h hu
  | centred w => exact Centred.premises_of_ok h hu

theorem premises_of_okV {pts : List (V3 κ)} {V : Views κ} {strong : Bool} {W : Wit κ}
    (h : W.premisesOkV pts V strong = true) {u : Fin 3 → ℝ} {r : ℝ} (hu : V.Mem u r)
    (hs : strong = true ∨ 0 < r) : W.Premises pts u := by
  cases W with
  | balanced w => exact Balanced.premises_of_okV h hu hs
  | width w => exact Width.premises_of_okV h hu hs
  | centred w => exact Centred.premises_of_okV h hu hs

/-- **At a fit with the premises, some anchor choice is negative.** -/
theorem exists_neg_val {pts : List (V3 κ)} {W : Wit κ} {u : Fin 3 → ℝ} {q : Fin 4 → ℝ}
    (hq : q ≠ 0) (h : W.Premises pts u)
    (hfit : (Polyhedron.ofPoints pts).FitsAlong u (quatRotation q)) :
    ∃ t ∈ W.choices, W.val pts t u q < 0 := by
  cases W with
  | balanced w =>
    obtain ⟨t, ht, hneg⟩ := Balanced.exists_neg_of_fitsAlong hq h hfit
    refine ⟨[t 0, t 1, t 2], ?_, ?_⟩
    · simp only [choices, List.mem_flatMap, List.mem_map]
      exact ⟨t 0, ht 0, t 1, ht 1, t 2, ht 2, rfl⟩
    · have hl : (fun i : Fin 3 ↦ Exact.reV (pt pts ([t 0, t 1, t 2].getD i 0))) =
          fun i ↦ Exact.reV (pt pts (t i)) := by
        funext i
        fin_cases i <;> rfl
      simp only [val]
      rw [hl]
      exact hneg
  | width w =>
    obtain ⟨i, hi, j, hj, hneg⟩ := Width.exists_neg_of_fitsAlong hq h hfit
    refine ⟨[i, j], ?_, hneg⟩
    simp only [choices, List.mem_flatMap, List.mem_map]
    exact ⟨i, hi, j, hj, rfl⟩
  | centred w =>
    obtain ⟨p, hp, hneg⟩ := Centred.exists_neg_of_fitsAlong hq h hfit
    exact ⟨[p.1, p.2], List.mem_map.mpr ⟨p, hp, rfl⟩, hneg⟩

/-- **At a fit with the premises, some anchor choice is negative**, at the outputs `o` followed by
the pre-rotation `pre`, if any. -/
theorem exists_neg {pts : List (V3 κ)} {W : Wit κ} {o : ℕ → ℝ} {pre : Option (Q4 κ)}
    (hq : outQ o ≠ 0) (hpre : ∀ c ∈ Exact.rePre pre, c ≠ 0) (h : W.Premises pts (outU o))
    (hfit : (Polyhedron.ofPoints pts).FitsAlong (outU o)
      (quatRotation (outQ o) * preRot (Exact.rePre pre))) :
    ∃ t ∈ W.choices, ((W.poly pts t).pre pre).eval o < 0 := by
  rw [← quatRotation_preQuat] at hfit
  obtain ⟨t, ht, hneg⟩ := exists_neg_val (preQuat_ne_zero hq hpre) h hfit
  exact ⟨t, ht, by rwa [eval_pre]⟩

end Wit

/-! ### Signs of monomials -/

/-- On the box `b` of `n` slots, every slot with an odd exponent in `e` is nonnegative, so the
monomial `x^e` is nonnegative there. -/
def monoOk (n : ℕ) (b : Box) (e : List ℕ) : Bool :=
  (List.range n).all fun i ↦ e.getD i 0 % 2 == 0 || decide (0 ≤ b.lo.getD i 0)

theorem getD_tail (e : List ℕ) (i : ℕ) : e.tail.getD i 0 = e.getD (i + 1) 0 := by
  cases e <;> simp

theorem headD_eq_getD (e : List ℕ) : e.headD 0 = e.getD 0 0 := by
  cases e <;> rfl

theorem monoVal_nonneg : ∀ (n : ℕ) (e : List ℕ) (x : Fin n → ℝ),
    (∀ i : Fin n, e.getD i 0 % 2 = 0 ∨ 0 ≤ x i) → 0 ≤ DPoly.monoVal n e x
  | 0, _, _, _ => by simp [DPoly.monoVal]
  | n + 1, e, x, h => by
    change 0 ≤ x 0 ^ e.headD 0 * DPoly.monoVal n e.tail (Fin.tail x)
    refine mul_nonneg ?_ (monoVal_nonneg n e.tail (Fin.tail x) fun i ↦ ?_)
    · rcases h 0 with h' | h'
      · rw [headD_eq_getD]
        exact Even.pow_nonneg (Nat.even_iff.mpr h') _
      · exact pow_nonneg h' _
    · rw [getD_tail]
      exact h i.succ

theorem monoVal_pos : ∀ (n : ℕ) (e : List ℕ) (x : Fin n → ℝ),
    (∀ i : Fin n, e.getD i 0 = 0 ∨ 0 < x i) → 0 < DPoly.monoVal n e x
  | 0, _, _, _ => by simp [DPoly.monoVal]
  | n + 1, e, x, h => by
    change 0 < x 0 ^ e.headD 0 * DPoly.monoVal n e.tail (Fin.tail x)
    refine mul_pos ?_ (monoVal_pos n e.tail (Fin.tail x) fun i ↦ ?_)
    · rcases h 0 with h' | h'
      · rw [headD_eq_getD]
        simp only [Fin.val_zero] at h'
        rw [h', pow_zero]
        exact one_pos
      · exact pow_pos h' _
    · rw [getD_tail]
      exact h i.succ

theorem monoOk_sound {n : ℕ} {b : Box} {e : List ℕ} (h : monoOk n b e = true) (hden : 0 < b.den)
    {x : Fin n → ℝ} (hx : b.Mem n x) : 0 ≤ DPoly.monoVal n e x := by
  refine monoVal_nonneg n e x fun i ↦ ?_
  have hi := List.all_eq_true.mp h i (List.mem_range.mpr i.2)
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hi
  rcases hi with hi | hi
  · exact Or.inl hi
  · right
    have hd : (0 : ℝ) < b.den := by exact_mod_cast hden
    exact (div_nonneg (by exact_mod_cast hi) hd.le).trans (hx i).1

/-- The monomial `x₀^e` is positive where slot `0` is. -/
theorem monoVal_single_pos {n : ℕ} (e : ℕ) {x : Fin n → ℝ} (hx : 0 < ext n x 0) :
    0 < DPoly.monoVal n [e] x := by
  refine monoVal_pos n [e] x fun i ↦ ?_
  rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
  · right
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) i.2
    have : ext n x 0 = x i := by
      simp only [Pull.ext, hn, ↓reduceDIte]
      congr 1
      exact Fin.ext h0.symm
    rw [← this]
    exact hx
  · left
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [hm]
    simp

/-! ### Obstruction leaves -/

/-- The weighted tuples of a combination: for the parts `(i, m, c)` (index, number of anchor
choices, weight), one choice `j < m` of every part, as the term `i K + j` with weight `c`. -/
def combTuples (K : ℕ) : List (ℕ × ℕ × ℤ) → List Tuple
  | [] => [[]]
  | (i, m, c) :: ps => (List.range m).flatMap fun j ↦
      (combTuples K ps).map fun τ ↦ (i * K + j, c) :: τ

theorem mem_combTuples (K : ℕ) (g : ℕ → ℕ) : ∀ ps : List (ℕ × ℕ × ℤ),
    (∀ p ∈ ps, g p.1 < p.2.1) → ps.map (fun p ↦ (p.1 * K + g p.1, p.2.2)) ∈ combTuples K ps
  | [], _ => by simp [combTuples]
  | (i, m, c) :: ps, h => by
    simp only [List.map_cons, combTuples, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨g i, h _ List.mem_cons_self, _,
      mem_combTuples K g ps fun p hp ↦ h p (List.mem_cons_of_mem _ hp), rfl⟩

theorem combTuples_eq_combL (K : ℕ) : ∀ ps : List (ℕ × ℕ × ℤ),
    combTuples K ps = Pull.combL K (fun _ _ ↦ 1) (ps.map fun p ↦ (p.1, List.range p.2.1, p.2.2))
  | [] => rfl
  | (i, m, c) :: ps => by
    simp only [combTuples, List.map_cons, Pull.combL, mul_one, combTuples_eq_combL K ps]

theorem sum_neg_of_forall {s : ℕ → ℝ} : ∀ τ : Tuple, τ ≠ [] →
    (∀ jw ∈ τ, 0 < jw.2 ∧ s jw.1 < 0) → (τ.map fun jw ↦ (jw.2 : ℝ) * s jw.1).sum < 0
  | [], h, _ => absurd rfl h
  | jw :: τ, _, h => by
    rw [List.map_cons, List.sum_cons]
    have h1 : (jw.2 : ℝ) * s jw.1 < 0 :=
      mul_neg_of_pos_of_neg (by exact_mod_cast (h jw List.mem_cons_self).1)
        (h jw List.mem_cons_self).2
    rcases τ with _ | ⟨jw', τ⟩
    · simpa using h1
    · have h2 := sum_neg_of_forall (jw' :: τ) (List.cons_ne_nil _ _) fun x hx ↦
        h x (List.mem_cons_of_mem _ hx)
      linarith

/-- An obstruction leaf: support witnesses with positive weights (one: an obstruction leaf;
several: a nonnegative combination), the exponents of the monomials dividing their polynomials
(per witness and anchor choice; a missing one is `[]`), whether the premises hold at all views
(`strong`) or only where the blow-up parameter is positive, and the bisection depth. -/
structure Obst (κ : Type) where
  /-- The witnesses and their weights. -/
  parts : List (Wit κ × ℕ)
  /-- The exponents of the dividing monomials, per witness and anchor choice. -/
  exps : List (List (List ℕ))
  /-- Whether the premises hold at all views. -/
  strong : Bool
  /-- The bisection depth of the sign check. -/
  depth : ℕ

namespace Obst

variable [ExactBasis κ]
variable (pts : List (V3 κ)) (n : ℕ) (Ψ : GenMap κ) (b : Box) (V : Views κ) (ob : Obst κ)
  (pre : Option (Q4 κ))

/-- Part `i`. -/
def part (i : ℕ) : Wit κ × ℕ := ob.parts.getD i default

/-- The stride of the term indices: the largest number of anchor choices of a part. -/
def K : ℕ := (ob.parts.map fun p ↦ p.1.choices.length).foldr max 0

/-- The term of choice `j` of part `i`, with the pre-rotation `pre`. -/
def term (i j : ℕ) : Term κ :=
  ⟨(((ob.part i).1.poly pts ((ob.part i).1.choices.getD j [])).pre pre).comp Ψ,
    (ob.exps.getD i []).getD j []⟩

/-- The terms: choice `j` of part `i` at index `i K + j`. -/
def terms : List (Term κ) :=
  (List.range (ob.parts.length * ob.K)).map fun idx ↦
    ob.term pts Ψ pre (idx / ob.K) (idx % ob.K)

/-- The parts as `(index, number of anchor choices, weight)`. -/
def specs : List (ℕ × ℕ × ℤ) :=
  (List.range ob.parts.length).map fun i ↦
    (i, (ob.part i).1.choices.length, ((ob.part i).2 : ℤ))

/-- **The check of an obstruction leaf** on the family with map `Ψ`, box `b` of `n` slots and
views `V`, with the pre-rotation `pre`. -/
def check : Bool :=
  !ob.parts.isEmpty &&
    ob.parts.all (fun p ↦ decide (0 < p.2) && p.1.premisesOkV pts V ob.strong) &&
    (List.range ob.parts.length).all (fun i ↦
      (List.range (ob.part i).1.choices.length).all fun j ↦
        monoOk n b ((ob.exps.getD i []).getD j [])) &&
    Pull.check n (ob.terms pts Ψ pre) false ob.depth b (combTuples ob.K ob.specs)

/-- `check` as compiled code runs it (`check_eq_checkF`): the sign check of the combinations by
`Pull.checkComb`, once per tuple of representatives of the anchor choices with equal data. -/
def checkF : Bool :=
  !ob.parts.isEmpty &&
    ob.parts.all (fun p ↦ decide (0 < p.2) && p.1.premisesOkV pts V ob.strong) &&
    (List.range ob.parts.length).all (fun i ↦
      (List.range (ob.part i).1.choices.length).all fun j ↦
        monoOk n b ((ob.exps.getD i []).getD j [])) &&
    Pull.checkComb n (ob.terms pts Ψ pre) false ob.depth b ob.K (fun _ _ ↦ 1)
      (ob.specs.map fun p ↦ (p.1, List.range p.2.1, p.2.2))

@[csimp] theorem check_eq_checkF : @check = @checkF := by
  funext κ _ _ _ _ pts n Ψ b V ob pre
  rw [check, checkF, combTuples_eq_combL, Pull.check_combL]

variable {pts n Ψ b V ob pre}

theorem part_mem {i : ℕ} (hi : i < ob.parts.length) : ob.part i ∈ ob.parts := by
  rw [part, List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem le_K {i : ℕ} (hi : i < ob.parts.length) : (ob.part i).1.choices.length ≤ ob.K :=
  le_foldr_max (List.mem_map.mpr ⟨_, part_mem hi, rfl⟩)

theorem getD_terms {i j : ℕ} (hi : i < ob.parts.length) (hj : j < ob.K) :
    (ob.terms pts Ψ pre).getD (i * ob.K + j) default = ob.term pts Ψ pre i j := by
  have hK : 0 < ob.K := lt_of_le_of_lt (Nat.zero_le j) hj
  have hlt : i * ob.K + j < ob.parts.length * ob.K := by
    have : (i + 1) * ob.K ≤ ob.parts.length * ob.K := Nat.mul_le_mul_right _ hi
    rw [Nat.succ_mul] at this
    omega
  rw [terms, Box.getD_range_map _ _ _ hlt, Nat.add_comm, Nat.add_mul_div_right _ _ hK,
    Nat.div_eq_of_lt hj, zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

/-- **Soundness of obstruction leaves from the signs of their combinations**: `check_sound` with
the conclusion of a sign check of the combinations (`Pull.check_sound`, `Pull.checkX_sound`) for
its last test. -/
theorem sound_of_signs (hne : ob.parts ≠ [])
    (hparts : ∀ p ∈ ob.parts, 0 < p.2 ∧ p.1.premisesOkV pts V ob.strong = true)
    (hmono : ∀ i < ob.parts.length, ∀ j < (ob.part i).1.choices.length,
      monoOk n b ((ob.exps.getD i []).getD j []) = true) (hden : 0 < b.den)
    (hsig : ∀ τ ∈ combTuples ob.K ob.specs, ∀ x : Fin n → ℝ, b.Mem n x → ∃ c : ℝ, 0 < c ∧
      ∃ s : ℕ → ℝ, (∀ jw ∈ τ, ((ob.terms pts Ψ pre).getD jw.1 default).G.run Exact.re
          (ext n x) = c * DPoly.monoVal n ((ob.terms pts Ψ pre).getD jw.1 default).e x * s jw.1) ∧
        Sign false (τ.map fun jw ↦ (jw.2 : ℝ) * s jw.1).sum)
    (hpre : ∀ c ∈ Exact.rePre pre, c ≠ 0) {z : Fin n → ℝ} (hz : b.Mem n z) {r : ℝ}
    (hV : V.Mem (outU (Ψ.run Exact.re (ext n z))) r) (hs : ob.strong = true ∨ 0 < r)
    (hq : outQ (Ψ.run Exact.re (ext n z)) ≠ 0) :
    NoFitRep pts (Exact.rePre pre) (Ψ.run Exact.re (ext n z)) := by
  intro hfit
  -- A negative anchor choice of every part.
  have hneg : ∀ i, i < ob.parts.length → ∃ j, j < (ob.part i).1.choices.length ∧
      (((ob.part i).1.poly pts ((ob.part i).1.choices.getD j [])).pre pre).eval
        (Ψ.run Exact.re (ext n z)) < 0 := by
    intro i hi
    obtain ⟨-, hp⟩ := hparts _ (part_mem hi)
    obtain ⟨t, ht, hlt⟩ := Wit.exists_neg hq hpre (Wit.premises_of_okV hp hV hs) hfit
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
    exact ⟨j, hj, by rwa [List.getD_eq_getElem _ _ hj]⟩
  choose! g hg hgneg using hneg
  -- The tuple of the negative choices.
  set τ := ob.specs.map fun p ↦ (p.1 * ob.K + g p.1, p.2.2) with hτ
  have hmem : τ ∈ combTuples ob.K ob.specs := mem_combTuples _ g _ fun p hp ↦ by
    simp only [specs, List.mem_map, List.mem_range] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    exact hg i hi
  obtain ⟨c, hc, s, heq, hsign⟩ := hsig τ hmem z hz
  have hall : ∀ jw ∈ τ, 0 < jw.2 ∧ s jw.1 < 0 := by
    intro jw hjw
    simp only [hτ, specs, List.map_map, List.mem_map, List.mem_range, Function.comp] at hjw
    obtain ⟨i, hi, rfl⟩ := hjw
    have hgi := hg i hi
    have hgK := lt_of_lt_of_le hgi (le_K hi)
    refine ⟨show (0 : ℤ) < ((ob.part i).2 : ℤ) by exact_mod_cast (hparts _ (part_mem hi)).1, ?_⟩
    have he := heq _ (List.mem_map.mpr ⟨(i, (ob.part i).1.choices.length, ((ob.part i).2 : ℤ)),
      List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, rfl⟩)
    simp only [getD_terms hi hgK, term, PosePoly.comp_run] at he
    have hm := monoOk_sound (hmono i hi (g i) hgi) hden hz
    have hn := hgneg i hi
    rw [he] at hn
    by_contra hs0
    have : 0 ≤ c * DPoly.monoVal n ((ob.exps.getD i []).getD (g i) []) z * s (i * ob.K + g i) :=
      mul_nonneg (mul_nonneg hc.le hm) (le_of_not_gt hs0)
    linarith
  have hτne : τ ≠ [] := by
    simp only [hτ, specs, ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
    exact fun h0 ↦ hne (List.length_eq_zero_iff.mp h0)
  have hsum := sum_neg_of_forall τ hτne hall
  simp only [Sign, Bool.false_eq_true, ↓reduceIte] at hsign
  linarith

/-- **Soundness of obstruction leaves.** At a point of the box where the views hold (with a
positive blow-up parameter unless the premises are strong), the outputs have no fit with the
pre-rotation. -/
theorem check_sound (h : ob.check pts n Ψ b V pre = true) (hpre : ∀ c ∈ Exact.rePre pre, c ≠ 0)
    {z : Fin n → ℝ} (hz : b.Mem n z) {r : ℝ}
    (hV : V.Mem (outU (Ψ.run Exact.re (ext n z))) r) (hs : ob.strong = true ∨ 0 < r)
    (hq : outQ (Ψ.run Exact.re (ext n z)) ≠ 0) :
    NoFitRep pts (Exact.rePre pre) (Ψ.run Exact.re (ext n z)) := by
  simp only [check, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.isEmpty_eq_false_iff, List.all_eq_true, decide_eq_true_eq, List.mem_range] at h
  obtain ⟨⟨⟨hne, hparts⟩, hmono⟩, hcheck⟩ := h
  exact sound_of_signs hne hparts hmono (Pull.den_pos_of_check hcheck) (Pull.check_sound hcheck)
    hpre hz hV hs hq

end Obst

/-- **One term.** The conclusion of the sign checks (`Pull.check_sound`, the sparse
`Pull.checkX_sound`) for the one term `⟨G, e⟩` and the one tuple `[(0, 1)]`: at a point `z` of the
box, `G = c z^e s` with `c > 0` and `s` positive (`strict`) or nonnegative. -/
theorem single_of_check [ExactBasis κ] {n : ℕ} {G : GenPoly κ} {e : List ℕ} {strict : Bool}
    {b : Box}
    (h : ∀ τ ∈ ([[(0, 1)]] : List Tuple), ∀ x : Fin n → ℝ, b.Mem n x → ∃ c : ℝ, 0 < c ∧
      ∃ s : ℕ → ℝ,
      (∀ jw ∈ τ, (([⟨G, e⟩] : List (Term κ)).getD jw.1 default).G.run Exact.re (ext n x) =
        c * DPoly.monoVal n (([⟨G, e⟩] : List (Term κ)).getD jw.1 default).e x * s jw.1) ∧
      Sign strict (τ.map fun jw ↦ (jw.2 : ℝ) * s jw.1).sum) {z : Fin n → ℝ} (hz : b.Mem n z) :
    ∃ c : ℝ, 0 < c ∧ ∃ s : ℝ, G.run Exact.re (ext n z) = c * DPoly.monoVal n e z * s ∧
      Sign strict s := by
  obtain ⟨c, hc0, s, heq, hsign⟩ := h _ List.mem_cons_self z hz
  have he := heq (0, 1) List.mem_cons_self
  simp only [List.getD_cons_zero] at he
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Int.cast_one, one_mul,
    add_zero] at hsign
  exact ⟨c, hc0, s 0, he, hsign⟩

/-! ### Excluded leaves -/

/-- The improvement numerator as a pose polynomial. -/
def improvementP (d : Improvement κ) : PosePoly κ :=
  ⟨fun k U Q ↦ improvementG k d U Q, fun _ hf k U Q ↦ map_improvementG hf k d U Q⟩

/-- An excluded leaf: the symmetries `i` and `j` of the symmetry data, the exponent `e` of the
power of slot `0` that divides the improvement numerator, and the bisection depth. -/
structure ExclLeaf where
  /-- The first symmetry (acting on the view and from the left). -/
  i : ℕ
  /-- The second symmetry (acting on the inner copy). -/
  j : ℕ
  /-- The exponent of slot `0`. -/
  e : ℕ
  /-- The bisection depth of the sign check. -/
  depth : ℕ

namespace ExclLeaf

variable [ExactBasis κ]

/-- **The check of an excluded leaf** on the family with map `Ψ` and box `b` of `n` slots: the
improvement numerator divided by `x₀ ^ e` is positive on the box. -/
def check (D : SymmData κ) (n : ℕ) (Ψ : GenMap κ) (b : Box) (x : ExclLeaf) : Bool :=
  match D.syms[x.i]?, D.syms[x.j]? with
  | some S₁, some S₂ => decide (0 < n) &&
      Pull.check n [⟨(improvementP (Improvement.of D.score S₁ S₂)).comp Ψ, [x.e]⟩] true x.depth b
        [[(0, 1)]]
  | _, _ => false

/-- **Soundness of excluded leaves** from the sign of the leaf's term at a point `z` of the box
(by either sign check: `check_sound`, `checkAny_sound`), where slot `0` is positive. -/
theorem sound_of {pts : List (V3 κ)} {D : SymmData κ} {n : ℕ} {Ψ : GenMap κ} {x : ExclLeaf}
    {S₁ S₂ : Symm κ} (hD : D.ok pts = true) (hS₁ : D.syms[x.i]? = some S₁)
    (hS₂ : D.syms[x.j]? = some S₂) {z : Fin n → ℝ}
    (hc : ∃ c : ℝ, 0 < c ∧ ∃ s : ℝ,
      ((improvementP (Improvement.of D.score S₁ S₂)).comp Ψ).run Exact.re (ext n z) =
        c * DPoly.monoVal n [x.e] z * s ∧ Sign true s)
    (hz0 : 0 < ext n z 0) (hu : outU (Ψ.run Exact.re (ext n z)) ≠ 0)
    (hq : outQ (Ψ.run Exact.re (ext n z)) ≠ 0) : ExclRep pts D (Ψ.run Exact.re (ext n z)) := by
  simp only [SymmData.ok, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at hD
  have h₁ := hD.1 S₁ (List.mem_of_getElem? hS₁)
  have h₂ := hD.1 S₂ (List.mem_of_getElem? hS₂)
  obtain ⟨c, hc0, s, he, hsign⟩ := hc
  simp only [PosePoly.comp_run, PosePoly.eval, improvementP, improvementG_re, toFun_viewOf,
    toFun_quatOf] at he
  simp only [Sign, ↓reduceIte] at hsign
  have hpos : 0 < improvementPoly (Improvement.of D.score S₁ S₂)
      (outU (Ψ.run Exact.re (ext n z))) (outQ (Ψ.run Exact.re (ext n z))) := by
    rw [he]
    exact mul_pos (mul_pos hc0 (monoVal_single_pos x.e hz0)) hsign
  rw [improvementPoly_eq h₁ h₂ hD.2 hu hq] at hpos
  have hdot (v : Fin 3 → ℝ) : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _
  have hlt := pos_of_mul_pos_right hpos (mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
    (hdot _)) (hdot _)) (Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _))
  exact ⟨S₁.rot, S₁.sign, S₂.rot, S₂.sign, Symm.ok_sound h₁, Symm.ok_sound h₂,
    sub_pos.mp hlt⟩

/-- **Soundness of excluded leaves**, where slot `0` is positive. -/
theorem check_sound {pts : List (V3 κ)} {D : SymmData κ} {n : ℕ} {Ψ : GenMap κ} {b : Box}
    {x : ExclLeaf} (hD : D.ok pts = true) (h : x.check D n Ψ b = true) {z : Fin n → ℝ}
    (hz : b.Mem n z) (hz0 : 0 < ext n z 0) (hu : outU (Ψ.run Exact.re (ext n z)) ≠ 0)
    (hq : outQ (Ψ.run Exact.re (ext n z)) ≠ 0) : ExclRep pts D (Ψ.run Exact.re (ext n z)) := by
  unfold check at h
  split at h
  next S₁ S₂ hS₁ hS₂ =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact sound_of hD hS₁ hS₂ (single_of_check (Pull.check_sound h.2) hz) hz0 hu hq
  next => exact absurd h (by simp)

end ExclLeaf

/-! ### Outside leaves -/

/-- The outputs of the numerator and the denominator of chart coordinate `c` (`s`, `t`, `x₀`,
`x₁`, `x₂`) in the charts `(a, k)`. -/
def coordIdx (a : Fin 3) (k : Fin 4) : Fin 5 → ℕ × ℕ
  | ⟨0, _⟩ => ((a + 1 : Fin 3), a)
  | ⟨1, _⟩ => ((a + 2 : Fin 3), a)
  | ⟨2, _⟩ => ((k.succAbove 0 : Fin 4) + 3, k + 3)
  | ⟨3, _⟩ => ((k.succAbove 1 : Fin 4) + 3, k + 3)
  | ⟨_ + 4, _⟩ => ((k.succAbove 2 : Fin 4) + 3, k + 3)

theorem coordIdx_lt (a : Fin 3) (k : Fin 4) (c : Fin 5) :
    (coordIdx a k c).1 < 7 ∧ (coordIdx a k c).2 < 7 := by
  fin_cases c <;> simp only [coordIdx] <;> omega

/-- Chart coordinate `c` of the pose of the outputs `o`, in the charts `(a, k)`. -/
noncomputable def coordOf (a : Fin 3) (k : Fin 4) (c : Fin 5) (o : ℕ → ℝ) : ℝ :=
  o (coordIdx a k c).1 / o (coordIdx a k c).2

theorem chartQuat_succAbove_apply {R : Type*} [CommRing R] (k : Fin 4) (x : Fin 3 → R)
    (i : Fin 3) : chartQuat k x (k.succAbove i) = x i := by
  fin_cases k <;> fin_cases i <;> rfl

theorem coordOf_of_represents {p : ChartPose} {o : ℕ → ℝ} (h : Represents p o) (c : Fin 5) :
    coordOf p.view p.rot c o = p.coords c := by
  obtain ⟨a, b, ha, hb, hu, hq⟩ := h
  have hU (i : Fin 3) : o i = a * viewDir p.view p.s p.t i := congrFun hu i
  have hQ (i : Fin 4) : o (i + 3) = b * chartQuat p.rot p.x i := congrFun hq i
  fin_cases c <;> simp only [coordOf, coordIdx, hU, hQ, chartQuat_succAbove_apply,
    chartQuat_self, ChartPose.coords, viewDir, add_sub_cancel_left] <;>
    simp [ha, hb]

theorem coordOf_sim {a : Fin 3} {k : Fin 4} {c : Fin 5} {o o' : ℕ → ℝ} (h : PoseSim o o') :
    coordOf a k c o' = coordOf a k c o := by
  obtain ⟨α, β, hα, hβ, hu, hq⟩ := h
  have hU (i : Fin 3) : o' i = α * o i := congrFun hu i
  have hQ (i : Fin 4) : o' (i + 3) = β * o (i + 3) := congrFun hq i
  fin_cases c <;> simp only [coordOf, coordIdx, hU, hQ, mul_div_mul_left _ _ hα,
    mul_div_mul_left _ _ hβ]

/-- `(hd N - hn D) D` for the numerator `N` and the denominator `D` of chart coordinate `c`
(`upper`): positive where the coordinate exceeds `hn / hd`; or `(hn D - hd N) D`, positive where
it is below. -/
def outsideP [Exact κ] (a : Fin 3) (k : Fin 4) (c : Fin 5) (upper : Bool) (hn hd : ℤ) :
    PosePoly κ where
  run kk U Q :=
    (bif upper then
      kk (Exact.ofInt hd) * outOf U Q (coordIdx a k c).1 -
        kk (Exact.ofInt hn) * outOf U Q (coordIdx a k c).2
      else kk (Exact.ofInt hn) * outOf U Q (coordIdx a k c).2 -
        kk (Exact.ofInt hd) * outOf U Q (coordIdx a k c).1) *
      outOf U Q (coordIdx a k c).2
  natural f hf kk U Q := by
    have h1 := map_outOf f U Q (coordIdx a k c).1
    have h2 := map_outOf f U Q (coordIdx a k c).2
    cases upper <;> simp only [Bool.cond_true, Bool.cond_false, hf.map_mul, hf.map_sub, h1, h2,
      Function.comp_apply]

theorem lt_div_of_pos {N D hn hd : ℝ} (hd0 : 0 < hd) (h : 0 < (hd * N - hn * D) * D) :
    hn / hd < N / D := by
  have hD : D ≠ 0 := by rintro rfl; simp at h
  have key : N / D - hn / hd = (hd * N - hn * D) * D / (hd * (D * D)) := by
    field_simp
  have : 0 < N / D - hn / hd := by
    rw [key]
    exact div_pos h (mul_pos hd0 (mul_self_pos.mpr hD))
  linarith

theorem div_lt_of_pos {N D hn hd : ℝ} (hd0 : 0 < hd) (h : 0 < (hn * D - hd * N) * D) :
    N / D < hn / hd := by
  have hD : D ≠ 0 := by rintro rfl; simp at h
  have key : hn / hd - N / D = (hn * D - hd * N) * D / (hd * (D * D)) := by
    field_simp
  have : 0 < hn / hd - N / D := by
    rw [key]
    exact div_pos h (mul_pos hd0 (mul_self_pos.mpr hD))
  linarith

/-- An outside leaf: chart coordinate `coord` lies above the claim box (`upper`) or below it,
certified with the exponent `e` of the power of slot `0` and the bisection depth. -/
structure OutLeaf where
  /-- The chart coordinate. -/
  coord : Fin 5
  /-- Above the upper end, or below the lower end. -/
  upper : Bool
  /-- The exponent of slot `0`. -/
  e : ℕ
  /-- The bisection depth of the sign check. -/
  depth : ℕ

namespace OutLeaf

variable [ExactBasis κ]

/-- The numerator of the bound of the claim box `B`. -/
def bound (B : ChartBox) (x : OutLeaf) : ℤ :=
  bif x.upper then B.box.hi.getD x.coord 0 else B.box.lo.getD x.coord 0

/-- **The check of an outside leaf** on the family with map `Ψ` and box `b` of `n` slots, for the
claim box `B`. -/
def check (B : ChartBox) (n : ℕ) (Ψ : GenMap κ) (b : Box) (x : OutLeaf) : Bool :=
  decide (0 < n) && decide (0 < B.box.den) &&
    Pull.check n
      [⟨(outsideP B.view B.rot x.coord x.upper (x.bound B) B.box.den).comp Ψ, [x.e]⟩]
      true x.depth b [[(0, 1)]]

/-- **Soundness of outside leaves** from the sign of the leaf's term at a point `z` of the box (by
either sign check: `check_sound`, `checkAny_sound`). Where slot `0` is positive, the outputs
represent no pose of the claim box. -/
theorem sound_of {B : ChartBox} {n : ℕ} {Ψ : GenMap κ} {x : OutLeaf} (hden : 0 < B.box.den)
    {z : Fin n → ℝ}
    (hc : ∃ c : ℝ, 0 < c ∧ ∃ s : ℝ,
      ((outsideP B.view B.rot x.coord x.upper (x.bound B) B.box.den).comp Ψ).run Exact.re
        (ext n z) = c * DPoly.monoVal n [x.e] z * s ∧ Sign true s)
    (hz0 : 0 < ext n z 0) {p : ChartPose} (hp : p ∈ B.poses)
    (hrep : Represents p (Ψ.run Exact.re (ext n z))) : False := by
  obtain ⟨c, hc0, s, he, hsign⟩ := hc
  simp only [PosePoly.comp_run] at he
  simp only [Sign, ↓reduceIte] at hsign
  have hpos : 0 < (outsideP (κ := κ) B.view B.rot x.coord x.upper (x.bound B) B.box.den).eval
      (Ψ.run Exact.re (ext n z)) := by
    rw [he]
    exact mul_pos (mul_pos hc0 (monoVal_single_pos x.e hz0)) hsign
  obtain ⟨hview, hrot, hy⟩ := hp
  have hco := coordOf_of_represents hrep x.coord
  rw [hview, hrot] at hco
  have hd : (0 : ℝ) < B.box.den := by exact_mod_cast hden
  obtain ⟨h1, h2⟩ := coordIdx_lt B.view B.rot x.coord
  have hyc := hy x.coord
  simp only [PosePoly.eval, outsideP, outOf_of h1, outOf_of h2, Exact.re_ofInt] at hpos
  cases hup : x.upper <;> simp only [hup, Bool.cond_true, Bool.cond_false, bound] at hpos <;>
    push_cast at hpos
  · have h3 : coordOf B.view B.rot x.coord (Ψ.run Exact.re (ext n z)) <
        (B.box.lo.getD x.coord 0 : ℝ) / B.box.den := div_lt_of_pos hd hpos
    rw [hco] at h3
    linarith [hyc.1]
  · have h3 : (B.box.hi.getD x.coord 0 : ℝ) / B.box.den <
        coordOf B.view B.rot x.coord (Ψ.run Exact.re (ext n z)) := lt_div_of_pos hd hpos
    rw [hco] at h3
    linarith [hyc.2]

/-- **Soundness of outside leaves.** Where slot `0` is positive, the outputs represent no pose of
the claim box. -/
theorem check_sound {B : ChartBox} {n : ℕ} {Ψ : GenMap κ} {b : Box} {x : OutLeaf}
    (h : x.check B n Ψ b = true) {z : Fin n → ℝ} (hz : b.Mem n z) (hz0 : 0 < ext n z 0)
    {p : ChartPose} (hp : p ∈ B.poses) (hrep : Represents p (Ψ.run Exact.re (ext n z))) :
    False := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨-, hden⟩, hc⟩ := h
  exact sound_of hden (single_of_check (Pull.check_sound hc) hz) hz0 hp hrep

end OutLeaf

/-! ### Views of leaves -/

theorem AlongPoly.const_mul {n : ℕ} {f : (Fin n → ℝ) → ℝ} {i : Fin n} {m : ℕ} (c : ℝ)
    (hf : AlongPoly f i m) : AlongPoly (fun x ↦ c * f x) i m := fun y ↦ by
  obtain ⟨p, hp, hfp⟩ := hf y
  refine ⟨Polynomial.C c * p, fun a ha ↦ hp a ?_, fun x ↦ by simp [hfp]⟩
  rw [Polynomial.coeff_C_mul] at ha
  exact right_ne_zero_of_mul ha

theorem length_le_of_mem_vertices : ∀ (lo hi : List ℤ) (act : List Bool) (L : List ℤ),
    L ∈ vertices lo hi act → L.length ≤ lo.length
  | l :: ls, h :: hs, a :: as, L, hL => by
    simp only [vertices, List.mem_append, List.mem_map] at hL
    rcases hL with ⟨L', hL', rfl⟩ | hL
    · simpa using length_le_of_mem_vertices ls hs as L' hL'
    · split_ifs at hL
      · obtain ⟨L', hL', rfl⟩ := List.mem_map.mp hL
        simpa using length_le_of_mem_vertices ls hs as L' hL'
      · simp at hL
  | [], _, _, L, hL => by
    simp only [vertices, List.mem_singleton] at hL
    simp [hL]
  | _ :: _, [], _, L, hL => by
    simp only [vertices, List.mem_singleton] at hL
    simp [hL]
  | _ :: _, _ :: _, [], L, hL => by
    simp only [vertices, List.mem_singleton] at hL
    simp [hL]

section Hull

variable [ExactBasis κ]

theorem GenPoly.run_div (G : GenPoly κ) {D : ℤ} (hD : (D : ℝ) ≠ 0) (L : ℕ → ℤ) :
    G.run Exact.re (fun i ↦ (L i : ℝ) / D) =
      Exact.re (G.runFV id (Exact.ofInt D) (Exact.ofInt ∘ L)).val / (D : ℝ) ^ G.expo := by
  have hD' : Exact.re (Exact.ofInt D : κ) ≠ 0 := by rwa [Exact.re_ofInt]
  have h1 := G.map_runFV Exact.isArith id (Exact.ofInt D) (Exact.ofInt ∘ L)
  have h2 := G.toVal_runFV hD' (Exact.re ∘ (Exact.ofInt : ℤ → κ) ∘ L)
  have h3 := congrArg FV.toVal h1
  simp only [Function.comp_id] at h3
  have hx : (fun i ↦ (L i : ℝ) / D) =
      fun i ↦ (Exact.re ∘ (Exact.ofInt : ℤ → κ) ∘ L) i / Exact.re (Exact.ofInt D : κ) := by
    funext i
    simp [Exact.re_ofInt]
  rw [hx, ← h2, ← h3, FV.toVal, FV.map_val, FV.map_exp, G.exp_runFV, Exact.re_ofInt]

/-- The masks of slots `0, …, n - 1` in the view outputs `0, 1, 2` of `Ψ`, united. -/
def viewProf (Ψ : GenMap κ) (n : ℕ) : List ℕ :=
  (List.range n).map fun i ↦
    ((Ψ.out 0).prof n).m.getD i 0 ||| ((Ψ.out 1).prof n).m.getD i 0 |||
      ((Ψ.out 2).prof n).m.getD i 0

/-- The exponent of the common denominator of the view outputs at integer points. -/
def viewExpo (Ψ : GenMap κ) : ℕ :=
  max (Ψ.out 0).expo (max (Ψ.out 1).expo (Ψ.out 2).expo)

/-- The numerator of output `j` of `Ψ` at the point `L / d`, over `d ^ E`, computed in `κ`. -/
def outNum (Ψ : GenMap κ) (j : ℕ) (d : ℤ) (E : ℕ) (L : List ℤ) : κ :=
  ((Ψ.out j).runFV id (Exact.ofInt d) (fun i ↦ Exact.ofInt (L.getD i 0))).val *
    Exact.ofInt (d ^ (E - (Ψ.out j).expo))

/-- The slots that the views need at both ends. -/
def viewAct (Ψ : GenMap κ) (n : ℕ) (b : Box) : List Bool :=
  (List.range n).map fun i ↦ slotAct ((viewProf Ψ n).getD i 0) (b.lo.getD i 0) (b.hi.getD i 0)

/-- **The hull points of the views of a leaf**: the images of the vertices of the box `b` (of
`n` slots) under the view outputs of `Ψ`, over a common power of the denominator, when every slot
enters the views with a single exponent, monotone on its range (`slotOk`; `view_points` in
`wzoom.rs`). -/
def hullPts (Ψ : GenMap κ) (n : ℕ) (b : Box) : Option (List (V3 κ)) :=
  if (List.range n).all fun i ↦
      slotOk ((viewProf Ψ n).getD i 0) (b.lo.getD i 0) (b.hi.getD i 0) then
    some ((boxVertices n b.lo b.hi (viewAct Ψ n b)).map fun L ↦
      ⟨outNum Ψ 0 b.den (viewExpo Ψ) L, outNum Ψ 1 b.den (viewExpo Ψ) L,
        outNum Ψ 2 b.den (viewExpo Ψ) L⟩)
  else none

theorem outNum_div {Ψ : GenMap κ} {j : ℕ} {d : ℕ} (hd : 0 < d) {E : ℕ}
    (hE : (Ψ.out j).expo ≤ E) (L : List ℤ) :
    ((d : ℝ) ^ E)⁻¹ * Exact.re (outNum Ψ j d E L) =
      Ψ.run Exact.re (fun i ↦ (L.getD i 0 : ℝ) / d) j := by
  have hd' : ((d : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have h := (Ψ.out j).run_div hd' (L.getD · 0)
  change _ = (Ψ.out j).run Exact.re _
  push_cast at h ⊢
  rw [h, outNum, Exact.re_mul, Exact.re_ofInt]
  push_cast
  have hpow : (d : ℝ) ^ E = (d : ℝ) ^ (E - (Ψ.out j).expo) * (d : ℝ) ^ (Ψ.out j).expo := by
    rw [← pow_add, Nat.sub_add_cancel hE]
  have h1 : (d : ℝ) ^ (Ψ.out j).expo ≠ 0 := pow_ne_zero _ (by exact_mod_cast hd.ne')
  have h2 : (d : ℝ) ^ (E - (Ψ.out j).expo) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hd.ne')
  rw [hpow]
  field_simp
  rfl

/-- **The hull points bound the views** at every point of the box. -/
theorem coneBound_hullPts {Ψ : GenMap κ} {n : ℕ} {b : Box} {us : List (V3 κ)}
    (h : hullPts Ψ n b = some us) (hden : 0 < b.den) {z : Fin n → ℝ} (hz : b.Mem n z) :
    ConeBound us (outU (Ψ.run Exact.re (ext n z))) := by
  unfold hullPts at h
  split_ifs at h with hok
  simp only [Option.some.injEq] at h
  subst h
  have hd : (0 : ℝ) < b.den := by exact_mod_cast hden
  refine ⟨((b.den : ℝ) ^ viewExpo Ψ)⁻¹, by positivity, fun g ↦ ?_⟩
  -- The functional `g` of the views, as a function of the slots.
  set f : (Fin n → ℝ) → ℝ := fun x ↦ g 0 * Ψ.run Exact.re (ext n x) 0 +
    g 1 * Ψ.run Exact.re (ext n x) 1 + g 2 * Ψ.run Exact.re (ext n x) 2 with hf
  have hfu (x : Fin n → ℝ) : f x = g ⬝ᵥ outU (Ψ.run Exact.re (ext n x)) := by
    simp only [hf, dotProduct, Fin.sum_univ_three, outU]
    rfl
  have hmin : ∀ i : Fin n, CoordMin f ((b.lo.getD i 0 : ℝ) / b.den)
      ((b.hi.getD i 0 : ℝ) / b.den) i ((viewAct Ψ n b).getD i false) := by
    intro i
    rw [viewAct, Box.getD_range_map n _ _ i.2]
    refine coordMin_of_slotOk hden (List.all_eq_true.mp hok i (List.mem_range.mpr i.2)) ?_
    rw [viewProf, Box.getD_range_map n _ _ i.2]
    exact ((((Ψ.out 0).alongPoly_prof n i).const_mul (g 0)).add
      (((Ψ.out 1).alongPoly_prof n i).const_mul (g 1))).add
        (((Ψ.out 2).alongPoly_prof n i).const_mul (g 2))
  obtain ⟨L, hL, hle⟩ := exists_boxVertex_le f b.lo b.hi _ hmin z fun i ↦ hz i
  refine ⟨_, List.mem_map.mpr ⟨L, hL, rfl⟩, ?_⟩
  rw [← hfu]
  refine le_trans (le_of_eq ?_) hle
  -- The value at the vertex.
  have hlen := length_le_of_mem_vertices _ _ _ L hL
  simp only [List.length_map, List.length_range] at hlen
  have hext : ext n (fun i : Fin n ↦ (L.getD i 0 : ℝ) / b.den) =
      fun i ↦ (L.getD i 0 : ℝ) / b.den := by
    funext i
    by_cases hi : i < n
    · simp [Pull.ext, hi]
    · simp only [Pull.ext, hi, ↓reduceDIte]
      rw [List.getD_eq_default _ _ (by omega)]
      simp
  have hE0 : (Ψ.out 0).expo ≤ viewExpo Ψ := le_max_left _ _
  have hE1 : (Ψ.out 1).expo ≤ viewExpo Ψ := (le_max_left _ _).trans (le_max_right _ _)
  have hE2 : (Ψ.out 2).expo ≤ viewExpo Ψ := (le_max_right _ _).trans (le_max_right _ _)
  simp only [hf, hext, ← outNum_div hden hE0 L, ← outNum_div hden hE1 L, ← outNum_div hden hE2 L,
    dotProduct, Fin.sum_univ_three, Exact.reV, V3.map, V3.toFun]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

/-- `hullPts` for compiled checks: one profile run, and one run of `Ψ` per vertex for the three
views (`GenMap.all`), instead of runs per slot, view and vertex. -/
def hullPtsW (Ψ : GenMap κ) (n : ℕ) (b : Box) : Option (List (V3 κ)) :=
  let pr := look (Ψ.all (Prof.const n) (Prof.var n)) (Ψ.run (Prof.const n) (Prof.var n))
  let prof := (List.range n).map fun i ↦
    (pr 0).m.getD i 0 ||| (pr 1).m.getD i 0 ||| (pr 2).m.getD i 0
  if (List.range n).all fun i ↦ slotOk (prof.getD i 0) (b.lo.getD i 0) (b.hi.getD i 0) then
    let e0 := (Ψ.out 0).expo
    let e1 := (Ψ.out 1).expo
    let e2 := (Ψ.out 2).expo
    let E := max e0 (max e1 e2)
    let act := (List.range n).map fun i ↦
      slotAct (prof.getD i 0) (b.lo.getD i 0) (b.hi.getD i 0)
    some ((boxVertices n b.lo b.hi act).map fun L ↦
      let x : ℕ → FV (Exact.ofInt b.den : κ) := fun i ↦ ⟨Exact.ofInt (L.getD i 0), 1⟩
      let r := look (Ψ.all (FV.const id) x) (Ψ.run (FV.const id) x)
      ⟨(r 0).val * Exact.ofInt ((b.den : ℤ) ^ (E - e0)),
        (r 1).val * Exact.ofInt ((b.den : ℤ) ^ (E - e1)),
        (r 2).val * Exact.ofInt ((b.den : ℤ) ^ (E - e2))⟩)
  else none

@[csimp] theorem hullPts_eq_hullPtsW : @hullPts = @hullPtsW := by
  funext κ _ _ _ _ Ψ n b
  simp only [hullPts, hullPtsW, GenMap.look_all, viewAct, viewProf, viewExpo, outNum]
  rfl

end Hull

end Check

end Nieuwland
