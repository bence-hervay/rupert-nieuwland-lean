import Modules.Nieuwland.Weak
import Modules.Root.System

/-!
# The weak fit at a root

At the zero of a root's system (`Modules/Root/System.lean`) the plug at the root's scale `l`
touches the hole: the weak-fit record of a D2 certificate (`code/src/proof/d2/`, "Weak fit")
shows that every plug vertex is weakly inside every edge of a cycle of hole vertices. Here:

* `WeakRec`: the cycle, a rational point strictly inside it (the witness of
  `Modules/Nieuwland/Weak.lean`), the checker's duplicates and coincidences.
* `IdRec`: an identity `D g = ∑ p_i g_i` of the slack `g` of a contact outside the system with
  the system's slacks: a coincidence of the checker, or a duplicate (a contact whose slack is a
  constant multiple of a slack of the system; in centred mode the antipodal contacts). The
  identities are checked over the field in `Modules/Root/Identity.lean`.
* `Sys.weakOk`: for every edge of the cycle the witness is strictly inside (a ball sign at the
  zero's enclosure), and every plug vertex has a slack that is a contact of the system (zero at
  the zero), one of the given contacts `zs` (zero at the zero by a checked identity), or
  negative on the zero's enclosure.
* `Sys.fitsThrough_of_weakOk`: then every smaller scale passes strictly (scaling the plug down
  about the witness), and `Sys.le_nieuwland_of_weakOk`: `l ≤ nieuwland P`.

The cycle need not be the hull of the hole's shadow: the plug is inside the cycle's polygon,
which lies in the shadow. Both modes: the translation of the zero is `0` in centred mode.
-/

open Nieuwland.Check Matrix

namespace Nieuwland

namespace Root

/-- `H` times the orientation of the point `(h₀ / H, h₁ / H)` against the hole edge
`va → vb`. -/
def witE (a : Fin 3) (V : ℕ → Fin 3 → Expr) (va vb : ℕ) (h₀ h₁ : ℤ) (H : ℕ) : Expr :=
  let A := screenE a (V va)
  let B := screenE a (V vb)
  (B 0 - A 0) * (.const h₁ - .const H * A 1) - (B 1 - A 1) * (.const h₀ - .const H * A 0)

theorem eval_witE (z : ℕ → ℝ) (a : Fin 3) (k : Fin 4) (V : ℕ → Fin 3 → Expr) (va vb : ℕ)
    (h₀ h₁ : ℤ) {H : ℕ} (hH : 0 < H) :
    (witE a V va vb h₀ h₁ H).eval z =
      H * orient ((poseOf z a k).screen (vertOf z V va)) ((poseOf z a k).screen (vertOf z V vb))
        ![(h₀ : ℝ) / H, (h₁ : ℝ) / H] := by
  have hH' : (H : ℝ) ≠ 0 := by positivity
  have hv : ∀ v, (fun i ↦ (V v i).eval z) = vertOf z V v := fun _ ↦ rfl
  simp only [witE, Expr.eval_sub, Expr.eval_mul, Expr.eval_const, eval_screenE, orient,
    Matrix.cons_val_zero, Matrix.cons_val_one, hv, ChartPose.screen, poseOf, Int.cast_natCast]
  field_simp

/-- An identity `D g = ∑ p_i g_i` between the slack `g` of the contact `con` and the slacks `g_i`
of a system's contacts, as expressions in the system's variables (module docs). -/
structure IdRec where
  /-- The contact `(a, b, k)`, outside the system. -/
  con : ℕ × ℕ × ℕ
  /-- The multiplier `D` of its slack, of one sign at the zero. -/
  D : Expr
  /-- The cofactors `p_i`, one per contact of the system (missing ones are `0`). -/
  p : List Expr

/-- A weak fit at the zero of a root's system (module docs). -/
structure WeakRec where
  /-- Hole vertices: a cycle around the plug's shadow. -/
  cycle : List ℕ
  /-- The numerator of the witness's first coordinate. -/
  h₀ : ℤ
  /-- The numerator of the witness's second coordinate. -/
  h₁ : ℤ
  /-- The denominator of the witness, positive. -/
  H : ℕ
  /-- Duplicates `(contact, of)`: the slack of `contact`, outside the system, is a constant
  multiple of the slack of the system's contact `of`. -/
  dups : List ((ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ))
  /-- Coincidences: identities of contacts outside the system. -/
  ids : List IdRec

namespace WeakRec

variable (W : WeakRec)

/-- The tail of the edge `i` of the cycle. -/
def a (i : ℕ) : ℕ := W.cycle.getD i 0

/-- The head of the edge `i` of the cycle. -/
def b (i : ℕ) : ℕ := W.cycle.getD ((i + 1) % W.cycle.length) 0

end WeakRec

namespace Sys

variable {S : Sys} {K : Kraw}

/-- The slack of a contact of the system vanishes at a zero. -/
theorem slack_zero_of_mem (hK : K.eqs = S.eqs) {p : ℕ → ℝ} {y : Fin K.n → ℝ}
    (h0 : K.F p y = 0) {c : ℕ × ℕ × ℕ} (hc : c ∈ S.contacts) :
    (S.slack c).eval (K.env p y) = 0 := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  have h := S.g_zero hK h0 (i := i) hi
  simpa [Sys.g, Sys.con, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using h

/-- The check of a weak fit at the zero, on the balls `Z` of the variables there, for a solid of
`nV` vertices; `zs` are contacts whose slacks vanish at the zero (module docs). -/
def weakOk (S : Sys) (nV : ℕ) (Z : List Ball) (W : WeakRec) (zs : List (ℕ × ℕ × ℕ)) : Bool :=
  let Y := Kraw.zball Z
  decide (0 < W.H) && decide (0 < W.cycle.length) &&
  (List.range W.cycle.length).all fun i ↦
    decide (W.a i < nV) &&
    (bval Y (witE S.view S.V (W.a i) (W.b i) W.h₀ W.h₁ W.H)).isPos &&
    (List.range nV).all fun v ↦
      S.contacts.contains (W.a i, W.b i, v) || zs.contains (W.a i, W.b i, v) ||
      (bval Y (S.slack (W.a i, W.b i, v))).isNeg

/-- **Soundness of the weak fit at a root**: every scale `0 ≤ c < l` passes strictly through. -/
theorem fitsThrough_of_weakOk (hK : K.eqs = S.eqs) {p : ℕ → ℝ} (hp : K.ParOk p)
    {y : Fin K.n → ℝ} (hy : y ∈ K.box) (h0 : K.F p y = 0)
    {P : Polyhedron} {nV : ℕ}
    (hV : ∀ x, x ∈ P.vertices ↔ ∃ v < nV, vertOf (K.env p y) S.V v = x) {W : WeakRec}
    {zs : List (ℕ × ℕ × ℕ)} (hzs : ∀ c ∈ zs, (S.slack c).eval (K.env p y) = 0)
    (hW : S.weakOk nV K.zballs W zs = true) :
    ∀ c, 0 ≤ c → c < (lE S.cen).eval (K.env p y) → (P.smul c).FitsThrough P := by
  intro c hc hlt
  have hY : ∀ i, (Kraw.zball K.zballs i).Encl (K.env p y i) := K.encl_zballs hp hy h0
  simp only [weakOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    Bool.or_eq_true] at hW
  obtain ⟨⟨hH, hm⟩, hall⟩ := hW
  have hzero : ∀ c ∈ S.contacts, (S.slack c).eval (K.env p y) = 0 :=
    fun c hc ↦ slack_zero_of_mem hK h0 hc
  generalize hz : K.env p y = z at *
  generalize hl : (lE S.cen).eval z = l at *
  have hl0 : 0 < l := hc.trans_lt hlt
  have ht0 : 0 ≤ c / l := div_nonneg hc hl0.le
  have ht1 : 0 < 1 - c / l := by rw [sub_pos, div_lt_one hl0]; exact hlt
  have hd := quat_pos S.rot ![z 2, z 3, z 4]
  have hn : W.cycle.length - 1 + 1 = W.cycle.length := by omega
  refine Polyhedron.fitsThrough_of_surjective _ _
    (screenₗ (poseOf z S.view S.rot).view (poseOf z S.view S.rot).s (poseOf z S.view S.rot).t)
    (screen_surjective _ _ _) (poseOf z S.view S.rot).rotation_mem
    ((c / l) • yOf z S.cen + (1 - c / l) • ![(W.h₀ : ℝ) / W.H, (W.h₁ : ℝ) / W.H]) fun x hx ↦ ?_
  obtain ⟨w, hw, rfl⟩ := Polyhedron.mem_smul_vertices.mp hx
  obtain ⟨v, hv, rfl⟩ := (hV w).mp hw
  have key : ∀ i : Fin (W.cycle.length - 1 + 1),
      0 < orient ((poseOf z S.view S.rot).screen (vertOf z S.V (W.cycle.getD i 0)))
        ((poseOf z S.view S.rot).screen (vertOf z S.V (W.cycle.getD ↑(i + 1) 0)))
        ((poseOf z S.view S.rot).screen
            ((poseOf z S.view S.rot).rotation *ᵥ (c • vertOf z S.V v)) +
          ((c / l) • yOf z S.cen + (1 - c / l) • ![(W.h₀ : ℝ) / W.H, (W.h₁ : ℝ) / W.H])) := by
    intro i
    have hi : ((i + 1 : Fin (W.cycle.length - 1 + 1)) : ℕ) = (i.val + 1) % W.cycle.length := by
      rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
      exact congrArg _ hn
    obtain ⟨⟨-, hwit⟩, hvs⟩ := hall i (by omega)
    have hpt : (poseOf z S.view S.rot).screen
          ((poseOf z S.view S.rot).rotation *ᵥ (c • vertOf z S.V v)) +
          ((c / l) • yOf z S.cen + (1 - c / l) • ![(W.h₀ : ℝ) / W.H, (W.h₁ : ℝ) / W.H]) =
        (c / l) • (l • (poseOf z S.view S.rot).screen
          ((poseOf z S.view S.rot).rotation *ᵥ vertOf z S.V v) + yOf z S.cen) +
          (1 - c / l) • ![(W.h₀ : ℝ) / W.H, (W.h₁ : ℝ) / W.H] := by
      rw [Matrix.mulVec_smul, FitData.screen_smul, smul_add, smul_smul, div_mul_cancel₀ c hl0.ne',
        add_assoc]
    rw [hpt, orient_add_smul, hi]
    refine add_pos_of_nonneg_of_pos (mul_nonneg ht0 ?_) (mul_pos ht1 ?_)
    · have hs : (S.slack (W.a i, W.b i, v)).eval z ≤ 0 := by
        rcases hvs v hv with (hA | hZ) | hC
        · exact (hzero _ (by simpa using hA)).le
        · exact (hzs _ (by simpa using hZ)).le
        · exact (Ball.neg_sound (encl_bval hY _) hC).le
      rw [Sys.slack, eval_slackE, hl] at hs
      exact (mul_nonneg_iff_of_pos_left hd).mp (neg_nonpos.mp hs)
    · have h1 := Ball.pos_sound (encl_bval hY _) hwit
      rw [eval_witE z S.view S.rot _ _ _ _ _ hH] at h1
      exact (mul_pos_iff_of_pos_left (by exact_mod_cast hH)).mp h1
  refine interior_mono (convexHull_mono ?_) (mem_interior_convexHull_of_forall_orient_pos
    (w := fun i : Fin (W.cycle.length - 1 + 1) ↦
      (poseOf z S.view S.rot).screen (vertOf z S.V (W.cycle.getD i 0))) key)
  rintro _ ⟨i, rfl⟩
  exact ⟨_, (hV _).mpr ⟨_, (hall i (by omega)).1.1, rfl⟩, rfl⟩

/-- **A weak fit at a root bounds the Nieuwland number**: `l ≤ nieuwland P`. -/
theorem le_nieuwland_of_weakOk (hK : K.eqs = S.eqs) {p : ℕ → ℝ} (hp : K.ParOk p)
    {y : Fin K.n → ℝ} (hy : y ∈ K.box) (h0 : K.F p y = 0)
    {P : Polyhedron} {nV : ℕ}
    (hV : ∀ x, x ∈ P.vertices ↔ ∃ v < nV, vertOf (K.env p y) S.V v = x) {W : WeakRec}
    {zs : List (ℕ × ℕ × ℕ)} (hzs : ∀ c ∈ zs, (S.slack c).eval (K.env p y) = 0)
    (hW : S.weakOk nV K.zballs W zs = true) (hdim : P.FullDim) :
    (lE S.cen).eval (K.env p y) ≤ P.nieuwland :=
  Polyhedron.le_nieuwland_of_forall_lt hdim fun c hc hlt ↦
    fitsThrough_of_weakOk hK hp hy h0 hV hzs hW c hc.le hlt

end Sys

end Root

end Nieuwland
