import Modules.Certificate.Whole
import Modules.Nieuwland.Bound

/-!
# Settled poses at a plug scale

The global layer of scaled certificates (`notes/nieuwland-lean.md`; Lemma G of
`code/src/proof/scale.rs`). A certificate at the plug scale `Θ` settles every pose `p` of the
twelve unit chart boxes: the plug `Θ P` has no fit along the view of `p` with the rotation of `p`
(`¬ P.FitsAlong u (Θ • R)`), or `p` is excluded by the symmetry data, or `p` lies in the null set
of its score (`SettledS`, the counterpart of `Settled`). Then `P` scaled by `Θ` does not fit
through `P` (`Polyhedron.not_fitsThrough_smul_of_settled`, from
`Polyhedron.not_fitsThrough_smul_of_excluded_off`), and `nieuwland P ≤ Θ`.

Every leaf states its own scale `θ_c` (`Scale`: `ν / d` with `ν` an exact value and `d > 0` a
natural number), and a NoFit leaf at `θ_c` settles its poses at every `Θ ≥ θ_c ≥ 0`: a fit of
`Θ R P` gives one of `θ_c R P` (`FitsAlong.smul_of_le`, Lemma M). `Scale.le` is the exact test of
`θ_c ≤ Θ`; `Scale.ok` that of `0 ≤ θ_c` with `d > 0`.
-/

open Matrix

namespace Nieuwland.Check

/-- A plug scale `num / den`: an exact value over a natural number (`ScaleSpec` in
`code/src/proof/scale.rs`, over the field of the points). -/
structure Scale (κ : Type) where
  /-- The numerator. -/
  num : κ
  /-- The denominator. -/
  den : ℕ

namespace Scale

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The real value `re num / den`. -/
noncomputable def re (s : Scale κ) : ℝ :=
  Exact.re s.num / s.den

/-- The scale `1`. -/
def one : Scale κ := ⟨Exact.ofInt 1, 1⟩

theorem re_one : (one : Scale κ).re = 1 := by
  simp [re, one, Exact.re_ofInt]

/-- The check of a scale: a positive denominator and a nonnegative numerator. -/
def ok (s : Scale κ) : Bool :=
  decide (0 < s.den) && Exact.nonneg s.num

theorem den_pos_of_ok {s : Scale κ} (h : s.ok = true) : 0 < s.den := by
  simp only [ok, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem re_nonneg_of_ok {s : Scale κ} (h : s.ok = true) : 0 ≤ s.re := by
  simp only [ok, Bool.and_eq_true, decide_eq_true_eq] at h
  exact div_nonneg (Exact.nonneg_sound _ h.2) (Nat.cast_nonneg _)

/-- The exact test of `s ≤ t`: `t.den s.num ≤ s.den t.num`. -/
def le (s t : Scale κ) : Bool :=
  decide (0 < s.den) && decide (0 < t.den) &&
    Exact.nonneg (Exact.ofInt s.den * t.num - Exact.ofInt t.den * s.num)

theorem re_le_of_le {s t : Scale κ} (h : s.le t = true) : s.re ≤ t.re := by
  simp only [le, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hs, ht⟩, h⟩ := h
  have h0 := Exact.nonneg_sound _ h
  rw [Exact.re_sub, Exact.re_mul, Exact.re_mul, Exact.re_ofInt, Exact.re_ofInt] at h0
  have hs' : (0 : ℝ) < s.den := by exact_mod_cast hs
  have ht' : (0 : ℝ) < t.den := by exact_mod_cast ht
  push_cast at h0
  rw [re, re, div_le_div_iff₀ hs' ht']
  linarith

end Scale

/-! ### Monotonicity -/

/-- **Lemma M for leaves.** No fit of `θ R P` on `S` gives no fit of `Θ R P` for `Θ ≥ θ ≥ 0`. -/
theorem Polyhedron.NoFitRot.smul_of_le {P : Polyhedron} {S : Set ChartPose}
    {M : Matrix (Fin 3) (Fin 3) ℝ} {θ Θ : ℝ} (h : P.NoFitRot S (θ • M)) (hθ : 0 ≤ θ)
    (hle : θ ≤ Θ) : P.NoFitRot S (Θ • M) := by
  intro p hp hfit
  rw [Matrix.mul_smul] at hfit
  exact h p hp (by rw [Matrix.mul_smul]; exact hfit.smul_of_le hθ hle)

/-! ### Settled poses -/

section Settled

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- At the pose `p`, the polyhedron of `pts` scaled by `Θ` has no fit, `p` is excluded by the
symmetry data `D`, or `p` lies in the null set of the score of `D`: `Settled` at the plug scale
`Θ`. -/
def SettledS (pts : List (V3 κ)) (D : SymmData κ) (Θ : ℝ) (p : ChartPose) : Prop :=
  ¬ (Polyhedron.ofPoints pts).FitsAlong (viewDir p.view p.s p.t) (Θ • p.rotation) ∨
    (Polyhedron.ofPoints pts).Excluded D.centre D.score.f p ∨ p.pose ∈ null κ D.score

/-- No fit at `Θ` on a set settles its poses. -/
theorem settledS_of_noFitRot {pts : List (V3 κ)} {D : SymmData κ} {Θ : ℝ} {S : Set ChartPose}
    (h : (Polyhedron.ofPoints pts).NoFitRot S (Θ • 1)) : ∀ p ∈ S, SettledS pts D Θ p := by
  intro p hp
  have h0 := h p hp
  rw [Matrix.mul_smul, Matrix.mul_one] at h0
  exact Or.inl h0

/-- Excluded poses are settled. -/
theorem settledS_of_excluded {pts : List (V3 κ)} {D : SymmData κ} {Θ : ℝ} {p : ChartPose}
    (h : (Polyhedron.ofPoints pts).Excluded D.centre D.score.f p) : SettledS pts D Θ p :=
  Or.inr (Or.inl h)

/-- **Scaled certificates decide the bound.** If the points span space and every pose of the
twelve unit chart boxes is settled at `Θ`, the polyhedron of `pts` scaled by `Θ` does not fit
through it. -/
theorem Polyhedron.not_fitsThrough_smul_of_settled [Countable κ] {pts : List (V3 κ)}
    {D : SymmData κ} {i j k l : ℕ} (hspan : spanOk pts i j k l = true) {Θ : ℝ}
    (h : ∀ a k, ∀ p ∈ (ChartBox.unit a k).poses, SettledS pts D Θ p) :
    ¬ ((Polyhedron.ofPoints pts).smul Θ).FitsThrough (Polyhedron.ofPoints pts) :=
  Polyhedron.not_fitsThrough_smul_of_excluded_off (spanOk_sound hspan D.centre) D.score.f
    (fun _ u R ha ↦ orbitScore_smul _ _ _ ha u R) (isMeagre_null κ D.score)
    (fun a u R ha hN ↦ null_smul D.score a u R ha hN) fun p hp ↦
      h p.view p.rot p (ChartBox.mem_unit_poses hp)

end Settled

section Roots

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- **Whole scaled certificates.** If the points span space, every unit chart box lies in one of
the boxes `roots`, and every pose of every root is settled at `Θ`, the polyhedron of `pts` scaled
by `Θ` does not fit through it. -/
theorem Polyhedron.not_fitsThrough_smul_of_roots [Countable κ] {pts : List (V3 κ)}
    {D : SymmData κ} {i j k l : ℕ} (hspan : spanOk pts i j k l = true) {roots : List ChartBox}
    (hroots : unitsIn roots = true) {Θ : ℝ}
    (h : roots.Forall fun B ↦ ∀ p ∈ B.poses, SettledS pts D Θ p) :
    ¬ ((Polyhedron.ofPoints pts).smul Θ).FitsThrough (Polyhedron.ofPoints pts) := by
  refine Polyhedron.not_fitsThrough_smul_of_settled (D := D) hspan fun a k p hp ↦ ?_
  simp only [unitsIn, List.all_eq_true, List.any_eq_true] at hroots
  obtain ⟨B, hB, hsub⟩ := hroots a (by fin_cases a <;> simp) k (by fin_cases k <;> simp)
  exact List.forall_iff_forall_mem.mp h B hB p (ChartBox.poses_subset hsub hp)

end Roots

end Nieuwland.Check
