import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# A zero of a system in a box, by contraction

The root of a D2 certificate (`code/src/proof/d2/`, notes/touch-leaf.md) is the unique zero of a
polynomial system `F : ℝⁿ → ℝⁿ` in a box `B`, certified by Krawczyk's test with a rational
preconditioner `C`. Its content, without derivatives: the map `T y = y - C F(y)` sends `B` into
itself and contracts there, and `C` is invertible. Then `T` has exactly one fixed point in `B`
(Banach), and the fixed points of `T` are the zeros of `F`.

The box has a half-width `w_i > 0` per coordinate (`Root.box`), and the distance that `T`
contracts is the sup distance of the coordinates over their half-widths: the unknowns of a
certificate's system are of different sizes (a translation in the units of the points, multipliers
in the inverse units of the slacks), and a test in one common half-width holds for none but
points of size about `1`.

* `Root.existsUnique_fixed`: a self-map of a closed ball of `Fin n → ℝ` that contracts there has
  exactly one fixed point in it.
* `Root.existsUnique_fixed_box`: the same on a box, for the weighted distance (the ball's case
  after the change of coordinates `y_i = c_i + w_i u_i`).
* `Root.existsUnique_zero`: with `C * D = 1`, the zeros of `F` in the box are the fixed points of
  `y ↦ y - C *ᵥ F y`: exactly one.

The checks that give the two premises from interval arithmetic are in `Modules/Root/Krawczyk.lean`.
-/

open Metric Matrix

namespace Nieuwland.Root

variable {n : ℕ}

/-- A self-map of a closed ball of `Fin n → ℝ` (the sup distance) that contracts on it has
exactly one fixed point in it. -/
theorem existsUnique_fixed (T : (Fin n → ℝ) → Fin n → ℝ) (c : Fin n → ℝ) {r κ : ℝ} (hr : 0 ≤ r)
    (hκ0 : 0 ≤ κ) (hκ : κ < 1) (hmaps : ∀ y ∈ closedBall c r, T y ∈ closedBall c r)
    (hlip : ∀ y ∈ closedBall c r, ∀ y' ∈ closedBall c r, dist (T y) (T y') ≤ κ * dist y y') :
    ∃! y, y ∈ closedBall c r ∧ T y = y := by
  have hc : c ∈ closedBall c r := mem_closedBall_self hr
  obtain ⟨K, rfl⟩ : ∃ K : NNReal, (K : ℝ) = κ := ⟨⟨κ, hκ0⟩, rfl⟩
  have hmt : Set.MapsTo T (closedBall c r) (closedBall c r) := hmaps
  have hcon : ContractingWith K (hmt.restrict T (closedBall c r) (closedBall c r)) := by
    refine ⟨by exact_mod_cast hκ, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
    exact hlip x.1 x.2 y.1 y.2
  obtain ⟨y, hy, hfix, -⟩ := hcon.exists_fixedPoint' (isClosed_closedBall.isComplete) hmt hc
    (edist_ne_top _ _)
  refine ⟨y, ⟨hy, hfix⟩, fun z hz ↦ ?_⟩
  have h := hlip z hz.1 y hy
  rw [hz.2, hfix.eq] at h
  have h0 : dist z y ≤ 0 := by
    by_contra hpos
    have hpos : 0 < dist z y := lt_of_not_ge hpos
    nlinarith
  exact dist_le_zero.mp h0

/-- The box of the centre `c` and the half-widths `w`. -/
def box (c w : Fin n → ℝ) : Set (Fin n → ℝ) := {y | ∀ i, |y i - c i| ≤ w i}

/-- A self-map of a box with positive half-widths `w` that contracts the distance weighted by
`w` (points within `t w_j` of each other in every coordinate `j` have images within `κ t w_i` in
every coordinate `i`) has exactly one fixed point in the box. -/
theorem existsUnique_fixed_box (T : (Fin n → ℝ) → Fin n → ℝ) (c w : Fin n → ℝ) {κ : ℝ}
    (hw : ∀ i, 0 < w i) (hκ0 : 0 ≤ κ) (hκ : κ < 1) (hmaps : ∀ y ∈ box c w, T y ∈ box c w)
    (hlip : ∀ y ∈ box c w, ∀ y' ∈ box c w, ∀ t : ℝ, 0 ≤ t → (∀ j, |y j - y' j| ≤ t * w j) →
      ∀ i, |T y i - T y' i| ≤ κ * t * w i) :
    ∃! y, y ∈ box c w ∧ T y = y := by
  -- the coordinates `u` of `y = c + w u`: the box is the unit ball
  let S : (Fin n → ℝ) → Fin n → ℝ := fun u i ↦ c i + w i * u i
  let T' : (Fin n → ℝ) → Fin n → ℝ := fun u i ↦ (T (S u) i - c i) / w i
  have hball : ∀ u : Fin n → ℝ, u ∈ closedBall (0 : Fin n → ℝ) 1 ↔ ∀ i, |u i| ≤ 1 := fun u ↦ by
    rw [mem_closedBall, dist_pi_le_iff zero_le_one]
    simp
  have hS : ∀ u ∈ closedBall (0 : Fin n → ℝ) 1, S u ∈ box c w := fun u hu i ↦ by
    have h1 := (hball u).mp hu i
    change |c i + w i * u i - c i| ≤ w i
    rw [add_sub_cancel_left, abs_mul, abs_of_pos (hw i)]
    nlinarith [hw i]
  have hmaps' : ∀ u ∈ closedBall (0 : Fin n → ℝ) 1, T' u ∈ closedBall (0 : Fin n → ℝ) 1 :=
    fun u hu ↦ (hball _).mpr fun i ↦ by
      change |(T (S u) i - c i) / w i| ≤ 1
      rw [abs_div, abs_of_pos (hw i), div_le_one (hw i)]
      exact hmaps _ (hS u hu) i
  have hlip' : ∀ u ∈ closedBall (0 : Fin n → ℝ) 1, ∀ u' ∈ closedBall (0 : Fin n → ℝ) 1,
      dist (T' u) (T' u') ≤ κ * dist u u' := fun u hu u' hu' ↦ by
    rw [dist_pi_le_iff (mul_nonneg hκ0 dist_nonneg)]
    intro i
    have hd : ∀ j, |S u j - S u' j| ≤ dist u u' * w j := fun j ↦ by
      have hj : |u j - u' j| ≤ dist u u' := by
        rw [← Real.dist_eq]
        exact dist_le_pi_dist u u' j
      change |c j + w j * u j - (c j + w j * u' j)| ≤ dist u u' * w j
      rw [show c j + w j * u j - (c j + w j * u' j) = w j * (u j - u' j) by ring, abs_mul,
        abs_of_pos (hw j), mul_comm]
      exact mul_le_mul_of_nonneg_right hj (hw j).le
    have h := hlip _ (hS u hu) _ (hS u' hu') _ dist_nonneg hd i
    rw [Real.dist_eq]
    change |(T (S u) i - c i) / w i - (T (S u') i - c i) / w i| ≤ κ * dist u u'
    rw [← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos (hw i), div_le_iff₀ (hw i)]
    exact h
  obtain ⟨u, ⟨hu, hfix⟩, huniq⟩ := existsUnique_fixed T' 0 zero_le_one hκ0 hκ hmaps' hlip'
  have hfix' : T (S u) = S u := funext fun i ↦ by
    have h := congrFun hfix i
    change (T (S u) i - c i) / w i = u i at h
    change T (S u) i = c i + w i * u i
    have := (hw i).ne'
    field_simp at h
    linarith
  refine ⟨S u, ⟨hS u hu, hfix'⟩, fun z hz ↦ ?_⟩
  -- a fixed point `z` of the box in the coordinates `u`
  let v : Fin n → ℝ := fun i ↦ (z i - c i) / w i
  have hSv : S v = z := funext fun i ↦ by
    change c i + w i * ((z i - c i) / w i) = z i
    have := (hw i).ne'
    field_simp
    ring
  have hv : v ∈ closedBall (0 : Fin n → ℝ) 1 := (hball v).mpr fun i ↦ by
    change |(z i - c i) / w i| ≤ 1
    rw [abs_div, abs_of_pos (hw i), div_le_one (hw i)]
    exact hz.1 i
  have hvfix : T' v = v := funext fun i ↦ by
    change (T (S v) i - c i) / w i = (z i - c i) / w i
    rw [hSv, hz.2]
  rw [← hSv, huniq v ⟨hv, hvfix⟩]

/-- The unique zero of a system in a box: `y ↦ y - C F(y)` maps the box into itself and contracts
the distance weighted by the half-widths there, and `C` is invertible. -/
theorem existsUnique_zero (F : (Fin n → ℝ) → Fin n → ℝ) (C D : Matrix (Fin n) (Fin n) ℝ)
    (hCD : C * D = 1) (c w : Fin n → ℝ) {κ : ℝ} (hw : ∀ i, 0 < w i) (hκ0 : 0 ≤ κ) (hκ : κ < 1)
    (hmaps : ∀ y ∈ box c w, y - C *ᵥ F y ∈ box c w)
    (hlip : ∀ y ∈ box c w, ∀ y' ∈ box c w, ∀ t : ℝ, 0 ≤ t → (∀ j, |y j - y' j| ≤ t * w j) →
      ∀ i, |(y - C *ᵥ F y) i - (y' - C *ᵥ F y') i| ≤ κ * t * w i) :
    ∃! y, y ∈ box c w ∧ F y = 0 := by
  have hDC : D * C = 1 := mul_eq_one_comm.mp hCD
  have hiff : ∀ y, y - C *ᵥ F y = y ↔ F y = 0 := fun y ↦ by
    constructor
    · intro h
      have h0 : C *ᵥ F y = 0 := by
        have := sub_eq_self.mp h
        exact this
      have : D *ᵥ (C *ᵥ F y) = 0 := by rw [h0, Matrix.mulVec_zero]
      rwa [Matrix.mulVec_mulVec, hDC, Matrix.one_mulVec] at this
    · intro h
      rw [h, Matrix.mulVec_zero, sub_zero]
  obtain ⟨y, ⟨hy, hfix⟩, huniq⟩ :=
    existsUnique_fixed_box (fun y ↦ y - C *ᵥ F y) c w hw hκ0 hκ hmaps hlip
  exact ⟨y, ⟨hy, (hiff y).mp hfix⟩, fun z hz ↦ huniq z ⟨hz.1, (hiff z).mpr hz.2⟩⟩

end Nieuwland.Root
