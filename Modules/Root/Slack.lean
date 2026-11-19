import Modules.Check.Polynomial.Expr
import Modules.NoFit.Along
import Modules.NoFit.Support
import Modules.Rupert.Interior

/-!
# Slacks at a strict fit

A contact of a D2 certificate (`code/src/proof/d2/`, "Unknowns and slacks") is a plug vertex `k`
against a hole edge `a → b`: an edge of the hole's shadow, every vertex of the hole weakly to its
left. At a strict fit of the plug `θ K` the shadow of the plug lies in the interior of the hole's
shadow, so the plug vertex lies strictly to the left of the edge's line
(`Polyhedron.exists_orient_pos_of_fitsAlong`: one translation for all edges and vertices).

This is the only geometry of the root-form proofs: the rest is algebra on the slack polynomials,
which are these orientations times the positive `|q|²` of the chart quaternion.
-/

open Matrix

namespace Nieuwland

/-- A point of the interior of a polygon lies strictly to the left of an edge line that has the
polygon's points weakly to its left, and one of them strictly. -/
theorem orient_pos_of_mem_interior {S : Set (Fin 2 → ℝ)} {a b : Fin 2 → ℝ}
    (hS : ∀ w ∈ S, 0 ≤ orient a b w) (hne : ∃ w ∈ S, 0 < orient a b w) {z : Fin 2 → ℝ}
    (hz : z ∈ interior (convexHull ℝ S)) : 0 < orient a b z := by
  let φ : (Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
    (b 1 - a 1) • LinearMap.proj 0 - (b 0 - a 0) • LinearMap.proj 1
  have hφ : ∀ c, orient a b c = φ a - φ c := fun c ↦ by
    simp only [orient, φ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      smul_eq_mul]
    ring
  have hφ0 : φ ≠ 0 := fun h0 ↦ by
    obtain ⟨w, -, hw⟩ := hne
    rw [hφ, h0] at hw
    simp at hw
  have := lt_of_mem_interior_convexHull hφ0 (h := φ a)
    (fun w hw ↦ by have := hS w hw; rw [hφ] at this; linarith) hz
  rw [hφ]
  linarith

namespace Polyhedron

/-- At a strict fit of the plug `θ K` at a chart pose, one translation moves the shadow of every
plug vertex into the interior of the hole's shadow. -/
theorem exists_mem_interior_of_fitsAlong {P : Polyhedron} {p : ChartPose} {θ : ℝ}
    (h : P.FitsAlong (viewDir p.view p.s p.t) (p.rotation * (θ • 1))) :
    ∃ τ : Fin 2 → ℝ, ∀ v ∈ P.vertices, θ • p.screen (p.rotation *ᵥ v) + τ ∈
      interior (convexHull ℝ {x | ∃ w ∈ P.vertices, screenₗ p.view p.s p.t w = x}) := by
  obtain ⟨τ, hτ⟩ := h.exists_add_subset (screen_surjective p.view p.s p.t) (ker_screenₗ _ _ _)
  have hv := (P.image_add_subset_interior_iff
    (screenₗ p.view p.s p.t ∘ₗ (p.rotation * (θ • 1)).mulVecLin) (screenₗ p.view p.s p.t) τ).mp hτ
  refine ⟨τ, fun v hvP ↦ ?_⟩
  have hz := hv v hvP
  have e : (screenₗ p.view p.s p.t ∘ₗ (p.rotation * (θ • 1)).mulVecLin) v =
      θ • p.screen (p.rotation *ᵥ v) := by
    rw [LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mulVec, map_smul]
    rfl
  rw [e] at hz
  exact hz

/-- **Slacks at a strict fit.** At a strict fit of the plug `θ K` at a chart pose, one
translation `τ` puts every plug vertex strictly to the left of every line `a → b` that has the
hole's shadow weakly to its left (and not on it). -/
theorem exists_orient_pos_of_fitsAlong {P : Polyhedron} {p : ChartPose} {θ : ℝ}
    (h : P.FitsAlong (viewDir p.view p.s p.t) (p.rotation * (θ • 1))) :
    ∃ τ : Fin 2 → ℝ, ∀ a b : Fin 2 → ℝ, (∀ w ∈ P.vertices, 0 ≤ orient a b (p.screen w)) →
      (∃ w ∈ P.vertices, 0 < orient a b (p.screen w)) →
      ∀ v ∈ P.vertices, 0 < orient a b (θ • p.screen (p.rotation *ᵥ v) + τ) := by
  obtain ⟨τ, hτ⟩ := exists_mem_interior_of_fitsAlong h
  refine ⟨τ, fun a b hS hne v hvP ↦ orient_pos_of_mem_interior ?_ ?_ (hτ v hvP)⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact hS w hw
  · obtain ⟨w, hw, hpos⟩ := hne
    exact ⟨_, ⟨w, hw, rfl⟩, hpos⟩

/-- **Slacks at a strict fit of a centrally symmetric solid**: no translation is needed (average
the fit with its reflection). -/
theorem orient_pos_of_fitsAlong_centred {P : Polyhedron} (hsym : ∀ x ∈ P.vertices, -x ∈ P.vertices)
    {p : ChartPose} {θ : ℝ} (h : P.FitsAlong (viewDir p.view p.s p.t) (p.rotation * (θ • 1)))
    (a b : Fin 2 → ℝ) (hS : ∀ w ∈ P.vertices, 0 ≤ orient a b (p.screen w))
    (hne : ∃ w ∈ P.vertices, 0 < orient a b (p.screen w)) {v : Fin 3 → ℝ} (hvP : v ∈ P.vertices) :
    0 < orient a b (θ • p.screen (p.rotation *ᵥ v)) := by
  obtain ⟨τ, hτ⟩ := exists_mem_interior_of_fitsAlong h
  have hT := forall_mem_interior_of_add_mem_interior
    (S := {x | ∃ w ∈ P.vertices, screenₗ p.view p.s p.t w = x})
    (T := {y | ∃ u ∈ P.vertices, θ • p.screen (p.rotation *ᵥ u) = y})
    (fun s ⟨w, hw, e⟩ ↦ ⟨-w, hsym w hw, by rw [map_neg, e]⟩)
    (fun y ⟨u, hu, e⟩ ↦
      ⟨-u, hsym u hu, by rw [Matrix.mulVec_neg, ChartPose.screen_neg, smul_neg, e]⟩)
    (t := τ) (fun y ⟨u, hu, e⟩ ↦ e ▸ hτ u hu)
  refine orient_pos_of_mem_interior ?_ ?_ (hT _ ⟨v, hvP, rfl⟩)
  · rintro _ ⟨w, hw, rfl⟩
    exact hS w hw
  · obtain ⟨w, hw, hpos⟩ := hne
    exact ⟨_, ⟨w, hw, rfl⟩, hpos⟩

end Polyhedron

/-! ### The slack polynomials

The variables: `0, 1` the view coordinates `(s, t)`; `2, 3, 4` the rotation coordinates `x`; in
general mode `5, 6` the screen translation `y`; then the scale `l` and the multipliers (`nx`,
`lE`, `yE`, `mE`: the order of the unknowns of `code/src/proof/d2/`). The coordinates of the
solid's vertices are expressions `V v c` in further variables (the field's basis values:
parameters). Centred mode has no translation: `y = 0`. -/

namespace Root

open Check (Expr)

/-- The number of pose unknowns: `(s, t, x₁, x₂, x₃)` and, in general mode, the translation. -/
def nx (cen : Bool) : ℕ := if cen then 5 else 7

/-- The scale `l`. -/
def lE (cen : Bool) : Expr := .var (nx cen)

/-- The translation `y`: zero in centred mode. -/
def yE (cen : Bool) (c : Fin 2) : Expr := if cen then .const 0 else .var (5 + c)

/-- The multiplier of the contact `i`. -/
def mE (cen : Bool) (i : ℕ) : Expr := .var (nx cen + 1 + i)

/-- The quaternion of rotation chart `k`, its coordinates in the variables `2, 3, 4`. -/
def qE (k j : Fin 4) : Expr :=
  if j = k then .const 1 else .var (2 + (if j < k then j.val else j.val - 1))

/-- `quatMatrix` on expressions. -/
def quatE (q : Fin 4 → Expr) : Fin 3 → Fin 3 → Expr :=
  ![![q 0 * q 0 + q 1 * q 1 - q 2 * q 2 - q 3 * q 3, .const 2 * (q 1 * q 2 - q 0 * q 3),
      .const 2 * (q 1 * q 3 + q 0 * q 2)],
    ![.const 2 * (q 1 * q 2 + q 0 * q 3), q 0 * q 0 - q 1 * q 1 + q 2 * q 2 - q 3 * q 3,
      .const 2 * (q 2 * q 3 - q 0 * q 1)],
    ![.const 2 * (q 1 * q 3 - q 0 * q 2), .const 2 * (q 2 * q 3 + q 0 * q 1),
      q 0 * q 0 - q 1 * q 1 - q 2 * q 2 + q 3 * q 3]]

/-- `|q|²` on expressions. -/
def normE (q : Fin 4 → Expr) : Expr := q 0 * q 0 + q 1 * q 1 + q 2 * q 2 + q 3 * q 3

/-- The screen map of view chart `a` on expressions, `(s, t)` in the variables `0, 1`. -/
def screenE (a : Fin 3) (x : Fin 3 → Expr) : Fin 2 → Expr :=
  ![x (a + 1) - .var 0 * x a, x (a + 2) - .var 1 * x a]

/-- `Q(q) x` on expressions, `q` the quaternion of rotation chart `k`. -/
def rotE (k : Fin 4) (x : Fin 3 → Expr) : Fin 3 → Expr :=
  fun i ↦ quatE (qE k) i 0 * x 0 + quatE (qE k) i 1 * x 1 + quatE (qE k) i 2 * x 2

/-- The slack of the plug vertex `vk` against the hole edge `va → vb`:
`-det(L(v_b - v_a), l L(Q v_k) + d (y - L v_a))` (`slack` of `code/src/proof/d2/mod.rs`). -/
def slackE (cen : Bool) (a : Fin 3) (k : Fin 4) (V : ℕ → Fin 3 → Expr) (va vb vk : ℕ) : Expr :=
  let A := screenE a (V va)
  let B := screenE a (V vb)
  let W := screenE a (rotE k (V vk))
  let z : Fin 2 → Expr := fun c ↦ lE cen * W c + normE (qE k) * (yE cen c - A c)
  (B 1 - A 1) * z 0 - (B 0 - A 0) * z 1

/-- The hole condition of the vertex `vk` against the hole edge `va → vb`:
`det(L(v_b - v_a), L(v_k - v_a))` (`hole` of `code/src/proof/d2/mod.rs`). -/
def holeE (a : Fin 3) (V : ℕ → Fin 3 → Expr) (va vb vk : ℕ) : Expr :=
  let A := screenE a (V va)
  let B := screenE a (V vb)
  let K := screenE a (V vk)
  (B 0 - A 0) * (K 1 - A 1) - (B 1 - A 1) * (K 0 - A 0)

variable (z : ℕ → ℝ)

theorem eval_qE (k j : Fin 4) : (qE k j).eval z = chartQuat k ![z 2, z 3, z 4] j := by
  fin_cases k <;> fin_cases j <;> simp [qE, chartQuat]

theorem eval_quatE (q : Fin 4 → Expr) (i j : Fin 3) :
    (quatE q i j).eval z = quatMatrix (fun m ↦ (q m).eval z) i j := by
  fin_cases i <;> fin_cases j <;> simp [quatE, quatMatrix] <;> ring

theorem eval_normE (q : Fin 4 → Expr) :
    (normE q).eval z = (fun m ↦ (q m).eval z) ⬝ᵥ fun m ↦ (q m).eval z := by
  simp [normE, dotProduct, Fin.sum_univ_four]

theorem eval_screenE (a : Fin 3) (x : Fin 3 → Expr) (c : Fin 2) :
    (screenE a x c).eval z = screen a (z 0) (z 1) (fun i ↦ (x i).eval z) c := by
  fin_cases c <;> simp [screenE, screen]

theorem eval_rotE (k : Fin 4) (x : Fin 3 → Expr) (i : Fin 3) :
    (rotE k x i).eval z =
      (quatMatrix (chartQuat k ![z 2, z 3, z 4]) *ᵥ fun j ↦ (x j).eval z) i := by
  simp only [rotE, Expr.eval_add, Expr.eval_mul, eval_quatE, eval_qE, mulVec, dotProduct,
    Fin.sum_univ_three]

/-- The chart pose of a point of the variables. -/
def poseOf (a : Fin 3) (k : Fin 4) : ChartPose := ⟨a, z 0, z 1, k, ![z 2, z 3, z 4]⟩

/-- The vertex `v` at a point of the variables. -/
def vertOf (V : ℕ → Fin 3 → Expr) (v : ℕ) : Fin 3 → ℝ := fun c ↦ (V v c).eval z

/-- The translation at a point of the variables. -/
def yOf (cen : Bool) : Fin 2 → ℝ := fun c ↦ (yE cen c).eval z

/-- `|q|² > 0` for the quaternion of a rotation chart. -/
theorem quat_pos (k : Fin 4) (x : Fin 3 → ℝ) : 0 < chartQuat k x ⬝ᵥ chartQuat k x :=
  lt_of_le_of_ne (Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _)
    (Ne.symm (dotProduct_self_eq_zero.not.mpr (chartQuat_ne_zero k x)))

/-- **The slack is the orientation**, times `-|q|²`: of the plug vertex at scale `l`, moved by
`y`, against the hole edge. -/
theorem eval_slackE (cen : Bool) (a : Fin 3) (k : Fin 4) (V : ℕ → Fin 3 → Expr) (va vb vk : ℕ) :
    (slackE cen a k V va vb vk).eval z =
      -((chartQuat k ![z 2, z 3, z 4] ⬝ᵥ chartQuat k ![z 2, z 3, z 4]) *
        orient ((poseOf z a k).screen (vertOf z V va)) ((poseOf z a k).screen (vertOf z V vb))
          ((lE cen).eval z • (poseOf z a k).screen ((poseOf z a k).rotation *ᵥ vertOf z V vk) +
            yOf z cen)) := by
  have hq : chartQuat k ![z 2, z 3, z 4] ⬝ᵥ chartQuat k ![z 2, z 3, z 4] ≠ 0 :=
    (quat_pos k _).ne'
  have hrot : (poseOf z a k).screen ((poseOf z a k).rotation *ᵥ vertOf z V vk) =
      (chartQuat k ![z 2, z 3, z 4] ⬝ᵥ chartQuat k ![z 2, z 3, z 4])⁻¹ •
        screen a (z 0) (z 1) (quatMatrix (chartQuat k ![z 2, z 3, z 4]) *ᵥ vertOf z V vk) := by
    change screenₗ a (z 0) (z 1)
      (quatRotation (chartQuat k ![z 2, z 3, z 4]) *ᵥ vertOf z V vk) = _
    rw [quatRotation, Matrix.smul_mulVec, map_smul]
    rfl
  rw [hrot]
  simp only [slackE, Expr.eval_sub, Expr.eval_mul, Expr.eval_add, eval_screenE, eval_normE,
    eval_qE, eval_rotE, orient, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hv : ∀ v, (fun i ↦ (V v i).eval z) = vertOf z V v := fun _ ↦ rfl
  simp only [hv, yOf, ChartPose.screen, poseOf]
  field_simp
  ring

/-- The derivative of the general-mode slack in the translation's coordinate `c`:
`|q|² (B - A)_1` and `-|q|² (B - A)_0`. -/
def slackYE (a : Fin 3) (k : Fin 4) (V : ℕ → Fin 3 → Expr) (va vb : ℕ) (c : Fin 2) : Expr :=
  let A := screenE a (V va)
  let B := screenE a (V vb)
  if c = 0 then normE (qE k) * (B 1 - A 1) else .const 0 - normE (qE k) * (B 0 - A 0)

/-- **The general-mode slack is affine in the translation**: between two points with the same
pose, scale and vertices it changes by `slackYE` times the translation's change. -/
theorem eval_slackE_move (a : Fin 3) (k : Fin 4) (V : ℕ → Fin 3 → Expr) (va vb vk : ℕ)
    {z z' : ℕ → ℝ} (h0 : z' 0 = z 0) (h1 : z' 1 = z 1) (h2 : z' 2 = z 2) (h3 : z' 3 = z 3)
    (h4 : z' 4 = z 4) (hl : z' 7 = z 7) (hV : ∀ v, vertOf z' V v = vertOf z V v) :
    (slackE false a k V va vb vk).eval z' = (slackE false a k V va vb vk).eval z +
      ((slackYE a k V va vb 0).eval z * (z' 5 - z 5) +
        (slackYE a k V va vb 1).eval z * (z' 6 - z 6)) := by
  have hv : ∀ (y : ℕ → ℝ) v, (fun i ↦ (V v i).eval y) = vertOf y V v := fun _ _ ↦ rfl
  simp only [slackE, slackYE, lE, yE, nx, Expr.eval_sub, Expr.eval_mul, eval_screenE,
    eval_normE, eval_qE, eval_rotE, hv, hV, h0, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte,
    Expr.eval, Fin.isValue, one_ne_zero, Fin.val_zero, Fin.val_one, add_zero, hl]
  ring

/-- **The hole condition is the orientation** of the vertex's shadow against the edge. -/
theorem eval_holeE (a : Fin 3) (k : Fin 4) (V : ℕ → Fin 3 → Expr) (va vb vk : ℕ) :
    (holeE a V va vb vk).eval z =
      orient ((poseOf z a k).screen (vertOf z V va)) ((poseOf z a k).screen (vertOf z V vb))
        ((poseOf z a k).screen (vertOf z V vk)) := by
  simp only [holeE, Expr.eval_sub, Expr.eval_mul, eval_screenE, orient]
  rfl

end Root

end Nieuwland
