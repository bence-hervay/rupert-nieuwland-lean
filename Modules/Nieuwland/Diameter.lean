import Modules.Nieuwland.Settled
import Modules.Nieuwland.Weak

/-!
# The diameter bound

An upper bound of the Nieuwland number that holds for every pose at once
(`code/src/proof/diameter.rs`, `notes/diameter.md`).

Let `D` bound the distance of any two points of `P` and let `c > 0`. A pair of points `x, y` of
`P` with `d = x - y` has, seen along a unit vector `u`, a shadow of squared length
`|d|² - (d · u)²`. **If every unit vector `u` has a pair whose shadow, scaled by `c`, is at least
`D` long, then `P` scaled by `c` does not fit through `P`**
(`Polyhedron.not_fitsThrough_smul_of_pairs`): the shadow points of that pair of the plug would be
two interior points of a shadow of `P` at distance at least `D`, the shadow would then hold two
points farther apart than `D`, and no two points of `P` are.

The hypothesis is checked on a cover of the directions by cones `C(w₀, w₁, w₂)` (the nonnegative
combinations of three vectors), starting from the four octants of `z ≥ 0` (the forms are even).
With `Θ = N / S` and `k = N² |d|² - S² D²` the form of a pair is
`Q(u) = k |u|² - N² (d · u)²`, which is `≥ 0` exactly when the pair's shadow along `u`, scaled by
`Θ`, is at least `D` long; `B(x, y) = k (x · y) - N² (d · x) (d · y)` is its bilinear form
(`pairForm`). The nodes of a cover, in depth-first order:

* `pair a b`, a leaf: the six values `B(wᵢ, wⱼ)` of the pair of the points `a`, `b` are `≥ 0`,
  so `Q ≥ 0` on the cone (`pairForm_cone_nonneg`);
* `split a₀ a₁ a₂`: coefficients `≥ 0`, not all zero; with `p = a₀ w₀ + a₁ w₁ + a₂ w₂` the
  children are the cones with `wᵢ` replaced by `p`, one for each `aᵢ > 0`, and they cover the
  cone (`InCone.split`).

Every test is an exact sign in the field of the points, so a direction in which the best pair's
form is zero (a view of least shadow diameter, at `Θ = D / δ`) is no obstacle: it is a generator
of the cones around it.

A long cover is checked in parts (`Check.Diam.part`): a run of consecutive nodes takes the cones
still to cover to the cones still to cover after it, both written out, so that each part is one
bounded evaluation (the kernel keeps what it has evaluated: about 8 MB a node, measured).

## Main statements

* `Polyhedron.not_fitsThrough_smul_of_pairs`: the bound, for real points.
* `Check.Diam.Cover`: a cover at a scale, over exact values; `Check.Diam.Cover.not_fitsThrough`.
  From one evaluation (`Check.Diam.check`, `Check.Diam.cover_of_check`) or from parts
  (`Check.Diam.part`, `Check.Diam.part_sound`).
* `Check.Polyhedron.nieuwland_eq_of_diameter`: with a weak fit at the same scale, the Nieuwland
  number is that scale; `Check.Polyhedron.nieuwland_eq_of_diameter_lift` for a fixture whose
  points lie in a smaller field (the form of the generated certificates).
-/

open Matrix

namespace Nieuwland

/-! ### Distances in a hull and in its shadows -/

/-- One coordinate of the convexity of a squared distance. -/
private theorem mul_self_comb_le {a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a * p + b * q) * (a * p + b * q) ≤ a * (p * p) + b * (q * q) := by
  obtain rfl : b = 1 - a := by linarith
  nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (p - q))]

/-- The points within a given squared distance of a point form a convex set. -/
theorem convex_sqDist_le (y : Fin 3 → ℝ) (D2 : ℝ) :
    Convex ℝ {w : Fin 3 → ℝ | (w - y) ⬝ᵥ (w - y) ≤ D2} := by
  intro w₁ h₁ w₂ h₂ a b ha hb hab
  simp only [Set.mem_ofPred_eq, dotProduct, Fin.sum_univ_three, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul] at h₁ h₂ ⊢
  have e : ∀ i, a * w₁ i + b * w₂ i - y i = a * (w₁ i - y i) + b * (w₂ i - y i) := fun i ↦ by
    linear_combination (y i) * hab
  rw [e 0, e 1, e 2]
  have s : a * D2 + b * D2 = D2 := by rw [← add_mul, hab, one_mul]
  have h0 := mul_self_comb_le (p := w₁ 0 - y 0) (q := w₂ 0 - y 0) ha hb hab
  have h1 := mul_self_comb_le (p := w₁ 1 - y 1) (q := w₂ 1 - y 1) ha hb hab
  have h2 := mul_self_comb_le (p := w₁ 2 - y 2) (q := w₂ 2 - y 2) ha hb hab
  have ha1 := mul_le_mul_of_nonneg_left h₁ ha
  have hb1 := mul_le_mul_of_nonneg_left h₂ hb
  linarith

theorem dotProduct_sub_self_comm {n : Type*} [Fintype n] (a b : n → ℝ) :
    (a - b) ⬝ᵥ (a - b) = (b - a) ⬝ᵥ (b - a) := by
  rw [← neg_sub b a, neg_dotProduct, dotProduct_neg, neg_neg]

/-- Two points of a hull are no farther apart than the farthest two of its points. -/
theorem sqDist_le_of_mem_convexHull {V : Set (Fin 3 → ℝ)} {D2 : ℝ}
    (h : ∀ x ∈ V, ∀ y ∈ V, (x - y) ⬝ᵥ (x - y) ≤ D2) {z z' : Fin 3 → ℝ}
    (hz : z ∈ convexHull ℝ V) (hz' : z' ∈ convexHull ℝ V) : (z - z') ⬝ᵥ (z - z') ≤ D2 := by
  have h1 : ∀ y ∈ V, (z - y) ⬝ᵥ (z - y) ≤ D2 := fun y hy ↦
    convexHull_min (t := {w | (w - y) ⬝ᵥ (w - y) ≤ D2}) (fun x hx ↦ h x hx y hy)
      (convex_sqDist_le y D2) hz
  have h2 : (z' - z) ⬝ᵥ (z' - z) ≤ D2 :=
    convexHull_min (t := {w | (w - z) ⬝ᵥ (w - z) ≤ D2})
      (fun y hy ↦ by
        have := h1 y hy
        rwa [dotProduct_sub_self_comm] at this)
      (convex_sqDist_le z D2) hz'
  rwa [dotProduct_sub_self_comm]

/-- An orthogonal matrix keeps the squared length of a vector. -/
theorem dotProduct_mulVec_self_of_mem_orthogonalGroup {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R ∈ O(3)) (v : Fin 3 → ℝ) : (R *ᵥ v) ⬝ᵥ (R *ᵥ v) = v ⬝ᵥ v := by
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec,
    transpose_mul_of_mem_orthogonalGroup hR, one_mulVec]

/-- The squared length of a shadow: the squared length less the square of the third
coordinate. -/
theorem projXY_dotProduct_self (w : Fin 3 → ℝ) :
    projXY w ⬝ᵥ projXY w = w ⬝ᵥ w - w 2 ^ 2 := by
  simp only [projXY, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

theorem projXY_sub (x y : Fin 3 → ℝ) : projXY (x - y) = projXY x - projXY y := by
  ext i
  fin_cases i <;> simp [projXY]

/-- An interior point `p` of a set of the plane is not its farthest point from any `q`. -/
theorem exists_sqDist_lt_of_mem_interior {S : Set (Fin 2 → ℝ)} {p : Fin 2 → ℝ}
    (hp : p ∈ interior S) (q : Fin 2 → ℝ) :
    ∃ r ∈ S, (p - q) ⬝ᵥ (p - q) < (r - q) ⬝ᵥ (r - q) := by
  -- a direction `e ≠ 0` that does not lead towards `q`
  obtain ⟨e, he, hpe⟩ : ∃ e : Fin 2 → ℝ, 0 < e ⬝ᵥ e ∧ 0 ≤ (p - q) ⬝ᵥ e := by
    by_cases h : p - q = 0
    · exact ⟨![1, 0], by simp [dotProduct, Fin.sum_univ_two], by simp [h]⟩
    · have hnn : 0 ≤ (p - q) ⬝ᵥ (p - q) := by
        simp only [dotProduct, Fin.sum_univ_two]
        exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
      have hne : (p - q) ⬝ᵥ (p - q) ≠ 0 := fun h0 ↦ h (dotProduct_self_eq_zero.mp h0)
      exact ⟨p - q, lt_of_le_of_ne hnn (Ne.symm hne), hnn⟩
  have hc : Continuous fun s : ℝ ↦ p + s • e := by fun_prop
  have h0 : (fun s : ℝ ↦ p + s • e) ⁻¹' interior S ∈ nhds (0 : ℝ) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using isOpen_interior.mem_nhds hp)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp h0
  have hs : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  refine ⟨p + (ε / 2) • e, interior_subset (hball hs), ?_⟩
  have hs0 : 0 < ε / 2 := by positivity
  simp only [dotProduct, Fin.sum_univ_two, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul] at he hpe ⊢
  have h1 := mul_pos (mul_pos hs0 hs0) he
  have h2 := mul_nonneg hs0.le hpe
  nlinarith

/-! ### The bound -/

/-- **The diameter bound.** No two points of `P` are farther apart than `√D2`, and every unit
vector `u` has a pair of points of `P` whose shadow along `u`, scaled by `c`, is at least `√D2`
long. Then `P` scaled by `c` does not fit through `P`. -/
theorem Polyhedron.not_fitsThrough_smul_of_pairs {P : Polyhedron} {c D2 : ℝ}
    (hD : ∀ x ∈ P.vertices, ∀ y ∈ P.vertices, (x - y) ⬝ᵥ (x - y) ≤ D2)
    (hcov : ∀ u : Fin 3 → ℝ, u ⬝ᵥ u = 1 → ∃ x ∈ P.vertices, ∃ y ∈ P.vertices,
      D2 ≤ c ^ 2 * ((x - y) ⬝ᵥ (x - y) - ((x - y) ⬝ᵥ u) ^ 2)) :
    ¬ (P.smul c).FitsThrough P := by
  rintro ⟨R₁, hR₁, R₂, hR₂, t, hsub⟩
  have hO₁ := (mem_specialOrthogonalGroup_iff.mp hR₁).1
  have hO₂ := (mem_specialOrthogonalGroup_iff.mp hR₂).1
  -- the direction, in the frame of the plug, along which its shadow is taken
  have hu : (fun j ↦ R₁ 2 j) ⬝ᵥ (fun j ↦ R₁ 2 j) = 1 := by
    have h := congrFun (congrFun (mul_transpose_of_mem_orthogonalGroup hO₁) 2) 2
    simpa [Matrix.mul_apply, dotProduct] using h
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov _ hu
  have hmem : ∀ v ∈ P.vertices, projXY (R₁ *ᵥ (c • v)) + t ∈
      interior {projXY (R₂ *ᵥ z) | z ∈ P.hull} := fun v hv ↦
    hsub ⟨c • v, subset_convexHull ℝ _
      (Finset.mem_coe.mpr (Polyhedron.mem_smul_vertices.mpr ⟨v, hv, rfl⟩)), rfl⟩
  -- the shadows of the two points of the plug are at least `√D2` apart
  have hdist : D2 ≤ (projXY (R₁ *ᵥ (c • x)) + t - (projXY (R₁ *ᵥ (c • y)) + t)) ⬝ᵥ
      (projXY (R₁ *ᵥ (c • x)) + t - (projXY (R₁ *ᵥ (c • y)) + t)) := by
    have e : projXY (R₁ *ᵥ (c • x)) + t - (projXY (R₁ *ᵥ (c • y)) + t) =
        c • projXY (R₁ *ᵥ (x - y)) := by
      rw [add_sub_add_right_eq_sub, ← projXY_sub, ← mulVec_sub, ← smul_sub, projXY_mulVec_smul]
    have h2 : (R₁ *ᵥ (x - y)) 2 = (x - y) ⬝ᵥ fun j ↦ R₁ 2 j := by
      simp only [mulVec, dotProduct]
      exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
    rw [e, smul_dotProduct, dotProduct_smul, projXY_dotProduct_self,
      dotProduct_mulVec_self_of_mem_orthogonalGroup hO₁, h2, smul_eq_mul, smul_eq_mul]
    linarith
  -- a point of the hole's shadow farther from the second than the first is
  obtain ⟨r, hr, hlt⟩ := exists_sqDist_lt_of_mem_interior (hmem x hx)
    (projXY (R₁ *ᵥ (c • y)) + t)
  obtain ⟨z, hz, rfl⟩ := hr
  obtain ⟨z', hz', hz'e⟩ := interior_subset (hmem y hy)
  have hle : (projXY (R₂ *ᵥ z) - (projXY (R₁ *ᵥ (c • y)) + t)) ⬝ᵥ
      (projXY (R₂ *ᵥ z) - (projXY (R₁ *ᵥ (c • y)) + t)) ≤ D2 := by
    rw [← hz'e, ← projXY_sub, ← mulVec_sub, projXY_dotProduct_self,
      dotProduct_mulVec_self_of_mem_orthogonalGroup hO₂]
    have := sqDist_le_of_mem_convexHull (V := (P.vertices : Set (Fin 3 → ℝ)))
      (fun a ha b hb ↦ hD a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb)) hz hz'
    nlinarith [sq_nonneg ((R₂ *ᵥ (z - z')) 2)]
  linarith

/-! ### Cones and the forms of pairs -/

/-- `u` is a nonnegative combination of `x`, `y`, `z`. -/
def InCone (x y z u : Fin 3 → ℝ) : Prop :=
  ∃ α β γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ u = α • x + β • y + γ • z

/-- Among nonnegative `a` with a positive entry: an index of the least ratio `α i / a i`. -/
theorem exists_min_ratio {a α : Fin 3 → ℝ} (ha : ∀ i, 0 ≤ a i) (hpos : ∃ i, 0 < a i)
    (hα : ∀ i, 0 ≤ α i) : ∃ i, 0 < a i ∧ ∀ j, α i * a j ≤ α j * a i := by
  classical
  obtain ⟨i₀, hi₀⟩ := hpos
  have hne : (Finset.univ.filter fun i ↦ 0 < a i).Nonempty :=
    ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₀⟩⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image _ (fun i ↦ α i / a i) hne
  have hi' : 0 < a i := (Finset.mem_filter.mp hi).2
  refine ⟨i, hi', fun j ↦ ?_⟩
  rcases (ha j).eq_or_lt with h0 | hj
  · rw [← h0, mul_zero]
    exact mul_nonneg (hα j) hi'.le
  · have := hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
    rwa [div_le_div_iff₀ hi' hj] at this

/-- The first generator replaced by a combination with a positive coefficient of it, for a point
whose ratio is least there. -/
private theorem inCone_replace {x y z : Fin 3 → ℝ} {a b c α β γ : ℝ} (ha : 0 < a) (hα : 0 ≤ α)
    (h1 : α * b ≤ β * a) (h2 : α * c ≤ γ * a) :
    InCone (a • x + b • y + c • z) y z (α • x + β • y + γ • z) := by
  refine ⟨α / a, β - α / a * b, γ - α / a * c, div_nonneg hα ha.le, ?_, ?_, ?_⟩
  · rw [sub_nonneg, div_mul_eq_mul_div, div_le_iff₀ ha]
    exact h1
  · rw [sub_nonneg, div_mul_eq_mul_div, div_le_iff₀ ha]
    exact h2
  · ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring

theorem InCone.swap₀₁ {x y z u : Fin 3 → ℝ} (h : InCone x y z u) : InCone y x z u := by
  obtain ⟨α, β, γ, hα, hβ, hγ, rfl⟩ := h
  exact ⟨β, α, γ, hβ, hα, hγ, by rw [add_comm (α • x)]⟩

theorem InCone.swap₀₂ {x y z u : Fin 3 → ℝ} (h : InCone x y z u) : InCone z y x u := by
  obtain ⟨α, β, γ, hα, hβ, hγ, rfl⟩ := h
  exact ⟨γ, β, α, hγ, hβ, hα, by abel⟩

/-- **A split covers its cone.** With coefficients `a, b, c ≥ 0`, not all zero, and
`p = a x + b y + c z`, every point of the cone of `x, y, z` lies in the cone with `p` in place of
a generator whose coefficient is positive. -/
theorem InCone.split {x y z u : Fin 3 → ℝ} (h : InCone x y z u) {a b c : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hpos : 0 < a ∨ 0 < b ∨ 0 < c) :
    (0 < a ∧ InCone (a • x + b • y + c • z) y z u) ∨
      (0 < b ∧ InCone x (a • x + b • y + c • z) z u) ∨
      (0 < c ∧ InCone x y (a • x + b • y + c • z) u) := by
  obtain ⟨α, β, γ, hα, hβ, hγ, rfl⟩ := h
  have hA : ∀ i, 0 ≤ (![a, b, c] : Fin 3 → ℝ) i := by
    intro i
    fin_cases i <;> simpa
  have hB : ∀ i, 0 ≤ (![α, β, γ] : Fin 3 → ℝ) i := by
    intro i
    fin_cases i <;> simpa
  have hP : ∃ i, 0 < (![a, b, c] : Fin 3 → ℝ) i := by
    rcases hpos with h | h | h
    · exact ⟨0, by simpa⟩
    · exact ⟨1, by simpa⟩
    · exact ⟨2, by simpa⟩
  obtain ⟨i, hi, hmin⟩ := exists_min_ratio hA hP hB
  have m0 := hmin 0
  have m1 := hmin 1
  have m2 := hmin 2
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hi m1 m2
    exact Or.inl ⟨hi, inCone_replace hi hα m1 m2⟩
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hi m0 m2
    refine Or.inr (Or.inl ⟨hi, ?_⟩)
    have := (inCone_replace (x := y) (y := x) (z := z) hi hβ m0 m2).swap₀₁
    have e1 : b • y + a • x + c • z = a • x + b • y + c • z := by rw [add_comm (b • y)]
    have e2 : β • y + α • x + γ • z = α • x + β • y + γ • z := by rw [add_comm (β • y)]
    rwa [e1, e2] at this
  · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hi m0 m1
    refine Or.inr (Or.inr ⟨hi, ?_⟩)
    have := (inCone_replace (x := z) (y := y) (z := x) hi hγ m1 m0).swap₀₂
    have e1 : c • z + b • y + a • x = a • x + b • y + c • z := by abel
    have e2 : γ • z + β • y + α • x = α • x + β • y + γ • z := by abel
    rwa [e1, e2] at this

/-- The bilinear form of a pair with difference `d`: `B(x, y) = k (x · y) - n (d · x) (d · y)`.
With `k = n |d|² - m` the value `B(u, u)` is `≥ 0` exactly when `n` times the squared length of
the pair's shadow along `u` is at least `m`. -/
def pairForm (k n : ℝ) (d x y : Fin 3 → ℝ) : ℝ :=
  k * (x ⬝ᵥ y) - n * ((d ⬝ᵥ x) * (d ⬝ᵥ y))

/-- **A leaf**: a form that is `≥ 0` on the six pairs of generators of a cone is `≥ 0` on the
cone. -/
theorem pairForm_cone_nonneg {k n : ℝ} {d x y z u : Fin 3 → ℝ} (hxx : 0 ≤ pairForm k n d x x)
    (hxy : 0 ≤ pairForm k n d x y) (hxz : 0 ≤ pairForm k n d x z)
    (hyy : 0 ≤ pairForm k n d y y) (hyz : 0 ≤ pairForm k n d y z)
    (hzz : 0 ≤ pairForm k n d z z) (h : InCone x y z u) : 0 ≤ pairForm k n d u u := by
  obtain ⟨α, β, γ, hα, hβ, hγ, rfl⟩ := h
  have e : pairForm k n d (α • x + β • y + γ • z) (α • x + β • y + γ • z) =
      α * α * pairForm k n d x x + β * β * pairForm k n d y y + γ * γ * pairForm k n d z z +
        2 * (α * β * pairForm k n d x y) + 2 * (α * γ * pairForm k n d x z) +
        2 * (β * γ * pairForm k n d y z) := by
    simp only [pairForm, dotProduct, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  rw [e]
  have := mul_nonneg (mul_nonneg hα hα) hxx
  have := mul_nonneg (mul_nonneg hβ hβ) hyy
  have := mul_nonneg (mul_nonneg hγ hγ) hzz
  have := mul_nonneg (mul_nonneg hα hβ) hxy
  have := mul_nonneg (mul_nonneg hα hγ) hxz
  have := mul_nonneg (mul_nonneg hβ hγ) hyz
  linarith

theorem pairForm_neg (k n : ℝ) (d u : Fin 3 → ℝ) :
    pairForm k n d (-u) (-u) = pairForm k n d u u := by
  simp only [pairForm, neg_dotProduct, dotProduct_neg, neg_neg, neg_mul_neg]

/-- Every vector or its negative is in one of the four octants of `z ≥ 0`. -/
theorem exists_octant (u : Fin 3 → ℝ) : ∃ s₁ ∈ ({1, -1} : Set ℝ), ∃ s₂ ∈ ({1, -1} : Set ℝ),
    InCone ![s₁, 0, 0] ![0, s₂, 0] ![0, 0, 1] u ∨
      InCone ![s₁, 0, 0] ![0, s₂, 0] ![0, 0, 1] (-u) := by
  -- a vector with `z ≥ 0` is in the octant of the signs of its other coordinates
  have key : ∀ v : Fin 3 → ℝ, 0 ≤ v 2 → ∃ s₁ ∈ ({1, -1} : Set ℝ), ∃ s₂ ∈ ({1, -1} : Set ℝ),
      InCone ![s₁, 0, 0] ![0, s₂, 0] ![0, 0, 1] v := by
    intro v hv
    have hs : ∀ t : ℝ, ∃ s ∈ ({1, -1} : Set ℝ), t = |t| * s := fun t ↦ by
      rcases le_total 0 t with h | h
      · exact ⟨1, by simp, by rw [abs_of_nonneg h, mul_one]⟩
      · exact ⟨-1, by simp, by rw [abs_of_nonpos h]; ring⟩
    obtain ⟨s₁, hs₁, e₁⟩ := hs (v 0)
    obtain ⟨s₂, hs₂, e₂⟩ := hs (v 1)
    refine ⟨s₁, hs₁, s₂, hs₂, |v 0|, |v 1|, v 2, abs_nonneg _, abs_nonneg _, hv, ?_⟩
    ext i
    fin_cases i <;> simp [← e₁, ← e₂]
  rcases le_total 0 (u 2) with h | h
  · obtain ⟨s₁, hs₁, s₂, hs₂, hc⟩ := key u h
    exact ⟨s₁, hs₁, s₂, hs₂, Or.inl hc⟩
  · obtain ⟨s₁, hs₁, s₂, hs₂, hc⟩ := key (-u) (by simpa using h)
    exact ⟨s₁, hs₁, s₂, hs₂, Or.inr hc⟩

namespace Check

namespace Diam

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- A node of a cover (module docs), as in `rupert::proof::diameter::Node`. -/
inductive Node (κ : Type) where
  /-- A leaf: the pair of the points with these indices. -/
  | pair (a b : ℕ)
  /-- A split, with its three coefficients. -/
  | split (a₀ a₁ a₂ : κ)

/-- A cone: its three generators. -/
structure Cone (κ : Type) where
  /-- The first generator. -/
  w₀ : V3 κ
  /-- The second generator. -/
  w₁ : V3 κ
  /-- The third generator. -/
  w₂ : V3 κ

/-- The points of a cone. -/
def Cone.Mem (C : Cone κ) (u : Fin 3 → ℝ) : Prop :=
  InCone (Exact.reV C.w₀) (Exact.reV C.w₁) (Exact.reV C.w₂) u

/-- The octant `C(s₁ e₁, s₂ e₂, e₃)`. -/
def octant (s₁ s₂ : ℤ) : Cone κ :=
  ⟨⟨Exact.ofInt s₁, Exact.ofInt 0, Exact.ofInt 0⟩, ⟨Exact.ofInt 0, Exact.ofInt s₂, Exact.ofInt 0⟩,
    ⟨Exact.ofInt 0, Exact.ofInt 0, Exact.ofInt 1⟩⟩

/-- The four octants of `z ≥ 0`, in the order of a cover. -/
def octants : List (Cone κ) :=
  [octant 1 1, octant (-1) 1, octant 1 (-1), octant (-1) (-1)]

/-- The coefficient `k = n2 |d|² - m` of a pair with difference `d`. -/
def coeff (n2 m : κ) (d : V3 κ) : κ :=
  n2 * d.dot d - m

/-- The value `B(x, y)` of the pair with difference `d` (`pairForm`). -/
def form (n2 m : κ) (d x y : V3 κ) : κ :=
  coeff n2 m d * x.dot y - n2 * (d.dot x * d.dot y)

/-- The test of a leaf: the points exist and the six values are `≥ 0`. -/
def leafOk (pts : List (V3 κ)) (n2 m : κ) (a b : ℕ) (C : Cone κ) : Bool :=
  match pts[a]?, pts[b]? with
  | some va, some vb =>
    let d := va.sub vb
    Exact.nonneg (form n2 m d C.w₀ C.w₀) && Exact.nonneg (form n2 m d C.w₀ C.w₁) &&
      Exact.nonneg (form n2 m d C.w₀ C.w₂) && Exact.nonneg (form n2 m d C.w₁ C.w₁) &&
      Exact.nonneg (form n2 m d C.w₁ C.w₂) && Exact.nonneg (form n2 m d C.w₂ C.w₂)
  | _, _ => false

/-- The test of a split's coefficients: each positive or zero, one positive. -/
def splitOk (a₀ a₁ a₂ : κ) : Bool :=
  (Exact.pos a₀ || Exact.isZero a₀) && (Exact.pos a₁ || Exact.isZero a₁) &&
    (Exact.pos a₂ || Exact.isZero a₂) && (Exact.pos a₀ || Exact.pos a₁ || Exact.pos a₂)

/-- The point `p = a₀ w₀ + a₁ w₁ + a₂ w₂` of a split. -/
def splitPoint (a₀ a₁ a₂ : κ) (C : Cone κ) : V3 κ :=
  ((V3.smul a₀ C.w₀).add (V3.smul a₁ C.w₁)).add (V3.smul a₂ C.w₂)

/-- The children of a split: `p` in place of each generator with a positive coefficient, in
order. -/
def kids (a₀ a₁ a₂ : κ) (C : Cone κ) : List (Cone κ) :=
  (if Exact.pos a₀ then [⟨splitPoint a₀ a₁ a₂ C, C.w₁, C.w₂⟩] else []) ++
    ((if Exact.pos a₁ then [⟨C.w₀, splitPoint a₀ a₁ a₂ C, C.w₂⟩] else []) ++
      (if Exact.pos a₂ then [⟨C.w₀, C.w₁, splitPoint a₀ a₁ a₂ C⟩] else []))

/-- The walk of a run of nodes of a cover: the nodes in depth-first order against the cones still
to cover, the next one first. Every node needs a cone; the result is the cones left. -/
def walk (pts : List (V3 κ)) (n2 m : κ) : List (Node κ) → List (Cone κ) → Option (List (Cone κ))
  | [], stack => some stack
  | _ :: _, [] => none
  | .pair a b :: rest, C :: stack =>
    if leafOk pts n2 m a b C then walk pts n2 m rest stack else none
  | .split a₀ a₁ a₂ :: rest, C :: stack =>
    if splitOk a₀ a₁ a₂ then walk pts n2 m rest (kids a₀ a₁ a₂ C ++ stack) else none

/-- Two vectors with the same coordinates. -/
def sameV (x y : V3 κ) : Bool :=
  Exact.isZero (x.x - y.x) && Exact.isZero (x.y - y.y) && Exact.isZero (x.z - y.z)

/-- Two cones with the same generators. -/
def Cone.same (C D : Cone κ) : Bool :=
  sameV C.w₀ D.w₀ && sameV C.w₁ D.w₁ && sameV C.w₂ D.w₂

/-- Two lists of the same cones. -/
def sameCones : List (Cone κ) → List (Cone κ) → Bool
  | [], [] => true
  | C :: cs, D :: ds => C.same D && sameCones cs ds
  | _, _ => false

/-- **A part of a cover**: the nodes take the cones `stack` still to cover to the cones `left`.
A whole cover takes the octants to no cone. -/
def part (pts : List (V3 κ)) (n2 m : κ) (nodes : List (Node κ)) (stack left : List (Cone κ)) :
    Bool :=
  match walk pts n2 m nodes stack with
  | some l => sameCones l left
  | none => false

/-- No two points are farther apart than `√D2`. -/
def diamOk (pts : List (V3 κ)) (D2 : κ) : Bool :=
  pts.all fun x ↦ pts.all fun y ↦ Exact.nonneg (D2 - (x.sub y).dot (x.sub y))

/-- The coefficient `n2 = num²` of the forms at the scale `Θ = num / den`. -/
def formN (Θ : Scale κ) : κ :=
  Θ.num * Θ.num

/-- The coefficient `m = den² D2` of the forms at the scale `Θ = num / den`. -/
def formM (Θ : Scale κ) (D2 : κ) : κ :=
  Exact.ofInt ((Θ.den * Θ.den : ℕ) : ℤ) * D2

/-- The scale `Θ = num / den` is positive and `D2` bounds the squared distances of the points. -/
def head (pts : List (V3 κ)) (Θ : Scale κ) (D2 : κ) : Bool :=
  decide (0 < Θ.den) && Exact.pos Θ.num && diamOk pts D2

/-- **The check of a diameter cover** at the scale `Θ = num / den > 0` in one evaluation: `D2`
bounds the squared distances of the points, and the nodes cover the four octants with the forms
of `n2 = num²`, `m = den² D2`. -/
def check (pts : List (V3 κ)) (Θ : Scale κ) (D2 : κ) (nodes : List (Node κ)) : Bool :=
  head pts Θ D2 && part pts (formN Θ) (formM Θ D2) nodes octants []

/-- A direction with a pair of the points whose form is `≥ 0` there. -/
def Good (pts : List (V3 κ)) (n2 m : κ) (u : Fin 3 → ℝ) : Prop :=
  ∃ va ∈ pts, ∃ vb ∈ pts, 0 ≤ pairForm (Exact.re (coeff n2 m (va.sub vb))) (Exact.re n2)
    (Exact.reV va - Exact.reV vb) u u

/-- A cone every point of which has a pair whose form is `≥ 0` there. -/
def Cone.Covered (pts : List (V3 κ)) (n2 m : κ) (C : Cone κ) : Prop :=
  ∀ u, C.Mem u → Good pts n2 m u

/-- **A diameter cover** at the scale `Θ = num / den > 0`: `D2` bounds the squared distances of
the points, and the four octants are covered with the forms of `n2 = num²`, `m = den² D2`. -/
def Cover (pts : List (V3 κ)) (Θ : Scale κ) (D2 : κ) : Prop :=
  head pts Θ D2 = true ∧
    ∀ C ∈ (octants : List (Cone κ)), C.Covered pts (formN Θ) (formM Θ D2)

theorem re_form (n2 m : κ) (d x y : V3 κ) :
    Exact.re (form n2 m d x y) =
      pairForm (Exact.re (coeff n2 m d)) (Exact.re n2) (Exact.reV d) (Exact.reV x)
        (Exact.reV y) := by
  simp only [form, pairForm, Exact.re_sub, Exact.re_mul, Exact.re_dot]

theorem leafOk_sound {pts : List (V3 κ)} {n2 m : κ} {a b : ℕ} {C : Cone κ}
    (h : leafOk pts n2 m a b C = true) {u : Fin 3 → ℝ} (hu : C.Mem u) : Good pts n2 m u := by
  unfold leafOk at h
  split at h
  · rename_i va vb ha hb
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨h00, h01⟩, h02⟩, h11⟩, h12⟩, h22⟩ := h
    refine ⟨va, List.mem_of_getElem? ha, vb, List.mem_of_getElem? hb, ?_⟩
    rw [← Exact.reV_sub]
    have f := fun x y (hxy : Exact.nonneg (form n2 m (va.sub vb) x y) = true) ↦
      (re_form n2 m (va.sub vb) x y) ▸ Exact.nonneg_sound _ hxy
    exact pairForm_cone_nonneg (f _ _ h00) (f _ _ h01) (f _ _ h02) (f _ _ h11) (f _ _ h12)
      (f _ _ h22) hu
  · exact absurd h (by simp)

theorem reV_splitPoint (a₀ a₁ a₂ : κ) (C : Cone κ) :
    Exact.reV (splitPoint a₀ a₁ a₂ C) = Exact.re a₀ • Exact.reV C.w₀ +
      Exact.re a₁ • Exact.reV C.w₁ + Exact.re a₂ • Exact.reV C.w₂ := by
  simp only [splitPoint, Exact.reV_add, Exact.reV_smul]

/-- A coefficient that passes its test is positive when `pos` says so and zero otherwise. -/
private theorem coeff_cases {a : κ} (h : (Exact.pos a || Exact.isZero a) = true) :
    (Exact.pos a = true ∧ 0 < Exact.re a) ∨ (Exact.pos a = false ∧ Exact.re a = 0) := by
  cases hp : Exact.pos a
  · rw [hp, Bool.false_or] at h
    exact Or.inr ⟨rfl, Exact.isZero_sound _ h⟩
  · exact Or.inl ⟨rfl, Exact.pos_sound _ hp⟩

theorem kids_cover {a₀ a₁ a₂ : κ} (h : splitOk a₀ a₁ a₂ = true) {C : Cone κ} {u : Fin 3 → ℝ}
    (hu : C.Mem u) : ∃ K ∈ kids a₀ a₁ a₂ C, K.Mem u := by
  simp only [splitOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, hp⟩ := h
  have c0 := coeff_cases h0
  have c1 := coeff_cases h1
  have c2 := coeff_cases h2
  have n0 : 0 ≤ Exact.re a₀ := by rcases c0 with ⟨_, h⟩ | ⟨_, h⟩ <;> linarith
  have n1 : 0 ≤ Exact.re a₁ := by rcases c1 with ⟨_, h⟩ | ⟨_, h⟩ <;> linarith
  have n2 : 0 ≤ Exact.re a₂ := by rcases c2 with ⟨_, h⟩ | ⟨_, h⟩ <;> linarith
  have hpos : 0 < Exact.re a₀ ∨ 0 < Exact.re a₁ ∨ 0 < Exact.re a₂ := by
    simp only [Bool.or_eq_true] at hp
    rcases hp with (hp | hp) | hp
    · exact Or.inl (Exact.pos_sound _ hp)
    · exact Or.inr (Or.inl (Exact.pos_sound _ hp))
    · exact Or.inr (Or.inr (Exact.pos_sound _ hp))
  have key := InCone.split hu n0 n1 n2 hpos
  rw [← reV_splitPoint] at key
  rcases key with ⟨hp0, hc⟩ | ⟨hp1, hc⟩ | ⟨hp2, hc⟩
  · have e : Exact.pos a₀ = true := by
      rcases c0 with ⟨e, _⟩ | ⟨_, e⟩
      · exact e
      · linarith
    exact ⟨⟨splitPoint a₀ a₁ a₂ C, C.w₁, C.w₂⟩, by simp [kids, e], hc⟩
  · have e : Exact.pos a₁ = true := by
      rcases c1 with ⟨e, _⟩ | ⟨_, e⟩
      · exact e
      · linarith
    exact ⟨⟨C.w₀, splitPoint a₀ a₁ a₂ C, C.w₂⟩, by simp [kids, e], hc⟩
  · have e : Exact.pos a₂ = true := by
      rcases c2 with ⟨e, _⟩ | ⟨_, e⟩
      · exact e
      · linarith
    exact ⟨⟨C.w₀, C.w₁, splitPoint a₀ a₁ a₂ C⟩, by simp [kids, e], hc⟩

/-- **A walk covers its cones** if the cones it leaves are covered: every point of every cone
it started with has a pair whose form is `≥ 0` there. -/
theorem walk_sound {pts : List (V3 κ)} {n2 m : κ} :
    ∀ (nodes : List (Node κ)) (stack left : List (Cone κ)),
      walk pts n2 m nodes stack = some left → (∀ C ∈ left, C.Covered pts n2 m) →
      ∀ C ∈ stack, C.Covered pts n2 m
  | [], stack, left, h, hl, C, hC => by
    rw [walk, Option.some.injEq] at h
    exact hl C (h ▸ hC)
  | _ :: _, [], _, h, _, _, _ => by simp [walk] at h
  | .pair a b :: rest, C₀ :: stack, left, h, hl, C, hC => by
    rw [walk] at h
    split at h
    · rename_i hleaf
      rcases List.mem_cons.mp hC with rfl | hC
      · exact fun u hu ↦ leafOk_sound hleaf hu
      · exact walk_sound rest stack left h hl C hC
    · exact absurd h (by simp)
  | .split a₀ a₁ a₂ :: rest, C₀ :: stack, left, h, hl, C, hC => by
    rw [walk] at h
    split at h
    · rename_i hs
      have ih := walk_sound rest _ left h hl
      rcases List.mem_cons.mp hC with rfl | hC
      · intro u hu
        obtain ⟨K, hK, hKu⟩ := kids_cover hs hu
        exact ih K (List.mem_append_left _ hK) u hKu
      · exact ih C (List.mem_append_right _ hC)
    · exact absurd h (by simp)

theorem sameV_sound {x y : V3 κ} (h : sameV x y = true) : Exact.reV x = Exact.reV y := by
  simp only [sameV, Bool.and_eq_true] at h
  obtain ⟨⟨hx, hy⟩, hz⟩ := h
  have ex := Exact.isZero_sound _ hx
  have ey := Exact.isZero_sound _ hy
  have ez := Exact.isZero_sound _ hz
  rw [Exact.re_sub, sub_eq_zero] at ex ey ez
  ext i
  fin_cases i <;> simp [Exact.reV, V3.map, V3.toFun, ex, ey, ez]

theorem Cone.same_sound {C D : Cone κ} (h : C.same D = true) {u : Fin 3 → ℝ} (hu : C.Mem u) :
    D.Mem u := by
  simp only [Cone.same, Bool.and_eq_true] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  unfold Cone.Mem at hu ⊢
  rwa [← sameV_sound h0, ← sameV_sound h1, ← sameV_sound h2]

theorem covered_of_sameCones {pts : List (V3 κ)} {n2 m : κ} :
    ∀ (l left : List (Cone κ)), sameCones l left = true →
      (∀ D ∈ left, D.Covered pts n2 m) → ∀ C ∈ l, C.Covered pts n2 m
  | [], [], _, _, C, hC => by simp at hC
  | C₀ :: cs, D₀ :: ds, h, hl, C, hC => by
    rw [sameCones, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hC with rfl | hC
    · exact fun u hu ↦ hl D₀ List.mem_cons_self u (Cone.same_sound h.1 hu)
    · exact covered_of_sameCones cs ds h.2 (fun D hD ↦ hl D (List.mem_cons_of_mem _ hD)) C hC
  | [], _ :: _, h, _, _, _ => by simp [sameCones] at h
  | _ :: _, [], h, _, _, _ => by simp [sameCones] at h

/-- **A part that passes covers its cones** if the cones it leaves are covered. -/
theorem part_sound {pts : List (V3 κ)} {n2 m : κ} {nodes : List (Node κ)}
    {stack left : List (Cone κ)} (h : part pts n2 m nodes stack left = true)
    (hl : ∀ C ∈ left, C.Covered pts n2 m) : ∀ C ∈ stack, C.Covered pts n2 m := by
  unfold part at h
  split at h
  · rename_i l hw
    exact walk_sound nodes stack l hw (covered_of_sameCones l left h hl)
  · exact absurd h (by simp)

/-- No cone is left: the end of the parts of a cover. -/
theorem covered_nil {pts : List (V3 κ)} {n2 m : κ} :
    ∀ C ∈ ([] : List (Cone κ)), C.Covered pts n2 m :=
  fun _ h ↦ absurd h List.not_mem_nil

/-- A check that passes is a cover. -/
theorem cover_of_check {pts : List (V3 κ)} {Θ : Scale κ} {D2 : κ} {nodes : List (Node κ)}
    (h : check pts Θ D2 nodes = true) : Cover pts Θ D2 := by
  rw [check, Bool.and_eq_true] at h
  exact ⟨h.1, part_sound h.2 covered_nil⟩

theorem mem_octant {s₁ s₂ : ℤ} {s₁' s₂' : ℝ} (h₁ : (s₁ : ℝ) = s₁') (h₂ : (s₂ : ℝ) = s₂')
    {u : Fin 3 → ℝ} (h : InCone ![s₁', 0, 0] ![0, s₂', 0] ![0, 0, 1] u) :
    (octant s₁ s₂ : Cone κ).Mem u := by
  have e : ∀ a b c : ℤ, Exact.reV (⟨Exact.ofInt a, Exact.ofInt b, Exact.ofInt c⟩ : V3 κ) =
      ![(a : ℝ), b, c] := by
    intro a b c
    ext i
    fin_cases i <;> simp [Exact.reV, V3.map, V3.toFun, Exact.re_ofInt]
  unfold Cone.Mem octant
  rw [e, e, e]
  simpa [h₁, h₂] using h

/-- The scale of a cover is positive. -/
theorem Cover.re_pos {pts : List (V3 κ)} {Θ : Scale κ} {D2 : κ} (h : Cover pts Θ D2) :
    0 < Θ.re := by
  have hh := h.1
  simp only [head, Bool.and_eq_true, decide_eq_true_eq] at hh
  exact div_pos (Exact.pos_sound _ hh.1.2) (by exact_mod_cast hh.1.1)

/-- **A diameter cover**: the polyhedron of the points scaled by `Θ` does not fit through it. -/
theorem Cover.not_fitsThrough {pts : List (V3 κ)} {Θ : Scale κ} {D2 : κ}
    (h : Cover pts Θ D2) :
    ¬ ((Polyhedron.ofPoints pts).smul Θ.re).FitsThrough (Polyhedron.ofPoints pts) := by
  obtain ⟨hhead, hrun⟩ := h
  simp only [head, Bool.and_eq_true, decide_eq_true_eq] at hhead
  obtain ⟨⟨hden, hnum⟩, hdiam⟩ := hhead
  have hS : (0 : ℝ) < Θ.den := by exact_mod_cast hden
  have hN : 0 < Exact.re Θ.num := Exact.pos_sound _ hnum
  refine Polyhedron.not_fitsThrough_smul_of_pairs (D2 := Exact.re D2) ?_ ?_
  · intro x hx y hy
    obtain ⟨vx, hvx, rfl⟩ := Polyhedron.mem_ofPoints.mp hx
    obtain ⟨vy, hvy, rfl⟩ := Polyhedron.mem_ofPoints.mp hy
    have h0 := Exact.nonneg_sound _
      (List.all_eq_true.mp (List.all_eq_true.mp hdiam vx hvx) vy hvy)
    rw [Exact.re_sub, Exact.re_dot, Exact.reV_sub] at h0
    linarith
  · intro u hu
    -- a pair whose form is `≥ 0` at `u`
    have hg : Good pts (formN Θ) (formM Θ D2) u := by
      obtain ⟨s₁, hs₁, s₂, hs₂, hc⟩ := exists_octant u
      have hmem : ∀ v, InCone ![s₁, 0, 0] ![0, s₂, 0] ![0, 0, 1] v →
          Good pts (formN Θ) (formM Θ D2) v := by
        intro v hv
        rcases hs₁ with rfl | rfl <;> rcases hs₂ with rfl | rfl
        · exact hrun (octant 1 1) (by simp [octants]) v
            (mem_octant (by norm_num) (by norm_num) hv)
        · exact hrun (octant 1 (-1)) (by simp [octants]) v
            (mem_octant (by norm_num) (by norm_num) hv)
        · exact hrun (octant (-1) 1) (by simp [octants]) v
            (mem_octant (by norm_num) (by norm_num) hv)
        · exact hrun (octant (-1) (-1)) (by simp [octants]) v
            (mem_octant (by norm_num) (by norm_num) hv)
      rcases hc with hc | hc
      · exact hmem u hc
      · obtain ⟨va, hva, vb, hvb, hq⟩ := hmem (-u) hc
        exact ⟨va, hva, vb, hvb, by rwa [pairForm_neg] at hq⟩
    obtain ⟨va, hva, vb, hvb, hq⟩ := hg
    refine ⟨Exact.reV va, Polyhedron.mem_ofPoints.mpr ⟨va, hva, rfl⟩, Exact.reV vb,
      Polyhedron.mem_ofPoints.mpr ⟨vb, hvb, rfl⟩, ?_⟩
    simp only [pairForm, coeff, formN, formM, Exact.re_sub, Exact.re_mul, Exact.re_dot,
      Exact.re_ofInt, Exact.reV_sub, hu, mul_one] at hq
    push_cast at hq
    rw [Scale.re, div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith

/-- **A passing check of a diameter cover**: the polyhedron of the points scaled by `Θ` does not
fit through it. -/
theorem check_sound {pts : List (V3 κ)} {Θ : Scale κ} {D2 : κ} {nodes : List (Node κ)}
    (h : check pts Θ D2 nodes = true) :
    ¬ ((Polyhedron.ofPoints pts).smul Θ.re).FitsThrough (Polyhedron.ofPoints pts) :=
  (cover_of_check h).not_fitsThrough

end Diam

/-- **Exact Nieuwland numbers from a diameter cover.** For `P = a • (polyhedron of pts)`,
`a ≠ 0`, of full dimension: a diameter cover at the scale `Θ` and a weak fit at `Θ` give
`nieuwland P = Θ`. -/
theorem Polyhedron.nieuwland_eq_of_diameter {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]
    {pts : List (V3 κ)} {Θ : Scale κ} {D2 : κ}
    (hcov : Diam.Cover pts Θ D2) {W : WeakFitData κ} (hW : W.check pts = true)
    (hWn : W.scaleNum = Θ.num) (hWd : W.scaleDen = Θ.den) {P : Polyhedron} {a : ℝ}
    (hP : P = (Polyhedron.ofPoints pts).smul a) (ha : a ≠ 0) (hdim : P.FullDim) :
    P.nieuwland = Θ.re := by
  have hlo : Θ.re ≤ P.nieuwland := by
    have h0 := W.le_nieuwland_smul hW ha hP hdim
    rwa [WeakFitData.scale, hWn, hWd] at h0
  refine le_antisymm ?_ hlo
  subst hP
  rw [Polyhedron.nieuwland_smul ha]
  exact Polyhedron.nieuwland_le_of_not_fitsThrough hcov.re_pos.le hcov.not_fitsThrough

/-- **Exact Nieuwland numbers from a diameter cover over a lift.** As
`Polyhedron.nieuwland_eq_of_diameter`, for `P = a • (polyhedron of ptsF)` and a cover and a weak
fit over points `ptsE` of a lift with `ofPoints ptsE = (ofPoints ptsF).smul c`, `c ≠ 0`
(`ofPoints_of_liftOk`; `c = 1` for a rational solid): the factor changes neither. -/
theorem Polyhedron.nieuwland_eq_of_diameter_lift {κF κE : Type} [Add κF] [Sub κF] [Mul κF]
    [Exact κF] [Add κE] [Sub κE] [Mul κE] [Exact κE] {ptsF : List (V3 κF)}
    {ptsE : List (V3 κE)} {c : ℝ} (hc : c ≠ 0)
    (hpts : Polyhedron.ofPoints ptsE = (Polyhedron.ofPoints ptsF).smul c) {Θ : Scale κE}
    {D2 : κE} (hcov : Diam.Cover ptsE Θ D2)
    {W : WeakFitData κE} (hW : W.check ptsE = true) (hWn : W.scaleNum = Θ.num)
    (hWd : W.scaleDen = Θ.den) {P : Polyhedron} {a : ℝ}
    (hP : P = (Polyhedron.ofPoints ptsF).smul a) (ha : a ≠ 0) (hdim : P.FullDim) :
    P.nieuwland = Θ.re := by
  have hP' : P = (Polyhedron.ofPoints ptsE).smul (a * c⁻¹) := by
    rw [hpts, Polyhedron.smul_smul_eq, inv_mul_cancel_right₀ hc]
    exact hP
  exact Polyhedron.nieuwland_eq_of_diameter hcov hW hWn hWd hP' (mul_ne_zero ha (inv_ne_zero hc))
    hdim

end Check

end Nieuwland
