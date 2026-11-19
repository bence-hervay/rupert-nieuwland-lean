import Modules.Nieuwland.Defs
import Modules.Rupert.FullDim
import Modules.NoFit.Along
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Nieuwland numbers: basic theory

The general facts about `Polyhedron.FitsThrough` and `Polyhedron.nieuwland` that per-solid
results use, all proved once in the kernel.

* **Lemma M** (monotonicity): a fit at scale `c` gives a fit at every scale `0 ≤ c' ≤ c`, with
  the same rotations and the translation `s t + (1 - s) h` (`s = c'/c`, `h` a point of the moved
  shadow): `FitsThrough.smul_of_le`, per pose `exists_shadow_smul_subset_of_le`, and in the form
  of the chunk checks `FitsAlong.smul_of_le` (`P.FitsAlong u (θ • R)` is the fit of `θ R P`).
* **Lemma W** (weak to strict): a weak fit at scale `c` through a full-dimensional hole gives a
  fit at every scale `0 ≤ c' < c` (`WeakFitsThrough.fitsThrough_smul_of_lt`).
* **Openness in the scale**: a fit at `c` gives one at some `c'' > c`, with the same rotations
  and translation (`FitsThrough.exists_lt_smul`).
* **Bounded scales**: if `P.smul c` fits weakly through `Q` and a ball of radius `r` lies in
  `P`, then `c r ≤ 6 C` for `C` a bound of the points of `Q` (`mul_le_of_weakFitsThrough`, by
  the width of the shadows along the first screen axis); so the scales are bounded for a
  full-dimensional `P` (`FullDim.bddAbove_weakFitsThrough`).
* **The Nieuwland number**: for a full-dimensional `P`, `P.smul c` fits through `P` exactly for
  `0 ≤ c < P.nieuwland` (`fitsThrough_smul_iff_lt_nieuwland`); `1 ≤ P.nieuwland`
  (`one_le_nieuwland`), with equality exactly when `P` is not Rupert (`nieuwland_eq_one_iff`).
  The forms used by certificates: `nieuwland_le_of_not_fitsThrough`, `le_nieuwland_of_forall_lt`,
  `le_nieuwland_of_weakFitsThrough`, `nieuwland_eq_of_iff`, `nieuwland_eq_one_of_not_isRupert`.
* **Scaling both copies** changes nothing (`fitsThrough_smul_iff`, `nieuwland_smul`), so exact
  checks may work with the points times a common denominator, as for `Polyhedron.IsRupert`
  (`Polyhedron.isRupert_smul_iff`).
* **Reflections** change nothing either: allowing `O(3)` gives the same `FitsThrough`
  (`fitsThrough_iff_orthogonal`), and a negative scale is the reflected copy
  (`fitsThrough_smul_neg`).
-/

open Matrix Pointwise

namespace Nieuwland

/-! ### Homotheties in the plane -/

/-- **Shrinking in a convex set.** If the points `c • f x + t` (`x ∈ K`) lie in a convex set `S`,
then for `0 ≤ c' ≤ c` the points `c' • f x + t'` do, for `t' = s • t + (1 - s) • h` with
`s = c' / c` and `h` one of the first points. -/
theorem exists_smul_add_mem_of_le {X : Type*} {S : Set (Fin 2 → ℝ)} (hS : Convex ℝ S)
    {K : Set X} {f : X → Fin 2 → ℝ} {t : Fin 2 → ℝ} {c c' : ℝ} (h : ∀ x ∈ K, c • f x + t ∈ S)
    (hc' : 0 ≤ c') (hle : c' ≤ c) : ∃ t' : Fin 2 → ℝ, ∀ x ∈ K, c' • f x + t' ∈ S := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, fun x hx ↦ hx.elim⟩
  rcases hle.lt_or_eq with hlt | rfl
  · have hc : 0 < c := hc'.trans_lt hlt
    have hs0 : 0 ≤ c' / c := div_nonneg hc' hc.le
    have hs1 : c' / c ≤ 1 := (div_le_one hc).mpr hlt.le
    refine ⟨(c' / c) • t + (1 - c' / c) • (c • f x₀ + t), fun x hx ↦ ?_⟩
    have hmem := hS (h x hx) (h x₀ hx₀) hs0 (show (0 : ℝ) ≤ 1 - c' / c by linarith) (by ring)
    convert hmem using 1
    rw [smul_add (c' / c), smul_smul, div_mul_cancel₀ c' hc.ne']
    abel
  · exact ⟨t, h⟩

/-- **Shrinking into the interior.** If the points `c • f x + t` (`x ∈ K`) lie in a convex set
`S` with an interior point `h`, then for `0 ≤ c' < c` the points `c' • f x + t'` lie in the
interior of `S`, for `t' = s • t + (1 - s) • h` with `s = c' / c`. -/
theorem exists_smul_add_mem_interior_of_lt {X : Type*} {S : Set (Fin 2 → ℝ)} (hS : Convex ℝ S)
    {h : Fin 2 → ℝ} (hh : h ∈ interior S) {K : Set X} {f : X → Fin 2 → ℝ} {t : Fin 2 → ℝ}
    {c c' : ℝ} (hK : ∀ x ∈ K, c • f x + t ∈ S) (hc' : 0 ≤ c') (hlt : c' < c) :
    ∃ t' : Fin 2 → ℝ, ∀ x ∈ K, c' • f x + t' ∈ interior S := by
  have hc : 0 < c := hc'.trans_lt hlt
  have hs0 : 0 ≤ c' / c := div_nonneg hc' hc.le
  have hs1 : c' / c < 1 := (div_lt_one hc).mpr hlt
  refine ⟨(c' / c) • t + (1 - c' / c) • h, fun x hx ↦ ?_⟩
  have hmem := hS.combo_self_interior_mem_interior (hK x hx) hh hs0
    (show (0 : ℝ) < 1 - c' / c by linarith) (by ring)
  convert hmem using 1
  rw [smul_add (c' / c), smul_smul, div_mul_cancel₀ c' hc.ne']
  abel

/-- **Growing in an open set.** If the points `c • f x + t` of a compact set `K` lie in an open
set `U` and `f` is continuous, then for some `c'' > c` the points `c'' • f x + t` do too. -/
theorem exists_lt_smul_add_mem {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {f : X → Fin 2 → ℝ} (hf : Continuous f) {U : Set (Fin 2 → ℝ)} (hU : IsOpen U)
    {t : Fin 2 → ℝ} {c : ℝ} (h : ∀ x ∈ K, c • f x + t ∈ U) :
    ∃ c'' > c, ∀ x ∈ K, c'' • f x + t ∈ U := by
  have hA : IsCompact (Set.image (fun x ↦ c • f x + t) K) :=
    hK.image ((hf.const_smul c).add continuous_const)
  obtain ⟨δ, hδ, hsub⟩ := hA.exists_thickening_subset_open hU (by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx)
  obtain ⟨M, hM⟩ := (hK.image hf).isBounded.exists_norm_le
  have hM₁ : 0 < max M 0 + 1 := by positivity
  refine ⟨c + δ / (max M 0 + 1), by linarith [div_pos hδ hM₁], fun x hx ↦ hsub ?_⟩
  refine Metric.mem_thickening_iff.mpr ⟨c • f x + t, ⟨x, hx, rfl⟩, ?_⟩
  have hfx : ‖f x‖ ≤ max M 0 := (hM _ ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  rw [dist_eq_norm, add_smul, add_sub_add_right_eq_sub, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg (div_pos hδ hM₁).le]
  calc δ / (max M 0 + 1) * ‖f x‖ ≤ δ / (max M 0 + 1) * max M 0 :=
        mul_le_mul_of_nonneg_left hfx (div_pos hδ hM₁).le
    _ < δ / (max M 0 + 1) * (max M 0 + 1) := mul_lt_mul_of_pos_left (lt_add_one _) (div_pos hδ hM₁)
    _ = δ := div_mul_cancel₀ δ hM₁.ne'

/-! ### Orthogonal matrices -/

/-- The squares of a row of an orthogonal matrix sum to `1`. -/
theorem sum_mul_self_of_mem_orthogonalGroup {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ O(3))
    (i : Fin 3) : ∑ j, R i j * R i j = 1 := by
  have h := congrFun (congrFun (mul_transpose_of_mem_orthogonalGroup hR) i) i
  simpa [Matrix.mul_apply] using h

/-- The entries of an orthogonal matrix lie in `[-1, 1]`. -/
theorem abs_le_one_of_mem_orthogonalGroup {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ O(3))
    (i j : Fin 3) : |R i j| ≤ 1 := by
  rw [abs_le_one_iff_mul_self_le_one, ← sum_mul_self_of_mem_orthogonalGroup hR i]
  exact Finset.single_le_sum (fun k _ ↦ mul_self_nonneg (R i k)) (Finset.mem_univ j)

/-- The half-turn `diag(-1, -1, 1)` about the `z`-axis. It negates every shadow. -/
def halfTurnZ : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal ![-1, -1, 1]

theorem halfTurnZ_mem : halfTurnZ ∈ SO(3) := by
  rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff, halfTurnZ, diagonal_transpose,
    diagonal_mul_diagonal, ← diagonal_one]
  refine ⟨congrArg diagonal ?_, ?_⟩
  · ext i; fin_cases i <;> norm_num
  · simp [det_diagonal, Fin.prod_univ_three]

theorem projXY_halfTurnZ_mulVec (x : Fin 3 → ℝ) : projXY (halfTurnZ *ᵥ x) = -projXY x := by
  ext i; fin_cases i <;> simp [projXY, halfTurnZ, mulVec_diagonal]

namespace Polyhedron

/-! ### Scaled polyhedra and their shadows -/

theorem hull_smul (c : ℝ) (P : Polyhedron) : (P.smul c).hull = c • P.hull := by
  classical
  rw [hull, hull, ← convexHull_smul]
  congr 1
  simp only [Polyhedron.smul, Finset.coe_image, Set.image_smul]

theorem smul_one (P : Polyhedron) : P.smul 1 = P := by
  classical
  cases P with
  | mk V => simp only [Polyhedron.smul, one_smul, Finset.image_id']

theorem smul_smul_eq (a c : ℝ) (P : Polyhedron) : (P.smul a).smul c = P.smul (c * a) := by
  classical
  simp only [Polyhedron.smul, Finset.image_image]
  congr 2
  funext v
  simp [smul_smul]

theorem smul_comm_smul (a c : ℝ) (P : Polyhedron) : (P.smul a).smul c = (P.smul c).smul a := by
  rw [smul_smul_eq, smul_smul_eq, mul_comm]

theorem isCompact_hull (P : Polyhedron) : IsCompact P.hull :=
  P.vertices.finite_toSet.isCompact_convexHull ℝ

/-- The shadow of a polyhedron is convex. -/
theorem convex_shadow (P : Polyhedron) (R : Matrix (Fin 3) (Fin 3) ℝ) :
    Convex ℝ {projXY (R *ᵥ x) | x ∈ P.hull} :=
  (convex_convexHull ℝ _).linear_image (projXYₗ ∘ₗ R.mulVecLin)

/-- The moved shadow of a scaled polyhedron is the scaled shadow, moved. -/
theorem shadow_smul (c : ℝ) (P : Polyhedron) (R : Matrix (Fin 3) (Fin 3) ℝ) (t : Fin 2 → ℝ) :
    {projXY (R *ᵥ x) + t | x ∈ (P.smul c).hull} = {c • projXY (R *ᵥ x) + t | x ∈ P.hull} := by
  rw [hull_smul]
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by rw [projXY_mulVec_smul]⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨c • x, Set.smul_mem_smul_set hx, by rw [projXY_mulVec_smul]⟩

/-- The shadow of a scaled polyhedron is the scaled shadow. -/
theorem shadow_hull_smul (c : ℝ) (P : Polyhedron) (R : Matrix (Fin 3) (Fin 3) ℝ) :
    {projXY (R *ᵥ x) | x ∈ (P.smul c).hull} = c • {projXY (R *ᵥ x) | x ∈ P.hull} := by
  rw [hull_smul]
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, (projXY_mulVec_smul R c x).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨c • x, Set.smul_mem_smul_set hx, projXY_mulVec_smul R c x⟩

/-- The moved shadow of a scaled polyhedron, moved by a scaled translation, is the scaled moved
shadow. -/
theorem shadow_smul_add_smul (c : ℝ) (P : Polyhedron) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (t : Fin 2 → ℝ) :
    {projXY (R *ᵥ x) + c • t | x ∈ (P.smul c).hull} = c • {projXY (R *ᵥ x) + t | x ∈ P.hull} := by
  rw [shadow_smul]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, smul_add c _ t⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (smul_add c _ t).symm⟩

/-- The shadow of a full-dimensional polyhedron has interior points. -/
theorem interior_shadow_nonempty {P : Polyhedron} (hP : P.FullDim)
    {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ O(3)) :
    (interior {projXY (R *ᵥ x) | x ∈ P.hull}).Nonempty := by
  obtain ⟨p, hp⟩ := hP
  have hg : IsOpenMap (projXYₗ ∘ₗ R.mulVecLin) :=
    (projXYₗ ∘ₗ R.mulVecLin).isOpenMap_of_finiteDimensional (projXY_mulVec_surjective hR)
  exact ⟨_, hg.image_interior_subset P.hull ⟨p, hp, rfl⟩⟩

/-! ### Strict and weak fits -/

theorem FitsThrough.weakFitsThrough {P Q : Polyhedron} (h : P.FitsThrough Q) :
    P.WeakFitsThrough Q := by
  obtain ⟨R₁, hR₁, R₂, hR₂, t, h⟩ := h
  exact ⟨R₁, hR₁, R₂, hR₂, t, h.trans interior_subset⟩

/-- Every polyhedron fits weakly through itself: no rotation, no translation. -/
theorem weakFitsThrough_self (P : Polyhedron) : P.WeakFitsThrough P :=
  ⟨1, one_mem _, 1, one_mem _, 0, by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, by rw [add_zero]⟩⟩

/-- **Lemma M, per pose.** If the shadow of `R₁ (c P)`, moved by `t`, lies in the interior of the
shadow of `R₂ Q`, then for `0 ≤ c' ≤ c` some translate of the shadow of `R₁ (c' P)` does too. -/
theorem exists_shadow_smul_subset_of_le {P Q : Polyhedron} {R₁ R₂ : Matrix (Fin 3) (Fin 3) ℝ}
    {t : Fin 2 → ℝ} {c c' : ℝ}
    (h : {projXY (R₁ *ᵥ x) + t | x ∈ (P.smul c).hull} ⊆ interior {projXY (R₂ *ᵥ x) | x ∈ Q.hull})
    (hc' : 0 ≤ c') (hle : c' ≤ c) :
    ∃ t', {projXY (R₁ *ᵥ x) + t' | x ∈ (P.smul c').hull} ⊆
      interior {projXY (R₂ *ᵥ x) | x ∈ Q.hull} := by
  rw [shadow_smul] at h
  obtain ⟨t', ht'⟩ := exists_smul_add_mem_of_le (Q.convex_shadow R₂).interior
    (fun x hx ↦ h ⟨x, hx, rfl⟩) hc' hle
  refine ⟨t', ?_⟩
  rw [shadow_smul]
  rintro _ ⟨x, hx, rfl⟩
  exact ht' x hx

/-- **Lemma M.** A fit of `P` scaled by `c` through `Q` gives a fit at every scale
`0 ≤ c' ≤ c`, with the same rotations. -/
theorem FitsThrough.smul_of_le {P Q : Polyhedron} {c c' : ℝ} (h : (P.smul c).FitsThrough Q)
    (hc' : 0 ≤ c') (hle : c' ≤ c) : (P.smul c').FitsThrough Q := by
  obtain ⟨R₁, hR₁, R₂, hR₂, t, h⟩ := h
  obtain ⟨t', h'⟩ := exists_shadow_smul_subset_of_le h hc' hle
  exact ⟨R₁, hR₁, R₂, hR₂, t', h'⟩

/-- **Lemma M for weak fits.** -/
theorem WeakFitsThrough.smul_of_le {P Q : Polyhedron} {c c' : ℝ}
    (h : (P.smul c).WeakFitsThrough Q) (hc' : 0 ≤ c') (hle : c' ≤ c) :
    (P.smul c').WeakFitsThrough Q := by
  obtain ⟨R₁, hR₁, R₂, hR₂, t, h⟩ := h
  rw [shadow_smul] at h
  obtain ⟨t', ht'⟩ := exists_smul_add_mem_of_le (Q.convex_shadow R₂)
    (fun x hx ↦ h ⟨x, hx, rfl⟩) hc' hle
  refine ⟨R₁, hR₁, R₂, hR₂, t', ?_⟩
  rw [shadow_smul]
  rintro _ ⟨x, hx, rfl⟩
  exact ht' x hx

/-- **Lemma M along a view direction**, the form of the chunk checks: `P.FitsAlong u (θ • R)` is
the fit of `θ R P` in `P`, and it holds at every `0 ≤ θ' ≤ θ` once it holds at `θ`. -/
theorem FitsAlong.smul_of_le {P : Polyhedron} {u : Fin 3 → ℝ} {R : Matrix (Fin 3) (Fin 3) ℝ}
    {θ θ' : ℝ} (h : P.FitsAlong u (θ • R)) (hθ' : 0 ≤ θ') (hle : θ' ≤ θ) :
    P.FitsAlong u (θ' • R) := by
  obtain ⟨L, hL, hker, τ, hτ⟩ := h
  have hS : Convex ℝ (interior {L x | x ∈ P.hull}) :=
    ((convex_convexHull ℝ _).linear_image L).interior
  obtain ⟨τ', hτ'⟩ := exists_smul_add_mem_of_le hS (K := P.hull) (f := fun x ↦ L (R *ᵥ x))
    (t := τ) (c := θ) (fun x hx ↦ by simpa only [smul_mulVec, map_smul] using hτ ⟨x, hx, rfl⟩)
    hθ' hle
  refine ⟨L, hL, hker, τ', ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  simpa only [smul_mulVec, map_smul] using hτ' x hx

/-- **Lemma W.** A weak fit of `P` scaled by `c` through a full-dimensional `Q` gives a fit at
every scale `0 ≤ c' < c`: shrink towards an interior point of the hole's shadow. -/
theorem WeakFitsThrough.fitsThrough_smul_of_lt {P Q : Polyhedron} {c c' : ℝ}
    (h : (P.smul c).WeakFitsThrough Q) (hQ : Q.FullDim) (hc' : 0 ≤ c') (hlt : c' < c) :
    (P.smul c').FitsThrough Q := by
  obtain ⟨R₁, hR₁, R₂, hR₂, t, h⟩ := h
  rw [shadow_smul] at h
  obtain ⟨h₀, hh₀⟩ := interior_shadow_nonempty hQ hR₂.1
  obtain ⟨t', ht'⟩ := exists_smul_add_mem_interior_of_lt (Q.convex_shadow R₂) hh₀
    (fun x hx ↦ h ⟨x, hx, rfl⟩) hc' hlt
  refine ⟨R₁, hR₁, R₂, hR₂, t', ?_⟩
  rw [shadow_smul]
  rintro _ ⟨x, hx, rfl⟩
  exact ht' x hx

/-- A full-dimensional polyhedron scaled by `0 ≤ c < 1` fits through itself (`R₁ = R₂ = 1`, shrunk
towards an interior point). -/
theorem fitsThrough_smul_of_lt_one {P : Polyhedron} (hP : P.FullDim) {c : ℝ} (hc : 0 ≤ c)
    (h1 : c < 1) : (P.smul c).FitsThrough P := by
  have h : (P.smul 1).WeakFitsThrough P := by
    rw [smul_one]
    exact weakFitsThrough_self P
  exact h.fitsThrough_smul_of_lt hP hc h1

/-- **Openness in the scale.** A fit of `P` scaled by `c` through `Q` gives a fit at some larger
scale, with the same rotations and translation. -/
theorem FitsThrough.exists_lt_smul {P Q : Polyhedron} {c : ℝ} (h : (P.smul c).FitsThrough Q) :
    ∃ c'' > c, (P.smul c'').FitsThrough Q := by
  obtain ⟨R₁, hR₁, R₂, hR₂, t, h⟩ := h
  rw [shadow_smul] at h
  obtain ⟨c'', hc'', h''⟩ := exists_lt_smul_add_mem P.isCompact_hull
    (f := fun x ↦ projXY (R₁ *ᵥ x))
    (projXYₗ ∘ₗ R₁.mulVecLin).continuous_of_finiteDimensional isOpen_interior
    (fun x hx ↦ h ⟨x, hx, rfl⟩)
  refine ⟨c'', hc'', R₁, hR₁, R₂, hR₂, t, ?_⟩
  rw [shadow_smul]
  rintro _ ⟨x, hx, rfl⟩
  exact h'' x hx

/-! ### Bounded scales -/

/-- **Width bound.** If the ball of radius `r > 0` about `p` lies in the hull of `P`, the points of
the hull of `Q` have norm at most `C` (sup norms), and `P` scaled by `c` fits weakly through `Q`,
then `c * r ≤ 6 * C`. The plug's shadow has width `r c` along the first screen axis (the first
row of `R₁` is a unit vector `v`, and `p ± (r/2) v` lie in `P`), and the hole's shadow has width at
most `6 C` along it. -/
theorem mul_le_of_weakFitsThrough {P Q : Polyhedron} {p : Fin 3 → ℝ} {r C c : ℝ} (hr : 0 < r)
    (hball : Metric.ball p r ⊆ P.hull) (hC : ∀ y ∈ Q.hull, ‖y‖ ≤ C)
    (h : (P.smul c).WeakFitsThrough Q) : c * r ≤ 6 * C := by
  obtain ⟨R₁, hR₁, R₂, hR₂, t, h⟩ := h
  rw [shadow_smul] at h
  have hvn : ‖(r / 2) • R₁ 0‖ < r := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have : ‖R₁ 0‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j ↦ by
      rw [Real.norm_eq_abs]
      exact abs_le_one_of_mem_orthogonalGroup hR₁.1 0 j
    calc r / 2 * ‖R₁ 0‖ ≤ r / 2 * 1 := mul_le_mul_of_nonneg_left this (by positivity)
      _ < r := by linarith
  have hx₁ : p + (r / 2) • R₁ 0 ∈ P.hull := hball (by rwa [Metric.mem_ball, dist_self_add_left])
  have hx₂ : p - (r / 2) • R₁ 0 ∈ P.hull := hball (by
    rwa [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg])
  obtain ⟨y₁, hy₁, e₁⟩ := h ⟨_, hx₁, rfl⟩
  obtain ⟨y₂, hy₂, e₂⟩ := h ⟨_, hx₂, rfl⟩
  have key (R : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) :
      projXY (R *ᵥ x) 0 = R 0 0 * x 0 + R 0 1 * x 1 + R 0 2 * x 2 := by
    simp [projXY, mulVec, dotProduct, Fin.sum_univ_three]
  have k₁ := congrFun e₁ 0
  have k₂ := congrFun e₂ 0
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, key] at k₁ k₂
  have hrow := sum_mul_self_of_mem_orthogonalGroup hR₁.1 0
  rw [Fin.sum_univ_three] at hrow
  have hdiff : R₂ 0 0 * (y₁ 0 - y₂ 0) + R₂ 0 1 * (y₁ 1 - y₂ 1) + R₂ 0 2 * (y₁ 2 - y₂ 2) =
      c * r := by
    linear_combination k₁ - k₂ + c * r * hrow
  have hb (j : Fin 3) : R₂ 0 j * (y₁ j - y₂ j) ≤ 2 * C := by
    have h₁ : |y₁ j| ≤ C := by
      have := norm_le_pi_norm y₁ j
      rw [Real.norm_eq_abs] at this
      exact this.trans (hC y₁ hy₁)
    have h₂ : |y₂ j| ≤ C := by
      have := norm_le_pi_norm y₂ j
      rw [Real.norm_eq_abs] at this
      exact this.trans (hC y₂ hy₂)
    calc R₂ 0 j * (y₁ j - y₂ j) ≤ |R₂ 0 j| * |y₁ j - y₂ j| := by
          rw [← abs_mul]; exact le_abs_self _
      _ ≤ 1 * (|y₁ j| + |y₂ j|) := by
          gcongr
          exacts [abs_le_one_of_mem_orthogonalGroup hR₂.1 0 j, abs_sub _ _]
      _ ≤ 2 * C := by linarith
  linarith [hb 0, hb 1, hb 2]

/-- **Bounded scales.** The scales at which a full-dimensional `P` fits weakly through `Q` are
bounded above. -/
theorem FullDim.bddAbove_weakFitsThrough {P : Polyhedron} (hP : P.FullDim) (Q : Polyhedron) :
    BddAbove {c : ℝ | (P.smul c).WeakFitsThrough Q} := by
  obtain ⟨p, hp⟩ := hP
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hp
  obtain ⟨C, hC⟩ := Q.isCompact_hull.isBounded.exists_norm_le
  exact ⟨6 * C / r, fun c hc ↦
    (le_div_iff₀ hr).mpr (mul_le_of_weakFitsThrough hr (hball.trans interior_subset) hC hc)⟩

/-- The scales of `nieuwland P` are bounded above for a full-dimensional `P`. -/
theorem FullDim.bddAbove_fitsThrough {P : Polyhedron} (hP : P.FullDim) :
    BddAbove {c : ℝ | 0 < c ∧ (P.smul c).FitsThrough P} :=
  (hP.bddAbove_weakFitsThrough P).mono fun _ hc ↦ hc.2.weakFitsThrough

/-! ### The Nieuwland number -/

theorem nieuwland_nonneg (P : Polyhedron) : 0 ≤ P.nieuwland :=
  Real.sSup_nonneg fun _ hc ↦ hc.1.le

/-- Below the Nieuwland number, `P` scaled by `c` fits through `P`. -/
theorem fitsThrough_smul_of_lt_nieuwland {P : Polyhedron} {c : ℝ} (hc : 0 ≤ c)
    (h : c < P.nieuwland) : (P.smul c).FitsThrough P := by
  have hne : {c : ℝ | 0 < c ∧ (P.smul c).FitsThrough P}.Nonempty := by
    by_contra he
    rw [Set.not_nonempty_iff_eq_empty] at he
    rw [nieuwland, he, Real.sSup_empty] at h
    linarith
  obtain ⟨c'', ⟨-, hfit⟩, hlt⟩ := exists_lt_of_lt_csSup hne h
  exact hfit.smul_of_le hc hlt.le

/-- A fit at a scale `c > 0` bounds the Nieuwland number of a full-dimensional `P` below. -/
theorem le_nieuwland_of_fitsThrough {P : Polyhedron} (hP : P.FullDim) {c : ℝ} (hc : 0 < c)
    (h : (P.smul c).FitsThrough P) : c ≤ P.nieuwland :=
  le_csSup hP.bddAbove_fitsThrough ⟨hc, h⟩

/-- **The Nieuwland number.** For a full-dimensional `P` and `c ≥ 0`, `P` scaled by `c` fits
through `P` exactly when `c < P.nieuwland`: the scales with a fit are `[0, nieuwland P)`. -/
theorem fitsThrough_smul_iff_lt_nieuwland {P : Polyhedron} (hP : P.FullDim) {c : ℝ}
    (hc : 0 ≤ c) : (P.smul c).FitsThrough P ↔ c < P.nieuwland := by
  refine ⟨fun h ↦ ?_, fitsThrough_smul_of_lt_nieuwland hc⟩
  obtain ⟨c'', hc'', h''⟩ := h.exists_lt_smul
  exact hc''.trans_le (le_nieuwland_of_fitsThrough hP (hc.trans_lt hc'') h'')

/-- At its Nieuwland number, a full-dimensional `P` does not fit through itself. -/
theorem not_fitsThrough_smul_nieuwland {P : Polyhedron} (hP : P.FullDim) :
    ¬ (P.smul P.nieuwland).FitsThrough P := fun h ↦
  lt_irrefl _ ((fitsThrough_smul_iff_lt_nieuwland hP P.nieuwland_nonneg).mp h)

/-- **Upper bounds.** If `P` scaled by `c ≥ 0` does not fit through `P`, then
`P.nieuwland ≤ c`. -/
theorem nieuwland_le_of_not_fitsThrough {P : Polyhedron} {c : ℝ} (hc : 0 ≤ c)
    (h : ¬ (P.smul c).FitsThrough P) : P.nieuwland ≤ c :=
  not_lt.mp fun hlt ↦ h (fitsThrough_smul_of_lt_nieuwland hc hlt)

/-- **Lower bounds.** If `P` is full-dimensional and `P` scaled by every `0 < c < L` fits through
`P`, then `L ≤ P.nieuwland`. -/
theorem le_nieuwland_of_forall_lt {P : Polyhedron} (hP : P.FullDim) {L : ℝ}
    (h : ∀ c, 0 < c → c < L → (P.smul c).FitsThrough P) : L ≤ P.nieuwland := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_
  rcases le_or_gt c 0 with h0 | h0
  · exact h0.trans P.nieuwland_nonneg
  · exact le_nieuwland_of_fitsThrough hP h0 (h c h0 hc)

/-- **Lower bounds from weak fits.** If `P` is full-dimensional and `P` scaled by `c` fits weakly
through `P`, then `c ≤ P.nieuwland`. -/
theorem le_nieuwland_of_weakFitsThrough {P : Polyhedron} (hP : P.FullDim) {c : ℝ}
    (h : (P.smul c).WeakFitsThrough P) : c ≤ P.nieuwland :=
  le_nieuwland_of_forall_lt hP fun _ hc' hlt ↦ h.fitsThrough_smul_of_lt hP hc'.le hlt

/-- **Exact values.** If `0 < L` and, for every `c > 0`, `P` scaled by `c` fits through `P`
exactly when `c < L`, then `P.nieuwland = L`. -/
theorem nieuwland_eq_of_iff {P : Polyhedron} {L : ℝ} (hL : 0 < L)
    (h : ∀ c, 0 < c → ((P.smul c).FitsThrough P ↔ c < L)) : P.nieuwland = L := by
  have hset : {c : ℝ | 0 < c ∧ (P.smul c).FitsThrough P} = Set.Ioo 0 L := by
    ext c
    exact ⟨fun hc ↦ ⟨hc.1, (h c hc.1).mp hc.2⟩, fun hc ↦ ⟨hc.1, (h c hc.1).mpr hc.2⟩⟩
  rw [nieuwland, hset, csSup_Ioo hL]

/-- A full-dimensional polyhedron has Nieuwland number at least `1`. -/
theorem one_le_nieuwland {P : Polyhedron} (hP : P.FullDim) : 1 ≤ P.nieuwland :=
  le_nieuwland_of_forall_lt hP fun _ hc h1 ↦ fitsThrough_smul_of_lt_one hP hc.le h1

/-- **Nieuwland.** A full-dimensional polyhedron that is not Rupert has Nieuwland number `1`. -/
theorem nieuwland_eq_one_of_not_isRupert {P : Polyhedron} (hP : P.FullDim) (h : ¬ P.IsRupert) :
    P.nieuwland = 1 :=
  le_antisymm (nieuwland_le_of_not_fitsThrough zero_le_one (by rw [smul_one]; exact h))
    (one_le_nieuwland hP)

/-- A full-dimensional polyhedron is Rupert exactly when its Nieuwland number exceeds `1`. -/
theorem one_lt_nieuwland_iff {P : Polyhedron} (hP : P.FullDim) :
    1 < P.nieuwland ↔ P.IsRupert := by
  rw [← fitsThrough_smul_iff_lt_nieuwland hP zero_le_one, smul_one, isRupert_iff_fitsThrough]

/-- A full-dimensional polyhedron has Nieuwland number `1` exactly when it is not Rupert. -/
theorem nieuwland_eq_one_iff {P : Polyhedron} (hP : P.FullDim) :
    P.nieuwland = 1 ↔ ¬ P.IsRupert := by
  rw [← one_lt_nieuwland_iff hP]
  refine ⟨fun h ↦ ?_, fun h ↦ le_antisymm (not_lt.mp h) (one_le_nieuwland hP)⟩
  rw [h]
  exact lt_irrefl 1

/-! ### Scaling both copies -/

theorem FitsThrough.smul {P Q : Polyhedron} (h : P.FitsThrough Q) {a : ℝ} (ha : a ≠ 0) :
    (P.smul a).FitsThrough (Q.smul a) := by
  obtain ⟨R₁, hR₁, R₂, hR₂, t, h⟩ := h
  refine ⟨R₁, hR₁, R₂, hR₂, a • t, ?_⟩
  rw [shadow_smul_add_smul, shadow_hull_smul, interior_smul₀ ha]
  exact Set.smul_set_mono h

/-- Scaling keeps weak fits, for every factor (`0` included). -/
theorem WeakFitsThrough.smul {P Q : Polyhedron} (h : P.WeakFitsThrough Q) (a : ℝ) :
    (P.smul a).WeakFitsThrough (Q.smul a) := by
  obtain ⟨R₁, hR₁, R₂, hR₂, t, h⟩ := h
  refine ⟨R₁, hR₁, R₂, hR₂, a • t, ?_⟩
  rw [shadow_smul_add_smul, shadow_hull_smul]
  exact Set.smul_set_mono h

/-- **Scaling.** Scaling plug and hole by the same `a ≠ 0` does not change whether one fits
through the other. -/
theorem fitsThrough_smul_iff {a : ℝ} (ha : a ≠ 0) (P Q : Polyhedron) :
    (P.smul a).FitsThrough (Q.smul a) ↔ P.FitsThrough Q := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.smul ha⟩
  rw [← smul_smul_inv ha P, ← smul_smul_inv ha Q]
  exact h.smul (inv_ne_zero ha)

theorem weakFitsThrough_smul_iff {a : ℝ} (ha : a ≠ 0) (P Q : Polyhedron) :
    (P.smul a).WeakFitsThrough (Q.smul a) ↔ P.WeakFitsThrough Q := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.smul a⟩
  rw [← smul_smul_inv ha P, ← smul_smul_inv ha Q]
  exact h.smul a⁻¹

/-- Plug scale `a / b` as integral scales: `P` scaled by `a` fits through `Q` scaled by `b ≠ 0`
exactly when `P` scaled by `a / b` fits through `Q`. -/
theorem fitsThrough_smul_smul_iff {a b : ℝ} (hb : b ≠ 0) (P Q : Polyhedron) :
    (P.smul a).FitsThrough (Q.smul b) ↔ (P.smul (a / b)).FitsThrough Q := by
  rw [← fitsThrough_smul_iff hb (P.smul (a / b)) Q, smul_smul_eq, mul_div_cancel₀ a hb]

/-- The scaled-plug form of `fitsThrough_smul_iff`, for rewriting a solid as its exact points
scaled back (`eq_smul` of the exported modules). -/
theorem fitsThrough_smul_comm_iff {a : ℝ} (ha : a ≠ 0) (c : ℝ) (P : Polyhedron) :
    ((P.smul a).smul c).FitsThrough (P.smul a) ↔ (P.smul c).FitsThrough P := by
  rw [smul_comm_smul, fitsThrough_smul_iff ha]

theorem weakFitsThrough_smul_comm_iff {a : ℝ} (ha : a ≠ 0) (c : ℝ) (P : Polyhedron) :
    ((P.smul a).smul c).WeakFitsThrough (P.smul a) ↔ (P.smul c).WeakFitsThrough P := by
  rw [smul_comm_smul, weakFitsThrough_smul_iff ha]

/-- **Scaling.** Scaling a polyhedron by `a ≠ 0` does not change its Nieuwland number. -/
theorem nieuwland_smul {a : ℝ} (ha : a ≠ 0) (P : Polyhedron) :
    (P.smul a).nieuwland = P.nieuwland := by
  simp only [nieuwland, fitsThrough_smul_comm_iff ha]

/-! ### Reflections -/

/-- **`O(3)` versus `SO(3)`.** Allowing improper rotations for both copies gives the same
`FitsThrough`, as for `IsRupert` (`Polyhedron.isRupert_iff_orthogonal`). -/
theorem fitsThrough_iff_orthogonal (P Q : Polyhedron) :
    P.FitsThrough Q ↔ ∃ R₁ ∈ O(3), ∃ R₂ ∈ O(3), ∃ t : Fin 2 → ℝ,
      {projXY (R₁ *ᵥ x) + t | x ∈ P.hull} ⊆ interior {projXY (R₂ *ᵥ x) | x ∈ Q.hull} := by
  constructor
  · rintro ⟨R₁, hR₁, R₂, hR₂, t, h⟩
    exact ⟨R₁, hR₁.1, R₂, hR₂.1, t, h⟩
  · rintro ⟨R₁, hR₁, R₂, hR₂, t, h⟩
    obtain ⟨R₁', hR₁', h₁⟩ := exists_mem_SO3_projXY_mulVec_eq hR₁
    obtain ⟨R₂', hR₂', h₂⟩ := exists_mem_SO3_projXY_mulVec_eq hR₂
    exact ⟨R₁', hR₁', R₂', hR₂', t, by simpa only [h₁, h₂]⟩

/-- **Negative scales.** `P` scaled by `-c` (a reflected copy of `P` scaled by `c`) fits through
`Q` exactly when `P` scaled by `c` does: the half-turn about the view axis negates the shadow. So
restricting `nieuwland` to scales `c > 0` loses nothing. -/
theorem fitsThrough_smul_neg (c : ℝ) (P Q : Polyhedron) :
    (P.smul (-c)).FitsThrough Q ↔ (P.smul c).FitsThrough Q := by
  have key (c : ℝ) (h : (P.smul (-c)).FitsThrough Q) : (P.smul c).FitsThrough Q := by
    obtain ⟨R₁, hR₁, R₂, hR₂, t, h⟩ := h
    refine ⟨halfTurnZ * R₁, Submonoid.mul_mem _ halfTurnZ_mem hR₁, R₂, hR₂, t, ?_⟩
    rw [shadow_smul] at h ⊢
    rintro _ ⟨x, hx, rfl⟩
    have := h ⟨x, hx, rfl⟩
    rwa [← mulVec_mulVec, projXY_halfTurnZ_mulVec, smul_neg, ← neg_smul]
  exact ⟨key c, fun h ↦ key (-c) (by rwa [neg_neg])⟩

end Polyhedron

end Nieuwland
