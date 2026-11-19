import Modules.NoFit.Open

/-!
# Density: NoFit on a box from NoFit on most of its interior

Part (a) of the density theorem of chart trees (`code/src/proof/tree.rs`, G3 of
`lean/DESIGN.md` §8). A chart box with `lo < hi` in every coordinate is the closure of its
interior, and fits form an open set (`Polyhedron.isOpen_chartFits`). In chart coordinates, the zero
set of a nonzero linear form of the view direction has empty interior (`interior_viewZero`), and
so does a finite union of such sets (`interior_viewZeros`). Hence if no pose of the interior of
the box off finitely many such zero sets fits, no pose of the closed box fits
(`Polyhedron.noFit_box_of_interior`): a fit in the box would give an open set of fits meeting the
interior, and that set has a point off the zero sets. The argument holds for any open set of chart
coordinates (`not_mem_box_of_interior`), so also for fits with a rotation applied first
(`Polyhedron.noFitRot_box_of_interior`, for pre-rotated charts).
-/

open Matrix Filter Topology Set

namespace Nieuwland

/-- The chart pose with chart coordinates `y = (s, t, x₀, x₁, x₂)` in the charts `(a, k)`. -/
def chartPose (a : Fin 3) (k : Fin 4) (y : Fin 5 → ℝ) : ChartPose :=
  ⟨a, y 0, y 1, k, ![y 2, y 3, y 4]⟩

theorem dot_viewDir (g : Fin 3 → ℝ) (a : Fin 3) (s t : ℝ) :
    g ⬝ᵥ viewDir a s t = g a + s * g (a + 1) + t * g (a + 2) := by
  fin_cases a <;> simp [viewDir, dotProduct, Fin.sum_univ_three] <;> ring

/-- The chart coordinates whose view direction is a zero of the linear form `g`. -/
def viewZero (a : Fin 3) (g : Fin 3 → ℝ) : Set (Fin 5 → ℝ) :=
  {y | g ⬝ᵥ viewDir a (y 0) (y 1) = 0}

theorem isClosed_viewZero (a : Fin 3) (g : Fin 3 → ℝ) : IsClosed (viewZero a g) := by
  have hc : Continuous fun y : Fin 5 → ℝ ↦ g ⬝ᵥ viewDir a (y 0) (y 1) := by
    simp only [dot_viewDir]
    fun_prop
  exact isClosed_eq hc continuous_const

/-- A function that vanishes near `y` on the line through `y` along coordinate `i` has
derivative `0` there: if `f (y + t eᵢ) = f y + t c` near `t = 0`, then `c = 0`. -/
theorem eq_zero_of_line {Z : Set (Fin 5 → ℝ)} {y : Fin 5 → ℝ} (hZ : Z ∈ 𝓝 y) (i : Fin 5)
    {f : (Fin 5 → ℝ) → ℝ} (hf : ∀ y' ∈ Z, f y' = 0) {c : ℝ}
    (hline : ∀ t : ℝ, f (y + t • Pi.single i 1) = f y + t * c) : c = 0 := by
  have hcont : Continuous fun t : ℝ ↦ y + t • Pi.single i (1 : ℝ) := by fun_prop
  have hpre : (fun t : ℝ ↦ y + t • Pi.single i (1 : ℝ)) ⁻¹' Z ∈ 𝓝 (0 : ℝ) :=
    hcont.continuousAt.preimage_mem_nhds (by rwa [zero_smul, add_zero])
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  have hmem : δ / 2 ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
    exact half_lt_self hδ
  have hy : y ∈ Z := mem_of_mem_nhds hZ
  have h1 := hf _ (hball hmem)
  rw [hline, hf y hy, zero_add] at h1
  exact (mul_eq_zero.mp h1).resolve_left (half_pos hδ).ne'

/-- **The zero set of a nonzero linear form of the view direction has empty interior** in chart
coordinates. -/
theorem interior_viewZero (a : Fin 3) {g : Fin 3 → ℝ} (hg : g ≠ 0) :
    interior (viewZero a g) = ∅ := by
  by_contra hne
  obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hZ : viewZero a g ∈ 𝓝 y := mem_interior_iff_mem_nhds.mp hy
  set f : (Fin 5 → ℝ) → ℝ := fun y ↦ g ⬝ᵥ viewDir a (y 0) (y 1) with hfdef
  have hf : ∀ y' ∈ viewZero a g, f y' = 0 := fun y' hy' ↦ hy'
  have h1 : g (a + 1) = 0 := eq_zero_of_line hZ 0 hf fun t ↦ by
    simp only [hfdef, dot_viewDir, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp
    ring
  have h2 : g (a + 2) = 0 := eq_zero_of_line hZ 1 hf fun t ↦ by
    simp only [hfdef, dot_viewDir, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp
    ring
  have h0 : g a = 0 := by
    have := hf y (mem_of_mem_nhds hZ)
    simp only [hfdef, dot_viewDir, h1, h2, mul_zero, add_zero] at this
    exact this
  apply hg
  funext i
  have hi : i = a ∨ i = a + 1 ∨ i = a + 2 := by
    fin_cases a <;> fin_cases i <;> simp
  rcases hi with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2

/-- The chart coordinates whose view direction is a zero of one of the linear forms `gs`. -/
def viewZeros (a : Fin 3) (gs : List (Fin 3 → ℝ)) : Set (Fin 5 → ℝ) :=
  {y | ∃ g ∈ gs, y ∈ viewZero a g}

/-- **Finitely many zero sets** of nonzero linear forms have a union with empty interior. -/
theorem interior_viewZeros (a : Fin 3) :
    ∀ (gs : List (Fin 3 → ℝ)), (∀ g ∈ gs, g ≠ 0) → interior (viewZeros a gs) = ∅
  | [], _ => by simp [viewZeros]
  | g :: gs, h => by
    have hset : viewZeros a (g :: gs) = viewZero a g ∪ viewZeros a gs := by
      ext y
      simp [viewZeros]
    rw [hset, interior_union_isClosed_of_interior_empty (isClosed_viewZero a g)
      (interior_viewZeros a gs fun g' hg' ↦ h g' (List.mem_cons_of_mem _ hg'))]
    exact interior_viewZero a (h g List.mem_cons_self)

/-- **Density, part (a), for an open set.** Let a box of chart coordinates have `lo < hi` in every
coordinate. If an open set `O` has no point of the interior of the box whose view direction is off
the zero sets of the nonzero linear forms `gs`, it has no point of the closed box. -/
theorem not_mem_box_of_interior {O : Set (Fin 5 → ℝ)} (hO : IsOpen O) (a : Fin 3)
    {lo hi : Fin 5 → ℝ} (hlt : ∀ i, lo i < hi i) (gs : List (Fin 3 → ℝ)) (hgs : ∀ g ∈ gs, g ≠ 0)
    (h : ∀ y : Fin 5 → ℝ, (∀ i, lo i < y i ∧ y i < hi i) →
      (∀ g ∈ gs, g ⬝ᵥ viewDir a (y 0) (y 1) ≠ 0) → y ∉ O)
    {y : Fin 5 → ℝ} (hy : ∀ i, lo i ≤ y i ∧ y i ≤ hi i) : y ∉ O := by
  intro hyO
  set I := Set.pi Set.univ fun i ↦ Set.Ioo (lo i) (hi i) with hIdef
  have hI : IsOpen I := isOpen_set_pi Set.finite_univ fun i _ ↦ isOpen_Ioo
  have hcl : y ∈ closure I := by
    rw [hIdef, closure_pi_set]
    intro i _
    change y i ∈ closure (Ioo (lo i) (hi i))
    rw [closure_Ioo (hlt i).ne]
    exact hy i
  obtain ⟨y₁, hy₁O, hy₁I⟩ := mem_closure_iff.mp hcl O hO hyO
  -- The open set `O ∩ I` is not inside the zero sets.
  have hsub : ¬ O ∩ I ⊆ viewZeros a gs := fun hs ↦ by
    have := interior_maximal hs (hO.inter hI)
    rw [interior_viewZeros a gs hgs] at this
    exact this ⟨hy₁O, hy₁I⟩
  obtain ⟨y₂, ⟨hy₂O, hy₂I⟩, hy₂Z⟩ := Set.not_subset.mp hsub
  exact h y₂ (fun i ↦ hy₂I i (Set.mem_univ i)) (fun g hg h0 ↦ hy₂Z ⟨g, hg, h0⟩) hy₂O

namespace Polyhedron

/-- **Density, part (a).** Let a box of chart coordinates have `lo < hi` in every coordinate. If
no pose of its interior whose view direction is off the zero sets of the nonzero linear forms
`gs` fits, then no pose of the closed box fits. -/
theorem noFit_box_of_interior (P : Polyhedron) (a : Fin 3) (k : Fin 4) {lo hi : Fin 5 → ℝ}
    (hlt : ∀ i, lo i < hi i) (gs : List (Fin 3 → ℝ)) (hgs : ∀ g ∈ gs, g ≠ 0)
    (h : ∀ y : Fin 5 → ℝ, (∀ i, lo i < y i ∧ y i < hi i) →
      (∀ g ∈ gs, g ⬝ᵥ viewDir a (y 0) (y 1) ≠ 0) → ∀ τ, ¬ P.FitsAt (chartPose a k y) τ)
    {y : Fin 5 → ℝ} (hy : ∀ i, lo i ≤ y i ∧ y i ≤ hi i) (τ : Fin 2 → ℝ) :
    ¬ P.FitsAt (chartPose a k y) τ := fun hfit ↦
  not_mem_box_of_interior (P.isOpen_chartFits a k) a hlt gs hgs
    (fun y hy hg ⟨τ', h'⟩ ↦ h y hy hg τ' h') hy ⟨τ, hfit⟩

/-- **Density, part (a), with a rotation applied first**: as `noFit_box_of_interior`, for fits
along the view with the rotation of the pose followed by `Rc`. -/
theorem noFitRot_box_of_interior (P : Polyhedron) (a : Fin 3) (k : Fin 4)
    (Rc : Matrix (Fin 3) (Fin 3) ℝ) {lo hi : Fin 5 → ℝ} (hlt : ∀ i, lo i < hi i)
    (gs : List (Fin 3 → ℝ)) (hgs : ∀ g ∈ gs, g ≠ 0)
    (h : ∀ y : Fin 5 → ℝ, (∀ i, lo i < y i ∧ y i < hi i) →
      (∀ g ∈ gs, g ⬝ᵥ viewDir a (y 0) (y 1) ≠ 0) →
      ¬ P.FitsAlong (viewDir a (y 0) (y 1)) ((chartPose a k y).rotation * Rc))
    {y : Fin 5 → ℝ} (hy : ∀ i, lo i ≤ y i ∧ y i ≤ hi i) :
    ¬ P.FitsAlong (viewDir a (y 0) (y 1)) ((chartPose a k y).rotation * Rc) :=
  not_mem_box_of_interior (P.isOpen_chartFitsRot a k Rc) a hlt gs hgs h hy

end Polyhedron

end Nieuwland
