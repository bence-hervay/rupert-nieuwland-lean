import Modules.Check.Sign.Box
import Modules.NoFit.Chart

/-!
# Chart boxes

A chart box (`ChartBox` in `code/src/proof/mod.rs`) is a view chart, a rotation chart and a box
of chart coordinates `(s, t, x₀, x₁, x₂)`; its poses are `ChartBox.poses`. Halving a coordinate
gives two chart boxes that together contain the box (`ChartBox.poses_subset_union`), and
`ChartBox.subset` compares boxes exactly.

The twelve unit chart boxes `ChartBox.unit a k` contain every pose of `unitPoses`, so `NoFit` on
all of them proves that a polyhedron is not Rupert (`Polyhedron.not_isRupert_of_unit`).
-/

namespace Nieuwland

/-- The chart coordinates `(s, t, x₀, x₁, x₂)` of a chart pose. -/
def ChartPose.coords (p : ChartPose) : Fin 5 → ℝ :=
  ![p.s, p.t, p.x 0, p.x 1, p.x 2]

namespace Check

/-- A chart box: view chart `view`, rotation chart `rot` and a box of chart coordinates
`(s, t, x₀, x₁, x₂)` (`ChartBox` in `code/src/proof/mod.rs`). -/
structure ChartBox where
  /-- The view chart. -/
  view : Fin 3
  /-- The rotation chart. -/
  rot : Fin 4
  /-- The box of chart coordinates. -/
  box : Box

namespace ChartBox

/-- The chart poses of a chart box. -/
def poses (B : ChartBox) : Set ChartPose :=
  {p | p.view = B.view ∧ p.rot = B.rot ∧ B.box.Mem 5 p.coords}

/-- `B ⊆ C`: the same charts and a smaller box. -/
def subset (B C : ChartBox) : Bool :=
  B.view == C.view && B.rot == C.rot && B.box.subset 5 C.box

theorem poses_subset {B C : ChartBox} (h : B.subset C = true) : B.poses ⊆ C.poses := by
  simp only [subset, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hv, hr⟩, hb⟩ := h
  rintro p ⟨hpv, hpr, hp⟩
  exact ⟨hpv.trans hv, hpr.trans hr, Box.mem_of_subset hb hp⟩

/-- The lower half along coordinate `k`. -/
def lowerHalf (B : ChartBox) (k : ℕ) : ChartBox :=
  ⟨B.view, B.rot, B.box.lowerHalf 5 k⟩

/-- The upper half along coordinate `k`. -/
def upperHalf (B : ChartBox) (k : ℕ) : ChartBox :=
  ⟨B.view, B.rot, B.box.upperHalf 5 k⟩

theorem poses_subset_union {B : ChartBox} (hden : 0 < B.box.den) (k : ℕ) :
    B.poses ⊆ (B.lowerHalf k).poses ∪ (B.upperHalf k).poses := by
  rintro p ⟨hv, hr, hp⟩
  exact (Box.mem_lowerHalf_or_upperHalf k hden hp).imp (fun h ↦ ⟨hv, hr, h⟩)
    fun h ↦ ⟨hv, hr, h⟩

/-- The unit chart box of view chart `a` and rotation chart `k`: all coordinates in
`[-1, 1]`. -/
def unit (a : Fin 3) (k : Fin 4) : ChartBox :=
  ⟨a, k, ⟨[-1, -1, -1, -1, -1], [1, 1, 1, 1, 1], 1⟩⟩

theorem mem_unit_poses {p : ChartPose} (hp : p ∈ unitPoses) : p ∈ (unit p.view p.rot).poses := by
  obtain ⟨hs, ht, hx⟩ := hp
  refine ⟨rfl, rfl, fun i ↦ ?_⟩
  have h : ∀ y : ℝ, |y| ≤ 1 → -1 ≤ y ∧ y ≤ 1 := fun y hy ↦ abs_le.mp hy
  fin_cases i
  · simpa [unit, ChartPose.coords] using h _ hs
  · simpa [unit, ChartPose.coords] using h _ ht
  · simpa [unit, ChartPose.coords] using h _ (hx 0)
  · simpa [unit, ChartPose.coords] using h _ (hx 1)
  · simpa [unit, ChartPose.coords] using h _ (hx 2)

end ChartBox

end Check

/-- **The unit chart boxes decide the problem.** A polyhedron with no fit at any pose of the
twelve unit chart boxes is not Rupert. -/
theorem Polyhedron.not_isRupert_of_unit {P : Polyhedron}
    (h : ∀ a k, P.NoFit (Check.ChartBox.unit a k).poses) : ¬ P.IsRupert :=
  P.not_isRupert_of_noFit fun p hp ↦ h p.view p.rot p (Check.ChartBox.mem_unit_poses hp)

end Nieuwland
