import Modules.Rupert.Charts
import Modules.Rupert.Interior
import Modules.Rupert.Screen

/-!
# Rupert fits from exact data

A `Polyhedron.Fit P` holds everything a concrete proof that `P` is Rupert supplies, and
`Polyhedron.Fit.isRupert` turns it into `P.IsRupert`. It consists of

* a pose in the charts of `Modules/Rupert/Charts.lean` (the format of `fixtures/fits/`): the
  screen map `F.pose.screen` views along `viewDir`, and `F.pose.rotation` rotates the inner copy;
* a translation of the inner shadow, in screen coordinates;
* the *hole polygon*: vertices `F.corner 0, …, F.corner n` of `P` whose screen images trace the
  outer shadow counterclockwise, and the evidence that the moved screen image of every vertex of
  `P` lies strictly to the left of every edge of that polygon.

The evidence is the strict half-plane test of the Rust module `code/src/geometry/contain.rs`, and
the polygon criterion `mem_interior_convexHull_of_forall_orient_pos` shows that it suffices.
Nothing else is required: the rotation is a rotation by construction (`ChartPose.rotation_mem`),
the screen map is onto (`screen_surjective`), and the polygon need not be checked to be convex or
to be the whole outer shadow. For exact data, the side conditions `corner_mem` and `orient_pos`
are finitely many memberships and strict polynomial inequalities, `(n + 1) * #P.vertices` of the
latter.

The chart form is no restriction: every rotation lies in some rotation chart and every viewing
direction in some view chart.
-/

open Matrix

namespace Nieuwland

/-- Exact data of a Rupert fit of `P`: a pose and a translation, together with a hole polygon
whose edges certify that the moved inner shadow lies in the interior of the outer shadow. -/
structure Polyhedron.Fit (P : Polyhedron) where
  /-- The pose: the view, and the rotation of the inner copy. -/
  pose : ChartPose
  /-- The translation of the inner shadow, in screen coordinates. -/
  translation : Fin 2 → ℝ
  /-- One less than the number of corners of the hole polygon. -/
  n : ℕ
  /-- Vertices of `P` whose screen images trace the outer shadow counterclockwise. -/
  corner : Fin (n + 1) → Fin 3 → ℝ
  /-- The corners are vertices of `P`. -/
  corner_mem : ∀ i, corner i ∈ P.vertices
  /-- The moved screen image of every vertex of the inner copy lies strictly to the left of every
  edge of the hole polygon. -/
  orient_pos : ∀ v ∈ P.vertices, ∀ i, 0 < orient (pose.screen (corner i))
    (pose.screen (corner (i + 1))) (pose.screen (pose.rotation *ᵥ v) + translation)

/-- **A fit proves the Rupert property.** -/
theorem Polyhedron.Fit.isRupert {P : Polyhedron} (F : P.Fit) : P.IsRupert := by
  refine P.isRupert_of_surjective (screenₗ F.pose.view F.pose.s F.pose.t)
    (screen_surjective _ _ _) F.pose.rotation_mem F.translation fun v hv ↦ ?_
  refine interior_mono (convexHull_mono ?_)
    (mem_interior_convexHull_of_forall_orient_pos (F.orient_pos v hv))
  rintro _ ⟨i, rfl⟩
  exact ⟨F.corner i, F.corner_mem i, rfl⟩

end Nieuwland
