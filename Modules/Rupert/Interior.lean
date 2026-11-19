import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

/-!
# Interior points of polygons

Finite exact tests for membership in the interior of a convex hull in the plane `Fin 2 → ℝ`.

`orient a b p` is twice the signed area of the triangle `a b p`: it is positive iff `p` lies
strictly to the left of the directed line from `a` to `b`.

* **Polygon criterion** (`mem_interior_convexHull_of_forall_orient_pos`): if `p` lies strictly to
  the left of every edge `w i → w (i + 1)` of a closed polygon `w 0, …, w n`, then `p` lies in the
  interior of the convex hull of the corners. This is the strict half-plane test of the Rust
  module `code/src/geometry/contain.rs`: for a hole polygon listed counterclockwise, a plug point
  is inside iff it is strictly inside every edge. It is complete for convex polygons, and the
  hypotheses are strict polynomial inequalities in the coordinates. Nothing is assumed about the
  polygon: neither convexity nor that the corners are vertices of the hull.
* **Triangle criterion** (`mem_interior_convexHull_of_orient_pos`): the case of three corners.

The proof uses the barycentric coordinates `orient b c p`, `orient c a p`, `orient a b p` of `p`
in a triangle `abc`, which add up to `orient a b c` (`orient_add_orient_add_orient`): a point with
nonnegative coordinates lies in the triangle (`mem_convexHull_of_orient_nonneg`). A point strictly
inside every edge of a polygon lies in one triangle of the fan from `w 0`
(`mem_convexHull_of_forall_orient_pos`), and these points form an open set.
-/

namespace Nieuwland

/-- Twice the signed area of the triangle `a b c` in the plane, `det (b - a, c - a)`. It is
positive iff `a`, `b`, `c` are in counterclockwise order, that is, iff `c` lies strictly to the
left of the directed line from `a` to `b`. -/
def orient (a b c : Fin 2 → ℝ) : ℝ :=
  (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)

/-- The three areas cut out by a point `p` add up to the area of the triangle. -/
theorem orient_add_orient_add_orient (a b c p : Fin 2 → ℝ) :
    orient a b p + orient b c p + orient c a p = orient a b c := by
  simp only [orient]; ring

theorem orient_swap (a b c : Fin 2 → ℝ) : orient b a c = -orient a b c := by
  simp only [orient]; ring

@[simp]
theorem orient_self (a c : Fin 2 → ℝ) : orient a a c = 0 := by
  simp [orient]

theorem continuous_orient (a b : Fin 2 → ℝ) : Continuous (orient a b) := by
  unfold orient; fun_prop

/-- If `p` lies weakly to the left of the three edges of a counterclockwise triangle `abc`, then
`p` lies in the triangle. -/
theorem mem_convexHull_of_orient_nonneg {a b c p : Fin 2 → ℝ} (habc : 0 < orient a b c)
    (hab : 0 ≤ orient a b p) (hbc : 0 ≤ orient b c p) (hca : 0 ≤ orient c a p) :
    p ∈ convexHull ℝ {a, b, c} := by
  have hsum : orient b c p + orient c a p + orient a b p = orient a b c := by
    rw [← orient_add_orient_add_orient a b c p]; ring
  have key := Finset.centerMass_mem_convexHull (R := ℝ) (s := ({a, b, c} : Set (Fin 2 → ℝ)))
    Finset.univ (w := ![orient b c p, orient c a p, orient a b p]) (z := ![a, b, c])
    (by intro i _; fin_cases i <;> assumption)
    (by simpa [Fin.sum_univ_three, hsum] using habc)
    (by intro i _; fin_cases i <;> simp)
  convert key using 1
  rw [Finset.centerMass, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [hsum, eq_comm, inv_smul_eq_iff₀ habc.ne']
  ext i
  fin_cases i <;> simp [orient] <;> ring

open Fin.NatCast in
/-- If `q` lies strictly to the left of every edge `w i → w (i + 1)` of a closed polygon
`w 0, …, w n`, then `q` lies in the convex hull of the corners: it lies in a triangle
`w 0, w k, w (k + 1)` of the fan from `w 0`. -/
theorem mem_convexHull_of_forall_orient_pos {n : ℕ} {w : Fin (n + 1) → Fin 2 → ℝ}
    {q : Fin 2 → ℝ} (h : ∀ i, 0 < orient (w i) (w (i + 1)) q) :
    q ∈ convexHull ℝ (Set.range w) := by
  -- Index the corners cyclically by natural numbers, and let `g j` be the area of `w 0, w j, q`.
  set c : ℕ → Fin 2 → ℝ := fun j ↦ w (j : Fin (n + 1))
  have hedge (j : ℕ) : 0 < orient (c j) (c (j + 1)) q := by
    simpa [c, Nat.cast_add_one] using h j
  set g : ℕ → ℝ := fun j ↦ orient (c 0) (c j) q
  have g1 : 0 < g 1 := by simpa [g] using hedge 0
  have gn : g n < 0 := by
    have hn := hedge n
    rw [show c (n + 1) = c 0 by simp [c], orient_swap] at hn
    simp only [g]
    linarith
  -- `g` turns from positive to negative between some `k ≥ 1` and `k + 1`.
  obtain ⟨k, hk, hgk, hgk'⟩ : ∃ k, 1 ≤ k ∧ 0 ≤ g k ∧ g (k + 1) < 0 := by
    by_contra hne
    simp only [not_exists, not_and, not_lt] at hne
    have hg (j : ℕ) (hj : 1 ≤ j) : 0 ≤ g j := by
      induction j, hj using Nat.le_induction with
      | base => exact g1.le
      | succ j hj ih => exact hne j hj ih
    have hn : 1 ≤ n := by
      by_contra h0
      have : n = 0 := by omega
      simp [g, this] at gn
    linarith [hg n hn]
  -- So `q` lies in the triangle `w 0, w k, w (k + 1)`.
  have hk' : 0 < orient (c (k + 1)) (c 0) q := by
    rw [orient_swap]; simp only [g] at hgk'; linarith
  have habc : 0 < orient (c 0) (c k) (c (k + 1)) := by
    rw [← orient_add_orient_add_orient _ _ _ q]
    linarith [hedge k]
  refine convexHull_mono ?_ (mem_convexHull_of_orient_nonneg habc hgk (hedge k).le hk'.le)
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-- **Polygon criterion.** If `p` lies strictly to the left of every edge `w i → w (i + 1)` of a
closed polygon `w 0, …, w n`, then `p` lies in the interior of the convex hull of the corners. -/
theorem mem_interior_convexHull_of_forall_orient_pos {n : ℕ} {w : Fin (n + 1) → Fin 2 → ℝ}
    {p : Fin 2 → ℝ} (h : ∀ i, 0 < orient (w i) (w (i + 1)) p) :
    p ∈ interior (convexHull ℝ (Set.range w)) := by
  -- The points strictly inside every edge form an open subset of the hull.
  have hU : IsOpen {q | ∀ i, 0 < orient (w i) (w (i + 1)) q} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const (continuous_orient _ _)
  exact interior_maximal (fun q hq ↦ mem_convexHull_of_forall_orient_pos hq) hU h

/-- **Triangle criterion.** If `p` lies strictly to the left of the three directed edges
`a → b`, `b → c` and `c → a`, then `p` lies in the interior of the triangle `abc`. -/
theorem mem_interior_convexHull_of_orient_pos {a b c p : Fin 2 → ℝ}
    (hab : 0 < orient a b p) (hbc : 0 < orient b c p) (hca : 0 < orient c a p) :
    p ∈ interior (convexHull ℝ {a, b, c}) := by
  have h := mem_interior_convexHull_of_forall_orient_pos (w := ![a, b, c]) (p := p) (by
    intro i
    fin_cases i
    exacts [hab, hbc, hca])
  rwa [Matrix.range_cons, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty,
    Set.union_empty, Set.singleton_union, Set.singleton_union] at h

end Nieuwland
