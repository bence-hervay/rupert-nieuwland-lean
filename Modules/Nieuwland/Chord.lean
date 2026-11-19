import Modules.Nieuwland.Supports
import Modules.Nieuwland.Diameter

/-!
# Chord pairs

The far-field evidence `ChordPair` of `code/src/proof/regional/chord.rs` (its module docs are
the contract; `notes/chord-pair.md`): the diameter bound (`Modules/Nieuwland/Diameter.lean`) made
local to a box of poses.

**Statement** (`Polyhedron.noFitRot_of_chordPair`). `K` is the hull of the points `v_j`, the
plug at a pose is `θ R K + τ` (the rotation `R` of the pose, the plug scale `θ`), and the
evidence names two pairs of points `(a₁, c₁)`, `(a₂, c₂)`. Put `W_i = θ (v_{a_i} - v_{c_i})` and
`δ² = min(|W₁|², |W₂|²) - |W₁ - W₂|² / 4`. If `δ² > 0` and at every pose `(u, R)` of a set of
poses

1. `u ⬝ R W₁ ≥ 0 ≥ u ⬝ R W₂` (the depths have opposite signs), and
2. for `i = 1, 2` and every pair of points `(y, z)` of `K` with `|y - z|² > δ²`, with `p_i` the
   orthogonal projection of `R W_i` along `u`: `|p_i|² ≥ p_i ⬝ (y - z)`,

then no pose of the set is a strict fit at the plug scale `θ`, for any translation.

The proof (`Polyhedron.not_fitsAlong_of_chords`, as in the Rust module docs): one chord has a
depth of at most `|W₁ - W₂| / 2`, so a shadow `p` with `|p|² ≥ δ² > 0`; the two plug points of
that chord seen along `u` differ by `p`, so a fit would put two interior points of the hole's
shadow at that difference, and the balanced argument with the opposite normals `p` and `-p`
(`Polyhedron.not_fitsAlong_of_balanced`, translation eliminated) needs a pair of points wider
than `|p|²` across `p`. Pairs no longer than `δ` are not (Cauchy–Schwarz), the longer ones are
excluded by (2). Without divisions (`Polyhedron.not_fitsAlong_of_chord`): with `n = |u|²` and
`t = u ⬝ X` for the chord `X = R W`, `n |p|² = A = n |X|² - t²` and `n (p ⬝ c) = B ⬝ c =
n (X ⬝ c) - t (u ⬝ c)` (`chordA`, `chordB`).

**The check** (`Chord.checkScaled`, the mirror of `check_chord_pair`) at the plug scale
`θ = ν / d` (`Scale`), on a chart box without pre-rotation, with the points `pts`:

* exact, in the points' field: the four indices are points; `δ² > 0`, as
  `ν² (4 |U_i|² - |U₁ - U₂|²) > 0` for both chords `U_i = v_{a_i} - v_{c_i}` (the least of the two
  is `4 δ² d²`); and for every ordered pair `(v, w)` of points whether it is short,
  `4 d² |v - w|² ≤ ν² (4 |U_i|² - |U₁ - U₂|²)` for both `i` (then `|v - w|² ≤ δ²`). Rust takes the
  least of the two by an exact comparison; Lean tests both, which decides the same.
* on the box, by the library's range bounds with bisection (`nonnegOn`, homogeneous in the chart
  variables, as for the other schemas): (1) the depths `u ⬝ Q W'₁ ≥ 0` and `u ⬝ Q (-W'₂) ≥ 0`
  (`depthGen`, degree 3), with `W'_i = ν U_i` and `Q = Q(q)` the quaternion matrix (`R = Q / |q|²`);
  (2) for each pair that is not short and each chord, the polynomial of Rust's (2) multiplied
  by `|q|⁴ |u|²`, `A - B ⬝ c' ≥ 0` with `A = |u|² |q|⁴ |W'|² - t²`, `t = u ⬝ Q W'`, and
  `B ⬝ c' = |u|² |q|² (Q W' ⬝ c') - |q|² t (u ⬝ c')` for `c' = d (v - w)` (`chordGen`, degree 6).
  Rust bounds `A` and `B` once per chord and combines them with the enclosure of `c`; Lean
  bounds the exact polynomial of each pair. Both orders of a pair are tested, as Rust's
  `A ∓ B ⬝ c`.

Lean tests the pairs of all points of the list, Rust the pairs of the hull's vertices: the same
when every point is a vertex (every solid of the project), and otherwise Lean tests more.

## Main statements

* `Polyhedron.not_fitsAlong_of_chords`: the argument at one view and matrix.
* `Polyhedron.noFitRot_of_chordPair`: the statement of the Rust module docs on a set of poses.
* `Chord.checkScaled_sound`: the check on a chart box gives `NoFitRot B.poses (θ • 1)`.
-/

open Matrix

namespace Nieuwland

/-! ### The argument -/

/-- Cauchy–Schwarz in `ℝ³`. -/
theorem dot_mul_dot_le (x y : Fin 3 → ℝ) : (x ⬝ᵥ y) * (x ⬝ᵥ y) ≤ (x ⬝ᵥ x) * (y ⬝ᵥ y) := by
  simp only [dotProduct, Fin.sum_univ_three]
  nlinarith [sq_nonneg (x 0 * y 1 - x 1 * y 0), sq_nonneg (x 0 * y 2 - x 2 * y 0),
    sq_nonneg (x 1 * y 2 - x 2 * y 1)]

/-- `|u|²` times the squared length of the shadow of `X` along `u`:
`A = |u|² |X|² - (u ⬝ X)²`. -/
def chordA (u X : Fin 3 → ℝ) : ℝ :=
  (u ⬝ᵥ u) * (X ⬝ᵥ X) - (u ⬝ᵥ X) * (u ⬝ᵥ X)

/-- `|u|²` times the extent along `c` of the shadow of `X` along `u`:
`B ⬝ c = |u|² (X ⬝ c) - (u ⬝ X) (u ⬝ c)`. -/
def chordB (u X c : Fin 3 → ℝ) : ℝ :=
  (u ⬝ᵥ u) * (X ⬝ᵥ c) - (u ⬝ᵥ X) * (u ⬝ᵥ c)

namespace Polyhedron

variable {P : Polyhedron}

/-- **One chord.** If the shadow of the chord `X = M (a - c)` of two points `a`, `c` of `P` along
`u ≠ 0` is not zero (`A > 0`) and no pair of points of `P` is wider across it than the chord
(`B ⬝ (y - z) ≤ A`), then `M P` does not fit along `u`, with any translation: the balanced
argument with the opposite normals `±p`, `p = |u|² X - (u ⬝ X) u`. -/
theorem not_fitsAlong_of_chord {u : Fin 3 → ℝ} (hu : u ≠ 0) {M : Matrix (Fin 3) (Fin 3) ℝ}
    {a c : Fin 3 → ℝ} (ha : a ∈ P.vertices) (hc : c ∈ P.vertices)
    (hA : 0 < chordA u (M *ᵥ (a - c)))
    (hw : ∀ y ∈ P.vertices, ∀ z ∈ P.vertices,
      chordB u (M *ᵥ (a - c)) (y - z) ≤ chordA u (M *ᵥ (a - c))) :
    ¬ P.FitsAlong u M := by
  classical
  set X := M *ᵥ (a - c) with hX
  set p : Fin 3 → ℝ := (u ⬝ᵥ u) • X - (u ⬝ᵥ X) • u with hp
  have hn : 0 < u ⬝ᵥ u := Check.dotProduct_self_pos hu
  have hpv (v : Fin 3 → ℝ) : p ⬝ᵥ v = (u ⬝ᵥ u) * (X ⬝ᵥ v) - (u ⬝ᵥ X) * (u ⬝ᵥ v) := by
    rw [hp, sub_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul,
      dotProduct_comm u v]
  have hpu : p ⬝ᵥ u = 0 := by
    rw [hpv, dotProduct_comm X u]
    ring
  have hpX : p ⬝ᵥ X = chordA u X := by
    rw [hpv, chordA]
  have hpp : p ⬝ᵥ p = (u ⬝ᵥ u) * chordA u X := by
    have e : X ⬝ᵥ p = p ⬝ᵥ X := dotProduct_comm _ _
    rw [hpv, e, hpX, dotProduct_comm u p, hpu]
    ring
  have hp0 : p ≠ 0 := fun h0 ↦ by
    have := mul_pos hn hA
    rw [← hpp, h0, zero_dotProduct] at this
    exact lt_irrefl _ this
  -- the supports of `p` and `-p` on the points of `P`
  have hne : P.vertices.Nonempty := ⟨a, ha⟩
  obtain ⟨y₀, hy₀, hmy⟩ := Finset.exists_max_image P.vertices (fun y ↦ p ⬝ᵥ y) hne
  obtain ⟨z₀, hz₀, hmz⟩ := Finset.exists_max_image P.vertices (fun z ↦ -p ⬝ᵥ z) hne
  refine not_fitsAlong_of_balanced (n := ![p, -p]) (h := ![p ⬝ᵥ y₀, -p ⬝ᵥ z₀])
    (w := fun _ ↦ 1) (v := ![a, c]) (fun i ↦ ?_) (fun i ↦ ?_) (fun i x hx ↦ ?_)
    (fun _ ↦ zero_le_one) (by simp) (by simp) (fun i ↦ ?_) ?_
  · fin_cases i
    · exact hp0
    · exact neg_ne_zero.mpr hp0
  · fin_cases i
    · exact hpu
    · change -p ⬝ᵥ u = 0
      rw [neg_dotProduct, hpu, neg_zero]
  · fin_cases i
    · exact hmy x hx
    · exact hmz x hx
  · fin_cases i
    · exact subset_convexHull ℝ _ ha
    · exact subset_convexHull ℝ _ hc
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul,
      neg_dotProduct]
    change 0 ≤ p ⬝ᵥ (M *ᵥ a) - p ⬝ᵥ y₀ + (-(p ⬝ᵥ (M *ᵥ c)) - -(p ⬝ᵥ z₀))
    have e1 : p ⬝ᵥ (M *ᵥ a) - p ⬝ᵥ (M *ᵥ c) = chordA u X := by
      rw [← dotProduct_sub, ← mulVec_sub, ← hX, hpX]
    have e2 : p ⬝ᵥ y₀ - p ⬝ᵥ z₀ = chordB u X (y₀ - z₀) := by
      rw [← dotProduct_sub, hpv, chordB]
    have := hw y₀ hy₀ z₀ hz₀
    linarith

/-- A chord whose depth is at most half of `|u| |X₁ - X₂|` has `A ≥ |u|² δ²` when
`4 δ² ≤ 4 |X|² - |X₁ - X₂|²`. -/
theorem chordA_ge {u X D : Fin 3 → ℝ} {δ2 : ℝ}
    (ht : 4 * ((u ⬝ᵥ X) * (u ⬝ᵥ X)) ≤ (u ⬝ᵥ u) * (D ⬝ᵥ D))
    (hδ : 4 * δ2 ≤ 4 * (X ⬝ᵥ X) - D ⬝ᵥ D) : (u ⬝ᵥ u) * δ2 ≤ chordA u X := by
  have hn : 0 ≤ u ⬝ᵥ u := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (u i)
  have := mul_le_mul_of_nonneg_left hδ hn
  unfold chordA
  nlinarith

/-- A pair no longer than `δ` is no wider across a chord than the chord, when `A ≥ |u|² δ²`. -/
theorem chordB_le_of_short {u X c : Fin 3 → ℝ} {δ2 : ℝ} (hu : u ≠ 0)
    (hA : (u ⬝ᵥ u) * δ2 ≤ chordA u X) (hδ : 0 < δ2) (hc : c ⬝ᵥ c ≤ δ2) :
    chordB u X c ≤ chordA u X := by
  have hn : 0 < u ⬝ᵥ u := Check.dotProduct_self_pos hu
  set p : Fin 3 → ℝ := (u ⬝ᵥ u) • X - (u ⬝ᵥ X) • u
  have hpv (v : Fin 3 → ℝ) : p ⬝ᵥ v = (u ⬝ᵥ u) * (X ⬝ᵥ v) - (u ⬝ᵥ X) * (u ⬝ᵥ v) := by
    simp only [p, sub_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_comm u v]
  have hpp : p ⬝ᵥ p = (u ⬝ᵥ u) * chordA u X := by
    have e : X ⬝ᵥ p = p ⬝ᵥ X := dotProduct_comm _ _
    have hpu : p ⬝ᵥ u = 0 := by
      rw [hpv, dotProduct_comm X u]
      ring
    rw [hpv, e, hpv X, dotProduct_comm u p, hpu, chordA]
    ring
  have hB : chordB u X c = p ⬝ᵥ c := by rw [hpv, chordB]
  have hA0 : 0 < chordA u X := lt_of_lt_of_le (mul_pos hn hδ) hA
  have hcs := dot_mul_dot_le p c
  rw [hpp, ← hB] at hcs
  -- `(B ⬝ c)² ≤ |u|² A |c|² ≤ |u|² A δ² ≤ A²`
  have h1 : (u ⬝ᵥ u) * chordA u X * (c ⬝ᵥ c) ≤ chordA u X * chordA u X := by
    have := mul_le_mul_of_nonneg_left hc (mul_pos hn hA0).le
    nlinarith
  by_contra hlt
  push Not at hlt
  nlinarith

/-- **Chord pairs at one view.** Let `a_i, c_i` be points of `P`, `X_i = M (a_i - c_i)` and
`δ² > 0` with `4 δ² ≤ 4 |X_i|² - |X₁ - X₂|²` for both chords. If the depths have opposite signs,
`u ⬝ X₁ ≥ 0 ≥ u ⬝ X₂`, and for both chords every pair of points of `P` farther apart than `δ` is
no wider across the chord's shadow than the chord (`B ⬝ (y - z) ≤ A`), then `M P` does not fit
along `u ≠ 0`, with any translation. -/
theorem not_fitsAlong_of_chords {u : Fin 3 → ℝ} (hu : u ≠ 0) {M : Matrix (Fin 3) (Fin 3) ℝ}
    {a₁ c₁ a₂ c₂ : Fin 3 → ℝ} (ha₁ : a₁ ∈ P.vertices) (hc₁ : c₁ ∈ P.vertices)
    (ha₂ : a₂ ∈ P.vertices) (hc₂ : c₂ ∈ P.vertices) {δ2 : ℝ} (hδ : 0 < δ2)
    (hδ₁ : 4 * δ2 ≤ 4 * ((M *ᵥ (a₁ - c₁)) ⬝ᵥ (M *ᵥ (a₁ - c₁))) -
      (M *ᵥ (a₁ - c₁) - M *ᵥ (a₂ - c₂)) ⬝ᵥ (M *ᵥ (a₁ - c₁) - M *ᵥ (a₂ - c₂)))
    (hδ₂ : 4 * δ2 ≤ 4 * ((M *ᵥ (a₂ - c₂)) ⬝ᵥ (M *ᵥ (a₂ - c₂))) -
      (M *ᵥ (a₁ - c₁) - M *ᵥ (a₂ - c₂)) ⬝ᵥ (M *ᵥ (a₁ - c₁) - M *ᵥ (a₂ - c₂)))
    (hd₁ : 0 ≤ u ⬝ᵥ (M *ᵥ (a₁ - c₁))) (hd₂ : u ⬝ᵥ (M *ᵥ (a₂ - c₂)) ≤ 0)
    (hl₁ : ∀ y ∈ P.vertices, ∀ z ∈ P.vertices, δ2 < (y - z) ⬝ᵥ (y - z) →
      chordB u (M *ᵥ (a₁ - c₁)) (y - z) ≤ chordA u (M *ᵥ (a₁ - c₁)))
    (hl₂ : ∀ y ∈ P.vertices, ∀ z ∈ P.vertices, δ2 < (y - z) ⬝ᵥ (y - z) →
      chordB u (M *ᵥ (a₂ - c₂)) (y - z) ≤ chordA u (M *ᵥ (a₂ - c₂))) :
    ¬ P.FitsAlong u M := by
  set X₁ := M *ᵥ (a₁ - c₁)
  set X₂ := M *ᵥ (a₂ - c₂)
  have hn : 0 < u ⬝ᵥ u := Check.dotProduct_self_pos hu
  -- the depth difference is at most `|u| |X₁ - X₂|`
  have hcs := dot_mul_dot_le u (X₁ - X₂)
  rw [dotProduct_sub] at hcs
  -- one chord: depths of opposite signs leave one of at most half the difference
  have key : ∀ {a c X}, a ∈ P.vertices → c ∈ P.vertices → X = M *ᵥ (a - c) →
      4 * δ2 ≤ 4 * (X ⬝ᵥ X) - (X₁ - X₂) ⬝ᵥ (X₁ - X₂) →
      4 * ((u ⬝ᵥ X) * (u ⬝ᵥ X)) ≤ (u ⬝ᵥ u) * ((X₁ - X₂) ⬝ᵥ (X₁ - X₂)) →
      (∀ y ∈ P.vertices, ∀ z ∈ P.vertices, δ2 < (y - z) ⬝ᵥ (y - z) →
        chordB u X (y - z) ≤ chordA u X) → ¬ P.FitsAlong u M := by
    intro a c X ha hc hX hδX ht hl
    have hA := chordA_ge ht hδX
    subst hX
    refine not_fitsAlong_of_chord hu ha hc (lt_of_lt_of_le (mul_pos hn hδ) hA)
      fun y hy z hz ↦ ?_
    by_cases hyz : δ2 < (y - z) ⬝ᵥ (y - z)
    · exact hl y hy z hz hyz
    · exact chordB_le_of_short hu hA hδ (not_lt.mp hyz)
  rcases le_total (u ⬝ᵥ X₁) (-(u ⬝ᵥ X₂)) with h | h
  · refine key ha₁ hc₁ rfl hδ₁ ?_ hl₁
    nlinarith
  · refine key ha₂ hc₂ rfl hδ₂ ?_ hl₂
    nlinarith

/-- The orthogonal projection of `X` along `u`: `X - ((u ⬝ X) / |u|²) u`. -/
noncomputable def shadowAlong (u X : Fin 3 → ℝ) : Fin 3 → ℝ :=
  X - ((u ⬝ᵥ X) / (u ⬝ᵥ u)) • u

/-- `δ²` of two chords: `min(|W₁|², |W₂|²) - |W₁ - W₂|² / 4`. -/
noncomputable def chordDelta2 (W₁ W₂ : Fin 3 → ℝ) : ℝ :=
  min (W₁ ⬝ᵥ W₁) (W₂ ⬝ᵥ W₂) - (W₁ - W₂) ⬝ᵥ (W₁ - W₂) / 4

/-- The shadow's squared length and extents, times `|u|²`: `A` and `B ⬝ c`. -/
theorem shadowAlong_dot {u : Fin 3 → ℝ} (hu : u ≠ 0) (X c : Fin 3 → ℝ) :
    (u ⬝ᵥ u) * (shadowAlong u X ⬝ᵥ shadowAlong u X) = chordA u X ∧
      (u ⬝ᵥ u) * (shadowAlong u X ⬝ᵥ c) = chordB u X c := by
  have hn : u ⬝ᵥ u ≠ 0 := (Check.dotProduct_self_pos hu).ne'
  simp only [shadowAlong, chordA, chordB, sub_dotProduct, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, dotProduct_comm X u]
  constructor
  · field_simp
    ring
  · field_simp

/-- **Chord pairs** (the statement of `code/src/proof/regional/chord.rs`). Let `a_i, c_i` be
points of `P`, `θ` a plug scale and `W_i = θ (a_i - c_i)` with `δ² > 0` (`chordDelta2`). If at
every pose of `S`, with its view direction `u` and rotation `R`, the depths have opposite signs,
`u ⬝ R W₁ ≥ 0 ≥ u ⬝ R W₂`, and for both chords every pair of points `y, z` of `P` with
`|y - z|² > δ²` satisfies `|p_i|² ≥ p_i ⬝ (y - z)` for the orthogonal projection `p_i` of `R W_i`
along `u` (`shadowAlong`), then no pose of `S` fits the plug `θ P` in `P`, with any
translation. -/
theorem noFitRot_of_chordPair {S : Set ChartPose} {θ : ℝ} {a₁ c₁ a₂ c₂ : Fin 3 → ℝ}
    (ha₁ : a₁ ∈ P.vertices) (hc₁ : c₁ ∈ P.vertices) (ha₂ : a₂ ∈ P.vertices)
    (hc₂ : c₂ ∈ P.vertices) (hδ : 0 < chordDelta2 (θ • (a₁ - c₁)) (θ • (a₂ - c₂)))
    (hdepth : ∀ p ∈ S, 0 ≤ viewDir p.view p.s p.t ⬝ᵥ (p.rotation *ᵥ (θ • (a₁ - c₁))) ∧
      viewDir p.view p.s p.t ⬝ᵥ (p.rotation *ᵥ (θ • (a₂ - c₂))) ≤ 0)
    (hlong : ∀ p ∈ S, ∀ y ∈ P.vertices, ∀ z ∈ P.vertices,
      chordDelta2 (θ • (a₁ - c₁)) (θ • (a₂ - c₂)) < (y - z) ⬝ᵥ (y - z) →
      ∀ W ∈ ({θ • (a₁ - c₁), θ • (a₂ - c₂)} : Set (Fin 3 → ℝ)),
        shadowAlong (viewDir p.view p.s p.t) (p.rotation *ᵥ W) ⬝ᵥ
            (shadowAlong (viewDir p.view p.s p.t) (p.rotation *ᵥ W) - (y - z)) ≥ 0) :
    P.NoFitRot S (θ • 1) := by
  intro p hp
  set u := viewDir p.view p.s p.t
  have hu : u ≠ 0 := viewDir_ne_zero _ _ _
  have hn : 0 < u ⬝ᵥ u := Check.dotProduct_self_pos hu
  have hO := (mem_specialOrthogonalGroup_iff.mp p.rotation_mem).1
  have hM : p.rotation * (θ • 1) = θ • p.rotation := by rw [Matrix.mul_smul, Matrix.mul_one]
  have hX : ∀ v : Fin 3 → ℝ, (θ • p.rotation) *ᵥ v = p.rotation *ᵥ (θ • v) := fun v ↦ by
    rw [smul_mulVec, mulVec_smul]
  have hlen : ∀ v : Fin 3 → ℝ, (p.rotation *ᵥ v) ⬝ᵥ (p.rotation *ᵥ v) = v ⬝ᵥ v :=
    dotProduct_mulVec_self_of_mem_orthogonalGroup hO
  rw [hM]
  obtain ⟨hd₁, hd₂⟩ := hdepth p hp
  set δ2 := chordDelta2 (θ • (a₁ - c₁)) (θ • (a₂ - c₂))
  have hdiff : (θ • p.rotation) *ᵥ (a₁ - c₁) - (θ • p.rotation) *ᵥ (a₂ - c₂) =
      p.rotation *ᵥ (θ • (a₁ - c₁) - θ • (a₂ - c₂)) := by
    rw [hX, hX, mulVec_sub]
  have hδi : ∀ W ∈ ({θ • (a₁ - c₁), θ • (a₂ - c₂)} : Set (Fin 3 → ℝ)),
      4 * δ2 ≤ 4 * ((p.rotation *ᵥ W) ⬝ᵥ (p.rotation *ᵥ W)) -
        (p.rotation *ᵥ (θ • (a₁ - c₁) - θ • (a₂ - c₂))) ⬝ᵥ
          (p.rotation *ᵥ (θ • (a₁ - c₁) - θ • (a₂ - c₂))) := by
    intro W hW
    rw [hlen, hlen]
    have h1 := min_le_left ((θ • (a₁ - c₁)) ⬝ᵥ (θ • (a₁ - c₁))) ((θ • (a₂ - c₂)) ⬝ᵥ (θ • (a₂ - c₂)))
    have h2 := min_le_right ((θ • (a₁ - c₁)) ⬝ᵥ (θ • (a₁ - c₁)))
      ((θ • (a₂ - c₂)) ⬝ᵥ (θ • (a₂ - c₂)))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hW
    simp only [δ2, chordDelta2]
    rcases hW with rfl | rfl <;> linarith
  have hlong' : ∀ W ∈ ({θ • (a₁ - c₁), θ • (a₂ - c₂)} : Set (Fin 3 → ℝ)),
      ∀ y ∈ P.vertices, ∀ z ∈ P.vertices, δ2 < (y - z) ⬝ᵥ (y - z) →
        chordB u (p.rotation *ᵥ W) (y - z) ≤ chordA u (p.rotation *ᵥ W) := by
    intro W hW y hy z hz hyz
    have h0 := hlong p hp y hy z hz hyz W hW
    obtain ⟨eA, eB⟩ := shadowAlong_dot hu (p.rotation *ᵥ W) (y - z)
    rw [dotProduct_sub] at h0
    rw [← eA, ← eB]
    nlinarith
  have hm1 : θ • (a₁ - c₁) ∈ ({θ • (a₁ - c₁), θ • (a₂ - c₂)} : Set (Fin 3 → ℝ)) := by simp
  have hm2 : θ • (a₂ - c₂) ∈ ({θ • (a₁ - c₁), θ • (a₂ - c₂)} : Set (Fin 3 → ℝ)) := by simp
  refine not_fitsAlong_of_chords hu ha₁ hc₁ ha₂ hc₂ hδ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hdiff, hX]
    exact hδi _ hm1
  · rw [hdiff, hX]
    exact hδi _ hm2
  · rw [hX]
    exact hd₁
  · rw [hX]
    exact hd₂
  · rw [hX]
    exact hlong' _ hm1
  · rw [hX]
    exact hlong' _ hm2

end Polyhedron

namespace Check

/-! ### The polynomials -/

section Poly

variable {R : Type*} [CommRing R]

/-- The depth `u ⬝ Q(q) W` of the chord `W` times `|q|²` (`R = Q(q) / |q|²`). -/
def depthPoly (u : Fin 3 → R) (q : Fin 4 → R) (W : Fin 3 → R) : R :=
  u ⬝ᵥ (quatMatrix q *ᵥ W)

/-- The polynomial of (2) for the chord `W` and the pair difference `c`: `A - B ⬝ c` with
`A = |u|² |q|⁴ |W|² - t²`, `t = u ⬝ Q(q) W`, and `B ⬝ c = |u|² |q|² (Q(q) W ⬝ c) - |q|² t (u ⬝ c)`
(`regional/chord.rs`). -/
def chordPoly (u : Fin 3 → R) (q : Fin 4 → R) (W c : Fin 3 → R) : R :=
  (u ⬝ᵥ u) * (q ⬝ᵥ q) * (q ⬝ᵥ q) * (W ⬝ᵥ W) -
      (u ⬝ᵥ (quatMatrix q *ᵥ W)) * (u ⬝ᵥ (quatMatrix q *ᵥ W)) -
    ((u ⬝ᵥ u) * (q ⬝ᵥ q) * ((quatMatrix q *ᵥ W) ⬝ᵥ c) -
      (q ⬝ᵥ q) * (u ⬝ᵥ (quatMatrix q *ᵥ W)) * (u ⬝ᵥ c))

theorem depthPoly_smul (d : R) (u : Fin 3 → R) (q : Fin 4 → R) (W : Fin 3 → R) :
    depthPoly (d • u) (d • q) W = d ^ 3 * depthPoly u q W := by
  simp only [depthPoly, quatMatrix_smul, smul_mulVec, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  ring

theorem chordPoly_smul (d : R) (u : Fin 3 → R) (q : Fin 4 → R) (W c : Fin 3 → R) :
    chordPoly (d • u) (d • q) W c = d ^ 6 * chordPoly u q W c := by
  simp only [chordPoly, quatMatrix_smul, smul_mulVec, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  ring

end Poly

/-- **The polynomials at a representative.** For `q ≠ 0`, `b > 0` and the chord
`X = ((a / b) • R(q)) U`: the depth polynomial of `a U` is `b |q|² (u ⬝ X)`, and the polynomial
of (2) of `a U` against `b c` is `b² |q|⁴ (A - B ⬝ c)`. -/
theorem chordPoly_rep {q : Fin 4 → ℝ} (hq : q ≠ 0) (u U c : Fin 3 → ℝ) {a b : ℝ} (hb : 0 < b) :
    depthPoly u q (a • U) = b * (q ⬝ᵥ q) * (u ⬝ᵥ (((a / b) • quatRotation q) *ᵥ U)) ∧
      chordPoly u q (a • U) (b • c) = b ^ 2 * (q ⬝ᵥ q) ^ 2 *
        (chordA u (((a / b) • quatRotation q) *ᵥ U) -
          chordB u (((a / b) • quatRotation q) *ᵥ U) c) := by
  have he : q ⬝ᵥ q ≠ 0 := (dotProduct_self_pos hq).ne'
  have hQ : quatMatrix q = (q ⬝ᵥ q) • quatRotation q := by
    rw [quatRotation, smul_smul, mul_inv_cancel₀ he, one_smul]
  have hlen := dotProduct_mulVec_self_of_mem_orthogonalGroup
    (mem_specialOrthogonalGroup_iff.mp (quatRotation_mem hq)).1 U
  have hb0 := hb.ne'
  constructor
  · simp only [depthPoly, hQ, smul_mulVec, mulVec_smul, dotProduct_smul, smul_eq_mul]
    field_simp
  · simp only [chordPoly, chordA, chordB, hQ, smul_mulVec, mulVec_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, hlen]
    field_simp

/-! ### Generic computations -/

section Generic

variable {κ α β : Type} [Add κ] [Sub κ] [Mul κ] [Add α] [Sub α] [Mul α] [Add β] [Sub β] [Mul β]

/-- The depth polynomial `U ⬝ Q(Q) W` in any type with `+`, `-`, `*`, the exact chord `W`
embedded by `k`. -/
def depthG (k : κ → α) (U : V3 α) (Q : Q4 α) (W : V3 κ) : α :=
  U.dot (Q.rotate (W.map k))

/-- The polynomial of (2) (`chordPoly`) in any type with `+`, `-`, `*`: with `Y = Q(Q) W`,
`t = U ⬝ Y`, `|U|² |Q|²` and `|W|²` (exact) first. -/
def chordG (k : κ → α) (U : V3 α) (Q : Q4 α) (W c : V3 κ) : α :=
  U.dot U * Q.norm2 * Q.norm2 * k (W.dot W) -
      U.dot (Q.rotate (W.map k)) * U.dot (Q.rotate (W.map k)) -
    (U.dot U * Q.norm2 * (Q.rotate (W.map k)).dot (c.map k) -
      Q.norm2 * U.dot (Q.rotate (W.map k)) * U.dot (c.map k))

variable {f : α → β}

omit [Add κ] [Sub κ] [Mul κ] in
theorem map_depthG (hf : IsArith f) (k : κ → α) (U : V3 α) (Q : Q4 α) (W : V3 κ) :
    f (depthG k U Q W) = depthG (f ∘ k) (U.map f) (Q.map f) W := by
  rw [depthG, V3.map_dot hf, Q4.map_rotate hf]
  rfl

omit [Sub κ] in
theorem map_chordG (hf : IsArith f) (k : κ → α) (U : V3 α) (Q : Q4 α) (W c : V3 κ) :
    f (chordG k U Q W c) = chordG (f ∘ k) (U.map f) (Q.map f) W c := by
  simp only [chordG, hf.map_sub, hf.map_mul, V3.map_dot hf, Q4.map_rotate hf, Q4.map_norm2 hf]
  rfl

end Generic

section Meaning

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

theorem depthG_re (U : V3 ℝ) (Q : Q4 ℝ) (W : V3 κ) :
    depthG Exact.re U Q W = depthPoly U.toFun Q.toFun (Exact.reV W) := by
  rw [depthG, V3.dot_eq_dotProduct, Q4.toFun_rotate]
  rfl

theorem chordG_re (U : V3 ℝ) (Q : Q4 ℝ) (W c : V3 κ) :
    chordG Exact.re U Q W c = chordPoly U.toFun Q.toFun (Exact.reV W) (Exact.reV c) := by
  simp only [chordG, chordPoly, V3.dot_eq_dotProduct, Q4.toFun_rotate, Q4.norm2_eq_dotProduct,
    Exact.re_dot]
  rfl

end Meaning

section Chart

variable {κ : Type} [Add κ] [Sub κ] [Mul κ]

/-- The depth polynomial on the variables of a chart box, as a generic computation (view `S, T`
in `0, 1`, rotation `X` in `2, 3, 4`, `D` in `5`). -/
def depthGen (a : Fin 3) (k : Fin 4) (W : V3 κ) : GenPoly κ where
  run emb x := depthG emb (homView a (x 5) (x 0) (x 1)) (homQuat k (x 5) ⟨x 2, x 3, x 4⟩) W
  natural f hf emb x := by
    rw [map_depthG hf, map_homView, map_homQuat]
    rfl

/-- The polynomial of (2) on the variables of a chart box, as a generic computation. -/
def chordGen (a : Fin 3) (k : Fin 4) (W c : V3 κ) : GenPoly κ where
  run emb x := chordG emb (homView a (x 5) (x 0) (x 1)) (homQuat k (x 5) ⟨x 2, x 3, x 4⟩) W c
  natural f hf emb x := by
    rw [map_chordG hf, map_homView, map_homQuat]
    rfl

variable [Exact κ]

theorem depthGen_homEnv (a : Fin 3) (k : Fin 4) (W : V3 κ) (d : ℝ) (y : Fin 5 → ℝ) :
    (depthGen a k W).run Exact.re (homEnv 5 d y) =
      d ^ 3 * depthPoly (viewDir a (y 0) (y 1)) (chartQuat k (rotCoords y)) (Exact.reV W) := by
  change depthG Exact.re (homView a (homEnv 5 d y 5) (homEnv 5 d y 0) (homEnv 5 d y 1))
    (homQuat k (homEnv 5 d y 5) ⟨homEnv 5 d y 2, homEnv 5 d y 3, homEnv 5 d y 4⟩) W = _
  rw [depthG_re, toFun_homView_homEnv, toFun_homQuat_homEnv, depthPoly_smul]

theorem chordGen_homEnv (a : Fin 3) (k : Fin 4) (W c : V3 κ) (d : ℝ) (y : Fin 5 → ℝ) :
    (chordGen a k W c).run Exact.re (homEnv 5 d y) =
      d ^ 6 * chordPoly (viewDir a (y 0) (y 1)) (chartQuat k (rotCoords y)) (Exact.reV W)
        (Exact.reV c) := by
  change chordG Exact.re (homView a (homEnv 5 d y 5) (homEnv 5 d y 0) (homEnv 5 d y 1))
    (homQuat k (homEnv 5 d y 5) ⟨homEnv 5 d y 2, homEnv 5 d y 3, homEnv 5 d y 4⟩) W c = _
  rw [chordG_re, toFun_homView_homEnv, toFun_homQuat_homEnv, chordPoly_smul]

theorem depthGen_isHomogeneous (a : Fin 3) (k : Fin 4) (W : V3 κ) :
    (depthGen a k W).IsHomogeneous 5 3 := fun d y ↦ by
  rw [depthGen_homEnv, depthGen_homEnv, one_pow, one_mul]

theorem chordGen_isHomogeneous (a : Fin 3) (k : Fin 4) (W c : V3 κ) :
    (chordGen a k W c).IsHomogeneous 5 6 := fun d y ↦ by
  rw [chordGen_homEnv, chordGen_homEnv, one_pow, one_mul]

end Chart

/-! ### The check -/

/-- Chord-pair evidence (`BoxEvidence::ChordPair`, wire `{"schema":"chord_pair","pairs":
[[a₁, c₁], [a₂, c₂]]}`): two pairs of points, the chords `v_{a_i} - v_{c_i}` of the plug. -/
structure Chord where
  /-- The first point of the first chord. -/
  a₁ : ℕ
  /-- The second point of the first chord. -/
  c₁ : ℕ
  /-- The first point of the second chord. -/
  a₂ : ℕ
  /-- The second point of the second chord. -/
  c₂ : ℕ

namespace Chord

section Exact

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The first chord `v_{a₁} - v_{c₁}`, unscaled. -/
def u₁ (pts : List (V3 κ)) (w : Chord) : V3 κ := (pt pts w.a₁).sub (pt pts w.c₁)

/-- The second chord `v_{a₂} - v_{c₂}`, unscaled. -/
def u₂ (pts : List (V3 κ)) (w : Chord) : V3 κ := (pt pts w.a₂).sub (pt pts w.c₂)

/-- `ν² (4 |U|² - |U₁ - U₂|²)` for the chord `U` of the two `U₁, U₂` and the numerator `ν` of the
plug scale: `4 d² δ²` is the least of the two chords' values. -/
def bound (ν : κ) (U U₁ U₂ : V3 κ) : κ :=
  ν * ν * (Exact.ofInt 4 * U.dot U - (U₁.sub U₂).dot (U₁.sub U₂))

/-- The pair `(v, w)` is no longer than `δ`: `4 d² |v - w|² ≤` both chords' `bound`. -/
def short (ν : κ) (d : ℕ) (U₁ U₂ v w : V3 κ) : Bool :=
  Exact.nonneg (bound ν U₁ U₁ U₂ - Exact.ofInt ((4 * d * d : ℕ) : ℤ) * (v.sub w).dot (v.sub w)) &&
    Exact.nonneg (bound ν U₂ U₁ U₂ - Exact.ofInt ((4 * d * d : ℕ) : ℤ) * (v.sub w).dot (v.sub w))

end Exact

section Basis

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- **The check of chord-pair evidence at the plug scale `s = ν / d`** on the chart box `B`
(without pre-rotation; module docs): the indices are points, `δ² > 0`, the depths have
opposite signs on the box, and every ordered pair of points that is not short satisfies (2) on
the box for both chords. -/
def checkScaled (pts : List (V3 κ)) (B : ChartBox) (depth : ℕ) (w : Chord) (s : Scale κ) : Bool :=
  decide (0 < s.den) && decide (0 < B.box.den) &&
    decide (w.a₁ < pts.length) && decide (w.c₁ < pts.length) &&
    decide (w.a₂ < pts.length) && decide (w.c₂ < pts.length) &&
    Exact.pos (bound s.num (w.u₁ pts) (w.u₁ pts) (w.u₂ pts)) &&
    Exact.pos (bound s.num (w.u₂ pts) (w.u₁ pts) (w.u₂ pts)) &&
    nonnegOn (depthGen B.view B.rot (V3.smul s.num (w.u₁ pts))) 5 depth B.box &&
    nonnegOn (depthGen B.view B.rot (V3.smul (Exact.ofInt (-1) * s.num) (w.u₂ pts))) 5 depth
      B.box &&
    pts.all fun v ↦ pts.all fun v' ↦
      short s.num s.den (w.u₁ pts) (w.u₂ pts) v v' ||
        (nonnegOn (chordGen B.view B.rot (V3.smul s.num (w.u₁ pts))
            (V3.smul (Exact.ofInt (s.den : ℤ)) (v.sub v'))) 5 depth B.box &&
          nonnegOn (chordGen B.view B.rot (V3.smul s.num (w.u₂ pts))
            (V3.smul (Exact.ofInt (s.den : ℤ)) (v.sub v'))) 5 depth B.box)

/-- The real value of `bound`. -/
theorem re_bound (ν : κ) (U U₁ U₂ : V3 κ) :
    Exact.re (bound ν U U₁ U₂) = Exact.re ν ^ 2 *
      (4 * (Exact.reV U ⬝ᵥ Exact.reV U) -
        (Exact.reV U₁ - Exact.reV U₂) ⬝ᵥ (Exact.reV U₁ - Exact.reV U₂)) := by
  simp only [bound, Exact.re_mul, Exact.re_sub, Exact.re_dot, Exact.re_ofInt, Exact.reV_sub]
  push_cast
  ring

/-- **Soundness of the chord-pair check at a plug scale**: no pose of the box fits the plug
`s P` in `P`, with any translation. -/
theorem checkScaled_sound {pts : List (V3 κ)} {B : ChartBox} {depth : ℕ} {w : Chord}
    {s : Scale κ} (h : w.checkScaled pts B depth s = true) :
    (Polyhedron.ofPoints pts).NoFitRot B.poses (s.re • 1) := by
  simp only [checkScaled, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsd, hden⟩, ha₁⟩, hc₁⟩, ha₂⟩, hc₂⟩, hp₁⟩, hp₂⟩, hd₁⟩, hd₂⟩, hall⟩ := h
  intro p hp
  set P := Polyhedron.ofPoints pts
  set q := chartQuat p.rot p.x
  have hq : q ≠ 0 := chartQuat_ne_zero _ _
  have he : 0 < q ⬝ᵥ q := dotProduct_self_pos hq
  have hb : (0 : ℝ) < s.den := by exact_mod_cast hsd
  set u := viewDir p.view p.s p.t
  have hu : u ≠ 0 := viewDir_ne_zero _ _ _
  set a := Exact.re s.num
  set b : ℝ := (↑s.den : ℝ)
  set U₁ := Exact.reV (w.u₁ pts)
  set U₂ := Exact.reV (w.u₂ pts)
  set M := (a / b) • quatRotation q
  have hrot : p.rotation * (s.re • 1) = M := by
    rw [Matrix.mul_smul, Matrix.mul_one, ChartPose.rotation, chartRotation, Scale.re]
  rw [hrot]
  obtain ⟨hview, hrotc, hy⟩ := hp
  -- the polynomials at the pose
  have hpose : ∀ {G : GenPoly κ} {k : ℕ}, G.IsHomogeneous 5 k → nonnegOn G 5 depth B.box = true →
      0 ≤ G.run Exact.re (homEnv 5 1 p.coords) := fun he h ↦ nonnegOn_hom he hden h hy
  have hcoords : viewDir B.view (p.coords 0) (p.coords 1) = u ∧
      chartQuat B.rot (rotCoords p.coords) = q := by
    rw [rotCoords_coords, ← hview, ← hrotc]
    exact ⟨rfl, rfl⟩
  have hdep : ∀ (σ : κ) (U : V3 κ),
      nonnegOn (depthGen B.view B.rot (V3.smul σ U)) 5 depth B.box = true →
      0 ≤ depthPoly u q (Exact.re σ • Exact.reV U) := fun σ U h ↦ by
    have := hpose (depthGen_isHomogeneous _ _ _) h
    rwa [depthGen_homEnv, one_pow, one_mul, hcoords.1, hcoords.2, Exact.reV_smul] at this
  have hchord : ∀ (U c : V3 κ),
      nonnegOn (chordGen B.view B.rot (V3.smul s.num U)
        (V3.smul (Exact.ofInt (s.den : ℤ)) c)) 5 depth B.box = true →
      chordB u (M *ᵥ Exact.reV U) (Exact.reV c) ≤ chordA u (M *ᵥ Exact.reV U) := fun U c h ↦ by
    have := hpose (chordGen_isHomogeneous _ _ _ _) h
    rw [chordGen_homEnv, one_pow, one_mul, hcoords.1, hcoords.2, Exact.reV_smul, Exact.reV_smul,
      Exact.re_ofInt, Int.cast_natCast, (chordPoly_rep hq u _ _ hb).2] at this
    have h2 := nonneg_of_mul_nonneg_right this (by positivity)
    linarith
  -- `δ²` and its two bounds
  have hE₁ := Exact.pos_sound _ hp₁
  have hE₂ := Exact.pos_sound _ hp₂
  rw [re_bound] at hE₁ hE₂
  set E₁ := a ^ 2 * (4 * (U₁ ⬝ᵥ U₁) - (U₁ - U₂) ⬝ᵥ (U₁ - U₂))
  set E₂ := a ^ 2 * (4 * (U₂ ⬝ᵥ U₂) - (U₁ - U₂) ⬝ᵥ (U₁ - U₂))
  set δ2 := min E₁ E₂ / (4 * b ^ 2)
  have hδ : 0 < δ2 := div_pos (lt_min hE₁ hE₂) (by positivity)
  have hO := (mem_specialOrthogonalGroup_iff.mp (quatRotation_mem hq)).1
  have hlen : ∀ v : Fin 3 → ℝ, (M *ᵥ v) ⬝ᵥ (M *ᵥ v) = (a / b) ^ 2 * (v ⬝ᵥ v) := fun v ↦ by
    rw [smul_mulVec, smul_dotProduct, dotProduct_smul,
      dotProduct_mulVec_self_of_mem_orthogonalGroup hO,
      smul_eq_mul, smul_eq_mul]
    ring
  have hsub : M *ᵥ U₁ - M *ᵥ U₂ = M *ᵥ (U₁ - U₂) := (mulVec_sub _ _ _).symm
  have h4 : ∀ E U, min E₁ E₂ ≤ E → E = a ^ 2 * (4 * (U ⬝ᵥ U) - (U₁ - U₂) ⬝ᵥ (U₁ - U₂)) →
      4 * δ2 ≤ 4 * ((M *ᵥ U) ⬝ᵥ (M *ᵥ U)) - (M *ᵥ U₁ - M *ᵥ U₂) ⬝ᵥ (M *ᵥ U₁ - M *ᵥ U₂) := by
    intro E U hle hE
    rw [hsub, hlen, hlen]
    have e : 4 * δ2 = min E₁ E₂ / b ^ 2 := by
      simp only [δ2]
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have h2 : (a / b) ^ 2 * b ^ 2 = a ^ 2 := by field_simp
    have h3 : (4 * ((a / b) ^ 2 * (U ⬝ᵥ U)) - (a / b) ^ 2 * ((U₁ - U₂) ⬝ᵥ (U₁ - U₂))) * b ^ 2 =
        E := by
      rw [hE, ← h2]
      ring
    linarith
  -- the pairs: a pair farther apart than `δ` is not short
  have hlong : ∀ U, (U = w.u₁ pts ∨ U = w.u₂ pts) → ∀ y ∈ P.vertices, ∀ z ∈ P.vertices,
      δ2 < (y - z) ⬝ᵥ (y - z) →
        chordB u (M *ᵥ Exact.reV U) (y - z) ≤ chordA u (M *ᵥ Exact.reV U) := by
    intro U hU y hy z hz hyz
    obtain ⟨v, hv, rfl⟩ := Polyhedron.mem_ofPoints.mp hy
    obtain ⟨v', hv', rfl⟩ := Polyhedron.mem_ofPoints.mp hz
    rcases hall v hv v' hv' with hs | ⟨h₁, h₂⟩
    · exfalso
      simp only [short, Bool.and_eq_true] at hs
      have s₁ := Exact.nonneg_sound _ hs.1
      have s₂ := Exact.nonneg_sound _ hs.2
      rw [Exact.re_sub, Exact.re_mul, re_bound, Exact.re_dot, Exact.reV_sub,
        Exact.re_ofInt] at s₁ s₂
      push_cast at s₁ s₂
      have hm : 4 * b ^ 2 * ((Exact.reV v - Exact.reV v') ⬝ᵥ (Exact.reV v - Exact.reV v')) ≤
          min E₁ E₂ := le_min (by simp only [E₁, b]; nlinarith) (by simp only [E₂, b]; nlinarith)
      have : (Exact.reV v - Exact.reV v') ⬝ᵥ (Exact.reV v - Exact.reV v') ≤ δ2 := by
        simp only [δ2]
        rw [le_div_iff₀ (by positivity)]
        linarith
      linarith
    · have hc := fun U' (hU' : _ = true) ↦ hchord U' (v.sub v') hU'
      rw [Exact.reV_sub] at hc
      rcases hU with rfl | rfl
      · exact hc _ h₁
      · exact hc _ h₂
  have hpt : ∀ {j : ℕ}, j < pts.length → Exact.reV (pt pts j) ∈ P.vertices :=
    fun hj ↦ Polyhedron.pt_mem_ofPoints hj
  have hU₁ : U₁ = Exact.reV (pt pts w.a₁) - Exact.reV (pt pts w.c₁) := Exact.reV_sub _ _
  have hU₂ : U₂ = Exact.reV (pt pts w.a₂) - Exact.reV (pt pts w.c₂) := Exact.reV_sub _ _
  refine Polyhedron.not_fitsAlong_of_chords hu (hpt ha₁) (hpt hc₁) (hpt ha₂) (hpt hc₂) hδ
    ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← hU₁, ← hU₂]
    exact h4 E₁ U₁ (min_le_left _ _) rfl
  · rw [← hU₁, ← hU₂]
    exact h4 E₂ U₂ (min_le_right _ _) rfl
  · rw [← hU₁]
    have h0 := hdep _ _ hd₁
    rw [(chordPoly_rep hq u U₁ 0 hb).1] at h0
    exact nonneg_of_mul_nonneg_right h0 (by positivity)
  · rw [← hU₂]
    have h0 := hdep _ _ hd₂
    rw [Exact.re_mul, Exact.re_ofInt, (chordPoly_rep hq u U₂ 0 hb).1] at h0
    have e : ((((-1 : ℤ) : ℝ) * a) / b) • quatRotation q = -M := by
      rw [show (((-1 : ℤ) : ℝ) * a) / b = -(a / b) by push_cast; ring, neg_smul]
    rw [e, neg_mulVec, dotProduct_neg] at h0
    have := nonneg_of_mul_nonneg_right h0 (by positivity)
    linarith
  · rw [← hU₁]
    exact hlong _ (Or.inl rfl)
  · rw [← hU₂]
    exact hlong _ (Or.inr rfl)

end Basis

end Chord

/-! ### Exact numbers from a whole cover at the exact scale -/

/-- **Exact Nieuwland numbers from a cover at the exact scale over a lift.** For
`P = a • (polyhedron of ptsF)`, `a ≠ 0`, of full dimension, and points `ptsE` of a lift with
`ofPoints ptsE = (ofPoints ptsF).smul c`, `c ≠ 0`: if the polyhedron of `ptsE` scaled by
`Θ ≥ 0` does not fit through itself (a cover whose every leaf holds at `Θ`, such as a far field of
chord pairs and supports restated at `Θ`: `Polyhedron.not_fitsThrough_smul_of_roots`) and a weak
fit holds at `Θ`, then `nieuwland P = Θ`. -/
theorem Polyhedron.nieuwland_eq_of_not_fitsThrough_lift {κF κE : Type} [Add κF] [Sub κF]
    [Mul κF] [Exact κF] [Add κE] [Sub κE] [Mul κE] [Exact κE] {ptsF : List (V3 κF)}
    {ptsE : List (V3 κE)} {c : ℝ} (hc : c ≠ 0)
    (hpts : Polyhedron.ofPoints ptsE = (Polyhedron.ofPoints ptsF).smul c) {Θ : Scale κE}
    (hΘ : 0 ≤ Θ.re)
    (hnf : ¬ ((Polyhedron.ofPoints ptsE).smul Θ.re).FitsThrough (Polyhedron.ofPoints ptsE))
    {W : WeakFitData κE} (hW : W.check ptsE = true) (hWn : W.scaleNum = Θ.num)
    (hWd : W.scaleDen = Θ.den) {P : Polyhedron} {a : ℝ}
    (hP : P = (Polyhedron.ofPoints ptsF).smul a) (ha : a ≠ 0) (hdim : P.FullDim) :
    P.nieuwland = Θ.re := by
  have hb : a * c⁻¹ ≠ 0 := mul_ne_zero ha (inv_ne_zero hc)
  have hP' : P = (Polyhedron.ofPoints ptsE).smul (a * c⁻¹) := by
    rw [hpts, Polyhedron.smul_smul_eq, inv_mul_cancel_right₀ hc]
    exact hP
  have hlo : Θ.re ≤ P.nieuwland := by
    have h0 := W.le_nieuwland_smul hW hb hP' hdim
    rwa [WeakFitData.scale, hWn, hWd] at h0
  refine le_antisymm ?_ hlo
  rw [hP', Polyhedron.nieuwland_smul hb]
  exact Polyhedron.nieuwland_le_of_not_fitsThrough hΘ hnf

end Check

end Nieuwland
