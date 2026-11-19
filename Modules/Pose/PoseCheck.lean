import Modules.Pose.PoseRoot
import Modules.System.PolyAux
import Modules.Nieuwland.Weak
import Modules.Check.Number.Theta

/-!
# Pose roots: the checks

The generic part of the theorems `<def>_pose_of_reps : IsRootEq [S₀] N → IsPoseRoot <def> S N i j k`
(`Modules/Pose/PoseRoot.lean`). Nothing here depends on a solid; a generated module
`Nieuwland.Pose.<Name>` (`lean/scripts/poseroot.py`) states its data and decides the checks.

## The witness from chart coordinates

A chart pose (`Modules/Rupert/Charts.lean`) has view chart `a`, coordinates `(s, t)` and screen map
`L y = (w₁ ⬝ y, w₂ ⬝ y)` with `w₁ = e_{a+1} - s e_a`, `w₂ = e_{a+2} - t e_a`, and the plug's
rotation `Q(q) / |q|²`. With `n₁`, `n₃` such that `(1 + s²) n₁² = 1` and `(1 + s² + t²) n₃² = 1`,
the matrix `holeMat` of rows `n₁ w₁`, `n₁ n₃ (-s t w₁ + (1 + s²) w₂)` and `n₃ u`
(`u = e_a + s e_{a+1} + t e_{a+2}`, the view direction) is a rotation (`holeMat_mem`; its rows
are orthonormal and its determinant is `n₁² n₃² (1 + s²) (1 + s² + t²) = 1`, whatever the signs of
`n₁`, `n₃`) whose shadow is the screen map followed by the linear map `aMap`:
`projXY (holeMat y) = aMap (L y)` (`projXY_holeMat`). So a weak fit in screen coordinates
(`ScreenWeak`: the moved screen image of the scaled plug's hull lies in the hole's screen image)
is a weak fit `PoseAt` with `R₂ = holeMat`, `R₁ = holeMat · Q(q) / |q|²` and `t = aMap τ`
(`poseAt_of`); `aMap` need not be invertible.

## The pose's variables (`poseExt`)

A system `S` with `n` variables and polynomials `s, t, q₀, …, q₃, τ₀, τ₁` in them is extended
by the pose:

* `helperExt`: three variables `n₁ = x n`, `n₃ = x (n + 1)`, `n_q = x (n + 2)`, each in `[0, 1]`,
  defined implicitly by `(1 + s²) n₁² = 1`, `(1 + s² + t²) n₃² = 1` and `|q|² n_q = 1`. If some
  `qₘ` has an interval value (`RationalPolynomial.ival`) on `S`'s box outside `(-1, 1)` (`helpersOk`), then
  `|q|² ≥ 1` at every root of `S`, the three values `1 / √(1 + s²)`, `1 / √(1 + s² + t²)`,
  `1 / |q|²` lie in `[0, 1]`, and a root of `S` has exactly one extension
  (`HasUniqueRoot.of_helperExt`, the same scales).
* `poseExt`: twenty more variables defined explicitly (`PolynomialSystem.auxOk` with `m = 20`,
  `Modules/System/PolyAux.lean`): `R₂ = holeMat` at `x (n + 3), …`, `R₁ = R₂ Q(q) n_q` at
  `x (n + 12), …` and `t = aMap τ` at `x (n + 21)`, `x (n + 22)`.

At every root (`poseExt_poseAt`), `ScreenWeak` at the values of `s, t, q, τ` and the scale `x 0`
gives `PoseAt P x (n + 12) (n + 3) (n + 21)`.

## Weak fits at the scale (`WeakFitData.screenWeak`)

`WeakFitData.check` (`Modules/Nieuwland/Weak.lean`) checks every moved point of the plug at the
scale `λ` weakly against every edge of the hole polygon and an interior witness strictly. A point
weakly inside every edge of a polygon with a strictly interior witness lies in the polygon
(`mem_convexHull_of_weak`: the points between it and the witness are strictly inside,
and the hull of finitely many points is closed). So a passing check is `ScreenWeak` at exactly
`λ`, with the data's pose and translation.

## Closed forms (`cfSystem`)

For a closed form the weak fit is over the lift `ℤ[α]` (`Root`, `ZTheta`) and its scale is
`λ = scaleNum(α) / scaleDen`. The system `cfSystem` has the variables `x 0 = ℓ`, `x 1 = α`
(`cfBase`: the equations of the representatives' system `S₀` in `ℓ` alone, `N(α) = 0` for the
root's monic polynomial `N`, `scaleDen ℓ = scaleNum(α)`, with `α`'s interval inside the root's
isolating interval), then `s, t, q₀, …, q₃, τ₀, τ₁` as polynomials in `α` (`cfCore`, explicit
definitions: the fit data's values, the translation times the factor `κ` from the lift's
points to the polyhedron's), then the pose (`poseExt`). `cfBaseOk` checks that `λ` is a root of
`S₀`'s equations (each is a multiple of `N` after substituting `ℓ = λ(α)`, with the quotient
given) in `S₀`'s interval (interval value on the enclosure of `α`), so `λ` is the one root `N`
of `S₀` (`cfBase_root`). `cf_isPoseRoot`: with `W.check` and `P` the lift's points scaled by
`κ`, `cfSystem` is a pose root of `P` at `N`.

## Main statements

* `holeMat_mem`, `projXY_holeMat`, `poseAt_of`, `ScreenWeak.smul`.
* `mem_convexHull_of_weak`, `Check.WeakFitData.screenWeak`.
* `PolynomialSystem.HasUniqueRoot.of_helperExt`, `PolynomialSystem.poseExt_poseAt`.
* `PolynomialSystem.cfBase_root`, `PolynomialSystem.cf_isPoseRoot`.
-/

open Matrix

namespace Nieuwland

namespace PoseCheck

/-! ### The witness -/

/-- `w₁ = e_{a+1} - s e_a` of view chart `a`. -/
def w₁ (a : Fin 3) (s : ℝ) (b : Fin 3) : ℝ := (if b = a + 1 then 1 else 0) - (if b = a then s else 0)

/-- `w₂ = e_{a+2} - t e_a` of view chart `a`. -/
def w₂ (a : Fin 3) (t : ℝ) (b : Fin 3) : ℝ := (if b = a + 2 then 1 else 0) - (if b = a then t else 0)

/-- The view direction `u = e_a + s e_{a+1} + t e_{a+2}` of view chart `a`. -/
def uv (a : Fin 3) (s t : ℝ) (b : Fin 3) : ℝ := if b = a then 1 else if b = a + 1 then s else t

/-- The hole's rotation: rows `n₁ w₁`, `n₁ n₃ (-s t w₁ + (1 + s²) w₂)`, `n₃ u` (module docs). -/
def holeMat (a : Fin 3) (s t n₁ n₃ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := fun r b ↦
  ![n₁ * w₁ a s b, n₁ * n₃ * (-(s * t) * w₁ a s b + (1 + s * s) * w₂ a t b), n₃ * uv a s t b] r

/-- The linear map from screen coordinates to the shadow of `holeMat`. -/
def aMap (s t n₁ n₃ : ℝ) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![n₁ * v 0, n₁ * n₃ * (-(s * t) * v 0 + (1 + s * s) * v 1)]

theorem aMap_add (s t n₁ n₃ : ℝ) (v w : Fin 2 → ℝ) :
    aMap s t n₁ n₃ (v + w) = aMap s t n₁ n₃ v + aMap s t n₁ n₃ w := by
  ext i
  fin_cases i <;> simp [aMap] <;> ring

/-- **The hole's matrix is a rotation.** -/
theorem holeMat_mem (a : Fin 3) {s t n₁ n₃ : ℝ} (h₁ : (1 + s * s) * (n₁ * n₁) = 1)
    (h₃ : (1 + s * s + t * t) * (n₃ * n₃) = 1) : holeMat a s t n₁ n₃ ∈ SO(3) := by
  rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · ext r c
    fin_cases a <;> fin_cases r <;> fin_cases c <;>
      simp [holeMat, w₁, w₂, uv, Matrix.mul_apply, Fin.sum_univ_three] <;>
      first
        | ring1
        | linear_combination h₁
        | linear_combination h₃
        | linear_combination (n₁ * n₁ * (1 + s * s)) * h₃ + h₁
  · rw [det_fin_three]
    fin_cases a <;> simp [holeMat, w₁, w₂, uv] <;>
      linear_combination (n₁ * n₁ * (1 + s * s)) * h₃ + h₁

/-- **The shadow of the hole's matrix** is the screen map followed by `aMap`. -/
theorem projXY_holeMat (a : Fin 3) (s t n₁ n₃ : ℝ) (y : Fin 3 → ℝ) :
    projXY (holeMat a s t n₁ n₃ *ᵥ y) = aMap s t n₁ n₃ (screen a s t y) := by
  ext c
  fin_cases a <;> fin_cases c <;>
    simp [projXY, holeMat, aMap, screen, w₁, w₂, uv, mulVec, dotProduct, Fin.sum_univ_three] <;>
    ring

/-- **A weak fit in screen coordinates**: the screen image of every point of the hull of `P`
scaled by `l`, rotated by `R` and moved by `τ`, is the screen image of a point of the hull of
`P`. -/
def ScreenWeak (P : Polyhedron) (a : Fin 3) (s t : ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (τ : Fin 2 → ℝ) (l : ℝ) : Prop :=
  ∀ y ∈ (P.smul l).hull, ∃ y' ∈ P.hull, screen a s t (R *ᵥ y) + τ = screen a s t y'

/-- **Scaling the polyhedron** scales the translation. -/
theorem ScreenWeak.smul {Q : Polyhedron} {a : Fin 3} {s t : ℝ} {R : Matrix (Fin 3) (Fin 3) ℝ}
    {τ : Fin 2 → ℝ} {l : ℝ} (h : ScreenWeak Q a s t R τ l) (c : ℝ) :
    ScreenWeak (Q.smul c) a s t R (c • τ) l := by
  intro y hy
  rw [Polyhedron.smul_smul_eq, mul_comm, ← Polyhedron.smul_smul_eq, Polyhedron.hull_smul] at hy
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  obtain ⟨y', hy', he⟩ := h y₀ hy₀
  refine ⟨c • y', by rw [Polyhedron.hull_smul]; exact Set.smul_mem_smul_set hy', ?_⟩
  rw [mulVec_smul, ← screenₗ_apply, ← screenₗ_apply, LinearMap.map_smul, LinearMap.map_smul,
    screenₗ_apply, screenₗ_apply, ← he, smul_add]

/-- **The witness**: a weak fit in screen coordinates at the rotation `Q(q) / |q|²` is a weak fit
`PoseAt` with `R₂ = holeMat`, `R₁ = holeMat · Q(q) / |q|²` and `t = aMap τ`. -/
theorem poseAt_of {P : Polyhedron} {x : ℕ → ℝ} {i j k : ℕ} {a : Fin 3} {s t n₁ n₃ : ℝ}
    {q : Fin 4 → ℝ} {τ : Fin 2 → ℝ} (h₁ : (1 + s * s) * (n₁ * n₁) = 1)
    (h₃ : (1 + s * s + t * t) * (n₃ * n₃) = 1) (hq : q ≠ 0)
    (hj : matAt x j = holeMat a s t n₁ n₃) (hi : matAt x i = holeMat a s t n₁ n₃ * quatRotation q)
    (hk : ![x k, x (k + 1)] = aMap s t n₁ n₃ τ)
    (hw : ScreenWeak P a s t (quatRotation q) τ (x 0)) : PoseAt P x i j k := by
  refine ⟨by rw [hi]; exact Submonoid.mul_mem _ (holeMat_mem a h₁ h₃) (quatRotation_mem hq),
    by rw [hj]; exact holeMat_mem a h₁ h₃, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨y', hy', he⟩ := hw y hy
  refine ⟨y', hy', ?_⟩
  rw [hi, hj, hk, ← mulVec_mulVec, projXY_holeMat, projXY_holeMat, ← aMap_add, he]

/-! ### Weak fits at the scale -/

/-- **A point weakly inside every edge** of a closed polygon `w 0, …, w n`, which has a point `h`
strictly inside every edge, lies in the convex hull of the corners. -/
theorem mem_convexHull_of_weak {n : ℕ} {w : Fin (n + 1) → Fin 2 → ℝ} {p h : Fin 2 → ℝ}
    (hp : ∀ i, 0 ≤ orient (w i) (w (i + 1)) p) (hh : ∀ i, 0 < orient (w i) (w (i + 1)) h) :
    p ∈ convexHull ℝ (Set.range w) := by
  have hC : IsClosed (convexHull ℝ (Set.range w)) :=
    Set.Finite.isClosed_convexHull ℝ (Set.finite_range w)
  let g : ℝ → Fin 2 → ℝ := fun ε ↦ ε • h + (1 - ε) • p
  have hg : Continuous g := by fun_prop
  have hsub : Set.Ioc (0 : ℝ) 1 ⊆ g ⁻¹' convexHull ℝ (Set.range w) := by
    rintro ε ⟨h0, h1⟩
    show g ε ∈ convexHull ℝ (Set.range w)
    refine interior_subset (mem_interior_convexHull_of_forall_orient_pos fun i ↦ ?_)
    change 0 < orient (w i) (w (i + 1)) (ε • h + (1 - ε) • p)
    rw [orient_add_smul]
    exact add_pos_of_pos_of_nonneg (mul_pos h0 (hh i)) (mul_nonneg (by linarith) (hp i))
  have h0 : (0 : ℝ) ∈ closure (Set.Ioc (0 : ℝ) 1) := by
    rw [closure_Ioc zero_ne_one]
    exact ⟨le_rfl, zero_le_one⟩
  have := closure_minimal hsub (hC.preimage hg) h0
  simpa [g] using this

end PoseCheck

namespace Check

open PoseCheck

variable {α : Type} [Add α] [Sub α] [Mul α] [Exact α]

/-- **A passing weak fit check is a weak fit at its scale** in screen coordinates: the plug of the
points scaled by `λ`, rotated by the data's rotation and moved by its translation, lies in the
screen image of the hole. -/
theorem WeakFitData.screenWeak (W : WeakFitData α) {pts : List (V3 α)} (h : W.check pts = true) :
    ScreenWeak (Polyhedron.ofPoints pts) W.fit.view W.fit.pose.s W.fit.pose.t W.fit.pose.rotation
      W.fit.translation W.scale := by
  simp only [WeakFitData.check, WeakFitData.checkHead, FitData.checkHead, Bool.and_eq_true,
    List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hD, hk⟩, hE⟩, hcor⟩, hlen⟩, hG⟩, hH⟩, hw⟩, hv⟩ := h
  have hD' := Exact.pos_sound _ hD
  have hk' := Exact.pos_sound _ hk
  have hE' := Exact.pos_sound _ hE
  have hH' := Exact.pos_sound _ hH
  have hG' : (0 : ℝ) < W.scaleDen := by exact_mod_cast hG
  have hN' : 0 < Exact.re W.fit.q.norm2 := by
    rw [Q4.map_norm2 Exact.isArith, Q4.norm2_eq_dotProduct]
    refine lt_of_lt_of_le (pow_pos hk' 2) ?_
    rw [FitData.re_qget, sq]
    exact Finset.single_le_sum (f := fun j ↦ (W.fit.q.map Exact.re).toFun j *
      (W.fit.q.map Exact.re).toFun j) (fun j _ ↦ mul_self_nonneg _) (Finset.mem_univ W.fit.rot)
  have hn : W.fit.corners.length - 1 + 1 = W.fit.corners.length := by omega
  let w : Fin (W.fit.corners.length - 1 + 1) → Fin 2 → ℝ :=
    fun i ↦ W.fit.pose.screen (Exact.reV (Exact.pt pts (W.fit.corners.getD i 0)))
  -- the corners are points
  have hC : convexHull ℝ (Set.range w) ⊆ {screen W.fit.view W.fit.pose.s W.fit.pose.t y' | y' ∈
      (Polyhedron.ofPoints pts).hull} := by
    have e := (Polyhedron.ofPoints pts).image_hull
      (screenₗ W.fit.pose.view W.fit.pose.s W.fit.pose.t)
    simp only [screenₗ_apply] at e
    rw [show W.fit.view = W.fit.pose.view from rfl, e]
    refine convexHull_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨_, Exact.reV_pt_mem (hcor _ (getD_mem_of_lt 0 (by omega))), rfl⟩
  -- the moved vertices lie in the polygon
  have hvert : ∀ y ∈ ((Polyhedron.ofPoints pts).smul W.scale).vertices,
      W.fit.pose.screen (W.fit.pose.rotation *ᵥ y) + W.fit.translation ∈
        convexHull ℝ (Set.range w) := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Polyhedron.mem_smul_vertices.mp hz
    obtain ⟨v, hvm, rfl⟩ := Polyhedron.mem_ofPoints.mp hy
    refine mem_convexHull_of_weak (h := W.witness) (fun i ↦ ?_) (fun i ↦ ?_)
    · have hi : ((i + 1 : Fin (W.fit.corners.length - 1 + 1)) : ℕ) =
          (i.val + 1) % W.fit.corners.length := by
        rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
        exact congrArg _ hn
      have h0 := Exact.nonneg_sound _ (hv i (by omega) v hvm)
      rw [WeakFitData.re_value] at h0
      simp only [w]
      rw [hi, Matrix.mulVec_smul, FitData.screen_smul, W.fit.screen_eq hD'.ne',
        W.fit.screen_eq hD'.ne', W.fit.rotation_mulVec hk'.ne', FitData.screen_smul,
        W.fit.screen_eq hD'.ne', FitData.translation, WeakFitData.scale,
        orient_weak hD'.ne' hN'.ne' hE'.ne' hG'.ne']
      exact div_nonneg h0 (by positivity)
    · have hi : ((i + 1 : Fin (W.fit.corners.length - 1 + 1)) : ℕ) =
          (i.val + 1) % W.fit.corners.length := by
        rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
        exact congrArg _ hn
      have h1 := Exact.pos_sound _ (hw i (by omega))
      rw [WeakFitData.re_witnessValue] at h1
      simp only [w]
      rw [hi, W.fit.screen_eq hD'.ne', W.fit.screen_eq hD'.ne', WeakFitData.witness,
        orient_witness hD'.ne' hH'.ne']
      exact div_pos h1 (by positivity)
  -- the moved hull lies in the polygon
  intro y hy
  have hconv : Convex ℝ ((fun z ↦ W.fit.pose.screen (W.fit.pose.rotation *ᵥ z) +
      W.fit.translation) ⁻¹' convexHull ℝ (Set.range w)) := by
    have := ((convex_convexHull ℝ (Set.range w)).translate_preimage_left
      W.fit.translation).linear_preimage
      ((screenₗ W.fit.pose.view W.fit.pose.s W.fit.pose.t) ∘ₗ W.fit.pose.rotation.mulVecLin)
    exact this
  obtain ⟨y', hy', he⟩ := hC (convexHull_min (fun z hz ↦ hvert z hz) hconv hy)
  exact ⟨y', hy', he.symm⟩

end Check

/-! ### The pose's polynomials -/

namespace RationalPolynomial

open PoseCheck

/-- `w₁` of view chart `a` (`PoseCheck.w₁`) in the polynomial `s`. -/
def w₁P (a : Fin 3) (s : RationalPolynomial) (b : Fin 3) : RationalPolynomial :=
  add (if b = a + 1 then const 1 else []) (if b = a then neg s else [])

/-- `w₂` of view chart `a` (`PoseCheck.w₂`) in the polynomial `t`. -/
def w₂P (a : Fin 3) (t : RationalPolynomial) (b : Fin 3) : RationalPolynomial :=
  add (if b = a + 2 then const 1 else []) (if b = a then neg t else [])

/-- The view direction (`PoseCheck.uv`) in the polynomials `s`, `t`. -/
def uP (a : Fin 3) (s t : RationalPolynomial) (b : Fin 3) : RationalPolynomial :=
  if b = a then const 1 else if b = a + 1 then s else t

/-- The entry `(r, b)` of `holeMat` in polynomials. -/
def holeP (a : Fin 3) (s t n₁ n₃ : RationalPolynomial) (r b : Fin 3) : RationalPolynomial :=
  ![mul n₁ (w₁P a s b),
    mul (mul n₁ n₃)
      (add (mul (neg (mul s t)) (w₁P a s b)) (mul (add (const 1) (mul s s)) (w₂P a t b))),
    mul n₃ (uP a s t b)] r

/-- `quatMatrix` in polynomials. -/
def qmP (q : Fin 4 → RationalPolynomial) : Fin 3 → Fin 3 → RationalPolynomial :=
  let sq := fun i ↦ mul (q i) (q i)
  let pr := fun i j ↦ mul (q i) (q j)
  ![![add (add (sq 0) (sq 1)) (neg (add (sq 2) (sq 3))), mul (const 2) (add (pr 1 2) (neg (pr 0 3))),
      mul (const 2) (add (pr 1 3) (pr 0 2))],
    ![mul (const 2) (add (pr 1 2) (pr 0 3)), add (add (sq 0) (sq 2)) (neg (add (sq 1) (sq 3))),
      mul (const 2) (add (pr 2 3) (neg (pr 0 1)))],
    ![mul (const 2) (add (pr 1 3) (neg (pr 0 2))), mul (const 2) (add (pr 2 3) (pr 0 1)),
      add (add (sq 0) (sq 3)) (neg (add (sq 1) (sq 2)))]]

/-- `|q|²` in polynomials. -/
def qqP (q : Fin 4 → RationalPolynomial) : RationalPolynomial :=
  add (add (mul (q 0) (q 0)) (mul (q 1) (q 1))) (add (mul (q 2) (q 2)) (mul (q 3) (q 3)))

/-- The entry `(r, b)` of `R₂ Q(q) n_q` for the matrix `R₂` of the variables `x j, …`. -/
def plugP (j : ℕ) (q : Fin 4 → RationalPolynomial) (nq : RationalPolynomial) (r b : Fin 3) : RationalPolynomial :=
  mul nq (add (add (mul (var (j + 3 * r + (0 : Fin 3))) (qmP q 0 b))
    (mul (var (j + 3 * r + (1 : Fin 3))) (qmP q 1 b))) (mul (var (j + 3 * r + (2 : Fin 3))) (qmP q 2 b)))

/-- `aMap τ` in polynomials. -/
def tP (s t n₁ n₃ τ₀ τ₁ : RationalPolynomial) : Fin 2 → RationalPolynomial :=
  ![mul n₁ τ₀, mul (mul n₁ n₃) (add (mul (neg (mul s t)) τ₀) (mul (add (const 1) (mul s s)) τ₁))]

variable (x : ℕ → ℝ)

theorem eval_w₁P (a : Fin 3) (s : RationalPolynomial) (b : Fin 3) : (w₁P a s b).eval x = w₁ a (s.eval x) b := by
  unfold w₁P w₁
  split_ifs <;> simp [eval_add, eval_neg]; ring

theorem eval_w₂P (a : Fin 3) (t : RationalPolynomial) (b : Fin 3) : (w₂P a t b).eval x = w₂ a (t.eval x) b := by
  unfold w₂P w₂
  split_ifs <;> simp [eval_add, eval_neg]; ring

theorem eval_uP (a : Fin 3) (s t : RationalPolynomial) (b : Fin 3) :
    (uP a s t b).eval x = uv a (s.eval x) (t.eval x) b := by
  unfold uP uv
  split_ifs <;> simp

theorem eval_holeP (a : Fin 3) (s t n₁ n₃ : RationalPolynomial) (r b : Fin 3) :
    (holeP a s t n₁ n₃ r b).eval x =
      holeMat a (s.eval x) (t.eval x) (n₁.eval x) (n₃.eval x) r b := by
  fin_cases r <;>
    simp [holeP, holeMat, eval_mul, eval_add, eval_neg, eval_w₁P, eval_w₂P, eval_uP]

theorem eval_qmP (q : Fin 4 → RationalPolynomial) (c b : Fin 3) :
    (qmP q c b).eval x = quatMatrix (fun i ↦ (q i).eval x) c b := by
  fin_cases c <;> fin_cases b <;> simp [qmP, quatMatrix, eval_mul, eval_add, eval_neg] <;> ring

theorem eval_qqP (q : Fin 4 → RationalPolynomial) :
    (qqP q).eval x = (fun i ↦ (q i).eval x) ⬝ᵥ (fun i ↦ (q i).eval x) := by
  simp [qqP, dotProduct, Fin.sum_univ_four, eval_mul, eval_add]
  ring

theorem eval_plugP (j : ℕ) (q : Fin 4 → RationalPolynomial) (nq : RationalPolynomial) (r b : Fin 3) :
    (plugP j q nq r b).eval x =
      nq.eval x * ∑ c, matAt x j r c * quatMatrix (fun i ↦ (q i).eval x) c b := by
  simp only [plugP, eval_mul, eval_add, eval_var, eval_qmP, Fin.sum_univ_three, matAt]

theorem eval_tP (s t n₁ n₃ τ₀ τ₁ : RationalPolynomial) (i : Fin 2) :
    (tP s t n₁ n₃ τ₀ τ₁ i).eval x =
      aMap (s.eval x) (t.eval x) (n₁.eval x) (n₃.eval x) ![τ₀.eval x, τ₁.eval x] i := by
  fin_cases i <;> simp [tP, aMap, eval_mul, eval_add, eval_neg]

end RationalPolynomial

/-! ### The pose's variables -/

namespace PolynomialSystem

open RationalPolynomial PoseCheck

/-- The equations of the helpers `n₁ = x n`, `n₃ = x (n + 1)`, `n_q = x (n + 2)`. -/
def helperEqs (n : ℕ) (s t : RationalPolynomial) (q : Fin 4 → RationalPolynomial) : List (RationalPolynomial × RationalPolynomial) :=
  [(mul (add (const 1) (mul s s)) (mul (var n) (var n)), const 1),
    (mul (add (add (const 1) (mul s s)) (mul t t)) (mul (var (n + 1)) (var (n + 1))), const 1),
    (mul (qqP q) (var (n + 2)), const 1)]

/-- `S` with the three helpers, each in `[0, 1]` (module docs). -/
def helperExt (S : PolynomialSystem) (s t : RationalPolynomial) (q : Fin 4 → RationalPolynomial) : PolynomialSystem :=
  ⟨helperEqs S.box.length s t q ++ S.eqs, S.box ++ [(0, 1), (0, 1), (0, 1)]⟩

/-- The helpers' check: `s`, `t`, `q` are polynomials in `S`'s variables (and the extension is
boxed), and some `qₘ` has an interval value on `S`'s box outside `(-1, 1)`, so `|q|² ≥ 1` at every
root of `S`. -/
def helpersOk (S : PolynomialSystem) (s t : RationalPolynomial) (q : Fin 4 → RationalPolynomial) : Bool :=
  (helperExt S s t q).boxed && s.varsLt S.box.length && t.varsLt S.box.length &&
    (List.finRange 4).all (fun m ↦ (q m).varsLt S.box.length) &&
    (List.finRange 4).any fun m ↦
      decide (1 ≤ (ival S.box (q m)).1 ∨ (ival S.box (q m)).2 ≤ -1)

/-- The places of a `3 × 3` matrix, row by row. -/
def places : List (Fin 3 × Fin 3) := [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

/-- The definitions of the pose's twenty variables after the helpers of `n` variables: `R₂` at
`x (n + 3), …`, `R₁` at `x (n + 12), …`, `t` at `x (n + 21)`, `x (n + 22)`. -/
def poseDefs (n : ℕ) (a : Fin 3) (s t : RationalPolynomial) (q : Fin 4 → RationalPolynomial) (τ₀ τ₁ : RationalPolynomial) :
    List RationalPolynomial :=
  places.map (fun p ↦ holeP a s t (var n) (var (n + 1)) p.1 p.2) ++
    places.map (fun p ↦ plugP (n + 3) q (var (n + 2)) p.1 p.2) ++
    [tP s t (var n) (var (n + 1)) τ₀ τ₁ 0, tP s t (var n) (var (n + 1)) τ₀ τ₁ 1]

/-- The equations `x m = d₀`, `x (m + 1) = d₁`, … -/
def defEqs : ℕ → List RationalPolynomial → List (RationalPolynomial × RationalPolynomial)
  | _, [] => []
  | m, d :: ds => (var m, d) :: defEqs (m + 1) ds

theorem mem_defEqs : ∀ (m : ℕ) (ds : List RationalPolynomial) (k : ℕ), k < ds.length →
    (var (m + k), ds.getD k []) ∈ defEqs m ds
  | _, [], _, h => absurd h (Nat.not_lt_zero _)
  | m, d :: ds, 0, _ => by simp [defEqs]
  | m, d :: ds, k + 1, h => by
    rw [defEqs]
    refine List.mem_cons_of_mem _ ?_
    have := mem_defEqs (m + 1) ds k (by simpa using h)
    rwa [show m + 1 + k = m + (k + 1) by omega] at this

/-- **`S` with the pose** (module docs): the helpers, then the twenty explicit definitions with
the intervals `B`. -/
def poseExt (S : PolynomialSystem) (a : Fin 3) (s t : RationalPolynomial) (q : Fin 4 → RationalPolynomial) (τ₀ τ₁ : RationalPolynomial)
    (B : List (ℚ × ℚ)) : PolynomialSystem :=
  ⟨defEqs (S.box.length + 3) (poseDefs S.box.length a s t q τ₀ τ₁) ++ (helperExt S s t q).eqs,
    (helperExt S s t q).box ++ B⟩

section Helpers

variable {S : PolynomialSystem} {s t : RationalPolynomial} {q : Fin 4 → RationalPolynomial}

theorem one_le_qq (h : helpersOk S s t q = true) {y : ℕ → ℝ} (hy : S.Solves y) :
    1 ≤ (qqP q).eval y := by
  simp only [helpersOk, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨-, -⟩, -⟩, hv⟩, m, -, hm⟩ := h
  have hI := inI_ival (B := S.box) (x := y) (fun i hi ↦ hy.1 i hi) (q m) (hv m (List.mem_finRange m))
  have hsq : 1 ≤ (q m).eval y * (q m).eval y := by
    rcases hm with hm | hm
    · have : (1 : ℝ) ≤ (q m).eval y := le_trans (by exact_mod_cast hm) hI.1
      nlinarith
    · have : (q m).eval y ≤ -1 := le_trans hI.2 (by exact_mod_cast hm)
      nlinarith
  rw [eval_qqP]
  simp only [dotProduct, Fin.sum_univ_four]
  fin_cases m <;> simp at hsq <;> nlinarith [mul_self_nonneg ((q 0).eval y),
    mul_self_nonneg ((q 1).eval y), mul_self_nonneg ((q 2).eval y), mul_self_nonneg ((q 3).eval y)]

/-- The helpers' values at a point of `S`. -/
noncomputable def helperPt (S : PolynomialSystem) (s t : RationalPolynomial) (q : Fin 4 → RationalPolynomial) (x : ℕ → ℝ) :
    ℕ → ℝ := fun i ↦
  if i < S.box.length then x i
  else if i = S.box.length then (Real.sqrt (1 + s.eval x * s.eval x))⁻¹
  else if i = S.box.length + 1 then (Real.sqrt (1 + s.eval x * s.eval x + t.eval x * t.eval x))⁻¹
  else ((qqP q).eval x)⁻¹

theorem helperPt_lt (x : ℕ → ℝ) {i : ℕ} (hi : i < S.box.length) : helperPt S s t q x i = x i := by
  simp [helperPt, hi]

theorem sqrt_inv_facts {A : ℝ} (hA : 1 ≤ A) :
    A * ((Real.sqrt A)⁻¹ * (Real.sqrt A)⁻¹) = 1 ∧ 0 ≤ (Real.sqrt A)⁻¹ ∧ (Real.sqrt A)⁻¹ ≤ 1 := by
  have h0 : 0 ≤ A := by linarith
  have hs : 1 ≤ Real.sqrt A := Real.one_le_sqrt.mpr hA
  refine ⟨?_, inv_nonneg.mpr (Real.sqrt_nonneg _), inv_le_one_of_one_le₀ hs⟩
  rw [← mul_inv, Real.mul_self_sqrt h0, mul_inv_cancel₀ (by linarith)]

/-- A root of `S` with the helpers' values is a root of `helperExt`. -/
theorem helperPt_solves (h : helpersOk S s t q = true) (hb : S.boxed = true) {x : ℕ → ℝ}
    (hx : S.Solves x) : (helperExt S s t q).Solves (helperPt S s t q x) := by
  have hv := h
  simp only [helpersOk, Bool.and_eq_true, List.all_eq_true] at hv
  obtain ⟨⟨⟨⟨-, hs⟩, ht⟩, hq⟩, -⟩ := hv
  set n := S.box.length
  have hagree : ∀ i < n, helperPt S s t q x i = x i := fun i hi ↦ helperPt_lt x hi
  have es : s.eval (helperPt S s t q x) = s.eval x := eval_congr hagree s hs
  have et : t.eval (helperPt S s t q x) = t.eval x := eval_congr hagree t ht
  have eq : (qqP q).eval (helperPt S s t q x) = (qqP q).eval x := by
    rw [eval_qqP, eval_qqP]
    congr 1 <;> funext m <;> exact eval_congr hagree _ (hq m (List.mem_finRange m))
  have hQ := one_le_qq h hx
  have f₁ := sqrt_inv_facts (A := 1 + s.eval x * s.eval x) (by nlinarith)
  have f₃ := sqrt_inv_facts (A := 1 + s.eval x * s.eval x + t.eval x * t.eval x) (by nlinarith)
  have hn : helperPt S s t q x n = (Real.sqrt (1 + s.eval x * s.eval x))⁻¹ := by simp [helperPt, n]
  have hn1 : helperPt S s t q x (n + 1) =
      (Real.sqrt (1 + s.eval x * s.eval x + t.eval x * t.eval x))⁻¹ := by simp [helperPt, n]
  have hn2 : helperPt S s t q x (n + 2) = ((qqP q).eval x)⁻¹ := by simp [helperPt, n]
  refine ⟨fun i hi ↦ ?_, fun e he ↦ ?_⟩
  · simp only [helperExt, List.length_append, List.length_cons, List.length_nil] at hi
    by_cases h' : i < n
    · simp only [helperExt]
      rw [List.getD_append _ _ _ _ h', helperPt_lt x h']
      exact hx.1 i h'
    · simp only [helperExt]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
      rw [Nat.add_sub_cancel_left]
      have hk : k < 3 := by omega
      interval_cases k
      · rw [Nat.add_zero, hn]
        simp only [List.getD_cons_zero, Rat.cast_zero, Rat.cast_one]
        exact ⟨f₁.2.1, f₁.2.2⟩
      · rw [hn1]
        simp only [List.getD_cons_succ, List.getD_cons_zero, Rat.cast_zero, Rat.cast_one]
        exact ⟨f₃.2.1, f₃.2.2⟩
      · rw [hn2]
        simp only [List.getD_cons_succ, List.getD_cons_zero, Rat.cast_zero, Rat.cast_one]
        exact ⟨inv_nonneg.mpr (by linarith), inv_le_one_of_one_le₀ hQ⟩
  · simp only [helperExt, helperEqs, List.mem_append, List.mem_cons, List.mem_nil_iff,
      or_false] at he
    rcases he with (rfl | rfl | rfl) | he
    · simp only [eval_mul, eval_add, eval_const, eval_var, es, Rat.cast_one]
      rw [hn]; exact f₁.1
    · simp only [eval_mul, eval_add, eval_const, eval_var, es, et, Rat.cast_one]
      rw [hn1]; exact f₃.1
    · simp only [eval_mul, eval_const, eval_var, eq, Rat.cast_one]
      rw [hn2]; exact mul_inv_cancel₀ (by linarith)
    · have hb' := List.all_eq_true.mp hb e he
      rw [Bool.and_eq_true] at hb'
      rw [eval_congr hagree _ hb'.1, eval_congr hagree _ hb'.2]
      exact hx.2 e he

/-- A root of `helperExt` is a root of `S`. -/
theorem solves_of_helperExt {y : ℕ → ℝ} (hy : (helperExt S s t q).Solves y) : S.Solves y := by
  refine ⟨fun i hi ↦ ?_, fun e he ↦ hy.2 e (List.mem_append_right _ he)⟩
  have := hy.1 i (by simp [helperExt]; omega)
  simp only [helperExt] at this
  rwa [List.getD_append _ _ _ _ hi] at this

/-- **The helpers keep the one root and the scales.** -/
theorem HasUniqueRoot.of_helperExt (hS : S.HasUniqueRoot) (h : helpersOk S s t q = true) :
    (helperExt S s t q).HasUniqueRoot ∧ scales [helperExt S s t q] = scales [S] := by
  obtain ⟨h0, hb, x, hx, hu⟩ := hS
  have hv := h
  simp only [helpersOk, Bool.and_eq_true, List.all_eq_true] at hv
  obtain ⟨⟨⟨⟨hb', hs⟩, ht⟩, hq⟩, -⟩ := hv
  set n := S.box.length
  have hx' := helperPt_solves h hb hx
  refine ⟨⟨by simp only [helperExt, List.length_append, List.length_cons, List.length_nil]; omega,
    hb', helperPt S s t q x, hx', fun y hy ↦ ?_⟩, ?_⟩
  · have hyS := solves_of_helperExt hy
    have hag : ∀ i < n, y i = helperPt S s t q x i := fun i hi ↦ by
      rw [hu y hyS i hi, helperPt_lt x hi]
    set z := helperPt S s t q x
    have es : s.eval y = s.eval z := eval_congr hag s hs
    have et : t.eval y = t.eval z := eval_congr hag t ht
    have eq : (qqP q).eval y = (qqP q).eval z := by
      rw [eval_qqP, eval_qqP]
      congr 1 <;> funext m <;> exact eval_congr hag _ (hq m (List.mem_finRange m))
    have mem : ∀ e ∈ helperEqs n s t q, e.1.eval y = e.2.eval y ∧ e.1.eval z = e.2.eval z :=
      fun e he ↦ ⟨hy.2 e (List.mem_append_left _ he), hx'.2 e (List.mem_append_left _ he)⟩
    have box : ∀ k < 3, 0 ≤ y (n + k) ∧ 0 ≤ z (n + k) := fun k hk ↦ by
      have hl : (helperExt S s t q).box.length = n + 3 := by simp [helperExt, n]
      have h1 := hy.1 (n + k) (by omega)
      have h2 := hx'.1 (n + k) (by omega)
      simp only [helperExt] at h1 h2
      rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left] at h1 h2
      interval_cases k <;> simp at h1 h2 <;> exact ⟨h1.1, h2.1⟩
    intro i hi
    simp only [helperExt, List.length_append, List.length_cons, List.length_nil] at hi
    by_cases h' : i < n
    · exact hag i h'
    obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
    have hk : k < 3 := by omega
    interval_cases k
    · obtain ⟨e1, e2⟩ := mem (mul (add (const 1) (mul s s)) (mul (var n) (var n)), const 1)
        (by simp [helperEqs])
      simp only [eval_mul, eval_add, eval_const, eval_var, Rat.cast_one] at e1 e2
      rw [es] at e1
      have hA : 0 < 1 + s.eval z * s.eval z := by nlinarith [mul_self_nonneg (s.eval z)]
      have := mul_left_cancel₀ hA.ne' (e1.trans e2.symm)
      exact (mul_self_inj (box 0 (by norm_num)).1 (box 0 (by norm_num)).2).mp this
    · obtain ⟨e1, e2⟩ := mem (mul (add (add (const 1) (mul s s)) (mul t t))
        (mul (var (n + 1)) (var (n + 1))), const 1) (by simp [helperEqs])
      simp only [eval_mul, eval_add, eval_const, eval_var, Rat.cast_one] at e1 e2
      rw [es, et] at e1
      have hA : 0 < 1 + s.eval z * s.eval z + t.eval z * t.eval z := by
        nlinarith [mul_self_nonneg (s.eval z), mul_self_nonneg (t.eval z)]
      have := mul_left_cancel₀ hA.ne' (e1.trans e2.symm)
      exact (mul_self_inj (box 1 (by norm_num)).1 (box 1 (by norm_num)).2).mp this
    · obtain ⟨e1, e2⟩ := mem (mul (qqP q) (var (n + 2)), const 1) (by simp [helperEqs])
      simp only [eval_mul, eval_const, eval_var, Rat.cast_one] at e1 e2
      rw [eq] at e1
      have hQ := one_le_qq h (solves_of_helperExt hx')
      exact mul_left_cancel₀ (by linarith) (e1.trans e2.symm)
  · ext l
    simp only [scales, Set.mem_ofPred_eq, List.mem_singleton, exists_eq_left]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, solves_of_helperExt hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨helperPt S s t q y, helperPt_solves h hb hy, helperPt_lt y h0⟩

end Helpers

/-- **The pose keeps the one root and the scales**: the helpers (`helpersOk`), then the twenty
definitions (`auxOk`, which checks that the intervals `B` hold their interval values). -/
theorem HasUniqueRoot.of_poseExt {S : PolynomialSystem} {a : Fin 3} {s t : RationalPolynomial} {q : Fin 4 → RationalPolynomial}
    {τ₀ τ₁ : RationalPolynomial} {B : List (ℚ × ℚ)} (hS : S.HasUniqueRoot) (h : helpersOk S s t q = true)
    (hb : (helperExt S s t q).auxOk (poseExt S a s t q τ₀ τ₁ B) 20 = true) :
    (poseExt S a s t q τ₀ τ₁ B).HasUniqueRoot ∧ scales [poseExt S a s t q τ₀ τ₁ B] = scales [S] := by
  have h₂ := HasUniqueRoot.of_helperExt hS h
  have h₃ := HasUniqueRoot.of_auxOk hb h₂.1
  exact ⟨h₃.1, h₃.2.trans h₂.2⟩

theorem poseDefs_hole (n : ℕ) (a : Fin 3) (s t : RationalPolynomial) (q : Fin 4 → RationalPolynomial) (τ₀ τ₁ : RationalPolynomial)
    (r c : Fin 3) : (poseDefs n a s t q τ₀ τ₁).getD (3 * r + c) [] =
      holeP a s t (var n) (var (n + 1)) r c := by
  fin_cases r <;> fin_cases c <;> rfl

theorem poseDefs_plug (n : ℕ) (a : Fin 3) (s t : RationalPolynomial) (q : Fin 4 → RationalPolynomial) (τ₀ τ₁ : RationalPolynomial)
    (r c : Fin 3) : (poseDefs n a s t q τ₀ τ₁).getD (9 + 3 * r + c) [] =
      plugP (n + 3) q (var (n + 2)) r c := by
  fin_cases r <;> fin_cases c <;> rfl

/-- **The pose at a root**: at a solution of `poseExt`, a weak fit in screen coordinates at the
values of `s, t, q, τ` and the scale `x 0` is the weak fit `PoseAt` of the pose's variables. -/
theorem poseExt_poseAt {S : PolynomialSystem} {a : Fin 3} {s t : RationalPolynomial} {q : Fin 4 → RationalPolynomial}
    {τ₀ τ₁ : RationalPolynomial} {B : List (ℚ × ℚ)} {P : Polyhedron} {x : ℕ → ℝ}
    (hx : (poseExt S a s t q τ₀ τ₁ B).Solves x)
    (hw : ScreenWeak P a (s.eval x) (t.eval x) (quatRotation fun m ↦ (q m).eval x)
      ![τ₀.eval x, τ₁.eval x] (x 0)) :
    PoseAt P x (S.box.length + 12) (S.box.length + 3) (S.box.length + 21) := by
  set n := S.box.length
  have he := hx.2
  have hdef : ∀ k < 20, x (n + 3 + k) = ((poseDefs n a s t q τ₀ τ₁).getD k []).eval x := by
    intro k hk
    have := he _ (List.mem_append_left _ (mem_defEqs (n + 3) _ k (by simp [poseDefs, places]; omega)))
    simpa using this
  have hh : ∀ e ∈ helperEqs n s t q, e.1.eval x = e.2.eval x := fun e he' ↦
    he e (List.mem_append_right _ (List.mem_append_left _ he'))
  have h₁ := hh (mul (add (const 1) (mul s s)) (mul (var n) (var n)), const 1) (by simp [helperEqs])
  have h₃ := hh (mul (add (add (const 1) (mul s s)) (mul t t)) (mul (var (n + 1)) (var (n + 1))),
    const 1) (by simp [helperEqs])
  have hq := hh (mul (qqP q) (var (n + 2)), const 1) (by simp [helperEqs])
  simp only [eval_mul, eval_add, eval_const, eval_var, Rat.cast_one] at h₁ h₃ hq
  rw [eval_qqP] at hq
  set Q : Fin 4 → ℝ := fun m ↦ (q m).eval x
  have hQ : Q ≠ 0 := fun h0 ↦ by rw [h0] at hq; simp at hq
  have hj : matAt x (n + 3) = holeMat a (s.eval x) (t.eval x) (x n) (x (n + 1)) := by
    ext r c
    rw [show matAt x (n + 3) r c = x (n + 3 + (3 * r + c)) by simp [matAt]; ring_nf,
      hdef _ (by omega), poseDefs_hole, eval_holeP, eval_var, eval_var]
  refine poseAt_of h₁ h₃ hQ hj ?_ ?_ hw
  · ext r c
    rw [show matAt x (n + 12) r c = x (n + 3 + (9 + 3 * r + c)) by simp [matAt]; ring_nf,
      hdef _ (by omega), poseDefs_plug, eval_plugP, eval_var, Matrix.mul_apply, quatRotation]
    have hinv : x (n + 2) = (Q ⬝ᵥ Q)⁻¹ := eq_inv_of_mul_eq_one_right hq
    simp only [hinv, Matrix.smul_apply, smul_eq_mul, hj, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' _ ↦ ?_
    simp only [Q]
    ring
  · ext i
    have h18 := hdef 18 (by norm_num)
    have h19 := hdef 19 (by norm_num)
    rw [show n + 3 + 18 = n + 21 by omega, show (poseDefs n a s t q τ₀ τ₁).getD 18 [] =
      tP s t (var n) (var (n + 1)) τ₀ τ₁ 0 from rfl, eval_tP] at h18
    rw [show n + 3 + 19 = n + 21 + 1 by omega, show (poseDefs n a s t q τ₀ τ₁).getD 19 [] =
      tP s t (var n) (var (n + 1)) τ₀ τ₁ 1 from rfl, eval_tP] at h19
    simp only [eval_var] at h18 h19
    fin_cases i
    · simpa using h18
    · simpa using h19

end PolynomialSystem

/-! ### Closed forms -/

namespace PolynomialSystem

open RationalPolynomial PoseCheck Check

variable {R : Root}

/-- The exact value `z` of `ℤ[α]` as a polynomial in the variable `x v` (`α`). -/
def zP (v : ℕ) (z : ZTheta R) : RationalPolynomial := ofUni v (z.c.map (↑))

/-- The constant coordinate of an exact value. -/
def cv (z : ZTheta R) : ℚ := z.c.headD 0

theorem eval_ofUni_int (l : List ℤ) (v : ℕ) (x : ℕ → ℝ) :
    (ofUni v (l.map (↑))).eval x = ∑ j ∈ Finset.range l.length, (l.getD j 0 : ℝ) * x v ^ j := by
  rw [eval_ofUni, List.length_map]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

theorem eval_zP {z : ZTheta R} (hz : z.c.length ≤ R.n) {v : ℕ} {x : ℕ → ℝ} (hx : x v = R.α) :
    (zP v z).eval x = Exact.re z := by
  obtain ⟨l⟩ := z
  rw [zP, eval_ofUni_int, ZTheta.re_mk, hx]
  refine (Finset.sum_subset (Finset.range_subset_range.mpr hz) fun j _ hj ↦ ?_).trans ?_
  · rw [List.getD_eq_default _ _ (by simpa using hj)]; simp
  · exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

theorem eval_ofUni_evalZ (N : List ℤ) (v : ℕ) (x : ℕ → ℝ) :
    (ofUni v (N.map (↑))).eval x = evalZ N (x v) := by
  rw [eval_ofUni_int, evalZ_eq_sum le_rfl]

theorem re_eq_cv {z : ZTheta R} (h : z.c.length ≤ 1) : Exact.re z = (cv z : ℝ) := by
  obtain ⟨l⟩ := z
  match l, h with
  | [], _ => simp [cv]
  | [d], _ => simpa [cv] using ZTheta.re_const (R := R) d

/-- The closed form's base: `ℓ = x 0` with the equations and the interval of `S₀` (in `ℓ`
alone), `α = x 1` with `N(α) = 0` in the interval `I`, and `scaleDen ℓ = scaleNum(α)`. -/
def cfBase (S₀ : PolynomialSystem) (R : Root) (W : WeakFitData (ZTheta R)) (I : ℚ × ℚ) : PolynomialSystem :=
  ⟨[(ofUni 1 (R.N.map (↑)), []), (mul (const (W.scaleDen : ℚ)) (var 0), zP 1 W.scaleNum)] ++ S₀.eqs,
    S₀.box ++ [I]⟩

/-- The scale `λ = scaleNum(α) / scaleDen` as a polynomial in `x 0` (`α`). -/
def cfScale (W : WeakFitData (ZTheta R)) : RationalPolynomial :=
  mul (const (1 / (W.scaleDen : ℚ))) (zP 0 W.scaleNum)

/-- The base's check (module docs): `S₀` is in `ℓ` alone; `I` lies in the root's isolating
interval and holds its enclosure; `λ` lies in `S₀`'s interval (interval value on `I`); and each
equation of `S₀` at `ℓ = λ` is `Q_e N` (as polynomials in `α`). -/
def cfBaseOk (S₀ : PolynomialSystem) (R : Root) (W : WeakFitData (ZTheta R)) (I : ℚ × ℚ)
    (Q : List RationalPolynomial) : Bool :=
  S₀.box.length == 1 && (cfBase S₀ R W I).boxed &&
    decide ((R.A : ℚ) / R.E ≤ I.1 ∧ I.2 ≤ (R.B : ℚ) / R.E ∧ I.1 ≤ (R.Xl : ℚ) / R.D ∧
      (R.Xh : ℚ) / R.D ≤ I.2) &&
    decide (0 < W.scaleDen) && decide (W.scaleNum.c.length ≤ R.n) && (cfScale W).varsLt 1 &&
    decide ((S₀.box.getD 0 (0, 0)).1 ≤ (ival [I] (cfScale W)).1 ∧
      (ival [I] (cfScale W)).2 ≤ (S₀.box.getD 0 (0, 0)).2) &&
    (List.range S₀.eqs.length).all fun e ↦
      (add (substP (fun _ ↦ cfScale W)
          (add (S₀.eqs.getD e ([], [])).1 (neg (S₀.eqs.getD e ([], [])).2)))
        (neg (mul (Q.getD e []) (ofUni 0 (R.N.map (↑)))))).isEmpty

/-- **The base has one root**, `(λ, α)`, and `λ` is the scale `N` of `S₀`'s root. -/
theorem cfBase_root {S₀ : PolynomialSystem} {W : WeakFitData (ZTheta R)} {I : ℚ × ℚ}
    {Q : List RationalPolynomial} {N : ℝ} (hok : cfBaseOk S₀ R W I Q = true)
    (hS₀ : S₀.HasUniqueRoot ∧ scales [S₀] = {N}) :
    (cfBase S₀ R W I).HasUniqueRoot ∧ scales [cfBase S₀ R W I] = {N} ∧
      ∀ x, (cfBase S₀ R W I).Solves x → x 1 = R.α ∧ x 0 = W.scale := by
  simp only [cfBaseOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hlen, hb⟩, hA, hB, hXl, hXh⟩, hG⟩, hn⟩, hL⟩, hbox⟩, hid⟩ := hok
  obtain ⟨hl, hh, h0⟩ := R.spec
  have hS₀b : S₀.boxed = true := hS₀.1.2.1
  have hG' : (0 : ℝ) < W.scaleDen := by exact_mod_cast hG
  have hE : (0 : ℝ) < R.E := by
    have := R.coarse
    simp only [coarseCheck, Bool.and_eq_true, decide_eq_true_eq] at this
    exact_mod_cast this.1.1.1.1.1.1
  have hD : (0 : ℝ) < R.D := by exact_mod_cast R.D_pos
  -- `α` lies in `I`, `I` in the isolating interval
  have hI1 : ((I.1 : ℚ) : ℝ) ≤ R.α := le_trans (by
    have := (Rat.cast_le (K := ℝ)).mpr hXl; push_cast at this; exact this) hl
  have hI2 : R.α ≤ ((I.2 : ℚ) : ℝ) := le_trans hh (by
    have := (Rat.cast_le (K := ℝ)).mpr hXh; push_cast at this; exact this)
  have hiso : ∀ y : ℝ, ((I.1 : ℚ) : ℝ) ≤ y → y ≤ ((I.2 : ℚ) : ℝ) → evalZ R.N y = 0 → R.α = y :=
    fun y h1 h2 hy ↦ R.eq_of_root (le_trans (by
      have := (Rat.cast_le (K := ℝ)).mpr hA; push_cast at this; exact this) h1) (le_trans h2 (by
      have := (Rat.cast_le (K := ℝ)).mpr hB; push_cast at this; exact this)) hy
  -- the scale
  have hLy : (cfScale W).eval (fun _ ↦ R.α) = W.scale := by
    rw [cfScale, eval_mul, eval_const, eval_zP hn rfl, WeakFitData.scale]
    push_cast
    field_simp
  have hIv := inI_ival (B := [I]) (x := fun _ ↦ R.α) (fun i hi ↦ by
    simp only [List.length_cons, List.length_nil] at hi
    obtain rfl : i = 0 := by omega
    exact ⟨hI1, hI2⟩) (cfScale W) hL
  rw [hLy] at hIv
  -- `λ` solves `S₀`
  let x₀ : ℕ → ℝ := fun i ↦ if i = 0 then W.scale else R.α
  have hS₀x : S₀.Solves x₀ := by
    refine ⟨fun i hi ↦ ?_, fun e he ↦ ?_⟩
    · obtain rfl : i = 0 := by omega
      exact ⟨le_trans (by exact_mod_cast hbox.1) hIv.1, le_trans hIv.2 (by exact_mod_cast hbox.2)⟩
    · obtain ⟨k, hk, rfl⟩ := exists_getD_of_mem he
      have h := congrArg (fun p : RationalPolynomial ↦ p.eval (fun _ ↦ R.α)) (List.isEmpty_iff.mp (hid k hk))
      simp only [eval_add, eval_neg, eval_mul, eval_substP, eval_ofUni_evalZ, h0, mul_zero,
        neg_zero, add_zero, eval_nil, hLy] at h
      have hb' := List.all_eq_true.mp hS₀b _ he
      rw [Bool.and_eq_true, hlen] at hb'
      have hag : ∀ i < 1, (fun _ ↦ W.scale) i = x₀ i := fun i hi ↦ by
        obtain rfl : i = 0 := by omega
        rfl
      rw [eval_congr hag _ hb'.1, eval_congr hag _ hb'.2] at h
      linarith
  have hN : W.scale = N := by
    have hm : x₀ 0 ∈ scales [S₀] := ⟨S₀, List.mem_singleton_self _, x₀, hS₀x, rfl⟩
    rw [hS₀.2] at hm
    exact hm
  -- the roots of the base
  have hroot : ∀ x, (cfBase S₀ R W I).Solves x → x 1 = R.α ∧ x 0 = W.scale := by
    intro x hx
    have hx1 := hx.1 1 (by simp [cfBase, hlen])
    simp only [cfBase] at hx1
    rw [List.getD_append_right _ _ _ _ (by omega), hlen] at hx1
    simp only [Nat.sub_self, List.getD_cons_zero] at hx1
    have hNx := hx.2 _ (show (ofUni 1 (R.N.map (↑)), ([] : RationalPolynomial)) ∈ (cfBase S₀ R W I).eqs by
      simp [cfBase])
    rw [eval_ofUni_evalZ, eval_nil] at hNx
    have ha := (hiso _ hx1.1 hx1.2 hNx).symm
    refine ⟨ha, ?_⟩
    have hlk := hx.2 _ (show (mul (const (W.scaleDen : ℚ)) (var 0), zP 1 W.scaleNum) ∈
      (cfBase S₀ R W I).eqs by simp [cfBase])
    rw [eval_mul, eval_const, eval_var, eval_zP hn ha] at hlk
    rw [WeakFitData.scale, ← hlk]
    push_cast
    field_simp
  have hx₀ : (cfBase S₀ R W I).Solves x₀ := by
    refine ⟨fun i hi ↦ ?_, fun e he ↦ ?_⟩
    · simp only [cfBase, List.length_append, hlen, List.length_cons, List.length_nil] at hi
      simp only [cfBase]
      by_cases h' : i = 0
      · subst h'
        rw [List.getD_append _ _ _ _ (by omega)]
        exact hS₀x.1 0 (by omega)
      · obtain rfl : i = 1 := by omega
        rw [List.getD_append_right _ _ _ _ (by omega), hlen]
        exact ⟨hI1, hI2⟩
    · simp only [cfBase, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at he
      rcases he with (rfl | rfl) | he
      · simp only [eval_ofUni_evalZ, eval_nil]
        exact h0
      · have hx0 : x₀ 0 = W.scale := rfl
        simp only [eval_mul, eval_const, eval_var]
        rw [eval_zP hn (show x₀ 1 = R.α from rfl), hx0, WeakFitData.scale]
        push_cast
        field_simp
      · exact hS₀x.2 e he
  refine ⟨⟨by simp [cfBase], hb, x₀, hx₀, fun y hy ↦ ?_⟩, ?_, hroot⟩
  · intro i hi
    simp only [cfBase, List.length_append, hlen, List.length_cons, List.length_nil] at hi
    obtain ⟨h1, h0'⟩ := hroot y hy
    by_cases h' : i = 0
    · subst h'; simp [x₀, h0']
    · obtain rfl : i = 1 := by omega
      simp [x₀, h1]
  · ext l
    simp only [scales, Set.mem_ofPred_eq, List.mem_singleton, exists_eq_left,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [(hroot y hy).2, hN]
    · rintro rfl
      exact ⟨x₀, hx₀, by simp [x₀, hN]⟩

/-- The definitions of `s, t, q₀, …, q₃, τ₀, τ₁` (`x 2, …, x 9`) as polynomials in `α = x 1`:
the fit data's values, the translation times `κ`. -/
def cfCoreDefs (W : WeakFitData (ZTheta R)) (κ : ℚ) : List RationalPolynomial :=
  [mul (const (1 / cv W.fit.D)) (zP 1 W.fit.S), mul (const (1 / cv W.fit.D)) (zP 1 W.fit.T),
    zP 1 (W.fit.q.get 0), zP 1 (W.fit.q.get 1), zP 1 (W.fit.q.get 2), zP 1 (W.fit.q.get 3),
    mul (const (κ / cv W.fit.E)) (zP 1 W.fit.τ₀), mul (const (κ / cv W.fit.E)) (zP 1 W.fit.τ₁)]

/-- The base with the pose's coordinates in the intervals `B₁`. -/
def cfCore (T : PolynomialSystem) (W : WeakFitData (ZTheta R)) (κ : ℚ) (B₁ : List (ℚ × ℚ)) :
    PolynomialSystem :=
  ⟨defEqs 2 (cfCoreDefs W κ) ++ T.eqs, T.box ++ B₁⟩

/-- The quaternion's variables. -/
def cfQuat : Fin 4 → RationalPolynomial := ![var 4, var 5, var 6, var 7]

/-- **The closed form's pose system** (module docs). -/
def cfSystem (S₀ : PolynomialSystem) (R : Root) (W : WeakFitData (ZTheta R)) (κ : ℚ) (I : ℚ × ℚ)
    (B₁ B₃ : List (ℚ × ℚ)) : PolynomialSystem :=
  poseExt (cfCore (cfBase S₀ R W I) W κ B₁) W.fit.view (var 2) (var 3) cfQuat (var 8) (var 9) B₃

/-- **The closed form's check**: the base (`cfBaseOk`), the eight definitions and the pose
(`auxOk`, `helpersOk`), and the exact values in the lift's basis with constant denominators. -/
def cfOk (S₀ : PolynomialSystem) (R : Root) (W : WeakFitData (ZTheta R)) (κ : ℚ) (I : ℚ × ℚ)
    (B₁ B₃ : List (ℚ × ℚ)) (Q : List RationalPolynomial) : Bool :=
  let T := cfBase S₀ R W I
  let C := cfCore T W κ B₁
  cfBaseOk S₀ R W I Q && T.auxOk C 8 && helpersOk C (var 2) (var 3) cfQuat &&
    (helperExt C (var 2) (var 3) cfQuat).auxOk (cfSystem S₀ R W κ I B₁ B₃) 20 &&
    decide (W.fit.D.c.length ≤ 1 ∧ W.fit.E.c.length ≤ 1 ∧ cv W.fit.D ≠ 0 ∧ cv W.fit.E ≠ 0) &&
    [W.fit.S, W.fit.T, W.fit.q.get 0, W.fit.q.get 1, W.fit.q.get 2, W.fit.q.get 3, W.fit.τ₀,
      W.fit.τ₁].all fun z ↦ decide (z.c.length ≤ R.n)

/-- **A closed form's pose root**: with the representatives' theorem for `S₀`, a passing weak fit
check of the lift's points `pts`, and the polyhedron `P` the lift's points scaled by `κ`, the
system `cfSystem` has one root, of scale `N`, and its pose is a weak fit of `P` scaled by `N`
through `P`. -/
theorem cf_isPoseRoot {S₀ : PolynomialSystem} {W : WeakFitData (ZTheta R)} {pts : List (V3 (ZTheta R))}
    {κ : ℚ} {I : ℚ × ℚ} {B₁ B₃ : List (ℚ × ℚ)} {Q : List RationalPolynomial} {N : ℝ} {P : Polyhedron}
    (hS₀ : IsRootEq [S₀] N) (hW : W.check pts = true)
    (hP : P = (Polyhedron.ofPoints pts).smul (κ : ℝ)) (hok : cfOk S₀ R W κ I B₁ B₃ Q = true) :
    IsPoseRoot P (cfSystem S₀ R W κ I B₁ B₃) N 22 13 31 := by
  simp only [cfOk, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
    Bool.and_true] at hok
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hD1, hE1, hD0, hE0⟩, hS, hT, hq0, hq1, hq2, hq3, hτ0, hτ1⟩ := hok
  have hTb := cfBase_root h1 (hS₀.2 S₀ (List.mem_singleton_self _))
  have A₁ := auxFacts h2
  have h₁ := HasUniqueRoot.of_auxOk h2 hTb.1
  have h₃ := HasUniqueRoot.of_poseExt h₁.1 h3 h4
  have hlen : (cfCore (cfBase S₀ R W I) W κ B₁).box.length = 10 := by
    rw [A₁.len]
    have := h1
    simp only [cfBaseOk, Bool.and_eq_true, beq_iff_eq] at this
    simp [cfBase, this.1.1.1.1.1.1.1]
  refine ⟨h₃.1, h₃.2.trans (h₁.2.trans hTb.2.1), fun x hx ↦ ?_⟩
  have hx₂ := solves_of_aux (auxFacts h4) hx
  have hx₁ := solves_of_helperExt hx₂
  have hx₀ := solves_of_aux A₁ hx₁
  obtain ⟨hα, hℓ⟩ := hTb.2.2 x hx₀
  have hdef : ∀ k < 8, x (2 + k) = ((cfCoreDefs W κ).getD k []).eval x := by
    intro k hk
    have := hx₁.2 _ (List.mem_append_left _ (mem_defEqs 2 (cfCoreDefs W κ) k
      (by simp [cfCoreDefs]; omega)))
    simpa using this
  have hDre := re_eq_cv hD1
  have hEre := re_eq_cv hE1
  have e2 : (var 2).eval x = W.fit.pose.s := by
    rw [eval_var, hdef 0 (by norm_num)]
    simp only [cfCoreDefs, List.getD_cons_zero, eval_mul, eval_const, eval_zP hS hα]
    simp only [FitData.pose, hDre]
    push_cast
    ring
  have e3 : (var 3).eval x = W.fit.pose.t := by
    rw [eval_var, hdef 1 (by norm_num)]
    simp only [cfCoreDefs, List.getD_cons_succ, List.getD_cons_zero, eval_mul, eval_const,
      eval_zP hT hα]
    simp only [FitData.pose, hDre]
    push_cast
    ring
  have eq : (fun m ↦ (cfQuat m).eval x) = (W.fit.q.map Exact.re).toFun := by
    funext m
    rw [← FitData.re_qget]
    fin_cases m
    · show (cfQuat 0).eval x = Exact.re (W.fit.q.get 0)
      rw [show (cfQuat 0).eval x = x (2 + 2) from eval_var _ _, hdef 2 (by norm_num)]
      exact eval_zP hq0 hα
    · show (cfQuat 1).eval x = Exact.re (W.fit.q.get 1)
      rw [show (cfQuat 1).eval x = x (2 + 3) from eval_var _ _, hdef 3 (by norm_num)]
      exact eval_zP hq1 hα
    · show (cfQuat 2).eval x = Exact.re (W.fit.q.get 2)
      rw [show (cfQuat 2).eval x = x (2 + 4) from eval_var _ _, hdef 4 (by norm_num)]
      exact eval_zP hq2 hα
    · show (cfQuat 3).eval x = Exact.re (W.fit.q.get 3)
      rw [show (cfQuat 3).eval x = x (2 + 5) from eval_var _ _, hdef 5 (by norm_num)]
      exact eval_zP hq3 hα
  have hrot : quatRotation (fun m ↦ (cfQuat m).eval x) = W.fit.pose.rotation := by
    have hk : Exact.re (W.fit.q.get W.fit.rot) ≠ 0 := by
      have := hW
      simp only [WeakFitData.check, WeakFitData.checkHead, FitData.checkHead,
        Bool.and_eq_true] at this
      exact (Exact.pos_sound _ this.1.1.1.1.1.1.1.2).ne'
    rw [eq, ChartPose.rotation, chartRotation, show W.fit.pose.rot = W.fit.rot from rfl,
      W.fit.chartQuat_pose hk, FitData.quatRotation_smul (inv_ne_zero hk)]
  have eτ : ![(var 8).eval x, (var 9).eval x] = (κ : ℝ) • W.fit.translation := by
    have h8 := hdef 6 (by norm_num)
    have h9 := hdef 7 (by norm_num)
    simp only [cfCoreDefs, List.getD_cons_succ, List.getD_cons_zero, eval_mul, eval_const,
      eval_zP hτ0 hα, eval_zP hτ1 hα] at h8 h9
    ext i
    fin_cases i
    · simp only [Nat.reduceAdd] at h8
      simp only [Fin.zero_eta, Fin.isValue, cons_val_zero, Pi.smul_apply, smul_eq_mul, eval_var,
        FitData.translation, h8, hEre]
      push_cast
      ring
    · simp only [Nat.reduceAdd] at h9
      simp only [Fin.mk_one, Fin.isValue, cons_val_one, cons_val_fin_one, Pi.smul_apply,
        smul_eq_mul, eval_var, FitData.translation, h9, hEre]
      push_cast
      ring
  have hw := (W.screenWeak hW).smul (κ : ℝ)
  rw [← hP, ← hℓ, ← e2, ← e3, ← hrot, ← eτ] at hw
  have := poseExt_poseAt hx hw
  rwa [hlen] at this

end PolynomialSystem

end Nieuwland
