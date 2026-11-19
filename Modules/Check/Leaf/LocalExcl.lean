import Modules.Check.Leaf.FamilyLeaf
import Modules.Check.Chart.Image
import Modules.Check.Sign.SparsePull

/-!
# Local exclusion leaves

A local exclusion leaf of a weighted zoom (`LocalExcluded` in `code/src/proof/regional/wzoom.rs`)
on the claim box `B`, pre-rotated by `q_c` or not, uses the pose map `P` of two symmetries of the
symmetry data (`SymmData.pmap`, `Modules/Check/Chart/Image.lean`) and the local score `T = -|x - c|²` of
the rotation chart coordinates `x` of `B`, about `c = P₀ / L`, the rotation part of the zoom's
frame centre. Its polynomials are pose polynomials of the representative `(U, Q)` of a chart pose
of `B` (`Q` its chart quaternion, before the pre-rotation), with the image view `V = M U` and the
image's chart quaternion `Y = [(0, M U)] p₁ (Q q_c) p₂ conj(q_c)` in the same charts (`locVQ`, as
`imgVQ` on representatives). On the leaf box (`LocLeaf.check`):

* the chart denominators `V a` and `Y k` of the image have the strict signs the leaf states;
* every chart coordinate `num / den` of the image lies in the bounds `lo / D`, `hi / D` of `B`
  (`σ (D num - lo den) ≥ 0`, `σ (hi den - D num) ≥ 0`), or is fixed: `num den_p - den num_p`
  vanishes (it is checked `≥ 0` and `≤ 0`) for the coordinate `num_p / den_p` of the
  representative's pose, which lies in `B` at every pose of `B`;
* the improvement numerator `Y_k² ∑ᵣ (L Q_r - P₀ᵣ Q_k)² - Q_k² ∑ᵣ (L Y_r - P₀ᵣ Y_k)²`
  (`r` over the rotation coordinates, `locImprove`), divided by `x₀^e`, is positive.

So at every point of the leaf box with `x₀ > 0` that represents a pose `p` of `B`, the pose map
sends `p` to a pose `p'` of `B` whose rotation coordinates are strictly closer to `c`
(`LocalExcl`, `LocLeaf.check_sound`).

**Local exclusion** (`noFitRot_of_local`): if every pose of `B` has no fit or is locally excluded,
no pose of `B` fits. The orbit of a fit under pairs of signed symmetries is finite and consists of
fits; a maximiser of the local score over the orbit (`locScore`: `exp T` at poses of `B`, read off
the rotation by `rotQuat`, and `0` elsewhere; `FitsAlong.exists_max_ge`) is a pose of `B`, since
the fit is, and a fit, hence locally excluded, and its image lies in the orbit with a larger score.
-/

open Matrix

namespace Nieuwland.Check

/-! ### Pose polynomials of images -/

section Gen

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]
variable {α β : Type} [Add α] [Sub α] [Mul α] [Add β] [Sub β] [Mul β]

/-- The image view `M U` and the image's chart quaternion `[(0, M U)] p₁ (Q q_c) p₂ conj(q_c)` of
the representative `(U, Q)` of a chart pose of a box pre-rotated by `pre`, in the box's charts. -/
def locVQ (P : PMap κ) (pre : Option (Q4 κ)) (emb : κ → α) (U : V3 α) (Q : Q4 α) :
    V3 α × Q4 α :=
  (M3.mulVecG emb P.M U, preQ emb (P.quatG emb U (preQ emb Q pre)) (pre.map Exact.conjQ))

theorem map_locVQ {f : α → β} (hf : IsArith f) (P : PMap κ) (pre : Option (Q4 κ)) (emb : κ → α)
    (U : V3 α) (Q : Q4 α) :
    locVQ P pre (f ∘ emb) (U.map f) (Q.map f) =
      ((locVQ P pre emb U Q).1.map f, (locVQ P pre emb U Q).2.map f) := by
  simp only [locVQ, M3.map_mulVecG hf, map_preQ hf, PMap.map_quatG hf]

/-- `σ (c₁ num - c₂ den)` for chart coordinate `i` (`s, t, x₀, x₁, x₂`) of the image in the charts
`(a, k)` (`imgGen` on representatives). -/
def locCoord (P : PMap κ) (pre : Option (Q4 κ)) (a : Fin 3) (k : Fin 4) (i : ℕ) (σ c₁ c₂ : ℤ) :
    PosePoly κ where
  run emb U Q :=
    emb (Exact.ofInt σ) *
      (emb (Exact.ofInt c₁) *
          (coordND a k (locVQ P pre emb U Q).1.get (locVQ P pre emb U Q).2.toFun i).1 -
        emb (Exact.ofInt c₂) *
          (coordND a k (locVQ P pre emb U Q).1.get (locVQ P pre emb U Q).2.toFun i).2)
  natural f hf emb U Q := by
    rw [map_locVQ hf]
    have hv : ((locVQ P pre emb U Q).1.map f).get = f ∘ (locVQ P pre emb U Q).1.get :=
      funext fun j ↦ V3.get_map f _ j
    have hq : ((locVQ P pre emb U Q).2.map f).toFun = f ∘ (locVQ P pre emb U Q).2.toFun :=
      funext fun j ↦ Q4.toFun_map f _ j
    simp only [hv, hq, map_coordND, hf.map_mul, hf.map_sub, Function.comp]

/-- `σ (num den_p - den num_p)` for chart coordinate `i` of the image (`num / den`) and of the
representative (`num_p / den_p`) in the charts `(a, k)`: it vanishes where they agree. -/
def locFixed (P : PMap κ) (pre : Option (Q4 κ)) (a : Fin 3) (k : Fin 4) (i : ℕ) (σ : ℤ) :
    PosePoly κ where
  run emb U Q :=
    emb (Exact.ofInt σ) *
      ((coordND a k (locVQ P pre emb U Q).1.get (locVQ P pre emb U Q).2.toFun i).1 *
          (coordND a k U.get Q.toFun i).2 -
        (coordND a k (locVQ P pre emb U Q).1.get (locVQ P pre emb U Q).2.toFun i).2 *
          (coordND a k U.get Q.toFun i).1)
  natural f hf emb U Q := by
    rw [map_locVQ hf]
    have hv : ((locVQ P pre emb U Q).1.map f).get = f ∘ (locVQ P pre emb U Q).1.get :=
      funext fun j ↦ V3.get_map f _ j
    have hq : ((locVQ P pre emb U Q).2.map f).toFun = f ∘ (locVQ P pre emb U Q).2.toFun :=
      funext fun j ↦ Q4.toFun_map f _ j
    have hU : (U.map f).get = f ∘ U.get := funext fun j ↦ V3.get_map f _ j
    have hQ : (Q.map f).toFun = f ∘ Q.toFun := funext fun j ↦ Q4.toFun_map f _ j
    simp only [hv, hq, hU, hQ, map_coordND, hf.map_mul, hf.map_sub, Function.comp]

/-- `∑ᵣ (L z_r - P₀ᵣ z_k)²` over the rotation coordinates `r` (`k.succAbove r`) of chart `k`. -/
def locDev (emb : κ → α) (k : Fin 4) (L : ℕ) (p0 : Fin 3 → κ) (z : Fin 4 → α) : α :=
  ((emb (Exact.ofInt L) * z (k.succAbove 0) - emb (p0 0) * z k) *
      (emb (Exact.ofInt L) * z (k.succAbove 0) - emb (p0 0) * z k) +
    (emb (Exact.ofInt L) * z (k.succAbove 1) - emb (p0 1) * z k) *
      (emb (Exact.ofInt L) * z (k.succAbove 1) - emb (p0 1) * z k)) +
    (emb (Exact.ofInt L) * z (k.succAbove 2) - emb (p0 2) * z k) *
      (emb (Exact.ofInt L) * z (k.succAbove 2) - emb (p0 2) * z k)

theorem map_locDev {f : α → β} (hf : IsArith f) (emb : κ → α) (k : Fin 4) (L : ℕ)
    (p0 : Fin 3 → κ) (z : Fin 4 → α) :
    f (locDev emb k L p0 z) = locDev (f ∘ emb) k L p0 (f ∘ z) := by
  simp only [locDev, hf.map_add, hf.map_mul, hf.map_sub, Function.comp]

/-- The improvement numerator of the local score about `P₀ / L` in rotation chart `k`:
`Y_k² ∑ᵣ (L Q_r - P₀ᵣ Q_k)² - Q_k² ∑ᵣ (L Y_r - P₀ᵣ Y_k)²`. -/
def locImprove (P : PMap κ) (pre : Option (Q4 κ)) (k : Fin 4) (L : ℕ) (p0 : Fin 3 → κ) :
    PosePoly κ where
  run emb U Q :=
    (locVQ P pre emb U Q).2.toFun k * (locVQ P pre emb U Q).2.toFun k *
        locDev emb k L p0 Q.toFun -
      Q.toFun k * Q.toFun k * locDev emb k L p0 (locVQ P pre emb U Q).2.toFun
  natural f hf emb U Q := by
    rw [map_locVQ hf]
    have hq : ((locVQ P pre emb U Q).2.map f).toFun = f ∘ (locVQ P pre emb U Q).2.toFun :=
      funext fun j ↦ Q4.toFun_map f _ j
    have hQ : (Q.map f).toFun = f ∘ Q.toFun := funext fun j ↦ Q4.toFun_map f _ j
    simp only [hq, hQ, hf.map_mul, hf.map_sub, map_locDev hf, Function.comp]

end Gen

/-! ### Real values -/

section Real

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The image quaternion scales with the representatives: linearly in `q`, and in `u` for a fold. -/
theorem PMap.imgQ_smul₂ (P : PMap κ) (a b : ℝ) (u : Fin 3 → ℝ) (q : Fin 4 → ℝ) :
    P.imgQ (a • u) (b • q) = (if P.fold then a * b else b) • P.imgQ u q := by
  unfold PMap.imgQ
  rw [qmul_smul_right, qmul_smul_left]
  split_ifs
  · rw [mulVec_smul, pureQ_smul, qmul_smul_left, qmul_smul_right, smul_smul]
  · rfl

/-- The real chart quaternion of the image of the representatives `u`, `q` of a pose of a box
pre-rotated by `pre`, in the box's rotation chart. -/
noncomputable def locY (P : PMap κ) (pre : Option (Q4 κ)) (u : Fin 3 → ℝ) (q : Fin 4 → ℝ) :
    Fin 4 → ℝ :=
  preQuat (P.imgQ u (preQuat q (Exact.rePre pre))) (Exact.rePre (pre.map Exact.conjQ))

theorem locVQ_re (P : PMap κ) (pre : Option (Q4 κ)) (U : V3 ℝ) (Q : Q4 ℝ) :
    (locVQ P pre Exact.re U Q).1.get = P.M.toMatrix *ᵥ U.toFun ∧
      (locVQ P pre Exact.re U Q).2.toFun = locY P pre U.toFun Q.toFun := by
  constructor
  · funext j
    rw [V3.get_eq_toFun, locVQ, M3.toFun_mulVecG]
  · rw [locVQ, toFun_preQ, PMap.toFun_quatG, toFun_preQ]
    rfl

theorem locCoord_run (P : PMap κ) (pre : Option (Q4 κ)) (a : Fin 3) (k : Fin 4) (i : ℕ)
    (σ c₁ c₂ : ℤ) (U : V3 ℝ) (Q : Q4 ℝ) :
    (locCoord P pre a k i σ c₁ c₂).run Exact.re U Q =
      σ * (c₁ * (coordND a k (P.M.toMatrix *ᵥ U.toFun) (locY P pre U.toFun Q.toFun) i).1 -
        c₂ * (coordND a k (P.M.toMatrix *ᵥ U.toFun) (locY P pre U.toFun Q.toFun) i).2) := by
  obtain ⟨hv, hq⟩ := locVQ_re P pre U Q
  change Exact.re (Exact.ofInt σ) * (Exact.re (Exact.ofInt c₁) * (coordND a k _ _ i).1 -
    Exact.re (Exact.ofInt c₂) * (coordND a k _ _ i).2) = _
  rw [hv, hq, Exact.re_ofInt, Exact.re_ofInt, Exact.re_ofInt]

theorem locFixed_run (P : PMap κ) (pre : Option (Q4 κ)) (a : Fin 3) (k : Fin 4) (i : ℕ) (σ : ℤ)
    (U : V3 ℝ) (Q : Q4 ℝ) :
    (locFixed P pre a k i σ).run Exact.re U Q =
      σ * ((coordND a k (P.M.toMatrix *ᵥ U.toFun) (locY P pre U.toFun Q.toFun) i).1 *
          (coordND a k U.toFun Q.toFun i).2 -
        (coordND a k (P.M.toMatrix *ᵥ U.toFun) (locY P pre U.toFun Q.toFun) i).2 *
          (coordND a k U.toFun Q.toFun i).1) := by
  obtain ⟨hv, hq⟩ := locVQ_re P pre U Q
  have hU : U.get = U.toFun := funext fun j ↦ V3.get_eq_toFun U j
  change Exact.re (Exact.ofInt σ) * ((coordND a k _ _ i).1 * (coordND a k U.get Q.toFun i).2 -
    (coordND a k _ _ i).2 * (coordND a k U.get Q.toFun i).1) = _
  rw [hv, hq, hU, Exact.re_ofInt]

theorem locDev_re (k : Fin 4) (L : ℕ) (p0 : Fin 3 → κ) (z : Fin 4 → ℝ) :
    locDev Exact.re k L p0 z =
      ∑ r : Fin 3, (L * z (k.succAbove r) - Exact.re (p0 r) * z k) ^ 2 := by
  simp only [locDev, Exact.re_ofInt, Int.cast_natCast, Fin.sum_univ_three, sq]

theorem locImprove_run (P : PMap κ) (pre : Option (Q4 κ)) (k : Fin 4) (L : ℕ) (p0 : Fin 3 → κ)
    (U : V3 ℝ) (Q : Q4 ℝ) :
    (locImprove P pre k L p0).run Exact.re U Q =
      locY P pre U.toFun Q.toFun k * locY P pre U.toFun Q.toFun k *
          locDev Exact.re k L p0 Q.toFun -
        Q.toFun k * Q.toFun k * locDev Exact.re k L p0 (locY P pre U.toFun Q.toFun) := by
  obtain ⟨-, hq⟩ := locVQ_re P pre U Q
  change (locVQ P pre Exact.re U Q).2.toFun k * (locVQ P pre Exact.re U Q).2.toFun k *
      locDev Exact.re k L p0 Q.toFun -
    Q.toFun k * Q.toFun k * locDev Exact.re k L p0 (locVQ P pre Exact.re U Q).2.toFun = _
  rw [hq]

end Real

/-! ### Local exclusion at a pose -/

/-- **Local exclusion** at the chart pose `p` of the box `B` pre-rotated by `pre`, for the local
score about `c`: the pose map of symmetries `i`, `j` of `D` sends `p` to a pose `p'` of `B` (view
and rotation as in `Image.rotation_eq`) whose rotation chart coordinates are strictly closer to
`c`. -/
def LocalExcl {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] (D : SymmData κ) (B : ChartBox)
    (pre : Option (Q4 κ)) (c : Fin 3 → ℝ) (p : ChartPose) : Prop :=
  ∃ i j P, D.pmap i j = some P ∧ ∃ p' ∈ B.poses, ∃ a : ℝ, a ≠ 0 ∧
    viewDir p'.view p'.s p'.t = a • (P.M.toMatrix *ᵥ viewDir p.view p.s p.t) ∧
    p'.rotation * preRot (Exact.rePre pre) = quatRotation (P.imgQ (viewDir p.view p.s p.t)
      (preQuat (chartQuat p.rot p.x) (Exact.rePre pre))) ∧
    ∑ r, (p'.x r - c r) ^ 2 < ∑ r, (p.x r - c r) ^ 2

/-! ### Leaves -/

/-- A local exclusion leaf: the symmetries `i`, `j` of the symmetry data whose pose map excludes
it, the signs of the image's view and rotation chart denominators (`true`: positive), the chart
coordinates the map fixes, the exponent `e` of the power of slot `0` that divides the improvement
numerator, and the bisection depth of the sign checks. -/
structure LocLeaf where
  /-- The first symmetry (acting on the view and from the left). -/
  i : ℕ
  /-- The second symmetry (acting on the inner copy). -/
  j : ℕ
  /-- The sign of the image's view denominator. -/
  pos₀ : Bool
  /-- The sign of the image's rotation denominator. -/
  pos₁ : Bool
  /-- The fixed chart coordinates. -/
  fixed : List ℕ
  /-- The exponent of slot `0` in the improvement. -/
  e : ℕ
  /-- The bisection depth of the sign checks. -/
  depth : ℕ

namespace LocLeaf

/-- The sign `±1` of a denominator. -/
def sgn (b : Bool) : ℤ :=
  if b then 1 else -1

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The sign check of the pose polynomial `G` at the outputs of `Ψ` on the box `b` of `n` slots,
divided by the monomial `e`: positive (`strict`) or nonnegative, by either sign check
(`Pull.checkAny`: the kernel tests the Kronecker one first, compiled code the sparse one). -/
def signOn (n : ℕ) (Ψ : GenMap κ) (b : Box) (depth : ℕ) (strict : Bool) (e : List ℕ)
    (G : PosePoly κ) : Bool :=
  Pull.checkAny n [⟨G.comp Ψ, e⟩] strict depth b [[(0, 1)]]

/-- Coordinate `i` of the image lies in the bounds of `B`, with the sign `σ` of its denominator,
or (`fixed`) equals that of the representative's pose. -/
def coordOk (P : PMap κ) (pre : Option (Q4 κ)) (B : ChartBox) (n : ℕ) (Ψ : GenMap κ) (b : Box)
    (depth : ℕ) (σ : ℤ) (fixed : Bool) (i : ℕ) : Bool :=
  if fixed then
    signOn n Ψ b depth false [] (locFixed P pre B.view B.rot i 1) &&
      signOn n Ψ b depth false [] (locFixed P pre B.view B.rot i (-1))
  else
    signOn n Ψ b depth false [] (locCoord P pre B.view B.rot i σ B.box.den (B.box.lo.getD i 0)) &&
      signOn n Ψ b depth false []
        (locCoord P pre B.view B.rot i σ (-(B.box.den : ℤ)) (-B.box.hi.getD i 0))

/-- **The check of a local exclusion leaf** on the family with map `Ψ` and box `b` of `n` slots,
for the claim box `B` pre-rotated by `pre`, the symmetry data `D` and the local score about
`p0 / L`. -/
def check (D : SymmData κ) (B : ChartBox) (pre : Option (Q4 κ)) (L : ℕ) (p0 : Fin 3 → κ)
    (n : ℕ) (Ψ : GenMap κ) (b : Box) (x : LocLeaf) : Bool :=
  match D.pmap x.i x.j with
  | some P =>
    decide (0 < n) && decide (0 < B.box.den) && decide (0 < L) && Exact.preOk pre &&
      signOn n Ψ b x.depth true [] (locCoord P pre B.view B.rot 0 (sgn x.pos₀) 0 (-1)) &&
      signOn n Ψ b x.depth true [] (locCoord P pre B.view B.rot 2 (sgn x.pos₁) 0 (-1)) &&
      coordOk P pre B n Ψ b x.depth (sgn x.pos₀) (x.fixed.contains 0) 0 &&
      coordOk P pre B n Ψ b x.depth (sgn x.pos₀) (x.fixed.contains 1) 1 &&
      coordOk P pre B n Ψ b x.depth (sgn x.pos₁) (x.fixed.contains 2) 2 &&
      coordOk P pre B n Ψ b x.depth (sgn x.pos₁) (x.fixed.contains 3) 3 &&
      coordOk P pre B n Ψ b x.depth (sgn x.pos₁) (x.fixed.contains 4) 4 &&
      signOn n Ψ b x.depth true [x.e] (locImprove P pre B.rot L p0)
  | none => false

/-! #### Soundness -/

section Sound

variable {n : ℕ} {Ψ : GenMap κ} {b : Box} {depth : ℕ}

/-- A sign check gives the sign of the polynomial at the outputs, where the monomial is
positive. -/
theorem signOn_sound {strict : Bool} {e : List ℕ} {G : PosePoly κ}
    (h : signOn n Ψ b depth strict e G = true) {z : Fin n → ℝ} (hz : b.Mem n z)
    (he : 0 < DPoly.monoVal n e z) :
    Sign strict (G.run Exact.re (viewOf (Ψ.run Exact.re (Pull.ext n z)))
      (quatOf (Ψ.run Exact.re (Pull.ext n z)))) := by
  obtain ⟨c, hc0, s, hG, hsign⟩ := single_of_check (Pull.checkAny_sound h) hz
  simp only [PosePoly.comp_run] at hG
  change Sign strict (G.eval (Ψ.run Exact.re (Pull.ext n z)))
  rw [hG]
  cases strict
  · exact mul_nonneg (mul_pos hc0 he).le hsign
  · exact mul_pos (mul_pos hc0 he) hsign

theorem monoVal_nil_pos (z : Fin n → ℝ) : 0 < DPoly.monoVal n [] z :=
  monoVal_pos n [] z fun _ ↦ Or.inl (by simp)

/-- Bounds of a ratio from the signs of `σ (D num - lo den)` and `σ (hi den - D num)`. -/
theorem div_bounds {σ N Dn D lo hi : ℝ} (hσ : 0 < σ * Dn) (hD : 0 < D)
    (h₁ : 0 ≤ σ * (D * N - lo * Dn)) (h₂ : 0 ≤ σ * (-D * N - -hi * Dn)) :
    lo / D ≤ N / Dn ∧ N / Dn ≤ hi / D := by
  have hσ0 : σ ≠ 0 := fun h0 ↦ by simp [h0] at hσ
  have hq : N / Dn = (σ * N) / (σ * Dn) := by rw [mul_div_mul_left _ _ hσ0]
  rw [hq]
  constructor
  · rw [div_le_div_iff₀ hD hσ]
    nlinarith
  · rw [div_le_div_iff₀ hσ hD]
    nlinarith

/-- The chart coordinates of a representative of a pose. -/
theorem coordND_rep {p : ChartPose} {u : Fin 3 → ℝ} {q : Fin 4 → ℝ} {α β : ℝ} (hα : α ≠ 0)
    (hβ : β ≠ 0) (hu : u = α • viewDir p.view p.s p.t) (hq : q = β • chartQuat p.rot p.x)
    (i : Fin 5) :
    (coordND p.view p.rot u q i).2 ≠ 0 ∧
      (coordND p.view p.rot u q i).1 / (coordND p.view p.rot u q i).2 = p.coords i := by
  subst hu hq
  fin_cases i <;>
    simp [coordND, viewDir, chartQuat_self, chartQuat_succAbove_apply, ChartPose.coords, hα, hβ]

/-- The image pose: the chart coordinates of the image view `V` and quaternion `Y` in the charts
of `B`. -/
noncomputable def imgPose (B : ChartBox) (V : Fin 3 → ℝ) (Y : Fin 4 → ℝ) : ChartPose :=
  ⟨B.view, V (B.view + 1) / V B.view, V (B.view + 2) / V B.view, B.rot,
    fun r ↦ Y (B.rot.succAbove r) / Y B.rot⟩

theorem imgPose_coords (B : ChartBox) (V : Fin 3 → ℝ) (Y : Fin 4 → ℝ) (i : Fin 5) :
    (imgPose B V Y).coords i =
      (coordND B.view B.rot V Y i).1 / (coordND B.view B.rot V Y i).2 := by
  fin_cases i <;> rfl

/-- The improvement numerator in the coordinates: `Y_k² β² L² (|x - c|² - |y - c|²)`. -/
theorem improve_eq {L β yk : ℝ} (hL : L ≠ 0) (hyk : yk ≠ 0) (y₀ y₁ y₂ x₀ x₁ x₂ c₀ c₁ c₂ : ℝ) :
    yk * yk * ((L * (β * x₀) - c₀ * β) ^ 2 + (L * (β * x₁) - c₁ * β) ^ 2 +
        (L * (β * x₂) - c₂ * β) ^ 2) -
      β * β * ((L * y₀ - c₀ * yk) ^ 2 + (L * y₁ - c₁ * yk) ^ 2 + (L * y₂ - c₂ * yk) ^ 2) =
    (yk * β * L) ^ 2 * (((x₀ - c₀ / L) ^ 2 + (x₁ - c₁ / L) ^ 2 + (x₂ - c₂ / L) ^ 2) -
      ((y₀ / yk - c₀ / L) ^ 2 + (y₁ / yk - c₁ / L) ^ 2 + (y₂ / yk - c₂ / L) ^ 2)) := by
  field_simp

/-- **Soundness of local exclusion leaves**: where slot `0` is positive, the poses of `B` that the
outputs represent are locally excluded about `p0 / L`. -/
theorem check_sound {D : SymmData κ} {B : ChartBox} {pre : Option (Q4 κ)} {L : ℕ}
    {p0 : Fin 3 → κ} {x : LocLeaf} (h : x.check D B pre L p0 n Ψ b = true) {z : Fin n → ℝ}
    (hz : b.Mem n z) (hz0 : 0 < Pull.ext n z 0) {p : ChartPose} (hp : p ∈ B.poses)
    (hrep : Represents p (Ψ.run Exact.re (Pull.ext n z))) :
    LocalExcl D B pre (fun r ↦ Exact.re (p0 r) / L) p := by
  unfold check at h
  split at h
  next P hP =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hden⟩, hL⟩, hpre⟩, hd0⟩, hd2⟩, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩, himp⟩ := h
    set o := Ψ.run Exact.re (Pull.ext n z) with ho
    have key : ∀ {strict : Bool} {e : List ℕ} {G : PosePoly κ},
        signOn n Ψ b x.depth strict e G = true → 0 < DPoly.monoVal n e z →
        Sign strict (G.run Exact.re (viewOf o) (quatOf o)) := fun h he ↦ signOn_sound h hz he
    obtain ⟨α, β, hα, hβ, hu, hq⟩ := hrep
    obtain ⟨hpv, hpr, hpy⟩ := hp
    have hUo : (viewOf o).toFun = outU o := toFun_viewOf o
    have hQo : (quatOf o).toFun = outQ o := toFun_quatOf o
    set V := P.M.toMatrix *ᵥ outU o with hV
    set Y := locY P pre (outU o) (outQ o) with hY
    -- The signs of the denominators.
    have s0 := key hd0 (monoVal_nil_pos z)
    have s2 := key hd2 (monoVal_nil_pos z)
    simp only [Sign, ↓reduceIte, locCoord_run, hUo, hQo, ← hV, ← hY, coordND] at s0 s2
    push_cast at s0 s2
    simp only [zero_mul, zero_sub, neg_mul, one_mul, neg_neg] at s0 s2
    have hVa : V B.view ≠ 0 := fun h0 ↦ by simp [h0] at s0
    have hYk : Y B.rot ≠ 0 := fun h0 ↦ by simp [h0] at s2
    have hd : (0 : ℝ) < B.box.den := by exact_mod_cast hden
    -- Each coordinate of the image lies in the bounds of `B`.
    have hcoord : ∀ (i : Fin 5) (σ : ℤ),
        0 < σ * (coordND B.view B.rot V Y i).2 →
        coordOk P pre B n Ψ b x.depth σ (x.fixed.contains i) i = true →
        (B.box.lo.getD i 0 : ℝ) / B.box.den ≤
            (coordND B.view B.rot V Y i).1 / (coordND B.view B.rot V Y i).2 ∧
          (coordND B.view B.rot V Y i).1 / (coordND B.view B.rot V Y i).2 ≤
            (B.box.hi.getD i 0 : ℝ) / B.box.den := by
      intro i σ hσ hc
      unfold coordOk at hc
      split_ifs at hc with hfix
      · simp only [Bool.and_eq_true] at hc
        have f1 := key hc.1 (monoVal_nil_pos z)
        have f2 := key hc.2 (monoVal_nil_pos z)
        simp only [Sign, Bool.false_eq_true, ↓reduceIte, locFixed_run, hUo, hQo, ← hV,
          ← hY] at f1 f2
        push_cast at f1 f2
        have hDn : (coordND B.view B.rot V Y i).2 ≠ 0 := fun h0 ↦ by simp [h0] at hσ
        rw [← hpv, ← hpr] at f1 f2 hDn ⊢
        obtain ⟨hDp, hrat⟩ := coordND_rep hα hβ hu hq i
        have hratio : (coordND p.view p.rot V Y i).1 / (coordND p.view p.rot V Y i).2 =
            p.coords i := by
          rw [← hrat, div_eq_div_iff hDn hDp]
          linarith
        rw [hratio]
        exact hpy i
      · simp only [Bool.and_eq_true] at hc
        have c1 := key hc.1 (monoVal_nil_pos z)
        have c2 := key hc.2 (monoVal_nil_pos z)
        simp only [Sign, Bool.false_eq_true, ↓reduceIte, locCoord_run, hUo, hQo, ← hV,
          ← hY] at c1 c2
        push_cast at c1 c2
        exact div_bounds hσ hd c1 c2
    have c0 := hcoord 0 _ (by simpa [coordND] using s0) h0
    have c1 := hcoord 1 _ (by simpa [coordND] using s0) h1
    have c2 := hcoord 2 _ (by simpa [coordND] using s2) h2
    have c3 := hcoord 3 _ (by simpa [coordND] using s2) h3
    have c4 := hcoord 4 _ (by simpa [coordND] using s2) h4
    -- The image pose.
    have hp'B : imgPose B V Y ∈ B.poses := by
      refine ⟨rfl, rfl, fun i ↦ ?_⟩
      rw [imgPose_coords]
      fin_cases i
      exacts [c0, c1, c2, c3, c4]
    refine ⟨x.i, x.j, P, hP, imgPose B V Y, hp'B, (V B.view)⁻¹ * α,
      mul_ne_zero (inv_ne_zero hVa) hα, ?_, ?_, ?_⟩
    · -- The view.
      change viewDir B.view (V (B.view + 1) / V B.view) (V (B.view + 2) / V B.view) = _
      rw [viewDir_div hVa, hV, hu, mulVec_smul, smul_smul]
    · -- The rotation.
      have hQ₂ : P.imgQ (outU o) (preQuat (outQ o) (Exact.rePre pre)) =
          (if P.fold then α * β else β) •
            P.imgQ (viewDir p.view p.s p.t) (preQuat (chartQuat p.rot p.x) (Exact.rePre pre)) := by
        rw [hu, hq, preQuat_smul, PMap.imgQ_smul₂]
      have hc0 : (if P.fold then α * β else β) ≠ 0 := by
        split_ifs
        · exact mul_ne_zero hα hβ
        · exact hβ
      change quatRotation (chartQuat B.rot fun r ↦ Y (B.rot.succAbove r) / Y B.rot) *
        preRot (Exact.rePre pre) = _
      rw [chartQuat_succAbove hYk, quatRotation_smul (inv_ne_zero hYk), hY, locY, hQ₂]
      cases pre with
      | none =>
        rw [Option.map_none, Exact.rePre_none, preQuat, preRot_none, Matrix.mul_one,
          quatRotation_smul hc0]
      | some c =>
        have hc : Exact.reQ c ≠ 0 := Exact.rePre_ne_zero hpre _ rfl
        change quatRotation (qmul (_ • _) (Exact.reQ (Exact.conjQ c))) *
          quatRotation (Exact.reQ c) = _
        rw [← quatRotation_qmul, Exact.reQ_conjQ, qmul_qconj_mul,
          quatRotation_smul (dotProduct_self_eq_zero.not.mpr hc), quatRotation_smul hc0]
    · -- The improvement.
      have hi := key himp (monoVal_single_pos x.e hz0)
      simp only [Sign, ↓reduceIte, locImprove_run, hUo, hQo, ← hY] at hi
      rw [locDev_re, locDev_re] at hi
      rw [← hpr] at hi hYk
      have hqk : outQ o p.rot = β := by
        rw [hq, Pi.smul_apply, chartQuat_self, smul_eq_mul, mul_one]
      have hqr (r : Fin 3) : outQ o (p.rot.succAbove r) = β * p.x r := by
        rw [hq, Pi.smul_apply, chartQuat_succAbove_apply, smul_eq_mul]
      simp only [hqk, hqr, Fin.sum_univ_three] at hi
      have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
      rw [improve_eq hL' hYk] at hi
      have hpos : 0 < (Y p.rot * β * L) ^ 2 := by positivity
      have hlt := pos_of_mul_pos_right hi hpos.le
      change ∑ r, (Y (B.rot.succAbove r) / Y B.rot - Exact.re (p0 r) / L) ^ 2 <
        ∑ r, (p.x r - Exact.re (p0 r) / L) ^ 2
      rw [← hpr, Fin.sum_univ_three, Fin.sum_univ_three]
      linarith
  next => simp at h

end Sound

end LocLeaf

/-! ### Local exclusion on a box -/

section Score

/-- The chart pose of `B` read off a pose `(u, R)` with the rotation `R Rcᵀ` (the pre-rotation
undone): view coordinates `u (a + 1) / u a`, `u (a + 2) / u a` and rotation coordinates from row
`k` of `rotQuat`. -/
noncomputable def poseOf (B : ChartBox) (Rc : Matrix (Fin 3) (Fin 3) ℝ) (u : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ) : ChartPose :=
  ⟨B.view, u (B.view + 1) / u B.view, u (B.view + 2) / u B.view, B.rot,
    fun r ↦ rotQuat (R * Rcᵀ) B.rot (B.rot.succAbove r) / rotQuat (R * Rcᵀ) B.rot B.rot⟩

open Classical in
/-- The local score of a pose `(u, R)` for the box `B` with the pre-rotation `Rc` and the centre
`c`: `exp (-|x - c|²)` for the rotation coordinates `x` of the pose of `B` that represents it
(`poseOf`), `0` if none does. -/
noncomputable def locScore (B : ChartBox) (Rc : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)
    (u : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  if poseOf B Rc u R ∈ B.poses ∧
      (∃ a : ℝ, a ≠ 0 ∧ u = a • viewDir B.view (poseOf B Rc u R).s (poseOf B Rc u R).t) ∧
      R = (poseOf B Rc u R).rotation * Rc then
    Real.exp (-∑ r, ((poseOf B Rc u R).x r - c r) ^ 2)
  else 0

theorem poseOf_eq {B : ChartBox} {Rc : Matrix (Fin 3) (Fin 3) ℝ} (hRc : Rc * Rcᵀ = 1)
    {p : ChartPose} (hp : p ∈ B.poses) {a : ℝ} (ha : a ≠ 0) :
    poseOf B Rc (a • viewDir p.view p.s p.t) (p.rotation * Rc) = p := by
  obtain ⟨view, s, t, rot, x⟩ := p
  obtain ⟨hv, hr, -⟩ := hp
  dsimp only at hv hr
  subst hv hr
  have hq := chartQuat_ne_zero (R := ℝ) B.rot x
  have hd : chartQuat B.rot x ⬝ᵥ chartQuat B.rot x ≠ 0 := dotProduct_self_eq_zero.not.mpr hq
  have hR : chartRotation B.rot x * Rc * Rcᵀ = quatRotation (chartQuat B.rot x) := by
    rw [Matrix.mul_assoc, hRc, Matrix.mul_one]
    rfl
  unfold poseOf
  simp only [ChartPose.rotation]
  rw [hR, rotQuat_quatRotation hq]
  simp only [ChartPose.mk.injEq, true_and]
  refine ⟨?_, ?_, ?_⟩
  · simp [viewDir, ha]
  · simp [viewDir, ha]
  · funext r
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, chartQuat_succAbove_apply,
      chartQuat_self]
    simp only [mul_one]
    exact mul_div_cancel_left₀ _ (div_ne_zero (by norm_num) hd)

theorem locScore_eq {B : ChartBox} {Rc : Matrix (Fin 3) (Fin 3) ℝ} (hRc : Rc * Rcᵀ = 1)
    (c : Fin 3 → ℝ) {p : ChartPose} (hp : p ∈ B.poses) {a : ℝ} (ha : a ≠ 0) :
    locScore B Rc c (a • viewDir p.view p.s p.t) (p.rotation * Rc) =
      Real.exp (-∑ r, (p.x r - c r) ^ 2) := by
  have he := poseOf_eq hRc hp ha
  unfold locScore
  split_ifs with hc
  · rw [he]
  · refine (hc ?_).elim
    rw [he]
    exact ⟨hp, ⟨a, ha, by rw [hp.1]⟩, rfl⟩

theorem exists_of_locScore_pos {B : ChartBox} {Rc : Matrix (Fin 3) (Fin 3) ℝ} {c : Fin 3 → ℝ}
    {u : Fin 3 → ℝ} {R : Matrix (Fin 3) (Fin 3) ℝ} (h : 0 < locScore B Rc c u R) :
    ∃ p ∈ B.poses, ∃ a : ℝ, a ≠ 0 ∧ u = a • viewDir p.view p.s p.t ∧ R = p.rotation * Rc := by
  unfold locScore at h
  split_ifs at h with hc
  · obtain ⟨hp, ⟨a, ha, hu⟩, hR⟩ := hc
    exact ⟨_, hp, a, ha, hu, hR⟩
  · exact absurd h (lt_irrefl 0)

theorem preRot_mem {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] {pre : Option (Q4 κ)}
    (h : Exact.preOk pre = true) : preRot (Exact.rePre pre) ∈ SO(3) := by
  cases pre with
  | none => exact one_mem _
  | some c => exact quatRotation_mem (Exact.rePre_ne_zero h _ rfl)

/-- **Local exclusion.** If every pose of the box `B` (pre-rotated by `pre`) has no fit or is
locally excluded about `c`, with checked symmetry data and points that span space, no pose of `B`
fits. -/
theorem noFitRot_of_local {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] {pts : List (V3 κ)}
    {D : SymmData κ} (hD : D.ok pts = true)
    (hspan : Submodule.span ℝ
      ((· - D.centre) '' ((Polyhedron.ofPoints pts).vertices : Set (Fin 3 → ℝ))) = ⊤)
    {B : ChartBox} {pre : Option (Q4 κ)} (hpre : Exact.preOk pre = true) {c : Fin 3 → ℝ}
    (h : ∀ p ∈ B.poses, ¬ (Polyhedron.ofPoints pts).FitsAlong (viewDir p.view p.s p.t)
      (p.rotation * preRot (Exact.rePre pre)) ∨ LocalExcl D B pre c p) :
    (Polyhedron.ofPoints pts).NoFitRot B.poses (preRot (Exact.rePre pre)) := by
  set Rc := preRot (Exact.rePre pre) with hRcdef
  have hRcSO : Rc ∈ SO(3) := preRot_mem hpre
  have hRc : Rc * Rcᵀ = 1 := (mem_SO3_rels hRcSO).1
  intro p hp hfit
  obtain ⟨u, R, -, -, hfit', hmax, hge⟩ := hfit.exists_max_ge hspan (locScore B Rc c)
    (viewDir_ne_zero _ _ _) (mul_mem p.rotation_mem hRcSO)
  have h0 : 0 < locScore B Rc c u R := by
    have := locScore_eq hRc c hp one_ne_zero
    rw [one_smul] at this
    rw [this] at hge
    exact (Real.exp_pos _).trans_le hge
  obtain ⟨q, hq, a, ha, hu, hR⟩ := exists_of_locScore_pos h0
  have hscore : locScore B Rc c u R = Real.exp (-∑ r, (q.x r - c r) ^ 2) := by
    rw [hu, hR]
    exact locScore_eq hRc c hq ha
  have hfitq : (Polyhedron.ofPoints pts).FitsAlong (viewDir q.view q.s q.t)
      (q.rotation * Rc) := by
    rw [hu, hR] at hfit'
    exact hfit'.of_smul ha
  rcases h q hq with hno | ⟨i, j, P, hP, q', hq', a', ha', hv', hr', hlt⟩
  · exact hno hfitq
  · obtain ⟨A, σ, B', τ, hacts, hA, hB'⟩ := SymmData.exists_acts_of_pmap hD hP
    obtain ⟨μ, hμ, hM⟩ := hacts.mul
    have hrot := hacts.quatRotation_imgQ hA.1 hA.2.1 hB'.2.1 (viewDir_ne_zero q.view q.s q.t)
      (preQuat (chartQuat q.rot q.x) (Exact.rePre pre))
    rw [quatRotation_preQuat] at hrot
    have hview : A *ᵥ u = (a * (a' * μ)⁻¹) • viewDir q'.view q'.s q'.t := by
      rw [hu, mulVec_smul, hv', hM, smul_mulVec, smul_smul, smul_smul]
      congr 1
      field_simp
    have hrotq : turn (σ * τ) (A *ᵥ u) * A * R * B' = q'.rotation * Rc := by
      rw [hr', hrot, hu, mulVec_smul, turn_smul ha, hR]
      rfl
    have himg : locScore B Rc c (A *ᵥ u) (turn (σ * τ) (A *ᵥ u) * A * R * B') =
        Real.exp (-∑ r, (q'.x r - c r) ^ 2) := by
      rw [hrotq, hview]
      exact locScore_eq hRc c hq' (mul_ne_zero ha (inv_ne_zero (mul_ne_zero ha' hμ)))
    have hle := hmax A σ B' τ hA hB'
    rw [himg, hscore, Real.exp_le_exp] at hle
    linarith

end Score

end Nieuwland.Check
