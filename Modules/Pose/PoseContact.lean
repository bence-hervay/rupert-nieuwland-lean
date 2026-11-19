import Modules.Pose.PoseCheck
import Modules.Root.Assembly
import Modules.Root.OneRoot

/-!
# Pose roots of contact systems

The representatives' system `S₀` of a root-form solid is the completed written-out system of a
root record `R` of its certificate (`Root.RootRec.explicitB`, `Modules/Root/HasUniqueRoot.lean`): its
variables are the scale `ℓ`, the chart pose `(s, t, r₁, r₂, r₃)`, in general mode the
translation `(u₁, u₂)`, the multipliers, the field's generator and the coordinates of the vertices
in contact. The pose root extends `S₀` by the witness of `Modules/Pose/PoseCheck.lean`
(`ctSystem`: `poseExt` with `s = x 1`, `t = x 2`, the chart quaternion of `x 3, x 4, x 5` and the
translation `c (x 6, x 7)`, or `0` in centred mode), and the weak fit at the root is the record's
weak fit (`Root.Sys.weakOk`, `Modules/Root/WeakFit.lean`) checked again, on the balls of the box
of the record's test:

* `Kraw.boxBalls`: the box's coordinates and the parameters as balls (no slopes, no Krawczyk
  test: a solution in the box is enough); `Kraw.encl_boxBalls`.
* `Sys.zero_of_solves_explicitZ`, `RootRec.zero_of_solves_explicitB`: a solution of the written-out
  system is a zero of the root's system in the box of its test (the part of
  `Sys.solves_explicit` that does not use the uniqueness of the zero).
* `Sys.slack_zero_of_idOk'`, `Sys.slack_zero_of_mem_zeroCons'`: the identities' contacts vanish
  at a zero enclosed by any balls (`Sys.slack_zero_of_idOk` for the balls of a test).
* `Sys.screenWeak_of_weakOk`: a passing weak-fit check is a weak fit at the zero's own scale
  (`ScreenWeak`; `Sys.fitsThrough_of_weakOk` gives the strict fits below it).
* `ct_isPoseRoot`: with `IsRootEq [S₀] N` and `S₀ = R.explicitB pts F vb`, the pose root
  `ctSystem` has exactly one root, of scale `N`, and its pose is a weak fit of the polyhedron
  `P = (ofPoints pts).smul c` scaled by `N` (`IsPoseRoot`).

Nothing of the certificate is used but the root record's data: the record's checks
(`Root.certOk`, Krawczyk's test, the touch leaf) are not needed, since the representatives'
theorem gives the one root.
-/

open Matrix Nieuwland.Check Nieuwland.PoseCheck Finset

namespace Nieuwland

namespace Root

/-! ### Balls of the box -/

namespace Kraw

/-- The balls of the box of the test's coordinates, then the parameters' balls. -/
def boxBalls (K : Kraw) : List Ball := (List.range K.n).map (K.coord K.rad) ++ K.par

theorem zball_boxBalls (K : Kraw) (i : ℕ) : zball K.boxBalls i = K.coord K.rad i := by
  unfold zball boxBalls coord
  by_cases hi : i < K.n
  · rw [List.getD_append _ _ _ _ (by simpa using hi), if_pos hi]
    simp [List.getD_eq_getElem?_getD, hi]
  · rw [List.getD_append_right _ _ _ _ (by simpa using hi), if_neg hi]
    simp

/-- **The box's balls enclose every point of the box** (and the parameters). -/
theorem encl_boxBalls (K : Kraw) {p : ℕ → ℝ} (hp : K.ParOk p) {y : Fin K.n → ℝ}
    (hy : y ∈ K.box) (i : ℕ) : (zball K.boxBalls i).Encl (K.env p y i) := by
  rw [zball_boxBalls]
  exact K.encl_coord hp (fun j ↦ hy j) i

end Kraw

/-! ### The identities at a zero, on any enclosing balls -/

namespace Sys

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] {S : Sys} {K : Kraw}

/-- `Sys.slack_zero_of_idOk` on any balls `Z` that enclose the zero. -/
theorem slack_zero_of_idOk' (hK : K.eqs = S.eqs) {y : Fin K.n → ℝ}
    (h0 : K.F (basisPar κ) y = 0) {Z : List Ball}
    (hY : ∀ i, (Kraw.zball Z i).Encl (K.env (basisPar κ) y i)) {r : IdRec}
    (h : idOk κ S Z r = true) : (S.slack r.con).eval (K.env (basisPar κ) y) = 0 := by
  simp only [idOk, Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨hsign, hemp⟩ := h
  have hz : ∀ j, K.env (basisPar κ) y (S.n + j) = basisPar κ j := fun j ↦ by
    rw [← Sys.n_eq hK, Kraw.env_par]
  have e := eval_eq_zero_of_toSP S.n _ hz hemp
  simp only [idE, Expr.eval, eval_sumE] at e
  rw [sum_eq_zero (fun i hi ↦ by rw [S.g_zero hK h0 (mem_range.mp hi), mul_zero]), sub_zero] at e
  have hD : r.D.eval (K.env (basisPar κ) y) ≠ 0 := by
    rcases hsign with h | h
    · exact (Ball.pos_sound (encl_bval hY r.D) h).ne'
    · exact (Ball.neg_sound (encl_bval hY r.D) h).ne
  exact (mul_eq_zero.mp e).resolve_left hD

/-- `Sys.slack_zero_of_mem_zeroCons` on any balls `Z` that enclose the zero. -/
theorem slack_zero_of_mem_zeroCons' (hK : K.eqs = S.eqs) {y : Fin K.n → ℝ}
    (h0 : K.F (basisPar κ) y = 0) {Z : List Ball}
    (hY : ∀ i, (Kraw.zball Z i).Encl (K.env (basisPar κ) y i)) {W : WeakRec} {c : ℕ × ℕ × ℕ}
    (hc : c ∈ zeroCons κ S Z W) : (S.slack c).eval (K.env (basisPar κ) y) = 0 := by
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
  exact slack_zero_of_idOk' hK h0 hY (List.mem_filter.mp hr).2

/-! ### The weak fit at a zero -/

/-- **A passing weak-fit check is a weak fit at the zero's scale**, in screen coordinates: every
point of `P` scaled by `l`, rotated and moved by the zero's translation, has the screen image of
a point of `P` (the plug lies in the polygon of the cycle, whose corners are vertices). The balls
`Z` enclose the point `z`, and the slacks of the system's contacts and of `zs` vanish there. -/
theorem screenWeak_of_weakOk {z : ℕ → ℝ} {Z : List Ball} (hY : ∀ i, (Kraw.zball Z i).Encl (z i))
    {P : Polyhedron} {nV : ℕ} (hV : ∀ x, x ∈ P.vertices ↔ ∃ v < nV, vertOf z S.V v = x)
    {W : WeakRec} {zs : List (ℕ × ℕ × ℕ)} (hzero : ∀ c ∈ S.contacts, (S.slack c).eval z = 0)
    (hzs : ∀ c ∈ zs, (S.slack c).eval z = 0) (hW : S.weakOk nV Z W zs = true) :
    ScreenWeak P S.view (z 0) (z 1) (chartRotation S.rot ![z 2, z 3, z 4]) (yOf z S.cen)
      ((lE S.cen).eval z) := by
  simp only [weakOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    Bool.or_eq_true] at hW
  obtain ⟨⟨hH, hm⟩, hall⟩ := hW
  set p := poseOf z S.view S.rot with hp
  set l := (lE S.cen).eval z
  have hd := quat_pos S.rot ![z 2, z 3, z 4]
  have hn : W.cycle.length - 1 + 1 = W.cycle.length := by omega
  let w : Fin (W.cycle.length - 1 + 1) → Fin 2 → ℝ :=
    fun i ↦ p.screen (vertOf z S.V (W.cycle.getD i 0))
  have hsucc : ∀ i : Fin (W.cycle.length - 1 + 1),
      ((i + 1 : Fin (W.cycle.length - 1 + 1)) : ℕ) = (i.val + 1) % W.cycle.length := by
    intro i
    rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
    exact congrArg _ hn
  -- the corners are vertices
  have hC : convexHull ℝ (Set.range w) ⊆ {screen S.view (z 0) (z 1) y' | y' ∈ P.hull} := by
    have e := P.image_hull (screenₗ S.view (z 0) (z 1))
    simp only [screenₗ_apply] at e
    rw [e]
    refine convexHull_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨_, (hV _).mpr ⟨_, (hall i (by omega)).1.1, rfl⟩, rfl⟩
  -- the moved vertices lie in the polygon
  have hvert : ∀ y ∈ (P.smul l).vertices,
      p.screen (p.rotation *ᵥ y) + yOf z S.cen ∈ convexHull ℝ (Set.range w) := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Polyhedron.mem_smul_vertices.mp hx
    obtain ⟨v, hv, rfl⟩ := (hV u).mp hu
    refine mem_convexHull_of_weak (h := ![(W.h₀ : ℝ) / W.H, (W.h₁ : ℝ) / W.H])
      (fun i ↦ ?_) (fun i ↦ ?_)
    · obtain ⟨-, hvs⟩ := hall i (by omega)
      have hs : (S.slack (W.a i, W.b i, v)).eval z ≤ 0 := by
        rcases hvs v hv with (hA | hZ) | hC
        · exact (hzero _ (by simpa using hA)).le
        · exact (hzs _ (by simpa using hZ)).le
        · exact (Ball.neg_sound (encl_bval hY _) hC).le
      rw [Sys.slack, eval_slackE] at hs
      simp only [w]
      rw [hsucc i, Matrix.mulVec_smul, FitData.screen_smul]
      exact (mul_nonneg_iff_of_pos_left hd).mp (neg_nonpos.mp hs)
    · obtain ⟨⟨-, hwit⟩, -⟩ := hall i (by omega)
      have h1 := Ball.pos_sound (encl_bval hY _) hwit
      rw [eval_witE z S.view S.rot _ _ _ _ _ hH] at h1
      simp only [w]
      rw [hsucc i]
      exact (mul_pos_iff_of_pos_left (by exact_mod_cast hH)).mp h1
  -- the moved hull lies in the polygon
  intro y hy
  have hconv : Convex ℝ ((fun x ↦ p.screen (p.rotation *ᵥ x) + yOf z S.cen) ⁻¹'
      convexHull ℝ (Set.range w)) := by
    have := ((convex_convexHull ℝ (Set.range w)).translate_preimage_left
      (yOf z S.cen)).linear_preimage ((screenₗ p.view p.s p.t) ∘ₗ p.rotation.mulVecLin)
    exact this
  obtain ⟨y', hy', he⟩ := hC (convexHull_min (fun x hx ↦ hvert x hx) hconv hy)
  exact ⟨y', hy', he.symm⟩

/-! ### A solution of the written-out system is a zero -/

/-- **A solution of the written-out system is a zero of the root's system** in the box of its
test, with the solution's unknowns: the first part of `Sys.solves_explicit`, which does not need
the zero to be unique. -/
theorem zero_of_solves_explicitZ (hK : K.eqs = S.eqs) {pts : List (V3 κ)}
    (hV : S.V = vertsE S.n pts) {F : ParData} (hF : F.Spec κ) {vs : List ℕ}
    (hvs : ∀ i < S.k, (S.con i).1 ∈ vs ∧ (S.con i).2.1 ∈ vs ∧ (S.con i).2.2 ∈ vs) {x : ℕ → ℝ}
    (hx : (S.explicitZ (ExactBasis.dim κ) vs K (F.par S.n) (F.eqs S.n) F.box).Solves x) :
    ∃ y : Fin K.n → ℝ, y ∈ K.box ∧ K.F (basisPar κ) y = 0 ∧
      ∀ i < S.n, x (S.pos i) = K.env (basisPar κ) y i := by
  obtain ⟨hsound, -⟩ := hF
  set dim := ExactBasis.dim κ
  set E := S.explicitZ dim vs K (F.par S.n) (F.eqs S.n) F.box with hE
  have hn : K.n = S.n := Sys.n_eq hK
  have hgen : InBox F.box S.n x ∧ ∀ p ∈ F.eqs S.n, p.eval x = 0 := by
    obtain ⟨hb, he⟩ := hx
    refine ⟨fun i hi ↦ ?_, fun p hp ↦ he p (List.mem_append_right _ hp)⟩
    have := hb (S.n + i) (by rw [Sys.box_length]; omega)
    rwa [Sys.box_getD_gen] at this
  have hpar := hsound S.n x hgen.1 hgen.2
  let zX : ℕ → ℝ := fun i ↦ (S.τ dim vs (F.par S.n) i).eval x
  have hzX_unknown : ∀ i, i < S.n → zX i = x (S.pos i) := fun i hi ↦ by
    simp only [zX, S.τ_unknown dim vs _ hi, RationalPolynomial.eval_var]
  have hzX_par : ∀ j < dim, zX (S.n + j) = basisPar κ j := fun j hj ↦ by
    simp only [zX, Sys.τ]
    rw [if_neg (by have := S.nx_lt; omega), if_neg (by have := S.nx_lt; omega),
      if_neg (by omega), if_pos (by omega)]
    rw [show S.n + j - S.n = j by omega, hpar]
  have hzX_rest : ∀ i, S.n + dim + 3 * vs.length ≤ i → zX i = 0 := fun i hi ↦ by
    simp only [zX, Sys.τ]
    rw [if_neg (by have := S.nx_lt; omega), if_neg (by have := S.nx_lt; omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp
  have hmem_g : ∀ i < S.k, RationalPolynomial.ofExpr (S.τ dim vs (F.par S.n)) (S.gc dim vs i) ∈ E.eqs :=
    fun i hi ↦ List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)))
  have hmem_s : ∀ v < S.nv, RationalPolynomial.ofExpr (S.τ dim vs (F.par S.n)) (S.statc dim vs v) ∈ E.eqs :=
    fun v hv ↦ List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨v, List.mem_range.mpr hv, rfl⟩)))
  have hmem_v : ∀ i < 3 * vs.length,
      RationalPolynomial.ofExpr (S.τ dim vs (F.par S.n)) (S.vertc dim vs i) ∈ E.eqs :=
    fun i hi ↦ List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
  have hW_lt : ∀ z i, i < S.n + dim → Sys.W S dim vs z i = z i := fun z i hi ↦ by
    simp only [Sys.W, Sys.σ_lt hi]; rfl
  have hW_vert : ∀ z r, r < 3 * vs.length → Sys.W S dim vs z (S.n + dim + r) =
      (S.V (vs.getD (r / 3) 0) ⟨r % 3, Nat.mod_lt _ (by norm_num)⟩).eval z := fun z r hr ↦ by
    simp only [Sys.W, Sys.σ_vert hr]
  have hW_rest : ∀ z i, S.n + dim + 3 * vs.length ≤ i → Sys.W S dim vs z i = 0 := fun z i hi ↦ by
    simp only [Sys.W, Sys.σ]
    rw [if_neg (by omega), if_neg (by omega)]
    simp [Expr.eval]
  have hV_congr : ∀ (z z' : ℕ → ℝ), (∀ j < dim, z (S.n + j) = z' (S.n + j)) → ∀ u c,
      (S.V u c).eval z = (S.V u c).eval z' := fun z z' h u c ↦ by
    rw [hV]; exact eval_vertsE_congr _ pts u c h
  have henv_par : ∀ (y : Fin K.n → ℝ) j, K.env (basisPar κ) y (S.n + j) = basisPar κ j :=
    fun y j ↦ by simp [Kraw.env, hn]
  have hvert : ∀ r < 3 * vs.length, zX (S.n + dim + r) =
      (S.V (vs.getD (r / 3) 0) ⟨r % 3, Nat.mod_lt _ (by norm_num)⟩).eval zX := fun r hr ↦ by
    have heq := hx.2 _ (hmem_v r hr)
    rw [RationalPolynomial.eval_ofExpr] at heq
    simp only [Sys.vertc, Expr.eval] at heq
    change zX (S.n + dim + r) - (S.V _ _).eval zX = 0 at heq
    exact sub_eq_zero.mp heq
  let y' : Fin K.n → ℝ := fun i ↦ zX i
  have hW : Sys.W S dim vs (K.env (basisPar κ) y') = zX := by
    funext i
    by_cases h1 : i < S.n
    · rw [hW_lt _ _ (by omega)]
      simp [Kraw.env, hn, h1, y']
    by_cases h2 : i < S.n + dim
    · obtain ⟨j, rfl⟩ : ∃ j, i = S.n + j := ⟨i - S.n, by omega⟩
      rw [hW_lt _ _ h2, henv_par, hzX_par j (by omega)]
    by_cases h3 : i < S.n + dim + 3 * vs.length
    · obtain ⟨r, rfl⟩ : ∃ r, i = S.n + dim + r := ⟨i - (S.n + dim), by omega⟩
      have hr : r < 3 * vs.length := by omega
      rw [hW_vert _ _ hr, hvert r hr]
      refine hV_congr _ _ (fun j hj ↦ ?_) _ _
      rw [henv_par, hzX_par j hj]
    · rw [hW_rest _ _ (by omega), hzX_rest _ (by omega)]
  have hbox : y' ∈ K.box := by
    rw [Kraw.mem_box]
    intro i
    have hi : (i : ℕ) < S.n := hn ▸ i.2
    rw [← Kraw.mem_kbox_iff]
    have hb := hx.1 (S.pos i) (by
      rw [Sys.box_length]; unfold Sys.pos; have := S.nx_lt; split_ifs <;> omega)
    rw [Sys.box_getD_pos _ _ _ _ _ _ _ hi] at hb
    simpa [y', hzX_unknown i hi] using hb
  have hF0 : K.F (basisPar κ) y' = 0 := by
    funext k
    have hk : (k : ℕ) < S.n := hn ▸ k.2
    change (K.eqs.getD k (.const 0)).eval (K.env (basisPar κ) y') = 0
    rw [hK]
    by_cases hkk : (k : ℕ) < S.k
    · rw [S.getD_eqs_g hkk, Sys.eval_g _ (hvs k hkk), hW]
      have := hx.2 _ (hmem_g k hkk)
      rwa [RationalPolynomial.eval_ofExpr] at this
    · obtain ⟨v, hv⟩ : ∃ v, (k : ℕ) = S.k + v := ⟨k - S.k, by omega⟩
      have hvn : v < S.nv := by rw [Sys.n] at hk; omega
      rw [hv, S.getD_eqs_stat hvn, Sys.eval_stat hV _ hvs hvn, hW]
      have := hx.2 _ (hmem_s v hvn)
      rwa [RationalPolynomial.eval_ofExpr] at this
  refine ⟨y', hbox, hF0, fun i hi ↦ ?_⟩
  rw [← hzX_unknown i hi]
  simp [Kraw.env, hn, hi, y']

end Sys

namespace RootRec

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- **A solution of a root's completed system is a zero of the root's system** in the box of
its test, with the solution's unknowns. -/
theorem zero_of_solves_explicitB (R : RootRec) (pts : List (V3 κ)) {F : ParData} (hF : F.Spec κ)
    {vb : List (ℚ × ℚ)} {x : ℕ → ℝ} (hx : (R.explicitB pts F vb).Solves x) :
    ∃ y : Fin (R.kraw pts).n → ℝ, y ∈ (R.kraw pts).box ∧ (R.kraw pts).F (basisPar κ) y = 0 ∧
      ∀ i < (R.sys pts).n, x ((R.sys pts).pos i) = (R.kraw pts).env (basisPar κ) y i := by
  set S := R.sys pts
  set E := S.explicitZ (ExactBasis.dim κ) R.vs (R.kraw pts) (F.par S.n) (F.eqs S.n) F.box
  have hB := (ZSystem.solves_toSystem _ x).mp hx
  have hE : E.Solves x := by
    refine ⟨fun i hi ↦ ?_, hB.2⟩
    have h := hB.1 i (by
      simp only [Sys.explicitZB, List.length_append]
      change i < E.box.length + vb.length
      omega)
    simp only [Sys.explicitZB] at h
    rwa [List.getD_append _ _ _ _ hi] at h
  refine Sys.zero_of_solves_explicitZ (R.kraw_eqs pts) rfl hF (fun i hi ↦ ?_) hE
  have hi' : i < R.contacts.length := hi
  simp only [Sys.con, RootRec.sys, List.getD_eq_getElem _ _ hi']
  exact R.mem_vs (List.getElem_mem hi')

end RootRec

end Root

/-! ### The pose root of a contact system -/

namespace RationalPolynomial

/-- The quaternion of rotation chart `k` in the variables `x 3, x 4, x 5` of a written-out system
(`Root.qE` with the scale first). -/
def cqP (k j : Fin 4) : RationalPolynomial :=
  if j = k then const 1 else var (3 + (if j < k then j.val else j.val - 1))

theorem eval_cqP (k j : Fin 4) (x : ℕ → ℝ) :
    (cqP k j).eval x = chartQuat k ![x 3, x 4, x 5] j := by
  fin_cases k <;> fin_cases j <;> simp [cqP, chartQuat]

/-- The translation of a written-out system scaled by `c`: `c (x 6, x 7)`, `0` in centred
mode. -/
def ctτ (cen : Bool) (c : ℚ) (i : ℕ) : RationalPolynomial := if cen then [] else mul (const c) (var (6 + i))

theorem eval_ctτ (cen : Bool) (c : ℚ) (i : ℕ) (x : ℕ → ℝ) :
    (ctτ cen c i).eval x = if cen then 0 else (c : ℝ) * x (6 + i) := by
  unfold ctτ
  split_ifs <;> simp [eval_mul]

end RationalPolynomial

namespace PolynomialSystem

open RationalPolynomial Root

/-- **The pose root of a contact system** `S₀` of the root record `R`: `S₀` with the witness of
its pose (`poseExt`), the translation scaled by `c`. -/
def ctSystem (S₀ : PolynomialSystem) (R : RootRec) (c : ℚ) (B : List (ℚ × ℚ)) : PolynomialSystem :=
  poseExt S₀ R.view (var 1) (var 2) (cqP R.rot) (ctτ R.cen c 0) (ctτ R.cen c 1) B

/-- The check of the pose root's definitions (`helpersOk`, `auxOk`). -/
def ctOk (S₀ : PolynomialSystem) (R : RootRec) (c : ℚ) (B : List (ℚ × ℚ)) : Bool :=
  helpersOk S₀ (var 1) (var 2) (cqP R.rot) &&
    (helperExt S₀ (var 1) (var 2) (cqP R.rot)).auxOk (ctSystem S₀ R c B) 20

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] [RootBasis κ]

/-- **ν and an optimal pose of a contact system as one root**: if the representatives' system
`S₀` (the completed system of the root record `R` over the points `pts`) has exactly one root, of
scale `N` (it is one of the systems `Ss` of `IsRootEq Ss N`), and the record's weak fit checks
on the balls of its box (with `zs` the contacts of its identities that check there: a separate
fact, since the identities' expansion is by well-founded recursion, which the kernel does not
evaluate), then the pose root
`ctSystem S₀ R c B` has exactly one root, of scale `N`, and its pose is a weak fit of
`P = (ofPoints pts).smul c` scaled by `N` through `P`. -/
theorem ct_isPoseRoot {pts : List (V3 κ)} {F : ParData} {R : RootRec} {vb : List (ℚ × ℚ)}
    {Ss : List PolynomialSystem} {S₀ : PolynomialSystem} {N : ℝ} {P : Polyhedron} {c : ℚ}
    {B : List (ℚ × ℚ)} {n : ℕ} (hSs : IsRootEq Ss N) (hmem : S₀ ∈ Ss) (hn : S₀.box.length = n)
    (hS : S₀ = R.explicitB pts F vb) (hF : F.Spec κ)
    (hpar : RootBasis.parCheck κ R.par = true) {zs : List (ℕ × ℕ × ℕ)}
    (hzs : Sys.zeroCons κ (R.sys pts) (R.kraw pts).boxBalls R.W = zs)
    (hW : (R.sys pts).weakOk pts.length (R.kraw pts).boxBalls R.W zs = true)
    (hP : P = (Polyhedron.ofPoints pts).smul (c : ℝ)) (hok : ctOk S₀ R c B = true) :
    IsPoseRoot P (ctSystem S₀ R c B) N (n + 12) (n + 3) (n + 21) := by
  subst hn
  simp only [ctOk, Bool.and_eq_true] at hok
  obtain ⟨hh, hb⟩ := hok
  obtain ⟨h1, h2⟩ := hSs.2 S₀ hmem
  obtain ⟨h3, h4⟩ := HasUniqueRoot.of_poseExt h1 hh hb
  refine ⟨h3, h4.trans h2, fun x hx ↦ ?_⟩
  -- the solution solves `S₀`, the root's completed system: a zero of the root's system
  have hx₂ := solves_of_aux (auxFacts hb) hx
  have hx₀ := solves_of_helperExt hx₂
  rw [hS] at hx₀
  obtain ⟨y, hy, h0, hxy⟩ := R.zero_of_solves_explicitB pts hF hx₀
  have hp : (R.kraw pts).ParOk (basisPar κ) := RootRec.parOk hpar
  have hY := (R.kraw pts).encl_boxBalls hp hy
  have hzero : ∀ c ∈ (R.sys pts).contacts,
      ((R.sys pts).slack c).eval ((R.kraw pts).env (basisPar κ) y) = 0 :=
    fun c hc ↦ Sys.slack_zero_of_mem (R.kraw_eqs pts) h0 hc
  have hzs : ∀ c ∈ zs, ((R.sys pts).slack c).eval ((R.kraw pts).env (basisPar κ) y) = 0 :=
    fun c hc ↦ Sys.slack_zero_of_mem_zeroCons' (R.kraw_eqs pts) h0 hY (hzs ▸ hc)
  have hw := (Sys.screenWeak_of_weakOk hY (RootRec.mem_vertices y) hzero hzs hW).smul (c : ℝ)
  rw [← hP] at hw
  -- the zero's coordinates are the solution's
  generalize hz0 : (R.kraw pts).env (basisPar κ) y = z at hw hxy
  have hsn : ∀ i ≤ nx R.cen, i < (R.sys pts).n := fun i hi ↦ by
    change i < nx R.cen + 1 + R.contacts.length
    omega
  have hz : ∀ i < nx R.cen, z i = x (i + 1) := fun i hi ↦ by
    rw [← hxy i (hsn i hi.le)]
    simp only [Sys.pos]
    rw [if_neg (by change ¬i = nx R.cen; omega), if_pos (show i < nx (R.sys pts).cen from hi)]
  have hl : (lE R.cen).eval z = x 0 := by
    have h := hxy (nx R.cen) (hsn _ le_rfl)
    simp only [Sys.pos] at h
    rw [if_pos (show nx R.cen = nx (R.sys pts).cen from rfl)] at h
    rw [h]
    rfl
  have hnx : 5 ≤ nx R.cen := by unfold nx; split_ifs <;> omega
  have hrot : chartRotation R.rot ![z 2, z 3, z 4] =
      quatRotation fun m ↦ (cqP R.rot m).eval x := by
    rw [chartRotation]
    congr 1
    funext m
    rw [eval_cqP, hz 2 (by omega), hz 3 (by omega), hz 4 (by omega)]
  have hτ : (c : ℝ) • yOf z R.cen = ![(ctτ R.cen c 0).eval x, (ctτ R.cen c 1).eval x] := by
    ext i
    cases hc : R.cen
    · have h5 := hz 5 (by simp [nx, hc])
      have h6 := hz 6 (by simp [nx, hc])
      fin_cases i <;> simp [yOf, yE, eval_ctτ, h5, h6]
    · fin_cases i <;> simp [yOf, yE, eval_ctτ]
  change ScreenWeak P R.view (z 0) (z 1) (chartRotation R.rot ![z 2, z 3, z 4])
    ((c : ℝ) • yOf z R.cen) ((lE R.cen).eval z) at hw
  rw [hl, hrot, hτ, hz 0 (by omega), hz 1 (by omega)] at hw
  have hv : ∀ i, (var i).eval x = x i := fun i ↦ eval_var i x
  rw [← hv 1, ← hv 2] at hw
  exact poseExt_poseAt hx hw

end PolynomialSystem

end Nieuwland
