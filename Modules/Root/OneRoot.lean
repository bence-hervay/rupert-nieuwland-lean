import Modules.Root.Explicit
import Modules.System.PolyRootOf

/-!
# A root's written-out system has exactly one root

`Modules/Root/Explicit.lean` writes a root record's system out as a `PolynomialSystem` and shows that
it has one scale (`RootRec.scales_explicit`). Here the same system, **with an interval for every
variable**, has exactly one root (`PolynomialSystem.HasUniqueRoot`, `Modules/System/PolyRootOf.lean`).

**The completed box.** The written-out system has intervals for the scale, pose, translation and
multipliers (the box of Krawczyk's test) and for the field's generator. `RootRec.explicitB` adds
intervals `vb` for the coordinates of the vertices, three per vertex of the root's contacts; they
are data of the statement, checked by `vboxOk`: each holds its coordinate, by the field's sound
sign test (`Check.Exact.nonneg`) of integer combinations. The equations are those of
`RootRec.explicit`, unchanged.

**Why one root** (`Sys.oneRoot_explicitB`). A solution of the written-out system gives a zero of
the root's system in the box of Krawczyk's test, which is the only one (`Kraw.IsZero`, from the
certificate): that fixes the scale, pose, translation and multipliers. The generator is the only
root of its equation in its interval (`ParData.Unique`: `sqrt_unique`, `theta_unique`). Each
vertex coordinate is fixed by its own equation. This holds for fields with a generator
(`F.box.length = 1`: `ℤ[√d]` and `ℤ[α]`); a solid with rational coordinates has no generator
variable, and its unused slot is not covered here.

## Main statements

* `Nieuwland.Root.ParData.Unique`, `sqrt_unique`, `theta_unique`: the generator is determined.
* `Nieuwland.Root.vboxOk`, `vboxOk_sound`: the test of the vertices' intervals (`vboxOf` proposes
  them: the coordinates' integer parts).
* `Nieuwland.Root.RootRec.oneRoot_explicitB`: the completed system of a root record has exactly one
  root.
* `Nieuwland.Root.IsSystemOf`, `IsSystemOf.oneRoot`, `IsSystemOf.scales_eq`: **one system at a
  time**: a system that is the completed system of a root has exactly one root, and the scales of
  the root's written-out system (the system of the theorems `<def>_exact_list`).
* `Nieuwland.Root.isRootMax_topScale`, `isRootMax_one`: the Nieuwland number of a root-form
  certificate is the largest scale of its roots' completed systems, each with exactly one root:
  the per-system fact for each system of the list, and the maximum of
  `Root.isGreatest_topScale`.
-/

open Finset

namespace Nieuwland.Root

open Check (Expr V3 Exact ExactBasis)

/-! ### The generator is determined -/

/-- The generator's conditions have one solution: two points that satisfy them agree on the
generator's variables. -/
def ParData.Unique (D : ParData) : Prop :=
  ∀ (G : ℕ) (x x' : ℕ → ℝ), InBox D.box G x → (∀ p ∈ D.eqs G, p.eval x = 0) →
    InBox D.box G x' → (∀ p ∈ D.eqs G, p.eval x' = 0) → ∀ i < D.box.length, x (G + i) = x' (G + i)

namespace ParData

theorem sqrt_unique {d : ℕ} {lo hi : ℚ} (h : sqrtOk d lo hi = true) : (sqrt d lo hi).Unique := by
  simp only [sqrtOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hlo, -⟩, -⟩, -⟩ := h
  have hlo' : (0 : ℝ) ≤ lo := by exact_mod_cast hlo
  have key : ∀ (G : ℕ) (x : ℕ → ℝ), InBox (sqrt d lo hi).box G x →
      (∀ p ∈ (sqrt d lo hi).eqs G, p.eval x = 0) → x G = √(d : ℝ) := by
    intro G x hb he
    have hx := hb 0 (by simp [sqrt])
    simp only [sqrt, List.getD_cons_zero, add_zero] at hx
    have he' := he _ (List.mem_singleton_self _)
    simp only [RationalPolynomial.eval_cons, RationalPolynomial.monomial_mono, RationalPolynomial.monomial_nil,
      RationalPolynomial.eval_nil] at he'
    have hx0 : 0 ≤ x G := hlo'.trans hx.1
    rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (Nat.cast_nonneg _) hx0]
    push_cast at he'
    nlinarith
  intro G x x' hb he hb' he' i hi
  obtain rfl : i = 0 := by simpa [sqrt] using hi
  rw [add_zero, key G x hb he, key G x' hb' he']

theorem theta_unique (R : Check.Root) : (theta R).Unique := by
  have key : ∀ (G : ℕ) (x : ℕ → ℝ), InBox (theta R).box G x →
      (∀ p ∈ (theta R).eqs G, p.eval x = 0) → R.α = x G := by
    intro G x hb he
    have hx := hb 0 (by simp [theta])
    simp only [theta, List.getD_cons_zero, add_zero] at hx
    push_cast at hx
    have he' := he _ (List.mem_singleton_self _)
    rw [evalZ_ofUni] at he'
    exact R.eq_of_root hx.1 hx.2 he'
  intro G x x' hb he hb' he' i hi
  obtain rfl : i = 0 := by simpa [theta] using hi
  rw [add_zero, ← key G x hb he, ← key G x' hb' he']

end ParData

/-! ### The intervals of the vertices' coordinates -/

section VBox

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- A sound test of `b.1 ≤ re a ≤ b.2`: the signs of `den * a - num` at both ends. -/
def inIcc (a : κ) (b : ℚ × ℚ) : Bool :=
  Exact.nonneg (Exact.ofInt (b.1.den : ℤ) * a - Exact.ofInt b.1.num) &&
    Exact.nonneg (Exact.ofInt b.2.num - Exact.ofInt (b.2.den : ℤ) * a)

theorem inIcc_sound {a : κ} {b : ℚ × ℚ} (h : inIcc a b = true) :
    (b.1 : ℝ) ≤ Exact.re a ∧ Exact.re a ≤ (b.2 : ℝ) := by
  rw [inIcc, Bool.and_eq_true] at h
  have h1 := Exact.nonneg_sound _ h.1
  have h2 := Exact.nonneg_sound _ h.2
  rw [Exact.re_sub, Exact.re_mul, Exact.re_ofInt, Exact.re_ofInt] at h1 h2
  have hd1 : (0 : ℝ) < b.1.den := by exact_mod_cast b.1.den_pos
  have hd2 : (0 : ℝ) < b.2.den := by exact_mod_cast b.2.den_pos
  have e1 : (b.1 : ℝ) = (b.1.num : ℝ) / (b.1.den : ℝ) := by exact_mod_cast (Rat.num_div_den b.1).symm
  have e2 : (b.2 : ℝ) = (b.2.num : ℝ) / (b.2.den : ℝ) := by exact_mod_cast (Rat.num_div_den b.2).symm
  push_cast at h1 h2
  rw [e1, e2, div_le_iff₀ hd1, le_div_iff₀ hd2]
  constructor <;> linarith

/-- The coordinate `r % 3` of the vertex `vs[r / 3]` of `pts`. -/
def vcoord (pts : List (V3 κ)) (vs : List ℕ) (r : ℕ) : κ :=
  (Exact.pt pts (vs.getD (r / 3) 0)).get ⟨r % 3, Nat.mod_lt _ (by norm_num)⟩

/-- The test of the intervals `vb` of the vertices' coordinates: three for each vertex of `vs`, in
turn, each holding its coordinate (`inIcc`). -/
def vboxOk (pts : List (V3 κ)) (vs : List ℕ) (vb : List (ℚ × ℚ)) : Bool :=
  decide (vb.length = 3 * vs.length) &&
    (List.range (3 * vs.length)).all fun r ↦ inIcc (vcoord pts vs r) (vb.getD r (0, 0))

theorem vboxOk_sound {pts : List (V3 κ)} {vs : List ℕ} {vb : List (ℚ × ℚ)}
    (h : vboxOk pts vs vb = true) : vb.length = 3 * vs.length ∧ ∀ r < 3 * vs.length,
      ((vb.getD r (0, 0)).1 : ℝ) ≤ Exact.re (vcoord pts vs r) ∧
        Exact.re (vcoord pts vs r) ≤ ((vb.getD r (0, 0)).2 : ℝ) := by
  rw [vboxOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1, fun r hr ↦ inIcc_sound (h.2 r (List.mem_range.mpr hr))⟩

/-- `m`, doubled until the sign test shows `-m ≤ re a ≤ m` (`fuel` only ends the recursion). -/
def ipartBound (ge le : ℤ → Bool) : ℕ → ℤ → ℤ
  | 0, m => m
  | fuel + 1, m => if ge (-m) && le m then m else ipartBound ge le fuel (2 * m)

/-- `(lo, hi)` with `lo ≤ re a ≤ hi` shown, halved while the sign test places the midpoint and
the ends are more than `1` apart. -/
def ipartBisect (ge le : ℤ → Bool) : ℕ → ℤ × ℤ → ℤ × ℤ
  | 0, p => p
  | fuel + 1, p => if p.2 - p.1 ≤ 1 then p else
      let mid := (p.1 + p.2) / 2
      if ge mid then ipartBisect ge le fuel (mid, p.2)
      else if le mid then ipartBisect ge le fuel (p.1, mid)
      else p

/-- An interval of integers for `re a`, found with the sign test: `[k, k]` for an integer `k`,
else `[⌊a⌋, ⌊a⌋ + 1]`, or a wider one where the test does not place a midpoint. No bound on the
size of `a` is assumed (the numbers of steps only end the recursions: `2 ^ 100000`). Nothing rests
on it: `vboxOk` decides the intervals that a statement uses. -/
def ipart (a : κ) : ℚ × ℚ :=
  let ge (k : ℤ) : Bool := Exact.nonneg (a - Exact.ofInt k)
  let le (k : ℤ) : Bool := Exact.nonneg (Exact.ofInt k - a)
  let m := ipartBound ge le 100000 1
  let p := ipartBisect ge le 100002 (-m, m)
  if le p.1 then (p.1, p.1) else if ge p.2 then (p.2, p.2) else (p.1, p.2)

/-- Intervals of integers for the coordinates of the vertices `vs` (`ipart`): what the generated
statements use, each checked by `vboxOk`. -/
def vboxOf (pts : List (V3 κ)) (vs : List ℕ) : List (ℚ × ℚ) :=
  (List.range (3 * vs.length)).map fun r ↦ ipart (vcoord pts vs r)

end VBox

/-! ### The completed system -/

namespace Sys

/-- The written-out system of a root with the intervals `vb` of the vertices' coordinates after
its box: the equations of `Sys.explicitZ`. -/
def explicitZB (S : Sys) (dim : ℕ) (vs : List ℕ) (K : Kraw) (par : ℕ → RationalPolynomial)
    (geqs : List RationalPolynomial) (gbox vb : List (ℚ × ℚ)) : ZSystem where
  eqs := (S.explicitZ dim vs K par geqs gbox).eqs
  box := (S.explicitZ dim vs K par geqs gbox).box ++ vb

/-- **The completed written-out system** of a root: `Sys.explicit` with an interval for every
variable. -/
def explicitB (S : Sys) (dim : ℕ) (vs : List ℕ) (K : Kraw) (par : ℕ → RationalPolynomial)
    (geqs : List RationalPolynomial) (gbox vb : List (ℚ × ℚ)) : PolynomialSystem :=
  (S.explicitZB dim vs K par geqs gbox vb).toSystem

end Sys

section Main

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- **The solutions of a root's written-out system.** With the only zero `y` of the root's system
in the box of the test: at a solution `x`, the unknowns are those of `y`, the generator's
conditions hold and the coordinate variables are the vertices' coordinates. -/
theorem Sys.solves_explicit {S : Sys} {K : Kraw} (hK : K.eqs = S.eqs) {pts : List (V3 κ)}
    (hV : S.V = vertsE S.n pts) {F : ParData} (hF : F.Spec κ) {vs : List ℕ}
    (hvs : ∀ i < S.k, (S.con i).1 ∈ vs ∧ (S.con i).2.1 ∈ vs ∧ (S.con i).2.2 ∈ vs)
    {y : Fin K.n → ℝ} (hz : K.IsZero (basisPar κ) y) {x : ℕ → ℝ}
    (hx : (S.explicitZ (ExactBasis.dim κ) vs K (F.par S.n) (F.eqs S.n) F.box).Solves x) :
    (∀ i < S.n, x (S.pos i) = K.env (basisPar κ) y i) ∧
      (InBox F.box S.n x ∧ ∀ p ∈ F.eqs S.n, p.eval x = 0) ∧
      ∀ r < 3 * vs.length, x (S.n + 1 + r) = Exact.re (vcoord pts vs r) := by
  obtain ⟨hsound, -⟩ := hF
  set dim := ExactBasis.dim κ
  set E := S.explicitZ dim vs K (F.par S.n) (F.eqs S.n) F.box with hE
  have hn : K.n = S.n := Sys.n_eq hK
  -- the parameters are the basis values where the generator's conditions hold
  have hgen : InBox F.box S.n x ∧ ∀ p ∈ F.eqs S.n, p.eval x = 0 := by
    obtain ⟨hb, he⟩ := hx
    refine ⟨fun i hi ↦ ?_, fun p hp ↦ he p (List.mem_append_right _ hp)⟩
    have := hb (S.n + i) (by rw [Sys.box_length]; omega)
    rwa [Sys.box_getD_gen] at this
  have hpar := hsound S.n x hgen.1 hgen.2
  -- the point of the root's system of the point `x`
  let zX : ℕ → ℝ := fun i ↦ (S.τ dim vs (F.par S.n) i).eval x
  have hzX_unknown : ∀ i, i < S.n → zX i = x (S.pos i) := fun i hi ↦ by
    simp only [zX, S.τ_unknown dim vs _ hi, RationalPolynomial.eval_var]
  have hzX_par : ∀ j < dim, zX (S.n + j) = basisPar κ j := fun j hj ↦ by
    simp only [zX, Sys.τ]
    rw [if_neg (by have := S.nx_lt; omega), if_neg (by have := S.nx_lt; omega),
      if_neg (by omega), if_pos (by omega)]
    rw [show S.n + j - S.n = j by omega, hpar]
  have hzX_vert : ∀ r, r < 3 * vs.length → zX (S.n + dim + r) = x (S.n + 1 + r) :=
    fun r hr ↦ by
      simp only [zX, Sys.τ]
      rw [if_neg (by have := S.nx_lt; omega), if_neg (by have := S.nx_lt; omega),
        if_neg (by omega), if_neg (by omega), if_pos (by omega), RationalPolynomial.eval_var]
      congr 1
      omega
  have hzX_rest : ∀ i, S.n + dim + 3 * vs.length ≤ i → zX i = 0 := fun i hi ↦ by
    simp only [zX, Sys.τ]
    rw [if_neg (by have := S.nx_lt; omega), if_neg (by have := S.nx_lt; omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp
  -- membership of the equations
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
  -- the values of `σ` agree with the parameters
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
  -- the vertices' equations: the coordinate variables are the vertices' coordinates
  have hvert : ∀ r < 3 * vs.length, zX (S.n + dim + r) =
      (S.V (vs.getD (r / 3) 0) ⟨r % 3, Nat.mod_lt _ (by norm_num)⟩).eval zX := fun r hr ↦ by
    have heq := hx.2 _ (hmem_v r hr)
    rw [RationalPolynomial.eval_ofExpr] at heq
    simp only [Sys.vertc, Expr.eval] at heq
    change zX (S.n + dim + r) - (S.V _ _).eval zX = 0 at heq
    exact sub_eq_zero.mp heq
  -- the point gives a zero of the root's system
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
  have hy : y' = y := hz.2 y' ⟨hbox, hF0⟩
  refine ⟨fun i hi ↦ ?_, hgen, fun r hr ↦ ?_⟩
  · rw [← hzX_unknown i hi, ← hy]
    simp [Kraw.env, hn, hi, y']
  · rw [← hzX_vert r hr, hvert r hr, hV]
    exact eval_elemE zX S.n (fun j hj ↦ by
      rw [hzX_par j hj]; unfold basisPar; rw [if_pos hj]) _

/-- **The completed written-out system of a root has exactly one root.** If the root's system has
exactly one zero in the box of the test (`Kraw.IsZero`), the field has a generator, which its
conditions determine (`ParData.Unique`), the intervals `vb` hold the vertices' coordinates
(`vboxOk`) and every variable of the equations has an interval, the completed system has exactly
one root. -/
theorem Sys.oneRoot_explicitB {S : Sys} {K : Kraw} (hK : K.eqs = S.eqs) {pts : List (V3 κ)}
    (hV : S.V = vertsE S.n pts) {F : ParData} (hF : F.Spec κ) (hU : F.Unique)
    (hF1 : F.box.length = 1) {vs : List ℕ}
    (hvs : ∀ i < S.k, (S.con i).1 ∈ vs ∧ (S.con i).2.1 ∈ vs ∧ (S.con i).2.2 ∈ vs)
    {y : Fin K.n → ℝ} (hz : K.IsZero (basisPar κ) y) {vb : List (ℚ × ℚ)}
    (hvb : vboxOk pts vs vb = true)
    (hb : (S.explicitB (ExactBasis.dim κ) vs K (F.par S.n) (F.eqs S.n) F.box vb).boxed = true) :
    (S.explicitB (ExactBasis.dim κ) vs K (F.par S.n) (F.eqs S.n) F.box vb).HasUniqueRoot := by
  obtain ⟨hvl, hvin⟩ := vboxOk_sound hvb
  set dim := ExactBasis.dim κ
  set E := S.explicitZ dim vs K (F.par S.n) (F.eqs S.n) F.box with hE
  set B := S.explicitZB dim vs K (F.par S.n) (F.eqs S.n) F.box vb with hB
  have hEl : E.box.length = S.n + 1 := by rw [hE, Sys.box_length, hF1]
  have hBl : B.box.length = S.n + 1 + 3 * vs.length := by
    rw [hB, Sys.explicitZB, List.length_append, ← hE, hEl, hvl]
  -- a solution of the completed system solves the written-out one
  have hBE : ∀ x : ℕ → ℝ, B.Solves x → E.Solves x := fun x hx ↦ by
    refine ⟨fun i hi ↦ ?_, hx.2⟩
    have := hx.1 i (by rw [hBl]; omega)
    rwa [hB, Sys.explicitZB, List.getD_append _ _ _ _ hi] at this
  -- a solution of the written-out system solves the completed one
  have hEB : ∀ x : ℕ → ℝ, E.Solves x → B.Solves x := fun x hx ↦ by
    refine ⟨fun i hi ↦ ?_, hx.2⟩
    rw [hBl] at hi
    by_cases h : i < S.n + 1
    · have := hx.1 i (by rw [hEl]; exact h)
      rwa [hB, Sys.explicitZB, List.getD_append _ _ _ _ (by rw [hEl]; exact h)]
    · obtain ⟨r, rfl⟩ : ∃ r, i = S.n + 1 + r := ⟨i - (S.n + 1), by omega⟩
      have hr : r < 3 * vs.length := by omega
      rw [hB, Sys.explicitZB, List.getD_append_right _ _ _ _ (by rw [hEl]; omega), hEl,
        show S.n + 1 + r - (S.n + 1) = r by omega,
        (Sys.solves_explicit hK hV hF hvs hz hx).2.2 r hr]
      exact hvin r hr
  -- a solution exists: the written-out system has a scale
  obtain ⟨x, hx⟩ : ∃ x : ℕ → ℝ, E.Solves x := by
    have h := Sys.scales_explicit hK hV hF hvs hz
    rw [Sys.explicit, ZSystem.scales_toSystem] at h
    have hm : K.env (basisPar κ) y (nx S.cen) ∈
        {l | ∃ x : ℕ → ℝ, E.Solves x ∧ x 0 = l} := by rw [h]; rfl
    obtain ⟨x, hx, -⟩ := hm
    exact ⟨x, hx⟩
  refine ⟨?_, hb, x, ?_, fun x' hx' i hi ↦ ?_⟩
  · change 0 < B.toSystem.box.length
    change 0 < B.box.length
    rw [hBl]; omega
  · exact (ZSystem.solves_toSystem B x).mpr (hEB x hx)
  · have hx'E := hBE x' ((ZSystem.solves_toSystem B x').mp hx')
    obtain ⟨hu, ⟨hgb, hge⟩, hv⟩ := Sys.solves_explicit hK hV hF hvs hz hx
    obtain ⟨hu', ⟨hgb', hge'⟩, hv'⟩ := Sys.solves_explicit hK hV hF hvs hz hx'E
    have hi' : i < S.n + 1 + 3 * vs.length := by
      have : i < B.box.length := hi
      rwa [hBl] at this
    have hnx := S.nx_lt
    by_cases h1 : i < S.n
    · -- the unknown at the explicit index `i`
      let j := if i = 0 then nx S.cen else if i ≤ nx S.cen then i - 1 else i
      have hj : j < S.n := by simp only [j]; split_ifs <;> omega
      have hpos : S.pos j = i := by simp only [j, Sys.pos]; split_ifs <;> omega
      rw [← hpos, hu j hj, hu' j hj]
    by_cases h2 : i = S.n
    · have := hU S.n x' x hgb' hge' hgb hge 0 (by rw [hF1]; exact Nat.one_pos)
      rw [h2]
      simpa using this
    · obtain ⟨r, rfl⟩ : ∃ r, i = S.n + 1 + r := ⟨i - (S.n + 1), by omega⟩
      rw [hv r (by omega), hv' r (by omega)]

/-- The completed written-out system of a root record, with the intervals `vb` of its vertices'
coordinates. -/
def RootRec.explicitB (R : RootRec) (pts : List (V3 κ)) (F : ParData) (vb : List (ℚ × ℚ)) :
    PolynomialSystem :=
  (R.sys pts).explicitB (ExactBasis.dim κ) R.vs (R.kraw pts) (F.par (R.sys pts).n)
    (F.eqs (R.sys pts).n) F.box vb

/-- **The completed system of a root record has exactly one root.** -/
theorem RootRec.oneRoot_explicitB (R : RootRec) (pts : List (V3 κ)) {F : ParData}
    (hF : F.Spec κ) (hU : F.Unique) (hF1 : F.box.length = 1)
    {y : Fin (R.kraw pts).n → ℝ} (hz : (R.kraw pts).IsZero (basisPar κ) y) {vb : List (ℚ × ℚ)}
    (hvb : vboxOk pts R.vs vb = true) (hb : (R.explicitB pts F vb).boxed = true) :
    (R.explicitB pts F vb).HasUniqueRoot := by
  refine Sys.oneRoot_explicitB (R.kraw_eqs pts) (pts := pts) rfl hF hU hF1 (fun i hi ↦ ?_) hz hvb hb
  have hi' : i < R.contacts.length := hi
  simp only [Sys.con, RootRec.sys, List.getD_eq_getElem _ _ hi']
  exact R.mem_vs (List.getElem_mem hi')

/-- The completed system has the scales of the written-out one when the intervals hold the
vertices' coordinates. -/
theorem RootRec.scales_explicitB (R : RootRec) (pts : List (V3 κ)) {F : ParData}
    (hF : F.Spec κ) (hU : F.Unique) (hF1 : F.box.length = 1)
    {y : Fin (R.kraw pts).n → ℝ} (hz : (R.kraw pts).IsZero (basisPar κ) y) {vb : List (ℚ × ℚ)}
    (hvb : vboxOk pts R.vs vb = true) (hb : (R.explicitB pts F vb).boxed = true) :
    PolynomialSystem.scales [R.explicitB pts F vb] = PolynomialSystem.scales [R.explicit pts F] := by
  obtain ⟨h0, -, x, hx, hu⟩ := R.oneRoot_explicitB pts hF hU hF1 hz hvb hb
  have hE : (R.explicit pts F).Solves x := by
    refine ⟨fun i hi ↦ ?_, hx.2⟩
    have hi' : i < ((R.sys pts).explicitZ (ExactBasis.dim κ) R.vs (R.kraw pts)
        (F.par (R.sys pts).n) (F.eqs (R.sys pts).n) F.box).box.length := hi
    have hlt : i < (R.explicitB pts F vb).box.length := by
      change i < (_ ++ vb).length
      rw [List.length_append]
      exact Nat.lt_add_right _ hi'
    have := hx.1 i hlt
    change (((_ ++ vb).getD i (0, 0)).1 : ℝ) ≤ x i ∧ x i ≤ (((_ ++ vb).getD i (0, 0)).2 : ℝ) at this
    rw [List.getD_append _ _ _ _ hi'] at this
    exact this
  rw [R.scales_explicit pts hF hz]
  have hxs : x 0 ∈ PolynomialSystem.scales [R.explicit pts F] :=
    ⟨_, List.mem_singleton_self _, x, hE, rfl⟩
  rw [R.scales_explicit pts hF hz, Set.mem_singleton_iff] at hxs
  ext l
  simp only [PolynomialSystem.scales, Set.mem_ofPred_eq, List.mem_singleton, exists_eq_left,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨x', hx', rfl⟩
    rw [hu x' hx' 0 h0, hxs]
  · rintro rfl
    exact ⟨x, hx, hxs⟩

end Main

/-! ### One system of a root -/

section One

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The completed system has the equations of the written-out system. -/
theorem RootRec.explicitB_eqs (R : RootRec) (pts : List (V3 κ)) (F : ParData)
    (vb : List (ℚ × ℚ)) : (R.explicitB pts F vb).eqs = (R.explicit pts F).eqs := rfl

/-- The completed system has the intervals of the written-out system, then those of the
vertices' coordinates. -/
theorem RootRec.explicitB_box (R : RootRec) (pts : List (V3 κ)) (F : ParData)
    (vb : List (ℚ × ℚ)) : (R.explicitB pts F vb).box = (R.explicit pts F).box ++ vb := rfl

/-- **`S` is the completed system of the root `R`**: the written-out system of `R` with intervals
that hold its vertices' coordinates (`vboxOk`), and every variable of its equations has an
interval. All three are checks of the system's data. -/
def IsSystemOf (pts : List (V3 κ)) (F : ParData) (R : RootRec) (S : PolynomialSystem) : Prop :=
  S.boxed = true ∧ ∃ vb, vboxOk pts R.vs vb = true ∧ S = R.explicitB pts F vb

theorem IsSystemOf.intro {pts : List (V3 κ)} {F : ParData} {R : RootRec} {S : PolynomialSystem}
    (vb : List (ℚ × ℚ)) (hvb : vboxOk pts R.vs vb = true) (hS : S = R.explicitB pts F vb)
    (hb : S.boxed = true) : IsSystemOf pts F R S :=
  ⟨hb, vb, hvb, hS⟩

/-- **One system, exactly one root**: the completed system of a root whose system has exactly one
zero in the box of Krawczyk's test. -/
theorem IsSystemOf.oneRoot {pts : List (V3 κ)} {F : ParData} {R : RootRec} {S : PolynomialSystem}
    (h : IsSystemOf pts F R S) (hF : F.Spec κ) (hU : F.Unique) (hF1 : F.box.length = 1)
    {P : (Fin (R.kraw pts).n → ℝ) → Prop}
    (hz : ∃ y, (R.kraw pts).IsZero (basisPar κ) y ∧ P y) : S.HasUniqueRoot := by
  obtain ⟨hb, vb, hvb, rfl⟩ := h
  obtain ⟨y, hy, -⟩ := hz
  exact R.oneRoot_explicitB pts hF hU hF1 hy hvb hb

/-- **The same scales as before**: the completed system of a root has the scales of its
written-out system (the system of `Root.isMaxSingle_topScale`). -/
theorem IsSystemOf.scales_eq {pts : List (V3 κ)} {F : ParData} {R : RootRec} {S : PolynomialSystem}
    (h : IsSystemOf pts F R S) (hF : F.Spec κ) (hU : F.Unique) (hF1 : F.box.length = 1)
    {P : (Fin (R.kraw pts).n → ℝ) → Prop}
    (hz : ∃ y, (R.kraw pts).IsZero (basisPar κ) y ∧ P y) :
    PolynomialSystem.scales [S] = PolynomialSystem.scales [R.explicit pts F] := by
  obtain ⟨hb, vb, hvb, rfl⟩ := h
  obtain ⟨y, hy, -⟩ := hz
  exact R.scales_explicitB pts hF hU hF1 hy hvb hb

end One

/-! ### The Nieuwland number of a root-form certificate -/

section Top

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

open PolynomialSystem

private theorem exists_left_of_forall₂ {α β : Type} {r : α → β → Prop} {l₁ : List α}
    {l₂ : List β} (h : List.Forall₂ r l₁ l₂) : ∀ b ∈ l₂, ∃ a ∈ l₁, r a b := by
  induction h with
  | nil => intro b hb; simp at hb
  | cons hab _ ih =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons.mpr (Or.inl rfl), hab⟩
    · obtain ⟨a, ha, hr⟩ := ih b hb
      exact ⟨a, List.mem_cons.mpr (Or.inr ha), hr⟩

private theorem exists_right_of_forall₂ {α β : Type} {r : α → β → Prop} {l₁ : List α}
    {l₂ : List β} (h : List.Forall₂ r l₁ l₂) : ∀ a ∈ l₁, ∃ b ∈ l₂, r a b := by
  induction h with
  | nil => intro a ha; simp at ha
  | cons hab _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, List.mem_cons.mpr (Or.inl rfl), hab⟩
    · obtain ⟨b, hb, hr⟩ := ih a ha
      exact ⟨b, List.mem_cons.mpr (Or.inr hb), hr⟩

/-- **A root form of several roots, one root per system**: `isMaxSingle_topScale` for completed
systems. `Ss` are the completed systems of the roots `T`, in turn (`IsSystemOf`, one fact per
system); the number is the largest scale of them, and each has exactly one root. -/
theorem isRootMax_topScale {pts : List (V3 κ)} {F : ParData} (hF : F.Spec κ) (hU : F.Unique)
    (hF1 : F.box.length = 1) {R : RootRec} {Rs : List RootRec} {N : ℝ}
    (hN : N = topScale pts R Rs)
    (hz : ∀ R' ∈ R :: Rs, ∃ y, (R'.kraw pts).IsZero (basisPar κ) y ∧
      R'.scale pts = (R'.kraw pts).env (basisPar κ) y (nx R'.cen))
    (T : List ℕ) (hT : ∀ i ∈ T, i < (R :: Rs).length) (hsep : sepOk R Rs T = true)
    {Ss : List PolynomialSystem}
    (hSs : List.Forall₂ (fun i S ↦ IsSystemOf pts F ((R :: Rs).getD i R) S) T Ss) :
    IsRootMax Ss N := by
  set A := R :: Rs
  have hmemA : ∀ i ∈ T, A.getD i R ∈ A := fun i hi ↦ by
    rw [List.getD_eq_getElem _ _ (hT i hi)]; exact List.getElem_mem _
  have hl := exists_left_of_forall₂ hSs
  have hr := exists_right_of_forall₂ hSs
  -- the scales of the completed systems are those of the written-out systems of `T`
  have hsc : scales Ss = scales (T.map fun i ↦ (A.getD i R).explicit pts F) := by
    ext l
    constructor
    · rintro ⟨S, hS, x, hx, rfl⟩
      obtain ⟨i, hi, h⟩ := hl S hS
      have h0 : x 0 ∈ scales [S] := ⟨_, List.mem_singleton_self _, x, hx, rfl⟩
      rw [h.scales_eq hF hU hF1 (hz _ (hmemA i hi))] at h0
      obtain ⟨S', hS', x', hx', h1⟩ := h0
      rw [List.mem_singleton.mp hS'] at hx'
      exact ⟨_, List.mem_map.mpr ⟨i, hi, rfl⟩, x', hx', h1⟩
    · rintro ⟨S, hS, x, hx, rfl⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hS
      obtain ⟨S', hS', h⟩ := hr i hi
      have h0 : x 0 ∈ scales [(A.getD i R).explicit pts F] :=
        ⟨_, List.mem_singleton_self _, x, hx, rfl⟩
      rw [← h.scales_eq hF hU hF1 (hz _ (hmemA i hi))] at h0
      obtain ⟨S'', hS'', x', hx', h1⟩ := h0
      rw [List.mem_singleton.mp hS''] at hx'
      exact ⟨S', hS', x', hx', h1⟩
  refine ⟨?_, fun S hS ↦ ?_⟩
  · rw [hsc]
    exact isGreatest_topScale hF hN hz T hT hsep rfl
  · obtain ⟨i, hi, h⟩ := hl S hS
    exact h.oneRoot hF hU hF1 (hz _ (hmemA i hi))

/-- **A root form of one root, one root of its system**: `isMaxSingle_one` for the completed
system. -/
theorem isRootMax_one {pts : List (V3 κ)} {F : ParData} (hF : F.Spec κ) (hU : F.Unique)
    (hF1 : F.box.length = 1) {R : RootRec} {N : ℝ}
    (h : ∃ y, (R.kraw pts).IsZero (basisPar κ) y ∧ N = (R.kraw pts).env (basisPar κ) y (nx R.cen))
    {S : PolynomialSystem} (hS : IsSystemOf pts F R S) : IsRootMax [S] N := by
  refine ⟨?_, fun S' hS' ↦ ?_⟩
  · have hs := hS.scales_eq hF hU hF1 h
    obtain ⟨y, hy, rfl⟩ := h
    rw [hs, R.scales_explicit pts hF hy]
    exact isGreatest_singleton
  · rw [List.mem_singleton.mp hS']
    exact hS.oneRoot hF hU hF1 h

end Top

end Nieuwland.Root
