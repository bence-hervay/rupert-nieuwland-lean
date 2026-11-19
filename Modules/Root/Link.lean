import Mathlib.Analysis.Calculus.Deriv.Inv
import Modules.Root.LinkMap

/-!
# A pose map takes a root's zero to a zero of another system

Two systems `S`, `S'` of a solid (`Modules/Root/System.lean`) with the same mode, number of
contacts and vertices, and a pose map `P` (`Modules/Root/PoseMap.lean`) that sends every contact
`i` of `S` to the contact `σ i` of `S'` (`Corr`: the hole edge's ends by the hole isometry, swapped
if `fl i`, the plug vertex by the plug isometry, in centred mode possibly all to the antipodes).
Then the image `z'` of a zero `z` of `S` (`imageP`: its coordinates the quotients of `coordE`) is
a zero of `S'` with the same scale (`zero_transport`):

* the slacks: `slack'_{σ i}(z') = ε_i factor · slack_i(z)` (`slackR_corr`, from
  `PoseMap.slackR_map`);
* the stationarity, with the multipliers `m'_{σ i} = ε_i m_i / factor`: along the line of each
  variable `v` through `z'`, the inverse map gives a curve through `z` on which
  `slack_i = ε_i factor⁻¹ · slack'_{σ i}` (`slackR_corr` for `P.inv`), and the chain rule
  (`stat_of_pullback`, `Modules/Root/Chain.lean`) turns the stationarity at `z` into that at `z'`.
-/

open Matrix Finset Filter
open Nieuwland.Check (Expr)

namespace Nieuwland.Root

/-! ### Contacts that correspond -/

/-- Contact `c` goes to contact `c'` under `P` (module docs). -/
def Corr (P : PoseMap) (vert : ℕ → Fin 3 → ℝ) (c c' : ℕ × ℕ × ℕ) (fl an : Bool) : Prop :=
  P.T *ᵥ vert c.1 + P.b = (if an then -1 else 1 : ℝ) • vert (if fl then c'.2.1 else c'.1) ∧
  P.T *ᵥ vert c.2.1 + P.b = (if an then -1 else 1 : ℝ) • vert (if fl then c'.1 else c'.2.1) ∧
  P.G *ᵥ vert c.2.2 + P.c = (if an then -1 else 1 : ℝ) • vert c'.2.2

/-- The sign of a contact's slack under a pose map: `-1` for a swapped edge. -/
def flipSign (fl : Bool) : ℝ := if fl then -1 else 1

theorem flipSign_mul_self (fl : Bool) : flipSign fl * flipSign fl = 1 := by
  cases fl <;> norm_num [flipSign]

theorem eq_smul_of_eq_smul {X A : Fin 3 → ℝ} {an : Bool}
    (h : X = (if an then -1 else 1 : ℝ) • A) : A = (if an then -1 else 1 : ℝ) • X := by
  cases an <;> simp_all

/-- **The slack of corresponding contacts.** -/
theorem slackR_corr {P : PoseMap} (hP : P.Valid) {s t : ℝ} {x : Fin 3 → ℝ}
    (hw : P.wv s t P.a' ≠ 0) (hq : P.qq s t x P.k' ≠ 0) {vert : ℕ → Fin 3 → ℝ}
    {c c' : ℕ × ℕ × ℕ} {fl an : Bool} (h : Corr P vert c c' fl an) (y : Fin 2 → ℝ) (l : ℝ)
    (han : an = true → y = 0 ∧ P.b = 0 ∧ P.c = 0) :
    slackR P.a' P.k' (P.s' s t) (P.t' s t) (P.x' s t x) (P.y' s t x y l) l (vert c'.1)
        (vert c'.2.1) (vert c'.2.2) =
      flipSign fl * P.factor s t x *
        slackR P.a P.k s t x y l (vert c.1) (vert c.2.1) (vert c.2.2) := by
  obtain ⟨h1, h2, h3⟩ := h
  have h1' := eq_smul_of_eq_smul h1
  have h2' := eq_smul_of_eq_smul h2
  have h3' := eq_smul_of_eq_smul h3
  have key := PoseMap.slackR_map hP hw hq (vert c.1) (vert c.2.1) (vert c.2.2) y l
  cases an
  · simp only [Bool.false_eq_true, ↓reduceIte, one_smul] at h1' h2' h3'
    cases fl
    · simp only [Bool.false_eq_true, ↓reduceIte] at h1' h2'
      rw [h1', h2', h3', key, flipSign]
      simp
    · simp only [↓reduceIte] at h1' h2'
      rw [h1', h2', h3', slackR_swap, key, flipSign]
      simp
  · obtain ⟨rfl, hb, hc⟩ := han rfl
    simp only [↓reduceIte, neg_one_smul] at h1' h2' h3'
    rw [P.y'_zero hb hc l] at key ⊢
    cases fl
    · simp only [Bool.false_eq_true, ↓reduceIte] at h1' h2'
      rw [h1', h2', h3', slackR_neg, key, flipSign]
      simp
    · simp only [↓reduceIte] at h1' h2'
      rw [h1', h2', h3', slackR_swap, slackR_neg, key, flipSign]
      simp

/-- An inverse sends the image back, signs kept. -/
theorem back_of_eq {M M' : Matrix (Fin 3) (Fin 3) ℝ} {b b' A A' : Fin 3 → ℝ} {an : Bool}
    (hinv : M' *ᵥ (M *ᵥ A + b) + b' = A) (hb' : an = true → b' = 0)
    (h : M *ᵥ A + b = (if an then -1 else 1 : ℝ) • A') :
    M' *ᵥ A' + b' = (if an then -1 else 1 : ℝ) • A := by
  have h' := eq_smul_of_eq_smul h
  cases an
  · simp only [Bool.false_eq_true, ↓reduceIte, one_smul] at h' ⊢
    rw [h', hinv]
  · have hb0 := hb' rfl
    simp only [↓reduceIte, neg_one_smul] at h' ⊢
    rw [hb0, add_zero] at hinv
    rw [h', mulVec_neg, hinv, hb0, add_zero]

/-- The inverse map sends corresponding contacts back. -/
theorem Corr.inv {P : PoseMap} (hP : P.Valid) {vert : ℕ → Fin 3 → ℝ} {c c' : ℕ × ℕ × ℕ}
    {fl an : Bool} (h : Corr P vert c c' fl an) (hb : an = true → P.b = 0 ∧ P.c = 0) :
    Corr P.inv vert c' c fl an := by
  obtain ⟨h1, h2, h3⟩ := h
  have hib : an = true → P.inv.b = 0 := fun ha ↦ by simp [PoseMap.inv_b, (hb ha).1]
  have hic : an = true → P.inv.c = 0 := fun ha ↦ by simp [PoseMap.inv_c, (hb ha).2]
  have e1 := back_of_eq (PoseMap.inv_hole hP _) hib h1
  have e2 := back_of_eq (PoseMap.inv_hole hP _) hib h2
  have e3 := back_of_eq (PoseMap.inv_plug hP _) hic h3
  cases fl
  · simp only [Bool.false_eq_true, ↓reduceIte] at e1 e2 ⊢
    exact ⟨e1, e2, e3⟩
  · simp only [↓reduceIte] at e1 e2 ⊢
    exact ⟨e2, e1, e3⟩

/-! ### Points with the map's data -/

/-- The point `w` with the variables from `o` on replaced by the list `cst`. -/
def withC (w : ℕ → ℝ) (o : ℕ) (cst : List ℝ) : ℕ → ℝ :=
  fun i ↦ if i < o then w i else cst.getD (i - o) 0

theorem withC_lt {w : ℕ → ℝ} {o : ℕ} {cst : List ℝ} {i : ℕ} (h : i < o) :
    withC w o cst i = w i := ite_eq_left h

theorem withC_line {w : ℕ → ℝ} {o : ℕ} {cst : List ℝ} {v : ℕ} (hv : v < o) (r : ℝ) :
    withC (line w v r) o cst = line (withC w o cst) v r := by
  funext i
  by_cases hiv : i = v
  · subst hiv
    simp [withC, line, hv]
  · by_cases hi : i < o <;> simp [withC, line, hiv, hi]

theorem yOf_withC {w : ℕ → ℝ} {o : ℕ} {cst : List ℝ} {cen : Bool} (h : nx cen < o) :
    yOf (withC w o cst) cen = yOf w cen := by
  funext c
  cases cen
  · have h5 : 5 < o := by simp [nx] at h; omega
    have h6 : 6 < o := by simp [nx] at h; omega
    fin_cases c <;> simp [yOf, yE, withC_lt h5, withC_lt h6]
  · simp [yOf, yE]

/-- The data of a pose map as a list (`d_b = d_c = 1`). -/
noncomputable def cstOf (P : PoseMap) : List ℝ :=
  [P.τ 0, P.τ 1, P.τ 2, P.τ 3, P.b 0, P.b 1, P.b 2, 1, P.γ 0, P.γ 1, P.γ 2, P.γ 3,
    P.c 0, P.c 1, P.c 2, 1]

theorem holds_cstOf {D : MapD} {P : PoseMap} (ha : P.a = D.a) (hk : P.k = D.k)
    (ha' : P.a' = D.a') (hk' : P.k' = D.k') (hs : P.sT = D.sT) (he : P.e = D.e)
    (w : ℕ → ℝ) (o : ℕ) : Holds D P (withC w o (cstOf P)) o where
  a := ha
  k := hk
  a' := ha'
  k' := hk'
  sT := hs
  e := he
  τ := by funext j; fin_cases j <;> simp [τE, withC, cstOf]
  b := by funext j; fin_cases j <;> simp [bE, dbE, withC, cstOf]
  db := by simp [dbE, withC, cstOf]
  γ := by funext j; fin_cases j <;> simp [γE, withC, cstOf]
  c := by funext j; fin_cases j <;> simp [cE, dcE, withC, cstOf]
  dc := by simp [dcE, withC, cstOf]

/-! ### The image -/

/-- The numerator and denominator of coordinate `j` of the image: the view and rotation
coordinates, the translation, the scale, and the multiplier of target contact `j'`, with `src j'`
the source contact and `fl` its flip. -/
def coordE (D : MapD) (o : ℕ) (src : ℕ → ℕ) (fl : ℕ → Bool) (j : ℕ) : Expr × Expr :=
  if j = 0 then (WE D o (D.a' + 1), WE D o D.a')
  else if j = 1 then (WE D o (D.a' + 2), WE D o D.a')
  else if j < 5 then
    (QQE D o (D.k'.succAbove ⟨(j - 2) % 3, Nat.mod_lt _ (by norm_num)⟩), QQE D o D.k')
  else if j < nx D.cen then (yNE D o ⟨(j - 5) % 2, Nat.mod_lt _ (by norm_num)⟩, yDE D o)
  else if j = nx D.cen then (lE D.cen, .const 1)
  else
    (.const (if fl (src (j - nx D.cen - 1)) then -1 else 1) * mE D.cen (src (j - nx D.cen - 1)) *
      fDE D o, fNE D o)

/-- The quotient of coordinate `j` at `ζ`. -/
noncomputable def coordV (D : MapD) (o : ℕ) (src : ℕ → ℕ) (fl : ℕ → Bool) (ζ : ℕ → ℝ)
    (j : ℕ) : ℝ :=
  (coordE D o src fl j).1.eval ζ / (coordE D o src fl j).2.eval ζ

/-- The image of `z`: the quotients at `z` with the map's data `cst` below `o`, `z` from `o` on. -/
noncomputable def imageP (D : MapD) (o : ℕ) (src : ℕ → ℕ) (fl : ℕ → Bool) (cst : List ℝ)
    (z : ℕ → ℝ) : ℕ → ℝ :=
  fun j ↦ if j < o then coordV D o src fl (withC z o cst) j else z j

/-- The hypotheses of the transport (module docs): two systems, a valid pose map with its data
`cst` at `z`, contacts that correspond under the permutation `σ` (inverse `src`), and the new view
and rotation charts defined at `z`. -/
structure LinkHyp (S S' : Sys) (D : MapD) (P : PoseMap) (σ src : ℕ → ℕ) (fl an : ℕ → Bool)
    (z : ℕ → ℝ) (cst : List ℝ) : Prop where
  valid : P.Valid
  cen : S.cen = D.cen
  cen' : S'.cen = D.cen
  view : S.view = D.a
  rot : S.rot = D.k
  view' : S'.view = D.a'
  rot' : S'.rot = D.k'
  k : S'.k = S.k
  V : S'.V = S.V
  perm : ∀ i < S.k, σ i < S.k ∧ src (σ i) = i
  perm' : ∀ j < S.k, src j < S.k ∧ σ (src j) = j
  cb : D.cen = true → P.b = 0 ∧ P.c = 0
  anti : ∀ i < S.k, an i = true → D.cen = true
  vert : ∀ w : ℕ → ℝ, (∀ u, S.n ≤ u → w u = z u) → ∀ v, vertOf w S.V v = vertOf z S.V v
  corr : ∀ i < S.k, Corr P (vertOf z S.V) (S.con i) (S'.con (σ i)) (fl i) (an i)
  holds : Holds D P (withC z S.n cst) S.n
  hw : P.wv (z 0) (z 1) P.a' ≠ 0
  hq : P.qq (z 0) (z 1) ![z 2, z 3, z 4] P.k' ≠ 0

theorem five_le_nx (cen : Bool) : 5 ≤ nx cen := by
  unfold nx
  split <;> omega

theorem yOf_true (z : ℕ → ℝ) : yOf z true = 0 := by
  funext c
  simp [yOf, yE]

theorem imageP_lt {D : MapD} {o : ℕ} {src : ℕ → ℕ} {fl : ℕ → Bool} {cst : List ℝ} {z : ℕ → ℝ}
    {j : ℕ} (hj : j < o) : imageP D o src fl cst z j = coordV D o src fl (withC z o cst) j :=
  ite_eq_left hj

theorem imageP_ge {D : MapD} {o : ℕ} {src : ℕ → ℕ} {fl : ℕ → Bool} {cst : List ℝ} {z : ℕ → ℝ}
    {u : ℕ} (hu : o ≤ u) : imageP D o src fl cst z u = z u :=
  ite_eq_right (by omega)

/-- The map's facts at a point `w` with its data from `o` on, in terms of `w`. -/
theorem holds_w {D : MapD} {Q : PoseMap} {w : ℕ → ℝ} {o : ℕ} {cst : List ℝ}
    (h : Holds D Q (withC w o cst) o) (ho : nx D.cen < o) :
    Q.wv (w 0) (w 1) Q.a' = (WE D o D.a').eval (withC w o cst) ∧
      Q.qq (w 0) (w 1) ![w 2, w 3, w 4] Q.k' = (QQE D o D.k').eval (withC w o cst) ∧
      Q.s' (w 0) (w 1) = (WE D o (D.a' + 1)).eval (withC w o cst) /
        (WE D o D.a').eval (withC w o cst) ∧
      Q.t' (w 0) (w 1) = (WE D o (D.a' + 2)).eval (withC w o cst) /
        (WE D o D.a').eval (withC w o cst) ∧
      (∀ i, Q.x' (w 0) (w 1) ![w 2, w 3, w 4] i =
        (QQE D o (D.k'.succAbove i)).eval (withC w o cst) /
          (QQE D o D.k').eval (withC w o cst)) ∧
      (Q.Valid → Q.wv (w 0) (w 1) Q.a' ≠ 0 → Q.qq (w 0) (w 1) ![w 2, w 3, w 4] Q.k' ≠ 0 →
        (∀ c, Q.y' (w 0) (w 1) ![w 2, w 3, w 4] (yOf w D.cen) (w (nx D.cen)) c =
          (yNE D o c).eval (withC w o cst) / (yDE D o).eval (withC w o cst)) ∧
        (yDE D o).eval (withC w o cst) ≠ 0 ∧
        Q.factor (w 0) (w 1) ![w 2, w 3, w 4] =
          (fNE D o).eval (withC w o cst) / (fDE D o).eval (withC w o cst) ∧
        (fDE D o).eval (withC w o cst) ≠ 0) := by
  have hlt : ∀ i, i ≤ nx D.cen → withC w o cst i = w i := fun i hi ↦
    withC_lt (lt_of_le_of_lt hi ho)
  have h5 := five_le_nx D.cen
  have e0 := hlt 0 (by omega)
  have e1 := hlt 1 (by omega)
  have e2 := hlt 2 (by omega)
  have e3 := hlt 3 (by omega)
  have e4 := hlt 4 (by omega)
  have el := hlt (nx D.cen) le_rfl
  have ey : yOf (withC w o cst) D.cen = yOf w D.cen := yOf_withC ho
  have hW := congrFun h.evalV_WE Q.a'
  have hQ := congrFun h.evalV_QQE Q.k'
  have hs := h.s'_eq
  have ht := h.t'_eq
  have hx := h.x'_eq
  rw [e0, e1] at hW hs ht
  simp only [e0, e1, e2, e3, e4] at hQ hx
  rw [evalV_apply, h.a'] at hW
  rw [evalV_apply, h.k'] at hQ
  refine ⟨by rw [h.a']; exact hW.symm, by rw [h.k']; exact hQ.symm, hs, ht, hx, fun hP hw hq ↦ ?_⟩
  rw [← e0, ← e1] at hw
  rw [← e0, ← e1, ← e2, ← e3, ← e4] at hq
  have hy := h.y'_eq hw hq hP.1
  have hf := h.factor_eq hP hw hq
  simp only [e0, e1, e2, e3, e4] at hf
  simp only [e0, e1, e2, e3, e4, el, ey] at hy
  exact ⟨hy, h.yD_ne hw hq hP.1, hf, h.fD_ne hw hq hP.1⟩

/-- The discrete data of the inverse map. -/
def MapD.inv (D : MapD) : MapD := ⟨D.a', D.k', D.a, D.k, D.sT, D.e, D.cen⟩

/-! ### The inverse map along lines -/

/-- The pose coordinates of `Q` at `w`. -/
noncomputable def psi (Q : PoseMap) (cen : Bool) (w : ℕ → ℝ) (u : ℕ) : ℝ :=
  if u = 0 then Q.s' (w 0) (w 1) else if u = 1 then Q.t' (w 0) (w 1)
  else if u < 5 then Q.x' (w 0) (w 1) ![w 2, w 3, w 4] ⟨(u - 2) % 3, Nat.mod_lt _ (by norm_num)⟩
  else Q.y' (w 0) (w 1) ![w 2, w 3, w 4] (yOf w cen) (w (nx cen))
    ⟨(u - 5) % 2, Nat.mod_lt _ (by norm_num)⟩

/-- `Q`'s image of `w`: its pose coordinates, the scale of `w`, the rest of `z`. -/
noncomputable def psiP (Q : PoseMap) (cen : Bool) (z w : ℕ → ℝ) : ℕ → ℝ :=
  fun u ↦ if u < nx cen then psi Q cen w u else if u = nx cen then w u else z u

section PsiP

variable {Q : PoseMap} {cen : Bool} {z w : ℕ → ℝ}

theorem psiP_pose :
    psiP Q cen z w 0 = Q.s' (w 0) (w 1) ∧ psiP Q cen z w 1 = Q.t' (w 0) (w 1) ∧
      ![psiP Q cen z w 2, psiP Q cen z w 3, psiP Q cen z w 4] =
        Q.x' (w 0) (w 1) ![w 2, w 3, w 4] := by
  have h5 := five_le_nx cen
  refine ⟨by simp [psiP, psi, show 0 < nx cen by omega], by
    simp [psiP, psi, show 1 < nx cen by omega], ?_⟩
  funext i
  fin_cases i <;> simp [psiP, psi, show 2 < nx cen by omega, show 3 < nx cen by omega,
    show 4 < nx cen by omega]

theorem psiP_l : psiP Q cen z w (nx cen) = w (nx cen) := by
  simp [psiP]

theorem psiP_gt {u : ℕ} (hu : nx cen < u) : psiP Q cen z w u = z u := by
  simp [psiP, show ¬u < nx cen by omega, show u ≠ nx cen by omega]

theorem psiP_y (hy : cen = true → Q.y' (w 0) (w 1) ![w 2, w 3, w 4] (yOf w cen) (w (nx cen)) = 0) :
    yOf (psiP Q cen z w) cen = Q.y' (w 0) (w 1) ![w 2, w 3, w 4] (yOf w cen) (w (nx cen)) := by
  rcases Bool.eq_false_or_eq_true cen with hc | hc
  · rw [hy hc, hc, yOf_true]
  · subst hc
    funext c
    fin_cases c <;> simp [yOf, yE, psiP, psi, nx]

end PsiP

/-- The derivative of a quotient of expressions along a line. -/
theorem differentiableAt_quot (N D : Expr) (ζ : ℕ → ℝ) (v : ℕ) (hD : D.eval ζ ≠ 0) :
    DifferentiableAt ℝ (fun r ↦ N.eval (line ζ v r) / D.eval (line ζ v r)) 0 :=
  (HasDerivAt.div (hasDerivAt_eval_line ζ v N) (hasDerivAt_eval_line ζ v D)
    (by rwa [line_zero])).differentiableAt

/-- An expression that does not vanish at `ζ` does not vanish near `ζ` on a line. -/
theorem eventually_eval_line_ne (e : Expr) (ζ : ℕ → ℝ) (v : ℕ) (h : e.eval ζ ≠ 0) :
    ∀ᶠ r in nhds (0 : ℝ), e.eval (line ζ v r) ≠ 0 :=
  (hasDerivAt_eval_line ζ v e).continuousAt.eventually_ne (by rwa [line_zero])

namespace LinkHyp

variable {S S' : Sys} {D : MapD} {P : PoseMap} {σ src : ℕ → ℕ} {fl an : ℕ → Bool}
  {z : ℕ → ℝ} {cst : List ℝ} (H : LinkHyp S S' D P σ src fl an z cst)
include H

theorem n_eq : S.n = nx D.cen + 1 + S.k := by
  simp only [Sys.n, Sys.nv, H.cen]

theorem n_eq' : S'.n = S.n := by
  simp only [Sys.n, Sys.nv, H.cen, H.cen', H.k]

theorem nx_lt : nx D.cen < S.n := by
  rw [H.n_eq]
  omega

/-- The facts of the map at `z`, in terms of `z`. -/
theorem holds_at :
    P.s' (z 0) (z 1) = (WE D S.n (D.a' + 1)).eval (withC z S.n cst) /
        (WE D S.n D.a').eval (withC z S.n cst) ∧
      P.t' (z 0) (z 1) = (WE D S.n (D.a' + 2)).eval (withC z S.n cst) /
        (WE D S.n D.a').eval (withC z S.n cst) ∧
      (∀ i, P.x' (z 0) (z 1) ![z 2, z 3, z 4] i =
        (QQE D S.n (D.k'.succAbove i)).eval (withC z S.n cst) /
          (QQE D S.n D.k').eval (withC z S.n cst)) ∧
      (∀ c, P.y' (z 0) (z 1) ![z 2, z 3, z 4] (yOf z D.cen) (z (nx D.cen)) c =
        (yNE D S.n c).eval (withC z S.n cst) / (yDE D S.n).eval (withC z S.n cst)) ∧
      P.factor (z 0) (z 1) ![z 2, z 3, z 4] =
        (fNE D S.n).eval (withC z S.n cst) / (fDE D S.n).eval (withC z S.n cst) := by
  obtain ⟨_, _, hs, ht, hx, hr⟩ := holds_w H.holds H.nx_lt
  obtain ⟨hy, _, hf, _⟩ := hr H.valid H.hw H.hq
  exact ⟨hs, ht, hx, hy, hf⟩

theorem img0 : imageP D S.n src fl cst z 0 = P.s' (z 0) (z 1) := by
  have := five_le_nx D.cen
  rw [imageP_lt (by have := H.nx_lt; omega), coordV, coordE, ite_eq_left rfl, H.holds_at.1]

theorem img1 : imageP D S.n src fl cst z 1 = P.t' (z 0) (z 1) := by
  have := five_le_nx D.cen
  rw [imageP_lt (by have := H.nx_lt; omega), coordV, coordE, ite_eq_right (by omega), ite_eq_left rfl,
    H.holds_at.2.1]

theorem imgx : ![imageP D S.n src fl cst z 2, imageP D S.n src fl cst z 3,
    imageP D S.n src fl cst z 4] = P.x' (z 0) (z 1) ![z 2, z 3, z 4] := by
  have := five_le_nx D.cen
  have hn := H.nx_lt
  funext i
  rw [H.holds_at.2.2.1]
  fin_cases i <;>
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
    rw [imageP_lt (by omega), coordV, coordE, ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left (by omega)]
    rfl

theorem imgl : imageP D S.n src fl cst z (nx D.cen) = z (nx D.cen) := by
  have := five_le_nx D.cen
  rw [imageP_lt H.nx_lt, coordV, coordE, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_left rfl]
  simp [lE, withC_lt H.nx_lt]

theorem imgy : yOf (imageP D S.n src fl cst z) D.cen =
    P.y' (z 0) (z 1) ![z 2, z 3, z 4] (yOf z D.cen) (z (nx D.cen)) := by
  have hn := H.nx_lt
  rcases Bool.eq_false_or_eq_true D.cen with hc | hc
  · obtain ⟨hb, hcc⟩ := H.cb hc
    rw [hc, yOf_true, yOf_true, P.y'_zero hb hcc]
  · funext c
    have h7 : nx D.cen = 7 := by simp [nx, hc]
    rw [H.holds_at.2.2.2.1]
    fin_cases c <;>
    · simp only [yOf, yE, hc, Bool.false_eq_true, ↓reduceIte, Expr.eval_var, Fin.zero_eta,
        Fin.isValue, Fin.mk_one]
      rw [imageP_lt (by omega), coordV, coordE, ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_left (by omega)]
      rfl

theorem imgm {i : ℕ} (hi : i < S.k) :
    imageP D S.n src fl cst z (nx D.cen + 1 + σ i) =
      flipSign (fl i) * z (nx D.cen + 1 + i) / P.factor (z 0) (z 1) ![z 2, z 3, z 4] := by
  have := five_le_nx D.cen
  have hn := H.n_eq
  obtain ⟨hσ, hs⟩ := H.perm i hi
  have hf0 := PoseMap.factor_ne_zero H.valid H.hw H.hq
  rw [H.holds_at.2.2.2.2] at hf0 ⊢
  have hD : (fDE D S.n).eval (withC z S.n cst) ≠ 0 := fun h0 ↦ hf0 (by rw [h0, div_zero])
  have hN : (fNE D S.n).eval (withC z S.n cst) ≠ 0 := fun h0 ↦ hf0 (by rw [h0, zero_div])
  rw [imageP_lt (by omega), coordV, coordE, ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  simp only [show nx D.cen + 1 + σ i - nx D.cen - 1 = σ i by omega, hs]
  simp only [Expr.eval_mul, Expr.eval_const, mE, Expr.eval_var,
    withC_lt (show nx D.cen + 1 + i < S.n by omega), flipSign]
  field_simp
  split <;> simp

theorem vert_img (v : ℕ) : vertOf (imageP D S.n src fl cst z) S.V v = vertOf z S.V v :=
  H.vert _ (fun _ hu ↦ imageP_ge hu) v

/-- **The slacks at the image.** -/
theorem slack_img {i : ℕ} (hi : i < S.k) :
    (S'.g (σ i)).eval (imageP D S.n src fl cst z) =
      flipSign (fl i) * P.factor (z 0) (z 1) ![z 2, z 3, z 4] * (S.g i).eval z := by
  have hy0 : an i = true → yOf z D.cen = 0 ∧ P.b = 0 ∧ P.c = 0 := fun ha ↦ by
    have hc := H.anti i hi ha
    exact ⟨by rw [hc, yOf_true], H.cb hc⟩
  have key := slackR_corr H.valid H.hw H.hq (H.corr i hi) (yOf z D.cen) (z (nx D.cen)) hy0
  simp only [Sys.g, Sys.slack, eval_slackE_eq_slackR, H.cen, H.cen', H.view, H.rot, H.view',
    H.rot', H.V, lE, Expr.eval_var, vert_img H, ← H.holds.a, ← H.holds.k, ← H.holds.a',
    ← H.holds.k']
  rw [H.img0, H.img1, H.imgx, H.imgy, H.imgl, key]

/-- The inverse map's data. -/
theorem holds_inv (w : ℕ → ℝ) : Holds D.inv P.inv (withC w S.n (cstOf P.inv)) S.n :=
  holds_cstOf (by simpa [MapD.inv] using H.holds.a') (by simpa [MapD.inv] using H.holds.k')
    (by simpa [MapD.inv] using H.holds.a) (by simpa [MapD.inv] using H.holds.k)
    (by simpa [MapD.inv] using H.holds.sT) (by simpa [MapD.inv] using H.holds.e) w S.n

/-- **The slacks at the inverse's image** of a point `w` that agrees with `z` from `S.n` on. -/
theorem slack_psi {i : ℕ} (hi : i < S.k) {w : ℕ → ℝ}
    (hw : P.inv.wv (w 0) (w 1) P.inv.a' ≠ 0) (hq : P.inv.qq (w 0) (w 1) ![w 2, w 3, w 4] P.inv.k' ≠ 0)
    (hwz : ∀ u, S.n ≤ u → w u = z u) :
    (S.g i).eval (psiP P.inv D.cen z w) =
      flipSign (fl i) * P.inv.factor (w 0) (w 1) ![w 2, w 3, w 4] * (S'.g (σ i)).eval w := by
  have hbc : an i = true → P.b = 0 ∧ P.c = 0 := fun ha ↦ H.cb (H.anti i hi ha)
  have hy0 : an i = true → yOf w D.cen = 0 ∧ P.inv.b = 0 ∧ P.inv.c = 0 := fun ha ↦ by
    have hc := H.anti i hi ha
    obtain ⟨hb, hcc⟩ := H.cb hc
    exact ⟨by rw [hc, yOf_true], by simp [hb], by simp [hcc]⟩
  have key := slackR_corr (PoseMap.inv_valid H.valid) hw hq ((H.corr i hi).inv H.valid hbc)
    (yOf w D.cen) (w (nx D.cen)) hy0
  have hyp : D.cen = true →
      P.inv.y' (w 0) (w 1) ![w 2, w 3, w 4] (yOf w D.cen) (w (nx D.cen)) = 0 := fun hc ↦ by
    obtain ⟨hb, hcc⟩ := H.cb hc
    rw [hc, yOf_true]
    exact P.inv.y'_zero (by simp [hb]) (by simp [hcc]) _
  have hv1 : ∀ v, vertOf (psiP P.inv D.cen z w) S.V v = vertOf z S.V v :=
    H.vert _ fun u hu ↦ psiP_gt (by have := H.nx_lt; omega)
  have hv2 : ∀ v, vertOf w S.V v = vertOf z S.V v := H.vert _ hwz
  obtain ⟨p0, p1, px⟩ := psiP_pose (Q := P.inv) (cen := D.cen) (z := z) (w := w)
  simp only [Sys.g, Sys.slack, eval_slackE_eq_slackR, H.cen, H.cen', H.view, H.rot, H.view',
    H.rot', H.V, lE, Expr.eval_var, hv1, hv2, ← H.holds.a, ← H.holds.k, ← H.holds.a',
    ← H.holds.k', p0, p1, px, psiP_y hyp, psiP_l]
  simpa using key

/-- **The stationarity at the image.** -/
theorem stat_img (hg : ∀ i < S.k, (S.g i).eval z = 0)
    (hst : ∀ v < S.nv, ∑ i ∈ range S.k, (mE S.cen i).eval z * (deriv v (S.g i)).eval z =
      ((if v = nx S.cen then 1 else 0 : ℤ) : ℝ))
    {v : ℕ} (hv : v < S'.nv) :
    ∑ j ∈ range S'.k, (mE S'.cen j).eval (imageP D S.n src fl cst z) *
        (deriv v (S'.g j)).eval (imageP D S.n src fl cst z) =
      ((if v = nx S'.cen then 1 else 0 : ℤ) : ℝ) := by
  set z' := imageP D S.n src fl cst z with hz'
  have hn := H.n_eq
  have h5 := five_le_nx D.cen
  have hvx : v < nx D.cen + 1 := by simpa [Sys.nv, H.cen'] using hv
  have hvn : v < S.n := by omega
  have ho := H.nx_lt
  have hP := H.valid
  have hPi := PoseMap.inv_valid hP
  have hzero : ∀ i < S.k, (S'.g (σ i)).eval z' = 0 := fun i hi ↦ by
    rw [hz', H.slack_img hi, hg i hi, mul_zero]
  -- the point `z'` and its inverse
  have i0 := H.img0
  have i1 := H.img1
  have ix := H.imgx
  have iy := H.imgy
  have il := H.imgl
  rw [← hz'] at i0 i1 ix iy il
  have hwz' : P.inv.wv (z' 0) (z' 1) P.inv.a' ≠ 0 := by
    rw [i0, i1, PoseMap.inv_a']
    exact PoseMap.inv_wv_ne hP H.hw
  have hqz' : P.inv.qq (z' 0) (z' 1) ![z' 2, z' 3, z' 4] P.inv.k' ≠ 0 := by
    rw [i0, i1, ix, PoseMap.inv_k']
    exact PoseMap.inv_qq_ne hP H.hw H.hq
  set ζ' := withC z' S.n (cstOf P.inv) with hζ'
  have hline : ∀ r, withC (line z' v r) S.n (cstOf P.inv) = line ζ' v r :=
    fun r ↦ withC_line hvn r
  obtain ⟨hW0, hQ0, -, -, -, hR0⟩ := holds_w (H.holds_inv z') ho
  obtain ⟨-, hyD0, -, hfD0⟩ := hR0 hPi hwz' hqz'
  rw [hW0] at hwz'
  rw [hQ0] at hqz'
  -- along the line
  have hW : ∀ r, P.inv.wv (line z' v r 0) (line z' v r 1) P.inv.a' =
      (WE D.inv S.n D.inv.a').eval (line ζ' v r) := fun r ↦ by
    rw [(holds_w (H.holds_inv (line z' v r)) ho).1, hline]
  have hQ : ∀ r, P.inv.qq (line z' v r 0) (line z' v r 1)
      ![line z' v r 2, line z' v r 3, line z' v r 4] P.inv.k' =
      (QQE D.inv S.n D.inv.k').eval (line ζ' v r) := fun r ↦ by
    rw [(holds_w (H.holds_inv (line z' v r)) ho).2.1, hline]
  have evw : ∀ᶠ r in nhds (0 : ℝ), P.inv.wv (line z' v r 0) (line z' v r 1) P.inv.a' ≠ 0 := by
    filter_upwards [eventually_eval_line_ne _ ζ' v hwz'] with r hr
    rwa [hW]
  have evq : ∀ᶠ r in nhds (0 : ℝ), P.inv.qq (line z' v r 0) (line z' v r 1)
      ![line z' v r 2, line z' v r 3, line z' v r 4] P.inv.k' ≠ 0 := by
    filter_upwards [eventually_eval_line_ne _ ζ' v hqz'] with r hr
    rwa [hQ]
  have hlz : ∀ r u, S.n ≤ u → line z' v r u = z u := fun r u hu ↦ by
    simp only [line, Function.update_apply, show u ≠ v by omega, ↓reduceIte, hz',
      imageP_ge hu]
  -- the curve and the factors
  set γ : ℝ → ℕ → ℝ := fun r ↦ psiP P.inv D.cen z (line z' v r) with hγ
  set c : ℕ → ℝ → ℝ := fun i r ↦ flipSign (fl i) *
    P.inv.factor (line z' v r 0) (line z' v r 1) ![line z' v r 2, line z' v r 3, line z' v r 4]
    with hc
  have hpull : ∀ i < S.k, ∀ᶠ r in nhds (0 : ℝ),
      (S.g i).eval (γ r) = c i r * (S'.g (σ i)).eval (line z' v r) := fun i hi ↦ by
    filter_upwards [evw, evq] with r hwr hqr
    exact H.slack_psi hi hwr hqr (hlz r)
  have hfac : (fun r ↦ P.inv.factor (line z' v r 0) (line z' v r 1)
      ![line z' v r 2, line z' v r 3, line z' v r 4]) =ᶠ[nhds 0]
      fun r ↦ (fNE D.inv S.n).eval (line ζ' v r) / (fDE D.inv S.n).eval (line ζ' v r) := by
    filter_upwards [evw, evq] with r hwr hqr
    rw [((holds_w (H.holds_inv (line z' v r)) ho).2.2.2.2.2 hPi hwr hqr).2.2.1, hline]
  have hcd : ∀ i < S.k, HasDerivAt (c i) (_root_.deriv (c i) 0) 0 := fun i _ ↦
    (((differentiableAt_quot _ _ ζ' v hfD0).congr_of_eventuallyEq hfac).const_mul
      (flipSign (fl i))).hasDerivAt
  -- the pose coordinates of the curve are differentiable
  have hdiff : ∀ u < nx D.cen, DifferentiableAt ℝ (fun r ↦ γ r u) 0 := by
    intro u hu
    have e : ∀ r, γ r u = psi P.inv D.cen (line z' v r) u := fun r ↦ by
      simp only [hγ, psiP, hu, ↓reduceIte]
    simp only [e]
    obtain ⟨-, -, hs, ht, hx, hr⟩ := holds_w (H.holds_inv z') ho
    by_cases h0 : u = 0
    · subst h0
      have : (fun r ↦ psi P.inv D.cen (line z' v r) 0) = fun r ↦
          (WE D.inv S.n (D.inv.a' + 1)).eval (line ζ' v r) /
            (WE D.inv S.n D.inv.a').eval (line ζ' v r) := by
        funext r
        rw [psi, ite_eq_left rfl, (holds_w (H.holds_inv (line z' v r)) ho).2.2.1, hline]
      rw [this]
      exact differentiableAt_quot _ _ ζ' v hwz'
    by_cases h1 : u = 1
    · subst h1
      have : (fun r ↦ psi P.inv D.cen (line z' v r) 1) = fun r ↦
          (WE D.inv S.n (D.inv.a' + 2)).eval (line ζ' v r) /
            (WE D.inv S.n D.inv.a').eval (line ζ' v r) := by
        funext r
        rw [psi, ite_eq_right h0, ite_eq_left rfl,
          (holds_w (H.holds_inv (line z' v r)) ho).2.2.2.1, hline]
      rw [this]
      exact differentiableAt_quot _ _ ζ' v hwz'
    by_cases h4 : u < 5
    · have : (fun r ↦ psi P.inv D.cen (line z' v r) u) = fun r ↦
          (QQE D.inv S.n (D.inv.k'.succAbove ⟨(u - 2) % 3, Nat.mod_lt _ (by norm_num)⟩)).eval
            (line ζ' v r) / (QQE D.inv S.n D.inv.k').eval (line ζ' v r) := by
        funext r
        rw [psi, ite_eq_right h0, ite_eq_right h1, ite_eq_left h4,
          (holds_w (H.holds_inv (line z' v r)) ho).2.2.2.2.1, hline]
      rw [this]
      exact differentiableAt_quot _ _ ζ' v hqz'
    · have hev : (fun r ↦ psi P.inv D.cen (line z' v r) u) =ᶠ[nhds 0] fun r ↦
          (yNE D.inv S.n ⟨(u - 5) % 2, Nat.mod_lt _ (by norm_num)⟩).eval (line ζ' v r) /
            (yDE D.inv S.n).eval (line ζ' v r) := by
        filter_upwards [evw, evq] with r hwr hqr
        have hy := ((holds_w (H.holds_inv (line z' v r)) ho).2.2.2.2.2 hPi hwr hqr).1
        rw [show D.inv.cen = D.cen from rfl, hline] at hy
        rw [psi, ite_eq_right h0, ite_eq_right h1, ite_eq_right h4, hy]
      exact (differentiableAt_quot _ _ ζ' v hyD0).congr_of_eventuallyEq hev
  -- the derivatives of the curve
  set γ' : ℕ → ℝ := fun u ↦ if u < nx D.cen then _root_.deriv (fun r ↦ γ r u) 0
    else if u = nx D.cen then (if u = v then 1 else 0) else 0 with hγ'
  set Sv : Finset ℕ := insert (nx D.cen) ((range S.k).biUnion fun i ↦ varsE (S.g i)) with hSv
  have hS : ∀ i < S.k, varsE (S.g i) ⊆ Sv := fun i hi ↦
    (Finset.subset_biUnion_of_mem (fun i ↦ varsE (S.g i)) (mem_range.mpr hi)).trans
      (Finset.subset_insert _ _)
  have hγd : ∀ u ∈ Sv, HasDerivAt (fun r ↦ γ r u) (γ' u) 0 := by
    intro u _
    by_cases hu : u < nx D.cen
    · simp only [hγ', hu, ↓reduceIte]
      exact (hdiff u hu).hasDerivAt
    by_cases hu' : u = nx D.cen
    · subst hu'
      have e : (fun r ↦ γ r (nx D.cen)) = fun r ↦ line z' v r (nx D.cen) := by
        funext r
        simp only [hγ, psiP_l]
      rw [e]
      simpa [hγ', hu] using hasDerivAt_line z' v (nx D.cen)
    · have e : (fun r ↦ γ r u) = fun _ ↦ z u := by
        funext r
        simp only [hγ, psiP_gt (show nx D.cen < u by omega)]
      rw [e]
      simpa [hγ', hu, hu'] using hasDerivAt_const (0 : ℝ) (z u)
  have hγ0 : γ 0 = z := by
    funext u
    simp only [hγ, line_zero]
    by_cases hu : u < nx D.cen
    · simp only [psiP, hu, ↓reduceIte, psi]
      have hs1 := PoseMap.inv_s' hP H.hw
      have ht1 := PoseMap.inv_t' hP H.hw
      have hx1 := PoseMap.inv_x' hP H.hw H.hq
      have hy1 := PoseMap.inv_y' hP H.hw H.hq (yOf z D.cen) (z (nx D.cen))
      rw [i0, i1, ix, iy, il]
      split_ifs with h0 h1 h4
      · rw [h0, hs1]
      · rw [h1, ht1]
      · rw [hx1]
        have : 2 ≤ u := by omega
        interval_cases u <;> rfl
      · rw [hy1]
        have : 5 ≤ u := by omega
        rcases Bool.eq_false_or_eq_true D.cen with hc | hc
        · simp [nx, hc] at hu
          omega
        · simp only [nx, hc, Bool.false_eq_true, ↓reduceIte] at hu
          interval_cases u <;> simp [yOf, yE, hc]
    by_cases hu' : u = nx D.cen
    · subst hu'
      rw [psiP_l, il]
    · rw [psiP_gt (by omega)]
  have hstat : ∀ u ∈ Sv, γ' u * ∑ i ∈ range S.k, (fun i ↦ z (nx D.cen + 1 + i)) i *
      (deriv u (S.g i)).eval z = γ' u * (if u = nx D.cen then 1 else 0) := by
    intro u _
    by_cases hu : u ≤ nx D.cen
    · have := hst u (by simp [Sys.nv, H.cen]; omega)
      simp only [mE, Expr.eval_var, H.cen] at this
      rw [this]
      push_cast
      rfl
    · simp [hγ', show ¬u < nx D.cen by omega, show u ≠ nx D.cen by omega]
  have key := stat_of_pullback hS hγ0 hγd hstat (Finset.mem_insert_self _ _) hcd hpull hzero
  -- conclude
  have hc0 : ∀ i, c i 0 = flipSign (fl i) / P.factor (z 0) (z 1) ![z 2, z 3, z 4] := fun i ↦ by
    have hf := PoseMap.factor_inv_mul hP H.hw H.hq
    have hf0 := PoseMap.factor_ne_zero hP H.hw H.hq
    simp only [hc, line_zero]
    rw [i0, i1, ix, eq_div_iff hf0, mul_assoc, hf, mul_one]
  have e1 : ∑ j ∈ range S'.k, (mE S'.cen j).eval z' * (deriv v (S'.g j)).eval z' =
      ∑ i ∈ range S.k, (mE D.cen (σ i)).eval z' * (deriv v (S'.g (σ i))).eval z' := by
    rw [H.k, H.cen']
    exact (Finset.sum_nbij' σ src (fun i hi ↦ mem_range.mpr (H.perm i (mem_range.mp hi)).1)
      (fun j hj ↦ mem_range.mpr (H.perm' j (mem_range.mp hj)).1)
      (fun i hi ↦ (H.perm i (mem_range.mp hi)).2) (fun j hj ↦ (H.perm' j (mem_range.mp hj)).2)
      (fun _ _ ↦ rfl)).symm
  rw [e1]
  have e2 : ∀ i ∈ range S.k, (mE D.cen (σ i)).eval z' * (deriv v (S'.g (σ i))).eval z' =
      c i 0 * z (nx D.cen + 1 + i) * (deriv v (S'.g (σ i))).eval z' := fun i hi ↦ by
    simp only [mE, Expr.eval_var]
    rw [hz', H.imgm (mem_range.mp hi), ← hz', hc0]
    ring
  rw [Finset.sum_congr rfl e2, key]
  simp only [hγ', lt_irrefl, ↓reduceIte, H.cen']
  by_cases hvn' : v = nx D.cen
  · subst hvn'
    simp
  · simp [hvn', Ne.symm hvn']

/-- **The transport of a zero** (module docs): the image of a zero of `S` is a zero of `S'`. -/
theorem zero_transport (hg : ∀ i < S.k, (S.g i).eval z = 0)
    (hst : ∀ v < S.nv, ∑ i ∈ range S.k, (mE S.cen i).eval z * (deriv v (S.g i)).eval z =
      ((if v = nx S.cen then 1 else 0 : ℤ) : ℝ)) :
    (∀ j < S'.k, (S'.g j).eval (imageP D S.n src fl cst z) = 0) ∧
      (∀ v < S'.nv, ∑ j ∈ range S'.k, (mE S'.cen j).eval (imageP D S.n src fl cst z) *
          (deriv v (S'.g j)).eval (imageP D S.n src fl cst z) =
        ((if v = nx S'.cen then 1 else 0 : ℤ) : ℝ)) := by
  refine ⟨fun j hj ↦ ?_, fun v hv ↦ H.stat_img hg hst hv⟩
  rw [H.k] at hj
  obtain ⟨hs, hσ⟩ := H.perm' j hj
  rw [← hσ, H.slack_img hs, hg _ hs, mul_zero]

end LinkHyp

end Nieuwland.Root
