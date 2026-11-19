import Modules.Root.Link
import Modules.Root.LinkData

/-!
# The check of links between roots, and its soundness

`linksOk pts R targets` checks links from the root `R` to each root `R'` of `targets` with its
link record (`Modules/Root/LinkData.lean`): the isometries of the frames, their data, the
contacts' correspondence, and that the pose map's image of `R`'s zero (`imageP`,
`Modules/Root/Link.lean`) lies in `R'`'s box, by balls at `R`'s zero (`quotIn`). The balls of the
map's data come from those of the field's basis values (`linkY`), as precise as the zero's.

`scale_eq_of_linksOk`: then every target root has the scale of `R`.
-/

open Matrix Finset
open Nieuwland.Check

namespace Nieuwland.Root

section Real

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

theorem toMatrix_smulM (a : κ) (G : M3 κ) : (smulM a G).toMatrix = Exact.re a • G.toMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [smulM, M3.toMatrix, V3.smul, V3.get, Exact.re_mul]

theorem toMatrix_quatM3 (q : Q4 κ) : (quatM3 q).toMatrix = quatMatrix (Exact.reQ q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatM3, M3.toMatrix, quatMatrix, Exact.reQ, Q4.map, Q4.toFun, V3.get, Exact.re_add,
      Exact.re_sub, Exact.re_mul, Exact.re_ofInt] <;> ring

namespace Iso

variable (I : Iso κ)

/-- The real linear part `M / d`. -/
noncomputable def Tr : Matrix (Fin 3) (Fin 3) ℝ := (Exact.re I.d)⁻¹ • I.M.toMatrix

/-- The real translation `b / d`. -/
noncomputable def br : Fin 3 → ℝ := (Exact.re I.d)⁻¹ • Exact.reV I.b

variable {I}

theorem d_ne (h : I.ok = true) : Exact.re I.d ≠ 0 := by
  simp only [ok, Bool.and_eq_true] at h
  have := Exact.pos_sound _ h.1.1.1
  rw [Exact.re_mul] at this
  exact fun h0 ↦ by rw [h0, mul_zero] at this; exact lt_irrefl _ this

theorem norm_pos (h : I.ok = true) : 0 < Exact.reQ I.q ⬝ᵥ Exact.reQ I.q := by
  simp only [ok, Bool.and_eq_true] at h
  have := Exact.pos_sound _ h.1.1.2
  rwa [Exact.re_norm2] at this

theorem s_eq (h : I.ok = true) : I.s = 1 ∨ I.s = -1 := by
  simp only [ok, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact h.1.2

theorem Tr_eq (h : I.ok = true) :
    I.Tr = ((I.s : ℝ) / (Exact.reQ I.q ⬝ᵥ Exact.reQ I.q)) • quatMatrix (Exact.reQ I.q) := by
  have hd := d_ne h
  have hn := (norm_pos h).ne'
  have hs := s_eq h
  simp only [ok, Bool.and_eq_true] at h
  have hE := M3.toMatrix_eq_of_eqb h.2
  rw [toMatrix_smulM, toMatrix_smulM, toMatrix_quatM3, Exact.re_mul, Exact.re_norm2,
    Exact.re_ofInt, show (Q4.map Exact.re I.q).toFun = Exact.reQ I.q from rfl] at hE
  ext i j
  have e := congrFun (congrFun hE i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at e
  simp only [Tr, Matrix.smul_apply, smul_eq_mul]
  change (Exact.re I.d)⁻¹ * I.M.toMatrix i j =
    I.s / (Exact.reQ I.q ⬝ᵥ Exact.reQ I.q) * quatMatrix (Exact.reQ I.q) i j
  rcases hs with h1 | h1 <;> rw [h1] at e ⊢ <;> push_cast at e ⊢ <;> field_simp <;>
    [linarith; linarith]

theorem maps_sound (h : I.ok = true) {v p : V3 κ} (hm : I.maps v p = true) :
    Exact.reV p = I.Tr *ᵥ Exact.reV v + I.br := by
  have hd := d_ne h
  have e := Exact.reV_eq_of_eqV hm
  rw [Exact.reV_smul, Exact.reV_add, ← M3.toMatrix_mulVec] at e
  rw [Tr, br, smul_mulVec, ← smul_add, ← e, smul_smul, inv_mul_cancel₀ hd, one_smul]

end Iso

theorem reV_signedPt (pts : List (V3 κ)) (an : Bool) (j : ℕ) :
    Exact.reV (signedPt pts an j) = (if an then -1 else 1 : ℝ) • Exact.reV (Exact.pt pts j) := by
  cases an
  · simp [signedPt]
  · simp [signedPt, negV3, Exact.reV_smul, Exact.re_ofInt]

/-- The real pose map of a link's isometries. -/
noncomputable def linkPose (D : MapD) (H G : Iso κ) : PoseMap :=
  ⟨D.a, D.k, D.a', D.k', Exact.reQ H.q, H.s, H.br, Exact.reQ G.q, G.s, G.br, D.e⟩

variable {D : MapD} {H G : Iso κ}

theorem linkPose_T (hH : H.ok = true) : (linkPose D H G).T = H.Tr := (Iso.Tr_eq hH).symm

theorem linkPose_G (hG : G.ok = true) : (linkPose D H G).G = G.Tr := (Iso.Tr_eq hG).symm

theorem linkPose_valid (hH : H.ok = true) (hG : G.ok = true) (he : D.e = (H.s != G.s)) :
    (linkPose D H G).Valid := by
  refine ⟨fun h0 ↦ ?_, fun h0 ↦ ?_, ?_, ?_, ?_⟩
  · have := Iso.norm_pos hH
    rw [show Exact.reQ H.q = 0 from h0, dotProduct_zero] at this
    exact lt_irrefl _ this
  · have := Iso.norm_pos hG
    rw [show Exact.reQ G.q = 0 from h0, dotProduct_zero] at this
    exact lt_irrefl _ this
  · rcases Iso.s_eq hH with h | h <;> simp [linkPose, h]
  · rcases Iso.s_eq hG with h | h <;> simp [linkPose, h]
  · simp only [linkPose, he]
    rcases Iso.s_eq hH with h | h <;> rcases Iso.s_eq hG with h' | h' <;> simp [h, h']

theorem corr_of_contactMaps {pts : List (V3 κ)} (hH : H.ok = true) (hG : G.ok = true)
    {c c' : ℕ × ℕ × ℕ} {fl an : Bool} (h : contactMaps pts H G c c' fl an = true) :
    Corr (linkPose D H G) (fun v ↦ Exact.reV (Exact.pt pts v)) c c' fl an := by
  rw [Corr, linkPose_T hH, linkPose_G hG]
  cases fl <;>
  · simp only [contactMaps, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at h ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨?_, ?_, ?_⟩
    · rw [← reV_signedPt, Iso.maps_sound hH h1]; rfl
    · rw [← reV_signedPt, Iso.maps_sound hH h2]; rfl
    · rw [← reV_signedPt, Iso.maps_sound hG h3]; rfl

/-- The data of a link's pose map, as exact values (`cstOf` over `κ`, with `d_b, d_c`). -/
def cstK (H G : Iso κ) : List κ :=
  [H.q.w, H.q.x, H.q.y, H.q.z, H.b.x, H.b.y, H.b.z, H.d, G.q.w, G.q.x, G.q.y, G.q.z,
    G.b.x, G.b.y, G.b.z, G.d]

theorem holds_link (hH : H.ok = true) (hG : G.ok = true) (hs : D.sT = H.s) (w : ℕ → ℝ) (o : ℕ) :
    Holds D (linkPose D H G) (withC w o ((cstK H G).map Exact.re)) o where
  a := rfl
  k := rfl
  a' := rfl
  k' := rfl
  sT := by simp [linkPose, hs]
  e := rfl
  τ := by
    funext j
    fin_cases j <;> simp [τE, withC, cstK, linkPose, Exact.reQ, Q4.map, Q4.toFun]
  b := by
    funext j
    have hd := Iso.d_ne hH
    fin_cases j <;> simp [bE, dbE, withC, cstK, linkPose, Iso.br, Exact.reV, V3.map, V3.toFun, hd]
  db := by simpa [dbE, withC, cstK] using Iso.d_ne hH
  γ := by
    funext j
    fin_cases j <;> simp [γE, withC, cstK, linkPose, Exact.reQ, Q4.map, Q4.toFun]
  c := by
    funext j
    have hd := Iso.d_ne hG
    fin_cases j <;> simp [cE, dcE, withC, cstK, linkPose, Iso.br, Exact.reV, V3.map, V3.toFun, hd]
  dc := by simpa [dcE, withC, cstK] using Iso.d_ne hG

end Real

/-! ### Quotients in a box, by balls -/

/-- The test that `N / D` lies in `[(c - ρ) / 2^s, (c + ρ) / 2^s]`, `D` of one sign, by the
balls `Y` of the variables. -/
def quotIn (Y : ℕ → Ball) (N D : Expr) (c : ℤ) (ρ : ℕ) (s : ℕ) : Bool :=
  let e1 : Expr := N * .const (2 ^ s) - .const (c - ρ) * D
  let e2 : Expr := .const (c + ρ) * D - N * .const (2 ^ s)
  ((bval Y D).isPos && (bval Y e1).isNonneg && (bval Y e2).isNonneg) ||
    ((bval Y D).isNeg && (bval Y (.const 0 - e1)).isNonneg &&
      (bval Y (.const 0 - e2)).isNonneg)

theorem abs_quot_le {n d c ρ t : ℝ} (ht : 0 < t) (hd : 0 < d) (h1 : 0 ≤ n * t - (c - ρ) * d)
    (h2 : 0 ≤ (c + ρ) * d - n * t) : |n / d - c / t| ≤ ρ / t := by
  have hx1 : (c - ρ) / t ≤ n / d := by rw [div_le_div_iff₀ ht hd]; linarith
  have hx2 : n / d ≤ (c + ρ) / t := by rw [div_le_div_iff₀ hd ht]; linarith
  rw [sub_div] at hx1
  rw [add_div] at hx2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem quotIn_sound {Y : ℕ → Ball} {ζ : ℕ → ℝ} (hY : ∀ i, (Y i).Encl (ζ i)) {N D : Expr}
    {c : ℤ} {ρ s : ℕ} (h : quotIn Y N D c ρ s = true) :
    D.eval ζ ≠ 0 ∧ |N.eval ζ / D.eval ζ - c / 2 ^ s| ≤ ρ / 2 ^ s := by
  have hs : (0 : ℝ) < 2 ^ s := by positivity
  simp only [quotIn, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨⟨hD, h1⟩, h2⟩ | ⟨⟨hD, h1⟩, h2⟩
  · have hd := Ball.pos_sound (encl_bval hY D) hD
    have e1 := Ball.nonneg_sound (encl_bval hY _) h1
    have e2 := Ball.nonneg_sound (encl_bval hY _) h2
    simp only [Expr.eval_sub, Expr.eval_mul, Expr.eval_const] at e1 e2
    push_cast at e1 e2
    exact ⟨hd.ne', abs_quot_le hs hd e1 e2⟩
  · have hd := Ball.neg_sound (encl_bval hY D) hD
    have e1 := Ball.nonneg_sound (encl_bval hY _) h1
    have e2 := Ball.nonneg_sound (encl_bval hY _) h2
    simp only [Expr.eval_sub, Expr.eval_mul, Expr.eval_const] at e1 e2
    push_cast at e1 e2
    refine ⟨hd.ne, ?_⟩
    rw [← neg_div_neg_eq]
    exact abs_quot_le hs (neg_pos.mpr hd) (by linarith) (by linarith)

/-! ### The check -/

section Check

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The balls of a link's variables: the zero's below `n`, then the map's data from the balls of
the basis values (in the zero's balls from `n` on). -/
def linkY (Z : List Ball) (n : ℕ) (cK : List κ) : ℕ → Ball :=
  let cb := cK.map fun a ↦ bval (Kraw.zball Z) (elemE n (ExactBasis.dim κ) (ExactBasis.coords a))
  fun i ↦ if i < n then Kraw.zball Z i else cb.getD (i - n) (Ball.ofInt 0)

/-- The discrete data of a link's pose map. -/
def linkD (R R' : RootRec) (H G : Iso κ) : MapD :=
  ⟨R.view, R.rot, R'.view, R'.rot, H.s, H.s != G.s, R.cen⟩

/-- The checks of a link with the isometries `H`, `G`, at the balls `Z` of `R`'s zero. -/
def linkOkWith (pts : List (V3 κ)) (Z : List Ball) (R R' : RootRec) (L : LinkRec)
    (H G : Iso κ) : Bool :=
  let k := R.contacts.length
  let n := nx R.cen + 1 + k
  let D := linkD R R' H G
  let σ : ℕ → ℕ := fun i ↦ L.sigma.getD i 0
  let src : ℕ → ℕ := fun j ↦ L.sigma.idxOf j
  let fl : ℕ → Bool := fun i ↦ L.flip.getD i false
  let an : ℕ → Bool := fun i ↦ L.anti.getD i false
  let Y := linkY Z n (cstK H G)
  H.ok && G.ok && (R'.cen == R.cen) && (R'.contacts.length == k) &&
    (!R.cen || (Exact.isZeroV H.b && Exact.isZeroV G.b)) &&
    (List.range k).all (fun i ↦ decide (σ i < k) && src (σ i) == i && (!an i || R.cen) &&
      contactMaps pts H G (R.contacts.getD i (0, 0, 0)) (R'.contacts.getD (σ i) (0, 0, 0))
        (fl i) (an i)) &&
    (List.range k).all (fun j ↦ decide (src j < k) && σ (src j) == j) &&
    (List.range n).all fun j ↦
      quotIn Y (coordE D n src fl j).1 (coordE D n src fl j).2 (R'.c.getD j 0) (R'.ρ.getD j 0)
        R'.s

/-- The checks of a link at the balls `Z` of `R`'s zero: its frames give isometries, and
`linkOkWith`. -/
def linkOkZ (pts : List (V3 κ)) (Z : List Ball) (R R' : RootRec) (L : LinkRec) : Bool :=
  match frameIso pts R.cen L.hole L.hn, frameIso pts R.cen L.plug L.pn with
  | some H, some G => linkOkWith pts Z R R' L H G
  | _, _ => false

/-- The checks of links from `R` to the roots of `targets`, at the balls of `R`'s zero, computed
once. -/
def linksOk (pts : List (V3 κ)) (R : RootRec) (targets : List (RootRec × LinkRec)) : Bool :=
  let Z := (R.kraw pts).zballs
  targets.all fun t ↦ linkOkZ pts Z R t.1 t.2

end Check

/-! ### Soundness -/

section Sound

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] [RootBasis κ]

omit [RootBasis κ] in
theorem linkY_encl {pts : List (V3 κ)} {R : RootRec} {y : Fin (R.kraw pts).n → ℝ}
    (hp : (R.kraw pts).ParOk (basisPar κ)) (hy : y ∈ (R.kraw pts).box)
    (h0 : (R.kraw pts).F (basisPar κ) y = 0) (cK : List κ) (i : ℕ) :
    (linkY (R.kraw pts).zballs (R.sys pts).n cK i).Encl
      (withC ((R.kraw pts).env (basisPar κ) y) (R.sys pts).n (cK.map Exact.re) i) := by
  have hZ := (R.kraw pts).encl_zballs hp hy h0
  simp only [linkY, withC]
  split_ifs with hi
  · exact hZ i
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_map]
    cases cK[i - (R.sys pts).n]? with
    | none => simpa using Ball.encl_ofInt 0
    | some a =>
      have e := encl_bval hZ (elemE (R.sys pts).n (ExactBasis.dim κ) (ExactBasis.coords a))
      rw [eval_elemE _ _ (fun j hj ↦ RootRec.env_basis y hj)] at e
      simpa using e

/-- **A link that checks gives its roots the same scale.** -/
theorem scale_eq_of_linkOkWith {pts : List (V3 κ)} {R R' : RootRec} {L : LinkRec}
    {H G : Iso κ} (hl : linkOkWith pts (R.kraw pts).zballs R R' L H G = true)
    (hR : R.ok pts = true) (hR' : R'.ok pts = true) : R.scale pts = R'.scale pts := by
  -- the zeros of the two roots
  have hpar := RootRec.parCheck_of_ok hR
  have hp := RootRec.parOk (pts := pts) hpar
  have hchk : (R.kraw pts).check = true := by
    simp only [RootRec.ok, Bool.and_eq_true] at hR
    exact hR.1.1.1.1.1.2
  obtain ⟨y, ⟨hy, h0⟩, huniq⟩ := (R.kraw pts).existsUnique hchk hp
  have hsc := RootRec.scale_eq (R := R) (pts := pts) ⟨⟨hy, h0⟩, huniq⟩
  have hp' := RootRec.parOk (pts := pts) (RootRec.parCheck_of_ok hR')
  have hchk' : (R'.kraw pts).check = true := by
    simp only [RootRec.ok, Bool.and_eq_true] at hR'
    exact hR'.1.1.1.1.1.2
  obtain ⟨y₂, ⟨hy₂, h0₂⟩, huniq₂⟩ := (R'.kraw pts).existsUnique hchk' hp'
  have hsc' := RootRec.scale_eq (R := R') (pts := pts) ⟨⟨hy₂, h0₂⟩, huniq₂⟩
  -- the checks
  simp only [linkOkWith, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at hl
  obtain ⟨⟨⟨⟨⟨⟨⟨hH, hG⟩, hcen⟩, hk⟩, hcb⟩, hc1⟩, hc2⟩, hbox⟩ := hl
  set S := R.sys pts with hS
  set S' := R'.sys pts with hS'
  set z := (R.kraw pts).env (basisPar κ) y with hz
  set D := linkD R R' H G with hD
  set P := linkPose D H G with hP
  set cst := (cstK H G).map Exact.re with hcst
  set σ : ℕ → ℕ := fun i ↦ L.sigma.getD i 0 with hσ
  set src : ℕ → ℕ := fun j ↦ L.sigma.idxOf j with hsrc
  set fl : ℕ → Bool := fun i ↦ L.flip.getD i false with hfl
  set an : ℕ → Bool := fun i ↦ L.anti.getD i false with han
  have hn : S.n = nx R.cen + 1 + R.contacts.length := rfl
  have h5 := five_le_nx R.cen
  have hY := linkY_encl (cK := cstK H G) hp hy h0
  have hHo := holds_link (D := D) hH hG rfl z S.n
  have hvert : ∀ v, vertOf z S.V v = Exact.reV (Exact.pt pts v) := RootRec.vertOf_env y
  -- the new charts are defined at the zero
  have hDc : D.cen = R.cen := rfl
  have hnx : nx D.cen < S.n := by rw [hDc]; omega
  have hw : P.wv (z 0) (z 1) P.a' ≠ 0 := by
    have hb := hbox 0 (by omega)
    rw [(holds_w hHo hnx).1]
    exact (quotIn_sound hY hb).1
  have hq : P.qq (z 0) (z 1) ![z 2, z 3, z 4] P.k' ≠ 0 := by
    have hb := hbox 2 (by omega)
    rw [(holds_w hHo hnx).2.1]
    exact (quotIn_sound hY hb).1
  have LH : LinkHyp S S' D P σ src fl an z cst :=
    { valid := linkPose_valid hH hG rfl
      cen := rfl
      cen' := hcen
      view := rfl
      rot := rfl
      view' := rfl
      rot' := rfl
      k := hk
      V := by
        change vertsE (nx R'.cen + 1 + R'.contacts.length) pts =
          vertsE (nx R.cen + 1 + R.contacts.length) pts
        rw [hcen, hk]
      perm := fun i hi ↦ ⟨(hc1 i hi).1.1.1, (hc1 i hi).1.1.2⟩
      perm' := fun j hj ↦ hc2 j hj
      cb := fun hc ↦ by
        rcases hcb with h | ⟨hb, hc'⟩
        · have h' : R.cen = true := hc
          rw [h] at h'
          exact absurd h' (by decide)
        · refine ⟨?_, ?_⟩
          · simp [hP, linkPose, Iso.br, Exact.reV_eq_zero_of_isZeroV hb]
          · simp [hP, linkPose, Iso.br, Exact.reV_eq_zero_of_isZeroV hc']
      anti := fun i hi ha ↦ by
        have := (hc1 i hi).1.2
        rcases this with h | h
        · have ha' : L.anti.getD i false = true := ha
          have h' : L.anti.getD i false = false := by rw [List.getD_eq_getElem?_getD]; exact h
          rw [ha'] at h'
          exact absurd h' (by decide)
        · exact h
      vert := fun w hwz v ↦ by
        rw [hvert]
        exact vertOf_vertsE w S.n (fun j hj ↦ by
          rw [hwz _ (by omega)]
          exact RootRec.env_basis y hj) pts v
      corr := fun i hi ↦ by
        have e : vertOf z S.V = fun v ↦ Exact.reV (Exact.pt pts v) := funext hvert
        rw [e]
        exact corr_of_contactMaps hH hG (hc1 i hi).2
      holds := hHo
      hw := hw
      hq := hq }
  obtain ⟨hgs, hst⟩ := LH.zero_transport (fun i hi ↦ Sys.g_zero (R.kraw_eqs pts) h0 hi)
    (fun v hv ↦ Sys.stat_zero (R.kraw_eqs pts) h0 hv)
  -- the image is the zero of `R'`
  set z' := imageP D S.n src fl cst z with hz'
  have hn' : (R'.kraw pts).n = S.n := (Sys.n_eq (R'.kraw_eqs pts)).trans LH.n_eq'
  have hn0 : (R.kraw pts).n = S.n := Sys.n_eq (R.kraw_eqs pts)
  set y' : Fin (R'.kraw pts).n → ℝ := fun j ↦ z' j with hy'
  have henv : (R'.kraw pts).env (basisPar κ) y' = z' := by
    funext i
    simp only [Kraw.env]
    split_ifs with hi
    · rfl
    · have e1 : imageP D S.n src fl cst z i = z i := imageP_ge (by omega)
      rw [hz', e1, hz]
      simp only [Kraw.env, show ¬i < (R.kraw pts).n by omega, ↓reduceDIte]
      congr 1
      omega
  have hF : (R'.kraw pts).F (basisPar κ) y' = 0 := by
    funext e
    change ((R'.kraw pts).eqs.getD e (.const 0)).eval ((R'.kraw pts).env (basisPar κ) y') = 0
    rw [henv, R'.kraw_eqs pts]
    have he : (e : ℕ) < S'.nv + S'.k := by
      have h1 := e.isLt
      have h2 : (R'.kraw pts).n = S'.nv + S'.k := Sys.n_eq (R'.kraw_eqs pts)
      omega
    by_cases hek : (e : ℕ) < S'.k
    · rw [S'.getD_eqs_g hek]
      exact hgs e hek
    · obtain ⟨v, hv⟩ : ∃ v, (e : ℕ) = S'.k + v := ⟨e - S'.k, by omega⟩
      rw [hv, S'.getD_eqs_stat (by omega), Sys.stat]
      change (sumE S'.k fun i ↦ .mul (mE S'.cen i) (deriv v (S'.g i))).eval z' - _ = 0
      rw [eval_sumE, sub_eq_zero]
      exact hst v (by omega)
  have hbox' : y' ∈ (R'.kraw pts).box := by
    intro i
    have hb := (quotIn_sound hY (hbox i (by have := i.2; omega))).2
    have e : y' i = coordV D S.n src fl (withC z S.n cst) i := by
      simp only [hy', hz', imageP_lt (show (i : ℕ) < S.n by have := i.2; omega)]
    rw [e]
    exact hb
  -- the scales
  have hyy := huniq₂ y' ⟨hbox', hF⟩
  rw [hsc, hsc', ← hyy, henv, hz', show nx R'.cen = nx D.cen by rw [hcen]; rfl]
  exact (LH.imgl).symm

/-- **Links that check give their target roots the scale of the source root.** -/
theorem scale_eq_of_linksOk {pts : List (V3 κ)} {R : RootRec}
    {targets : List (RootRec × LinkRec)} (h : linksOk pts R targets = true)
    (hR : R.ok pts = true) (hok : ∀ t ∈ targets, t.1.ok pts = true) :
    ∀ t ∈ targets, t.1.scale pts = R.scale pts := by
  intro t ht
  have h1 := List.all_eq_true.mp h t ht
  simp only [linkOkZ] at h1
  split at h1
  · exact (scale_eq_of_linkOkWith h1 hR (hok t ht)).symm
  · exact absurd h1 Bool.false_ne_true

end Sound

end Nieuwland.Root
