import Modules.Root.Identity
import Modules.Root.Reps

/-!
# Links that exchange contacts

Two roots of one optimal pose may list different contacts: at the pose more contacts touch than
a system needs (coincidences of the weak fit, `Modules/Root/Identity.lean`), and each root's
system lists its own choice. A pose map (`Modules/Root/Link.lean`) then sends some contact of the
source to a contact the target does not list but that touches by an identity of the target
(`D g = ∑ p_j g_j` over the target's contacts), and some contact the target lists is the image
of no listed contact of the source, only of one the source touches by an identity of its own.

The image `w` of the source's zero is still the target's zero, with other multipliers:

* the image is the zero of the **middle system**, the target's pose with the images of the
  source's contacts (`exMid`; the transport `LinkHyp.zero_transport`);
* every contact the target lists touches at `w`: it is the image of a listed contact, or of a
  contact of a source identity (`LinkHyp.slack_img_corr`, `Sys.slack_zero_of_idOk`);
* at a common zero of the target's slacks an identity's derivative gives
  `D ∂g = ∑ p_j ∂g_j` (`Sys.id_deriv`), so the stationarity of the middle system with the
  multipliers `m_i` is that of the target with `μ_j = ∑_i m_i q_ij`, `q_ij = [σ i = j]` for a
  listed image and `p_ij / D_i` for an identity's (`stat_exchange`);
* the slacks do not depend on the multipliers (`eval_slackE_congr`,
  `eval_deriv_slackE_congr`), so `w` with the multipliers `μ` is a zero of the target, and the
  check (`exLinkOkWith`) puts it in the target's box by balls: quotients of balls by `quotB`
  (`quotIn` on two variables) at candidates of `divCand`.

`scale_eq_of_exLinkOkWith`: then the two roots have the same scale. A link that exchanges
nothing (`back` empty, every image listed) is checked the same way, so a solid's links may all be
of this kind: `exGroupsOk` and `isRootEq_of_exLinks` are `Root.linkGroupsOk` and
`Root.isRootEq_of_links` (`Modules/Root/Reps.lean`) for them.
-/

open Matrix Finset
open Nieuwland.Check

namespace Nieuwland.Root

/-! ### Slacks do not depend on the multipliers -/

section Vars

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- A slack of the vertices `vertsE nu pts` has one value at two points that agree on the pose
and the scale (the variables up to `nx cen`) and hold the basis values from `nu` on. -/
theorem eval_slackE_congr {cen : Bool} {a : Fin 3} {k : Fin 4} {nu : ℕ} {pts : List (V3 κ)}
    {z w : ℕ → ℝ} (hzw : ∀ u ≤ nx cen, z u = w u)
    (hz : ∀ j < ExactBasis.dim κ, z (nu + j) = ExactBasis.basis κ j)
    (hw : ∀ j < ExactBasis.dim κ, w (nu + j) = ExactBasis.basis κ j) (va vb vk : ℕ) :
    (slackE cen a k (vertsE nu pts) va vb vk).eval z =
      (slackE cen a k (vertsE nu pts) va vb vk).eval w := by
  have h5 := five_le_nx cen
  have hy : yOf z cen = yOf w cen := by
    funext c
    cases cen
    · have h7 : nx false = 7 := rfl
      fin_cases c
      · simp [yOf, yE, hzw 5 (by omega)]
      · simp [yOf, yE, hzw 6 (by omega)]
    · simp [yOf, yE]
  rw [eval_slackE_eq_slackR, eval_slackE_eq_slackR]
  simp only [vertOf_vertsE z nu hz, vertOf_vertsE w nu hw, hy]
  simp only [lE, Expr.eval_var, hzw 0 (by omega), hzw 1 (by omega), hzw 2 (by omega),
    hzw 3 (by omega), hzw 4 (by omega), hzw (nx cen) le_rfl]

/-- The same for the derivative in a variable of the pose or the scale. -/
theorem eval_deriv_slackE_congr {cen : Bool} {a : Fin 3} {k : Fin 4} {nu : ℕ}
    {pts : List (V3 κ)} {z w : ℕ → ℝ} (hzw : ∀ u ≤ nx cen, z u = w u)
    (hz : ∀ j < ExactBasis.dim κ, z (nu + j) = ExactBasis.basis κ j)
    (hw : ∀ j < ExactBasis.dim κ, w (nu + j) = ExactBasis.basis κ j) {v : ℕ} (hv : v ≤ nx cen)
    (hnu : nx cen < nu) (va vb vk : ℕ) :
    (deriv v (slackE cen a k (vertsE nu pts) va vb vk)).eval z =
      (deriv v (slackE cen a k (vertsE nu pts) va vb vk)).eval w := by
  set e := slackE cen a k (vertsE nu pts) va vb vk
  have hf : (fun r ↦ e.eval (line z v r)) = fun r ↦ e.eval (line w v r) := by
    funext r
    refine eval_slackE_congr (fun u hu ↦ ?_) (fun j hj ↦ ?_) (fun j hj ↦ ?_) va vb vk
    · simp only [line, Function.update_apply]
      split_ifs with h
      · rw [hzw v hv]
      · exact hzw u hu
    · rw [line, Function.update_of_ne (by omega)]
      exact hz j hj
    · rw [line, Function.update_of_ne (by omega)]
      exact hw j hj
  have h1 := hasDerivAt_eval_line z v e
  rw [hf] at h1
  exact h1.unique (hasDerivAt_eval_line w v e)

end Vars

/-! ### The derivative of an identity -/

namespace Sys

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- **An identity's derivative at a common zero**: if `D g = ∑ p_j g_j` expands to the polynomial
without terms (`idOk`'s expansion) and `g` and the `g_j` vanish at `w`, then
`D ∂ᵥ g = ∑ p_j ∂ᵥ g_j` at `w`, for every unknown `v`. -/
theorem id_deriv {S : Sys} {r : IdRec} (hemp : (toSP κ S.n (S.idE r)).terms.isEmpty = true)
    {w : ℕ → ℝ} (hw : ∀ j, w (S.n + j) = basisPar κ j) {v : ℕ} (hv : v < S.n)
    (hg : ∀ j < S.k, (S.g j).eval w = 0) (hc : (S.slack r.con).eval w = 0) :
    r.D.eval w * (deriv v (S.slack r.con)).eval w =
      ∑ j ∈ range S.k, (r.p.getD j (.const 0)).eval w * (deriv v (S.g j)).eval w := by
  have h0 : ∀ t : ℝ, (S.idE r).eval (line w v t) = 0 := fun t ↦
    eval_eq_zero_of_toSP S.n _ (fun j ↦ by rw [line, Function.update_of_ne (by omega)]; exact hw j)
      hemp
  have hd0 : HasDerivAt (fun t ↦ (S.idE r).eval (line w v t)) 0 0 := by
    simp only [h0]
    exact hasDerivAt_const _ _
  have e := (hasDerivAt_eval_line w v (S.idE r)).unique hd0
  change ((deriv v r.D).eval w * (S.slack r.con).eval w +
      r.D.eval w * (deriv v (S.slack r.con)).eval w) -
    (deriv v (sumE S.k fun i ↦ .mul (r.p.getD i (.const 0)) (S.g i))).eval w = 0 at e
  rw [eval_deriv_sumE, hc, mul_zero, zero_add, sub_eq_zero] at e
  rw [e]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  change (deriv v (r.p.getD j (.const 0))).eval w * (S.g j).eval w +
    (r.p.getD j (.const 0)).eval w * (deriv v (S.g j)).eval w = _
  rw [hg j (mem_range.mp hj), mul_zero, zero_add]

end Sys

/-! ### The slack of any two contacts that correspond -/

namespace LinkHyp

variable {S S' : Sys} {D : MapD} {P : PoseMap} {σ src : ℕ → ℕ} {fl an : ℕ → Bool}
  {z : ℕ → ℝ} {cst : List ℝ} (H : LinkHyp S S' D P σ src fl an z cst)
include H

/-- **The slack of corresponding contacts at the image**, for any contacts (`slack_img` for the
system's own). -/
theorem slack_img_corr {c c' : ℕ × ℕ × ℕ} {f a : Bool} (hc : Corr P (vertOf z S.V) c c' f a)
    (ha : a = true → D.cen = true) :
    (S'.slack c').eval (imageP D S.n src fl cst z) =
      flipSign f * P.factor (z 0) (z 1) ![z 2, z 3, z 4] * (S.slack c).eval z := by
  have hy0 : a = true → yOf z D.cen = 0 ∧ P.b = 0 ∧ P.c = 0 := fun h ↦ by
    have hc' := ha h
    exact ⟨by rw [hc', yOf_true], H.cb hc'⟩
  have key := slackR_corr H.valid H.hw H.hq hc (yOf z D.cen) (z (nx D.cen)) hy0
  simp only [Sys.slack, eval_slackE_eq_slackR, H.cen, H.cen', H.view, H.rot, H.view',
    H.rot', H.V, lE, Expr.eval_var, vert_img H, ← H.holds.a, ← H.holds.k, ← H.holds.a',
    ← H.holds.k']
  rw [H.img0, H.img1, H.imgx, H.imgy, H.imgl, key]

end LinkHyp

/-! ### The stationarity with exchanged contacts -/

/-- **Multipliers recombined**: if `∑ m_i ∂g''_i = δ` and each `∂g''_i = ∑_j q_ij ∂g'_j`, then
`∑_j μ_j ∂g'_j = δ` with `μ_j = ∑_i m_i q_ij`. -/
theorem stat_exchange {k : ℕ} {g'' g' : ℕ → Expr} {w : ℕ → ℝ} {m : ℕ → ℝ} {q : ℕ → ℕ → ℝ} {v : ℕ}
    {δ : ℝ} (hstat : ∑ i ∈ range k, m i * (deriv v (g'' i)).eval w = δ)
    (hq : ∀ i < k, (deriv v (g'' i)).eval w = ∑ j ∈ range k, q i j * (deriv v (g' j)).eval w) :
    ∑ j ∈ range k, (∑ i ∈ range k, m i * q i j) * (deriv v (g' j)).eval w = δ := by
  have e : ∑ i ∈ range k, m i * (deriv v (g'' i)).eval w =
      ∑ i ∈ range k, m i * ∑ j ∈ range k, q i j * (deriv v (g' j)).eval w :=
    Finset.sum_congr rfl fun i hi ↦ by rw [hq i (mem_range.mp hi)]
  rw [← hstat, e]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-! ### Quotients of balls -/

/-- The test that the quotient of the values of the balls `Nb`, `Db` lies in `⟨c, ρ, t⟩`
(`quotIn` on two variables). -/
def quotB (Nb Db : Ball) (c : ℤ) (ρ t : ℕ) : Bool :=
  quotIn (fun i ↦ if i = 0 then Nb else Db) (.var 0) (.var 1) c ρ t

theorem quotB_sound {Nb Db : Ball} {x y : ℝ} (hx : Nb.Encl x) (hy : Db.Encl y) {c : ℤ}
    {ρ t : ℕ} (h : quotB Nb Db c ρ t = true) : y ≠ 0 ∧ (⟨c, ρ, t⟩ : Ball).Encl (x / y) := by
  have hY : ∀ i, (if i = 0 then Nb else Db).Encl ((fun i ↦ if i = 0 then x else y) i) := by
    intro i
    by_cases hi : i = 0 <;> simp [hi, hx, hy]
  obtain ⟨h1, h2⟩ := quotIn_sound hY h
  simp only [Expr.eval_var, one_ne_zero, ite_false, ite_true] at h1 h2
  refine ⟨h1, ?_⟩
  have ht : (0 : ℝ) < 2 ^ t := by positivity
  unfold Ball.Encl
  have e : (2 : ℝ) ^ t * (x / y) - c = 2 ^ t * (x / y - c / 2 ^ t) := by field_simp
  rw [e, abs_mul, abs_of_pos ht]
  calc 2 ^ t * |x / y - c / 2 ^ t| ≤ 2 ^ t * (ρ / 2 ^ t) := mul_le_mul_of_nonneg_left h2 ht.le
    _ = ρ := by field_simp

/-- A ball for the quotient of two balls' values at the scale `t`: a candidate, unchecked
(`quotB` checks it): the centre `2^t m_N / m_D` and the first-order radius, rounded up. -/
def divCand (Nb Db : Ball) (t : ℕ) : Ball :=
  let am := Db.m.natAbs
  ⟨(Nb.m * 2 ^ (t + Db.s)) / (Db.m * 2 ^ Nb.s),
    2 ^ (t + Db.s) * (Nb.r * am + Nb.m.natAbs * Db.r) / (2 ^ Nb.s * am * (am - Db.r)) + 2, t⟩

/-! ### The check -/

section Check

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The identity `r` of a root's weak fit (out of range: one that checks nothing). -/
def idAt (R : RootRec) (r : ℕ) : IdRec := R.W.ids.getD r ⟨(0, 0, 0), .const 1, []⟩

/-- A link that may exchange contacts: the record of `Root.LinkRec`, whose `sigma` may send a
contact to `k + r`, the contact of the target's identity `r` (`idAt`); and `back`, entries
`(r, j, flip, anti)`: the target's contact `j` is the image of the contact of the source's
identity `r`. -/
structure ExLinkRec where
  /-- The link. -/
  L : LinkRec
  /-- The target's contacts that are images of the source's identities' contacts. -/
  back : List (ℕ × ℕ × Bool × Bool)
  deriving Repr

/-- The image of the source's contact `i`: a contact of the target, or of its identity. -/
def exImg (R' : RootRec) (k : ℕ) (σ : ℕ → ℕ) (i : ℕ) : ℕ × ℕ × ℕ :=
  if σ i < k then R'.contacts.getD (σ i) (0, 0, 0) else (idAt R' (σ i - k)).con

/-- The middle root: the target with the images of the source's contacts. -/
def exMid (R' : RootRec) (k : ℕ) (σ : ℕ → ℕ) : RootRec :=
  { R' with contacts := (List.range k).map (exImg R' k σ) }

/-- The balls of the numerators and denominators of the image's coordinates. -/
def exND (Y : ℕ → Ball) (D : MapD) (n : ℕ) (fl : ℕ → Bool) : List (Ball × Ball) :=
  (List.range n).map fun u ↦ (bval Y (coordE D n id fl u).1, bval Y (coordE D n id fl u).2)

/-- The candidate balls of the image's coordinates. -/
def exT (ND : List (Ball × Ball)) (t : ℕ) : List Ball := ND.map fun p ↦ divCand p.1 p.2 t

/-- Their checks. -/
def exTOk (ND : List (Ball × Ball)) (T : List Ball) (t n : ℕ) : Bool :=
  (List.range n).all fun u ↦
    quotB (ND.getD u (Ball.ofInt 0, Ball.ofInt 0)).1 (ND.getD u (Ball.ofInt 0, Ball.ofInt 0)).2
      (T.getD u (Ball.ofInt 0)).m (T.getD u (Ball.ofInt 0)).r t

/-- The balls of the image: its coordinates below `n`, the parameters' from the zero's. -/
def exW (T : List Ball) (n : ℕ) (Z : List Ball) : ℕ → Ball :=
  fun u ↦ if u < n then T.getD u (Ball.ofInt 0) else Kraw.zball Z u

/-- The ball of `q_ij`: `[σ i = j]`, or `p_j / D` of the target's identity. -/
def exQ (R' : RootRec) (k : ℕ) (σ : ℕ → ℕ) (W : ℕ → Ball) (t i j : ℕ) : Ball :=
  if σ i < k then Ball.ofInt (if σ i = j then 1 else 0)
  else divCand (bval W ((idAt R' (σ i - k)).p.getD j (.const 0))) (bval W (idAt R' (σ i - k)).D) t

/-- Its checks: `D` of one sign, and every quotient in its ball. -/
def exQOk (R' : RootRec) (k : ℕ) (σ : ℕ → ℕ) (W : ℕ → Ball) (t i : ℕ) : Bool :=
  decide (σ i < k) ||
    ((bval W (idAt R' (σ i - k)).D).isPos || (bval W (idAt R' (σ i - k)).D).isNeg) &&
      (List.range k).all fun j ↦
        quotB (bval W ((idAt R' (σ i - k)).p.getD j (.const 0))) (bval W (idAt R' (σ i - k)).D)
          (exQ R' k σ W t i j).m (exQ R' k σ W t i j).r t

/-- The ball of the multiplier `μ_j = ∑_i m_i q_ij` (the `m_i` the image's, from `nv` on). -/
def exMu (W : ℕ → Ball) (Q : ℕ → ℕ → Ball) (k nv j : ℕ) : Ball :=
  bval (fun u ↦ if u < k then W (nv + u) else if u < k + k then Q (u - k) j else Ball.ofInt 0)
    (sumE k fun i ↦ .mul (.var i) (.var (k + i)))

/-- **The checks of a link that may exchange contacts** (module docs), with the isometries `H`,
`G`, at the balls `Z` of `R`'s zero. The precision of the quotients is the target's box's and 64
bits. -/
def exLinkOkWith (pts : List (V3 κ)) (Z : List Ball) (R R' : RootRec) (E : ExLinkRec)
    (H G : Iso κ) : Bool :=
  let k := R.contacts.length
  let nv := nx R.cen + 1
  let n := nv + k
  let D := linkD R R' H G
  let σ : ℕ → ℕ := fun i ↦ E.L.sigma.getD i 0
  let fl : ℕ → Bool := fun i ↦ E.L.flip.getD i false
  let an : ℕ → Bool := fun i ↦ E.L.anti.getD i false
  let Y := linkY Z n (cstK H G)
  let t := R'.s + 64
  let ND := exND Y D n fl
  let T := exT ND t
  let W := exW T n Z
  H.ok && G.ok && (R'.cen == R.cen) && (R'.contacts.length == k) &&
    (!R.cen || (Exact.isZeroV H.b && Exact.isZeroV G.b)) &&
    (List.range k).all (fun i ↦ (!an i || R.cen) &&
      contactMaps pts H G (R.contacts.getD i (0, 0, 0)) (exImg R' k σ i) (fl i) (an i) &&
      (decide (σ i < k) ||
        (toSP κ (R'.sys pts).n ((R'.sys pts).idE (idAt R' (σ i - k)))).terms.isEmpty)) &&
    (List.range k).all (fun j ↦ (List.range k).any (fun i ↦ σ i == j) ||
      E.back.any fun b ↦ b.2.1 == j && Sys.idOk κ (R.sys pts) Z (idAt R b.1) &&
        (!b.2.2.2 || R.cen) &&
        contactMaps pts H G (idAt R b.1).con (R'.contacts.getD j (0, 0, 0)) b.2.2.1 b.2.2.2) &&
    (List.range nv).all (fun j ↦
      quotIn Y (coordE D n id fl j).1 (coordE D n id fl j).2 (R'.c.getD j 0) (R'.ρ.getD j 0)
        R'.s) &&
    exTOk ND T t n &&
    (List.range k).all (exQOk R' k σ W t) &&
    (List.range k).all fun j ↦
      quotIn (fun _ ↦ exMu W (exQ R' k σ W t) k nv j) (.var 0) (.const 1)
        (R'.c.getD (nv + j) 0) (R'.ρ.getD (nv + j) 0) R'.s

/-- The checks at the balls `Z` of `R`'s zero: the frames give isometries, and
`exLinkOkWith`. -/
def exLinkOkZ (pts : List (V3 κ)) (Z : List Ball) (R R' : RootRec) (E : ExLinkRec) : Bool :=
  match frameIso pts R.cen E.L.hole E.L.hn, frameIso pts R.cen E.L.plug E.L.pn with
  | some H, some G => exLinkOkWith pts Z R R' E H G
  | _, _ => false

end Check

/-! ### Balls of the image -/

section Balls

theorem exT_encl {Y : ℕ → Ball} {ζ : ℕ → ℝ} (hY : ∀ i, (Y i).Encl (ζ i)) {D : MapD} {n : ℕ}
    {fl : ℕ → Bool} {t : ℕ} (h : exTOk (exND Y D n fl) (exT (exND Y D n fl) t) t n = true) {u : ℕ}
    (hu : u < n) :
    ((exT (exND Y D n fl) t).getD u (Ball.ofInt 0)).Encl (coordV D n id fl ζ u) ∧
      (coordE D n id fl u).2.eval ζ ≠ 0 := by
  have hu' := List.all_eq_true.mp h u (List.mem_range.mpr hu)
  have e1 : (exND Y D n fl).getD u (Ball.ofInt 0, Ball.ofInt 0) =
      (bval Y (coordE D n id fl u).1, bval Y (coordE D n id fl u).2) := by
    simp [exND, List.getD_eq_getElem?_getD, hu]
  have e2 : (exT (exND Y D n fl) t).getD u (Ball.ofInt 0) =
      divCand (bval Y (coordE D n id fl u).1) (bval Y (coordE D n id fl u).2) t := by
    simp [exT, exND, List.getD_eq_getElem?_getD, hu]
  rw [e1, e2] at hu'
  rw [e2]
  obtain ⟨hd, he⟩ := quotB_sound (encl_bval hY _) (encl_bval hY _) hu'
  exact ⟨he, hd⟩

theorem exW_encl {T : List Ball} {n : ℕ} {Z : List Ball} {w : ℕ → ℝ}
    (hT : ∀ u < n, (T.getD u (Ball.ofInt 0)).Encl (w u))
    (hZ : ∀ u, n ≤ u → (Kraw.zball Z u).Encl (w u)) (u : ℕ) : (exW T n Z u).Encl (w u) := by
  unfold exW
  split_ifs with h
  · exact hT u h
  · exact hZ u (by omega)

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The value `q_ij` (module docs) at `w`. -/
noncomputable def exq (R' : RootRec) (k : ℕ) (σ : ℕ → ℕ) (w : ℕ → ℝ) (i j : ℕ) : ℝ :=
  if σ i < k then (if σ i = j then 1 else 0)
  else ((idAt R' (σ i - k)).p.getD j (.const 0)).eval w / (idAt R' (σ i - k)).D.eval w

theorem exQ_encl {R' : RootRec} {k : ℕ} {σ : ℕ → ℕ} {W : ℕ → Ball} {w : ℕ → ℝ}
    (hW : ∀ u, (W u).Encl (w u)) {t i : ℕ} (h : exQOk R' k σ W t i = true) :
    (k ≤ σ i → (idAt R' (σ i - k)).D.eval w ≠ 0) ∧
      ∀ j < k, (exQ R' k σ W t i j).Encl (exq R' k σ w i j) := by
  by_cases hs : σ i < k
  · refine ⟨fun h' ↦ absurd h' (by omega), fun j _ ↦ ?_⟩
    simp only [exQ, exq, hs, ↓reduceIte]
    split_ifs
    · simpa using Ball.encl_ofInt 1
    · simpa using Ball.encl_ofInt 0
  · simp only [exQOk, hs, decide_false, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
      List.all_eq_true, List.mem_range] at h
    obtain ⟨hD, hq⟩ := h
    have hDe := encl_bval hW (idAt R' (σ i - k)).D
    refine ⟨fun _ ↦ ?_, fun j hj ↦ ?_⟩
    · rcases hD with hD | hD
      · exact (Ball.pos_sound hDe hD).ne'
      · exact (Ball.neg_sound hDe hD).ne
    · have := (quotB_sound (encl_bval hW _) hDe (hq j hj)).2
      simp only [exQ, exq, hs, ↓reduceIte] at this ⊢
      exact this

theorem exMu_encl {W : ℕ → Ball} {Q : ℕ → ℕ → Ball} {w : ℕ → ℝ} {q : ℕ → ℕ → ℝ} {k nv j : ℕ}
    (hW : ∀ u, (W u).Encl (w u)) (hQ : ∀ i < k, (Q i j).Encl (q i j)) :
    (exMu W Q k nv j).Encl (∑ i ∈ range k, w (nv + i) * q i j) := by
  set ζ : ℕ → ℝ := fun u ↦ if u < k then w (nv + u) else if u < k + k then q (u - k) j else 0
  have hY : ∀ u,
      (if u < k then W (nv + u) else if u < k + k then Q (u - k) j else Ball.ofInt 0).Encl
      (ζ u) := by
    intro u
    by_cases hu : u < k
    · simp only [ζ, hu, ↓reduceIte]
      exact hW _
    · by_cases hu' : u < k + k
      · simp only [ζ, hu, hu', ↓reduceIte]
        exact hQ _ (by omega)
      · simp only [ζ, hu, hu', ↓reduceIte]
        simpa using Ball.encl_ofInt 0
  have h := encl_bval hY (sumE k fun i ↦ .mul (.var i) (.var (k + i)))
  rw [eval_sumE (R := ℝ)] at h
  have e : ∑ i ∈ range k, (Expr.mul (.var i) (.var (k + i))).eval ζ =
      ∑ i ∈ range k, w (nv + i) * q i j := by
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' := mem_range.mp hi
    change ζ i * ζ (k + i) = _
    simp only [ζ, hi', ↓reduceIte, show ¬ k + i < k by omega, show k + i < k + k by omega,
      Nat.add_sub_cancel_left]
  rwa [e] at h

end Balls

/-! ### Soundness -/

section Sound

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] [RootBasis κ]

omit [RootBasis κ] in
/-- The middle root's slacks are the target's. -/
theorem slack_exMid {pts : List (V3 κ)} {R' : RootRec} {k : ℕ} {σ : ℕ → ℕ}
    (hk : R'.contacts.length = k) (c : ℕ × ℕ × ℕ) :
    ((exMid R' k σ).sys pts).slack c = (R'.sys pts).slack c := by
  simp [Sys.slack, RootRec.sys, exMid, hk]

/-- **A link that exchanges contacts and checks gives its roots the same scale.** -/
theorem scale_eq_of_exLinkOkWith {pts : List (V3 κ)} {R R' : RootRec} {E : ExLinkRec}
    {H G : Iso κ} (hl : exLinkOkWith pts (R.kraw pts).zballs R R' E H G = true)
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
  simp only [exLinkOkWith, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true] at hl
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hH, hG⟩, hcen⟩, hk⟩, hcb⟩, hc1⟩, hc2⟩, hbox⟩, hT⟩, hQ⟩, hmu⟩ := hl
  set k := R.contacts.length with hkdef
  set S := R.sys pts with hS
  set S' := R'.sys pts with hS'
  set z := (R.kraw pts).env (basisPar κ) y with hz
  set D := linkD R R' H G with hD
  set P := linkPose D H G with hP
  set cst := (cstK H G).map Exact.re with hcst
  set σ : ℕ → ℕ := fun i ↦ E.L.sigma.getD i 0 with hσ
  set fl : ℕ → Bool := fun i ↦ E.L.flip.getD i false with hfl
  set an : ℕ → Bool := fun i ↦ E.L.anti.getD i false with han
  set R'' := exMid R' k σ with hR''
  set S'' := R''.sys pts with hS''
  have hn : S.n = nx R.cen + 1 + k := rfl
  have hn' : S'.n = S.n := by
    change nx R'.cen + 1 + R'.contacts.length = nx R.cen + 1 + k
    rw [hcen, hk]
  have hk'' : R''.contacts.length = k := by simp [hR'', exMid]
  have h5 := five_le_nx R.cen
  set Y := linkY (R.kraw pts).zballs S.n (cstK H G) with hYdef
  have hY := linkY_encl (cK := cstK H G) hp hy h0
  have hHo := holds_link (D := D) hH hG rfl z S.n
  have hvert : ∀ v, vertOf z S.V v = Exact.reV (Exact.pt pts v) := RootRec.vertOf_env y
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
  have hcon'' : ∀ i < k, S''.con i = exImg R' k σ i := fun i hi ↦ by
    simp [Sys.con, hS'', RootRec.sys, hR'', exMid, List.getD_eq_getElem?_getD, hi]
  have LH : LinkHyp S S'' D P id id fl an z cst :=
    { valid := linkPose_valid hH hG rfl
      cen := rfl
      cen' := hcen
      view := rfl
      rot := rfl
      view' := rfl
      rot' := rfl
      k := hk''
      V := by
        change vertsE (nx R'.cen + 1 + R''.contacts.length) pts =
          vertsE (nx R.cen + 1 + R.contacts.length) pts
        rw [hcen, hk'']
      perm := fun i hi ↦ ⟨hi, rfl⟩
      perm' := fun j hj ↦ ⟨hj, rfl⟩
      cb := fun hc ↦ by
        rcases hcb with h | ⟨hb, hc'⟩
        · have h' : R.cen = true := hc
          rw [h] at h'
          exact absurd h' (by decide)
        · refine ⟨?_, ?_⟩
          · simp [hP, linkPose, Iso.br, Exact.reV_eq_zero_of_isZeroV hb]
          · simp [hP, linkPose, Iso.br, Exact.reV_eq_zero_of_isZeroV hc']
      anti := fun i hi ha ↦ by
        rcases (hc1 i hi).1.1 with h | h
        · have ha' : E.L.anti.getD i false = true := ha
          have h' : E.L.anti.getD i false = false := by rw [List.getD_eq_getElem?_getD]; exact h
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
        rw [e, show S''.con (id i) = exImg R' k σ i from hcon'' i hi]
        exact corr_of_contactMaps hH hG (hc1 i hi).1.2
      holds := hHo
      hw := hw
      hq := hq }
  obtain ⟨hgs, hst⟩ := LH.zero_transport (fun i hi ↦ Sys.g_zero (R.kraw_eqs pts) h0 hi)
    (fun v hv ↦ Sys.stat_zero (R.kraw_eqs pts) h0 hv)
  set w := imageP D S.n id fl cst z with hwdef
  -- the image's parameters
  have hwpar : ∀ j, w (S.n + j) = basisPar κ j := fun j ↦ by
    rw [hwdef, imageP_ge (by omega), hz, ← Sys.n_eq (R.kraw_eqs pts), Kraw.env_par]
  have hwb : ∀ j < ExactBasis.dim κ, w (S'.n + j) = ExactBasis.basis κ j := fun j hj ↦ by
    rw [hn', hwpar j]
    simp [basisPar, hj]
  -- the target's slacks vanish at the image
  have hgS'' : ∀ i < k, (S''.g i).eval w = 0 := fun i hi ↦ hgs i (by rw [LH.k]; exact hi)
  have hslack : ∀ j < k, (S'.g j).eval w = 0 := by
    intro j hj
    rcases hc2 j hj with ⟨i, hi, hij⟩ | ⟨b, hb, ⟨⟨⟨hbj, hid⟩, hban⟩, hbm⟩⟩
    · have e : S''.g i = S'.g j := by
        change S''.slack (S''.con i) = S'.slack (S'.con j)
        rw [hcon'' i hi]
        have e2 : exImg R' k σ i = R'.contacts.getD j (0, 0, 0) := by
          simp only [exImg, hσ, hij, hj, ↓reduceIte]
        rw [e2, hS'', hR'', slack_exMid hk]
        rfl
      rw [← e]
      exact hgS'' i hi
    · have hcorr : Corr P (vertOf z S.V) (idAt R b.1).con (R'.contacts.getD j (0, 0, 0)) b.2.2.1
          b.2.2.2 := by
        have e : vertOf z S.V = fun v ↦ Exact.reV (Exact.pt pts v) := funext hvert
        rw [e]
        exact corr_of_contactMaps hH hG hbm
      have ha : b.2.2.2 = true → D.cen = true := fun h ↦ by
        rcases hban with h' | h'
        · rw [h] at h'
          exact absurd h' (by decide)
        · exact h'
      have e1 := LH.slack_img_corr hcorr ha
      rw [Sys.slack_zero_of_idOk (R.kraw_eqs pts) hp hy h0 hid, mul_zero] at e1
      have e : S'.g j = S''.slack (R'.contacts.getD j (0, 0, 0)) := by
        rw [hS'', hR'', slack_exMid hk]
        rfl
      rw [e, ← hbj]
      rw [hbj]
      exact e1
  -- the balls of the image, of the `q_ij` and of the `μ_j`
  have hn0 : (R.kraw pts).n = S.n := Sys.n_eq (R.kraw_eqs pts)
  have hTe : ∀ u < S.n, ((exT (exND Y D S.n fl) (R'.s + 64)).getD u (Ball.ofInt 0)).Encl (w u) :=
    fun u hu ↦ by
      have := (exT_encl hY hT hu).1
      rwa [hwdef, imageP_lt hu]
  have hWe : ∀ u, (exW (exT (exND Y D S.n fl) (R'.s + 64)) S.n (R.kraw pts).zballs u).Encl (w u) :=
    exW_encl hTe fun u hu ↦ by
      have := (R.kraw pts).encl_zballs hp hy h0 u
      rwa [hwdef, imageP_ge hu]
  set W := exW (exT (exND Y D S.n fl) (R'.s + 64)) S.n (R.kraw pts).zballs with hWdef
  have hQe : ∀ i < k, (k ≤ σ i → (idAt R' (σ i - k)).D.eval w ≠ 0) ∧
      ∀ j < k, (exQ R' k σ W (R'.s + 64) i j).Encl (exq R' k σ w i j) :=
    fun i hi ↦ exQ_encl hWe (hQ i hi)
  set q := exq R' k σ w with hqdef
  set μ : ℕ → ℝ := fun j ↦ ∑ i ∈ range k, w (nx R.cen + 1 + i) * q i j with hμ
  set w2 : ℕ → ℝ := fun u ↦ if nx R.cen < u ∧ u < S.n then μ (u - (nx R.cen + 1)) else w u
    with hw2
  have hw2lo : ∀ u ≤ nx R.cen, w2 u = w u := fun u hu ↦ by
    simp only [hw2, show ¬ (nx R.cen < u ∧ u < S.n) by omega, ↓reduceIte]
  have hw2hi : ∀ u, S.n ≤ u → w2 u = w u := fun u hu ↦ by
    simp only [hw2, show ¬ (nx R.cen < u ∧ u < S.n) by omega, ↓reduceIte]
  have hw2b : ∀ j < ExactBasis.dim κ, w2 (S'.n + j) = ExactBasis.basis κ j := fun j hj ↦ by
    rw [hw2hi _ (by omega)]
    exact hwb j hj
  have hcen' : nx R'.cen = nx R.cen := by rw [hcen]
  -- the target's slacks at `w2`, and their derivatives
  have hg2 : ∀ j < k, (S'.g j).eval w2 = (S'.g j).eval w := fun j _ ↦
    eval_slackE_congr (fun u hu ↦ hw2lo u (by rw [← hcen']; exact hu)) hw2b hwb _ _ _
  have hd2 : ∀ j < k, ∀ v < S'.nv, (deriv v (S'.g j)).eval w2 = (deriv v (S'.g j)).eval w :=
    fun j _ v hv ↦ eval_deriv_slackE_congr (fun u hu ↦ hw2lo u (by rw [← hcen']; exact hu)) hw2b
      hwb (by change v < nx R'.cen + 1 at hv; change v ≤ nx R'.cen; omega)
      (by change nx R'.cen < nx R'.cen + 1 + R'.contacts.length; omega) _ _ _
  -- an identity's derivative gives the `q_ij`
  have hS''g : ∀ i < k, S''.g i = S'.slack (exImg R' k σ i) := fun i hi ↦ by
    change S''.slack (S''.con i) = _
    rw [hcon'' i hi, hS'', hR'', slack_exMid hk]
  have hqrel : ∀ i < k, ∀ v < S'.nv, (deriv v (S''.g i)).eval w =
      ∑ j ∈ range k, q i j * (deriv v (S'.g j)).eval w := by
    intro i hi v hv
    rw [hS''g i hi]
    by_cases hs : σ i < k
    · have e : exImg R' k σ i = R'.contacts.getD (σ i) (0, 0, 0) := by
        simp only [exImg, hs, ↓reduceIte]
      rw [e]
      simp only [hqdef, exq, hs, ↓reduceIte, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq (range k) (σ i), ite_eq_left (mem_range.mpr hs)]
      rfl
    · have e : exImg R' k σ i = (idAt R' (σ i - k)).con := by simp only [exImg, hs, ↓reduceIte]
      rw [e]
      have hemp : (toSP κ S'.n (S'.idE (idAt R' (σ i - k)))).terms.isEmpty = true := by
        rcases (hc1 i hi).2 with h | h
        · exact absurd h hs
        · exact h
      have hc : (S'.slack (idAt R' (σ i - k)).con).eval w = 0 := by
        rw [← e, ← hS''g i hi]
        exact hgS'' i hi
      have hid := Sys.id_deriv hemp (fun j ↦ by rw [hn']; exact hwpar j)
        (show v < S'.n by change v < nx R'.cen + 1 at hv; rw [hn']; omega)
        (fun j hj ↦ hslack j (by rw [← hk]; exact hj)) hc
      have hD0 := (hQe i hi).1 (by omega)
      rw [show S'.k = k from hk] at hid
      simp only [hqdef, exq, hs, ↓reduceIte]
      have e3 : (deriv v (S'.slack (idAt R' (σ i - k)).con)).eval w =
          ((idAt R' (σ i - k)).D.eval w)⁻¹ * ∑ j ∈ range k,
            ((idAt R' (σ i - k)).p.getD j (.const 0)).eval w * (deriv v (S'.g j)).eval w := by
        rw [← hid]
        field_simp
      rw [e3, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      ring
  -- the target's stationarity at `w2`
  have hst2 : ∀ v < S'.nv, ∑ j ∈ range S'.k, (mE S'.cen j).eval w2 * (deriv v (S'.g j)).eval w2 =
      ((if v = nx S'.cen then 1 else 0 : ℤ) : ℝ) := by
    intro v hv
    rw [show S'.k = k from hk]
    have e : ∀ j ∈ range k, (mE S'.cen j).eval w2 * (deriv v (S'.g j)).eval w2 =
        μ j * (deriv v (S'.g j)).eval w := by
      intro j hj
      have hj' := mem_range.mp hj
      rw [hd2 j hj' v hv]
      congr 1
      simp only [mE, Expr.eval_var, hw2]
      change (if nx R.cen < nx R'.cen + 1 + j ∧ nx R'.cen + 1 + j < S.n then
        μ (nx R'.cen + 1 + j - (nx R.cen + 1)) else w (nx R'.cen + 1 + j)) = μ j
      rw [ite_eq_left (by rw [hcen']; omega), hcen']
      congr 1
      omega
    rw [Finset.sum_congr rfl e]
    have hst' := hst v (by change v < nx R''.cen + 1; change v < nx R'.cen + 1 at hv; exact hv)
    rw [show S''.k = k from hk''] at hst'
    have hm : ∀ i ∈ range k, (mE S''.cen i).eval w * (deriv v (S''.g i)).eval w =
        w (nx R.cen + 1 + i) * (deriv v (S''.g i)).eval w := fun i _ ↦ by
      simp only [mE, Expr.eval_var]
      rw [show S''.cen = R.cen from hcen]
    rw [Finset.sum_congr rfl hm] at hst'
    rw [show nx S'.cen = nx S''.cen from rfl]
    exact stat_exchange hst' fun i hi ↦ hqrel i hi v hv
  -- the point of the target
  have hnK : (R'.kraw pts).n = S.n := (Sys.n_eq (R'.kraw_eqs pts)).trans hn'
  set y' : Fin (R'.kraw pts).n → ℝ := fun j ↦ w2 j with hy'
  have henv : (R'.kraw pts).env (basisPar κ) y' = w2 := by
    funext i
    simp only [Kraw.env]
    split_ifs with hi
    · rfl
    · rw [hw2hi i (by omega)]
      have := hwpar (i - S.n)
      rw [show S.n + (i - S.n) = i by omega] at this
      rw [this, hnK]
  have hF : (R'.kraw pts).F (basisPar κ) y' = 0 := by
    funext e
    change ((R'.kraw pts).eqs.getD e (.const 0)).eval ((R'.kraw pts).env (basisPar κ) y') = 0
    rw [henv, R'.kraw_eqs pts]
    have he : (e : ℕ) < S'.nv + S'.k := by
      have h1 := e.isLt
      have h2 : (R'.kraw pts).n = S'.nv + S'.k := Sys.n_eq (R'.kraw_eqs pts)
      omega
    by_cases hek : (e : ℕ) < S'.k
    · rw [S'.getD_eqs_g hek, hg2 e (by rw [← hk]; exact hek)]
      exact hslack e (by rw [← hk]; exact hek)
    · obtain ⟨v, hv⟩ : ∃ v, (e : ℕ) = S'.k + v := ⟨e - S'.k, by omega⟩
      rw [hv, S'.getD_eqs_stat (by omega), Sys.stat]
      change (sumE S'.k fun i ↦ .mul (mE S'.cen i) (deriv v (S'.g i))).eval w2 - _ = 0
      rw [eval_sumE, sub_eq_zero]
      exact hst2 v (by omega)
  have hbox' : y' ∈ (R'.kraw pts).box := by
    intro i
    have hi : (i : ℕ) < S.n := by have := i.2; omega
    by_cases hil : (i : ℕ) ≤ nx R.cen
    · have hb := (quotIn_sound hY (hbox i (by omega))).2
      have e : y' i = coordV D S.n id fl (withC z S.n cst) i := by
        simp only [hy', hw2lo i hil, hwdef, imageP_lt hi]
      rw [e]
      exact hb
    · obtain ⟨j, hj⟩ : ∃ j, (i : ℕ) = nx R.cen + 1 + j := ⟨i - (nx R.cen + 1), by omega⟩
      have hjk : j < k := by omega
      have hmu' := hmu j hjk
      have hY' : ∀ _ : ℕ, (exMu W (exQ R' k σ W (R'.s + 64)) k (nx R.cen + 1) j).Encl
          ((fun _ ↦ μ j) 0) := fun _ ↦ exMu_encl hWe fun i hi ↦ (hQe i hi).2 j hjk
      have hb := (quotIn_sound hY' hmu').2
      simp only [Expr.eval_var, Expr.eval_const, Int.cast_one, div_one] at hb
      have e : y' i = μ j := by
        simp only [hy', hw2, hj]
        rw [ite_eq_left (by omega)]
        congr 1
        omega
      rw [e]
      change |μ j - (R'.c.getD i 0 : ℝ) / 2 ^ R'.s| ≤ (R'.ρ.getD i 0 : ℝ) / 2 ^ R'.s
      rw [hj]
      exact hb
  -- the scales
  have hyy := huniq₂ y' ⟨hbox', hF⟩
  rw [hsc, hsc', ← hyy, henv, hw2lo _ (by rw [hcen']), hwdef, hcen']
  exact (LH.imgl).symm

end Sound

/-! ### Links in groups -/

section Groups

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The checks of links that may exchange contacts from `R` to the roots of `targets`, at the
balls of `R`'s zero, computed once. -/
def exLinksOk (pts : List (V3 κ)) (R : RootRec) (targets : List (RootRec × ExLinkRec)) : Bool :=
  let Z := (R.kraw pts).zballs
  targets.all fun t ↦ exLinkOkZ pts Z R t.1 t.2

/-- `Root.linkGroupsOk` for links that may exchange contacts. -/
def exGroupsOk (pts : List (V3 κ)) (A : List RootRec) (R : RootRec) :
    List ℕ → List (ℕ × List (ℕ × ExLinkRec)) → Bool
  | _, [] => true
  | known, (i, ts) :: gs => known.contains i &&
      exLinksOk pts (A.getD i R) (ts.map fun t ↦ (A.getD t.1 R, t.2)) &&
      exGroupsOk pts A R (ts.map Prod.fst ++ known) gs

variable [RootBasis κ]

theorem scale_eq_of_exLinksOk {pts : List (V3 κ)} {R : RootRec}
    {targets : List (RootRec × ExLinkRec)} (h : exLinksOk pts R targets = true)
    (hR : R.ok pts = true) (hok : ∀ t ∈ targets, t.1.ok pts = true) :
    ∀ t ∈ targets, t.1.scale pts = R.scale pts := by
  intro t ht
  have h1 := List.all_eq_true.mp h t ht
  simp only [exLinkOkZ] at h1
  split at h1
  · exact (scale_eq_of_exLinkOkWith h1 hR (hok t ht)).symm
  · exact absurd h1 Bool.false_ne_true

/-- **Links in groups give one scale** to the roots they reach. -/
theorem scale_of_exGroupsOk {pts : List (V3 κ)} {A : List RootRec} {R : RootRec}
    (hok : ∀ i, (A.getD i R).ok pts = true) {c : ℝ} :
    ∀ {known : List ℕ} {gs : List (ℕ × List (ℕ × ExLinkRec))},
      exGroupsOk pts A R known gs = true → (∀ i ∈ known, (A.getD i R).scale pts = c) →
        ∀ i ∈ reached known gs, (A.getD i R).scale pts = c
  | known, [], _, hk => by simpa [reached] using hk
  | known, (i, ts) :: gs, h, hk => by
    simp only [exGroupsOk, Bool.and_eq_true, List.contains_iff_mem] at h
    obtain ⟨⟨hi, hl⟩, hgs⟩ := h
    have hts : ∀ t ∈ ts, (A.getD t.1 R).scale pts = c := by
      intro t ht
      have := scale_eq_of_exLinksOk hl (hok i) (fun t' ht' ↦ by
        obtain ⟨u, -, rfl⟩ := List.mem_map.mp ht'
        exact hok u.1) _ (List.mem_map.mpr ⟨t, ht, rfl⟩)
      rw [this, hk i hi]
    have hk' : ∀ j ∈ ts.map Prod.fst ++ known, (A.getD j R).scale pts = c := by
      intro j hj
      rcases List.mem_append.mp hj with hj | hj
      · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hj
        exact hts t ht
      · exact hk j hj
    have ih := scale_of_exGroupsOk hok hgs hk'
    intro j hj
    simp only [reached, List.flatMap_cons, List.mem_append] at hj
    rcases hj with hj | hj | hj
    · exact hk j hj
    · exact hk' j (List.mem_append_left _ hj)
    · exact ih j (List.mem_append_right _ hj)

/-- **Representatives by links that may exchange contacts**: `Root.isRootEq_of_links` with
`exGroupsOk`. -/
theorem isRootEq_of_exLinks {pts : List (V3 κ)} {F : ParData} (hF : F.Spec κ) (hU : F.Unique)
    (hF1 : F.box.length = 1) {R : RootRec} {Rs : List RootRec} {N : ℝ}
    (hok : ∀ R' ∈ R :: Rs, R'.ok pts = true) {Ss : List PolynomialSystem}
    (hN : PolynomialSystem.IsRootMax Ss N) (T : List ℕ)
    (hSs : List.Forall₂ (fun i S ↦ IsSystemOf pts F ((R :: Rs).getD i R) S) T Ss)
    (gs : List (ℕ × List (ℕ × ExLinkRec))) (hl : exGroupsOk pts (R :: Rs) R [0] gs = true)
    (hT : T.all (fun i ↦ (reached [0] gs).contains i) = true)
    {Reps : List PolynomialSystem} (hne : Reps ≠ []) (hsub : ∀ S ∈ Reps, S ∈ Ss) :
    PolynomialSystem.IsRootEq Reps N := by
  have hok' : ∀ i, ((R :: Rs).getD i R).ok pts = true := fun i ↦ hok _ (getD_mem_cons R Rs i)
  have hsc := scale_of_exGroupsOk hok' (c := R.scale pts) hl (fun i hi ↦ by
    rw [List.mem_singleton.mp hi]; rfl)
  refine PolynomialSystem.IsRootMax.isRootEq hN (c := R.scale pts) (fun S hS ↦ ?_) hne hsub
  obtain ⟨i, hi, h⟩ := exists_left_of_forall₂' hSs S hS
  have hiT := List.all_eq_true.mp hT i hi
  rw [List.contains_iff_mem] at hiT
  rw [h.scales_eq_scale hF hU hF1 (hok' i), hsc i hiT]

end Groups

end Nieuwland.Root
