import Modules.Check.Leaf.FullDim
import Modules.Nieuwland.Cover
import Modules.Root.Identity
import Modules.Root.Leaf

/-!
# Exact Nieuwland numbers in root form

A root-form certificate gives the Nieuwland number of a solid as a coordinate of the zero of a
polynomial system: at an optimal pose the plug touches the hole at contacts `(a, b, k)`, and the
pose, the scale `l` and the multipliers `m` are the zero of the contacts' slacks and of the
stationarity equations (`Sys.eqs`, `Modules/Root/System.lean`). This file assembles the checks of
the root records with a far field (`Modules/Nieuwland/Cover.lean`).

A root record (`RootRec`) holds the system's charts and contacts, the data of Krawczyk's test
(`Modules/Root/Krawczyk.lean`), a weak fit (`Modules/Root/WeakFit.lean`) and a touch leaf
(`Modules/Root/Leaf.lean`). Over points `pts` with coordinates in a field with a basis, the
vertices are expressions in the basis values, the parameters of the system; their balls are tested
by `RootBasis.parCheck` (`1` exactly, `√d` by squares, the powers of a number field's `α` by its
enclosure and by products).

* `RootRec.ok`: the parameters' balls, Krawczyk's test (one zero in the box), in centred mode the
  antipodes (the solid is centrally symmetric), a nonnegative scale, a weak fit at the zero (the
  scale is at most the Nieuwland number) and the touch leaf (no fit at the root's scale in the
  leaf's box; in general mode with the translation's confinement).
* `RootRec.scale`: the scale coordinate of the zero. `certOk`: every root's checks, and the far
  field's scale `θ` at most the first root's.

`nieuwland_eq_of_certOk`: with a far field settled at `θ` outside the leaves' boxes, the Nieuwland
number is the largest of the roots' scales (`topScale`; roots of equal scales need no order);
`nieuwland_eq_of_certOk_one` states it with the zero for one root, and
`nieuwland_mem_Icc_of_certOk` gives its decimals from the roots' balls.

Both modes of the certificates: centred (a centrally symmetric solid, no translation) and general
(the translation is an unknown of the system).
-/

open Nieuwland.Check Finset Metric

namespace Nieuwland.Root

/-! ### Balls of the basis values -/

/-- The test that `b` is the ball of `1`. -/
def oneOk (b : Ball) : Bool :=
  decide (b.m = 1) && decide (b.r = 0) && decide (b.s = 0)

theorem encl_one {b : Ball} (h : oneOk b = true) : b.Encl 1 := by
  obtain ⟨m, r, s⟩ := b
  simp only [oneOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  simp [Ball.Encl]

/-- The test that `b` is a ball of `√d`: `0 ≤ m - r` and `(m - r)² ≤ 4^s d ≤ (m + r)²`. -/
def sqrtOk (d : ℕ) (b : Ball) : Bool :=
  decide (0 ≤ b.m - b.r) && decide ((b.m - b.r) ^ 2 ≤ (d : ℤ) * 4 ^ b.s) &&
    decide ((d : ℤ) * 4 ^ b.s ≤ (b.m + b.r) ^ 2)

theorem encl_sqrt {d : ℕ} {b : Ball} (h : sqrtOk d b = true) : b.Encl √(d : ℝ) := by
  simp only [sqrtOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have h4 : ((2 : ℝ) ^ b.s) ^ 2 = 4 ^ b.s := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have ht0 : 0 ≤ (2 : ℝ) ^ b.s * √(d : ℝ) := by positivity
  have ht2 : ((2 : ℝ) ^ b.s * √(d : ℝ)) ^ 2 = (d : ℝ) * 4 ^ b.s := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), h4, mul_comm]
  have hr : (0 : ℝ) ≤ b.r := Nat.cast_nonneg _
  have h0' : (0 : ℝ) ≤ (b.m : ℝ) - b.r := by exact_mod_cast h0
  have h1' : ((b.m : ℝ) - b.r) ^ 2 ≤ ((2 : ℝ) ^ b.s * √(d : ℝ)) ^ 2 := by
    rw [ht2]
    exact_mod_cast h1
  have h2' : ((2 : ℝ) ^ b.s * √(d : ℝ)) ^ 2 ≤ ((b.m : ℝ) + b.r) ^ 2 := by
    rw [ht2]
    exact_mod_cast h2
  have hl := (sq_le_sq₀ h0' ht0).mp h1'
  have hu := (sq_le_sq₀ ht0 (by linarith)).mp h2'
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Fields with a test of balls of their basis values, the parameters of a root's system. -/
class RootBasis (κ : Type) [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] where
  /-- The test of the balls of the basis values. -/
  parCheck : List Ball → Bool
  parCheck_sound : ∀ par, parCheck par = true →
    ∀ j, (par.getD j (Ball.ofInt 0)).Encl (basisPar κ j)

/-- Balls of the basis values are balls of the parameters, for a list. -/
theorem encl_basisPar {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] {par : List Ball}
    (hlen : par.length = ExactBasis.dim κ)
    (hb : ∀ j < ExactBasis.dim κ, (par.getD j (Ball.ofInt 0)).Encl (ExactBasis.basis κ j)) :
    ∀ j, (par.getD j (Ball.ofInt 0)).Encl (basisPar κ j) :=
  parOk_of_basis (K := ⟨[], par, [], [], 0, [], 0, [], 0⟩) hlen hb

instance : RootBasis ℤ where
  parCheck par := decide (par.length = 1) && oneOk (par.getD 0 (Ball.ofInt 0))
  parCheck_sound par h := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    refine encl_basisPar h.1 fun j hj ↦ ?_
    obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
    have h1 : ExactBasis.basis ℤ 0 = 1 := Erased.out_mk _
    rw [h1]
    exact encl_one h.2

instance {d : ℕ} : RootBasis (ZSqrt d) where
  parCheck par := decide (par.length = 2) && oneOk (par.getD 0 (Ball.ofInt 0)) &&
    sqrtOk d (par.getD 1 (Ball.ofInt 0))
  parCheck_sound par h := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    refine encl_basisPar h.1.1 fun j hj ↦ ?_
    rw [ZSqrt.basis_eq]
    rcases (show j = 0 ∨ j = 1 from by
      have : j < 2 := hj
      omega) with rfl | rfl
    · simpa [ZSqrt.basisVal] using encl_one h.1.2
    · simpa [ZSqrt.basisVal] using encl_sqrt h.2

/-- The test that the ball `b` contains the interval `[lo / D, hi / D]`. -/
def hasIcc (b : Ball) (lo hi : ℤ) (D : ℕ) : Bool :=
  decide ((b.m - b.r) * D ≤ lo * 2 ^ b.s) && decide (hi * 2 ^ b.s ≤ (b.m + b.r) * D)

theorem encl_of_hasIcc {b : Ball} {lo hi : ℤ} {D : ℕ} (hD : 0 < D) {x : ℝ}
    (h1 : (lo : ℝ) / D ≤ x) (h2 : x ≤ (hi : ℝ) / D) (h : hasIcc b lo hi D = true) : b.Encl x := by
  simp only [hasIcc, Bool.and_eq_true, decide_eq_true_eq] at h
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hs : (0 : ℝ) < 2 ^ b.s := by positivity
  have e1 : ((b.m : ℝ) - b.r) * D ≤ lo * 2 ^ b.s := by exact_mod_cast h.1
  have e2 : (hi : ℝ) * 2 ^ b.s ≤ ((b.m : ℝ) + b.r) * D := by exact_mod_cast h.2
  rw [div_le_iff₀ hD'] at h1
  rw [le_div_iff₀ hD'] at h2
  refine abs_le.mpr ⟨?_, ?_⟩
  · refine le_of_mul_le_mul_right ?_ hD'
    nlinarith
  · refine le_of_mul_le_mul_right ?_ hD'
    nlinarith

/-- The test that the ball `a` lies in the ball `b`. -/
def ballSub (a b : Ball) : Bool :=
  decide ((b.m - b.r) * 2 ^ a.s ≤ (a.m - a.r) * 2 ^ b.s) &&
    decide ((a.m + a.r) * 2 ^ b.s ≤ (b.m + b.r) * 2 ^ a.s)

theorem encl_of_ballSub {a b : Ball} {x : ℝ} (ha : a.Encl x) (h : ballSub a b = true) :
    b.Encl x := by
  simp only [ballSub, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := abs_le.mp ha
  have ha' : (0 : ℝ) < 2 ^ a.s := by positivity
  have hb' : (0 : ℝ) < 2 ^ b.s := by positivity
  have e1 : ((b.m : ℝ) - b.r) * 2 ^ a.s ≤ ((a.m : ℝ) - a.r) * 2 ^ b.s := by exact_mod_cast h.1
  have e2 : ((a.m : ℝ) + a.r) * 2 ^ b.s ≤ ((b.m : ℝ) + b.r) * 2 ^ a.s := by exact_mod_cast h.2
  refine abs_le.mpr ⟨?_, ?_⟩
  · refine le_of_mul_le_mul_right ?_ ha'
    nlinarith
  · refine le_of_mul_le_mul_right ?_ ha'
    nlinarith

/-- A number field `ℤ[α]`: the ball of `1`, a ball of `α` around the root's enclosure, and for
each further power a ball around the product of the balls of `α` and of the power before. -/
instance {R : Root} : RootBasis (ZTheta R) where
  parCheck par := decide (par.length = R.n) && oneOk (par.getD 0 (Ball.ofInt 0)) &&
    (List.range R.n).all fun j ↦ decide (j = 0) ||
      (if j = 1 then hasIcc (par.getD 1 (Ball.ofInt 0)) R.Xl R.Xh R.D
       else ballSub (par.getD 1 (Ball.ofInt 0) * par.getD (j - 1) (Ball.ofInt 0))
        (par.getD j (Ball.ofInt 0)))
  parCheck_sound par h := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      Bool.or_eq_true] at h
    obtain ⟨⟨hlen, hone⟩, hall⟩ := h
    have hb : ∀ j, ExactBasis.basis (ZTheta R) j = R.α ^ j := fun j ↦ Erased.out_mk _
    refine encl_basisPar hlen fun j hj ↦ ?_
    rw [hb]
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · subst h0
        simpa using encl_one hone
      rcases hall j hj with h0' | hj'
      · omega
      · split_ifs at hj' with h1
        · subst h1
          rw [pow_one]
          exact encl_of_hasIcc R.D_pos R.spec.1 R.spec.2.1 hj'
        · have hj2 : 2 ≤ j := by omega
          have e : R.α ^ j = R.α * R.α ^ (j - 1) := by
            rw [← pow_succ']
            congr 1
            omega
          rw [e]
          have h1' : (par.getD 1 (Ball.ofInt 0)).Encl R.α := by
            have := ih 1 (by omega) (by omega)
            rwa [pow_one] at this
          exact encl_of_ballSub (Ball.encl_mul h1' (ih (j - 1) (by omega) (by omega))) hj'

/-! ### Points, antipodes, scales -/

section Points

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The vertices of the polyhedron of `pts`, by index. -/
theorem mem_ofPoints_iff_pt {pts : List (V3 κ)} {x : Fin 3 → ℝ} :
    x ∈ (Polyhedron.ofPoints pts).vertices ↔
      ∃ v < pts.length, Exact.reV (Exact.pt pts v) = x := by
  rw [Polyhedron.mem_ofPoints]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨v, hv, rfl⟩ := List.mem_iff_getElem.mp hu
    exact ⟨v, hv, by rw [Exact.pt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv]; rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact Polyhedron.mem_ofPoints.mp (Exact.reV_pt_mem hv)

/-- The test of a list of antipodes: point `neg v` is minus point `v`, exactly. -/
def negOk (pts : List (V3 κ)) (neg : List ℕ) : Bool :=
  (List.range pts.length).all fun v ↦
    decide (neg.getD v 0 < pts.length) &&
      Exact.isZeroV ((Exact.pt pts (neg.getD v 0)).add (Exact.pt pts v))

theorem negOk_spec {pts : List (V3 κ)} {neg : List ℕ} (h : negOk pts neg = true) {v : ℕ}
    (hv : v < pts.length) : neg.getD v 0 < pts.length ∧
      Exact.reV (Exact.pt pts (neg.getD v 0)) = -Exact.reV (Exact.pt pts v) := by
  have h' := List.all_eq_true.mp h v (List.mem_range.mpr hv)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
  refine ⟨h'.1, eq_neg_of_add_eq_zero_left ?_⟩
  rw [← Exact.reV_add]
  exact Exact.reV_eq_zero_of_isZeroV h'.2

/-- Points with antipodes: the polyhedron is centrally symmetric. -/
theorem neg_mem_of_negOk {pts : List (V3 κ)} {neg : List ℕ} (h : negOk pts neg = true) :
    ∀ x ∈ (Polyhedron.ofPoints pts).vertices, -x ∈ (Polyhedron.ofPoints pts).vertices := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := mem_ofPoints_iff_pt.mp hx
  obtain ⟨h1, h2⟩ := negOk_spec h hv
  rw [← h2]
  exact Exact.reV_pt_mem h1

/-- The test of `θ ≤ z_il` on the balls `Z` of the variables, the basis values from `nu` on:
the ball of `den z_il - num` is nonnegative. -/
def scaleLe (θ : Scale κ) (nu : ℕ) (Z : List Ball) (il : ℕ) : Bool :=
  decide (0 < θ.den) &&
    (Ball.ofInt θ.den * Kraw.zball Z il -
      bval (Kraw.zball Z) (elemE nu (ExactBasis.dim κ) (ExactBasis.coords θ.num))).isNonneg

theorem re_le_of_scaleLe {θ : Scale κ} {nu : ℕ} {Z : List Ball} {il : ℕ} {z : ℕ → ℝ}
    (hZ : ∀ i, (Kraw.zball Z i).Encl (z i))
    (hz : ∀ j < ExactBasis.dim κ, z (nu + j) = ExactBasis.basis κ j)
    (h : scaleLe θ nu Z il = true) : θ.re ≤ z il := by
  simp only [scaleLe, Bool.and_eq_true, decide_eq_true_eq] at h
  have hd : (0 : ℝ) < θ.den := by exact_mod_cast h.1
  have e := Ball.nonneg_sound (Ball.encl_sub (Ball.encl_mul (Ball.encl_ofInt θ.den) (hZ il))
    (encl_bval hZ (elemE nu (ExactBasis.dim κ) (ExactBasis.coords θ.num)))) h.2
  rw [eval_elemE z nu hz] at e
  rw [Scale.re, div_le_iff₀ hd]
  push_cast at e
  linarith

end Points

/-! ### Root records -/

/-- `y` is the zero of the system in the box of the test, and the only one. -/
def Kraw.IsZero (K : Kraw) (p : ℕ → ℝ) (y : Fin K.n → ℝ) : Prop :=
  (y ∈ K.box ∧ K.F p y = 0) ∧
    ∀ y', y' ∈ K.box ∧ K.F p y' = 0 → y' = y

/-- A root record of a certificate: the system's mode, charts and contacts, the data of
Krawczyk's test (balls of the parameters, centre, half-width, preconditioner and its inverse),
the weak fit and the touch leaf. -/
structure RootRec where
  /-- Centred mode. -/
  cen : Bool
  /-- The view chart. -/
  view : Fin 3
  /-- The rotation chart. -/
  rot : Fin 4
  /-- The contacts. -/
  contacts : List (ℕ × ℕ × ℕ)
  /-- Centred mode: the antipode of every point. -/
  neg : List ℕ
  /-- Balls of the parameters, the basis values of the field. -/
  par : List Ball
  /-- The centre, times `2^s`. -/
  c : List ℤ
  /-- The half-widths, one per unknown, times `2^s`. -/
  ρ : List ℕ
  /-- The scale of the box. -/
  s : ℕ
  /-- The preconditioner, times `2^cs`. -/
  C : List (List ℤ)
  /-- The scale of the preconditioner. -/
  cs : ℕ
  /-- `C D = d` (as integer matrices). -/
  D : List (List ℤ)
  /-- The positive integer `d`. -/
  d : ℕ
  /-- The weak fit. -/
  W : WeakRec
  /-- The touch leaf. -/
  L : LeafRec

namespace RootRec

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The root's system over the points `pts`: the vertices are expressions in the basis values,
the variables after the unknowns. -/
def sys (R : RootRec) (pts : List (V3 κ)) : Sys :=
  ⟨R.cen, R.view, R.rot, R.contacts, vertsE (nx R.cen + 1 + R.contacts.length) pts⟩

/-- The data of Krawczyk's test at the root. -/
def kraw (R : RootRec) (pts : List (V3 κ)) : Kraw :=
  ⟨(R.sys pts).eqs, R.par, R.c, R.ρ, R.s, R.C, R.cs, R.D, R.d⟩

theorem kraw_eqs (R : RootRec) (pts : List (V3 κ)) : (R.kraw pts).eqs = (R.sys pts).eqs := rfl

variable {R : RootRec} {pts : List (V3 κ)}

theorem env_basis (y : Fin (R.kraw pts).n → ℝ) {j : ℕ} (hj : j < ExactBasis.dim κ) :
    (R.kraw pts).env (basisPar κ) y ((R.sys pts).n + j) = ExactBasis.basis κ j := by
  rw [← Sys.n_eq (R.kraw_eqs pts), Kraw.env_par]
  simp only [basisPar, hj, ↓reduceIte]

/-- The vertices at a point of the system are the points. -/
theorem vertOf_env (y : Fin (R.kraw pts).n → ℝ) (v : ℕ) :
    vertOf ((R.kraw pts).env (basisPar κ) y) (R.sys pts).V v = Exact.reV (Exact.pt pts v) :=
  vertOf_vertsE ((R.kraw pts).env (basisPar κ) y) (R.sys pts).n (fun _ hj ↦ env_basis y hj) pts v

/-- The vertices do not depend on the pose. -/
theorem vertOf_fix (y : Fin (R.kraw pts).n → ℝ) {z : ℕ → ℝ}
    (hz : ∀ i, nx (R.sys pts).cen ≤ i → z i = (R.kraw pts).env (basisPar κ) y i) (v : ℕ) :
    vertOf z (R.sys pts).V v = vertOf ((R.kraw pts).env (basisPar κ) y) (R.sys pts).V v := by
  rw [vertOf_env]
  refine vertOf_vertsE z (R.sys pts).n (fun j hj ↦ ?_) pts v
  have hle : nx (R.sys pts).cen ≤ (R.sys pts).n + j := by
    change nx R.cen ≤ nx R.cen + 1 + R.contacts.length + j
    omega
  rw [hz _ hle, env_basis y hj]

theorem mem_vertices (y : Fin (R.kraw pts).n → ℝ) (x : Fin 3 → ℝ) :
    x ∈ (Polyhedron.ofPoints pts).vertices ↔
      ∃ v < pts.length, vertOf ((R.kraw pts).env (basisPar κ) y) (R.sys pts).V v = x := by
  simp only [vertOf_env]
  exact mem_ofPoints_iff_pt

variable [RootBasis κ]

theorem parOk (h : RootBasis.parCheck κ R.par = true) : (R.kraw pts).ParOk (basisPar κ) :=
  RootBasis.parCheck_sound R.par h

section Facts

variable {y : Fin (R.kraw pts).n → ℝ}

/-- A weak fit at the root: its scale is at most the Nieuwland number. -/
theorem le_nieuwland (hpar : RootBasis.parCheck κ R.par = true)
    (hW : (R.sys pts).weakOk pts.length (R.kraw pts).zballs R.W
      (Sys.zeroCons κ (R.sys pts) (R.kraw pts).zballs R.W) = true)
    (hdim : (Polyhedron.ofPoints pts).FullDim)
    (hy : y ∈ (R.kraw pts).box)
    (h0 : (R.kraw pts).F (basisPar κ) y = 0) :
    (R.kraw pts).env (basisPar κ) y (nx R.cen) ≤ (Polyhedron.ofPoints pts).nieuwland :=
  Sys.le_nieuwland_of_weakOk (R.kraw_eqs pts) (parOk hpar) hy h0 (mem_vertices y)
    (fun _ hc ↦ Sys.slack_zero_of_mem_zeroCons (R.kraw_eqs pts) (parOk hpar) hy h0 hc) hW hdim

/-- The touch leaf at the root: no fit at the root's scale in the leaf's box. -/
theorem noFitRot (hpar : RootBasis.parCheck κ R.par = true)
    (hneg : R.cen = true → negOk pts R.neg = true)
    (hL : (R.sys pts).leafOk pts.length (R.kraw pts).zballs R.L = true)
    (hS : (R.sys pts).spOk κ R.L = true)
    (hy : y ∈ (R.kraw pts).box)
    (h0 : (R.kraw pts).F (basisPar κ) y = 0) :
    (Polyhedron.ofPoints pts).NoFitRot R.L.B.poses
      ((R.kraw pts).env (basisPar κ) y (nx R.cen) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) :=
  Sys.noFitRot_of_leafOk (R.kraw_eqs pts) (parOk hpar) hy h0 (mem_vertices y)
    (fun _ hz v ↦ vertOf_fix y hz v) (fun hc ↦ neg_mem_of_negOk (hneg hc)) hL
    fun _ hr _ hz ↦ Sys.idE_zero_of_spOk (R.kraw_eqs pts) hS hr hz

/-- The far field's scale is at most the root's. -/
theorem scale_le {θ : Scale κ} (hpar : RootBasis.parCheck κ R.par = true)
    (hθ : scaleLe θ (R.sys pts).n (R.kraw pts).zballs (nx R.cen) = true)
    (hy : y ∈ (R.kraw pts).box)
    (h0 : (R.kraw pts).F (basisPar κ) y = 0) :
    θ.re ≤ (R.kraw pts).env (basisPar κ) y (nx R.cen) :=
  re_le_of_scaleLe ((R.kraw pts).encl_zballs (parOk hpar) hy h0) (fun _ hj ↦ env_basis y hj) hθ

end Facts

/-- The checks of a root record over `pts`: the parameters' balls, Krawczyk's test, in centred
mode the antipodes, a nonnegative scale, the weak fit (with the contacts of its checked
identities), the touch leaf and the identities of its spread. -/
def ok (R : RootRec) (pts : List (V3 κ)) : Bool :=
  let K := R.kraw pts
  let Z := K.zballs
  RootBasis.parCheck κ R.par && K.check && (!R.cen || negOk pts R.neg) &&
    (Kraw.zball Z (nx R.cen)).isNonneg &&
    (R.sys pts).weakOk pts.length Z R.W (Sys.zeroCons κ (R.sys pts) Z R.W) &&
    (R.sys pts).leafOk pts.length Z R.L && (R.sys pts).spOk κ R.L

open Classical in
/-- The scale of a root over `pts`: the scale coordinate of the zero of its system in its box
(`0` if there is none; `ok` gives one, `exists_scale`). -/
noncomputable def scale (R : RootRec) (pts : List (V3 κ)) : ℝ :=
  if h : ∃ y, (R.kraw pts).IsZero (basisPar κ) y then
    (R.kraw pts).env (basisPar κ) (Classical.choose h) (nx R.cen)
  else 0

omit [RootBasis κ] in
theorem scale_eq {y : Fin (R.kraw pts).n → ℝ} (h : (R.kraw pts).IsZero (basisPar κ) y) :
    R.scale pts = (R.kraw pts).env (basisPar κ) y (nx R.cen) := by
  have hex : ∃ y, (R.kraw pts).IsZero (basisPar κ) y := ⟨y, h⟩
  have hc := Classical.choose_spec hex
  simp only [scale, hex, ↓reduceDIte]
  rw [h.2 _ hc.1]

theorem parCheck_of_ok (hok : R.ok pts = true) : RootBasis.parCheck κ R.par = true := by
  simp only [ok, Bool.and_eq_true] at hok
  exact hok.1.1.1.1.1.1

/-- **A root's facts**: its system has one zero in its box; the scale there is nonnegative, at
most the Nieuwland number (the weak fit), admits no fit in the leaf's box (the touch leaf), and
lies in its ball. -/
theorem facts (hok : R.ok pts = true) (hdim : (Polyhedron.ofPoints pts).FullDim) :
    (∃ y, (R.kraw pts).IsZero (basisPar κ) y ∧
      R.scale pts = (R.kraw pts).env (basisPar κ) y (nx R.cen)) ∧
    0 ≤ R.scale pts ∧ R.scale pts ≤ (Polyhedron.ofPoints pts).nieuwland ∧
    (Polyhedron.ofPoints pts).NoFitRot R.L.B.poses
      (R.scale pts • (1 : Matrix (Fin 3) (Fin 3) ℝ)) ∧
    (Kraw.zball (R.kraw pts).zballs (nx R.cen)).Encl (R.scale pts) := by
  simp only [ok, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨hpar, hchk⟩, hneg⟩, hnn⟩, hW⟩, hL⟩, hS⟩ := hok
  obtain ⟨y, ⟨hy, h0⟩, huniq⟩ := (R.kraw pts).existsUnique hchk (parOk hpar)
  have hs := scale_eq (R := R) (pts := pts) (y := y) ⟨⟨hy, h0⟩, huniq⟩
  have e := (R.kraw pts).encl_zballs (parOk hpar) hy h0 (nx R.cen)
  rw [hs]
  have hneg' : R.cen = true → negOk pts R.neg = true := fun hc ↦ by
    simpa [hc] using hneg
  exact ⟨⟨y, ⟨⟨hy, h0⟩, huniq⟩, rfl⟩, Ball.nonneg_sound e hnn, le_nieuwland hpar hW hdim hy h0,
    noFitRot hpar hneg' hL hS hy h0, e⟩

end RootRec

/-! ### The assembly -/

section Assembly

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] [RootBasis κ]

/-- The checks of the root records of a certificate: every root's (`RootRec.ok`), and the far
field's scale `θ` at most the first root's. -/
def certOk (pts : List (V3 κ)) (θ : Scale κ) (R : RootRec) (Rs : List RootRec) : Bool :=
  (R :: Rs).all (·.ok pts) && scaleLe θ (R.sys pts).n (R.kraw pts).zballs (nx R.cen)

/-- The largest of the roots' scales. -/
noncomputable def topScale (pts : List (V3 κ)) (R : RootRec) (Rs : List RootRec) : ℝ :=
  Rs.foldr (fun R' m ↦ max (R'.scale pts) m) (R.scale pts)

omit [RootBasis κ] in
theorem le_topScale (pts : List (V3 κ)) (R : RootRec) (Rs : List RootRec) {R' : RootRec}
    (h : R' ∈ R :: Rs) : R'.scale pts ≤ topScale pts R Rs := by
  induction Rs with
  | nil =>
    obtain rfl : R' = R := by simpa using h
    exact le_rfl
  | cons A As ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact (ih List.mem_cons_self).trans (le_max_right _ _)
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih (List.mem_cons_of_mem _ h)).trans (le_max_right _ _)

omit [RootBasis κ] in
theorem topScale_mem (pts : List (V3 κ)) (R : RootRec) (Rs : List RootRec) :
    ∃ R' ∈ R :: Rs, topScale pts R Rs = R'.scale pts := by
  induction Rs with
  | nil => exact ⟨R, List.mem_cons_self, rfl⟩
  | cons A As ih =>
    obtain ⟨R', hR', h⟩ := ih
    rcases le_total (A.scale pts) (topScale pts R As) with hle | hle
    · refine ⟨R', ?_, (max_eq_right hle).trans h⟩
      rcases List.mem_cons.mp hR' with rfl | hR'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hR')
    · exact ⟨A, List.mem_cons_of_mem _ List.mem_cons_self, max_eq_left hle⟩

theorem ok_of_certOk {pts : List (V3 κ)} {θ : Scale κ} {R : RootRec} {Rs : List RootRec}
    (hok : certOk pts θ R Rs = true) {R' : RootRec} (h : R' ∈ R :: Rs) : R'.ok pts = true := by
  simp only [certOk, Bool.and_eq_true] at hok
  exact List.all_eq_true.mp hok.1 R' h

/-- The zero of a root of a checked certificate, and its scale. -/
theorem exists_scale {pts : List (V3 κ)} {θ : Scale κ} {R : RootRec} {Rs : List RootRec}
    {i j k l : ℕ} (hspan : spanOk pts i j k l = true)
    (hok : certOk pts θ R Rs = true) {R' : RootRec} (h : R' ∈ R :: Rs) :
    ∃ y, (R'.kraw pts).IsZero (basisPar κ) y ∧
      R'.scale pts = (R'.kraw pts).env (basisPar κ) y (nx R'.cen) :=
  (RootRec.facts (ok_of_certOk hok h) (Polyhedron.fullDim_of_spanOk hspan)).1

/-- **Exact Nieuwland numbers in root form.** For `P = a • (polyhedron of pts)`, `a ≠ 0`: a far
field settled at `θ` outside the boxes of the roots' leaves and the checks of the root records
(`certOk`) give the Nieuwland number of `P` as the largest of the roots' scales, each the scale
coordinate of the only zero of the root's system in its box (`exists_scale`). -/
theorem nieuwland_eq_of_certOk [Countable κ] {pts : List (V3 κ)} {D : SymmData κ}
    {i j k l : ℕ} (hspan : spanOk pts i j k l = true) {roots : List ChartBox}
    (hroots : unitsIn roots = true) {claims : List ChartBox} {θ : Scale κ} (hθ : θ.ok = true)
    (h : roots.Forall fun B ↦ ∀ p ∈ B.poses, SettledS pts D θ.re p ∨ ∃ C ∈ claims, p ∈ C.poses)
    {P : Polyhedron} {a : ℝ} (hP : P = (Polyhedron.ofPoints pts).smul a) (ha : a ≠ 0)
    {R : RootRec} {Rs : List RootRec} (hcl : claims = (R :: Rs).map fun R ↦ R.L.B)
    (hok : certOk pts θ R Rs = true) : P.nieuwland = topScale pts R Rs := by
  have hdim := Polyhedron.fullDim_of_spanOk hspan
  have hf : ∀ R' ∈ R :: Rs, _ := fun R' hR' ↦ RootRec.facts (ok_of_certOk hok hR') hdim
  have hle : θ.re ≤ topScale pts R Rs := by
    obtain ⟨⟨y, hy, hs⟩, -⟩ := hf R List.mem_cons_self
    have hsc : scaleLe θ (R.sys pts).n (R.kraw pts).zballs (nx R.cen) = true := by
      simp only [certOk, Bool.and_eq_true] at hok
      exact hok.2
    have h1 := RootRec.scale_le
      (RootRec.parCheck_of_ok (ok_of_certOk hok List.mem_cons_self)) hsc hy.1.1 hy.1.2
    rw [← hs] at h1
    exact h1.trans (le_topScale pts R Rs List.mem_cons_self)
  have hlo : topScale pts R Rs ≤ P.nieuwland := by
    obtain ⟨R', hR', hR⟩ := topScale_mem pts R Rs
    rw [hP, Polyhedron.nieuwland_smul ha, hR]
    exact (hf R' hR').2.2.1
  refine Polyhedron.nieuwland_eq_of_claims hspan hroots (Scale.re_nonneg_of_ok hθ) hle h ?_ hP ha
    hlo
  intro C hC
  rw [hcl, List.mem_map] at hC
  obtain ⟨R', hR', rfl⟩ := hC
  exact Polyhedron.NoFitRot.smul_of_le (hf R' hR').2.2.2.1 (hf R' hR').2.1
    (le_topScale pts R Rs hR')

/-- A certificate with one root: the Nieuwland number is the scale coordinate of the only zero
of the root's system in its box. -/
theorem nieuwland_eq_of_certOk_one [Countable κ] {pts : List (V3 κ)} {D : SymmData κ}
    {i j k l : ℕ} (hspan : spanOk pts i j k l = true) {roots : List ChartBox}
    (hroots : unitsIn roots = true) {claims : List ChartBox} {θ : Scale κ} (hθ : θ.ok = true)
    (h : roots.Forall fun B ↦ ∀ p ∈ B.poses, SettledS pts D θ.re p ∨ ∃ C ∈ claims, p ∈ C.poses)
    {P : Polyhedron} {a : ℝ} (hP : P = (Polyhedron.ofPoints pts).smul a) (ha : a ≠ 0)
    {R : RootRec} (hcl : claims = [R.L.B]) (hok : certOk pts θ R [] = true) :
    ∃ y, (R.kraw pts).IsZero (basisPar κ) y ∧
      P.nieuwland = (R.kraw pts).env (basisPar κ) y (nx R.cen) := by
  obtain ⟨y, hy, hs⟩ := exists_scale hspan hok (R' := R) List.mem_cons_self
  refine ⟨y, hy, ?_⟩
  rw [nieuwland_eq_of_certOk hspan hroots hθ h hP ha (R := R) (Rs := []) hcl hok, ← hs]
  rfl

end Assembly

/-! ### Decimals -/

/-- The test that the ball `b` lies in `[lo / 10^k, hi / 10^k]`. -/
def ballIn (b : Ball) (lo hi : ℤ) (k : ℕ) : Bool :=
  decide (lo * 2 ^ b.s ≤ 10 ^ k * (b.m - b.r)) && decide (10 ^ k * (b.m + b.r) ≤ hi * 2 ^ b.s)

theorem mem_Icc_of_ballIn {b : Ball} {x : ℝ} (h : b.Encl x) {lo hi : ℤ} {k : ℕ}
    (hb : ballIn b lo hi k = true) : x ∈ Set.Icc ((lo : ℝ) / 10 ^ k) ((hi : ℝ) / 10 ^ k) := by
  simp only [ballIn, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨h1, h2⟩ := abs_le.mp h
  have hs : (0 : ℝ) < 2 ^ b.s := by positivity
  have hk : (0 : ℝ) < 10 ^ k := by positivity
  have e1 : (lo : ℝ) * 2 ^ b.s ≤ 10 ^ k * ((b.m : ℝ) - b.r) := by exact_mod_cast hb.1
  have e2 : (10 : ℝ) ^ k * ((b.m : ℝ) + b.r) ≤ hi * 2 ^ b.s := by exact_mod_cast hb.2
  constructor
  · rw [div_le_iff₀ hk]
    refine le_of_mul_le_mul_right ?_ hs
    nlinarith
  · rw [le_div_iff₀ hk]
    refine le_of_mul_le_mul_right ?_ hs
    nlinarith

section Decimals

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] [RootBasis κ]

/-- The test that the balls of the roots' scales lie in `[lo / 10^k, hi / 10^k]`. -/
def ballsIn (pts : List (V3 κ)) (Rs : List RootRec) (lo hi : ℤ) (k : ℕ) : Bool :=
  Rs.all fun R ↦ ballIn (Kraw.zball (R.kraw pts).zballs (nx R.cen)) lo hi k

/-- **The decimals of a root-form Nieuwland number**: the roots' balls in an interval put the
number there. -/
theorem nieuwland_mem_Icc_of_certOk [Countable κ] {pts : List (V3 κ)} {D : SymmData κ}
    {i j k l : ℕ} (hspan : spanOk pts i j k l = true) {roots : List ChartBox}
    (hroots : unitsIn roots = true) {claims : List ChartBox} {θ : Scale κ} (hθ : θ.ok = true)
    (h : roots.Forall fun B ↦ ∀ p ∈ B.poses, SettledS pts D θ.re p ∨ ∃ C ∈ claims, p ∈ C.poses)
    {P : Polyhedron} {a : ℝ} (hP : P = (Polyhedron.ofPoints pts).smul a) (ha : a ≠ 0)
    {R : RootRec} {Rs : List RootRec} (hcl : claims = (R :: Rs).map fun R ↦ R.L.B)
    (hok : certOk pts θ R Rs = true) {lo hi : ℤ} {n : ℕ}
    (hin : ballsIn pts (R :: Rs) lo hi n = true) :
    P.nieuwland ∈ Set.Icc ((lo : ℝ) / 10 ^ n) ((hi : ℝ) / 10 ^ n) := by
  rw [nieuwland_eq_of_certOk hspan hroots hθ h hP ha hcl hok]
  obtain ⟨R', hR', hR⟩ := topScale_mem pts R Rs
  rw [hR]
  exact mem_Icc_of_ballIn
    (RootRec.facts (ok_of_certOk hok hR') (Polyhedron.fullDim_of_spanOk hspan)).2.2.2.2
    (List.all_eq_true.mp hin R' hR')

end Decimals

end Nieuwland.Root
