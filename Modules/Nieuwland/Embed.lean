import Modules.Nieuwland.Exact

/-!
# Exact Nieuwland numbers: a solid over a field below the lift

`Modules/Nieuwland/Exact.lean` lifts integer points. A solid over `ℚ(√d)` has its far field over
`ℤ[√d]` (`ZSqrt d`) and its claims and weak fit over a lift `κE` that holds `√d` and the exact
scale; a solid over a number field `ℚ(α)` has its far field over `ℤ[α]` (`ZTheta R`) likewise.
The lift's points are then the far field's under an embedding, up to a positive factor (each
field has its own common denominator of the coordinates), and this file carries the
certificate's facts across that factor.

* `Polyhedron.fitsAlong_smul_poly_iff`, `Polyhedron.noFitRot_smul_iff`: fits along a direction do
  not change when the polyhedron is scaled.
* `liftOk`, `ofPoints_of_liftOk`: points of `κE` that are those of `κF` under a map `f` with
  `re (f x) = m re x`, up to integer factors, checked exactly in `κE`; the polyhedra then differ
  by a factor.
* `sqrtOk`, `ZSqrt.embed`, `ZSqrt.re_embed`: `G ∈ κE` checked to be `S √d`, and the embedding
  `a + b √d ↦ S a + b G` of `ℤ[√d]`, which multiplies real values by `S`.
* `thetaOk`, `ZTheta.embed`, `ZTheta.re_embed`: for a solid over a number field `ℚ(α)` with the
  root data `R`, `G ∈ κE` checked to be `S α` (the polynomial of `α` vanishes at `G / S`, which
  lies where `α` is its only root), and the embedding `∑ xᵢ αⁱ ↦ ∑ xᵢ S^(n-1-i) Gⁱ` of `ℤ[α]`,
  which multiplies real values by `S^(n-1)`.
* `Polyhedron.nieuwland_eq_of_lift_smul`: the assembly of `nieuwland_eq_of_lift` with the lift's
  points a nonzero multiple of the far field's.
-/

open Matrix Pointwise

namespace Nieuwland

namespace Polyhedron

variable {P : Polyhedron}

/-- A fit of the scaled polyhedron along `u` is a fit of the polyhedron: screen coordinates
scale with it. -/
theorem FitsAlong.of_smul_poly {u : Fin 3 → ℝ} {R : Matrix (Fin 3) (Fin 3) ℝ} {c : ℝ} (hc : c ≠ 0)
    (h : (P.smul c).FitsAlong u R) : P.FitsAlong u R := by
  obtain ⟨L, hL, hker, τ, hτ⟩ := h
  have hB : {L y | y ∈ (P.smul c).hull} = c • {L x | x ∈ P.hull} := by
    rw [hull_smul]
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_smul_set]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨L x, ⟨x, hx, rfl⟩, (map_smul L c x).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨c • x, ⟨x, hx, rfl⟩, map_smul L c x⟩
  refine ⟨L, hL, hker, c⁻¹ • τ, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hx' : c • x ∈ (P.smul c).hull := by
    rw [hull_smul]
    exact Set.smul_mem_smul_set hx
  have h1 := hτ ⟨c • x, hx', rfl⟩
  rw [hB, interior_smul₀ hc] at h1
  have e : L (R *ᵥ (c • x)) + τ = c • (L (R *ᵥ x) + c⁻¹ • τ) := by
    rw [Matrix.mulVec_smul, map_smul, smul_add, smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [e] at h1
  exact (Set.smul_mem_smul_set_iff₀ hc _ _).mp h1

/-- **Scaling the polyhedron.** Fits along a direction do not change when the polyhedron is
scaled by `c ≠ 0` (plug and hole together). -/
theorem fitsAlong_smul_poly_iff {u : Fin 3 → ℝ} {R : Matrix (Fin 3) (Fin 3) ℝ} {c : ℝ}
    (hc : c ≠ 0) : (P.smul c).FitsAlong u R ↔ P.FitsAlong u R :=
  ⟨FitsAlong.of_smul_poly hc, fun h ↦
    FitsAlong.of_smul_poly (P := P.smul c) (inv_ne_zero hc) (by rwa [smul_smul_inv hc])⟩

theorem noFitRot_smul_iff {S : Set ChartPose} {Rc : Matrix (Fin 3) (Fin 3) ℝ} {c : ℝ}
    (hc : c ≠ 0) : (P.smul c).NoFitRot S Rc ↔ P.NoFitRot S Rc := by
  simp only [NoFitRot, fitsAlong_smul_poly_iff hc]

end Polyhedron

namespace Check

variable {κF κE : Type} [Add κF] [Sub κF] [Mul κF] [Exact κF] [Add κE] [Sub κE] [Mul κE] [Exact κE]

/-- A map of exact values that multiplies real values by `m` does so for points. -/
theorem reV_map_of_re {f : κF → κE} {m : ℝ} (hf : ∀ x, Exact.re (f x) = m * Exact.re x)
    (p : V3 κF) : Exact.reV (p.map f) = m • Exact.reV p := by
  funext i
  fin_cases i <;> simp [Exact.reV, V3.map, V3.toFun, hf]

/-- **The points of a lift.** The points `ptsE` are those of `ptsF` under `f`, one for one and up
to positive integer factors: `nE q = nF (f p)` in every coordinate, as exact values of `κE`. -/
def liftOk (f : κF → κE) (nE nF : ℕ) (ptsF : List (V3 κF)) (ptsE : List (V3 κE)) : Bool :=
  decide (0 < nE) && decide (0 < nF) && ptsF.length == ptsE.length &&
    (ptsF.zip ptsE).all fun pq ↦
      Exact.eqV (V3.smul (Exact.ofInt nE) pq.2) (V3.smul (Exact.ofInt nF) (pq.1.map f))

/-- **The polyhedron of a lift's points** is that of the points below, scaled: by `nF m / nE`
when `f` multiplies real values by `m`. -/
theorem ofPoints_of_liftOk {f : κF → κE} {m : ℝ} (hf : ∀ x, Exact.re (f x) = m * Exact.re x)
    {nE nF : ℕ} {ptsF : List (V3 κF)} {ptsE : List (V3 κE)}
    (h : liftOk f nE nF ptsF ptsE = true) :
    Polyhedron.ofPoints ptsE = (Polyhedron.ofPoints ptsF).smul (nF * m / nE) := by
  simp only [liftOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hnE, -⟩, hlen⟩, hall⟩ := h
  have hnE' : (nE : ℝ) ≠ 0 := by exact_mod_cast hnE.ne'
  have key : ptsE.map Exact.reV = ptsF.map fun p ↦ ((nF : ℝ) * m / nE) • Exact.reV p := by
    refine List.ext_getElem (by simp [hlen]) fun i h1 h2 ↦ ?_
    have hi : i < ptsF.length := by simpa using h2
    have hi' : i < ptsE.length := by simpa using h1
    simp only [List.getElem_map]
    have hmem : (ptsF[i], ptsE[i]) ∈ ptsF.zip ptsE := by
      rw [List.mem_iff_getElem]
      exact ⟨i, by simp [hi, hi'], by simp⟩
    have e := Exact.reV_eq_of_eqV (hall _ hmem)
    rw [Exact.reV_smul, Exact.reV_smul, Exact.re_ofInt, Exact.re_ofInt, reV_map_of_re hf] at e
    simp only [Int.cast_natCast] at e
    calc Exact.reV ptsE[i] = (nE : ℝ)⁻¹ • ((nE : ℝ) • Exact.reV ptsE[i]) := by
          rw [smul_smul, inv_mul_cancel₀ hnE', one_smul]
      _ = ((nF : ℝ) * m / nE) • Exact.reV ptsF[i] := by
          rw [e, smul_smul, smul_smul]
          congr 1
          field_simp
  classical
  unfold Polyhedron.ofPoints Polyhedron.smul
  rw [key]
  simp only [Polyhedron.mk.injEq]
  ext x
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨_, ⟨p, hp, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, rfl⟩

/-- **A square root in the lift.** `G` is known to be `S √d` with `S > 0`: its square is `S² d`
and it is positive, as exact values of `κE`. -/
def sqrtOk (d S : ℕ) (G : κE) : Bool :=
  decide (0 < S) && Exact.isZero (G * G - Exact.ofInt ((S * S * d : ℕ) : ℤ)) && Exact.pos G

theorem re_of_sqrtOk {d S : ℕ} {G : κE} (h : sqrtOk d S G = true) :
    Exact.re G = S * √(d : ℝ) := by
  simp only [sqrtOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨-, hz⟩, hp⟩ := h
  have h0 := Exact.isZero_sound _ hz
  have hpos := Exact.pos_sound _ hp
  rw [Exact.re_sub, Exact.re_mul, Exact.re_ofInt] at h0
  push_cast at h0
  have hsq : Exact.re G * Exact.re G = (S * √(d : ℝ)) * (S * √(d : ℝ)) := by
    linear_combination h0 - (S : ℝ) * S * (ZSqrt.sqrt_facts d).2
  rcases mul_self_eq_mul_self_iff.mp hsq with h1 | h1
  · exact h1
  · have : 0 ≤ (S : ℝ) * √(d : ℝ) := by positivity
    linarith

theorem pos_of_sqrtOk {d S : ℕ} {G : κE} (h : sqrtOk d S G = true) : 0 < S := by
  simp only [sqrtOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

/-- `S (a + b √d)` as an exact value of `κE`, with `G` for `S √d`. -/
def ZSqrt.embed {d : ℕ} (S : ℕ) (G : κE) (x : ZSqrt d) : κE :=
  Exact.ofInt (S * x.a) + Exact.ofInt x.b * G

/-- **The embedding of `ℤ[√d]`** multiplies real values by `S`. -/
theorem ZSqrt.re_embed {d S : ℕ} {G : κE} (h : sqrtOk d S G = true) (x : ZSqrt d) :
    Exact.re (ZSqrt.embed S G x) = S * Exact.re x := by
  rw [ZSqrt.embed, Exact.re_add, Exact.re_mul, Exact.re_ofInt, Exact.re_ofInt, re_of_sqrtOk h,
    ZSqrt.re_eq, ZSqrt.re]
  push_cast
  ring

/-! ### A number field below the lift -/

/-- `∑ᵢ aᵢ S^(k-1-i) Gⁱ` for the coefficients `a₀, …, a_(k-1)`: their polynomial, homogeneous in
`(G, S)`, as an exact value of `κE`. -/
def homE (S : ℕ) (G : κE) : List ℤ → κE
  | [] => Exact.ofInt 0
  | a :: q => Exact.ofInt (a * (S : ℤ) ^ q.length) + G * homE S G q

/-- The homogeneous polynomial is `S^(k-1)` times the polynomial at `G / S`. -/
theorem re_homE_mul {S : ℕ} (hS : 0 < S) (G : κE) : ∀ l : List ℤ,
    Exact.re (homE S G l) * S = (S : ℝ) ^ l.length * evalZ l (Exact.re G / S)
  | [] => by simp [homE, Exact.re_ofInt, evalZ_nil]
  | a :: q => by
    have hS' : (S : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
    rw [homE, Exact.re_add, Exact.re_mul, Exact.re_ofInt, evalZ_cons, List.length_cons, add_mul,
      mul_assoc, re_homE_mul hS G q]
    push_cast
    field_simp
    ring

/-- **A root in the lift.** `G` is known to be `S α` for the root `α` of `R`, with `S > 0`: the
monic polynomial `N` of `α`, homogeneous in `(G, S)`, vanishes, and `G / S` lies in `[A/E, B/E]`,
where `α` is the only root of `N` (`Root.eq_of_root`); all as exact values of `κE`. -/
def thetaOk (R : Root) (S : ℕ) (G : κE) : Bool :=
  decide (0 < S) && Exact.isZero (homE S G R.N) &&
    Exact.nonneg (Exact.ofInt (R.E : ℤ) * G - Exact.ofInt (R.A * S)) &&
    Exact.nonneg (Exact.ofInt (R.B * S) - Exact.ofInt (R.E : ℤ) * G)

theorem pos_of_thetaOk {R : Root} {S : ℕ} {G : κE} (h : thetaOk R S G = true) : 0 < S := by
  simp only [thetaOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

theorem re_of_thetaOk {R : Root} {S : ℕ} {G : κE} (h : thetaOk R S G = true) :
    Exact.re G = S * R.α := by
  have hS := pos_of_thetaOk h
  simp only [thetaOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨-, hz⟩, hlo⟩, hhi⟩ := h
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hE : (0 : ℝ) < R.E := by
    have h₂ := R.coarse
    simp only [coarseCheck, Bool.and_eq_true, decide_eq_true_eq] at h₂
    exact_mod_cast h₂.1.1.1.1.1.1
  have h0 := re_homE_mul hS G R.N
  rw [Exact.isZero_sound _ hz, zero_mul] at h0
  have hev : evalZ R.N (Exact.re G / S) = 0 := by
    rcases mul_eq_zero.mp h0.symm with h1 | h1
    · exact absurd h1 (pow_ne_zero _ hS'.ne')
    · exact h1
  have hlo' := Exact.nonneg_sound _ hlo
  have hhi' := Exact.nonneg_sound _ hhi
  rw [Exact.re_sub, Exact.re_mul, Exact.re_ofInt, Exact.re_ofInt] at hlo' hhi'
  push_cast at hlo' hhi'
  have hα := R.eq_of_root (y := Exact.re G / S) (by rw [div_le_div_iff₀ hE hS']; linarith)
    (by rw [div_le_div_iff₀ hS' hE]; linarith) hev
  rw [hα]
  field_simp

/-- `S^(n-1) ∑ᵢ xᵢ αⁱ` as an exact value of `κE`, with `G` for `S α`: the `n` coordinates of `x`
as a polynomial homogeneous in `(G, S)`. -/
def ZTheta.embed {R : Root} (S : ℕ) (G : κE) (x : ZTheta R) : κE :=
  homE S G ((List.range R.n).map fun i ↦ x.c.getD i 0)

/-- **The embedding of `ℤ[α]`** multiplies real values by `S^(n-1)`; the exponent is stated as
`k` with `n = k + 1`, so that a certificate writes it as a numeral. -/
theorem ZTheta.re_embed {R : Root} {S : ℕ} {G : κE} (h : thetaOk R S G = true) {k : ℕ}
    (hk : R.n = k + 1) (x : ZTheta R) :
    Exact.re (ZTheta.embed S G x) = (S : ℝ) ^ k * Exact.re x := by
  have hS := pos_of_thetaOk h
  have hS' : (S : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
  have h1 := re_homE_mul hS G ((List.range R.n).map fun i ↦ x.c.getD i 0)
  rw [re_of_thetaOk h, mul_div_cancel_left₀ _ hS', List.length_map, List.length_range] at h1
  have hl : evalZ ((List.range R.n).map fun i ↦ x.c.getD i 0) R.α = Exact.re x := by
    rw [ZTheta.re_eq, ZTheta.re_eq_evalZ, evalZ_eq_sum (m := R.n) (by simp),
      evalZ_eq_sum (m := R.n) (by simp)]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' : i < R.n := Finset.mem_range.mp hi
    congr 2
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hi', List.getElem?_take_of_lt hi']
    simp [List.getD_eq_getElem?_getD]
  have hp : (S : ℝ) ^ R.n = (S : ℝ) ^ k * S := by rw [hk, pow_succ]
  rw [hl, hp] at h1
  rw [ZTheta.embed]
  exact mul_right_cancel₀ hS' (by rw [h1]; ring)

/-- **Exact Nieuwland numbers from a certificate over a lift, with the lift's points a multiple
of the far field's.** As `Polyhedron.nieuwland_eq_of_lift`, with
`ofPoints ptsE = (ofPoints ptsF).smul c`, `c ≠ 0` (`ofPoints_of_liftOk`): the claims' facts and
the weak fit do not depend on the factor. -/
theorem Polyhedron.nieuwland_eq_of_lift_smul [Countable κF]
    {ptsF : List (V3 κF)} {D : SymmData κF} {i j k l : ℕ} (hspan : spanOk ptsF i j k l = true)
    {roots : List ChartBox} (hroots : unitsIn roots = true) {claims : List ChartBox}
    {θ : Scale κF} (hθ : θ.ok = true)
    (h : roots.Forall fun B ↦ ∀ p ∈ B.poses, SettledS ptsF D θ.re p ∨ ∃ C ∈ claims, p ∈ C.poses)
    {ptsE : List (V3 κE)} {c : ℝ} (hc : c ≠ 0)
    (hpts : Polyhedron.ofPoints ptsE = (Polyhedron.ofPoints ptsF).smul c)
    {Θ θE : Scale κE} (hθE : θE.re = θ.re) (hle : θE.le Θ = true)
    (hcl : ∀ C ∈ claims, (Polyhedron.ofPoints ptsE).NoFitRot C.poses (Θ.re • 1))
    {W : WeakFitData κE} (hW : W.check ptsE = true) (hWn : W.scaleNum = Θ.num)
    (hWd : W.scaleDen = Θ.den) {P : Polyhedron} {a : ℝ}
    (hP : P = (Polyhedron.ofPoints ptsF).smul a) (ha : a ≠ 0) (hdim : P.FullDim) :
    P.nieuwland = Θ.re := by
  have hlo : Θ.re ≤ P.nieuwland := by
    have hP' : P = (Polyhedron.ofPoints ptsE).smul (a * c⁻¹) := by
      rw [hpts, Polyhedron.smul_smul_eq, inv_mul_cancel_right₀ hc]
      exact hP
    have h0 := W.le_nieuwland_smul hW (mul_ne_zero ha (inv_ne_zero hc)) hP' hdim
    rwa [WeakFitData.scale, hWn, hWd] at h0
  refine Polyhedron.nieuwland_eq_of_claims hspan hroots (Scale.re_nonneg_of_ok hθ) ?_ h ?_ hP ha
    hlo
  · rw [← hθE]
    exact Scale.re_le_of_le hle
  · intro C hC
    have h1 := hcl C hC
    rw [hpts] at h1
    exact (Polyhedron.noFitRot_smul_iff hc).mp h1

end Check

end Nieuwland
