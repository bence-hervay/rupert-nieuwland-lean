import Modules.Root.Assembly

/-!
# Touch leaves with weights of `c`

A touch leaf (`Modules/Root/Leaf.lean`) tests the function `G = ∑ (cd m_i + cn g_i) g_i` of the
slacks `g_i` of its contacts, with one constant `cn / cd` for all of them. A leaf **with weights
of `c`** gives the contact `i` its own numerator `cn_i` over `cd` (`cw`, `LeafRec.cnW`; the
contacts past the list take `cn`): `G = ∑ (cd m_i [+ ∑_k λ_i,k d_k] + cn_i g_i) g_i`. Where one
contact's multiplier is far below the others', its own smaller constant keeps its factor
nonnegative on a larger box [measured: the square trapezohedron, `notes/prism-duals.md`].

Nothing in the leaf's argument uses equal constants: the form is `form_eqW` with `cn_i`
(`ν_jk = ∑_i (φ_i μ_i,jk + cn_i σ_i,j γ_i,k)`), and the factors tested are the `φ_i` with their
own `cn_i`. This file repeats the leaf's check and its soundness with the weights as an argument
(`Sys.leafOkW`, `Sys.noFitRot_of_leafOkW`), and the root's checks and the one-root assembly with
them (`RootRec.okW`, `certOkW`, `nieuwland_eq_of_certOkW_one`, `nieuwland_mem_Icc_of_certOkW`).
The root records (`RootRec`, `LeafRec`) are those of `Modules/Root/Assembly.lean`; a certificate
gives its weights beside its record. With `cw = []` every check here is the plain one's.

A separate module, so that no module of the library changes (the solids built before it keep
their compiled modules).
-/

set_option linter.style.longLine false

open Nieuwland.Check Finset Matrix

namespace Nieuwland.Root

/-! ### The quadratic form with a constant per contact -/

/-- **The weighted sum of the slacks is a quadratic form of the displacement.** With
`g_i = ∑ σ_ik d_k = ∑ γ_ik d_k + ∑ μ_ijk d_j d_k` and `∑ m_i γ_ik = 0`:
`∑ (cd m_i + cn_i g_i) g_i = ∑ ν_jk d_j d_k` with
`ν_jk = ∑_i ((cd m_i + cn_i g_i) μ_ijk + cn_i σ_ij γ_ik)`; a constant `cn_i` per slack (the
plain leaf's are all equal, `code/src/proof/d2/`, "Leaf with weights of `c`"). -/
theorem form_eqW {n kk : ℕ} (cd : ℝ) (cn : ℕ → ℝ) (m g : ℕ → ℝ) (γ σ : ℕ → ℕ → ℝ)
    (μ : ℕ → ℕ → ℕ → ℝ) (d : ℕ → ℝ) (hs : ∀ i < kk, g i = ∑ k ∈ range n, σ i k * d k)
    (hm : ∀ i < kk, g i = ∑ k ∈ range n, γ i k * d k +
      ∑ j ∈ range n, ∑ k ∈ range n, μ i j k * d j * d k)
    (hst : ∀ k < n, ∑ i ∈ range kk, m i * γ i k = 0) :
    ∑ i ∈ range kk, (cd * m i + cn i * g i) * g i =
      ∑ j ∈ range n, ∑ k ∈ range n,
        (∑ i ∈ range kk, ((cd * m i + cn i * g i) * μ i j k + cn i * σ i j * γ i k)) * d j *
          d k := by
  have hterm : ∀ i ∈ range kk, (cd * m i + cn i * g i) * g i =
      cd * (∑ k ∈ range n, m i * γ i k * d k) +
        ∑ j ∈ range n, ∑ k ∈ range n,
          ((cd * m i + cn i * g i) * μ i j k + cn i * σ i j * γ i k) * d j * d k := by
    intro i hi
    have e1 := hm i (mem_range.mp hi)
    have e2 := hs i (mem_range.mp hi)
    have e3 : ∑ j ∈ range n, ∑ k ∈ range n,
          ((cd * m i + cn i * g i) * μ i j k + cn i * σ i j * γ i k) * d j * d k =
        (cd * m i + cn i * g i) * (∑ j ∈ range n, ∑ k ∈ range n, μ i j k * d j * d k) +
          cn i * ((∑ j ∈ range n, σ i j * d j) * ∑ k ∈ range n, γ i k * d k) := by
      rw [sum_mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun j _ ↦ ?_
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun k _ ↦ by ring
    have e4 : ∑ k ∈ range n, m i * γ i k * d k = m i * ∑ k ∈ range n, γ i k * d k := by
      rw [mul_sum]
      exact sum_congr rfl fun k _ ↦ by ring
    rw [e3, e4]
    linear_combination (cd * m i + cn i * g i) * e1 + cn i * (∑ k ∈ range n, γ i k * d k) * e2
  rw [sum_congr rfl hterm, sum_add_distrib, ← mul_sum]
  have z1 : ∑ i ∈ range kk, ∑ k ∈ range n, m i * γ i k * d k = 0 := by
    rw [sum_comm]
    refine sum_eq_zero fun k hk ↦ ?_
    rw [← sum_mul, hst k (mem_range.mp hk), zero_mul]
  rw [z1, mul_zero, zero_add, sum_comm]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [sum_comm]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [sum_mul, sum_mul]

/-- **The leaf with linear multipliers** (`code/src/proof/d2/`, "Leaf with linear multipliers"):
`form_eqW` with the multipliers `cd m_i + ∑_k λ_ik d_k + cn_i g_i` of the first `kl` slacks. The
terms `(∑_k λ_ik d_k) g_i` are, by the slopes of the slacks, the form of `∑_i λ_ij σ_ik`. -/
theorem form_eq_linW {n kk kl : ℕ} (cd : ℝ) (cn : ℕ → ℝ) (m g : ℕ → ℝ) (lam γ σ : ℕ → ℕ → ℝ)
    (μ : ℕ → ℕ → ℕ → ℝ) (d : ℕ → ℝ) (hkl : kl ≤ kk)
    (hs : ∀ i < kk, g i = ∑ k ∈ range n, σ i k * d k)
    (hm : ∀ i < kk, g i = ∑ k ∈ range n, γ i k * d k +
      ∑ j ∈ range n, ∑ k ∈ range n, μ i j k * d j * d k)
    (hst : ∀ k < n, ∑ i ∈ range kk, m i * γ i k = 0) :
    ∑ i ∈ range kk, (cd * m i + cn i * g i) * g i +
        ∑ i ∈ range kl, (∑ k ∈ range n, lam i k * d k) * g i =
      ∑ j ∈ range n, ∑ k ∈ range n,
        (∑ i ∈ range kk, ((cd * m i + cn i * g i) * μ i j k + cn i * σ i j * γ i k) +
          ∑ i ∈ range kl, lam i j * σ i k) * d j * d k := by
  have h1 : ∑ i ∈ range kl, (∑ k ∈ range n, lam i k * d k) * g i =
      ∑ j ∈ range n, ∑ k ∈ range n, (∑ i ∈ range kl, lam i j * σ i k) * d j * d k := by
    have e : ∀ i ∈ range kl, (∑ k ∈ range n, lam i k * d k) * g i =
        ∑ j ∈ range n, ∑ k ∈ range n, lam i j * σ i k * d j * d k := fun i hi ↦ by
      rw [hs i (lt_of_lt_of_le (mem_range.mp hi) hkl), sum_mul_sum]
      exact sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ by ring
    rw [sum_congr rfl e, sum_comm]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [sum_comm]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [sum_mul, sum_mul]
  rw [form_eqW cd cn m g γ σ μ d hs hm hst, h1, ← sum_add_distrib]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [← sum_add_distrib]
  exact sum_congr rfl fun k _ ↦ by ring

/-- **The leaf with a spread** (`code/src/proof/d2/`, "Leaf with a spread"). Slacks `g_i` of the
system with factors `F_i`, and slacks `g'_j` of further contacts tied to them by identities
`D_j g'_j = ∑ p_ji g_i` with `D_j > 0`. If the factors less the spread's share,
`F_i - ∑_j w_j p_ji / D_j`, and the spread's own factors `w_j + cn_j g'_j` are nonnegative, then
`∑ F_i g_i + ∑ cn_j g'_j²` is at most `0` wherever no slack is positive: it is
`∑ (F_i - ∑_j w_j p_ji / D_j) g_i + ∑ (w_j + cn_j g'_j) g'_j`. -/
theorem spread_nonposW {k ns : ℕ} (cn : ℕ → ℝ) (F g g' D w : ℕ → ℝ) (p : ℕ → ℕ → ℝ)
    (hD : ∀ j < ns, 0 < D j) (hid : ∀ j < ns, D j * g' j = ∑ i ∈ range k, p j i * g i)
    (hσ : ∀ i < k, 0 ≤ F i - ∑ j ∈ range ns, w j * p j i / D j)
    (hτ : ∀ j < ns, 0 ≤ w j + cn j * g' j) (hg : ∀ i < k, g i ≤ 0) (hg' : ∀ j < ns, g' j ≤ 0) :
    ∑ i ∈ range k, F i * g i + ∑ j ∈ range ns, cn j * g' j * g' j ≤ 0 := by
  have hsw : ∑ i ∈ range k, (∑ j ∈ range ns, w j * p j i / D j) * g i =
      ∑ j ∈ range ns, w j * g' j := by
    simp_rw [sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun j hj ↦ ?_
    have hne := (hD j (mem_range.mp hj)).ne'
    have e : ∑ i ∈ range k, w j * p j i / D j * g i =
        w j / D j * ∑ i ∈ range k, p j i * g i := by
      rw [mul_sum]
      exact sum_congr rfl fun i _ ↦ by ring
    rw [e, ← hid j (mem_range.mp hj)]
    field_simp
  have e : ∑ i ∈ range k, F i * g i + ∑ j ∈ range ns, cn j * g' j * g' j =
      ∑ i ∈ range k, (F i - ∑ j ∈ range ns, w j * p j i / D j) * g i +
        ∑ j ∈ range ns, (w j + cn j * g' j) * g' j := by
    have e1 : ∑ i ∈ range k, (F i - ∑ j ∈ range ns, w j * p j i / D j) * g i =
        ∑ i ∈ range k, F i * g i - ∑ j ∈ range ns, w j * g' j := by
      rw [← hsw, ← sum_sub_distrib]
      exact sum_congr rfl fun i _ ↦ by ring
    have e2 : ∑ j ∈ range ns, (w j + cn j * g' j) * g' j =
        ∑ j ∈ range ns, w j * g' j + ∑ j ∈ range ns, cn j * g' j * g' j := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun j _ ↦ by ring
    rw [e1, e2]
    ring
  rw [e]
  exact add_nonpos
    (sum_nonpos fun i hi ↦ mul_nonpos_of_nonneg_of_nonpos (hσ i (mem_range.mp hi))
      (hg i (mem_range.mp hi)))
    (sum_nonpos fun j hj ↦ mul_nonpos_of_nonneg_of_nonpos (hτ j (mem_range.mp hj))
      (hg' j (mem_range.mp hj)))

/-- The numerator of the constant of the contact `i` of `G` under the weights `cw`: its entry
of `cw`, else the leaf's `cn` (`LeafRec.cn`). -/
def LeafRec.cnW (L : LeafRec) (cw : List ℤ) (i : ℕ) : ℤ := cw.getD i L.cn

namespace Leaf

variable {R : Type} [Enc R]

/-- The enclosure of `φ_i = cd m_i + cn_i g_i(a + d)`, the slack by its slopes from the zero;
`M i` encloses the multiplier `m_i`. -/
def phiW (cd : ℤ) (cn : ℕ → ℤ) (n : ℕ) (A Zq M : ℕ → R) (T : ℕ → TBall R) (i : ℕ) : R :=
  Enc.ofInt cd * M i + Enc.ofInt (cn i) * Enc.sum n fun k ↦ (T i).s k * (Zq k - A k)

/-- The enclosure of `ν_jk = ∑_i (φ_i μ_i,jk + cn_i σ_i,j γ_i,k)`. -/
def nbW (cn : ℕ → ℤ) (n kk : ℕ) (T : ℕ → TBall R) (Φ : ℕ → R) (j k : ℕ) : R :=
  Enc.sum kk fun i ↦ Φ i * (T i).m n j k + Enc.ofInt (cn i) * (T i).s j * (T i).g k

/-- `nbW` with the linear parts' share `∑_{i < kl} λ_i,j σ_i,k` of `ν_jk`; `plain`: a leaf without
linear parts, whose `ν` is `nbW`'s. -/
def nblW (cn : ℕ → ℤ) (n kk : ℕ) (plain : Bool) (lam : ℕ → ℕ → ℤ) (kl : ℕ) (T : ℕ → TBall R)
    (Φ : ℕ → R) (j k : ℕ) : R :=
  if plain then nbW cn n kk T Φ j k
  else nbW cn n kk T Φ j k + Enc.sum kl fun i ↦ Enc.ofInt (lam i j) * (T i).s k

variable {E : R → ℝ → Prop}

theorem encl_phiW (hE : Enc.Sound E) {cd : ℤ} {cn : ℕ → ℤ} {n : ℕ} {A Zq M : ℕ → R} {T : ℕ → TBall R}
    {a yy σ : ℕ → ℝ} {m : ℝ} {i : ℕ} (hA : ∀ i, E (A i) (a i)) (hZ : ∀ k, E (Zq k) (yy k))
    (hM : E (M i) m) (hσ : ∀ k < n, E ((T i).s k) (σ k)) :
    E (phiW cd cn n A Zq M T i) (cd * m + cn i * ∑ k ∈ range n, σ k * (yy k - a k)) :=
  hE.add (hE.mul (hE.ofInt cd) hM)
    (hE.mul (hE.ofInt (cn i)) (hE.sum fun k hk ↦ hE.mul (hσ k hk) (hE.sub (hZ k) (hA k))))

theorem encl_nbW (hE : Enc.Sound E) {cn : ℕ → ℤ} {n kk : ℕ} {T : ℕ → TBall R} {Φ : ℕ → R}
    {φ : ℕ → ℝ} {μ : ℕ → ℕ → ℕ → ℝ} {σ γ : ℕ → ℕ → ℝ} (hΦ : ∀ i < kk, E (Φ i) (φ i))
    (hμ : ∀ i < kk, ∀ j < n, ∀ k < n, E ((T i).m n j k) (μ i j k))
    (hσ : ∀ i < kk, ∀ k < n, E ((T i).s k) (σ i k))
    (hγ : ∀ i < kk, ∀ k < n, E ((T i).g k) (γ i k)) {j k : ℕ} (hj : j < n) (hk : k < n) :
    E (nbW cn n kk T Φ j k) (∑ i ∈ range kk, (φ i * μ i j k + cn i * σ i j * γ i k)) :=
  hE.sum fun i hi ↦ hE.add (hE.mul (hΦ i hi) (hμ i hi j hj k hk))
    (hE.mul (hE.mul (hE.ofInt (cn i)) (hσ i hi j hj)) (hγ i hi k hk))

theorem encl_nblW (hE : Enc.Sound E) {cn : ℕ → ℤ} {n kk kl : ℕ} {plain : Bool} {lam : ℕ → ℕ → ℤ}
    {T : ℕ → TBall R} {Φ : ℕ → R} {φ : ℕ → ℝ} {μ : ℕ → ℕ → ℕ → ℝ} {σ γ : ℕ → ℕ → ℝ}
    (hpl : plain = true → ∀ i j, lam i j = 0) (hkl : kl ≤ kk)
    (hΦ : ∀ i < kk, E (Φ i) (φ i))
    (hμ : ∀ i < kk, ∀ j < n, ∀ k < n, E ((T i).m n j k) (μ i j k))
    (hσ : ∀ i < kk, ∀ k < n, E ((T i).s k) (σ i k))
    (hγ : ∀ i < kk, ∀ k < n, E ((T i).g k) (γ i k)) {j k : ℕ} (hj : j < n) (hk : k < n) :
    E (nblW cn n kk plain lam kl T Φ j k)
      (∑ i ∈ range kk, (φ i * μ i j k + cn i * σ i j * γ i k) +
        ∑ i ∈ range kl, (lam i j : ℝ) * σ i k) := by
  unfold nblW
  split_ifs with h
  · have z : ∑ i ∈ range kl, (lam i j : ℝ) * σ i k = 0 :=
      sum_eq_zero fun i _ ↦ by rw [hpl h i j, Int.cast_zero, zero_mul]
    rw [z, add_zero]
    exact encl_nbW hE hΦ hμ hσ hγ hj hk
  · exact hE.add (encl_nbW hE hΦ hμ hσ hγ hj hk)
      (hE.sum fun i hi ↦ hE.mul (hE.ofInt _) (hσ i (lt_of_lt_of_le hi hkl) k hk))

end Leaf

namespace Sys

variable (S : Sys)

/-- The forms of the `φ_i`. -/
def philW (Z qb : List Ball) (L : LeafRec) (cw : List ℤ) : List (Aff (nx S.cen) L.bits) :=
  (List.range (S.lk L)).map
    (Leaf.phiW L.cd (L.cnW cw) (nx S.cen) (S.za L.bits Z) (S.zq L.bits Z qb) (S.zm L.bits Z)
      (Leaf.tat (S.tl Z qb L)))

/-- The forms of the `ν_jk`. -/
def nlW (Z qb : List Ball) (L : LeafRec) (cw : List ℤ) : List (Aff (nx S.cen) L.bits) :=
  tab2 (nx S.cen)
    (Leaf.nblW (L.cnW cw) (nx S.cen) (S.lk L) L.lin.isEmpty L.lam S.k (Leaf.tat (S.tl Z qb L))
      (Leaf.at1 (S.philW Z qb L cw)))

/-- The balls of `P^T ν P` on `Q`. -/
def blW (Z qb : List Ball) (L : LeafRec) (cw : List ℤ) : List Ball :=
  tab2 (nx S.cen) fun a b ↦
    (Leaf.bb L.P (nx S.cen) (Leaf.at2 (nx S.cen) (S.nlW Z qb L cw)) a b).toBall

/-- The core check of a touch leaf on the balls `Z` of the variables at the zero and `qb` of the
pose unknowns on `Q` (module docs): the factors of the system's contacts less the spread's
share (without a spread: the `φ_i`, with their linear parts if the leaf has them), the spread's
`D_j` and factors, the dominance. -/
def leafCoreW (Z qb : List Ball) (L : LeafRec) (cw : List ℤ) : Bool :=
  let n := nx S.cen
  let Φl := S.philW Z qb L cw
  let Ψl := S.psil Z qb L Φl
  let Bl := S.blW Z qb L cw
  decide (0 < S.k) && decide (L.pd ≠ 0) &&
    ((List.range n).all fun j ↦ (List.range n).all fun k ↦
      decide ((∑ a ∈ range n, Kraw.ent L.P j a * Kraw.ent L.Pa a k) =
        if j = k then L.pd else 0)) &&
    ((List.range L.sp.length).all fun j ↦
      (bval (Kraw.zball Z) (L.spr j).id.D).isPos &&
      (S.spv Z qb L (L.spr j).id.D).toBall.isPos &&
      (Enc.ofInt (L.spr j).w + Leaf.at1 Φl (S.k + j)).toBall.isNonneg) &&
    ((List.range S.k).all fun i ↦
      (Leaf.fac (fun j ↦ (L.spr j).w) (fun j ↦ S.spv Z qb L (L.spr j).id.D)
        (fun j ↦ S.spv Z qb L ((L.spr j).id.p.getD i (.const 0))) (Leaf.at1 Ψl i) (Enc.ofInt 1)
        L.sp.length).1.toBall.isNonneg) &&
    (List.range n).all fun a ↦ (Leaf.dom n (fun c b ↦ Bl.getD (c * n + b) (Ball.ofInt 0)) a).isPos

variable {S} {K : Kraw}

/-- **Soundness of the core of the touch leaf**: no point of `Q` (the pose unknowns in the balls
`qb`, the other variables at the zero) makes every slack of the contacts of `G` negative. `hid`:
the identities of the spread hold. -/
theorem not_all_neg_of_leafCoreW (hK : K.eqs = S.eqs) {p : ℕ → ℝ} (hp : K.ParOk p)
    {y : Fin K.n → ℝ} (hy : y ∈ K.box) (h0 : K.F p y = 0)
    {qb : List Ball} {L : LeafRec} {cw : List ℤ} (hL : S.leafCoreW K.zballs qb L cw = true)
    (hid : ∀ r ∈ L.sp, ∀ z : ℕ → ℝ, (∀ i, nx S.cen ≤ i → z i = K.env p y i) →
      (S.idE r.id).eval z = 0) {yy : ℕ → ℝ}
    (hq : ∀ i < nx S.cen, (qb.getD i (Ball.ofInt 0)).Encl (yy i))
    (hfix : ∀ i, nx S.cen ≤ i → yy i = K.env p y i) :
    ¬ ∀ i < S.lk L, (S.lg L i).eval yy < 0 := by
  intro hneg
  have hA0 : ∀ i, (Kraw.zball K.zballs i).Encl (K.env p y i) := K.encl_zballs hp hy h0
  simp only [leafCoreW, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
    at hL
  obtain ⟨⟨⟨⟨⟨hk0, hpd⟩, hPP⟩, hsp⟩, hΦnn⟩, hdom⟩ := hL
  -- the identities of the spread, at a point with the zero's other variables
  have hidz : ∀ j < L.sp.length, ∀ z : ℕ → ℝ, (∀ i, nx S.cen ≤ i → z i = K.env p y i) →
      (L.spr j).id.D.eval z * (S.lg L (S.k + j)).eval z =
        ∑ i ∈ range S.k, ((L.spr j).id.p.getD i (.const 0)).eval z * (S.g i).eval z :=
    fun j hj z hz ↦ by
      have e := hid _ (L.spr_mem hj) z hz
      simp only [idE, Expr.eval, eval_sumE] at e
      rw [S.lg_add L hj]
      exact sub_eq_zero.mp e
  have hidy := fun j hj ↦ hidz j hj yy hfix
  -- the slacks of `G` vanish at the zero
  have hga : ∀ i < S.lk L, (S.lg L i).eval (K.env p y) = 0 := fun i hi ↦ by
    by_cases hik : i < S.k
    · rw [S.lg_of_lt L hik]
      exact g_zero hK h0 hik
    · obtain ⟨j, rfl⟩ : ∃ j, i = S.k + j := ⟨i - S.k, by omega⟩
      have hj : j < L.sp.length := by
        unfold lk at hi
        omega
      have e := hidz j hj (K.env p y) fun _ _ ↦ rfl
      rw [sum_eq_zero fun i hi ↦ by rw [g_zero hK h0 (mem_range.mp hi), mul_zero]] at e
      have hD : 0 < (L.spr j).id.D.eval (K.env p y) :=
        Ball.pos_sound (encl_bval hA0 _) (hsp j hj).1.1
      exact (mul_eq_zero.mp e).resolve_left hD.ne'
  have hst0 : ∀ k < nx S.cen, ∑ i ∈ range S.k,
      K.env p y (nx S.cen + 1 + i) * (deriv k (S.g i)).eval (K.env p y) = 0 := by
    intro k hk
    have h := stat_zero hK h0 (v := k) (by rw [nv]; omega)
    have hne : ¬ k = nx S.cen := by omega
    simp only [hne, ↓reduceIte, Int.cast_zero] at h
    exact h
  generalize K.env p y = a at hA0 hga hst0 hfix
  obtain ⟨δ, hδ, hA, hZ⟩ := exists_delta L.bits hA0 hq hfix
  have hδ' : ∀ k < nx S.cen, |δ k| ≤ 1 := fun k _ ↦ hδ k
  have hE : Enc.Sound (Aff.Encl (n := nx S.cen) (p := L.bits) δ) := Aff.sound hδ'
  -- the multipliers: `0` for the spread's contacts
  set m : ℕ → ℝ := fun i ↦ if i < S.k then a (nx S.cen + 1 + i) else 0 with hm
  have hM : ∀ i, Aff.Encl δ (S.zm L.bits K.zballs i) (m i) := fun i ↦ by
    unfold zm
    by_cases hik : i < S.k
    · simp only [hm, hik, ↓reduceIte]
      exact Aff.encl_ofBall δ (hA0 _)
    · simp only [hm, hik, ↓reduceIte]
      exact_mod_cast hE.ofInt 0
  have hst : ∀ k < nx S.cen,
      ∑ i ∈ range (S.lk L), m i * (deriv k (S.lg L i)).eval a = 0 := fun k hk ↦ by
    rw [lk, sum_range_add, ← hst0 k hk]
    have z2 : ∑ j ∈ range L.sp.length,
        m (S.k + j) * (deriv k (S.lg L (S.k + j))).eval a = 0 :=
      sum_eq_zero fun j _ ↦ by simp [hm]
    rw [z2, add_zero]
    refine sum_congr rfl fun i hi ↦ ?_
    have hik := mem_range.mp hi
    simp only [hm, hik, ↓reduceIte, S.lg_of_lt L hik]
  -- the expansions of the slacks
  have H : ∀ i, (second (nx S.cen) (S.za L.bits K.zballs) (S.zq L.bits K.zballs qb)
      (S.lg L i)).Holds
      (Aff.Encl δ) (nx S.cen) (fun k ↦ yy k - a k) ((S.lg L i).eval a) ((S.lg L i).eval yy)
      (fun k ↦ (deriv k (S.lg L i)).eval a) := fun i ↦ second_holds hE hA hZ hfix (S.lg L i)
  choose σ hσ hs using fun i ↦ (H i).sl
  choose μ hμ hmat using fun i ↦ (H i).mat
  have hT : ∀ i < S.lk L, Leaf.tat (S.tl K.zballs qb L) i =
      second (nx S.cen) (S.za L.bits K.zballs) (S.zq L.bits K.zballs qb) (S.lg L i) :=
    fun i hi ↦ by
    rw [Leaf.tat, tl, getD_map_range hi]
  -- the slack at the point, by slopes and by its expansion
  have hgs : ∀ i < S.lk L, (S.lg L i).eval yy = ∑ k ∈ range (nx S.cen), σ i k * (yy k - a k) :=
    fun i hi ↦ by
      have e := hs i
      rw [hga i hi, sub_zero] at e
      exact e
  have hgm : ∀ i < S.lk L, (S.lg L i).eval yy =
      ∑ k ∈ range (nx S.cen), (deriv k (S.lg L i)).eval a * (yy k - a k) +
        ∑ j ∈ range (nx S.cen), ∑ k ∈ range (nx S.cen),
          μ i j k * (yy j - a j) * (yy k - a k) := fun i hi ↦ by
    have e := hmat i
    rw [hga i hi, zero_add] at e
    exact e
  -- φ
  have hΦ : ∀ i < S.lk L, Aff.Encl δ (Leaf.at1 (S.philW K.zballs qb L cw) i)
      (L.cd * m i + (L.cnW cw) i * (S.lg L i).eval yy) := fun i hi ↦ by
    rw [Leaf.at1, philW, getD_map_range hi, hgs i hi]
    exact Leaf.encl_phiW hE hA hZ (hM i) fun k hk ↦ by rw [hT i hi]; exact hσ i k hk
  -- ψ: the factors of the system's contacts, with their linear parts
  have hkl : S.k ≤ S.lk L := Nat.le_add_right _ _
  have hΨ : ∀ i < S.k, Aff.Encl δ
      (Leaf.at1 (S.psil K.zballs qb L (S.philW K.zballs qb L cw)) i)
      (L.cd * m i + (L.cnW cw) i * (S.lg L i).eval yy +
        ∑ k ∈ range (nx S.cen), (L.lam i k : ℝ) * (yy k - a k)) := fun i hi ↦ by
    unfold psil
    split_ifs with hl
    · have z : ∑ k ∈ range (nx S.cen), (L.lam i k : ℝ) * (yy k - a k) = 0 :=
        sum_eq_zero fun k _ ↦ by rw [L.lam_of_isEmpty hl, Int.cast_zero, zero_mul]
      rw [z, add_zero]
      exact hΦ i (lt_of_lt_of_le hi hkl)
    · rw [Leaf.at1, getD_map_range hi]
      exact hE.add (hΦ i (lt_of_lt_of_le hi hkl)) (Leaf.encl_lpart hE hA hZ)
  -- G is the quadratic form of ν
  have hG := form_eq_linW (L.cd : ℝ) (fun i ↦ ((L.cnW cw) i : ℝ)) m
    (fun i ↦ (S.lg L i).eval yy) (fun i k ↦ (L.lam i k : ℝ))
    (fun i k ↦ (deriv k (S.lg L i)).eval a) σ μ
    (fun k ↦ yy k - a k) hkl hgs hgm hst
  -- G ≤ 0 at a point where every slack is negative: the factors less the spread's share
  have hDy : ∀ j < L.sp.length, 0 < (L.spr j).id.D.eval yy := fun j hj ↦
    Ball.pos_sound (Aff.encl_toBall hδ' (hE.val hZ _)) (hsp j hj).1.2
  have hle : ∑ i ∈ range (S.lk L),
      (L.cd * m i + (L.cnW cw) i * (S.lg L i).eval yy) * (S.lg L i).eval yy +
      ∑ i ∈ range S.k, (∑ k ∈ range (nx S.cen), (L.lam i k : ℝ) * (yy k - a k)) *
        (S.lg L i).eval yy ≤ 0 := by
    rw [lk, sum_range_add]
    have e1 : ∑ i ∈ range S.k, (L.cd * m i + (L.cnW cw) i * (S.lg L i).eval yy) * (S.lg L i).eval yy =
        ∑ i ∈ range S.k,
          (L.cd * a (nx S.cen + 1 + i) + (L.cnW cw) i * (S.g i).eval yy) * (S.g i).eval yy :=
      sum_congr rfl fun i hi ↦ by
        have hik := mem_range.mp hi
        simp only [hm, hik, ↓reduceIte, S.lg_of_lt L hik]
    have e2 : ∑ j ∈ range L.sp.length,
        (L.cd * m (S.k + j) + (L.cnW cw) (S.k + j) * (S.lg L (S.k + j)).eval yy) *
          (S.lg L (S.k + j)).eval yy =
        ∑ j ∈ range L.sp.length,
          (L.cnW cw) (S.k + j) * (S.lg L (S.k + j)).eval yy * (S.lg L (S.k + j)).eval yy :=
      sum_congr rfl fun j _ ↦ by simp [hm]
    have e3 : ∑ i ∈ range S.k, (∑ k ∈ range (nx S.cen), (L.lam i k : ℝ) * (yy k - a k)) *
          (S.lg L i).eval yy =
        ∑ i ∈ range S.k, (∑ k ∈ range (nx S.cen), (L.lam i k : ℝ) * (yy k - a k)) *
          (S.g i).eval yy :=
      sum_congr rfl fun i hi ↦ by rw [S.lg_of_lt L (mem_range.mp hi)]
    rw [e1, e2, e3, add_right_comm, ← sum_add_distrib]
    have e4 : ∑ i ∈ range S.k,
        ((L.cd * a (nx S.cen + 1 + i) + (L.cnW cw) i * (S.g i).eval yy) * (S.g i).eval yy +
          (∑ k ∈ range (nx S.cen), (L.lam i k : ℝ) * (yy k - a k)) * (S.g i).eval yy) =
        ∑ i ∈ range S.k, (L.cd * a (nx S.cen + 1 + i) + (L.cnW cw) i * (S.g i).eval yy +
          ∑ k ∈ range (nx S.cen), (L.lam i k : ℝ) * (yy k - a k)) * (S.g i).eval yy :=
      sum_congr rfl fun i _ ↦ by ring
    rw [e4]
    refine spread_nonposW (fun j ↦ ((L.cnW cw) (S.k + j) : ℝ))
      (fun i ↦ L.cd * a (nx S.cen + 1 + i) + (L.cnW cw) i * (S.g i).eval yy +
        ∑ k ∈ range (nx S.cen), (L.lam i k : ℝ) * (yy k - a k))
      (fun i ↦ (S.g i).eval yy) (fun j ↦ (S.lg L (S.k + j)).eval yy)
      (fun j ↦ (L.spr j).id.D.eval yy) (fun j ↦ ((L.spr j).w : ℝ))
      (fun j i ↦ ((L.spr j).id.p.getD i (.const 0)).eval yy) hDy hidy (fun i hi ↦ ?_)
      (fun j hj ↦ ?_) (fun i hi ↦ ?_) fun j hj ↦ (hneg (S.k + j) (by unfold lk; omega)).le
    · have hN := hΨ i hi
      simp only [hm, hi, ↓reduceIte, S.lg_of_lt L hi] at hN
      have h1 : Aff.Encl δ (Enc.ofInt 1 : Aff (nx S.cen) L.bits) (1 : ℝ) := by
        exact_mod_cast hE.ofInt 1
      have hf := (Leaf.encl_fac hE (w := fun j ↦ (L.spr j).w) hN h1 L.sp.length
        (fun j _ ↦ hE.val hZ (L.spr j).id.D)
        fun j _ ↦ hE.val hZ ((L.spr j).id.p.getD i (.const 0))).1
      exact sub_share_nonneg hDy (Ball.nonneg_sound (Aff.encl_toBall hδ' hf) (hΦnn i hi))
    · have hw := hE.add (hE.ofInt (L.spr j).w) (hΦ (S.k + j) (by unfold lk; omega))
      have e := Ball.nonneg_sound (Aff.encl_toBall hδ' hw) (hsp j hj).2
      simpa [hm] using e
    · have h := hneg i (by unfold lk; omega)
      rw [S.lg_of_lt L hi] at h
      exact h.le
  -- the displacement is zero, or the form is positive
  by_cases hd : ∃ k < nx S.cen, yy k - a k ≠ 0
  · -- enclosures of ν and of P^T ν P
    have hN : ∀ j < nx S.cen, ∀ k < nx S.cen,
        Aff.Encl δ (Leaf.at2 (nx S.cen) (S.nlW K.zballs qb L cw) j k)
        (∑ i ∈ range (S.lk L), ((L.cd * m i + (L.cnW cw) i * (S.lg L i).eval yy) * μ i j k +
          (L.cnW cw) i * σ i j * (deriv k (S.lg L i)).eval a) +
          ∑ i ∈ range S.k, (L.lam i j : ℝ) * σ i k) := fun j hj k hk ↦ by
      rw [Leaf.at2, nlW, getD_tab2 hj hk]
      exact Leaf.encl_nblW hE (μ := μ) (σ := σ) (γ := fun i k ↦ (deriv k (S.lg L i)).eval a)
        (fun hl ↦ L.lam_of_isEmpty hl) hkl hΦ
        (fun i hi j hj k hk ↦ by rw [hT i hi]; exact hμ i j hj k hk)
        (fun i hi k hk ↦ by rw [hT i hi]; exact hσ i k hk)
        (fun i hi k hk ↦ by rw [hT i hi]; exact (H i).gr k hk) hj hk
    have hB : ∀ c < nx S.cen, ∀ b < nx S.cen,
        ((S.blW K.zballs qb L cw).getD (c * nx S.cen + b) (Ball.ofInt 0)).Encl
        (∑ j ∈ range (nx S.cen), ∑ k ∈ range (nx S.cen), (Kraw.ent L.P j c : ℝ) *
          (∑ i ∈ range (S.lk L), ((L.cd * m i + (L.cnW cw) i * (S.lg L i).eval yy) * μ i j k +
            (L.cnW cw) i * σ i j * (deriv k (S.lg L i)).eval a) +
            ∑ i ∈ range S.k, (L.lam i j : ℝ) * σ i k) * (Kraw.ent L.P k b : ℝ)) :=
      fun c hc b hb ↦ by
        rw [blW, getD_tab2 hc hb]
        exact Aff.encl_toBall hδ' (Leaf.encl_bb hE hN c b)
    have hdom' := fun c (hc : c < nx S.cen) ↦ Leaf.dom_sound hB hc (hdom c hc)
    have hPP' : ∀ j < nx S.cen, ∀ k < nx S.cen, ∑ c ∈ range (nx S.cen),
        (Kraw.ent L.P j c : ℝ) * (Kraw.ent L.Pa c k : ℝ) = if j = k then (L.pd : ℝ) else 0 :=
      fun j hj k hk ↦ by
        have hc := congrArg (Int.cast : ℤ → ℝ) (hPP j hj k hk)
        rw [Int.cast_sum] at hc
        rw [show (∑ c ∈ range (nx S.cen), (Kraw.ent L.P j c : ℝ) * (Kraw.ent L.Pa c k : ℝ)) =
          ∑ c ∈ range (nx S.cen), ((Kraw.ent L.P j c * Kraw.ent L.Pa c k : ℤ) : ℝ) from
            sum_congr rfl fun c _ ↦ (Int.cast_mul _ _).symm, hc]
        split_ifs <;> simp
    have hpos := quad_pos_of_dominant_subst
      (fun j k ↦ ∑ i ∈ range (S.lk L),
        ((L.cd * m i + (L.cnW cw) i * (S.lg L i).eval yy) * μ i j k +
          (L.cnW cw) i * σ i j * (deriv k (S.lg L i)).eval a) +
          ∑ i ∈ range S.k, (L.lam i j : ℝ) * σ i k)
      (fun j c ↦ (Kraw.ent L.P j c : ℝ)) (fun c k ↦ (Kraw.ent L.Pa c k : ℝ))
      (pd := (L.pd : ℝ)) (by exact_mod_cast hpd) hPP' hdom' hd
    exact absurd hle (not_le.mpr (lt_of_lt_of_eq hpos hG.symm))
  · have hd0 : ∀ k < nx S.cen, yy k - a k = 0 := fun k hk ↦
      by_contra fun hne ↦ hd ⟨k, hk, hne⟩
    have hk0' : 0 < S.lk L := by
      unfold lk
      omega
    have e := hgs 0 hk0'
    rw [sum_eq_zero fun k hk ↦ by rw [hd0 k (mem_range.mp hk), mul_zero]] at e
    exact absurd (hneg 0 hk0') (by rw [e]; exact lt_irrefl 0)

variable (S) in
/-- The pose unknown along which a refused box is halved: the one with the largest sum of the
magnitudes of its coefficients in the affine forms of the entries of `P^T ν P`. A heuristic; the
soundness of `leafCoreAdW` does not depend on it. -/
def pickW (Z qb : List Ball) (L : LeafRec) (cw : List ℤ) : ℕ :=
  let n := nx S.cen
  let N := Leaf.at2 n (S.nlW Z qb L cw)
  let fs := (List.range n).flatMap fun a ↦ (List.range n).map fun b ↦ Leaf.bb L.P n N a b
  let score (k : ℕ) : ℕ :=
    (fs.map fun f ↦ ((f.lk k).m.natAbs + (f.lk k).r) * 2 ^ (L.bits + 64 - (f.lk k).s)).sum
  (List.range n).foldl (fun best k ↦ if score best < score k then k else best) 0

variable (S) in
/-- **The core check with bisections**: the core on the box `qb`, or, at most `f` times in a
row, on both halves of `qb` along the pose unknown `pickW`. -/
def leafCoreAdW (Z : List Ball) (L : LeafRec) (cw : List ℤ) : ℕ → List Ball → Bool
  | 0, qb => S.leafCoreW Z qb L cw
  | f + 1, qb => S.leafCoreW Z qb L cw ||
      (leafCoreAdW Z L cw f (halfBox (nx S.cen) qb (S.pickW Z qb L cw) false) &&
        leafCoreAdW Z L cw f (halfBox (nx S.cen) qb (S.pickW Z qb L cw) true))

/-- A point of a box that passes the core check with bisections lies in a box that passes the
core check. -/
theorem exists_of_leafCoreAdW {Z : List Ball} {L : LeafRec} {cw : List ℤ} {yy : ℕ → ℝ} :
    ∀ (f : ℕ) (qb : List Ball), S.leafCoreAdW Z L cw f qb = true →
      (∀ j < nx S.cen, (qb.getD j (Ball.ofInt 0)).Encl (yy j)) →
      ∃ qb' : List Ball, S.leafCoreW Z qb' L cw = true ∧
        ∀ j < nx S.cen, (qb'.getD j (Ball.ofInt 0)).Encl (yy j)
  | 0, qb, h, hq => ⟨qb, h, hq⟩
  | f + 1, qb, h, hq => by
    rw [leafCoreAdW, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact ⟨qb, h, hq⟩
    · obtain ⟨up, hup⟩ := encl_halfBox (S.pickW Z qb L cw) hq
      cases up
      · exact exists_of_leafCoreAdW f _ h1 hup
      · exact exists_of_leafCoreAdW f _ h2 hup

variable (S) in
/-- **The check of a touch leaf**, on the balls `Z` of the variables at the zero, for a solid of
`nV` vertices: the leaf's pose box is in the system's charts and has a denominator `2 ^ qs`; the
hole conditions on it (`holesOk`); in general mode the translation's confinement (`confOk`);
and the core on `Q`, after bisections of `Q` if it needs them (`leafCoreAdW`). -/
def leafOkW (nV : ℕ) (Z : List Ball) (L : LeafRec) (cw : List ℤ) : Bool :=
  decide (L.B.view = S.view) && decide (L.B.rot = S.rot) && decide (L.B.box.den = 2 ^ L.qs) &&
    S.holesOk nV Z L && (S.cen || S.confOk Z L) && S.leafCoreAdW Z L cw Leaf.depth L.qb

/-- **Soundness of the touch leaf**: at the scale of the zero, the solid has no strict fit at a
pose of the leaf's box (with any translation). `hVz`: the vertex expressions do not depend on
the pose unknowns; `hsym`: in centred mode the solid is centrally symmetric; `hid`: the
identities of the spread hold. -/
theorem noFitRot_of_leafOkW (hK : K.eqs = S.eqs) {p : ℕ → ℝ} (hp : K.ParOk p)
    {y : Fin K.n → ℝ} (hy : y ∈ K.box) (h0 : K.F p y = 0)
    {P : Polyhedron} {nV : ℕ}
    (hV : ∀ x, x ∈ P.vertices ↔ ∃ v < nV, vertOf (K.env p y) S.V v = x)
    (hVz : ∀ z : ℕ → ℝ, (∀ i, nx S.cen ≤ i → z i = K.env p y i) →
      ∀ v, vertOf z S.V v = vertOf (K.env p y) S.V v)
    (hsym : S.cen = true → ∀ x ∈ P.vertices, -x ∈ P.vertices) {L : LeafRec} {cw : List ℤ}
    (hL : S.leafOkW nV K.zballs L cw = true)
    (hid : ∀ r ∈ L.sp, ∀ z : ℕ → ℝ, (∀ i, nx S.cen ≤ i → z i = K.env p y i) →
      (S.idE r.id).eval z = 0) :
    P.NoFitRot L.B.poses ((lE S.cen).eval (K.env p y) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) := by
  rintro ⟨qv, qs, qt, qr, qx⟩ hq hfit
  simp only [leafOkW, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hL
  obtain ⟨⟨⟨⟨⟨hview, hrot⟩, hden⟩, hhole⟩, hmode⟩, hcore⟩ := hL
  have hqv : qv = S.view := hq.1.trans hview
  have hqr : qr = S.rot := hq.2.1.trans hrot
  have hqb : L.B.box.Mem 5 ![qs, qt, qx 0, qx 1, qx 2] := hq.2.2
  subst hqv hqr
  have hA0 : ∀ i, (Kraw.zball K.zballs i).Encl (K.env p y i) := K.encl_zballs hp hy h0
  have hx : ∀ z : ℕ → ℝ, z 2 = qx 0 → z 3 = qx 1 → z 4 = qx 2 →
      (![z 2, z 3, z 4] : Fin 3 → ℝ) = qx := fun z h2 h3 h4 ↦ by
    funext j
    fin_cases j
    · exact h2
    · exact h3
    · exact h4
  rcases Bool.eq_false_or_eq_true S.cen with hcen | hcen
  · -- centred mode: no translation
    have hnx : nx S.cen = 5 := by rw [hcen]; rfl
    let yy : ℕ → ℝ := fun i ↦
      if h : i < 5 then (![qs, qt, qx 0, qx 1, qx 2] : Fin 5 → ℝ) ⟨i, h⟩ else K.env p y i
    have hfix : ∀ i, nx S.cen ≤ i → yy i = K.env p y i := fun i hi ↦ by
      have h5 : ¬ i < 5 := by omega
      simp only [yy, h5, ↓reduceDIte]
    have hq5 : ∀ i < 5, (boxBall L.B.box L.qs i).Encl (yy i) := fun i hi ↦ by
      have e : yy i = (![qs, qt, qx 0, qx 1, qx 2] : Fin 5 → ℝ) ⟨i, hi⟩ := by
        simp only [yy, hi, ↓reduceDIte]
      rw [e]
      exact encl_boxBall hden (hqb ⟨i, hi⟩)
    have hqe : ∀ i < nx S.cen, (L.qb.getD i (Ball.ofInt 0)).Encl (yy i) := fun i hi ↦ by
      have hi5 : i < 5 := by omega
      rw [LeafRec.qb, getD_map_range (by omega : i < 7)]
      simp only [LeafRec.qf, hi5, ↓reduceIte]
      exact hq5 i hi5
    obtain ⟨qb', hcore', hqe'⟩ := exists_of_leafCoreAdW _ _ hcore hqe
    refine not_all_neg_of_leafCoreW hK hp hy h0 hcore' hid hqe' hfix fun i hi ↦ ?_
    have hpose : poseOf yy S.view S.rot = ⟨S.view, qs, qt, S.rot, qx⟩ := by
      rw [poseOf, hx yy rfl rfl rfl]
      rfl
    have hl : (lE S.cen).eval yy = (lE S.cen).eval (K.env p y) := hfix (nx S.cen) le_rfl
    have hy0 : yOf yy S.cen = 0 := by
      funext c
      simp [yOf, yE, hcen]
    have hvy : ∀ v, vertOf yy S.V v = vertOf (K.env p y) S.V v := hVz yy hfix
    obtain ⟨hvk, hS, hne⟩ := holes_of_holesOk hA0 hV hVz hhole hq5 hfix (S.lcon_mem L hi)
    rw [hpose] at hS hne
    have ho := Polyhedron.orient_pos_of_fitsAlong_centred (hsym hcen) hfit _ _ hS hne hvk
    rw [lg, slack, eval_slackE, hpose, hl, hy0, add_zero, hvy, hvy, hvy]
    exact neg_neg_of_pos (mul_pos (quat_pos _ _) ho)
  · -- general mode: the translation of the fit, confined to its box
    have hnx : nx S.cen = 7 := by rw [hcen]; rfl
    obtain ⟨τ, hτ⟩ := Polyhedron.exists_orient_pos_of_fitsAlong hfit
    let yy : ℕ → ℝ := fun i ↦
      if h : i < 5 then (![qs, qt, qx 0, qx 1, qx 2] : Fin 5 → ℝ) ⟨i, h⟩
      else if i = 5 then τ 0 else if i = 6 then τ 1 else K.env p y i
    have hfix : ∀ i, nx S.cen ≤ i → yy i = K.env p y i := fun i hi ↦ by
      have h5 : ¬ i < 5 := by omega
      have h5' : ¬ i = 5 := by omega
      have h6 : ¬ i = 6 := by omega
      simp only [yy, h5, h5', h6, ↓reduceDIte, ↓reduceIte]
    have hq5 : ∀ i < 5, (boxBall L.B.box L.qs i).Encl (yy i) := fun i hi ↦ by
      have e : yy i = (![qs, qt, qx 0, qx 1, qx 2] : Fin 5 → ℝ) ⟨i, hi⟩ := by
        simp only [yy, hi, ↓reduceDIte]
      rw [e]
      exact encl_boxBall hden (hqb ⟨i, hi⟩)
    have hpose : poseOf yy S.view S.rot = ⟨S.view, qs, qt, S.rot, qx⟩ := by
      rw [poseOf, hx yy rfl rfl rfl]
      rfl
    have hl : (lE S.cen).eval yy = (lE S.cen).eval (K.env p y) := hfix (nx S.cen) le_rfl
    have hyτ : yOf yy S.cen = τ := by
      funext c
      fin_cases c <;> simp [yOf, yE, hcen, yy]
    have hvy : ∀ v, vertOf yy S.V v = vertOf (K.env p y) S.V v := hVz yy hfix
    have hsl : ∀ i < S.lk L, (S.lg L i).eval yy < 0 := fun i hi ↦ by
      obtain ⟨hvk, hS, hne⟩ := holes_of_holesOk hA0 hV hVz hhole hq5 hfix (S.lcon_mem L hi)
      rw [hpose] at hS hne
      have ho := hτ _ _ hS hne _ hvk
      rw [lg, slack, eval_slackE, hpose, hl, hyτ, hvy, hvy, hvy]
      exact neg_neg_of_pos (mul_pos (quat_pos _ _) ho)
    have hslack : ∀ i < S.k, (S.g i).eval yy < 0 := fun i hi ↦ by
      have h := hsl i (by unfold lk; omega)
      rwa [S.lg_of_lt L hi] at h
    have hconf : S.confOk K.zballs L = true := by
      rcases hmode with h | h
      · rw [hcen] at h
        exact absurd h (by decide)
      · exact h
    obtain ⟨qb', hcore', hqe'⟩ := exists_of_leafCoreAdW _ _ hcore
      (encl_of_confOk hA0 hcen hVz hconf hq5 hfix hslack)
    exact not_all_neg_of_leafCoreW hK hp hy h0 hcore' hid hqe' hfix hsl

end Sys
/-! ### Root records with weights -/

namespace RootRec

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] [RootBasis κ]
variable {R : RootRec} {pts : List (V3 κ)} {cw : List ℤ}

/-- The touch leaf with the weights `cw` at the root: no fit at the root's scale in the leaf's
box. -/
theorem noFitRotW {y : Fin (R.kraw pts).n → ℝ} (hpar : RootBasis.parCheck κ R.par = true)
    (hneg : R.cen = true → negOk pts R.neg = true)
    (hL : (R.sys pts).leafOkW pts.length (R.kraw pts).zballs R.L cw = true)
    (hS : (R.sys pts).spOk κ R.L = true)
    (hy : y ∈ (R.kraw pts).box)
    (h0 : (R.kraw pts).F (basisPar κ) y = 0) :
    (Polyhedron.ofPoints pts).NoFitRot R.L.B.poses
      ((R.kraw pts).env (basisPar κ) y (nx R.cen) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) :=
  Sys.noFitRot_of_leafOkW (R.kraw_eqs pts) (parOk hpar) hy h0 (mem_vertices y)
    (fun _ hz v ↦ vertOf_fix y hz v) (fun hc ↦ neg_mem_of_negOk (hneg hc)) hL
    fun _ hr _ hz ↦ Sys.idE_zero_of_spOk (R.kraw_eqs pts) hS hr hz

/-- `RootRec.ok` with the touch leaf's weights `cw`. -/
def okW (R : RootRec) (pts : List (V3 κ)) (cw : List ℤ) : Bool :=
  let K := R.kraw pts
  let Z := K.zballs
  RootBasis.parCheck κ R.par && K.check && (!R.cen || negOk pts R.neg) &&
    (Kraw.zball Z (nx R.cen)).isNonneg &&
    (R.sys pts).weakOk pts.length Z R.W (Sys.zeroCons κ (R.sys pts) Z R.W) &&
    (R.sys pts).leafOkW pts.length Z R.L cw && (R.sys pts).spOk κ R.L

theorem parCheck_of_okW (hok : R.okW pts cw = true) : RootBasis.parCheck κ R.par = true := by
  simp only [okW, Bool.and_eq_true] at hok
  exact hok.1.1.1.1.1.1

/-- **A root's facts** (`RootRec.facts`) with the touch leaf's weights. -/
theorem factsW (hok : R.okW pts cw = true) (hdim : (Polyhedron.ofPoints pts).FullDim) :
    (∃ y, (R.kraw pts).IsZero (basisPar κ) y ∧
      R.scale pts = (R.kraw pts).env (basisPar κ) y (nx R.cen)) ∧
    0 ≤ R.scale pts ∧ R.scale pts ≤ (Polyhedron.ofPoints pts).nieuwland ∧
    (Polyhedron.ofPoints pts).NoFitRot R.L.B.poses
      (R.scale pts • (1 : Matrix (Fin 3) (Fin 3) ℝ)) ∧
    (Kraw.zball (R.kraw pts).zballs (nx R.cen)).Encl (R.scale pts) := by
  simp only [okW, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨hpar, hchk⟩, hneg⟩, hnn⟩, hW⟩, hL⟩, hS⟩ := hok
  obtain ⟨y, ⟨hy, h0⟩, huniq⟩ := (R.kraw pts).existsUnique hchk (parOk hpar)
  have hs := scale_eq (R := R) (pts := pts) (y := y) ⟨⟨hy, h0⟩, huniq⟩
  have e := (R.kraw pts).encl_zballs (parOk hpar) hy h0 (nx R.cen)
  rw [hs]
  have hneg' : R.cen = true → negOk pts R.neg = true := fun hc ↦ by
    simpa [hc] using hneg
  exact ⟨⟨y, ⟨⟨hy, h0⟩, huniq⟩, rfl⟩, Ball.nonneg_sound e hnn, le_nieuwland hpar hW hdim hy h0,
    noFitRotW hpar hneg' hL hS hy h0, e⟩

end RootRec

/-! ### The assembly of one root with weights -/

section Assembly

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] [RootBasis κ]

/-- `certOk` of one root whose touch leaf has the weights `cw`: the root's checks
(`RootRec.okW`), and the far field's scale `θ` at most the root's. -/
def certOkW (pts : List (V3 κ)) (θ : Scale κ) (R : RootRec) (cw : List ℤ) : Bool :=
  R.okW pts cw && scaleLe θ (R.sys pts).n (R.kraw pts).zballs (nx R.cen)

/-- The root of a checked one-root certificate with weights: the zero, its scale, and the
scale is the Nieuwland number of `P`. -/
theorem nieuwland_eq_scale_of_certOkW [Countable κ] {pts : List (V3 κ)} {D : SymmData κ}
    {i j k l : ℕ} (hspan : spanOk pts i j k l = true) {roots : List ChartBox}
    (hroots : unitsIn roots = true) {claims : List ChartBox} {θ : Scale κ} (hθ : θ.ok = true)
    (h : roots.Forall fun B ↦ ∀ p ∈ B.poses, SettledS pts D θ.re p ∨ ∃ C ∈ claims, p ∈ C.poses)
    {P : Polyhedron} {a : ℝ} (hP : P = (Polyhedron.ofPoints pts).smul a) (ha : a ≠ 0)
    {R : RootRec} {cw : List ℤ} (hcl : claims = [R.L.B]) (hok : certOkW pts θ R cw = true) :
    P.nieuwland = R.scale pts := by
  have hdim := Polyhedron.fullDim_of_spanOk hspan
  simp only [certOkW, Bool.and_eq_true] at hok
  obtain ⟨⟨y, hy, hs⟩, hnn, hlo0, hnf, -⟩ := RootRec.factsW hok.1 hdim
  have hle : θ.re ≤ R.scale pts := by
    have h1 := RootRec.scale_le (RootRec.parCheck_of_okW hok.1) hok.2 hy.1.1 hy.1.2
    rwa [← hs] at h1
  have hlo : R.scale pts ≤ P.nieuwland := by
    rw [hP, Polyhedron.nieuwland_smul ha]
    exact hlo0
  refine Polyhedron.nieuwland_eq_of_claims hspan hroots (Scale.re_nonneg_of_ok hθ) hle h ?_ hP ha
    hlo
  intro C hC
  rw [hcl, List.mem_singleton] at hC
  subst hC
  exact Polyhedron.NoFitRot.smul_of_le hnf hnn le_rfl

/-- `nieuwland_eq_of_certOk_one` for a root whose touch leaf has the weights `cw`: the Nieuwland
number is the scale coordinate of the only zero of the root's system in its box. -/
theorem nieuwland_eq_of_certOkW_one [Countable κ] {pts : List (V3 κ)} {D : SymmData κ}
    {i j k l : ℕ} (hspan : spanOk pts i j k l = true) {roots : List ChartBox}
    (hroots : unitsIn roots = true) {claims : List ChartBox} {θ : Scale κ} (hθ : θ.ok = true)
    (h : roots.Forall fun B ↦ ∀ p ∈ B.poses, SettledS pts D θ.re p ∨ ∃ C ∈ claims, p ∈ C.poses)
    {P : Polyhedron} {a : ℝ} (hP : P = (Polyhedron.ofPoints pts).smul a) (ha : a ≠ 0)
    {R : RootRec} {cw : List ℤ} (hcl : claims = [R.L.B]) (hok : certOkW pts θ R cw = true) :
    ∃ y, (R.kraw pts).IsZero (basisPar κ) y ∧
      P.nieuwland = (R.kraw pts).env (basisPar κ) y (nx R.cen) := by
  have hok' := hok
  simp only [certOkW, Bool.and_eq_true] at hok'
  obtain ⟨⟨y, hy, hs⟩, -⟩ := RootRec.factsW hok'.1 (Polyhedron.fullDim_of_spanOk hspan)
  exact ⟨y, hy, (nieuwland_eq_scale_of_certOkW hspan hroots hθ h hP ha hcl hok).trans hs⟩

/-- `nieuwland_mem_Icc_of_certOk` for one root whose touch leaf has the weights `cw`: the root's
ball in an interval puts the Nieuwland number there. -/
theorem nieuwland_mem_Icc_of_certOkW [Countable κ] {pts : List (V3 κ)} {D : SymmData κ}
    {i j k l : ℕ} (hspan : spanOk pts i j k l = true) {roots : List ChartBox}
    (hroots : unitsIn roots = true) {claims : List ChartBox} {θ : Scale κ} (hθ : θ.ok = true)
    (h : roots.Forall fun B ↦ ∀ p ∈ B.poses, SettledS pts D θ.re p ∨ ∃ C ∈ claims, p ∈ C.poses)
    {P : Polyhedron} {a : ℝ} (hP : P = (Polyhedron.ofPoints pts).smul a) (ha : a ≠ 0)
    {R : RootRec} {cw : List ℤ} (hcl : claims = [R.L.B]) (hok : certOkW pts θ R cw = true)
    {lo hi : ℤ} {n : ℕ} (hin : ballsIn pts [R] lo hi n = true) :
    P.nieuwland ∈ Set.Icc ((lo : ℝ) / 10 ^ n) ((hi : ℝ) / 10 ^ n) := by
  rw [nieuwland_eq_scale_of_certOkW hspan hroots hθ h hP ha hcl hok]
  have hok' := hok
  simp only [certOkW, Bool.and_eq_true] at hok'
  exact mem_Icc_of_ballIn (RootRec.factsW hok'.1 (Polyhedron.fullDim_of_spanOk hspan)).2.2.2.2
    (List.all_eq_true.mp hin R List.mem_cons_self)

end Assembly

end Nieuwland.Root
