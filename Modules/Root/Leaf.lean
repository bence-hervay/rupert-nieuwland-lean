import Modules.Check.Chart.ChartBox
import Modules.NoFit.Pre
import Modules.Root.Identity
import Modules.Root.Quad
import Modules.Root.Second

/-!
# The touch leaf of a root

At the zero `a` of a root's system (`Modules/Root/System.lean`) the plug at the root's scale
touches the hole. The leaf record of a D2 certificate (`code/src/proof/d2/`, "Leaf") shows that
no pose of a box `Q` around the zero's pose has a strict fit at that scale. With the multipliers
`m_i` of the zero and a constant `c = cn / cd`, the function
`G = ∑ (cd m_i + cn g_i) g_i` of the pose has, by the second-order expansion of the slacks
(`Modules/Root/Second.lean`) at `a`:

* value `0` at `a` (the slacks vanish there) and no first-order term (the stationarity
  equations of the system: `∑ m_i ∂_v g_i = 0` for the pose unknowns `v`), so
  `G(a + d) = ∑ ν_jk d_j d_k` with `ν_jk = ∑_i (φ_i μ_i,jk + cn σ_i,j γ_i,k)`,
  `φ_i = cd m_i + cn g_i(a + d)`;
* a positive form: with `d = P e`, the matrix `P^T ν P` is diagonally dominant on `Q`
  (`quad_pos_of_dominant`), so `G > 0` off the zero;
* while at a strict fit every `g_i < 0` and `φ_i ≥ 0` on `Q`, so `G ≤ 0`; and at the zero's own
  pose the slacks are `0`, not negative.

`Sys.leafCore` is the check and `Sys.not_all_neg_of_leafCore` its soundness: no point of `Q`
makes every slack negative. The statement is pointwise in `Q`, so the leaf's check
(`Sys.leafCoreAd`) may bisect `Q`: a box that the core refuses is halved along the pose unknown
that the entries of `P^T ν P` depend on most (`Sys.pick`, a heuristic: any choice is sound),
at most `Leaf.depth` times in a row, and the core is asked of each half. [Measured: the Rust
check encloses the Hessian of `G`, this one the form `ν`; on two of the five leaves of the
gyroelongated pentagonal cupola the form's dominance fails on `Q` by 6 % in one row, and
passes after one bisection on one leaf and two on the other.] The enclosures on `Q` are affine
forms in the pose unknowns
(`Modules/Root/Aff.lean`), which keep the first-order cancellations of the polynomials; plain
balls are too wide on the certificates' boxes [measured: the triakis icosahedron's leaf of radius
`2^-12` passes in balls only on boxes of a quarter of its width]. `Sys.leafOk` adds the premises
(the pose box `Q_z`, the hole conditions of the contacts' edges on it, in general mode the
translation's confinement) and `Sys.noFitRot_of_leafOk` concludes `NoFitRot` on the pose box at
the root's scale.

In centred mode `Q = Q_z` and a strict fit needs no translation. In general mode a strict fit
at a pose of `Q_z` has a translation `τ`, and `Q = Q_z × (y_c ± D)²`: the slack of a contact is
affine in the translation, with the gradient `∇_y g_i` a function of the pose
(`eval_slackE_move`). For each direction `w` of `+e1, -e1, +e2, -e2` the record gives weights
`b_i ≥ 0` of the contacts and a common `bd` with `∑ b_i ∇_y g_i` close to `bd w`: with
`e = bd w - ∑ b_i ∇_y g_i` and `G = ∑ b_i g_i` at the centre `y_c` (forms on `Q_z`), the checks
`bd - ε·e > 0` and `D (bd - ε·e) + G ≥ 0` for the four sign pairs `ε` (`Sys.confOk`) give
`|τ - y_c|_∞ ≤ D` at a strict fit (`Sys.encl_of_confOk`): there `∑ b_i g_i(τ) ≤ 0`, that is
`G + bd w·u - e·u ≤ 0` for `u = τ - y_c`, and for the `w` with `w·u = |u|_∞`,
`(bd - |e|_1) |u|_∞ ≤ -G ≤ D (bd - |e|_1)`. This is the checker's `confinement` with the bound
`D` given in the record (the checker computes its own from the same inequalities).

A leaf may have a spread (the checker's "Leaf with a spread"): contacts `j` outside the system,
each with an identity `D_j g_j = ∑ p_ji g_i` of its slack with the system's (`D_j > 0` at the zero
and on `Q`) and a weight `w_j`. Their slacks vanish at the zero too and enter `G` with the
multiplier `0`: `G = ∑ (cd m_i + cn g_i) g_i + ∑ cn g_j²`. At a strict fit `G ≤ 0` as long as
`cd m_i + cn g_i - ∑_j w_j p_ji / D_j ≥ 0` and `w_j + cn g_j ≥ 0` on `Q` (`spread_nonpos`); the
multipliers `m_i` need no sign then (where the contacts' gradients are dependent, a zero of the
system may have a multiplier `0`). The first is tested without a division (`Leaf.fac`). The
hole conditions are those of the spread's edges too. That the identities hold is a premise of
the leaf's theorems (`hid`); `Sys.spOk` tests it over the solid's field.

A leaf may have linear multipliers (the checker's "Leaf with linear multipliers"): integers
`λ_i,k` per contact `i` of the system and pose unknown `k`, the certificate's `l_i,k` times `cd`,
and `G = ∑ (cd m_i + ∑_k λ_i,k d_k + cn g_i) g_i`. The added terms `(λ_i · d) g_i` vanish at the
zero with their gradients, and by the slopes of the slacks they add `∑_i λ_i,j σ_i,k` to `ν_jk`
(`form_eq_lin`); the factors tested are those with the linear parts (`Sys.psil`). The parts make
the leaf of a zero with very small multipliers larger [measured: the triaugmented hexagonal
prism, `notes/residual-j57.md`].

The check differs from the Rust checker's in its arithmetic (slopes about the zero in place of
the Hessian's enclosure, affine forms in place of polynomials expanded to every order, an exact
inverse of `P` in place of its triangular shape), not in what it proves.
-/

open Nieuwland.Check Finset Matrix

namespace Nieuwland.Root

/-! ### Tabulation -/

/-- A function of two indices below `n`, tabulated row by row. -/
def tab2 {α : Type} (n : ℕ) (f : ℕ → ℕ → α) : List α :=
  (List.range (n * n)).map fun i ↦ f (i / n) (i % n)

theorem getD_tab2 {α : Type} {n j k : ℕ} (hj : j < n) (hk : k < n) (f : ℕ → ℕ → α) (d : α) :
    (tab2 n f).getD (j * n + k) d = f j k := by
  have h1 : j * n + k < n * n := by
    calc j * n + k < j * n + n := by omega
      _ = (j + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right n hj
  have h2 : (j * n + k) / n = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hk, Nat.zero_add]
  have h3 : (j * n + k) % n = k := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  rw [tab2, getD_map_range h1, h2, h3]

/-! ### The enclosures of the leaf -/

namespace Leaf

variable {R : Type} [Enc R]

/-- The entry `i` of a list of enclosures. -/
def at1 (l : List R) (i : ℕ) : R := l.getD i (Enc.ofInt 0)

/-- The entry `(j, k)` of a table of enclosures. -/
def at2 (n : ℕ) (l : List R) (j k : ℕ) : R := l.getD (j * n + k) (Enc.ofInt 0)

/-- The entry `i` of a list of expansions. -/
def tat (l : List (TBall R)) (i : ℕ) : TBall R :=
  l.getD i ⟨Enc.ofInt 0, Enc.ofInt 0, [], [], []⟩

/-- The enclosure of `φ_i = cd m_i + cn g_i(a + d)`, the slack by its slopes from the zero;
`M i` encloses the multiplier `m_i`. -/
def phi (cd cn : ℤ) (n : ℕ) (A Zq M : ℕ → R) (T : ℕ → TBall R) (i : ℕ) : R :=
  Enc.ofInt cd * M i + Enc.ofInt cn * Enc.sum n fun k ↦ (T i).s k * (Zq k - A k)

/-- The recursion `facR` on enclosures: from `(N, M)` the spread's contact `j` gives
`(N D_j - w_j p_j M, M D_j)`. -/
def fac (w : ℕ → ℤ) (D p : ℕ → R) (N M : R) : ℕ → R × R
  | 0 => (N, M)
  | j + 1 =>
    let a := fac w D p N M j
    (a.1 * D j - Enc.ofInt (w j) * p j * a.2, a.2 * D j)

/-- The enclosure of `ν_jk = ∑_i (φ_i μ_i,jk + cn σ_i,j γ_i,k)`. -/
def nb (cn : ℤ) (n kk : ℕ) (T : ℕ → TBall R) (Φ : ℕ → R) (j k : ℕ) : R :=
  Enc.sum kk fun i ↦ Φ i * (T i).m n j k + Enc.ofInt cn * (T i).s j * (T i).g k

/-- The enclosure of `∑_k λ_k (y_k - a_k)`, the linear part of a multiplier. -/
def lpart (lam : ℕ → ℤ) (n : ℕ) (A Zq : ℕ → R) : R :=
  Enc.sum n fun k ↦ Enc.ofInt (lam k) * (Zq k - A k)

/-- `nb` with the linear parts' share `∑_{i < kl} λ_i,j σ_i,k` of `ν_jk`; `plain`: a leaf without
linear parts, whose `ν` is `nb`'s. -/
def nbl (cn : ℤ) (n kk : ℕ) (plain : Bool) (lam : ℕ → ℕ → ℤ) (kl : ℕ) (T : ℕ → TBall R)
    (Φ : ℕ → R) (j k : ℕ) : R :=
  if plain then nb cn n kk T Φ j k
  else nb cn n kk T Φ j k + Enc.sum kl fun i ↦ Enc.ofInt (lam i j) * (T i).s k

/-- The enclosure of the entry `(a, b)` of `P^T ν P`. -/
def bb (P : List (List ℤ)) (n : ℕ) (N : ℕ → ℕ → R) (a b : ℕ) : R :=
  Enc.sum n fun j ↦ Enc.sum n fun k ↦
    Enc.ofInt (Kraw.ent P j a) * N j k * Enc.ofInt (Kraw.ent P k b)

/-- The dominance of row `a`: `2 β_aa - ∑_{b ≠ a} (β_ab + β_ba) [-1, 1]`. -/
def dom (n : ℕ) (B : ℕ → ℕ → Ball) (a : ℕ) : Ball :=
  Ball.ofInt 2 * B a a -
    Ball'.sum n fun b ↦ if a = b then Ball.ofInt 0 else (B a b + B b a) * ⟨0, 1, 0⟩

variable {E : R → ℝ → Prop}

theorem encl_phi (hE : Enc.Sound E) {cd cn : ℤ} {n : ℕ} {A Zq M : ℕ → R} {T : ℕ → TBall R}
    {a yy σ : ℕ → ℝ} {m : ℝ} {i : ℕ} (hA : ∀ i, E (A i) (a i)) (hZ : ∀ k, E (Zq k) (yy k))
    (hM : E (M i) m) (hσ : ∀ k < n, E ((T i).s k) (σ k)) :
    E (phi cd cn n A Zq M T i) (cd * m + cn * ∑ k ∈ range n, σ k * (yy k - a k)) :=
  hE.add (hE.mul (hE.ofInt cd) hM)
    (hE.mul (hE.ofInt cn) (hE.sum fun k hk ↦ hE.mul (hσ k hk) (hE.sub (hZ k) (hA k))))

theorem encl_fac (hE : Enc.Sound E) {w : ℕ → ℤ} {D p : ℕ → R} {d q : ℕ → ℝ} {N M : R}
    {x m : ℝ} (hN : E N x) (hM : E M m) :
    ∀ ns : ℕ, (∀ j < ns, E (D j) (d j)) → (∀ j < ns, E (p j) (q j)) →
      E (fac w D p N M ns).1 (facR w d q x m ns).1 ∧ E (fac w D p N M ns).2 (facR w d q x m ns).2
  | 0, _, _ => ⟨hN, hM⟩
  | ns + 1, hD, hp => by
    obtain ⟨h1, h2⟩ := encl_fac hE hN hM ns (fun j hj ↦ hD j (Nat.lt_succ_of_lt hj))
      fun j hj ↦ hp j (Nat.lt_succ_of_lt hj)
    have hd := hD ns (Nat.lt_succ_self ns)
    have hq := hp ns (Nat.lt_succ_self ns)
    exact ⟨hE.sub (hE.mul h1 hd) (hE.mul (hE.mul (hE.ofInt _) hq) h2), hE.mul h2 hd⟩

theorem encl_nb (hE : Enc.Sound E) {cn : ℤ} {n kk : ℕ} {T : ℕ → TBall R} {Φ : ℕ → R}
    {φ : ℕ → ℝ} {μ : ℕ → ℕ → ℕ → ℝ} {σ γ : ℕ → ℕ → ℝ} (hΦ : ∀ i < kk, E (Φ i) (φ i))
    (hμ : ∀ i < kk, ∀ j < n, ∀ k < n, E ((T i).m n j k) (μ i j k))
    (hσ : ∀ i < kk, ∀ k < n, E ((T i).s k) (σ i k))
    (hγ : ∀ i < kk, ∀ k < n, E ((T i).g k) (γ i k)) {j k : ℕ} (hj : j < n) (hk : k < n) :
    E (nb cn n kk T Φ j k) (∑ i ∈ range kk, (φ i * μ i j k + cn * σ i j * γ i k)) :=
  hE.sum fun i hi ↦ hE.add (hE.mul (hΦ i hi) (hμ i hi j hj k hk))
    (hE.mul (hE.mul (hE.ofInt cn) (hσ i hi j hj)) (hγ i hi k hk))

theorem encl_lpart (hE : Enc.Sound E) {lam : ℕ → ℤ} {n : ℕ} {A Zq : ℕ → R} {a yy : ℕ → ℝ}
    (hA : ∀ i, E (A i) (a i)) (hZ : ∀ k, E (Zq k) (yy k)) :
    E (lpart lam n A Zq) (∑ k ∈ range n, (lam k : ℝ) * (yy k - a k)) :=
  hE.sum fun k _ ↦ hE.mul (hE.ofInt _) (hE.sub (hZ k) (hA k))

theorem encl_nbl (hE : Enc.Sound E) {cn : ℤ} {n kk kl : ℕ} {plain : Bool} {lam : ℕ → ℕ → ℤ}
    {T : ℕ → TBall R} {Φ : ℕ → R} {φ : ℕ → ℝ} {μ : ℕ → ℕ → ℕ → ℝ} {σ γ : ℕ → ℕ → ℝ}
    (hpl : plain = true → ∀ i j, lam i j = 0) (hkl : kl ≤ kk)
    (hΦ : ∀ i < kk, E (Φ i) (φ i))
    (hμ : ∀ i < kk, ∀ j < n, ∀ k < n, E ((T i).m n j k) (μ i j k))
    (hσ : ∀ i < kk, ∀ k < n, E ((T i).s k) (σ i k))
    (hγ : ∀ i < kk, ∀ k < n, E ((T i).g k) (γ i k)) {j k : ℕ} (hj : j < n) (hk : k < n) :
    E (nbl cn n kk plain lam kl T Φ j k)
      (∑ i ∈ range kk, (φ i * μ i j k + cn * σ i j * γ i k) +
        ∑ i ∈ range kl, (lam i j : ℝ) * σ i k) := by
  unfold nbl
  split_ifs with h
  · have z : ∑ i ∈ range kl, (lam i j : ℝ) * σ i k = 0 :=
      sum_eq_zero fun i _ ↦ by rw [hpl h i j, Int.cast_zero, zero_mul]
    rw [z, add_zero]
    exact encl_nb hE hΦ hμ hσ hγ hj hk
  · exact hE.add (encl_nb hE hΦ hμ hσ hγ hj hk)
      (hE.sum fun i hi ↦ hE.mul (hE.ofInt _) (hσ i (lt_of_lt_of_le hi hkl) k hk))

theorem encl_bb (hE : Enc.Sound E) {P : List (List ℤ)} {n : ℕ} {N : ℕ → ℕ → R}
    {ν : ℕ → ℕ → ℝ} (hN : ∀ j < n, ∀ k < n, E (N j k) (ν j k)) (a b : ℕ) :
    E (bb P n N a b)
      (∑ j ∈ range n, ∑ k ∈ range n, (Kraw.ent P j a : ℝ) * ν j k * (Kraw.ent P k b : ℝ)) :=
  hE.sum fun j hj ↦ hE.sum fun k hk ↦
    hE.mul (hE.mul (hE.ofInt _) (hN j hj k hk)) (hE.ofInt _)

/-- A positive dominance ball: the row of the symmetrised matrix is dominated by its diagonal
entry. -/
theorem dom_sound {n : ℕ} {B : ℕ → ℕ → Ball} {β : ℕ → ℕ → ℝ}
    (hB : ∀ a < n, ∀ b < n, (B a b).Encl (β a b)) {a : ℕ} (ha : a < n)
    (h : (dom n B a).isPos = true) :
    ∑ b ∈ range n, (if a = b then 0 else |β a b + β b a|) < 2 * β a a := by
  have ht : ∀ b, (⟨0, 1, 0⟩ : Ball).Encl (if 0 ≤ β a b + β b a then (1 : ℝ) else -1) :=
    fun b ↦ by
      unfold Ball.Encl
      split_ifs <;> norm_num
  have habs : ∀ b, (β a b + β b a) * (if 0 ≤ β a b + β b a then (1 : ℝ) else -1) =
      |β a b + β b a| := fun b ↦ by
    split_ifs with h0
    · rw [mul_one, abs_of_nonneg h0]
    · rw [mul_neg_one, abs_of_neg (not_le.mp h0)]
  have h2 : (Ball.ofInt 2).Encl (2 : ℝ) := by exact_mod_cast Ball.encl_ofInt 2
  have henc : (dom n B a).Encl
      (2 * β a a - ∑ b ∈ range n, if a = b then 0 else |β a b + β b a|) := by
    refine Ball.encl_sub (Ball.encl_mul h2 (hB a ha a ha)) (Ball'.encl_sum fun b hb ↦ ?_)
    by_cases hab : a = b
    · simpa [hab] using Ball.encl_ofInt 0
    · simp only [hab, ↓reduceIte]
      rw [← habs b]
      exact Ball.encl_mul (Ball.encl_add (hB a ha b hb) (hB b hb a ha)) (ht b)
  have := Ball.pos_sound henc h
  linarith

end Leaf

/-- The translation's box of a general-mode leaf, `(y0, y1) / 2^ys ± yr / 2^ys` in both
coordinates, and the weights that confine the translation of a strict fit to it (module docs).
Not read in centred mode. -/
structure ConfRec where
  /-- The centre's first coordinate, times `2^ys`. -/
  y0 : ℤ
  /-- The centre's second coordinate, times `2^ys`. -/
  y1 : ℤ
  /-- The half-width `D`, times `2^ys`. -/
  yr : ℕ
  /-- The scale of the box. -/
  ys : ℕ
  /-- The common factor `bd` of the directions. -/
  bd : ℕ
  /-- Per direction `+e1, -e1, +e2, -e2`: the weights of the contacts. -/
  dirs : List (List ℕ)

/-- The weight of the contact `i` in the direction `w`. -/
def ConfRec.b (T : ConfRec) (w i : ℕ) : ℤ := ((T.dirs.getD w []).getD i 0 : ℕ)

theorem ConfRec.b_nonneg (T : ConfRec) (w i : ℕ) : 0 ≤ T.b w i := Int.natCast_nonneg _

/-- A contact of a leaf's spread (module docs): the identity `D g = ∑ p_i g_i` of its slack with
the slacks of the system, `D > 0` at the zero and on the leaf's box, and its weight. -/
structure SpRec where
  /-- The contact and its identity. -/
  id : IdRec
  /-- The weight: the certificate's, times `cd`. -/
  w : ℤ

/-- The touch leaf of a root (module docs). -/
structure LeafRec where
  /-- The pose box `Q_z`. -/
  B : ChartBox
  /-- The box's denominator is `2 ^ qs`. -/
  qs : ℕ
  /-- `c = cn / cd`. -/
  cn : ℤ
  /-- `c = cn / cd`. -/
  cd : ℤ
  /-- The change of coordinates `d = P e`, an integer matrix. -/
  P : List (List ℤ)
  /-- `P Pa = pd`: the inverse of `P` up to `pd ≠ 0`. -/
  Pa : List (List ℤ)
  /-- `P Pa = pd`. -/
  pd : ℤ
  /-- The scale `2^bits` of the balls of the affine forms. -/
  bits : ℕ
  /-- General mode: the translation's box and its confinement. -/
  T : ConfRec
  /-- The spread: contacts outside the system whose slacks enter `G`. -/
  sp : List SpRec
  /-- The linear parts of the multipliers (module docs): per contact of the system the integers
  `λ_i,k` of the pose unknowns; empty for a leaf without them. -/
  lin : List (List ℤ)

/-- The contact `j` of the spread. -/
def LeafRec.spr (L : LeafRec) (j : ℕ) : SpRec := L.sp.getD j ⟨⟨(0, 0, 0), .const 0, []⟩, 0⟩

/-- The linear part `λ_i,k` of the multiplier of the system's contact `i` in the pose unknown
`k`; `0` outside the record. -/
def LeafRec.lam (L : LeafRec) (i k : ℕ) : ℤ := (L.lin.getD i []).getD k 0

theorem LeafRec.lam_of_isEmpty {L : LeafRec} (h : L.lin.isEmpty = true) (i k : ℕ) :
    L.lam i k = 0 := by
  simp [LeafRec.lam, List.isEmpty_iff.mp h]

theorem LeafRec.spr_mem (L : LeafRec) {j : ℕ} (hj : j < L.sp.length) : L.spr j ∈ L.sp := by
  have h : L.spr j = L.sp[j] := by
    simp [LeafRec.spr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rw [h]
  exact List.getElem_mem hj

namespace Sys

variable (S : Sys)

/-- The contacts of the leaf's function `G`: the system's, then the spread's. -/
def lcons (L : LeafRec) : List (ℕ × ℕ × ℕ) := S.contacts ++ L.sp.map (·.id.con)

/-- The number of the contacts of `G`. -/
def lk (L : LeafRec) : ℕ := S.k + L.sp.length

/-- The slack of the contact `i` of `G`. -/
def lg (L : LeafRec) (i : ℕ) : Expr := S.slack ((S.lcons L).getD i (0, 0, 0))

theorem lg_of_lt (L : LeafRec) {i : ℕ} (hi : i < S.k) : S.lg L i = S.g i := by
  unfold lg lcons g con
  rw [List.getD_append _ _ _ _ hi]

theorem lg_add (L : LeafRec) {j : ℕ} (hj : j < L.sp.length) :
    S.lg L (S.k + j) = S.slack (L.spr j).id.con := by
  unfold lg lcons LeafRec.spr k
  rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem lcon_mem (L : LeafRec) {i : ℕ} (hi : i < S.lk L) :
    (S.lcons L).getD i (0, 0, 0) ∈ S.lcons L := by
  have hl : i < (S.lcons L).length := by
    simpa [lcons, lk, k] using hi
  have h : (S.lcons L).getD i (0, 0, 0) = (S.lcons L)[i] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  rw [h]
  exact List.getElem_mem hl

/-- The multipliers at the zero as forms: `0` for the spread's contacts. -/
def zm (p : ℕ) (Z : List Ball) (i : ℕ) : Aff (nx S.cen) p :=
  if i < S.k then Aff.ofBall (Kraw.zball Z (nx S.cen + 1 + i)) else Enc.ofInt 0

/-- The variables at the zero, as constant forms. -/
def za (p : ℕ) (Z : List Ball) (i : ℕ) : Aff (nx S.cen) p := Aff.ofBall (Kraw.zball Z i)

/-- The variables on the leaf's box: the pose unknowns as the variables of the affine forms, on
their intervals of `Q` (`qb`), the others at the zero (`Z`). -/
def zq (p : ℕ) (Z qb : List Ball) (i : ℕ) : Aff (nx S.cen) p :=
  if i < nx S.cen then Aff.varOf (qb.getD i (Ball.ofInt 0)) i else Aff.ofBall (Kraw.zball Z i)

/-- The expansions of the slacks of the contacts of `G` between the zero and `Q`. -/
def tl (Z qb : List Ball) (L : LeafRec) : List (TBall (Aff (nx S.cen) L.bits)) :=
  (List.range (S.lk L)).map fun i ↦
    second (nx S.cen) (S.za L.bits Z) (S.zq L.bits Z qb) (S.lg L i)

/-- The forms of the `φ_i`. -/
def phil (Z qb : List Ball) (L : LeafRec) : List (Aff (nx S.cen) L.bits) :=
  (List.range (S.lk L)).map
    (Leaf.phi L.cd L.cn (nx S.cen) (S.za L.bits Z) (S.zq L.bits Z qb) (S.zm L.bits Z)
      (Leaf.tat (S.tl Z qb L)))

/-- The forms of the factors of the system's contacts, `ψ_i = φ_i + ∑_k λ_i,k (y_k - a_k)`: the
`φ_i` (`Φl`) for a leaf without linear parts. -/
def psil (Z qb : List Ball) (L : LeafRec) (Φl : List (Aff (nx S.cen) L.bits)) :
    List (Aff (nx S.cen) L.bits) :=
  if L.lin.isEmpty then Φl
  else (List.range S.k).map fun i ↦ Leaf.at1 Φl i +
    Leaf.lpart (L.lam i) (nx S.cen) (S.za L.bits Z) (S.zq L.bits Z qb)

/-- The forms of the `ν_jk`. -/
def nl (Z qb : List Ball) (L : LeafRec) : List (Aff (nx S.cen) L.bits) :=
  tab2 (nx S.cen)
    (Leaf.nbl L.cn (nx S.cen) (S.lk L) L.lin.isEmpty L.lam S.k (Leaf.tat (S.tl Z qb L))
      (Leaf.at1 (S.phil Z qb L)))

/-- The balls of `P^T ν P` on `Q`. -/
def bl (Z qb : List Ball) (L : LeafRec) : List Ball :=
  tab2 (nx S.cen) fun a b ↦
    (Leaf.bb L.P (nx S.cen) (Leaf.at2 (nx S.cen) (S.nl Z qb L)) a b).toBall

/-- The form on `Q` of an expression of the spread's identities. -/
def spv (Z qb : List Ball) (L : LeafRec) (e : Expr) : Aff (nx S.cen) L.bits :=
  Enc.val (S.zq L.bits Z qb) e

/-- The core check of a touch leaf on the balls `Z` of the variables at the zero and `qb` of the
pose unknowns on `Q` (module docs): the factors of the system's contacts less the spread's
share (without a spread: the `φ_i`, with their linear parts if the leaf has them), the spread's
`D_j` and factors, the dominance. -/
def leafCore (Z qb : List Ball) (L : LeafRec) : Bool :=
  let n := nx S.cen
  let Φl := S.phil Z qb L
  let Ψl := S.psil Z qb L Φl
  let Bl := S.bl Z qb L
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

/-- A point of `Q` as a point of the variables of the affine forms. -/
theorem exists_delta (p : ℕ) {Z qb : List Ball} {a yy : ℕ → ℝ}
    (hA : ∀ i, (Kraw.zball Z i).Encl (a i))
    (hq : ∀ i < nx S.cen, (qb.getD i (Ball.ofInt 0)).Encl (yy i))
    (hfix : ∀ i, nx S.cen ≤ i → yy i = a i) :
    ∃ δ : ℕ → ℝ, (∀ k, |δ k| ≤ 1) ∧ (∀ i, Aff.Encl δ (S.za p Z i) (a i)) ∧
      ∀ i, Aff.Encl δ (S.zq p Z qb i) (yy i) := by
  have hex : ∀ i, ∃ t : ℝ, |t| ≤ 1 ∧ (i < nx S.cen →
      yy i = ((qb.getD i (Ball.ofInt 0)).m : ℝ) / 2 ^ (qb.getD i (Ball.ofInt 0)).s +
        ((qb.getD i (Ball.ofInt 0)).r : ℝ) / 2 ^ (qb.getD i (Ball.ofInt 0)).s * t) := fun i ↦ by
    by_cases hi : i < nx S.cen
    · obtain ⟨t, ht, e⟩ := Aff.exists_param (hq i hi)
      exact ⟨t, ht, fun _ ↦ e⟩
    · exact ⟨0, by simp, fun h ↦ absurd h hi⟩
  choose δ hδ hyδ using hex
  refine ⟨δ, hδ, fun i ↦ Aff.encl_ofBall δ (hA i), fun i ↦ ?_⟩
  unfold zq
  split_ifs with hi
  · rw [hyδ i hi]
    exact Aff.encl_varOf hi
  · rw [hfix i (not_lt.mp hi)]
    exact Aff.encl_ofBall δ (hA i)

/-- **Soundness of the core of the touch leaf**: no point of `Q` (the pose unknowns in the balls
`qb`, the other variables at the zero) makes every slack of the contacts of `G` negative. `hid`:
the identities of the spread hold. -/
theorem not_all_neg_of_leafCore (hK : K.eqs = S.eqs) {p : ℕ → ℝ} (hp : K.ParOk p)
    {y : Fin K.n → ℝ} (hy : y ∈ K.box) (h0 : K.F p y = 0)
    {qb : List Ball} {L : LeafRec} (hL : S.leafCore K.zballs qb L = true)
    (hid : ∀ r ∈ L.sp, ∀ z : ℕ → ℝ, (∀ i, nx S.cen ≤ i → z i = K.env p y i) →
      (S.idE r.id).eval z = 0) {yy : ℕ → ℝ}
    (hq : ∀ i < nx S.cen, (qb.getD i (Ball.ofInt 0)).Encl (yy i))
    (hfix : ∀ i, nx S.cen ≤ i → yy i = K.env p y i) :
    ¬ ∀ i < S.lk L, (S.lg L i).eval yy < 0 := by
  intro hneg
  have hA0 : ∀ i, (Kraw.zball K.zballs i).Encl (K.env p y i) := K.encl_zballs hp hy h0
  simp only [leafCore, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
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
  have hΦ : ∀ i < S.lk L, Aff.Encl δ (Leaf.at1 (S.phil K.zballs qb L) i)
      (L.cd * m i + L.cn * (S.lg L i).eval yy) := fun i hi ↦ by
    rw [Leaf.at1, phil, getD_map_range hi, hgs i hi]
    exact Leaf.encl_phi hE hA hZ (hM i) fun k hk ↦ by rw [hT i hi]; exact hσ i k hk
  -- ψ: the factors of the system's contacts, with their linear parts
  have hkl : S.k ≤ S.lk L := Nat.le_add_right _ _
  have hΨ : ∀ i < S.k, Aff.Encl δ
      (Leaf.at1 (S.psil K.zballs qb L (S.phil K.zballs qb L)) i)
      (L.cd * m i + L.cn * (S.lg L i).eval yy +
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
  have hG := form_eq_lin (L.cd : ℝ) (L.cn : ℝ) m
    (fun i ↦ (S.lg L i).eval yy) (fun i k ↦ (L.lam i k : ℝ))
    (fun i k ↦ (deriv k (S.lg L i)).eval a) σ μ
    (fun k ↦ yy k - a k) hkl hgs hgm hst
  -- G ≤ 0 at a point where every slack is negative: the factors less the spread's share
  have hDy : ∀ j < L.sp.length, 0 < (L.spr j).id.D.eval yy := fun j hj ↦
    Ball.pos_sound (Aff.encl_toBall hδ' (hE.val hZ _)) (hsp j hj).1.2
  have hle : ∑ i ∈ range (S.lk L),
      (L.cd * m i + L.cn * (S.lg L i).eval yy) * (S.lg L i).eval yy +
      ∑ i ∈ range S.k, (∑ k ∈ range (nx S.cen), (L.lam i k : ℝ) * (yy k - a k)) *
        (S.lg L i).eval yy ≤ 0 := by
    rw [lk, sum_range_add]
    have e1 : ∑ i ∈ range S.k, (L.cd * m i + L.cn * (S.lg L i).eval yy) * (S.lg L i).eval yy =
        ∑ i ∈ range S.k,
          (L.cd * a (nx S.cen + 1 + i) + L.cn * (S.g i).eval yy) * (S.g i).eval yy :=
      sum_congr rfl fun i hi ↦ by
        have hik := mem_range.mp hi
        simp only [hm, hik, ↓reduceIte, S.lg_of_lt L hik]
    have e2 : ∑ j ∈ range L.sp.length,
        (L.cd * m (S.k + j) + L.cn * (S.lg L (S.k + j)).eval yy) * (S.lg L (S.k + j)).eval yy =
        ∑ j ∈ range L.sp.length,
          L.cn * (S.lg L (S.k + j)).eval yy * (S.lg L (S.k + j)).eval yy :=
      sum_congr rfl fun j _ ↦ by simp [hm]
    have e3 : ∑ i ∈ range S.k, (∑ k ∈ range (nx S.cen), (L.lam i k : ℝ) * (yy k - a k)) *
          (S.lg L i).eval yy =
        ∑ i ∈ range S.k, (∑ k ∈ range (nx S.cen), (L.lam i k : ℝ) * (yy k - a k)) *
          (S.g i).eval yy :=
      sum_congr rfl fun i hi ↦ by rw [S.lg_of_lt L (mem_range.mp hi)]
    rw [e1, e2, e3, add_right_comm, ← sum_add_distrib]
    have e4 : ∑ i ∈ range S.k,
        ((L.cd * a (nx S.cen + 1 + i) + L.cn * (S.g i).eval yy) * (S.g i).eval yy +
          (∑ k ∈ range (nx S.cen), (L.lam i k : ℝ) * (yy k - a k)) * (S.g i).eval yy) =
        ∑ i ∈ range S.k, (L.cd * a (nx S.cen + 1 + i) + L.cn * (S.g i).eval yy +
          ∑ k ∈ range (nx S.cen), (L.lam i k : ℝ) * (yy k - a k)) * (S.g i).eval yy :=
      sum_congr rfl fun i _ ↦ by ring
    rw [e4]
    refine spread_nonpos (L.cn : ℝ)
      (fun i ↦ L.cd * a (nx S.cen + 1 + i) + L.cn * (S.g i).eval yy +
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
        Aff.Encl δ (Leaf.at2 (nx S.cen) (S.nl K.zballs qb L) j k)
        (∑ i ∈ range (S.lk L), ((L.cd * m i + L.cn * (S.lg L i).eval yy) * μ i j k +
          L.cn * σ i j * (deriv k (S.lg L i)).eval a) +
          ∑ i ∈ range S.k, (L.lam i j : ℝ) * σ i k) := fun j hj k hk ↦ by
      rw [Leaf.at2, nl, getD_tab2 hj hk]
      exact Leaf.encl_nbl hE (μ := μ) (σ := σ) (γ := fun i k ↦ (deriv k (S.lg L i)).eval a)
        (fun hl ↦ L.lam_of_isEmpty hl) hkl hΦ
        (fun i hi j hj k hk ↦ by rw [hT i hi]; exact hμ i j hj k hk)
        (fun i hi k hk ↦ by rw [hT i hi]; exact hσ i k hk)
        (fun i hi k hk ↦ by rw [hT i hi]; exact (H i).gr k hk) hj hk
    have hB : ∀ c < nx S.cen, ∀ b < nx S.cen,
        ((S.bl K.zballs qb L).getD (c * nx S.cen + b) (Ball.ofInt 0)).Encl
        (∑ j ∈ range (nx S.cen), ∑ k ∈ range (nx S.cen), (Kraw.ent L.P j c : ℝ) *
          (∑ i ∈ range (S.lk L), ((L.cd * m i + L.cn * (S.lg L i).eval yy) * μ i j k +
            L.cn * σ i j * (deriv k (S.lg L i)).eval a) +
            ∑ i ∈ range S.k, (L.lam i j : ℝ) * σ i k) * (Kraw.ent L.P k b : ℝ)) :=
      fun c hc b hb ↦ by
        rw [bl, getD_tab2 hc hb]
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
        ((L.cd * m i + L.cn * (S.lg L i).eval yy) * μ i j k +
          L.cn * σ i j * (deriv k (S.lg L i)).eval a) +
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

/-! ### Bisections of `Q` -/

/-- A half of a ball: the lower one, with `up` the upper one. -/
def _root_.Nieuwland.Root.halfBall (b : Ball) (up : Bool) : Ball :=
  ⟨if up then 2 * b.m + b.r else 2 * b.m - b.r, b.r, b.s + 1⟩

theorem _root_.Nieuwland.Root.encl_halfBall {b : Ball} {x : ℝ} (h : b.Encl x) :
    (halfBall b false).Encl x ∨ (halfBall b true).Encl x := by
  simp only [Ball.Encl, halfBall, Bool.false_eq_true, ↓reduceIte] at h ⊢
  have h2 := abs_le.mp h
  rcases le_total ((2 : ℝ) ^ b.s * x - b.m) 0 with ht | ht
  · left
    rw [abs_le, pow_succ]
    push_cast
    constructor <;> linarith [h2.1, h2.2]
  · right
    rw [abs_le, pow_succ]
    push_cast
    constructor <;> linarith [h2.1, h2.2]

/-- The first `n` balls of `qb`, the ball `i` replaced by a half of it. -/
def _root_.Nieuwland.Root.halfBox (n : ℕ) (qb : List Ball) (i : ℕ) (up : Bool) : List Ball :=
  (List.range n).map fun j ↦
    if j = i then halfBall (qb.getD j (Ball.ofInt 0)) up else qb.getD j (Ball.ofInt 0)

theorem _root_.Nieuwland.Root.encl_halfBox {n : ℕ} {qb : List Ball} {yy : ℕ → ℝ} (i : ℕ)
    (hq : ∀ j < n, (qb.getD j (Ball.ofInt 0)).Encl (yy j)) :
    ∃ up, ∀ j < n, ((halfBox n qb i up).getD j (Ball.ofInt 0)).Encl (yy j) := by
  have key : ∀ up, (i < n → (halfBall (qb.getD i (Ball.ofInt 0)) up).Encl (yy i)) →
      ∀ j < n, ((halfBox n qb i up).getD j (Ball.ofInt 0)).Encl (yy j) := fun up h j hj ↦ by
    rw [halfBox, getD_map_range hj]
    split_ifs with e
    · subst e
      exact h hj
    · exact hq j hj
  by_cases hi : i < n
  · rcases encl_halfBall (hq i hi) with h | h
    · exact ⟨false, key false fun _ ↦ h⟩
    · exact ⟨true, key true fun _ ↦ h⟩
  · exact ⟨false, key false fun h ↦ absurd h hi⟩

/-- The most bisections in a row of a leaf's box (a bound on the work, not a precision). -/
def _root_.Nieuwland.Root.Leaf.depth : ℕ := 5

variable (S) in
/-- The pose unknown along which a refused box is halved: the one with the largest sum of the
magnitudes of its coefficients in the affine forms of the entries of `P^T ν P`. A heuristic; the
soundness of `leafCoreAd` does not depend on it. -/
def pick (Z qb : List Ball) (L : LeafRec) : ℕ :=
  let n := nx S.cen
  let N := Leaf.at2 n (S.nl Z qb L)
  let fs := (List.range n).flatMap fun a ↦ (List.range n).map fun b ↦ Leaf.bb L.P n N a b
  let score (k : ℕ) : ℕ :=
    (fs.map fun f ↦ ((f.lk k).m.natAbs + (f.lk k).r) * 2 ^ (L.bits + 64 - (f.lk k).s)).sum
  (List.range n).foldl (fun best k ↦ if score best < score k then k else best) 0

variable (S) in
/-- **The core check with bisections**: the core on the box `qb`, or, at most `f` times in a
row, on both halves of `qb` along the pose unknown `pick`. -/
def leafCoreAd (Z : List Ball) (L : LeafRec) : ℕ → List Ball → Bool
  | 0, qb => S.leafCore Z qb L
  | f + 1, qb => S.leafCore Z qb L ||
      (leafCoreAd Z L f (halfBox (nx S.cen) qb (S.pick Z qb L) false) &&
        leafCoreAd Z L f (halfBox (nx S.cen) qb (S.pick Z qb L) true))

/-- A point of a box that passes the core check with bisections lies in a box that passes the
core check. -/
theorem exists_of_leafCoreAd {Z : List Ball} {L : LeafRec} {yy : ℕ → ℝ} :
    ∀ (f : ℕ) (qb : List Ball), S.leafCoreAd Z L f qb = true →
      (∀ j < nx S.cen, (qb.getD j (Ball.ofInt 0)).Encl (yy j)) →
      ∃ qb' : List Ball, S.leafCore Z qb' L = true ∧
        ∀ j < nx S.cen, (qb'.getD j (Ball.ofInt 0)).Encl (yy j)
  | 0, qb, h, hq => ⟨qb, h, hq⟩
  | f + 1, qb, h, hq => by
    rw [leafCoreAd, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact ⟨qb, h, hq⟩
    · obtain ⟨up, hup⟩ := encl_halfBox (S.pick Z qb L) hq
      cases up
      · exact exists_of_leafCoreAd f _ h1 hup
      · exact exists_of_leafCoreAd f _ h2 hup

/-! ### The leaf's box -/

/-- The ball of the coordinate `i` of a box with the denominator `2 ^ qs`. -/
def _root_.Nieuwland.Root.boxBall (b : Box) (qs : ℕ) (i : ℕ) : Ball :=
  ⟨b.lo.getD i 0 + b.hi.getD i 0, (b.hi.getD i 0 - b.lo.getD i 0).toNat, qs + 1⟩

theorem _root_.Nieuwland.Root.encl_boxBall {b : Box} {qs : ℕ} (hden : b.den = 2 ^ qs) {i : ℕ}
    {x : ℝ} (h : (b.lo.getD i 0 : ℝ) / b.den ≤ x ∧ x ≤ (b.hi.getD i 0 : ℝ) / b.den) :
    (boxBall b qs i).Encl x := by
  have hd : (0 : ℝ) < 2 ^ qs := by positivity
  have hden' : (b.den : ℝ) = 2 ^ qs := by rw [hden]; norm_cast
  rw [hden'] at h
  have h1 : (b.lo.getD i 0 : ℝ) ≤ x * 2 ^ qs := (div_le_iff₀ hd).mp h.1
  have h2 : x * 2 ^ qs ≤ (b.hi.getD i 0 : ℝ) := (le_div_iff₀ hd).mp h.2
  have hle : b.lo.getD i 0 ≤ b.hi.getD i 0 := by exact_mod_cast h1.trans h2
  have hr : (((b.hi.getD i 0 - b.lo.getD i 0).toNat : ℕ) : ℝ) =
      (b.hi.getD i 0 : ℝ) - b.lo.getD i 0 := by
    have e := congrArg (Int.cast : ℤ → ℝ)
      (Int.toNat_of_nonneg (show 0 ≤ b.hi.getD i 0 - b.lo.getD i 0 by omega))
    push_cast at e
    exact e
  change |(2 : ℝ) ^ (qs + 1) * x - ((b.lo.getD i 0 + b.hi.getD i 0 : ℤ) : ℝ)| ≤
    (((b.hi.getD i 0 - b.lo.getD i 0).toNat : ℕ) : ℝ)
  rw [hr, abs_le, pow_succ]
  push_cast
  constructor <;> linarith

theorem con_mem (S : Sys) {i : ℕ} (hi : i < S.k) : S.con i ∈ S.contacts := by
  have h : S.con i = S.contacts[i] := by
    simp [con, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rw [h]
  exact List.getElem_mem hi

/-- The ball of the pose unknown `i` on the leaf's box, the translation's half-width
`r / 2^ys`. -/
def _root_.Nieuwland.Root.LeafRec.qf (L : LeafRec) (r i : ℕ) : Ball :=
  if i < 5 then boxBall L.B.box L.qs i else ⟨if i = 5 then L.T.y0 else L.T.y1, r, L.T.ys⟩

/-- The balls of the pose unknowns on the leaf's box `Q` (the first five in centred mode). -/
def _root_.Nieuwland.Root.LeafRec.qb (L : LeafRec) : List Ball := (List.range 7).map (L.qf L.T.yr)

/-- The balls of the pose unknowns on `Q_z`, the translation at its centre. -/
def _root_.Nieuwland.Root.LeafRec.qb0 (L : LeafRec) : List Ball := (List.range 7).map (L.qf 0)

theorem _root_.Nieuwland.Root.nx_le (cen : Bool) : nx cen ≤ 7 := by cases cen <;> decide

theorem _root_.Nieuwland.Root.le_nx (cen : Bool) : 5 ≤ nx cen := by cases cen <;> decide

variable (S) in
/-- The point `yy` with the translation at the centre of its box (general mode; in centred mode
the point itself). -/
noncomputable def atC (L : LeafRec) (yy : ℕ → ℝ) (i : ℕ) : ℝ :=
  if 5 ≤ i ∧ i < nx S.cen then ((L.qf 0 i).m : ℝ) / 2 ^ L.T.ys else yy i

theorem atC_of_lt {L : LeafRec} {yy : ℕ → ℝ} {i : ℕ} (hi : i < 5) : S.atC L yy i = yy i := by
  have h : ¬ (5 ≤ i ∧ i < nx S.cen) := fun h ↦ absurd h.1 (by omega)
  simp only [atC, h, ↓reduceIte]

theorem atC_of_ge {L : LeafRec} {yy : ℕ → ℝ} {i : ℕ} (hi : nx S.cen ≤ i) :
    S.atC L yy i = yy i := by
  have h : ¬ (5 ≤ i ∧ i < nx S.cen) := fun h ↦ absurd h.2 (by omega)
  simp only [atC, h, ↓reduceIte]

theorem poseOf_atC (L : LeafRec) (yy : ℕ → ℝ) (a : Fin 3) (k : Fin 4) :
    poseOf (S.atC L yy) a k = poseOf yy a k := by
  simp only [poseOf, atC_of_lt (S := S) (L := L) (yy := yy) (show 0 < 5 by norm_num),
    atC_of_lt (S := S) (L := L) (yy := yy) (show 1 < 5 by norm_num),
    atC_of_lt (S := S) (L := L) (yy := yy) (show 2 < 5 by norm_num),
    atC_of_lt (S := S) (L := L) (yy := yy) (show 3 < 5 by norm_num),
    atC_of_lt (S := S) (L := L) (yy := yy) (show 4 < 5 by norm_num)]

/-- A ball from a centre and a radius over `2^s`. -/
theorem _root_.Nieuwland.Root.Leaf.encl_of_abs_sub_le {m : ℤ} {r s : ℕ} {x : ℝ}
    (h : |x - (m : ℝ) / 2 ^ s| ≤ (r : ℝ) / 2 ^ s) : (⟨m, r, s⟩ : Ball).Encl x := by
  have hs : (0 : ℝ) < 2 ^ s := by positivity
  change |(2 : ℝ) ^ s * x - m| ≤ r
  have e : (2 : ℝ) ^ s * x - m = 2 ^ s * (x - m / 2 ^ s) := by field_simp
  rw [e, abs_mul, abs_of_pos hs]
  calc 2 ^ s * |x - m / 2 ^ s| ≤ 2 ^ s * (r / 2 ^ s) := mul_le_mul_of_nonneg_left h hs.le
    _ = r := by field_simp

/-- The point with the translation at its centre lies in `Q_z`'s balls. -/
theorem encl_atC {L : LeafRec} {yy : ℕ → ℝ}
    (hq : ∀ i < 5, (boxBall L.B.box L.qs i).Encl (yy i)) :
    ∀ i < nx S.cen, (L.qb0.getD i (Ball.ofInt 0)).Encl (S.atC L yy i) := by
  intro i hi
  have h7 : i < 7 := lt_of_lt_of_le hi (nx_le S.cen)
  rw [LeafRec.qb0, getD_map_range h7]
  by_cases h5 : i < 5
  · simp only [atC_of_lt h5, LeafRec.qf, h5, ↓reduceIte]
    exact hq i h5
  · have hc : 5 ≤ i ∧ i < nx S.cen := ⟨by omega, hi⟩
    simp only [atC, hc, and_self, LeafRec.qf, h5, ↓reduceIte]
    exact Leaf.encl_of_abs_sub_le (by simp)

/-! ### The hole conditions -/

variable (S) in
/-- The hole conditions of the edges of the contacts of `G` on `Q_z`, for a solid of `nV`
vertices: every other vertex of the hole lies strictly to the left of the edge of each
contact. -/
def holesOk (nV : ℕ) (Z : List Ball) (L : LeafRec) : Bool :=
  (S.lcons L).all fun c ↦
    decide (c.1 < nV) && decide (c.2.1 < nV) && decide (c.2.2 < nV) &&
    ((List.range nV).any fun w ↦ decide (w ≠ c.1) && decide (w ≠ c.2.1)) &&
    (List.range nV).all fun w ↦ decide (w = c.1) || decide (w = c.2.1) ||
      (Enc.val (S.zq L.bits Z L.qb0) (holeE S.view S.V c.1 c.2.1 w)).toBall.isPos

/-- The hole conditions at a pose of `Q_z`: the plug vertex of a contact is a vertex, and the
hole's shadow lies weakly to the left of the contact's edge, a vertex strictly. `hVz`: the
vertex expressions do not depend on the pose unknowns. -/
theorem holes_of_holesOk {Z : List Ball} {a : ℕ → ℝ} (hA : ∀ i, (Kraw.zball Z i).Encl (a i))
    {P : Polyhedron} {nV : ℕ} (hV : ∀ x, x ∈ P.vertices ↔ ∃ v < nV, vertOf a S.V v = x)
    (hVz : ∀ z : ℕ → ℝ, (∀ i, nx S.cen ≤ i → z i = a i) → ∀ v, vertOf z S.V v = vertOf a S.V v)
    {L : LeafRec} (hH : S.holesOk nV Z L = true) {yy : ℕ → ℝ}
    (hq : ∀ i < 5, (boxBall L.B.box L.qs i).Encl (yy i)) (hfix : ∀ i, nx S.cen ≤ i → yy i = a i)
    {c : ℕ × ℕ × ℕ} (hc : c ∈ S.lcons L) :
    vertOf a S.V c.2.2 ∈ P.vertices ∧
    (∀ w ∈ P.vertices, 0 ≤ orient
      ((poseOf yy S.view S.rot).screen (vertOf a S.V c.1))
      ((poseOf yy S.view S.rot).screen (vertOf a S.V c.2.1))
      ((poseOf yy S.view S.rot).screen w)) ∧
    ∃ w ∈ P.vertices, 0 < orient
      ((poseOf yy S.view S.rot).screen (vertOf a S.V c.1))
      ((poseOf yy S.view S.rot).screen (vertOf a S.V c.2.1))
      ((poseOf yy S.view S.rot).screen w) := by
  have hfix0 : ∀ j, nx S.cen ≤ j → S.atC L yy j = a j := fun j hj ↦
    (atC_of_ge hj).trans (hfix j hj)
  obtain ⟨δ, hδ, -, hZq⟩ := exists_delta L.bits hA (encl_atC hq) hfix0
  have hδ' : ∀ k < nx S.cen, |δ k| ≤ 1 := fun k _ ↦ hδ k
  have hE : Enc.Sound (Aff.Encl (n := nx S.cen) (p := L.bits) δ) := Aff.sound hδ'
  have hv0 : ∀ v, vertOf (S.atC L yy) S.V v = vertOf a S.V v := hVz _ hfix0
  have hmem : ∀ v < nV, vertOf a S.V v ∈ P.vertices := fun v hv ↦ (hV _).mpr ⟨v, hv, rfl⟩
  obtain ⟨⟨⟨⟨hva, hvb⟩, hvk⟩, hany⟩, hhole⟩ :=
    (by simpa only [Bool.and_eq_true, decide_eq_true_eq] using
      List.all_eq_true.mp hH _ hc :
      (((c.1 < nV ∧ c.2.1 < nV) ∧ c.2.2 < nV) ∧
        ((List.range nV).any fun w ↦ decide (w ≠ c.1) && decide (w ≠ c.2.1)) =
          true) ∧
        ((List.range nV).all fun w ↦ decide (w = c.1) || decide (w = c.2.1) ||
          (Enc.val (S.zq L.bits Z L.qb0)
            (holeE S.view S.V c.1 c.2.1 w)).toBall.isPos) = true)
  -- every other vertex of the hole is strictly to the left of the contact's edge
  have hpos : ∀ w < nV, w ≠ c.1 → w ≠ c.2.1 →
      0 < orient
        ((poseOf yy S.view S.rot).screen (vertOf a S.V c.1))
        ((poseOf yy S.view S.rot).screen (vertOf a S.V c.2.1))
        ((poseOf yy S.view S.rot).screen (vertOf a S.V w)) := by
    intro w hw h1 h2
    have h := List.all_eq_true.mp hhole w (List.mem_range.mpr hw)
    simp only [Bool.or_eq_true, decide_eq_true_eq, h1, h2, false_or] at h
    have e := Ball.pos_sound (Aff.encl_toBall hδ' (hE.val hZq _)) h
    rwa [eval_holeE (S.atC L yy) S.view S.rot, poseOf_atC, hv0, hv0, hv0] at e
  refine ⟨hmem _ hvk, fun w hw ↦ ?_, ?_⟩
  · obtain ⟨v, hv, rfl⟩ := (hV w).mp hw
    by_cases h1 : v = c.1
    · rw [h1]
      simp [orient]
    by_cases h2 : v = c.2.1
    · rw [h2]
      apply le_of_eq
      simp only [orient]
      ring
    exact (hpos v hv h1 h2).le
  · obtain ⟨w, hw, hw2⟩ := List.any_eq_true.mp hany
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hw2
    have hw' := List.mem_range.mp hw
    exact ⟨_, hmem w hw', hpos w hw' hw2.1 hw2.2⟩

/-! ### The translation's confinement (general mode) -/

/-- The coordinate `c` of the direction `w` of `+e1, -e1, +e2, -e2`. -/
def _root_.Nieuwland.Root.Leaf.dir (w c : ℕ) : ℤ :=
  if w / 2 = c then (if w % 2 = 0 then 1 else -1) else 0

/-- One direction of the confinement, on real numbers (module docs): `u` the translation from
the centre, `M` its maximum norm, attained along the direction. -/
theorem _root_.Nieuwland.Root.Leaf.conf_le {bd D G e0 e1 u0 u1 M : ℝ} (h0 : |u0| ≤ M)
    (h1 : |u1| ≤ M) (hfit : G + bd * M - (e0 * u0 + e1 * u1) ≤ 0)
    (h : ∀ ε0 ∈ [(1 : ℤ), -1], ∀ ε1 ∈ [(1 : ℤ), -1],
      0 < bd - ε0 * e0 - ε1 * e1 ∧ 0 ≤ D * (bd - ε0 * e0 - ε1 * e1) + G) : M ≤ D := by
  have hsg : ∀ e : ℝ, ∃ ε ∈ [(1 : ℤ), -1], (ε : ℝ) * e = |e| := fun e ↦ by
    rcases le_total 0 e with he | he
    · exact ⟨1, by simp, by simp [abs_of_nonneg he]⟩
    · exact ⟨-1, by simp, by simp [abs_of_nonpos he]⟩
  obtain ⟨ε0, hε0, he0⟩ := hsg e0
  obtain ⟨ε1, hε1, he1⟩ := hsg e1
  obtain ⟨ht, hD⟩ := h ε0 hε0 ε1 hε1
  rw [he0, he1] at ht hD
  have a0 : e0 * u0 ≤ |e0| * M :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left h0 (abs_nonneg _))
  have a1 : e1 * u1 ≤ |e1| * M :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
  have hle : (bd - |e0| - |e1|) * M ≤ (bd - |e0| - |e1|) * D := by nlinarith
  exact le_of_mul_le_mul_left hle ht

variable (S) in
/-- The derivative of the slack of the contact `i` in the translation's coordinate `c`. -/
def gy (c : Fin 2) (i : ℕ) : Expr := slackYE S.view S.rot S.V (S.con i).1 (S.con i).2.1 c

variable (S) in
/-- The form of `∑ b_i f_i` over the contacts on `Q_z`, the translation at its centre, with the
weights of the direction `w`. -/
def confSum (Z : List Ball) (L : LeafRec) (w : ℕ) (f : ℕ → Expr) : Aff (nx S.cen) L.bits :=
  Enc.sum S.k fun i ↦ Enc.ofInt (L.T.b w i) * Enc.val (S.zq L.bits Z L.qb0) (f i)

variable (S) in
/-- The test of the direction `w` of the confinement (module docs). -/
def confDirOk (Z : List Ball) (L : LeafRec) (w : ℕ) : Bool :=
  let G : Aff (nx S.cen) L.bits := S.confSum Z L w S.g
  let e0 : Aff (nx S.cen) L.bits :=
    Enc.ofInt ((L.T.bd : ℤ) * Leaf.dir w 0) - S.confSum Z L w (S.gy 0)
  let e1 : Aff (nx S.cen) L.bits :=
    Enc.ofInt ((L.T.bd : ℤ) * Leaf.dir w 1) - S.confSum Z L w (S.gy 1)
  [(1 : ℤ), -1].all fun ε0 ↦ [(1 : ℤ), -1].all fun ε1 ↦
    let t : Aff (nx S.cen) L.bits :=
      Enc.ofInt (L.T.bd : ℤ) - Enc.ofInt ε0 * e0 - Enc.ofInt ε1 * e1
    t.toBall.isPos &&
      (Enc.ofInt (L.T.yr : ℤ) * t + Enc.ofInt ((2 : ℤ) ^ L.T.ys) * G).toBall.isNonneg

variable (S) in
/-- **The check of the translation's confinement** (module docs): the four directions. -/
def confOk (Z : List Ball) (L : LeafRec) : Bool := (List.range 4).all (S.confDirOk Z L)

/-- One direction of the confinement: if the translation's distance `M` from the centre is
attained along the direction `w`, it is at most `D`. -/
theorem le_of_confDirOk {Z : List Ball} {a : ℕ → ℝ} (hA : ∀ i, (Kraw.zball Z i).Encl (a i))
    (hcen : S.cen = false)
    (hVz : ∀ z : ℕ → ℝ, (∀ i, nx S.cen ≤ i → z i = a i) → ∀ v, vertOf z S.V v = vertOf a S.V v)
    {L : LeafRec} {w : ℕ} (hC : S.confDirOk Z L w = true) {yy : ℕ → ℝ}
    (hq : ∀ i < 5, (boxBall L.B.box L.qs i).Encl (yy i)) (hfix : ∀ i, nx S.cen ≤ i → yy i = a i)
    (hneg : ∀ i < S.k, (S.g i).eval yy < 0) {M : ℝ}
    (h0 : |yy 5 - S.atC L yy 5| ≤ M) (h1 : |yy 6 - S.atC L yy 6| ≤ M)
    (hM : (Leaf.dir w 0 : ℝ) * (yy 5 - S.atC L yy 5) +
      (Leaf.dir w 1 : ℝ) * (yy 6 - S.atC L yy 6) = M) :
    M ≤ (L.T.yr : ℝ) / 2 ^ L.T.ys := by
  have hnx : nx S.cen = 7 := by rw [hcen]; rfl
  have hfix0 : ∀ j, nx S.cen ≤ j → S.atC L yy j = a j := fun j hj ↦
    (atC_of_ge hj).trans (hfix j hj)
  obtain ⟨δ, hδ, -, hZq⟩ := exists_delta L.bits hA (encl_atC hq) hfix0
  have hδ' : ∀ k < nx S.cen, |δ k| ≤ 1 := fun k _ ↦ hδ k
  have hE : Enc.Sound (Aff.Encl (n := nx S.cen) (p := L.bits) δ) := Aff.sound hδ'
  -- the slacks along the translation
  have hmove : ∀ i, (S.g i).eval yy = (S.g i).eval (S.atC L yy) +
      ((S.gy 0 i).eval (S.atC L yy) * (yy 5 - S.atC L yy 5) +
        (S.gy 1 i).eval (S.atC L yy) * (yy 6 - S.atC L yy 6)) := fun i ↦ by
    rw [g, slack, hcen]
    exact eval_slackE_move S.view S.rot S.V _ _ _
      (atC_of_lt (by norm_num)).symm (atC_of_lt (by norm_num)).symm
      (atC_of_lt (by norm_num)).symm (atC_of_lt (by norm_num)).symm
      (atC_of_lt (by norm_num)).symm (atC_of_ge (by rw [hnx])).symm
      fun v ↦ (hVz yy hfix v).trans (hVz _ hfix0 v).symm
  -- the forms of the weighted sums
  have hsum : ∀ f : ℕ → Expr, Aff.Encl δ (S.confSum Z L w f)
      (∑ i ∈ range S.k, (L.T.b w i : ℝ) * (f i).eval (S.atC L yy)) := fun f ↦
    hE.sum fun i _ ↦ hE.mul (hE.ofInt _) (hE.val hZq _)
  -- at a strict fit the weighted sum of the slacks is not positive
  have hfit : ∑ i ∈ range S.k, (L.T.b w i : ℝ) * (S.g i).eval (S.atC L yy) +
      ((∑ i ∈ range S.k, (L.T.b w i : ℝ) * (S.gy 0 i).eval (S.atC L yy)) *
          (yy 5 - S.atC L yy 5) +
        (∑ i ∈ range S.k, (L.T.b w i : ℝ) * (S.gy 1 i).eval (S.atC L yy)) *
          (yy 6 - S.atC L yy 6)) ≤ 0 := by
    have hle : ∑ i ∈ range S.k, (L.T.b w i : ℝ) * (S.g i).eval yy ≤ 0 :=
      sum_nonpos fun i hi ↦ mul_nonpos_of_nonneg_of_nonpos
        (by exact_mod_cast L.T.b_nonneg w i) (hneg i (mem_range.mp hi)).le
    refine le_of_eq_of_le ?_ hle
    rw [sum_mul, sum_mul, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun i _ ↦ by rw [hmove i]; ring
  refine Leaf.conf_le (bd := (L.T.bd : ℝ))
    (G := ∑ i ∈ range S.k, (L.T.b w i : ℝ) * (S.g i).eval (S.atC L yy))
    (e0 := (L.T.bd : ℝ) * (Leaf.dir w 0 : ℝ) -
      ∑ i ∈ range S.k, (L.T.b w i : ℝ) * (S.gy 0 i).eval (S.atC L yy))
    (e1 := (L.T.bd : ℝ) * (Leaf.dir w 1 : ℝ) -
      ∑ i ∈ range S.k, (L.T.b w i : ℝ) * (S.gy 1 i).eval (S.atC L yy)) h0 h1 ?_ ?_
  · rw [← hM]
    linarith
  · intro ε0 hε0 ε1 hε1
    simp only [confDirOk, List.all_eq_true, Bool.and_eq_true] at hC
    obtain ⟨hpos, hnn⟩ := hC ε0 hε0 ε1 hε1
    have he : ∀ c : Fin 2, Aff.Encl δ
        (Enc.ofInt ((L.T.bd : ℤ) * Leaf.dir w c) - S.confSum Z L w (S.gy c))
        ((L.T.bd : ℝ) * (Leaf.dir w c : ℝ) -
          ∑ i ∈ range S.k, (L.T.b w i : ℝ) * (S.gy c i).eval (S.atC L yy)) := fun c ↦ by
      have h := hE.sub (hE.ofInt ((L.T.bd : ℤ) * Leaf.dir w c)) (hsum (S.gy c))
      push_cast at h
      exact h
    have ht := hE.sub (hE.sub (hE.ofInt (L.T.bd : ℤ)) (hE.mul (hE.ofInt ε0) (he 0)))
      (hE.mul (hE.ofInt ε1) (he 1))
    have h1 := Ball.pos_sound (Aff.encl_toBall hδ' ht) hpos
    have h2 := Ball.nonneg_sound (Aff.encl_toBall hδ'
      (hE.add (hE.mul (hE.ofInt (L.T.yr : ℤ)) ht)
        (hE.mul (hE.ofInt ((2 : ℤ) ^ L.T.ys)) (hsum S.g)))) hnn
    push_cast at h1 h2
    simp only [Fin.val_zero, Fin.val_one] at h1 h2
    refine ⟨h1, ?_⟩
    have hs : (0 : ℝ) < 2 ^ L.T.ys := by positivity
    rw [div_mul_eq_mul_div, div_add' _ _ _ hs.ne']
    exact div_nonneg (by linarith) hs.le

/-- **Soundness of the confinement**: at a pose of `Q_z`, a translation that makes every slack
negative lies in the translation's box, so the point lies in `Q`. -/
theorem encl_of_confOk {Z : List Ball} {a : ℕ → ℝ} (hA : ∀ i, (Kraw.zball Z i).Encl (a i))
    (hcen : S.cen = false)
    (hVz : ∀ z : ℕ → ℝ, (∀ i, nx S.cen ≤ i → z i = a i) → ∀ v, vertOf z S.V v = vertOf a S.V v)
    {L : LeafRec} (hC : S.confOk Z L = true) {yy : ℕ → ℝ}
    (hq : ∀ i < 5, (boxBall L.B.box L.qs i).Encl (yy i)) (hfix : ∀ i, nx S.cen ≤ i → yy i = a i)
    (hneg : ∀ i < S.k, (S.g i).eval yy < 0) :
    ∀ i < nx S.cen, (L.qb.getD i (Ball.ofInt 0)).Encl (yy i) := by
  have hnx : nx S.cen = 7 := by rw [hcen]; rfl
  have hdir : ∀ w < 4, ∀ M : ℝ, |yy 5 - S.atC L yy 5| ≤ M → |yy 6 - S.atC L yy 6| ≤ M →
      (Leaf.dir w 0 : ℝ) * (yy 5 - S.atC L yy 5) +
        (Leaf.dir w 1 : ℝ) * (yy 6 - S.atC L yy 6) = M → M ≤ (L.T.yr : ℝ) / 2 ^ L.T.ys :=
    fun w hw M h0 h1 hM ↦ le_of_confDirOk hA hcen hVz
      (List.all_eq_true.mp hC w (List.mem_range.mpr hw)) hq hfix hneg h0 h1 hM
  -- the maximum norm is attained along one of the four directions
  have hmax : max |yy 5 - S.atC L yy 5| |yy 6 - S.atC L yy 6| ≤ (L.T.yr : ℝ) / 2 ^ L.T.ys := by
    rcases le_total |yy 6 - S.atC L yy 6| |yy 5 - S.atC L yy 5| with h | h
    · rw [max_eq_left h]
      rcases le_total 0 (yy 5 - S.atC L yy 5) with hs | hs
      · exact hdir 0 (by norm_num) _ le_rfl h (by simp [Leaf.dir, abs_of_nonneg hs])
      · exact hdir 1 (by norm_num) _ le_rfl h (by simp [Leaf.dir, abs_of_nonpos hs])
    · rw [max_eq_right h]
      rcases le_total 0 (yy 6 - S.atC L yy 6) with hs | hs
      · exact hdir 2 (by norm_num) _ h le_rfl (by simp [Leaf.dir, abs_of_nonneg hs])
      · exact hdir 3 (by norm_num) _ h le_rfl (by simp [Leaf.dir, abs_of_nonpos hs])
  have hc5 : S.atC L yy 5 = (L.T.y0 : ℝ) / 2 ^ L.T.ys := by
    simp [atC, hnx, LeafRec.qf]
  have hc6 : S.atC L yy 6 = (L.T.y1 : ℝ) / 2 ^ L.T.ys := by
    simp [atC, hnx, LeafRec.qf]
  intro i hi
  have h7 : i < 7 := by omega
  rw [LeafRec.qb, getD_map_range h7]
  by_cases h5 : i < 5
  · simp only [LeafRec.qf, h5, ↓reduceIte]
    exact hq i h5
  · by_cases h6 : i = 5
    · subst h6
      simp only [LeafRec.qf, lt_self_iff_false, ↓reduceIte]
      apply Leaf.encl_of_abs_sub_le
      rw [← hc5]
      exact (le_max_left _ _).trans hmax
    · obtain rfl : i = 6 := by omega
      simp only [LeafRec.qf, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte]
      apply Leaf.encl_of_abs_sub_le
      rw [← hc6]
      exact (le_max_right _ _).trans hmax

/-! ### The leaf -/

variable (S) in
/-- **The check of a touch leaf**, on the balls `Z` of the variables at the zero, for a solid of
`nV` vertices: the leaf's pose box is in the system's charts and has a denominator `2 ^ qs`; the
hole conditions on it (`holesOk`); in general mode the translation's confinement (`confOk`);
and the core on `Q`, after bisections of `Q` if it needs them (`leafCoreAd`). -/
def leafOk (nV : ℕ) (Z : List Ball) (L : LeafRec) : Bool :=
  decide (L.B.view = S.view) && decide (L.B.rot = S.rot) && decide (L.B.box.den = 2 ^ L.qs) &&
    S.holesOk nV Z L && (S.cen || S.confOk Z L) && S.leafCoreAd Z L Leaf.depth L.qb

/-- **Soundness of the touch leaf**: at the scale of the zero, the solid has no strict fit at a
pose of the leaf's box (with any translation). `hVz`: the vertex expressions do not depend on
the pose unknowns; `hsym`: in centred mode the solid is centrally symmetric; `hid`: the
identities of the spread hold. -/
theorem noFitRot_of_leafOk (hK : K.eqs = S.eqs) {p : ℕ → ℝ} (hp : K.ParOk p)
    {y : Fin K.n → ℝ} (hy : y ∈ K.box) (h0 : K.F p y = 0)
    {P : Polyhedron} {nV : ℕ}
    (hV : ∀ x, x ∈ P.vertices ↔ ∃ v < nV, vertOf (K.env p y) S.V v = x)
    (hVz : ∀ z : ℕ → ℝ, (∀ i, nx S.cen ≤ i → z i = K.env p y i) →
      ∀ v, vertOf z S.V v = vertOf (K.env p y) S.V v)
    (hsym : S.cen = true → ∀ x ∈ P.vertices, -x ∈ P.vertices) {L : LeafRec}
    (hL : S.leafOk nV K.zballs L = true)
    (hid : ∀ r ∈ L.sp, ∀ z : ℕ → ℝ, (∀ i, nx S.cen ≤ i → z i = K.env p y i) →
      (S.idE r.id).eval z = 0) :
    P.NoFitRot L.B.poses ((lE S.cen).eval (K.env p y) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) := by
  rintro ⟨qv, qs, qt, qr, qx⟩ hq hfit
  simp only [leafOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hL
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
    obtain ⟨qb', hcore', hqe'⟩ := exists_of_leafCoreAd _ _ hcore hqe
    refine not_all_neg_of_leafCore hK hp hy h0 hcore' hid hqe' hfix fun i hi ↦ ?_
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
    obtain ⟨qb', hcore', hqe'⟩ := exists_of_leafCoreAd _ _ hcore
      (encl_of_confOk hA0 hcen hVz hconf hq5 hfix hslack)
    exact not_all_neg_of_leafCore hK hp hy h0 hcore' hid hqe' hfix hsl

/-! ### The identities of the spread -/

section Spread

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

variable (S) in
/-- The identities of a leaf's spread over `κ`: each `D g - ∑ p_i g_i` expands to the polynomial
without terms. -/
def spOk (κ : Type) [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] (L : LeafRec) : Bool :=
  L.sp.all fun r ↦ (toSP κ S.n (S.idE r.id)).terms.isEmpty

/-- The identities of the spread hold at every point with the parameters of the zero. -/
theorem idE_zero_of_spOk (hK : K.eqs = S.eqs) {y : Fin K.n → ℝ} {L : LeafRec}
    (h : S.spOk κ L = true) {r : SpRec} (hr : r ∈ L.sp) {z : ℕ → ℝ}
    (hz : ∀ i, nx S.cen ≤ i → z i = K.env (basisPar κ) y i) : (S.idE r.id).eval z = 0 := by
  have hz' : ∀ j, z (S.n + j) = basisPar κ j := fun j ↦ by
    rw [hz _ (by unfold n nv; omega), ← Sys.n_eq hK, Kraw.env_par]
  exact eval_eq_zero_of_toSP S.n z hz' (List.all_eq_true.mp h r hr)

end Spread

end Sys

end Nieuwland.Root
