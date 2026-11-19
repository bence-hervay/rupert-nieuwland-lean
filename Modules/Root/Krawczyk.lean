import Modules.Root.Contraction
import Modules.Root.Slope

/-!
# Krawczyk's test with slopes: the unique zero of a polynomial system in a box

The root of a D2 certificate (`code/src/proof/d2/`, `check_root`) is the zero of a square
polynomial system in a box around a dyadic centre `ŷ = c / 2^s`, with a preconditioner `C`. The
box has a half-width `ρ_i / 2^s > 0` per unknown: the certificate's box has one half-width in the
units of the solid, and over Lean's points (the solid's times their common denominator `L`) its
translation is `L` times as wide and its multipliers `L²` times as narrow, which for the points
of a number field are hundreds of bits. `Kraw.check` is Krawczyk's test in the form that
`Modules/Root/Contraction.lean` needs, on balls (`Modules/Check/Number/Ball.lean`), with slopes in place
of the Jacobian (`Modules/Root/Slope.lean`):

* the slopes `S` of the equations between two points of the box, so `M = 1 - C S` holds
  `1 - C σ(y, y')` for all `y`, `y'` in the box;
* the rows against the box, `R_i = ∑_j M_ij [-ρ_j, ρ_j]`;
* **the box maps into itself**: `T y - ŷ = M(y, ŷ) (y - ŷ) - C F(ŷ)` lies in the ball
  `W_i = R_i - ∑_k C_ik F_k(ŷ)`, and `|W_i| ≤ ρ_i / 2^s`;
* **it contracts**: `|R_i| ≤ ρ_i / 2^(s + 1)` for every row, so points within `t ρ_j` of each
  other in every coordinate have images within `t ρ_i / 2`: the factor `1/2` in the sup distance
  of the coordinates over their half-widths. Krawczyk's own test asks only for a factor below
  `1`; a preconditioner close to the inverse Jacobian on a box as small as a certificate's gives
  a factor near `0`;
* **`C` is invertible**: integers `D`, `d > 0` with `C D = d`.

`Kraw.existsUnique` then gives the unique zero in the box, and `Kraw.encl` its enclosure
`ŷ_i + W_i`, by which later checks decide signs at the root.

The equations are expressions (`Expr`) in the unknowns `0, …, n - 1`; the variables from `n` on
are parameters (the coordinates of a solid's vertices), real numbers known by balls.
-/

open Nieuwland.Check Metric

namespace Nieuwland.Root

namespace Ball'

/-- The sum of the balls `f 0, …, f (n - 1)`. -/
def sum (n : ℕ) (f : ℕ → Ball) : Ball := (List.range n).foldl (fun acc k ↦ acc + f k) (Ball.ofInt 0)

theorem encl_sum {n : ℕ} {f : ℕ → Ball} {x : ℕ → ℝ} (h : ∀ k < n, (f k).Encl (x k)) :
    (sum n f).Encl (∑ k ∈ Finset.range n, x k) := by
  induction n with
  | zero => simpa [sum] using Ball.encl_ofInt 0
  | succ n ih =>
    have ih' := ih fun k hk ↦ h k (Nat.lt_succ_of_lt hk)
    rw [Finset.sum_range_succ]
    have : sum (n + 1) f = sum n f + f n := by simp [sum, List.range_succ]
    rw [this]
    exact Ball.encl_add ih' (h n (Nat.lt_succ_self n))

/-- A bound of what a ball holds. -/
theorem abs_le {b : Ball} {x : ℝ} (h : b.Encl x) : (2 : ℝ) ^ b.s * |x| ≤ b.m.natAbs + b.r := by
  unfold Ball.Encl at h
  have h2 : (0 : ℝ) < 2 ^ b.s := by positivity
  have hm : |(b.m : ℝ)| = (b.m.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
  calc (2 : ℝ) ^ b.s * |x| = |(2 : ℝ) ^ b.s * x| := by rw [abs_mul, abs_of_pos h2]
    _ = |((2 : ℝ) ^ b.s * x - b.m) + b.m| := by ring_nf
    _ ≤ |(2 : ℝ) ^ b.s * x - b.m| + |(b.m : ℝ)| := abs_add_le _ _
    _ ≤ b.m.natAbs + b.r := by rw [hm]; linarith

end Ball'

/-- The data of Krawczyk's test. -/
structure Kraw where
  /-- The equations: as many as unknowns. -/
  eqs : List Expr
  /-- Balls of the parameters (the variables from `eqs.length` on). -/
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

namespace Kraw

variable (K : Kraw)

/-- The number of unknowns. -/
def n : ℕ := K.eqs.length

/-- An entry of an integer matrix. -/
def ent (A : List (List ℤ)) (i k : ℕ) : ℤ := (A.getD i []).getD k 0

/-- The half-width of the unknown `i`, times `2^s`. -/
def rad (i : ℕ) : ℕ := K.ρ.getD i 0

/-- The ball of a coordinate: its interval of the box (`r = rad`) or the centre's (`r = 0`), or
a parameter's ball. -/
def coord (r : ℕ → ℕ) (i : ℕ) : Ball :=
  if i < K.n then ⟨K.c.getD i 0, r i, K.s⟩ else K.par.getD (i - K.n) (Ball.ofInt 0)

/-- The slopes of the equation `k` between two points of the box. -/
def S (k : ℕ) : SBall := slope K.n (K.coord K.rad) (K.coord K.rad) (K.eqs.getD k (.const 0))

/-- The value of the equation `k` at the centre. -/
def Fc (k : ℕ) : Ball :=
  (slope 0 (K.coord fun _ ↦ 0) (K.coord fun _ ↦ 0) (K.eqs.getD k (.const 0))).v

/-- The ball of an entry of the preconditioner. -/
def Cb (i k : ℕ) : Ball := ⟨ent K.C i k, 0, K.cs⟩

/-- The entries of `1 - C S`, from the slopes `Sl`. -/
def M (Sl : List SBall) (i j : ℕ) : Ball :=
  Ball.ofInt (if i = j then 1 else 0) -
    Ball'.sum K.n fun k ↦ K.Cb i k * (Sl.getD k ⟨Ball.ofInt 0, Ball.ofInt 0, []⟩).sl j

/-- The ball of row `i` of `1 - C S` against a vector within the box's half-widths. -/
def R (Sl : List SBall) (i : ℕ) : Ball := Ball'.sum K.n fun j ↦ K.M Sl i j * ⟨0, K.rad j, K.s⟩

/-- The ball of row `i` of `C F(ŷ)`. -/
def CF (Fcs : List Ball) (i : ℕ) : Ball :=
  Ball'.sum K.n fun k ↦ K.Cb i k * Fcs.getD k (Ball.ofInt 0)

/-- The ball of `T y - ŷ`, coordinate `i`, for `y` in the box. -/
def W (Sl : List SBall) (Fcs : List Ball) (i : ℕ) : Ball := K.R Sl i - K.CF Fcs i

/-- The slopes of all equations, computed once. -/
def slopes : List SBall := (List.range K.n).map K.S

/-- The equations' values at the centre, computed once. -/
def centres : List Ball := (List.range K.n).map K.Fc

/-- Krawczyk's test (module docs). -/
def check : Bool :=
  let Sl := K.slopes
  let Fcs := K.centres
  decide (0 < K.d) &&
    (List.range K.n).all (fun i ↦ (List.range K.n).all fun j ↦
      decide ((∑ k ∈ Finset.range K.n, ent K.C i k * ent K.D k j) =
        if i = j then (K.d : ℤ) else 0)) &&
    (List.range K.n).all fun i ↦
      let b := K.R Sl i
      let w := b - K.CF Fcs i
      decide (0 < K.rad i) && decide ((w.m.natAbs + w.r) * 2 ^ K.s ≤ K.rad i * 2 ^ w.s) &&
        decide (2 * (b.m.natAbs + b.r) * 2 ^ K.s ≤ K.rad i * 2 ^ b.s)

/-- The enclosure of the zero's coordinate `i`: `ŷ_i + W_i`. -/
def encl (i : ℕ) : Ball := (⟨K.c.getD i 0, 0, K.s⟩ : Ball) + K.W K.slopes K.centres i

/-! ### Soundness -/

/-- Reals held by the parameters' balls. -/
def ParOk (p : ℕ → ℝ) : Prop := ∀ j, (K.par.getD j (Ball.ofInt 0)).Encl (p j)

/-- The point of all variables: the unknowns `y`, then the parameters `p`. -/
def env (p : ℕ → ℝ) (y : Fin K.n → ℝ) (i : ℕ) : ℝ := if h : i < K.n then y ⟨i, h⟩ else p (i - K.n)

/-- The value of the equation `k` at a point of all variables. -/
def Fr (z : ℕ → ℝ) (k : ℕ) : ℝ := (K.eqs.getD k (.const 0)).eval z

/-- The system as a map of the unknowns. -/
def F (p : ℕ → ℝ) (y : Fin K.n → ℝ) : Fin K.n → ℝ := fun k ↦ K.Fr (K.env p y) k

/-- The centre of the box. -/
noncomputable def centre : Fin K.n → ℝ := fun i ↦ (K.c.getD i 0 : ℝ) / 2 ^ K.s

/-- The half-width of the box in the unknown `i`. -/
noncomputable def radius (i : Fin K.n) : ℝ := (K.rad i : ℝ) / 2 ^ K.s

/-- The box of the test. -/
noncomputable def box : Set (Fin K.n → ℝ) := Root.box K.centre K.radius

/-- The preconditioner's entries. -/
noncomputable def Cr (i k : ℕ) : ℝ := (ent K.C i k : ℝ) / 2 ^ K.cs

/-- The preconditioner. -/
noncomputable def Cm : Matrix (Fin K.n) (Fin K.n) ℝ := fun i k ↦ K.Cr i k

/-- Krawczyk's map `y ↦ y - C F(y)`. -/
noncomputable def T (p : ℕ → ℝ) (y : Fin K.n → ℝ) : Fin K.n → ℝ := y - K.Cm.mulVec (K.F p y)

theorem radius_nonneg (i : Fin K.n) : 0 ≤ K.radius i := by unfold radius; positivity

theorem mem_box {y : Fin K.n → ℝ} : y ∈ K.box ↔ ∀ i, |y i - K.centre i| ≤ K.radius i := Iff.rfl

theorem encl_cb (i k : ℕ) : (K.Cb i k).Encl (K.Cr i k) := by
  have h : (2 : ℝ) ^ K.cs * ((ent K.C i k : ℝ) / 2 ^ K.cs) = ent K.C i k := by field_simp
  change |(2 : ℝ) ^ K.cs * ((ent K.C i k : ℝ) / 2 ^ K.cs) - (ent K.C i k : ℤ)| ≤ ((0 : ℕ) : ℝ)
  simp [h]

theorem encl_coord {p : ℕ → ℝ} (hp : K.ParOk p) {r : ℕ → ℕ} {y : Fin K.n → ℝ}
    (hy : ∀ i : Fin K.n, |y i - K.centre i| ≤ (r i : ℝ) / 2 ^ K.s) (i : ℕ) :
    (K.coord r i).Encl (K.env p y i) := by
  unfold coord env
  split_ifs with h
  · have h2 : (0 : ℝ) < 2 ^ K.s := by positivity
    have hi := hy ⟨i, h⟩
    unfold centre at hi
    change |(2 : ℝ) ^ K.s * y ⟨i, h⟩ - (K.c.getD i 0 : ℤ)| ≤ (r i : ℝ)
    have e : (2 : ℝ) ^ K.s * y ⟨i, h⟩ - (K.c.getD i 0 : ℤ) =
        2 ^ K.s * (y ⟨i, h⟩ - (K.c.getD i 0 : ℝ) / 2 ^ K.s) := by field_simp
    rw [e, abs_mul, abs_of_pos h2]
    calc (2 : ℝ) ^ K.s * |y ⟨i, h⟩ - (K.c.getD i 0 : ℝ) / 2 ^ K.s|
        ≤ 2 ^ K.s * ((r i : ℝ) / 2 ^ K.s) := mul_le_mul_of_nonneg_left hi h2.le
      _ = r i := by field_simp
  · exact hp _

theorem getD_slopes {k : ℕ} (hk : k < K.n) :
    K.slopes.getD k ⟨Ball.ofInt 0, Ball.ofInt 0, []⟩ = K.S k := by
  simp [slopes, List.getD, hk]

theorem getD_centres {k : ℕ} (hk : k < K.n) : K.centres.getD k (Ball.ofInt 0) = K.Fc k := by
  simp [centres, List.getD, hk]

/-- The slopes of the equation `k` between two points of the box. -/
theorem slopes_spec {p : ℕ → ℝ} (hp : K.ParOk p) {y y' : Fin K.n → ℝ}
    (hy : y ∈ K.box) (hy' : y' ∈ K.box) (k : ℕ) :
    ∃ σ : ℕ → ℝ, (∀ j < K.n, ((K.S k).sl j).Encl (σ j)) ∧
      K.Fr (K.env p y) k - K.Fr (K.env p y') k =
        ∑ j ∈ Finset.range K.n, σ j * (K.env p y j - K.env p y' j) :=
  (slope_holds (n := K.n) (K.encl_coord hp hy) (K.encl_coord hp hy')
    (fun i hi ↦ by simp [env, not_lt.mpr hi]) (K.eqs.getD k (.const 0))).2.2

theorem encl_M {σ : ℕ → ℕ → ℝ} (hσ : ∀ k < K.n, ∀ j < K.n, ((K.S k).sl j).Encl (σ k j)) (i : ℕ)
    {j : ℕ} (hj : j < K.n) :
    (K.M K.slopes i j).Encl
      ((if i = j then 1 else 0) - ∑ k ∈ Finset.range K.n, K.Cr i k * σ k j) := by
  unfold M
  refine Ball.encl_sub ?_ (Ball'.encl_sum fun k hk ↦ ?_)
  · by_cases h : i = j
    · simpa [h] using Ball.encl_ofInt 1
    · simpa [h] using Ball.encl_ofInt 0
  · rw [K.getD_slopes hk]
    exact Ball.encl_mul (K.encl_cb i k) (hσ k hk j hj)

/-- `δ - C g = (1 - C σ) δ` in coordinate `i`, when `g = σ δ`. -/
private theorem key (n : ℕ) (C σ : ℕ → ℕ → ℝ) (δ g : ℕ → ℝ) {i : ℕ} (hi : i < n)
    (hg : ∀ k < n, g k = ∑ j ∈ Finset.range n, σ k j * δ j) :
    δ i - ∑ k ∈ Finset.range n, C i k * g k =
      ∑ j ∈ Finset.range n,
        ((if i = j then 1 else 0) - ∑ k ∈ Finset.range n, C i k * σ k j) * δ j := by
  have h1 : ∑ k ∈ Finset.range n, C i k * g k =
      ∑ j ∈ Finset.range n, (∑ k ∈ Finset.range n, C i k * σ k j) * δ j := by
    rw [Finset.sum_congr rfl fun k hk ↦ by rw [hg k (Finset.mem_range.mp hk), Finset.mul_sum]]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_range, hi, ite_true, h1]

theorem T_apply (p : ℕ → ℝ) (y : Fin K.n → ℝ) (i : Fin K.n) :
    K.T p y i = y i - ∑ k ∈ Finset.range K.n, K.Cr i k * K.Fr (K.env p y) k := by
  simp only [T, Pi.sub_apply, Matrix.mulVec, dotProduct, Cm, F]
  rw [← Fin.sum_univ_eq_sum_range (fun k ↦ K.Cr i k * K.Fr (K.env p y) k)]

theorem env_fin (p : ℕ → ℝ) (y : Fin K.n → ℝ) (i : Fin K.n) : K.env p y i = y i := by
  simp [env]

/-- `∑_j (1 - C σ)_ij u_j` lies in the ball `R_i` for `u` within the box's half-widths. -/
theorem encl_R {σ : ℕ → ℕ → ℝ} (hσ : ∀ k < K.n, ∀ j < K.n, ((K.S k).sl j).Encl (σ k j)) (i : ℕ)
    {u : ℕ → ℝ} (hu : ∀ j (hj : j < K.n), |u j| ≤ K.radius ⟨j, hj⟩) :
    (K.R K.slopes i).Encl (∑ j ∈ Finset.range K.n,
      ((if i = j then 1 else 0) - ∑ k ∈ Finset.range K.n, K.Cr i k * σ k j) * u j) := by
  refine Ball'.encl_sum fun j hj ↦ Ball.encl_mul (K.encl_M hσ i hj) ?_
  have h2 : (0 : ℝ) < 2 ^ K.s := by positivity
  change |(2 : ℝ) ^ K.s * u j - ((0 : ℤ) : ℝ)| ≤ ((K.rad j : ℕ) : ℝ)
  rw [Int.cast_zero, sub_zero, abs_mul, abs_of_pos h2]
  calc (2 : ℝ) ^ K.s * |u j| ≤ 2 ^ K.s * K.radius ⟨j, hj⟩ :=
        mul_le_mul_of_nonneg_left (hu j hj) h2.le
    _ = K.rad j := by unfold radius; field_simp

/-- `T y - ŷ` lies in the balls `W` for `y` in the box. -/
theorem encl_W {p : ℕ → ℝ} (hp : K.ParOk p) {y : Fin K.n → ℝ} (hy : y ∈ K.box) (i : Fin K.n) :
    (K.W K.slopes K.centres i).Encl (K.T p y i - K.centre i) := by
  have hc : K.centre ∈ K.box := fun i ↦ by simpa using K.radius_nonneg i
  have hc0 : ∀ i : Fin K.n, |K.centre i - K.centre i| ≤ ((0 : ℕ) : ℝ) / 2 ^ K.s := fun i ↦ by simp
  choose σ hσ hs using fun k ↦ K.slopes_spec hp hy hc k
  have hkey := key K.n K.Cr σ (fun j ↦ K.env p y j - K.env p K.centre j)
    (fun k ↦ K.Fr (K.env p y) k - K.Fr (K.env p K.centre) k) i.2 (fun k _ ↦ hs k)
  have hT : K.T p y i - K.centre i =
      (∑ j ∈ Finset.range K.n, ((if (i : ℕ) = j then 1 else 0) -
        ∑ k ∈ Finset.range K.n, K.Cr i k * σ k j) * (K.env p y j - K.env p K.centre j)) -
        ∑ k ∈ Finset.range K.n, K.Cr i k * K.Fr (K.env p K.centre) k := by
    rw [← hkey, K.T_apply]
    simp only [mul_sub, Finset.sum_sub_distrib, K.env_fin]
    ring
  rw [hT]
  unfold W CF
  refine Ball.encl_sub (K.encl_R (fun k _ j hj ↦ hσ k j hj) i fun j hj ↦ ?_)
    (Ball'.encl_sum fun k hk ↦ Ball.encl_mul (K.encl_cb i k) ?_)
  · rw [K.env_fin p y ⟨j, hj⟩, K.env_fin p K.centre ⟨j, hj⟩]
    exact hy ⟨j, hj⟩
  · rw [K.getD_centres hk]
    exact (slope_holds (n := 0) (K.encl_coord hp hc0) (K.encl_coord hp hc0) (fun _ _ ↦ rfl)
      (K.eqs.getD k (.const 0))).1

/-- The facts of the test. -/
theorem check_iff : K.check = true ↔
    0 < K.d ∧
    (∀ i < K.n, ∀ j < K.n,
      (∑ k ∈ Finset.range K.n, ent K.C i k * ent K.D k j) = if i = j then (K.d : ℤ) else 0) ∧
    ∀ i < K.n, 0 < K.rad i ∧
      ((K.W K.slopes K.centres i).m.natAbs + (K.W K.slopes K.centres i).r) * 2 ^ K.s ≤
        K.rad i * 2 ^ (K.W K.slopes K.centres i).s ∧
      2 * ((K.R K.slopes i).m.natAbs + (K.R K.slopes i).r) * 2 ^ K.s ≤
        K.rad i * 2 ^ (K.R K.slopes i).s := by
  simp only [check, W, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    and_assoc]

/-- The half-widths are positive. -/
theorem radius_pos (h : K.check = true) (i : Fin K.n) : 0 < K.radius i := by
  obtain ⟨-, -, hrow⟩ := K.check_iff.mp h
  have : (0 : ℝ) < K.rad i := by exact_mod_cast (hrow i i.2).1
  unfold radius
  positivity

/-- The box maps into itself. -/
theorem T_mem (h : K.check = true) {p : ℕ → ℝ} (hp : K.ParOk p) {y : Fin K.n → ℝ}
    (hy : y ∈ K.box) : K.T p y ∈ K.box := by
  obtain ⟨-, -, hrow⟩ := K.check_iff.mp h
  intro i
  have hb := Ball'.abs_le (K.encl_W hp hy i)
  have hw : (((K.W K.slopes K.centres i).m.natAbs + (K.W K.slopes K.centres i).r : ℕ) : ℝ) *
      2 ^ K.s ≤ K.rad i * 2 ^ (K.W K.slopes K.centres i).s := by exact_mod_cast (hrow i i.2).2.1
  have h2 : (0 : ℝ) < 2 ^ K.s := by positivity
  have h3 : (0 : ℝ) < 2 ^ (K.W K.slopes K.centres i).s := by positivity
  unfold radius
  rw [le_div_iff₀ h2]
  have h4 : (2 : ℝ) ^ (K.W K.slopes K.centres i).s * (|K.T p y i - K.centre i| * 2 ^ K.s) ≤
      2 ^ (K.W K.slopes K.centres i).s * K.rad i := by
    push_cast at hw
    nlinarith
  exact le_of_mul_le_mul_left h4 h3

/-- The map contracts on the box, in the distance weighted by the half-widths: points within
`t ρ_j` of each other in every coordinate have images within `t ρ_i / 2`. -/
theorem T_contr (h : K.check = true) {p : ℕ → ℝ} (hp : K.ParOk p) {y y' : Fin K.n → ℝ}
    (hy : y ∈ K.box) (hy' : y' ∈ K.box) {t : ℝ} (ht : 0 ≤ t)
    (hd : ∀ j, |y j - y' j| ≤ t * K.radius j) (i : Fin K.n) :
    |K.T p y i - K.T p y' i| ≤ 1 / 2 * t * K.radius i := by
  obtain ⟨-, -, hrow⟩ := K.check_iff.mp h
  rcases ht.eq_or_lt with ht0 | htpos
  · have : y = y' := funext fun j ↦ by
      have hj := hd j
      rw [← ht0, zero_mul] at hj
      exact sub_eq_zero.mp (abs_nonpos_iff.mp hj)
    subst this
    rw [sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) ht) (K.radius_nonneg i)
  choose σ hσ hs using fun k ↦ K.slopes_spec hp hy hy' k
  have hkey := key K.n K.Cr σ (fun j ↦ K.env p y j - K.env p y' j)
    (fun k ↦ K.Fr (K.env p y) k - K.Fr (K.env p y') k) i.2 (fun k _ ↦ hs k)
  have hT : K.T p y i - K.T p y' i =
      ∑ j ∈ Finset.range K.n, ((if (i : ℕ) = j then 1 else 0) -
        ∑ k ∈ Finset.range K.n, K.Cr i k * σ k j) * (K.env p y j - K.env p y' j) := by
    rw [← hkey, K.T_apply, K.T_apply]
    simp only [mul_sub, Finset.sum_sub_distrib, K.env_fin]
    ring
  have hu : ∀ j (hj : j < K.n), |(K.env p y j - K.env p y' j) / t| ≤ K.radius ⟨j, hj⟩ := by
    intro j hj
    rw [K.env_fin p y ⟨j, hj⟩, K.env_fin p y' ⟨j, hj⟩, abs_div, abs_of_pos htpos,
      div_le_iff₀ htpos, mul_comm]
    exact hd ⟨j, hj⟩
  have hb := Ball'.abs_le (K.encl_R (fun k _ j hj ↦ hσ k j hj) i hu)
  have hr : ((2 * ((K.R K.slopes i).m.natAbs + (K.R K.slopes i).r) * 2 ^ K.s : ℕ) : ℝ) ≤
      ((K.rad i * 2 ^ (K.R K.slopes i).s : ℕ) : ℝ) := by exact_mod_cast (hrow i i.2).2.2
  have h2 : (0 : ℝ) < 2 ^ K.s := by positivity
  have h3 : (0 : ℝ) < 2 ^ (K.R K.slopes i).s := by positivity
  have hsum : K.T p y i - K.T p y' i = t * ∑ j ∈ Finset.range K.n,
      ((if (i : ℕ) = j then 1 else 0) - ∑ k ∈ Finset.range K.n, K.Cr i k * σ k j) *
        ((K.env p y j - K.env p y' j) / t) := by
    rw [hT, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by field_simp
  have hhalf : |∑ j ∈ Finset.range K.n, ((if (i : ℕ) = j then 1 else 0) -
      ∑ k ∈ Finset.range K.n, K.Cr i k * σ k j) * ((K.env p y j - K.env p y' j) / t)| ≤
      1 / 2 * K.radius i := by
    unfold radius
    rw [show (1 : ℝ) / 2 * ((K.rad i : ℝ) / 2 ^ K.s) = (K.rad i : ℝ) / (2 * 2 ^ K.s) by
      field_simp, le_div_iff₀ (by positivity)]
    push_cast at hr
    have h5 := mul_le_mul_of_nonneg_right hb (by positivity : (0 : ℝ) ≤ 2 * 2 ^ K.s)
    have h6 : (2 : ℝ) ^ (K.R K.slopes i).s * (|∑ j ∈ Finset.range K.n,
        ((if (i : ℕ) = j then 1 else 0) - ∑ k ∈ Finset.range K.n, K.Cr i k * σ k j) *
          ((K.env p y j - K.env p y' j) / t)| * (2 * 2 ^ K.s)) ≤
        2 ^ (K.R K.slopes i).s * K.rad i := by
      nlinarith
    exact le_of_mul_le_mul_left h6 h3
  rw [hsum, abs_mul, abs_of_pos htpos]
  calc t * _ ≤ t * (1 / 2 * K.radius i) := mul_le_mul_of_nonneg_left hhalf htpos.le
    _ = 1 / 2 * t * K.radius i := by ring

/-- The inverse of the preconditioner. -/
noncomputable def Dm : Matrix (Fin K.n) (Fin K.n) ℝ :=
  fun k j ↦ (ent K.D k j : ℝ) * 2 ^ K.cs / K.d

theorem Cm_mul_Dm (h : K.check = true) : K.Cm * K.Dm = 1 := by
  obtain ⟨hd, hCD, -⟩ := K.check_iff.mp h
  ext i j
  have hc := congrArg (Int.cast : ℤ → ℝ) (hCD i i.2 j j.2)
  push_cast at hc
  have hd' : (K.d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [Matrix.mul_apply, Matrix.one_apply, Cm, Cr, Dm]
  rw [Fin.sum_univ_eq_sum_range
    (fun k ↦ (ent K.C i k : ℝ) / 2 ^ K.cs * ((ent K.D k j : ℝ) * 2 ^ K.cs / K.d))]
  have e : ∀ k, (ent K.C i k : ℝ) / 2 ^ K.cs * ((ent K.D k j : ℝ) * 2 ^ K.cs / K.d) =
      (ent K.C i k : ℝ) * (ent K.D k j : ℝ) / K.d := fun k ↦ by field_simp
  simp_rw [e, div_eq_mul_inv]
  rw [← Finset.sum_mul, hc]
  by_cases hij : i = j
  · subst hij
    simp [hd']
  · have : (i : ℕ) ≠ j := fun h ↦ hij (Fin.ext h)
    simp [hij, this]

/-- **Krawczyk's test is sound**: the system has exactly one zero in the box. -/
theorem existsUnique (h : K.check = true) {p : ℕ → ℝ} (hp : K.ParOk p) :
    ∃! y, y ∈ K.box ∧ K.F p y = 0 :=
  existsUnique_zero (K.F p) K.Cm K.Dm (K.Cm_mul_Dm h) K.centre K.radius (K.radius_pos h)
    (by norm_num) (by norm_num) (fun _ hy ↦ K.T_mem h hp hy)
    (fun _ hy _ hy' _ ht hd i ↦ K.T_contr h hp hy hy' ht hd i)

/-- A zero in the box lies in the enclosure `ŷ + W`. -/
theorem encl_zero {p : ℕ → ℝ} (hp : K.ParOk p) {y : Fin K.n → ℝ}
    (hy : y ∈ K.box) (h0 : K.F p y = 0) (i : Fin K.n) :
    (K.encl i).Encl (y i) := by
  have hT : K.T p y = y := by simp [T, h0]
  have hw := K.encl_W hp hy i
  rw [hT] at hw
  have hc : (⟨K.c.getD i 0, 0, K.s⟩ : Ball).Encl (K.centre i) := by
    have h : (2 : ℝ) ^ K.s * ((K.c.getD i 0 : ℝ) / 2 ^ K.s) = K.c.getD i 0 := by field_simp
    change |(2 : ℝ) ^ K.s * ((K.c.getD i 0 : ℝ) / 2 ^ K.s) - (K.c.getD i 0 : ℤ)| ≤ ((0 : ℕ) : ℝ)
    rw [h, sub_self, abs_zero, Nat.cast_zero]
  have := Ball.encl_add hc hw
  rwa [add_sub_cancel] at this

end Kraw

end Nieuwland.Root
