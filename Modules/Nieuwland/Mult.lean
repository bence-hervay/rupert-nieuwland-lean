import Modules.Check.Polynomial.Sparse
import Modules.Nieuwland.Settled

/-!
# Multiplier leaves

The check of `multiplier` evidence (`code/src/proof/regional/multiplier.rs`, its contract and
proof in the module documentation; `notes/multiplier-leaf.md`) at a plug scale `θ = ν / d`
(`Scale`). Evidence: groups `g` of terms `(j, m)` that share a direction `c_g = v_b - v_a`, with
a plug point `v_j` and a multiplier `m(z)`, a sparse polynomial in the chart coordinates
`z = (s, t, x₀, x₁, x₂)` with exact coefficients. With `u` the view, `Q = Q(q)`, `d = |q|²`:

* `P(z) = ∑_g ∑_{(j, m) ∈ g} m u ⬝ᵥ (c_g ⨯₃ Q ν v_j)`, the plug part with the plug scaled by `ν`;
* `V_g(z) = (∑_{(j, m) ∈ g} m) d (u ⨯₃ c_g)`;
* the hole points `d' v_a` (`d'` the scale's denominator) and the translation bound
  `T = max_a |d' v_a|₁ + |ν v₀|₁` (none for centred evidence).

In tensor Bernstein form at the degree `D` (the multipliers' degree plus `(1, 1, 2, 2, 2)`) on the
box, the check passes if every coefficient of every multiplier is `≥ 0` and for every index `β`

  `P_β - ∑_g max_a (d' v_a) ⬝ᵥ V_{g,β} - T |∑_g V_{g,β}|₁ > 0`.

This is the Rust condition multiplied by `d' > 0`. The Bernstein coefficients are read from the
polynomials themselves (`bcoef`), which are computed exactly as sparse polynomials (`SP`); Rust
computes the same coefficients by products of Bernstein forms.

The rows are evaluated without the direction in the polynomial: `V_g = W_g ⨯₃ c_g` with
`W_g(z) = (∑_{(j, m) ∈ g} m) d u` (`holeW`), so `V_{g,β} = W_{g,β} ⨯₃ c_g` and
`(d' v_a) ⬝ᵥ V_{g,β} = (c_g ⨯₃ d' v_a) ⬝ᵥ W_{g,β}` (`GRow`). The vectors `c_g ⨯₃ d' v_a` are
computed once for a leaf, and every product of a row has `W_{g,β}` as a factor, whose
coordinates are rational when the multipliers' are (as the search's are): over a number field of
degree `n` such a product costs `n` integer products, not the `2 n²` of two general elements
(measured at degree 24: 5 µs against 430 µs, and a leaf has `6 · rows · groups · points` of
them). A coefficient is *scaled* (times the
binomials of its index) and homogeneous: on `[L / D₀, H / D₀]` the monomial `z^e` at degree `n` is
`(D₀ X + D₀ Y)^(n - e) (L X + H Y)^e` (`uni`), so at `X = H - D₀ z`, `Y = D₀ z - L` (both `≥ 0`
on the box) its value is `(D₀ (H - L))^n z^e`.

Groups need not have distinct directions: the argument holds for any grouping (the exporter
groups by direction, as Rust does, so the condition is Rust's).
-/

namespace Nieuwland.Check

/-- A group of a multiplier leaf: the direction `pt b - pt a` of `dir = (a, b)`, and its terms
`(j, m)`: the plug point `j` and the multiplier `m` in the chart coordinates `0, …, 4`. -/
structure MGroup (κ : Type) where
  /-- The direction, as indices `(a, b)` of points. -/
  dir : ℕ × ℕ
  /-- The terms: plug point and multiplier. -/
  terms : List (ℕ × SPoly κ)

/-- A multiplier leaf: centred or not, and its groups. -/
structure MLeaf (κ : Type) where
  /-- Centred evidence (no translation bound; the points must be centrally symmetric). -/
  centred : Bool
  /-- The groups. -/
  groups : List (MGroup κ)

namespace Mult

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-! ### Computation -/

section Comp

/-- `x` added to the head of a coefficient list. -/
def addHead {α : Type*} [Add α] (x : α) : List α → List α
  | [] => [x]
  | d :: r => (x + d) :: r

/-- The homogeneous form times `p X + q Y`: coefficients of `X^(n - j) Y^j`, `j = 0, …, n`
(`z` is zero). -/
def mulLin {α : Type*} [Add α] [Mul α] (z p q : α) : List α → List α
  | [] => [z]
  | c :: l => (p * c) :: addHead (q * c) (mulLin z p q l)

/-- The scaled Bernstein coefficients of `z^e` at degree `n` on `[L / D₀, H / D₀]`:
`(D₀ X + D₀ Y)^(n - e) (L X + H Y)^e`. -/
def uni (D₀ L H : κ) (n e : ℕ) : List κ :=
  (mulLin (Exact.ofInt 0) L H)^[e] ((mulLin (Exact.ofInt 0) D₀ D₀)^[n - e] [Exact.ofInt 1])

/-- The first variable's Bernstein index `β₀` substituted: each term `c x₀^e₀ m` becomes
`c U[e₀][β₀] m` in the remaining variables, like terms merged (`SPoly.normal`). -/
def subst (U : List (List κ)) (β₀ : ℕ) (p : SPoly κ) : SPoly κ :=
  SPoly.normal (p.map fun t ↦ (t.1 * (U.getD (t.2.headD 0) []).getD β₀ (Exact.ofInt 0), t.2.tail))

/-- The tables of `uni` of a box at the degree `D`: entry `k`, `e` is `z_k^e` at degree `D_k`. -/
def tabs (den : ℤ) : List ℤ → List ℤ → List ℕ → List (List (List κ))
  | _, _, [] => []
  | lo, hi, d :: Ds =>
    ((List.range (d + 1)).map
      (uni (Exact.ofInt den) (Exact.ofInt (lo.headD 0)) (Exact.ofInt (hi.headD 0)) d)) ::
      tabs den lo.tail hi.tail Ds

/-- The dense scaled Bernstein coefficients of `p` at the degree `D` with the tables `Us`
(`tabs`), in the order of `idxN D` (the last variable fastest), and whether every exponent is at
most `D` (beyond `D`, every exponent `0`). One variable at a time: the coefficients of index `β₀`
in the first variable are those of `subst U β₀ p` in the others. -/
def bern : List ℕ → List (List (List κ)) → SPoly κ → List κ × Bool
  | [], _, p => ([Exact.sumL (p.map (·.1))], p.all fun t ↦ t.2.all (· == 0))
  | d :: Ds, Us, p =>
    let parts := (List.range (d + 1)).map fun b ↦ bern Ds Us.tail (subst (Us.headD []) b p)
    (parts.flatMap (·.1), (p.all fun t ↦ decide (t.2.headD 0 ≤ d)) && parts.all (·.2))

/-- A candidate for the maximum of a list (`maxOk` checks it). -/
def maxC : List κ → κ
  | [] => Exact.ofInt 0
  | x :: l => l.foldl (fun m y ↦ bif Exact.nonneg (y - m) then y else m) x

/-- `m` bounds every entry of `l`. -/
def maxOk (m : κ) (l : List κ) : Bool := l.all fun y ↦ Exact.nonneg (m - y)

/-- A candidate for `|x|` (`absOk` checks it). -/
def absC (x : κ) : κ := bif Exact.nonneg x then x else Exact.ofInt 0 - x

/-- `c` bounds `x` and `-x`. -/
def absOk (c x : κ) : Bool := Exact.nonneg (c - x) && Exact.nonneg (c + x)

/-- A bound for `|v|₁`. -/
def norm1C (v : V3 κ) : κ := absC v.x + absC v.y + absC v.z

/-- `norm1C v` bounds `|v|₁`. -/
def norm1Ok (v : V3 κ) : Bool :=
  absOk (absC v.x) v.x && absOk (absC v.y) v.y && absOk (absC v.z) v.z

/-- The view of view chart `a` on the variables `0, 1`. -/
def viewSP (a : Fin 3) : V3 (SP κ) := homView a (SP.cst (Exact.ofInt 1)) (SP.var 0) (SP.var 1)

/-- The quaternion of rotation chart `k` on the variables `2, 3, 4`. -/
def quatSP (k : Fin 4) : Q4 (SP κ) :=
  homQuat k (SP.cst (Exact.ofInt 1)) ⟨SP.var 2, SP.var 3, SP.var 4⟩

/-- The zero vector. -/
def zeroV : V3 κ := ⟨Exact.ofInt 0, Exact.ofInt 0, Exact.ofInt 0⟩

/-- The sum of a list of sparse polynomials. -/
def sumSP (l : List (SP κ)) : SP κ := l.foldr (· + ·) ⟨[]⟩

/-- The direction of a group. -/
def dirOf (pts : List (V3 κ)) (g : MGroup κ) : V3 κ := (pt pts g.dir.2).sub (pt pts g.dir.1)

/-- The multiplier sum `∑_{(j, m) ∈ g} m` of a group. -/
def msum (g : MGroup κ) : SP κ := sumSP (g.terms.map fun t ↦ ⟨t.2⟩)

/-- The plug part `P` of the leaf, with the plug scaled by `ν`. -/
def plugSP (pts : List (V3 κ)) (a : Fin 3) (k : Fin 4) (ν : κ) (m : MLeaf κ) : SP κ :=
  sumSP (m.groups.map fun g ↦ sumSP (g.terms.map fun t ↦
    (⟨t.2⟩ : SP κ) * supportG SP.cst (viewSP a) (quatSP k) (dirOf pts g) (V3.smul ν (pt pts t.1))
      zeroV))

/-- The hole part of a group without its direction: `W_g = (∑ m) |q|² u`, with
`V_g = W_g ⨯₃ c_g = (∑ m) |q|² (u ⨯₃ c_g)`. -/
def holeW (a : Fin 3) (k : Fin 4) (g : MGroup κ) : V3 (SP κ) :=
  V3.smul (msum g * (quatSP k).norm2) (viewSP a)

/-- The degree of the multipliers: the largest exponent of each variable. -/
def adeg (m : MLeaf κ) : List ℕ :=
  (List.range 5).map fun k ↦ (m.groups.flatMap fun g ↦ g.terms.flatMap fun t ↦
    t.2.map fun e ↦ e.2.getD k 0).foldr max 0

/-- The degree of the check: `adeg + (1, 1, 2, 2, 2)`. -/
def degOf (m : MLeaf κ) : List ℕ :=
  List.zipWith (· + ·) (adeg m) [1, 1, 2, 2, 2]

/-- The points are centrally symmetric: each one's negative is a point. -/
def symOk (pts : List (V3 κ)) : Bool :=
  pts.all fun v ↦ pts.any fun w ↦ Exact.eqV w (zeroV.sub v)

/-- The box: a positive denominator, five coordinates, `lo < hi` in each. -/
def boxOk (b : Box) : Bool :=
  decide (0 < b.den) && decide (b.lo.length = 5) && decide (b.hi.length = 5) &&
    (List.range 5).all fun k ↦ decide (b.lo.getD k 0 < b.hi.getD k 0)

/-- The translation bound `max_a |d' v_a|₁ + |ν v₀|₁`, and whether its parts bound what they
should. -/
def tbound (hole : List (V3 κ)) (v₀ : V3 κ) : κ × Bool :=
  let ns := hole.map norm1C
  let m := maxC ns
  (m + norm1C v₀, maxOk m ns && hole.all norm1Ok && norm1Ok v₀)

/-- A group at one index `β`: its direction `c = c_g`, the hole points crossed with it
(`c_g ⨯₃ a` for the hole points `a`), and `w = W_{g,β}`. -/
structure GRow (κ : Type) where
  /-- The direction of the group. -/
  c : V3 κ
  /-- The hole points crossed with the direction: `c ⨯₃ a`. -/
  hs : List (V3 κ)
  /-- The coefficient `W_{g,β}`. -/
  w : V3 κ

/-- The hole coefficient `V_{g,β} = W_{g,β} ⨯₃ c_g`. -/
def GRow.v (r : GRow κ) : V3 κ := r.w.cross r.c

/-- A candidate for `max_a a ⬝ᵥ V_{g,β}`, as `max_a (c_g ⨯₃ a) ⬝ᵥ W_{g,β}`, and whether it
bounds every `(c_g ⨯₃ a) ⬝ᵥ W_{g,β}`. -/
def GRow.bound (r : GRow κ) : κ × Bool :=
  let ds := r.hs.map (·.dot r.w)
  let m := maxC ds
  (m, maxOk m ds)

/-- The row of one index `β` on its groups: `p = P_β`. The value that must be positive,
`p - ∑_g max_a a ⬝ᵥ V_{g,β} - T |∑_g V_{g,β}|₁`, and whether its maxima and absolute values
bound what they should. -/
def rowOkR (tb : Option κ) (p : κ) (rs : List (GRow κ)) : Bool :=
  let hs := rs.map GRow.bound
  let g := p - Exact.sumL (hs.map (·.1))
  hs.all (·.2) &&
    match tb with
    | none => Exact.pos g
    | some t =>
      let w := (rs.map GRow.v).foldr V3.add zeroV
      norm1Ok w && Exact.pos (g - t * norm1C w)

/-- The row of one index `β`: `p = P_β` and `ws = (W_{g,β})_g`, with the groups' directions and
crossed hole points `G = (c_g, (c_g ⨯₃ a)_a)_g`. -/
def rowOk (G : List (V3 κ × List (V3 κ))) (tb : Option κ) (p : κ) (ws : List (V3 κ)) : Bool :=
  rowOkR tb p (List.zipWith (fun x w ↦ ⟨x.1, x.2, w⟩) G ws)

/-- Every row: the heads of the lists, then their tails. -/
def rowsOk (ok : κ → List (V3 κ) → Bool) : List κ → List (List (V3 κ)) → Bool
  | [], _ => true
  | p :: ps, Vs => ok p (Vs.map fun l ↦ l.headD zeroV) && rowsOk ok ps (Vs.map List.tail)

/-- The dense coefficients of a vector of polynomials, and whether its exponents are at most
`D`. -/
def bernV (D : List ℕ) (Us : List (List (List κ))) (V : V3 (SP κ)) : List (V3 κ) × Bool :=
  let x := bern D Us V.x.terms
  let y := bern D Us V.y.terms
  let z := bern D Us V.z.terms
  (List.zipWith3 V3.mk x.1 y.1 z.1, x.2 && y.2 && z.2)

/-- **The check of a multiplier leaf** at the plug scale `s` on the chart box `B`. -/
@[nospecialize]
def check (pts : List (V3 κ)) (B : ChartBox) (s : Scale κ) (m : MLeaf κ) : Bool :=
  let A := adeg m
  let D := degOf m
  let UA : List (List (List κ)) := tabs B.box.den B.box.lo B.box.hi A
  let UD : List (List (List κ)) := tabs B.box.den B.box.lo B.box.hi D
  let hole := pts.map (V3.smul (Exact.ofInt s.den))
  let P := bern D UD (plugSP pts B.view B.rot s.num m).terms
  let Ws := m.groups.map fun g ↦ bernV D UD (holeW B.view B.rot g)
  let G := m.groups.map fun g ↦ (dirOf pts g, hole.map (dirOf pts g).cross)
  let tb : Option κ × Bool :=
    if m.centred then (none, symOk pts) else
      let r := tbound hole (V3.smul s.num (pt pts 0))
      (some r.1, r.2)
  boxOk B.box && s.ok && !pts.isEmpty && tb.2 &&
    (m.groups.all fun g ↦ g.terms.all fun t ↦ decide (t.1 < pts.length) &&
      let M := bern A UA t.2
      M.2 && M.1.all Exact.nonneg) &&
    (bern D UD [((Exact.ofInt 1 : κ), [])]).2 && P.2 && Ws.all (·.2) &&
    rowsOk (rowOk G tb.1) P.1 (Ws.map (·.1))

end Comp

/-! ### Homogeneous forms in one variable -/

section Uni

/-- The value `∑_j l_j a^(n - j) b^j` of a coefficient list with `n + 1` entries. -/
def hE (a b : ℝ) : List ℝ → ℝ
  | [] => 0
  | c :: l => c * a ^ l.length + b * hE a b l

theorem length_addHead {α : Type*} [Add α] (x : α) {l : List α} (hl : l ≠ []) :
    (addHead x l).length = l.length := by
  cases l with
  | nil => exact absurd rfl hl
  | cons d r => rfl

theorem length_mulLin {α : Type*} [Add α] [Mul α] (z p q : α) :
    ∀ l : List α, (mulLin z p q l).length = l.length + 1
  | [] => rfl
  | c :: l => by
    rw [mulLin, List.length_cons, length_addHead _ (by
      rw [← List.length_pos_iff, length_mulLin z p q l]; omega), length_mulLin z p q l,
      List.length_cons]

theorem hE_addHead (a b x : ℝ) : ∀ {l : List ℝ}, l ≠ [] →
    hE a b (addHead x l) = x * a ^ (l.length - 1) + hE a b l
  | [], h => absurd rfl h
  | d :: r, _ => by
    simp only [addHead, hE, List.length_cons, Nat.add_sub_cancel]
    ring

theorem hE_mulLin (a b p q : ℝ) : ∀ l : List ℝ,
    hE a b (mulLin 0 p q l) = (p * a + q * b) * hE a b l
  | [] => by simp [mulLin, hE]
  | c :: l => by
    have hne : mulLin 0 p q l ≠ [] := by
      rw [← List.length_pos_iff, length_mulLin]; omega
    rw [mulLin, hE, length_addHead _ hne, hE_addHead a b _ hne, length_mulLin, hE_mulLin a b p q l,
      hE, Nat.add_sub_cancel]
    ring

theorem map_addHead {α β : Type*} [Add α] [Add β] {f : α → β} (hf : ∀ x y, f (x + y) = f x + f y)
    (x : α) : ∀ l : List α, (addHead x l).map f = addHead (f x) (l.map f)
  | [] => rfl
  | d :: r => by simp [addHead, hf]

theorem map_mulLin {α β : Type*} [Add α] [Mul α] [Add β] [Mul β] {f : α → β}
    (hadd : ∀ x y, f (x + y) = f x + f y) (hmul : ∀ x y, f (x * y) = f x * f y) (z p q : α) :
    ∀ l : List α, (mulLin z p q l).map f = mulLin (f z) (f p) (f q) (l.map f)
  | [] => rfl
  | c :: l => by
    rw [mulLin, List.map_cons, map_addHead hadd, map_mulLin hadd hmul z p q l, hmul, hmul]
    rfl

theorem map_iterate_mulLin {α β : Type*} [Add α] [Mul α] [Add β] [Mul β] {f : α → β}
    (hadd : ∀ x y, f (x + y) = f x + f y) (hmul : ∀ x y, f (x * y) = f x * f y) (z p q : α)
    (l : List α) : ∀ n : ℕ, ((mulLin z p q)^[n] l).map f = (mulLin (f z) (f p) (f q))^[n] (l.map f)
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_mulLin hadd hmul,
      map_iterate_mulLin hadd hmul z p q l n]

theorem hE_iterate (a b p q : ℝ) (l : List ℝ) : ∀ n : ℕ,
    hE a b ((mulLin 0 p q)^[n] l) = (p * a + q * b) ^ n * hE a b l
  | 0 => by simp
  | n + 1 => by
    rw [Function.iterate_succ_apply', hE_mulLin, hE_iterate a b p q l n, pow_succ]
    ring

theorem length_iterate {α : Type*} [Add α] [Mul α] (z p q : α) (l : List α) : ∀ n : ℕ,
    ((mulLin z p q)^[n] l).length = l.length + n
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply', length_mulLin, length_iterate z p q l n]
    omega

theorem length_uni (D₀ L H : κ) (n e : ℕ) : (uni D₀ L H n e).length = n - e + e + 1 := by
  rw [uni, length_iterate, length_iterate, List.length_singleton]
  omega

theorem hE_uni (a b : ℝ) (D₀ L H : κ) (n e : ℕ) :
    hE a b ((uni D₀ L H n e).map Exact.re) =
      (Exact.re D₀ * a + Exact.re D₀ * b) ^ (n - e) * (Exact.re L * a + Exact.re H * b) ^ e := by
  rw [uni, map_iterate_mulLin Exact.re_add Exact.re_mul,
    map_iterate_mulLin Exact.re_add Exact.re_mul, Exact.re_ofInt, Int.cast_zero, hE_iterate,
    hE_iterate]
  simp [hE, Exact.re_ofInt]
  ring

/-- `hE` as a sum over the entries. -/
theorem hE_eq_sum (a b : ℝ) : ∀ l : List ℝ,
    hE a b l = ∑ j ∈ Finset.range l.length, l.getD j 0 * a ^ (l.length - 1 - j) * b ^ j
  | [] => by simp [hE]
  | c :: l => by
    rw [hE, hE_eq_sum a b l, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, Nat.add_sub_cancel,
      Nat.sub_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [show l.length - (j + 1) = l.length - 1 - j by omega, pow_succ]
    ring

end Uni

/-! ### Dense coefficients in several variables -/

section Dense

/-- The indices `β ≤ D` in the order of `bern` (the last variable fastest). -/
def idxN : List ℕ → List (List ℕ)
  | [] => [[]]
  | d :: Ds => (List.range (d + 1)).flatMap fun i ↦ (idxN Ds).map (i :: ·)

/-- The number of indices `∏ (D_k + 1)`. -/
def sizeN (D : List ℕ) : ℕ := (D.map (· + 1)).prod

/-- The variables shifted by one: `k ↦ a (k + 1)`. -/
def sh (a : ℕ → ℝ) : ℕ → ℝ := fun k ↦ a (k + 1)

/-- The Bernstein monomial `∏ a_k^(D_k - β_k) b_k^β_k` of the index `β` at the degree `D`. -/
def monoN : List ℕ → List ℕ → (ℕ → ℝ) → (ℕ → ℝ) → ℝ
  | [], _, _, _ => 1
  | d :: Ds, β, a, b => a 0 ^ (d - β.headD 0) * b 0 ^ β.headD 0 * monoN Ds β.tail (sh a) (sh b)

/-- The value at `(a, b)` of the dense coefficients `L` at the degree `D`. -/
def EN (D : List ℕ) (L : List ℝ) (a b : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (sizeN D), monoN D ((idxN D).getD i []) a b * L.getD i 0

theorem sizeN_cons (d : ℕ) (Ds : List ℕ) : sizeN (d :: Ds) = (d + 1) * sizeN Ds := by
  simp [sizeN]

theorem length_flatMap_range {α : Type*} (f : ℕ → List α) (m : ℕ) (hf : ∀ i, (f i).length = m) :
    ∀ k, ((List.range k).flatMap f).length = k * m
  | 0 => by simp
  | k + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, length_flatMap_range f m hf k]
    simp [hf, add_mul]

theorem getD_flatMap_range {α : Type*} (f : ℕ → List α) (m : ℕ) (hf : ∀ i, (f i).length = m)
    (d : α) : ∀ k i j, i < k → j < m →
      ((List.range k).flatMap f).getD (i * m + j) d = (f i).getD j d
  | 0, i, _, hi, _ => absurd hi (Nat.not_lt_zero i)
  | k + 1, i, j, hi, hj => by
    rw [List.range_succ, List.flatMap_append]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have hlt : i * m + j < ((List.range k).flatMap f).length := by
        rw [length_flatMap_range f m hf k]
        calc i * m + j < i * m + m := by omega
          _ = (i + 1) * m := by ring
          _ ≤ k * m := Nat.mul_le_mul_right m hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD,
        getD_flatMap_range f m hf d k i j hi hj]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by
        rw [length_flatMap_range f m hf]; omega), length_flatMap_range f m hf]
      simp [List.getD_eq_getElem?_getD]

theorem sum_range_mul (g : ℕ → ℝ) (m : ℕ) : ∀ k,
    ∑ x ∈ Finset.range (k * m), g x = ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range m, g (i * m + j)
  | 0 => by simp
  | k + 1 => by
    rw [show (k + 1) * m = k * m + m by ring, Finset.sum_range_add, sum_range_mul g m k,
      Finset.sum_range_succ]

theorem length_idxN : ∀ D : List ℕ, (idxN D).length = sizeN D
  | [] => rfl
  | d :: Ds => by
    rw [idxN, length_flatMap_range _ (sizeN Ds) (fun i ↦ by rw [List.length_map, length_idxN Ds]),
      sizeN_cons]

/-- **Dense values by the first variable.** -/
theorem EN_cons (d : ℕ) (Ds : List ℕ) (f : ℕ → List ℝ) (hf : ∀ i, (f i).length = sizeN Ds)
    (a b : ℕ → ℝ) :
    EN (d :: Ds) ((List.range (d + 1)).flatMap f) a b =
      ∑ i ∈ Finset.range (d + 1), a 0 ^ (d - i) * b 0 ^ i * EN Ds (f i) (sh a) (sh b) := by
  rw [EN, sizeN_cons, sum_range_mul]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [EN, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  rw [getD_flatMap_range f _ hf 0 _ i j hi' hj', idxN, getD_flatMap_range _ (sizeN Ds)
    (fun i ↦ by rw [List.length_map, length_idxN]) [] _ i j hi' hj']
  have hj2 : j < (idxN Ds).length := by rw [length_idxN]; exact hj'
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj2,
    Option.map_some, Option.getD_some, monoN, List.headD_cons, List.tail_cons]
  ring

end Dense

/-! ### The dense coefficients are Bernstein coefficients -/

section BernSound

/-- The positive factor of `bern` on a box: `∏ (den (hi_k - lo_k))^(D_k)`. -/
noncomputable def omegaN (den : ℤ) : List ℤ → List ℤ → List ℕ → ℝ
  | _, _, [] => 1
  | lo, hi, d :: Ds =>
    ((den : ℝ) * ((hi.headD 0 : ℤ) - (lo.headD 0 : ℤ))) ^ d * omegaN den lo.tail hi.tail Ds

/-- The first coordinates of a point of the box: `X_k = hi_k - den z_k`. -/
def avar (den : ℤ) (hi : List ℤ) (z : ℕ → ℝ) : ℕ → ℝ := fun k ↦ (hi.getD k 0 : ℝ) - den * z k

/-- The second coordinates: `Y_k = den z_k - lo_k`. -/
def bvar (den : ℤ) (lo : List ℤ) (z : ℕ → ℝ) : ℕ → ℝ := fun k ↦ den * z k - (lo.getD k 0 : ℝ)

theorem getD_zero_eq_headD (l : List ℤ) : l.getD 0 0 = l.headD 0 := by
  cases l <;> simp

theorem sh_avar (den : ℤ) (hi : List ℤ) (z : ℕ → ℝ) :
    sh (avar den hi z) = avar den hi.tail (sh z) := by
  funext k
  simp [sh, avar]

theorem sh_bvar (den : ℤ) (lo : List ℤ) (z : ℕ → ℝ) :
    sh (bvar den lo z) = bvar den lo.tail (sh z) := by
  funext k
  simp [sh, bvar]

omit [Add κ] [Sub κ] [Mul κ] [Exact κ] in
theorem mono_succ (x : ℕ → ℝ) : ∀ (e : List ℕ) (i : ℕ),
    SPoly.mono (1 : ℝ) x (i + 1) e = SPoly.mono 1 (sh x) i e
  | [], _ => rfl
  | d :: e, i => by
    rw [SPoly.mono_cons, SPoly.mono_cons, mono_succ x e (i + 1)]
    rfl

omit [Add κ] [Sub κ] [Mul κ] [Exact κ] in
/-- The first variable of a monomial. -/
theorem mono_split (x : ℕ → ℝ) (e : List ℕ) :
    SPoly.mono (1 : ℝ) x 0 e = x 0 ^ e.headD 0 * SPoly.mono 1 (sh x) 0 e.tail := by
  cases e with
  | nil => simp [SPoly.mono_nil]
  | cons d e =>
    rw [SPoly.mono_cons, mono_succ]
    rfl

omit [Add κ] [Sub κ] [Mul κ] [Exact κ] in
theorem mono_zeros (x : ℕ → ℝ) : ∀ (e : List ℕ) (i : ℕ), e.all (· == 0) = true →
    SPoly.mono (1 : ℝ) x i e = 1
  | [], _, _ => rfl
  | d :: e, i, h => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    rw [SPoly.mono_cons, h.1, pow_zero, one_mul, mono_zeros x e (i + 1) h.2]

theorem re_getD (l : List κ) (j : ℕ) :
    (l.map Exact.re).getD j 0 = Exact.re (l.getD j (Exact.ofInt 0)) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[j]? <;> simp [Exact.re_ofInt]

theorem run_subst (x : ℕ → ℝ) (U : List (List κ)) (b : ℕ) (p : SPoly κ) :
    SPoly.run Exact.re x (subst U b p) = (p.map fun t ↦ Exact.re t.1 *
      Exact.re ((U.getD (t.2.headD 0) []).getD b (Exact.ofInt 0)) *
        SPoly.mono 1 x 0 t.2.tail).sum := by
  rw [subst, SPoly.run_normal, SPoly.run_eq_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ ↦ ?_
  simp [SPoly.tval, Exact.re_mul]

theorem run_split (x : ℕ → ℝ) (p : SPoly κ) :
    SPoly.run Exact.re x p = (p.map fun t ↦ Exact.re t.1 * x 0 ^ t.2.headD 0 *
      SPoly.mono 1 (sh x) 0 t.2.tail).sum := by
  rw [SPoly.run_eq_sum]
  congr 1
  refine List.map_congr_left fun t _ ↦ ?_
  rw [SPoly.tval, mono_split, mul_assoc]

theorem sum_range_listSum {α : Type*} (l : List α) (n : ℕ) (g : ℕ → α → ℝ) :
    ∑ i ∈ Finset.range n, (l.map (g i)).sum = (l.map fun t ↦ ∑ i ∈ Finset.range n, g i t).sum := by
  induction l with
  | nil => simp
  | cons t l ih => simp [Finset.sum_add_distrib, ih]

/-- **One variable**: the coefficients of `z^e` (`e ≤ d`) at `(X, Y)` give `(den w)^d z^e`. -/
theorem sum_uni (den lo hi : ℤ) (d e : ℕ) (he : e ≤ d) (z : ℝ) :
    ∑ i ∈ Finset.range (d + 1), ((hi : ℝ) - den * z) ^ (d - i) * (den * z - lo) ^ i *
      Exact.re ((uni (Exact.ofInt den : κ) (Exact.ofInt lo) (Exact.ofInt hi) d e).getD i
        (Exact.ofInt 0)) = ((den : ℝ) * (hi - lo)) ^ d * z ^ e := by
  have hl := length_uni (Exact.ofInt den : κ) (Exact.ofInt lo) (Exact.ofInt hi) d e
  have h := hE_uni ((hi : ℝ) - den * z) (den * z - lo) (Exact.ofInt den : κ) (Exact.ofInt lo)
    (Exact.ofInt hi) d e
  rw [hE_eq_sum, List.length_map, hl, show d - e + e + 1 = d + 1 by omega] at h
  simp only [Exact.re_ofInt] at h
  calc _ = ∑ j ∈ Finset.range (d + 1), ((uni (Exact.ofInt den : κ) (Exact.ofInt lo)
        (Exact.ofInt hi) d e).map Exact.re).getD j 0 * ((hi : ℝ) - den * z) ^ (d + 1 - 1 - j) *
          (den * z - lo) ^ j := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [re_getD, Nat.add_sub_cancel]
        ring
    _ = _ := by
        rw [h]
        have h2 : (den : ℝ) * (hi - den * z) + den * (den * z - lo) = den * (hi - lo) := by ring
        have h3 : (lo : ℝ) * (hi - den * z) + hi * (den * z - lo) = den * (hi - lo) * z := by ring
        rw [h2, h3, mul_pow _ z, ← mul_assoc, ← pow_add, Nat.sub_add_cancel he]

theorem length_bern : ∀ (D : List ℕ) (Us : List (List (List κ))) (p : SPoly κ),
    (bern D Us p).1.length = sizeN D
  | [], _, _ => rfl
  | d :: Ds, Us, p => by
    simp only [bern, List.flatMap_map]
    exact (length_flatMap_range _ _ (fun i ↦ length_bern Ds _ _) _).trans (sizeN_cons d Ds).symm

/-- **Soundness of `bern`**: the dense coefficients at the point `(X, Y)` of a point `z` of the
box are `omegaN` times the polynomial's value. -/
theorem bern_spec (den : ℤ) : ∀ (D : List ℕ) (lo hi : List ℤ) (p : SPoly κ) (z : ℕ → ℝ),
    (bern D (tabs den lo hi D) p).2 = true →
    EN D ((bern D (tabs den lo hi D) p).1.map Exact.re) (avar den hi z) (bvar den lo z) =
      omegaN den lo hi D * SPoly.run Exact.re z p
  | [], lo, hi, p, z, h => by
    simp only [bern, List.all_eq_true] at h
    simp only [EN, sizeN, List.map_nil, List.prod_nil, Finset.range_one, Finset.sum_singleton,
      monoN, bern, List.map_cons, List.map_nil, omegaN, one_mul, List.getD_cons_zero]
    rw [Exact.re_sumL, SPoly.run_eq_sum, List.map_map]
    congr 1
    refine List.map_congr_left fun t ht ↦ ?_
    simp [SPoly.tval, mono_zeros z t.2 0 (List.all_eq_true.mpr (h t ht))]
  | d :: Ds, lo, hi, p, z, h => by
    set U : List (List κ) := (List.range (d + 1)).map
      (uni (Exact.ofInt den) (Exact.ofInt (lo.headD 0)) (Exact.ofInt (hi.headD 0)) d) with hUdef
    have hT : tabs den lo hi (d :: Ds) = U :: tabs den lo.tail hi.tail Ds := rfl
    have hU (e : ℕ) (he : e ≤ d) : U.getD e [] =
        uni (Exact.ofInt den) (Exact.ofInt (lo.headD 0)) (Exact.ofInt (hi.headD 0)) d e := by
      rw [hUdef, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
      rfl
    rw [hT] at h ⊢
    simp only [bern, List.headD_cons, List.tail_cons, Bool.and_eq_true, List.all_eq_true,
      decide_eq_true_eq, List.mem_map, List.mem_range, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at h
    obtain ⟨hd, hp⟩ := h
    simp only [bern, List.headD_cons, List.tail_cons, List.flatMap_map, List.map_flatMap]
    rw [EN_cons d Ds _ (fun i ↦ by rw [List.length_map, length_bern]), sh_avar, sh_bvar]
    rw [Finset.sum_congr rfl fun i hi' ↦ by
      rw [bern_spec den Ds lo.tail hi.tail _ (sh z) (hp i (Finset.mem_range.mp hi')), run_subst,
        ← List.sum_map_mul_left, ← List.sum_map_mul_left], sum_range_listSum, run_split,
      ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun t ht ↦ ?_
    have he := hd t ht
    have hs := sum_uni (κ := κ) den (lo.headD 0) (hi.headD 0) d _ he (z 0)
    simp only [hU _ he, avar, bvar, getD_zero_eq_headD]
    calc _ = omegaN den lo.tail hi.tail Ds * Exact.re t.1 * SPoly.mono 1 (sh z) 0 t.2.tail *
          ∑ i ∈ Finset.range (d + 1), ((hi.headD 0 : ℤ) - (den : ℝ) * z 0) ^ (d - i) *
            ((den : ℝ) * z 0 - (lo.headD 0 : ℤ)) ^ i * Exact.re ((uni (Exact.ofInt den : κ)
              (Exact.ofInt (lo.headD 0)) (Exact.ofInt (hi.headD 0)) d (t.2.headD 0)).getD i
                (Exact.ofInt 0)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          ring
      _ = _ := by
          rw [hs, omegaN]
          ring

end BernSound

end Mult

/-! ### Support inequalities of a fit -/

namespace Polyhedron

open Matrix

variable {P : Polyhedron}

/-- **Support inequalities of a fit.** A fit of `M P` along `u` has a translation `τ` with
`n ⬝ᵥ (M x + τ) ≤ H` for every `n ⊥ u`, every point `x` of `P` and every bound `H` of `n` on the
vertices of `P` (weak: the moved points lie in the shadow). -/
theorem _root_.Nieuwland.Polyhedron.FitsAlong.exists_support {u : Fin 3 → ℝ}
    {M : Matrix (Fin 3) (Fin 3) ℝ}
    (h : P.FitsAlong u M) : ∃ τ : Fin 3 → ℝ, ∀ n, n ⬝ᵥ u = 0 → ∀ x ∈ P.hull, ∀ H : ℝ,
      (∀ y ∈ P.vertices, n ⬝ᵥ y ≤ H) → n ⬝ᵥ (M *ᵥ x + τ) ≤ H := by
  obtain ⟨L, hL, hker, τ₂, hfit⟩ := h
  obtain ⟨S, hS⟩ := L.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hL)
  refine ⟨S τ₂, fun n hn x hx H hH ↦ ?_⟩
  obtain ⟨φ, hφ⟩ := exists_functional_comp hL hker hn
  have hin := interior_subset (hfit ⟨x, hx, rfl⟩)
  obtain ⟨y, hy, hyx⟩ := hin
  have hLS : L (S τ₂) = τ₂ := by rw [← LinearMap.comp_apply, hS, LinearMap.id_apply]
  rw [← hφ, map_add, hLS, ← hyx, hφ]
  exact convexHull_min (fun v hv ↦ hH v hv) ((convex_halfSpace_le
    (f := fun y : Fin 3 → ℝ ↦ n ⬝ᵥ y) ⟨fun a b ↦ dotProduct_add n a b, fun c a ↦ by
      simp [dotProduct_smul]⟩ H)) hy

/-- **Support inequalities of a centred fit.** If the vertices of `P` are centrally symmetric,
the translation `0` serves. -/
theorem _root_.Nieuwland.Polyhedron.FitsAlong.support_centred {u : Fin 3 → ℝ}
    {M : Matrix (Fin 3) (Fin 3) ℝ}
    (h : P.FitsAlong u M) (hP : ∀ x ∈ P.vertices, -x ∈ P.vertices) : ∀ n, n ⬝ᵥ u = 0 →
      ∀ x ∈ P.hull, ∀ H : ℝ, (∀ y ∈ P.vertices, n ⬝ᵥ y ≤ H) → n ⬝ᵥ (M *ᵥ x) ≤ H := by
  obtain ⟨L, hL, hker, τ₂, hfit⟩ := h
  intro n hn x hx H hH
  obtain ⟨φ, hφ⟩ := exists_functional_comp hL hker hn
  have hneg : ∀ y ∈ P.hull, -y ∈ P.hull := by
    intro y hy
    have hV : -(P.vertices : Set (Fin 3 → ℝ)) = P.vertices :=
      Set.ext fun v ↦ ⟨fun h ↦ by simpa using hP _ h, fun h ↦ by simpa using hP v h⟩
    have : -y ∈ convexHull ℝ (-(P.vertices : Set (Fin 3 → ℝ))) := by
      rw [convexHull_neg]; exact Set.neg_mem_neg.mpr hy
    rwa [hV] at this
  have hS : ∀ s ∈ {L v | v ∈ P.vertices}, -s ∈ {L v | v ∈ P.vertices} := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨-v, hP v hv, map_neg L v⟩
  have hT : ∀ y ∈ {L (M *ᵥ w) | w ∈ P.hull}, -y ∈ {L (M *ᵥ w) | w ∈ P.hull} := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨-w, hneg w hw, by rw [mulVec_neg, map_neg]⟩
  have h0 := forall_mem_interior_of_add_mem_interior hS hT (t := τ₂) (by
    rintro _ ⟨w, hw, rfl⟩
    rw [← P.image_hull L]
    exact hfit ⟨w, hw, rfl⟩) _ ⟨x, hx, rfl⟩
  rw [← P.image_hull L] at h0
  obtain ⟨y, hy, hyx⟩ := interior_subset h0
  rw [← hφ, ← hyx, hφ]
  exact convexHull_min (fun v hv ↦ hH v hv) ((convex_halfSpace_le
    (f := fun y : Fin 3 → ℝ ↦ n ⬝ᵥ y) ⟨fun a b ↦ dotProduct_add n a b, fun c a ↦ by
      simp [dotProduct_smul]⟩ H)) hy

end Polyhedron

/-! ### Norms -/

namespace Mult

open Matrix

/-- `|x|₁`. -/
noncomputable def l1 (x : Fin 3 → ℝ) : ℝ := |x 0| + |x 1| + |x 2|

theorem l1_nonneg (x : Fin 3 → ℝ) : 0 ≤ l1 x := by
  unfold l1; positivity

theorem abs_dot_le (x y : Fin 3 → ℝ) : |x ⬝ᵥ y| ≤ l1 x * l1 y := by
  simp only [dotProduct, Fin.sum_univ_three, l1]
  have h0 := abs_nonneg (y 0); have h1 := abs_nonneg (y 1); have h2 := abs_nonneg (y 2)
  have g0 := abs_nonneg (x 0); have g1 := abs_nonneg (x 1); have g2 := abs_nonneg (x 2)
  calc |x 0 * y 0 + x 1 * y 1 + x 2 * y 2| ≤ |x 0| * |y 0| + |x 1| * |y 1| + |x 2| * |y 2| := by
        rw [← abs_mul, ← abs_mul, ← abs_mul]
        exact (abs_add_le _ _).trans (by linarith [abs_add_le (x 0 * y 0) (x 1 * y 1)])
    _ ≤ _ := by nlinarith

/-- Each entry of `R v` for an orthogonal `R` is at most `|v|₁`: `|(R v)_i| ≤ |R v| = |v|`. -/
theorem abs_mulVec_le {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO(3)) (v : Fin 3 → ℝ)
    (i : Fin 3) : |(R *ᵥ v) i| ≤ l1 v := by
  have hO : Rᵀ * R = 1 := (mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hR.1
  have hn : (R *ᵥ v) ⬝ᵥ (R *ᵥ v) = v ⬝ᵥ v := by
    rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hO, one_mulVec]
  have hsq : (R *ᵥ v) i ^ 2 ≤ l1 v ^ 2 := by
    have h1 : (R *ᵥ v) i ^ 2 ≤ (R *ᵥ v) ⬝ᵥ (R *ᵥ v) := by
      simp only [dotProduct, Fin.sum_univ_three]
      fin_cases i <;> simp <;> nlinarith [sq_nonneg ((R *ᵥ v) 0), sq_nonneg ((R *ᵥ v) 1),
        sq_nonneg ((R *ᵥ v) 2)]
    rw [hn] at h1
    refine h1.trans ?_
    simp only [dotProduct, Fin.sum_univ_three, l1]
    have h0 := abs_nonneg (v 0); have h1' := abs_nonneg (v 1); have h2 := abs_nonneg (v 2)
    nlinarith [sq_abs (v 0), sq_abs (v 1), sq_abs (v 2), mul_nonneg h0 h1', mul_nonneg h0 h2,
      mul_nonneg h1' h2]
  exact abs_le_of_sq_le_sq hsq (l1_nonneg v)

/-- `|W ⬝ᵥ R v| ≤ |W|₁ |v|₁` for an orthogonal `R`. -/
theorem abs_dot_mulVec_le {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO(3)) (W v : Fin 3 → ℝ) :
    |W ⬝ᵥ (R *ᵥ v)| ≤ l1 W * l1 v := by
  simp only [dotProduct, Fin.sum_univ_three, l1]
  have e0 := abs_mulVec_le hR v 0; have e1 := abs_mulVec_le hR v 1
  have e2 := abs_mulVec_le hR v 2
  have g0 := abs_nonneg (W 0); have g1 := abs_nonneg (W 1); have g2 := abs_nonneg (W 2)
  calc _ ≤ |W 0| * |(R *ᵥ v) 0| + |W 1| * |(R *ᵥ v) 1| + |W 2| * |(R *ᵥ v) 2| := by
        rw [← abs_mul, ← abs_mul, ← abs_mul]
        exact (abs_add_le _ _).trans
          (by linarith [abs_add_le (W 0 * (R *ᵥ v) 0) (W 1 * (R *ᵥ v) 1)])
    _ ≤ (|W 0| + |W 1| + |W 2|) * l1 v := by nlinarith
    _ = _ := rfl

end Mult

namespace Mult


/-! ### The values of the polynomials -/

section Eval

open Matrix

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] (z : ℕ → ℝ)

theorem eval_sumSP : ∀ l : List (SP κ), SP.eval z (sumSP l) = (l.map (SP.eval z)).sum
  | [] => by
    simp only [sumSP, List.foldr_nil, List.map_nil, List.sum_nil]
    exact SPoly.run_nil z
  | p :: l => by
    change SP.eval z (p + sumSP l) = _
    rw [(SP.isArith_eval z).map_add, eval_sumSP l, List.map_cons, List.sum_cons]

theorem eval_comp_cst : SP.eval (κ := κ) z ∘ SP.cst = Exact.re :=
  funext fun c ↦ SP.eval_cst z c

theorem toFun_viewSP (a : Fin 3) :
    ((viewSP (κ := κ) a).map (SP.eval z)).toFun = viewDir a (z 0) (z 1) := by
  rw [viewSP, map_homView, SP.eval_cst, SP.eval_var, SP.eval_var, SPoly.re_one,
    ← one_mul (z 0), ← one_mul (z 1), toFun_homView, one_smul]
  simp only [one_mul]

theorem toFun_quatSP (k : Fin 4) :
    ((quatSP (κ := κ) k).map (SP.eval z)).toFun = chartQuat k ![z 2, z 3, z 4] := by
  rw [quatSP, map_homQuat, SP.eval_cst, SPoly.re_one]
  have h := toFun_homQuat k (1 : ℝ) ![z 2, z 3, z 4]
  simp only [one_mul, one_smul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] at h
  rw [← h]
  simp [V3.map, SP.eval_var]

theorem eval_plugTerm (a : Fin 3) (k : Fin 4) (c v : V3 κ) :
    SP.eval z (supportG SP.cst (viewSP a) (quatSP k) c v zeroV) =
      (chartQuat k ![z 2, z 3, z 4] ⬝ᵥ chartQuat k ![z 2, z 3, z 4]) *
        ((viewDir a (z 0) (z 1) ⨯₃ Exact.reV c) ⬝ᵥ
          (quatRotation (chartQuat k ![z 2, z 3, z 4]) *ᵥ Exact.reV v)) := by
  rw [map_supportG (SP.isArith_eval z), eval_comp_cst, supportG_re, toFun_viewSP, toFun_quatSP,
    supportPoly_rep (chartQuat_ne_zero _ _)]
  have h0 : Exact.reV (zeroV : V3 κ) = 0 := by
    funext i; fin_cases i <;> simp [Exact.reV, zeroV, V3.map, V3.toFun, Exact.re_ofInt]
  rw [h0, dotProduct_zero, sub_zero]

theorem toFun_holeW (a : Fin 3) (k : Fin 4) (g : MGroup κ) :
    ((holeW a k g).map (SP.eval z)).toFun =
      (SP.eval z (msum g) * (chartQuat k ![z 2, z 3, z 4] ⬝ᵥ chartQuat k ![z 2, z 3, z 4])) •
        viewDir a (z 0) (z 1) := by
  rw [holeW, V3.map_smul (SP.isArith_eval z), V3.toFun_smul, (SP.isArith_eval z).map_mul,
    Q4.map_norm2 (SP.isArith_eval z), Q4.norm2_eq_dotProduct, toFun_quatSP, toFun_viewSP]

end Eval

/-! ### The final combination -/

section Final

open Matrix

theorem listSum_finsetSum {β : Type*} {M : Type*} [AddCommMonoid M] (gs : List β) (n : ℕ)
    (f : β → ℕ → M) :
    (gs.map fun g ↦ ∑ i ∈ Finset.range n, f g i).sum =
      ∑ i ∈ Finset.range n, (gs.map fun g ↦ f g i).sum := by
  induction gs with
  | nil => simp
  | cons g gs ih => simp [ih, Finset.sum_add_distrib]

theorem listSum_dotProduct {β : Type*} (gs : List β) (f : β → Fin 3 → ℝ) (τ : Fin 3 → ℝ) :
    (gs.map fun g ↦ f g ⬝ᵥ τ).sum = (gs.map f).sum ⬝ᵥ τ := by
  induction gs with
  | nil => simp
  | cons g gs ih => simp [ih, add_dotProduct]

theorem smul_cross (c : ℝ) (u v : Fin 3 → ℝ) : (c • u) ⨯₃ v = c • (u ⨯₃ v) := by
  rw [map_smul, LinearMap.smul_apply]

theorem sum_smul_cross (n : ℕ) (w : ℕ → ℝ) (W : ℕ → Fin 3 → ℝ) (c : Fin 3 → ℝ) :
    ∑ i ∈ Finset.range n, w i • (W i ⨯₃ c) = (∑ i ∈ Finset.range n, w i • W i) ⨯₃ c := by
  rw [map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ ↦ (smul_cross _ _ _).symm

/-- **The combination of the rows** (reals): with nonnegative weights `w i`, one positive, and at
every index `P_i - ∑_g H_{g,i} - TN_i > 0` with `H_{g,i}` bounding `a_g ⬝ᵥ V_{g,i}`, and a
translation term bounded by `- ∑ w_i TN_i`, the weighted value is positive. -/
theorem final_pos {β : Type*} {n : ℕ} {w Pd TN : ℕ → ℝ} {gs : List β} {a : β → Fin 3 → ℝ}
    {V : β → ℕ → Fin 3 → ℝ} {H : β → ℕ → ℝ} {Tr : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i < n, 0 < w i)
    (hrow : ∀ i < n, 0 < Pd i - (gs.map fun g ↦ H g i).sum - TN i)
    (hH : ∀ i < n, ∀ g ∈ gs, a g ⬝ᵥ V g i ≤ H g i)
    (hτ : -(∑ i ∈ Finset.range n, w i * TN i) ≤ Tr) :
    0 < ∑ i ∈ Finset.range n, w i * Pd i + Tr -
        (gs.map fun g ↦ a g ⬝ᵥ ∑ i ∈ Finset.range n, w i • V g i).sum := by
  have hA : (gs.map fun g ↦ a g ⬝ᵥ ∑ i ∈ Finset.range n, w i • V g i).sum ≤
      ∑ i ∈ Finset.range n, w i * (gs.map fun g ↦ H g i).sum := by
    calc _ = (gs.map fun g ↦ ∑ i ∈ Finset.range n, w i * (a g ⬝ᵥ V g i)).sum := by
          congr 1
          refine List.map_congr_left fun g _ ↦ ?_
          rw [dotProduct_sum]
          simp [dotProduct_smul]
      _ ≤ (gs.map fun g ↦ ∑ i ∈ Finset.range n, w i * H g i).sum := by
          refine List.sum_le_sum fun g hg ↦ Finset.sum_le_sum fun i hi ↦ ?_
          exact mul_le_mul_of_nonneg_left (hH i (Finset.mem_range.mp hi) g hg) (hw i)
      _ = _ := by
          rw [listSum_finsetSum]
          simp [List.sum_map_mul_left]
  have hS : 0 < ∑ i ∈ Finset.range n, w i * (Pd i - (gs.map fun g ↦ H g i).sum - TN i) := by
    obtain ⟨j, hj, hwj⟩ := hpos
    exact Finset.sum_pos' (fun i hi ↦ mul_nonneg (hw i) (hrow i (Finset.mem_range.mp hi)).le)
      ⟨j, Finset.mem_range.mpr hj, mul_pos hwj (hrow j hj)⟩
  have hsplit : ∑ i ∈ Finset.range n, w i * (Pd i - (gs.map fun g ↦ H g i).sum - TN i) =
      ∑ i ∈ Finset.range n, w i * Pd i - ∑ i ∈ Finset.range n, w i * (gs.map fun g ↦ H g i).sum -
        ∑ i ∈ Finset.range n, w i * TN i := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  linarith

theorem l1_add (x y : Fin 3 → ℝ) : l1 (x + y) ≤ l1 x + l1 y := by
  simp only [l1, Pi.add_apply]
  linarith [abs_add_le (x 0) (y 0), abs_add_le (x 1) (y 1), abs_add_le (x 2) (y 2)]

theorem l1_smul {c : ℝ} (hc : 0 ≤ c) (x : Fin 3 → ℝ) : l1 (c • x) = c * l1 x := by
  simp only [l1, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hc]
  ring

theorem l1_neg (x : Fin 3 → ℝ) : l1 (-x) = l1 x := by
  simp [l1]

theorem l1_sum_le (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i) (W : ℕ → Fin 3 → ℝ) : ∀ n : ℕ,
    l1 (∑ i ∈ Finset.range n, w i • W i) ≤ ∑ i ∈ Finset.range n, w i * l1 (W i)
  | 0 => by simp [l1]
  | n + 1 => by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    refine (l1_add _ _).trans ?_
    rw [l1_smul (hw n)]
    linarith [l1_sum_le w hw W n]

end Final

/-! ### The checks of the rows -/

section Rows

open Matrix

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

theorem reV_zeroV : Exact.reV (zeroV : V3 κ) = 0 := by
  funext i; fin_cases i <;> simp [Exact.reV, zeroV, V3.map, V3.toFun, Exact.re_ofInt]

theorem re_dot (u v : V3 κ) : Exact.re (u.dot v) = Exact.reV u ⬝ᵥ Exact.reV v := by
  rw [V3.map_dot Exact.isArith, V3.dot_eq_dotProduct]
  rfl

theorem reV_foldr_add : ∀ l : List (V3 κ), Exact.reV (l.foldr V3.add zeroV) = (l.map Exact.reV).sum
  | [] => reV_zeroV
  | v :: l => by rw [List.foldr_cons, Exact.reV_add, reV_foldr_add l, List.map_cons, List.sum_cons]

theorem maxOk_spec {c : κ} {l : List κ} (h : maxOk c l = true) :
    ∀ y ∈ l, Exact.re y ≤ Exact.re c := by
  intro y hy
  have := Exact.nonneg_sound _ (List.all_eq_true.mp h y hy)
  rw [Exact.re_sub] at this
  linarith

theorem absOk_spec {c x : κ} (h : absOk c x = true) : |Exact.re x| ≤ Exact.re c := by
  simp only [absOk, Bool.and_eq_true] at h
  have h1 := Exact.nonneg_sound _ h.1
  have h2 := Exact.nonneg_sound _ h.2
  rw [Exact.re_sub] at h1
  rw [Exact.re_add] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem norm1Ok_spec {v : V3 κ} (h : norm1Ok v = true) :
    l1 (Exact.reV v) ≤ Exact.re (norm1C v) := by
  simp only [norm1Ok, Bool.and_eq_true] at h
  have h1 := absOk_spec h.1.1
  have h2 := absOk_spec h.1.2
  have h3 := absOk_spec h.2
  rw [norm1C, Exact.re_add, Exact.re_add]
  simp only [l1, Exact.reV, V3.toFun, V3.map]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  linarith

theorem getD_tail {β : Type*} (l : List β) (i : ℕ) (d : β) :
    l.tail.getD i d = l.getD (i + 1) d := by
  cases l <;> simp

theorem rowsOk_spec (ok : κ → List (V3 κ) → Bool) : ∀ (ps : List κ) (Vs : List (List (V3 κ))),
    rowsOk ok ps Vs = true → ∀ i < ps.length,
      ok (ps.getD i (Exact.ofInt 0)) (Vs.map fun l ↦ l.getD i zeroV) = true
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | p :: ps, Vs, h, i, hi => by
    simp only [rowsOk, Bool.and_eq_true] at h
    cases i with
    | zero =>
      convert h.1 using 3
      · simp only [List.getD_cons_zero]
      · funext l
        cases l <;> rfl
    | succ i =>
      have := rowsOk_spec ok ps _ h.2 i (by simpa using hi)
      simpa [List.map_map, Function.comp_def, getD_tail] using this

/-- The translation term of a row. -/
noncomputable def tnOf (tb : Option κ) (vs : List (V3 κ)) : ℝ :=
  match tb with
  | none => 0
  | some t => Exact.re t * Exact.re (norm1C (vs.foldr V3.add zeroV))

theorem GRow.bound_spec {r : GRow κ} (h : r.bound.2 = true) :
    ∀ x ∈ r.hs, Exact.reV x ⬝ᵥ Exact.reV r.w ≤ Exact.re r.bound.1 := by
  intro x hx
  rw [← re_dot]
  exact maxOk_spec h _ (List.mem_map.mpr ⟨x, hx, rfl⟩)

theorem zipWith_map_map {α β γ δ : Type*} (f : β → γ → δ) (a : α → β) (b : α → γ) (l : List α) :
    List.zipWith f (l.map a) (l.map b) = l.map fun x ↦ f (a x) (b x) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

theorem rowOkR_spec {tb : Option κ} {p : κ} {rs : List (GRow κ)}
    (h : rowOkR tb p rs = true) :
    (∀ r ∈ rs, ∀ x ∈ r.hs, Exact.reV x ⬝ᵥ Exact.reV r.w ≤ Exact.re r.bound.1) ∧
    0 < Exact.re p - (rs.map fun r ↦ Exact.re r.bound.1).sum - tnOf tb (rs.map GRow.v) ∧
    (tb.isSome = true → l1 (Exact.reV ((rs.map GRow.v).foldr V3.add zeroV)) ≤
      Exact.re (norm1C ((rs.map GRow.v).foldr V3.add zeroV))) := by
  simp only [rowOkR, Bool.and_eq_true, List.all_eq_true, List.forall_mem_map] at h
  obtain ⟨hmax, hrest⟩ := h
  have hsum : Exact.re (p - Exact.sumL ((rs.map GRow.bound).map (·.1))) =
      Exact.re p - (rs.map fun r ↦ Exact.re r.bound.1).sum := by
    rw [Exact.re_sub, Exact.re_sumL, List.map_map, List.map_map]
    rfl
  refine ⟨fun r hr ↦ GRow.bound_spec (hmax r hr), ?_, ?_⟩
  · cases tb with
    | none =>
      have := Exact.pos_sound _ hrest
      rw [hsum] at this
      simpa [tnOf] using this
    | some t =>
      simp only [Bool.and_eq_true] at hrest
      have := Exact.pos_sound _ hrest.2
      rw [Exact.re_sub, hsum, Exact.re_mul] at this
      simpa [tnOf] using this
  · intro hs
    cases tb with
    | none => simp at hs
    | some t =>
      simp only [Bool.and_eq_true] at hrest
      exact norm1Ok_spec hrest.1

end Rows

/-! ### Signs on the box -/

section Signs

open Matrix

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

theorem omegaN_pos {den : ℤ} (hd : 0 < den) : ∀ (D : List ℕ) (lo hi : List ℤ),
    (∀ k < D.length, lo.getD k 0 < hi.getD k 0) → 0 < omegaN den lo hi D
  | [], _, _, _ => by simp [omegaN]
  | d :: Ds, lo, hi, h => by
    rw [omegaN]
    have h0 := h 0 (by simp)
    rw [getD_zero_eq_headD, getD_zero_eq_headD] at h0
    refine mul_pos (pow_pos (mul_pos (by exact_mod_cast hd) ?_) _) (omegaN_pos hd Ds _ _ ?_)
    · have : ((lo.headD 0 : ℤ) : ℝ) < (hi.headD 0 : ℤ) := by exact_mod_cast h0
      linarith
    · intro k hk
      have := h (k + 1) (by simpa using hk)
      rwa [← getD_tail, ← getD_tail] at this

theorem monoN_nonneg : ∀ (D β : List ℕ) (a b : ℕ → ℝ), (∀ k, 0 ≤ a k) → (∀ k, 0 ≤ b k) →
    0 ≤ monoN D β a b
  | [], _, _, _, _, _ => by simp [monoN]
  | d :: Ds, β, a, b, ha, hb => by
    rw [monoN]
    exact mul_nonneg (mul_nonneg (pow_nonneg (ha 0) _) (pow_nonneg (hb 0) _))
      (monoN_nonneg Ds _ _ _ (fun k ↦ ha (k + 1)) fun k ↦ hb (k + 1))

theorem EN_nonneg {D : List ℕ} {L : List ℝ} {a b : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (hL : ∀ x ∈ L, 0 ≤ x) : 0 ≤ EN D L a b := by
  refine Finset.sum_nonneg fun i _ ↦ mul_nonneg (monoN_nonneg _ _ _ _ ha hb) ?_
  rw [List.getD_eq_getElem?_getD]
  cases hi : L[i]? with
  | none => simp
  | some x => exact hL x (List.mem_of_getElem? hi)

theorem exists_monoN_ne {D : List ℕ} {L : List ℝ} {a b : ℕ → ℝ} (h : EN D L a b ≠ 0) :
    ∃ i < sizeN D, monoN D ((idxN D).getD i []) a b ≠ 0 := by
  by_contra hc
  simp only [not_exists, not_and, not_not] at hc
  exact h (Finset.sum_eq_zero fun i hi ↦ by rw [hc i (Finset.mem_range.mp hi), zero_mul])

theorem getD_zipWith3 {α β γ δ : Type*} (f : α → β → γ → δ) (d : δ) (da : α) (db : β) (dc : γ)
    (hd : d = f da db dc) : ∀ (x : List α) (y : List β) (w : List γ) (i : ℕ),
    i < x.length → i < y.length → i < w.length →
      (List.zipWith3 f x y w).getD i d = f (x.getD i da) (y.getD i db) (w.getD i dc)
  | [], _, _, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | _ :: _, [], _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ :: _, _ :: _, [], _, _, _, h => absurd h (Nat.not_lt_zero _)
  | a :: x, b :: y, c :: w, 0, _, _, _ => rfl
  | a :: x, b :: y, c :: w, i + 1, h1, h2, h3 => by
    simp only [List.zipWith3, List.getD_cons_succ]
    exact getD_zipWith3 f d da db dc hd x y w i (by simpa using h1) (by simpa using h2)
      (by simpa using h3)

/-- **Soundness of `bernV`**: the dense coefficients of a vector of polynomials. -/
theorem bernV_spec (den : ℤ) (D : List ℕ) (lo hi : List ℤ) (V : V3 (SP κ)) (z : ℕ → ℝ)
    (h : (bernV D (tabs den lo hi D) V).2 = true) :
    ∑ i ∈ Finset.range (sizeN D), monoN D ((idxN D).getD i []) (avar den hi z) (bvar den lo z) •
        Exact.reV ((bernV D (tabs den lo hi D) V).1.getD i zeroV) =
      omegaN den lo hi D • (V.map (SP.eval z)).toFun := by
  simp only [bernV, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨hx, hy⟩, hz⟩ := h
  have ex := bern_spec den D lo hi V.x.terms z hx
  have ey := bern_spec den D lo hi V.y.terms z hy
  have ez := bern_spec den D lo hi V.z.terms z hz
  simp only [EN] at ex ey ez
  have hg : ∀ i ∈ Finset.range (sizeN D),
      (List.zipWith3 V3.mk (bern D (tabs den lo hi D) V.x.terms).1
        (bern D (tabs den lo hi D) V.y.terms).1 (bern D (tabs den lo hi D) V.z.terms).1).getD i
          zeroV =
        ⟨(bern D (tabs den lo hi D) V.x.terms).1.getD i (Exact.ofInt 0),
          (bern D (tabs den lo hi D) V.y.terms).1.getD i (Exact.ofInt 0),
          (bern D (tabs den lo hi D) V.z.terms).1.getD i (Exact.ofInt 0)⟩ := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact getD_zipWith3 V3.mk zeroV _ _ _ rfl _ _ _ i (by rw [length_bern]; exact hi')
      (by rw [length_bern]; exact hi') (by rw [length_bern]; exact hi')
  rw [Finset.sum_congr rfl fun i hi ↦ by rw [hg i hi]]
  funext c
  rw [Finset.sum_apply]
  fin_cases c <;>
    simp only [Exact.reV, V3.map, V3.toFun, Pi.smul_apply, smul_eq_mul, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, SP.eval]
  · rw [← ex]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [re_getD]
  · rw [← ey]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [re_getD]
  · rw [← ez]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [re_getD]

/-- The point of a chart pose as a point of the variables `0, …, 4`. -/
noncomputable def ptOf (p : ChartPose) : ℕ → ℝ := fun k ↦ if hk : k < 5 then p.coords ⟨k, hk⟩ else 0

theorem box_vars {b : Box} (hb : boxOk b = true) {p : ChartPose} (hp : b.Mem 5 p.coords) (k : ℕ) :
    0 ≤ avar b.den b.hi (ptOf p) k ∧ 0 ≤ bvar b.den b.lo (ptOf p) k := by
  simp only [boxOk, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨hd, hlo⟩, hhi⟩, -⟩ := hb
  have hd' : (0 : ℝ) < b.den := by exact_mod_cast hd
  by_cases hk : k < 5
  · have := hp ⟨k, hk⟩
    simp only [avar, bvar, ptOf, hk, ↓reduceDIte, Int.cast_natCast]
    rw [div_le_iff₀ hd', le_div_iff₀ hd'] at this
    constructor <;> linarith
  · simp only [avar, bvar, ptOf, hk, ↓reduceDIte, mul_zero, sub_zero, zero_sub]
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    simp

theorem boxOk_lt {b : Box} (hb : boxOk b = true) (D : List ℕ) (hD : D.length = 5) :
    ∀ k < D.length, b.lo.getD k 0 < b.hi.getD k 0 := by
  simp only [boxOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hb
  intro k hk
  exact hb.2 k (by omega)

omit [Add κ] [Sub κ] [Mul κ] [Exact κ] in
theorem length_adeg (m : MLeaf κ) : (adeg m).length = 5 := by simp [adeg]

omit [Add κ] [Sub κ] [Mul κ] [Exact κ] in
theorem length_degOf (m : MLeaf κ) : (degOf m).length = 5 := by simp [degOf, length_adeg]

end Signs

/-! ### Soundness -/

section Sound

open Matrix

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

theorem sum_nonpos' : ∀ {l : List ℝ}, (∀ x ∈ l, x ≤ 0) → l.sum ≤ 0
  | [], _ => le_rfl
  | x :: l, h => by
    rw [List.sum_cons]
    exact add_nonpos (h x List.mem_cons_self)
      (sum_nonpos' fun y hy ↦ h y (List.mem_cons_of_mem _ hy))

theorem sum_map_add_sub {β : Type*} (l : List β) (f g k : β → ℝ) :
    (l.map fun x ↦ f x + g x - k x).sum = (l.map f).sum + (l.map g).sum - (l.map k).sum := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

theorem sum_comb {β : Type*} (l : List β) (r X : β → ℝ) (c K : ℝ) :
    (l.map fun t ↦ r t * (c * X t)).sum + (l.map r).sum * c * K =
      (l.map fun t ↦ r t * c * (X t + K)).sum := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih]
    ring

/-- The value of the plug part of one group. -/
noncomputable def plugG (pts : List (V3 κ)) (a : Fin 3) (k : Fin 4) (ν : κ) (z : ℕ → ℝ)
    (g : MGroup κ) : ℝ :=
  SP.eval z (sumSP (g.terms.map fun t ↦ (⟨t.2⟩ : SP κ) *
    supportG SP.cst (viewSP a) (quatSP k) (dirOf pts g) (V3.smul ν (pt pts t.1)) zeroV))

theorem eval_plugSP (pts : List (V3 κ)) (a : Fin 3) (k : Fin 4) (ν : κ) (m : MLeaf κ)
    (z : ℕ → ℝ) : SP.eval z (plugSP pts a k ν m) = (m.groups.map (plugG pts a k ν z)).sum := by
  rw [plugSP, eval_sumSP, List.map_map]
  rfl

theorem plugG_eq (pts : List (V3 κ)) (a : Fin 3) (k : Fin 4) (ν : κ) (z : ℕ → ℝ)
    (g : MGroup κ) : plugG pts a k ν z g = (g.terms.map fun t ↦ SPoly.run Exact.re z t.2 *
      ((chartQuat k ![z 2, z 3, z 4] ⬝ᵥ chartQuat k ![z 2, z 3, z 4]) *
        ((viewDir a (z 0) (z 1) ⨯₃ Exact.reV (dirOf pts g)) ⬝ᵥ
          (chartRotation k ![z 2, z 3, z 4] *ᵥ Exact.reV (V3.smul ν (pt pts t.1)))))).sum := by
  rw [plugG, eval_sumSP, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ ↦ ?_
  rw [Function.comp_apply, (SP.isArith_eval z).map_mul, eval_plugTerm]
  rfl

theorem eval_msum (z : ℕ → ℝ) (g : MGroup κ) :
    SP.eval z (msum g) = (g.terms.map fun t ↦ SPoly.run Exact.re z t.2).sum := by
  rw [msum, eval_sumSP, List.map_map]
  rfl

theorem ptOf_view (p : ChartPose) : viewDir p.view p.s p.t =
    viewDir p.view (ptOf p 0) (ptOf p 1) := by
  simp [ptOf, ChartPose.coords]

theorem ptOf_rot (p : ChartPose) : (![ptOf p 2, ptOf p 3, ptOf p 4] : Fin 3 → ℝ) = p.x := by
  funext i
  fin_cases i <;> simp [ptOf, ChartPose.coords]

theorem run_one (z : ℕ → ℝ) : SPoly.run Exact.re z [((Exact.ofInt 1 : κ), [])] = 1 := by
  rw [SPoly.run_cons, SPoly.run_nil, SPoly.mono_nil, SPoly.re_one, mul_one, add_zero]

/-- **Soundness of the multiplier check**: no pose of the box fits at the scale `s`. -/
theorem check_sound {pts : List (V3 κ)} {B : ChartBox} {s : Scale κ} {m : MLeaf κ}
    (h : check pts B s m = true) : (Polyhedron.ofPoints pts).NoFitRot B.poses (s.re • 1) := by
  classical
  intro p hp hfit
  obtain ⟨hview, hrot, hmem⟩ := hp
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hbox, hs⟩, hne⟩, htb⟩, hterms⟩, hone⟩, hP⟩, hVs⟩, hrows⟩ := h
  have hpts : pts ≠ [] := by
    rintro rfl
    simp at hne
  rw [ptOf_view, hview, ChartPose.rotation, hrot, ← ptOf_rot] at hfit
  -- the pose
  set z := ptOf p with hz
  set u := viewDir B.view (z 0) (z 1) with hu
  set xq : Fin 3 → ℝ := ![z 2, z 3, z 4] with hxq
  set q := chartQuat B.rot xq with hq
  set R := chartRotation B.rot xq with hR
  have hRSO : R ∈ SO(3) := chartRotation_mem _ _
  have hq2 : 0 < q ⬝ᵥ q := dotProduct_self_pos (chartQuat_ne_zero _ _)
  have hsd : (0 : ℝ) < s.den := by exact_mod_cast Scale.den_pos_of_ok hs
  set sd : ℝ := (s.den : ℝ) with hsdd
  have hθ : sd * s.re = Exact.re s.num := by
    rw [Scale.re, hsdd, mul_div_assoc']
    exact mul_div_cancel_left₀ _ hsd.ne'
  have hsdR : Exact.re (Exact.ofInt (s.den : ℤ) : κ) = sd := by rw [Exact.re_ofInt]; simp [sd]
  have hMx : ∀ x, (R * (s.re • 1)) *ᵥ x = s.re • (R *ᵥ x) := by
    intro x
    rw [Matrix.mul_smul, mul_one, smul_mulVec]
  have hperp : ∀ c : Fin 3 → ℝ, (u ⨯₃ c) ⬝ᵥ u = 0 := fun c ↦ by
    rw [dotProduct_comm, dot_self_cross]
  -- the translation
  obtain ⟨τ, hτ0, S⟩ : ∃ τ : Fin 3 → ℝ, (m.centred = true → τ = 0) ∧ ∀ n, n ⬝ᵥ u = 0 →
      ∀ x ∈ (Polyhedron.ofPoints pts).hull, ∀ H : ℝ,
        (∀ y ∈ (Polyhedron.ofPoints pts).vertices, n ⬝ᵥ y ≤ H) →
          n ⬝ᵥ (s.re • (R *ᵥ x) + τ) ≤ H := by
    cases hc : m.centred
    · obtain ⟨τ, hτ⟩ := hfit.exists_support
      exact ⟨τ, by simp, fun n hn x hx H hH ↦ by rw [← hMx]; exact hτ n hn x hx H hH⟩
    · simp only [hc, ↓reduceIte] at htb
      have hsym : ∀ x ∈ (Polyhedron.ofPoints pts).vertices,
          -x ∈ (Polyhedron.ofPoints pts).vertices := by
        intro x hx
        obtain ⟨v, hv, rfl⟩ := Polyhedron.mem_ofPoints.mp hx
        obtain ⟨w, hw, heq⟩ := List.any_eq_true.mp (List.all_eq_true.mp htb v hv)
        exact Polyhedron.mem_ofPoints.mpr ⟨w, hw, by
          rw [Exact.reV_eq_of_eqV heq, Exact.reV_sub, reV_zeroV, zero_sub]⟩
      exact ⟨0, fun _ ↦ rfl, fun n hn x hx H hH ↦ by
        rw [add_zero, ← hMx]; exact hfit.support_centred hsym n hn x hx H hH⟩
  set τ' : Fin 3 → ℝ := sd • τ with hτ'
  -- the box
  have hd : (0 : ℤ) < (B.box.den : ℤ) := by
    simp only [boxOk, Bool.and_eq_true, decide_eq_true_eq] at hbox
    exact_mod_cast hbox.1.1.1
  have hXY := box_vars hbox hmem
  have hωA := omegaN_pos hd (adeg m) B.box.lo B.box.hi (boxOk_lt hbox _ (length_adeg m))
  have hω := omegaN_pos hd (degOf m) B.box.lo B.box.hi (boxOk_lt hbox _ (length_degOf m))
  set ω := omegaN (B.box.den : ℤ) B.box.lo B.box.hi (degOf m) with hωd
  set w : ℕ → ℝ := fun i ↦ monoN (degOf m) ((idxN (degOf m)).getD i [])
    (avar B.box.den B.box.hi z) (bvar B.box.den B.box.lo z) with hwd
  have hw : ∀ i, 0 ≤ w i := fun i ↦
    monoN_nonneg _ _ _ _ (fun k ↦ (hXY k).1) fun k ↦ (hXY k).2
  have hpos : ∃ i < sizeN (degOf m), 0 < w i := by
    have e := bern_spec (B.box.den : ℤ) (degOf m) B.box.lo B.box.hi
      [((Exact.ofInt 1 : κ), [])] z hone
    rw [run_one, mul_one] at e
    obtain ⟨i, hi, hwi⟩ := exists_monoN_ne (e.trans_ne hω.ne')
    exact ⟨i, hi, lt_of_le_of_ne (hw i) (Ne.symm hwi)⟩
  -- the multipliers
  have hmult : ∀ g ∈ m.groups, ∀ t ∈ g.terms,
      t.1 < pts.length ∧ 0 ≤ SPoly.run Exact.re z t.2 := by
    intro g hg t ht
    have := List.all_eq_true.mp (List.all_eq_true.mp hterms g hg) t ht
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at this
    obtain ⟨hlt, hfl, hnn⟩ := this
    refine ⟨hlt, ?_⟩
    have e := bern_spec (B.box.den : ℤ) (adeg m) B.box.lo B.box.hi t.2 z hfl
    have e0 := EN_nonneg (D := adeg m) (fun k ↦ (hXY k).1) (fun k ↦ (hXY k).2)
      (L := (bern (adeg m) (tabs B.box.den B.box.lo B.box.hi (adeg m)) t.2).1.map Exact.re)
      (by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact Exact.nonneg_sound _ (hnn y hy))
    rw [e] at e0
    exact (mul_nonneg_iff_of_pos_left hωA).mp e0
  -- the maximisers
  have hmax : ∀ n : Fin 3 → ℝ, ∃ a ∈ pts, ∀ y ∈ pts, n ⬝ᵥ Exact.reV y ≤ n ⬝ᵥ Exact.reV a := by
    intro n
    have hne' : pts.toFinset.Nonempty := List.toFinset_nonempty_iff _ |>.mpr hpts
    obtain ⟨a, ha, hmx⟩ := pts.toFinset.exists_max_image (fun v ↦ n ⬝ᵥ Exact.reV v) hne'
    exact ⟨a, List.mem_toFinset.mp ha, fun y hy ↦ hmx y (List.mem_toFinset.mpr hy)⟩
  choose amax hamem hamax using hmax
  set ng : MGroup κ → Fin 3 → ℝ := fun g ↦ u ⨯₃ Exact.reV (dirOf pts g) with hng
  set a' : MGroup κ → Fin 3 → ℝ := fun g ↦ sd • Exact.reV (amax (ng g)) with ha'
  set Wz : MGroup κ → Fin 3 → ℝ := fun g ↦
    ((holeW B.view B.rot g).map (SP.eval z)).toFun with hWz
  set Vz : MGroup κ → Fin 3 → ℝ := fun g ↦ Wz g ⨯₃ Exact.reV (dirOf pts g) with hVz
  have hVz_eq : ∀ g, Vz g = ((g.terms.map fun t ↦ SPoly.run Exact.re z t.2).sum * (q ⬝ᵥ q)) •
      ng g := fun g ↦ by
    simp only [hVz, hWz, toFun_holeW, eval_msum, smul_cross]
    rfl
  -- the inequality of the fit, group by group
  have hgrp : ∀ g ∈ m.groups, plugG pts B.view B.rot s.num z g + Vz g ⬝ᵥ τ' -
      a' g ⬝ᵥ Vz g ≤ 0 := by
    intro g hg
    have e1 : plugG pts B.view B.rot s.num z g = (g.terms.map fun t ↦ SPoly.run Exact.re z t.2 *
        ((q ⬝ᵥ q) * (ng g ⬝ᵥ (R *ᵥ Exact.reV (V3.smul s.num (pt pts t.1)))))).sum := by
      rw [plugG_eq]
    have e2 : Vz g ⬝ᵥ τ' - a' g ⬝ᵥ Vz g = (g.terms.map fun t ↦ SPoly.run Exact.re z t.2).sum *
        (q ⬝ᵥ q) * (ng g ⬝ᵥ τ' - ng g ⬝ᵥ a' g) := by
      rw [hVz_eq]
      simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [dotProduct_comm (a' g) (ng g)]
      ring
    rw [add_sub_assoc, e1, e2, sum_comb]
    refine sum_nonpos' fun x hx ↦ ?_
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hlt, hm⟩ := hmult g hg t ht
    have hv := Nieuwland.Polyhedron.pt_mem_ofPoints hlt
    have hS := S (ng g) (hperp _) _ (subset_convexHull ℝ _ hv) _ fun y hy ↦ by
      obtain ⟨v, hv', rfl⟩ := Polyhedron.mem_ofPoints.mp hy
      exact hamax (ng g) v hv'
    have key : ng g ⬝ᵥ (R *ᵥ Exact.reV (V3.smul s.num (pt pts t.1))) + ng g ⬝ᵥ τ' -
        ng g ⬝ᵥ a' g = sd * (ng g ⬝ᵥ (s.re • (R *ᵥ Exact.reV (pt pts t.1)) + τ) -
          ng g ⬝ᵥ Exact.reV (amax (ng g))) := by
      simp only [ha', hτ', Exact.reV_smul, mulVec_smul, dotProduct_add, dotProduct_smul,
        smul_eq_mul, ← hθ]
      ring
    have : ng g ⬝ᵥ (R *ᵥ Exact.reV (V3.smul s.num (pt pts t.1))) + ng g ⬝ᵥ τ' -
        ng g ⬝ᵥ a' g ≤ 0 := by
      rw [key]
      exact mul_nonpos_of_nonneg_of_nonpos hsd.le (by linarith)
    rw [← add_sub_assoc]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hm hq2.le) this
  -- the total inequality of the fit
  have hAtot : (m.groups.map fun g ↦ plugG pts B.view B.rot s.num z g + Vz g ⬝ᵥ τ' -
      a' g ⬝ᵥ Vz g).sum ≤ 0 :=
    sum_nonpos' fun x hx ↦ by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
      exact hgrp g hg
  -- the dense coefficients
  set UD : List (List (List κ)) := tabs (B.box.den : ℤ) B.box.lo B.box.hi (degOf m) with hUD
  set PL := bern (degOf m) UD (plugSP pts B.view B.rot s.num m).terms with hPL
  set Wd : MGroup κ → ℕ → V3 κ := fun g i ↦
    (bernV (degOf m) UD (holeW B.view B.rot g)).1.getD i zeroV with hWd
  set Vd : MGroup κ → ℕ → Fin 3 → ℝ := fun g i ↦
    Exact.reV ((Wd g i).cross (dirOf pts g)) with hVd
  set n := sizeN (degOf m) with hn
  have hPw : ∑ i ∈ Finset.range n, w i * Exact.re (PL.1.getD i (Exact.ofInt 0)) =
      ω * (m.groups.map (plugG pts B.view B.rot s.num z)).sum := by
    have e := bern_spec (B.box.den : ℤ) (degOf m) B.box.lo B.box.hi _ z hP
    rw [← eval_plugSP, SP.eval, ← e, EN]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [re_getD]
  have hVw : ∀ g ∈ m.groups, ∑ i ∈ Finset.range n, w i • Vd g i = ω • Vz g := fun g hg ↦ by
    have e : ∑ i ∈ Finset.range n, w i • Exact.reV (Wd g i) = ω • Wz g :=
      bernV_spec _ _ _ _ _ z (List.all_eq_true.mp hVs _ (List.mem_map.mpr ⟨g, hg, rfl⟩))
    simp only [hVd, hVz, Exact.reV_cross]
    rw [sum_smul_cross, e, smul_cross]
  -- the rows
  set hole := pts.map (V3.smul (Exact.ofInt (s.den : ℤ) : κ)) with hhole
  set rs : ℕ → List (GRow κ) := fun i ↦ m.groups.map fun g ↦
    (⟨dirOf pts g, hole.map (dirOf pts g).cross, Wd g i⟩ : GRow κ) with hrs
  set vs : ℕ → List (V3 κ) := fun i ↦ m.groups.map fun g ↦
    (Wd g i).cross (dirOf pts g) with hvs
  have hrv : ∀ i, (rs i).map GRow.v = vs i := fun i ↦ by
    simp only [hrs, hvs, List.map_map]
    rfl
  set Hm : MGroup κ → ℕ → ℝ := fun g i ↦ Exact.re
    (⟨dirOf pts g, hole.map (dirOf pts g).cross, Wd g i⟩ : GRow κ).bound.1 with hHm
  have main : ∀ tb : Option κ, rowsOk (rowOk (m.groups.map fun g ↦
        (dirOf pts g, hole.map (dirOf pts g).cross)) tb) PL.1
      ((m.groups.map fun g ↦ bernV (degOf m) UD (holeW B.view B.rot g)).map (·.1)) = true →
      (tb = none → τ = 0) → (∀ T, tb = some T → T = (tbound hole (V3.smul s.num (pt pts 0))).1 ∧
        (tbound hole (V3.smul s.num (pt pts 0))).2 = true) → False := by
    intro tb hrw htn hts
    have hrow : ∀ i < n, rowOkR tb (PL.1.getD i (Exact.ofInt 0)) (rs i) = true := by
      intro i hi
      have := rowsOk_spec _ _ _ hrw i (by rw [length_bern]; exact hi)
      rw [List.map_map, List.map_map, rowOk, zipWith_map_map] at this
      exact this
    have hspec : ∀ i < n,
        (∀ r ∈ rs i, ∀ x ∈ r.hs, Exact.reV x ⬝ᵥ Exact.reV r.w ≤ Exact.re r.bound.1) ∧
        0 < Exact.re (PL.1.getD i (Exact.ofInt 0)) -
          ((rs i).map fun r ↦ Exact.re r.bound.1).sum - tnOf tb (vs i) ∧
        (tb.isSome = true → l1 (Exact.reV ((vs i).foldr V3.add zeroV)) ≤
          Exact.re (norm1C ((vs i).foldr V3.add zeroV))) := fun i hi ↦ by
      have := rowOkR_spec (hrow i hi)
      rw [hrv] at this
      exact this
    -- the translation term
    have hτb : -(∑ i ∈ Finset.range n, w i * tnOf tb (vs i)) ≤
        (m.groups.map fun g ↦ (∑ i ∈ Finset.range n, w i • Vd g i) ⬝ᵥ τ').sum := by
      cases tb with
      | none =>
        have h0 := htn rfl
        simp [tnOf, hτ', h0]
      | some T =>
        obtain ⟨hT, hTok⟩ := hts T rfl
        simp only [tbound, Bool.and_eq_true, List.all_eq_true] at hT hTok
        obtain ⟨⟨hmx, hhl⟩, hv0⟩ := hTok
        have hb1 : ∀ a ∈ hole, l1 (Exact.reV a) ≤ Exact.re (maxC (hole.map norm1C)) :=
          fun a ha ↦ (norm1Ok_spec (hhl a ha)).trans
            (maxOk_spec hmx _ (List.mem_map.mpr ⟨a, ha, rfl⟩))
        have hTre : Exact.re T = Exact.re (maxC (hole.map norm1C)) +
            Exact.re (norm1C (V3.smul s.num (pt pts 0))) := by rw [hT, Exact.re_add]
        have hN0 := norm1Ok_spec hv0
        have hT0 : 0 ≤ Exact.re T := by
          obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil pts hpts
          have := hb1 _ (List.mem_map.mpr ⟨v, hv, rfl⟩)
          rw [hTre]
          linarith [l1_nonneg (Exact.reV (V3.smul (Exact.ofInt (s.den : ℤ) : κ) v)),
            l1_nonneg (Exact.reV (V3.smul s.num (pt pts 0)))]
        set W' := (m.groups.map fun g ↦ ∑ i ∈ Finset.range n, w i • Vd g i).sum with hW'
        rw [listSum_dotProduct]
        have hWu : W' ⬝ᵥ u = 0 := by
          rw [hW', ← listSum_dotProduct]
          refine List.sum_eq_zero fun x hx ↦ ?_
          obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
          rw [hVw g hg, hVz_eq, smul_dotProduct, smul_dotProduct, hperp, smul_zero, smul_zero]
        have hWsum : W' = ∑ i ∈ Finset.range n, w i • Exact.reV ((vs i).foldr V3.add zeroV) := by
          rw [hW', listSum_finsetSum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [reV_foldr_add, List.smul_sum, List.map_map, List.map_map]
          rfl
        have hl1W : l1 W' ≤ ∑ i ∈ Finset.range n,
            w i * Exact.re (norm1C ((vs i).foldr V3.add zeroV)) := by
          rw [hWsum]
          exact (l1_sum_le w hw _ _).trans (Finset.sum_le_sum fun i hi ↦
            mul_le_mul_of_nonneg_left ((hspec i (Finset.mem_range.mp hi)).2.2 rfl) (hw i))
        -- the bound from the fit
        have hH : ∀ y ∈ (Polyhedron.ofPoints pts).vertices,
            (-W') ⬝ᵥ y ≤ l1 W' * (Exact.re (maxC (hole.map norm1C)) / sd) := by
          intro y hy
          obtain ⟨v, hv, rfl⟩ := Polyhedron.mem_ofPoints.mp hy
          have h1 := hb1 _ (List.mem_map.mpr ⟨v, hv, rfl⟩)
          rw [Exact.reV_smul, hsdR, l1_smul hsd.le] at h1
          have h2 : l1 (Exact.reV v) ≤ Exact.re (maxC (hole.map norm1C)) / sd := by
            rw [le_div_iff₀ hsd]; linarith
          calc (-W') ⬝ᵥ Exact.reV v ≤ |(-W') ⬝ᵥ Exact.reV v| := le_abs_self _
            _ ≤ l1 (-W') * l1 (Exact.reV v) := abs_dot_le _ _
            _ ≤ _ := by rw [l1_neg]; exact mul_le_mul_of_nonneg_left h2 (l1_nonneg _)
        have h0 := Nieuwland.Polyhedron.pt_mem_ofPoints (pts := pts) (j := 0)
          (List.length_pos_of_ne_nil hpts)
        have hS := S (-W') (by rw [neg_dotProduct, hWu, neg_zero]) _ (subset_convexHull ℝ _ h0)
          _ hH
        simp only [neg_dotProduct, dotProduct_add, dotProduct_smul, smul_eq_mul] at hS
        have hR0 := abs_dot_mulVec_le hRSO W' (Exact.reV (V3.smul s.num (pt pts 0)))
        rw [Exact.reV_smul, mulVec_smul, dotProduct_smul, smul_eq_mul] at hR0
        have hS2 : -(sd * s.re * (W' ⬝ᵥ (R *ᵥ Exact.reV (pt pts 0)))) - sd * (W' ⬝ᵥ τ) ≤
            l1 W' * Exact.re (maxC (hole.map norm1C)) := by
          calc _ = sd * (s.re * -(W' ⬝ᵥ (R *ᵥ Exact.reV (pt pts 0))) + -(W' ⬝ᵥ τ)) := by ring
            _ ≤ sd * (l1 W' * (Exact.re (maxC (hole.map norm1C)) / sd)) :=
              mul_le_mul_of_nonneg_left hS hsd.le
            _ = _ := by field_simp
        rw [hθ] at hS2
        have hfitb : -(W' ⬝ᵥ τ') ≤ l1 W' * Exact.re T := by
          rw [hτ', dotProduct_smul, smul_eq_mul, hTre, mul_add]
          rw [Exact.reV_smul] at hN0
          have := mul_le_mul_of_nonneg_left hN0 (l1_nonneg W')
          linarith [le_abs_self (Exact.re s.num * (W' ⬝ᵥ (R *ᵥ Exact.reV (pt pts 0))))]
        have hsumT : ∑ i ∈ Finset.range n, w i * tnOf (some T) (vs i) = Exact.re T *
            ∑ i ∈ Finset.range n, w i * Exact.re (norm1C ((vs i).foldr V3.add zeroV)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          simp only [tnOf]
          ring
        rw [hsumT]
        have := mul_le_mul_of_nonneg_left hl1W hT0
        linarith
    have hfin := final_pos (gs := m.groups) (a := a') (V := Vd) (H := Hm)
      (TN := fun i ↦ tnOf tb (vs i)) (Pd := fun i ↦ Exact.re (PL.1.getD i (Exact.ofInt 0)))
      hw hpos (fun i hi ↦ by
        have := (hspec i hi).2.1
        simp only [hrs, List.map_map, Function.comp_def] at this
        exact this) (fun i hi g hg ↦ by
        have := (hspec i hi).1 _ (List.mem_map.mpr ⟨g, hg, rfl⟩) _
          (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨_, hamem (ng g), rfl⟩, rfl⟩)
        rw [Exact.reV_cross, Exact.reV_smul, hsdR] at this
        simp only [hVd, ha', Exact.reV_cross]
        rw [triple_product_permutation, dotProduct_comm]
        exact this) hτb
    have e2 : (m.groups.map fun g ↦ (∑ i ∈ Finset.range n, w i • Vd g i) ⬝ᵥ τ').sum =
        ω * (m.groups.map fun g ↦ Vz g ⬝ᵥ τ').sum := by
      rw [← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun g hg ↦ ?_
      rw [hVw g hg, smul_dotProduct, smul_eq_mul]
    have e3 : (m.groups.map fun g ↦ a' g ⬝ᵥ ∑ i ∈ Finset.range n, w i • Vd g i).sum =
        ω * (m.groups.map fun g ↦ a' g ⬝ᵥ Vz g).sum := by
      rw [← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun g hg ↦ ?_
      rw [hVw g hg, dotProduct_smul, smul_eq_mul]
    have e4 : (m.groups.map fun g ↦ plugG pts B.view B.rot s.num z g + Vz g ⬝ᵥ τ' -
        a' g ⬝ᵥ Vz g).sum = (m.groups.map (plugG pts B.view B.rot s.num z)).sum +
          (m.groups.map fun g ↦ Vz g ⬝ᵥ τ').sum - (m.groups.map fun g ↦ a' g ⬝ᵥ Vz g).sum := by
      exact sum_map_add_sub _ _ _ _
    have hneg := mul_le_mul_of_nonneg_left hAtot hω.le
    rw [e4, mul_zero, mul_sub, mul_add] at hneg
    rw [hPw, e2, e3] at hfin
    linarith
  cases hc : m.centred
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hrows htb
    exact main _ hrows (fun h ↦ by simp at h) fun T hT ↦ by
      simp only [Option.some.injEq] at hT
      exact ⟨hT.symm, htb⟩
  · simp only [hc, ↓reduceIte] at hrows
    exact main none hrows (fun _ ↦ hτ0 hc) fun T hT ↦ by simp at hT

end Sound

end Mult

end Nieuwland.Check
