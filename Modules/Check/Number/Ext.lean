import Modules.Check.Number.Exact
import Modules.Check.Sign.Bound
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.GetD

/-!
# Exact values in coordinates

A check computes with polynomials whose coefficients are exact values of a body's field: integers
for rational bodies, `ℤ[√d]`, `ℤ[θ]`. The kernel evaluates such a polynomial at a packed integer
point (`Modules/Check/Polynomial/Pack.lean`) and reads its coefficients off the digits; over a field this needs
the *coordinates* of exact values in a basis `β₀, β₁, …` of real numbers. `ExactBasis κ` extends
`Exact κ` by them:

* `coords a`: integer coordinates with `re a = ∑ᵢ βᵢ aᵢ` (`ExactBasis.re_eq`), linear in `a` and
  multiplicative through `mulG`; `ofCoords` is the converse.
* `mulG k a b`: the product of coordinate lists over any type with `+`, `-`, `*` and integer
  constants embedded by `k`, natural in maps that commute with the operations
  (`ExactBasis.mulG_natural`) and the product of values over `ℝ` (`ExactBasis.bsum_mulG`).
* `lowerOf`: the centred-form lower bound (`Modules/Check/Sign/Bound.lean`) of a polynomial whose
  coordinates are packed in numerals, one per coordinate, with whether every sign it needed was
  decided (`ExactBasis.lowerOf_le`). For a field it reads the coordinates of each coefficient in
  lockstep and tests the sign of the coefficient they form (`readK`, `readK_le`); for the integers
  it is `DPoly.penalty`, which reads with natural-number arithmetic only, about twenty times faster
  in the kernel.

`Ext κ γ` is the coordinate ring of `κ` over `γ`: coordinate lists with entries in `γ`, multiplied
by `mulG`. Computations whose constants lie in `κ` run in `Ext κ γ` for the interpretations of
`Modules/Check/Number/Arith.lean`: expressions (one per coordinate, in proofs), `AbsNat` and `ShapeL`
(coefficient and degree bounds, for the kernel) and `ℝ`, where `Ext.re` is the value. The kernel
computes values in `κ` itself, whose coordinates are those over `ℤ` (`Ext.isArith_ofExact`). An
input `x` is `x` times the coordinates of `1` (`Ext.var`), so that `Exact.ofInt` has the
coordinates of an input (`ExactBasis.coords_ofInt`).

`GenPoly κ` is a computation with constants in `κ`, natural in maps that commute with the
operations; its expression `GenPoly.ext` has one integer polynomial per coordinate, and its real
value is `GenPoly.run_re`.

## Main definitions

* `Nieuwland.Check.readK`: the lockstep reading of coordinate numerals.
* `Nieuwland.Check.ExactBasis`: the interface; instances for `ℤ` and `ZSqrt d`.
* `Nieuwland.Check.Ext`: the coordinate ring over `γ`, with `Ext.map`, `Ext.re`, `Ext.const`.
* `Nieuwland.Check.GenPoly`: generic computations with constants in `κ`.
-/

open Finset

namespace Nieuwland.Check

/-! ### Lists padded with a default -/

/-- `f` entrywise on two lists, the shorter one padded by `z`. -/
def zipD {γ : Type*} (z : γ) (f : γ → γ → γ) : List γ → List γ → List γ
  | [], bs => bs.map (f z)
  | a :: as, [] => (a :: as).map (f · z)
  | a :: as, b :: bs => f a b :: zipD z f as bs

theorem getD_zipD {γ : Type*} {z : γ} {f : γ → γ → γ} (hz : f z z = z) :
    ∀ (as bs : List γ) (i : ℕ), (zipD z f as bs).getD i z = f (as.getD i z) (bs.getD i z)
  | [], bs, i => by
    have := List.getD_map (l := bs) (n := i) (d := z) (f z)
    rw [hz] at this
    simp only [zipD, this, List.getD_nil]
  | a :: as, [], i => by
    have := List.getD_map (l := a :: as) (n := i) (d := z) (f · z)
    rw [hz] at this
    simp only [zipD, this, List.getD_nil]
  | _ :: _, _ :: _, 0 => rfl
  | _ :: as, _ :: bs, i + 1 => by
    simp only [zipD, List.getD_cons_succ, getD_zipD hz as bs i]

theorem map_zipD {γ δ : Type*} {z : γ} {f : γ → γ → γ} {g : δ → δ → δ} {h : γ → δ}
    (hh : ∀ a b, h (f a b) = g (h a) (h b)) :
    ∀ as bs : List γ, (zipD z f as bs).map h = zipD (h z) g (as.map h) (bs.map h)
  | [], bs => by simp [zipD, hh]
  | a :: as, [] => by simp [zipD, hh]
  | a :: as, b :: bs => by simp [zipD, hh, map_zipD hh as bs]

/-- `getD` of a mapped list, when `f` maps the default to the default. -/
theorem getD_map_of_eq {γ δ : Type*} {f : γ → δ} {z : γ} {z' : δ} (hz : f z = z') (l : List γ)
    (i : ℕ) : (l.map f).getD i z' = f (l.getD i z) := by
  rw [← hz]
  exact List.getD_map (l := l) (n := i) (d := z) f

/-- `getD` of a mapped list, inside the list. -/
theorem getD_map_of_lt {γ δ : Type*} (f : γ → δ) (z : γ) (z' : δ) {l : List γ} {i : ℕ}
    (hi : i < l.length) : (l.map f).getD i z' = f (l.getD i z) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi,
    List.getElem_map]

/-! ### Sums against a basis -/

/-- `∑_{i < n} β i * l[i]`, missing entries counting as `0`. -/
noncomputable def bsum (β : ℕ → ℝ) (n : ℕ) (l : List ℝ) : ℝ :=
  ∑ i ∈ range n, β i * l.getD i 0

theorem bsum_zipD_add (β : ℕ → ℝ) (n : ℕ) (a b : List ℝ) :
    bsum β n (zipD 0 (· + ·) a b) = bsum β n a + bsum β n b := by
  simp only [bsum, getD_zipD (add_zero (0 : ℝ)), mul_add, sum_add_distrib]

theorem bsum_zipD_sub (β : ℕ → ℝ) (n : ℕ) (a b : List ℝ) :
    bsum β n (zipD 0 (· - ·) a b) = bsum β n a - bsum β n b := by
  simp only [bsum, getD_zipD (sub_zero (0 : ℝ)), mul_sub, sum_sub_distrib]

theorem bsum_map_mul (β : ℕ → ℝ) (n : ℕ) (l : List ℤ) (x : ℝ) :
    bsum β n (l.map fun e : ℤ ↦ (e : ℝ) * x) = bsum β n (l.map Int.cast) * x := by
  simp only [bsum, sum_mul]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [getD_map_of_eq (z := (0 : ℤ)) (by simp), getD_map_of_eq (z := (0 : ℤ)) (by simp)]
  ring

/-! ### Reading coordinate numerals -/

section Read

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The contribution of the coefficient `q` to the centred-form bound at a monomial of value `m`
(flags as in `DPoly.lower`): `q` if `zr` (`m = 1`), else `min(0, q)` if `ev` (`m ∈ [0, 1]`) and
`-|q|` otherwise (`m ∈ [-1, 1]`); with whether the sign of `q` was decided. -/
def leafK (ev zr : Bool) (q : κ) : κ × Bool :=
  bif zr then (q, true)
  else bif Exact.nonneg q then (bif ev then Exact.ofInt 0 else Exact.ofInt 0 - q, true)
  else bif Exact.nonneg (Exact.ofInt 0 - q) then (q, true)
  else (Exact.ofInt 0, false)

theorem re_zero : Exact.re (Exact.ofInt 0 : κ) = 0 := by
  rw [Exact.re_ofInt, Int.cast_zero]

theorem leafK_le {ev zr : Bool} {q : κ} {m : ℝ} (hzr : zr = true → m = 1)
    (hev : ev = true → 0 ≤ m) (hm : |m| ≤ 1) (h : (leafK ev zr q).2 = true) :
    Exact.re (leafK ev zr q).1 ≤ m * Exact.re q := by
  have hneg : Exact.re (Exact.ofInt 0 - q) = -Exact.re q := by rw [Exact.re_sub, re_zero]; ring
  have hab := abs_le.mp hm
  cases zr
  · cases hq : Exact.nonneg q
    · cases hq' : Exact.nonneg (Exact.ofInt 0 - q)
      · simp [leafK, hq, hq'] at h
      · have := Exact.nonneg_sound _ hq'
        rw [hneg] at this
        simp only [leafK, hq, hq', Bool.cond_false, Bool.cond_true]
        nlinarith
    · have := Exact.nonneg_sound _ hq
      cases ev
      · simp only [leafK, hq, Bool.cond_false, Bool.cond_true, hneg]
        nlinarith
      · simp only [leafK, hq, Bool.cond_false, Bool.cond_true, re_zero]
        exact mul_nonneg (hev rfl) this
  · simp [leafK, hzr rfl]

/-- The sum of two contributions; both signs must have been decided. -/
def addK (a b : κ × Bool) : κ × Bool := (a.1 + b.1, a.2 && b.2)

/-- **The centred-form bound of coordinate numerals.** The numerals `Ns` hold the coordinates of a
polynomial's coefficients, one numeral per coordinate, in `B`-bit digits biased by `h = 2^(B-1)`
(`P₀ = 2^B`) in the layout `ls` (`DPoly.layout`). They are read in lockstep: the digits of a slot
are the coordinates of its coefficient (built by `ofC`), whose contribution is `leafK`; flags as
in `DPoly.lower`. -/
def readK (ofC : List ℤ → κ) (h P₀ : ℕ) : List (ℕ × ℕ) → Bool → Bool → List ℕ → κ × Bool
  | [], ev, zr, Ns => leafK ev zr (ofC (Ns.map fun N ↦ Int.subNatNat (Nat.mod N P₀) h))
  | (m, P) :: ls, ev, zr, Ns => readKL (readK ofC h P₀ ls) P ev zr 0 m Ns
where
  /-- `m` blocks of modulus `P` of each numeral, the first of exponent `k`, each read by `f`. -/
  readKL (f : Bool → Bool → List ℕ → κ × Bool) (P : ℕ) (ev zr : Bool) :
      ℕ → ℕ → List ℕ → κ × Bool
    | _, 0, _ => (Exact.ofInt 0, true)
    | k, m + 1, Ns => addK (f (ev && k % 2 == 0) (zr && k == 0) (Ns.map fun N ↦ Nat.mod N P))
        (readKL f P ev zr (k + 1) m (Ns.map fun N ↦ Nat.div N P))

/-- `readK` with shifts and masks where the block moduli are powers of two (`DPoly.divP2`,
`DPoly.modP2`). -/
def readKS (ofC : List ℤ → κ) (h P₀ : ℕ) : List (ℕ × ℕ) → Bool → Bool → List ℕ → κ × Bool
  | [], ev, zr, Ns => leafK ev zr (ofC (Ns.map fun N ↦ Int.subNatNat (Nat.mod N P₀) h))
  | (m, P) :: ls, ev, zr, Ns => readKLS (readKS ofC h P₀ ls) P ev zr 0 m Ns
where
  /-- `readK.readKL` with shifts and masks. -/
  readKLS (f : Bool → Bool → List ℕ → κ × Bool) (P : ℕ) (ev zr : Bool) :
      ℕ → ℕ → List ℕ → κ × Bool
    | _, 0, _ => (Exact.ofInt 0, true)
    | k, m + 1, Ns => addK (f (ev && k % 2 == 0) (zr && k == 0)
        (Ns.map fun N ↦ DPoly.modP2 N P)) (readKLS f P ev zr (k + 1) m
          (Ns.map fun N ↦ DPoly.divP2 N P))

private theorem nat_div' (a b : ℕ) : Nat.div a b = a / b := rfl
private theorem nat_mod' (a b : ℕ) : Nat.mod a b = a % b := rfl

theorem readKL_eq_readKLS (f : Bool → Bool → List ℕ → κ × Bool) (P : ℕ) (ev zr : Bool) :
    ∀ k m Ns, readK.readKL f P ev zr k m Ns = readKS.readKLS f P ev zr k m Ns
  | _, 0, _ => rfl
  | k, m + 1, Ns => by
    simp only [readK.readKL, readKS.readKLS, DPoly.divP2_eq, DPoly.modP2_eq, nat_div', nat_mod',
      readKL_eq_readKLS f P ev zr (k + 1) m]

@[csimp] theorem readK_eq_readKS : @readK = @readKS := by
  funext κ _ _ _ _ ofC h P₀ ls
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    funext ev zr Ns
    obtain ⟨m, P⟩ := l
    simp only [readK, readKS, readKL_eq_readKLS, ih]

/-- **Soundness of `readK`**: if `ofC` builds values with the given coordinates in the basis
`β₀, …, β_{dim-1}`, the bound read off the numerals is at most `m` times the polynomial
`∑ⱼ βⱼ Tⱼ` of the unpacked numerals `Tⱼ`. -/
theorem readK_le (ofC : List ℤ → κ) (β : ℕ → ℝ) (dim : ℕ)
    (hofC : ∀ l : List ℤ, dim ≤ l.length →
      Exact.re (ofC l) = ∑ j ∈ range dim, β j * (l.getD j 0 : ℝ))
    {B : ℕ} (hB : 0 < B) : ∀ (n : ℕ) (e : List ℕ) (ev zr : Bool) (Ns : List ℕ) (y : Fin n → ℝ)
      (m : ℝ), dim ≤ Ns.length → (∀ i, |y i| ≤ 1) → (zr = true → m = 1) → (ev = true → 0 ≤ m) →
      |m| ≤ 1 → (readK ofC (2 ^ (B - 1)) (2 ^ B) (DPoly.layout B n e) ev zr Ns).2 = true →
      Exact.re (readK ofC (2 ^ (B - 1)) (2 ^ B) (DPoly.layout B n e) ev zr Ns).1 ≤
        m * ∑ j ∈ range dim, β j * DPoly.eval n (DPoly.unpack n e B (Ns.getD j 0)) y
  | 0, e, ev, zr, Ns, y, m, hlen, _, hzr, hev, hm, h => by
    simp only [DPoly.layout, readK] at h ⊢
    refine (leafK_le hzr hev hm h).trans (le_of_eq ?_)
    rw [hofC _ (by simpa using hlen)]
    congr 1
    refine sum_congr rfl fun j hj ↦ ?_
    have hj' : j < Ns.length := lt_of_lt_of_le (mem_range.mp hj) hlen
    rw [getD_map_of_lt _ 0 _ hj', DPoly.unpack, DPoly.eval_ofInt, Int.subNatNat_eq_coe]
    push_cast
    rfl
  | n + 1, e, ev, zr, Ns, y, m, hlen, hy, hzr, hev, hm, h => by
    set w := B * DPoly.slots e.tail
    set f := readK ofC (2 ^ (B - 1)) (2 ^ B) (DPoly.layout B n e.tail)
    have key : ∀ (M k : ℕ) (Ns : List ℕ), dim ≤ Ns.length →
        (readK.readKL f (2 ^ w) ev zr k M Ns).2 = true →
        Exact.re (readK.readKL f (2 ^ w) ev zr k M Ns).1 ≤
          m * y 0 ^ k * ∑ j ∈ range dim, β j * horner (fun q ↦ DPoly.eval n q (Fin.tail y))
            (y 0) (DPoly.unpackL (DPoly.unpack n e.tail B) w M (Ns.getD j 0)) := by
      intro M
      induction M with
      | zero =>
        intro k Ns _ _
        simp [readK.readKL, DPoly.unpackL, re_zero]
      | succ M ih =>
        intro k Ns hl h
        simp only [readK.readKL, addK, Bool.and_eq_true] at h ⊢
        have h₀ : |y 0| ≤ 1 := hy 0
        have hmk : |m * y 0 ^ k| ≤ 1 := by
          rw [abs_mul, abs_pow]
          calc |m| * |y 0| ^ k ≤ 1 * 1 :=
                mul_le_mul hm (pow_le_one₀ (abs_nonneg _) h₀) (by positivity) zero_le_one
            _ = 1 := one_mul 1
        have ha := readK_le ofC β dim hofC hB n e.tail (ev && k % 2 == 0) (zr && k == 0)
          (Ns.map fun N ↦ Nat.mod N (2 ^ w)) (Fin.tail y) (m * y 0 ^ k) (by simpa using hl)
          (fun i ↦ hy i.succ) (by
            intro h
            simp only [Bool.and_eq_true, beq_iff_eq] at h
            rw [hzr h.1, h.2, pow_zero, mul_one])
          (by
            intro h
            simp only [Bool.and_eq_true, beq_iff_eq] at h
            have hk : Even k := Nat.even_iff.mpr h.2
            exact mul_nonneg (hev h.1) (hk.pow_nonneg _)) hmk h.1
        have hb := ih (k + 1) (Ns.map fun N ↦ Nat.div N (2 ^ w)) (by simpa using hl) h.2
        have hmod : ∀ j, (Ns.map fun N ↦ Nat.mod N (2 ^ w)).getD j 0 = Ns.getD j 0 % 2 ^ w :=
          fun j ↦ getD_map_of_eq (f := fun N ↦ Nat.mod N (2 ^ w)) (z := 0) (Nat.zero_mod _) Ns j
        have hdiv : ∀ j, (Ns.map fun N ↦ Nat.div N (2 ^ w)).getD j 0 = Ns.getD j 0 / 2 ^ w :=
          fun j ↦ getD_map_of_eq (f := fun N ↦ Nat.div N (2 ^ w)) (z := 0) (Nat.zero_div _) Ns j
        simp only [hmod] at ha
        simp only [hdiv] at hb
        rw [Exact.re_add]
        simp only [DPoly.unpackL, horner_cons, mul_add, sum_add_distrib]
        have e₁ : ∑ j ∈ range dim, β j * (y 0 * horner (fun q ↦ DPoly.eval n q (Fin.tail y))
            (y 0) (DPoly.unpackL (DPoly.unpack n e.tail B) w M (Ns.getD j 0 / 2 ^ w))) =
            y 0 * ∑ j ∈ range dim, β j * horner (fun q ↦ DPoly.eval n q (Fin.tail y)) (y 0)
              (DPoly.unpackL (DPoly.unpack n e.tail B) w M (Ns.getD j 0 / 2 ^ w)) := by
          rw [mul_sum]
          exact sum_congr rfl fun _ _ ↦ by ring
        rw [e₁, pow_succ] at *
        nlinarith [ha, hb]
    simp only [DPoly.layout_succ, readK] at h ⊢
    have := key (e.headD 0 + 1) 0 Ns hlen h
    simp only [pow_zero, mul_one] at this
    refine this.trans (le_of_eq ?_)
    rfl

end Read

/-! ### The interface -/

/-- **Exact values in coordinates** (module docs): `Exact κ` with integer coordinates in a basis
`β₀, …, β_{dim-1}` of real numbers, the product of coordinate lists as a generic computation
`mulG`, and the centred-form bound of packed coordinates `lowerOf`. -/
class ExactBasis (κ : Type) [Add κ] [Sub κ] [Mul κ] extends Exact κ where
  /-- The number of coordinates. -/
  dim : ℕ
  /-- The basis values, erased like `Exact.reE`; `ExactBasis.basis` reads them. -/
  basisE : ℕ → Erased ℝ
  /-- The coordinates of a value (missing ones are `0`). -/
  coords : κ → List ℤ
  /-- The value with given coordinates. -/
  ofCoords : List ℤ → κ
  /-- The product of coordinate lists, with integer constants embedded by the first argument. -/
  mulG : {γ : Type} → [Add γ] → [Sub γ] → [Mul γ] → (ℤ → γ) → List γ → List γ → List γ
  /-- The centred-form bound read off the numerals of the coordinates (shape, digit size,
  numerals), with whether every sign it needed was decided. -/
  lowerOf : ℕ → List ℕ → ℕ → List ℕ → κ × Bool
  /-- The scale `2^apxK` of the approximations `apx`. -/
  apxK : ℕ
  /-- Integer approximations `aⱼ` of `2^apxK βⱼ` with error bounds `εⱼ`, as pairs `(aⱼ, εⱼ)`
  (missing ones are `(0, 0)`). -/
  apx : List (ℤ × ℕ)
  mulG_natural : ∀ {γ δ : Type} [Add γ] [Sub γ] [Mul γ] [Add δ] [Sub δ] [Mul δ] (f : γ → δ),
    IsArith f → ∀ (k : ℤ → γ) (a b : List γ), (mulG k a b).map f = mulG (f ∘ k) (a.map f) (b.map f)
  bsum_mulG' : ∀ a b : List ℝ, bsum (fun j ↦ (basisE j).out) dim (mulG Int.cast a b) =
    bsum (fun j ↦ (basisE j).out) dim a * bsum (fun j ↦ (basisE j).out) dim b
  re_eq' : ∀ a, (reE a).out = bsum (fun j ↦ (basisE j).out) dim ((coords a).map Int.cast)
  coords_add : ∀ a b, coords (a + b) = zipD 0 (· + ·) (coords a) (coords b)
  coords_sub : ∀ a b, coords (a - b) = zipD 0 (· - ·) (coords a) (coords b)
  coords_mul : ∀ a b, coords (a * b) = mulG id (coords a) (coords b)
  coords_ofInt : ∀ c, coords (ofInt c) = (coords (ofInt 1)).map (· * c)
  coords_ofCoords : ∀ (l : List ℤ) (i : ℕ), i < dim → (coords (ofCoords l)).getD i 0 = l.getD i 0
  lowerOf_le' : ∀ (n : ℕ) (sh : List ℕ) (B : ℕ) (Ns : List ℕ) (y : Fin n → ℝ), 0 < B →
    dim ≤ Ns.length → (∀ i, |y i| ≤ 1) → (lowerOf n sh B Ns).2 = true →
    (reE (lowerOf n sh B Ns).1).out ≤
      ∑ j ∈ range dim, (basisE j).out * DPoly.eval n (DPoly.unpack n sh B (Ns.getD j 0)) y
  apx_sound' : ∀ j < dim,
    |(2 : ℝ) ^ apxK * (basisE j).out - ((apx.getD j (0, 0)).1 : ℝ)| ≤ ((apx.getD j (0, 0)).2 : ℝ)

namespace ExactBasis

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The basis values. -/
noncomputable def basis (κ : Type) [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] (j : ℕ) : ℝ :=
  (basisE (κ := κ) j).out

theorem bsum_mulG (a b : List ℝ) : bsum (basis κ) (dim κ) (mulG κ Int.cast a b) =
    bsum (basis κ) (dim κ) a * bsum (basis κ) (dim κ) b :=
  bsum_mulG' a b

theorem re_eq (a : κ) : Exact.re a = bsum (basis κ) (dim κ) ((coords a).map Int.cast) :=
  re_eq' a

theorem lowerOf_le (n : ℕ) (sh : List ℕ) (B : ℕ) (Ns : List ℕ) (y : Fin n → ℝ) (hB : 0 < B)
    (hl : dim κ ≤ Ns.length) (hy : ∀ i, |y i| ≤ 1) (h : (lowerOf (κ := κ) n sh B Ns).2 = true) :
    Exact.re (lowerOf (κ := κ) n sh B Ns).1 ≤
      ∑ j ∈ range (dim κ), basis κ j * DPoly.eval n (DPoly.unpack n sh B (Ns.getD j 0)) y :=
  lowerOf_le' n sh B Ns y hB hl hy h

theorem apx_sound (j : ℕ) (hj : j < dim κ) :
    |(2 : ℝ) ^ apxK κ * basis κ j - ((apx κ |>.getD j (0, 0)).1 : ℝ)| ≤
      ((apx κ |>.getD j (0, 0)).2 : ℝ) :=
  apx_sound' j hj

theorem bsum_congr {l l' : List ℝ} (h : ∀ i < dim κ, l.getD i 0 = l'.getD i 0) :
    bsum (basis κ) (dim κ) l = bsum (basis κ) (dim κ) l' :=
  sum_congr rfl fun i hi ↦ by rw [h i (mem_range.mp hi)]

theorem re_ofCoords (l : List ℤ) : Exact.re (ofCoords l : κ) =
    bsum (basis κ) (dim κ) (l.map Int.cast) := by
  rw [re_eq]
  refine bsum_congr fun i hi ↦ ?_
  rw [getD_map_of_eq (z := (0 : ℤ)) Int.cast_zero, getD_map_of_eq (z := (0 : ℤ)) Int.cast_zero,
    coords_ofCoords l i hi]

end ExactBasis

/-! ### Instances -/

/-- The centred-form bound of one numeral, with natural-number arithmetic (`DPoly.penalty`). -/
def intLower (n : ℕ) (sh : List ℕ) (B : ℕ) (Ns : List ℕ) : ℤ × Bool :=
  (((Ns.headD 0 % 2 ^ B - 2 ^ (B - 1) : ℕ) : ℤ) -
    DPoly.penalty (2 ^ (B - 1)) (2 ^ B) (DPoly.layout B n sh) false (Ns.headD 0), true)

theorem intLower_le (n : ℕ) (sh : List ℕ) (B : ℕ) (Ns : List ℕ) (y : Fin n → ℝ) (hB : 0 < B)
    (hy : ∀ i, |y i| ≤ 1) :
    ((intLower n sh B Ns).1 : ℝ) ≤ DPoly.eval n (DPoly.unpack n sh B (Ns.headD 0)) y := by
  have h := DPoly.lower_le n true true (DPoly.unpack n sh B (Ns.headD 0)) y 1 hy (fun _ ↦ rfl)
    (fun _ ↦ zero_le_one) (by simp)
  rw [one_mul, DPoly.lower_unpack hB n sh true true _ fun _ ↦ rfl] at h
  simpa [intLower] using h

/-- One coordinate. -/
instance : ExactBasis ℤ where
  dim := 1
  basisE _ := Erased.mk 1
  coords a := [a]
  ofCoords l := l.headD 0
  mulG k a b := [a.headD (k 0) * b.headD (k 0)]
  lowerOf := intLower
  apxK := 0
  apx := [(1, 0)]
  mulG_natural f hf k a b := by
    cases a <;> cases b <;> simp [hf.map_mul]
  bsum_mulG' a b := by
    cases a <;> cases b <;> simp [bsum]
  re_eq' a := by
    change Exact.re a = _
    simp [bsum]
  coords_add _ _ := rfl
  coords_sub _ _ := rfl
  coords_mul _ _ := rfl
  coords_ofInt c := by simp [Exact.ofInt]
  coords_ofCoords l i hi := by
    obtain rfl : i = 0 := by omega
    cases l <;> rfl
  lowerOf_le' n sh B Ns y hB _ hy _ := by
    have := intLower_le n sh B Ns y hB hy
    change Exact.re _ ≤ _
    cases Ns <;> simpa using this
  apx_sound' j hj := by
    obtain rfl : j = 0 := by omega
    simp

namespace ZSqrt

variable {d : ℕ}

/-- The product of coordinate lists `[a, b]` of `a + b √d` (with the signature of
`ExactBasis.mulG`, whose subtraction it does not need). -/
@[nolint unusedArguments]
def mulG {γ : Type} [Add γ] [Sub γ] [Mul γ] (d : ℕ) (k : ℤ → γ) (x y : List γ) : List γ :=
  [x.getD 0 (k 0) * y.getD 0 (k 0) + k d * (x.getD 1 (k 0) * y.getD 1 (k 0)),
    x.getD 0 (k 0) * y.getD 1 (k 0) + x.getD 1 (k 0) * y.getD 0 (k 0)]

/-- The basis `1, √d`. -/
noncomputable def basisVal (d : ℕ) (i : ℕ) : ℝ :=
  if i = 0 then 1 else √(d : ℝ)

theorem bsum_two (d : ℕ) (l : List ℝ) :
    bsum (basisVal d) 2 l = l.getD 0 0 + √(d : ℝ) * l.getD 1 0 := by
  simp [bsum, sum_range_succ, basisVal]

/-- The value with coordinates `[a, b]`. -/
def ofCoords (l : List ℤ) : ZSqrt d := ⟨l.getD 0 0, l.getD 1 0⟩

theorem re_ofCoords (l : List ℤ) :
    Exact.re (ofCoords l : ZSqrt d) = ∑ j ∈ range 2, basisVal d j * (l.getD j 0 : ℝ) := by
  simp [ofCoords, sum_range_succ, basisVal, mul_comm]

/-- `⌊2^64 √d⌋` approximates `2^64 √d` within `1`. -/
theorem apx_sqrt (d : ℕ) : |(2 : ℝ) ^ 64 * √(d : ℝ) - (Nat.sqrt (d * 2 ^ 128) : ℝ)| ≤ 1 := by
  set s := Nat.sqrt (d * 2 ^ 128)
  set r := (2 : ℝ) ^ 64 * √(d : ℝ)
  have hr0 : 0 ≤ r := by positivity
  have hr2 : r ^ 2 = ((d * 2 ^ 128 : ℕ) : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    push_cast
    ring
  have h₁ : (s : ℝ) ^ 2 ≤ r ^ 2 := by rw [hr2]; exact_mod_cast Nat.sqrt_le' _
  have h₂ : r ^ 2 < ((s : ℝ) + 1) ^ 2 := by rw [hr2]; exact_mod_cast Nat.lt_succ_sqrt' _
  have h₃ : (s : ℝ) ≤ r := le_of_pow_le_pow_left₀ two_ne_zero hr0 h₁
  have h₄ : r < s + 1 := lt_of_pow_lt_pow_left₀ 2 (by positivity) h₂
  rw [abs_le]
  constructor <;> linarith

/-- Two coordinates: `a + b √d` is `[a, b]`; bounds are read in lockstep (`readK`). -/
instance : ExactBasis (ZSqrt d) where
  dim := 2
  basisE i := Erased.mk (basisVal d i)
  coords x := [x.a, x.b]
  ofCoords := ofCoords
  mulG := mulG d
  lowerOf n sh B Ns := readK ofCoords (2 ^ (B - 1)) (2 ^ B) (DPoly.layout B n sh) true true Ns
  apxK := 64
  apx := [(2 ^ 64, 0), ((Nat.sqrt (d * 2 ^ 128) : ℕ), 1)]
  mulG_natural f hf k x y := by
    have h : ∀ (l : List _) (i : ℕ), (l.map f).getD i (f (k 0)) = f (l.getD i (k 0)) :=
      fun l i ↦ List.getD_map (l := l) (n := i) (d := k 0) f
    simp only [mulG, List.map_cons, List.map_nil, Function.comp, h, hf.map_add, hf.map_mul]
  bsum_mulG' x y := by
    simp only [Erased.out_mk, bsum_two, mulG, List.getD_cons_zero, List.getD_cons_succ,
      Int.cast_natCast, Int.cast_zero]
    linear_combination (-(x.getD 1 0) * y.getD 1 0) * (sqrt_facts d).2
  re_eq' x := by
    change Exact.re x = _
    simp [bsum_two, re_eq, re, mul_comm]
  coords_add _ _ := rfl
  coords_sub _ _ := rfl
  coords_mul _ _ := rfl
  coords_ofInt c := by simp [Exact.ofInt]
  coords_ofCoords l i hi := by
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> rfl
  lowerOf_le' n sh B Ns y hB hl hy h := by
    change Exact.re _ ≤ _
    simpa using readK_le ofCoords (basisVal d) 2 (fun l _ ↦ re_ofCoords l) hB n sh true true Ns
      y 1 hl hy (fun _ ↦ rfl) (fun _ ↦ zero_le_one) (by simp) h
  apx_sound' j hj := by
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · norm_num [basisVal]
    · simpa [basisVal] using apx_sqrt d

theorem basis_eq : ExactBasis.basis (ZSqrt d) = basisVal d :=
  funext fun _ ↦ Erased.out_mk _

end ZSqrt

/-! ### Integer constants of the interpretations -/

instance : IntCast Expr := ⟨Expr.const⟩

instance : IntCast AbsNat := ⟨AbsNat.ofInt⟩

instance : IntCast ShapeL := ⟨fun _ ↦ ⟨[]⟩⟩

/-! ### The coordinate ring over `γ` -/

/-- Values of `κ` over `γ`: coordinate lists with entries in `γ`, with the operations of `κ`
(module docs). -/
structure Ext (κ : Type) (γ : Type) where
  /-- The coordinates. -/
  c : List γ

namespace Ext

section Ops

variable {κ γ : Type} [IntCast γ]

instance [Add γ] : Add (Ext κ γ) := ⟨fun a b ↦ ⟨zipD ((0 : ℤ) : γ) (· + ·) a.c b.c⟩⟩
instance [Sub γ] : Sub (Ext κ γ) := ⟨fun a b ↦ ⟨zipD ((0 : ℤ) : γ) (· - ·) a.c b.c⟩⟩
instance [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] [Add γ] [Sub γ] [Mul γ] : Mul (Ext κ γ) :=
  ⟨fun a b ↦ ⟨ExactBasis.mulG (κ := κ) Int.cast a.c b.c⟩⟩

theorem add_c [Add γ] (a b : Ext κ γ) : (a + b).c = zipD ((0 : ℤ) : γ) (· + ·) a.c b.c := rfl
theorem sub_c [Sub γ] (a b : Ext κ γ) : (a - b).c = zipD ((0 : ℤ) : γ) (· - ·) a.c b.c := rfl
theorem mul_c [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] [Add γ] [Sub γ] [Mul γ] (a b : Ext κ γ) :
    (a * b).c = ExactBasis.mulG (κ := κ) Int.cast a.c b.c := rfl

end Ops

/-- Applies `f` to every coordinate. -/
def map {κ γ δ : Type} (f : γ → δ) (a : Ext κ γ) : Ext κ δ := ⟨a.c.map f⟩

theorem map_c {κ γ δ : Type} (f : γ → δ) (a : Ext κ γ) : (a.map f).c = a.c.map f := rfl

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The input `x`: `x` times the coordinates of `1`. -/
def var {γ : Type} [IntCast γ] [Mul γ] (x : γ) : Ext κ γ :=
  ⟨(ExactBasis.coords (Exact.ofInt 1 : κ)).map fun e : ℤ ↦ (e : γ) * x⟩

/-- The constant `a`: its coordinates. -/
def const {γ : Type} [IntCast γ] (a : κ) : Ext κ γ := ⟨(ExactBasis.coords a).map Int.cast⟩

theorem map_var {γ δ : Type} [IntCast γ] [Mul γ] [IntCast δ] [Mul δ] {f : γ → δ}
    (hf : ∀ a b, f (a * b) = f a * f b) (hk : ∀ n : ℤ, f n = n) (x : γ) :
    map f (var x : Ext κ γ) = var (f x) := by
  simp only [map, var, List.map_map]
  congr 2
  funext e
  simp [hf, hk]

/-- **Naturality**: a map that commutes with the operations and the integer constants does so
coordinatewise. -/
theorem isArith_map {γ δ : Type} [Add γ] [Sub γ] [Mul γ] [IntCast γ] [Add δ] [Sub δ] [Mul δ]
    [IntCast δ] {f : γ → δ} (hf : IsArith f) (hk : ∀ n : ℤ, f n = n) :
    IsArith (map f : Ext κ γ → Ext κ δ) where
  map_add a b := by
    simp only [map, add_c, map_zipD hf.map_add, hk]
    rfl
  map_sub a b := by
    simp only [map, sub_c, map_zipD hf.map_sub, hk]
    rfl
  map_mul a b := by
    have hk' : f ∘ (Int.cast : ℤ → γ) = Int.cast := funext hk
    simp only [map, mul_c, ExactBasis.mulG_natural f hf, hk']
    rfl

theorem map_const {γ δ : Type} [IntCast γ] [IntCast δ] {f : γ → δ} (hk : ∀ n : ℤ, f n = n)
    (a : κ) : map f (const a : Ext κ γ) = const a := by
  simp only [map, const, List.map_map]
  congr 2
  funext n
  exact hk n

/-- The real value `∑ᵢ βᵢ cᵢ`. -/
noncomputable def re (a : Ext κ ℝ) : ℝ := bsum (ExactBasis.basis κ) (ExactBasis.dim κ) a.c

theorem isArith_re : IsArith (re : Ext κ ℝ → ℝ) where
  map_add a b := by simp only [re, add_c, Int.cast_zero, bsum_zipD_add]
  map_sub a b := by simp only [re, sub_c, Int.cast_zero, bsum_zipD_sub]
  map_mul a b := by simp only [re, mul_c, ExactBasis.bsum_mulG]

theorem re_const (a : κ) : re (const a : Ext κ ℝ) = Exact.re a := by
  rw [re, const, ExactBasis.re_eq]

theorem re_var (x : ℝ) : re (var x : Ext κ ℝ) = x := by
  rw [re, var, bsum_map_mul, ← ExactBasis.re_eq, Exact.re_ofInt, Int.cast_one, one_mul]

/-- The coordinates of an exact value. -/
def ofExact (a : κ) : Ext κ ℤ := ⟨ExactBasis.coords a⟩

theorem isArith_ofExact : IsArith (ofExact : κ → Ext κ ℤ) where
  map_add a b := by
    simp only [ofExact]
    rw [ExactBasis.coords_add]
    rfl
  map_sub a b := by
    simp only [ofExact]
    rw [ExactBasis.coords_sub]
    rfl
  map_mul a b := by
    simp only [ofExact]
    rw [ExactBasis.coords_mul]
    rfl

theorem ofExact_eq_const (a : κ) : ofExact a = (const a : Ext κ ℤ) := by
  rw [ofExact, const, show (Int.cast : ℤ → ℤ) = id from rfl, List.map_id]

theorem ofExact_ofInt (c : ℤ) : ofExact (Exact.ofInt c : κ) = var c := by
  rw [ofExact, var, ExactBasis.coords_ofInt]
  rfl

/-- Coordinate `j` of coordinate expressions. -/
def coord {κ : Type} (a : Ext κ Expr) (j : ℕ) : Expr := a.c.getD j (.const 0)

/-- The real value of coordinate expressions at `x`, as a sum over the coordinates. -/
theorem re_map_eval (a : Ext κ Expr) (x : ℕ → ℝ) :
    re (a.map (Expr.eval x)) =
      ∑ j ∈ range (ExactBasis.dim κ), ExactBasis.basis κ j * (a.coord j).eval x := by
  rw [re, bsum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [map_c, getD_map_of_eq (z := Expr.const 0) (by simp), coord]

omit [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] in
theorem evalInt_coord (a : Ext κ Expr) (x : List ℤ) (j : ℕ) :
    (a.coord j).evalInt x = (a.c.map (Expr.evalInt x)).getD j 0 := by
  rw [getD_map_of_eq (f := Expr.evalInt x) (z := Expr.const 0) (z' := 0) rfl, coord]

end Ext

/-! ### Generic computations -/

/-- `a[i]` where `a` has an entry `i`, else `f i`: values of `f` computed in advance, as data
(`look_eq`). Compiled code computes an argument once, but recomputes a value bound outside a
function that a definition returns at every call (the compiler moves such bindings inside), so
values used repeatedly are passed around as arrays and read with `look`. -/
def look {α : Type*} (a : Array α) (f : ℕ → α) (i : ℕ) : α :=
  if h : i < a.size then a[i] else f i

theorem look_eq {α : Type*} {a : Array α} {f : ℕ → α} (h : ∀ i (hi : i < a.size), a[i] = f i) :
    look a f = f := by
  funext i
  unfold look
  split
  · exact h _ _
  · rfl

theorem look_ofFn {α : Type*} (m : ℕ) (f : ℕ → α) : look (Array.ofFn (n := m) fun i ↦ f i) f = f :=
  look_eq fun _ _ ↦ Array.getElem_ofFn ..

/-- `f` at `0, …, m - 1`, each computed when first read and then kept (`lookT`). -/
def thunks {α : Type*} (m : ℕ) (f : ℕ → α) : Array (Thunk α) :=
  Array.ofFn (n := m) fun i ↦ Thunk.mk fun _ ↦ f i

/-- `a[i].get` where `a` has an entry `i`, else `f i` (`lookT_thunks`). -/
def lookT {α : Type*} (a : Array (Thunk α)) (f : ℕ → α) (i : ℕ) : α :=
  if h : i < a.size then a[i].get else f i

theorem lookT_thunks {α : Type*} (m : ℕ) (f : ℕ → α) : lookT (thunks m f) f = f := by
  funext i
  unfold lookT thunks
  split
  · simp only [Array.getElem_ofFn]
    rfl
  · rfl

/-- A polynomial computation with constants in `κ`, in any type with `+`, `-` and `*`: from the
inputs `x i` and constants embedded by `k`, natural in maps that commute with the operations.
Witness polynomials, and their pullbacks along exact maps, are of this kind. -/
structure GenPoly (κ : Type) where
  /-- The computation. -/
  run : {α : Type} → [Add α] → [Sub α] → [Mul α] → (κ → α) → (ℕ → α) → α
  /-- Naturality. -/
  natural : ∀ {α β : Type} [Add α] [Sub α] [Mul α] [Add β] [Sub β] [Mul β] (f : α → β),
    IsArith f → ∀ (k : κ → α) (x : ℕ → α), f (run k x) = run (f ∘ k) (f ∘ x)

namespace GenPoly

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The computation as polynomials in the inputs `0, 1, …`, one per coordinate. -/
def ext (G : GenPoly κ) : Ext κ Expr := G.run Ext.const fun i ↦ Ext.var (.var i)

/-- Coordinate `j` of `G.ext`. -/
def coord (G : GenPoly κ) (j : ℕ) : Expr := G.ext.coord j

/-- The computation over `γ`, with inputs `x`: the image of `G.ext`. -/
theorem run_ext {γ : Type} [Add γ] [Sub γ] [Mul γ] [IntCast γ] (G : GenPoly κ) {f : Expr → γ}
    (hf : IsArith f) (hk : ∀ n : ℤ, f n = n) :
    G.ext.map f = G.run Ext.const fun i ↦ Ext.var (f (.var i)) := by
  rw [ext, G.natural _ (Ext.isArith_map hf hk)]
  congr 1
  · funext a
    exact Ext.map_const hk a
  · funext i
    exact Ext.map_var hf.map_mul hk _

/-- **The real value** of the computation is the value of its coordinate polynomials. -/
theorem run_re (G : GenPoly κ) (x : ℕ → ℝ) :
    G.run Exact.re x = Ext.re (G.ext.map (Expr.eval x)) := by
  rw [G.run_ext (Expr.isArith_eval x) fun _ ↦ rfl, G.natural _ Ext.isArith_re]
  congr 1
  · funext a
    exact (Ext.re_const a).symm
  · funext i
    exact (Ext.re_var (x i)).symm

/-- The real value as a sum over the coordinates. -/
theorem run_re_eq_sum (G : GenPoly κ) (x : ℕ → ℝ) :
    G.run Exact.re x =
      ∑ j ∈ range (ExactBasis.dim κ), ExactBasis.basis κ j * (G.coord j).eval x := by
  rw [run_re, Ext.re_map_eval]
  rfl

/-- **Values in `κ`**: the coordinates of the computation at integer inputs are the values of its
coordinate polynomials. -/
theorem coords_run (G : GenPoly κ) (x : List ℤ) :
    ExactBasis.coords (G.run id fun i ↦ (Exact.ofInt (x.getD i 0) : κ)) =
      G.ext.c.map (Expr.evalInt x) := by
  have h := G.natural _ Ext.isArith_ofExact id fun i ↦ (Exact.ofInt (x.getD i 0) : κ)
  have h' := G.run_ext (Expr.isArith_evalInt x) fun _ ↦ rfl
  rw [← Ext.map_c, h']
  change (Ext.ofExact _).c = _
  rw [h]
  congr 2
  · funext a
    exact Ext.ofExact_eq_const a
  · funext i
    exact Ext.ofExact_ofInt _

/-- Coordinate `j` of the value at integer inputs. -/
theorem getD_coords_run (G : GenPoly κ) (x : List ℤ) (j : ℕ) :
    (ExactBasis.coords (G.run id fun i ↦ (Exact.ofInt (x.getD i 0) : κ))).getD j 0 =
      (G.coord j).evalInt x := by
  rw [coords_run, coord, Ext.evalInt_coord]

/-- The norm bounds of the coordinate polynomials, by a run in `AbsNat`. -/
theorem norms_run (G : GenPoly κ) (b : List ℕ) :
    (G.run Ext.const fun i ↦ Ext.var ⟨b.getD i 0⟩ : Ext κ AbsNat).c =
      G.ext.c.map fun e ↦ ⟨e.normBound b⟩ := by
  rw [← Ext.map_c, G.run_ext (Expr.isArith_normBound b) fun _ ↦ rfl]
  rfl

/-- The shapes of the coordinate polynomials, by a run in `ShapeL`. -/
theorem shapes_run (G : GenPoly κ) (s : List (List ℕ)) :
    (G.run Ext.const fun i ↦ Ext.var ⟨s.getD i []⟩ : Ext κ ShapeL).c =
      G.ext.c.map fun e ↦ ⟨e.shape s⟩ := by
  rw [← Ext.map_c, G.run_ext (Expr.isArith_shape s) fun _ ↦ rfl]
  rfl

end GenPoly

end Nieuwland.Check
