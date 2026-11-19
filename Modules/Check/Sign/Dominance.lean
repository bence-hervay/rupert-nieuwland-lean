import Modules.Check.Number.Ext
import Modules.Check.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.List.Sort

/-!
# Dominance bounds on the unit cube

On `[0, 1]^n` every monomial `y^α` lies in `[0, 1]` and decreases when its exponents grow. So a
polynomial `∑ c_α y^α` is at least `s₀ + ∑_β min(0, s_β)` when its terms are distributed into
*buckets* `y^β`: a term `c y^α` goes to a bucket whose monomial divides `y^α`, all of `c` if
`β = α` and its negative part otherwise (`min(0, c) y^β ≤ c y^α`), or its negative part to the
constant `s₀` (all of `c` if `α = 0`). The bound holds for every distribution (`pass_le`). The
two distributions of the Rust check (`code/src/math/smallpoly.rs`) are

* *vertex dominance* (`vertex_dominance_on_unit_cube`, `vertBound`): the buckets are the
  variables `yᵢ`; the linear terms go to their own buckets, then every other term to the bucket of
  largest sum among the variables of its support, the first on ties;
* *monomial dominance* (`monomial_dominance_on_unit_cube`, `monoBound`): the buckets are the
  positive terms; every other term goes to the dividing bucket of largest sum, the last on ties,
  the terms with fewest dividing buckets and most negative coefficients first.

At a vertex of a box where a polynomial vanishes but grows into the box, no subdivision makes the
centred form certify its sign, while dominance does once the box is small enough; monomial
dominance also where the linear terms vanish but a positive product term dominates.

Monomials are numbers, exponent `i` in bits `[16 i, 16 i + 16)` (`packExp`, read back by `pexp`
in proofs), so that the kernel tests divisibility with a few operations on numbers (`divP`). The
choices of buckets need no correctness: they use approximate sums, for vertex dominance in
numerals with a slot per variable, for monomial dominance in an array indexed by bucket. The bound
is made by an exact pass (`pass`), with exact divisibility and signs.
Coefficients lie in an exact type `κ` (`Modules/Check/Number/Ext.lean`); negative parts need the sign of
a coefficient, so every bound comes with whether all the signs it needed were decided.

* `monosK`: the nonzero monomials of a polynomial whose coordinates are packed in numerals, read in
  lockstep as `readK` reads the centred form (`monoSumK_monosK`); `monosP` reads them with packed
  monomials (`monosP_eq`).
* `domOf`: the better of the two bounds, read off packed coordinates (`domOf_le`).
-/

open Finset

namespace Nieuwland.Check

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-! ### Monomial lists -/

/-- The value `∑ c x^α` of a monomial list. -/
noncomputable def monoSumK (n : ℕ) (ms : List (List ℕ × κ)) (x : Fin n → ℝ) : ℝ :=
  (ms.map fun m ↦ Exact.re m.2 * DPoly.monoVal n m.1 x).sum

/-- The monomials of the polynomial whose coordinates are packed in the numerals `Ns`, in `B`-bit
digits biased by `h = 2^(B-1)` (`P₀ = 2^B`) in the layout `ls`: exponent lists with the
coefficients their digits form, lexicographically with `x₀` first, the zero ones left out. -/
def monosK (h P₀ : ℕ) : List (ℕ × ℕ) → List ℕ → List (List ℕ × κ)
  | [], Ns =>
    bif (Ns.map fun N ↦ Int.subNatNat (Nat.mod N P₀) h).all (· == 0) then []
    else [([], ExactBasis.ofCoords (Ns.map fun N ↦ Int.subNatNat (Nat.mod N P₀) h))]
  | (m, P) :: ls, Ns => monosKL (monosK h P₀ ls) P 0 m Ns
where
  /-- The monomials of `m` blocks of modulus `P` of each numeral, the first of exponent `k`, each
  read by `f`. -/
  monosKL (f : List ℕ → List (List ℕ × κ)) (P : ℕ) : ℕ → ℕ → List ℕ → List (List ℕ × κ)
    | _, 0, _ => []
    | k, m + 1, Ns => (f (Ns.map fun N ↦ Nat.mod N P)).map (fun mo ↦ (k :: mo.1, mo.2)) ++
        monosKL f P (k + 1) m (Ns.map fun N ↦ Nat.div N P)

/-- **The monomials of packed coordinates**: their sum is the polynomial `∑ⱼ βⱼ Tⱼ` of the
unpacked numerals `Tⱼ`. -/
theorem monoSumK_monosK {B : ℕ} : ∀ (n : ℕ) (e : List ℕ) (Ns : List ℕ) (y : Fin n → ℝ),
    ExactBasis.dim κ ≤ Ns.length →
    monoSumK n (monosK (κ := κ) (2 ^ (B - 1)) (2 ^ B) (DPoly.layout B n e) Ns) y =
      ∑ j ∈ range (ExactBasis.dim κ),
        ExactBasis.basis κ j * DPoly.eval n (DPoly.unpack n e B (Ns.getD j 0)) y
  | 0, e, Ns, y, hlen => by
    have hd : ∀ j ∈ range (ExactBasis.dim κ),
        DPoly.eval 0 (DPoly.unpack 0 e B (Ns.getD j 0)) y =
          (((Ns.map fun N ↦ Int.subNatNat (Nat.mod N (2 ^ B)) (2 ^ (B - 1))).getD j 0 : ℤ) :
            ℝ) := by
      intro j hj
      have hj' : j < Ns.length := lt_of_lt_of_le (mem_range.mp hj) hlen
      rw [getD_map_of_lt _ 0 _ hj', DPoly.unpack, DPoly.eval_ofInt, Int.subNatNat_eq_coe]
      push_cast
      rfl
    rw [sum_congr rfl fun j hj ↦ by rw [hd j hj]]
    simp only [DPoly.layout, monosK]
    cases hz : (Ns.map fun N ↦ Int.subNatNat (Nat.mod N (2 ^ B)) (2 ^ (B - 1))).all (· == 0)
    · simp only [Bool.cond_false, monoSumK, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero, DPoly.monoVal, mul_one, ExactBasis.re_ofCoords, bsum]
      refine sum_congr rfl fun j _ ↦ ?_
      rw [getD_map_of_eq (z := (0 : ℤ)) Int.cast_zero]
    · simp only [Bool.cond_true, monoSumK, List.map_nil, List.sum_nil]
      refine (sum_eq_zero fun j hj ↦ ?_).symm
      have hj' : j < (Ns.map fun N ↦ Int.subNatNat (Nat.mod N (2 ^ B)) (2 ^ (B - 1))).length := by
        simpa using lt_of_lt_of_le (mem_range.mp hj) hlen
      have h0 := List.all_eq_true.mp hz _ (List.getElem_mem hj')
      rw [List.getD_eq_getElem _ _ hj', beq_iff_eq.mp h0]
      simp
  | n + 1, e, Ns, y, hlen => by
    set w := B * DPoly.slots e.tail
    set f := monosK (κ := κ) (2 ^ (B - 1)) (2 ^ B) (DPoly.layout B n e.tail)
    have key : ∀ (M k : ℕ) (Ns : List ℕ), ExactBasis.dim κ ≤ Ns.length →
        monoSumK (n + 1) (monosK.monosKL f (2 ^ w) k M Ns) y =
          y 0 ^ k * ∑ j ∈ range (ExactBasis.dim κ), ExactBasis.basis κ j *
            horner (fun q ↦ DPoly.eval n q (Fin.tail y)) (y 0)
              (DPoly.unpackL (DPoly.unpack n e.tail B) w M (Ns.getD j 0)) := by
      intro M
      induction M with
      | zero => intro k Ns _; simp [monosK.monosKL, monoSumK, DPoly.unpackL]
      | succ M ih =>
        intro k Ns hl
        have ha := monoSumK_monosK (B := B) n e.tail (Ns.map fun N ↦ Nat.mod N (2 ^ w)) (Fin.tail y)
          (by simpa using hl)
        have hb := ih (k + 1) (Ns.map fun N ↦ Nat.div N (2 ^ w)) (by simpa using hl)
        have hmod : ∀ j, (Ns.map fun N ↦ Nat.mod N (2 ^ w)).getD j 0 = Ns.getD j 0 % 2 ^ w :=
          fun j ↦ getD_map_of_eq (f := fun N ↦ Nat.mod N (2 ^ w)) (z := 0) (Nat.zero_mod _) Ns j
        have hdiv : ∀ j, (Ns.map fun N ↦ Nat.div N (2 ^ w)).getD j 0 = Ns.getD j 0 / 2 ^ w :=
          fun j ↦ getD_map_of_eq (f := fun N ↦ Nat.div N (2 ^ w)) (z := 0) (Nat.zero_div _) Ns j
        simp only [hmod] at ha
        simp only [hdiv] at hb
        have hmap : monoSumK (n + 1) ((f (Ns.map fun N ↦ Nat.mod N (2 ^ w))).map
            (fun mo ↦ (k :: mo.1, mo.2))) y =
            y 0 ^ k * monoSumK n (f (Ns.map fun N ↦ Nat.mod N (2 ^ w))) (Fin.tail y) := by
          simp only [monoSumK, List.map_map, Function.comp_def, DPoly.monoVal, List.headD_cons,
            List.tail_cons, ← List.sum_map_mul_left]
          congr 1
          exact List.map_congr_left fun m _ ↦ by ring
        rw [monosK.monosKL, monoSumK, List.map_append, List.sum_append, ← monoSumK, ← monoSumK,
          hmap, hb, ha]
        simp only [DPoly.unpackL, horner_cons, mul_add, sum_add_distrib, mul_sum, pow_succ]
        congr 1
        exact sum_congr rfl fun _ _ ↦ by ring
    simp only [DPoly.layout_succ, monosK]
    rw [key _ 0 Ns hlen, pow_zero, one_mul]
    rfl


theorem monosK_lt (h P₀ M : ℕ) : ∀ (ls : List (ℕ × ℕ)) (Ns : List ℕ), (∀ l ∈ ls, l.1 ≤ M) →
    ∀ t ∈ monosK (κ := κ) h P₀ ls Ns, ∀ a ∈ t.1, a < M
  | [], Ns, _, t, ht, a, ha => by
    simp only [monosK] at ht
    cases (Ns.map fun N ↦ Int.subNatNat (Nat.mod N P₀) h).all (· == 0) <;>
      simp at ht <;> simp [ht] at ha
  | (m, P) :: ls, Ns, hls, t, ht, a, ha => by
    have key : ∀ (m k : ℕ) (Ns : List ℕ), k + m ≤ M →
        ∀ t ∈ monosK.monosKL (κ := κ) (monosK h P₀ ls) P k m Ns, ∀ a ∈ t.1, a < M := by
      intro m
      induction m with
      | zero => intro k Ns _ t ht; simp [monosK.monosKL] at ht
      | succ m ih =>
        intro k Ns hk t ht a ha
        simp only [monosK.monosKL, List.mem_append, List.mem_map] at ht
        rcases ht with ⟨mo, hmo, rfl⟩ | ht
        · rcases List.mem_cons.mp ha with rfl | ha
          · omega
          · exact monosK_lt h P₀ M ls _ (fun l hl ↦ hls l (List.mem_cons_of_mem _ hl)) mo hmo a ha
        · exact ih (k + 1) _ (by omega) t ht a ha
    simp only [monosK] at ht
    exact key m 0 Ns (by simpa using hls (m, P) List.mem_cons_self) t ht a ha

/-! ### Packed monomials

A monomial `y^α` with exponents below `2^16` is the number `packExp α = ∑ᵢ αᵢ 2^(16 i)`, read back
by `pexp` in proofs; terms `(a, c)` are coefficients `c` with packed monomials `a`. -/

/-- An exponent list packed, exponent `i` in bits `[16 i, 16 i + 16)`. -/
def packExp (α : List ℕ) : ℕ := α.foldr (fun a k ↦ a + k * 2 ^ 16) 0

/-- The first `n` exponents of a packed monomial (in proofs). -/
def pexp : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, a => a % 2 ^ 16 :: pexp n (a / 2 ^ 16)

/-- The value `∑ c y^α` of terms `(a, c)` with packed monomials `a`. -/
noncomputable def psum (n : ℕ) (L : List (ℕ × κ)) (y : Fin n → ℝ) : ℝ :=
  (L.map fun t ↦ Exact.re t.2 * DPoly.monoVal n (pexp n t.1) y).sum

theorem pexp_succ_add {n a : ℕ} (b : ℕ) (ha : a < 2 ^ 16) :
    pexp (n + 1) (a + b * 2 ^ 16) = a :: pexp n b := by
  rw [pexp, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha,
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos 16), Nat.div_eq_of_lt ha, Nat.zero_add]

theorem monoVal_pexp_packExp {n : ℕ} {y : Fin n → ℝ} {α : List ℕ} (hα : ∀ a ∈ α, a < 2 ^ 16) :
    DPoly.monoVal n (pexp n (packExp α)) y = DPoly.monoVal n α y := by
  induction n generalizing α with
  | zero => rfl
  | succ n ih =>
    cases α with
    | nil =>
      have := ih (y := Fin.tail y) (α := []) (by simp)
      simp only [packExp, List.foldr_nil] at this ⊢
      simp [pexp, DPoly.monoVal, this]
    | cons a α =>
      rw [show packExp (a :: α) = a + packExp α * 2 ^ 16 from rfl,
        pexp_succ_add _ (hα a List.mem_cons_self), DPoly.monoVal, DPoly.monoVal,
        List.headD_cons, List.tail_cons, List.headD_cons, List.tail_cons,
        ih fun x hx ↦ hα x (List.mem_cons_of_mem _ hx)]

theorem psum_map_packExp {n : ℕ} {y : Fin n → ℝ} (L : List (List ℕ × κ))
    (hL : ∀ m ∈ L, ∀ a ∈ m.1, a < 2 ^ 16) :
    psum n (L.map fun m ↦ (packExp m.1, m.2)) y = monoSumK n L y := by
  simp only [psum, monoSumK, List.map_map]
  congr 1
  exact List.map_congr_left fun m hm ↦ by
    simp only [Function.comp_apply, monoVal_pexp_packExp (hL m hm)]

/-- The monomials of `monosK` with packed monomials (`monosP_eq`), before `acc`: exponent `i` at
scale `s 2^(16 i)` over the prefix `p`. -/
def monosP (h P₀ : ℕ) : List (ℕ × ℕ) → ℕ → ℕ → List ℕ → List (ℕ × κ) → List (ℕ × κ)
  | [], _, p, Ns, acc =>
    bif Ns.all fun N ↦ Nat.beq (Nat.mod N P₀) h then acc
    else (p, ExactBasis.ofCoords (Ns.map fun N ↦ Int.subNatNat (Nat.mod N P₀) h)) :: acc
  | (m, P) :: ls, s, p, Ns, acc => monosPL (monosP h P₀ ls (Nat.mul s 65536)) P s m p Ns acc
where
  /-- The monomials of `m` blocks of modulus `P` of each numeral, the first over the prefix `p`
  and the next ones `s` further, each read by `f`, before `acc`. -/
  monosPL (f : ℕ → List ℕ → List (ℕ × κ) → List (ℕ × κ)) (P s : ℕ) :
      ℕ → ℕ → List ℕ → List (ℕ × κ) → List (ℕ × κ)
    | 0, _, _, acc => acc
    | m + 1, p, Ns, acc => f p (Ns.map fun N ↦ Nat.mod N P)
        (monosPL f P s m (Nat.add p s) (Ns.map fun N ↦ Nat.div N P) acc)

/-- `monosP` with shifts and masks where the block moduli are powers of two (`DPoly.divP2`,
`DPoly.modP2`). -/
def monosPS (h P₀ : ℕ) : List (ℕ × ℕ) → ℕ → ℕ → List ℕ → List (ℕ × κ) → List (ℕ × κ)
  | [], _, p, Ns, acc =>
    bif Ns.all fun N ↦ Nat.beq (Nat.mod N P₀) h then acc
    else (p, ExactBasis.ofCoords (Ns.map fun N ↦ Int.subNatNat (Nat.mod N P₀) h)) :: acc
  | (m, P) :: ls, s, p, Ns, acc => monosPLS (monosPS h P₀ ls (Nat.mul s 65536)) P s m p Ns acc
where
  /-- `monosP.monosPL` with shifts and masks. -/
  monosPLS (f : ℕ → List ℕ → List (ℕ × κ) → List (ℕ × κ)) (P s : ℕ) :
      ℕ → ℕ → List ℕ → List (ℕ × κ) → List (ℕ × κ)
    | 0, _, _, acc => acc
    | m + 1, p, Ns, acc => f p (Ns.map fun N ↦ DPoly.modP2 N P)
        (monosPLS f P s m (Nat.add p s) (Ns.map fun N ↦ DPoly.divP2 N P) acc)

private theorem nat_div' (a b : ℕ) : Nat.div a b = a / b := rfl
private theorem nat_mod' (a b : ℕ) : Nat.mod a b = a % b := rfl

omit [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] in
theorem monosPL_eq_monosPLS (f : ℕ → List ℕ → List (ℕ × κ) → List (ℕ × κ)) (P s : ℕ) :
    ∀ m p Ns acc, monosP.monosPL f P s m p Ns acc = monosPS.monosPLS f P s m p Ns acc
  | 0, _, _, _ => rfl
  | m + 1, p, Ns, acc => by
    simp only [monosP.monosPL, monosPS.monosPLS, DPoly.divP2_eq, DPoly.modP2_eq, nat_div',
      nat_mod', monosPL_eq_monosPLS f P s m]

@[csimp] theorem monosP_eq_monosPS : @monosP = @monosPS := by
  funext κ _ _ _ _ h P₀ ls
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    funext s p Ns acc
    obtain ⟨m, P⟩ := l
    simp only [monosP, monosPS, monosPL_eq_monosPLS, ih]

theorem all_beq_eq (h P₀ : ℕ) (Ns : List ℕ) :
    (Ns.map fun N ↦ Int.subNatNat (Nat.mod N P₀) h).all (· == 0) =
      Ns.all fun N ↦ Nat.beq (Nat.mod N P₀) h := by
  rw [List.all_map]
  congr 1
  funext N
  simp only [Function.comp_apply, Int.subNatNat_eq_coe]
  cases hb : Nat.beq (Nat.mod N P₀) h
  · have hne : Nat.mod N P₀ ≠ h := Nat.ne_of_beq_eq_false hb
    simp only [beq_eq_false_iff_ne, ne_eq]
    omega
  · rw [Nat.eq_of_beq_eq_true hb]
    simp

/-- **The packed monomials of packed coordinates** are those of `monosK`, packed. -/
theorem monosP_eq (h P₀ : ℕ) : ∀ (ls : List (ℕ × ℕ)) (s p : ℕ) (Ns : List ℕ)
    (acc : List (ℕ × κ)), monosP h P₀ ls s p Ns acc =
      (monosK h P₀ ls Ns).map (fun t ↦ (p + s * packExp t.1, t.2)) ++ acc
  | [], s, p, Ns, acc => by
    simp only [monosP, monosK, all_beq_eq]
    cases Ns.all fun N ↦ Nat.beq (Nat.mod N P₀) h <;> simp [packExp]
  | (m, P) :: ls, s, p, Ns, acc => by
    have key : ∀ (m k : ℕ) (Ns : List ℕ) (acc : List (ℕ × κ)),
        monosP.monosPL (monosP h P₀ ls (Nat.mul s 65536)) P s m (p + s * k) Ns acc =
          (monosK.monosKL (monosK h P₀ ls) P k m Ns).map
            (fun t ↦ (p + s * packExp t.1, t.2)) ++ acc := by
      intro m
      induction m with
      | zero => intro k Ns acc; rfl
      | succ m ih =>
        intro k Ns acc
        have e : Nat.add (p + s * k) s = p + s * (k + 1) := by
          change p + s * k + s = p + s * (k + 1)
          ring
        rw [monosP.monosPL, e, ih, monosP_eq h P₀ ls, monosK.monosKL, List.map_append,
          List.map_map, List.append_assoc]
        congr 1
        refine List.map_congr_left fun t _ ↦ Prod.ext ?_ rfl
        change p + s * k + s * 65536 * packExp t.1 = p + s * packExp (k :: t.1)
        rw [show packExp (k :: t.1) = k + packExp t.1 * 2 ^ 16 from rfl]
        ring
    simp only [monosP, monosK]
    have := key m 0 Ns acc
    rwa [Nat.mul_zero, Nat.add_zero] at this

theorem psum_monosP {n : ℕ} {y : Fin n → ℝ} (h P₀ : ℕ) (ls : List (ℕ × ℕ)) (Ns : List ℕ)
    (hls : ∀ l ∈ ls, l.1 ≤ 2 ^ 16) :
    psum n (monosP (κ := κ) h P₀ ls 1 0 Ns []) y = monoSumK n (monosK (κ := κ) h P₀ ls Ns) y := by
  rw [monosP_eq, List.append_nil]
  simp only [Nat.zero_add, Nat.one_mul]
  exact psum_map_packExp _ (monosK_lt h P₀ _ ls Ns hls)

/-- The number of leading entries of the shape `e` up to the last positive one. -/
def effLen : List ℕ → ℕ
  | [] => 0
  | a :: e => bif Nat.beq (effLen e) 0 && Nat.beq a 0 then 0 else Nat.add (effLen e) 1

/-- The first `n` variables up to the last of positive degree in the shape `sh`: the variables
after them only repeat the reduction of the digits (`monosP_trim`). -/
def nEff (n : ℕ) (sh : List ℕ) : ℕ := bif Nat.ble n (effLen sh) then n else effLen sh

theorem drop_effLen : ∀ (e : List ℕ), ∀ x ∈ e.drop (effLen e), x = 0
  | [], _, hx => by simp at hx
  | a :: e, x, hx => by
    have ih := drop_effLen e
    simp only [effLen] at hx
    cases hc : (Nat.beq (effLen e) 0 && Nat.beq a 0)
    · rw [hc, Bool.cond_false, Nat.add_eq, List.drop_succ_cons] at hx
      exact ih x hx
    · rw [hc, Bool.cond_true, List.drop_zero] at hx
      obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp hc
      rw [Nat.eq_of_beq_eq_true h₁, List.drop_zero] at ih
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Nat.eq_of_beq_eq_true h₂
      · exact ih x hx

theorem slots_of_zero : ∀ {e : List ℕ}, (∀ x ∈ e, x = 0) → DPoly.slots e = 1
  | [], _ => rfl
  | a :: e, h => by
    rw [DPoly.slots, h a List.mem_cons_self,
      slots_of_zero fun x hx ↦ h x (List.mem_cons_of_mem _ hx)]

theorem layout_of_zero (B : ℕ) : ∀ (k : ℕ) {e : List ℕ}, (∀ x ∈ e, x = 0) →
    DPoly.layout B k e = List.replicate k (1, 2 ^ B)
  | 0, _, _ => rfl
  | k + 1, e, h => by
    have ht : ∀ x ∈ e.tail, x = 0 := fun x hx ↦ h x (List.mem_of_mem_tail hx)
    have hh : e.headD 0 = 0 := by
      cases e with
      | nil => rfl
      | cons a e => exact h a List.mem_cons_self
    rw [DPoly.layout_succ, layout_of_zero B k ht, slots_of_zero ht, hh, List.replicate_succ,
      Nat.mul_one]

theorem layout_add (B : ℕ) : ∀ (a b : ℕ) (e : List ℕ),
    DPoly.layout B (a + b) e = DPoly.layout B a e ++ DPoly.layout B b (e.drop a)
  | 0, b, e => by simp [DPoly.layout]
  | a + 1, b, e => by
    rw [show a + 1 + b = (a + b) + 1 by omega, DPoly.layout_succ, DPoly.layout_succ,
      layout_add B a b e.tail, List.cons_append, List.drop_tail]

theorem layout_trim (B n : ℕ) (sh : List ℕ) : DPoly.layout B n sh =
    DPoly.layout B (nEff n sh) sh ++ List.replicate (n - nEff n sh) (1, 2 ^ B) := by
  unfold nEff
  cases hc : Nat.ble n (effLen sh)
  · rw [Bool.cond_false]
    have hlt : effLen sh < n := by
      by_contra hle
      rw [Nat.ble_eq_true_of_le (Nat.le_of_not_lt hle)] at hc
      cases hc
    conv_lhs => rw [show n = effLen sh + (n - effLen sh) by omega]
    rw [layout_add, layout_of_zero B _ (drop_effLen sh)]
  · rw [Bool.cond_true, Nat.sub_self, List.replicate_zero, List.append_nil]

theorem monosP_leaf (h P₀ s s' p : ℕ) (Ns : List ℕ) (acc : List (ℕ × κ)) :
    monosP h P₀ [] s p (Ns.map fun N ↦ Nat.mod N P₀) acc = monosP h P₀ [] s' p Ns acc := by
  have hm : ∀ N, Nat.mod (Nat.mod N P₀) P₀ = Nat.mod N P₀ := fun N ↦ Nat.mod_mod N P₀
  simp only [monosP, List.all_map, List.map_map, Function.comp_def, hm]

theorem monosP_ones (h P₀ k : ℕ) : ∀ (s p : ℕ) (Ns : List ℕ) (acc : List (ℕ × κ)),
    monosP h P₀ (List.replicate k (1, P₀)) s p Ns acc = monosP h P₀ [] s p Ns acc := by
  induction k with
  | zero => intro s p Ns acc; rfl
  | succ k ih =>
    intro s p Ns acc
    have e : monosP h P₀ ((1, P₀) :: List.replicate k (1, P₀)) s p Ns acc =
        monosP h P₀ (List.replicate k (1, P₀)) (Nat.mul s 65536) p
          (Ns.map fun N ↦ Nat.mod N P₀) acc := rfl
    rw [List.replicate_succ, e, ih, monosP_leaf h P₀ _ s]

/-- **Trailing constant variables**: they leave the packed monomials unchanged. -/
theorem monosP_trim (h P₀ k : ℕ) : ∀ (ls : List (ℕ × ℕ)) (s p : ℕ) (Ns : List ℕ)
    (acc : List (ℕ × κ)),
    monosP h P₀ (ls ++ List.replicate k (1, P₀)) s p Ns acc = monosP h P₀ ls s p Ns acc
  | [], s, p, Ns, acc => monosP_ones h P₀ k s p Ns acc
  | (m, P) :: ls, s, p, Ns, acc => by
    have e : monosP (κ := κ) h P₀ (ls ++ List.replicate k (1, P₀)) (Nat.mul s 65536) =
        monosP h P₀ ls (Nat.mul s 65536) := by
      funext p Ns acc
      exact monosP_trim h P₀ k ls _ p Ns acc
    rw [List.cons_append, monosP, monosP, e]

/-! ### Monomials on the unit cube -/

section Cube

variable {n : ℕ} {y : Fin n → ℝ}

theorem monoVal_mem_unit (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (α : List ℕ) :
    0 ≤ DPoly.monoVal n α y ∧ DPoly.monoVal n α y ≤ 1 := by
  induction n generalizing α with
  | zero => simp [DPoly.monoVal]
  | succ n ih =>
    obtain ⟨h₀, h₁⟩ := ih (y := Fin.tail y) (fun i ↦ hy i.succ) α.tail
    have hp₀ : 0 ≤ y 0 ^ α.headD 0 := pow_nonneg (hy 0).1 _
    have hp₁ : y 0 ^ α.headD 0 ≤ 1 := pow_le_one₀ (hy 0).1 (hy 0).2
    exact ⟨mul_nonneg hp₀ h₀, (mul_le_mul hp₁ h₁ h₀ zero_le_one).trans_eq (one_mul 1)⟩

theorem monoVal_of_sum_zero {α : List ℕ} (hα : α.sum = 0) : DPoly.monoVal n α y = 1 := by
  induction n generalizing α with
  | zero => rfl
  | succ n ih =>
    cases α with
    | nil => simp [DPoly.monoVal, ih (α := []) rfl]
    | cons a α =>
      rw [List.sum_cons] at hα
      simp [DPoly.monoVal, show a = 0 by omega, ih (α := α) (by omega)]

theorem monoVal_pexp_zero : DPoly.monoVal n (pexp n 0) y = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pexp, Nat.zero_mod, Nat.zero_div, DPoly.monoVal, List.headD_cons, List.tail_cons,
      pow_zero, one_mul]
    exact ih

end Cube

/-! ### Distributions into buckets -/

section Buckets

/-- `y^β` divides `y^α`: no exponent of `β` exceeds that of `α`. -/
def expLE : List ℕ → List ℕ → Bool
  | [], _ => true
  | b :: β, α => decide (b ≤ α.headD 0) && expLE β α.tail

/-- `min(0, c)`, with whether the sign of `c` was decided. -/
def negPart (c : κ) : κ × Bool :=
  bif Exact.nonneg c then (Exact.ofInt 0, true)
  else bif Exact.nonneg (Exact.ofInt 0 - c) then (c, true) else (Exact.ofInt 0, false)

theorem negPart_le {c : κ} (h : (negPart c).2 = true) :
    Exact.re (negPart c).1 ≤ 0 ∧ Exact.re (negPart c).1 ≤ Exact.re c := by
  unfold negPart at h ⊢
  cases hc : Exact.nonneg c
  · cases hc' : Exact.nonneg (Exact.ofInt 0 - c)
    · simp [hc, hc'] at h
    · have := Exact.nonneg_sound _ hc'
      rw [Exact.re_sub, re_zero] at this
      simp only [Bool.cond_false, Bool.cond_true]
      constructor <;> linarith
  · have := Exact.nonneg_sound _ hc
    simp only [Bool.cond_true, re_zero]
    exact ⟨le_rfl, this⟩

/-- The guard bits of `n` packed exponents: bit `15` of each. -/
def guardBits (n : ℕ) : ℕ := packExp (List.replicate n (2 ^ 15))

/-- `y^β` divides `y^α`, for packed monomials `a` and `b` of `n` exponents below `2^15`, with
`G = guardBits n` and `T = 2^(16 n)` (`divP_sound`): neither has bits above its exponents or guard
bits set, and `(a ||| G) - b` keeps every guard bit (no exponent of `b` exceeds that of `a`, so
none borrows). -/
def divP (G T a b : ℕ) : Bool :=
  Nat.blt (Nat.lor a b) T && Nat.beq (Nat.land (Nat.lor a b) G) 0 &&
    Nat.beq (Nat.land (Nat.sub (Nat.lor a G) b) G) G

/-! #### The exact pass

Terms come with the keys of their buckets: increasing numbers, the first bucket's `1` and the
next one's `nx q` after `q` (slot powers for vertex dominance, indices plus one for monomial
dominance), `0` or any number that is no bucket's key for none. Sorted by key, the terms meet the
buckets in order, so each bucket's sum is made in one pass (`pass`), with exact divisibility and
signs. -/

/-- A term `(a, c)` alone: all of `c` if it is constant (`a = 0`), else `min(0, c)`. -/
def lone (t : ℕ × κ) : κ × Bool :=
  bif Nat.beq t.1 0 then (t.2, true) else negPart t.2

/-- Adds a value to a bound, with whether its signs were decided. -/
def addB (acc x : κ × Bool) : κ × Bool := (acc.1 + x.1, acc.2 && x.2)

/-- A state of the exact pass: the key of the current bucket, the buckets from it on with their
sums so far, and the bound so far. -/
abbrev PassSt (κ : Type) := ℕ × List (ℕ × κ) × (κ × Bool)

/-- Closes the buckets before key `p` (the current one has key `q`; the next `nx q`): each adds
the negative part of its sum to the bound. -/
def advance (nx : ℕ → ℕ) (p : ℕ) : ℕ → List (ℕ × κ) → κ × Bool → PassSt κ
  | q, [], acc => (q, [], acc)
  | q, b :: bs, acc =>
    bif Nat.blt q p then advance nx p (nx q) bs (addB acc (negPart b.2))
    else (q, b :: bs, acc)

/-- One term `t` of key `p`: to the current bucket if it has key `p` and divides the term (`divP`
with `G` and `T`; all of the coefficient for the same monomial, else its negative part), else
alone. -/
def step (G T : ℕ) (nx : ℕ → ℕ) (st : PassSt κ) (pt : ℕ × (ℕ × κ)) : PassSt κ :=
  match advance nx pt.1 st.1 st.2.1 st.2.2 with
  | (q, b :: bs, acc) =>
    bif Nat.beq pt.1 q && divP G T pt.2.1 b.1 then
      bif Nat.beq pt.2.1 b.1 then (q, (b.1, b.2 + pt.2.2) :: bs, acc)
      else (q, (b.1, b.2 + (negPart pt.2.2).1) :: bs, (acc.1, acc.2 && (negPart pt.2.2).2))
    else (q, b :: bs, addB acc (lone pt.2))
  | (q, [], acc) => (q, [], addB acc (lone pt.2))

/-- **The exact pass** in `n` variables: the terms with the keys of their buckets (sorted by them)
into the buckets `(b, s)` with their initial sums (keys `1, nx 1, nx (nx 1), …`), then the
negative parts of the sums. -/
def pass (n : ℕ) (nx : ℕ → ℕ) (bs : List (ℕ × κ)) (L : List (ℕ × (ℕ × κ))) : κ × Bool :=
  let st := L.foldl (step (guardBits n) (2 ^ (16 * n)) nx) (1, bs, (Exact.ofInt 0, true))
  st.2.1.foldl (fun acc b ↦ addB acc (negPart b.2)) st.2.2

/-! #### Choices of buckets

The choices need no correctness (the exact pass checks divisibility, and its bound holds for every
assignment, `pass_le`). They use approximate sums of the buckets (`apxVal`, exact over `ℤ`). For
vertex dominance they run on numerals with one slot of `16 k` bits per variable: the sums are
biased, so that a term's variable is found by visiting its support by the lowest set bits; the
kernel does these operations natively. Monomial dominance has a bucket for every positive term, so
a slot per bucket would make numerals of `#buckets` slots, one per term (quadratic memory and
time): its sums lie in an array indexed by bucket instead, and each term is tested against each
bucket by `divP`. -/

/-- Rows `kⱼ` packed in slots of `W` bits: `∑ⱼ kⱼ 2^(W j)`. -/
def rows (W : ℕ) : List ℕ → ℕ
  | [] => 0
  | k :: ks => Nat.add k (Nat.shiftLeft (rows W ks) W)

/-- An integer approximation `∑ⱼ cⱼ aⱼ` of `2^apxK c` from the coordinates `cⱼ` of `c`
(`ExactBasis.apx`); `c` itself over `ℤ`. -/
def apxVal (c : κ) : ℤ :=
  ((ExactBasis.coords c).zipWith (fun x a ↦ x * a.1) (ExactBasis.apx κ)).sum

/-- A width `w`, doubled until `t < 2^w` (at most `f` times). -/
def widthFor (t : ℕ) : ℕ → ℕ → ℕ
  | 0, w => w
  | f + 1, w => bif Nat.blt t (Nat.shiftLeft 1 w) then w else widthFor t f (Nat.mul 2 w)

/-- Merges two lists sorted by the key, the first on ties (`f` steps; then they are appended). -/
def mergeK {α : Type} : ℕ → List (ℕ × α) → List (ℕ × α) → List (ℕ × α)
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, x :: xs, [] => x :: xs
  | f + 1, x :: xs, y :: ys =>
    bif Nat.ble x.1 y.1 then x :: mergeK f xs (y :: ys) else y :: mergeK f (x :: xs) ys

/-- Merges the runs in adjacent pairs. -/
def mergePairs {α : Type} (f : ℕ) : List (List (ℕ × α)) → List (List (ℕ × α))
  | a :: b :: rs => mergeK f a b :: mergePairs f rs
  | rs => rs

/-- Merges the runs in pairs until one is left (`g` rounds; then they are appended). -/
def mergeRuns {α : Type} (f : ℕ) : ℕ → List (List (ℕ × α)) → List (ℕ × α)
  | 0, rs => rs.flatten
  | _ + 1, [] => []
  | _ + 1, [r] => r
  | g + 1, r :: s :: rs => mergeRuns f g (mergePairs f (r :: s :: rs))

/-- Merge sort by the key, stable, bottom up. -/
def sortK {α : Type} (l : List (ℕ × α)) : List (ℕ × α) :=
  mergeRuns l.length l.length (l.map fun x ↦ [x])

/-- Bit `0` of each of `n` packed exponents. -/
def unitBits (n : ℕ) : ℕ := packExp (List.replicate n 1)

/-- The packed monomial `a` has degree at most one (`M = unitBits n`): `0`, or one bit, at bit `0`
of an exponent. -/
def isLow (M a : ℕ) : Bool := Nat.beq (Nat.land a (Nat.sub a 1)) 0 && Nat.beq (Nat.land a M) a

/-- The packed monomial `a` is a variable. -/
def isLin (M a : ℕ) : Bool := !Nat.beq a 0 && isLow M a

/-- The variable of largest sum among those whose guard bits are set in `d` (at most `f` of them),
the first on ties, given the best so far: its slot power `p = 2^(16 k i)` and its sum `v`, biased
in the slots of `16 k` bits of `S`. The lowest set bit of `d` comes next; `0` stands for none. -/
def vBest (k S mask : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, p, _ => p
  | f + 1, d, p, v =>
    bif Nat.beq d 0 then p else
      let low := Nat.land d (Nat.xor d (Nat.sub d 1))
      let q := Nat.pow (Nat.shiftRight low 15) k
      let u := Nat.land (Nat.div S q) mask
      bif Nat.blt v u then vBest k S mask f (Nat.xor d low) q u
      else vBest k S mask f (Nat.xor d low) p v

/-- `vBest` with a shift for the division by the slot power (`DPoly.divP2`). -/
def vBestS (k S mask : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, p, _ => p
  | f + 1, d, p, v =>
    bif Nat.beq d 0 then p else
      let low := Nat.land d (Nat.xor d (Nat.sub d 1))
      let q := Nat.pow (Nat.shiftRight low 15) k
      let u := Nat.land (DPoly.divP2 S q) mask
      bif Nat.blt v u then vBestS k S mask f (Nat.xor d low) q u
      else vBestS k S mask f (Nat.xor d low) p v

@[csimp] theorem vBest_eq_vBestS : @vBest = @vBestS := by
  funext k S mask f
  induction f with
  | zero => funext d p v; rfl
  | succ f ih =>
    funext d p v
    simp only [vBest, vBestS, DPoly.divP2_eq, nat_div', ih]

/-- Assigns the terms in order, each to the variable of largest sum in its support (whose guard
bits are set in `a + M`, `M` holding `2^15 - 1` in every exponent, `G = guardBits n`), whose sum
then takes the term's approximate coefficient: the slot power of the variable (`0` for none) with
the term. -/
def vAssign (n k mask M G : ℕ) : ℕ → List (ℕ × κ) → List (ℕ × (ℕ × κ))
  | _, [] => []
  | S, t :: L =>
    let p := vBest k S mask n (Nat.land (Nat.add t.1 M) G) 0 0
    let v := apxVal t.2
    (p, t) :: vAssign n k mask M G
      (Nat.sub (Nat.add S (Nat.mul v.toNat p)) (Nat.mul (-v).toNat p)) L

/-- The terms of vertex dominance: those of degree at most one or of possibly negative
coefficient (the others are at least `0` on `[0, 1]^n`), the linear ones first. -/
def vertTerms (n : ℕ) (ms : List (ℕ × κ)) : List (ℕ × κ) :=
  let L := ms.filter fun t ↦ isLow (unitBits n) t.1 || !Exact.nonneg t.2
  L.filter (fun t ↦ isLin (unitBits n) t.1) ++ L.filter fun t ↦ !isLin (unitBits n) t.1

/-- `vertTerms` with the unit bits `M` given. -/
def vertTermsM (M : ℕ) (ms : List (ℕ × κ)) : List (ℕ × κ) :=
  let L := ms.filter fun t ↦ isLow M t.1 || !Exact.nonneg t.2
  L.filter (fun t ↦ isLin M t.1) ++ L.filter fun t ↦ !isLin M t.1

/-- `vertTerms` as compiled code runs it (`vertTerms_eq_vertTermsS`): the unit bits once, not once
for each term in each filter. -/
def vertTermsS (n : ℕ) (ms : List (ℕ × κ)) : List (ℕ × κ) := vertTermsM (unitBits n) ms

@[csimp] theorem vertTerms_eq_vertTermsS : @vertTerms = @vertTermsS := rfl

/-- The slot width of vertex dominance (`16 k` bits, with room for the biased approximate sums) and
the terms with the slot powers of their variables, sorted by them. -/
def vertAssign (n : ℕ) (L : List (ℕ × κ)) : ℕ × List (ℕ × (ℕ × κ)) :=
  let w := widthFor (L.foldl (fun t x ↦ Nat.add t (apxVal x.2).natAbs) 0) 64 64
  let k := Nat.add (Nat.div w 16) 1
  let W := Nat.mul 16 k
  (W, sortK (vAssign n k (Nat.sub (Nat.shiftLeft 1 W) 1) (packExp (List.replicate n 32767))
    (guardBits n) (rows W (List.replicate n (Nat.shiftLeft 1 (W - 2)))) L))

/-- **Vertex dominance** of terms with packed monomials in `n` variables: the buckets are the
variables; the linear terms first, the other terms of possibly negative coefficient (and the
constant) after. -/
def vertBound (n : ℕ) (ms : List (ℕ × κ)) : κ × Bool :=
  let A := vertAssign n (vertTerms n ms)
  pass n (fun q ↦ Nat.shiftLeft q A.1)
    ((List.range n).map fun i ↦ (Nat.shiftLeft 1 (16 * i), Exact.ofInt 0)) A.2

/-- A term is a bucket of monomial dominance: not constant, with positive coefficient. -/
def isBucket (t : ℕ × κ) : Bool := !Nat.beq t.1 0 && Exact.pos t.2

/-- The number of the monomials `ks` that `y^a` is divisible by (`dv a k`), added to `c`. -/
def divCount (dv : ℕ → ℕ → Bool) (a : ℕ) : List ℕ → ℕ → ℕ
  | [], c => c
  | k :: ks, c => divCount dv a ks (bif dv a k then Nat.succ c else c)

/-- The bucket of largest approximate sum (`S`, by index) among the monomials `ks` that `y^a` is
divisible by (`dv a k`), the last on ties, given the best so far: its index plus one (`0` for none)
and its sum; `j` is the index of the head of `ks`. -/
def bestIdx (dv : ℕ → ℕ → Bool) (a : ℕ) (S : Array ℤ) : List ℕ → ℕ → ℕ → ℤ → ℕ
  | [], _, i, _ => i
  | k :: ks, j, i, s =>
    bif dv a k then
      bif Nat.beq i 0 || decide (s ≤ S.getD j 0) then
        bestIdx dv a S ks (Nat.succ j) (Nat.succ j) (S.getD j 0)
      else bestIdx dv a S ks (Nat.succ j) i s
    else bestIdx dv a S ks (Nat.succ j) i s

/-- Assigns the terms `(a, v, t)` (monomial `a`, approximate coefficient `v`) in order, each to its
bucket of largest sum among the buckets `ks` that `y^a` is divisible by (`bestIdx`), whose sum then
takes `v`: the index of the bucket plus one (`0` for none) with the term. -/
def assignIdx (dv : ℕ → ℕ → Bool) (ks : List ℕ) :
    Array ℤ → List (ℕ × ℤ × (ℕ × κ)) → List (ℕ × (ℕ × κ))
  | _, [] => []
  | S, (a, v, t) :: L =>
    let i := bestIdx dv a S ks 0 0 0
    (i, t) :: assignIdx dv ks (bif Nat.beq i 0 then S else S.modify (Nat.pred i) (· + v)) L

/-- The fields `I` (each of `16` bits) of the packed monomial `a`, repacked in `w` bits each. -/
def squeeze (w a : ℕ) : List ℕ → ℕ
  | [] => 0
  | i :: I => Nat.add (Nat.land (Nat.shiftRight a (16 * i)) 65535) (Nat.shiftLeft (squeeze w a I) w)

/-- The divisibility test of the choices of monomial dominance and the monomials it takes, for
the packed monomials whose bits are all among those of `o`, in `n` variables: if `o` passes the
checks of `divP`, the monomials repacked (`squeeze`) to the fields of `o` that are not `0`, in
fields of the width of its largest one and a guard bit, where `divP`'s test is a word operation on
small numbers; else `divP` on the packed monomials. -/
def divTest (n o : ℕ) : (ℕ → ℕ → Bool) × (ℕ → ℕ) :=
  let G := guardBits n
  let T := 2 ^ (16 * n)
  bif Nat.blt o T && Nat.beq (Nat.land o G) 0 then
    let I := (List.range n).filter fun i ↦ !Nat.beq (Nat.land (Nat.shiftRight o (16 * i)) 65535) 0
    let w := Nat.log2 (I.foldl (fun m i ↦ max m (Nat.land (Nat.shiftRight o (16 * i)) 65535)) 0) + 2
    let G' := rows w (List.replicate I.length (Nat.shiftLeft 1 (w - 1)))
    (fun a b ↦ Nat.beq (Nat.land (Nat.sub (Nat.lor a G') b) G') G', fun a ↦ squeeze w a I)
  else (divP G T, id)

/-- The terms `rest` with the indices plus one of their buckets among the terms `pos` (`0` for
none), sorted by them: by the number of buckets dividing them, then by approximate coefficient
(biased in `W` bits), each to the dividing bucket of largest sum, the last on ties, as in the Rust
check. Divisibility is `divP`'s, on small numbers where it can (`divTest`). -/
def monoAssign (n : ℕ) (pos rest : List (ℕ × κ)) : List (ℕ × (ℕ × κ)) :=
  let W := widthFor (rest.foldl (fun t x ↦ Nat.add t (apxVal x.2).natAbs) 0) 64 64 + 1
  let d := divTest n (rest.foldl (fun o t ↦ Nat.lor o t.1) (pos.foldl (fun o t ↦ Nat.lor o t.1) 0))
  let ks := pos.map fun t ↦ d.2 t.1
  let keyed := rest.map fun t ↦
    let a := d.2 t.1
    let v := apxVal t.2
    (Nat.add (Nat.shiftLeft (divCount d.1 a ks 0) W) (v + (Nat.shiftLeft 1 (W - 1) : ℕ)).toNat,
      (a, v, t))
  sortK (assignIdx d.1 ks (pos.map fun x ↦ apxVal x.2).toArray ((sortK keyed).map Prod.snd))

/-- **Monomial dominance** of terms with packed monomials in `n` variables: the buckets are the
positive terms, keyed by their indices plus one; the other terms go to buckets by `monoAssign`. -/
def monoBound (n : ℕ) (ms : List (ℕ × κ)) : κ × Bool :=
  let pos := ms.filter isBucket
  pass n Nat.succ pos (monoAssign n pos (ms.filter fun t ↦ !isBucket t))

/-- **The dominance bound** of terms with packed monomials in `n` variables on `[0, 1]^n`: vertex
dominance, and monomial dominance where vertex dominance is not positive. -/
def domBound (n : ℕ) (ms : List (ℕ × κ)) : κ × Bool :=
  let v := vertBound n ms
  bif v.2 && Exact.pos v.1 then v else
    let m := monoBound n ms
    bif m.2 && (!v.2 || Exact.nonneg (m.1 - v.1)) then m else v

variable {n : ℕ} {y : Fin n → ℝ}

theorem monoVal_le_of_expLE (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) {β α : List ℕ}
    (h : expLE β α = true) : DPoly.monoVal n α y ≤ DPoly.monoVal n β y := by
  induction n generalizing β α with
  | zero => exact le_rfl
  | succ n ih =>
    have hy' : ∀ i, 0 ≤ Fin.tail y i ∧ Fin.tail y i ≤ 1 := fun i ↦ hy i.succ
    cases β with
    | nil =>
      rw [monoVal_of_sum_zero (α := []) rfl]
      exact (monoVal_mem_unit hy α).2
    | cons b β =>
      simp only [expLE, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [DPoly.monoVal, DPoly.monoVal, List.headD_cons, List.tail_cons]
      exact mul_le_mul (pow_le_pow_of_le_one (hy 0).1 (hy 0).2 h.1) (ih hy' h.2)
        (monoVal_mem_unit hy' α.tail).1 (pow_nonneg (hy 0).1 _)

theorem negPart_le_mul (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) {c : κ} (h : (negPart c).2 = true)
    (α : List ℕ) : Exact.re (negPart c).1 ≤ Exact.re c * DPoly.monoVal n α y := by
  obtain ⟨hn₀, hn₁⟩ := negPart_le h
  obtain ⟨h₀, h₁⟩ := monoVal_mem_unit hy α
  rcases le_total 0 (Exact.re c) with hc | hc
  · exact hn₀.trans (mul_nonneg hc h₀)
  · nlinarith

/-! #### Soundness of the divisibility test -/

theorem land_split16 {x z : ℕ} (y w : ℕ) (hx : x < 2 ^ 16) (hz : z < 2 ^ 16) :
    (x + y * 2 ^ 16) &&& (z + w * 2 ^ 16) = (x &&& z) + (y &&& w) * 2 ^ 16 := by
  have e : ∀ a b : ℕ, a + b * 2 ^ 16 = 2 ^ 16 * b + a := fun a b ↦ by ring
  rw [e, e, e]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ hx, Nat.testBit_two_pow_mul_add _ hz,
    Nat.testBit_two_pow_mul_add _ (Nat.and_lt_two_pow x hz)]
  split_ifs <;> simp

theorem lor_split16 {x z : ℕ} (y w : ℕ) (hx : x < 2 ^ 16) (hz : z < 2 ^ 16) :
    (x + y * 2 ^ 16) ||| (z + w * 2 ^ 16) = (x ||| z) + (y ||| w) * 2 ^ 16 := by
  have e : ∀ a b : ℕ, a + b * 2 ^ 16 = 2 ^ 16 * b + a := fun a b ↦ by ring
  rw [e, e, e]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, Nat.testBit_two_pow_mul_add _ hx, Nat.testBit_two_pow_mul_add _ hz,
    Nat.testBit_two_pow_mul_add _ (Nat.or_lt_two_pow hx hz)]
  split_ifs <;> simp

theorem land_bit15 {d : ℕ} (hd : d < 2 ^ 16) :
    d &&& 2 ^ 15 = if 2 ^ 15 ≤ d then 2 ^ 15 else 0 := by
  have h15 : d.testBit 15 = decide (2 ^ 15 ≤ d) := by
    rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_decide]
    norm_num at hd ⊢
    omega
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  split_ifs with h
  · rw [Nat.testBit_two_pow]
    by_cases hj : 15 = j
    · subst hj
      rw [h15, decide_eq_true h, Bool.true_and]
    · simp [hj]
  · rw [Nat.zero_testBit]
    by_cases hj : 15 = j
    · subst hj
      rw [h15, decide_eq_false h, Bool.false_and]
    · simp [hj]

theorem lor_bit15 {x : ℕ} (hx : x < 2 ^ 15) : x ||| 2 ^ 15 = x + 2 ^ 15 := by
  have := Nat.two_pow_add_eq_or_of_lt hx 1
  rw [mul_one] at this
  rw [Nat.or_comm, ← this, Nat.add_comm]

theorem guardBits_succ (n : ℕ) : guardBits (n + 1) = 2 ^ 15 + guardBits n * 2 ^ 16 := rfl

theorem le_guardBits (n : ℕ) : ∀ x : ℕ, x < 2 ^ (16 * n) → x &&& guardBits n = 0 →
    x ≤ guardBits n := by
  induction n with
  | zero => intro x hx _; simp at hx; omega
  | succ n ih =>
    intro x hx hg
    obtain ⟨x₀, x', hx₀, rfl⟩ : ∃ x₀ x', x₀ < 2 ^ 16 ∧ x = x₀ + x' * 2 ^ 16 :=
      ⟨_, _, Nat.mod_lt x (Nat.two_pow_pos 16), (Nat.mod_add_div' x _).symm⟩
    rw [guardBits_succ, land_split16 _ _ hx₀ (by norm_num)] at hg
    have h₁ : x₀ &&& 2 ^ 15 = 0 := by omega
    have h₂ : x' &&& guardBits n = 0 := by omega
    rw [land_bit15 hx₀] at h₁
    have hlt : x₀ < 2 ^ 15 := by
      by_contra hc
      rw [ite_eq_left (by omega : 2 ^ 15 ≤ x₀)] at h₁
      norm_num at h₁
    have hx' : x' < 2 ^ (16 * n) := by
      have e : 2 ^ (16 * (n + 1)) = 2 ^ (16 * n) * 2 ^ 16 := by rw [← pow_add]; ring_nf
      rw [e] at hx
      exact Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt (Nat.le_add_left _ _) hx)
    have := ih x' hx' h₂
    rw [guardBits_succ]
    omega

theorem divP_succ {n a₀ a' b₀ b' : ℕ} (ha : a₀ < 2 ^ 16) (hb : b₀ < 2 ^ 16)
    (h : divP (guardBits (n + 1)) (2 ^ (16 * (n + 1))) (a₀ + a' * 2 ^ 16) (b₀ + b' * 2 ^ 16) =
      true) :
    b₀ ≤ a₀ ∧ divP (guardBits n) (2 ^ (16 * n)) a' b' = true := by
  have lor : ∀ a b : ℕ, Nat.lor a b = a ||| b := fun _ _ ↦ rfl
  have land : ∀ a b : ℕ, Nat.land a b = a &&& b := fun _ _ ↦ rfl
  have sub : ∀ a b : ℕ, Nat.sub a b = a - b := fun _ _ ↦ rfl
  simp only [divP, lor, land, sub, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h ⊢
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h
  rw [guardBits_succ] at h₂ h₃
  have hab : a₀ ||| b₀ < 2 ^ 16 := Nat.or_lt_two_pow ha hb
  rw [lor_split16 _ _ ha hb] at h₁ h₂
  rw [land_split16 _ _ hab (by norm_num)] at h₂
  have h₂a : (a₀ ||| b₀) &&& 2 ^ 15 = 0 := by omega
  have h₂b : (a' ||| b') &&& guardBits n = 0 := by omega
  rw [land_bit15 hab] at h₂a
  have hab' : a₀ ||| b₀ < 2 ^ 15 := by
    by_contra hc
    rw [ite_eq_left (by omega : 2 ^ 15 ≤ a₀ ||| b₀)] at h₂a
    norm_num at h₂a
  have ha' : a₀ < 2 ^ 15 := lt_of_le_of_lt Nat.left_le_or hab'
  have hb' : b₀ < 2 ^ 15 := lt_of_le_of_lt Nat.right_le_or hab'
  have h₁' : a' ||| b' < 2 ^ (16 * n) := by
    have e : 2 ^ (16 * (n + 1)) = 2 ^ (16 * n) * 2 ^ 16 := by rw [← pow_add]; ring_nf
    rw [e] at h₁
    exact Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt (Nat.le_add_left _ _) h₁)
  have hbG : b' ≤ guardBits n := by
    refine le_guardBits n b' (lt_of_le_of_lt Nat.right_le_or h₁') ?_
    rw [Nat.and_or_distrib_right, Nat.or_eq_zero_iff] at h₂b
    exact h₂b.2
  rw [lor_split16 _ _ ha (by norm_num), lor_bit15 ha'] at h₃
  have hX : b' ≤ a' ||| guardBits n := hbG.trans Nat.right_le_or
  have hsub : a₀ + 2 ^ 15 + (a' ||| guardBits n) * 2 ^ 16 - (b₀ + b' * 2 ^ 16) =
      (a₀ + 2 ^ 15 - b₀) + ((a' ||| guardBits n) - b') * 2 ^ 16 := by
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hX
    rw [hc, Nat.add_sub_cancel_left]
    have : b₀ ≤ a₀ + 2 ^ 15 := by omega
    rw [add_mul]
    omega
  rw [hsub, land_split16 _ _ (by omega) (by norm_num)] at h₃
  have hl : (a₀ + 2 ^ 15 - b₀) &&& 2 ^ 15 ≤ 2 ^ 15 := Nat.and_le_right
  have h₃a : (a₀ + 2 ^ 15 - b₀) &&& 2 ^ 15 = 2 ^ 15 := by omega
  have h₃b : ((a' ||| guardBits n) - b') &&& guardBits n = guardBits n := by omega
  rw [land_bit15 (by omega)] at h₃a
  refine ⟨?_, ⟨h₁', h₂b⟩, h₃b⟩
  by_contra hc
  rw [ite_eq_right (by omega : ¬2 ^ 15 ≤ a₀ + 2 ^ 15 - b₀)] at h₃a
  norm_num at h₃a

/-- **Soundness of the divisibility test**: no exponent of `b` exceeds that of `a`. -/
theorem divP_sound (n : ℕ) : ∀ (a b : ℕ), divP (guardBits n) (2 ^ (16 * n)) a b = true →
    expLE (pexp n b) (pexp n a) = true := by
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
    intro a b h
    obtain ⟨a₀, a', ha, rfl⟩ : ∃ a₀ a', a₀ < 2 ^ 16 ∧ a = a₀ + a' * 2 ^ 16 :=
      ⟨_, _, Nat.mod_lt a (Nat.two_pow_pos 16), (Nat.mod_add_div' a _).symm⟩
    obtain ⟨b₀, b', hb, rfl⟩ : ∃ b₀ b', b₀ < 2 ^ 16 ∧ b = b₀ + b' * 2 ^ 16 :=
      ⟨_, _, Nat.mod_lt b (Nat.two_pow_pos 16), (Nat.mod_add_div' b _).symm⟩
    obtain ⟨h₁, h₂⟩ := divP_succ ha hb h
    rw [pexp_succ_add _ ha, pexp_succ_add _ hb]
    simp only [expLE, List.headD_cons, List.tail_cons, Bool.and_eq_true]
    exact ⟨decide_eq_true h₁, ih a' b' h₂⟩

/-! #### Soundness of the exact pass -/

theorem psum_perm {L L' : List (ℕ × κ)} (h : L.Perm L') : psum n L y = psum n L' y :=
  (h.map _).sum_eq

theorem psum_append (L L' : List (ℕ × κ)) : psum n (L ++ L') y = psum n L y + psum n L' y := by
  simp [psum, List.map_append, List.sum_append]

theorem psum_filter_le (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (p : ℕ × κ → Bool) :
    ∀ L : List (ℕ × κ), (∀ t ∈ L, p t = false → 0 ≤ Exact.re t.2) →
      psum n (L.filter p) y ≤ psum n L y
  | [], _ => le_rfl
  | t :: L, h => by
    have ih := psum_filter_le hy p L fun t' ht' ↦ h t' (List.mem_cons_of_mem _ ht')
    simp only [psum] at ih ⊢
    rw [List.filter_cons]
    by_cases hp : p t = true
    · simp only [hp, ↓reduceIte, List.map_cons, List.sum_cons]
      linarith
    · have hc := h t List.mem_cons_self (by simpa using hp)
      have := mul_nonneg hc (monoVal_mem_unit hy (pexp n t.1)).1
      simp only [hp, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons]
      linarith

theorem lone_le (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (t : ℕ × κ) (h : (lone t).2 = true) :
    Exact.re (lone t).1 ≤ Exact.re t.2 * DPoly.monoVal n (pexp n t.1) y := by
  unfold lone at h ⊢
  cases hz : Nat.beq t.1 0
  · simp only [hz, Bool.cond_false] at h ⊢
    exact negPart_le_mul hy h _
  · simp only [Bool.cond_true]
    rw [Nat.eq_of_beq_eq_true hz, monoVal_pexp_zero, mul_one]

/-- The value `s₀ + ∑ s_b y^b` of a state of the exact pass (in proofs). -/
noncomputable def passVal (n : ℕ) (st : PassSt κ) (y : Fin n → ℝ) : ℝ :=
  Exact.re st.2.2.1 + psum n st.2.1 y

theorem advance_le (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (nx : ℕ → ℕ) (p : ℕ) :
    ∀ (q : ℕ) (bs : List (ℕ × κ)) (acc : κ × Bool), (advance nx p q bs acc).2.2.2 = true →
      acc.2 = true ∧ passVal n (advance nx p q bs acc) y ≤ passVal n (q, bs, acc) y
  | q, [], acc, h => by
    simp only [advance] at h ⊢
    exact ⟨h, le_rfl⟩
  | q, b :: bs, acc, h => by
    simp only [advance] at h ⊢
    cases hq : Nat.blt q p
    · simp only [hq, Bool.cond_false] at h ⊢
      exact ⟨h, le_rfl⟩
    · simp only [hq, Bool.cond_true] at h ⊢
      obtain ⟨h₁, h₂⟩ := advance_le hy nx p _ bs _ h
      simp only [addB, Bool.and_eq_true] at h₁
      refine ⟨h₁.1, h₂.trans ?_⟩
      have := negPart_le_mul hy h₁.2 (pexp n b.1)
      simp only [passVal, addB, Exact.re_add, psum, List.map_cons, List.sum_cons]
      linarith

theorem step_le (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (nx : ℕ → ℕ) (st : PassSt κ) (pt : ℕ × (ℕ × κ))
    (h : (step (guardBits n) (2 ^ (16 * n)) nx st pt).2.2.2 = true) :
    st.2.2.2 = true ∧ passVal n (step (guardBits n) (2 ^ (16 * n)) nx st pt) y ≤
      passVal n st y + Exact.re pt.2.2 * DPoly.monoVal n (pexp n pt.2.1) y := by
  obtain ⟨q₀, bs₀, acc₀⟩ := st
  have hA := advance_le (n := n) (y := y) hy nx pt.1 q₀ bs₀ acc₀
  simp only [step] at h ⊢
  rcases ha : advance nx pt.1 q₀ bs₀ acc₀ with ⟨q, _ | ⟨b, bs⟩, acc⟩ <;>
    simp only [ha] at hA h ⊢
  · simp only [addB, Bool.and_eq_true] at h
    obtain ⟨hok, hle⟩ := hA h.1
    refine ⟨hok, ?_⟩
    have := lone_le hy pt.2 h.2
    simp only [passVal, addB, Exact.re_add] at hle ⊢
    linarith
  · cases hc : (Nat.beq pt.1 q && divP (guardBits n) (2 ^ (16 * n)) pt.2.1 b.1)
    · simp only [hc, Bool.cond_false, addB, Bool.and_eq_true] at h ⊢
      obtain ⟨hok, hle⟩ := hA h.1
      refine ⟨hok, ?_⟩
      have := lone_le hy pt.2 h.2
      simp only [passVal, Exact.re_add] at hle ⊢
      linarith
    · have hd := monoVal_le_of_expLE hy (divP_sound n _ _ (Bool.and_eq_true_iff.mp hc).2)
      obtain ⟨h₀, -⟩ := monoVal_mem_unit hy (pexp n pt.2.1)
      cases he : Nat.beq pt.2.1 b.1
      · simp only [hc, he, Bool.cond_true, Bool.cond_false, Bool.and_eq_true] at h ⊢
        obtain ⟨hok, hle⟩ := hA h.1
        refine ⟨hok, ?_⟩
        obtain ⟨hn₀, hn₁⟩ := negPart_le h.2
        have k₁ := mul_nonpos_of_nonpos_of_nonneg hn₀ (sub_nonneg.mpr hd)
        have k₂ := mul_nonneg (sub_nonneg.mpr hn₁) h₀
        simp only [passVal, Exact.re_add, psum, List.map_cons, List.sum_cons] at hle ⊢
        nlinarith
      · simp only [hc, he, Bool.cond_true] at h ⊢
        obtain ⟨hok, hle⟩ := hA h
        refine ⟨hok, ?_⟩
        have heq : pt.2.1 = b.1 := Nat.eq_of_beq_eq_true he
        simp only [passVal, Exact.re_add, psum, List.map_cons, List.sum_cons] at hle ⊢
        rw [heq]
        linarith

theorem foldl_step_le (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (nx : ℕ → ℕ) :
    ∀ (L : List (ℕ × (ℕ × κ))) (st : PassSt κ),
      (L.foldl (step (guardBits n) (2 ^ (16 * n)) nx) st).2.2.2 = true →
        st.2.2.2 = true ∧ passVal n (L.foldl (step (guardBits n) (2 ^ (16 * n)) nx) st) y ≤
          passVal n st y + psum n (L.map Prod.snd) y
  | [], st, h => ⟨h, by simp [psum]⟩
  | pt :: L, st, h => by
    rw [List.foldl_cons] at h ⊢
    obtain ⟨h₁, h₂⟩ := foldl_step_le hy nx L _ h
    obtain ⟨h₃, h₄⟩ := step_le hy nx st pt h₁
    refine ⟨h₃, ?_⟩
    simp only [psum, List.map_cons, List.sum_cons] at h₂ ⊢
    linarith

theorem foldl_negPart_le (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) :
    ∀ (bs : List (ℕ × κ)) (acc : κ × Bool),
      (bs.foldl (fun acc b ↦ addB acc (negPart b.2)) acc).2 = true → acc.2 = true ∧
        Exact.re (bs.foldl (fun acc b ↦ addB acc (negPart b.2)) acc).1 ≤
          Exact.re acc.1 + psum n bs y
  | [], acc, h => ⟨h, by simp [psum]⟩
  | b :: bs, acc, h => by
    rw [List.foldl_cons] at h ⊢
    obtain ⟨h₁, h₂⟩ := foldl_negPart_le hy bs _ h
    simp only [addB, Bool.and_eq_true] at h₁
    have := negPart_le_mul hy h₁.2 (pexp n b.1)
    refine ⟨h₁.1, ?_⟩
    simp only [addB, Exact.re_add, psum, List.map_cons, List.sum_cons] at h₂ ⊢
    linarith

/-- **Soundness of the exact pass**: for any keys (any `nx`, any keys of the terms) and any order,
its bound is a lower bound of the buckets' initial terms and the terms on `[0, 1]^n`. -/
theorem pass_le (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (nx : ℕ → ℕ) (bs : List (ℕ × κ))
    (L : List (ℕ × (ℕ × κ))) (h : (pass n nx bs L).2 = true) :
    Exact.re (pass n nx bs L).1 ≤ psum n bs y + psum n (L.map Prod.snd) y := by
  obtain ⟨h₁, h₂⟩ := foldl_negPart_le hy _ _ h
  obtain ⟨-, h₃⟩ := foldl_step_le hy nx L _ h₁
  have h₀ : passVal n ((1, bs, (Exact.ofInt 0, true)) : PassSt κ) y = psum n bs y := by
    simp [passVal, re_zero (κ := κ)]
  simp only [passVal] at h₃ h₀
  simp only [pass]
  linarith

/-! #### Soundness of the bounds -/

theorem mergeK_perm {α : Type} : ∀ (f : ℕ) (xs ys : List (ℕ × α)),
    (mergeK f xs ys).Perm (xs ++ ys)
  | 0, _, _ => List.Perm.refl _
  | _ + 1, [], _ => List.Perm.refl _
  | _ + 1, _ :: _, [] => by simp only [mergeK, List.append_nil, List.Perm.refl]
  | f + 1, x :: xs, y :: ys => by
    simp only [mergeK]
    cases Nat.ble x.1 y.1
    · exact ((mergeK_perm f (x :: xs) ys).cons y).trans List.perm_middle.symm
    · exact (mergeK_perm f xs (y :: ys)).cons x

theorem mergePairs_perm {α : Type} (f : ℕ) : ∀ rs : List (List (ℕ × α)),
    (mergePairs f rs).flatten.Perm rs.flatten
  | a :: b :: rs => by
    simp only [mergePairs, List.flatten_cons, ← List.append_assoc]
    exact (mergeK_perm f a b).append (mergePairs_perm f rs)
  | [] => List.Perm.refl _
  | [_] => List.Perm.refl _

theorem mergeRuns_perm {α : Type} (f : ℕ) : ∀ (g : ℕ) (rs : List (List (ℕ × α))),
    (mergeRuns f g rs).Perm rs.flatten
  | 0, _ => List.Perm.refl _
  | _ + 1, [] => List.Perm.refl _
  | _ + 1, [_] => by simp only [mergeRuns, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.Perm.refl]
  | g + 1, r :: s :: rs => (mergeRuns_perm f g _).trans (mergePairs_perm f _)

theorem sortK_perm {α : Type} (l : List (ℕ × α)) : (sortK l).Perm l := by
  refine (mergeRuns_perm _ _ _).trans (List.Perm.of_eq ?_)
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, List.flatten_cons, ih, List.singleton_append]

theorem vAssign_map (n k mask M G : ℕ) : ∀ (S : ℕ) (L : List (ℕ × κ)),
    (vAssign n k mask M G S L).map Prod.snd = L
  | _, [] => rfl
  | S, t :: L => by simp only [vAssign, List.map_cons, vAssign_map n k mask M G _ L]

theorem vertAssign_perm (n : ℕ) (L : List (ℕ × κ)) :
    ((vertAssign n L).2.map Prod.snd).Perm L := by
  simp only [vertAssign]
  refine ((sortK_perm _).map Prod.snd).trans ?_
  rw [vAssign_map]

theorem vertBound_le (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (ms : List (ℕ × κ))
    (h : (vertBound n ms).2 = true) : Exact.re (vertBound n ms).1 ≤ psum n ms y := by
  have e : vertBound n ms = pass n (fun q ↦ Nat.shiftLeft q (vertAssign n (vertTerms n ms)).1)
      ((List.range n).map fun i ↦ (Nat.shiftLeft 1 (16 * i), Exact.ofInt 0))
      (vertAssign n (vertTerms n ms)).2 := rfl
  rw [e] at h ⊢
  have h₁ := pass_le hy _ _ _ h
  have h₀ : psum n ((List.range n).map fun i ↦ (Nat.shiftLeft 1 (16 * i), (Exact.ofInt 0 : κ)))
      y = 0 := by
    simp [psum, Function.comp_def, re_zero (κ := κ)]
  rw [h₀, zero_add, psum_perm (vertAssign_perm n _)] at h₁
  have hT : (vertTerms n ms).Perm
      (ms.filter fun t ↦ isLow (unitBits n) t.1 || !Exact.nonneg t.2) :=
    List.filter_append_perm _ _
  rw [psum_perm hT] at h₁
  exact h₁.trans (psum_filter_le hy _ ms fun t _ ht ↦ by
    simp only [Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false] at ht
    exact Exact.nonneg_sound _ ht.2)

omit [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] in
theorem assignIdx_map (dv : ℕ → ℕ → Bool) (ks : List ℕ) :
    ∀ (S : Array ℤ) (L : List (ℕ × ℤ × (ℕ × κ))),
      (assignIdx dv ks S L).map Prod.snd = L.map fun t ↦ t.2.2
  | _, [] => rfl
  | S, (a, v, t) :: L => by simp only [assignIdx, List.map_cons, assignIdx_map dv ks _ L]

theorem monoAssign_perm (n : ℕ) (pos rest : List (ℕ × κ)) :
    ((monoAssign n pos rest).map Prod.snd).Perm rest := by
  simp only [monoAssign]
  refine ((sortK_perm _).map Prod.snd).trans ?_
  rw [assignIdx_map, List.map_map]
  refine ((sortK_perm _).map _).trans ?_
  rw [List.map_map]
  exact List.Perm.of_eq (by simp [Function.comp_def])

theorem monoBound_le (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (ms : List (ℕ × κ))
    (h : (monoBound n ms).2 = true) : Exact.re (monoBound n ms).1 ≤ psum n ms y := by
  have e : monoBound n ms = pass n Nat.succ (ms.filter isBucket)
      (monoAssign n (ms.filter isBucket) (ms.filter fun t ↦ !isBucket t)) := rfl
  rw [e] at h ⊢
  have h₁ := pass_le hy _ _ _ h
  rw [psum_perm (monoAssign_perm n _ _), ← psum_append,
    psum_perm (List.filter_append_perm isBucket ms)] at h₁
  exact h₁

/-- **Soundness of the dominance bound**: on `[0, 1]^n` it is a lower bound of the sum of the
terms. -/
theorem domBound_le (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (ms : List (ℕ × κ))
    (h : (domBound n ms).2 = true) : Exact.re (domBound n ms).1 ≤ psum n ms y := by
  simp only [domBound] at h ⊢
  cases h₁ : ((vertBound n ms).2 && Exact.pos (vertBound n ms).1)
  · simp only [h₁, Bool.cond_false] at h ⊢
    cases h₂ : ((monoBound n ms).2 && (!(vertBound n ms).2 ||
        Exact.nonneg ((monoBound n ms).1 - (vertBound n ms).1)))
    · simp only [h₂, Bool.cond_false] at h ⊢
      exact vertBound_le hy ms h
    · simp only [h₂, Bool.cond_true] at h ⊢
      exact monoBound_le hy ms h
  · simp only [h₁, Bool.cond_true] at h ⊢
    exact vertBound_le hy ms h

end Buckets

/-! ### Packed coordinates -/

/-- The dominance bound read off the numerals `Ns` of the coordinates of a polynomial with shape
`sh` and `B`-bit digits (degrees below `2^16`), the variables after the last of positive degree
left out of the reading. -/
def domOf (n : ℕ) (sh : List ℕ) (B : ℕ) (Ns : List ℕ) : κ × Bool :=
  bif (DPoly.layout B n sh).all fun l ↦ Nat.ble l.1 65536 then
    domBound n (monosP (κ := κ) (2 ^ (B - 1)) (2 ^ B) (DPoly.layout B (nEff n sh) sh) 1 0 Ns [])
  else (Exact.ofInt 0, false)

/-- **Soundness of `domOf`**: on `[0, 1]^n` it is a lower bound of the polynomial `∑ⱼ βⱼ Tⱼ` of
the unpacked numerals `Tⱼ`. -/
theorem domOf_le (n : ℕ) (sh : List ℕ) (B : ℕ) (Ns : List ℕ) (y : Fin n → ℝ)
    (hlen : ExactBasis.dim κ ≤ Ns.length) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1)
    (h : (domOf (κ := κ) n sh B Ns).2 = true) :
    Exact.re (domOf (κ := κ) n sh B Ns).1 ≤
      ∑ j ∈ range (ExactBasis.dim κ),
        ExactBasis.basis κ j * DPoly.eval n (DPoly.unpack n sh B (Ns.getD j 0)) y := by
  unfold domOf at h ⊢
  cases hc : (DPoly.layout B n sh).all fun l ↦ Nat.ble l.1 65536
  · rw [hc] at h
    simp at h
  · rw [hc, Bool.cond_true] at h
    rw [Bool.cond_true, ← monoSumK_monosK n sh Ns y hlen, ← psum_monosP _ _ _ _
      fun l hl ↦ le_of_le_of_eq (Nat.le_of_ble_eq_true (List.all_eq_true.mp hc l hl))
        (by norm_num), layout_trim B n sh, monosP_trim]
    exact domBound_le hy _ h

end Nieuwland.Check
