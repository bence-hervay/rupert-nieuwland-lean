import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Ring

/-!
# Dense integer polynomials

`DPoly n` is the type of polynomials with integer coefficients in the variables
`x₀, …, x_{n-1}`, stored densely: a polynomial in `n + 1` variables is the list of its
coefficients in `x₀`, lowest degree first, each a polynomial in `x₁, …, x_n`. Lists need not be
trimmed, so a polynomial has many representations; everything below is stated through `eval`.

These polynomials are the objects that the checks of `Nieuwland/Check/` reason about. The kernel
never multiplies them term by term: it evaluates expressions at packed integers
(`Modules/Check/Polynomial/Pack.lean`) and only reads off coefficient lists. Hence the operations here favour
simple proofs over speed.

## Main definitions

* `DPoly.eval`: evaluation at a point of any commutative ring.
* `DPoly.add`, `DPoly.neg`, `DPoly.mul`, `DPoly.const`, `DPoly.linear`: the ring operations and
  the inputs `C + H xᵢ` of a box, with `eval_add`, `eval_mul`, ….
* `DPoly.Fits p e`: the degree of `p` in `xᵢ` is at most `e[i]` (as a list shape).
* `DPoly.absSum p`: the sum of the absolute values of the coefficients, which bounds each of them
  (`DPoly.AllCoeff`), with `absSum_add_le` and `absSum_mul_le`.
-/

namespace Nieuwland.Check

/-- Dense polynomials with integer coefficients in `n` variables. An element of `DPoly (n + 1)` is
the list of its coefficients in the first variable, lowest degree first. -/
def DPoly : ℕ → Type
  | 0 => ℤ
  | n + 1 => List (DPoly n)

/-- Elementwise combination of two lists, the shorter one padded by the other's entries. -/
def zipPad {α : Type*} (f : α → α → α) : List α → List α → List α
  | [], bs => bs
  | a :: as, [] => a :: as
  | a :: as, b :: bs => f a b :: zipPad f as bs

/-- Horner evaluation `f a₀ + z * (f a₁ + z * (…))` of a coefficient list. -/
def horner {α R : Type*} [Semiring R] (f : α → R) (z : R) : List α → R
  | [] => 0
  | a :: as => f a + z * horner f z as

/-- Product of two coefficient lists, given the zero, sum and product of coefficients. -/
def mulList {α : Type*} (z : α) (add mul : α → α → α) : List α → List α → List α
  | [], _ => []
  | a :: as, bs => zipPad add (bs.map (mul a)) (z :: mulList z add mul as bs)

@[simp] theorem horner_nil {α R : Type*} [Semiring R] {f : α → R} {z : R} : horner f z [] = 0 :=
  rfl

@[simp] theorem horner_cons {α R : Type*} [Semiring R] {f : α → R} {z : R} (a : α) (as : List α) :
    horner f z (a :: as) = f a + z * horner f z as := rfl

section Lists

variable {α R : Type*} [CommRing R] {f : α → R} {z : R}

theorem horner_zipPad {g : α → α → α} (hg : ∀ a b, f (g a b) = f a + f b) :
    ∀ as bs : List α, horner f z (zipPad g as bs) = horner f z as + horner f z bs
  | [], bs => by simp [zipPad]
  | a :: as, [] => by simp [zipPad]
  | a :: as, b :: bs => by
    simp only [zipPad, horner_cons, hg, horner_zipPad hg as bs]
    ring

theorem horner_map {g : α → α} {c : R} (hg : ∀ a, f (g a) = c * f a) :
    ∀ as : List α, horner f z (as.map g) = c * horner f z as
  | [] => by simp
  | a :: as => by
    simp only [List.map_cons, horner_cons, hg, horner_map hg as]
    ring

theorem horner_mulList {z₀ : α} {add mul : α → α → α} (h₀ : f z₀ = 0)
    (hadd : ∀ a b, f (add a b) = f a + f b) (hmul : ∀ a b, f (mul a b) = f a * f b) :
    ∀ as bs : List α, horner f z (mulList z₀ add mul as bs) = horner f z as * horner f z bs
  | [], bs => by simp [mulList]
  | a :: as, bs => by
    simp only [mulList, horner_zipPad hadd, horner_map (hmul a), horner_cons, h₀,
      horner_mulList h₀ hadd hmul as bs]
    ring

theorem mem_zipPad {g : α → α → α} {c : α} :
    ∀ {as bs : List α}, c ∈ zipPad g as bs →
      (∃ a ∈ as, ∃ b ∈ bs, c = g a b) ∨ c ∈ as ∨ c ∈ bs
  | [], bs, h => Or.inr (Or.inr h)
  | a :: as, [], h => Or.inr (Or.inl h)
  | a :: as, b :: bs, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl ⟨a, List.mem_cons_self, b, List.mem_cons_self, rfl⟩
    · rcases mem_zipPad h with ⟨a', ha, b', hb, rfl⟩ | h | h
      · exact Or.inl ⟨a', List.mem_cons_of_mem _ ha, b', List.mem_cons_of_mem _ hb, rfl⟩
      · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h))
      · exact Or.inr (Or.inr (List.mem_cons_of_mem _ h))

theorem length_zipPad (g : α → α → α) :
    ∀ as bs : List α, (zipPad g as bs).length = max as.length bs.length
  | [], bs => by simp [zipPad]
  | a :: as, [] => by simp [zipPad]
  | a :: as, b :: bs => by simp [zipPad, length_zipPad g as bs, Nat.succ_max_succ]

theorem length_mulList (z₀ : α) (add mul : α → α → α) :
    ∀ as bs : List α, (mulList z₀ add mul as bs).length + 1 ≤ as.length + max bs.length 1
  | [], bs => by simp [mulList]
  | a :: as, bs => by
    have := length_mulList z₀ add mul as bs
    simp only [mulList, length_zipPad, List.length_map, List.length_cons]
    omega

theorem zipPad_self_max : ∀ e : List ℕ, zipPad max e e = e
  | [] => rfl
  | a :: e => by simp [zipPad, zipPad_self_max e]

theorem headD_zipPad (g : ℕ → ℕ → ℕ) (hg : ∀ a, g a 0 = a) (hg' : ∀ b, g 0 b = b) :
    ∀ e e' : List ℕ, (zipPad g e e').headD 0 = g (e.headD 0) (e'.headD 0)
  | [], [] => by simp [zipPad, hg]
  | [], b :: e' => by simp [zipPad, hg']
  | a :: e, [] => by simp [zipPad, hg]
  | a :: e, b :: e' => by simp [zipPad]

theorem zipPad_nil_right (g : α → α → α) : ∀ as : List α, zipPad g as [] = as
  | [] => rfl
  | _ :: _ => rfl

theorem tail_zipPad (g : ℕ → ℕ → ℕ) :
    ∀ e e' : List ℕ, (zipPad g e e').tail = zipPad g e.tail e'.tail
  | [], e' => by simp [zipPad]
  | a :: e, [] => by simp [zipPad, zipPad_nil_right]
  | a :: e, b :: e' => by simp [zipPad]

end Lists

namespace DPoly

/-! ### Views

`DPoly 0` is `ℤ` and `DPoly (n + 1)` is `List (DPoly n)` by definition. The identity maps below
make the change of view explicit, so that statements stay well typed under rewriting. -/

/-- A constant, as a polynomial in no variables. -/
def ofInt (c : ℤ) : DPoly 0 := c

/-- The value of a polynomial in no variables. -/
def toInt (p : DPoly 0) : ℤ := p

/-- A list of coefficients in `x₀`, as a polynomial. -/
def ofList {n : ℕ} (ps : List (DPoly n)) : DPoly (n + 1) := ps

/-- The list of coefficients in `x₀`. -/
def toList {n : ℕ} (p : DPoly (n + 1)) : List (DPoly n) := p

@[simp] theorem toInt_ofInt (c : ℤ) : toInt (ofInt c) = c := rfl
@[simp] theorem ofInt_toInt (p : DPoly 0) : ofInt (toInt p) = p := rfl
@[simp] theorem toList_ofList {n : ℕ} (ps : List (DPoly n)) : toList (ofList ps) = ps := rfl
@[simp] theorem ofList_toList {n : ℕ} (p : DPoly (n + 1)) : ofList (toList p) = p := rfl

/-! ### Operations -/

/-- The zero polynomial. -/
def zero : (n : ℕ) → DPoly n
  | 0 => ofInt 0
  | _ + 1 => ofList []

/-- The constant polynomial `c`. -/
def const : (n : ℕ) → ℤ → DPoly n
  | 0, c => ofInt c
  | n + 1, c => ofList [const n c]

/-- Sum of polynomials. -/
def add : (n : ℕ) → DPoly n → DPoly n → DPoly n
  | 0, p, q => ofInt (toInt p + toInt q)
  | n + 1, p, q => ofList (zipPad (add n) (toList p) (toList q))

/-- The constant multiple `c • p`. -/
def smul : (n : ℕ) → ℤ → DPoly n → DPoly n
  | 0, c, p => ofInt (c * toInt p)
  | n + 1, c, p => ofList ((toList p).map (smul n c))

/-- Product of polynomials. -/
def mul : (n : ℕ) → DPoly n → DPoly n → DPoly n
  | 0, p, q => ofInt (toInt p * toInt q)
  | n + 1, p, q => ofList (mulList (zero n) (add n) (mul n) (toList p) (toList q))

/-- The polynomial `C + H xᵢ` (the constant `C` if `i ≥ n`). -/
def linear : (n : ℕ) → ℕ → ℤ → ℤ → DPoly n
  | 0, _, C, _ => ofInt C
  | n + 1, 0, C, H => ofList [const n C, const n H]
  | n + 1, i + 1, C, H => ofList [linear n i C H]

variable {R : Type*} [CommRing R]

/-- Evaluation at a point `x` of a commutative ring. -/
def eval : (n : ℕ) → DPoly n → (Fin n → R) → R
  | 0, p, _ => (toInt p : R)
  | n + 1, p, x => horner (fun q ↦ eval n q (Fin.tail x)) (x 0) (toList p)

@[simp] theorem eval_ofInt (c : ℤ) (x : Fin 0 → R) : eval 0 (ofInt c) x = c := rfl

@[simp] theorem eval_ofList {n : ℕ} (ps : List (DPoly n)) (x : Fin (n + 1) → R) :
    eval (n + 1) (ofList ps) x = horner (fun q ↦ eval n q (Fin.tail x)) (x 0) ps := rfl

@[simp] theorem eval_zero (n : ℕ) (x : Fin n → R) : eval n (zero n) x = 0 := by
  cases n <;> simp [zero]

@[simp] theorem eval_const : ∀ (n : ℕ) (c : ℤ) (x : Fin n → R), eval n (const n c) x = c
  | 0, c, x => rfl
  | n + 1, c, x => by simp [const, eval_const n]

@[simp] theorem eval_add : ∀ (n : ℕ) (p q : DPoly n) (x : Fin n → R),
    eval n (add n p q) x = eval n p x + eval n q x
  | 0, p, q, _ => Int.cast_add (R := R) (toInt p) (toInt q)
  | n + 1, p, q, x => horner_zipPad (fun a b ↦ eval_add n a b (Fin.tail x)) (toList p) (toList q)

@[simp] theorem eval_smul : ∀ (n : ℕ) (c : ℤ) (p : DPoly n) (x : Fin n → R),
    eval n (smul n c p) x = c * eval n p x
  | 0, c, p, _ => Int.cast_mul (α := R) c (toInt p)
  | n + 1, c, p, x => horner_map (fun a ↦ eval_smul n c a (Fin.tail x)) (toList p)

@[simp] theorem eval_mul : ∀ (n : ℕ) (p q : DPoly n) (x : Fin n → R),
    eval n (mul n p q) x = eval n p x * eval n q x
  | 0, p, q, _ => Int.cast_mul (α := R) (toInt p) (toInt q)
  | n + 1, p, q, x => horner_mulList (f := fun p ↦ eval n p (Fin.tail x)) (eval_zero n _)
      (fun a b ↦ eval_add n a b (Fin.tail x)) (fun a b ↦ eval_mul n a b (Fin.tail x))
      (toList p) (toList q)

theorem eval_linear : ∀ (n i : ℕ) (C H : ℤ) (x : Fin n → R),
    eval n (linear n i C H) x = if h : i < n then C + H * x ⟨i, h⟩ else (C : R)
  | 0, i, C, H, x => by simp [linear]
  | n + 1, 0, C, H, x => by simp [linear]; ring
  | n + 1, i + 1, C, H, x => by
    simp only [linear, eval_ofList, horner_cons, horner_nil, mul_zero, add_zero, eval_linear n i]
    by_cases h : i < n
    · simp [h, Fin.tail]
    · simp [h]

/-! ### Shapes -/

/-- `Fits n p e`: for each `i`, the degree of `p` in `xᵢ` is at most `e[i]` (missing entries
count as `0`). -/
def Fits : (n : ℕ) → DPoly n → List ℕ → Prop
  | 0, _, _ => True
  | n + 1, p, e => (toList p).length ≤ e.headD 0 + 1 ∧ ∀ q ∈ toList p, Fits n q e.tail

/-- `ShapeLE e e'`: the shape `e` is pointwise at most `e'` (missing entries count as `0`). -/
def ShapeLE : List ℕ → List ℕ → Prop
  | [], _ => True
  | a :: e, e' => a ≤ e'.headD 0 ∧ ShapeLE e e'.tail

theorem ShapeLE.refl : ∀ e : List ℕ, ShapeLE e e
  | [] => trivial
  | a :: e => ⟨le_refl a, ShapeLE.refl e⟩

theorem ShapeLE.headD_le : ∀ {e e' : List ℕ}, ShapeLE e e' → e.headD 0 ≤ e'.headD 0
  | [], _, _ => Nat.zero_le _
  | _ :: _, _, h => h.1

theorem ShapeLE.tail : ∀ {e e' : List ℕ}, ShapeLE e e' → ShapeLE e.tail e'.tail
  | [], _, _ => trivial
  | _ :: _, _, h => h.2

theorem ShapeLE.zipPad_max_left : ∀ e e' : List ℕ, ShapeLE e (zipPad max e e')
  | [], _ => trivial
  | _ :: _, [] => ShapeLE.refl _
  | a :: e, b :: e' => ⟨le_max_left a b, ShapeLE.zipPad_max_left e e'⟩

theorem ShapeLE.zipPad_max_right : ∀ e e' : List ℕ, ShapeLE e' (zipPad max e e')
  | _, [] => trivial
  | [], _ :: _ => ShapeLE.refl _
  | a :: e, b :: e' => ⟨le_max_right a b, ShapeLE.zipPad_max_right e e'⟩

theorem fits_mono : ∀ (n : ℕ) {p : DPoly n} {e e' : List ℕ}, ShapeLE e e' → Fits n p e →
    Fits n p e'
  | 0, _, _, _, _, _ => trivial
  | n + 1, _, _, _, hee, ⟨hlen, hp⟩ =>
    ⟨hlen.trans (Nat.add_le_add_right hee.headD_le 1), fun q hq ↦ fits_mono n hee.tail (hp q hq)⟩

theorem fits_zero : ∀ (n : ℕ) (e : List ℕ), Fits n (zero n) e
  | 0, _ => trivial
  | _ + 1, _ => ⟨by simp [zero], by simp [zero]⟩

theorem fits_const : ∀ (n : ℕ) (c : ℤ) (e : List ℕ), Fits n (const n c) e
  | 0, _, _ => trivial
  | n + 1, c, e => ⟨by simp [const], by simp [const, fits_const n c e.tail]⟩

theorem fits_add : ∀ (n : ℕ) {p q : DPoly n} {e e' : List ℕ}, Fits n p e → Fits n q e' →
    Fits n (add n p q) (zipPad max e e')
  | 0, _, _, _, _, _, _ => trivial
  | n + 1, p, q, e, e', ⟨hlp, hp⟩, ⟨hlq, hq⟩ => by
    refine ⟨?_, fun r hr ↦ ?_⟩
    · simp only [add, toList_ofList, length_zipPad]
      rw [headD_zipPad max (fun a ↦ by simp) (fun b ↦ by simp)]
      omega
    · rw [tail_zipPad]
      simp only [add, toList_ofList] at hr
      rcases mem_zipPad hr with ⟨a, ha, b, hb, rfl⟩ | h | h
      · exact fits_add n (hp a ha) (hq b hb)
      · exact fits_mono n (ShapeLE.zipPad_max_left _ _) (hp r h)
      · exact fits_mono n (ShapeLE.zipPad_max_right _ _) (hq r h)

theorem fits_smul : ∀ (n : ℕ) (c : ℤ) {p : DPoly n} {e : List ℕ}, Fits n p e →
    Fits n (smul n c p) e
  | 0, _, _, _, _ => trivial
  | n + 1, c, p, e, ⟨hl, hp⟩ => by
    refine ⟨by simpa [smul] using hl, fun r hr ↦ ?_⟩
    simp only [smul, toList_ofList] at hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    exact fits_smul n c (hp a ha)

theorem fits_mul : ∀ (n : ℕ) {p q : DPoly n} {e e' : List ℕ}, Fits n p e → Fits n q e' →
    Fits n (mul n p q) (zipPad (· + ·) e e')
  | 0, _, _, _, _, _, _ => trivial
  | n + 1, p, q, e, e', ⟨hlp, hp⟩, ⟨hlq, hq⟩ => by
    have hhead := headD_zipPad (· + ·) (fun a ↦ Nat.add_zero a) (fun b ↦ Nat.zero_add b) e e'
    refine ⟨?_, ?_⟩
    · simp only [mul, toList_ofList]
      have := length_mulList (zero n) (add n) (mul n) (toList p) (toList q)
      rw [hhead]
      omega
    · rw [tail_zipPad]
      simp only [mul, toList_ofList]
      exact mem_mulList hq (toList p) hp
where
  /-- Every entry of a product list fits the sum of the shapes. -/
  mem_mulList {n : ℕ} {e e' : List ℕ} {qs : List (DPoly n)} (hq : ∀ q ∈ qs, Fits n q e'.tail) :
      ∀ ps : List (DPoly n), (∀ p ∈ ps, Fits n p e.tail) →
      ∀ r ∈ mulList (zero n) (add n) (mul n) ps qs, Fits n r (zipPad (· + ·) e.tail e'.tail)
    | [], _, r, hr => by simp [mulList] at hr
    | a :: as, hp, r, hr => by
      have hmul : ∀ b ∈ qs, Fits n (mul n a b) (zipPad (· + ·) e.tail e'.tail) :=
        fun b hb ↦ fits_mul n (hp a List.mem_cons_self) (hq b hb)
      have hrest : ∀ r ∈ zero n :: mulList (zero n) (add n) (mul n) as qs,
          Fits n r (zipPad (· + ·) e.tail e'.tail) := by
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact fits_zero n _
        · exact mem_mulList hq as (fun p hp' ↦ hp p (List.mem_cons_of_mem _ hp')) r hr
      rcases mem_zipPad hr with ⟨x, hx, y, hy, rfl⟩ | h | h
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
        have := fits_add n (hmul b hb) (hrest y hy)
        rwa [zipPad_self_max] at this
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
        exact hmul b hb
      · exact hrest r h

theorem fits_linear : ∀ (n i : ℕ) (C H : ℤ),
    Fits n (linear n i C H) ((List.replicate i 0) ++ [1])
  | 0, _, _, _ => trivial
  | n + 1, 0, C, H => ⟨by simp [linear], by simp [linear, fits_const]⟩
  | n + 1, i + 1, C, H => ⟨by simp [linear], by simpa [linear] using fits_linear n i C H⟩

/-! ### Coefficient bounds -/

/-- `AllCoeff n P p`: every coefficient of `p` satisfies `P`. -/
def AllCoeff : (n : ℕ) → (ℤ → Prop) → DPoly n → Prop
  | 0, P, p => P (toInt p)
  | n + 1, P, p => ∀ q ∈ toList p, AllCoeff n P q

theorem allCoeff_mono : ∀ (n : ℕ) {P Q : ℤ → Prop}, (∀ c, P c → Q c) → ∀ {p : DPoly n},
    AllCoeff n P p → AllCoeff n Q p
  | 0, _, _, hPQ, _, h => hPQ _ h
  | n + 1, _, _, hPQ, _, h => fun q hq ↦ allCoeff_mono n hPQ (h q hq)

theorem allCoeff_zero (P : ℤ → Prop) (h : P 0) : ∀ n : ℕ, AllCoeff n P (zero n)
  | 0 => h
  | _ + 1 => fun _ hq ↦ by simp [zero] at hq

/-- The sum of the absolute values of the coefficients. -/
def absSum : (n : ℕ) → DPoly n → ℕ
  | 0, p => (toInt p).natAbs
  | n + 1, p => ((toList p).map (absSum n)).sum

theorem allCoeff_absSum_le : ∀ (n : ℕ) (p : DPoly n),
    AllCoeff n (fun c ↦ c.natAbs ≤ absSum n p) p
  | 0, _ => le_refl _
  | n + 1, p => fun q hq ↦ by
    have hle : absSum n q ≤ ((toList p).map (absSum n)).sum :=
      List.le_sum_of_mem (List.mem_map_of_mem hq)
    exact allCoeff_mono n (fun c hc ↦ hc.trans hle) (allCoeff_absSum_le n q)

theorem absSum_zero : ∀ n : ℕ, absSum n (zero n) = 0
  | 0 => rfl
  | _ + 1 => rfl

theorem absSum_const : ∀ (n : ℕ) (c : ℤ), absSum n (const n c) = c.natAbs
  | 0, _ => rfl
  | n + 1, c => by simp [absSum, const, absSum_const n c]

theorem absSum_add_le : ∀ (n : ℕ) (p q : DPoly n), absSum n (add n p q) ≤ absSum n p + absSum n q
  | 0, p, q => Int.natAbs_add_le (toInt p) (toInt q)
  | n + 1, p, q => go (toList p) (toList q)
where
  go {n : ℕ} : ∀ ps qs : List (DPoly n),
      ((zipPad (add n) ps qs).map (absSum n)).sum ≤ (ps.map (absSum n)).sum +
        (qs.map (absSum n)).sum
    | [], qs => by simp [zipPad]
    | a :: as, [] => by simp [zipPad]
    | a :: as, b :: bs => by
      have h₁ := absSum_add_le n a b
      have h₂ := go as bs
      simp only [zipPad, List.map_cons, List.sum_cons]
      omega

theorem absSum_smul : ∀ (n : ℕ) (c : ℤ) (p : DPoly n),
    absSum n (smul n c p) = c.natAbs * absSum n p
  | 0, c, p => Int.natAbs_mul c (toInt p)
  | n + 1, c, p => by
    simp only [absSum, smul, toList_ofList, List.map_map, Function.comp_def, absSum_smul n c]
    exact List.sum_map_mul_left (l := toList p) (f := absSum n) (r := c.natAbs)

theorem absSum_mul_le : ∀ (n : ℕ) (p q : DPoly n), absSum n (mul n p q) ≤ absSum n p * absSum n q
  | 0, p, q => (Int.natAbs_mul (toInt p) (toInt q)).le
  | n + 1, p, q => go (toList p) (toList q)
where
  go {n : ℕ} : ∀ ps qs : List (DPoly n),
      ((mulList (zero n) (add n) (mul n) ps qs).map (absSum n)).sum ≤
        (ps.map (absSum n)).sum * (qs.map (absSum n)).sum
    | [], qs => by simp [mulList]
    | a :: as, qs => by
      have h₁ := absSum_add_le.go (qs.map (mul n a))
        (zero n :: mulList (zero n) (add n) (mul n) as qs)
      have h₂ : ((qs.map (mul n a)).map (absSum n)).sum ≤
          absSum n a * (qs.map (absSum n)).sum := by
        rw [List.map_map, ← List.sum_map_mul_left]
        exact List.sum_le_sum fun b _ ↦ absSum_mul_le n a b
      have h₃ := go as qs
      simp only [mulList, List.map_cons, List.sum_cons, absSum_zero, zero_add] at h₁ ⊢
      calc _ ≤ _ := h₁
        _ ≤ absSum n a * (qs.map (absSum n)).sum + (as.map (absSum n)).sum *
            (qs.map (absSum n)).sum := Nat.add_le_add h₂ h₃
        _ = _ := by ring

theorem absSum_linear_le : ∀ (n i : ℕ) (C H : ℤ),
    absSum n (linear n i C H) ≤ C.natAbs + H.natAbs
  | 0, _, _, _ => Nat.le_add_right _ _
  | n + 1, 0, C, H => by simp [absSum, linear, absSum_const]
  | n + 1, i + 1, C, H => by simpa [absSum, linear] using absSum_linear_le n i C H

end DPoly

end Nieuwland.Check
