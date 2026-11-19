import Modules.Check.Sign.Pull
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Vertices of boxes under polynomial maps

Premises of zoom pieces concern the image of a parameter box under a polynomial map, not a box.
A linear function of the image attains its minimum over the box at a vertex when the map is
*multilinear in monotone powers*: along each coordinate `i` it is `α + β xᵢ ^ eᵢ` with one
exponent `eᵢ`, and `xᵢ ↦ xᵢ ^ eᵢ` is monotone on the range of `xᵢ` (`eᵢ = 1`, or the range is
nonnegative). Then checks at the images of the vertices hold on the whole image, as
`view_points` in `code/src/proof/regional/wzoom.rs` uses.

* `exists_vertex_le`: if along every coordinate a function is at least its value at one end of
  the range (`CoordMin`), it is at least its value at some vertex. Coordinates on which it does
  not depend, or whose range is a point, stay at the lower end, so only the *active* coordinates
  need both ends.
* Exponent profiles: `AlongPoly f i m` says that along coordinate `i`, `f` is a polynomial whose
  exponents are the bits of the mask `m`. Profiles (`Prof`, one mask per coordinate) are computed
  by running a generic computation on masks (`GenPoly.prof`): sums take unions, products take sums
  of exponents (`sumset`). Running it on functions paired with their profiles (`ProfFun`) proves
  that the computed profile is one of the real function (`GenPoly.alongPoly_prof`).
* `slotOk`, `coordMin_of_slotOk`: a mask with at most one nonzero exponent, which is `1` unless
  the range is nonnegative, gives `CoordMin`.
* `vertices`: the vertices of a box over its active coordinates, for the kernel
  (`mem_vertices`).
-/

namespace Nieuwland.Check

/-! ### Minima at vertices -/

section VertexMin

variable {n : ℕ}

/-- Along coordinate `i`, on `[lo, hi]`, the function `f` is at least its value at `lo`, or (if
`act`) at `hi`. -/
def CoordMin (f : (Fin n → ℝ) → ℝ) (lo hi : ℝ) (i : Fin n) (act : Bool) : Prop :=
  ∀ y : Fin n → ℝ, ∀ x, lo ≤ x → x ≤ hi →
    f (Function.update y i lo) ≤ f (Function.update y i x) ∨
      (act = true ∧ f (Function.update y i hi) ≤ f (Function.update y i x))

/-- **Minima at vertices.** If along every coordinate `f` is at least its value at one end of
the range, then at every point of the box it is at least its value at a vertex, whose inactive
coordinates are at their lower ends. -/
theorem exists_vertex_le (f : (Fin n → ℝ) → ℝ) (lo hi : Fin n → ℝ) (act : Fin n → Bool)
    (hf : ∀ i, CoordMin f (lo i) (hi i) i (act i)) (y : Fin n → ℝ)
    (hy : ∀ i, lo i ≤ y i ∧ y i ≤ hi i) :
    ∃ v : Fin n → ℝ, (∀ i, v i = lo i ∨ (act i = true ∧ v i = hi i)) ∧ f v ≤ f y := by
  classical
  -- Move the coordinates of `T` to the ends, one at a time.
  have key : ∀ T : Finset (Fin n), ∃ v : Fin n → ℝ,
      (∀ i ∈ T, v i = lo i ∨ (act i = true ∧ v i = hi i)) ∧ (∀ i ∉ T, v i = y i) ∧ f v ≤ f y := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨y, by simp, fun _ _ ↦ rfl, le_rfl⟩
    | insert j T hj ih =>
      obtain ⟨v, hT, hout, hle⟩ := ih
      have hvj : v j = y j := hout j hj
      have hv : Function.update v j (v j) = v := Function.update_eq_self j v
      rcases hf j v (v j) (hvj ▸ (hy j).1) (hvj ▸ (hy j).2) with h | ⟨ha, h⟩
      · refine ⟨Function.update v j (lo j), fun i hi ↦ ?_, fun i hi ↦ ?_, ?_⟩
        · rcases Finset.mem_insert.mp hi with rfl | hi
          · left; simp
          · rw [Function.update_of_ne (fun h : i = j ↦ hj (h ▸ hi))]; exact hT i hi
        · rw [Function.update_of_ne (fun h : i = j ↦ hi (h ▸ Finset.mem_insert_self j T))]
          exact hout i fun h ↦ hi (Finset.mem_insert_of_mem h)
        · rw [hv] at h; exact h.trans hle
      · refine ⟨Function.update v j (hi j), fun i hi ↦ ?_, fun i hi ↦ ?_, ?_⟩
        · rcases Finset.mem_insert.mp hi with rfl | hi
          · right; simp [ha]
          · rw [Function.update_of_ne (fun h : i = j ↦ hj (h ▸ hi))]; exact hT i hi
        · rw [Function.update_of_ne (fun h : i = j ↦ hi (h ▸ Finset.mem_insert_self j T))]
          exact hout i fun h ↦ hi (Finset.mem_insert_of_mem h)
        · rw [hv] at h; exact h.trans hle
  obtain ⟨v, hv, -, hle⟩ := key Finset.univ
  exact ⟨v, fun i ↦ hv i (Finset.mem_univ i), hle⟩

end VertexMin

/-! ### Exponent masks -/

/-- The mask of `{a + b | a ∈ A, b ∈ B}`, for masks `A`, `B` (bit `a` for exponent `a`). -/
def sumset (A B : ℕ) : ℕ :=
  (List.range (A.log2 + 1)).foldr (fun a acc ↦ if A.testBit a then (B <<< a) ||| acc else acc) 0

theorem testBit_foldr_sumset {A B a b : ℕ} (ha : A.testBit a = true) (hb : B.testBit b = true) :
    ∀ l : List ℕ, a ∈ l → (l.foldr (fun a acc ↦ if A.testBit a then (B <<< a) ||| acc else acc)
      0).testBit (a + b) = true
  | x :: l, hx => by
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [ha, Nat.testBit_shiftLeft, hb]
    · have := testBit_foldr_sumset ha hb l hx
      split_ifs
      · rw [Nat.testBit_or, this, Bool.or_true]
      · exact this

theorem testBit_sumset {A B a b : ℕ} (ha : A.testBit a = true) (hb : B.testBit b = true) :
    (sumset A B).testBit (a + b) = true := by
  have hA : A ≠ 0 := by rintro rfl; simp at ha
  have hlt : a < A.log2 + 1 :=
    Nat.lt_succ_of_le ((Nat.le_log2 hA).mpr (Nat.ge_two_pow_of_testBit ha))
  exact testBit_foldr_sumset ha hb _ (List.mem_range.mpr hlt)

/-! ### Polynomials along a coordinate -/

section Along

open Polynomial

variable {n : ℕ}

/-- Along coordinate `i`, the function `f` is a polynomial whose exponents are bits of `m`. -/
def AlongPoly (f : (Fin n → ℝ) → ℝ) (i : Fin n) (m : ℕ) : Prop :=
  ∀ y : Fin n → ℝ, ∃ p : ℝ[X], (∀ a, p.coeff a ≠ 0 → m.testBit a = true) ∧
    ∀ x, f (Function.update y i x) = p.eval x

namespace AlongPoly

variable {f g : (Fin n → ℝ) → ℝ} {i : Fin n} {m m' : ℕ}

theorem const (c : ℝ) (hm : c ≠ 0 → m.testBit 0 = true) : AlongPoly (fun _ ↦ c) i m :=
  fun _ ↦ ⟨C c, fun a ha ↦ by
    rw [coeff_C] at ha
    split_ifs at ha with h
    · subst h; exact hm ha
    · exact absurd rfl ha, fun _ ↦ by simp⟩

theorem var_self : AlongPoly (fun x ↦ x i) i 2 :=
  fun _ ↦ ⟨X, fun a ha ↦ by
    rw [coeff_X] at ha
    split_ifs at ha with h
    · subst h; rfl
    · exact absurd rfl ha, fun _ ↦ by simp⟩

theorem var_ne {j : Fin n} (h : j ≠ i) : AlongPoly (fun x ↦ x j) i 1 :=
  fun y ↦ ⟨C (y j), fun a ha ↦ by
    rw [coeff_C] at ha
    split_ifs at ha with h'
    · subst h'; rfl
    · exact absurd rfl ha, fun _ ↦ by simp [Function.update_of_ne h]⟩

theorem mono (hf : AlongPoly f i m) (hm : ∀ a, m.testBit a = true → m'.testBit a = true) :
    AlongPoly f i m' := fun y ↦ by
  obtain ⟨p, hp, hfp⟩ := hf y
  exact ⟨p, fun a ha ↦ hm a (hp a ha), hfp⟩

theorem add (hf : AlongPoly f i m) (hg : AlongPoly g i m') :
    AlongPoly (fun x ↦ f x + g x) i (m ||| m') := fun y ↦ by
  obtain ⟨p, hp, hfp⟩ := hf y
  obtain ⟨q, hq, hgq⟩ := hg y
  refine ⟨p + q, fun a ha ↦ ?_, fun x ↦ by simp [hfp, hgq]⟩
  rw [coeff_add] at ha
  rw [Nat.testBit_or, Bool.or_eq_true]
  by_cases h₁ : p.coeff a = 0
  · right; exact hq a (by rwa [h₁, zero_add] at ha)
  · left; exact hp a h₁

theorem sub (hf : AlongPoly f i m) (hg : AlongPoly g i m') :
    AlongPoly (fun x ↦ f x - g x) i (m ||| m') := fun y ↦ by
  obtain ⟨p, hp, hfp⟩ := hf y
  obtain ⟨q, hq, hgq⟩ := hg y
  refine ⟨p - q, fun a ha ↦ ?_, fun x ↦ by simp [hfp, hgq]⟩
  rw [coeff_sub] at ha
  rw [Nat.testBit_or, Bool.or_eq_true]
  by_cases h₁ : p.coeff a = 0
  · right; exact hq a (fun h₂ ↦ ha (by rw [h₁, h₂, sub_zero]))
  · left; exact hp a h₁

theorem mul (hf : AlongPoly f i m) (hg : AlongPoly g i m') :
    AlongPoly (fun x ↦ f x * g x) i (sumset m m') := fun y ↦ by
  obtain ⟨p, hp, hfp⟩ := hf y
  obtain ⟨q, hq, hgq⟩ := hg y
  refine ⟨p * q, fun c hc ↦ ?_, fun x ↦ by simp [hfp, hgq]⟩
  rw [coeff_mul] at hc
  obtain ⟨⟨a, b⟩, hab, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  rw [Finset.mem_antidiagonal] at hab
  subst hab
  exact testBit_sumset (hp a (left_ne_zero_of_mul hne)) (hq b (right_ne_zero_of_mul hne))

/-- A polynomial whose nonzero exponents are all `e` is affine in the `e`-th power. -/
theorem eval_eq_of_coeff {p : ℝ[X]} {e : ℕ} (he : e ≠ 0) (h : ∀ a, p.coeff a ≠ 0 → a = 0 ∨ a = e)
    (x : ℝ) : p.eval x = p.coeff 0 + p.coeff e * x ^ e := by
  rw [eval_eq_sum_range' (n := max (p.natDegree + 1) (e + 1)) (by omega)]
  rw [Finset.sum_eq_add 0 e (Ne.symm he)]
  · simp
  · intro c _ hc
    by_contra h'
    rcases h c (left_ne_zero_of_mul h') with h'' | h''
    · exact hc.1 h''
    · exact hc.2 h''
  · intro h'; exact absurd (Finset.mem_range.mpr (by omega)) h'
  · intro h'; exact absurd (Finset.mem_range.mpr (by omega)) h'

/-- A polynomial whose only possible exponent is `0` is constant. -/
theorem eval_eq_of_coeff_zero {p : ℝ[X]} (h : ∀ a, p.coeff a ≠ 0 → a = 0) (x : ℝ) :
    p.eval x = p.coeff 0 := by
  rw [eval_eq_sum_range' (n := p.natDegree + 1) (by omega), Finset.sum_eq_single 0]
  · simp
  · intro c _ hc
    by_contra h'
    exact hc (h c (left_ne_zero_of_mul h'))
  · intro h'; exact absurd (Finset.mem_range.mpr (by omega)) h'

end AlongPoly

end Along

/-! ### Single exponents -/

/-- The mask `m` has at most one nonzero exponent (its top bit), which is `1` unless `0 ≤ lo`;
or the range `[lo, hi]` is a point. -/
def slotOk (m : ℕ) (lo hi : ℤ) : Bool :=
  lo == hi || (m ||| 1 == 2 ^ m.log2 ||| 1 && (m.log2 ≤ 1 || 0 ≤ lo))

/-- The range is not a point and the mask has a nonzero exponent: the vertices need both ends. -/
def slotAct (m : ℕ) (lo hi : ℤ) : Bool :=
  lo != hi && 2 ≤ m

theorem testBit_of_single {m a : ℕ} (h : m ||| 1 = 2 ^ m.log2 ||| 1) (ha : m.testBit a = true) :
    a = 0 ∨ a = m.log2 := by
  have h1 := congrArg (Nat.testBit · a) h
  simp only [Nat.testBit_or, ha, Bool.true_or, Nat.testBit_two_pow] at h1
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · exact Or.inl h0
  · right
    have h1' : (1 : ℕ).testBit a = false := by
      rw [show (1 : ℕ) = 2 ^ 0 from rfl, Nat.testBit_two_pow]
      simp [hpos.ne]
    rw [h1', Bool.or_false] at h1
    exact (of_decide_eq_true h1.symm).symm

theorem two_le_of_log2_pos {m : ℕ} (h : 0 < m.log2) : 2 ≤ m := by
  by_contra h'
  rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl <;> exact absurd h (by decide)

/-- **Single exponents give minima at the ends.** -/
theorem coordMin_of_slotOk {n : ℕ} {f : (Fin n → ℝ) → ℝ} {i : Fin n} {m : ℕ} {lo hi : ℤ}
    {d : ℕ} (hd : 0 < d) (hm : slotOk m lo hi = true) (hf : AlongPoly f i m) :
    CoordMin f ((lo : ℝ) / d) ((hi : ℝ) / d) i (slotAct m lo hi) := by
  intro y x hlo hhi
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  by_cases heq : lo = hi
  · left
    subst heq
    rw [le_antisymm hhi hlo]
  simp only [slotOk, heq, beq_iff_eq, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    false_or] at hm
  obtain ⟨hs, hpos⟩ := hm
  obtain ⟨p, hp, hfp⟩ := hf y
  have hsupp : ∀ a, p.coeff a ≠ 0 → a = 0 ∨ a = m.log2 := fun a ha ↦ testBit_of_single hs (hp a ha)
  rcases Nat.eq_zero_or_pos m.log2 with he | he
  · -- Constant along `i`.
    left
    have hc : ∀ a, p.coeff a ≠ 0 → a = 0 := fun a ha ↦ by
      rcases hsupp a ha with h | h
      · exact h
      · exact h.trans he
    rw [hfp, hfp, AlongPoly.eval_eq_of_coeff_zero hc, AlongPoly.eval_eq_of_coeff_zero hc]
  · -- `α + β x ^ e` with `x ↦ x ^ e` monotone on the range.
    have hmono : ((lo : ℝ) / d) ^ m.log2 ≤ x ^ m.log2 ∧ x ^ m.log2 ≤ ((hi : ℝ) / d) ^ m.log2 := by
      rcases hpos with h1 | h0
      · have he1 : m.log2 = 1 := by omega
        rw [he1, pow_one, pow_one, pow_one]
        exact ⟨hlo, hhi⟩
      · have h0' : (0 : ℝ) ≤ (lo : ℝ) / d := div_nonneg (by exact_mod_cast h0) hd'.le
        exact ⟨pow_le_pow_left₀ h0' hlo _, pow_le_pow_left₀ (h0'.trans hlo) hhi _⟩
    rw [hfp, hfp, hfp, AlongPoly.eval_eq_of_coeff he.ne' hsupp,
      AlongPoly.eval_eq_of_coeff he.ne' hsupp, AlongPoly.eval_eq_of_coeff he.ne' hsupp]
    rcases le_total 0 (p.coeff m.log2) with hβ | hβ
    · left
      nlinarith [mul_le_mul_of_nonneg_left hmono.1 hβ]
    · right
      refine ⟨?_, by nlinarith [mul_le_mul_of_nonpos_left hmono.2 hβ]⟩
      simp [slotAct, heq, two_le_of_log2_pos he]

/-! ### Exponent profiles -/

theorem sumset_zero_left (B : ℕ) : sumset 0 B = 0 := by
  simp [sumset]

theorem sumset_zero_right (A : ℕ) : sumset A 0 = 0 := by
  unfold sumset
  generalize List.range (A.log2 + 1) = l
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.foldr_cons, ih]; simp

theorem getD_zipPad_or : ∀ (l₁ l₂ : List ℕ) (i : ℕ),
    (zipPad (· ||| ·) l₁ l₂).getD i 0 = l₁.getD i 0 ||| l₂.getD i 0
  | [], l₂, i => by simp [zipPad]
  | a :: l₁, [], i => by simp [zipPad]
  | a :: l₁, b :: l₂, 0 => rfl
  | a :: l₁, b :: l₂, i + 1 => getD_zipPad_or l₁ l₂ i

theorem getD_zipWith_sumset : ∀ (l₁ l₂ : List ℕ) (i : ℕ),
    (List.zipWith sumset l₁ l₂).getD i 0 = sumset (l₁.getD i 0) (l₂.getD i 0)
  | [], l₂, i => by simp [sumset_zero_left]
  | a :: l₁, [], i => by simp [sumset_zero_right]
  | a :: l₁, b :: l₂, 0 => rfl
  | a :: l₁, b :: l₂, i + 1 => getD_zipWith_sumset l₁ l₂ i

/-- An exponent profile: one mask per coordinate (`0` beyond the list). -/
structure Prof where
  /-- The masks. -/
  m : List ℕ

namespace Prof

instance : Add Prof := ⟨fun P Q ↦ ⟨zipPad (· ||| ·) P.m Q.m⟩⟩
instance : Sub Prof := ⟨fun P Q ↦ ⟨zipPad (· ||| ·) P.m Q.m⟩⟩
instance : Mul Prof := ⟨fun P Q ↦ ⟨List.zipWith sumset P.m Q.m⟩⟩

/-- The profile of the constant `c` in `n` variables: empty where `c` is known to be zero. -/
def const {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] (n : ℕ) (c : κ) : Prof :=
  ⟨if Exact.isZero c then [] else List.replicate n 1⟩

/-- The profile of variable `j` in `n` variables (the zero function if `j ≥ n`). -/
def var (n j : ℕ) : Prof :=
  ⟨if j < n then (List.range n).map fun i ↦ if i = j then 2 else 1 else []⟩

end Prof

/-- A function of `n` real variables with an exponent profile. -/
structure ProfFun (n : ℕ) where
  /-- The function. -/
  f : (Fin n → ℝ) → ℝ
  /-- Its profile. -/
  P : Prof
  /-- Along each coordinate, the function is a polynomial with exponents in the profile. -/
  ok : ∀ i : Fin n, AlongPoly f i (P.m.getD i 0)

namespace ProfFun

variable {n : ℕ}

instance : Add (ProfFun n) := ⟨fun F G ↦ ⟨fun x ↦ F.f x + G.f x, F.P + G.P, fun i ↦ by
  change AlongPoly _ i ((zipPad _ F.P.m G.P.m).getD i 0)
  rw [getD_zipPad_or]
  exact (F.ok i).add (G.ok i)⟩⟩

instance : Sub (ProfFun n) := ⟨fun F G ↦ ⟨fun x ↦ F.f x - G.f x, F.P - G.P, fun i ↦ by
  change AlongPoly _ i ((zipPad _ F.P.m G.P.m).getD i 0)
  rw [getD_zipPad_or]
  exact (F.ok i).sub (G.ok i)⟩⟩

instance : Mul (ProfFun n) := ⟨fun F G ↦ ⟨fun x ↦ F.f x * G.f x, F.P * G.P, fun i ↦ by
  change AlongPoly _ i ((List.zipWith sumset F.P.m G.P.m).getD i 0)
  rw [getD_zipWith_sumset]
  exact (F.ok i).mul (G.ok i)⟩⟩

/-- The constant `c`. -/
noncomputable def const {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] (c : κ) : ProfFun n :=
  ⟨fun _ ↦ Exact.re c, Prof.const n c, fun i ↦ AlongPoly.const _ fun hc ↦ by
    have hc' : Exact.isZero c = false := by
      by_contra h
      exact hc (Exact.isZero_sound c (by simpa using h))
    simp [Prof.const, hc', List.getD_eq_getElem?_getD, i.2]⟩

/-- Variable `j` (the zero function if `j ≥ n`). -/
def var (j : ℕ) : ProfFun n :=
  ⟨fun x ↦ Pull.ext n x j, Prof.var n j, fun i ↦ by
    by_cases hj : j < n
    · have hx : (fun x : Fin n → ℝ ↦ Pull.ext n x j) = fun x ↦ x ⟨j, hj⟩ := by
        funext x
        simp [Pull.ext, hj]
      rw [hx]
      by_cases hij : (⟨j, hj⟩ : Fin n) = i
      · subst hij
        simpa [Prof.var, hj, List.getD_eq_getElem?_getD] using AlongPoly.var_self (i := ⟨j, hj⟩)
      · have hij' : (i : ℕ) ≠ j := fun h ↦ hij (Fin.ext h.symm)
        simpa [Prof.var, hj, List.getD_eq_getElem?_getD, hij'] using AlongPoly.var_ne hij
    · have hx : (fun x : Fin n → ℝ ↦ Pull.ext n x j) = fun _ ↦ 0 := by
        funext x
        simp [Pull.ext, hj]
      rw [hx]
      exact AlongPoly.const 0 fun h ↦ absurd rfl h⟩

theorem isArith_f : IsArith (fun F : ProfFun n ↦ F.f) :=
  ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

theorem isArith_eval (x : Fin n → ℝ) : IsArith (fun F : ProfFun n ↦ F.f x) :=
  ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

theorem isArith_P : IsArith (fun F : ProfFun n ↦ F.P) :=
  ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

end ProfFun

section Prof

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The exponent profile of a generic computation in `n` variables, computed on masks. -/
def GenPoly.prof (G : GenPoly κ) (n : ℕ) : Prof :=
  G.run (Prof.const n) (Prof.var n)

/-- **Profiles of computations.** Along every coordinate, a computation in `n` real variables
is a polynomial whose exponents are bits of its profile. -/
theorem GenPoly.alongPoly_prof (G : GenPoly κ) (n : ℕ) (i : Fin n) :
    AlongPoly (fun x ↦ G.run Exact.re (Pull.ext n x)) i ((G.prof n).m.getD i 0) := by
  have R := (G.run (ProfFun.const (n := n)) ProfFun.var).ok i
  have hP : (G.run (ProfFun.const (n := n)) ProfFun.var).P = G.prof n :=
    G.natural _ ProfFun.isArith_P _ _
  have hf : (G.run (ProfFun.const (n := n)) ProfFun.var).f =
      fun x ↦ G.run Exact.re (Pull.ext n x) := by
    funext x
    exact G.natural _ (ProfFun.isArith_eval x) _ _
  rw [hP, hf] at R
  exact R

end Prof

/-! ### Vertices for the kernel -/

/-- The vertices of a box with ends `lo`, `hi`: every slot at its lower end, and also at its
upper end where `act`. -/
def vertices : List ℤ → List ℤ → List Bool → List (List ℤ)
  | l :: ls, h :: hs, a :: as =>
    let r := vertices ls hs as
    r.map (l :: ·) ++ if a then r.map (h :: ·) else []
  | _, _, _ => [[]]

theorem mem_vertices : ∀ (lo hi : List ℤ) (act : List Bool) (L : List ℤ),
    hi.length = lo.length → act.length = lo.length → L.length = lo.length →
    (∀ i, L.getD i 0 = lo.getD i 0 ∨ (act.getD i false = true ∧ L.getD i 0 = hi.getD i 0)) →
    L ∈ vertices lo hi act
  | [], _, _, [], _, _, _, _ => by simp [vertices]
  | l :: ls, h :: hs, a :: as, x :: L, hh, ha, hL, hv => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hh ha hL
    have ih := mem_vertices ls hs as L hh ha hL fun i ↦ hv (i + 1)
    simp only [vertices, List.mem_append, List.mem_map]
    rcases hv 0 with h0 | ⟨ha0, h0⟩
    · exact Or.inl ⟨L, ih, by simp_all⟩
    · simp only [List.getD_cons_zero] at ha0 h0
      exact Or.inr (by simp only [ha0, ↓reduceIte, List.mem_map]; exact ⟨L, ih, by rw [h0]⟩)
  | [], _ :: _, _, _, hh, _, _, _ => by simp at hh
  | [], [], _ :: _, _, _, ha, _, _ => by simp at ha
  | [], [], [], _ :: _, _, _, hL, _ => by simp at hL
  | _ :: _, [], _, _, hh, _, _, _ => by simp at hh
  | _ :: _, _ :: _, [], _, _, ha, _, _ => by simp at ha
  | _ :: _, _ :: _, _ :: _, [], _, _, hL, _ => by simp at hL

/-- The vertices of the box `∏ [lo i, hi i]` of `n` slots, over the slots where `act`. -/
def boxVertices (n : ℕ) (lo hi : List ℤ) (act : List Bool) : List (List ℤ) :=
  vertices ((List.range n).map (lo.getD · 0)) ((List.range n).map (hi.getD · 0))
    ((List.range n).map (act.getD · false))

/-- **Minima at enumerated vertices.** If along every slot `f` is at least its value at one end
of the range (both ends for the slots where `act`), then at every point of the box `f` is at
least its value at one of `boxVertices`. -/
theorem exists_boxVertex_le {n : ℕ} (f : (Fin n → ℝ) → ℝ) (lo hi : List ℤ) {d : ℕ}
    (act : List Bool)
    (hf : ∀ i : Fin n, CoordMin f ((lo.getD i 0 : ℝ) / d) ((hi.getD i 0 : ℝ) / d) i
      (act.getD i false))
    (y : Fin n → ℝ) (hy : ∀ i : Fin n, (lo.getD i 0 : ℝ) / d ≤ y i ∧ y i ≤ (hi.getD i 0 : ℝ) / d) :
    ∃ L ∈ boxVertices n lo hi act, f (fun i ↦ (L.getD i 0 : ℝ) / d) ≤ f y := by
  classical
  obtain ⟨v, hv, hle⟩ := exists_vertex_le f _ _ _ hf y hy
  -- The numerators of the vertex.
  set L : List ℤ := (List.range n).map fun i ↦
    if h : i < n then (if act.getD i false = true ∧ v ⟨i, h⟩ = (hi.getD i 0 : ℝ) / d then
      hi.getD i 0 else lo.getD i 0) else 0 with hLdef
  have hLi' (i : ℕ) (hin : i < n) : L.getD i 0 = if act.getD i false = true ∧
      v ⟨i, hin⟩ = (hi.getD i 0 : ℝ) / d then hi.getD i 0 else lo.getD i 0 := by
    rw [hLdef, Box.getD_range_map n _ _ hin]
    simp only [hin, ↓reduceDIte]
  have hLi (i : Fin n) : L.getD i 0 = if act.getD i false = true ∧ v i = (hi.getD i 0 : ℝ) / d
      then hi.getD i 0 else lo.getD i 0 := hLi' i i.2
  refine ⟨L, mem_vertices _ _ _ _ (by simp) (by simp) (by simp [hLdef]) fun i ↦ ?_, ?_⟩
  · by_cases hin : i < n
    · rw [hLi' i hin, Box.getD_range_map n _ _ hin, Box.getD_range_map n _ _ hin,
        Box.getD_range_map n _ _ hin]
      split_ifs with h
      · exact Or.inr ⟨h.1, rfl⟩
      · exact Or.inl rfl
    · left
      rw [List.getD_eq_default _ _ (by simp [hLdef]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
  · convert hle using 2
    funext i
    rw [hLi i]
    split_ifs with h
    · exact h.2.symm
    · rcases hv i with h' | h'
      · exact h'.symm
      · exact absurd h' h

end Nieuwland.Check
