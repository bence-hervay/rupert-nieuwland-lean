import Modules.Check.Polynomial.Poly
import Mathlib.Tactic.Linarith

/-!
# Kronecker packing

A polynomial `p` in `n` variables whose degree in `xᵢ` is at most `eᵢ` and whose coefficients
are smaller than `2^(B-1)` in absolute value is determined by one integer, its value at the
*packing point* `xᵢ = 2^(B σᵢ)`, where `σᵢ = ∏_{j > i} (eⱼ + 1)`: after adding the *offset*, which
has the digit `2^(B-1)` in each of the `∏ (eᵢ + 1)` slots of `B` bits, the slots hold the
coefficients plus `2^(B-1)`, without carries. `DPoly.unpack` reads them back.

The kernel computes the packed value of a polynomial by evaluating it at the packing point with
big-integer arithmetic, and then only reads off digits (`Modules/Check/Sign/Bound.lean`).
`DPoly.eval_unpack` is the correctness statement: the unpacked polynomial has the same values as
`p` everywhere.
-/

namespace Nieuwland.Check

namespace DPoly

/-- The number of coefficient slots `∏ (eᵢ + 1)` of the shape `e`. -/
def slots : List ℕ → ℕ
  | [] => 1
  | a :: e => (a + 1) * slots e

theorem one_le_slots : ∀ e : List ℕ, 1 ≤ slots e
  | [] => le_refl 1
  | a :: e => Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.succ_ne_zero a)
      (Nat.one_le_iff_ne_zero.mp (one_le_slots e)))

theorem slots_eq (e : List ℕ) : slots e = (e.headD 0 + 1) * slots e.tail := by
  cases e <;> simp [slots]

/-- Coordinate `i` of the packing point for the shape `e` and digit size `B`:
`2^(B ∏_{j > i} (eⱼ + 1))` (`packPoint'_eq`), computed as a shift: the kernel refuses powers
whose result exceeds `2^24` bits, but not shifts. -/
def packPoint' (e : List ℕ) (B i : ℕ) : ℤ := ((1 <<< (B * slots (e.drop (i + 1))) : ℕ) : ℤ)

theorem packPoint'_eq (e : List ℕ) (B i : ℕ) :
    packPoint' e B i = 2 ^ (B * slots (e.drop (i + 1))) := by
  simp [packPoint', Nat.one_shiftLeft]

/-- The packing point for the shape `e` and digit size `B`: `xᵢ = 2^(B ∏_{j > i} (eⱼ + 1))`. -/
def packPoint (n : ℕ) (e : List ℕ) (B : ℕ) : Fin n → ℤ :=
  fun i ↦ packPoint' e B i

theorem packPoint_zero (n : ℕ) (e : List ℕ) (B : ℕ) :
    packPoint (n + 1) e B 0 = 2 ^ (B * slots e.tail) := by
  simp [packPoint, packPoint'_eq]

theorem tail_packPoint (n : ℕ) (e : List ℕ) (B : ℕ) :
    Fin.tail (packPoint (n + 1) e B) = packPoint n e.tail B := by
  funext i
  simp only [Fin.tail, packPoint, packPoint', Fin.val_succ, List.drop_tail]

/-! ### Compiled arithmetic with powers of two

Compiled code multiplies, divides and reduces big numbers by powers of two with general
multiplication and division, which on numerals of millions of bits is a hundred times slower than
a shift or a mask. `divP2` and `modP2` shift and mask where the divisor is a power of two
(`divP2_eq`, `modP2_eq`); the `@[csimp]` lemmas of the digit readers (`offset_eq_offsetS` here,
`dig_eq_digS`, `penaltyL_eq_penaltyLS`, `readK_eq_readKS`, `monosP_eq_monosPS`,
`vBest_eq_vBestS`, `best_eq_bestS`) and of the masks and offsets (`posN_eq_posNS`,
`negN_eq_negNS`, `absN_eq_absNS`, `maskSum_eq_maskSumS`, `offN_eq_offNS`, `subN_eq_subNS`,
`maskAt_eq_maskAtS`) prove versions that use them, or shifts for products with `2^k` and
`2^k - 1`, equal to the definitions, which proofs and the kernel keep using. -/

/-- `N / q`, by a shift when `q` is a power of two (`divP2_eq`). -/
def divP2 (N q : ℕ) : ℕ := bif Nat.beq q (1 <<< q.log2) then N >>> q.log2 else N / q

theorem divP2_eq (N q : ℕ) : divP2 N q = N / q := by
  unfold divP2
  cases h : Nat.beq q (1 <<< q.log2)
  · rfl
  · have hq : q = 2 ^ q.log2 := by rw [Nat.eq_of_beq_eq_true h, Nat.one_shiftLeft]; simp
    simp only [Bool.cond_true, Nat.shiftRight_eq_div_pow]
    rw [← hq]

/-- `N % q`, by a mask when `q` is a power of two (`modP2_eq`). -/
def modP2 (N q : ℕ) : ℕ := bif Nat.beq q (1 <<< q.log2) then N &&& (q - 1) else N % q

theorem modP2_eq (N q : ℕ) : modP2 N q = N % q := by
  unfold modP2
  cases h : Nat.beq q (1 <<< q.log2)
  · rfl
  · have hq : q = 2 ^ q.log2 := by rw [Nat.eq_of_beq_eq_true h, Nat.one_shiftLeft]; simp
    simp only [Bool.cond_true]
    rw [hq, Nat.and_two_pow_sub_one_eq_mod, ← hq]

/-- `a + z a + ⋯ + z^(m-1) a`. -/
def rep : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | m + 1, z, a => a + z * rep m z a

/-- `rep m (2^s) a`, by shifts (`rep_shiftLeft`). -/
def repS : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | m + 1, s, a => a + repS m s a <<< s

theorem rep_shiftLeft (s a : ℕ) : ∀ m, rep m (1 <<< s) a = repS m s a
  | 0 => rfl
  | m + 1 => by
    rw [rep, repS, rep_shiftLeft s a m, Nat.shiftLeft_eq, Nat.shiftLeft_eq, one_mul, Nat.mul_comm]

/-- The offset: the digit `2^(B-1)` in every slot of the shape `e`. -/
def offset : ℕ → List ℕ → ℕ → ℕ
  | 0, _, B => 2 ^ (B - 1)
  | n + 1, e, B => rep (e.headD 0 + 1) (1 <<< (B * slots e.tail)) (offset n e.tail B)

/-- `offset` by shifts. -/
def offsetS : ℕ → List ℕ → ℕ → ℕ
  | 0, _, B => 2 ^ (B - 1)
  | n + 1, e, B => repS (e.headD 0 + 1) (B * slots e.tail) (offsetS n e.tail B)

@[csimp] theorem offset_eq_offsetS : @offset = @offsetS := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih => funext e B; rw [offset, offsetS, rep_shiftLeft, ih]

theorem offset_zero (e : List ℕ) (B : ℕ) : offset 0 e B = 2 ^ (B - 1) := rfl

theorem offset_succ (n : ℕ) (e : List ℕ) (B : ℕ) :
    offset (n + 1) e B = rep (e.headD 0 + 1) (2 ^ (B * slots e.tail)) (offset n e.tail B) := by
  rw [offset, Nat.one_shiftLeft]

/-- `m` blocks of `w` bits of `N`, lowest first, each read by `f`. -/
def unpackL {α : Type*} (f : ℕ → α) (w : ℕ) : ℕ → ℕ → List α
  | 0, _ => []
  | m + 1, N => f (N % 2 ^ w) :: unpackL f w m (N / 2 ^ w)

/-- The polynomial whose coefficients, plus `2^(B-1)`, are the `B`-bit digits of `N`, laid out
in the slots of the shape `e`. -/
def unpack : (n : ℕ) → List ℕ → ℕ → ℕ → DPoly n
  | 0, _, B, N => ofInt (((N % 2 ^ B : ℕ) : ℤ) - 2 ^ (B - 1))
  | n + 1, e, B, N => ofList (unpackL (unpack n e.tail B) (B * slots e.tail) (e.headD 0 + 1) N)

/-! ### Lists of blocks -/

theorem unpackL_horner {α : Type*} (f : ℕ → α) (w : ℕ) :
    ∀ bs : List ℕ, (∀ b ∈ bs, b < 2 ^ w) →
      unpackL f w bs.length (horner id (2 ^ w) bs) = bs.map f
  | [], _ => rfl
  | b :: bs, h => by
    have hb : b < 2 ^ w := h b List.mem_cons_self
    have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
    simp only [List.length_cons, unpackL, horner_cons, id, List.map_cons]
    have h₁ : (b + 2 ^ w * horner id (2 ^ w) bs) % 2 ^ w = b := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
    have h₂ : (b + 2 ^ w * horner id (2 ^ w) bs) / 2 ^ w = horner id (2 ^ w) bs := by
      rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hb, zero_add]
    rw [h₁, h₂, unpackL_horner f w bs fun b' hb' ↦ h b' (List.mem_cons_of_mem _ hb')]

theorem horner_lt {w : ℕ} : ∀ bs : List ℕ, (∀ b ∈ bs, b < 2 ^ w) →
    horner id (2 ^ w) bs < 2 ^ (w * bs.length)
  | [], _ => by simp
  | b :: bs, h => by
    have hb : b < 2 ^ w := h b List.mem_cons_self
    have ih := horner_lt bs fun b' hb' ↦ h b' (List.mem_cons_of_mem _ hb')
    simp only [horner_cons, id, List.length_cons]
    calc b + 2 ^ w * horner id (2 ^ w) bs < 2 ^ w + 2 ^ w * horner id (2 ^ w) bs := by omega
      _ = 2 ^ w * (horner id (2 ^ w) bs + 1) := by ring
      _ ≤ 2 ^ w * 2 ^ (w * bs.length) := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (w * (bs.length + 1)) := by rw [← pow_add]; ring_nf

theorem horner_natCast {α : Type*} (f : α → ℕ) (z : ℕ) :
    ∀ as : List α, ((horner f z as : ℕ) : ℤ) = horner (fun a ↦ (f a : ℤ)) (z : ℤ) as
  | [] => rfl
  | a :: as => by simp [horner_natCast f z as]

theorem horner_add_const {α : Type*} (f : α → ℤ) (z c : ℤ) :
    ∀ as : List α, horner f z as + horner (fun _ ↦ c) z as = horner (fun a ↦ f a + c) z as
  | [] => by simp
  | a :: as => by simp only [horner_cons, ← horner_add_const f z c as]; ring

theorem horner_const_rep {α : Type*} (z c : ℕ) :
    ∀ as : List α, horner (fun _ ↦ (c : ℤ)) (z : ℤ) as = ((rep as.length z c : ℕ) : ℤ)
  | [] => by simp [rep]
  | a :: as => by simp [rep, horner_const_rep z c as]

theorem horner_map' {α β R : Type*} [Semiring R] (f : β → R) (g : α → β) (z : R) :
    ∀ as : List α, horner f z (as.map g) = horner (fun a ↦ f (g a)) z as
  | [] => rfl
  | a :: as => by simp [horner_map' f g z as]

theorem horner_congr {α R : Type*} [Semiring R] {f g : α → R} (z : R) :
    ∀ {as : List α}, (∀ a ∈ as, f a = g a) → horner f z as = horner g z as
  | [], _ => rfl
  | a :: as, h => by
    simp only [horner_cons, h a List.mem_cons_self,
      horner_congr z fun b hb ↦ h b (List.mem_cons_of_mem _ hb)]

theorem horner_toNat {α : Type*} (f : α → ℤ) (z : ℕ) :
    ∀ as : List α, (∀ a ∈ as, 0 ≤ f a) →
      horner f (z : ℤ) as = ((horner (fun a ↦ (f a).toNat) z as : ℕ) : ℤ)
  | [], _ => rfl
  | a :: as, h => by
    have ha := h a List.mem_cons_self
    simp only [horner_cons, Nat.cast_add, Nat.cast_mul, Int.toNat_of_nonneg ha,
      horner_toNat f z as fun b hb ↦ h b (List.mem_cons_of_mem _ hb)]

/-- `as` padded with `a` to length at least `m`. -/
def padTo {α : Type*} (m : ℕ) (a : α) (as : List α) : List α :=
  as ++ List.replicate (m - as.length) a

theorem length_padTo {α : Type*} {m : ℕ} (a : α) {as : List α} (h : as.length ≤ m) :
    (padTo m a as).length = m := by
  simp [padTo]; omega

theorem mem_padTo {α : Type*} {m : ℕ} {a b : α} {as : List α} (h : b ∈ padTo m a as) :
    b ∈ as ∨ b = a := by
  rcases List.mem_append.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (List.eq_of_mem_replicate h)

theorem horner_replicate {α R : Type*} [Semiring R] {f : α → R} {z : R} {a : α}
    (ha : f a = 0) : ∀ k : ℕ, horner f z (List.replicate k a) = 0
  | 0 => rfl
  | k + 1 => by simp [List.replicate_succ, ha, horner_replicate ha k]

theorem horner_padTo {α R : Type*} [Semiring R] {f : α → R} {z : R} {a : α}
    (ha : f a = 0) (m : ℕ) (as : List α) : horner f z (padTo m a as) = horner f z as := by
  unfold padTo
  generalize m - as.length = k
  induction as with
  | nil => simp [horner_replicate ha]
  | cons b as ih => simp [ih]

/-! ### Correctness -/

variable {R : Type*} [CommRing R]

theorem toNat_lt_two_pow {z : ℤ} {k : ℕ} (h : z < 2 ^ k) : z.toNat < 2 ^ k := by
  have h' : z < ((2 ^ k : ℕ) : ℤ) := by exact_mod_cast h
  rcases le_or_gt 0 z with hz | hz
  · exact_mod_cast (Int.toNat_of_nonneg hz).symm ▸ h'
  · rw [Int.toNat_of_nonpos hz.le]; exact Nat.two_pow_pos k

/-- The small-coefficient hypothesis of packing with `B`-bit digits. -/
def Small (n B : ℕ) (p : DPoly n) : Prop :=
  AllCoeff n (fun c ↦ c.natAbs < 2 ^ (B - 1)) p

theorem small_zero (B n : ℕ) : Small n B (zero n) :=
  allCoeff_zero _ (Nat.two_pow_pos _) n

/-- The biased packed value: the value at the packing point plus the offset. -/
def biased (n : ℕ) (e : List ℕ) (B : ℕ) (p : DPoly n) : ℤ :=
  eval n p (packPoint n e B) + offset n e B

theorem biased_succ (n : ℕ) (e : List ℕ) (B : ℕ) (p : DPoly (n + 1))
    (hlen : (toList p).length ≤ e.headD 0 + 1) :
    biased (n + 1) e B p =
      horner (fun q ↦ biased n e.tail B q) ((2 ^ (B * slots e.tail) : ℕ) : ℤ)
        (padTo (e.headD 0 + 1) (zero n) (toList p)) := by
  have heval : eval (n + 1) p (packPoint (n + 1) e B) =
      horner (fun q ↦ eval n q (packPoint n e.tail B)) ((2 ^ (B * slots e.tail) : ℕ) : ℤ)
        (padTo (e.headD 0 + 1) (zero n) (toList p)) := by
    rw [horner_padTo (f := fun q ↦ eval n q (packPoint n e.tail B)) (eval_zero n _),
      ← tail_packPoint]
    simp [eval, packPoint_zero]
  have hoff : ((offset (n + 1) e B : ℕ) : ℤ) = horner (fun _ ↦ ((offset n e.tail B : ℕ) : ℤ))
      ((2 ^ (B * slots e.tail) : ℕ) : ℤ) (padTo (e.headD 0 + 1) (zero n) (toList p)) := by
    rw [horner_const_rep, length_padTo _ hlen, offset_succ]
  rw [biased, heval, hoff, horner_add_const]
  rfl

theorem biased_range : ∀ (n : ℕ) {e : List ℕ} {B : ℕ} {p : DPoly n}, 0 < B → Fits n p e →
    Small n B p → 0 ≤ biased n e B p ∧ biased n e B p < 2 ^ (B * slots e)
  | 0, e, B, p, hB, _, hc => by
    have hc' : |toInt p| < 2 ^ (B - 1) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast (hc : (toInt p).natAbs < 2 ^ (B - 1))
    have h2 : (2 : ℤ) ^ B = 2 * 2 ^ (B - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hle : (2 : ℤ) ^ B ≤ 2 ^ (B * slots e) :=
      pow_le_pow_right₀ (by norm_num) (Nat.le_mul_of_pos_right B (one_le_slots e))
    have hb : biased 0 e B p = toInt p + 2 ^ (B - 1) := by
      simp [biased, eval, offset]
    rw [hb]
    constructor
    · linarith [neg_abs_le (toInt p)]
    · linarith [le_abs_self (toInt p)]
  | n + 1, e, B, p, hB, ⟨hlen, hfit⟩, hsmall => by
    have hblock : ∀ q ∈ padTo (e.headD 0 + 1) (zero n) (toList p),
        0 ≤ biased n e.tail B q ∧ biased n e.tail B q < 2 ^ (B * slots e.tail) := by
      intro q hq
      rcases mem_padTo hq with hq | rfl
      · exact biased_range n hB (hfit q hq) (hsmall q hq)
      · exact biased_range n hB (fits_zero n _) (small_zero B n)
    rw [biased_succ n e B p hlen, horner_toNat _ _ _ fun q hq ↦ (hblock q hq).1]
    refine ⟨Int.natCast_nonneg _, ?_⟩
    have hlt := horner_lt (w := B * slots e.tail)
      ((padTo (e.headD 0 + 1) (zero n) (toList p)).map fun q ↦ (biased n e.tail B q).toNat) (by
        intro b hb
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
        exact toNat_lt_two_pow (hblock q hq).2)
    rw [horner_map', List.length_map, length_padTo _ hlen] at hlt
    have : B * slots e.tail * (e.headD 0 + 1) = B * slots e := by
      rw [slots_eq e]; ring
    rw [this] at hlt
    exact_mod_cast hlt

/-- **Correctness of unpacking.** If `p` fits the shape `e` and has coefficients below
`2^(B-1)` in absolute value, the digits of its biased packed value are its coefficients:
`unpack` has the same values as `p`. -/
theorem eval_unpack : ∀ (n : ℕ) {e : List ℕ} {B : ℕ} {p : DPoly n}, 0 < B → Fits n p e →
    Small n B p → ∀ x : Fin n → R, eval n (unpack n e B (biased n e B p).toNat) x = eval n p x
  | 0, e, B, p, hB, _, hc, x => by
    have hc' : |toInt p| < 2 ^ (B - 1) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast (hc : (toInt p).natAbs < 2 ^ (B - 1))
    have h2 : (2 : ℤ) ^ B = 2 * 2 ^ (B - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hb : biased 0 e B p = toInt p + 2 ^ (B - 1) := by
      simp [biased, eval, offset]
    have h0 : 0 ≤ biased 0 e B p := by rw [hb]; linarith [neg_abs_le (toInt p)]
    have hlt : (biased 0 e B p).toNat < 2 ^ B :=
      toNat_lt_two_pow (by rw [hb]; linarith [le_abs_self (toInt p)])
    have hval : (((biased 0 e B p).toNat % 2 ^ B : ℕ) : ℤ) - 2 ^ (B - 1) = toInt p := by
      rw [Nat.mod_eq_of_lt hlt, Int.toNat_of_nonneg h0, hb]
      ring
    simp only [unpack, eval_ofInt, hval]
    rfl
  | n + 1, e, B, p, hB, ⟨hlen, hfit⟩, hsmall, x => by
    have hblock : ∀ q ∈ padTo (e.headD 0 + 1) (zero n) (toList p),
        0 ≤ biased n e.tail B q ∧ biased n e.tail B q < 2 ^ (B * slots e.tail) ∧
        ∀ y : Fin n → R, eval n (unpack n e.tail B (biased n e.tail B q).toNat) y = eval n q y := by
      intro q hq
      rcases mem_padTo hq with hq | rfl
      · exact ⟨(biased_range n hB (hfit q hq) (hsmall q hq)).1,
          (biased_range n hB (hfit q hq) (hsmall q hq)).2,
          eval_unpack n hB (hfit q hq) (hsmall q hq)⟩
      · exact ⟨(biased_range n hB (fits_zero n _) (small_zero B n)).1,
          (biased_range n hB (fits_zero n _) (small_zero B n)).2,
          eval_unpack n hB (fits_zero n _) (small_zero B n)⟩
    have hN : (biased (n + 1) e B p).toNat = horner id (2 ^ (B * slots e.tail))
        ((padTo (e.headD 0 + 1) (zero n) (toList p)).map fun q ↦ (biased n e.tail B q).toNat) := by
      rw [biased_succ n e B p hlen, horner_toNat _ _ _ fun q hq ↦ (hblock q hq).1,
        Int.toNat_natCast, horner_map']
      rfl
    have hunpack : toList (unpack (n + 1) e B (biased (n + 1) e B p).toNat) =
        (padTo (e.headD 0 + 1) (zero n) (toList p)).map fun q ↦
          unpack n e.tail B (biased n e.tail B q).toNat := by
      have := unpackL_horner (unpack n e.tail B) (B * slots e.tail)
        ((padTo (e.headD 0 + 1) (zero n) (toList p)).map fun q ↦ (biased n e.tail B q).toNat) (by
          intro b hb
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
          exact toNat_lt_two_pow (hblock q hq).2.1)
      rw [List.length_map, length_padTo _ hlen, List.map_map] at this
      rw [unpack, toList_ofList, hN]
      exact this
    rw [eval, hunpack, horner_map', eval,
      ← horner_padTo (a := zero n) (eval_zero n _) (e.headD 0 + 1) (toList p)]
    exact horner_congr _ fun q hq ↦ (hblock q hq).2.2 _

end DPoly

end Nieuwland.Check
