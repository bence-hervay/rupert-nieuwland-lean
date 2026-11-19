import Modules.Check.Polynomial.Coeff

/-!
# Zero patterns read off packed digits

A packed value `N` (`Modules/Check/Polynomial/Pack.lean`) holds the coefficients of a polynomial, each plus
the bias `2^(B-1)`, in digits of `B` bits. A coefficient is zero exactly when its digit equals the
bias, so a whole pattern of zero coefficients is one comparison of big numbers: `N` and the offset
(the bias in every digit) agree on the bits of the *mask*, which has all ones in the digits of the
pattern (`DPoly.mask`). `DPoly.zeroOn_unpack_of_mask` is the soundness statement: the polynomial
read from `N` then vanishes on the pattern (`DPoly.ZeroOn`).

The kernel computes the conjunctions with `Nat.land` and builds the mask with shifts.
-/

namespace Nieuwland.Check

namespace DPoly

/-- `f k + 2^w f (k + 1) + ⋯ + 2^(w (m - 1)) f (k + m - 1)`. -/
def blocks (f : ℕ → ℕ) (w : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | k, m + 1 => f k + blocks f w (k + 1) m <<< w

/-- The mask of the pattern `P` in the slots of the shape `sh`, with digits of `B` bits: all ones
in the digit of every exponent list `α` with `P α`, zeros elsewhere. -/
def mask : (n : ℕ) → (List ℕ → Bool) → List ℕ → ℕ → ℕ
  | 0, P, _, B => if P [] then 2 ^ B - 1 else 0
  | n + 1, P, sh, B =>
    blocks (fun k ↦ mask n (fun α ↦ P (k :: α)) sh.tail B) (B * slots sh.tail) 0 (sh.headD 0 + 1)

/-- The digits of `N` agree with the bias on the pattern `P`. -/
def maskOk (n : ℕ) (P : List ℕ → Bool) (sh : List ℕ) (B N : ℕ) : Bool :=
  let M := mask n P sh B
  N &&& M == offset n sh B &&& M

theorem blocks_mod {f : ℕ → ℕ} {w k : ℕ} (hf : f k < 2 ^ w) (m : ℕ) :
    blocks f w k (m + 1) % 2 ^ w = f k := by
  rw [blocks, Nat.shiftLeft_eq, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hf]

theorem blocks_div {f : ℕ → ℕ} {w k : ℕ} (hf : f k < 2 ^ w) (m : ℕ) :
    blocks f w k (m + 1) / 2 ^ w = blocks f w (k + 1) m := by
  rw [blocks, Nat.shiftLeft_eq, Nat.mul_comm, Nat.add_mul_div_left _ _ (Nat.two_pow_pos w),
    Nat.div_eq_of_lt hf, zero_add]

theorem blocks_lt {f : ℕ → ℕ} {w : ℕ} (hf : ∀ k, f k < 2 ^ w) :
    ∀ (k m : ℕ), blocks f w k m < 2 ^ (w * m)
  | _, 0 => by simp [blocks]
  | k, m + 1 => by
    have h₁ := blocks_lt hf (k + 1) m
    have h₂ := hf k
    rw [blocks, Nat.shiftLeft_eq]
    calc f k + blocks f w (k + 1) m * 2 ^ w < 2 ^ w + blocks f w (k + 1) m * 2 ^ w := by omega
      _ = (blocks f w (k + 1) m + 1) * 2 ^ w := by ring
      _ ≤ 2 ^ (w * m) * 2 ^ w := Nat.mul_le_mul_right _ h₁
      _ = 2 ^ (w * (m + 1)) := by rw [← pow_add]; ring_nf

theorem mask_lt : ∀ (n : ℕ) (P : List ℕ → Bool) (sh : List ℕ) (B : ℕ),
    mask n P sh B < 2 ^ (B * slots sh)
  | 0, P, sh, B => by
    have : 2 ^ B ≤ 2 ^ (B * slots sh) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right B (one_le_slots sh))
    have h0 : 0 < 2 ^ B := Nat.two_pow_pos B
    unfold mask
    split_ifs <;> omega
  | n + 1, P, sh, B => by
    have h := blocks_lt (f := fun k ↦ mask n (fun α ↦ P (k :: α)) sh.tail B)
      (w := B * slots sh.tail) (fun k ↦ mask_lt n _ sh.tail B) 0 (sh.headD 0 + 1)
    rw [mask]
    rwa [slots_eq sh, ← Nat.mul_assoc, Nat.mul_right_comm B]

theorem offset_lt {B : ℕ} (hB : 0 < B) (n : ℕ) (sh : List ℕ) :
    offset n sh B < 2 ^ (B * slots sh) := by
  have h := (biased_range n hB (fits_zero n sh) (small_zero B n)).2
  simp only [biased, eval_zero, zero_add] at h
  exact_mod_cast h

theorem rep_mod {z a : ℕ} (ha : a < z) (m : ℕ) : rep (m + 1) z a % z = a := by
  rw [rep, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

theorem rep_div {z a : ℕ} (ha : a < z) (m : ℕ) : rep (m + 1) z a / z = rep m z a := by
  have hz : 0 < z := lt_of_le_of_lt (Nat.zero_le a) ha
  rw [rep, Nat.add_mul_div_left _ _ hz, Nat.div_eq_of_lt ha, zero_add]

/-- **Soundness of the mask check.** Where the digits of `N` equal the bias, the polynomial read
from `N` has zero coefficients. -/
theorem zeroOn_unpack_of_mask {B : ℕ} (hB : 0 < B) : ∀ (n : ℕ) (P : List ℕ → Bool)
    (sh : List ℕ) (N : ℕ), N &&& mask n P sh B = offset n sh B &&& mask n P sh B →
      ZeroOn n P (unpack n sh B N)
  | 0, P, sh, N, h => by
    intro hP
    simp only [mask, hP, ↓reduceIte, Nat.and_two_pow_sub_one_eq_mod, offset] at h
    have hlt : 2 ^ (B - 1) < 2 ^ B := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [Nat.mod_eq_of_lt hlt] at h
    simp [unpack, h]
  | n + 1, P, sh, N, h => by
    set w := B * slots sh.tail
    set f : ℕ → ℕ := fun k ↦ mask n (fun α ↦ P (k :: α)) sh.tail B
    have hf : ∀ k, f k < 2 ^ w := fun k ↦ mask_lt n _ sh.tail B
    have hO : offset n sh.tail B < 2 ^ w := offset_lt hB n sh.tail
    have key : ∀ (m k N : ℕ), N &&& blocks f w k m = rep m (2 ^ w) (offset n sh.tail B) &&&
        blocks f w k m →
        ForallIdx (fun j q ↦ ZeroOn n (fun α ↦ P (j :: α)) q) k
          (unpackL (unpack n sh.tail B) w m N) := by
      intro m
      induction m with
      | zero => intro k N _; trivial
      | succ m ih =>
        intro k N hN
        refine ⟨zeroOn_unpack_of_mask hB n _ sh.tail _ ?_, ih (k + 1) _ ?_⟩
        · have := congrArg (· % 2 ^ w) hN
          simp only [Nat.and_mod_two_pow, blocks_mod (hf k), rep_mod hO] at this
          exact this
        · have := congrArg (· / 2 ^ w) hN
          simp only [Nat.and_div_two_pow, blocks_div (hf k), rep_div hO] at this
          exact this
    rw [offset_succ] at h
    exact key _ 0 N h

theorem zeroOn_unpack_of_maskOk {B : ℕ} (hB : 0 < B) {n : ℕ} {P : List ℕ → Bool}
    {sh : List ℕ} {N : ℕ} (h : maskOk n P sh B N = true) : ZeroOn n P (unpack n sh B N) :=
  zeroOn_unpack_of_mask hB n P sh N (by simpa [maskOk] using h)

end DPoly

end Nieuwland.Check
