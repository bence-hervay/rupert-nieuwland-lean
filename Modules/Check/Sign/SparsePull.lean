import Modules.Check.Sign.SparseTop
import Modules.Check.Polynomial.FPoly

/-!
# Sparse sign checks

`Pull.checkX` is `Pull.check` with the terms computed as rupert computes them
(`witness_polys`, `code/src/proof/tree.rs`): each term's polynomial is run in the ring of sparse
polynomials (`SP`) on the box inputs, so that its numerator in the varying coordinates comes out
exactly, with like terms merged and zero coefficients dropped (`numerS`). Its monomial `x^e` is
divided off exponentwise (`SPoly.divE`, replacing the mask checks), and its coordinates in the
basis of `κ` are integer polynomials (`SPoly.coordS`). Their shapes and coefficient bounds are
read off the polynomials themselves (`SPoly.shapeS`, `SPoly.normS`), not from formal runs, and
their values at the packing point by Horner's rule, where multiplying by a packing input
`Cᵢ + Hᵢ 2^k` is two products by small numbers and a shift (`SPoly.evalPk`). The tuples' sums,
digit sizes and the engine are those of `Pull.check` (`Frame.runTupleW`, `Frame.bitsW`).

Where the engine fails on a tuple, the tuple is tested at bounded precision (`Lay.tPass`), twice.
In the truncated test from the exact values (`Frame.tPassX`), each term's values are scaled to the
tuple's denominator degree `K` and truncated `tPrec` bits below the largest bound of the terms at
that degree (`tTerm`, `Frame.tShiftK`, once per term and degree), and the engine runs on the
truncated sums at the digit size `tBits` with the truncation errors subtracted from their constant,
at the top box only (a tuple with a zero on the box needs the exact engine, and would bisect to the
full depth before failing). The truncated test at bounded precision (`Frame.tPassFX`) is the same
test from values computed by Horner's rule at about `fPrec` bits (`FPoly.fE`, with an error bound
proved on the whole box) and truncated with their errors (`FPoly.trunc`); a tuple that passes it
needs no exact values. It runs where its values are much smaller than the exact ones
(`Frame.fFirst`), and then first in compiled code; otherwise compiled code runs the truncated test
first where that is cheaper (`Frame.tFirst`). Where it fails, on numerals of at least `bMin` bits,
the top box from second truncations of those values (`Frame.procFX`, `Pull.fTop`): the centred
and vertex tests on one integer enclosure of the tuple's sums on the cube, then rupert's bisection
on it (`Pull.cubeZ`), so that a tuple it closes needs no exact values either.

Then rupert's own procedure (`Frame.runTupleNX`; `nonneg_exact_rec` in
`code/src/proof/regional.rs`, `Modules/Check/Sign/SparseBox.lean`): the leaf's box on the tuple's
numerals, then rupert's bisection of the tuple's weighted sparse terms, each box's frame and its
vertex frame by Horner's rule from the terms, with the centred form and dominance at bounded
precision with the exact vertex value. Compiled code runs it before the engine
(`checkXCombFP`). A tuple passes if any of the four passes (`Frame.runTupleXT`).

The conclusion is that of `Pull.check` (`Pull.checkX_sound`): at every box point, every checked
combination of the terms divided by their monomials has the sign.
-/

namespace Nieuwland.Check

open DPoly

namespace Pull

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-! ### Truncated tests -/

/-- The bits of precision of the truncated tests below the bound of a leaf's sums. -/
def tPrec : ℕ := 64

/-- Spare bits of the truncated tests' digits (for sums above the bound's scale). -/
def tSlack : ℕ := 16

variable (κ) in
/-- The digit size of the truncated tests: the precision, the approximations' bits and room for
the bias and the spare bits (no bisection). -/
def tBits : ℕ := Lay.apxBits κ + 2 + tPrec + tSlack

/-- The precision of the top box from the values at bounded precision (`Frame.procFW`): its
truncations keep about this many bits below the bound of a tuple's terms (`Frame.tBound`), as the
values keep `fPrec` bits of each. -/
def pPrec : ℕ := 128

variable (κ) in
/-- The digit size of those truncations (`tBits` at the precision `pPrec`). -/
def pBits : ℕ := Lay.apxBits κ + 2 + pPrec + tSlack

variable (κ) in
/-- The truncated coordinates of a term from its values `v` at the packing point of digit size `B`
(offset `O`), scaled by `mult` and floored to multiples of `2^s`, as signed numerals of the digit
size `B'` with the sums of their digits' absolute values (`Lay.truncL`). -/
def tTerm (shape : List ℕ) (O B B' s : ℕ) (mult : ℤ) (v : List ℤ) : List (ℤ × ℕ) :=
  (List.range (ExactBasis.dim κ)).map fun c ↦
    Lay.truncL B B' s (2 ^ (B - 1)) mult (DPoly.slots shape) (v.getD c 0 + O).toNat

variable (κ) in
/-- Term `j`'s truncated coordinates (`tTerm` of its values `v j`) in a tuple of denominator degree
`K`, scaled by `D^(K - mⱼ)`, at the digit size `B'`. -/
def tTermF (shape : List ℕ) (O B B' s : ℕ) (D : ℤ) (K : ℕ) (tf : ℕ → TermFrame)
    (v : ℕ → List ℤ) (j : ℕ) : List (ℤ × ℕ) :=
  tTerm κ shape O B B' s (D ^ (K - (tf j).m)) (v j)

/-- The pairs of a term and the denominator degree of a tuple of `τs` that uses it, once each:
the truncations the truncated tests of `τs` read. -/
def tPairs (tf : ℕ → TermFrame) (τs : List Tuple) : List (ℕ × ℕ) :=
  τs.foldl (fun a τ ↦
    let K := Frame.tupleKW tf τ
    τ.foldl (fun a jw ↦ bif a.contains (jw.1, K) then a else (jw.1, K) :: a) a) []

/-- The values of `f` at the keys `ks`, each computed when first read and then kept (`lookK`). A
separate array, not a closure over it: compiled code eta-expands a definition that returns a
closure, and would rebuild its array on every call. -/
def memoA {α : Type} (ks : List (ℕ × ℕ)) (f : ℕ → ℕ → α) : Array ((ℕ × ℕ) × Thunk α) :=
  ks.toArray.map fun k ↦ (k, Thunk.mk fun _ ↦ f k.1 k.2)

/-- The value kept in `a` at the key `(j, K)`, else `f j K` (`lookK_memoA`). -/
def lookK {α : Type} (a : Array ((ℕ × ℕ) × Thunk α)) (f : ℕ → ℕ → α) (j K : ℕ) : α :=
  match a.find? (fun x ↦ x.1 == (j, K)) with
  | some x => x.2.get
  | none => f j K

theorem lookK_memoA {α : Type} (ks : List (ℕ × ℕ)) (f : ℕ → ℕ → α) : lookK (memoA ks f) f = f := by
  funext j K
  simp only [lookK, memoA]
  split
  · next x hx =>
    have hp := Array.find?_some hx
    obtain ⟨k, -, rfl⟩ := Array.mem_map.mp (Array.mem_of_find?_eq_some hx)
    simp only [beq_iff_eq] at hp
    subst hp
    rfl
  · rfl

theorem cond_or_comm (c a b : Bool) : (bif c then a || b else b || a) = (b || a) := by
  cases c <;> simp [Bool.or_comm]

/-! ### Values at bounded precision -/

/-- The precision of the values at bounded precision (`FPoly`): about this many bits of each value
are kept, against the `tPrec` bits that the truncated tests read. -/
def fPrec : ℕ := 128

/-- Term `j`'s coordinates at bounded precision (`FPoly.fE`) from its quotients `tq j`. -/
def fvalW (fc : FPoly.Ctx) (tq : ℕ → List (SPoly ℤ)) (j : ℕ) : List (Option FPoly.FP) :=
  (tq j).map fun q ↦ FPoly.fE fc (SPoly.fuelOf q) 0 q

/-- The truncations (`FPoly.trunc`: digit size `B'`, shift `s`, scale `mult`) of values at bounded
precision, with the largest of their errors; `none` if a value is missing (`ftL_spec`). -/
def ftL (fc : FPoly.Ctx) (B' s : ℕ) (mult : ℤ) :
    List (Option FPoly.FP) → Option (List (ℤ × ℕ) × ℕ)
  | [] => some ([], 0)
  | none :: _ => none
  | some x :: xs => (ftL fc B' s mult xs).map fun r ↦
      ((FPoly.trunc fc B' s mult x).1 :: r.1, max (FPoly.trunc fc B' s mult x).2 r.2)

/-- Term `j`'s truncated coordinates from its values at bounded precision `fv j` in a tuple of
denominator degree `K`, scaled by `D^(K - mⱼ)` (`ftL`). -/
def ftTermF (fc : FPoly.Ctx) (B' s : ℕ) (D : ℤ) (K : ℕ) (tf : ℕ → TermFrame)
    (fv : ℕ → List (Option FPoly.FP)) (j : ℕ) : Option (List (ℤ × ℕ) × ℕ) :=
  ftL fc B' s (D ^ (K - (tf j).m)) (fv j)


namespace Frame

variable (F : Frame κ)

/-- The largest bound `|D|^(K - mⱼ) nbⱼ` of the terms `j < nt` of denominator degree at most `K`
(frames `tf`, bounds `nb`), scaled to the degree `K`. -/
def tBound (tf : ℕ → TermFrame) (nb : ℕ → ℕ) (nt K : ℕ) : ℕ :=
  (List.range nt).foldr (fun j a ↦
    bif decide ((tf j).m ≤ K) then max (F.D.natAbs ^ (K - (tf j).m) * nb j) a else a) 0

/-- The truncation shift of the tuples of denominator degree `K`: `tPrec` bits below the largest
bound of the terms at that degree (`tBound`). Any shift is sound (`tPassX_sound`); this one keeps
about `tPrec` bits of every sum. -/
def tShiftK (tf : ℕ → TermFrame) (nb : ℕ → ℕ) (nt K : ℕ) : ℕ :=
  Nat.log2 (F.tBound tf nb nt K) + 1 - tPrec

/-- The truncation shift of the top box at bounded precision (`procFW`) for the tuples of
denominator degree `K`: `pPrec` bits below `tBound`. Any shift is sound (`procFX_sound`). -/
def pShiftK (tf : ℕ → TermFrame) (nb : ℕ → ℕ) (nt K : ℕ) : ℕ :=
  Nat.log2 (F.tBound tf nb nt K) + 1 - pPrec

/-- **The truncated test of a tuple** (`Lay.tPass` at the top box, without vertex expansions:
it fails fast where the exact engine is needed; `tPassX_sound`), with the terms' truncated
coordinates `td`. -/
def tPassW (shape : List ℕ) (td : ℕ → List (ℤ × ℕ)) (B' : ℕ) (strict : Bool) (τ : Tuple) : Bool :=
  Lay.tPass κ F.n shape B' strict false true 0 F.W (fun j c ↦ ((td j).getD c (0, 0)).1)
    (fun j c ↦ ((td j).getD c (0, 0)).2) (fun _ ↦ DPoly.slots shape) τ

/-- `tPassW` with the masks of the digit size `B'` given (`tPassWM_masks`). -/
def tPassWM (m : Lay.Masks) (shape : List ℕ) (td : ℕ → List (ℤ × ℕ)) (B' : ℕ) (strict : Bool)
    (τ : Tuple) : Bool :=
  Lay.tPassM κ m F.n shape B' strict false true 0 F.W (fun j c ↦ ((td j).getD c (0, 0)).1)
    (fun j c ↦ ((td j).getD c (0, 0)).2) (fun _ ↦ DPoly.slots shape) τ

theorem tPassWM_masks (shape : List ℕ) (td : ℕ → List (ℤ × ℕ)) (B' : ℕ) (strict : Bool)
    (τ : Tuple) :
    F.tPassWM (Lay.masks B' shape) shape td B' strict τ = F.tPassW shape td B' strict τ := by
  simp only [tPassWM, tPassW, Lay.tPassM_masks]

/-- The context of the values at bounded precision of the frame with the shape `shape`: the box
inputs, `fPrec` bits, and digits with room for a product by a box input (`FPoly.mulZ`). -/
def fCtx (shape : List ℕ) : FPoly.Ctx :=
  ⟨shape, F.C, F.H,
    fPrec + Nat.log2 ((F.C.map Int.natAbs).foldr max 0 + (F.H.map Int.natAbs).foldr max 0) + 5,
    fPrec⟩

/-- Whether the truncated test at bounded precision runs (`runTupleXT`): where the digits of its
values (`fB` bits) are at most a quarter of the exact values' (`B` bits). Its values cost about
2.5 times the exact values' per bit of digit (K_{√3/3}'s leaf 8765: 163 against 2007 ms a term
with digits of 174 against 5367 bits, one thread, 2026-11-05); below that, the exact values cost
little and the truncated test from them is as precise. Any choice is sound (`runTupleXT_sound`). -/
def fFirst (fB B : ℕ) : Bool := decide (4 * fB ≤ B)

/-- **The truncated test at bounded precision** (`Lay.tPass` at the top box, `tPassFX_sound`):
with the truncations `ftd j` of the terms' values at bounded precision and their errors; every
term of the tuple needs its truncations. -/
def tPassFW (shape : List ℕ) (ftd : ℕ → Option (List (ℤ × ℕ) × ℕ)) (B' : ℕ) (strict : Bool)
    (τ : Tuple) : Bool :=
  τ.all (fun jw ↦ (ftd jw.1).isSome) &&
    Lay.tPass κ F.n shape B' strict false true 0 F.W
      (fun j c ↦ (((ftd j).getD ([], 0)).1.getD c (0, 0)).1)
      (fun j c ↦ (((ftd j).getD ([], 0)).1.getD c (0, 0)).2) (fun j ↦ ((ftd j).getD ([], 0)).2) τ

/-- `tPassFW` with the masks of the digit size `B'` given (`tPassFWM_masks`). -/
def tPassFWM (m : Lay.Masks) (shape : List ℕ) (ftd : ℕ → Option (List (ℤ × ℕ) × ℕ)) (B' : ℕ)
    (strict : Bool) (τ : Tuple) : Bool :=
  τ.all (fun jw ↦ (ftd jw.1).isSome) &&
    Lay.tPassM κ m F.n shape B' strict false true 0 F.W
      (fun j c ↦ (((ftd j).getD ([], 0)).1.getD c (0, 0)).1)
      (fun j c ↦ (((ftd j).getD ([], 0)).1.getD c (0, 0)).2) (fun j ↦ ((ftd j).getD ([], 0)).2) τ

theorem tPassFWM_masks (shape : List ℕ) (ftd : ℕ → Option (List (ℤ × ℕ) × ℕ)) (B' : ℕ)
    (strict : Bool) (τ : Tuple) :
    F.tPassFWM (Lay.masks B' shape) shape ftd B' strict τ = F.tPassFW shape ftd B' strict τ := by
  simp only [tPassFWM, tPassFW, Lay.tPassM_masks]

/-- **The top box at bounded precision** (`Pull.fTop` on the leaf's box; `procFX_sound`), as rupert
tests a tuple whose centred test fails: from the truncations `ftd j` of its terms' values at bounded
precision, their sums' enclosure on the cube, its centred test and its vertex test, then rupert's
bisection on it (`cubeZ`, along the leaf's widths, at most `depth` levels deep). Every term of the
tuple needs its truncations. -/
def procFW (shape : List ℕ) (ftd : ℕ → Option (List (ℤ × ℕ) × ℕ)) (B' : ℕ) (strict : Bool)
    (depth : ℕ) (τ : Tuple) : Bool :=
  τ.all (fun jw ↦ (ftd jw.1).isSome) &&
    fTop κ 0 0 F.n shape strict depth F.W B' (fun j c ↦ (((ftd j).getD ([], 0)).1.getD c (0, 0)).1)
      (fun j c ↦ (((ftd j).getD ([], 0)).1.getD c (0, 0)).2) (fun j ↦ ((ftd j).getD ([], 0)).2) τ

/-- `procFW` with the tuple `i` of `nτ` labelling the beat lines of its bisection (`procFWL_eq`),
as compiled code runs it. -/
def procFWL (i nτ : ℕ) (shape : List ℕ) (ftd : ℕ → Option (List (ℤ × ℕ) × ℕ)) (B' : ℕ)
    (strict : Bool) (depth : ℕ) (τ : Tuple) : Bool :=
  τ.all (fun jw ↦ (ftd jw.1).isSome) &&
    fTop κ i nτ F.n shape strict depth F.W B'
      (fun j c ↦ (((ftd j).getD ([], 0)).1.getD c (0, 0)).1)
      (fun j c ↦ (((ftd j).getD ([], 0)).1.getD c (0, 0)).2) (fun j ↦ ((ftd j).getD ([], 0)).2) τ

theorem procFWL_eq (i nτ : ℕ) (shape : List ℕ) (ftd : ℕ → Option (List (ℤ × ℕ) × ℕ)) (B' : ℕ)
    (strict : Bool) (depth : ℕ) (τ : Tuple) :
    F.procFWL i nτ shape ftd B' strict depth τ = F.procFW shape ftd B' strict depth τ := by
  simp only [procFWL, procFW, fTop_tag (κ := κ) i nτ]

/-- The sparse terms of all terms. -/
def termSL : List TermS := F.ts.map fun t ↦ termS F.n t F.C F.H F.D

/-- Term `j` computed sparsely on the frame (`default`, which fails, beyond the terms). -/
def tS (j : ℕ) : TermS := F.termSL.getD j default

/-- The packing shape of the sparse terms. -/
def shapeX : List ℕ := shapeMax (F.termSL.map (·.sh))

/-- The frames of the sparse terms. -/
def tfX (j : ℕ) : TermFrame := (F.tS j).tf

/-- The bounds of the sparse terms. -/
def nbX (j : ℕ) : ℕ := (F.tS j).nb

/-- The values of the sparse terms at the packing point of digit size `B`. -/
def valX (B j : ℕ) : List ℤ := valS F.shapeX F.C F.H B (F.tS j)

/-- The digit size of the sparse check of the tuples `τs` (`bitsW`). -/
def bitsX (depth : ℕ) (τs : List Tuple) : ℕ := F.bitsW F.shapeX F.tfX F.nbX depth τs

/-- Certifies the tuple `τ` with the sparse terms (`runTupleW`). -/
def runTupleX (strict : Bool) (depth B : ℕ) : Tuple → Bool :=
  F.runTupleW F.shapeX F.tfX (fun _ ↦ true) (fun _ ↦ true) (F.valX B) strict depth B

/-- The truncated coordinates of the sparse terms (`tTermF`) from their values at the digit size
`B`, in a tuple of denominator degree `K` (shift `tShiftK`). -/
def tTermX (B K : ℕ) : ℕ → List (ℤ × ℕ) :=
  tTermF κ F.shapeX (offset F.n F.shapeX B) B (tBits κ) (F.tShiftK F.tfX F.nbX F.ts.length K) F.D
    K F.tfX (F.valX B)

/-- The truncated test of the tuple `τ` with the sparse terms (`tPassW`). -/
def tPassX (strict : Bool) (B : ℕ) (τ : Tuple) : Bool :=
  F.tPassW F.shapeX (F.tTermX B (tupleKW F.tfX τ)) (tBits κ) strict τ

/-- The values at bounded precision of the sparse terms (`fvalW`). -/
def fvalX (j : ℕ) : List (Option FPoly.FP) := fvalW (F.fCtx F.shapeX) (fun j ↦ (F.tS j).q) j

/-- The truncated coordinates of the sparse terms from their values at bounded precision in a
tuple of denominator degree `K` (shift `tShiftK`). -/
def ftTermX (K : ℕ) : ℕ → Option (List (ℤ × ℕ) × ℕ) :=
  ftTermF (F.fCtx F.shapeX) (tBits κ) (F.tShiftK F.tfX F.nbX F.ts.length K) F.D K F.tfX F.fvalX

/-- The truncated test at bounded precision of the tuple `τ` with the sparse terms (`tPassFW`). -/
def tPassFX (strict : Bool) (τ : Tuple) : Bool :=
  F.tPassFW F.shapeX (F.ftTermX (tupleKW F.tfX τ)) (tBits κ) strict τ

/-- The truncations at the precision `pPrec` of the sparse terms' values at bounded precision in a
tuple of denominator degree `K` (shift `pShiftK`). -/
def ptTermX (K : ℕ) : ℕ → Option (List (ℤ × ℕ) × ℕ) :=
  ftTermF (F.fCtx F.shapeX) (pBits κ) (F.pShiftK F.tfX F.nbX F.ts.length K) F.D K F.tfX F.fvalX

/-- The top box at bounded precision of the tuple `τ` with the sparse terms (`procFW`). -/
def procFX (strict : Bool) (depth : ℕ) (τ : Tuple) : Bool :=
  F.procFW F.shapeX (F.ptTermX (tupleKW F.tfX τ)) (pBits κ) strict depth τ

/-- A tuple's terms as weighted terms of denominator degree `K` (`WTerms`): the weights
`w D^(K - mⱼ)` (frames `tf`) and the coordinates `tq j` of the quotients. -/
def wtW (tf : ℕ → TermFrame) (tq : ℕ → List (SPoly ℤ)) (K : ℕ) (τ : Tuple) : WTerms :=
  τ.map fun jw ↦ (jw.2 * F.D ^ (K - (tf jw.1).m), tq jw.1)

/-- The numerals of a tuple's sums at the digit size `B` from the terms' values `val` (those of
`runTupleW`). -/
def numsW (shape : List ℕ) (tf : ℕ → TermFrame) (val : ℕ → List ℤ) (B : ℕ) (τ : Tuple) :
    List ℕ :=
  (List.range (ExactBasis.dim κ)).map fun c ↦
    ((F.valueSumW tf val (tupleKW tf τ) τ).getD c 0 + offset F.n shape B).toNat

/-- **rupert's procedure on a tuple** (`nonneg_exact_rec`; `runTupleNX_sound`): the leaf's box by
the centred form on the tuple's numerals at the digit size `B` (from the values `val` that the
tuples share), or by their enclosure at bounded precision (`procB`, at the precision of the exact
value at the vertex, on numerals of at least `bMin` bits), or by its exact vertex frame and
rupert's bisection on its one-sided enclosure (`procA`), or by rupert's bisection (`boxRec`) of the
tuple's weighted terms (`wtW`, quotients `tq`) below it, at most `depth` levels deep. Compiled code
tests these in one of two orders (`runTupleNP`). -/
def runTupleNW (shape : List ℕ) (tf : ℕ → TermFrame) (tq : ℕ → List (SPoly ℤ))
    (val : ℕ → List ℤ) (strict : Bool) (depth B : ℕ) (τ : Tuple) : Bool :=
  let wt := F.wtW tf tq (tupleKW tf τ) τ
  let Ns := F.numsW shape tf val B τ
  Lay.boxOk κ F.n shape B strict false Ns ||
    (useB B shape && procB κ 0 0 F.n shape strict wt F.C F.H B Ns) ||
    procA κ 0 0 F.n shape strict depth wt F.C F.H F.W B Ns ||
    boxRec κ F.n shape strict (WTerms.deg wt) wt depth false F.C F.H 0 F.W

/-- rupert's procedure on the tuple `τ` with the sparse terms (`runTupleNW`). -/
def runTupleNX (strict : Bool) (depth B : ℕ) : Tuple → Bool :=
  F.runTupleNW F.shapeX F.tfX (fun j ↦ (F.tS j).q) (F.valX B) strict depth B

/-- Certifies the tuple `τ` with the sparse terms: the engine (`runTupleX`); where the values at
bounded precision are much smaller than the exact ones (`fFirst`), the truncated test from them
(`tPassFX`) or, on numerals of at least `bMin` bits (`useB`), the top box from them (`procFX`); the
truncated test (`tPassX`) or rupert's procedure (`runTupleNX`). -/
def runTupleXT (strict : Bool) (depth B : ℕ) (τ : Tuple) : Bool :=
  F.runTupleX strict depth B τ || (fFirst (F.fCtx F.shapeX).B B && (F.tPassFX strict τ ||
    useB B F.shapeX && F.procFX strict depth τ)) || F.tPassX strict B τ ||
    F.runTupleNX strict depth B τ

/-- **The sparse check on the frame `F`** as compiled code runs it (`checkXF_eq`): the terms
computed sparsely once, the shape, the digit size of the tuples (`bitsW`), the values of the terms
at the packing point and at bounded precision (each once, when first used), then on every tuple the
engine (`runTupleW`), the truncated test at bounded precision and the top box from it (`tPassFW`,
`procFW`, where `fFirst`), the truncated test from the values (`tPassW`; each term truncated once
per denominator degree of its tuples and precision, when first used) and rupert's procedure
(`runTupleNW`). -/
def checkXF (den : ℕ) (strict : Bool) (depth : ℕ) (τs : List Tuple) : Bool :=
  let tsa := F.termSL.toArray
  let tS := fun j ↦ tsa.getD j default
  let tf := fun j ↦ (tS j).tf
  let nb := fun j ↦ (tS j).nb
  let shape := shapeMax (tsa.toList.map (·.sh))
  let B := F.bitsW shape tf nb depth τs
  let vala := thunks F.ts.length fun j ↦ valS shape F.C F.H B (tS j)
  let v := lookT vala fun j ↦ valS shape F.C F.H B (tS j)
  let tt := fun j K ↦ tTermF κ shape (offset F.n shape B) B (tBits κ)
    (F.tShiftK tf nb F.ts.length K) F.D K tf v j
  let td := lookK (memoA (tPairs tf τs) tt) tt
  let fc := F.fCtx shape
  let fv := lookT (thunks F.ts.length (fvalW fc fun j ↦ (tS j).q)) (fvalW fc fun j ↦ (tS j).q)
  let ft := fun j K ↦ ftTermF fc (tBits κ) (F.tShiftK tf nb F.ts.length K) F.D K tf fv j
  let ftd := lookK (memoA (tPairs tf τs) ft) ft
  let pt := fun j K ↦ ftTermF fc (pBits κ) (F.pShiftK tf nb F.ts.length K) F.D K tf fv j
  let ptd := lookK (memoA (tPairs tf τs) pt) pt
  let useF := fFirst fc.B B
  decide (0 < den) && decide (shape.length ≤ F.n) &&
    τs.all (fun τ ↦ τ.all fun jw ↦ (tS jw.1).ok) &&
    τs.all (fun τ ↦ F.runTupleW shape tf (fun _ ↦ true) (fun _ ↦ true) v strict depth B τ ||
      (useF && (F.tPassFW shape (fun j ↦ ftd j (tupleKW tf τ)) (tBits κ) strict τ ||
        useB B shape && F.procFW shape (fun j ↦ ptd j (tupleKW tf τ)) (pBits κ) strict depth τ)) ||
      F.tPassW shape (fun j ↦ td j (tupleKW tf τ)) (tBits κ) strict τ ||
      F.runTupleNW shape tf (fun j ↦ (tS j).q) v strict depth B τ)

theorem getD_termSL_toArray (j : ℕ) : F.termSL.toArray.getD j default = F.tS j := by
  simp [tS, List.getD_eq_getElem?_getD]

theorem checkXF_eq (den : ℕ) (strict : Bool) (depth : ℕ) (τs : List Tuple) :
    F.checkXF den strict depth τs = (decide (0 < den) && decide (F.shapeX.length ≤ F.n) &&
      τs.all (fun τ ↦ τ.all fun jw ↦ (F.tS jw.1).ok) &&
      τs.all (F.runTupleXT strict depth (F.bitsX depth τs))) := by
  simp only [checkXF, getD_termSL_toArray, lookT_thunks, lookK_memoA]
  rfl

theorem tS_cases (j : ℕ) :
    j < F.ts.length ∧ F.tS j = termS F.n (F.term j) F.C F.H F.D ∨ F.tS j = default := by
  by_cases hj : j < F.ts.length
  · refine Or.inl ⟨hj, ?_⟩
    rw [tS, termSL, getD_map_of_lt _ default _ hj]
    rfl
  · exact Or.inr (List.getD_eq_default _ _ (by simp [termSL]; omega))

theorem tS_of_ok {j : ℕ} (h : (F.tS j).ok = true) :
    j < F.ts.length ∧ F.tS j = termS F.n (F.term j) F.C F.H F.D := by
  rcases F.tS_cases j with h' | h'
  · exact h'
  · rw [h'] at h
    exact absurd h (by decide)

theorem shapeLE_shapeX (j : ℕ) : ShapeLE (F.tS j).sh F.shapeX := by
  rcases F.tS_cases j with ⟨hj, -⟩ | h
  · refine shapeLE_shapeMax (List.mem_map.mpr ⟨F.tS j, ?_, rfl⟩)
    rw [tS, List.getD_eq_getElem _ _ (by simpa [termSL] using hj)]
    exact List.getElem_mem _
  · rw [h]
    trivial

theorem bounded_tS (j c : ℕ) :
    ShapeLE (SPoly.shapeS F.n ((F.tS j).q.getD c [])) (F.tS j).sh ∧
      SPoly.normS (boxNorms F.n F.C F.H F.D) ((F.tS j).q.getD c []) ≤ (F.tS j).nb := by
  rcases F.tS_cases j with ⟨-, h⟩ | h
  · rw [h]
    exact termS_bounded c
  · rw [h]
    exact ⟨trivial, Nat.le_refl 0⟩

theorem lenOk_tS {j : ℕ} (h : (F.tS j).ok = true) (c : ℕ) :
    SPoly.lenOk F.n ((F.tS j).q.getD c []) = true := by
  obtain ⟨-, heq⟩ := F.tS_of_ok h
  rw [heq] at h ⊢
  exact termS_lenOk h c

theorem le_tupleKW (tf : ℕ → TermFrame) {τ : Tuple} {jw : ℕ × ℤ} (h : jw ∈ τ) :
    (tf jw.1).m ≤ tupleKW tf τ := by
  induction τ with
  | nil => simp at h
  | cons a τ ih =>
    rw [tupleKW, List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

/-! #### Soundness -/

/-- Coordinate `c` of `∑ w D^(K - mⱼ) qⱼ` of a tuple of sparse terms as an expression in the box
variables (in proofs). -/
def sumExprX (K c : ℕ) : Tuple → Expr
  | [] => .const 0
  | (j, w) :: τ =>
    .const (w * F.D ^ (K - (F.tfX j).m)) * SPoly.qE ((F.tS j).q.getD c []) + sumExprX K c τ

/-- Coordinate `c` of `∑ w D^(K - mⱼ) qⱼ` at a real point (in proofs). -/
noncomputable def sumAtX (y : ℕ → ℝ) (K c : ℕ) : Tuple → ℝ
  | [] => 0
  | (j, w) :: τ => ((w * F.D ^ (K - (F.tfX j).m) : ℤ) : ℝ) *
      SPoly.run Exact.re y ((F.tS j).q.getD c []) + sumAtX y K c τ

theorem shape_sumExprX (K c : ℕ) :
    ∀ τ : Tuple, ShapeLE ((F.sumExprX K c τ).shape (boxShapes F.n)) F.shapeX
  | [] => trivial
  | (j, w) :: τ => by
    refine shapeLE_zipPad_max ?_ (shape_sumExprX K c τ)
    change ShapeLE ((SPoly.qE ((F.tS j).q.getD c [])).shape (boxShapes F.n)) F.shapeX
    rw [SPoly.shape_qE]
    exact (F.bounded_tS j c).1.trans (F.shapeLE_shapeX j)

theorem normBound_sumExprX (K c : ℕ) : ∀ τ : Tuple,
    (F.sumExprX K c τ).normBound (boxNorms F.n F.C F.H F.D) ≤ F.normSumW F.tfX F.nbX K τ
  | [] => Nat.le_refl 0
  | (j, w) :: τ => by
    change (w * F.D ^ (K - (F.tfX j).m)).natAbs *
        (SPoly.qE ((F.tS j).q.getD c [])).normBound (boxNorms F.n F.C F.H F.D) +
        (F.sumExprX K c τ).normBound (boxNorms F.n F.C F.H F.D) ≤
      w.natAbs * F.D.natAbs ^ (K - (F.tfX j).m) * F.nbX j + F.normSumW F.tfX F.nbX K τ
    rw [SPoly.normBound_qE, Int.natAbs_mul, Int.natAbs_pow]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (F.bounded_tS j c).2) (normBound_sumExprX K c τ)

theorem evalInt_sumExprX {B K c : ℕ} : ∀ {τ : Tuple}, (∀ jw ∈ τ, (F.tS jw.1).ok = true) →
    (F.sumExprX K c τ).evalInt (boxPacked F.n F.shapeX B F.C F.H F.D) =
      (F.valueSumW F.tfX (F.valX B) K τ).getD c 0
  | [], _ => by simp [sumExprX, valueSumW, Expr.evalInt]
  | (j, w) :: τ, h => by
    have hj := h (j, w) List.mem_cons_self
    rw [valueSumW, getD_zipD (z := (0 : ℤ)) (f := (· + ·)) (by simp),
      getD_map_of_eq (f := fun v : ℤ ↦ w * F.D ^ (K - (F.tfX j).m) * v) (z := 0) (mul_zero _),
      ← evalInt_sumExprX fun jw hjw ↦ h jw (List.mem_cons_of_mem _ hjw), valX, getD_valS]
    change (w * F.D ^ (K - (F.tfX j).m)) *
        (SPoly.qE ((F.tS j).q.getD c [])).evalInt (boxPacked F.n F.shapeX B F.C F.H F.D) +
        (F.sumExprX K c τ).evalInt (boxPacked F.n F.shapeX B F.C F.H F.D) = _
    rw [SPoly.evalInt_qE, SPoly.run_congr_lenOk (fun c : ℤ ↦ c)
      (x' := pointW F.shapeX F.C F.H B) (fun i hi ↦ ?_) (F.lenOk_tS hj c)]
    simp only [boxPacked, getD_range_map_append, hi, ↓reduceIte, pointW]

theorem eval_sumExprX (y : ℕ → ℝ) (K c : ℕ) :
    ∀ τ : Tuple, (F.sumExprX K c τ).eval y = F.sumAtX y K c τ
  | [] => by simp [sumExprX, sumAtX]
  | (j, w) :: τ => by
    rw [sumExprX, Expr.eval_add, Expr.eval_mul, Expr.eval_const, SPoly.eval_qE,
      eval_sumExprX y K c τ, sumAtX, SPoly.run_re_int]

theorem sumAtX_congr {y y' : ℕ → ℝ} {K c : ℕ} : ∀ {τ : Tuple},
    (∀ jw ∈ τ, (F.tS jw.1).ok = true) → (∀ i < F.n, y i = y' i) →
      F.sumAtX y K c τ = F.sumAtX y' K c τ
  | [], _, _ => rfl
  | (j, w) :: τ, hok, h => by
    rw [sumAtX, sumAtX, SPoly.run_congr_lenOk Exact.re h (F.lenOk_tS (hok _ List.mem_cons_self) c),
      sumAtX_congr (fun jw hjw ↦ hok jw (List.mem_cons_of_mem _ hjw)) h]

theorem sumAtX_eq_sum (y : ℕ → ℝ) (K : ℕ) (τ : Tuple) :
    ∑ c ∈ Finset.range (ExactBasis.dim κ), ExactBasis.basis κ c * F.sumAtX y K c τ =
      (τ.map fun jw ↦ (jw.2 : ℝ) * ((F.D : ℝ) ^ (K - (F.tfX jw.1).m) *
        ∑ c ∈ Finset.range (ExactBasis.dim κ),
          ExactBasis.basis κ c * SPoly.run Exact.re y ((F.tS jw.1).q.getD c []))).sum := by
  induction τ with
  | nil => simp [sumAtX]
  | cons a τ ih =>
    obtain ⟨j, w⟩ := a
    rw [List.map_cons, List.sum_cons, ← ih]
    simp only [sumAtX, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    push_cast
    ring

/-- The packed numeral of coordinate `c` of a tuple of sparse terms at digit size `B` satisfies
the invariant of the engine, and its slot polynomial is the tuple's polynomial at the box
inputs. -/
theorem numeralsX_spec {K B c : ℕ} {τ : Tuple} (hB : 0 < B) (hsh : F.shapeX.length ≤ F.n)
    (hok : ∀ jw ∈ τ, (F.tS jw.1).ok = true)
    (hnb : F.normSumW F.tfX F.nbX K τ < 2 ^ (B - 1)) :
    Lay.Inv B F.shapeX
        (((F.valueSumW F.tfX (F.valX B) K τ).getD c 0 + offset F.n F.shapeX B).toNat) ∧
      ∀ y : ℕ → ℝ, Lay.pv F.shapeX (Lay.cf B
          (((F.valueSumW F.tfX (F.valX B) K τ).getD c 0 + offset F.n F.shapeX B).toNat)) y =
        F.sumAtX (fun i ↦ boxEnv F.n F.C F.H F.D (fun i ↦ y i) i) K c τ := by
  obtain ⟨hfit, hnorm, hv⟩ := box_packing_lt (F.sumExprX K c τ) (F.shape_sumExprX K c τ) F.C
    F.H F.D (F.normBound_sumExprX K c τ) B
  rw [← F.evalInt_sumExprX hok, hv]
  obtain ⟨hinv, hpv⟩ := Lay.inv_biased hsh hB hfit hnorm hnb
  refine ⟨hinv, fun y ↦ ?_⟩
  rw [hpv, Expr.eval_toDPoly, F.eval_sumExprX]
  simp only [eval_boxInputs]

/-- A sign at every point of the cube in the box inputs is the sign at `D x` for every point `x` of
the box. -/
theorem sign_of_cube {strict : Bool} {b : Box} (hden : 0 < b.den)
    (hC : F.C = b.centres F.n) (hH : F.H = b.widths F.n) (hD : F.D = 2 * b.den) {τ : Tuple}
    (hok : ∀ jw ∈ τ, (F.tS jw.1).ok = true) {K : ℕ}
    (hs : ∀ y : ℕ → ℝ, (∀ i, |y i| ≤ 1) → Sign strict (∑ c ∈ Finset.range (ExactBasis.dim κ),
      ExactBasis.basis κ c * F.sumAtX (fun i ↦ boxEnv F.n F.C F.H F.D (fun i ↦ y i) i) K c τ))
    {x : Fin F.n → ℝ} (hx : b.Mem F.n x) :
    Sign strict (∑ c ∈ Finset.range (ExactBasis.dim κ), ExactBasis.basis κ c *
      F.sumAtX (fun i ↦ (F.D : ℝ) * ext F.n x i) K c τ) := by
  choose y hy hyx using fun i : Fin F.n ↦ Box.exists_centred hden (hx i)
  set y' : ℕ → ℝ := fun k ↦ if h : k < F.n then y ⟨k, h⟩ else 0
  have hy' : ∀ k, |y' k| ≤ 1 := fun k ↦ by
    simp only [y']
    split_ifs
    · exact hy _
    · simp
  have hE : ∀ i < F.n, boxEnv F.n F.C F.H F.D (fun i ↦ y' i) i = (F.D : ℝ) * ext F.n x i := by
    intro i hi
    simp only [boxEnv, hi, ↓reduceDIte, y', hC, hH, hD, Box.centres, Box.widths,
      Box.getD_range_map _ _ _ hi, ext]
    have := hyx ⟨i, hi⟩
    push_cast at this ⊢
    linear_combination this
  refine (congrArg (Sign strict) (Finset.sum_congr rfl fun c _ ↦ ?_)).mp (hs y' hy')
  rw [F.sumAtX_congr hok hE]

/-- **Soundness of a tuple of sparse terms**: a tuple that the engine certifies on the frame box
`b` has a polynomial of the right sign at `D x` for every point `x` of the box. -/
theorem runTupleX_sound {strict : Bool} {depth B : ℕ} {b : Box} (hden : 0 < b.den)
    (hC : F.C = b.centres F.n) (hH : F.H = b.widths F.n) (hD : F.D = 2 * b.den)
    (hsh : F.shapeX.length ≤ F.n) (hB : 0 < B) {τ : Tuple}
    (hok : ∀ jw ∈ τ, (F.tS jw.1).ok = true)
    (hnb : F.normSumW F.tfX F.nbX (tupleKW F.tfX τ) τ < 2 ^ (B - 1))
    (h : F.runTupleX strict depth B τ = true) {x : Fin F.n → ℝ} (hx : b.Mem F.n x) :
    Sign strict (∑ c ∈ Finset.range (ExactBasis.dim κ), ExactBasis.basis κ c *
      F.sumAtX (fun i ↦ (F.D : ℝ) * ext F.n x i) (tupleKW F.tfX τ) c τ) := by
  simp only [runTupleX, runTupleW, Bool.and_eq_true] at h
  obtain ⟨-, hrun⟩ := h
  have hinv : ∀ N ∈ (List.range (ExactBasis.dim κ)).map fun c ↦
      ((F.valueSumW F.tfX (F.valX B) (tupleKW F.tfX τ) τ).getD c 0 +
        offset F.n F.shapeX B).toNat, Lay.Inv B F.shapeX N := by
    intro N hN
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hN
    exact (F.numeralsX_spec hB hsh hok hnb).1
  refine F.sign_of_cube hden hC hH hD hok (fun y' hy' ↦ ?_) hx
  have hs := Lay.runDiv_sound hB hsh depth F.W F.divisors hinv (by simp) hrun y' hy'
  unfold Lay.val at hs
  refine (congrArg (Sign strict) (Finset.sum_congr rfl fun c hc ↦ ?_)).mp hs
  rw [Box.getD_range_map _ _ _ (Finset.mem_range.mp hc), (F.numeralsX_spec hB hsh hok hnb).2 y']

/-- The numeral of one sparse term at digit size `B` satisfies the invariant of the engine, and its
slot polynomial is the term's coordinate at the box inputs. -/
theorem valX_spec {B j c : ℕ} (hB : 0 < B) (hsh : F.shapeX.length ≤ F.n)
    (hok : (F.tS j).ok = true) (hnb : F.nbX j < 2 ^ (B - 1)) :
    Lay.Inv B F.shapeX (((F.valX B j).getD c 0 + offset F.n F.shapeX B).toNat) ∧
      ∀ y : ℕ → ℝ, Lay.pv F.shapeX (Lay.cf B
          (((F.valX B j).getD c 0 + offset F.n F.shapeX B).toNat)) y =
        SPoly.run Exact.re (fun i ↦ boxEnv F.n F.C F.H F.D (fun i ↦ y i) i)
          ((F.tS j).q.getD c []) := by
  have hv : (F.valueSumW F.tfX (F.valX B) (F.tfX j).m [(j, 1)]).getD c 0 =
      (F.valX B j).getD c 0 := by
    rw [valueSumW, getD_zipD (add_zero (0 : ℤ)), valueSumW,
      getD_map_of_eq (z := (0 : ℤ)) (mul_zero _)]
    simp
  have hn : F.normSumW F.tfX F.nbX (F.tfX j).m [(j, 1)] = F.nbX j := by
    simp [normSumW]
  have hs := F.numeralsX_spec (K := (F.tfX j).m) (c := c) (τ := [(j, 1)]) hB hsh
    (by simpa using hok) (hn ▸ hnb)
  rw [hv] at hs
  refine ⟨hs.1, fun y ↦ ?_⟩
  rw [hs.2 y]
  simp [sumAtX]

omit [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] in
theorem nb_le_normSumW (tf : ℕ → TermFrame) (nb : ℕ → ℕ) (K : ℕ) (hD : F.D ≠ 0) :
    ∀ {τ : Tuple} {jw : ℕ × ℤ}, jw ∈ τ → jw.2 ≠ 0 → nb jw.1 ≤ F.normSumW tf nb K τ
  | [], _, h, _ => absurd h List.not_mem_nil
  | (j, w) :: τ, jw, h, hw => by
    rw [normSumW]
    rcases List.mem_cons.mp h with rfl | h
    · have h₁ : 1 ≤ w.natAbs := Int.natAbs_pos.mpr hw
      have h₂ : 1 ≤ F.D.natAbs ^ (K - (tf j).m) :=
        Nat.one_le_pow _ _ (Int.natAbs_pos.mpr hD)
      have : nb j ≤ w.natAbs * F.D.natAbs ^ (K - (tf j).m) * nb j :=
        Nat.le_mul_of_pos_left _ (Nat.mul_pos h₁ h₂)
      exact this.trans (Nat.le_add_right _ _)
    · exact (nb_le_normSumW tf nb K hD h hw).trans (Nat.le_add_left _ _)

/-- The scaled sum of a tuple's terms: `∑ w D^(Kmax - mⱼ) qⱼ = D^(Kmax - K) ∑ w D^(K - mⱼ) qⱼ`. -/
theorem sumAtX_scale (y : ℕ → ℝ) {K Kmax : ℕ} (c : ℕ) (hK : K ≤ Kmax) :
    ∀ {τ : Tuple}, (∀ jw ∈ τ, (F.tfX jw.1).m ≤ K) →
      (τ.map fun jw ↦ (jw.2 : ℝ) * (((F.D ^ (Kmax - (F.tfX jw.1).m) : ℤ) : ℝ) *
        SPoly.run Exact.re y ((F.tS jw.1).q.getD c []))).sum =
      (F.D : ℝ) ^ (Kmax - K) * F.sumAtX y K c τ
  | [], _ => by simp [sumAtX]
  | (j, w) :: τ, hm => by
    rw [List.map_cons, List.sum_cons, sumAtX_scale y c hK fun jw hjw ↦ hm jw
      (List.mem_cons_of_mem _ hjw), sumAtX]
    have hj := hm (j, w) List.mem_cons_self
    have hp : (F.D : ℝ) ^ (Kmax - (F.tfX j).m) =
        (F.D : ℝ) ^ (Kmax - K) * (F.D : ℝ) ^ (K - (F.tfX j).m) := by
      rw [← pow_add]
      congr 1
      simp only at hj
      omega
    push_cast
    rw [hp]
    ring

/-- **Soundness of the truncated test of a tuple of sparse terms**, on the cube in the box
inputs. -/
theorem tPassX_sound {strict : Bool} {B : ℕ} (hD : 0 < F.D)
    (hsh : F.shapeX.length ≤ F.n) (hB : 0 < B) {τ : Tuple}
    (hok : ∀ jw ∈ τ, (F.tS jw.1).ok = true)
    (hnb : F.normSumW F.tfX F.nbX (tupleKW F.tfX τ) τ < 2 ^ (B - 1))
    (h : F.tPassX strict B τ = true) {y : ℕ → ℝ} (hy : ∀ i, |y i| ≤ 1) :
    Sign strict (∑ c ∈ Finset.range (ExactBasis.dim κ), ExactBasis.basis κ c *
      F.sumAtX (fun i ↦ boxEnv F.n F.C F.H F.D (fun i ↦ y i) i) (tupleKW F.tfX τ) c τ) := by
  simp only [tPassX, tPassW] at h
  set K := tupleKW F.tfX τ with hKdef
  set s := F.tShiftK F.tfX F.nbX F.ts.length K with hs
  set L := DPoly.slots F.shapeX with hL
  set N : ℕ → ℕ → ℕ := fun j c ↦ ((F.valX B j).getD c 0 + offset F.n F.shapeX B).toNat with hN
  set mult : ℕ → ℤ := fun j ↦ F.D ^ (K - (F.tfX j).m) with hmult
  have hB' : 0 < tBits κ := by simp [tBits]
  have hsg := Lay.tPass_sound (κ := κ) hB' hsh s
    (fun j c q ↦ Lay.cf B (N j c) q * mult j / 2 ^ s)
    (fun j c y ↦ (mult j : ℝ) * SPoly.run Exact.re (fun i ↦ boxEnv F.n F.C F.H F.D (fun i ↦ y i) i)
      ((F.tS j).q.getD c []))
    (fun jw hjw hw c hc ↦ ?_) h hy
  · have hm : ∀ jw ∈ τ, (F.tfX jw.1).m ≤ K := fun jw hjw ↦ le_tupleKW F.tfX hjw
    simp only [hmult] at hsg
    refine (congrArg (Sign strict) (Finset.sum_congr rfl fun c _ ↦ ?_)).mp hsg
    rw [F.sumAtX_scale _ c le_rfl hm, Nat.sub_self, pow_zero, one_mul]
  · have hnbj : F.nbX jw.1 < 2 ^ (B - 1) :=
      (F.nb_le_normSumW F.tfX F.nbX K hD.ne' hjw hw).trans_lt hnb
    obtain ⟨hinv, hpv⟩ := F.valX_spec (c := c) hB hsh (hok jw hjw) hnbj
    have hget : (F.tTermX B K jw.1).getD c (0, 0) =
        Lay.truncL B (tBits κ) s (2 ^ (B - 1)) (mult jw.1) L (N jw.1 c) := by
      rw [tTermX, tTermF, tTerm, Box.getD_range_map _ _ _ hc]
    have hd : ∀ q, ((dig B (N jw.1 c) q : ℤ) - ((2 ^ (B - 1) : ℕ) : ℤ)) * mult jw.1 / 2 ^ s =
        Lay.cf B (N jw.1 c) q * mult jw.1 / 2 ^ s := fun q ↦ by
      rw [Lay.cf]
      push_cast
      ring
    rw [hget, Lay.truncL_eq _ _ _ _ _ _ _ hinv.1]
    refine ⟨Num.snum_congr fun q _ ↦ (hd q).symm, le_of_eq ?_, fun y hy ↦ ?_⟩
    · exact Finset.sum_congr rfl fun q _ ↦ by rw [hd q]
    · rw [← hpv y]
      exact Lay.abs_pv_trunc_le _ _ _ _ hy

/-- **The truncations of values at bounded precision** (`ftL`): each value present, with its
truncation and an error at most the largest; zero beyond the values. -/
theorem ftL_spec {fc : FPoly.Ctx} {B' s : ℕ} {mult : ℤ} :
    ∀ {xs : List (Option FPoly.FP)} {l : List (ℤ × ℕ)} {ρ : ℕ}, ftL fc B' s mult xs = some (l, ρ) →
      ∀ c, (c < xs.length → ∃ x, xs[c]? = some (some x) ∧
        l.getD c (0, 0) = (FPoly.trunc fc B' s mult x).1 ∧ (FPoly.trunc fc B' s mult x).2 ≤ ρ) ∧
      (xs.length ≤ c → l.getD c (0, 0) = (0, 0))
  | [], l, ρ, h, c => by
    simp only [ftL, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun hc ↦ absurd hc (Nat.not_lt_zero _), fun _ ↦ rfl⟩
  | none :: _, _, _, h, _ => by simp [ftL] at h
  | some x :: xs, l, ρ, h, c => by
    simp only [ftL] at h
    obtain ⟨r, hr, h⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rcases c with _ | c
    · exact ⟨fun _ ↦ ⟨x, rfl, rfl, le_max_left _ _⟩, fun hc ↦ absurd hc (by simp)⟩
    · obtain ⟨h₁, h₂⟩ := ftL_spec hr c
      refine ⟨fun hc ↦ ?_, fun hc ↦ ?_⟩
      · obtain ⟨x', hx', hl, hρ⟩ := h₁ (by simpa using hc)
        exact ⟨x', by simpa using hx', by simpa using hl, hρ.trans (le_max_right _ _)⟩
      · simpa using h₂ (by simpa using hc)

omit [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] in
/-- The box inputs of the values at bounded precision are those of the frame. -/
theorem run_fCtx {q : SPoly ℤ} (hq : SPoly.lenOk F.n q = true) {sh : List ℕ} (y : ℕ → ℝ) :
    SPoly.run (fun a : ℤ ↦ (a : ℝ)) (FPoly.X (F.fCtx sh) y) q =
      SPoly.run Exact.re (fun i ↦ boxEnv F.n F.C F.H F.D (fun i ↦ y i) i) q := by
  rw [SPoly.run_re_int]
  refine SPoly.run_congr_lenOk _ (fun i hi ↦ ?_) hq
  simp [FPoly.X, fCtx, boxEnv, hi]

/-- **The truncations of the sparse terms' values at bounded precision** (`ftTermF` at any digit
size `B'` and shift `s`, in a tuple of denominator degree `K`): where every term of the tuple has
them, they are numerals of digits `td j c` within their error of `D^(K - mⱼ)` times the term's
coordinate `c` on the cube. -/
theorem ftTermX_spec {B' s K : ℕ} {τ : Tuple}
    (hok : ∀ jw ∈ τ, (F.tS jw.1).ok = true)
    (hsome : ∀ jw ∈ τ,
      (ftTermF (F.fCtx F.shapeX) B' s F.D K F.tfX F.fvalX jw.1).isSome = true) :
    ∃ td : ℕ → ℕ → ℕ → ℤ, ∀ jw ∈ τ, jw.2 ≠ 0 → ∀ c < ExactBasis.dim κ,
      (((ftTermF (F.fCtx F.shapeX) B' s F.D K F.tfX F.fvalX jw.1).getD ([], 0)).1.getD c
          (0, 0)).1 = Num.snum B' (td jw.1 c) (DPoly.slots F.shapeX) ∧
        Lay.l1 F.shapeX (td jw.1 c) ≤
          (((ftTermF (F.fCtx F.shapeX) B' s F.D K F.tfX F.fvalX jw.1).getD ([], 0)).1.getD c
            (0, 0)).2 ∧
        ∀ y : ℕ → ℝ, (∀ i, |y i| ≤ 1) →
          |((F.D ^ (K - (F.tfX jw.1).m) : ℤ) : ℝ) * SPoly.run Exact.re
              (fun i ↦ boxEnv F.n F.C F.H F.D (fun i ↦ y i) i) ((F.tS jw.1).q.getD c []) -
            2 ^ s * Lay.pv F.shapeX (td jw.1 c) y| ≤
          (((ftTermF (F.fCtx F.shapeX) B' s F.D K F.tfX F.fvalX jw.1).getD ([], 0)).2 : ℝ) *
            2 ^ s := by
  set fc := F.fCtx F.shapeX with hfc
  set ftd := ftTermF fc B' s F.D K F.tfX F.fvalX with hftd
  set mult : ℕ → ℤ := fun j ↦ F.D ^ (K - (F.tfX j).m) with hmult
  set P : ℕ → ℕ → (ℕ → ℝ) → ℝ := fun j c y ↦ (mult j : ℝ) *
    SPoly.run Exact.re (fun i ↦ boxEnv F.n F.C F.H F.D (fun i ↦ y i) i) ((F.tS j).q.getD c [])
    with hP
  have hfB : 0 < fc.B := by simp [fc, fCtx]
  -- The truncated digits of each term and coordinate.
  have hex : ∀ jw ∈ τ, ∀ c < ExactBasis.dim κ, ∃ td : ℕ → ℤ,
      (((ftd jw.1).getD ([], 0)).1.getD c (0, 0)).1 = Num.snum B' td (DPoly.slots F.shapeX) ∧
      Lay.l1 F.shapeX td ≤ (((ftd jw.1).getD ([], 0)).1.getD c (0, 0)).2 ∧
      ∀ y : ℕ → ℝ, (∀ i, |y i| ≤ 1) →
        |P jw.1 c y - 2 ^ s * Lay.pv F.shapeX td y| ≤
          (((ftd jw.1).getD ([], 0)).2 : ℝ) * 2 ^ s := by
    intro jw hjw c _
    obtain ⟨⟨l, ρ⟩, hlρ⟩ := Option.isSome_iff_exists.mp (hsome jw hjw)
    rw [hlρ, Option.getD_some]
    obtain ⟨h₁, h₂⟩ := ftL_spec hlρ c
    by_cases hc : c < (F.fvalX jw.1).length
    · obtain ⟨x, hx, hl, hρ⟩ := h₁ hc
      have hlen : c < ((F.tS jw.1).q).length := by simpa [fvalX, fvalW] using hc
      have hq : (F.tS jw.1).q.getD c [] = (F.tS jw.1).q[c] := by
        rw [List.getD_eq_getElem _ _ hlen]
      have hfx : FPoly.fE fc (SPoly.fuelOf ((F.tS jw.1).q[c])) 0 ((F.tS jw.1).q[c]) = some x := by
        simpa [fvalX, fvalW, hlen] using hx
      obtain ⟨td, htv, htl, herr⟩ := FPoly.trunc_spec (FPoly.fE_spec hfx) hfB B' s (mult jw.1)
      have hlen' := F.lenOk_tS (hok jw hjw) c
      rw [hq] at hlen'
      refine ⟨td, by rw [hl]; exact htv, by rw [hl]; exact htl.le, fun y hy ↦ ?_⟩
      have := herr y hy
      rw [F.run_fCtx hlen'] at this
      simp only [hP, hq]
      refine this.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      exact_mod_cast hρ
    · rw [h₂ (by omega)]
      have hq : (F.tS jw.1).q.getD c [] = [] :=
        List.getD_eq_default _ _ (by simp [fvalX, fvalW] at hc; omega)
      refine ⟨fun _ ↦ 0, by simp [Num.snum], by simp [Lay.l1], fun y _ ↦ ?_⟩
      simp only [hP, hq, SPoly.run_nil, mul_zero, Lay.pv_zero, sub_zero, abs_zero]
      positivity
  classical
  refine ⟨fun j c ↦
    if hj : ∃ td : ℕ → ℤ,
        (((ftd j).getD ([], 0)).1.getD c (0, 0)).1 = Num.snum B' td (DPoly.slots F.shapeX) ∧
        Lay.l1 F.shapeX td ≤ (((ftd j).getD ([], 0)).1.getD c (0, 0)).2 ∧
        ∀ y : ℕ → ℝ, (∀ i, |y i| ≤ 1) →
          |P j c y - 2 ^ s * Lay.pv F.shapeX td y| ≤ (((ftd j).getD ([], 0)).2 : ℝ) * 2 ^ s
    then Classical.choose hj else fun _ ↦ 0, fun jw hjw _ c hc ↦ ?_⟩
  have hj := hex jw hjw c hc
  simp only [hj, ↓reduceDIte]
  exact Classical.choose_spec hj

/-- **Soundness of the truncated test at bounded precision of a tuple of sparse terms**, on the
cube in the box inputs. -/
theorem tPassFX_sound {strict : Bool} (hsh : F.shapeX.length ≤ F.n) {τ : Tuple}
    (hok : ∀ jw ∈ τ, (F.tS jw.1).ok = true)
    (h : F.tPassFX strict τ = true) {y : ℕ → ℝ} (hy : ∀ i, |y i| ≤ 1) :
    Sign strict (∑ c ∈ Finset.range (ExactBasis.dim κ), ExactBasis.basis κ c *
      F.sumAtX (fun i ↦ boxEnv F.n F.C F.H F.D (fun i ↦ y i) i) (tupleKW F.tfX τ) c τ) := by
  simp only [tPassFX, tPassFW, ftTermX, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hsome, h⟩ := h
  obtain ⟨td, htd⟩ := F.ftTermX_spec hok hsome
  have hsg := Lay.tPass_sound (κ := κ) (by simp [tBits]) hsh _ td (fun j c y ↦
    ((F.D ^ (tupleKW F.tfX τ - (F.tfX j).m) : ℤ) : ℝ) * SPoly.run Exact.re
      (fun i ↦ boxEnv F.n F.C F.H F.D (fun i ↦ y i) i) ((F.tS j).q.getD c [])) htd h hy
  have hm : ∀ jw ∈ τ, (F.tfX jw.1).m ≤ tupleKW F.tfX τ := fun jw hjw ↦ le_tupleKW F.tfX hjw
  refine (congrArg (Sign strict) (Finset.sum_congr rfl fun c _ ↦ ?_)).mp hsg
  rw [F.sumAtX_scale _ c le_rfl hm, Nat.sub_self, pow_zero, one_mul]

/-- **Soundness of the top box at bounded precision of a tuple of sparse terms**, on the cube in
the box inputs. -/
theorem procFX_sound {strict : Bool} {depth : ℕ} {τ : Tuple}
    (hok : ∀ jw ∈ τ, (F.tS jw.1).ok = true)
    (h : F.procFX strict depth τ = true) {y : ℕ → ℝ} (hy : ∀ i, |y i| ≤ 1) :
    Sign strict (∑ c ∈ Finset.range (ExactBasis.dim κ), ExactBasis.basis κ c *
      F.sumAtX (fun i ↦ boxEnv F.n F.C F.H F.D (fun i ↦ y i) i) (tupleKW F.tfX τ) c τ) := by
  simp only [procFX, procFW, ptTermX, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hsome, h⟩ := h
  obtain ⟨td, htd⟩ := F.ftTermX_spec hok hsome
  have hsg := fTop_sound (κ := κ) (by simp [pBits]) _ td (fun j c y ↦
    ((F.D ^ (tupleKW F.tfX τ - (F.tfX j).m) : ℤ) : ℝ) * SPoly.run Exact.re
      (fun i ↦ boxEnv F.n F.C F.H F.D (fun i ↦ y i) i) ((F.tS j).q.getD c [])) htd h hy
  have hm : ∀ jw ∈ τ, (F.tfX jw.1).m ≤ tupleKW F.tfX τ := fun jw hjw ↦ le_tupleKW F.tfX hjw
  refine (congrArg (Sign strict) (Finset.sum_congr rfl fun c _ ↦ ?_)).mp hsg
  rw [F.sumAtX_scale _ c le_rfl hm, Nat.sub_self, pow_zero, one_mul]

theorem valAt_wtW (X : ℕ → ℝ) (K c : ℕ) : ∀ τ : Tuple,
    WTerms.valAt c X (F.wtW F.tfX (fun j ↦ (F.tS j).q) K τ) = F.sumAtX X K c τ
  | [] => rfl
  | (j, w) :: τ => by
    change ((w * F.D ^ (K - (F.tfX j).m) : ℤ) : ℝ) *
        SPoly.run (fun a : ℤ ↦ (a : ℝ)) X ((F.tS j).q.getD c []) +
        WTerms.valAt c X (F.wtW F.tfX (fun j ↦ (F.tS j).q) K τ) = _
    rw [valAt_wtW X K c τ, sumAtX, SPoly.run_re_int]

theorem fit_wtW (K : ℕ) {τ : Tuple} (hok : ∀ jw ∈ τ, (F.tS jw.1).ok = true) :
    WTerms.Fit F.n F.shapeX (F.wtW F.tfX (fun j ↦ (F.tS j).q) K τ) := by
  intro x hx c
  obtain ⟨jw, hjw, rfl⟩ := List.mem_map.mp hx
  exact ⟨(F.bounded_tS jw.1 c).1.trans (F.shapeLE_shapeX jw.1), F.lenOk_tS (hok jw hjw) c⟩

/-- **Soundness of rupert's procedure on a tuple of sparse terms**, on the cube in the box
inputs. -/
theorem runTupleNX_sound {strict : Bool} {depth B : ℕ} (hsh : F.shapeX.length ≤ F.n)
    (hB : 0 < B) {τ : Tuple} (hok : ∀ jw ∈ τ, (F.tS jw.1).ok = true)
    (hnb : F.normSumW F.tfX F.nbX (tupleKW F.tfX τ) τ < 2 ^ (B - 1))
    (h : F.runTupleNX strict depth B τ = true) {y : ℕ → ℝ} (hy : ∀ i, |y i| ≤ 1) :
    Sign strict (∑ c ∈ Finset.range (ExactBasis.dim κ), ExactBasis.basis κ c *
      F.sumAtX (fun i ↦ boxEnv F.n F.C F.H F.D (fun i ↦ y i) i) (tupleKW F.tfX τ) c τ) := by
  have hfit := F.fit_wtW (tupleKW F.tfX τ) hok
  have hE : ∀ i < F.n, boxEnv F.n F.C F.H F.D (fun i ↦ y i) i = envK F.C F.H 0 y i := by
    intro i hi
    simp [boxEnv, hi, envK]
  have hcomb : (∑ c ∈ Finset.range (ExactBasis.dim κ), ExactBasis.basis κ c *
      F.sumAtX (fun i ↦ boxEnv F.n F.C F.H F.D (fun i ↦ y i) i) (tupleKW F.tfX τ) c τ) =
      comb (κ := κ) (F.wtW F.tfX (fun j ↦ (F.tS j).q) (tupleKW F.tfX τ) τ)
        (envK F.C F.H 0 y) := by
    unfold comb
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [← F.valAt_wtW, WTerms.valAt_congr hE hfit]
  rw [hcomb]
  have he : (fun i ↦ (F.C.getD i 0 : ℝ) + F.H.getD i 0 * y i) = envK F.C F.H 0 y := by
    funext i
    simp [envK]
  have hNs : ∀ c < ExactBasis.dim κ,
      Lay.Inv B F.shapeX ((F.numsW F.shapeX F.tfX (F.valX B) B τ).getD c 0) ∧
        ∀ y' : ℕ → ℝ, Lay.pv F.shapeX (Lay.cf B ((F.numsW F.shapeX F.tfX (F.valX B) B τ).getD c 0))
          y' = WTerms.valAt c (fun i ↦ (F.C.getD i 0 : ℝ) + F.H.getD i 0 * y' i)
            (F.wtW F.tfX (fun j ↦ (F.tS j).q) (tupleKW F.tfX τ) τ) := by
    intro c hc
    obtain ⟨hinv, hpv⟩ := F.numeralsX_spec (c := c) hB hsh hok hnb
    rw [numsW, Box.getD_range_map _ _ _ hc]
    refine ⟨hinv, fun y' ↦ ?_⟩
    rw [hpv y', ← F.valAt_wtW]
    exact WTerms.valAt_congr (fun i hi ↦ by simp [boxEnv, hi]) hfit
  simp only [runTupleNX, runTupleNW, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ((h | ⟨-, h⟩) | h) | h
  · rw [← he]
    exact topT_sound hB hsh hfit (by simp [numsW]) hNs (by simp [topT, h]) hy
  · rw [← he]
    exact procB_sound hfit (by simp [numsW]) hNs h hy
  · rw [← he]
    exact procA_sound hsh hfit h hy
  · exact boxRec_sound hsh hfit (fun x hx c t ht ↦ WTerms.le_deg hx c ht) depth false F.C F.H 0
      F.W h y hy

/-- **Soundness of a tuple of sparse terms with the truncated test and rupert's procedure**:
`runTupleX_sound` for `runTupleXT`. -/
theorem runTupleXT_sound {strict : Bool} {depth B : ℕ} {b : Box} (hden : 0 < b.den)
    (hC : F.C = b.centres F.n) (hH : F.H = b.widths F.n) (hD : F.D = 2 * b.den)
    (hsh : F.shapeX.length ≤ F.n) (hB : 0 < B) {τ : Tuple}
    (hok : ∀ jw ∈ τ, (F.tS jw.1).ok = true)
    (hnb : F.normSumW F.tfX F.nbX (tupleKW F.tfX τ) τ < 2 ^ (B - 1))
    (h : F.runTupleXT strict depth B τ = true) {x : Fin F.n → ℝ} (hx : b.Mem F.n x) :
    Sign strict (∑ c ∈ Finset.range (ExactBasis.dim κ), ExactBasis.basis κ c *
      F.sumAtX (fun i ↦ (F.D : ℝ) * ext F.n x i) (tupleKW F.tfX τ) c τ) := by
  simp only [runTupleXT, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ((h | ⟨-, h | ⟨-, h⟩⟩) | h) | h
  · exact F.runTupleX_sound hden hC hH hD hsh hB hok hnb h hx
  · exact F.sign_of_cube hden hC hH hD hok (fun y hy ↦ F.tPassFX_sound hsh hok h hy) hx
  · exact F.sign_of_cube hden hC hH hD hok (fun y hy ↦ F.procFX_sound hok h hy) hx
  · have hD0 : 0 < F.D := by rw [hD]; omega
    exact F.sign_of_cube hden hC hH hD hok (fun y hy ↦ F.tPassX_sound hD0 hsh hB hok hnb h hy) hx
  · exact F.sign_of_cube hden hC hH hD hok (fun y hy ↦ F.runTupleNX_sound hsh hB hok hnb h hy) hx

end Frame

/-- **The sparse sign check of weighted combinations of pulled-back polynomials** on the box `b`,
with at most `depth` bisections along each branch, in the bisection order `o` (`bisW`;
`checkX_sound`): `check` with the terms computed sparsely. -/
def checkX (n : ℕ) (ts : List (Term κ)) (strict : Bool) (depth : ℕ) (b : Box) (τs : List Tuple)
    (o : List (ℕ × ℕ) := []) : Bool :=
  (frameOf n ts b (bisW n depth (b.widths n) o)).checkXF b.den strict depth τs

theorem den_pos_of_checkX {n : ℕ} {ts : List (Term κ)} {strict : Bool} {depth : ℕ} {b : Box}
    {τs : List Tuple} {o : List (ℕ × ℕ)} (h : checkX n ts strict depth b τs o = true) :
    0 < b.den := by
  rw [checkX, Frame.checkXF_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

/-- **Soundness of the sparse sign check**, with the conclusion of `check_sound`. At every point
`x` of the box and for every checked tuple, each term's polynomial is `c x^eⱼ sⱼ` with one
`c > 0`, and `∑ wⱼ sⱼ` is positive (`strict`) or nonnegative. -/
theorem checkX_sound {n : ℕ} {ts : List (Term κ)} {strict : Bool} {depth : ℕ} {b : Box}
    {τs : List Tuple} {o : List (ℕ × ℕ)} (h : checkX n ts strict depth b τs o = true) :
    ∀ τ ∈ τs, ∀ x : Fin n → ℝ, b.Mem n x → ∃ c : ℝ, 0 < c ∧ ∃ s : ℕ → ℝ,
      (∀ jw ∈ τ, (ts.getD jw.1 default).G.run Exact.re (ext n x) =
        c * monoVal n (ts.getD jw.1 default).e x * s jw.1) ∧
      Sign strict (τ.map fun jw ↦ (jw.2 : ℝ) * s jw.1).sum := by
  rw [checkX, Frame.checkXF_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hden, hsh⟩, hok⟩, hc⟩ := h
  set F := frameOf n ts b (bisW n depth (b.widths n) o) with hFdef
  have hC : ∀ i, F.C.getD i 0 = if i < n then b.lo.getD i 0 + b.hi.getD i 0 else 0 := by
    intro i
    split_ifs with hi
    · exact Box.getD_range_map _ _ _ hi
    · exact List.getD_eq_default _ _ (by simp [F, frameOf, Box.centres]; omega)
  have hH : ∀ i, F.H.getD i 0 = if i < n then b.hi.getD i 0 - b.lo.getD i 0 else 0 := by
    intro i
    split_ifs with hi
    · exact Box.getD_range_map _ _ _ hi
    · exact List.getD_eq_default _ _ (by simp [F, frameOf, Box.widths]; omega)
  have hF : ∀ i, F.H.getD i 0 ≠ 0 → i < n := fun i hi ↦ by
    rw [hH] at hi
    split_ifs at hi with h₁
    · exact h₁
    · exact absurd rfl hi
  have hD : F.D = 2 * b.den := rfl
  have hD0 : (F.D : ℝ) ≠ 0 := by
    rw [hD]
    push_cast
    positivity
  intro τ hτ x hx
  have hsign := F.runTupleXT_sound hden rfl rfl hD hsh (Lay.digitsFor_pos _ _) (hok τ hτ)
    ((le_foldr_max_of_mem (fun τ ↦ F.normSumW F.tfX F.nbX (Frame.tupleKW F.tfX τ) τ) hτ).trans_lt
      (Lay.le_digitsFor _ _)) (hc τ hτ) hx
  have hx' : ∀ i : Fin n, F.H.getD i 0 = 0 → (F.C.getD i 0 : ℝ) = F.D * x i := by
    intro i h0
    simp only [hH, i.2, ↓reduceIte] at h0
    simp only [hC, i.2, ↓reduceIte, hD]
    have hlh : b.hi.getD i 0 = b.lo.getD i 0 := by omega
    have hd : (0 : ℝ) < b.den := by exact_mod_cast hden
    obtain ⟨h₁, h₂⟩ := hx i
    rw [hlh] at h₂
    have hxi : x i = (b.lo.getD i 0 : ℝ) / b.den := le_antisymm h₂ h₁
    rw [hxi, hlh]
    push_cast
    field_simp
    ring
  have hDpos : (0 : ℝ) < F.D := by
    rw [hD]
    push_cast
    positivity
  refine ⟨((F.D : ℝ) ^ Frame.tupleKW F.tfX τ)⁻¹, by positivity,
    fun j ↦ (F.D : ℝ) ^ (Frame.tupleKW F.tfX τ - (F.tfX j).m) *
      ∑ c ∈ Finset.range (ExactBasis.dim κ),
        ExactBasis.basis κ c * SPoly.run Exact.re (fun i ↦ (F.D : ℝ) * ext n x i)
          ((F.tS j).q.getD c []),
    fun jw hjw ↦ ?_, ?_⟩
  · have hokj := hok τ hτ jw hjw
    obtain ⟨-, hteq⟩ := F.tS_of_ok hokj
    rw [hteq] at hokj
    have hn : F.n = n := rfl
    have hrun := termS_run hokj hF (fun i hi ↦ by
      simp only [hC, show ¬i < n by omega, ↓reduceIte]) hD0 x hx'
    change (F.term jw.1).G.run Exact.re (ext F.n x) = _
    rw [hrun]
    change ((F.D : ℝ) ^ (termS F.n (F.term jw.1) F.C F.H F.D).m)⁻¹ *
        monoVal n (F.term jw.1).e x * ∑ c ∈ Finset.range (ExactBasis.dim κ),
          ExactBasis.basis κ c * SPoly.run Exact.re (fun i ↦ (F.D : ℝ) * ext n x i)
            ((termS F.n (F.term jw.1) F.C F.H F.D).q.getD c []) = _
    rw [← hteq]
    have hm := Frame.le_tupleKW F.tfX hjw
    have hpow : (F.D : ℝ) ^ Frame.tupleKW F.tfX τ =
        (F.D : ℝ) ^ (Frame.tupleKW F.tfX τ - (F.tfX jw.1).m) * (F.D : ℝ) ^ (F.tfX jw.1).m := by
      rw [← pow_add, Nat.sub_add_cancel hm]
    have h1 : (F.D : ℝ) ^ (F.tfX jw.1).m ≠ 0 := pow_ne_zero _ hD0
    have h2 : (F.D : ℝ) ^ (Frame.tupleKW F.tfX τ - (F.tfX jw.1).m) ≠ 0 := pow_ne_zero _ hD0
    rw [hpow]
    field_simp
    have hm' : (F.tfX jw.1).m = (F.tS jw.1).m := rfl
    have he' : ts.getD jw.1 default = F.term jw.1 := rfl
    rw [hm', he']
    ring
  · rw [Frame.sumAtX_eq_sum] at hsign
    exact hsign

/-! ### Combinations -/

namespace Frame

variable (F : Frame κ)

/-- Choice `j'` of part `i` has the sign, the frame and the quotients `tq` of choice `j`: all that
the tests of a tuple read of a term (`sameData` with no monomial checks, and the values compared
through the quotients they are computed from). -/
def sameDataT (K : ℕ) (σ : ℕ → ℕ → ℤ) (tf : ℕ → TermFrame) (tq : ℕ → List (SPoly ℤ))
    (i j' j : ℕ) : Bool :=
  σ i j' == σ i j && (tf (i * K + j')).ok == (tf (i * K + j)).ok &&
    (tf (i * K + j')).m == (tf (i * K + j)).m && decide (tq (i * K + j') = tq (i * K + j))

theorem sameDataT_rep {K : ℕ} {σ : ℕ → ℕ → ℤ} {tf : ℕ → TermFrame} {tq : ℕ → List (SPoly ℤ)}
    {x' x : ℕ × ℤ}
    (h : RepEntry K σ (fun i j' j ↦ j' = j ∨ sameDataT K σ tf tq i j' j = true) x' x) :
    x'.2 = x.2 ∧ (tf x'.1).ok = (tf x.1).ok ∧ (tf x'.1).m = (tf x.1).m ∧ tq x'.1 = tq x.1 := by
  obtain ⟨i, j', j, c, hR, rfl, rfl⟩ := h
  rcases hR with rfl | hR
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · simp only [sameDataT, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hR
    obtain ⟨⟨⟨hσ, hok⟩, hm⟩, hq⟩ := hR
    exact ⟨by rw [hσ], hok, hm, hq⟩

theorem tupleKW_congr (tf : ℕ → TermFrame) {τ' τ : Tuple}
    (h : List.Forall₂ (fun x' x ↦ (tf x'.1).m = (tf x.1).m) τ' τ) :
    tupleKW tf τ' = tupleKW tf τ := by
  induction h with
  | nil => rfl
  | cons h _ ih =>
    simp only [tupleKW, List.foldr_cons] at ih ⊢
    rw [h, ih]

omit [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] in
theorem valueSumW_congr (tf : ℕ → TermFrame) (val : ℕ → List ℤ) (K : ℕ) {τ' τ : Tuple}
    (h : List.Forall₂ (fun x' x ↦ x'.2 = x.2 ∧ val x'.1 = val x.1 ∧ (tf x'.1).m = (tf x.1).m)
      τ' τ) :
    F.valueSumW tf val K τ' = F.valueSumW tf val K τ := by
  induction h with
  | nil => rfl
  | @cons x' x τ' τ h _ ih =>
    obtain ⟨j', w'⟩ := x'
    obtain ⟨j, w⟩ := x
    obtain ⟨hw, hv, hm⟩ := h
    simp only at hw hv hm
    rw [valueSumW, valueSumW, hw, hv, hm, ih]

omit [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] in
theorem normSumW_le_congr (tf : ℕ → TermFrame) (nb : ℕ → ℕ) (K : ℕ) {τ' τ : Tuple}
    (h : List.Forall₂ (fun x' x ↦ (tf x'.1).m = (tf x.1).m ∧
      x.2.natAbs * nb x.1 ≤ x'.2.natAbs * nb x'.1) τ' τ) :
    F.normSumW tf nb K τ ≤ F.normSumW tf nb K τ' := by
  induction h with
  | nil => exact le_rfl
  | @cons x' x τ' τ h _ ih =>
    obtain ⟨j', w'⟩ := x'
    obtain ⟨j, w⟩ := x
    obtain ⟨hm, hle⟩ := h
    simp only at hm hle
    rw [normSumW, normSumW, hm]
    have : w.natAbs * F.D.natAbs ^ (K - (tf j).m) * nb j ≤
        w'.natAbs * F.D.natAbs ^ (K - (tf j).m) * nb j' := by
      rw [Nat.mul_right_comm w.natAbs, Nat.mul_right_comm w'.natAbs]
      exact Nat.mul_le_mul_right _ hle
    exact Nat.add_le_add this ih

theorem runTupleW_congr (shape : List ℕ) (tf : ℕ → TermFrame) (rm mz : ℕ → Bool)
    (val : ℕ → List ℤ) (strict : Bool) (depth B : ℕ) {τ' τ : Tuple}
    (h : List.Forall₂ (fun x' x ↦ x'.2 = x.2 ∧ rm x'.1 = rm x.1 ∧ mz x'.1 = mz x.1 ∧
      val x'.1 = val x.1 ∧ (tf x'.1).m = (tf x.1).m) τ' τ) :
    F.runTupleW shape tf rm mz val strict depth B τ' =
      F.runTupleW shape tf rm mz val strict depth B τ := by
  rw [runTupleW, runTupleW, tupleKW_congr tf (h.imp fun _ _ h ↦ h.2.2.2.2),
    F.valueSumW_congr tf val (tupleKW tf τ) (h.imp fun _ _ h ↦ ⟨h.1, h.2.2.2.1, h.2.2.2.2⟩),
    all_congr_forall₂ (g := fun jw ↦ rm jw.1 && mz jw.1) (g' := fun jw ↦ rm jw.1 && mz jw.1)
      (h.imp fun _ _ h ↦ by simp only [h.2.1, h.2.2.1])]

theorem tPassW_congr (shape : List ℕ) (td : ℕ → List (ℤ × ℕ)) (B' : ℕ) (strict : Bool)
    {τ' τ : Tuple} (h : List.Forall₂ (fun x' x ↦ x'.2 = x.2 ∧ td x'.1 = td x.1) τ' τ) :
    F.tPassW shape td B' strict τ' = F.tPassW shape td B' strict τ := by
  rw [tPassW, tPassW,
    Lay.tPass_congr _ _ _ _ _ _ _ _ _ _ _ (h.imp fun _ _ h ↦ by simp only [h.1, h.2, and_self])]

theorem tPassFW_congr (shape : List ℕ) (ftd : ℕ → Option (List (ℤ × ℕ) × ℕ)) (B' : ℕ)
    (strict : Bool) {τ' τ : Tuple}
    (h : List.Forall₂ (fun x' x ↦ x'.2 = x.2 ∧ ftd x'.1 = ftd x.1) τ' τ) :
    F.tPassFW shape ftd B' strict τ' = F.tPassFW shape ftd B' strict τ := by
  rw [tPassFW, tPassFW, all_congr_forall₂ (g := fun jw ↦ (ftd jw.1).isSome)
      (g' := fun jw ↦ (ftd jw.1).isSome) (h.imp fun _ _ h ↦ by simp only [h.2]),
    Lay.tPass_congr _ _ _ _ _ _ _ _ _ _ _ (h.imp fun _ _ h ↦ by simp only [h.1, h.2, and_self])]

theorem procFW_congr (shape : List ℕ) (ftd : ℕ → Option (List (ℤ × ℕ) × ℕ)) (B' : ℕ)
    (strict : Bool) (depth : ℕ) {τ' τ : Tuple}
    (h : List.Forall₂ (fun x' x ↦ x'.2 = x.2 ∧ ftd x'.1 = ftd x.1) τ' τ) :
    F.procFW shape ftd B' strict depth τ' = F.procFW shape ftd B' strict depth τ := by
  rw [procFW, procFW, all_congr_forall₂ (g := fun jw ↦ (ftd jw.1).isSome)
      (g' := fun jw ↦ (ftd jw.1).isSome) (h.imp fun _ _ h ↦ by simp only [h.2]),
    fTop_congr _ _ _ _ _ _ _ _ _ _ _ (h.imp fun _ _ h ↦ by simp only [h.1, h.2, and_self])]

omit [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] in
theorem wtW_congr (tf : ℕ → TermFrame) (tq : ℕ → List (SPoly ℤ)) (K : ℕ) {τ' τ : Tuple}
    (h : List.Forall₂ (fun x' x ↦ x'.2 = x.2 ∧ (tf x'.1).m = (tf x.1).m ∧ tq x'.1 = tq x.1)
      τ' τ) :
    F.wtW tf tq K τ' = F.wtW tf tq K τ := by
  induction h with
  | nil => rfl
  | @cons x' x τ' τ h _ ih =>
    obtain ⟨hw, hm, hq⟩ := h
    simp only [wtW, List.map_cons] at ih ⊢
    rw [hw, hm, hq, ih]

theorem runTupleNW_congr (shape : List ℕ) (tf : ℕ → TermFrame) (tq : ℕ → List (SPoly ℤ))
    (val : ℕ → List ℤ) (strict : Bool) (depth B : ℕ) {τ' τ : Tuple}
    (h : List.Forall₂ (fun x' x ↦ x'.2 = x.2 ∧ val x'.1 = val x.1 ∧ (tf x'.1).m = (tf x.1).m ∧
      tq x'.1 = tq x.1) τ' τ) :
    F.runTupleNW shape tf tq val strict depth B τ' =
      F.runTupleNW shape tf tq val strict depth B τ := by
  have hK := tupleKW_congr tf (h.imp fun _ _ h ↦ h.2.2.1)
  simp only [runTupleNW, numsW, hK,
    F.wtW_congr tf tq (tupleKW tf τ) (h.imp fun _ _ h ↦ ⟨h.1, h.2.2.1, h.2.2.2⟩),
    F.valueSumW_congr tf val (tupleKW tf τ) (h.imp fun _ _ h ↦ ⟨h.1, h.2.1, h.2.2.1⟩)]

theorem runTupleWP_apply (shape : List ℕ) (tf : ℕ → TermFrame) (rm mz : ℕ → Bool)
    (val : ℕ → List ℤ) (strict : Bool) (depth B i n : ℕ) (τ : Tuple) :
    F.runTupleWP (Lay.masks B shape) (offset F.n shape B) shape tf rm mz val strict depth B i n τ =
      F.runTupleW shape tf rm mz val strict depth B τ := by
  rw [runTupleWP_eq]

/-- The engine on the tuples `combL K σ ps` with the term data `tf`, `nb`, `tq` and the values
`val B` at digit size `B` given (computed from the quotients `tq`), and the further test
`tt B (val B)` of a tuple where the engine fails, as compiled code runs it (`combRun_eq`): the digit
size from the tuples of the choices of largest bound for each denominator degree of each part, and
the tuples of the first choices of each part's classes of equal data (`sameDataT`) only. -/
def combRun (shape : List ℕ) (tf : ℕ → TermFrame) (nb : ℕ → ℕ) (tq : ℕ → List (SPoly ℤ))
    (val : ℕ → ℕ → List ℤ) (tt : ℕ → (ℕ → List ℤ) → Tuple → Bool)
    (den : ℕ) (strict : Bool) (depth K : ℕ) (σ : ℕ → ℕ → ℤ) (ps : List (ℕ × List ℕ × ℤ)) :
    Bool :=
  let B := F.bitsW shape tf nb depth (combL K σ (repParts (fun i js ↦
    firstReps (bigger K σ tf nb i) [] (byBound K σ nb i js)) ps))
  let v := val B
  let τs := combL K σ (repParts (fun i js ↦ firstReps (sameDataT K σ tf tq i) [] js) ps)
  decide (0 < den) && decide (shape.length ≤ F.n) &&
    τs.all (fun τ ↦ τ.all fun jw ↦ (tf jw.1).ok) &&
    τs.all (fun τ ↦ F.runTupleW shape tf (fun _ ↦ true) (fun _ ↦ true) v strict depth B τ ||
      tt B v τ)

theorem combRun_eq (shape : List ℕ) (tf : ℕ → TermFrame) (nb : ℕ → ℕ) (tq : ℕ → List (SPoly ℤ))
    (val : ℕ → ℕ → List ℤ) (tt : ℕ → (ℕ → List ℤ) → Tuple → Bool)
    (hval : ∀ (B j' j : ℕ), tq j' = tq j → val B j' = val B j)
    (htt : ∀ (B : ℕ) (τ' τ : Tuple), List.Forall₂ (fun x' x ↦ x'.2 = x.2 ∧
      val B x'.1 = val B x.1 ∧ (tf x'.1).m = (tf x.1).m ∧ tq x'.1 = tq x.1) τ' τ →
      tt B (val B) τ' = tt B (val B) τ)
    (den : ℕ) (strict : Bool) (depth K : ℕ) (σ : ℕ → ℕ → ℤ) (ps : List (ℕ × List ℕ × ℤ)) :
    F.combRun shape tf nb tq val tt den strict depth K σ ps =
      (decide (0 < den) && decide (shape.length ≤ F.n) &&
        (combL K σ ps).all (fun τ ↦ τ.all fun jw ↦ (tf jw.1).ok) &&
        (combL K σ ps).all (fun τ ↦ F.runTupleW shape tf (fun _ ↦ true) (fun _ ↦ true)
          (val (F.bitsW shape tf nb depth (combL K σ ps))) strict depth
          (F.bitsW shape tf nb depth (combL K σ ps)) τ ||
          tt (F.bitsW shape tf nb depth (combL K σ ps))
            (val (F.bitsW shape tf nb depth (combL K σ ps))) τ)) := by
  -- The digit size: the largest bound is that of the tuples of the largest choices.
  have hB : F.bitsW shape tf nb depth (combL K σ (repParts (fun i js ↦
      firstReps (bigger K σ tf nb i) [] (byBound K σ nb i js)) ps)) =
      F.bitsW shape tf nb depth (combL K σ ps) := by
    simp only [bitsW]
    congr 1
    refine (foldr_max_combL_repParts (fun i js ↦
      firstReps (bigger K σ tf nb i) [] (byBound K σ nb i js))
      (fun i j' j ↦ j' = j ∨ bigger K σ tf nb i j' j = true)
      (fun i js j hj ↦ List.mem_mergeSort.mp
        ((mem_firstReps _ [] _ hj).resolve_left List.not_mem_nil))
      (fun i js j hj ↦ (firstReps_spec _ [] _).2 j (List.mem_mergeSort.mpr hj))
      (fun τ ↦ F.normSumW tf nb (tupleKW tf τ) τ) (fun τ' τ h ↦ ?_) ps).symm
    rw [tupleKW_congr tf (h.imp fun _ _ h ↦ (bigger_rep h).1)]
    exact F.normSumW_le_congr tf nb _ (h.imp fun _ _ h ↦ bigger_rep h)
  simp only [combRun]
  rw [hB]
  -- The runs: tuples of representatives have the same data.
  rw [← all_combL_firstReps (sameDataT K σ tf tq)
      (fun τ ↦ τ.all fun jw ↦ (tf jw.1).ok)
      (fun τ' τ h ↦ all_congr_forall₂ (h.imp fun _ _ h ↦ (sameDataT_rep h).2.1)) ps,
    ← all_combL_firstReps (sameDataT K σ tf tq)
      (fun τ ↦ F.runTupleW shape tf (fun _ ↦ true) (fun _ ↦ true)
        (val (F.bitsW shape tf nb depth (combL K σ ps))) strict depth
        (F.bitsW shape tf nb depth (combL K σ ps)) τ ||
        tt (F.bitsW shape tf nb depth (combL K σ ps))
          (val (F.bitsW shape tf nb depth (combL K σ ps))) τ)
      (fun τ' τ h ↦ by
        rw [F.runTupleW_congr _ _ _ _ _ _ _ _ (h.imp fun _ _ h ↦
          have h := sameDataT_rep h
          ⟨h.1, rfl, rfl, hval _ _ _ h.2.2.2, h.2.2.1⟩),
          htt _ _ _ (h.imp fun _ _ h ↦
          have h := sameDataT_rep h
          ⟨h.1, hval _ _ _ h.2.2.2, h.2.2.1, h.2.2.2⟩)]) ps]

/-- **`checkXF` on the tuples `combL K σ ps` as compiled code runs it** (`checkXCombF_eq`): the
sparse terms once, then `combRun` with the truncated tests at bounded precision (`tPassFW`) and from
the values (`tPassW`), and rupert's procedure (`runTupleNW`). -/
def checkXCombF (den : ℕ) (strict : Bool) (depth K : ℕ) (σ : ℕ → ℕ → ℤ)
    (ps : List (ℕ × List ℕ × ℤ)) : Bool :=
  let tsa := F.termSL.toArray
  let tS := fun j ↦ tsa.getD j default
  let shape := shapeMax (tsa.toList.map (·.sh))
  let tf := fun j ↦ (tS j).tf
  let nb := fun j ↦ (tS j).nb
  let tq := fun j ↦ (tS j).q
  let fc := F.fCtx shape
  let fv := lookT (thunks F.ts.length fun j ↦ fvalW fc tq j) fun j ↦ fvalW fc tq j
  F.combRun shape tf nb tq
    (fun B ↦ lookT (thunks F.ts.length fun j ↦ valS shape F.C F.H B (tS j))
      fun j ↦ valS shape F.C F.H B (tS j))
    (fun B v τ ↦ (fFirst fc.B B && (F.tPassFW shape
      (ftTermF fc (tBits κ) (F.tShiftK tf nb F.ts.length (tupleKW tf τ)) F.D (tupleKW tf τ) tf fv)
      (tBits κ) strict τ || useB B shape && F.procFW shape
      (ftTermF fc (pBits κ) (F.pShiftK tf nb F.ts.length (tupleKW tf τ)) F.D (tupleKW tf τ) tf fv)
      (pBits κ) strict depth τ)) ||
      F.tPassW shape
      (tTermF κ shape (offset F.n shape B) B (tBits κ)
        (F.tShiftK tf nb F.ts.length (tupleKW tf τ)) F.D (tupleKW tf τ) tf v)
      (tBits κ) strict τ || F.runTupleNW shape tf tq v strict depth B τ) den strict depth K σ ps

theorem checkXCombF_eq (den : ℕ) (strict : Bool) (depth K : ℕ) (σ : ℕ → ℕ → ℤ)
    (ps : List (ℕ × List ℕ × ℤ)) :
    F.checkXCombF den strict depth K σ ps = F.checkXF den strict depth (combL K σ ps) := by
  rw [checkXF_eq, checkXCombF]
  simp only [getD_termSL_toArray, lookT_thunks]
  have hT : ∀ B, F.runTupleXT strict depth B = fun τ ↦ F.runTupleX strict depth B τ ||
      ((fFirst (F.fCtx F.shapeX).B B && (F.tPassFX strict τ ||
        useB B F.shapeX && F.procFX strict depth τ)) || F.tPassX strict B τ ||
        F.runTupleNX strict depth B τ) :=
    fun B ↦ funext fun τ ↦ by simp only [runTupleXT, Bool.or_assoc]
  rw [combRun_eq, hT]
  · rfl
  · intro B j' j h
    simp only [valS, h]
  · intro B τ' τ h
    rw [F.runTupleNW_congr _ _ _ _ _ _ _ (h.imp fun _ _ h ↦ h),
      tupleKW_congr _ (h.imp fun _ _ h ↦ h.2.2.1),
      F.tPassW_congr _ _ _ _ (h.imp fun _ _ h ↦ ⟨h.1, ?_⟩),
      F.tPassFW_congr _ _ _ _ (h.imp fun _ _ h ↦ ⟨h.1, ?_⟩),
      F.procFW_congr _ _ _ _ _ (h.imp fun _ _ h ↦ ⟨h.1, ?_⟩)]
    · simp only [ftTermF, fvalW, h.2.2.1, h.2.2.2]
    · simp only [ftTermF, fvalW, h.2.2.1, h.2.2.2]
    · simp only [tTermF, h.2.1, h.2.2.1]

/-- The tests of `runTupleNW` in either of `runTupleNP`'s orders check the same. -/
theorem cond_or4 (p c b a r : Bool) :
    (bif p then b || a || r || c else c || b || a || r) = (c || b || a || r) := by
  cases p <;> cases c <;> cases b <;> cases a <;> cases r <;> rfl

/-- `runTupleNW` as compiled code runs it (`runTupleNP_apply`): with the engine's masks `mT` (forced
by the exact centred test only) and the offset `O` of the digit size `B` given, and beat lines
after the exact centred test at the top box (`ntop`), after `procB` (`btop`), in `procA` (`boxa`,
`arec`) and after the bisection (`nrec`, with the boxes it tested; each box's own line is `box`,
`boxRecP`). Where the truncated test has already failed on the tuple (`u`) and `procB` runs
(`useB`), the exact centred test and its absolute sums come last, after `procB`, `procA` and the
bisection: on K_{√3/3}'s leaves every exact centred test after a failing truncated test failed
too, and the absolute sums and the centred test were 68–79% of its cost. Every order checks the
same (`cond_or4`). -/
def runTupleNP (mT : Thunk Lay.Masks) (O : ℕ) (shape : List ℕ) (tf : ℕ → TermFrame)
    (tq : ℕ → List (SPoly ℤ)) (val : ℕ → List ℤ) (strict : Bool) (depth B i nτ : ℕ) (u : Bool)
    (τ : Tuple) : Bool :=
  let wt := F.wtW tf tq (tupleKW tf τ) τ
  let Ns := (List.range (ExactBasis.dim κ)).map fun c ↦
    ((F.valueSumW tf val (tupleKW tf τ) τ).getD c 0 + O).toNat
  let c := fun _ : Unit ↦ beat "ntop" (fun r ↦ s!" i={i} n={nτ} ok={r}")
    (Lay.boxOkM κ mT.get F.n shape B strict false (Ns.map (Lay.l1O B mT.get.ones)) Ns)
  let b := fun _ : Unit ↦ useB B shape && procB κ i nτ F.n shape strict wt F.C F.H B Ns
  let a := fun _ : Unit ↦ procA κ i nτ F.n shape strict depth wt F.C F.H F.W B Ns
  let r := fun _ : Unit ↦ (beat "nrec" (fun r ↦ s!" i={i} n={nτ} boxes={r.2} ok={r.1}")
    (boxRecP κ i nτ F.n shape strict (WTerms.deg wt) wt depth 0 false F.C F.H 0 F.W 0)).1
  bif u && useB B shape then b () || a () || r () || c () else c () || b () || a () || r ()

theorem runTupleNP_apply (shape : List ℕ) (tf : ℕ → TermFrame) (tq : ℕ → List (SPoly ℤ))
    (val : ℕ → List ℤ) (strict : Bool) (depth B i nτ : ℕ) (u : Bool) (τ : Tuple) :
    F.runTupleNP (Thunk.mk fun _ ↦ Lay.masks B shape) (offset F.n shape B) shape tf tq val strict
      depth B i nτ u τ = F.runTupleNW shape tf tq val strict depth B τ := by
  simp only [runTupleNP, runTupleNW, numsW, beat_eq, Lay.thunk_get_mk, Lay.masks_ones,
    Lay.boxOkM_masks, boxRecP_fst, cond_or4]
  rw [procA_tag, procB_tag]

/-- Hundredths of a nanosecond per bit of a tuple's numerals of `bits` bits for its sums of one part
and its exact centred test (`tFirst`): from 1.7 ns at `2^20` bits to 12 ns at `2^28` and 17 ns
from `2^29`, where the passes are bound by memory (measured on one thread, K_{√3/3}'s leaves,
2026-11-03 and 2026-11-04). -/
def tNs (bits : ℕ) : ℕ :=
  let l := Nat.log2 bits
  if l < 20 then 170 else [170, 200, 240, 290, 360, 430, 520, 700, 1200].getD (l - 20) 1700

/-- Whether compiled code runs the truncated test first (`checkXCombFP`): where the `keys`
truncations it needs cost less than the exact centred tests of the `u` tuples of `k` parts that
it spares. A truncation costs about 0.31 ns per bit of the packed numerals (`B` bits a digit, in
`slots` slots) and per level of `log₂ slots`, a centred test `tNs` with 22% more per part beyond
the first. Performance only: every order checks the same (`or_orders`). -/
def tFirst (keys u k slots B : ℕ) : Bool :=
  decide (3100 * max (Nat.log2 slots) 1 * keys ≤ u * tNs (B * slots) * (78 + 22 * k))

/-- The tests of `checkXCombF` in each of `checkXCombFP`'s orders check the same. -/
theorem or_orders (fF uT e f t N : Bool) :
    (bif fF then f || N || e || t else bif uT then t || N || e else N || e || t) =
      (e || ((fF && f) || t || N)) := by
  cases fF <;> cases uT <;> cases e <;> cases f <;> cases t <;> cases N <;> rfl

/-- `checkXCombF` with stage lines (`Modules/Check/Leaf/Progress.lean`) after the sparse terms
(`terms`), the packing (`bits`) and the tuples (`tuples`), a beat after each term (`term`), each
value at the packing point (`val`) and at bounded precision (`fval`), each truncation from either
(`trunc`, `ftrunc`), and the beats of each tuple (`fpass`, `runTupleNP`, `runTupleWP`, with the
engine's masks and the offset built once per leaf, and `tpass`): what compiled code runs
(`checkXCombF_eq_checkXCombFP`). The values and truncations are computed when first used, each
term's truncations once per denominator degree of the tuples that use it (`tPairs`, `memoA`).
Where the values at bounded precision are much smaller than the exact ones (`fFirst`), their
truncated test goes first, then on numerals of at least `bMin` bits the top box from their
truncations at `pPrec` bits (`procFW`: beat `ftop`, truncations `ptrunc`), and a tuple that
passes either needs no exact values; then rupert's procedure with its exact centred test last
(`runTupleNP`), the engine and the truncated test from the exact values. Otherwise, where the
truncations cost less than the exact centred tests they spare (`tFirst`), the truncated test goes
first, then rupert's procedure with its exact centred test last, then the engine; otherwise
rupert's procedure, the engine and the truncated test. Every order checks the same (`or_orders`). -/
def checkXCombFP (den : ℕ) (strict : Bool) (depth K : ℕ) (σ : ℕ → ℕ → ℤ)
    (ps : List (ℕ × List ℕ × ℤ)) : Bool :=
  let tsa := stage "terms" (fun a ↦ s!" terms={a.size}") (mapIdxP (fun j t ↦
    beat "term" (fun s ↦ s!" i={j} n={F.ts.length} shape={csv s.sh}")
      (termS F.n t F.C F.H F.D)) 0 F.ts).toArray
  let tS := fun j ↦ tsa.getD j default
  let shape := shapeMax (tsa.toList.map (·.sh))
  let tf := fun j ↦ (tS j).tf
  let nb := fun j ↦ (tS j).nb
  let tq := fun j ↦ (tS j).q
  let fc := F.fCtx shape
  let fv := lookT (thunks F.ts.length fun j ↦
      beat "fval" (fun _ ↦ s!" i={j} n={F.ts.length}") (fvalW fc tq j))
    fun j ↦ fvalW fc tq j
  let B := stage "bits" (fun B ↦ s!" slots={DPoly.slots shape} B={B} " ++
      s!"bits={B * DPoly.slots shape} fB={fc.B} terms={F.ts.length} shape={csv shape}")
    (F.bitsW shape tf nb depth (combL K σ (repParts (fun i js ↦
      firstReps (bigger K σ tf nb i) [] (byBound K σ nb i js)) ps)))
  let v := lookT (thunks F.ts.length fun j ↦
      beat "val" (fun _ ↦ s!" i={j} n={F.ts.length}") (valS shape F.C F.H B (tS j)))
    fun j ↦ valS shape F.C F.H B (tS j)
  let τs := stage "tuples" (fun τs ↦ s!" tuples={τs.length}") (combL K σ (repParts (fun i js ↦
    firstReps (sameDataT K σ tf tq i) [] js) ps))
  let mT := Thunk.mk fun _ ↦ Lay.masks B shape
  let OT := Thunk.mk fun _ ↦ offset F.n shape B
  let keys := tPairs tf τs
  let tt := fun j k ↦ beat "trunc" (fun _ ↦ s!" i={j} K={k} n={F.ts.length}")
    (tTermF κ shape OT.get B (tBits κ) (F.tShiftK tf nb F.ts.length k) F.D k tf v j)
  let td := lookK (memoA keys tt) tt
  let ft := fun j k ↦ beat "ftrunc" (fun _ ↦ s!" i={j} K={k} n={F.ts.length}")
    (ftTermF fc (tBits κ) (F.tShiftK tf nb F.ts.length k) F.D k tf fv j)
  let ftd := lookK (memoA keys ft) ft
  let pt := fun j k ↦ beat "ptrunc" (fun _ ↦ s!" i={j} K={k} n={F.ts.length}")
    (ftTermF fc (pBits κ) (F.pShiftK tf nb F.ts.length k) F.D k tf fv j)
  let ptd := lookK (memoA keys pt) pt
  let mT' := Thunk.mk fun _ ↦ Lay.masks (tBits κ) shape
  let useF := fFirst fc.B B
  let useT := tFirst keys.length τs.length ps.length (DPoly.slots shape) B
  decide (0 < den) && decide (shape.length ≤ F.n) &&
    τs.all (fun τ ↦ τ.all fun jw ↦ (tf jw.1).ok) &&
    allIdx (fun i τ ↦
      let f := fun _ : Unit ↦ beat "fpass" (fun r ↦ s!" i={i} n={τs.length} ok={r}")
          (F.tPassFWM mT'.get shape (fun j ↦ ftd j (tupleKW tf τ)) (tBits κ) strict τ) ||
        useB B shape && beat "ftop" (fun r ↦ s!" i={i} n={τs.length} ok={r}")
          (F.procFWL i τs.length shape (fun j ↦ ptd j (tupleKW tf τ)) (pBits κ) strict depth τ)
      let N := fun u : Bool ↦ F.runTupleNP mT OT.get shape tf tq v strict depth B i τs.length u τ
      let e := fun _ : Unit ↦ F.runTupleWP mT.get OT.get shape tf (fun _ ↦ true) (fun _ ↦ true) v
        strict depth B i τs.length τ
      let t := fun _ : Unit ↦ beat "tpass" (fun r ↦ s!" i={i} n={τs.length} ok={r}")
        (F.tPassWM mT'.get shape (fun j ↦ td j (tupleKW tf τ)) (tBits κ) strict τ)
      bif useF then f () || N true || e () || t ()
      else bif useT then t () || N true || e () else N false || e () || t ()) 0 τs

@[csimp] theorem checkXCombF_eq_checkXCombFP : @checkXCombF = @checkXCombFP := by
  funext κ _ _ _ _ F den strict depth K σ ps
  simp only [checkXCombF, checkXCombFP, combRun, stage_eq, beat_eq, Lay.thunk_get_mk,
    runTupleWP_apply, runTupleNP_apply, lookK_memoA, tPassWM_masks, tPassFWM_masks, procFWL_eq,
    or_orders, allIdx_eq, mapIdxP_eq, lookT_thunks]
  rfl

end Frame

/-- `checkX` on the tuples `combL K σ ps` as compiled code runs it (`checkX_combL`). -/
def checkXComb (n : ℕ) (ts : List (Term κ)) (strict : Bool) (depth : ℕ) (b : Box) (K : ℕ)
    (σ : ℕ → ℕ → ℤ) (ps : List (ℕ × List ℕ × ℤ)) (o : List (ℕ × ℕ) := []) : Bool :=
  (frameOf n ts b (bisW n depth (b.widths n) o)).checkXCombF b.den strict depth K σ ps

theorem checkX_combL (n : ℕ) (ts : List (Term κ)) (strict : Bool) (depth : ℕ) (b : Box) (K : ℕ)
    (σ : ℕ → ℕ → ℤ) (ps : List (ℕ × List ℕ × ℤ)) (o : List (ℕ × ℕ)) :
    checkX n ts strict depth b (combL K σ ps) o = checkXComb n ts strict depth b K σ ps o := by
  rw [checkXComb, Frame.checkXCombF_eq]
  rfl

end Pull

/-! ### Premise forms, obstruction and combination leaves -/

section Forms

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- `formsPull` with the sparse sign check (`Pull.checkX`). -/
def formsPullX (n : ℕ) (Ψ : GenMap κ) (b : Box) (depth : ℕ) (fs : List (V3 κ × List ℕ))
    (o : List (ℕ × ℕ) := []) : Bool :=
  fs.all (fun f ↦ monoSign n b f.2 != 0) &&
    Pull.checkX n (fs.map fun f ↦ (⟨(dotU f.1).comp Ψ, f.2⟩ : Term κ)) false depth b
      ((List.range fs.length).map fun i ↦ [(i, monoSign n b (fs.getD i dfltForm).2)]) o

/-- `formsOk` with the sparse sign check (`formsPullX`). -/
def formsOkX (n : ℕ) (Ψ : GenMap κ) (b : Box) (depth : ℕ) (fs : List (V3 κ × List ℕ))
    (o : List (ℕ × ℕ) := []) : Bool :=
  formsPullX n Ψ b depth (formsLeft n Ψ b fs) o

theorem formsPullX_sound {n : ℕ} {Ψ : GenMap κ} {b : Box} {depth : ℕ}
    {fs : List (V3 κ × List ℕ)} {o : List (ℕ × ℕ)} (h : formsPullX n Ψ b depth fs o = true)
    {z : Fin n → ℝ} (hz : b.Mem n z) :
    ∀ f ∈ fs, 0 ≤ Exact.reV f.1 ⬝ᵥ outU (Ψ.run Exact.re (Pull.ext n z)) := by
  simp only [formsPullX, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨hsg, hc⟩ := h
  have hden : 0 < b.den := Pull.den_pos_of_checkX hc
  intro f hf
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hf
  have hfi : fs.getD i dfltForm = fs[i] := List.getD_eq_getElem _ _ hi
  have hmem : [(i, monoSign n b (fs.getD i dfltForm).2)] ∈
      (List.range fs.length).map fun i ↦ [(i, monoSign n b (fs.getD i dfltForm).2)] :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  obtain ⟨c, hc0, s, heq, hsign⟩ := Pull.checkX_sound hc _ hmem z hz
  have he := heq _ List.mem_cons_self
  rw [getD_map_of_lt _ dfltForm _ hi, hfi] at he
  simp only [PosePoly.comp_run, dotU_eval] at he
  simp only [Sign, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, hfi] at hsign
  have hs0 : monoSign n b fs[i].2 ≠ 0 := hsg _ (List.getElem_mem hi)
  exact nonneg_of_signed hc0 (monoSign_eq hs0) (monoSign_mul_nonneg hs0 hden hz) he hsign

theorem formsOkX_sound {n : ℕ} {Ψ : GenMap κ} {b : Box} {depth : ℕ}
    {fs : List (V3 κ × List ℕ)} {o : List (ℕ × ℕ)} (h : formsOkX n Ψ b depth fs o = true)
    {z : Fin n → ℝ} (hz : b.Mem n z) :
    ∀ f ∈ fs, 0 ≤ Exact.reV f.1 ⬝ᵥ outU (Ψ.run Exact.re (Pull.ext n z)) := by
  have hden : 0 < b.den := by
    simp only [formsOkX, formsPullX, Bool.and_eq_true] at h
    exact Pull.den_pos_of_checkX h.2
  have hp := formsPullX_sound h hz
  intro f hf
  unfold formsLeft at hp
  split at hp
  · rename_i us hus
    by_cases hu : nonnegAt us f.1 = true
    · exact (coneBound_hullPts hus hden hz).nonneg hu
    · exact hp f (List.mem_filter.mpr ⟨hf, by simpa using hu⟩)
  · exact hp f hf

end Forms

namespace Obst

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]
variable (pts : List (V3 κ)) (n : ℕ) (Ψ : GenMap κ) (b : Box) (ob : Obst κ) (pre : Option (Q4 κ))

/-- `polyOkS` with the sparse sign check (`Pull.checkX`). -/
def polyOkSX (o : List (ℕ × ℕ) := []) (f : List (List ℤ) := []) : Bool :=
  (List.range ob.parts.length).all (fun i ↦
    (List.range (ob.part i).1.choices.length).all fun j ↦
      ob.sgn n b i j != 0 && decide (0 < fac f i j)) &&
    Pull.checkX n (ob.terms pts Ψ pre) false ob.depth b
      (combTuplesS ob.K (ob.sgnF n b f) ob.specs) o

/-- `polyOkSX` as compiled code runs it (`polyOkSX_eq_polyOkSXF`): the sparse sign check of the
combinations by `Pull.checkXComb`, once per tuple of representatives of the anchor choices with
equal data. -/
def polyOkSXF (o : List (ℕ × ℕ) := []) (f : List (List ℤ) := []) : Bool :=
  (List.range ob.parts.length).all (fun i ↦
    (List.range (ob.part i).1.choices.length).all fun j ↦
      ob.sgn n b i j != 0 && decide (0 < fac f i j)) &&
    Pull.checkXComb n (ob.terms pts Ψ pre) false ob.depth b ob.K (ob.sgnF n b f)
      (ob.specs.map fun p ↦ (p.1, List.range p.2.1, p.2.2)) o

@[csimp] theorem polyOkSX_eq_polyOkSXF : @polyOkSX = @polyOkSXF := by
  funext κ _ _ _ _ pts n Ψ b ob pre o f
  rw [polyOkSX, polyOkSXF, combTuplesS_eq_combL, Pull.checkX_combL]

variable {pts n Ψ b ob pre}

/-- **Soundness of signed combinations by the sparse check** (`polyOkS_sound`). -/
theorem polyOkSX_sound {o : List (ℕ × ℕ)} {f : List (List ℤ)}
    (h : ob.polyOkSX pts n Ψ b pre o f = true) {z : Fin n → ℝ} (hz : b.Mem n z)
    (hne : ob.parts ≠ []) (hw : ∀ p ∈ ob.parts, 0 < p.2)
    (hneg : ∀ i, i < ob.parts.length → ∃ j, j < (ob.part i).1.choices.length ∧
      (((ob.part i).1.poly pts ((ob.part i).1.choices.getD j [])).pre pre).eval
        (Ψ.run Exact.re (Pull.ext n z)) < 0) : False := by
  simp only [polyOkSX, Bool.and_eq_true, List.all_eq_true, List.mem_range, bne_iff_ne,
    ne_eq, decide_eq_true_eq] at h
  obtain ⟨hmono, hcheck⟩ := h
  have hden : 0 < b.den := Pull.den_pos_of_checkX hcheck
  choose! g hg hgneg using hneg
  set τ := ob.specs.map fun p ↦ (p.1 * ob.K + g p.1, p.2.2 * ob.sgnF n b f p.1 (g p.1)) with hτ
  have hmem : τ ∈ combTuplesS ob.K (ob.sgnF n b f) ob.specs :=
    mem_combTuplesS _ _ g _ fun p hp ↦ by
    simp only [specs, List.mem_map, List.mem_range] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    exact hg i hi
  obtain ⟨c, hc, s, heq, hsign⟩ := Pull.checkX_sound hcheck τ hmem z hz
  have hall : ∀ jw ∈ τ, (jw.2 : ℝ) * s jw.1 < 0 := by
    intro jw hjw
    simp only [hτ, specs, List.map_map, List.mem_map, List.mem_range, Function.comp] at hjw
    obtain ⟨i, hi, rfl⟩ := hjw
    have hgi := hg i hi
    have hgK := lt_of_lt_of_le hgi (le_K hi)
    have he := heq _ (List.mem_map.mpr ⟨(i, (ob.part i).1.choices.length, ((ob.part i).2 : ℤ)),
      List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, rfl⟩)
    simp only [getD_terms hi hgK, term, PosePoly.comp_run] at he
    have hs0 : ob.sgn n b i (g i) ≠ 0 := (hmono i hi (g i) hgi).1
    have hf0 : (0 : ℝ) < (fac f i (g i) : ℝ) := by exact_mod_cast (hmono i hi (g i) hgi).2
    have hσs := neg_of_signed hc (monoSign_eq hs0) (monoSign_mul_nonneg hs0 hden hz) he
      (hgneg i hi)
    have hwi : (0 : ℝ) < ((ob.part i).2 : ℝ) := by exact_mod_cast hw _ (part_mem hi)
    simp only [sgnF, sgn] at hσs ⊢
    push_cast
    have : ((ob.part i).2 : ℝ) * ((monoSign n b ((ob.exps.getD i []).getD (g i) []) : ℝ) *
        (fac f i (g i) : ℝ)) * s (i * ob.K + g i) = ((ob.part i).2 : ℝ) * (fac f i (g i) : ℝ) *
        ((monoSign n b ((ob.exps.getD i []).getD (g i) []) : ℝ) * s (i * ob.K + g i)) := by ring
    rw [this]
    exact mul_neg_of_pos_of_neg (mul_pos hwi hf0) hσs
  have hτne : τ ≠ [] := by
    simp only [hτ, specs, ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
    exact fun h0 ↦ hne (List.length_eq_zero_iff.mp h0)
  have hsum := sum_neg_of_mul_neg τ hτne hall
  simp only [Sign, Bool.false_eq_true, ↓reduceIte] at hsign
  linarith

end Obst

/-! ### Obstruction leaves of weighted zooms

Rupert checks a weighted zoom's leaf on its witnesses' exact polynomials (`WCheck`,
`code/src/proof/regional/wzoom.rs`): sparse, divided exactly by their monomials, then
`nonneg_on_fbox_exact`. `Obst.checkS` gives the leaf the sparse sign check (`Pull.checkX`: the
terms' quotients as exact sparse polynomials, their values by Horner's rule, the engine, the
truncated test and rupert's procedure) beside the Kronecker one (`Pull.check`: mask checks and
values at packing points in `κ`, whose numerals carry every power of the variables up to the
packing shape). The kernel tests the Kronecker check first, so a kernel check of a leaf costs what
it did; compiled code tests the sparse one first (`checkS_eq_checkSF`). -/

namespace Obst

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]
variable (pts : List (V3 κ)) (n : ℕ) (Ψ : GenMap κ) (b : Box) (V : Views κ) (ob : Obst κ)
  (pre : Option (Q4 κ))

/-- **The check of a weighted zoom's obstruction leaf** (`WFrame.leafOk`): `check` whose sign check
of the combinations is the Kronecker one (`Pull.check`) or the sparse one (`Pull.checkX`). -/
def checkS : Bool :=
  !ob.parts.isEmpty &&
    ob.parts.all (fun p ↦ decide (0 < p.2) && p.1.premisesOkV pts V ob.strong) &&
    (List.range ob.parts.length).all (fun i ↦
      (List.range (ob.part i).1.choices.length).all fun j ↦
        monoOk n b ((ob.exps.getD i []).getD j [])) &&
    (Pull.check n (ob.terms pts Ψ pre) false ob.depth b (combTuples ob.K ob.specs) ||
      Pull.checkX n (ob.terms pts Ψ pre) false ob.depth b (combTuples ob.K ob.specs))

/-- `checkS` as compiled code runs it (`checkS_eq_checkSF`): the sparse sign check first, both
once per tuple of representatives of the anchor choices with equal data (`Pull.checkXComb`,
`Pull.checkComb`). -/
def checkSF : Bool :=
  !ob.parts.isEmpty &&
    ob.parts.all (fun p ↦ decide (0 < p.2) && p.1.premisesOkV pts V ob.strong) &&
    (List.range ob.parts.length).all (fun i ↦
      (List.range (ob.part i).1.choices.length).all fun j ↦
        monoOk n b ((ob.exps.getD i []).getD j [])) &&
    (Pull.checkXComb n (ob.terms pts Ψ pre) false ob.depth b ob.K (fun _ _ ↦ 1)
        (ob.specs.map fun p ↦ (p.1, List.range p.2.1, p.2.2)) ||
      Pull.checkComb n (ob.terms pts Ψ pre) false ob.depth b ob.K (fun _ _ ↦ 1)
        (ob.specs.map fun p ↦ (p.1, List.range p.2.1, p.2.2)))

@[csimp] theorem checkS_eq_checkSF : @checkS = @checkSF := by
  funext κ _ _ _ _ pts n Ψ b V ob pre
  rw [checkS, checkSF, combTuples_eq_combL, Pull.check_combL, Pull.checkX_combL,
    Bool.or_comm (Pull.checkComb _ _ _ _ _ _ _ _ _)]

variable {pts n Ψ b V ob pre}

/-- **Soundness of weighted zooms' obstruction leaves**, with the conclusion of `check_sound`. -/
theorem checkS_sound (h : ob.checkS pts n Ψ b V pre = true)
    (hpre : ∀ c ∈ Exact.rePre pre, c ≠ 0) {z : Fin n → ℝ} (hz : b.Mem n z) {r : ℝ}
    (hV : V.Mem (outU (Ψ.run Exact.re (Pull.ext n z))) r) (hs : ob.strong = true ∨ 0 < r)
    (hq : outQ (Ψ.run Exact.re (Pull.ext n z)) ≠ 0) :
    NoFitRep pts (Exact.rePre pre) (Ψ.run Exact.re (Pull.ext n z)) := by
  simp only [checkS, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.isEmpty_eq_false_iff, List.all_eq_true, decide_eq_true_eq, List.mem_range] at h
  obtain ⟨⟨⟨hne, hparts⟩, hmono⟩, hcheck | hcheck⟩ := h
  · exact sound_of_signs hne hparts hmono (Pull.den_pos_of_check hcheck)
      (Pull.check_sound hcheck) hpre hz hV hs hq
  · exact sound_of_signs hne hparts hmono (Pull.den_pos_of_checkX hcheck)
      (Pull.checkX_sound hcheck) hpre hz hV hs hq

end Obst

namespace TObst

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]
variable (pts : List (V3 κ)) (n : ℕ) (Ψ : GenMap κ) (b : Box) (t : TObst κ) (pre : Option (Q4 κ))

/-- **The sparse check of an obstruction or combination leaf**: `check` with the sign checks of
the premise forms and of the anchor choices' combinations by `Pull.checkX`. -/
def checkX (o : List (ℕ × ℕ) := []) (f : List (List ℤ) := []) : Bool :=
  !t.parts.isEmpty &&
    t.parts.all (fun p ↦
      decide (0 < p.weight) && p.wit.domOk pts p.dom && (p.wit.excs pts).isSome) &&
    formsOkX n Ψ b t.depth (t.forms pts) o && t.obst.polyOkSX pts n Ψ b pre o f

/-- `checkX` as compiled code runs it (`checkX_eq_checkXP`): with a stage line after the premise
forms (`Modules/Check/Leaf/Progress.lean`). -/
def checkXP (o : List (ℕ × ℕ) := []) (f : List (List ℤ) := []) : Bool :=
  !t.parts.isEmpty &&
    t.parts.all (fun p ↦
      decide (0 < p.weight) && p.wit.domOk pts p.dom && (p.wit.excs pts).isSome) &&
    stage "forms" (fun r ↦ s!" forms={(t.forms pts).length} ok={r}")
      (formsOkX n Ψ b t.depth (t.forms pts) o) && t.obst.polyOkSX pts n Ψ b pre o f

@[csimp] theorem checkX_eq_checkXP : @checkX = @checkXP := by
  funext κ _ _ _ _ pts n Ψ b t pre o f
  simp only [checkX, checkXP, stage_eq]

variable {pts n Ψ b t pre}

/-- **Soundness of tree obstruction leaves by the sparse check** (`check_sound`). -/
theorem checkX_sound {o : List (ℕ × ℕ)} {f : List (List ℤ)}
    (h : t.checkX pts n Ψ b pre o f = true) (hpre : ∀ c ∈ Exact.rePre pre, c ≠ 0)
    {z : Fin n → ℝ} (hz : b.Mem n z)
    (hexc : ∀ g ∈ t.excs pts, Exact.reV g ⬝ᵥ outU (Ψ.run Exact.re (Pull.ext n z)) ≠ 0)
    (hq : outQ (Ψ.run Exact.re (Pull.ext n z)) ≠ 0) :
    NoFitRep pts (Exact.rePre pre) (Ψ.run Exact.re (Pull.ext n z)) := by
  simp only [checkX, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.isEmpty_eq_false_iff, List.all_eq_true, decide_eq_true_eq, Option.isSome_iff_exists]
    at h
  obtain ⟨⟨⟨hne, hparts⟩, hforms⟩, hpoly⟩ := h
  have hf := formsOkX_sound hforms hz
  intro hfit
  refine Obst.polyOkSX_sound hpoly hz (by simpa [obst] using hne) (fun q hq' ↦ ?_) fun i hi ↦ ?_
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq'
    exact (hparts p hp).1.1
  · have hi' : i < t.parts.length := by simpa [obst] using hi
    rw [obst_part hi']
    set p := t.parts[i] with hpdef
    have hp : p ∈ t.parts := List.getElem_mem hi'
    obtain ⟨⟨-, hd⟩, gs, hgs⟩ := hparts p hp
    have hprem := Wit.premises_of_weak hd hgs (fun g hg ↦ by
      obtain ⟨e, he⟩ := mem_forms hp hg
      exact hf _ he) fun g hg ↦ hexc g (List.mem_flatMap.mpr ⟨p, hp, by rw [hgs]; exact hg⟩)
    obtain ⟨tt, ht, hlt⟩ := Wit.exists_neg hq hpre hprem hfit
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
    exact ⟨j, hj, by rwa [List.getD_eq_getElem _ _ hj]⟩

theorem excs_ne_of_checkX {o : List (ℕ × ℕ)} {f : List (List ℤ)}
    (h : t.checkX pts n Ψ b pre o f = true) :
    ∀ g ∈ t.excs pts, Exact.nonzeroV g = true := by
  simp only [checkX, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Option.isSome_iff_exists] at h
  obtain ⟨⟨⟨-, hparts⟩, -⟩, -⟩ := h
  intro g hg
  obtain ⟨p, hp, hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨-, gs, hgs⟩ := hparts p hp
  rw [hgs, Option.getD_some] at hg
  exact Wit.excs_ne hgs g hg

end TObst

/-! ### Outside and exclusion leaves on exact maps

One polynomial each, the outside or improvement numerator after the leaf's map: on an exact map
(`ChartTree.leafMap`) the sparse sign check computes it as a sparse polynomial, as rupert does
(`weak_nonneg`, `proof/tree.rs`), instead of the formal check at full digit size. -/

namespace TOut

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- **The sparse check of an outside leaf**: `check` with the sign check by `Pull.checkX`. -/
def checkX (B : ChartBox) (n : ℕ) (Ψ : GenMap κ) (b : Box) (x : TOut) (o : List (ℕ × ℕ) := []) :
    Bool :=
  decide (0 < B.box.den) && monoSign n b x.e != 0 &&
    Pull.checkX n
      [⟨(outsideP B.view B.rot x.coord x.upper (x.bound B) B.box.den).comp Ψ, x.e⟩]
      false x.depth b [[(0, monoSign n b x.e)]] o

/-- **Soundness of outside leaves by the sparse check** (`check_sound`). -/
theorem checkX_sound {B : ChartBox} {n : ℕ} {Ψ : GenMap κ} {b : Box} {x : TOut}
    {o : List (ℕ × ℕ)} (h : x.checkX B n Ψ b o = true) {z : Fin n → ℝ} (hz : b.Mem n z)
    {p : ChartPose} (hv : p.view = B.view) (hr : p.rot = B.rot)
    (hrep : Represents p (Ψ.run Exact.re (Pull.ext n z))) :
    bif x.upper then (B.box.hi.getD x.coord 0 : ℝ) / B.box.den ≤ p.coords x.coord
      else p.coords x.coord ≤ (B.box.lo.getD x.coord 0 : ℝ) / B.box.den := by
  simp only [checkX, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨hden, hs0⟩, hc⟩ := h
  exact sound_of hden hs0 (Pull.den_pos_of_checkX hc) hz
    (single_of_pull (Pull.checkX_sound hc) hz) hv hr hrep

end TOut

namespace TExcl

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- **The sparse check of an exclusion leaf**: `check` with the sign check by `Pull.checkX`. -/
def checkX (D : SymmData κ) (n : ℕ) (Ψ : GenMap κ) (b : Box) (pre : Option (Q4 κ)) (x : TExcl)
    (o : List (ℕ × ℕ) := []) : Bool :=
  match D.syms[x.i]?, D.syms[x.j]? with
  | some S₁, some S₂ => monoSign n b x.e != 0 &&
      Exact.nonzero (improvementG id (Improvement.of D.score S₁ S₂) (x.wu.map Exact.ofInt)
        (x.wq.map Exact.ofInt)) &&
      Pull.checkX n [⟨((improvementT (Improvement.of D.score S₁ S₂)).pre pre).comp Ψ, x.e⟩] false
        x.depth b [[(0, monoSign n b x.e)]] o
  | _, _ => false

/-- **Soundness of exclusion leaves by the sparse check** (`check_sound`). -/
theorem checkX_sound {pts : List (V3 κ)} {D : SymmData κ} {n : ℕ} {Ψ : GenMap κ}
    {b : Box} {pre : Option (Q4 κ)} {x : TExcl} {o : List (ℕ × ℕ)} (hD : D.ok pts = true)
    (h : x.checkX D n Ψ b pre o = true) (hpre : ∀ c ∈ Exact.rePre pre, c ≠ 0) {z : Fin n → ℝ}
    (hz : b.Mem n z) {p : ChartPose} (hp : Represents p (Ψ.run Exact.re (Pull.ext n z))) :
    (Polyhedron.ofPoints pts).ExcludedAt D.centre D.score.f (viewDir p.view p.s p.t)
        (p.rotation * preRot (Exact.rePre pre)) ∨
      (viewDir p.view p.s p.t, p.rotation * preRot (Exact.rePre pre)) ∈ null κ D.score := by
  unfold checkX at h
  split at h
  next S₁ S₂ hS₁ hS₂ =>
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨hsg, hw⟩, hc⟩ := h
    exact sound_of hD hS₁ hS₂ hsg hw (Pull.den_pos_of_checkX hc) hpre hz
      (single_of_pull (Pull.checkX_sound hc) hz) hp
  next => exact absurd h (by simp)

end TExcl

/-! ### Either sign check, and the excluded and outside leaves of weighted zooms

Rupert checks these leaves on the exact polynomials after the zoom's map (`WCheck`,
`code/src/proof/regional/wzoom.rs`). `Pull.checkAny` accepts what the Kronecker sign check
(`Pull.check`) or the sparse one (`Pull.checkX`) accepts, with their common conclusion
(`checkAny_sound`). The kernel tests `check` first, so a kernel check costs what it did; compiled
code tests `checkX` first (`checkAny_eq_checkAnyF`). `ExclLeaf.checkAny` and `OutLeaf.checkAny`
are `check` with this sign check (`WFrame.leafOk`); local exclusion leaves use it in
`LocLeaf.signOn`. -/

namespace Pull

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- **Either sign check**: `check` or `checkX`, in the bisection order `o`. -/
def checkAny (n : ℕ) (ts : List (Term κ)) (strict : Bool) (depth : ℕ) (b : Box)
    (τs : List Tuple) (o : List (ℕ × ℕ) := []) : Bool :=
  check n ts strict depth b τs o || checkX n ts strict depth b τs o

/-- `checkAny` as compiled code runs it (`checkAny_eq_checkAnyF`): the sparse check first. -/
def checkAnyF (n : ℕ) (ts : List (Term κ)) (strict : Bool) (depth : ℕ) (b : Box)
    (τs : List Tuple) (o : List (ℕ × ℕ) := []) : Bool :=
  checkX n ts strict depth b τs o || check n ts strict depth b τs o

@[csimp] theorem checkAny_eq_checkAnyF : @checkAny = @checkAnyF := by
  funext κ _ _ _ _ n ts strict depth b τs o
  exact Bool.or_comm _ _

/-- **Soundness of either sign check**, with the conclusion of `check_sound`. -/
theorem checkAny_sound {n : ℕ} {ts : List (Term κ)} {strict : Bool} {depth : ℕ} {b : Box}
    {τs : List Tuple} {o : List (ℕ × ℕ)} (h : checkAny n ts strict depth b τs o = true) :
    ∀ τ ∈ τs, ∀ x : Fin n → ℝ, b.Mem n x → ∃ c : ℝ, 0 < c ∧ ∃ s : ℕ → ℝ,
      (∀ jw ∈ τ, (ts.getD jw.1 default).G.run Exact.re (ext n x) =
        c * monoVal n (ts.getD jw.1 default).e x * s jw.1) ∧
      Sign strict (τ.map fun jw ↦ (jw.2 : ℝ) * s jw.1).sum := by
  simp only [checkAny, Bool.or_eq_true] at h
  rcases h with h | h
  · exact check_sound h
  · exact checkX_sound h

end Pull

namespace ExclLeaf

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- **The check of an excluded leaf by either sign check**: `check` with `Pull.checkAny`. -/
def checkAny (D : SymmData κ) (n : ℕ) (Ψ : GenMap κ) (b : Box) (x : ExclLeaf) : Bool :=
  match D.syms[x.i]?, D.syms[x.j]? with
  | some S₁, some S₂ => decide (0 < n) &&
      Pull.checkAny n [⟨(improvementP (Improvement.of D.score S₁ S₂)).comp Ψ, [x.e]⟩] true
        x.depth b [[(0, 1)]]
  | _, _ => false

/-- **Soundness of excluded leaves by either sign check** (`check_sound`). -/
theorem checkAny_sound {pts : List (V3 κ)} {D : SymmData κ} {n : ℕ} {Ψ : GenMap κ} {b : Box}
    {x : ExclLeaf} (hD : D.ok pts = true) (h : x.checkAny D n Ψ b = true) {z : Fin n → ℝ}
    (hz : b.Mem n z) (hz0 : 0 < Pull.ext n z 0)
    (hu : outU (Ψ.run Exact.re (Pull.ext n z)) ≠ 0)
    (hq : outQ (Ψ.run Exact.re (Pull.ext n z)) ≠ 0) :
    ExclRep pts D (Ψ.run Exact.re (Pull.ext n z)) := by
  unfold checkAny at h
  split at h
  next S₁ S₂ hS₁ hS₂ =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact sound_of hD hS₁ hS₂ (single_of_check (Pull.checkAny_sound h.2) hz) hz0 hu hq
  next => exact absurd h (by simp)

end ExclLeaf

namespace OutLeaf

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- **The check of an outside leaf by either sign check**: `check` with `Pull.checkAny`. -/
def checkAny (B : ChartBox) (n : ℕ) (Ψ : GenMap κ) (b : Box) (x : OutLeaf) : Bool :=
  decide (0 < n) && decide (0 < B.box.den) &&
    Pull.checkAny n
      [⟨(outsideP B.view B.rot x.coord x.upper (x.bound B) B.box.den).comp Ψ, [x.e]⟩]
      true x.depth b [[(0, 1)]]

/-- **Soundness of outside leaves by either sign check** (`check_sound`). -/
theorem checkAny_sound {B : ChartBox} {n : ℕ} {Ψ : GenMap κ} {b : Box} {x : OutLeaf}
    (h : x.checkAny B n Ψ b = true) {z : Fin n → ℝ} (hz : b.Mem n z) (hz0 : 0 < Pull.ext n z 0)
    {p : ChartPose} (hp : p ∈ B.poses) (hrep : Represents p (Ψ.run Exact.re (Pull.ext n z))) :
    False := by
  simp only [checkAny, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨-, hden⟩, hc⟩ := h
  exact sound_of hden (single_of_check (Pull.checkAny_sound hc) hz) hz0 hp hrep

end OutLeaf

end Nieuwland.Check
