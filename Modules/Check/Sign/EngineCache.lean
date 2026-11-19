import Modules.Check.Polynomial.Divide

/-!
# The engine with its masks built once

The packed engine (`Lay.run`, `Lay.runDiv`) reads every box through masks that depend only on the
digit size `B` and the shape `sh`: the ones `onesN`, the offset `offN`, the slots of the centred
form (`oddM`, `even0M`) and the slices of each variable (`ind B sh (zeroAt i)` for a substitution,
`ind B sh (topAt i (deg sh i))` for a division). The definitions rebuild them at every use, and
the box test computes the absolute coefficient sum of each numeral (`l1N`) up to four times and the
combination of the approximate centred form (`apxNum`) twice. On numerals of hundreds of millions
of bits this costs several times the tests themselves (`notes/lean-perf.md`).

`Masks` holds the masks, built once by `masks B sh` (a variable's slices when first used), and
`runM`, `runDivM` are the engine with the masks given and the sums `l1N` computed once per box,
shared by the approximate centred form, its gate and the bisection (`boxOkM`, `runL`). They are
equal to `run` and `runDiv` at `masks B sh` (`runM_masks`, `runDivM_masks`). Compiled code runs
them through `@[csimp]` lemmas (`run_eq_runF`, `runDiv_eq_runDivF`: the masks built per call), and
the checks of chart-tree leaves build the masks once per leaf (`Pull.Frame.runTupleWP`). The
definitions that the kernel checks and the theorem statements are unchanged.
-/

open Finset

namespace Nieuwland.Check

namespace Lay

open DPoly Num

/-! ### The masks -/

/-- The masks of a digit size and a shape (`masks`). -/
structure Masks where
  /-- `onesN B sh`. -/
  ones : ℕ
  /-- `offN B sh`. -/
  off : ℕ
  /-- `oddM B sh` spread over whole digits, `(oddM <<< B) - oddM` (as in `maskSumS`). -/
  oddX : ℕ
  /-- `even0M B sh` spread over whole digits. -/
  even0X : ℕ
  /-- `ind B sh (zeroAt i)` for each variable `i`, built when first used. -/
  zero : Array (Thunk ℕ)
  /-- `ind B sh (topAt i (deg sh i))` for each variable `i`, built when first used. -/
  top : Array (Thunk ℕ)

/-- A thunk's value is its function's (compiled code computes it once). -/
theorem thunk_get_mk {α : Type*} (f : Unit → α) : (Thunk.mk f).get = f () := rfl

/-- The masks of the digit size `B` and the shape `sh`. -/
def masks (B : ℕ) (sh : List ℕ) : Masks :=
  let o := onesN B sh
  let e := evenN B sh
  let od := o - e
  let e0 := e - 1
  ⟨o, o <<< (B - 1), (od <<< B) - od, (e0 <<< B) - e0,
    thunks sh.length fun i ↦ ind B sh (zeroAt i),
    thunks sh.length fun i ↦ ind B sh (topAt i (deg sh i))⟩

/-- `ind B sh (zeroAt i)`, from the masks (`zeroI_masks`). -/
def Masks.zeroI (m : Masks) (B : ℕ) (sh : List ℕ) (i : ℕ) : ℕ :=
  lookT m.zero (fun i ↦ ind B sh (zeroAt i)) i

/-- `ind B sh (topAt i (deg sh i))`, from the masks (`topI_masks`). -/
def Masks.topI (m : Masks) (B : ℕ) (sh : List ℕ) (i : ℕ) : ℕ :=
  lookT m.top (fun i ↦ ind B sh (topAt i (deg sh i))) i

@[simp] theorem masks_ones (B : ℕ) (sh : List ℕ) : (masks B sh).ones = onesN B sh := rfl

theorem masks_off (B : ℕ) (sh : List ℕ) : (masks B sh).off = offN B sh := by
  rw [offN_eq_offNS]
  rfl

theorem zeroI_masks (B : ℕ) (sh : List ℕ) (i : ℕ) :
    (masks B sh).zeroI B sh i = ind B sh (zeroAt i) :=
  congrFun (lookT_thunks sh.length fun i ↦ ind B sh (zeroAt i)) i

theorem topI_masks (B : ℕ) (sh : List ℕ) (i : ℕ) :
    (masks B sh).topI B sh i = ind B sh (topAt i (deg sh i)) :=
  congrFun (lookT_thunks sh.length fun i ↦ ind B sh (topAt i (deg sh i))) i

/-! ### Sums of digits -/

/-- `absN` with the ones `o` given (`absO_onesN`). -/
def absO (B o N : ℕ) : ℕ :=
  let s := (N >>> (B - 1)) &&& o
  let t := o - s
  ((N &&& ((s <<< B) - s)) - (s <<< (B - 1))) + ((t <<< (B - 1)) - (N &&& ((t <<< B) - t)))

theorem absO_onesN (B : ℕ) (sh : List ℕ) (N : ℕ) : absO B (onesN B sh) N = absN B sh N := by
  rw [absN_eq_absNS]
  rfl

/-- `l1N` with the ones `o` given (`l1O_onesN`). -/
def l1O (B o N : ℕ) : ℕ := absO B o N % (2 ^ B - 1)

theorem l1O_onesN (B : ℕ) (sh : List ℕ) (N : ℕ) : l1O B (onesN B sh) N = l1N B sh N := by
  rw [l1O, absO_onesN, l1N]

/-- `oddAbs B sh N + evenNeg B sh N` with the masks given, the signs of the digits read once
(`penM_masks`). -/
def penM (m : Masks) (B N : ℕ) : ℕ :=
  let o := m.ones
  let s := (N >>> (B - 1)) &&& o
  let t := o - s
  let neg := (t <<< (B - 1)) - (N &&& ((t <<< B) - t))
  ((((N &&& ((s <<< B) - s)) - (s <<< (B - 1))) + neg) &&& m.oddX) % (2 ^ B - 1) +
    (neg &&& m.even0X) % (2 ^ B - 1)

theorem penM_masks (B : ℕ) (sh : List ℕ) (N : ℕ) :
    penM (masks B sh) B N = oddAbs B sh N + evenNeg B sh N := by
  rw [oddAbs, evenNeg, maskSum_eq_maskSumS, absN_eq_absNS, negN_eq_negNS]
  rfl

/-- The digit `0` of `N` as a coefficient, by one mask of `B` bits (`cf0_eq`). -/
def cf0 (B N : ℕ) : ℤ := ((N &&& (2 ^ B - 1) : ℕ) : ℤ) - 2 ^ (B - 1)

theorem cf0_eq (B N : ℕ) : cf0 B N = cf B N 0 := by
  rw [cf0, cf, dig, mul_zero, pow_zero, Nat.div_one, Nat.and_two_pow_sub_one_eq_mod]

/-- The entry `j` of `ls`, or `f 0` beyond its end: for `ls = Ns.map f`, `f (Ns.getD j 0)`
(`getF_map`). -/
def getF (ls : List ℕ) (f : ℕ → ℕ) (j : ℕ) : ℕ :=
  match ls[j]? with
  | some l => l
  | none => f 0

theorem getF_map (Ns : List ℕ) (f : ℕ → ℕ) (j : ℕ) : getF (Ns.map f) f j = f (Ns.getD j 0) := by
  unfold getF
  rw [List.getElem?_map, List.getD_eq_getElem?_getD]
  cases Ns[j]? <;> rfl

/-! ### Substitutions and divisions -/

/-- `subN` with the masks given (`subNM_masks`). -/
def subNM (m : Masks) (B : ℕ) (sh : List ℕ) (i : ℕ) (w : ℕ → ℤ) (a b : ℤ) (N : ℕ) : ℕ :=
  let s := stride sh i
  let I := m.zeroI B sh i
  let M := (I <<< B) - I
  let hI : ℤ := ((I <<< (B - 1) : ℕ) : ℤ)
  (hsub (B * s) a b w (fun k ↦ (((N >>> (B * (k * s))) &&& M : ℕ) : ℤ) - hI) 0 (deg sh i + 1) +
    (m.off : ℤ)).toNat

theorem subNM_masks (B : ℕ) (sh : List ℕ) (i : ℕ) (w : ℕ → ℤ) (a b : ℤ) :
    subNM (masks B sh) B sh i w a b = subN B sh i w a b := by
  funext N
  rw [subN_eq_subNS, subNM, subNS, zeroI_masks, masks_off]

/-- `subAll` with the masks and the absolute sums `ls` of the numerals given
(`subAllM_masks`). -/
def subAllM (m : Masks) (B : ℕ) (sh : List ℕ) (i : ℕ) (w : ℕ → ℤ) (a b : ℤ) (W : ℕ)
    (ls Ns : List ℕ) : Option (List ℕ) :=
  bif ls.all fun l ↦ decide (W * l < 2 ^ (B - 1)) then some (Ns.map (subNM m B sh i w a b))
  else none

theorem subAllM_masks (B : ℕ) (sh : List ℕ) (i : ℕ) (w : ℕ → ℤ) (a b : ℤ) (W : ℕ)
    (Ns : List ℕ) :
    subAllM (masks B sh) B sh i w a b W (Ns.map (l1O B (onesN B sh))) Ns =
      subAll B sh i w a b W Ns := by
  simp only [subAllM, subAll, List.all_map, Function.comp_def, l1O_onesN, subNM_masks]

/-- `vertAll` with the masks given (`vertAllM_masks`). -/
def vertAllM (m : Masks) (B : ℕ) (sh : List ℕ) (σ : ℕ → ℤ) : ℕ → List ℕ → Option (List ℕ)
  | 0, Ns => some Ns
  | k + 1, Ns =>
    match vertAllM m B sh σ k Ns with
    | none => none
    | some Ns' =>
      bif deg sh k == 0 then some Ns'
      else subAllM m B sh k (fun _ ↦ 1) (σ k) (-2 * σ k) (3 ^ deg sh k)
        (Ns'.map (l1O B m.ones)) Ns'

theorem vertAllM_masks (B : ℕ) (sh : List ℕ) (σ : ℕ → ℤ) :
    ∀ (k : ℕ) (Ns : List ℕ), vertAllM (masks B sh) B sh σ k Ns = vertAll B sh σ k Ns
  | 0, Ns => rfl
  | k + 1, Ns => by
    simp only [vertAllM, vertAll, vertAllM_masks B sh σ k Ns, masks_ones, subAllM_masks]
    rfl

/-- `divMask` by shifts, with the ones `o` and the top slice `T` given (`divMaskO_eq`). -/
def divMaskO (B o T e : ℕ) : ℕ := (o <<< B) - (o <<< (e + 1)) + ((T <<< (e + 1)) - T)

theorem divMaskO_eq (B : ℕ) (sh : List ℕ) (i e : ℕ) :
    divMaskO B (onesN B sh) (ind B sh (topAt i (deg sh i))) e = divMask B sh i e := by
  rw [divMaskO, divMask, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.sub_mul,
    Nat.sub_mul, one_mul, Nat.mul_comm (2 ^ B), Nat.mul_comm (2 ^ (e + 1)),
    Nat.mul_comm (2 ^ (e + 1))]

/-- `divN` with the masks given, the offset `offN` theirs (`divNM_masks`). -/
def divNM (m : Masks) (B : ℕ) (sh : List ℕ) (i : ℕ) (a b : ℤ) (e N : ℕ) : Option ℕ :=
  let v : ℤ := (N : ℤ) - m.off
  let f : ℤ := a + b * 2 ^ (B * stride sh i)
  bif v % f != 0 then none
  else
    let T := m.topI B sh i
    let X : ℤ := v / f + ((m.ones <<< e : ℕ) : ℤ)
    bif decide (X < 0) || X.toNat >>> (B * slots sh) != 0 ||
        X.toNat &&& divMaskO B m.ones T e != T <<< e then none
    else some (v / f + m.off).toNat

theorem divNM_masks (B : ℕ) (sh : List ℕ) (i : ℕ) (a b : ℤ) (e N : ℕ) :
    divNM (masks B sh) B sh i a b e N = divN B sh i a b e (offN B sh) N := by
  simp only [divNM, divN, masks_off, masks_ones, topI_masks, divMaskO_eq, Nat.shiftLeft_eq]

/-- `divL` with the masks given (`divLM_masks`). -/
def divLM (m : Masks) (B : ℕ) (sh : List ℕ) (i : ℕ) (a b : ℤ) (e : ℕ) :
    List ℕ → Option (List ℕ)
  | [] => some []
  | N :: Ns =>
    match divNM m B sh i a b e N with
    | none => none
    | some N' => (divLM m B sh i a b e Ns).map (N' :: ·)

theorem divLM_masks (B : ℕ) (sh : List ℕ) (i : ℕ) (a b : ℤ) (e : ℕ) :
    ∀ Ns : List ℕ, divLM (masks B sh) B sh i a b e Ns = divL B sh i a b e (offN B sh) Ns
  | [] => rfl
  | N :: Ns => by
    simp only [divLM, divL, divNM_masks, divLM_masks B sh i a b e Ns]
    rfl

/-- `divRep` with the masks given (`divRepM_masks`). -/
def divRepM (m : Masks) (B : ℕ) (sh : List ℕ) (i : ℕ) (a b : ℤ) :
    ℕ → List ℕ → Option (List ℕ)
  | 0, _ => none
  | k + 1, Ns =>
    let e := divE B sh a b
    bif decide ((a.natAbs + b.natAbs) * 2 ^ e < 2 ^ (B - 1)) &&
        decide (slots sh * 2 ^ e < 2 ^ (B - 1)) then
      match divLM m B sh i a b e Ns with
      | none => none
      | some Ns' => some ((divRepM m B sh i a b k Ns').getD Ns')
    else none

theorem divRepM_masks (B : ℕ) (sh : List ℕ) (i : ℕ) (a b : ℤ) :
    ∀ (k : ℕ) (Ns : List ℕ),
      divRepM (masks B sh) B sh i a b k Ns = divRep B sh i a b (offN B sh) k Ns
  | 0, _ => rfl
  | k + 1, Ns => by
    simp only [divRepM, divRep, divLM_masks, divRepM_masks B sh i a b k]
    rfl

/-- `divAll` with the masks given (`divAllM_masks`). -/
def divAllM (m : Masks) (B : ℕ) (sh : List ℕ) :
    List (ℕ × ℤ × ℤ) → List ℕ → Option (List ℕ)
  | [], _ => none
  | (i, a, b) :: fs, Ns =>
    match bif decide ((b.natAbs : ℤ) ≤ a) then divRepM m B sh i a b (deg sh i) Ns else none with
    | none => divAllM m B sh fs Ns
    | some Ts => some ((divAllM m B sh fs Ts).getD Ts)

theorem divAllM_masks (B : ℕ) (sh : List ℕ) :
    ∀ (fs : List (ℕ × ℤ × ℤ)) (Ns : List ℕ),
      divAllM (masks B sh) B sh fs Ns = divAll B sh (offN B sh) fs Ns
  | [], _ => rfl
  | (i, a, b) :: fs, Ns => by
    simp only [divAllM, divAll, divRepM_masks, divAllM_masks B sh fs]
    rfl

/-! ### The engine -/

section Field

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

variable (κ) in
/-- `apxNum` with the masks given (`apxNumM_masks`). -/
def apxNumM (m : Masks) (Ns : List ℕ) : ℕ :=
  (sumZ (fun j ↦ apxA κ j * ((Ns.getD j 0 : ℤ) - m.off)) (ExactBasis.dim κ) + m.off).toNat

theorem apxNumM_masks (B : ℕ) (sh : List ℕ) (Ns : List ℕ) :
    apxNumM κ (masks B sh) Ns = apxNum κ B sh Ns := by
  rw [apxNumM, apxNum, masks_off]

variable (κ) in
/-- The exact centred form's test (`exactOk` behind its gate). -/
def lowerOk (n : ℕ) (sh : List ℕ) (B : ℕ) (strict : Bool) (Ns : List ℕ) : Bool :=
  let r := ExactBasis.lowerOf (κ := κ) n sh B Ns
  r.2 && signTest strict r.1

variable (κ) in
/-- `domOk` with the masks given (`domOkM_masks`). -/
def domOkM (m : Masks) (n : ℕ) (sh : List ℕ) (B : ℕ) (strict : Bool) (Ns : List ℕ) : Bool :=
  match vertAllM m B sh (lowSign κ sh B Ns) n Ns with
  | none => false
  | some Vs =>
    let r := domOf (κ := κ) n sh B Vs
    r.2 && signTest strict r.1

theorem domOkM_masks (n : ℕ) (sh : List ℕ) (B : ℕ) (strict : Bool) (Ns : List ℕ) :
    domOkM κ (masks B sh) n sh B strict Ns = domOk κ n sh B strict Ns := by
  rw [domOkM, domOk, vertAllM_masks]
  rfl

variable (κ) in
/-- `boxOk` with the masks and the absolute sums `ls` of the numerals given (`boxOkM_masks`):
the approximate centred form and its gate share the sums, the combination's numeral and its
penalties; with a beat line after the dominance (`Modules/Check/Leaf/Progress.lean`). -/
def boxOkM (m : Masks) (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom : Bool) (ls Ns : List ℕ) :
    Bool :=
  let l := getF ls (l1O B m.ones)
  let d := ExactBasis.dim κ
  let err := sumN (fun j ↦ apxE κ j * l j) d
  (bif decide (sumN (fun j ↦ (apxA κ j).natAbs * l j) d < 2 ^ (B - 1)) then
      let v : κ := Exact.ofInt (2 ^ ExactBasis.apxK κ) *
          ExactBasis.ofCoords ((List.range d).map fun j ↦ cf0 B (Ns.getD j 0)) -
        Exact.ofInt ((penM m B (apxNumM κ m Ns) + err : ℕ) : ℤ)
      signTest strict v ||
        decide (0 < err) && signTest strict (v + Exact.ofInt (2 * err : ℤ)) &&
          lowerOk κ n sh B strict Ns
    else lowerOk κ n sh B strict Ns) ||
    dom && beat "dom" (fun r ↦ s!" ok={r}") (domOkM κ m n sh B strict Ns)

theorem boxOkM_masks (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom : Bool) (Ns : List ℕ) :
    boxOkM κ (masks B sh) n sh B strict dom (Ns.map (l1O B (onesN B sh))) Ns =
      boxOk κ n sh B strict dom Ns := by
  simp only [boxOkM, boxOk, apxOk, exactOk, apxGate, apxPen, apxErr, lowerOk, masks_ones,
    getF_map, l1O_onesN, penM_masks, apxNumM_masks, cf0_eq, domOkM_masks, beat_eq]
  cases decide (sumN (fun j ↦ (apxA κ j).natAbs * l1N B sh (Ns.getD j 0)) (ExactBasis.dim κ) <
    2 ^ (B - 1))
  · simp only [Bool.cond_false, Bool.false_and, Bool.not_false, Bool.true_or, Bool.true_and,
      Bool.false_or]
  · simp only [Bool.cond_true, Bool.true_and, Bool.not_true, Bool.false_or, Bool.and_assoc]
    rfl

variable (κ) in
/-- `run` with the masks given, the absolute sums `ls` of the numerals computed once per box and
shared by its tests and its bisection (`runL_masks`). -/
def runL (m : Masks) (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom last : Bool) :
    ℕ → List ℤ → List ℕ → List ℕ → Bool
  | 0, _, ls, Ns => boxOkM κ m n sh B strict dom ls Ns
  | d + 1, W, ls, Ns =>
    boxOkM κ m n sh B strict dom ls Ns ||
      let i := pickW last n W
      let W' := halveW W i
      bif deg sh i == 0 then runL m n sh B strict dom last d W' ls Ns
      else
        match subAllM m B sh i (halfW sh i) (-1) 1 (2 ^ deg sh i) ls Ns,
          subAllM m B sh i (halfW sh i) 1 1 (2 ^ deg sh i) ls Ns with
        | some Lo, some Hi =>
          runL m n sh B strict dom last d W' (Lo.map (l1O B m.ones)) Lo &&
            runL m n sh B strict dom last d W' (Hi.map (l1O B m.ones)) Hi
        | _, _ => false

theorem runL_masks (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom last : Bool) :
    ∀ (d : ℕ) (W : List ℤ) (Ns : List ℕ),
      runL κ (masks B sh) n sh B strict dom last d W (Ns.map (l1O B (onesN B sh))) Ns =
        run κ n sh B strict dom last d W Ns
  | 0, W, Ns => boxOkM_masks n sh B strict dom Ns
  | d + 1, W, Ns => by
    simp only [runL, run, boxOkM_masks, subAllM_masks, masks_ones,
      runL_masks n sh B strict dom last d]
    rfl

variable (κ) in
/-- `run` with the masks given (`runM_masks`). -/
def runM (m : Masks) (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom last : Bool) (depth : ℕ)
    (W : List ℤ) (Ns : List ℕ) : Bool :=
  runL κ m n sh B strict dom last depth W (Ns.map (l1O B m.ones)) Ns

theorem runM_masks (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom last : Bool) (depth : ℕ)
    (W : List ℤ) (Ns : List ℕ) :
    runM κ (masks B sh) n sh B strict dom last depth W Ns =
      run κ n sh B strict dom last depth W Ns :=
  runL_masks n sh B strict dom last depth W Ns

variable (κ) in
/-- The bisection step of `runL` (`split` with the masks and the sums given, `splitL_masks`). -/
def splitL (m : Masks) (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom last : Bool) :
    ℕ → List ℤ → List ℕ → List ℕ → Bool
  | 0, _, _, _ => false
  | d + 1, W, ls, Ns =>
    let i := pickW last n W
    let W' := halveW W i
    bif deg sh i == 0 then runL κ m n sh B strict dom last d W' ls Ns
    else
      match subAllM m B sh i (halfW sh i) (-1) 1 (2 ^ deg sh i) ls Ns,
        subAllM m B sh i (halfW sh i) 1 1 (2 ^ deg sh i) ls Ns with
      | some Lo, some Hi =>
        runL κ m n sh B strict dom last d W' (Lo.map (l1O B m.ones)) Lo &&
          runL κ m n sh B strict dom last d W' (Hi.map (l1O B m.ones)) Hi
      | _, _ => false

theorem splitL_masks (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom last : Bool) :
    ∀ (d : ℕ) (W : List ℤ) (Ns : List ℕ),
      splitL κ (masks B sh) n sh B strict dom last d W (Ns.map (l1O B (onesN B sh))) Ns =
        split κ n sh B strict dom last d W Ns
  | 0, _, _ => rfl
  | d + 1, W, Ns => by
    simp only [splitL, split, subAllM_masks, masks_ones, runL_masks]
    rfl

variable (κ) in
/-- `runDiv` with the masks given (`runDivM_masks`). -/
def runDivM (m : Masks) (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom last : Bool) (depth : ℕ)
    (W : List ℤ) (fs : List (ℕ × ℤ × ℤ)) (Ns : List ℕ) : Bool :=
  bif strict then runM κ m n sh B strict dom last depth W Ns
  else
    let ls := Ns.map (l1O B m.ones)
    boxOkM κ m n sh B strict dom ls Ns ||
      (match divAllM m B sh fs Ns with
        | some Ts => runM κ m n sh B strict dom last depth W Ts
        | none => false) ||
      splitL κ m n sh B strict dom last depth W ls Ns

theorem runDivM_masks (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom last : Bool) (depth : ℕ)
    (W : List ℤ) (fs : List (ℕ × ℤ × ℤ)) (Ns : List ℕ) :
    runDivM κ (masks B sh) n sh B strict dom last depth W fs Ns =
      runDiv κ n sh B strict dom last depth W fs Ns := by
  simp only [runDivM, runDiv, runM_masks, boxOkM_masks, divAllM_masks, masks_ones,
    splitL_masks]
  rfl

variable (κ) in
/-- `run` as compiled code runs it (`run_eq_runF`): with the masks built once per call. -/
def runF (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom last : Bool) (depth : ℕ) (W : List ℤ)
    (Ns : List ℕ) : Bool :=
  runM κ (masks B sh) n sh B strict dom last depth W Ns

@[csimp] theorem run_eq_runF : @run = @runF := by
  funext κ _ _ _ _ n sh B strict dom last depth W Ns
  exact (runM_masks n sh B strict dom last depth W Ns).symm

variable (κ) in
/-- `runDiv` as compiled code runs it (`runDiv_eq_runDivF`): with the masks built once per call. -/
def runDivF (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom last : Bool) (depth : ℕ) (W : List ℤ)
    (fs : List (ℕ × ℤ × ℤ)) (Ns : List ℕ) : Bool :=
  runDivM κ (masks B sh) n sh B strict dom last depth W fs Ns

@[csimp] theorem runDiv_eq_runDivF : @runDiv = @runDivF := by
  funext κ _ _ _ _ n sh B strict dom last depth W fs Ns
  exact (runDivM_masks n sh B strict dom last depth W fs Ns).symm

/-! ### Counted copies

`runDivM` with the tuple and the boxes in the dominance's beat line: compiled code runs these
(`Pull.Frame.runTupleWP`), so that a long dominance test can be told from a stall. -/

/-- The keys of a box in a beat line: the tuple `i`, the boxes tested so far with this one, and
the box's level in the bisection. -/
def boxKeys (i boxes lvl : ℕ) : String := s!" i={i} boxes={boxes} depth={lvl}"

variable (κ) in
/-- `boxOkM` with the keys `pre` in the dominance's beat line (`boxOkMK_eq`). -/
def boxOkMK (pre : String) (m : Masks) (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom : Bool)
    (ls Ns : List ℕ) : Bool :=
  let l := getF ls (l1O B m.ones)
  let d := ExactBasis.dim κ
  let err := sumN (fun j ↦ apxE κ j * l j) d
  (bif decide (sumN (fun j ↦ (apxA κ j).natAbs * l j) d < 2 ^ (B - 1)) then
      let v : κ := Exact.ofInt (2 ^ ExactBasis.apxK κ) *
          ExactBasis.ofCoords ((List.range d).map fun j ↦ cf0 B (Ns.getD j 0)) -
        Exact.ofInt ((penM m B (apxNumM κ m Ns) + err : ℕ) : ℤ)
      signTest strict v ||
        decide (0 < err) && signTest strict (v + Exact.ofInt (2 * err : ℤ)) &&
          lowerOk κ n sh B strict Ns
    else lowerOk κ n sh B strict Ns) ||
    dom && beat "dom" (fun r ↦ s!"{pre} ok={r}") (domOkM κ m n sh B strict Ns)

theorem boxOkMK_eq (pre : String) (m : Masks) (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom : Bool)
    (ls Ns : List ℕ) :
    boxOkMK κ pre m n sh B strict dom ls Ns = boxOkM κ m n sh B strict dom ls Ns := by
  simp only [boxOkMK, boxOkM, beat_eq]

variable (κ) in
/-- `runL` with the boxes counted (`runLC_fst`): the tuple `i`, the boxes tested before
(`cnt`, returned with the boxes tested) and the level `lvl` in the dominance's beat line. -/
def runLC (i : ℕ) (m : Masks) (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom last : Bool) :
    ℕ → ℕ → List ℤ → List ℕ → List ℕ → ℕ → Bool × ℕ
  | 0, lvl, _, ls, Ns, cnt =>
    (boxOkMK κ (boxKeys i (cnt + 1) lvl) m n sh B strict dom ls Ns, cnt + 1)
  | d + 1, lvl, W, ls, Ns, cnt =>
    bif boxOkMK κ (boxKeys i (cnt + 1) lvl) m n sh B strict dom ls Ns then (true, cnt + 1)
    else
      let j := pickW last n W
      let W' := halveW W j
      bif deg sh j == 0 then runLC i m n sh B strict dom last d lvl W' ls Ns (cnt + 1)
      else
        match subAllM m B sh j (halfW sh j) (-1) 1 (2 ^ deg sh j) ls Ns,
          subAllM m B sh j (halfW sh j) 1 1 (2 ^ deg sh j) ls Ns with
        | some Lo, some Hi =>
          let lo := runLC i m n sh B strict dom last d (lvl + 1) W' (Lo.map (l1O B m.ones)) Lo
            (cnt + 1)
          bif lo.1 then
            runLC i m n sh B strict dom last d (lvl + 1) W' (Hi.map (l1O B m.ones)) Hi lo.2
          else lo
        | _, _ => (false, cnt + 1)

theorem cond_fst {α β : Type*} (c : Bool) (a b : α × β) :
    (bif c then a else b).1 = bif c then a.1 else b.1 := by
  cases c <;> rfl

theorem cond_self_and (a b : Bool) : (bif a then b else a) = (a && b) := by
  cases a <;> rfl

theorem runLC_fst (i : ℕ) (m : Masks) (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom last : Bool)
    (d : ℕ) : ∀ (lvl : ℕ) (W : List ℤ) (ls Ns : List ℕ) (cnt : ℕ),
      (runLC κ i m n sh B strict dom last d lvl W ls Ns cnt).1 =
        runL κ m n sh B strict dom last d W ls Ns := by
  induction d with
  | zero => intro lvl W ls Ns cnt; simp only [runLC, runL, boxOkMK_eq]
  | succ d ih =>
    intro lvl W ls Ns cnt
    simp only [runLC, runL, boxOkMK_eq, cond_fst]
    cases boxOkM κ m n sh B strict dom ls Ns
    · simp only [Bool.cond_false, Bool.false_or]
      cases deg sh (pickW last n W) == 0
      · simp only [Bool.cond_false]
        split
        · simp only [cond_fst, ih, cond_self_and]
        · rfl
      · simp only [Bool.cond_true, ih]
    · rfl

variable (κ) in
/-- `splitL` with the boxes counted (`splitLC_fst`; `runLC`). -/
def splitLC (i : ℕ) (m : Masks) (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom last : Bool) :
    ℕ → List ℤ → List ℕ → List ℕ → ℕ → Bool × ℕ
  | 0, _, _, _, cnt => (false, cnt)
  | d + 1, W, ls, Ns, cnt =>
    let j := pickW last n W
    let W' := halveW W j
    bif deg sh j == 0 then runLC κ i m n sh B strict dom last d 0 W' ls Ns cnt
    else
      match subAllM m B sh j (halfW sh j) (-1) 1 (2 ^ deg sh j) ls Ns,
        subAllM m B sh j (halfW sh j) 1 1 (2 ^ deg sh j) ls Ns with
      | some Lo, some Hi =>
        let lo := runLC κ i m n sh B strict dom last d 1 W' (Lo.map (l1O B m.ones)) Lo cnt
        bif lo.1 then runLC κ i m n sh B strict dom last d 1 W' (Hi.map (l1O B m.ones)) Hi lo.2
        else lo
      | _, _ => (false, cnt)

theorem splitLC_fst (i : ℕ) (m : Masks) (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom last : Bool) :
    ∀ (d : ℕ) (W : List ℤ) (ls Ns : List ℕ) (cnt : ℕ),
      (splitLC κ i m n sh B strict dom last d W ls Ns cnt).1 =
        splitL κ m n sh B strict dom last d W ls Ns
  | 0, _, _, _, _ => rfl
  | d + 1, W, ls, Ns, cnt => by
    simp only [splitLC, splitL]
    cases deg sh (pickW last n W) == 0
    · simp only [Bool.cond_false]
      split
      · simp only [cond_fst, runLC_fst, cond_self_and]
      · rfl
    · simp only [Bool.cond_true, runLC_fst]

variable (κ) in
/-- `runDivM` with the tuple `i` and the boxes counted in the dominance's beat lines
(`runDivMC_eq`). -/
def runDivMC (i : ℕ) (m : Masks) (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom last : Bool)
    (depth : ℕ) (W : List ℤ) (fs : List (ℕ × ℤ × ℤ)) (Ns : List ℕ) : Bool :=
  bif strict then (runLC κ i m n sh B strict dom last depth 0 W (Ns.map (l1O B m.ones)) Ns 0).1
  else
    let ls := Ns.map (l1O B m.ones)
    bif boxOkMK κ (boxKeys i 1 0) m n sh B strict dom ls Ns then true
    else
      let r := match divAllM m B sh fs Ns with
        | some Ts => runLC κ i m n sh B strict dom last depth 0 W (Ts.map (l1O B m.ones)) Ts 1
        | none => (false, 1)
      r.1 || (splitLC κ i m n sh B strict dom last depth W ls Ns r.2).1

theorem runDivMC_eq (i : ℕ) (m : Masks) (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom last : Bool)
    (depth : ℕ) (W : List ℤ) (fs : List (ℕ × ℤ × ℤ)) (Ns : List ℕ) :
    runDivMC κ i m n sh B strict dom last depth W fs Ns =
      runDivM κ m n sh B strict dom last depth W fs Ns := by
  simp only [runDivMC, runDivM, runLC_fst, splitLC_fst, boxOkMK_eq, runM]
  cases strict
  · simp only [Bool.cond_false]
    cases boxOkM κ m n sh B false dom (Ns.map (l1O B m.ones)) Ns
    · simp only [Bool.cond_false, Bool.false_or]
      split <;> simp only [runLC_fst]
    · rfl
  · rfl

end Field

end Lay

end Nieuwland.Check
