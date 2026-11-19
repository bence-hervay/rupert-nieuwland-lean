/-!
# Progress lines of compiled checks

A check of the leaves of a chart tree or weighted zoom in parts (`ChartTree.leavesOk`,
`WZoom.leavesOk`) can run for hours in one native module. Compiled code reports its progress on
stderr, in lines

`NOPERTS-PROGRESS 1 <kind> <done> <total> idx=<k> [key=value ...]`

with the leaves of the range checked so far (`done`) and in the range (`total`), and the index
`k` in the whole tree of the current leaf. The kinds:

* `leaf`: after each leaf (`done` counts it), with `ok=<result>`;
* `stage`: once per leaf at a stage boundary, `stage=<name>` with the stage's sizes: `forms` (the
  premise forms, `forms=`, `ok=`), `masks` (the terms' frames, `terms=`), `bits` (the packing:
  `slots=`, `B=` the digit bits, `bits=` the numeral bits, `terms=`, `shape=`) and `tuples`
  (`tuples=`);
* `beat`: inside the loops of a leaf, `stage=<name>`: `mask` after a term's frame and `val`
  after its value (`i=<term> n=<terms>`, `mask` with `shape=`), `vals` after a tuple's numerals
  and `engine` after its sign check (`i=<tuple> n=<tuples>`, `engine` with `ok=`), and `dom`
  after the dominance of one box (`ok=`). At most one beat line is written per
  `NOPERTS_PROGRESS_BEAT_MS` milliseconds (default 20000; `0`: all), so that heavy leaves log a
  few lines a minute.

Lines are written only while a range of leaves is checked (`withLeaves`); the reader timestamps
them.

**Logic.** Nothing is printed: `withLeaves total g` is `g` at the plain step
`fun _ idx f ↦ f idx`, with which `allP` is `List.all` (`allP_eq`), and `stage` and `beat` return
their last argument (`stage_eq`, `beat_eq`). The checks use them only in copies of their
definitions that compiled code runs through `@[csimp]` lemmas proved from these equations
(`ChartTree.leavesOk_eq_leavesOkP`, `WZoom.leavesOk_eq_leavesOkP`, `TObst.check_eq_checkP`,
`Pull.Frame.checkComb_eq_checkCombP`, `Lay.boxOk_eq_boxOkP`), so the definitions that the
kernel checks and the theorem statements are those without progress, and `#print axioms` of every
theorem is unchanged.

**Compiled code** runs them as their `@[implemented_by]` implementations below. These are
`unsafe` (no definition or theorem can refer to them) and, unlike a `@[csimp]` lemma, are not
proved equal to the definitions: a native check trusts them as it trusts the compiler, so each must
compute exactly its definition's value, and does. Each returns its value argument, computed before
the call, unchanged: `stage` and `beat` their last argument, and `withLeaves total g` the value of
`g` at the step `fun _ idx f ↦ f idx` (`aroundImpl` gives `f` the index `idx` read back from the
state it has just set). Beside that they keep the range, the leaf and the count of leaves in one
reference (`Progress.ref`) and the time of the last beat line in another (`Progress.lastBeat`), and
write to the standard error stream of the process (`Progress.err`, flushed after each line): a few
reads of the references and one short line per stage. The compiler treats every function as pure,
so the order of the effects comes from data alone: the leaf's check takes the index from the state
just set, the leaf's line takes the check's result (`endImpl`), and a range's state is made before
the step that captures it. (A version that sequenced the effects through an unused argument lost
them: the compiler removes unused parameters and then the dead calls.)
-/

namespace Nieuwland.Check

universe u v

/-- The state of the progress lines of compiled code: whether a range of leaves is being
checked, the current leaf's index in the tree, and the leaves of the range checked and in all. -/
structure ProgState where
  /-- Whether a range of leaves is being checked. -/
  active : Bool := false
  /-- The current leaf's index in the tree. -/
  idx : Nat := 0
  /-- The leaves of the range checked so far. -/
  done : Nat := 0
  /-- The leaves of the range. -/
  total : Nat := 0

namespace Progress

/-! ### Compiled code -/

/-- The state (compiled code only). -/
@[noinline] unsafe def ref : IO.Ref ProgState := unsafeBaseIO (IO.mkRef {})

/-- The line of `kind` with the keys `keys` (each with a leading space) in the state `p`. -/
unsafe def text (p : ProgState) (kind keys : String) : String :=
  s!"NOPERTS-PROGRESS 1 {kind} {p.done} {p.total} idx={p.idx}{keys}"

/-- The standard error stream as the library is loaded (compiled code initializes the constant
then), before Lean redirects the streams of each command it elaborates: through it a line is
written at once, not when the command (the `native_decide`) ends. -/
@[noinline] unsafe def err : IO.FS.Stream := unsafeBaseIO IO.getStderr

/-- Writes `line` and flushes (errors ignored). -/
unsafe def emit (line : String) : BaseIO Unit := do
  let _ ← (err.putStrLn line *> err.flush).toBaseIO

/-- Sets the state to `p`, then returns it. -/
@[noinline, never_extract] unsafe def setImpl (p : ProgState) : ProgState :=
  unsafeBaseIO do
    ref.set p
    pure p

/-- The end of the leaf of the state `p` (`done` counting it) with its result `r`: sets the
state and writes the leaf's line, then returns `r`. -/
@[noinline, never_extract] unsafe def endImpl (p : ProgState) (r : Bool) : Bool :=
  unsafeBaseIO do
    ref.set p
    emit (text p "leaf" s!" ok={r}")
    pure r

/-- The end of a range, with its result `r`. -/
@[noinline, never_extract] unsafe def stopImpl (r : Bool) : Bool :=
  unsafeBaseIO do
    ref.set {}
    pure r

/-- The step around the `done`-th leaf `idx` of the range of state `s`, checked by `f`: `f` gets
the index `idx` back from the state just set, and the leaf's line the result of `f`. -/
@[noinline] unsafe def aroundImpl (s : ProgState) (done idx : Nat) (f : Nat → Bool) : Bool :=
  let p := setImpl { s with idx, done := done - 1 }
  endImpl { p with done } (f p.idx)

/-- `withLeaves`: the range's state, then `g` at the step around each leaf. -/
unsafe def withLeavesImpl (total : Nat) (g : (Nat → Nat → (Nat → Bool) → Bool) → Bool) : Bool :=
  let s := setImpl { active := true, total }
  stopImpl (g (aroundImpl s))

/-- `stage`: the line of the stage `name` with the keys `keys x`, then `x`. -/
@[noinline, never_extract] unsafe def stageImpl {α : Type} (name : String) (keys : α → String)
    (x : α) : α :=
  unsafeBaseIO do
    let p ← ref.get
    if p.active then emit (text p "stage" s!" stage={name}{keys x}")
    return x

/-- The least milliseconds between two beat lines: `NOPERTS_PROGRESS_BEAT_MS`, default 20000. -/
@[noinline] unsafe def beatMs : Nat :=
  unsafeBaseIO do return ((← IO.getEnv "NOPERTS_PROGRESS_BEAT_MS").bind String.toNat?).getD 20000

/-- The time of the last beat line (milliseconds, `IO.monoMsNow`). -/
@[noinline] unsafe def lastBeat : IO.Ref Nat := unsafeBaseIO (IO.mkRef 0)

/-- `beat`: its line, if `beatMs` have passed since the last beat line. -/
@[noinline, never_extract] unsafe def beatImpl {α : Type} (name : String) (keys : α → String)
    (x : α) : α :=
  unsafeBaseIO do
    let p ← ref.get
    if p.active then
      let now ← IO.monoMsNow
      if (← lastBeat.get) + beatMs ≤ now then
        lastBeat.set now
        emit (text p "beat" s!" stage={name}{keys x}")
    return x

end Progress

/-! ### The logical definitions -/

/-- A check of a range of `total` leaves, given the step around each leaf: logically the step
that checks the leaf (compiled code: `Progress.withLeavesImpl`, progress lines). -/
@[implemented_by Progress.withLeavesImpl]
def withLeaves (_total : Nat) (g : (Nat → Nat → (Nat → Bool) → Bool) → Bool) : Bool :=
  g fun _ idx f ↦ f idx

/-- `x` (compiled code: the stage line `name` with the keys `keys x`, `Progress.stageImpl`). -/
@[implemented_by Progress.stageImpl]
def stage {α : Type} (_name : String) (_keys : α → String) (x : α) : α := x

/-- `x` (compiled code: a beat line `name` with the keys `keys x` if the last is old enough,
`Progress.beatImpl`). -/
@[implemented_by Progress.beatImpl]
def beat {α : Type} (_name : String) (_keys : α → String) (x : α) : α := x

@[simp] theorem withLeaves_eq (total : Nat) (g : (Nat → Nat → (Nat → Bool) → Bool) → Bool) :
    withLeaves total g = g fun _ idx f ↦ f idx := rfl

@[simp] theorem stage_eq {α : Type} (name : String) (keys : α → String) (x : α) :
    stage name keys x = x := rfl

@[simp] theorem beat_eq {α : Type} (name : String) (keys : α → String) (x : α) :
    beat name keys x = x := rfl

/-- `l.all p` with the step `around (k + 1) (a + k)` around the check of the `k`-th element
(from `0`) of `l`, whose index in the whole list is `a + k`. The step returns before the next
element, so the recursion stays a loop. -/
def allP {α : Type u} (p : α → Bool) (around : Nat → Nat → (Nat → Bool) → Bool) (a : Nat) :
    Nat → List α → Bool
  | _, [] => true
  | k, x :: xs => around (k + 1) (a + k) (fun _ ↦ p x) && allP p around a (k + 1) xs

theorem allP_eq {α : Type u} (p : α → Bool) (a : Nat) :
    ∀ k l, allP p (fun _ idx f ↦ f idx) a k l = l.all p
  | _, [] => rfl
  | k, x :: xs => by simp only [allP, List.all_cons, allP_eq p a (k + 1) xs]

/-- `l.all`, with each element's index (from `k`) passed to `p`: for the index in a line. -/
def allIdx {α : Type u} (p : Nat → α → Bool) : Nat → List α → Bool
  | _, [] => true
  | k, x :: xs => p k x && allIdx p (k + 1) xs

theorem allIdx_eq {α : Type u} (p : α → Bool) : ∀ k l, allIdx (fun _ ↦ p) k l = l.all p
  | _, [] => rfl
  | k, x :: xs => by simp only [allIdx, List.all_cons, allIdx_eq p (k + 1) xs]

/-- `l.map`, with each element's index (from `k`) passed to `f`: for the index in a line. -/
def mapIdxP {α : Type u} {β : Type v} (f : Nat → α → β) : Nat → List α → List β
  | _, [] => []
  | k, x :: xs => f k x :: mapIdxP f (k + 1) xs

theorem mapIdxP_eq {α : Type u} {β : Type v} (f : α → β) :
    ∀ k l, mapIdxP (fun _ ↦ f) k l = l.map f
  | _, [] => rfl
  | k, x :: xs => by simp only [mapIdxP, List.map_cons, mapIdxP_eq f (k + 1) xs]

end Nieuwland.Check
