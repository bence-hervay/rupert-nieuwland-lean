import Modules.Certificate.Decode

/-!
# Native checks of exported subtrees

The exporter's native mode (`code/lean-export cert --native`) writes a subtree of a certificate's
cover as one string: entries `@name term` in the exporter's Lean syntax, with the cover tree as the
entry `cover` (`Cert/Syn.lean`, `Cert/Decode.lean`). `Native.check` decodes the string and checks
the subtree, and a chunk module proves `Native.check … = true` by `native_decide`: compiled code
evaluates the check, and Lean records the result as an axiom of that statement, which
`#print axioms` lists. **This is the trust level of whole certificates: the kernel checks
`Native.settled_of_check` and everything else, but not the evaluation of the checks.** The library
and its examples remain checked by the kernel alone.

The decoded data (`Native.Data`) keeps every claim once (`claims`), every leaf of the tree once
(`leaves`, keyed by its term), and the tree with the leaves' indices, so that a claim cited from
several leaves, or by mapped leaves, is checked once. `Native.settled_of_check` is the counterpart
of `GCover.settled_of_checked` for any data the check accepts; the decoder is not trusted.

Claims cited from several chunks, or heavy ones, are checked once in claims modules: a claims text
lists them (entries `claims`, and `leaves` for claims with exclusion leaves), and its module proves
`claimsCheck … = true` natively. A chunk cites claim `j` of the claims module with key `m` as
`.claim (.ext m j)` (leaf `j` as `.ext m j`), and `checkExt` takes the texts it cites by key;
`settled_of_checkExt` needs their `claimsCheck` (`extOk_cons`, `extOk_nil`).

Unsupported parts cannot be decoded: a native check proves its box settled unconditionally.
-/

namespace Nieuwland.Cert.Native

open Check

/-- The claim of a leaf: the claim with index `i` in the data's claims, or the claim with index `j`
of the claims module with key `m` (checked once there: `checkExt`). -/
inductive CRef where
  /-- The claim with index `i` in the data's claims. -/
  | own (i : ℕ)
  /-- The claim with index `j` of the claims module with key `m`. -/
  | ext (m j : ℕ)

/-- The claims and leaves of a claims module (a claims text), each checked once there. Leaves are
claims with exclusion leaves (weighted zooms and chart trees), checked with the symmetry data. -/
structure Ext (κ : Type) where
  /-- The claims. -/
  claims : Array (Claim κ)
  /-- The leaves. -/
  leaves : Array (Leaf κ)

/-- A leaf of a natively checked tree. -/
inductive NLeaf (κ : Type) where
  /-- The claim `c`. -/
  | claim (c : CRef)
  /-- A mapped leaf (`Leaf.mapped`) citing the claim `c`. -/
  | mapped (region : ChartBox) (pre : Option (Q4 κ)) (i j : ℕ) (c : CRef)
  /-- Any other leaf. -/
  | leaf (l : Leaf κ)
  /-- The leaf with index `j` of the claims module with key `m`. -/
  | ext (m j : ℕ)

/-- The decoded data of a subtree: its claims, its leaves, and its cover tree with the indices of
its leaves. -/
structure Data (κ : Type) where
  /-- Every claim of the subtree, once. -/
  claims : Array (Claim κ)
  /-- Every leaf of the tree, once. -/
  leaves : Array (NLeaf κ)
  /-- The cover tree, with the indices of its leaves. -/
  tree : GCover κ ℕ

section Check

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The claim `r`, with the data's claims `cs` and the claims modules' `es` (by key). -/
def CRef.get (cs : Array (Claim κ)) (es : List (ℕ × Ext κ)) : CRef → Option (Claim κ)
  | .own i => cs[i]?
  | .ext m j => (es.lookup m).bind (·.claims[j]?)

/-- The leaf, with the claims and the claims modules. -/
def NLeaf.toLeaf (cs : Array (Claim κ)) (es : List (ℕ × Ext κ)) : NLeaf κ → Option (Leaf κ)
  | .claim c => (c.get cs es).map .claim
  | .mapped r pre i j c => (c.get cs es).map (.mapped r pre i j)
  | .leaf l => some l
  | .ext m j => (es.lookup m).bind (·.leaves[j]?)

/-- The check of the leaf other than its claim's, which is checked once with the claims (or in its
claims module). -/
def NLeaf.check (pts : List (V3 κ)) (D : SymmData κ) (depth : ℕ) (cs : Array (Claim κ))
    (es : List (ℕ × Ext κ)) : NLeaf κ → Bool
  | .claim _ => true
  | .mapped r pre i j c =>
    match c.get cs es with
    | some c => Leaf.imageOk D depth r pre i j c
    | none => false
  | .leaf l => l.check pts D depth
  | .ext _ _ => true

/-- The check of a claims module's claims and leaves. -/
def Ext.check (pts : List (V3 κ)) (D : SymmData κ) (depth : ℕ) (e : Ext κ) : Bool :=
  e.claims.all (·.check pts depth) && e.leaves.all (·.check pts D depth)

/-- The leaf with index `k` fits the tree at the box `B` with the pre-rotation `pre`. -/
def Data.ok (d : Data κ) (es : List (ℕ × Ext κ)) (B : ChartBox) (pre : Option (Q4 κ))
    (k : ℕ) : Bool :=
  match d.leaves[k]?.bind (NLeaf.toLeaf d.claims es) with
  | some l => Leaf.ok B pre l
  | none => false

/-- The check of decoded data on the box `B`, with the claims modules `es` (checked there): every
claim of the data, leaf and chart change checks, and the tree's leaves lie in their regions. -/
def Data.check (pts : List (V3 κ)) (D : SymmData κ) (depth : ℕ) (B : ChartBox) (d : Data κ)
    (es : List (ℕ × Ext κ)) : Bool :=
  d.claims.all (·.check pts depth) && d.leaves.all (NLeaf.check pts D depth d.claims es) &&
    d.tree.recharts.all (·.check depth) && d.tree.check (d.ok es) B none

theorem mem_of_lookup {α : Type} {es : List (ℕ × α)} {m : ℕ} {a : α} (h : es.lookup m = some a) :
    (m, a) ∈ es := by
  induction es with
  | nil => simp [List.lookup] at h
  | cons e es ih =>
    obtain ⟨k, b⟩ := e
    by_cases hk : m = k
    · subst hk
      simp only [List.lookup, BEq.rfl, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    · have hb : (m == k) = false := by simpa using hk
      simp only [List.lookup, hb] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem CRef.check_get {pts : List (V3 κ)} {D : SymmData κ} {depth : ℕ} {cs : Array (Claim κ)}
    {es : List (ℕ × Ext κ)} (hcs : ∀ c ∈ cs, c.check pts depth = true)
    (hes : ∀ e ∈ es, e.2.check pts D depth = true) {r : CRef} {c : Claim κ}
    (h : r.get cs es = some c) : c.check pts depth = true := by
  cases r with
  | own i => exact hcs c (Array.mem_of_getElem? h)
  | ext m j =>
    simp only [get, Option.bind_eq_some_iff] at h
    obtain ⟨a, ha, hc⟩ := h
    have := hes (m, a) (mem_of_lookup ha)
    simp only [Ext.check, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at this
    exact this.1 c (Array.mem_of_getElem? hc)

theorem NLeaf.check_leaf {pts : List (V3 κ)} {D : SymmData κ} {depth : ℕ}
    {cs : Array (Claim κ)} {es : List (ℕ × Ext κ)}
    (hcs : ∀ c ∈ cs, c.check pts depth = true) (hes : ∀ e ∈ es, e.2.check pts D depth = true)
    {n : NLeaf κ} (hn : n.check pts D depth cs es = true) {l : Leaf κ}
    (hl : n.toLeaf cs es = some l) : l.check pts D depth = true := by
  cases n with
  | claim c =>
    simp only [toLeaf, Option.map_eq_some_iff] at hl
    obtain ⟨c', hc', rfl⟩ := hl
    exact CRef.check_get hcs hes hc'
  | mapped r pre i j c =>
    simp only [toLeaf, Option.map_eq_some_iff] at hl
    obtain ⟨c', hc', rfl⟩ := hl
    simp only [check, hc'] at hn
    exact Leaf.check_mapped hn (CRef.check_get hcs hes hc')
  | leaf l' =>
    simp only [toLeaf, Option.some.injEq] at hl
    subst hl
    exact hn
  | ext m j =>
    simp only [toLeaf, Option.bind_eq_some_iff] at hl
    obtain ⟨a, ha, hl⟩ := hl
    have := hes (m, a) (mem_of_lookup ha)
    simp only [Ext.check, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at this
    exact this.2 l (Array.mem_of_getElem? hl)

/-- **Soundness of decoded data.** If the data checks on the box `B` with the claims modules `es`,
and these check, every pose of `B` is settled. -/
theorem Data.settled_of_check {pts : List (V3 κ)} {D : SymmData κ} {depth : ℕ}
    (hD : D.ok pts = true) {B : ChartBox} {d : Data κ} {es : List (ℕ × Ext κ)}
    (hes : ∀ e ∈ es, e.2.check pts D depth = true) (h : d.check pts D depth B es = true) :
    ∀ p ∈ B.poses, Settled pts D p := by
  simp only [Data.check, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem,
    List.all_eq_true] at h
  obtain ⟨⟨⟨hcs, hls⟩, hr⟩, ht⟩ := h
  have := GCover.check_sound (depth := depth) (fun C pre k _ hok p hp ↦ by
    simp only [Data.ok] at hok
    split at hok
    next l hl =>
      simp only [Leaf.ok, Bool.and_eq_true] at hok
      simp only [Option.bind_eq_some_iff] at hl
      obtain ⟨n, hn, hnl⟩ := hl
      have hs := Leaf.check_sound hD
        (NLeaf.check_leaf hcs hes (hls n (Array.mem_of_getElem? hn)) hnl)
        p (ChartBox.poses_subset hok.1 hp)
      rwa [Exact.rePre_eq_of_preEq hok.2] at hs
    next => simp at hok) hr ht
  exact fun p hp ↦ settledRot_none.mp (this p hp)

end Check

/-! ### Decoding -/

section Decode

variable {κ : Type} [Dec κ]

/-- The state of decoding a tree: the claims and leaves so far, by key. -/
structure St (κ : Type) where
  /-- The index of each claim decoded from a reference, by its name. -/
  claimIx : Std.HashMap String ℕ := {}
  /-- The claims so far. -/
  claims : Array (Claim κ) := #[]
  /-- The index of each leaf with a key (`leafKey`), by its key. -/
  leafIx : Std.HashMap String ℕ := {}
  /-- The leaves so far. -/
  leaves : Array (NLeaf κ) := #[]

/-- The claim `s`: a claim of a claims text (`.ext m j`), or the index of a claim of the data (a
reference or a term), added if new. -/
def claimIdx (env : Env) (s : Syn) (st : St κ) : Option (CRef × St κ) :=
  match s with
  | .dot "ext" #[m, j] => do some (.ext (← Dec.dec env m) (← Dec.dec env j), st)
  | .name n =>
    match st.claimIx[n]? with
    | some i => some (.own i, st)
    | none => do
      let c ← Dec.dec env s
      some (.own st.claims.size,
        { st with claimIx := st.claimIx.insert n st.claims.size, claims := st.claims.push c })
  | _ => do
    let c ← Dec.dec env s
    some (.own st.claims.size, { st with claims := st.claims.push c })

/-- The leaf `s`, its claim added to the state. -/
def nleaf (env : Env) (s : Syn) (st : St κ) : Option (NLeaf κ × St κ) :=
  match Dec.view env s with
  | .dot "claim" #[c] => do
    let (k, st) ← claimIdx env c st
    some (.claim k, st)
  | .dot "mapped" #[r, p, i, j, c] => do
    let (k, st) ← claimIdx env c st
    some (.mapped (← Dec.dec env r) (← Dec.dec env p) (← Dec.dec env i) (← Dec.dec env j) k, st)
  | .dot "ext" #[m, j] => do some (.ext (← Dec.dec env m) (← Dec.dec env j), st)
  | t => do some (.leaf (← Dec.dec env t), st)

/-- The key of a leaf's term, if it is a reference or a constructor applied to one. -/
def leafKey : Syn → Option String
  | .name n => some n
  | .dot c #[.name n] => some (c ++ " " ++ n)
  | _ => none

/-- The index of the leaf `s`, added if new. -/
def leafIdx (env : Env) (s : Syn) (st : St κ) : Option (ℕ × St κ) :=
  let key := leafKey s
  match key.bind (st.leafIx[·]?) with
  | some i => some (i, st)
  | none => do
    let (n, st) ← nleaf env s st
    let i := st.leaves.size
    let st := { st with leaves := st.leaves.push n }
    some (i, match key with
      | some k => { st with leafIx := st.leafIx.insert k i }
      | none => st)

/-- The cover tree `s` (`GCover` of items `.leaf l`) with the indices of its leaves. -/
partial def tree (env : Env) (s : Syn) (st : St κ) : Option (GCover κ ℕ × St κ) :=
  match Dec.view env s with
  | .dot "leaf" #[.dot "leaf" #[x]] => do
    let (i, st) ← leafIdx env x st
    some (.leaf i, st)
  | .dot "split" #[d, lo, hi] => do
    let d ← Dec.dec env d
    let (lo, st) ← tree env lo st
    let (hi, st) ← tree env hi st
    some (.split d lo hi, st)
  | .dot "rechart" #[r, t] => do
    let r ← Dec.dec env r
    let (t, st) ← tree env t st
    some (.rechart r t, st)
  | _ => none

/-- The data of a text: its entries, with the cover tree as the entry `cover`. -/
def decode (text : String) : Option (Data κ) := do
  let env ← Syn.entries text
  let (t, st) ← tree env (← env["cover"]?) {}
  some ⟨st.claims, st.leaves, t⟩

/-- The claims and leaves of a claims text: its entries, with the lists of its claims and leaves as
the entries `claims` and `leaves`. -/
def decodeClaims (text : String) : Option (Ext κ) := do
  let env ← Syn.entries text
  let cs : List (Claim κ) ← Dec.dec env (← env["claims"]?)
  let ls : List (Leaf κ) ← Dec.dec env (← env["leaves"]?)
  some ⟨cs.toArray, ls.toArray⟩

/-- The claims modules of the claims texts `exts`, by key. -/
def decodeExts (exts : List (ℕ × String)) : Option (List (ℕ × Ext κ)) :=
  exts.mapM fun e ↦ (decodeClaims e.2).map (e.1, ·)

end Decode

/-! ### Native checks -/

section Native

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] [Dec κ]

/-! The entry points of generated modules are `@[nospecialize]`: compiled code calls them with the
instances of the field as arguments, instead of specializing them, and everything below them, in
the generated module, where only the interpreter would run them. Compiled code only. -/

/-- The check of the subtree in `text` on the box `B`. -/
@[nospecialize]
def check (pts : List (V3 κ)) (D : SymmData κ) (depth : ℕ) (B : ChartBox) (text : String) :
    Bool :=
  match decode (κ := κ) text with
  | some d => d.check pts D depth B []
  | none => false

/-- **Native checks.** If the subtree in `text` checks on the box `B`, every pose of `B` is
settled. -/
theorem settled_of_check {pts : List (V3 κ)} {D : SymmData κ} {depth : ℕ} {B : ChartBox}
    {text : String} (hD : D.ok pts = true) (h : check pts D depth B text = true) :
    ∀ p ∈ B.poses, Settled pts D p := by
  unfold check at h
  split at h
  next d _ => exact Data.settled_of_check hD (by simp) h
  next => simp at h

/-- The check of a claims text (a claims module): every claim and leaf checks. -/
@[nospecialize]
def claimsCheck (pts : List (V3 κ)) (D : SymmData κ) (depth : ℕ) (text : String) : Bool :=
  match decodeClaims (κ := κ) text with
  | some e => e.check pts D depth
  | none => false

/-- The check of the subtree in `text` on the box `B`, citing the claims of the claims texts
`exts` (by key; each checked once, by `claimsCheck` in its claims module). -/
@[nospecialize]
def checkExt (pts : List (V3 κ)) (D : SymmData κ) (depth : ℕ) (B : ChartBox) (text : String)
    (exts : List (ℕ × String)) : Bool :=
  match decode (κ := κ) text, decodeExts (κ := κ) exts with
  | some d, some es => d.check pts D depth B es
  | _, _ => false

theorem decodeExts_check {pts : List (V3 κ)} {D : SymmData κ} {depth : ℕ}
    {exts : List (ℕ × String)} (hx : ∀ e ∈ exts, claimsCheck pts D depth e.2 = true)
    {es : List (ℕ × Ext κ)} (h : decodeExts exts = some es) :
    ∀ e ∈ es, e.2.check pts D depth = true := by
  induction exts generalizing es with
  | nil =>
    simp only [decodeExts, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    simp [← h]
  | cons x xs ih =>
    simp only [decodeExts, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.map_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨_, ⟨cs, hcs, rfl⟩, rest, hrest, rfl⟩ := h
    have hx0 := hx x List.mem_cons_self
    simp only [claimsCheck, hcs] at hx0
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact hx0
    · exact ih (fun e he ↦ hx e (List.mem_cons_of_mem _ he)) hrest e he

/-- **Native checks with claims modules.** If the claims texts `exts` check (`claimsCheck`, in
their modules) and the subtree in `text` checks on the box `B` citing them, every pose of `B` is
settled. -/
theorem settled_of_checkExt {pts : List (V3 κ)} {D : SymmData κ} {depth : ℕ} {B : ChartBox}
    {text : String} {exts : List (ℕ × String)} (hD : D.ok pts = true)
    (hx : ∀ e ∈ exts, claimsCheck pts D depth e.2 = true)
    (h : checkExt pts D depth B text exts = true) : ∀ p ∈ B.poses, Settled pts D p := by
  unfold checkExt at h
  split at h
  next d es _ hes => exact Data.settled_of_check hD (decodeExts_check hx hes) h
  next => simp at h

theorem extOk_nil {pts : List (V3 κ)} {D : SymmData κ} {depth : ℕ} :
    ∀ e ∈ ([] : List (ℕ × String)), claimsCheck pts D depth e.2 = true := by
  simp

theorem extOk_cons {pts : List (V3 κ)} {D : SymmData κ} {depth : ℕ} {m : ℕ} {t : String}
    {exts : List (ℕ × String)} (h : claimsCheck pts D depth t = true)
    (hs : ∀ e ∈ exts, claimsCheck pts D depth e.2 = true) :
    ∀ e ∈ (m, t) :: exts, claimsCheck pts D depth e.2 = true := by
  intro e he
  rcases List.mem_cons.1 he with rfl | he
  · exact h
  · exact hs e he

end Native

/-! ### Heavy entries in parts

A claims text with one entry, a claim or a leaf whose evidence is a chart tree or a weighted zoom,
is checked in parts, as the kernel checks large ones (`ChartTree.check_of_parts`,
`WZoom.check_of_parts`): the head (the box and the steps, with the number `m` of leaves) and the
leaves `a, …, b - 1` of consecutive ranges, each natively in its own module. `claimsCheck_of_parts`
concludes the text's `claimsCheck` from the head and the leaves `0, …, m - 1`, which
`partCheck_trans` chains from the ranges. -/

section Parts

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The only entry of a claims module: a claim or a leaf. -/
def Ext.only (e : Ext κ) : Option (Claim κ ⊕ Leaf κ) :=
  match e.claims.toList, e.leaves.toList with
  | [c], [] => some (.inl c)
  | [], [l] => some (.inr l)
  | _, _ => none

/-- The head of the only entry of `e`, a chart tree or a weighted zoom with `m` leaves. -/
def Ext.head (e : Ext κ) (m : ℕ) : Bool :=
  match e.only with
  | some (.inl c) =>
    match c.ev with
    | .tree T => T.head c.region m
    | .wzoom z => z.head c.region m
    | _ => false
  | some (.inr (.tree r _ T)) => T.head r m
  | some (.inr (.zoom r z)) => z.head r m
  | _ => false

/-- The checks of the leaves `a, …, b - 1` of the only entry of `e`. -/
def Ext.part (pts : List (V3 κ)) (D : SymmData κ) (e : Ext κ) (a b : ℕ) : Bool :=
  match e.only with
  | some (.inl c) =>
    match c.ev with
    | .tree T => T.leavesOk pts none c.region a b c.pre
    | .wzoom z => z.leavesOk pts none c.region a b c.pre
    | _ => false
  | some (.inr (.tree r pre T)) => T.leavesOk pts (some D) r a b pre
  | some (.inr (.zoom r z)) => z.leavesOk pts (some D) r a b
  | _ => false

theorem Ext.part_trans {pts : List (V3 κ)} {D : SymmData κ} {e : Ext κ} {a b c : ℕ}
    (h₁ : e.part pts D a b = true) (h₂ : e.part pts D b c = true) : e.part pts D a c = true := by
  unfold Ext.part at *
  rcases ho : e.only with _ | (c' | l) <;> simp only [ho, Bool.false_eq_true] at h₁ h₂ ⊢
  · cases hev : c'.ev <;> simp only [hev, Bool.false_eq_true] at h₁ h₂ ⊢
    · exact WZoom.leavesOk_trans h₁ h₂
    · exact ChartTree.leavesOk_trans h₁ h₂
  · cases l <;> simp only [Bool.false_eq_true] at h₁ h₂ ⊢
    · exact WZoom.leavesOk_trans h₁ h₂
    · exact ChartTree.leavesOk_trans h₁ h₂

theorem Ext.check_of_inl {pts : List (V3 κ)} {D : SymmData κ} {depth : ℕ} {e : Ext κ}
    {c : Claim κ} (ho : e.only = some (.inl c)) (hc : c.check pts depth = true) :
    e.check pts D depth = true := by
  unfold Ext.only at ho
  unfold Ext.check
  rw [← Array.all_toList, ← Array.all_toList]
  split at ho
  · next c' hcs hls =>
    simp only [Option.some.injEq, Sum.inl.injEq] at ho
    subst ho
    simp [hcs, hls, hc]
  · simp at ho
  · simp at ho

theorem Ext.check_of_inr {pts : List (V3 κ)} {D : SymmData κ} {depth : ℕ} {e : Ext κ}
    {l : Leaf κ} (ho : e.only = some (.inr l)) (hl : l.check pts D depth = true) :
    e.check pts D depth = true := by
  unfold Ext.only at ho
  unfold Ext.check
  rw [← Array.all_toList, ← Array.all_toList]
  split at ho
  · simp at ho
  · next l' hcs hls =>
    simp only [Option.some.injEq, Sum.inr.injEq] at ho
    subst ho
    simp [hcs, hls, hl]
  · simp at ho

/-- **The check of the only entry from its parts.** -/
theorem Ext.check_of_parts {pts : List (V3 κ)} {D : SymmData κ} {depth : ℕ} {e : Ext κ} {m : ℕ}
    (h : e.head m = true) (hp : e.part pts D 0 m = true) : e.check pts D depth = true := by
  unfold Ext.head at h
  unfold Ext.part at hp
  rcases ho : e.only with _ | (c | l) <;> simp only [ho, Bool.false_eq_true] at h hp
  · refine Ext.check_of_inl ho ?_
    unfold Claim.check
    cases hev : c.ev <;> simp only [hev, Bool.false_eq_true] at h hp
    · exact WZoom.check_of_parts h hp
    · exact ChartTree.check_of_parts h hp
  · refine Ext.check_of_inr ho ?_
    cases l <;> simp only [Bool.false_eq_true] at h hp
    · exact WZoom.check_of_parts h hp
    · exact ChartTree.check_of_parts h hp

end Parts

section NativeParts

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] [Dec κ]

/-- The head of the only entry of the claims text `text`, with `m` leaves (`pts` gives the type of
exact values only). -/
@[nospecialize]
def headCheck (_pts : List (V3 κ)) (text : String) (m : ℕ) : Bool :=
  match decodeClaims (κ := κ) text with
  | some e => e.head m
  | none => false

/-- The checks of the leaves `a, …, b - 1` of the only entry of the claims text `text`. -/
@[nospecialize]
def partCheck (pts : List (V3 κ)) (D : SymmData κ) (text : String) (a b : ℕ) : Bool :=
  match decodeClaims (κ := κ) text with
  | some e => e.part pts D a b
  | none => false

theorem partCheck_trans {pts : List (V3 κ)} {D : SymmData κ} {text : String} {a b c : ℕ}
    (h₁ : partCheck pts D text a b = true) (h₂ : partCheck pts D text b c = true) :
    partCheck pts D text a c = true := by
  unfold partCheck at *
  split at h₁
  next e he => simp only [he] at h₂; exact Ext.part_trans h₁ h₂
  next => simp at h₁

/-- **A claims text checked in parts.** -/
theorem claimsCheck_of_parts {pts : List (V3 κ)} {D : SymmData κ} {depth : ℕ} {text : String}
    {m : ℕ} (h : headCheck pts text m = true) (hp : partCheck pts D text 0 m = true) :
    claimsCheck pts D depth text = true := by
  unfold headCheck at h
  unfold partCheck at hp
  unfold claimsCheck
  split at h
  next e he => simp only [he] at hp ⊢; exact Ext.check_of_parts h hp
  next => simp at h

end NativeParts

end Nieuwland.Cert.Native
