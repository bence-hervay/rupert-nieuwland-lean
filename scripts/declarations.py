#!/usr/bin/env python3
"""Fingerprints of declarations: what decides whether a compiled module still stands.

A compiled module is a list of declarations that Lean's kernel checked in the environment of
that day. It stands in today's environment when **every declaration it uses is the same
declaration today**: the same statement, for a definition the same value, and the same for
everything those use in turn. A theorem's proof is not followed: whoever uses a theorem uses its
statement. This file computes that notion of "the same declaration" as a fingerprint.

    python3 scripts/declarations.py library            the library's table (cached), a summary
    python3 scripts/declarations.py modules OLEAN...   the declarations of compiled modules

**The fingerprint of a declaration** is a SHA-256 of

* its kind and the kernel's data of it (a definition's safety and reducibility hints, an
  inductive type's constructors and counts, a recursor's rules, …), its universe parameters;
* its type, and its value when it is a definition, an opaque constant or a recursor's rule: the
  whole term, written out node by node (`ser` below; binder names, binder kinds and metadata
  nodes are left out, as the kernel ignores them);
* the fingerprints of the declarations of this project that those terms name (the library's and
  the solids'; Mathlib's and Lean's own are fixed by their versions), and of its **companions**:
  the code that runs in its place when a check is evaluated (`native_decide`). These are its
  `_unsafe_rec` twin (the compiled body of a `partial` or well-founded definition), its
  `implemented_by` target and its `@[csimp]` replacement. With them the fingerprint also says
  "the same code ran" for the constants whose value the kernel does not see (the certificate
  parsers are `partial`) or does not run (the progress hooks).

Declarations that name each other (an inductive type with its constructors and recursor, mutual
definitions) are fingerprinted together.

What follows for a compiled module `M` whose own text is unchanged and whose used declarations
all have the fingerprints they had when `M` was compiled:

* every statement and definition of `M` means what it meant: the terms are the same and name
  the same declarations, all the way down;
* every proof of `M` was checked by the kernel against those same statements. A used theorem's
  proof may have changed, its statement has not, and the old proof remains a proof of it
  (adding the old library's declarations under other names changes no statement), so each of
  `M`'s statements is a theorem of today's environment. `build.py --replay` has the kernel
  check `M`'s proofs in today's environment again, with today's proofs;
* an axiom of `native_decide` in `M` says that a definition of `M` evaluates to `true`. The
  definition and everything its evaluation runs is the same today, so the evaluation of that
  day is the evaluation of today.

Not covered, by design: the toolchain, the compile options and Mathlib (the build's base key),
and the correspondence of the compiled library to the library's definitions (`native.py`).
An `extern` declaration in the library is refused: its code is not in any term.
"""
import hashlib
import itertools
import json
import os
import subprocess
import sys
from pathlib import Path

LEAN = Path(__file__).resolve().parents[1]
LIBS = ("Definitions", "Modules")
SEP = "\x1f"
COUNT = itertools.count()

# The Lean side. A declaration is printed as one line:
#   D <name> <kernel data> <universe parameters> <names in the type> <names in the value>
#     <names in the proof> <companions> <the type> <the value>
# (tab-separated; names are separated by U+001F; a name or string has `\`, tab, newline, return,
# U+001F and the separators of `ser` escaped).
COMMON = r"""
open Lean

namespace Decls

def esc (s : String) : String :=
  if s.any (fun c => c == '\\' || c == '\t' || c == '\n' || c == '\r' || c == '\x1f' || c == ';'
      || c == '|' || c == ',' || c == '(' || c == ')') then
    s.foldl (fun acc c => match c with
      | '\\' => acc ++ "\\\\" | '\t' => acc ++ "\\t" | '\n' => acc ++ "\\n" | '\r' => acc ++ "\\r"
      | '\x1f' => acc ++ "\\u" | ';' => acc ++ "\\s" | '|' => acc ++ "\\b" | ',' => acc ++ "\\c"
      | '(' => acc ++ "\\l" | ')' => acc ++ "\\g" | c => acc.push c) ""
  else s

def nm (n : Name) : String := esc (n.toString (escape := true))

partial def lvl : Level → String
  | .zero => "0"
  | .succ l => "S" ++ lvl l
  | .max a b => "M(" ++ lvl a ++ "," ++ lvl b ++ ")"
  | .imax a b => "I(" ++ lvl a ++ "," ++ lvl b ++ ")"
  | .param n => "P(" ++ nm n ++ ")"
  | .mvar _ => "?"

/-- The term `root` written out: its distinct subterms in the order a depth-first walk finishes
them, each as one token that names its children by their numbers; and the constants it names.
Without `emit` only the constants are collected (a proof). No recursion: a list literal of a
certificate is as deep as it is long. -/
def ser (emit : Bool) (root : Expr) (cs0 : Std.HashSet Name) : String × Std.HashSet Name := Id.run do
  let mut ids : Std.HashMap Expr Nat := {}
  let mut next := 0
  let mut out : String := ""
  let mut cs := cs0
  let mut stack : Array Expr := #[root]
  while !stack.isEmpty do
    let e := stack.back!
    if ids.contains e then
      stack := stack.pop
    else
      let kids : Array Expr := match e with
        | .app f a => #[f, a]
        | .lam _ t b _ => #[t, b]
        | .forallE _ t b _ => #[t, b]
        | .letE _ t v b _ => #[t, v, b]
        | .mdata _ b => #[b]
        | .proj _ _ b => #[b]
        | _ => #[]
      let mut ready := true
      for k in kids.reverse do
        if !ids.contains k then
          stack := stack.push k
          ready := false
      if ready then
        stack := stack.pop
        if let .mdata _ b := e then
          ids := ids.insert e ids[b]!
        else
          if let .const n _ := e then cs := cs.insert n
          if let .proj s _ _ := e then cs := cs.insert s
          if emit then
            let k (i : Nat) : String := toString ids[kids[i]!]!
            let tok := match e with
              | .bvar i => "b" ++ toString i
              | .sort u => "s" ++ lvl u
              | .const n us => us.foldl (fun acc u => acc ++ "|" ++ lvl u) ("c" ++ nm n)
              | .app .. => "a" ++ k 0 ++ "," ++ k 1
              | .lam .. => "l" ++ k 0 ++ "," ++ k 1
              | .forallE .. => "p" ++ k 0 ++ "," ++ k 1
              | .letE .. => "z" ++ k 0 ++ "," ++ k 1 ++ "," ++ k 2
              | .lit (.natVal n) => "n" ++ toString n
              | .lit (.strVal s) => "t" ++ esc s
              | .proj s i _ => "j" ++ nm s ++ "|" ++ toString i ++ "|" ++ k 0
              | .mvar _ => "?m"
              | .fvar _ => "?f"
              | .mdata .. => ""
            out := out ++ tok ++ ";"
          ids := ids.insert e next
          next := next + 1
  return (out, cs)

def names (cs : Std.HashSet Name) (keep : Name → Bool) : String :=
  "\x1f".intercalate ((cs.toArray.filter keep).map nm |>.qsort (· < ·)).toList

def boolS (b : Bool) : String := if b then "1" else "0"

/-- One declaration as a line. `companions`: the code that runs in its place; `keep`: the names
worth printing (of this project, when that is known). -/
def line (name : Name) (ci : ConstantInfo) (companions : Array Name) (keep : Name → Bool) : String := Id.run do
  let list (ns : List Name) : String := ",".intercalate (ns.map nm)
  let (tS, tC) := ser true ci.type {}
  let mut data := ""
  let mut vS := ""
  let mut vC : Std.HashSet Name := {}
  let mut pC : Std.HashSet Name := {}
  match ci with
  | .axiomInfo v => data := "axiom " ++ boolS v.isUnsafe
  | .thmInfo v =>
    data := "theorem"
    pC := (ser false v.value {}).2
  | .defnInfo v =>
    let safety := match v.safety with | .safe => "safe" | .unsafe => "unsafe" | .partial => "partial"
    let hints := match v.hints with | .opaque => "opaque" | .abbrev => "abbrev" | .regular h => "regular" ++ toString h
    data := "def " ++ safety ++ " " ++ hints
    (vS, vC) := ser true v.value {}
  | .opaqueInfo v =>
    data := "opaque " ++ boolS v.isUnsafe
    (vS, vC) := ser true v.value {}
  | .quotInfo v =>
    data := "quot " ++ (match v.kind with | .type => "type" | .ctor => "ctor" | .lift => "lift" | .ind => "ind")
  | .inductInfo v =>
    data := s!"inductive {v.numParams} {v.numIndices} {v.numNested} {boolS v.isRec} {boolS v.isUnsafe} {boolS v.isReflexive} ({list v.all}) ({list v.ctors})"
    for n in v.all ++ v.ctors do vC := vC.insert n
  | .ctorInfo v =>
    data := s!"constructor {nm v.induct} {v.cidx} {v.numParams} {v.numFields} {boolS v.isUnsafe}"
    vC := vC.insert v.induct
  | .recInfo v =>
    data := s!"recursor {v.numParams} {v.numIndices} {v.numMotives} {v.numMinors} {boolS v.k} {boolS v.isUnsafe} ({list v.all})"
    for n in v.all do vC := vC.insert n
    for r in v.rules do
      let (s, c) := ser true r.rhs vC
      vS := vS ++ "(" ++ nm r.ctor ++ "|" ++ toString r.nfields ++ ")" ++ s ++ "#"
      vC := c.insert r.ctor
  let lv := ",".intercalate (ci.levelParams.map nm)
  let comp := "\x1f".intercalate (companions.map nm).toList
  return "D\t" ++ nm name ++ "\t" ++ data ++ "\t" ++ lv ++ "\t" ++ names tC keep ++ "\t" ++ names vC keep ++ "\t"
    ++ names pC keep ++ "\t" ++ comp ++ "\t" ++ tS ++ "\t" ++ vS

end Decls
"""

# A library (the modules under the roots ROOTS, imported by IMPORTS), in the environment of its
# compiled modules: `M` lines name its modules.
LIBRARY = "IMPORTS" + COMMON + r"""
open Decls in
#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let roots : List Name := [ROOTS]
  let lib (m : Name) : Bool := roots.any (·.isPrefixOf m)
  let ours (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some i => lib mods[i.toNat]!
    | none => false
  let out ← IO.getStdout
  for m in mods do
    if lib m then out.putStrLn ("M\t" ++ nm m)
  let csimp := Compiler.CSimp.ext.getState env
  for (c, ci) in env.constants.toList do
    unless ours c do continue
    if isExtern env c then throwError "an extern declaration in the library: {c}"
    let mut comp : Array Name := #[]
    if env.contains (Compiler.mkUnsafeRecName c) then comp := comp.push (Compiler.mkUnsafeRecName c)
    if let some t := Compiler.implementedByAttr.getParam? env c then comp := comp.push t
    if let some e := csimp.map.find? c then comp := comp.push e.toDeclName
    out.putStrLn (line c ci comp ours)
  out.putStrLn "END"
"""

# Compiled modules read as files, with no environment: `F <path> <imports>` before each one's
# declarations. A generated module has no attribute (the screen), so its only companions are
# `_unsafe_rec` twins, which are beside their definitions.
MODULES = "import Lean\n" + COMMON + r"""
open Decls in
unsafe def run (list : String) : IO Unit := do
  let out ← IO.getStdout
  for p in (← IO.FS.lines list) do
    let (mod, _) ← readModuleData p
    out.putStrLn ("F\t" ++ p ++ "\t" ++ "\x1f".intercalate (mod.imports.map fun i => nm i.module).toList)
    let own : Std.HashSet Name := mod.constNames.foldl (·.insert ·) {}
    for name in mod.constNames, ci in mod.constants do
      let twin := Compiler.mkUnsafeRecName name
      out.putStrLn (line name ci (if own.contains twin then #[twin] else #[]) (fun _ => true))
  out.putStrLn "END"

#eval run "LIST"
"""


def sha(*parts):
    h = hashlib.sha256()
    for p in parts:
        b = p if isinstance(p, bytes) else p.encode()
        h.update(len(b).to_bytes(8, "big") + b)
    return h.hexdigest()


def run_lean(text, lean, env):
    """The lines `lean` prints for the module `text`, as lists of tab-separated byte fields;
    exits when it fails or the output does not end with `END`."""
    tmp = LEAN / f".lake/decls-{os.getpid()}-{next(COUNT)}.lean"
    tmp.write_text(text)
    p = None
    try:
        # (a deep term needs no deep stack: `ser` is a loop)
        p = subprocess.Popen([lean, "-DmaxRecDepth=100000", f"--root={LEAN}", str(tmp)], cwd=LEAN, env=env,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        last = None
        for raw in p.stdout:
            last = raw.rstrip(b"\n").split(b"\t")
            if last[0] in (b"D", b"F", b"M"):
                yield last
            elif last != [b"END"]:
                sys.exit(f"declarations: unexpected output: {raw[:400]!r}")
        err = p.stderr.read().decode(errors="replace")
        if p.wait() != 0 or last != [b"END"]:
            sys.exit(f"declarations: lean failed (exit {p.returncode}):\n{err[-3000:]}")
    finally:
        if p is not None:
            if p.poll() is None:
                p.kill()
            p.wait()
            p.stdout.close()
            p.stderr.close()
        tmp.unlink(missing_ok=True)


def entry(f):
    """A `D` line as (name, local fingerprint, names for whoever uses it, names in its proof)."""
    if len(f) != 10:
        sys.exit(f"declarations: a line of {len(f)} fields: {b' '.join(f)[:300]!r}")
    name, data, levels, t, v, p, comp, ts, vs = (x.decode() if i < 7 else x for i, x in enumerate(f[1:]))
    split = lambda s: set(s.split(SEP)) if s else set()
    return name, sha(data, levels, ts, vs), split(t) | split(v) | split(comp), split(p)


def fingerprints(entries, known):
    """The fingerprints of `entries` (name -> (local fingerprint, names used)), given those of
    the declarations fingerprinted before (`known`). A used name in neither is not of this
    project. Declarations that use each other get their fingerprints together."""
    index, low, on, stack, out, n = {}, {}, set(), [], {}, 0
    deps = {a: sorted(d for d in ds if d in entries and d != a) for a, (_, ds) in entries.items()}
    for root in entries:  # Tarjan's components, without recursion
        if root in index:
            continue
        work = [(root, 0)]
        while work:
            a, i = work.pop()
            if i == 0:
                index[a] = low[a] = n
                n += 1
                stack.append(a)
                on.add(a)
            for j in range(i, len(deps[a])):
                b = deps[a][j]
                if b not in index:
                    work.append((a, j + 1))
                    work.append((b, 0))
                    break
                if b in on:
                    low[a] = min(low[a], index[b])
            else:
                if low[a] == index[a]:
                    comp = []
                    while True:
                        b = stack.pop()
                        on.discard(b)
                        comp.append(b)
                        if b == a:
                            break
                    members = set(comp)
                    outer = sorted({d for b in comp for d in entries[b][1]} - members)
                    parts = [f"{b}={entries[b][0]}" for b in sorted(comp)]
                    for d in outer:
                        fp = out.get(d) or known.get(d)
                        if fp:
                            parts.append(f"{d}:{fp}")
                    whole = sha(*parts)
                    for b in comp:
                        out[b] = sha(whole, b)
                if work:
                    low[work[-1][0]] = min(low[work[-1][0]], low[a])
    return out


def library_key():
    """A digest of the compiled library: the oleans of `Definitions` and `Modules`."""
    out = LEAN / ".lake/build/lib/lean"
    files = sorted(p for d in LIBS for p in [out / f"{d}.olean", *(out / d).rglob("*.olean")] if p.exists()
                   and not p.name.endswith((".server.olean", ".private.olean")))
    if not files:
        sys.exit("declarations: no compiled library (lake build Definitions Modules)")
    return sha(*(f"{p.relative_to(out)}={hashlib.sha256(p.read_bytes()).hexdigest()}" for p in files))


def table(roots, lean, env):
    """(the modules, {declaration: fingerprint}) of the compiled library under `roots`."""
    text = LIBRARY.replace("IMPORTS", "import Lean\n" + "".join(f"import {r}\n" for r in roots)).replace("ROOTS", ", ".join(f"`{r}" for r in roots))
    modules, entries = [], {}
    for f in run_lean(text, lean, env):
        if f[0] == b"M":
            modules.append(f[1].decode())
        else:
            name, local, uses, _ = entry(f)
            entries[name] = (local, uses)
    return sorted(modules), fingerprints(entries, {})


def library(lean, env, log=lambda s: None):
    """The library's table: {"key", "modules": [...], "decls": {name: fingerprint}}; computed
    from the compiled library and kept beside it (`.lake/build/declarations.json`) under the
    oleans' digest."""
    cache, key = LEAN / ".lake/build/declarations.json", library_key()
    if cache.exists():
        t = json.loads(cache.read_text())
        if t.get("key") == key:
            return t
    modules, decls = table(LIBS, lean, env)
    t = {"key": key, "modules": modules, "decls": decls}
    tmp = cache.with_suffix(".tmp")
    tmp.write_text(json.dumps(t))
    os.replace(tmp, cache)
    log(f"  the library's declarations: {len(t['decls'])} in {len(modules)} modules")
    return t


def modules(oleans, lean, env):
    """The declarations of compiled modules, read from their oleans: yields
    (path, imports, {name: (local fingerprint, names used)}, all names used), in the order
    given. The names used are every constant in the module's terms, proofs included."""
    if not oleans:
        return
    lst = LEAN / f".lake/decls-{os.getpid()}-{next(COUNT)}.list"
    lst.write_text("".join(f"{p}\n" for p in oleans))
    cur = None
    try:
        for f in run_lean(MODULES.replace("LIST", str(lst)), lean, env):
            if f[0] == b"F":
                if cur:
                    yield cur
                cur = (f[1].decode(), [i for i in f[2].decode().split(SEP) if i], {}, set())
            else:
                name, local, uses, proof = entry(f)
                cur[2][name] = (local, uses)
                cur[3].update(uses, proof)
        if cur:
            yield cur
    finally:
        lst.unlink(missing_ok=True)


def main():
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import build
    lean_path, lean = build.lean_env()
    env = {**os.environ, "LEAN_PATH": lean_path, "LEAN_NUM_THREADS": "1"}
    if sys.argv[1:] == ["library"]:
        t = library(lean, env, print)
        print(f"library {t['key'][:12]}: {len(t['decls'])} declarations in {len(t['modules'])} modules")
    elif sys.argv[1:2] == ["modules"] and sys.argv[2:]:
        known = library(lean, env, print)["decls"]
        for path, imps, entries, used in modules([str(Path(p).resolve()) for p in sys.argv[2:]], lean, env):
            fps = fingerprints(entries, known)
            ours = sorted(u for u in used if u in known)
            print(f"{path}: {len(entries)} declarations, {len(imps)} imports, uses {len(ours)} of the library's")
            known = {**known, **fps}
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
