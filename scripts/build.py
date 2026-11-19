#!/usr/bin/env python3
"""Compile a solid's modules with the shared library as compiled code, keep every compiled module,
and audit the result in Lean.

    python3 scripts/build.py Polyhedra/Platonic/Cube --jobs N [--keep DIR] [--only PART]

1. every module of the directory that a generator wrote (all but nothing: the reader's files
   too) passes the screen (`screen`: no axiom, attribute, code-running command, option but the
   linter's, `maxHeartbeats 0` and `maxRecDepth 100000`);
2. the modules are compiled in dependency order, at most `--jobs` at a time and only while the
   machine has a core and the memory the module is predicted to need (`Pool`: one account for
   every build on the machine, so several solids on one VM share its cores and none overcommits
   its memory), each by `lean --load-dynlib` (the library as compiled code,
   `scripts/native.py`), their oleans next to the library's. A compile the kernel's OOM killer
   ends is started again later with twice the memory set aside (at most the machine's). After
   each module a line `NOPERTS-PROGRESS 1 leaf DONE TOTAL` (kilobytes of source compiled, of
   those to compile) gives `burst` the pace and the ETA. With `--keep DIR` each compiled olean is kept in `DIR` with a record of what
   it was compiled from, and **a kept module stands for a compile as long as its own text and
   every declaration it uses are unchanged** (`declarations.py`: the declarations' fingerprints
   follow statements and definitions, not proofs or files). So a change recompiles exactly the
   modules that use what changed: moving a definition to another file, a new docstring or
   layout of a reader's file, a changed proof in the library or a new statement on top of a
   solid's results never costs the certificate's compile. `--replay` has Lean's kernel check
   every reused module again in today's environment (an axiom of `native_decide` is taken as it
   is: its definition is the same by the fingerprints);
3. the audit (`audit`), in Lean on the built modules: the result theorems have exactly the
   stated types; no constant of the solid's modules is unsafe, opaque, replaced by other code or
   an axiom but `native_decide`'s own; the theorems' axioms are Lean's three and `native_decide`
   axioms declared in this solid's modules.

`--only certificates` compiles the modules under `Certificates/` alone (what costs: the reader's
files and the proofs on top need them compiled; no audit then).

Environment: the Lake project here, or with `NIEUWLAND_PACKED=1` an unpacked environment
(`scripts/env.py`: `../toolchain/bin/lean`, the oleans under `.lake`, no Lake).
"""
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import declarations  # noqa: E402
import parallel  # noqa: E402

LEAN = Path(__file__).resolve().parents[1]
PACKED = bool(os.environ.get("NIEUWLAND_PACKED"))
SO = LEAN / ".lake/build/lib/libNieuwlandNative.so"
OUT = LEAN / ".lake/build/lib/lean"
LEAN_OPTS = ["-DautoImplicit=false", "-DrelaxedAutoImplicit=false", "-DmaxSynthPendingDepth=3"]
LIBS = ("Definitions", "Modules", "Polyhedra")
IMPORT = re.compile(r"^import (\S+)[ \t]*$", re.M)


def imports(text):
    return IMPORT.findall(text)


def module_of(path):
    return str(Path(path).resolve().relative_to(LEAN))[:-5].replace("/", ".")


def source_of(module):
    return LEAN / (module.replace(".", "/") + ".lean")


def lean_env():
    """`LEAN_PATH` and the `lean` binary: the Lake project's, or the packed environment's."""
    if PACKED:
        paths = [OUT] + sorted(p / ".lake/build/lib/lean" for p in (LEAN / ".lake/packages").iterdir()
                               if (p / ".lake/build/lib/lean").is_dir())
        return ":".join(map(str, paths)), str(LEAN.parent / "toolchain/bin/lean")
    p = subprocess.run(["lake", "env", "sh", "-c", 'printf "%s\\n%s" "$LEAN_PATH" "$(command -v lean)"'],
                       cwd=LEAN, capture_output=True, text=True, check=True)
    lean_path, lean = p.stdout.split("\n")
    return lean_path, lean


def digest(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


# ---------------------------------------------------------------------------------------------
# the screen of generated modules

# What a generated module may not contain (applied to the code that `strip` leaves): no attribute
# (such as `implemented_by` or `extern`, which would change what `native_decide` evaluates), no
# axiom, sorry or opaque constant, no commands that run code or change the syntax (but local
# notations), and no options but the linter's, an unlimited `maxHeartbeats` and `maxRecDepth`
# (resource bounds of elaboration; `debug.skipKernelTC` would skip the kernel).
FORBIDDEN = re.compile(r"\b(axiom|sorry|sorryAx|opaque|unsafe|partial|implemented_by|extern|"
                       r"attribute|macro|macro_rules|elab|elab_rules|syntax|infix|infixl|"
                       r"infixr|prefix|postfix|initialize|builtin_initialize|instance|deriving)\b|"
                       r"(?<!local )\bnotation\b|"
                       r"#(eval|reduce|exit|guard_msgs|print)|\brun_(cmd|elab|meta)\b")
ATTRIBUTE = re.compile(r"@\[([^\]]*)\]")
ATTRIBUTES = {"inherit_doc"}
OPTION = re.compile(r"\bset_option\s+(\S+)\s+(\S+)")
OPTIONS = {("linter.style.longLine", "false"), ("maxHeartbeats", "0"), ("maxRecDepth", "100000")}
CHAR = re.compile(r"'(\\(?:u\{[0-9a-fA-F]+\}|x[0-9a-fA-F]{2}|.)|[^\\'\n])'")


def ident_char(ch):
    return ch.isalnum() or ch in "_'!?"


def strip(text):
    """The code of a Lean module with comments removed and string and character literals emptied,
    read left to right as Lean reads it. Raises ValueError on what this reading does not follow:
    a comment inside a comment, raw or interpolated strings, escaped names `«…»`, unterminated
    literals or comments."""
    out, i, n = [], 0, len(text)
    while i < n:
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            out.append(" ")
        elif text.startswith("/-", i):
            j = text.find("-/", i + 2)
            if j < 0:
                raise ValueError("an unterminated comment")
            if "/-" in text[i + 2:j]:
                raise ValueError("a comment inside a comment")
            i = j + 2
            out.append(" ")
        elif text[i] == '"':
            if i > 0 and text[i - 1] in "r#!":
                raise ValueError("a raw or interpolated string")
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            if j >= n:
                raise ValueError("an unterminated string")
            i = j + 1
            out.append('""')
        elif text[i] == "«":
            raise ValueError("an escaped name «…», which may hold quotes")
        elif text[i] == "'" and not (i > 0 and ident_char(text[i - 1])):
            m = CHAR.match(text, i)
            if not m:
                raise ValueError("a quote that is neither in a name nor a character literal")
            i = m.end()
            out.append("' '")
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def screen(text):
    """Why the generated module `text` is refused, or None."""
    try:
        code = strip(text)
    except ValueError as e:
        return f"cannot screen: {e}"
    m = FORBIDDEN.search(code)
    if m:
        return f"forbidden in a generated module: {m.group(0)!r}"
    for a in ATTRIBUTE.finditer(code):
        if a.group(1).strip() not in ATTRIBUTES:
            return f"attribute not allowed in a generated module: @[{a.group(1)}]"
    if "@[" in ATTRIBUTE.sub("", code):
        return "an unclosed attribute in a generated module"
    for o in OPTION.finditer(code):
        if (o.group(1), o.group(2)) not in OPTIONS:
            return f"option not allowed in a generated module: {o.group(1)} {o.group(2)}"
    return None


# ---------------------------------------------------------------------------------------------
# keys and kept modules

def base_key(lean):
    """What every key starts from: the toolchain, the compile options and the dependencies'
    versions (the manifest's revisions)."""
    version = subprocess.run([lean, "--version"], capture_output=True, text=True, check=True).stdout.strip()
    man = json.loads((LEAN / "lake-manifest.json").read_text())
    revs = sorted(f"{p['name']}@{p.get('rev')}" for p in man["packages"])
    return "\0".join([version, *LEAN_OPTS, *revs])


def piece_records(mods):
    """The certificate's pieces among `mods` (module -> source path) whose source is absent:
    module -> the record of `Certificates/manifest.json` beside it (`bytes`, `sha256`, `imports`
    of the source). Such a module is never compiled: its kept olean, under the key the record's
    hash and imports give, stands for it. Exits when an absent source has no record."""
    out, manifests = {}, {}
    for m, p in mods.items():
        if p.exists():
            continue
        man = p.parent / "manifest.json"
        if man not in manifests:
            manifests[man] = ({r["file"]: r for r in json.loads(man.read_text())["pieces"]} if man.exists() else {})
        r = manifests[man].get(p.name)
        if p.parent.name != "Certificates" or not r or "imports" not in r:
            sys.exit(f"no source of {m} and no record of it in {man}")
        out[m] = r
    return out


def old_keys(sources, base, library):
    """The keys of the scheme before the declarations' fingerprints, which a kept module of
    that time has as its `key`: the module's name, its source and the keys of its imports, down
    to the library's sources. `sources`: module -> (SHA-256 of its text then, its imports);
    `library`: the keys of the library's modules then (a library's description). A module whose
    text of that time is not known has no key."""
    keys = {}

    def key(m, above=()):
        if m in above or m not in sources:
            return None
        if m not in keys:
            sha, deps = sources[m]
            parts = [base, m, sha]
            for d in sorted(deps):
                if d.split(".")[0] not in LIBS:
                    parts.append(d)
                    continue
                k = library.get(d) or key(d, (*above, m))
                if k is None:
                    keys[m] = None
                    return None
                parts.append(f"{d}={k}")
            keys[m] = hashlib.sha256("\0".join(parts).encode()).hexdigest()
        return keys[m]

    return {m: key(m) for m in sources}


def kept_record(keep, m):
    """The record of the kept module `m` when the olean beside it is the record's, or None."""
    try:
        rec = json.loads((keep / f"{m}.json").read_text())
        olean = keep / f"{m}.olean"
        if rec["module"] == m and olean.stat().st_size == rec["bytes"] and digest(olean) == rec["sha256"]:
            return rec
    except (OSError, ValueError, TypeError, AttributeError, KeyError):
        pass
    return None


def stands(rec, source, base, table, library_modules, mods):
    """Why the kept module of the record `rec` does not stand for a compile now, or None when it
    does: it was compiled from the text `source` (its SHA-256) with today's toolchain and
    Mathlib (`base`), the modules it imports are there, and every declaration it uses has the
    fingerprint of that day in `table` (the library's declarations and those of the solid's
    modules settled before it)."""
    if not rec or rec.get("format") != 2:
        return "no kept module" if not rec else "a kept module of the old scheme (--migrate)"
    if rec["base"] != base:
        return "the toolchain, the options or Mathlib changed"
    if rec["source"] != source:
        return "its text changed"
    for i in rec["imports"]:
        if i.split(".")[0] in LIBS and i not in library_modules and i not in mods:
            return f"the imported module {i} is gone"
    for name, fp in rec["uses"].items():
        if table.get(name) != fp:
            return f"`{name}` {'changed' if name in table else 'is gone'}"
    return None


def kept_save(keep, m, olean, fields):
    """Keep module `m`'s compiled olean with its record (`fields`: what it was compiled from,
    its declarations and what it uses): the old record goes first and the new one is written
    last, each file by rename, so a copy of `keep` taken at any moment holds no record of an
    olean other than the one beside it (and one torn between the two is refused by its digest).
    `olean` may be the kept olean itself (a record of the old scheme, rewritten)."""
    keep.mkdir(parents=True, exist_ok=True)
    rec, dst = keep / f"{m}.json", keep / f"{m}.olean"
    if Path(olean).resolve() != dst.resolve():
        rec.unlink(missing_ok=True)
        tmp = keep / f"{m}.olean.tmp"
        shutil.copyfile(olean, tmp)
        os.replace(tmp, dst)
    tmp = keep / f"{m}.json.tmp"
    tmp.write_text(json.dumps({"format": 2, "module": m, "sha256": digest(dst), "bytes": dst.stat().st_size, **fields}))
    os.replace(tmp, rec)


def described(info, table):
    """What a record says of a compiled module's declarations (`info`, of
    `declarations.modules`): their fingerprints, and the fingerprints in `table` of the
    declarations of this project that the module uses. `table` gets the module's own."""
    _, imps, entries, used = info
    fps = declarations.fingerprints(entries, table)
    uses = {u: table[u] for u in sorted(used) if u in table and u not in entries}
    table.update(fps)
    return {"imports": imps, "decls": fps, "uses": uses}


def migrate(keep, mods, src, old, prev, directory, jobs, lean, env, log):
    """Rewrite the kept modules of the old scheme as records of declarations. `old` is the
    description of the library they were compiled with (its modules' keys of the old scheme and
    its declarations' fingerprints); `prev` holds the solid's files of that time. A kept module
    is rewritten when its old key is the key its text of that time and that library give, and
    the modules of the solid it imports are rewritten too: its declarations and what it uses are
    read from its olean and written with that library's fingerprints. Whether it stands today
    is then the ordinary question."""
    raw = base_key(lean)
    if old["base"] != hashlib.sha256(raw.encode()).hexdigest():
        log("  kept modules of the old scheme: not rewritten (the toolchain, the options or Mathlib changed)")
        return
    then = {}
    for m, p in mods.items():
        q = prev / p.resolve().relative_to(directory) if prev else None
        if q is not None and q.suffix == ".lean" and q.exists():
            text = q.read_bytes()
            then[m] = (hashlib.sha256(text).hexdigest(), imports(text.decode()))
        elif ".Certificates." in m:
            then[m] = src[m]  # a piece: the manifest's record, which is of that time
    keys, recs = old_keys(then, raw, old["source_keys"]), {}
    for m in mods:
        rec = kept_record(keep, m)
        if rec and (rec.get("library") == old["library"] if rec.get("format") == 2 else rec.get("key") == keys.get(m, 0)):
            recs[m] = rec
    todo = [m for m in recs if recs[m].get("format") != 2]
    if not todo:
        return
    t0 = time.time()
    chunks = [[] for _ in range(max(1, min(jobs, len(todo))))]
    for n, m in enumerate(sorted(todo, key=lambda m: -recs[m]["bytes"])):
        chunks[n % len(chunks)].append(m)
    with ThreadPoolExecutor(len(chunks)) as ex:
        infos = [i for part in ex.map(lambda c: list(declarations.modules([keep / f"{m}.olean" for m in c], lean, env)), chunks)
                 for i in part]
    infos = {Path(i[0]).name[:-len(".olean")]: i for i in infos}
    need = {m: {d for d in (then[m][1] if m in then else recs[m]["imports"]) if d in mods} for m in recs}
    table, settled, left = dict(old["decls"]), set(), set(recs)
    while ready := sorted(m for m in left if need[m] <= settled):
        for m in ready:
            left.discard(m)
            settled.add(m)
            if recs[m].get("format") == 2:
                table.update(recs[m]["decls"])
            else:
                kept_save(keep, m, keep / f"{m}.olean",
                          {"base": old["base"], "source": then[m][0], "library": old["library"], **described(infos[m], table)})
    log(f"  kept modules of the old scheme: {len([m for m in todo if m in settled])} of {len(todo)} rewritten as records of "
        f"declarations ({time.time() - t0:.0f} s)")


class Pool:
    """The compile slots of this machine, shared by every build on it (several solids on one VM):
    a compile starts while fewer compiles than cores run and the memory predicted for the running
    ones and the new one fits in the machine's, less `RESERVE_MB` for everything else. The account
    is a file in /dev/shm under a lock; an entry whose process is gone is dropped."""
    PATH, LOCK, RESERVE_MB = Path("/dev/shm/nieuwland-pool.json"), Path("/dev/shm/nieuwland-pool.lock"), 2500

    def __init__(self):
        self.cores = os.cpu_count() or 1
        self.mem_mb = Pool.meminfo("MemTotal") - Pool.RESERVE_MB
        self.n = 0

    @staticmethod
    def meminfo(field):
        for line in open("/proc/meminfo"):
            if line.startswith(field + ":"):
                return int(line.split()[1]) // 1024
        raise RuntimeError(f"no {field} in /proc/meminfo")

    def _edit(self, f):
        import fcntl
        with open(Pool.LOCK, "a") as lk:
            fcntl.flock(lk, fcntl.LOCK_EX)
            try:
                held = json.loads(Pool.PATH.read_text()) if Pool.PATH.exists() else {}
            except ValueError:
                held = {}
            alive = {}
            for k, (pid, mb) in held.items():
                try:
                    os.kill(pid, 0)
                    alive[k] = (pid, mb)
                except ProcessLookupError:
                    pass
                except PermissionError:
                    alive[k] = (pid, mb)
            out = f(alive)
            tmp = Pool.PATH.with_suffix(f".{os.getpid()}")
            tmp.write_text(json.dumps(alive))
            os.replace(tmp, Pool.PATH)
            return out

    def take(self, mb):
        """A slot for a compile predicted to need `mb` MB, or None now. One compile always fits
        an empty machine (its memory is then at most the machine's)."""
        def f(held):
            used = sum(x[1] for x in held.values())
            if held and (len(held) >= self.cores or used + mb > self.mem_mb):
                return None
            self.n += 1
            key = f"{os.getpid()}-{self.n}"
            held[key] = (os.getpid(), mb)
            return key
        return self._edit(f)

    def give(self, key):
        self._edit(lambda held: held.pop(key, None))


NEED_MB = 3400  # a compile's memory when nothing better is known (the certificates' pieces, measured)


def olean_of(m):
    return OUT / (m.replace(".", "/") + ".olean")


def compile_modules(mods, jobs, keep=None, log=print, replay=False, old=None, prev=None, directory=None):
    """Compile `mods` (module -> source path) in dependency order, `jobs` at a time; a module
    whose kept one in `keep` stands (`stands`) is not compiled. Returns the `lean` binary, its
    environment and the modules reused from `keep`. Exits on the first failure (what was
    compiled before it is kept). `old`, `prev`, `directory`: `migrate`. `replay`: the kernel
    checks the reused modules again."""
    if not SO.exists():
        sys.exit(f"no compiled library at {SO} (scripts/native.py)")
    lean_path, lean = lean_env()
    env = {**os.environ, "LEAN_PATH": lean_path, "LEAN_NUM_THREADS": "1"}
    records = piece_records(mods)
    src = {}
    for m, p in mods.items():
        if m in records:
            src[m] = (records[m]["sha256"], records[m]["imports"])
        else:
            text = p.read_bytes()
            src[m] = (hashlib.sha256(text).hexdigest(), imports(text.decode()))
    deps = {m: {d for d in src[m][1] if d in mods} for m in mods}
    base = hashlib.sha256(base_key(lean).encode()).hexdigest()
    lib = declarations.library(lean, env, log)
    table, library_modules = dict(lib["decls"]), set(lib["modules"])
    if keep is not None and old is not None:
        migrate(keep, mods, src, old, prev, directory, jobs, lean, env, log)
    done, reused, running, why, t0 = set(), set(), {}, {}, time.time()
    pool, need, killed = Pool(), {m: NEED_MB for m in mods}, {}

    def build(m, slot):
        try:
            o = olean_of(m)
            o.parent.mkdir(parents=True, exist_ok=True)
            s = time.time()
            r = subprocess.run([lean, *LEAN_OPTS, f"--root={LEAN}", f"--load-dynlib={SO}", "-o", str(o), str(mods[m])],
                               cwd=LEAN, env=env, capture_output=True, text=True)
            secs = time.time() - s
        finally:
            pool.give(slot)
        info = next(declarations.modules([o], lean, env)) if r.returncode == 0 else None
        return m, r, secs, info

    # the small modules first (cheap mistakes show before the long checks), then the largest first
    # (a long compile started last is a long tail)
    size = {m: records[m]["bytes"] if m in records else mods[m].stat().st_size for m in mods}
    order = sorted(mods, key=lambda m: (size[m] >= 100_000, -size[m], m))
    compiled = 0

    def progress():
        total = sum(size[m] for m in mods if m not in reused)
        print(f"NOPERTS-PROGRESS 1 leaf {min(compiled, total) // 1000} {max(total // 1000, 1)} modules={len(done)}/{len(mods)} "
              f"running={len(running)}", flush=True)

    with ThreadPoolExecutor(jobs) as ex:
        while len(done) < len(mods):
            settled = True
            while settled and keep is not None:  # the kept modules that stand, as their imports settle
                settled = False
                for m in order:
                    if m not in done and m not in why and deps[m] <= done:
                        rec = kept_record(keep, m)
                        why[m] = stands(rec, src[m][0], base, table, library_modules, mods)
                        if why[m] is None:
                            del why[m]
                            olean_of(m).parent.mkdir(parents=True, exist_ok=True)
                            shutil.copyfile(keep / f"{m}.olean", olean_of(m))
                            table.update(rec["decls"])
                            done.add(m)
                            reused.add(m)
                            settled = True
            if keep is None and (lost := sorted(m for m in records if not mods[m].exists())):
                sys.exit(f"{len(lost)} pieces have no source here (first: {lost[0]}) and no kept modules were given (--keep)")
            if lost := sorted(m for m in why if m in records):
                sys.exit(f"{len(lost)} pieces have no source here and no kept module that stands (first: {lost[0]}: "
                         f"{why[lost[0]]}); build from the certificate's sources")
            ready = [m for m in order if m not in done and m not in running.values() and deps[m] <= done]
            for m in ready:
                if len(running) >= jobs:
                    break
                slot = pool.take(need[m])
                if slot is None:
                    break  # the machine is full: wait for a compile here or elsewhere to end
                running[ex.submit(build, m, slot)] = m
            if not running:
                if not ready:
                    sys.exit("the modules' imports have a cycle")
                time.sleep(5)  # every slot is held by other builds on this machine
                continue
            fin, _ = wait(running, timeout=5 if ready else None, return_when=FIRST_COMPLETED)
            for f in fin:
                m, r, secs, info = f.result()
                del running[f]
                if r.returncode in (-9, 137) and killed.get(m, 0) < 3 and need[m] < pool.mem_mb:
                    # killed (by the kernel's OOM killer, as a rule): again later, with more memory set aside
                    killed[m] = killed.get(m, 0) + 1
                    need[m] = min(2 * need[m], pool.mem_mb)
                    log(f"  {m} was killed after {secs:.0f} s (exit {r.returncode}); again with {need[m]} MB set aside")
                    continue
                if r.returncode != 0:
                    # a negative code is a signal (-9: killed, as by the kernel's OOM killer)
                    errs = re.findall(r"^\S+:\d+:\d+: error.*(?:\n(?!\S+:\d+:\d+: ).*)*", r.stdout, re.M)
                    first = "".join(f"{e[:600]}\n" for e in errs[:3])
                    sys.exit(f"{m} failed (exit {r.returncode}; {len(errs)} errors):\n{first}{r.stdout[-2000:]}{r.stderr[-2000:]}")
                fields = {"base": base, "source": src[m][0], "library": lib["key"], **described(info, table)}
                if keep is not None:
                    kept_save(keep, m, olean_of(m), fields)
                done.add(m)
                compiled += size[m]
                log(f"  [{len(done)}/{len(mods)}] {m} ({secs:.0f} s; {time.time() - t0:.0f} s in all"
                    + (f"; its kept module did not stand: {why[m]}" if why.get(m, "no kept module") != "no kept module" else "") + ")")
                progress()
    if keep is not None:
        log(f"  kept modules in {keep}: {len(reused)} of {len(mods)} reused")
    if replay and reused:
        s = time.time()
        n, ax = replay_modules(mods, deps, reused, lean, env, jobs)
        log(f"  the kernel checked the {n} declarations of the reused modules and the modules they import again "
            f"({ax} axioms of native_decide taken as they are; {time.time() - s:.0f} s)")
    return lean, env, frozenset(reused)


# Each line of LIST is a compiled module of the solid: its name and its olean, a module after
# the modules it imports. Their imports from outside the list give the environment; then every
# declaration of every module goes to the kernel again, in that order.
REPLAY = """import Lean
import Lean.Replay
open Lean

unsafe def run (list : String) : IO Unit := do
  let mut data : Array (Name × ModuleData) := #[]
  let mut own : Std.HashSet Name := {}
  for l in (← IO.FS.lines list) do
    let [n, p] := l.splitOn "\t" | throw (IO.userError s!"a line of the list: {l}")
    own := own.insert n.toName
    data := data.push (n.toName, (← readModuleData p).1)
  let mut imps : Array Import := #[]
  for (_, mod) in data do
    for i in mod.imports do
      unless own.contains i.module || imps.any (·.module == i.module) do imps := imps.push i
  let env ← importModules imps {} 0
  let mut kenv := env.toKernelEnv
  let mut n := 0
  let mut ax := 0
  for (name, mod) in data do
    let mut consts : Std.HashMap Name ConstantInfo := {}
    for c in mod.constNames, ci in mod.constants do
      if kenv.find? c |>.isSome then throw (IO.userError s!"{name}: {c} is declared before it")
      consts := consts.insert c ci
      if ci matches .axiomInfo _ then ax := ax + 1
    kenv ← kenv.replay consts
    -- (the kernel is not given an unsafe constant or the compiled twin of a recursive definition)
    for c in mod.constNames, ci in mod.constants do
      unless (kenv.find? c |>.isSome) || ci.isUnsafe || ci.isPartial do
        throw (IO.userError s!"{name}: {c} was not checked")
    n := n + consts.size
  IO.println s!"REPLAY-OK {n} {ax}"

#eval run "LIST"
"""


def replay_modules(mods, deps, reused, lean, env, jobs):
    """Lean's kernel checks the `reused` modules again, in the environment of today's library:
    every declaration of their oleans, and of the solid's modules they import (in whose
    declarations theirs are stated). Returns the numbers of declarations and of axioms (taken
    as they are). Exits on a failure.

    In up to `jobs` processes at once (slots of the machine's `Pool`): the modules in dependency
    order are cut into consecutive slices, and a slice's modules are checked in the environment
    of their imports from outside the slice, read from their oleans. Those are today's library
    and modules of the solid before the slice, which are checked in their own slices; nothing
    outside a slice imports a module of it, since every import comes earlier in the order. So
    every declaration is checked once, against what its module imports, as Lean checks a module
    against its imports' oleans; the counts are the slices' sums, those of one process."""
    todo, stack = set(), list(reused)
    while stack:
        m = stack.pop()
        if m not in todo:
            todo.add(m)
            stack.extend(deps[m])
    order, placed = [], set()
    while len(order) < len(todo):
        for m in sorted(todo - placed):
            if deps[m] <= placed:
                order.append(m)
                placed.add(m)
    pool = Pool()

    def check(i, part):
        while (slot := pool.take(NEED_MB)) is None:
            time.sleep(5)  # the machine is full
        lst = LEAN / f".lake/replay-{os.getpid()}-{i}.list"
        try:
            lst.write_text("".join(f"{m}\t{olean_of(m)}\n" for m in part))
            out = lean_output(REPLAY.replace("LIST", str(lst)), lean, env, tag=f"{os.getpid()}-{i}")
        finally:
            lst.unlink(missing_ok=True)
            pool.give(slot)
        m = re.search(r"REPLAY-OK (\d+) (\d+)", out)
        if not m:
            sys.exit(f"replay: {out[-800:]}")
        return int(m.group(1)), int(m.group(2))
    parts = slices(order, {m: olean_of(m).stat().st_size for m in order}, min(len(order), REPLAY_SLICES * jobs))
    with ThreadPoolExecutor(max(1, jobs)) as ex:
        done = list(ex.map(check, range(len(parts)), parts))
    return sum(n for n, _ in done), sum(ax for _, ax in done)


# slices per process: a slice whose modules take long (a pose's kernel `decide`s, hours for the rhombic
# triacontahedron) leaves the other slices to the other processes; each slice costs a process's
# imports (5 s), so few
REPLAY_SLICES = 2


def slices(order, weight, n):
    """`order` cut into `n` consecutive nonempty slices (`n` at most its length), each about an
    equal share of the weight left after the slices before it."""
    total, parts, before, acc = sum(weight[m] for m in order), [[]], 0, 0
    for i, m in enumerate(order):
        left = n - len(parts)  # the slices still to open
        if parts[-1] and left > 0 and (acc >= (total - before) / (left + 1) or len(order) - i <= left):
            parts.append([])
            before, acc = before + acc, 0
        parts[-1].append(m)
        acc += weight[m]
    return parts


# ---------------------------------------------------------------------------------------------
# the audit

AUDIT = """open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods : Array Name := #[{mods}]
  let idx : Std.HashSet ModuleIdx := mods.foldl (fun s m => match env.getModuleIdx? m with
    | some i => s.insert i | none => s) {{}}
  unless idx.size == mods.size do throwError "a module of the solid is not imported"
  let mut n := 0
  let mut bad := #[]
  for (c, j) in env.const2ModIdx.toList do
    if idx.contains j then
      let some ci := env.find? c | continue
      n := n + 1
      let nativeAx := (c.toString.splitOn "._native.native_decide.ax_").length == 2
      if ci.isUnsafe || (Compiler.implementedByAttr.getParam? env c).isSome || isExtern env c
          || ci matches .opaqueInfo _ || (ci matches .axiomInfo _ && !nativeAx) then
        bad := bad.push c
  unless bad.isEmpty do throwError "refused constants: {{bad}}"
  logInfo m!"AUDIT-OK {{n}} constants in {{mods.size}} modules"
  let kernel : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut native : Std.HashSet Name := {{}}
  for t in ([{thms}] : List Name) do
    unless (env.find? t).isSome do throwError "no theorem {{t}}"
    for a in (← Lean.collectAxioms t) do
      if kernel.contains a then continue
      let nativeAx := (a.toString.splitOn "._native.native_decide.ax_").length == 2
      let here := match env.getModuleIdxFor? a with
        | some j => idx.contains j
        | none => false
      unless nativeAx && here do throwError "{{t}} depends on the axiom {{a}}"
      native := native.insert a
  logInfo m!"AXIOMS-OK {{native.size}} native_decide axioms"
"""


def lean_output(text, lean, env, tag=None):
    """What `lean` prints for the module `text` (compiled against the built modules); exits on
    an error. `tag` names its file, for several at once."""
    tmp = LEAN / f".audit-{tag or os.getpid()}.lean"
    tmp.write_text(text)
    try:
        r = subprocess.run([lean, *LEAN_OPTS, f"--root={LEAN}", f"--load-dynlib={SO}", str(tmp)],
                           cwd=LEAN, env=env, capture_output=True, text=True)
    finally:
        tmp.unlink(missing_ok=True)
    if r.returncode != 0:
        sys.exit(f"lean failed on a check of the built modules:\n{r.stdout[-3000:]}{r.stderr[-2000:]}")
    return r.stdout


# the theorem's type as an expression, compared with the statement elaborated from its source
# (no notation or coercion of the theorem's file can change what is compared); as a theorem's
# header, the statement's nondependent `let`s become `have`s (`Meta.letToHave`, which Lean applies
# to every declaration's type; a list literal of 33 or more elements is a chain of `let`s)
AUDIT_TYPE = """open Lean Elab Command Term in
#eval show CommandElabM Unit from do
  let want ← liftTermElabM do
    let e ← elabType (← `({ty}))
    synthesizeSyntheticMVarsNoPostponing
    Meta.letToHave (← instantiateMVars e)
  let some c := (← getEnv).find? `{thm} | throwError "no {thm}"
  unless c.type == want do throwError "the type of {thm} is {{c.type}}, not {{want}}"
  logInfo "TYPE-OK {thm}"
"""


def audit(top, mods, statements, lean, env):
    """Check in Lean, on the built modules (`top` imported): each of `statements` (a theorem's
    name and the type it must have, as Lean source with full names) has exactly that type; the
    constants of `mods`; the axioms of the theorems. Returns the numbers of `native_decide`
    axioms and of constants."""
    text = (f"import {top}\n"
            + AUDIT.format(mods=", ".join(f"`{m}" for m in sorted(mods)), thms=", ".join(f"`{t}" for t, _ in statements))
            + "".join(AUDIT_TYPE.format(thm=t, ty=ty) for t, ty in statements))
    out = lean_output(text, lean, env)
    m = re.search(r"AXIOMS-OK (\d+) native_decide axioms", out)
    if "AUDIT-OK" not in out or not m or any(f"TYPE-OK {t}" not in out for t, _ in statements):
        sys.exit(f"audit: {out[-600:]}")
    return int(m.group(1)), re.search(r"AUDIT-OK (\d+) constants", out).group(1)


def solid_modules(directory, only=None):
    """The modules of a solid's directory (module -> source path): its Lean files and the pieces
    of `Certificates/manifest.json`, whose sources may be absent (`piece_records`)."""
    d = (LEAN / directory).resolve()
    mods = {module_of(p): p for p in sorted(d.rglob("*.lean"))}
    man = d / "Certificates/manifest.json"
    if man.exists():
        for r in json.loads(man.read_text())["pieces"]:
            mods.setdefault(module_of(man.parent / r["file"]), man.parent / r["file"])
    if only == "certificates":
        mods = {m: p for m, p in mods.items() if ".Certificates." in m}
    return mods


def screen_file(p):
    return screen(p.read_text())


def screen_all(mods):
    """Screen the sources present; returns the megabytes of all sources (absent pieces by their
    records). A piece without its source was screened when its kept module was compiled; the
    audit, which reads the compiled modules, covers it as every other."""
    records = piece_records(mods)
    present = [(m, p) for m, p in mods.items() if m not in records]
    # on all cores, in order: the first refused module is the serial loop's
    for (m, _), why in zip(present, parallel.ordered_map(screen_file, [p for _, p in present])):
        if why:
            sys.exit(f"screen: {m}: {why}")
    return sum(records[m]["bytes"] if m in records else p.stat().st_size for m, p in mods.items()) / 1e6


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("directory", help="a solid's directory, as Polyhedra/Platonic/Cube")
    ap.add_argument("--jobs", type=int, required=True)
    ap.add_argument("--keep", type=Path)
    ap.add_argument("--only", choices=["certificates"])
    ap.add_argument("--replay", action="store_true", help="the kernel checks the reused modules again")
    ap.add_argument("--migrate", type=Path, help="the description of the library that kept modules of the old scheme were compiled with")
    ap.add_argument("--prev", type=Path, help="with --migrate: the solid's directory of that time")
    a = ap.parse_args()
    mods = solid_modules(a.directory, a.only)
    if not mods:
        sys.exit(f"no modules under {a.directory}")
    size = screen_all(mods)
    t0 = time.time()
    lean, env, reused = compile_modules(mods, a.jobs, a.keep, log=lambda s: print(s, flush=True), replay=a.replay,
                                        old=json.loads(a.migrate.read_text()) if a.migrate else None, prev=a.prev,
                                        directory=(LEAN / a.directory).resolve())
    line = f"{len(mods)} modules, {size:.1f} MB, compiled in {time.time() - t0:.0f} s ({len(reused)} kept)"
    spec = (LEAN / a.directory / "statements.json")
    if a.only is None and spec.exists():
        st = json.loads(spec.read_text())
        native, consts = audit(st["top"], mods, [(s["name"], s["type"]) for s in st["statements"]], lean, env)
        line += f"; audit: {len(st['statements'])} statements, {consts} constants, axioms: Lean's three and {native} native_decide axioms of the solid's modules"
    print(f"ok: {a.directory}: {line}", flush=True)


if __name__ == "__main__":
    main()
