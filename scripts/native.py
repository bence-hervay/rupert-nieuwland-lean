#!/usr/bin/env python3
"""Compile the shared library (`Definitions`, `Modules`) into one shared library that
`lean --load-dynlib` loads, so that `native_decide` in a solid's modules runs the checkers as
compiled code instead of in Lean's interpreter.

    python3 scripts/native.py [--out PATH] [--jobs N]

What it compiles: the C that Lean emitted for every module of `Definitions` and `Modules`
(`.lake/build/ir`), except those no check runs (`UNCOMPILED`), and the dependency C files
(Mathlib, Batteries, …, shipped with their caches) that define a symbol the compiled code reaches,
closed under that relation. Module initializers of dependencies left out get hidden stubs: `lean`
runs the initializer of an imported module only if it finds it exported (`runModInit`), so those
modules are still initialized by the interpreter as without the library.

Consistency: the C and the olean of each library module must come from the same Lake build step
(their hashes in the module's trace), or nothing is built: the compiled code must be the code of
the definitions the kernel checked. Trust: Lean's C backend and the toolchain's clang, as for any
compiled Lean program, besides the compiler and interpreter `native_decide` trusts.
"""
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

LEAN = Path(__file__).resolve().parents[1]
BUILD = LEAN / ".lake/build"
# statement-layer modules whose definitions no compiled check runs (the kernel and the
# elaborator unfold them): left out of the compiled code
UNCOMPILED = {"Modules/Pose/Optimum",
              "Modules/Check/Number/ThetaRoot",
              "Modules/System/Enclose",
              "Modules/Pose/PoseCheck",
              "Modules/Pose/PoseContact",
              "Modules/Pose/PoseRoot",
              "Modules/Root/Chain",
              "Modules/Root/ExLink",
              "Modules/Root/Link",
              "Modules/Root/LinkCheck",
              "Modules/Root/LinkData",
              "Modules/Root/LinkMap",
              "Modules/Root/OneRoot",
              "Modules/Root/PoseMap",
              "Modules/Root/Reps",
              "Modules/System/OneRoot",
              "Modules/System/PolyAux",
              "Modules/System/PolyMax",
              "Modules/System/PolyMaxOf",
              "Modules/System/PolyRoot",
              "Modules/System/PolyRootEq",
              "Modules/System/PolyRootOf",
              "Modules/System/Readable",
              "Modules/System/Single"}


def toolchain():
    tc = (LEAN / "lean-toolchain").read_text().strip().replace("/", "--").replace(":", "---")
    return Path.home() / ".elan/toolchains" / tc


def library_modules():
    """The library's modules (paths without `.lean`): what a solid's modules may import."""
    return [str(f.relative_to(LEAN))[:-5] for d in ("Definitions", "Modules") for f in sorted((LEAN / d).rglob("*.lean"))]


def check_trace(m):
    """Why the C and the olean of the module `m` may not come from one build step, or None."""
    tr = BUILD / f"lib/lean/{m}.trace"
    if not tr.exists():
        return f"{m}: no trace (not built by Lake)"
    outs = json.loads(tr.read_text()).get("outputs", {})
    c = (BUILD / f"ir/{m}.c.hash")
    o = (BUILD / f"lib/lean/{m}.olean.hash")
    if not c.exists() or not o.exists() or not (BUILD / f"ir/{m}.c").exists():
        return f"{m}: no C or olean hash"
    want_c = outs.get("c", "").split(".")[0]
    want_o = (outs.get("o") or [""])[0].split(".")[0]
    if c.read_text().strip() != want_c or o.read_text().strip() != want_o:
        return f"{m}: C or olean not from the traced build step"
    return None


def exported_symbols():
    """Symbol -> dependency C file defining it (exported definitions)."""
    index = {}
    pat = re.compile(r"^LEAN_EXPORT [A-Za-z_0-9* ]+ (lp?_\w+|initialize_\w+|runtime_initialize_\w+)",
                     re.M)
    for d in sorted((LEAN / ".lake/packages").glob("*/.lake/build/ir")):
        for f in d.rglob("*.c"):
            for s in pat.findall(f.read_text(errors="replace")):
                index.setdefault(s, f)
    return index


def nm(o, flag):
    out = subprocess.run(["nm", flag, str(o)], capture_output=True, text=True, check=True).stdout
    return {l.split()[-1] for l in out.splitlines() if l.strip()}


def dyn_symbols(so, flag):
    out = subprocess.run(["nm", "-D", flag, str(so)], capture_output=True, text=True, check=True).stdout
    return {l.split()[-1] for l in out.splitlines() if l.strip()}


def build(out, jobs):
    if shutil.which("nm") is None:
        sys.exit("native.py needs `nm` to list symbols: install binutils (e.g. `apt install binutils`)")
    tc = toolchain()
    leanc = tc / "bin/leanc"
    mods = [m for m in library_modules() if m not in UNCOMPILED]
    bad = [w for m in mods if (w := check_trace(m))]
    if bad:
        sys.exit("not built consistently (run `lake build Definitions Modules`):\n" + "\n".join(bad[:10]))
    core = set()  # the toolchain's shared libraries (`lean` itself)
    for so in (tc / "lib/lean").glob("*.so"):
        core |= dyn_symbols(so, "--defined-only")
    index = exported_symbols()
    cache = BUILD / "native"
    cache.mkdir(parents=True, exist_ok=True)

    def compile_c(c):
        h = hashlib.sha256(c.read_bytes()).hexdigest()[:20]
        o = cache / f"{h}.o"
        if not o.exists():
            tmp = cache / f"{h}.{os.getpid()}.tmp.o"
            subprocess.run([str(leanc), "-c", "-O3", "-fPIC", "-DLEAN_EXPORTING", str(c), "-o", str(tmp)],
                           check=True)
            tmp.rename(o)
        return o

    todo = [BUILD / f"ir/{m}.c" for m in mods]
    done, objs, defined, undef = set(), {}, set(), set()
    while todo:
        with ThreadPoolExecutor(jobs) as ex:
            for c, o in zip(todo, ex.map(compile_c, todo)):
                done.add(c)
                objs[c] = o
                defined |= nm(o, "--defined-only")
                undef |= nm(o, "--undefined-only")
        init = ("initialize_", "runtime_initialize_")
        miss = {s for s in undef - defined - core if not s.startswith(init) and "@" not in s
                and not s.startswith("__")}
        unknown = sorted(s for s in miss if s not in index)
        if unknown:
            sys.exit(f"symbols defined nowhere: {unknown[:10]}")
        todo = sorted({index[s] for s in miss} - done)
    stubs = sorted(s for s in undef - defined - core if s.startswith(init))
    sc = cache / "stubs.c"
    sc.write_text('#include <lean/lean.h>\n' + "".join(
        f'__attribute__((visibility("hidden"))) lean_object* {s}(uint8_t b) '
        '{ return lean_io_result_mk_ok(lean_box(0)); }\n' for s in stubs))
    so = cache / "stubs.o"
    subprocess.run([str(leanc), "-c", "-O2", "-fPIC", str(sc), "-o", str(so)], check=True)
    out.parent.mkdir(parents=True, exist_ok=True)
    tmp = out.with_suffix(".tmp.so")
    subprocess.run([str(leanc), "-shared", "-o", str(tmp), str(so)] + [str(objs[c]) for c in sorted(done)],
                   check=True)
    left = [s for s in dyn_symbols(tmp, "--undefined-only") - core if "@" not in s
            and not s.startswith("__")]
    if left:
        sys.exit(f"unresolved after linking: {left[:10]}")
    tmp.rename(out)
    man = {"toolchain": tc.name, "modules": len(mods), "files": len(done), "stubs": len(stubs),
           "c": {str(c.relative_to(LEAN)): hashlib.sha256(c.read_bytes()).hexdigest() for c in sorted(done)}}
    Path(str(out) + ".json").write_text(json.dumps(man, indent=1) + "\n")
    print(f"{out}: {len(mods)} library modules, {len(done)} C files, {len(stubs)} initializer stubs, "
          f"{out.stat().st_size / 2**20:.1f} MiB")
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--out", type=Path, default=BUILD / "lib/libNieuwlandNative.so")
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 1)
    ap.add_argument("--list", action="store_true", help="print the library's modules, one per line, and stop")
    a = ap.parse_args()
    if a.list:
        print("\n".join(m.replace("/", ".") for m in library_modules()))
        return
    build(a.out, a.jobs)


if __name__ == "__main__":
    main()
