#!/usr/bin/env python3
"""Check solids from a checkout of this repository: the library once, then for each solid its
certificate's pieces, the compile of all its modules and the audit of its theorems.

    python3 scripts/check.py SOLID... --jobs N [--source SRC] [--clean]

SOLID: a solid's directory (`Polyhedra/Platonic/Cube`), a family (`Johnson`) or `all`. Solids run
cheapest first (the compile times in `results.tsv`).

1. Once: Mathlib's compiled cache (`lake exe cache get`), `lake build Definitions Modules`, and
   the library as compiled code for `native_decide` (`scripts/native.py`, if not built yet).
2. For each solid: its pieces from the release (`scripts/certificates.py fetch`; `--source`:
   from a directory or URL instead), checked against `Certificates/manifest.json`; then
   `scripts/build.py`: the screen of the generated modules, their compile and the audit, which
   ends in a line `ok: …`. With `--clean` a solid that passed has its pieces and its compiled
   modules deleted again (to keep the disk small when checking many).

Each solid's line, `ok: …` or `FAILED: …`, is appended to `checks.tsv` with the time.
"""
import argparse
import csv
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import certificates  # noqa: E402

ROOT = certificates.ROOT
SO = ROOT / ".lake/build/lib/libNieuwlandNative.so"


def run(cmd):
    print("$ " + " ".join(cmd), flush=True)
    subprocess.run(cmd, cwd=ROOT, check=True)


def library(jobs):
    run(["lake", "exe", "cache", "get"])
    run(["lake", "build", "Definitions", "Modules"])
    if not SO.exists():
        run([sys.executable, "scripts/native.py", "--jobs", str(jobs)])


def order(ds):
    """Cheapest first by the recorded compile time; unknown ones last."""
    t = {r["directory"]: int(r["compile_s"]) for r in csv.DictReader(open(ROOT / "results.tsv"), delimiter="\t")}
    return sorted(ds, key=lambda d: t.get(str(d.relative_to(ROOT)), 10 ** 9))


def clean(d):
    for f in (d / "Certificates").glob("*.lean"):
        f.unlink()
    built = ROOT / ".lake/build/lib/lean" / d.relative_to(ROOT)
    for f in sorted(built.rglob("*")) if built.exists() else []:
        if f.is_file():
            f.unlink()


def check(d, jobs, source):
    rel = str(d.relative_to(ROOT))
    try:
        print(certificates.fetch(d, source), flush=True)
    except Exception as e:  # noqa: BLE001 (a failed fetch is this solid's result)
        return f"FAILED: {rel}: certificate: {e}"
    p = subprocess.Popen([sys.executable, "scripts/build.py", rel, "--jobs", str(jobs)], cwd=ROOT,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    last = ""
    for line in p.stdout:
        print("  " + line, end="", flush=True)
        if line.strip():
            last = line.strip()
    if p.wait() == 0 and last.startswith(f"ok: {rel}:"):
        return last
    return f"FAILED: {rel}: {last}"


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("solids", nargs="+")
    ap.add_argument("--jobs", type=int, required=True, help="modules compiled at a time")
    ap.add_argument("--source", help="a directory or URL holding the archives (default: the release)")
    ap.add_argument("--clean", action="store_true", help="delete a passed solid's pieces and compiled modules")
    a = ap.parse_args()
    ds = order(certificates.solids(a.solids))
    library(a.jobs)
    failed = 0
    for i, d in enumerate(ds, 1):
        print(f"[{i}/{len(ds)}] {d.relative_to(ROOT)}", flush=True)
        t0 = time.time()
        line = check(d, a.jobs, a.source)
        failed += line.startswith("FAILED")
        with open(ROOT / "checks.tsv", "a") as fh:
            fh.write(f"{time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}\t{time.time() - t0:.0f}\t{line}\n")
        print(line, flush=True)
        if a.clean and not line.startswith("FAILED"):
            clean(d)
    print(f"{len(ds) - failed} of {len(ds)} solids passed" + (f"; {failed} FAILED" if failed else ""))
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
