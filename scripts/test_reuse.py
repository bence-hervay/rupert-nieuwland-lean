#!/usr/bin/env python3
"""Tests of the rule by which a kept compiled module stands (`declarations.py`, `build.py`):
small Lean modules compiled here, changed in one way at a time.

    python3 scripts/test_reuse.py        (about two minutes; needs the Lake project)

What must change a fingerprint: a definition's value, a statement, a constructor, the body of a
`partial` definition, an `implemented_by` target, a `@[csimp]` replacement. What must not: a
proof, a docstring, a binder's name, the file a declaration is in. An `extern` declaration in a
library is refused. The kernel's re-check (`build.REPLAY`) passes a module whose imports changed
only in a proof and fails one whose proof no longer holds.
"""
import os
import shutil
import subprocess
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import build  # noqa: E402
import declarations  # noqa: E402

TMP = build.LEAN / ".lake/test-reuse"
A = """namespace T
/-- A function. -/
def f (n : Nat) : Nat := n + 1
theorem f_pos (n : Nat) : 0 < f n := Nat.succ_pos n
def g : Nat := f 2
inductive Col | red | green
structure Pt where
  x : Nat
def w (n : Nat) : Nat := if h : n = 0 then 0 else w (n / 2) + 1
termination_by n
decreasing_by omega
partial def p (n : Nat) : Nat := if n > 100 then n else p (n + 1)
end T
"""
B = """import A
namespace T
theorem g_eq : g = 3 := by decide
theorem uses_pos : 0 < f 5 := f_pos 5
def col : Col := .red
def viaPartial : Nat := p 3
def viaW : Nat := w 8
end T
"""
VARIANTS = {
    "proof": lambda a: a.replace(":= Nat.succ_pos n", ":= by unfold f; omega"),
    "doc": lambda a: a.replace("/-- A function. -/", "/-- The same function, described again. -/").replace("def f (n : Nat) : Nat := n + 1", "def f (m : Nat) : Nat := m + 1"),
    "value": lambda a: a.replace("def f (n : Nat) : Nat := n + 1", "def f (n : Nat) : Nat := n + 2").replace("Nat.succ_pos n", "by unfold f; omega"),
    "statement": lambda a: a.replace("theorem f_pos (n : Nat) : 0 < f n := Nat.succ_pos n", "theorem f_pos (n : Nat) : 1 ≤ f n := Nat.succ_pos n"),
    "partial": lambda a: a.replace("if n > 100 then", "if n > 200 then"),
    "constructor": lambda a: a.replace("inductive Col | red | green", "inductive Col | red | green | blue"),
}
L = """namespace L
def slow (n : Nat) : Nat := n
def fast (n : Nat) : Nat := n
@[csimp] theorem slow_eq_fast : @slow = @fast := rfl
def hookImpl (n : Nat) : Nat := n
@[implemented_by hookImpl] def hook (n : Nat) : Nat := n
def user (n : Nat) : Nat := hook (slow n)
def other (n : Nat) : Nat := n
end L
"""


class Reuse(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        lean_path, cls.lean = build.lean_env()
        shutil.rmtree(TMP, ignore_errors=True)
        cls.lean_path = lean_path

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(TMP, ignore_errors=True)

    def env(self, d):
        return {**os.environ, "LEAN_PATH": f"{d}:{self.lean_path}", "LEAN_NUM_THREADS": "1"}

    def compile(self, d, name, text):
        d.mkdir(parents=True, exist_ok=True)
        (d / f"{name}.lean").write_text(text)
        r = subprocess.run([self.lean, f"--root={d}", "-o", str(d / f"{name}.olean"), str(d / f"{name}.lean")],
                           env=self.env(d), capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        return d / f"{name}.olean"

    def fps(self, d, names):
        """The fingerprints of the declarations of the compiled modules `names` of `d`, in order."""
        table = {}
        for _, _, entries, _ in declarations.modules([d / f"{n}.olean" for n in names], self.lean, self.env(d)):
            table.update(declarations.fingerprints(entries, table))
        return table

    def test_modules(self):
        base = TMP / "base"
        self.compile(base, "A", A)
        self.compile(base, "B", B)
        want = self.fps(base, ["A", "B"])
        for n in ("T.f", "T.f_pos", "T.g", "T.Col", "T.Col.red", "T.Col.rec", "T.Pt", "T.w", "T.p", "T.p._unsafe_rec",
                  "T.g_eq", "T.viaPartial", "T.viaW"):
            self.assertIn(n, want)
        changed = {
            "proof": set(), "doc": set(),
            "value": {"T.f", "T.f_pos", "T.g"},
            "statement": {"T.f_pos"},
            "partial": {"T.p", "T.p._unsafe_rec"},
            "constructor": {"T.Col", "T.Col.red", "T.Col.green", "T.Col.rec"},
        }
        same = {"proof": {"T.f", "T.f_pos", "T.g", "T.w", "T.p"}, "doc": {"T.f", "T.f_pos", "T.g"}, "value": {"T.Col", "T.p", "T.w", "T.Pt"},
                "statement": {"T.f", "T.g", "T.Col"}, "partial": {"T.f", "T.g", "T.w"}, "constructor": {"T.f", "T.g", "T.p", "T.Pt"}}
        for v, change in VARIANTS.items():
            d = TMP / v
            self.assertNotEqual(change(A), A, v)
            self.compile(d, "A", change(A))
            got = self.fps(d, ["A"])
            for n in changed[v]:
                self.assertNotEqual(got.get(n), want[n], f"{v}: {n} must change")
            for n in same[v]:
                self.assertEqual(got.get(n), want[n], f"{v}: {n} must not change")
            if not changed[v]:  # (a proof may add or drop auxiliary lemmas of its own)
                self.assertEqual({n: fp for n, fp in got.items() if n in want}, {n: fp for n, fp in want.items() if n in got}, v)
                self.assertGreater(len(set(got) & set(want)), 30, v)

    def test_moved(self):
        """The same declarations in two files, and a module on top compiled against each."""
        base, d = TMP / "base2", TMP / "moved"
        self.compile(base, "A", A)
        self.compile(base, "B", B)
        i = A.index("inductive Col")
        self.compile(d, "A0", A[:i] + "end T\n")
        self.compile(d, "A", "import A0\nnamespace T\n" + A[i:])
        self.compile(d, "B", B)
        want, got = self.fps(base, ["A", "B"]), self.fps(d, ["A0", "A", "B"])
        self.assertEqual(got, want)

    def test_dependents(self):
        """A module on top is fingerprinted through what it uses."""
        base, d = TMP / "base3", TMP / "partial3"
        for x, a in ((base, A), (d, VARIANTS["partial"](A))):
            self.compile(x, "A", a)
            self.compile(x, "B", B)
        want, got = self.fps(base, ["A", "B"]), self.fps(d, ["A", "B"])
        self.assertNotEqual(got["T.viaPartial"], want["T.viaPartial"])
        self.assertEqual(got["T.viaW"], want["T.viaW"])
        self.assertEqual(got["T.g_eq"], want["T.g_eq"])

    def test_record(self):
        """`build.described` and `build.stands`: a record of B stands against the same A, and
        names the first declaration that changed otherwise."""
        base = TMP / "base4"
        self.compile(base, "A", A)
        self.compile(base, "B", B)
        infos = list(declarations.modules([base / "A.olean", base / "B.olean"], self.lean, self.env(base)))
        table = {}
        build.described(infos[0], table)
        before = dict(table)
        rec = {"format": 2, "base": "b", "source": "s", **build.described(infos[1], table)}
        self.assertIn("T.f_pos", rec["uses"])      # used in a proof only
        self.assertIn("T.g", rec["uses"])
        self.assertNotIn("T.g_eq", rec["uses"])    # its own
        ok = lambda **kw: build.stands(kw.get("rec", rec), kw.get("source", "s"), kw.get("base", "b"), kw.get("table", before), set(), {"A", "B"})
        self.assertIsNone(ok())
        self.assertIn("text", ok(source="other"))
        self.assertIn("toolchain", ok(base="other"))
        self.assertIn("`T.g` changed", ok(table={**before, "T.g": "0"}))
        self.assertIn("is gone", ok(table={n: fp for n, fp in before.items() if n != "T.f_pos"}))
        self.assertIn("old scheme", ok(rec={"module": "B", "key": "k"}))
        self.assertIn("no kept", ok(rec=None))
        gone = {**rec, "imports": ["Modules.Gone"]}
        self.assertIn("is gone", build.stands(gone, "s", "b", before, {"Modules.There"}, {"A", "B"}))

    def test_library(self):
        """A library's table: the code that runs in a declaration's place is in its fingerprint."""
        def table(name, text):
            d = TMP / name
            self.compile(d, "L", text)
            return declarations.table(["L"], self.lean, self.env(d))[1]
        want = table("lib", L)
        self.assertEqual(len({want[n] for n in ("L.slow", "L.fast", "L.hook", "L.hookImpl", "L.user", "L.other")}), 6)
        got = table("lib-csimp", L.replace("def fast (n : Nat) : Nat := n", "def fast (n : Nat) : Nat := n + 0"))
        for n in ("L.fast", "L.slow", "L.user"):
            self.assertNotEqual(got[n], want[n], n)
        self.assertEqual(got["L.other"], want["L.other"])
        self.assertEqual(got["L.hook"], want["L.hook"])
        got = table("lib-impl", L.replace("def hookImpl (n : Nat) : Nat := n", "def hookImpl (n : Nat) : Nat := n + 0"))
        for n in ("L.hookImpl", "L.hook", "L.user"):
            self.assertNotEqual(got[n], want[n], n)
        self.assertEqual(got["L.slow"], want["L.slow"])
        d = TMP / "lib-extern"
        self.compile(d, "L", L.replace("def other (n : Nat) : Nat := n", '@[extern "lean_other"] def other (n : Nat) : Nat := n'))
        with self.assertRaises(SystemExit) as e:
            declarations.table(["L"], self.lean, self.env(d))
        self.assertIn("extern", str(e.exception))

    def replay(self, d, names):
        lst = d / "replay.list"
        lst.write_text("".join(f"{n}\t{d / (n + '.olean')}\n" for n in names))
        tmp = d / "replay.lean"
        tmp.write_text(build.REPLAY.replace("LIST", str(lst)))
        return subprocess.run([self.lean, f"--root={d}", str(tmp)], env=self.env(d), capture_output=True, text=True)

    def test_replay(self):
        """The kernel's re-check of B: against an A whose proof changed it passes, against an A in
        which B's proof no longer holds it fails; an olean declared twice is refused."""
        base = TMP / "replay"
        self.compile(base, "A", A)
        b = self.compile(base, "B", B)
        r = self.replay(base, ["B"])
        self.assertIn("REPLAY-OK 5 0", r.stdout, r.stdout + r.stderr)
        for v, good in (("proof", True), ("value", False), ("statement", True), ("constructor", True)):
            d = TMP / f"replay-{v}"
            self.compile(d, "A", VARIANTS[v](A))
            shutil.copyfile(b, d / "B.olean")
            r = self.replay(d, ["B"])
            self.assertEqual("REPLAY-OK" in r.stdout, good, f"{v}: {r.stdout[-600:]}{r.stderr[-300:]}")
        r = self.replay(base, ["A", "B"])
        self.assertIn("REPLAY-OK", r.stdout, r.stdout + r.stderr)
        shutil.copyfile(b, base / "B2.olean")
        r = self.replay(base, ["B", "B2"])
        self.assertNotIn("REPLAY-OK", r.stdout)


if __name__ == "__main__":
    unittest.main(verbosity=2)
