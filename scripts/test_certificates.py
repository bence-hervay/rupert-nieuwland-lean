#!/usr/bin/env python3
"""Tests of `certificates.py`: an archive is unpacked only when it holds exactly the manifest's
pieces, and nothing is written outside the solid's `Certificates/`.

    python3 scripts/test_certificates.py
"""
import hashlib
import io
import json
import lzma
import sys
import tarfile
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import certificates as C  # noqa: E402

PIECES = {"Lift.lean": b"import Mathlib\n", "Claim0.lean": b"-- a piece\n" * 1000, "Root0.lean": b"theorem t : True := trivial\n"}


def solid(tmp):
    d = tmp / "Polyhedra/Platonic/Fake"
    (d / "Certificates").mkdir(parents=True)
    man = [{"file": f, "bytes": len(b), "sha256": hashlib.sha256(b).hexdigest(), "imports": []} for f, b in PIECES.items()]
    (d / "Certificates/manifest.json").write_text(json.dumps({"solid": "platonic/fake", "pieces": man}))
    for f, b in PIECES.items():
        (d / "Certificates" / f).write_bytes(b)
    return d


def archive(path, members):
    """An archive with `members`: (name, bytes) or (name, None, TarInfo-type, linkname)."""
    with lzma.open(path, "wb") as z, tarfile.open(fileobj=z, mode="w") as t:
        for m in members:
            info = tarfile.TarInfo(m[0])
            if m[1] is None:
                info.type, info.linkname = m[2], m[3]
                t.addfile(info)
            else:
                info.size = len(m[1])
                t.addfile(info, io.BytesIO(m[1]))


class Certificates(unittest.TestCase):
    def setUp(self):
        self.tmpdir = tempfile.TemporaryDirectory()
        self.tmp = Path(self.tmpdir.name)
        self.d = solid(self.tmp)
        self.src = self.tmp / "release"
        self.src.mkdir()
        self.asset = self.src / "Platonic.Fake.tar.xz"

    def tearDown(self):
        self.tmpdir.cleanup()

    def clear(self):
        for f in (self.d / "Certificates").glob("*.lean"):
            f.unlink()

    def refused(self, members):
        archive(self.asset, members)
        self.clear()
        with self.assertRaises(ValueError):
            C.fetch(self.d, str(self.src))
        self.assertEqual(sorted(f.name for f in (self.d / "Certificates").iterdir()), ["manifest.json"])
        self.assertFalse((self.tmp / "evil").exists())

    def good(self):
        return [("Certificates/" + f, b) for f, b in PIECES.items()]

    def test_pack_then_fetch(self):
        print(C.pack(self.d, self.src))
        self.clear()
        self.assertTrue(C.problems(self.d))
        self.assertIn("fetched and checked", C.fetch(self.d, str(self.src)))
        self.assertEqual(C.problems(self.d), [])

    def test_pack_is_deterministic(self):
        C.pack(self.d, self.src)
        first = self.asset.read_bytes()
        C.pack(self.d, self.src)
        self.assertEqual(first, self.asset.read_bytes())

    def test_in_place_needs_no_archive(self):
        self.assertIn("in place", C.fetch(self.d, str(self.tmp / "nowhere")))

    def test_tampered_piece(self):
        m = self.good()
        m[1] = (m[1][0], m[1][1][:-1] + b"!")
        self.refused(m)

    def test_extra_member(self):
        self.refused(self.good() + [("Certificates/Extra.lean", b"axiom bad : False\n")])

    def test_missing_member(self):
        self.refused(self.good()[:-1])

    def test_duplicate_member(self):
        self.refused(self.good() + [self.good()[0]])

    def test_path_outside(self):
        self.refused([("../../../../evil", b"x")] + self.good())

    def test_symlink_member(self):
        self.refused([("Certificates/Lift.lean", None, tarfile.SYMTYPE, "/etc/passwd")] + self.good()[1:])

    def test_pack_refuses_a_changed_piece(self):
        (self.d / "Certificates/Root0.lean").write_bytes(b"theorem t : False := sorry\n")
        with self.assertRaises(ValueError):
            C.pack(self.d, self.src)
        self.assertFalse(self.asset.exists())

    def test_stray_lean_file_is_a_problem(self):
        (self.d / "Certificates/Stray.lean").write_bytes(b"")
        self.assertIn("Stray.lean: not in the manifest", C.problems(self.d))


if __name__ == "__main__":
    unittest.main()
