#!/usr/bin/env python3
"""The certificates' pieces: one archive per solid, checked against the solid's manifest.

    python3 scripts/certificates.py fetch SOLID... [--source SRC]
    python3 scripts/certificates.py pack SOLID... --out DIR [--jobs N]
    python3 scripts/certificates.py status SOLID...

SOLID: a solid's directory (`Polyhedra/Platonic/Cube`), a family (`Johnson`) or `all`.

A certificate's pieces are Lean files, too large for Git (51 GB in all). The solid's
`Certificates/manifest.json`, which is in Git, names every piece with its size and SHA-256. The
release `certificates` of this repository holds one archive per solid, `<Family>.<Solid>.tar.xz`.

fetch: downloads a solid's archive (with `gh` when it is installed and logged in, otherwise over
HTTPS; or from SRC, a directory or URL that holds the archives), unpacks it into a temporary
directory under `.lake/`, and moves the pieces into `Certificates/` only when the archive holds
exactly the manifest's files, each with its size and SHA-256. A solid whose pieces are already
in place and match is left as it is.
pack: writes the archives of solids whose pieces are in place and match (deterministic: sorted as
the manifest, no times or owners).
status: which solids have their pieces in place.
"""
import argparse
import hashlib
import json
import lzma
import os
import shutil
import subprocess
import sys
import tarfile
import tempfile
import urllib.request
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO, TAG = "bence-hervay/rupert-nieuwland-lean", "certificates"
CHUNK = 1 << 20


def solids(args):
    """The solids' directories named by `args` (directories, families or `all`), in order."""
    every = sorted(m.parents[1] for m in ROOT.glob("Polyhedra/*/*/Certificates/manifest.json"))
    out = []
    for a in args:
        p = Path(a)
        if a == "all":
            out += every
        elif len(p.parts) == 1 and (ROOT / "Polyhedra" / a).is_dir():
            out += [d for d in every if d.parent.name == a]
        else:
            d = (p if p.is_absolute() else ROOT / p).resolve()
            if not (d / "Certificates/manifest.json").exists():
                sys.exit(f"{a}: not a solid's directory (Polyhedra/<Family>/<Solid>)")
            out.append(d)
    return list(dict.fromkeys(out))


def name(d):
    return f"{d.parent.name}.{d.name}"


def pieces(d):
    return json.loads((d / "Certificates/manifest.json").read_text())["pieces"]


def sha256(f):
    h = hashlib.sha256()
    with open(f, "rb") as fh:
        while b := fh.read(CHUNK):
            h.update(b)
    return h.hexdigest()


def problems(d):
    """What keeps the pieces in `Certificates/` from being exactly the manifest's."""
    c, out = d / "Certificates", []
    for p in pieces(d):
        f = c / p["file"]
        if not f.is_file():
            out.append(f"{p['file']}: missing")
        elif f.stat().st_size != p["bytes"] or sha256(f) != p["sha256"]:
            out.append(f"{p['file']}: not the manifest's")
    extra = {f.name for f in c.glob("*.lean")} - {p["file"] for p in pieces(d)}
    out += [f"{f}: not in the manifest" for f in sorted(extra)]
    return out


def download(asset, source, into):
    """The archive `asset` as a file in `into`."""
    dst = into / asset
    if source and not source.startswith(("http://", "https://")):
        shutil.copyfile(Path(source) / asset, dst)
        return dst
    if not source and shutil.which("gh"):
        r = subprocess.run(["gh", "release", "download", TAG, "--repo", REPO, "--pattern", asset, "--dir", str(into),
                            "--clobber"], capture_output=True, text=True)
        if r.returncode == 0 and dst.exists():
            return dst
    url = f"{source.rstrip('/')}/{asset}" if source else f"https://github.com/{REPO}/releases/download/{TAG}/{asset}"
    with urllib.request.urlopen(url) as r, open(dst, "wb") as fh:
        shutil.copyfileobj(r, fh, CHUNK)
    return dst


def unpack(archive, d, into):
    """The archive's pieces into the directory `into`, refused unless they are exactly the
    manifest's (names, sizes, SHA-256)."""
    want = {"Certificates/" + p["file"]: p for p in pieces(d)}
    seen = set()
    with tarfile.open(archive, "r:xz") as t:
        for m in t:
            p = want.get(m.name)
            if p is None or not m.isfile() or m.name in seen:
                raise ValueError(f"{archive.name}: {m.name!r} is not one of the manifest's pieces")
            seen.add(m.name)
            h, size = hashlib.sha256(), 0
            with t.extractfile(m) as src, open(into / p["file"], "wb") as out:
                while b := src.read(CHUNK):
                    h.update(b)
                    size += len(b)
                    out.write(b)
            if size != p["bytes"] or h.hexdigest() != p["sha256"]:
                raise ValueError(f"{archive.name}: {p['file']} is not the manifest's (size or SHA-256)")
    if missing := sorted(set(want) - seen):
        raise ValueError(f"{archive.name}: {len(missing)} pieces missing, as {missing[0]}")


def fetch(d, source=None):
    """Puts the pieces of the solid `d` in place; returns a line saying what it did."""
    if not problems(d):
        return f"{name(d)}: {len(pieces(d))} pieces in place"
    work = ROOT / ".lake/certificates"
    work.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=work) as tmp:
        tmp = Path(tmp)
        archive = download(name(d) + ".tar.xz", source, tmp)
        (tmp / "pieces").mkdir()
        unpack(archive, d, tmp / "pieces")
        for f in (d / "Certificates").glob("*.lean"):
            f.unlink()
        for f in sorted((tmp / "pieces").iterdir()):
            os.replace(f, d / "Certificates" / f.name)
        size = archive.stat().st_size
    if bad := problems(d):
        raise ValueError(f"{name(d)}: {bad[0]}")
    return f"{name(d)}: {len(pieces(d))} pieces fetched and checked ({size / 1e6:.1f} MB archive)"


def pack(d, out):
    if bad := problems(d):
        raise ValueError(f"{name(d)}: {bad[0]}")
    part = out / f"{name(d)}.tar.xz.part"
    with lzma.open(part, "wb", preset=6) as z, tarfile.open(fileobj=z, mode="w", format=tarfile.PAX_FORMAT) as t:
        for p in pieces(d):
            info = tarfile.TarInfo("Certificates/" + p["file"])
            info.size, info.mode = p["bytes"], 0o644
            with open(d / "Certificates" / p["file"], "rb") as fh:
                t.addfile(info, fh)
    part.rename(out / f"{name(d)}.tar.xz")
    return f"{name(d)}: {len(pieces(d))} pieces, {(out / f'{name(d)}.tar.xz').stat().st_size / 1e6:.1f} MB"


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("command", choices=["fetch", "pack", "status"])
    ap.add_argument("solids", nargs="+")
    ap.add_argument("--source", help="fetch: a directory or URL holding the archives (default: the release)")
    ap.add_argument("--out", type=Path, help="pack: the directory for the archives")
    ap.add_argument("--jobs", type=int, default=1, help="pack: archives written at a time")
    a = ap.parse_args()
    ds = solids(a.solids)
    failed = 0
    if a.command == "status":
        for d in ds:
            bad = problems(d)
            print(f"{name(d)}: " + (f"{len(pieces(d))} pieces in place" if not bad else f"{len(bad)} problems, as {bad[0]}"))
        return
    if a.command == "pack":
        if not a.out:
            sys.exit("pack needs --out DIR")
        a.out.mkdir(parents=True, exist_ok=True)
        with ProcessPoolExecutor(a.jobs) as ex:
            for d, f in [(d, ex.submit(pack, d, a.out)) for d in ds]:
                try:
                    print(f.result(), flush=True)
                except ValueError as e:
                    failed += 1
                    print(f"FAILED {e}", flush=True)
    else:
        for d in ds:
            try:
                print(fetch(d, a.source), flush=True)
            except (ValueError, OSError, tarfile.TarError, lzma.LZMAError) as e:
                failed += 1
                print(f"FAILED {name(d)}: {e}", flush=True)
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
