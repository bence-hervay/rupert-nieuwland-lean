#!/usr/bin/env python3
"""Two plots of `Definitions/`: which file imports which, and which definition uses which.

    python3 scripts/deps.py          (in `lean-new/`; needs `lake`, Graphviz's `dot`)

Writes `docs/definitions-files.svg`, `docs/definitions-declarations.svg` and `docs/definitions-uses.tsv`.

* **Files**: the `import` lines of `Definitions/*.lean`, as written (Mathlib's modules too).
* **Declarations**: every `def`, `abbrev`, `structure` and `notation` of the sources. Lean gives
  the uses: each constant of the library's modules with the constants its type and value mention
  (a structure's fields, constructor and generated constants count as the structure). A notation
  is not a constant: a declaration uses it when its source text has it, and the arrow to what
  the notation stands for replaces the direct one.

While `PROPOSED` below names a regrouping of the files that is not built, two more plots show
it: `docs/definitions-proposed-files.svg` (the new files with what each would hold, and the
imports their definitions need) and `docs/definitions-proposed-declarations.svg` (the same
declarations and uses, boxed by new file, with today's files as sections).

An arrow `A → B` reads "A needs B"; what is needed is drawn on the left. The second plot leaves out a
use that also follows from other arrows (`A → C → B`): `docs/definitions-uses.tsv` lists every direct
use, those too.
"""
import collections
import json
import re
import subprocess
import sys
from pathlib import Path

LEAN = Path(__file__).resolve().parents[1]
DOCS = LEAN / "docs"
FONT = "DejaVu Sans Mono"
# the two strands of the definitions and the files where they meet
GEOMETRY = {"Polyhedra", "Rupertness"}
POLYNOMIALS = {"Polynomials"}
ORANGE, BLUE, WHITE, GREY, GREEN = "#ff8000", "#0080ff", "#ffffff", "#b4b4b4", "#3ddc5a"
TOPICS = ((ORANGE, "geometry"), (BLUE, "polynomials"), (WHITE, "both: where they meet"))
# A regrouping by topic that is not built: the new file -> today's files, in the order of their
# text, and the new file's colour. Empty: no plot of a proposal. (The four files of today were
# such a proposal on 2026-11-18.)
PROPOSED = {}

EXTRACT = """import Definitions
open Lean
#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let inDefs (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some i => (`Definitions).isPrefixOf mods[i.toNat]!
    | none => false
  let rows := env.constants.fold (init := #[]) fun acc c ci =>
    if inDefs c then
      let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
      acc.push s!"USES\\t{c}\\t{" ".intercalate ((used.filter fun d => inDefs d && d != c).toList.map toString)}"
    else acc
  for r in rows.qsort (· < ·) do IO.println r
"""


def colour(stem):
    return ORANGE if stem in GEOMETRY else BLUE if stem in POLYNOMIALS else WHITE


def sources():
    """The files' imports, and the declarations: full name -> (file, kind, source text)."""
    imports, decl = {}, {}
    for f in sorted((LEAN / "Definitions").glob("*.lean")):
        lines = f.read_text().splitlines()
        imports[f.stem] = [m.group(1) for m in (re.match(r"import (\S+)", l) for l in lines) if m]
        stack, cur = [], None
        for line in lines:
            if re.match(r"(/--|end |namespace |open |scoped|noncomputable |def |abbrev |structure )", line):
                cur = None
            m = re.match(r"namespace (\S+)", line)
            if m:
                stack.append(m.group(1))
            m = re.match(r"end (\S+)", line)
            if m and stack and stack[-1] == m.group(1):
                stack.pop()
            m = re.match(r"(?:noncomputable )?(def|abbrev|structure) (\S+)", line)
            n = re.search(r'notation "([^"]+)"', line)
            if m:
                cur = ".".join(stack + [m.group(2)])
                decl[cur] = [f.stem, m.group(1), ""]
            elif n:
                decl["notation " + n.group(1).strip()] = [f.stem, "notation", line.split("=>", 1)[1]]
            if cur:
                decl[cur][2] += line + "\n"
    return imports, decl


def uses(decl):
    """The direct uses among the declarations (a -> the set of b)."""
    tmp = LEAN / ".lake/deps-extract.lean"
    tmp.write_text(EXTRACT)
    out = subprocess.run(["lake", "env", "lean", str(tmp)], cwd=LEAN, capture_output=True, text=True)
    tmp.unlink()
    rows = [l.split("\t") for l in out.stdout.splitlines() if l.startswith("USES\t")]
    if out.returncode != 0 or not rows:
        sys.exit(f"the extraction failed: {out.stdout[-400:]}{out.stderr[-400:]}")
    consts = {r[1] for r in rows}
    lost = [d for d in decl if not d.startswith("notation ") and d not in consts]
    if lost:
        sys.exit(f"declared in the sources but not in Lean: {lost}")

    def owner(c):
        parts = c.split(".")
        for i in range(len(parts), 0, -1):
            if ".".join(parts[:i]) in decl:
                return ".".join(parts[:i])
        return None  # a notation's own constants

    edges = collections.defaultdict(set)
    for _, c, used in rows:
        a = owner(c)
        for d in used.split():
            b = owner(d)
            if a and b and a != b:
                edges[a].add(b)
    # the notations: used where the source text has them; they stand for what their text names
    for n, (_, kind, text) in decl.items():
        if kind != "notation":
            continue
        token = n[len("notation "):]
        target = [d for d in decl if not d.startswith("notation ") and re.search(r"\b" + re.escape(d) + r"\b", text)]
        target = [d for d in target if not any(e.startswith(d + ".") for e in target)]
        edges[n].update(target)
        for d, (_, k, body) in decl.items():
            if k != "notation" and token in body:
                edges[d].add(n)
                edges[d].difference_update(target)
    return edges


def implied(edges):
    """The arrows a -> b that also follow from a longer path."""
    def reach(a, seen):
        for b in edges.get(a, ()):
            if b not in seen:
                seen.add(b)
                reach(b, seen)
        return seen
    out = set()
    for a in list(edges):
        for b in edges[a]:
            if any(b in reach(c, set()) for c in edges[a] if c != b):
                out.add((a, b))
    return out


def head(title, note, legend=TOPICS):
    legend = "&#160;&#160;&#160;&#160;".join(f'<font color="{c}">■&#160;</font>{name}' for c, name in legend)
    return (f'digraph G {{\n  graph [bgcolor="#000000", fontname="{FONT}", fontcolor="{WHITE}", fontsize=15, rankdir=RL, '
            f'nodesep=0.3, ranksep=0.9, pad=0.35, labelloc=t, labeljust=l,\n'
            f'    label=<{title}<br align="left"/>'
            + "".join(f'<font point-size="10" color="{GREY}">{n}</font><br align="left"/>' for n in note) +
            f'<font point-size="10">{legend}</font><br align="left"/>>];\n'
            f'  node [shape=box, style=rounded, fontname="{FONT}", fontcolor="{WHITE}", fontsize=11, penwidth=1.3, margin="0.14,0.07"];\n'
            f'  edge [color="{GREY}", arrowsize=0.65, penwidth=1.0];\n')


def render(name, dot):
    DOCS.mkdir(exist_ok=True)
    r = subprocess.run(["dot", "-Tsvg", "-o", str(DOCS / f"{name}.svg")], input=dot, text=True, capture_output=True)
    if r.returncode != 0:
        sys.exit(f"dot: {r.stderr[-600:]}")
    # other machines: any monospace font; the black background as a rectangle of the whole picture
    svg = (DOCS / f"{name}.svg").read_text().replace(f'font-family="{FONT}"', f"font-family=\"'{FONT}', Menlo, Consolas, monospace\"")
    svg = re.sub(r"(<svg [^>]*>)", r'\1\n<rect width="100%" height="100%" fill="#000000"/>', svg, count=1)
    (DOCS / f"{name}.svg").write_text(svg)
    print(DOCS / f"{name}.svg")


def short(d):
    return d[len("notation "):] if d.startswith("notation ") else d.replace("Nieuwland.", "", 1)


def pieces_files():
    """Today's files of `Definitions` that the certificates' pieces depend on (through the
    modules they import), by the solids' manifests."""
    todo, seen = set(), set()
    for m in (LEAN / "Polyhedra").glob("*/*/Certificates/manifest.json"):
        for piece in json.loads(m.read_text())["pieces"]:
            todo.update(i for i in piece.get("imports", []) if not i.startswith("Polyhedra."))
    todo = sorted(todo)
    while todo:
        m = todo.pop()
        f = LEAN / (m.replace(".", "/") + ".lean")
        if m not in seen and f.exists():
            seen.add(m)
            todo += [i for i in re.findall(r"^import (\S+)", f.read_text(), re.M) if i.split(".")[0] in ("Modules", "Definitions")]
    return {m.split(".", 1)[1] for m in seen if m.startswith("Definitions.")}


def proposed(imports, decl, edges, dim):
    """The two plots of `PROPOSED`."""
    new_of = {f: n for n, (_, fs) in PROPOSED.items() for f in fs}
    if sorted(new_of) != sorted(imports) or len(new_of) != sum(len(fs) for _, fs in PROPOSED.values()):
        sys.exit("PROPOSED names each of today's files once")
    at = {d: new_of[v[0]] for d, v in decl.items()}
    needs = collections.defaultdict(set)  # the new files' imports: what their declarations use
    for a, bs in edges.items():
        needs[at[a]].update(at[b] for b in bs if at[b] != at[a])
    for n in PROPOSED:
        seen, todo = set(), list(needs[n])
        while todo:
            m = todo.pop()
            if m not in seen:
                seen.add(m)
                todo += needs[m]
        if n in seen:
            sys.exit(f"PROPOSED: {n}.lean would import itself through {sorted(seen)}")
    inherited = implied(needs)
    pieces = pieces_files()
    legend = [(c, f"{n}.lean") for n, (c, _) in PROPOSED.items()]
    files = collections.defaultdict(list)
    for d, (f, _, _) in decl.items():
        files[f].append(d)
    # the files
    dot = head(f"Definitions regrouped by topic: {len(PROPOSED)} files for today's {len(imports)} (a proposal, not built)",
               ["A → B: the file A would import B, because a definition of A uses one of B; what is imported is on the left.",
                "In each file: today's files, in the order of their text, with their declarations. Small, last: its imports from Mathlib."],
               legend)
    for n, (c, fs) in PROPOSED.items():
        lines = sum(len((LEAN / "Definitions" / f"{f}.lean").read_text().splitlines()) for f in fs)
        mine = [f for f in fs if f in pieces]
        used = ("the certificates' pieces use none of it" if not mine else "the certificates' pieces use all of it" if mine == fs
                else "the certificates' pieces use " + ", ".join(f"{f}.lean" for f in mine) + " of it")
        rows = (f'<tr><td colspan="2" align="left"><font point-size="13">{n}.lean</font></td></tr>'
                f'<tr><td colspan="2" align="left"><font point-size="8" color="{GREY}">{len(fs)} files of today, {lines} lines'
                f'<br align="left"/>{used}</font><br align="left"/></td></tr>')
        for f in fs:
            rows += (f'<tr><td align="left" valign="top"><font point-size="9" color="{GREY}">{f}.lean</font></td><td align="left">'
                     + "".join(f'<font point-size="9">{short(d)}</font><br align="left"/>' for d in files[f]) + "</td></tr>")
        mathlib = list(dict.fromkeys(i for f in fs for i in imports[f] if not i.startswith("Definitions.")))
        if mathlib:
            rows += ('<tr><td colspan="2" align="left">' + "".join(f'<font point-size="8" color="#808080">{i}</font><br align="left"/>' for i in mathlib)
                     + "</td></tr>")
        dot += f'  "{n}" [label=<<table border="0" cellborder="0" cellspacing="0" cellpadding="3">{rows}</table>>, color="{c}", margin="0.2,0.1"];\n'
    for a in PROPOSED:
        for b in sorted(needs[a]):
            if (a, b) not in inherited:
                dot += f'  "{a}" -> "{b}";\n'
    render("definitions-proposed-files", dot + "}\n")
    # the declarations
    dot = head("Definitions regrouped by topic: the declarations (a proposal, not built)",
               ["A → B: the definition A uses B; what is used is on the left. A box: a new file; inside it, dashed: today's files. "
                "Dashed node: a notation.",
                f"Not drawn: {len(dim)} uses that follow from the drawn arrows (A → C → B); definitions-uses.tsv lists every use."],
               legend)
    for n, (c, fs) in PROPOSED.items():
        dot += (f'  subgraph "cluster_new_{n}" {{\n    label="{n}.lean"; fontsize=13; fontcolor="{WHITE}"; color="{c}"; penwidth=1.2; '
                f'style=rounded; labeljust=r; margin=16;\n')
        for f in fs:
            dot += (f'    subgraph "cluster_{f}" {{\n      label="today {f}.lean"; fontsize=9; fontcolor="{GREY}"; color="#4a4a4a"; penwidth=0.8; '
                    f'style="rounded,dashed"; labeljust=l; margin=8;\n')
            for d in files[f]:
                style = "rounded,dashed" if decl[d][1] == "notation" else "rounded"
                dot += f'      "{d}" [label="{short(d)}", color="{c}", style="{style}"];\n'
            dot += "    }\n"
        dot += "  }\n"
    for a in sorted(edges):
        for b in sorted(edges[a]):
            if (a, b) not in dim:
                dot += f'  "{a}" -> "{b}";\n'
    # a file's declarations right of those of the files it imports: unseen arrows from its first to their last
    # (between boxes dot weighs an arrow instead of obeying it: weight 0 would be no arrow)
    inside = {d: {b for b in edges.get(d, ()) if at[b] == at[d]} for d in decl}
    first = {n: [d for d in decl if at[d] == n and not inside[d]] for n in PROPOSED}
    last = {n: [d for d in decl if at[d] == n and not any(d in inside[e] for e in decl)] for n in PROPOSED}
    for a in PROPOSED:
        for b in sorted(needs[a]):
            if (a, b) not in inherited:
                dot += "".join(f'  "{x}" -> "{y}" [style=invis, weight=3];\n' for x in first[a] for y in last[b])
    render("definitions-proposed-declarations", dot.replace("ranksep=0.9", "ranksep=0.6") + "}\n")
    print(f"proposed: {len(PROPOSED)} files; imports " + ", ".join(f"{a} → {b}" for a in PROPOSED for b in sorted(needs[a]) if (a, b) not in inherited)
          + f"; the pieces depend on today's {sorted(pieces)}")


def main():
    imports, decl = sources()
    # the files
    dot = head("Definitions: the files", ["A → B: the file A imports B, as written; what is imported is on the left.",
                                          "Small: the file's imports from Mathlib."])
    for f, v in imports.items():
        mathlib = "".join(f'<br/><font point-size="8" color="{GREY}">{i}</font>' for i in v if not i.startswith("Definitions."))
        margin = ', margin="0.34,0.09"' if mathlib else ""
        dot += f'  "{f}" [label=<{f}.lean{mathlib}>, color="{colour(f)}"{margin}];\n'
        for i in v:
            if i.startswith("Definitions."):
                dot += f'  "{f}" -> "{i.split(".", 1)[1]}";\n'
    render("definitions-files", dot + "}\n")
    # the declarations
    edges = uses(decl)
    dim = implied(edges)
    dot = head("Definitions: the declarations",
               ["A → B: the definition A uses B; what is used is on the left. A box: a file. Dashed: a notation.",
                f"Not drawn: {len(dim)} uses that follow from the drawn arrows (A → C → B); definitions-uses.tsv lists every use."])
    files = collections.defaultdict(list)
    for d, (f, _, _) in decl.items():
        files[f].append(d)
    for f, ds in files.items():
        dot += (f'  subgraph "cluster_{f}" {{\n    label="{f}.lean"; fontsize=10; fontcolor="{GREY}"; color="#3c3c3c"; '
                f'style=rounded; labeljust=l; margin=10;\n')
        for d in ds:
            style = "rounded,dashed" if decl[d][1] == "notation" else "rounded"
            dot += f'    "{d}" [label="{short(d)}", color="{colour(f)}", style="{style}"];\n'
        dot += "  }\n"
    for a in sorted(edges):
        for b in sorted(edges[a]):
            if (a, b) not in dim:
                dot += f'  "{a}" -> "{b}";\n'
    render("definitions-declarations", dot + "}\n")
    (DOCS / "definitions-uses.tsv").write_text("declaration\tfile\tkind\tuses\tuses_not_drawn\n" + "".join(
        f"{short(d)}\tDefinitions/{f}.lean\t{k}\t{', '.join(short(b) for b in sorted(edges.get(d, ())) if (d, b) not in dim)}"
        f"\t{', '.join(short(b) for b in sorted(edges.get(d, ())) if (d, b) in dim)}\n" for d, (f, k, _) in decl.items()))
    if PROPOSED:
        proposed(imports, decl, edges, dim)
    print(f"{len(imports)} files; {sum(k != 'notation' for _, k, _ in decl.values())} definitions and "
          f"{sum(k == 'notation' for _, k, _ in decl.values())} notations; {sum(map(len, edges.values()))} uses, {len(dim)} of them implied")


if __name__ == "__main__":
    main()
