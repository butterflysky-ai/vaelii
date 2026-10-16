#!/usr/bin/env python3
# SPDX-License-Identifier: SSPL-1.0
# Copyright © 2026 Vaelii LLC and the Vaelii contributors.
"""Draw the upper-ontology genl graph as one standalone SVG.

The edges come from vaelii: scripts/ontology-edges.clj loads the upper ontology (with
--include-middle, the starter) into an in-memory KB and prints the believed taxonomy,
so an edge a cover roster or an intersection installs is drawn beside a stated genl.
The export is cached under target/, keyed by the KB files, that script and src/. The
diagram has:

  - one node per type below `thing` (with --predicates, also the genl components that
    relate predicates, which have no edge to `thing`),
  - one edge per minimal genl, the transitive reduction (with --all-edges, every direct
    edge, a redundant stated genl included), arrow pointing at the more general super,
  - node fill tinted by the file the term is *defined* in (its `(comment term …)`),
  - edge colour set by the file whose sentence installs the edge.

The KB loads every upper file into CxUniverse, so the two file colours are read off the
`resources/kb/*.txt` text. An edge whose colour differs from its child node's fill is a
genl written in a file other than the one that documents its subject; an edge no file
sentence installs is grey.

Four layout engines, none required to be installed:

  - dot        Graphviz ranks the DAG and minimises crossings. It lays out a handful of
               candidates (rank direction, label wrapping at underscores, leaf-fan
               staggering by `unflatten`, root-tree packing) and keeps the most compact. --direction down keeps `thing`
               at the top, at about four times as wide as tall for the upper ontology.
               Label size is set by --text-scale.
  - gridfold   a left-to-right dendrogram whose wide terminal fans fold into grids, so
               the leaves stack instead of stretching; it keeps the most compact of
               several fold widths. Keeps arrows and the edge-context colours, no
               dependency. The auto fallback when dot is absent.
  - icicle     a space-filling partition: depth is the column, a box is as tall as the
               leaves under it, leaves reach the right edge. Fills the sheet; tree edges
               become shared borders and only the multiple-inheritance genl draw.
  - dendrogram the plain left-to-right tree, portrait (about as tall as it has leaves).

Usage:
  scripts/ontology-graph.py [--out FILE] [--include-middle] [--predicates] [--all-edges]
  scripts/ontology-graph.py --engine {auto,dot,gridfold,icicle,dendrogram}
  scripts/ontology-graph.py --engine dot --ratio 0.72 --text-scale 1.4
  scripts/ontology-graph.py --engine gridfold --out target/upper.svg

`--ratio` is the height / width of the page or window the drawing fills. dot and
gridfold keep the candidate layout that shows the labels largest on it. No layout is
stretched to the ratio: spreading nodes apart adds whitespace and shrinks every label
once the drawing is scaled to fit. `--text-scale` sets the dot label size against the
fixed node spacing.

In a browser the SVG covers the window: its shorter side fills the window and the
longer side scrolls.
"""
import argparse
import collections
import glob
import hashlib
import json
import math
import os
import re
import shutil
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# One hue per file, keyed by its basename: an upper file (`core`, `abstract`, …), all
# loaded into CxUniverse, or a middle context. `line` draws the genl edges written in
# that file; `fill` tints a node defined there (the same hue lightened toward white so a
# black label reads).
CONTEXT_COLORS = {
    "core":       ("#2f5d8f", "#dbe6f2"),
    "abstract":   ("#6b4c9a", "#e5dcf1"),
    "life":       ("#2f8f5d", "#d7efe0"),
    "organism":   ("#1f8a8a", "#d3ecec"),
    "measure":    ("#c07a1f", "#f5e6cf"),
    "society":    ("#b03a6e", "#f4d9e5"),
    "space":      ("#8a5a2f", "#eee0d0"),
    "time":       ("#b03030", "#f3d6d6"),
    "CxWell":     ("#444444", "#dcdcdc"),
}
FALLBACK = ("#777777", "#e6e6e6")

TOKEN_RE = re.compile(r';[^\n]*|"(?:\\.|[^"\\])*"|[()]|[^\s()";]+')

# A cover installs one (genl part whole) per part, the whole first; an intersection
# installs one (genl combined conjunct) per conjunct, the combined type first.
COVERS = ("partition", "covering", "separating")


def kb_files(include_middle):
    """The .txt files the KB loads: every upper file, `core.txt` first, then optionally
    middle."""
    files = [os.path.join(REPO, "resources/kb/upper/core.txt")]
    files += sorted(f for f in glob.glob(os.path.join(REPO, "resources/kb/upper/*.txt"))
                    if os.path.basename(f) != "core.txt")
    if include_middle:
        files += sorted(glob.glob(os.path.join(REPO, "resources/kb/middle/*.txt")))
    return files


EDGES_CLJ = os.path.join(REPO, "scripts/ontology-edges.clj")


def engine_edges(files, include_middle, predicates):
    """The believed genl edges as (sub, super, minimal) from scripts/ontology-edges.clj,
    read from target/ when an export for the same KB files, script and src/ is there."""
    flags = (["middle"] if include_middle else []) + (["predicates"] if predicates else [])
    key = hashlib.sha1(" ".join(flags).encode())
    for f in files + [EDGES_CLJ]:
        with open(f, "rb") as fh:
            key.update(fh.read())
    for cmd in (["git", "rev-parse", "HEAD:src"], ["git", "diff", "HEAD", "--", "src"]):
        key.update(subprocess.run(cmd, cwd=REPO, capture_output=True, check=True).stdout)
    cache = os.path.join(REPO, "target", f"ontology-edges-{key.hexdigest()[:16]}.json")
    if not os.path.exists(cache):
        print("loading the ontology into vaelii (about 30 s) …", file=sys.stderr)
        out = subprocess.run(["lein", "run", "-m", "clojure.main", EDGES_CLJ] + flags,
                             cwd=REPO, capture_output=True, text=True)
        if out.returncode != 0:
            sys.exit(f"ontology-edges.clj failed:\n{out.stderr[-2000:]}")
        os.makedirs(os.path.dirname(cache), exist_ok=True)
        with open(cache, "w", encoding="utf-8") as fh:
            fh.write(out.stdout.strip().splitlines()[-1])
    with open(cache, encoding="utf-8") as fh:
        return [tuple(row) for row in json.load(fh)["edges"]]


def forms(text):
    """The top-level forms of a KB file as nested lists of token strings, comments
    dropped."""
    stack = [[]]
    for tok in TOKEN_RE.findall(text):
        if tok.startswith(";"):
            continue
        if tok == "(":
            stack.append([])
        elif tok == ")":
            done = stack.pop()
            stack[-1].append(done)
        else:
            stack[-1].append(tok)
    return stack[0]


def genl_edges(form):
    """The (sub, super) edges a top-level ground form installs: a `genl`, a cover or an
    `intersection`, unwrapped from a `set/…` strength wrapper. A rule installs none."""
    if form and form[0].startswith("set/") and len(form) == 2 and isinstance(form[1], list):
        form = form[1]
    if len(form) < 3 or not all(isinstance(t, str) for t in form):
        return []
    head, args = form[0], form[1:]
    if head == "genl":
        return [(args[0], args[1])]
    if head in COVERS:
        return [(part, args[0]) for part in args[1:]]
    if head == "intersection":
        return [(args[0], conjunct) for conjunct in args[1:]]
    return []


def parse(files):
    """Return (written, home): `written` maps a (sub, super) edge to the file whose
    sentence installs it, and `home` maps a term to the file of its first
    `(comment term …)`. Only the colours read these; the edges are the engine's."""
    written = {}
    home = {}
    for f in files:
        cx = os.path.splitext(os.path.basename(f))[0]
        with open(f, encoding="utf-8") as fh:
            text = fh.read()
        for form in forms(text):
            if not isinstance(form, list):
                continue
            for edge in genl_edges(form):
                written.setdefault(edge, cx)
            if len(form) >= 2 and form[0] == "comment" and isinstance(form[1], str):
                home.setdefault(form[1], cx)
    return written, home


# ---- spanning tree ------------------------------------------------------

def longest_depth(nodes, parents):
    """Longest path from a root to each node. Used to pick a node's *most specific*
    parent (the deepest one) as its tree edge, and shown in a node's tooltip."""
    depth = {}

    def d(n, stack):
        if n in depth:
            return depth[n]
        if n in stack:  # a genl cycle would be a bug; break it rather than recurse
            return 0
        ps = [p for p in parents.get(n, ()) if p in nodes]
        depth[n] = 0 if not ps else 1 + max(d(p, stack | {n}) for p in ps)
        return depth[n]

    for n in nodes:
        d(n, set())
    return depth


def spanning_tree(nodes, parents, depth):
    """Choose one parent per non-root node — the deepest, so a term hangs under its most
    specific generalisation — and return the roots and the ordered child lists.

    Children are ordered leaves-last and, among branchy children, larger subtrees first,
    so a parent's wide leaf fan collects on one side and the heavier subtrees balance
    toward the centre."""
    primary = {}
    roots = []
    for n in nodes:
        ps = [p for p in parents.get(n, ()) if p in nodes]
        if not ps:
            roots.append(n)
        else:
            primary[n] = max(ps, key=lambda p: (depth[p], p))

    children = collections.defaultdict(list)
    for n, p in primary.items():
        children[p].append(n)

    size = {}

    def subtree_size(n):
        if n in size:
            return size[n]
        size[n] = 1 + sum(subtree_size(c) for c in children.get(n, ()))
        return size[n]

    for n in nodes:
        subtree_size(n)

    def order(kids):
        branchy = sorted((k for k in kids if children.get(k)),
                         key=lambda k: (-size[k], k))
        leaves = sorted(k for k in kids if not children.get(k))
        return branchy + leaves

    for p in children:
        children[p] = order(children[p])
    return sorted(roots, key=lambda r: (-size[r], r)), children


# ---- geometry -----------------------------------------------------------

CHAR_W = 7.0
PAD = 12
NODE_H = 26
ROW_H = 30       # vertical pitch between two leaves of the spanning tree
COL_GAP = 46     # horizontal gap between one column's boxes and the next column's
ROOT_GAP = 2     # blank rows between separate root trees
FOLD_MIN = 4     # a parent with at least this many leaf children folds them into a grid
GRID_HGAP = 16   # horizontal gap between the columns of a folded leaf grid
FOLD_COLS = 4    # a folded leaf grid grows to at most this many columns


def node_w(label):
    return max(64, int(CHAR_W * len(label) + 2 * PAD))


def bbox(pos):
    """The (minx, maxx, miny, maxy) covering every node's box in `pos`."""
    xs0 = [x - node_w(n) / 2.0 for n, (x, y) in pos.items()]
    xs1 = [x + node_w(n) / 2.0 for n, (x, y) in pos.items()]
    ys0 = [y - NODE_H / 2.0 for n, (x, y) in pos.items()]
    ys1 = [y + NODE_H / 2.0 for n, (x, y) in pos.items()]
    return min(xs0), max(xs1), min(ys0), max(ys1)


def column_centres(nodes, depth):
    """The x centre of each depth column, spaced by the widest box in the column to its
    left so a long name never overlaps its neighbour column."""
    width = collections.defaultdict(lambda: 64)
    for n in nodes:
        width[depth[n]] = max(width[depth[n]], node_w(n))
    cx = {}
    prev = 0.0
    for d in range(max(depth.values()) + 1):
        half = width[d] / 2.0
        cx[d] = prev + half if d == 0 else prev + COL_GAP + half
        prev = cx[d] + half
    return cx


def dendrogram(roots, children, depth):
    """Assign every node an (x, y). x is its column centre (by longest depth); y is a
    tidy spanning-tree row — a leaf takes the next row, a parent sits level with the
    middle of its children. A depth-first walk visits a parent's children in a run, so
    siblings land on adjacent rows and read as one group."""
    cx = column_centres(set(depth), depth)
    y = {}
    row = [0]  # next free leaf row, boxed so the closure can advance it

    def walk(v):
        kids = children.get(v, [])
        if not kids:
            y[v] = row[0]
            row[0] += 1
        else:
            for k in kids:
                walk(k)
            y[v] = (y[kids[0]] + y[kids[-1]]) / 2.0

    for r in roots:
        walk(r)
        row[0] += ROOT_GAP

    return {n: (cx[depth[n]], y[n] * ROW_H) for n in y}


def gridfold_layout(roots, children, depth, fold_cols=FOLD_COLS):
    """The dendrogram, but a parent whose children are all leaves and number at least
    FOLD_MIN packs them into a grid of at most `fold_cols` columns to its right rather
    than one tall column. Folding the wide terminal fans (a genus and its species, a
    predicate and its properties) is what turns the portrait dendrogram into a landscape
    sheet: the fans are most of the leaves, and a grid of them is a few rows tall instead
    of a dozen."""
    cx = column_centres(set(depth), depth)
    pos = {}
    row = [0.0]  # next free row, boxed so the closure can advance it

    def cols_for(n):
        return min(fold_cols, max(1, math.ceil(math.sqrt(n))))

    def walk(v):
        kids = children.get(v, [])
        if not kids:
            a = row[0]
            row[0] += 1
            pos[v] = (cx[depth[v]], a * ROW_H)
            return a
        branchy = [k for k in kids if children.get(k)]
        leaves = [k for k in kids if not children.get(k)]
        anchors = [walk(k) for k in branchy]
        if leaves:
            cols = cols_for(len(leaves)) if len(leaves) >= FOLD_MIN else 1
            rows = math.ceil(len(leaves) / cols)
            start = row[0]
            base = cx[depth[v] + 1]
            cell = max(node_w(leaf) for leaf in leaves) + GRID_HGAP
            for i, leaf in enumerate(leaves):
                r, c = divmod(i, cols)
                pos[leaf] = (base + c * cell, (start + r) * ROW_H)
            row[0] = start + rows
            anchors.append(start + (rows - 1) / 2.0)
        a = (min(anchors) + max(anchors)) / 2.0
        pos[v] = (cx[depth[v]], a * ROW_H)
        return a

    for r in roots:
        walk(r)
        row[0] += ROOT_GAP
    return pos


def best_gridfold(roots, children, depth, target):
    """The gridfold layout over each fold width in FOLD_WIDTHS with the smallest
    `sheet_area` for `target`."""
    def area(pos):
        mnx, mxx, mny, mxy = bbox(pos)
        return sheet_area(mxx - mnx, mxy - mny, target)

    return min((gridfold_layout(roots, children, depth, cols) for cols in FOLD_WIDTHS),
               key=area)


FOLD_WIDTHS = (1, 2, 3, 4, 6, 8, 12, 16)


# ---- svg ----------------------------------------------------------------

def esc(s):
    return str(s).replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def svg(pos, depth, home, edges, margin=28, legend_cx=None):
    mnx, mxx, mny, mxy = bbox(pos)
    legend_h = 26 * (len(legend_cx) + 1) + 16 if legend_cx else 0
    w = (mxx - mnx) + 2 * margin
    h = (mxy - mny) + 2 * margin + legend_h

    def px(n):
        return pos[n][0] - mnx + margin

    def py(n):
        return pos[n][1] - mny + margin + legend_h

    out = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{int(w)}" height="{int(h)}" '
        f'viewBox="0 0 {int(w)} {int(h)}" font-family="ui-sans-serif,system-ui,sans-serif">',
        '<rect width="100%" height="100%" fill="#ffffff"/>',
        "<defs>",
    ]
    for cx, (line, _) in list(CONTEXT_COLORS.items()) + [("_fallback", FALLBACK)]:
        out.append(
            f'<marker id="ah-{cx}" viewBox="0 0 10 10" refX="9" refY="5" '
            f'markerWidth="6" markerHeight="6" orient="auto-start-reverse">'
            f'<path d="M0 0 L10 5 L0 10 z" fill="{line}"/></marker>'
        )
    out.append("</defs>")

    def colors(cx):
        return CONTEXT_COLORS.get(cx, FALLBACK)

    def marker(cx):
        return cx if cx in CONTEXT_COLORS else "_fallback"

    # edges first, so no line crosses over a node label
    for sub, sup, cx in edges:
        if sub not in pos or sup not in pos:
            continue
        line = colors(cx)[0]
        x1, y1 = px(sub), py(sub)
        x2, y2 = px(sup), py(sup)
        dx, dy = x2 - x1, y2 - y1
        if dx == 0 and dy == 0:
            continue
        # trim each endpoint to the node box edge so the arrowhead lands on the border
        for (nx, ny, node, sign) in ((x1, y1, sub, 1), (x2, y2, sup, -1)):
            hw, hh = node_w(node) / 2.0, NODE_H / 2.0
            tx = 1e9 if dx == 0 else hw / abs(dx)
            ty = 1e9 if dy == 0 else hh / abs(dy)
            t = min(tx, ty)
            if sign == 1:
                x1, y1 = nx + t * dx, ny + t * dy
            else:
                x2, y2 = nx - t * dx, ny - t * dy
        out.append(
            f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" '
            f'stroke="{line}" stroke-width="1.4" stroke-opacity="0.7" '
            f'marker-end="url(#ah-{marker(cx)})"/>'
        )

    for n, _ in pos.items():
        w0 = node_w(n)
        cx = home.get(n)
        line, fill = colors(cx)
        cxc, cyc = px(n), py(n)
        out.append(
            f'<g><title>{esc(n)}  (defined in {esc(cx or "?")}, depth {depth[n]})</title>'
            f'<rect x="{cxc - w0 / 2.0:.1f}" y="{cyc - NODE_H / 2.0:.1f}" '
            f'width="{w0}" height="{NODE_H}" rx="{NODE_H // 2}" '
            f'fill="{fill}" stroke="{line}" stroke-width="1.5"/>'
            f'<text x="{cxc:.1f}" y="{cyc + 4:.1f}" text-anchor="middle" '
            f'font-size="12" fill="#111">{esc(n)}</text></g>'
        )

    if legend_cx:
        lx, ly = margin, 20
        out.append(
            f'<text x="{lx}" y="{ly}" font-size="14" font-weight="600" fill="#111">'
            f'file — node fill = where a term is defined, edge colour = where its genl '
            f'is written</text>'
        )
        for i, cx in enumerate(legend_cx):
            line, fill = colors(cx)
            ry = ly + 12 + i * 26
            out.append(
                f'<rect x="{lx}" y="{ry}" width="34" height="18" rx="9" '
                f'fill="{fill}" stroke="{line}" stroke-width="1.5"/>'
                f'<line x1="{lx + 44}" y1="{ry + 9}" x2="{lx + 80}" y2="{ry + 9}" '
                f'stroke="{line}" stroke-width="2.4"/>'
                f'<text x="{lx + 90}" y="{ry + 13}" font-size="13" fill="#111">'
                f'{esc(cx)}</text>'
            )
    out.append("</svg>")
    return "\n".join(out)


# ---- graphviz path ------------------------------------------------------

def wrap_label(name, width):
    """`name` broken after an underscore into lines of at most `width` characters where
    its parts allow, joined by DOT's `\\n`; unchanged when `width` is 0."""
    if not width:
        return name
    lines = [""]
    for part in re.findall(r"[^_]+_?", name):
        if lines[-1] and len(lines[-1]) + len(part) > width:
            lines.append(part)
        else:
            lines[-1] += part
    return "\\n".join(lines)


def to_dot(nodes, edges, home, depth, rankdir="TB", packmode="graph", text_scale=1.0,
           wrap=0):
    """A DOT document for `dot`. General terms rank before specific ones: a genl edge is
    emitted `super -> sub [dir=back]`, so `dot` puts the super on the earlier rank and the
    arrowhead still points at the super. `packmode` arranges the separate root trees
    (Graphviz's `packmode` values); `text_scale` multiplies the label point size while the
    rank and node spacing stay fixed, so raising it enlarges the text relative to the
    layout. A `wrap` above 0 breaks each label into lines of about that many characters
    (`wrap_label`), which narrows the boxes."""
    def colors(cx):
        return CONTEXT_COLORS.get(cx, FALLBACK)

    fs = round(11 * text_scale, 1)
    out = ["digraph ontology {",
           f'  graph [rankdir={rankdir}, pack=true, packmode="{packmode}", ranksep=0.55, '
           f'nodesep=0.18, margin=0, bgcolor="white"];',
           f'  node [shape=box, style="rounded,filled", fontname="Helvetica", '
           f'fontsize={fs}, height=0.30, margin="0.09,0.03", penwidth=1.4, '
           f'fontcolor="#111"];',
           '  edge [penwidth=1.1, arrowsize=0.7];']
    for n in sorted(nodes):
        line, fill = colors(home.get(n))
        out.append(f'  "{n}" [label="{wrap_label(n, wrap)}", fillcolor="{fill}", '
                   f'color="{line}", '
                   f'tooltip="{n} — defined in {home.get(n) or "?"}, depth {depth[n]}"];')
    for sub, sup, cx in edges:
        line = colors(cx)[0]
        out.append(f'  "{sup}" -> "{sub}" [dir=back, color="{line}"];')
    out.append("}")
    return "\n".join(out)


def render_dot(dot_text, stagger=0):
    """Run `dot -Tsvg`, returning the SVG text. A `stagger` above 0 first runs
    `unflatten -l stagger -f -c stagger`, which spreads a wide fan of leaves over that many
    ranks."""
    if stagger:
        dot_text = subprocess.run(["unflatten", "-l", str(stagger), "-f", "-c", str(stagger)],
                                  input=dot_text, capture_output=True, text=True,
                                  check=True).stdout
    proc = subprocess.run(["dot", "-Tsvg"], input=dot_text, capture_output=True,
                          text=True, check=True)
    return proc.stdout


def sheet_area(w, h, target):
    """The area of the smallest sheet of aspect `target` (height / width) holding a w × h
    drawing, or the drawing's own area when `target` is None. Every engine keeps the
    candidate layout with the smallest: the labels are one size in every candidate, so
    the smallest sheet is the one that shows them largest when it is scaled to a page or
    window of that shape."""
    return w * h if target is None else max(w, h / target) * max(h, w * target)


def best_dot(nodes, edges, home, depth, target, text_scale, rankdirs=None, roots=1):
    """Lay out every candidate in `rankdirs` (default RANKDIRS) × WRAPS × STAGGERS, and
    × PACKMODES when there is more than one root tree, and return the SVG of the one
    with the smallest `sheet_area`. No layout is stretched toward `target`. Returns None
    when Graphviz is not installed."""
    if not shutil.which("dot"):
        return None
    staggers = STAGGERS if shutil.which("unflatten") else (0,)
    packmodes = PACKMODES if roots > 1 else PACKMODES[:1]
    best = None
    for rankdir in rankdirs or RANKDIRS:
        for packmode in packmodes:
            for wrap in WRAPS:
                text = to_dot(nodes, edges, home, depth, rankdir, packmode, text_scale, wrap)
                for stagger in staggers:
                    doc = render_dot(text, stagger)
                    w, h = map(float, re.search(
                        r'viewBox="[\d.]+ [\d.]+ ([\d.]+) ([\d.]+)"', doc).groups())
                    sheet = sheet_area(w, h, target)
                    if best is None or sheet < best[0]:
                        best = (sheet, doc)
    return best[1]


RANKDIRS = ("TB", "LR")
DIRECTIONS = {"auto": RANKDIRS, "down": ("TB",), "right": ("LR",)}
PACKMODES = ("graph", "array_c2", "array_c3", "array_c4", "array_c6")
STAGGERS = (0, 2, 4)
WRAPS = (0, 16, 10)


def fit_to_window(svg_text):
    """Size the root element in a browser to cover its window: the drawing scales until
    it fills both window axes, so its shorter side fills the window and the longer side
    scrolls. The width and height attributes stay for tools that read no CSS."""
    m = re.search(r'<svg\b[^>]*?viewBox="[\d.]+ [\d.]+ ([\d.]+) ([\d.]+)"', svg_text)
    if not m:
        return svg_text
    aspect = float(m.group(1)) / float(m.group(2))
    style = (f'style="display:block; width:max(100vw, {aspect:.4f} * 100vh); '
             f'height:max(100vh, 100vw / {aspect:.4f})"')
    return svg_text.replace("<svg ", f"<svg {style} ", 1)


def inject_legend(svg_text, legend_cx, scale=1.0):
    """Add the colour legend above a `dot`-produced SVG: grow the canvas by a top band,
    shift the drawing down into the space below it, and draw one swatch and line per
    context. Operates on the SVG text so the legend lands in pixel space, not in the
    graph's own scaled and translated coordinate system. `scale` matches the legend to
    the drawing's `text_scale` so it stays the same visual size as a node label."""
    def colors(cx):
        return CONTEXT_COLORS.get(cx, FALLBACK)

    def s(v):
        return round(v * scale, 1)

    row = s(26)
    band = row * (len(legend_cx) + 1) + s(20)
    m = re.search(r'<svg\s[^>]*width="([\d.]+)pt"\s+height="([\d.]+)pt"'
                  r'[^>]*viewBox="([\d.\s]+)"', svg_text)
    if not m:
        return svg_text
    w, h = float(m.group(1)), float(m.group(2))
    vb = [float(v) for v in m.group(3).split()]
    new = svg_text.replace(f'width="{m.group(1)}pt" height="{m.group(2)}pt"',
                           f'width="{w:.0f}pt" height="{h + band:.0f}pt"', 1)
    new = new.replace(f'viewBox="{m.group(3)}"',
                      f'viewBox="{vb[0]} {vb[1]} {vb[2]} {vb[3] + band}"', 1)
    # shift the graph body down by the band, then draw the legend in the freed top strip
    new = re.sub(r'(<g id="graph0")', rf'<g transform="translate(0,{band})">\1', new, count=1)
    new = new.replace("</svg>", "</g></svg>", 1)

    leg = [f'<rect x="0" y="0" width="{vb[2]}" height="{band}" fill="white"/>',
           f'<text x="{s(14)}" y="{s(22)}" font-family="Helvetica" font-size="{s(15)}" '
           f'font-weight="700" fill="#111">file — node fill = where a term is defined, '
           f'edge colour = where its genl is written</text>']
    for i, cx in enumerate(legend_cx):
        line, fill = colors(cx)
        ry = s(34) + i * row
        leg.append(
            f'<rect x="{s(14)}" y="{ry}" width="{s(34)}" height="{s(18)}" rx="{s(9)}" '
            f'fill="{fill}" stroke="{line}" stroke-width="1.5"/>'
            f'<line x1="{s(58)}" y1="{ry + s(9)}" x2="{s(96)}" y2="{ry + s(9)}" '
            f'stroke="{line}" stroke-width="{s(2.6)}"/>'
            f'<text x="{s(106)}" y="{ry + s(13)}" font-family="Helvetica" '
            f'font-size="{s(13)}" fill="#111">{cx}</text>')
    return new.replace("</svg>", "".join(leg) + "</svg>", 1)


# ---- icicle -------------------------------------------------------------

def icicle_svg(roots, children, depth, home, edges, legend_cx, ratio, leaf_h=17,
               margin=24):
    """A space-filling partition of the spanning tree. Depth is the column; a node's box
    is as tall as the leaves under it, so the picture fills a rectangle with no edge
    whitespace. A leaf's box stretches to the right margin, giving its label room. Tree
    edges are the shared borders between columns; the multiple-inheritance genl edges the
    tree left out are drawn as faint curves in the writing context's colour, so the
    cross-context placement is still visible."""
    def colors(cx):
        return CONTEXT_COLORS.get(cx, FALLBACK)

    leafcount = {}

    def count(v):
        ch = children.get(v, [])
        leafcount[v] = 1 if not ch else sum(count(c) for c in ch)
        return leafcount[v]

    total = sum(count(r) for r in roots)
    ncols = max(depth.values()) + 1
    band = 26 * (len(legend_cx) + 1) + 20
    height = total * leaf_h
    width = height / (ratio or 0.62)
    colw = width / ncols

    boxes = {}  # node -> (x0, y0, x1, y1)

    def place(v, y0, y1):
        x0 = depth[v] * colw
        x1 = width if not children.get(v) else x0 + colw  # leaves fill to the right edge
        boxes[v] = (x0, y0, x1, y1)
        cy = y0
        for c in children.get(v, []):
            ch_h = (y1 - y0) * leafcount[c] / leafcount[v]
            place(c, cy, cy + ch_h)
            cy += ch_h

    cy = 0.0
    for r in roots:
        rh = height * leafcount[r] / total
        place(r, cy, cy + rh)
        cy += rh

    out = [f'<svg xmlns="http://www.w3.org/2000/svg" '
           f'width="{width + 2 * margin:.0f}" height="{height + 2 * margin + band:.0f}" '
           f'viewBox="0 0 {width + 2 * margin:.0f} {height + 2 * margin + band:.0f}" '
           f'font-family="Helvetica,system-ui,sans-serif">',
           '<rect width="100%" height="100%" fill="#ffffff"/>']

    def X(x):
        return x + margin

    def Y(y):
        return y + margin + band

    # faint overlays for the genl edges the spanning tree left out (multiple inheritance)
    drawn_tree = {(c, p) for p in children for c in children[p]}
    for sub, sup, cx in edges:
        if sub not in boxes or sup not in boxes or (sub, sup) in drawn_tree:
            continue
        sx0, sy0, sx1, sy1 = boxes[sub]
        px0, py0, px1, py1 = boxes[sup]
        x1v, y1v = X(sx0), Y((sy0 + sy1) / 2)
        x2v, y2v = X(px1), Y((py0 + py1) / 2)
        mx = (x1v + x2v) / 2
        out.append(
            f'<path d="M{x1v:.1f},{y1v:.1f} C{mx:.1f},{y1v:.1f} {mx:.1f},{y2v:.1f} '
            f'{x2v:.1f},{y2v:.1f}" fill="none" stroke="{colors(cx)[0]}" '
            f'stroke-width="1.1" stroke-opacity="0.5"/>')

    # boxes, deepest last so a child's border sits over its parent's
    for n in sorted(boxes, key=lambda n: depth[n]):
        x0, y0, x1, y1 = boxes[n]
        line, fill = colors(home.get(n))
        bx, by, bw, bh = X(x0) + 1, Y(y0) + 1, (x1 - x0) - 2, (y1 - y0) - 2
        if bh <= 0 or bw <= 0:
            continue
        out.append(f'<rect x="{bx:.1f}" y="{by:.1f}" width="{bw:.1f}" height="{bh:.1f}" '
                   f'rx="3" fill="{fill}" stroke="{line}" stroke-width="1"/>')
        if bh >= 9:  # a cell too short for a line of text carries only its colour
            fs = min(13, bh - 3)
            out.append(f'<title>{esc(n)} — defined in {esc(home.get(n) or "?")}, '
                       f'depth {depth[n]}</title>'
                       f'<text x="{bx + 5:.1f}" y="{by + bh / 2 + fs / 2 - 1.5:.1f}" '
                       f'font-size="{fs:.0f}" fill="#111">{esc(n)}</text>')

    lx = margin
    out.append(f'<text x="{lx}" y="20" font-size="15" font-weight="700" fill="#111">'
               f'file — box fill = where a term is defined; faint curve = a '
               f'multiple-inheritance genl, coloured by where it is written</text>')
    for i, cx in enumerate(legend_cx):
        line, fill = colors(cx)
        ry = 32 + i * 26
        out.append(f'<rect x="{lx}" y="{ry}" width="34" height="18" rx="4" fill="{fill}" '
                   f'stroke="{line}" stroke-width="1.2"/>'
                   f'<text x="{lx + 44}" y="{ry + 13}" font-size="13" fill="#111">'
                   f'{cx}</text>')
    out.append("</svg>")
    return "\n".join(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--out", default="-", help="SVG output path, or - for stdout")
    ap.add_argument("--engine",
                    choices=["auto", "dot", "gridfold", "icicle", "dendrogram"],
                    default="auto",
                    help="auto uses Graphviz dot when present, else gridfold; gridfold "
                    "and icicle and dendrogram are the built-in, dependency-free layouts")
    ap.add_argument("--ratio", type=float, default=None,
                    help="height / width of the page or window to fill (0.72 for "
                    "landscape): dot and gridfold keep the candidate that shows the labels "
                    "largest on it, icicle draws to it; omitted, the smallest drawing wins")
    ap.add_argument("--direction", choices=sorted(DIRECTIONS), default="auto",
                    help="dot: down roots the tree at the top, right at the left; auto "
                    "keeps whichever is more compact for --ratio")
    ap.add_argument("--text-scale", type=float, default=1.0,
                    help="dot only: multiply label point size (raise to read a chosen ratio)")
    ap.add_argument("--include-middle", action="store_true",
                    help="load the starter (upper + resources/kb/middle) instead of upper")
    ap.add_argument("--predicates", action="store_true",
                    help="also draw the genl components outside thing, which relate "
                    "predicates")
    ap.add_argument("--all-edges", action="store_true",
                    help="draw every direct genl edge, not only the transitive reduction")
    args = ap.parse_args()

    files = kb_files(args.include_middle)
    written, home = parse(files)
    edges = [(sub, sup, written.get((sub, sup)))
             for sub, sup, minimal in engine_edges(files, args.include_middle,
                                                   args.predicates)
             if minimal or args.all_edges]

    nodes = set()
    for a, b, _ in edges:
        nodes.add(a)
        nodes.add(b)
    for n in nodes:
        home.setdefault(n, None)

    parents = collections.defaultdict(set)
    for a, b, _ in edges:
        parents[a].add(b)

    depth = longest_depth(nodes, parents)

    seen = {home[n] for n in nodes if home.get(n)} | {cx for _, _, cx in edges if cx}
    legend_cx = [c for c in CONTEXT_COLORS if c in seen] + sorted(
        c for c in seen if c not in CONTEXT_COLORS)

    doc = None
    used = args.engine
    if args.engine in ("auto", "dot"):
        doc = best_dot(nodes, edges, home, depth, args.ratio, args.text_scale,
                       DIRECTIONS[args.direction], sum(1 for n in nodes if not parents[n]))
        if doc is None and args.engine == "dot":
            sys.exit("dot: Graphviz is not installed (try --engine gridfold)")
        if doc is not None:
            doc = inject_legend(doc, legend_cx, args.text_scale)
            used = "dot"
    if doc is None:  # auto fell back, or a built-in engine was asked for
        roots, children = spanning_tree(nodes, parents, depth)
        if args.engine == "icicle":
            doc = icicle_svg(roots, children, depth, home, edges, legend_cx, args.ratio)
            used = "icicle"
        elif args.engine == "dendrogram":
            doc = svg(dendrogram(roots, children, depth), depth, home, edges,
                      legend_cx=legend_cx)
            used = "dendrogram"
        else:  # gridfold, and the auto fallback
            doc = svg(best_gridfold(roots, children, depth, args.ratio), depth, home, edges,
                      legend_cx=legend_cx)
            used = "gridfold"
    doc = fit_to_window(doc)

    if args.out == "-":
        sys.stdout.write(doc)
    else:
        os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)
        with open(args.out, "w", encoding="utf-8") as fh:
            fh.write(doc)
        print(f"wrote {args.out} [{used}]: {len(nodes)} nodes, {len(edges)} genl edges",
              file=sys.stderr)


if __name__ == "__main__":
    main()
