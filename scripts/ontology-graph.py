#!/usr/bin/env python3
# SPDX-License-Identifier: SSPL-1.0
# Copyright © 2026 Vaelii LLC and the Vaelii contributors.
"""Draw the upper-ontology genl graph as one standalone SVG.

Reads the KB authoring surface (the `resources/kb/*.txt` files) directly, the same
surface the placement tests reason over, and emits an is-a diagram:

  - one node per type that appears in a `(genl sub super)`,
  - one edge per `(genl sub super)`, arrow pointing at the more general `super`,
  - node fill tinted by the file the term is *defined* in (its `(comment term …)`),
  - edge colour set by the file the `genl` is *written* in.

An edge whose colour differs from its child node's fill is a genl written in a file
other than the one that documents its subject.

Four layout engines, none required to be installed:

  - dot        Graphviz ranks the DAG general-at-top and minimises crossings; fitted to
               a landscape sheet by --ratio, label size set by --text-scale. Widest,
               because dot spreads each rank of leaves across a row.
  - gridfold   a left-to-right dendrogram whose wide terminal fans fold into grids, so
               the leaves stack instead of stretching; landscape, keeps arrows and the
               edge-context colours, no dependency. The auto fallback when dot is absent.
  - icicle     a space-filling partition: depth is the column, a box is as tall as the
               leaves under it, leaves reach the right edge. Fills the sheet; tree edges
               become shared borders and only the multiple-inheritance genl draw.
  - dendrogram the plain left-to-right tree, portrait (about as tall as it has leaves).

Parsing the text is enough because every genl line is a single ground `(genl sub super)`;
no KB is booted by any engine.

Usage:
  scripts/ontology-graph.py [--out FILE] [--include-middle] [--include CX ...]
  scripts/ontology-graph.py --engine {auto,dot,gridfold,icicle,dendrogram}
  scripts/ontology-graph.py --engine dot --ratio 0.72 --text-scale 1.4
  scripts/ontology-graph.py --engine gridfold --out target/upper.svg

`--ratio` chooses the layout's shape and `--text-scale` its label size independently:
pick the aspect you want to print, then raise the text scale until the labels read.
The two compose because label text grows against the fixed rank and node spacing, so a
larger scale is a larger share of the ink and survives the fit-to-page shrink.
"""
import argparse
import collections
import glob
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

GENL_RE = re.compile(r"\(genl\s+(\S+)\s+([^\s)]+)\)\s*$")
COMMENT_RE = re.compile(r"\(comment\s+(\S+)\s")


def kb_files(include_middle, extra):
    """The .txt files to read: every upper file, `core.txt` first, then optionally middle,
    then any explicit `extra` context names."""
    files = [os.path.join(REPO, "resources/kb/upper/core.txt")]
    files += sorted(f for f in glob.glob(os.path.join(REPO, "resources/kb/upper/*.txt"))
                    if os.path.basename(f) != "core.txt")
    if include_middle:
        files += sorted(glob.glob(os.path.join(REPO, "resources/kb/middle/*.txt")))
    for cx in extra:
        p = os.path.join(REPO, "resources/kb", cx + ".txt")
        if os.path.exists(p):
            files.append(p)
        elif os.path.exists(os.path.join(REPO, "resources/kb/upper", cx + ".txt")):
            files.append(os.path.join(REPO, "resources/kb/upper", cx + ".txt"))
    return files


def parse(files):
    """Return (edges, home). `edges` is a list of (sub, super, context); `home` maps a
    term to the context of its first `(comment term …)`."""
    edges = []
    home = {}
    for f in files:
        cx = os.path.splitext(os.path.basename(f))[0]
        with open(f, encoding="utf-8") as fh:
            for line in fh:
                m = GENL_RE.match(line)
                if m:
                    edges.append((m.group(1), m.group(2), cx))
                    continue
                c = COMMENT_RE.match(line)
                if c:
                    home.setdefault(c.group(1), cx)
    return edges, home


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


def gridfold_layout(roots, children, depth):
    """The dendrogram, but a parent whose children are all leaves and number at least
    FOLD_MIN packs them into a grid to its right rather than one tall column. Folding the
    wide terminal fans (a genus and its species, a predicate and its properties) is what
    turns the portrait dendrogram into a landscape sheet: the fans are most of the leaves,
    and a grid of them is a few rows tall instead of a dozen."""
    cx = column_centres(set(depth), depth)
    pos = {}
    row = [0.0]  # next free row, boxed so the closure can advance it

    def cols_for(n):
        return min(FOLD_COLS, max(1, math.ceil(math.sqrt(n))))

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

def to_dot(nodes, edges, home, depth, ratio, text_scale=1.0):
    """A DOT document for `dot`. General terms rank above specific ones: a genl edge is
    emitted `super -> sub [dir=back]`, so `dot` puts the super on the higher rank and the
    arrowhead still points at the super. `ratio` (height / width) fits the drawing to a
    landscape sheet; `text_scale` multiplies the label point size while the rank and node
    spacing stay fixed, so raising it enlarges the text relative to the layout."""
    def colors(cx):
        return CONTEXT_COLORS.get(cx, FALLBACK)

    fs = round(11 * text_scale, 1)
    ratio_attr = "" if ratio in ("none", "", None) else f"ratio={ratio}, "
    out = ["digraph ontology {",
           f'  graph [rankdir=TB, {ratio_attr}ranksep=0.55, nodesep=0.18, '
           f'margin=0, bgcolor="white"];',
           f'  node [shape=box, style="rounded,filled", fontname="Helvetica", '
           f'fontsize={fs}, height=0.30, margin="0.09,0.03", penwidth=1.4, '
           f'fontcolor="#111"];',
           '  edge [penwidth=1.1, arrowsize=0.7];']
    for n in sorted(nodes):
        line, fill = colors(home.get(n))
        out.append(f'  "{n}" [fillcolor="{fill}", color="{line}", '
                   f'tooltip="{n} — defined in {home.get(n) or "?"}, depth {depth[n]}"];')
    for sub, sup, cx in edges:
        line = colors(cx)[0]
        out.append(f'  "{sup}" -> "{sub}" [dir=back, color="{line}"];')
    out.append("}")
    return "\n".join(out)


def render_dot(dot_text):
    """Run `dot -Tsvg`, returning the SVG text, or None when Graphviz is not installed."""
    if not shutil.which("dot"):
        return None
    proc = subprocess.run(["dot", "-Tsvg"], input=dot_text, capture_output=True,
                          text=True, check=True)
    return proc.stdout


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
    ratio_f = 0.62 if ratio in ("none", "", None) else float(ratio)
    width = height / ratio_f
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
    ap.add_argument("--ratio", default="0.72",
                    help="dot/icicle: drawing height / width, ~0.72 for a landscape sheet")
    ap.add_argument("--text-scale", type=float, default=1.0,
                    help="dot only: multiply label point size (raise to read a chosen ratio)")
    ap.add_argument("--include-middle", action="store_true",
                    help="also read resources/kb/middle/*.txt")
    ap.add_argument("--include", nargs="*", default=[],
                    help="extra files to read, by path under resources/kb without .txt (e.g. koinii/CxRegistry)")
    args = ap.parse_args()

    files = kb_files(args.include_middle, args.include)
    edges, home = parse(files)

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

    seen = {home[n] for n in nodes if home.get(n)} | {cx for _, _, cx in edges}
    legend_cx = [c for c in CONTEXT_COLORS if c in seen] + sorted(
        c for c in seen if c not in CONTEXT_COLORS)

    doc = None
    used = args.engine
    if args.engine in ("auto", "dot"):
        doc = render_dot(to_dot(nodes, edges, home, depth, args.ratio, args.text_scale))
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
            doc = svg(gridfold_layout(roots, children, depth), depth, home, edges,
                      legend_cx=legend_cx)
            used = "gridfold"

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
