#!/usr/bin/env python3
"""scripts/check-derived-state.py — every piece of state the engine keeps has a register row.

`vaelii.impl.caches/register-derived` is the derived-state register (docs/caches.md):
each row declares its key, what it reads and the write events that retire it.  A
structure without a row is one no test checks against the writes that move it.  This
check fails on two kinds of unregistered state:

  - a top-level `defonce` under `src/vaelii/impl/`, or a top-level `def` whose value is
    an atom, a volatile or a `java.util.concurrent` structure, that no
    `register-derived` or `register-cache` form in the same file names as `#'name`;
  - a field of the `Reasoning` record (`vaelii.impl.types.reasoning`) that no
    `register-derived` form locates with `:at [[:field …]]`;
  - a row id in `scripts/derived-state-features.edn` that no `register-derived` form
    declares, or one that two features name;
  - a `register-derived` form with no `:holds-content? true|false`, or one declaring
    true that `HOLDS_CONTENT` does not name: such a row holds a sentence the KB holds or
    would hold outside every store (docs/nmtms.md, "3. Separated state");
  - a row of kind `:index` or `:cache`, computed at the write or the settle, whose
    `:reads` do not reach M1 and whose namespace does not implement `IndexStore`, that
    `OUTSIDE_INDEX` does not name: such a row keeps a belief-free index outside the
    IndexStore (the same section).

The keys inside a field that holds several rows' entries (`:taxonomy`,
`:nogood-candidates`) are written from many namespaces under keys that
are partly data (a reader), so `derived_state_test` checks them at run time instead.

State that is not derived from the KB's knowledge (instrumentation, storage spaces,
locks, configuration, warning flags, native handles) is named in `NOT_DERIVED` below
with the reason.  An entry there that names no stateful def, or one that is registered,
fails too, so the list cannot go stale.

    scripts/check-derived-state.py     # exit 1 on a finding
"""

from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
IMPL = ROOT / "src" / "vaelii" / "impl"
REASONING = IMPL / "types" / "reasoning.clj"
FEATURES = ROOT / "scripts" / "derived-state-features.edn"

# `(file relative to src/vaelii/impl, var or Reasoning field) -> reason`.
NOT_DERIVED: dict[tuple[str, str], str] = {
    ("asp/clingo.clj", "lib"): "the native clingo library handle",
    ("asp/solver.clj", "clasp-usable"): "a probe of the environment for the clasp binary",
    ("asp/solver.clj", "clingo-verdict"): "whether the native clingo library loads",
    ("asp/solver.clj", "clingo-vm-error-logged?"): "a one-time warning flag",
    ("budget.clj", "running"): "a count of the metered reads running",
    ("caches.clj", "derived"): "the derived-state register itself",
    ("caches.clj", "registry"): "the cache register itself",
    ("caches.clj", "the-profile"): "configuration: the cache scale, pressure and pins",
    ("caches.clj", "guard"): "the memory-pressure guard's listener state",
    ("caches.clj", "guard-lifecycle"): "a lock",
    ("caches.clj", "tallying"): "instrumentation: the derived-state event instrument's state",
    ("columnar.clj", "state-spaces"): "storage: the columnar index spaces",
    ("dense_kv.clj", "index-spaces"): "storage: the dense index spaces",
    ("disk/backend.clj", "stores"): "storage: the open disk stores by directory",
    ("disk/durability.clj", "registry"): "storage lifecycle: the stores the daemon syncs",
    ("disk/durability.clj", "next-id"): "storage lifecycle: a registration counter",
    ("disk/durability.clj", "scheduler"): "storage lifecycle: the sync executor",
    ("disk/durability.clj", "shutdown-hook"): "storage lifecycle: the JVM shutdown hook",
    ("disk/durability.clj", "compaction-executor"): "storage lifecycle: the compaction executor",
    ("disk/durability.clj", "compaction-in-flight"): "storage lifecycle: the stores compacting",
    ("disk/durability.clj", "last-compact-check-ms"): "storage lifecycle: the compaction throttle",
    ("disk/durability.clj", "compaction-paused"): "storage lifecycle: the pause count",
    ("disk/durability.clj", "compaction-stopped"): "storage lifecycle: the stop flag",
    ("disk/durability.clj", "lifecycle"): "a lock",
    ("disk/durability.clj", "quiescence"): "a lock",
    ("disk/files.clj", "dir-fsync-warned"): "a one-time warning flag",
    ("disk/index_snapshot.clj", "image-state"): "the write cadence of the index image",
    ("disk/lock.clj", "held"): "the directory locks this process holds",
    ("disk/record_store.clj", "rewrite-barrier"): "a test hook inside compaction",
    ("except.clj", "route-reach"): "the fact-relation walk `vaelii.impl.inherit` installs",
    ("except.clj", "firing-reach"): "the backward claim search `vaelii.impl.inherit` installs",
    ("feed.clj", "dispatch"): "the renderer `vaelii.core` installs",
    ("foreign.clj", "registered"): "configuration: the reader formats registered in code",
    ("io/frames.clj", "open-readers"): "resource lifecycle: the frame readers to close",
    ("io/thaw.clj", "installed"): "the thaw allowlist hook",
    ("io/thaw.clj", "original-read-record"): "the thaw allowlist hook",
    ("io/thaw.clj", "original-read-deftype"): "the thaw allowlist hook",
    ("kb.clj", "default-ram-space-opens"): "a one-time warning counter",
    ("logging.clj", "dial"): "configuration: the log level",
    ("memory.clj", "record-spaces"): "storage: the in-memory record spaces",
    ("memory.clj", "record-counters"): "storage: the in-memory handle counters",
    ("memory.clj", "index-spaces"): "storage: the in-memory index spaces",
    ("memory.clj", "engine-space-seq"): "a private space id counter",
    ("naming.clj", "advised"): "a one-time warning set",
    ("observe.clj", "holds"): "the open belief holds by token, the lifecycle of M3",
    ("observe.clj", "neighbour-hits"): "instrumentation: R7's process counters",
    ("observe.clj", "neighbour-misses"): "instrumentation: R7's process counters",
    ("observe.clj", "on-add"): "the store observer hooks R9 installs",
    ("observe.clj", "on-remove"): "the store observer hooks R9 installs",
    ("oplog.clj", "dispatch"): "the oplog's replay table",
    ("profile.clj", "tally"): "instrumentation: the profiler",
    ("rete.clj", "reg-queue"): "the reference queue R9's weak keys are purged through",
    ("settle_phases.clj", "clock"): "instrumentation: the settle phase clock",
    ("types/reasoning.clj", "violations"): "a report ledger of what writes exposed, read by no derivation",
    ("types/reasoning.clj", "settle-stats"): "instrumentation: settle pass counts",
    ("types/reasoning.clj", "chain-stats"): "instrumentation: chaining run counts",
}

# `row id -> what its entries hold`: the rows still holding KB content outside the KB.
# An entry leaves when its row's content becomes stored sentexes; an entry naming a row
# that does not declare `:holds-content? true` fails, so the list only shrinks.
HOLDS_CONTENT: dict[str, str] = {
    "S5": "refused firings and the `:constraint`, `:lift` and `:mint` entries",
}

# `row id -> what it indexes`: the rows still holding a belief-free index outside the
# IndexStore.  Same shrink-only rule as HOLDS_CONTENT.
OUTSIDE_INDEX: dict[str, str] = {
    "R9": "the rete matcher's facts by functor and argument, held only under "
          "`VAELII_RETE=1` or `rete/track!`",
}

# The row whose entries are the beliefs; a row reading it, directly or through other
# rows, reads belief.
BELIEF_ROW = "M1"

STATEFUL_DEF_BODY = re.compile(
    r"^\s*\((?:atom|volatile!|observe/held-atom|held-atom|ref|agent)\b"
    r"|^\s*\((?:java\.util\.concurrent\.[\w.$]+|Atomic\w+|ConcurrentHashMap|WeakHashMap|"
    r"java\.util\.WeakHashMap|java\.util\.LinkedHashMap|LinkedHashMap)\.")
REGISTER = re.compile(r"\((?:caches/)?register-(?:derived|cache)\b")
DERIVED = re.compile(r"\((?:caches/)?register-derived\s+\{:id\s+:([A-Z]+\d+)\b")
HOLDS = re.compile(r":holds-content\?\s+(true|false)\b")
READS = re.compile(r":reads\s+\[([^\]]*)\]")
KIND = re.compile(r":kind\s+:([\w-]+)")
COMPUTED = re.compile(r":computed\s+:([\w-]+)")
INDEX_STORE_IMPL = re.compile(r"^\s*p/IndexStore\s*$", re.M)


def top_level_forms(text: str):
    """Yield `(start, end)` spans of the top-level forms in `text`, skipping strings,
    character literals and comments when counting brackets."""
    i, n, depth, start = 0, len(text), 0, None
    while i < n:
        c = text[i]
        if c == ";":
            while i < n and text[i] != "\n":
                i += 1
            continue
        if c == "\\" and i + 1 < n:
            i += 2
            continue
        if c == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
            continue
        if c in "([{":
            if depth == 0:
                start = i
            depth += 1
        elif c in ")]}":
            depth -= 1
            if depth == 0 and start is not None:
                yield start, i + 1
                start = None
        i += 1


def skip_meta(s: str, i: int) -> int:
    """The index past whitespace and any `^meta` forms at `i`."""
    while True:
        while i < len(s) and s[i].isspace():
            i += 1
        if i < len(s) and s[i] == "^":
            i += 1
            if i < len(s) and s[i] == "{":
                for a, b in top_level_forms(s[i:]):
                    i += b
                    break
            else:
                while i < len(s) and not s[i].isspace():
                    i += 1
            continue
        return i


def def_name_and_body(form: str):
    """`(head, name, body)` of a top-level `def`/`defonce`, or None."""
    m = re.match(r"\((defonce|def)\s", form)
    if not m:
        return None
    i = skip_meta(form, m.end())
    j = i
    while j < len(form) and not form[j].isspace() and form[j] not in "()":
        j += 1
    name = form[i:j]
    body = form[j:]
    # a docstring between the name and the value
    k = skip_meta(body, 0)
    if body[k:k + 1] == '"':
        k += 1
        while k < len(body) and body[k] != '"':
            k += 2 if body[k] == "\\" else 1
        body = body[k + 1:]
    return m.group(1), name, body


def main() -> int:
    findings: list[str] = []
    stateful: dict[tuple[str, str], str] = {}
    registered_vars: set[tuple[str, str]] = set()
    located_fields: set[str] = set()
    row_ids: set[str] = set()
    content_rows: set[str] = set()
    # row id -> (file:line, reads, kind, computed, owner implements IndexStore)
    rows: dict[str, tuple[str, list[str], str, str, bool]] = {}

    for path in sorted(IMPL.rglob("*.clj")):
        rel = str(path.relative_to(IMPL))
        text = path.read_text()
        index_store = bool(INDEX_STORE_IMPL.search(text))
        for a, b in top_level_forms(text):
            form = text[a:b]
            line = text.count("\n", 0, a) + 1
            d = def_name_and_body(form)
            if d:
                head, name, body = d
                if head == "defonce" or STATEFUL_DEF_BODY.search(body):
                    stateful[(rel, name)] = f"{rel}:{line}"
            for rid in DERIVED.findall(form):
                row_ids.add(rid)
                reads, kind, computed = READS.search(form), KIND.search(form), COMPUTED.search(form)
                rows[rid] = (f"{rel}:{line}",
                             re.findall(r":([\w-]+)", reads.group(1)) if reads else [],
                             kind.group(1) if kind else "", computed.group(1) if computed else "",
                             index_store)
                h = HOLDS.search(form)
                if not h:
                    findings.append(f"{rel}:{line}: row {rid} declares no "
                                    f"`:holds-content? true|false`")
                elif h.group(1) == "true":
                    content_rows.add(rid)
                    if rid not in HOLDS_CONTENT:
                        findings.append(f"{rel}:{line}: row {rid} holds KB content outside "
                                        f"the KB (`:holds-content? true`), and is not in "
                                        f"HOLDS_CONTENT")
            if REGISTER.search(form):
                for v in re.findall(r"#'([\w.*+!?<>=/-]+)", form):
                    registered_vars.add((rel, v.split("/")[-1]))
                for at in re.finditer(r":at\s*\[", form):
                    span = next(top_level_forms(form[at.end() - 1:]), None)
                    if span:
                        vec = form[at.end() - 1:at.end() - 1 + span[1]]
                        located_fields.update(re.findall(r"\[\s*:([\w-]+)", vec[1:]))

    rec = re.search(r"\(defrecord\s+Reasoning\s+\[([^\]]*)\]", REASONING.read_text())
    fields = rec.group(1).split() if rec else []
    if not fields:
        findings.append("types/reasoning.clj: no `defrecord Reasoning` field vector found")

    for key, where in sorted(stateful.items()):
        if key in registered_vars or key in NOT_DERIVED:
            continue
        findings.append(f"{where}: `{key[1]}` holds state and has no register row "
                        f"(`caches/register-derived` naming #'{key[1]}), and is not in "
                        f"NOT_DERIVED")
    for f in fields:
        if f in located_fields or ("types/reasoning.clj", f) in NOT_DERIVED:
            continue
        findings.append(f"types/reasoning.clj: Reasoning field `{f}` has no register row "
                        f"locating it (`:at [[:{f} …]]`), and is not in NOT_DERIVED")
    for key in sorted(NOT_DERIVED):
        if key[0] == "types/reasoning.clj":
            if key[1] not in fields:
                findings.append(f"NOT_DERIVED names `{key[1]}`, which is no Reasoning field")
            elif key[1] in located_fields:
                findings.append(f"NOT_DERIVED names `{key[1]}`, which a register row locates")
        elif key not in stateful:
            findings.append(f"NOT_DERIVED names {key[0]} `{key[1]}`, which is no stateful def")
        elif key in registered_vars:
            findings.append(f"NOT_DERIVED names {key[0]} `{key[1]}`, which is registered")

    findings.extend(f"HOLDS_CONTENT names {r}, which no row declaring "
                    f"`:holds-content? true` is" for r in sorted(HOLDS_CONTENT)
                    if r not in content_rows)

    def reads_belief(rid: str, seen: frozenset = frozenset()) -> bool:
        return rid == BELIEF_ROW or (rid in rows and rid not in seen and any(
            reads_belief(r, seen | {rid}) for r in rows[rid][1]))

    outside: set[str] = set()
    for rid, (where, reads, kind, computed, index_store) in sorted(rows.items()):
        if (kind in ("index", "cache") and computed in ("write", "settle")
                and rid not in content_rows and not index_store
                and not reads_belief(rid)):
            outside.add(rid)
            if rid not in OUTSIDE_INDEX:
                findings.append(f"{where}: row {rid} keeps a belief-free index at the write "
                                f"outside the IndexStore, and is not in OUTSIDE_INDEX "
                                f"(docs/nmtms.md, \"3. Separated state\")")
    findings.extend(f"OUTSIDE_INDEX names {r}, which is no belief-free index kept outside "
                    f"the IndexStore" for r in sorted(OUTSIDE_INDEX) if r not in outside)

    featured: dict[str, int] = {}
    for vec in re.findall(r":rows\s*\[([^\]]*)\]", re.sub(r";[^\n]*", "", FEATURES.read_text())):
        for r in re.findall(r":([\w-]+)", vec):
            featured[r] = featured.get(r, 0) + 1
            if r not in row_ids:
                findings.append(f"{FEATURES.relative_to(ROOT)}: `:{r}` is no register row")
    findings.extend(f"{FEATURES.relative_to(ROOT)}: `:{r}` is in {n} features"
                    for r, n in sorted(featured.items()) if n > 1)

    for f in findings:
        print(f)
    regd = sum(1 for k in stateful if k in registered_vars)
    allowed = sum(1 for k in stateful if k in NOT_DERIVED)
    print(f"derived-state: {len(stateful)} stateful defs ({regd} registered, "
          f"{allowed} not derived), {len(fields)} Reasoning fields, "
          f"{len(row_ids)} rows ({len(content_rows)} holding content, "
          f"{len(outside)} indexing outside the IndexStore), "
          f"{len(featured)} in a feature, "
          f"{len(findings)} findings")
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
