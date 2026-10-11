#!/usr/bin/env bash
# scripts/perf-ab.sh — `lein perf-ab <base-rev>`: the working tree against an older
# revision, in absolute time, on this machine and this JDK.
#
# `lein perf` gates the growth of a cost between two sizes, so a cost added to every
# operation moves both readings and passes; `test/vaelii/assert_cost_test.clj` counts
# index operations, so a slower operation that reads no more of the index passes too.
# This is the check for that class: the probes in `vaelii.bench.ab`, run in fresh JVMs
# alternating base and head, and judged by the paired ratio head/base.
#
# The base is `git archive`d into `testbench/perf-ab/<hash>/` (kept for the next run)
# and the head's `bench/vaelii/bench/ab.clj` is copied over its own, so both sides time
# the same probe code.  The pair order alternates per rep, so a drift in machine load
# lands on both sides.
#
#   lein perf-ab <base-rev> [--reps N] [--threshold X] [--only probe,probe]
#
# A probe REGRESSED when its median paired ratio exceeds the threshold (default 1.25)
# and every pair but at most one reads above 1.  Exit: 0 clean, 1 on a regression,
# 2 on a bad argument.
{ # one brace group, read whole before it runs: scripts/lint-shellcheck.sh says why
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 1

# shellcheck source=scripts/lib/runlog.sh
. "$ROOT/scripts/lib/runlog.sh"
# shellcheck source=scripts/lib/slots.sh
. "$ROOT/scripts/lib/slots.sh"

usage() { echo "usage: lein perf-ab <base-rev> [--reps N] [--threshold X] [--only a,b]" >&2; exit 2; }

[[ $# -ge 1 && "$1" != --* ]] || usage
BASE_REV="$1"; shift
REPS=5; THRESHOLD=1.25; ONLY=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --reps)      [[ $# -ge 2 ]] || usage; REPS="$2"; shift 2 ;;
    --threshold) [[ $# -ge 2 ]] || usage; THRESHOLD="$2"; shift 2 ;;
    --only)      [[ $# -ge 2 ]] || usage; ONLY=(--only "$2"); shift 2 ;;
    *)           usage ;;
  esac
done
BASE=$(git rev-parse --short "$BASE_REV^{commit}" 2>/dev/null) \
  || { echo "perf-ab: no such revision: $BASE_REV" >&2; exit 2; }

require_primary "lein perf-ab"
perf_lock_take lein perf-ab "$@"

AB_ROOT="logs/perf-ab"
LOG="$AB_ROOT/run-$$.log"
TSV="$AB_ROOT/run-$$.tsv"
BASE_TREE="testbench/perf-ab/$BASE"
mkdir -p "$AB_ROOT" || exit 1

if [[ ! -f "$BASE_TREE/project.clj" ]]; then
  mkdir -p "$BASE_TREE" && git archive "$BASE" | tar -x -C "$BASE_TREE" || exit 1
fi
mkdir -p "$BASE_TREE/bench/vaelii/bench"
cp bench/vaelii/bench/ab.clj "$BASE_TREE/bench/vaelii/bench/ab.clj" || exit 1

runlog_start
{ revision_stamp "perf-ab against $BASE"
  echo "# base $(git log -1 --format='%h %s' "$BASE")"
  echo "# $REPS rep(s), threshold ${THRESHOLD}x"; } >"$LOG"
cat "$LOG"

# side <name> <dir>: one JVM, every probe, rows appended to the TSV
side() {
  local name="$1" dir="$2" out
  out=$(cd "$dir" && lein with-profile +bench run -m vaelii.bench.ab ${ONLY[@]+"${ONLY[@]}"} 2>&1)
  printf '%s\n' "$out" | sed "s/^/[$name] /" >>"$LOG"
  printf '%s\n' "$out" | awk -v s="$name" -v r="$rep" '$1=="ab-result"{print r"\t"s"\t"$2"\t"$3}' >>"$TSV"
  grep -q '^ab-result' <<<"$out" \
    || { echo "perf-ab: the $name JVM printed no result:" >&2; tail -20 <<<"$out" >&2; return 1; }
}

: >"$TSV"
for rep in $(seq "$REPS"); do
  echo "perf-progress $rep/$REPS" >&2
  if (( rep % 2 )); then side base "$BASE_TREE" && side head "$ROOT"
  else                   side head "$ROOT"      && side base "$BASE_TREE"; fi || exit 1
done

python3 - "$TSV" "$THRESHOLD" <<'PY' | tee -a "$LOG"
import sys, statistics as st
rows = [l.split("\t") for l in open(sys.argv[1]).read().splitlines()]
thr = float(sys.argv[2])
by = {}
for rep, side, probe, ms in rows:
    by.setdefault(probe, {}).setdefault(rep, {})[side] = float(ms)
bad = []
print(f"\n{'probe':16} {'base ms':>10} {'head ms':>10} {'head/base':>10}  pairs slower")
for probe, reps in by.items():
    pairs = [(r["base"], r["head"]) for r in reps.values() if "base" in r and "head" in r]
    ratios = [h / b for b, h in pairs]
    med = st.median(ratios)
    slower = sum(x > 1 for x in ratios)
    verdict = ""
    if med > thr and slower >= len(ratios) - 1:
        verdict = "REGRESSED"; bad.append(probe)
    elif med < 1 / thr and slower <= 1:
        verdict = "faster"
    print(f"{probe:16} {st.median(b for b, _ in pairs):10.3f} {st.median(h for _, h in pairs):10.3f}"
          f" {med:9.2f}x  {slower}/{len(ratios)}  {verdict}")
print()
print(f"{len(bad)} of {len(by)} probes REGRESSED: {bad}" if bad
      else f"{len(by)} probe(s) within {thr}x of the base")
PY

ln -sfn "$(basename "$LOG")" "$AB_ROOT/latest" 2>/dev/null || true
verdict=$(grep -E '^[0-9]+ (probe\(s\) within|of [0-9]+ probes REGRESSED)' "$LOG" | tail -1)
[[ -n "$verdict" ]] || exit 1
if [[ "$verdict" == *REGRESSED* ]]; then rc=1; state=failed; else rc=0; state=passed; fi
runlog_record perf-ab "$BASE" "$state" "$verdict" "$LOG"
exit "$rc"
}
