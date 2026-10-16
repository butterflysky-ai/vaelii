#!/usr/bin/env bash
# scripts/ci-weights.sh — rewrite the CI shard weights from measured namespace times.
#
#   scripts/ci-weights.sh <run-id> [--repo owner/name]      # both legs, from a run's logs
#   scripts/ci-weights.sh --from DIR --leg disk|memory --out FILE [--prev FILE]
#                                                           # one leg, from timing rows
#
# scripts/ci-shard.sh packs the shards of .github/workflows/test.yml by measured
# namespace time, one weights file per leg: scripts/ci-test-weights-disk.tsv and
# scripts/ci-test-weights-memory.tsv.  The two legs differ per namespace (the
# durable record store costs some namespaces far more than others), so each leg
# is packed from its own column.
#
# THE RUN-ID FORM rewrites both committed files from a finished run's job logs.
# The runner stamps every line, so the gap between one `lein test <namespace>`
# line and the next is what that namespace cost on CI's hardware.
#
# THE --from FORM is what the workflow runs after every green leg: DIR holds one
# `<shard>-of-<total>.tsv` per shard, the `namespace<TAB>seconds` rows its
# scripts/lib/ns-timings.sh wrote, and FILE goes into the Actions cache, where the
# next run's shards read it in place of the committed file.  A DIR missing a shard
# is refused: that shard's namespaces would be written at 0.00.  The committed
# files are the fallback for a run that finds no cache entry.  With --prev, the
# weights the run packed from, each measured figure goes into PREV's as a moving
# average (scripts/lib/ns-timings.sh, `ns_timings_average`), so one slow runner
# moves a weight by 0.3 of its excess.
#
# A NAMESPACE THE RUN DID NOT ENTER IS WRITTEN AT 0.00 rather than left out, so a
# namespace whose every test is `^:slow` is weighted at what it costs the
# `:default` selector instead of at the mean.  A namespace added to the tree since
# the run gets no line at all, and scripts/ci-shard.sh gives it the mean.
{ # one brace group, read whole before it runs: scripts/lint-shellcheck.sh says why
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 1

REPO="vaelii/vaelii"
RUN=""; FROM=""; LEG=""; OUT=""; PREV=""

usage() {
  sed -n '4,6p' "$0" | sed 's/^# \{0,1\}//' >&2
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --repo) REPO="${2:?--repo needs owner/name}"; shift 2 ;;
    --from) FROM="${2:?--from needs a directory}"; shift 2 ;;
    --leg)  LEG="${2:?--leg needs disk or memory}"; shift 2 ;;
    --out)  OUT="${2:?--out needs a file}"; shift 2 ;;
    --prev) PREV="${2:?--prev needs a file}"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    -*) echo "ci-weights: unknown option $1" >&2; usage; exit 2 ;;
    *)  RUN="$1"; shift ;;
  esac
done

tmp=$(mktemp -d) || exit 1
trap 'rm -rf "$tmp"' EXIT

find test -name '*_test.clj' \
  | sed -e 's|^test/||' -e 's|\.clj$||' -e 's|/|.|g' -e 's|_|-|g' \
  | sort > "$tmp/tree.txt"

# write_weights <leg> <timings.tsv> <out> <source line>: the header, then one row per
# tree namespace, 0.00 for one the timings lack.
write_weights() {
  local leg="$1" timings="$2" out="$3" source="$4" total count
  total=$(awk -F'\t' '{ s += $2 } END { printf "%.0f", s }' "$timings")
  count=$(wc -l < "$tmp/tree.txt" | tr -d ' ')
  {
    cat <<HDR
# scripts/ci-test-weights-$leg.tsv — how long each test namespace takes on a CI
# runner, VAELII_TEST_BACKEND=$( [[ $leg == disk ]] && echo disk-log || echo memory ).
#
# \`namespace<TAB>seconds\`.  scripts/ci-shard.sh --leg $leg bin-packs the namespaces
# by these numbers so that the shards of that .github/workflows/test.yml leg finish
# together.  The workflow reads this file only when the Actions cache holds no
# timings from an earlier green run of the leg.  A namespace absent here still runs,
# weighted at the mean; one at 0.00 has every test \`^:slow\` or \`^:multi-jvm\`.
#
# Regenerate with scripts/ci-weights.sh <run-id>.
#
# Source: $source, $count namespaces, ${total}s of namespace time.
HDR
    awk -F'\t' '
      NR == FNR { w[$1] = $2; next }
      { printf "%s\t%.2f\n", $1, ($1 in w) ? w[$1] : 0 }' "$timings" "$tmp/tree.txt"
  } > "$out.new" && mv "$out.new" "$out"
  echo "ci-weights: $out — $count namespaces, ${total}s, from $source" >&2
}

if [[ -n "$FROM" ]]; then
  [[ -n "$LEG" && -n "$OUT" && -z "$RUN" ]] || { usage; exit 2; }
  case "$LEG" in disk|memory) ;; *) echo "ci-weights: --leg is disk or memory, not $LEG" >&2; exit 2 ;; esac
  files=$(cd "$FROM" 2>/dev/null && ls -- *-of-*.tsv 2>/dev/null)
  of=$(sed -n 's/^[0-9]*-of-\([0-9]*\)\.tsv$/\1/p' <<< "$files" | sort -u)
  complete=0
  if [[ "$of" =~ ^[0-9]+$ && "$(wc -l <<< "$files" | tr -d ' ')" -eq "$of" ]]; then
    complete=1
    for ((i = 1; i <= of; i++)); do [[ -f "$FROM/$i-of-$of.tsv" ]] || complete=0; done
  fi
  if [[ $complete -ne 1 ]]; then
    echo "ci-weights: $FROM does not hold one <shard>-of-<total>.tsv per shard: $(tr "\n" " " <<< "$files")" >&2
    exit 1
  fi
  mkdir -p "$(dirname "$OUT")" || exit 1
  # A namespace appears in one shard's rows only; the last row wins if one repeats.
  find "$FROM" -name '*-of-*.tsv' -exec cat {} + \
    | awk -F'\t' '$1 != "" { s[$1] = $2 } END { for (k in s) printf "%s\t%s\n", k, s[k] }' \
    | sort > "$tmp/$LEG.tsv"
  [[ -s "$tmp/$LEG.tsv" ]] || { echo "ci-weights: no timing rows under $FROM" >&2; exit 1; }
  source="${GITHUB_REPOSITORY:-$REPO} run ${GITHUB_RUN_ID:-local}"
  if [[ -n "$PREV" ]]; then
    [[ -f "$PREV" ]] || { echo "ci-weights: --prev $PREV is not a file" >&2; exit 1; }
    # every tree namespace gets a measured figure, 0 for one the run did not enter, so
    # a namespace that turned all-`^:slow` falls toward 0.00 instead of holding PREV's
    awk -F'\t' 'NR == FNR { m[$1] = $2; next } { printf "%s\t%s\n", $1, ($1 in m) ? m[$1] : 0 }' \
      "$tmp/$LEG.tsv" "$tmp/tree.txt" > "$tmp/$LEG.measured"
    # shellcheck source=scripts/lib/ns-timings.sh
    . scripts/lib/ns-timings.sh
    ns_timings_average "$PREV" "$tmp/$LEG.measured" > "$tmp/$LEG.tsv"
    source="$source, averaged into $PREV at $NS_TIMINGS_WEIGHT"
  fi
  write_weights "$LEG" "$tmp/$LEG.tsv" "$OUT" "$source"
  exit 0
fi

[[ -n "$RUN" && -z "$LEG$OUT$PREV" ]] || { usage; exit 2; }
command -v gh >/dev/null 2>&1 || { echo "ci-weights: gh not found on PATH" >&2; exit 127; }

# One `gh` call resolves the job ids; the logs come one job at a time because a
# run's combined log is a zip this would have to unpack.  The gate jobs `memory`
# and `disk` log no `lein test` line and are skipped.
jobs=$(gh api "repos/$REPO/actions/runs/$RUN/jobs" --paginate \
         --jq '.jobs[] | select(.name | test("^(memory|disk)-shard-[0-9]+$")) | "\(.id) \(.name)"') || exit 1
if [[ -z "$jobs" ]]; then
  echo "ci-weights: run $RUN has no memory or disk shard jobs" >&2
  exit 1
fi

: > "$tmp/disk.log"
: > "$tmp/memory.log"
while read -r id name; do
  echo "ci-weights: reading $name" >&2
  gh run view --repo "$REPO" --job "$id" --log >> "$tmp/${name%%-*}.log" || exit 1
done <<< "$jobs"

# A namespace's cost is the gap from its own `lein test` line to the next one, and
# the last namespace of a shard is closed by that shard's `Ran N tests` line. The
# runner stamps every line, so the field before the message is the clock; a run
# crossing midnight adds the day back rather than recording a negative gap.
timings() {
  awk -F'\t' '
    { line = $0
      sub(/^[^\t]*\t[^\t]*\t/, "", line)   # the job and step columns gh prefixes
      sub(/^[^0-9]+/, "", line)               # a byte-order mark on the first line
      if (line !~ /^[0-9][0-9][0-9][0-9]-[0-9][0-9]-[0-9][0-9]T/) next
      stamp = substr(line, 12, 15); msg = substr(line, index(line, "Z ") + 2)
      split(stamp, c, ":"); t = c[1] * 3600 + c[2] * 60 + c[3]
      if (msg ~ /^lein test vaelii/) { ns = substr(msg, 11) }
      else if (msg ~ /^Ran [0-9]+ tests/) { ns = "" }
      else next
      if (prev != "") { d = t - pt; if (d < 0) d += 86400; secs[prev] = d }
      prev = ns; pt = t
    }
    END { for (k in secs) printf "%s\t%.2f\n", k, secs[k] }' "$1" | sort
}

for leg in disk memory; do
  timings "$tmp/$leg.log" > "$tmp/$leg.tsv"
  [[ -s "$tmp/$leg.tsv" ]] || { echo "ci-weights: no namespace timings in the $leg-shard logs" >&2; exit 1; }
  write_weights "$leg" "$tmp/$leg.tsv" "scripts/ci-test-weights-$leg.tsv" "$REPO run $RUN"
done
exit
}
