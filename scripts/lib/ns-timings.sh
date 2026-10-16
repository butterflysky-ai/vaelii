#!/usr/bin/env bash
# scripts/lib/ns-timings.sh — how long each namespace of a `lein test` run took.
#
# Sourced, never executed:
#   . scripts/lib/ns-timings.sh
#   lein test … 2>&1 | ns_timings FILE | tee LOG
#
# `ns_timings` copies stdin to stdout unchanged and writes `namespace<TAB>seconds`
# rows to FILE.  A namespace's cost is the gap from its own `lein test <ns>` line
# to the next one, and clojure.test's `Ran N tests` total closes the last
# namespace.  Each row is written when the line after the namespace arrives, so
# a run killed partway keeps the rows of the namespaces it finished.
#
# scripts/test-parallel.sh packs its local shards from these rows, and
# .github/workflows/test.yml packs its CI shards from them (scripts/ci-weights.sh
# turns a run's rows into the weights the next run reads).

# The clock is in microseconds: bash 5's EPOCHREALTIME, else perl's Time::HiRes for
# bash 3.2 (macOS's /bin/bash), else whole SECONDS.  Most namespaces take under a
# second, and at whole seconds they all read 0 and pack into one shard.
ns_timings() {
  local out="$1" line prev="" pt=0 t d
  : > "$out"
  while IFS= read -r line; do
    printf '%s\n' "$line"
    case "$line" in
      "lein test "*|"Ran "*" tests containing "*)
        if [[ -n "${EPOCHREALTIME:-}" ]]; then t=${EPOCHREALTIME/[.,]/}
        else t=$(perl -MTime::HiRes=time -e 'printf "%d", time * 1e6' 2>/dev/null) || t=$((SECONDS * 1000000))
        fi
        if [[ -n "$prev" ]]; then
          d=$(((t - pt) / 10000))
          printf '%s\t%d.%02d\n' "$prev" "$((d / 100))" "$((d % 100))" >> "$out"
        fi
        prev=""; pt=$t
        [[ "$line" == "lein test "* ]] && prev="${line#lein test }" ;;
    esac
  done
}

# `ns_timings_average PREV NEW` writes `namespace<TAB>seconds` rows to stdout: each
# NEW figure moved NS_TIMINGS_WEIGHT of the way from PREV's figure for the same
# namespace, an exponential moving average.  A namespace in one file only keeps that
# file's figure.  PREV may be missing, and `#` lines in either file are skipped.
#
# One run's figure is a noisy reading of a namespace's cost: disjointness-audit-test
# took 143 s, 159 s and 270 s on three CI runs of the same tree, and a local run on
# one shard reads every namespace slower than one on five.  At a weight of 0.3 the
# average's variance from that noise is 0.3/1.7 = 18% of one reading's, and a
# namespace whose real cost changes is 76% of the way to the new figure after four
# runs.
NS_TIMINGS_WEIGHT=0.3
ns_timings_average() {
  local prev="$1" new="$2"
  [[ -f "$prev" ]] || prev=/dev/null
  awk -F'\t' -v a="$NS_TIMINGS_WEIGHT" '
    $1 == "" || $1 ~ /^#/ { next }
    FILENAME == ARGV[1] { old[$1] = $2 + 0; next }
    { cur[$1] = $2 + 0 }
    END {
      for (k in old) if (!(k in cur)) printf "%s\t%.2f\n", k, old[k]
      for (k in cur) printf "%s\t%.2f\n", k, (k in old) ? a * cur[k] + (1 - a) * old[k] : cur[k]
    }' "$prev" "$new" | LC_ALL=C sort
}
