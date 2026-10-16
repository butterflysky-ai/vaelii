#!/usr/bin/env bash
# scripts/test-sweeps.sh — run the whole suite once per ALTERNATIVE IMPLEMENTATION
# and report a ✔ / ✘ per test namespace as it goes, then one per run.
#
# The other axis the suite can be run on.  `test-backends.sh` varies where the
# sentexes live; this varies which implementation answers, holding storage at the
# default.  Six switches each re-run the whole suite through a component the engine
# otherwise picks for itself, and a seventh re-runs it under the other reading of the
# argument declarations:
#
#   tms-reference  VAELII_TEST_TMS=reference    the persistent-map JTMS instead of the
#                                               default dense one
#   rete           VAELII_RETE=1                the RETE-ish sweep instead of the
#                                               re-derivation fixpoint
#   query-engine   VAELII_QUERY_ENGINE=…        the node engine instead of the goal-stack DFS
#   tactician      …plus VAELII_QUERY_STRATEGY  one of the node engine's orderings
#   hier-off       VAELII_HIER=0                the reference nested fan-out instead of
#                                               the set-algebra context retrieval
#   plan-off       VAELII_PLAN=0                the generators in written order instead
#                                               of the cost ranking
#   assertive-off  VAELII_ASSERTIVE_ARG_TYPES=0 the declarations as constraints only
#                                               instead of entailments (docs/argtypes.md)
#
# Each is a COST decision rather than a semantic one — a tactician orders goals, it
# does not choose answers — so the suite must be **failing-set-identical** across all
# seven and against a plain `lein test`.  A sweep that answers differently is a bug in
# the alternative, not a feature of it: running these by hand is what found a clash
# reported against a different sentex depending on which retrieval path answered.
# `assertive-off` is a semantic switch, and it holds the same claim by a different
# route: a test whose answer depends on the reading pins it with `tu/with-entailing` or
# `tu/without-entailing`, and every other test answers alike under both.
#
# The ASSERTION COUNT is identical here too, as it is in `test-backends.sh`.  Where an
# assertion pins an artifact of one implementation — `prove` returns one solution per
# derivation on the DFS and one per answer on the node engine, so counting its results
# is an engine-specific number (docs/inference.md) — the test asserts the number for
# the engine in force, read off `tu/query-engine-override`, rather than standing
# aside.  A count that moves is a run that skipped something.
#
# CHECKED at the foot of this script rather than left to be read: `config_expected_delta`
# in scripts/lib/suite-configs.sh holds the expected shortfall, zero for every
# configuration, and any other fails the run.  Standing aside silently is the thing
# being made impossible; a configuration that had to would be recorded there with its
# reason.
#
# WHY THIS IS A SCRIPT AND NOT A CI JOB.  It is both, and the local one is the
# gate.  `deep.yml` runs these seven and the nine backends on a runner, which is
# 240 job-minutes against a 2,000-minute monthly allowance — eight runs a month,
# for a matrix a release wants once.  The same coverage here costs wall time and
# no money, so the CI job is the confirmation and this is what you run before a
# cut.  `lein gate` covers neither: it is one backend and every switch at its
# default, which is what keeps it a check you run before every landing.
#
# Runs here are SEQUENTIAL for the reason `test-backends.sh` gives — one run at a time
# is one readable wall time, on a box somebody is still using — and not because
# anything forbids sharing: these seven write no durable store at all.
# **`scripts/test-matrix.sh` is the concurrent one**, these seven and the nine backends
# at once in ~13 minutes rather than ~55, and it is what to run when a change owes the
# matrix.  This script is for one sweep, or for a timing that means something.
#
# A leading-colon argument is a TEST SELECTOR passed straight to `lein test`.
# `:default` — what a bare run takes — skips the `^:slow` tests; `:all` is the
# one to run before a release, and the one `deep.yml` uses.  A non-default
# selector writes `<sweep>.<selector>.log`, so passes at two selectors sit beside
# each other.
#
# Usage:
#   ./scripts/test-sweeps.sh                     # all seven, :default
#   ./scripts/test-sweeps.sh :all                # all seven, slow tests included
#   ./scripts/test-sweeps.sh query-engine        # only this one
#   ./scripts/test-sweeps.sh :all rete tms-reference
#   ./scripts/test-sweeps.sh --fail-fast
#
# Env:
#   TEST_SWEEPS_OUT   log directory (default logs/test-sweeps)
#   SUITE_PROGRESS    marks | lines | auto (default: marks on a terminal, lines into
#                     anything else — `test-backends.sh` says why)
#
# Progress and the revision read exactly as they do there: a ✔/✘ per namespace as it
# finishes, named rather than marked when the output is not a terminal, and the
# revision on the header, on every summary row and at the top of every log — read per
# run, so a commit landing mid-matrix is called out rather than left to look like a
# run that skipped something.
#
# ^C stops the suite that is running and then the script.
#
# Exit: 0 when every sweep passed, 1 when one failed, 130 when interrupted.

{ # one brace group, read whole before it runs: scripts/lint-shellcheck.sh says why
set -uo pipefail
cd "$(dirname "$0")/.." || exit 1

# leiningen's own terminal state, handed down first by the alias: lein-shell pipes
# this script's stdout, so `-t 1` here would say "not a terminal" and the graph
# would fall to one line per namespace even with someone watching (suite-marks.sh
# reads SUITE_TTY at source time below).  Absent when run directly, where `-t 1` stands.
case "${1:-}" in
  --tty)    SUITE_TTY=1; shift ;;
  --no-tty) SUITE_TTY=0; shift ;;
esac

# shellcheck source=scripts/lib/suite-marks.sh
. scripts/lib/suite-marks.sh

# The roster, and the env assignments that select each: `scripts/lib/suite-configs.sh`,
# shared with `test-backends.sh` and `test-matrix.sh`.  Cheapest first there, so a matrix
# that is going to fail on the retrieval switch says so before spending twenty minutes on
# the node engine.
# shellcheck source=scripts/lib/suite-configs.sh
. scripts/lib/suite-configs.sh
SWEEP_NAMES=("${ALL_SWEEPS[@]}")

FAIL_FAST=0
SELECTOR=":default"
WANTED=()

while [[ $# -gt 0 ]]; do
  case "$1" in
    --fail-fast) FAIL_FAST=1; shift ;;
    -h|--help) awk 'NR>1 && /^#/ {sub(/^# ?/, ""); print; next} NR>1 {exit}' "$0"; exit 0 ;;
    # checked here rather than left to lein, which answers an unknown selector with
    # "Please specify :test-selectors in project.clj" — true, and not the problem
    :all|:slow|:default) SELECTOR="$1"; shift ;;
    :*) echo "unknown selector $1 (:all, :slow, :default)" >&2; exit 2 ;;
    -*) echo "unknown flag $1 (try --help)" >&2; exit 2 ;;
    # named here rather than at run time: an unknown sweep would otherwise run the
    # suite with no switch set at all and report a clean pass for a configuration
    # nothing ran, which is the exact failure the switches' own domains refuse
    *) config_env "$1" >/dev/null \
         || { echo "unknown sweep $1 (${SWEEP_NAMES[*]})" >&2; exit 2; }
       WANTED+=("$1"); shift ;;
  esac
done

# A worktree runs `lein gate` and nothing heavier (scripts/lib/slots.sh says why).
# shellcheck source=scripts/lib/slots.sh
. scripts/lib/slots.sh
require_primary "lein test-sweeps"

if [[ ${#WANTED[@]} -gt 0 ]]; then
  SWEEPS=("${WANTED[@]}")
else
  SWEEPS=("${SWEEP_NAMES[@]}")
fi

OUT_DIR="${TEST_SWEEPS_OUT:-logs/test-sweeps}"
mkdir -p "$OUT_DIR"

RUN_NS_COUNT=$(selected_ns_count "$SELECTOR")

# ^C stops the run in progress AND the script; `test-backends.sh` carries the long
# form of why neither half is automatic.  In short: the suite runs in the
# background so a trap can interrupt the `wait`, and `set -m` gives it its own
# process group so one signal reaches the `lein` wrapper, its JVM, the project JVM
# it forks, and the readers on the pipe.
set -m
child_pid=""
child_pgid=""
current_sweep=""
current_log=""
FAILED=()
COUNT_PAIRS=()
DONE_RUNS=()
rev=""
prev_rev=""
REVS=()

# Two codes for one fact: shellcheck 0.10 split "this function is never called"
# out of SC2317 into SC2329, so naming only the new one leaves the script red on
# every older shellcheck — including the one ubuntu-latest ships.
# shellcheck disable=SC2317,SC2329  # invoked from the INT/TERM trap below
stop_child() {
  [[ -z "$child_pgid" ]] && return 0
  kill -TERM -"$child_pgid" 2>/dev/null            # the negative pid: the whole group
  for _ in $(seq 1 20); do
    kill -0 -"$child_pgid" 2>/dev/null || return 0
    sleep 0.25
  done
  kill -KILL -"$child_pgid" 2>/dev/null
}

# shellcheck disable=SC2317,SC2329  # ditto — `trap on_interrupt INT TERM`
on_interrupt() {
  trap - INT TERM                                  # a second ^C is the OS's now
  echo
  echo "  ${RED}^C${OFF} ${DIM}stopping ${current_sweep:-the run}${OFF}"
  { stop_child; [[ -n "$child_pid" ]] && wait "$child_pid"; } 2>/dev/null
  [[ -n "$current_log" ]] && echo "  ${DIM}partial log: $current_log${OFF}"
  echo
  echo "${RED}interrupted${OFF} ${DIM}after ${#DONE_RUNS[@]} of ${#SWEEPS[@]}${OFF}"
  exit 130
}
trap on_interrupt INT TERM

echo "${BOLD}running the suite on ${#SWEEPS[@]} sweep(s)${OFF}" \
     "${DIM}$SELECTOR — $RUN_NS_COUNT of $NS_COUNT namespaces${OFF}"
echo "${DIM}at $(revision_line)${OFF}"
echo "${DIM}logs in $OUT_DIR/${OFF}"
echo

for sweep in "${SWEEPS[@]}"; do
  if [[ "$SELECTOR" == ":default" ]]; then
    log="$OUT_DIR/$sweep.log"
  else
    log="$OUT_DIR/$sweep${SELECTOR/:/.}.log"
  fi
  current_sweep="$sweep"
  current_log="$log"

  # as an `env` argument list rather than an assignment prefix: a prefix is
  # recognized before expansion, so one built from a variable cannot be used.
  # Word-splitting is exactly what is wanted here — the tactician row is two
  # assignments, and neither ever contains a space.
  # shellcheck disable=SC2207
  envv=( $(config_env "$sweep") )

  # the revision THIS run is about to be taken at, read per run: seven runs are
  # long enough for a commit to land between two of them, and the symptom of that
  # is a count that moved — which is also the symptom of a run that skipped
  # something.  `test-backends.sh` carries the long form.
  rev=$(revision_hash)
  if [[ -n "$prev_rev" && "$rev" != "$prev_rev" ]]; then
    echo "  ${RED}⚠${OFF} ${DIM}the tree moved: $prev_rev → $rev —" \
         "counts below are not comparable with the ones above${OFF}"
  fi
  prev_rev="$rev"
  REVS+=("$rev")

  # the command verbatim, so a run can be reproduced by copying the line, and the
  # log it is going to — printed BEFORE the run, so a suite still going is already
  # tailable
  echo "  ${DIM}env ${envv[*]} lein test $SELECTOR  # $log${OFF}"
  echo "  ${DIM}loading a JVM and all $NS_COUNT test namespaces; the first namespace waits on that${OFF}"
  start=$SECONDS
  # `< /dev/null` is what keeps it RUNNING: `set -m` puts the job outside the
  # terminal's foreground group and leiningen pumps its own stdin into the project
  # subprocess, so a run that reads the tty takes SIGTTIN and the whole group stops
  # — 0% CPU and an empty log, indistinguishable from a hang.
  # the stamp first, then append: a log has to say what it was run *against*, or a
  # count that moved because the tree moved is indistinguishable from one that moved
  # because a run skipped something.  Labelled with the sweep, so a per-config log
  # names its config on line 1 as well as the revision
  revision_stamp "sweep $sweep" > "$log"
  RUN_START=$start                                 # the clock a `lines` run times against
  env "${envv[@]}" lein test "$SELECTOR" < /dev/null 2>&1 | tee -a "$log" | ns_progress &
  child_pid=$!
  child_pgid=$(ps -o pgid= -p "$child_pid" 2>/dev/null | tr -d ' ')
  child_pgid="${child_pgid:-$child_pid}"
  wait "$child_pid" 2>/dev/null                    # 2>/dev/null: the job-done notice
  code=$?
  child_pid=""
  child_pgid=""
  DONE_RUNS+=("$sweep")
  elapsed=$((SECONDS - start))

  summary=$(run_summary "$log")
  counts=$(run_counts "$log")
  # the count on its own, for the cross-run comparison at the foot of this script
  run_asserts=$(run_assertions "$log")
  [[ -n "$run_asserts" ]] && COUNT_PAIRS+=("$sweep:$run_asserts")

  if [[ $code -eq 0 ]]; then mark="$TICK"; else mark="$CROSS"; FAILED+=("$sweep"); fi
  printf '  %s %-16s %-52s %8s  %s\n' \
    "$mark" "$sweep" "${summary:-did not finish}${counts:+, $counts}" "$(hms $elapsed)" "$rev"

  if [[ $code -ne 0 ]]; then
    while read -r ns; do
      [[ -z "$ns" ]] && continue
      printf '      %s %s\n' "$CROSS" "$ns"
    done < <(failing_namespaces "$log")
  fi

  if [[ $code -ne 0 && $FAIL_FAST -eq 1 ]]; then
    echo; echo "${RED}stopping: --fail-fast${OFF}"; break
  fi
done

echo
# one revision for the whole matrix, or the several it ran across — the sweeps'
# failing-set-identical claim is a claim about one tree.  Guarded on the length
# because this is bash 3.2, where `"${a[@]}"` on an empty array is an error under
# `set -u` rather than an empty list.
if [[ ${#REVS[@]} -eq 0 ]]; then
  matrix_rev="at $(revision_hash)"
else
  uniq_revs=$(printf '%s\n' "${REVS[@]}" | sort -u | tr '\n' ' ')
  if [[ $(printf '%s\n' "${REVS[@]}" | sort -u | wc -l) -gt 1 ]]; then
    matrix_rev="across ${uniq_revs% }"
  else
    matrix_rev="at ${uniq_revs% }"
  fi
fi

# ---- did every run run the same suite? ---------------------------------------
# A green set of runs has still said nothing if one of them ran fewer assertions than the
# rest: a namespace that failed to load, a `deftest` that stood aside without saying so, a
# gate that inherited a switch and measured nothing.  Every one of those is green.
# `config_expected_delta` in suite-configs.sh expects no shortfall anywhere, and says why
# no configuration stands aside; any shortfall is reported here and fails the run.  Skipped when something
# already failed — an error aborts the rest of its namespace, so the shortfall means
# nothing — and when the runs did not all compile one revision.
deltas_bad=0
if [[ ${#FAILED[@]} -eq 0 && ${#COUNT_PAIRS[@]} -gt 1 ]]; then
  if [[ $(printf '%s\n' "${REVS[@]}" | sort -u | wc -l) -le 1 ]]; then
    if ! delta_report=$(assertion_deltas_ok "${COUNT_PAIRS[@]}"); then
      echo "${BOLD}assertion counts: a run did not run what the others ran${OFF}"
      echo "$delta_report"
      echo "  ${DIM}Every run passed, so this is a test that did not run rather than one that"
      echo "  failed.  Find what the short run skipped — or, where an artifact really is"
      echo "  one implementation's, assert that configuration's own expectation.${OFF}"
      deltas_bad=1
    fi
  else
    echo "${DIM}assertion counts: not compared — the runs did not all compile one revision${OFF}"
  fi
fi

if [[ ${#FAILED[@]} -eq 0 ]]; then
  echo "${GREEN}${BOLD}all ${#SWEEPS[@]} sweeps green${OFF} ${matrix_rev}" \
       "${DIM}($OUT_DIR/)${OFF}"
  [[ $deltas_bad -eq 0 ]] && exit 0
  exit 1
fi
echo "${RED}${BOLD}${#FAILED[@]} of ${#SWEEPS[@]} failed:${OFF} ${FAILED[*]} ${DIM}(${matrix_rev})${OFF}"
for s in "${FAILED[@]}"; do
  if [[ "$SELECTOR" == ":default" ]]; then
    echo "  ${DIM}$OUT_DIR/$s.log${OFF}"
  else
    echo "  ${DIM}$OUT_DIR/$s${SELECTOR/:/.}.log${OFF}"
  fi
done
exit 1
}
