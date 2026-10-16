#!/usr/bin/env bash
# scripts/test-full-kb.sh [KB-DIR] [<lein test args>…] — `lein test-full-kb`: the `^:full-kb`
# probes (test/vaelii/full_kb_test.clj) against a full-size KB, on a disposable clone of it.
#
# KB-DIR defaults to checkouts/kb and must be a store (`records/`).
#
#   1. scripts/upgrade-kb.sh brings KB-DIR itself up to this checkout's engine
#      (docs/operations.md). It writes KB-DIR's reasoning and index images and never its
#      records. When the engine's belief-deriving source moved it pays one full recover,
#      which grows with the store. Otherwise it installs the image it finds. The
#      upgraded image is KB-DIR's, so the next run, another checkout at the same source,
#      and any other open of it install it rather than recover it again.
#   2. KB-DIR is cloned to $VAELII_FULL_KB_WORK/run-<pid> (default testbench/full-kb), an APFS
#      clone (`cp -c`) that shares its blocks, which the test JVM opens as
#      VAELII_FULL_KB_DIR, and which is deleted after: the probes write into the KB they
#      open.
#
# The run goes through scripts/test-selector.sh, so the report lands in
# logs/test/full-kb-run-<pid>.log and a row in logs/runs.tsv. Both JVMs take VAELII_HEAP,
# default 44g, sized for a full recover of a full-size KB, so a browser with a heap of its
# own beside it wants a machine with room for both. KB-DIR must be held open by no other
# process: the upgrade is refused by its single-writer lock, and the clone of a live store
# is torn.
#
#   lein test-full-kb
#   lein test-full-kb /path/to/store
#
# Exit: 2 on a bad KB-DIR, the upgrade's status when it fails, else `lein test`'s.
{ # one brace group, read whole before it runs: scripts/lint-shellcheck.sh says why
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 1
# shellcheck source=scripts/lib/start.sh
. "$ROOT/scripts/lib/start.sh"

ARG=""
if [ $# -gt 0 ] && [ -d "$1" ]; then ARG="$1"; shift; fi
KB="$(start_kb_dir "$ARG")" || exit 2
if [ ! -d "$KB/records" ]; then
  echo "test-full-kb: $KB holds no records/ — name a store" >&2
  exit 2
fi

WORK="${VAELII_FULL_KB_WORK:-$ROOT/testbench/full-kb}"
mkdir -p "$WORK" || exit 1

VAELII_HEAP="${VAELII_HEAP:-44g}"
export VAELII_HEAP

echo "test-full-kb: upgrading $KB to $(git rev-parse --short HEAD)" >&2
bash "$ROOT/scripts/upgrade-kb.sh" "$KB" || exit $?

JVM_OPTS="${JVM_OPTS:-} $(start_jvm_opts) -Dvaelii.disk.sync-ms=0"
export JVM_OPTS

RUN="$WORK/run-$$"
trap 'command rm -rf "$RUN"' EXIT
cp -cR "$KB" "$RUN" || exit 1
command rm -f "$RUN/.vaelii.lock"

VAELII_FULL_KB_DIR="$RUN" bash "$ROOT/scripts/test-selector.sh" :full-kb "$@"
exit
}
