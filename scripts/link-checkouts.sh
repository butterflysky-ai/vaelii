#!/usr/bin/env bash
# scripts/link-checkouts.sh [-f] [PREFIX] [SUFFIX] — link the published Apache-2.0
# siblings into checkouts/, so Leiningen resolves them from live source instead of a
# released jar:
#
#   checkouts/vaelii-foreign  -> ../../vaelii-foreign
#   checkouts/vaelii-postgres -> ../../vaelii-postgres
#   checkouts/vaelii-sqlite   -> ../../vaelii-sqlite
#
# The siblings reach into `vaelii.impl.*`, which this engine is free to change, and a
# link surfaces that break when it lands rather than at the next sibling release.
#
# A link adds a sibling's source to EVERY command's classpath and none of its
# dependencies. The `+with-foreign`, `+with-postgres` and `+with-sqlite` profiles
# (project.clj) add the released jar, whose pom brings the dependencies, and the
# linked source shadows the jar's namespaces: `lein with-profile +with-postgres
# browser`. Without the profile, opening a `:pg-*` or `:sqlite` KB refuses with
# `:missing-adapter`, naming the namespace that failed to load. The suite's absence
# tests stub the adapter's load instead of reading the classpath, so `lein gate` is
# the same with and without the links.
#
# checkouts/ is gitignored, so the links are not committed: rerun after a fresh
# clone. Idempotent (ln -snf). A missing target is skipped with a WARN unless -f /
# --force is given (a dangling link resolves once the sibling is cloned). Only a
# published sibling is named here, because this script ships and every repo it names
# must be one a reader can clone.
#
# PREFIX / SUFFIX wrap the *target repo dir name* so a modified sibling clone can be
# linked while the checkout name stays fixed (Leiningen matches a checkout by the
# project.clj it finds, not by the directory name): `link-checkouts.sh "" -wip` points
# checkouts/vaelii-foreign at ../../vaelii-foreign-wip.
{ # one brace group, read whole before it runs: scripts/lint-shellcheck.sh says why
set -euo pipefail
cd "$(dirname "$0")/.."   # repo root
mkdir -p checkouts

force=0
while [[ "${1:-}" == -* ]]; do
  case "$1" in
    -f|--force) force=1; shift ;;
    -h|--help)  sed -n '2,31p' "$0"; exit 0 ;;
    --) shift; break ;;
    *)  echo "unknown option: $1" >&2; exit 2 ;;
  esac
done

prefix="${1:-}"
suffix="${2:-}"

# $1 = checkout name (fixed — Leiningen resolves the artifact against it)
# $2 = repo dir name (prefix/suffix applied here)
link() {
  local name="$1" repo="$2"
  local target="../../${prefix}${repo}${suffix}"
  # target is relative to checkouts/, so test it from there.
  if [[ $force -eq 0 && ! -e "checkouts/$target" ]]; then
    echo "WARN: skipping checkouts/$name -> $target (target missing; -f to link anyway)" >&2
    return
  fi
  ln -snf "$target" "checkouts/$name"
  echo "linked checkouts/$name -> $target"
}

link vaelii-foreign vaelii-foreign
link vaelii-postgres vaelii-postgres
link vaelii-sqlite vaelii-sqlite
exit
}
