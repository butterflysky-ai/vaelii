#!/usr/bin/env bash
# scripts/check-breaking-siblings.sh — a release step: read the `*Breaks:*`
# tokens off a CHANGELOG section and grep the sibling checkouts for each, so a
# release's Breaking entries are read once with the question "who does this
# break?" put to every one of them.
#
# The engine ships beside siblings that consume it — the reader plugin, the
# field harness, the store adapters — and a Breaking entry is a sentence
# addressed to a reader, which nothing verifies. The 0.5.0 release renamed an
# `open-kb` option and broke `vaelii-foreign`'s test scaffolding and a
# downstream harness's benchmark cells; both were found by hand, afterwards.
#
# The asymmetry is the argument for grepping wide. An entry that names a sibling
# it does not break costs a maintainer one grep; an entry that names nobody
# ships a green release and a red sibling, found by whoever pulls next.
#
# ## The hook it reads
#
# Every entry sits under a `### ` heading naming its class, and every Breaking
# entry carries one line (CONTRIBUTING §3.8) holding one backticked token per name
# a caller would have written:
#
#   *Breaks:* `:record-space`, `:index-space`
#
# A token is a retired option key or symbol, an ex-info `:type`, a fragment of a
# message somebody matches on, or the API name whose behaviour moves. More
# tokens than fit on one line take a second `*Breaks:*` line in the same entry —
# each line is read on its own, and nothing is carried across the wrap.
#
# ## What it finds, and what it does not
#
# **It greps text.** It finds a renamed option key, a matched message fragment
# and a named symbol. It does not find a behavioural change a sibling depends on
# without naming: a caller that counts a justification's antecedents, or one that
# relies on two facts merging, writes no token this can look for. So **absence of
# hits is not proof** — it says no sibling spells the name, not that no sibling
# breaks. A hit is likewise a place to look and not a verdict: the sibling may
# have moved already, or use the name for something of its own.
#
# The scan is per sibling checkout and covers its **tracked** files (`git grep`),
# which is what keeps a build tree and a gitignored 471 GB bench corpus out of
# the report. A directory that is not a git checkout — an unpacked release, say —
# is grepped directly, minus the build and scratch directories.
#
# ## Not a gate
#
# This is a release step, not a check the suite runs: it reads other repositories
# on the machine, and which of them are cloned is not a fact about this tree. A
# missing sibling is reported by name and adds no work. It exits 0 whatever it
# finds; `--strict` is the one exception, and it fails on three things, all of
# them an entry saying less than §3.8 asks: a Breaking or Refusal entry naming no
# token at all — an entry nothing can check — one carrying no `*Migration:*` line,
# and one whose stated class is not among the five §3.8 defines (Breaking,
# Refusal, Additive, Fix, Internal). That last is the fail-open case and the reason the
# other two are checked here: the class is what decides the release number, and
# everything downstream reads a word it does not recognise as Additive.
#
# Only Breaking and Refusal owe a `*Breaks:*` line and a `*Migration:*` line.
# Additive, Fix and Internal owe neither — a Fix moves the code to what the engine
# already documents, so it retires no name a sibling could be grepped for, and an
# Internal change is one no caller observes — and all three ride any release.
#
#   bash scripts/check-breaking-siblings.sh                 # the unreleased section
#   bash scripts/check-breaking-siblings.sh --section 0.5.0
#   bash scripts/check-breaking-siblings.sh --root ~/src    # where the siblings live
#   bash scripts/check-breaking-siblings.sh --limit 0       # every hit, not the first 5
#   bash scripts/check-breaking-siblings.sh --all-files     # prose and data too
#   bash scripts/check-breaking-siblings.sh --strict        # fail on an entry saying too little
#
# `lein check-siblings` runs it over the unreleased section.
{ # one brace group, read whole before it runs: scripts/lint-shellcheck.sh says why
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 1

# The siblings that consume the engine's API, named one by one rather than
# globbed off the parent directory — the same reason scripts/lint.sh names its
# scripts. A directory beside this checkout is not evidence of a consumer (an
# archived port, a scratch clone and this repo's own release staging all live
# there), and a roster is the place the judgement gets written down.
#
# The shipped roster is the published consumer alone. **Your own downstreams go
# in `.sibling-repos`**, one directory name per line, `#` comments allowed —
# untracked, because a roster is a fact about one machine's checkouts and a
# repository that published one would be advertising every private consumer it
# has by name.
#
# A file rather than an environment variable, deliberately: a `VAELII_*` name is
# part of the configuration surface (CONTRIBUTING §3.8) and owes a golden entry,
# a row in docs/operations.md and a changelog line, which is a lot of ceremony
# for a roster only a release step reads. `--root` already covers the one-off.
#
# What belongs on it is anything that goes through an entry point this repo can break:
# a plugin reaching into `vaelii.impl.*` on purpose, a store or feed adapter
# implementing the protocols, a harness driving the whole API — and content
# repositories too, since a newly refused sentence shape breaks a corpus that
# asserts it exactly like it breaks a caller.
SIBLINGS=(vaelii-foreign)
if [[ -r "$ROOT/.sibling-repos" ]]; then
  while read -r line; do
    line="${line%%#*}"; line="${line// /}"
    [[ -n "$line" ]] && SIBLINGS+=("$line")
  done <"$ROOT/.sibling-repos"
fi

# What a hit has to be in to be worth printing: code, configuration, and the
# term-centric KB text an ontology sibling holds.  A name in a sibling's prose is
# not a caller — the engine's own vocabulary is discussed in every README and
# design note beside it, and a report that lists those buries the call sites
# under them.  `--all-files` lifts the scoping for a token whose whole audience
# is prose (a message fragment somebody quotes in a runbook, say).
SCAN_GLOBS=('*.clj' '*.cljc' '*.cljs' '*.edn' '*.txt' '*.sh' '*.py' '*.java'
            '*.sql' '*.yml' '*.yaml')

section=""
limit=5
strict=0
all_files=0
roots=()

# The header, from under the shebang to the last comment line before the code.
# Read by shape rather than by line number: a fixed range silently truncates the
# moment somebody adds a paragraph above it, and `--strict` fell off the end of
# `--help` that way — the one flag whose description had just grown.
usage() { awk 'NR == 1 { next } /^#/ { print; next } { exit }' "$0"; }

while [[ $# -gt 0 ]]; do
  case "$1" in
    --section)   section="${2:-}"; shift 2 ;;
    --root)      roots+=("${2:-}"); shift 2 ;;
    --limit)     limit="${2:-5}"; shift 2 ;;
    --strict)    strict=1; shift ;;
    --all-files) all_files=1; shift ;;
    -h|--help)   usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 2 ;;
  esac
done

# Where the siblings live, when nothing named a root: the directory holding the
# MAIN checkout. `--git-common-dir` rather than the toplevel, so a run from a git
# worktree (several writers share this tree) still resolves to the siblings beside
# the repository rather than to the worktree's own parent, which holds none.
if [[ ${#roots[@]} -eq 0 ]]; then
  common="$(git rev-parse --path-format=absolute --git-common-dir 2>/dev/null)"
  [[ -n "$common" ]] || common="$(git rev-parse --show-toplevel 2>/dev/null)/.git"
  roots=("$(dirname "$(dirname "$common")")")
fi

# A token prints inside backticks, as the changelog writes it. In a variable
# rather than inline: shellcheck reads a backtick inside a single-quoted printf
# format as a command substitution somebody forgot to escape (SC2016), and a
# suppression per printf is more noise than the variable is.
BQ='`'

color=0
case "$(printf '%s' "${VAELII_COLOR:-}" | tr '[:upper:]' '[:lower:]')" in
  always) color=1 ;;
  never)  color=0 ;;
  *) [[ -z "${NO_COLOR:-}" && -z "${CI:-}" \
        && ( -t 1 || ( -n "${TERM:-}" && "${TERM:-}" != dumb ) ) ]] && color=1 ;;
esac
if [[ $color -eq 1 ]]; then
  BOLD=$'\e[1m'; DIM=$'\e[2m'; YELLOW=$'\e[33m'; RST=$'\e[0m'
else
  BOLD=''; DIM=''; YELLOW=''; RST=''
fi

# ── the siblings actually on this machine ──────────────────────────────────
present_names=(); present_dirs=(); absent=()
for name in "${SIBLINGS[@]}"; do
  found=""
  for r in "${roots[@]}"; do
    [[ -d "$r/$name" ]] && { found="$r/$name"; break; }
  done
  if [[ -n "$found" ]]; then
    present_names+=("$name"); present_dirs+=("$found")
  else
    absent+=("$name")
  fi
done

# ── scan <dir> <token> — file:line:text, one per hit ───────────────────────
#
# Tracked files only where the directory is a checkout: an untracked tree is a
# build output or a scratch corpus, and one of those is 471 GB. `-w` so a token
# matches a whole name — `:out` is not `:output`, and `ask?` is not `task`.
scan() {
  local dir="$1" token="$2" g
  local paths=() includes=()
  if [[ $all_files -eq 0 ]]; then
    for g in "${SCAN_GLOBS[@]}"; do paths+=("$g"); includes+=("--include=$g"); done
  else
    paths=('.')
  fi
  if git -C "$dir" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    git -C "$dir" grep -I -F -w -n --no-color -e "$token" -- "${paths[@]}" 2>/dev/null
  elif [[ ${#includes[@]} -gt 0 ]]; then
    grep -rInFw "${includes[@]}" --exclude-dir=.git --exclude-dir=target \
         --exclude-dir=checkouts --exclude-dir=scratch --exclude-dir=node_modules \
         -e "$token" "$dir" 2>/dev/null | sed "s|^$dir/||"
  else
    grep -rInFw --exclude-dir=.git --exclude-dir=target --exclude-dir=checkouts \
         --exclude-dir=scratch --exclude-dir=node_modules \
         -e "$token" "$dir" 2>/dev/null | sed "s|^$dir/||"
  fi
  return 0
}

# ── parse the section into a record stream ─────────────────────────────────
#
#   E <class> <headline>   one per changelog entry
#   T <token>              one per backticked token on that entry's *Breaks:* lines
records="$(mktemp -t vaelii-breaks.XXXXXX)"
trap 'rm -f "$records"' EXIT

awk -v want="$section" '
# The headline is the entry claim — the bold run an entry opens with, which
# wraps across lines as often as not, so it is read off the whole body rather
# than off the first line.
function headline(   h) {
  h = body
  gsub(/\n +/, " ", h)
  sub(/^- /, "", h)
  if (h ~ /^\*\*/) { sub(/^\*\*/, "", h); sub(/\*\*.*/, "", h) }
  else             { sub(/\. .*/, "", h) }
  gsub(/`/, "", h)
  if (length(h) > 96) h = substr(h, 1, 93) "..."
  return h
}
# The class of the entries below a `### ` heading is the first word of the heading,
# lowercased: `### Breaking`, `### Fix: storage`.  An entry above every such
# heading in its section states no class.
function flush(   i, cls, cw, headlined) {
  if (!started) return
  cw  = heading_class
  cls = "other"
  if (body ~ /\*\*Breaking:/ || cw == "breaking") cls = "breaking"
  else if (body ~ /\*\*Refusal:/ || cw == "refusal") cls = "refusal"
  # THE CLASS DECIDES THE RELEASE NUMBER, so an unreadable one may not pass as
  # Additive by default.  The two tests above match a word; everything else they
  # see is "other" — which is what Additive and Fix look like, and what a typo
  # looks like too, so `### Braeking` would skip the Breaking treatment silently,
  # which is the wrong direction to fail in.  An entry states its class in its
  # headline or in the `### ` heading above it, and the word in the heading has to be
  # one CONTRIBUTING §3.8 defines.  Additive and Fix are both "other" here on
  # purpose: neither owes a `*Breaks:*` or a `*Migration:*` line, so the checks
  # below have nothing to ask them, and the class check alone reads the word.
  headlined = (body ~ /^- \*\*(Breaking|Refusal):/)
  if (cw == "") {
    if (!headlined) printf "X\t%s\t%s\n", headline(), "states no class"
  } else if (cw !~ /^(breaking|refusal|additive|fix|internal|neither|none)$/) {
    printf "X\t%s\t%s\n", headline(), "unknown class `" cw "`"
  }
  # An entry under a weaker heading that names a stronger class in its body —
  # "Additive for the reading; **Breaking** for the refusal message" — is classified
  # `other`, and its `*Breaks:*` tokens are never put to a sibling.  The class decides
  # the release number, so such an entry goes under the stronger heading.
  if (cls != "breaking" && body ~ /\*\*Breaking\*\*/)
    printf "X\t%s\t%s\n", headline(), "names **Breaking** in its body but sits under `" cw "` — move it under ### Breaking"
  if (cls != "breaking" && cls != "refusal" && body ~ /\*\*Refusal\*\*/)
    printf "X\t%s\t%s\n", headline(), "names **Refusal** in its body but sits under `" cw "` — move it under ### Refusal"
  # §3.8 asks a Breaking or Refusal entry for a migration line, and nothing read
  # it until now: the sibling sweep answers "who does this break", and a caller
  # who reads the answer next needs "what do I write instead".
  if ((cls == "breaking" || cls == "refusal") && body !~ /\*Migration:\*/)
    printf "X\t%s\t%s\n", headline(), "no *Migration:* line"
  printf "E\t%s\t%s\n", cls, headline()
  for (i = 1; i <= ntok; i++) printf "T\t%s\n", tok[i]
  started = 0; ntok = 0; body = ""
}
/^## / {
  if (insec) { flush(); insec = 0; exit }
  hdr = substr($0, 4)
  ver = hdr; sub(/ .*/, "", ver)
  if (want == "" || ver == want || (want == "unreleased" && hdr ~ /unreleased/)) {
    insec = 1; matched = 1
  }
  next
}
!insec { next }
/^### / { flush(); heading_class = tolower($2); sub(/[^a-z].*/, "", heading_class); next }
# A col-0 line that is not a bullet ends the entry it follows: a section may
# carry a lead paragraph and a table between its entries.
/^[^ ]/ && !/^- / { flush(); next }
/^- / { flush(); started = 1; body = "" }
started {
  body = (body == "" ? $0 : body "\n" $0)
  if ($0 ~ /\*Breaks:\*/) {
    s = $0
    sub(/.*\*Breaks:\*/, "", s)
    while (match(s, /`[^`]+`/)) {
      tok[++ntok] = substr(s, RSTART + 1, RLENGTH - 2)
      s = substr(s, RSTART + RLENGTH)
    }
  }
}
END { flush(); if (!matched) exit 3 }
' CHANGELOG.md >"$records"
awk_rc=$?
if [[ $awk_rc -eq 3 ]]; then
  echo "no changelog section matches --section ${section:-<the first one>}" >&2
  exit 2
fi

# The section header, for the banner — the same choice the awk above made.
header="$(grep -m1 '^## ' CHANGELOG.md)"
if [[ -n "$section" ]]; then
  header="$(grep -m1 "^## ${section} " CHANGELOG.md)"
  [[ -n "$header" ]] || header="$(grep -m1 '^## .*unreleased' CHANGELOG.md)"
fi

printf '%sbreaking-siblings%s  %s\n' "$BOLD" "$RST" "${header#\#\# }"
if [[ ${#present_names[@]} -gt 0 ]]; then
  printf '  %sread: %s%s\n' "$DIM" "${present_names[*]}" "$RST"
else
  printf '  %sread: no sibling checkout under %s%s\n' "$DIM" "${roots[*]}" "$RST"
fi
[[ ${#absent[@]} -gt 0 ]] &&
  printf '  %snot cloned here, so unchecked: %s%s\n' "$DIM" "${absent[*]}" "$RST"
echo

entries=0; unhooked=0; with_hits=0; total_hits=0
cls=""; head=""; toks=(); malformed=()

report_entry() {
  local i dir name hits shown n token entry_hits=0
  [[ "$cls" == "breaking" || "$cls" == "refusal" ]] || return 0
  entries=$((entries + 1))
  printf '%s%s%s\n' "$BOLD" "$head" "$RST"
  if [[ ${#toks[@]} -eq 0 ]]; then
    printf '  %s! no *Breaks:* line — nothing to check this entry against%s\n\n' \
           "$YELLOW" "$RST"
    unhooked=$((unhooked + 1))
    return 0
  fi
  local quiet=() token_hits body line
  for token in "${toks[@]}"; do
    token_hits=0; body=""
    for ((i = 0; i < ${#present_dirs[@]}; i++)); do
      dir="${present_dirs[$i]}"; name="${present_names[$i]}"
      hits="$(scan "$dir" "$token")"
      [[ -n "$hits" ]] || continue
      n="$(printf '%s\n' "$hits" | wc -l | tr -d ' ')"
      token_hits=$((token_hits + n))
      # awk rather than `head`, which closes the pipe on its Nth line and leaves
      # the printf feeding it writing to a broken one.
      if [[ "$limit" -gt 0 ]]; then
        shown="$(printf '%s\n' "$hits" | awk -v n="$limit" 'NR <= n')"
      else
        shown="$hits"
      fi
      while IFS= read -r line; do
        body+="$(printf '      %-16s %s' "$name" "${line:0:120}")"$'\n'
      done <<<"$shown"
      if [[ "$limit" -gt 0 && "$n" -gt "$limit" ]]; then
        body+="$(printf '      %-16s %s… %d more%s' "$name" "$DIM" "$((n - limit))" "$RST")"$'\n'
      fi
    done
    # A token nothing names is a line of report and no information, so the
    # quiet ones are one line between them at the end of the entry.
    if [[ $token_hits -eq 0 ]]; then
      quiet+=("$token")
    else
      entry_hits=$((entry_hits + token_hits)); total_hits=$((total_hits + token_hits))
      printf '  %s%s%s\n%s' "$BQ" "$token" "$BQ" "$body"
    fi
  done
  if [[ ${#quiet[@]} -gt 0 ]]; then
    printf '  %sno sibling names: %s%s%s%s\n' "$DIM" "$BQ" \
           "$(printf "%s${BQ}, ${BQ}" "${quiet[@]}" | sed "s/${BQ}, ${BQ}\$//")" \
           "$BQ" "$RST"
  fi
  [[ $entry_hits -gt 0 ]] && with_hits=$((with_hits + 1))
  echo
  return 0
}

while IFS=$'\t' read -r kind a b; do
  case "$kind" in
    E) report_entry; cls="$a"; head="$b"; toks=() ;;
    T) toks+=("$a") ;;
    X) malformed+=("$b — $a") ;;
  esac
done <"$records"
report_entry

printf '%s%d Breaking/Refusal entries, %d with sibling hits, %d hits in all%s\n' \
       "$BOLD" "$entries" "$with_hits" "$total_hits" "$RST"
bad=0
if [[ ${#malformed[@]} -gt 0 ]]; then
  printf '%s%d entry(ies) the class check refuses:%s\n' "$YELLOW" "${#malformed[@]}" "$RST"
  printf '  %s\n' "${malformed[@]}"
  printf '%sthe class decides the release number, so an entry stating one this does not\n' "$DIM"
  printf 'know is read as Additive by everything downstream. CONTRIBUTING §3.8 has the\n'
  printf 'five: Breaking, Refusal, Additive, Fix, Internal — "neither label" and "none" also spell\n'
  printf 'Additive.%s\n' "$RST"
  bad=1
fi
if [[ $unhooked -gt 0 ]]; then
  printf '%s%d entry(ies) carry no *Breaks:* line%s\n' "$YELLOW" "$unhooked" "$RST"
  bad=1
fi
[[ $bad -eq 1 && $strict -eq 1 ]] && exit 1
printf '%sa hit is a place to look; no hit is not proof — this greps names, and a\n'  "$DIM"
printf 'sibling can depend on a behaviour without spelling one.%s\n' "$RST"
exit 0
}
