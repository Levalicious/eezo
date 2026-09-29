#!/bin/bash
# ci/drift.sh - what this repository pins that its upstream has moved past (the scheduled drift job, .github/workflows/drift.yml).
#
# A dependant pins what it depends on - deps.lock (the sibling repositories its CI fetches), the uses: lines of its
# workflows (the mk and mkroot actions), and in the umbrella the submodules - and CI fetches exactly those. Nothing
# propagates by itself; this reports, as a markdown table on stdout (nothing when every pin is current), the pins
# whose upstream main has moved on in substance. A change upstream that touches only its own pins or CI (deps.lock,
# .github/, ci/) is not substance: repositories that pin each other (stdlib and its checkers) would otherwise never
# be current at once.
set -e
here=$(cd "$(dirname "$0")/.." && pwd)
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
pins() {   # name sha, one per line
    [ -f "$here/deps.lock" ] && grep -v '^\s*\(#\|$\)' "$here/deps.lock" | awk '{print $1, $2}'
    cat "$here"/.github/workflows/*.yml 2>/dev/null | grep -o 'Levalicious/[A-Za-z0-9_-]*@[0-9a-f]\{40\}' | sed 's|Levalicious/||; s|@| |' | sort -u
    git -C "$here" ls-tree HEAD 2>/dev/null | awk '$2 == "commit" {print $4, $3}'
}
rows=""
while read -r name sha; do
    [ -n "$name" ] || continue
    head=$(git ls-remote "https://github.com/Levalicious/$name.git" refs/heads/main | cut -f1)
    [ -n "$head" ] && [ "$head" != "$sha" ] || continue
    bare="$tmp/$name.git"
    [ -d "$bare" ] || git clone -q --bare --filter=blob:none "https://github.com/Levalicious/$name.git" "$bare"
    files=$(git -C "$bare" diff --name-only "$sha" "$head" | grep -v '^deps\.lock$\|^\.github/\|^ci/' || true)
    [ -n "$files" ] || continue
    behind=$(git -C "$bare" rev-list --count "$sha..$head")
    rows="$rows| $name | \`${sha:0:7}\` | \`${head:0:7}\` | $behind | $(echo "$files" | wc -l) |"$'\n'
done < <(pins | sort -u)
[ -z "$rows" ] && exit 0
printf '| pinned | at | upstream main | commits behind | files changed |\n|---|---|---|---|---|\n%s' "$rows"
