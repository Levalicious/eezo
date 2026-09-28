#!/bin/sh
# ci/deps.sh - fetch the repositories this one depends on, at the commits deps.lock pins, as siblings of this checkout
# (the workspace layout every mkfile and test script assumes: ../libeezo, ../eezo, ...). A dependant fetches the versions
# it pinned, nothing else; bumping a pin is an ordinary commit.
set -e
here=$(cd "$(dirname "$0")/.." && pwd); ws=$(dirname "$here")
while read -r name sha; do
    case "$name" in ''|'#'*) continue;; esac
    [ -d "$ws/$name/.git" ] || git clone -q "https://github.com/Levalicious/$name.git" "$ws/$name"
    git -C "$ws/$name" fetch -q origin "$sha"
    git -C "$ws/$name" checkout -q "$sha"
    echo "$name at $(git -C "$ws/$name" rev-parse --short HEAD)"
done < "$here/deps.lock"
