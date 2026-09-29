#!/usr/bin/env bash
# Build or fetch the four verification tools at their pinned revisions, into .tools/.
# Idempotent and non-interactive: safe to re-run, and what CI calls before
# `lake exe squeeze verify`.
#
#   comparator, lean4export   Lake dependencies (lakefile.toml / lake-manifest.json);
#                             built with `lake build comparator lean4export`, then COPIED
#                             out of .lake/ — see "why the copy" below.
#   landrun                   `go install` at the commit in scripts/tools.lock
#   nanoda_bin                `cargo build --release --locked` at the commit in tools.lock
#
# Why the copy. Comparator builds the untrusted Solution inside a landrun sandbox with
# .lake/ writable, and only afterwards runs lean4export on the result. A Solution's
# elaboration-time IO could therefore overwrite .lake/packages/lean4export/.lake/build/bin/
# lean4export, and a forged export defeats the statement comparison. .tools/ lives under
# the project root, which that sandbox mounts read-only. The source still arrives through
# Lake; only the built artifact leaves the writable tree.
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd); cd "$ROOT"
LOCK=scripts/tools.lock
TOOLS="$ROOT/.tools"; BIN="$TOOLS/bin"; STAMP="$TOOLS/stamp"
mkdir -p "$BIN"

die()  { echo "bootstrap: $*" >&2; exit 1; }
step() { echo "== $*"; }
lock() { sed -n "s/^[[:space:]]*$1[[:space:]]*=[[:space:]]*\"\{0,1\}\([^\"#]*\)\"\{0,1\}.*/\1/p" "$LOCK" | head -1 | tr -d '[:space:]'; }
stamp_get() { sed -n "s/^$1=//p" "$STAMP" 2>/dev/null | head -1; }
stamp_set() { touch "$STAMP"; grep -v "^$1=" "$STAMP" > "$STAMP.new" || true; echo "$1=$2" >> "$STAMP.new"; mv "$STAMP.new" "$STAMP"; }
manifest_rev() { python3 -c "import json,sys; print(next(p['rev'] for p in json.load(open('lake-manifest.json'))['packages'] if p['name']==sys.argv[1]))" "$1"; }

# ---------------------------------------------------------------- 1. the Lean tools
step "comparator + lean4export (Lake, pinned by lake-manifest.json)"
lake build comparator lean4export >/dev/null
CMP_SRC=.lake/packages/Comparator/.lake/build/bin/comparator
EXP_SRC=.lake/packages/lean4export/.lake/build/bin/lean4export
[ -x "$CMP_SRC" ] && [ -x "$EXP_SRC" ] || die "lake build did not produce both executables"

# ---------------------------------------------------------------- 2. toolchain guard
# Every surveyed adopter checks lean4export's toolchain against the project's; none checks
# Comparator's. Both are checked here: a Lean release with different .olean headers on
# either side makes the export meaningless.
step "toolchain guard"
ours=$(tr -d '[:space:]' < lean-toolchain)
for pkg in Comparator lean4export; do
  theirs=$(tr -d '[:space:]' < ".lake/packages/$pkg/lean-toolchain")
  [ "$ours" = "$theirs" ] || die "lean-toolchain is $ours but $pkg targets $theirs — bump the Comparator rev in lakefile.toml to the tag matching lean-toolchain, then lake update Comparator"
done
echo "   all on $ours"

# ---------------------------------------------------------------- 3. copy out of .lake
step "copying comparator and lean4export out of the sandbox-writable tree"
for pair in "$CMP_SRC:comparator" "$EXP_SRC:lean4export"; do
  src=${pair%%:*}; dst="$BIN/${pair##*:}"
  if [ -f "$dst" ] && cmp -s "$src" "$dst"; then echo "   $dst up to date"; else install -m 755 "$src" "$dst"; echo "   $dst"; fi
done
stamp_set comparator "$(manifest_rev Comparator)"; stamp_set lean4export "$(manifest_rev lean4export)"

# ---------------------------------------------------------------- 4. a Go >= 1.24
step "go toolchain"
go_ok() { command -v "$1" >/dev/null 2>&1 && "$1" version | awk '{v=$3; sub(/^go/,"",v); split(v,a,"."); exit !(a[1]>1 || (a[1]==1 && a[2]>=24))}'; }
GO=""
if go_ok go; then GO=$(command -v go); echo "   system $(go version)"
elif go_ok "$TOOLS/go/bin/go"; then GO="$TOOLS/go/bin/go"; echo "   pinned $($GO version)"
else
  ver=$(lock go-version); url=$(lock go-url); sha=$(lock go-sha256)
  echo "   no Go >= 1.24 found; fetching official go$ver"
  curl -sSL -o "$TOOLS/go.tgz" "$url"
  echo "$sha  $TOOLS/go.tgz" | sha256sum -c --quiet - || die "go$ver tarball sha256 mismatch"
  rm -rf "$TOOLS/go"; tar -C "$TOOLS" -xzf "$TOOLS/go.tgz"; rm -f "$TOOLS/go.tgz"
  GO="$TOOLS/go/bin/go"; echo "   $($GO version)"
fi

# ---------------------------------------------------------------- 5. landrun
step "landrun"
LR_COMMIT=$(lock landrun-commit); LR_MOD=$(lock landrun-module)
if [ -x "$BIN/landrun" ] && [ "$(stamp_get landrun)" = "$LR_COMMIT" ]; then echo "   up to date at $LR_COMMIT"
else
  # GOTOOLCHAIN=local: never let Go auto-download a different toolchain behind our back.
  GOBIN="$BIN" GOPATH="$TOOLS/gopath" GOMODCACHE="$TOOLS/go-mod" GOCACHE="$TOOLS/go-build" \
    GOTOOLCHAIN=local CGO_ENABLED=0 "$GO" install "$LR_MOD@$LR_COMMIT"
  stamp_set landrun "$LR_COMMIT"; echo "   $BIN/landrun ($("$BIN/landrun" --version 2>&1 | head -1))"
fi

# ---------------------------------------------------------------- 6. nanoda
step "nanoda (from source, --locked)"
ND_COMMIT=$(lock nanoda-commit); ND_REPO=$(lock nanoda-repo); ND_SRC="$TOOLS/src/nanoda_lib"
if [ -x "$BIN/nanoda_bin" ] && [ "$(stamp_get nanoda)" = "$ND_COMMIT" ]; then echo "   up to date at $ND_COMMIT"
else
  command -v cargo >/dev/null || die "cargo is required to build nanoda (https://rustup.rs)"
  if [ ! -d "$ND_SRC/.git" ]; then mkdir -p "$TOOLS/src"; git clone --quiet --filter=blob:none "$ND_REPO" "$ND_SRC"; fi
  git -C "$ND_SRC" fetch --quiet --depth 1 origin "$ND_COMMIT"
  git -C "$ND_SRC" checkout --quiet --detach "$ND_COMMIT"
  (cd "$ND_SRC" && cargo build --release --locked --quiet)
  install -m 755 "$ND_SRC/target/release/nanoda_bin" "$BIN/nanoda_bin"
  stamp_set nanoda "$ND_COMMIT"; echo "   $BIN/nanoda_bin"
fi

# ---------------------------------------------------------------- 7. env.sh
# Defaults only: a variable already set in the caller's environment wins.
cat > "$TOOLS/env.sh" <<EOF
# generated by scripts/bootstrap_tools.sh — source, do not edit
: "\${COMPARATOR_BIN:=$BIN/comparator}";           export COMPARATOR_BIN
: "\${COMPARATOR_LEAN4EXPORT:=$BIN/lean4export}";  export COMPARATOR_LEAN4EXPORT
: "\${COMPARATOR_NANODA:=$BIN/nanoda_bin}";        export COMPARATOR_NANODA
: "\${SQUEEZE_LANDRUN_BIN:=$BIN/landrun}";         export SQUEEZE_LANDRUN_BIN
: "\${COMPARATOR_LANDRUN:=$ROOT/scripts/landrun-wrapper.sh}"; export COMPARATOR_LANDRUN
EOF
step "done — tools in $BIN, environment in $TOOLS/env.sh"
sed -n 's/^: "\${\([A-Z0-9_]*\):=\(.*\)}".*/   \1=\2/p' "$TOOLS/env.sh"
