#!/usr/bin/env bash
# Prepare a fresh clone for the baseline evaluation: check the machine, then fetch Mathlib, build, and bootstrap the verifier.
# usage: evaluation/setup.sh
set -uo pipefail
cd "$(dirname "$0")/.."
missing=0
need() { command -v "$1" >/dev/null 2>&1 || { echo "missing: $1 — $2"; missing=1; }; }

need git     "install it with the system package manager"
need curl    "install it with the system package manager"
need python3 "install it with the system package manager"
need flock   "part of util-linux; install it with the system package manager"
need cc      "a C compiler, for cargo; e.g. sudo apt install build-essential"
need lake    "install elan: curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none"
need cargo   "install Rust: curl https://sh.rustup.rs -sSf | sh -s -- -y --profile minimal"
need claude  "install Claude Code: curl -fsSL https://claude.ai/install.sh | bash"
need systemd-run "the evaluation needs systemd"
if command -v systemd-run >/dev/null && ! systemd-run --user --scope --quiet -p MemoryMax=64M true 2>/dev/null; then
  echo "missing: a systemd user session — run 'loginctl enable-linger $USER', then log out and in again"; missing=1
fi
grep -qw landlock /sys/kernel/security/lsm 2>/dev/null ||
  { echo "missing: Landlock in the kernel, which the Comparator's sandbox (landrun) needs"; missing=1; }
(( missing )) && { echo "setup: install what is missing (open a new shell afterwards), then run this again"; exit 1; }

set -e
echo "== Mathlib cache";  lake exe cache get
echo "== build";          lake build
echo "== verifier tools"; lake exe squeeze bootstrap
set +e

claude auth status 2>/dev/null | grep -q '"loggedIn": true' ||
  echo "log in to Claude Code once: run 'claude' and follow the login"
mem_gb=$(awk '/MemTotal/ {print int($2 / 2^20)}' /proc/meminfo)
echo "ready: $(nproc) cores, ${mem_gb} GB; at 16G per agent and 16 GB for the Comparator, up to $(( (mem_gb - 16) / 16 )) agents at a time"
