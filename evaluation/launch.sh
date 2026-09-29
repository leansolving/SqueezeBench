#!/usr/bin/env bash
# Run one model on every track of every problem, a fixed number of tracks at a time.
# usage: evaluation/launch.sh <model> <timelimit> <trials> <mem-limit> <parallel-agents>
#   the first four are passed to run.sh for each track; a restart skips the tracks already done
set -uo pipefail
cd "$(dirname "$0")/.."
(( $# == 5 )) || { sed -n 3,4p "$0" >&2; exit 2; }
MODEL=$1; LIMIT=$2; TRIALS=$3; MEM=$4; JOBS=$5
say() { echo "$(date '+%F %T') $*"; }
die() { say "launch: $*" >&2; exit 1; }

# checks before hours of unattended work
systemd-run --user --scope --quiet -p MemoryMax=64M true 2>/dev/null ||
  die "systemd-run --user does not work here; run 'loginctl enable-linger $USER' and log in again"
claude auth status 2>/dev/null | grep -q '"loggedIn": true' || die "claude is not logged in; run 'claude' once"
[ -x .tools/bin/comparator ] || die "the Comparator is missing; run 'lake exe squeeze bootstrap'"
say "building the project"
lake build > /dev/null || die "lake build failed"
say "verifying a seed record, to check the Comparator and its sandbox"
lake exe squeeze verify SqueezeBench/Problems/Tutorial/Records/Lower/V000 --accepted > /dev/null 2>&1 ||
  die "squeeze verify fails on the Tutorial seed; run it by hand to see why"
mem_gb=$(awk '/MemTotal/ {print int($2 / 2^20)}' /proc/meminfo)
if [[ $MEM == *G ]] && (( JOBS * ${MEM%G} + 16 > mem_gb )); then
  say "warning: $JOBS agents at $MEM plus one Comparator may need more than this machine's ${mem_gb} GB"
fi

# every track of every problem but the tutorial
tracks=()
for toml in Challenges/*/problem.toml; do
  P=$(basename "$(dirname "$toml")")
  [ "$P" = Tutorial ] && continue
  for d in $(sed -n 's/^directions *= *\[\(.*\)\]/\1/p' "$toml" | tr -d '",'); do tracks+=("$P ${d^}"); done
done
say "model $MODEL: ${#tracks[@]} tracks, $JOBS at a time, $LIMIT and $TRIALS trials each, $MEM per agent"

# a track that cannot start at all stops the whole run, instead of marking every track done
abort=.lake/launch-abort; rm -f "$abort"
for t in "${tracks[@]}"; do
  [ -e "$abort" ] && { say "a track could not run; stopping the rest"; break; }
  while (( $(jobs -rp | wc -l) >= JOBS )); do wait -n; done
  # shellcheck disable=SC2086
  { evaluation/run.sh $t "$MODEL" "$LIMIT" "$TRIALS" "$MEM" || touch "$abort"; } &
  sleep 5
done
wait
say "all tracks done"
