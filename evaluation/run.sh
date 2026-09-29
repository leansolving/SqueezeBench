#!/usr/bin/env bash
# Run one model on one track: headless Claude Code sessions until the time is used up or it plateaus.
# usage: evaluation/run.sh <Problem> <Lower|Upper> <model> <timelimit> <trials> <mem-limit>
#   timelimit  total for the track over all sessions, e.g. 90m or 2h
#   trials     stop after this many sessions in a row without an accepted version
#   mem-limit  memory of the agent and everything it starts, e.g. 16G; verify's fuel check alone needs ~7G
set -uo pipefail
cd "$(dirname "$0")/.."
(( $# == 6 )) || { sed -n 3,6p "$0" >&2; exit 2; }
secs() { case $1 in *h) echo $(( ${1%h} * 3600 ));; *m) echo $(( ${1%m} * 60 ));; *s) echo "${1%s}";; *) echo "$1";; esac; }
P=$1; D=$2; MODEL=$3; LIMIT=$(secs "$4"); TRIALS=$5; MEM=$6
NAME="baseline $MODEL"
# the track's REPORT.md is shared by all sessions and models; each session has its own directory
track=evaluation/runs/$P-$D
out=$track/$MODEL
unit=squeeze-eval-$P-$D.scope
# accept writes the problem's README and Challenges, so it takes the problem's lock
lock=.lake/locks/$P.lock
# scratch files of one track stay apart from other tracks and from /tmp
scratch=.lake/scratch/$P-$D
mkdir -p "$out" .lake/transcripts .lake/locks "$scratch"
say() { echo "$(date '+%F %T') $P $D: $*"; }
die() { say "$*" >&2; exit 1; }
# OOMPolicy on a scope needs a recent systemd; without it the whole agent is stopped on an OOM
props=(-p "MemoryMax=$MEM" -p MemorySwapMax=0 -p TimeoutStopSec=10)
systemd-run --user --scope --quiet "${props[@]}" -p OOMPolicy=continue true 2>/dev/null &&
  props+=(-p OOMPolicy=continue)
systemd-run --user --scope --quiet "${props[@]}" true 2>/dev/null ||
  die "systemd-run --user --scope does not work here; the agent needs it for its memory limit"
field() { python3 -c "import json,sys; print(json.load(open(sys.argv[1]))[sys.argv[2]])" "$1" "$2"; }
opened() { ls "Challenges/$P/$D"/V*.lean | wc -l; }

[ -e "$out/summary.json" ] && { say "already done"; exit 0; }

# a version whose next Challenge does not exist was never accepted: remove it
prune() {
  local v k
  for v in "SqueezeBench/Problems/$P/Records/$D"/V*; do
    k=${v##*/V}
    [ -e "Challenges/$P/$D/$(printf 'V%03d' $((10#$k + 1))).lean" ] || rm -r "$v"
  done
}

# one session: fill in the prompt, start the agent in its own cgroup, stop it safely, write run.json
session() {
  local s=s$1 left=$2
  local dir=$out/$s log=.lake/transcripts/$P-$D-$MODEL-s$1.jsonl
  mkdir -p "$dir"
  local oracles
  oracles=$(sed -n 's/^oracles *= *\[\(.*\)\]/\1/p' "Challenges/$P/problem.toml" | tr '"' '`')
  sed -e "s|{P}|$P|g" -e "s|{DIR}|$D|g" -e "s|{DIR_LC}|${D,,}|g" -e "s|{NAME}|$NAME|g" \
      -e "s|{ORACLES}|$oracles|g" -e "s|{MEM}|$MEM|g" -e "s|{MINUTES}|$(( left / 60 ))|g" \
      evaluation/baseline-prompt.md > "$dir/prompt.md"

  # the agent sees only the prompt and this project: no user settings, memory, CLAUDE.md or MCP servers
  # past MEM the kernel kills the largest process of this cgroup only, and the agent carries on
  systemctl --user reset-failed "$unit" 2>/dev/null
  local before start pid cg mem peak=0 ooms=0 stopped=self
  before=$(opened); start=$(date +%s)
  CLAUDE_CODE_DISABLE_AUTO_MEMORY=1 CLAUDE_CODE_DISABLE_CLAUDE_MDS=1 TMPDIR=$PWD/$scratch \
  systemd-run --user --scope --quiet --unit="$unit" "${props[@]}" \
    claude -p "$(cat "$dir/prompt.md")" --model "$MODEL" --setting-sources project \
    --strict-mcp-config --no-session-persistence --allowedTools Bash Read Write Edit WebSearch WebFetch \
    --output-format stream-json --verbose --include-partial-messages < /dev/null > "$log" &
  pid=$!
  sleep 2
  cg=/sys/fs/cgroup$(systemctl --user show "$unit" -p ControlGroup --value)
  # the cgroup goes away with its last process, so its peak memory and OOM kills are read while it runs;
  # kernels before 5.19 have no memory.peak, and there the highest memory.current seen is kept
  while kill -0 "$pid" 2>/dev/null && (( $(date +%s) - start < left )); do
    mem=$(cat "$cg/memory.peak" 2>/dev/null || cat "$cg/memory.current" 2>/dev/null || echo 0)
    (( mem > peak )) && peak=$mem
    ooms=$(sed -n 's/^oom_kill //p' "$cg/memory.events" 2>/dev/null || echo "$ooms")
    sleep 10
  done
  kill -0 "$pid" 2>/dev/null && stopped=limit
  # under the accept lock, so an accept is never cut off, stop everything the agent started
  flock "$lock" systemctl --user stop "$unit" 2>/dev/null
  wait "$pid" 2>/dev/null
  local seconds=$(( $(date +%s) - start ))

  prune

  # only numbers are kept; the raw transcript identifies the machine, so it stays in .lake/
  python3 - "$log" "$seconds" "$stopped" "$MODEL" "$MEM" "$peak" "$ooms" "$(( $(opened) - before ))" \
    > "$dir/run.json" <<'PY'
import json, re, sys
log, seconds, stopped, model, mem, peak, ooms, accepted = sys.argv[1:]
keys = ("input_tokens", "output_tokens", "cache_creation_input_tokens", "cache_read_input_tokens")
results, calls, models = [], 0, set()
summed = dict.fromkeys(keys, 0)
for line in open(log):
    try: e = json.loads(line)
    except ValueError: continue
    # a session with background tasks writes a result each time it goes idle, each with its own totals
    if e.get("type") == "result": results.append(e)
    ev = e.get("event", {}) if e.get("type") == "stream_event" else {}
    if ev.get("type") == "message_start": models.add(ev["message"].get("model"))
    # each model request ends with a message_delta carrying its final usage
    if ev.get("type") == "message_delta":
        calls += 1
        for k in keys: summed[k] += ev.get("usage", {}).get(k) or 0
# a session in which the model never answered did not run at all
if not results and not calls:
    stopped = "failed"
# the totals are summed over the results; a session stopped at the time limit writes no result,
# and then they are summed from the stream
if results:
    turns = sum(r.get("num_turns") or 0 for r in results)
    usage = {k: sum(r.get("usage", {}).get(k) or 0 for r in results) for k in keys}
    models = {m for r in results for m in r.get("modelUsage", {})}
else:
    turns, usage = calls, summed
# a session cut short by the subscription's usage limit is not a failed trial
last = results[-1] if results else {}
if last.get("is_error") and (last.get("api_error_status") == 429
                             or re.search(r"limit", str(last.get("result", "")), re.I)):
    stopped = "usage-limit"
print(json.dumps({"model": model, "models_used": sorted(models - {None}),
                  "seconds": int(seconds), "stopped": stopped, "accepted": int(accepted),
                  "memory": {"limit": mem, "peak_mb": int(peak) // 2**20, "oom_kills": int(ooms)},
                  "turns": turns,
                  "tokens": usage}, indent=2))
PY
}

# sessions until the time is used up or TRIALS sessions in a row accept nothing;
# a track cut off by a restart continues from the sessions it already has
used=0; n=0; idle=0
count() {
  case $(field "$1" stopped) in
    usage-limit) return 1 ;;
    *) if (( $(field "$1" accepted) > 0 )); then idle=0; else idle=$(( idle + 1 )); fi ;;
  esac
}
while [ -e "$out/s$(( n + 1 ))/run.json" ]; do
  n=$(( n + 1 ))
  used=$(( used + $(field "$out/s$n/run.json" seconds) ))
  count "$out/s$n/run.json"
done
# a session cut off by a restart may have left a version that was never accepted
prune
while (( idle < TRIALS && LIMIT - used >= 300 )); do
  n=$(( n + 1 ))
  say "session $n, $(( (LIMIT - used) / 60 )) min left"
  session "$n" $(( LIMIT - used ))
  j=$out/s$n/run.json
  used=$(( used + $(field "$j" seconds) ))
  say "session $n ended ($(field "$j" stopped)), $(field "$j" accepted) accepted"
  # a session that never reached the model is not a plateau: stop the track and say so
  [ "$(field "$j" stopped)" = failed ] && die "the agent did not start; see .lake/transcripts/$P-$D-$MODEL-s$n.jsonl"
  # the usage limit is not a plateau: wait for it to reset, without counting the wait
  count "$j" || sleep 900
done
ended=time; (( idle >= TRIALS )) && ended=plateau
python3 - "$out" "$n" "$used" "$ended" > "$out/summary.json" <<'PY'
import json, sys, pathlib
out, n, used, ended = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
runs = [json.loads((pathlib.Path(out) / f"s{i}" / "run.json").read_text()) for i in range(1, n + 1)]
print(json.dumps({"sessions": n, "seconds": used, "ended": ended,
                  "accepted": sum(r["accepted"] for r in runs),
                  "oom_kills": sum(r["memory"]["oom_kills"] for r in runs)}, indent=2))
PY
say "done: $ended after $n sessions, $(field "$out/summary.json" accepted) accepted"
