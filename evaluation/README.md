# Baseline evaluation

The records after each problem's seed were produced by AI agents playing the submitter, one
agent per track, all with the same prompt. This folder holds what is needed to repeat that.
The second phase, a continuation from the baseline's records with newer models, is described in `continuation/README.md`.

> **Note.** The prompts and reports here are kept exactly as they were used. The repository has
> changed since, so they would not apply as written today: some files they cite, such as
> `docs/DESIGN.md`, no longer exist. Their content is now in `docs/CONTRIBUTING.md`.

| file | what it is |
|---|---|
| `baseline-prompt.md` | the prompt template; `{P}`, `{DIR}`, `{DIR_LC}`, `{NAME}`, `{ORACLES}`, `{MEM}` and `{MINUTES}` are filled in per session |
| `run.sh` | runs one model on one track, session after session |
| `setup.sh` | prepares a fresh clone: checks the machine, fetches Mathlib, builds, bootstraps the verifier |
| `launch.sh` | runs one model on every track, several tracks at a time |
| `runs/<P>-<Dir>/REPORT.md` | the track's report, written by the agents and shared by all its sessions |
| `runs/<P>-<Dir>/<model>/s<k>/` | per session: the filled-in `prompt.md` and `run.json` (model, wall time, how it ended, versions accepted, peak memory and OOM kills, turns and tokens) |
| `runs/<P>-<Dir>/<model>/summary.json` | per track: sessions, time used, versions accepted, and whether it ended on the time limit or a plateau |

## Protocol

- **Agent**: Claude Code in headless mode (`claude -p`), tools `Bash`, `Read`, `Write`, `Edit`,
  `WebSearch`, `WebFetch`. The session is isolated from the machine's configuration: project
  settings only, no MCP servers, no auto-memory and no `CLAUDE.md` files, so the agent sees the
  prompt and the project and nothing else.
- **Loop**: the agent writes a record, proves `valid`, `improves` and `strict`, runs
  `lake exe squeeze verify`, and on `ACCEPT` runs `lake exe squeeze accept`; then it starts the
  next version. It is its own maintainer: no pull requests and no git.
- **Sessions**: when a session ends, whether the agent stopped or its time ran out, `run.sh`
  deletes any version that was not accepted and starts a new session from the current record,
  with the track's `REPORT.md` as its notes. It stops when the track's time limit is used up, or
  when `trials` sessions in a row accepted nothing (a plateau). A session stopped by the
  subscription's usage limit is not counted as a trial; `run.sh` waits 15 minutes and goes on.
- **Time**: the time limit is the track's total over all its sessions. The prompt gives each
  session the time left. `run.sh` stops the agent only while holding the problem's accept lock,
  so an `accept` is never cut off.
- **Memory**: each agent runs in its own cgroup (`systemd-run --user --scope`) with the memory
  limit and no swap, for itself and everything it starts, including `squeeze verify`, whose fuel
  check alone peaks near 7 GB. Past the limit the kernel kills the largest process in that
  cgroup only, and the agent continues. At the end of a session `run.sh` stops the cgroup, which
  also ends searches left in the background. Scratch files go to `.lake/scratch/<P>-<Dir>/`
  (`$TMPDIR`). The Comparator runs outside it, in its own unit with a 16 GB limit, and so does
  `verify`'s computation-budget probe, after the Comparator, with 8 GB; so the machine needs up
  to `parallel agents × memory limit + 16 GB` per running `verify`.
- **Parallelism**: `launch.sh` keeps a fixed number of tracks running, in one checkout. `verify`
  runs concurrently; `accept`, which writes the problem's README and Challenges, is serialised
  per problem by `flock` on `.lake/locks/<P>.lock`.
- **Start**: every track starts from its seed `V000` with `V001` open.
- **Credit**: `baseline <model>`.
- **Web**: agents search the literature online, so a rerun may find different sources; each
  report lists the citations used.

## Running

On Linux with systemd, from the project root. `setup.sh` checks the machine (the programs
needed, a systemd user session, Landlock for the Comparator's sandbox), then runs
`lake exe cache get`, `lake build` and `lake exe squeeze bootstrap`; log in to `claude` once.

```sh
evaluation/setup.sh
evaluation/launch.sh claude-opus-5 2h 2 16G 8     # model, time per track, trials, memory, parallel agents
evaluation/run.sh ExC4 Lower claude-opus-5 2h 2 16G   # one track only
```

`launch.sh` first checks that `systemd-run --user` works, that `claude` is logged in, that the
project builds and that `verify` accepts a seed record. If `systemd-run --user` fails on a machine
reached only by SSH, run `loginctl enable-linger $USER` and log in again. To keep the run going
after the terminal closes, start it as a user service and follow its log:

```sh
systemd-run --user --unit=squeeze-launch --same-dir -E PATH="$PATH" \
  evaluation/launch.sh claude-opus-5 2h 2 16G 8
journalctl --user -u squeeze-launch -f
systemctl --user stop squeeze-launch 'squeeze-eval-*.scope'     # stop everything
```

A restart skips the tracks that have a `summary.json` and continues the others from their last
session.

The agent's full transcript is written to `.lake/transcripts/`, outside the published files: it
records the machine's configuration and paths, so it is kept locally and not released.
