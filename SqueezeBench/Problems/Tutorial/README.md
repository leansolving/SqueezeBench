# Tutorial: doubling-free subsets

`g(m)` is the largest size of a subset of `{1, …, m}` containing no element together with
its double. For example `g(5) = 4`, witnessed by `{1, 3, 4, 5}` — adding `2` would fail
because `1` is present, and `{1,2,3,4,5}` fails for the same reason.

This problem exists to exercise the submission pipeline: the three obligations, both record
idioms, and the admissibility gates. It is **not on any leaderboard**.

`nMin = 1`. Not live, by design.

## Why it is not a real benchmark problem

`g` is computable. That makes it a good tutorial — a contributor can prove `4 ≤ f 5` by
`decide` and watch the whole workflow run — and a bad benchmark, because the interesting
part of a real problem is precisely that `f` cannot be evaluated.

The ten real problems (listed in the project README) have noncomputable or intractable `f`, and each
needs its own formalisation before any bound can be stated.

## Known values

Unusually, these are not citations: `f` is computable here, so every value below is
machine-checked in `Def.lean` rather than taken on trust. That is exactly what makes this a
tutorial and not a benchmark problem.

| m | f(m) |
|---|---|
| 1 | 1 |
| 2 | 1 |
| 3 | 2 |
| 4 | 3 |
| 5 | 4 |
| 6 | 4 |
| 7 | 5 |
| 8 | 5 |
| 9 | 6 |
| 10 | 6 |
| 11 | 7 |

## Current state

| | |
|---|---|
| Lower record | `Records/Lower/V002/` — beats V001 at witness `6` (Pablo Manrique; based on V001, 2026-09-29) |
| Fixtures | `Fixtures/Tutorial/` — 14 test submissions, one or more per gate. They answer `V002` (one answers `V001`) and are judged against that version's Challenge, so new records do not affect them. Checked by `lake exe squeeze test` |
| Upper record | not seeded |
| Live | no |

## Record history

One row per accepted version, oldest first, appended by `lake exe squeeze accept`.
The author is the `name` in the record's `metadata.toml`.

### Lower

| version | date | author | witness | value at the witness |
|---|---|---|---|---|
| V001 | 2026-08-04 | Alice | 5 | 1 → 4 |
| V002 | 2026-09-29 | Pablo Manrique; based on V001 | 6 | 1 → 4 |
