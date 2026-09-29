# Tutorial, lower record, V002

By Pablo Manrique.

This is a test submission. Its purpose is to exercise the pull-request pipeline, not to
contribute new mathematics.

## How the bound was obtained

The record patches V001 at `n = 6`, raising the value from `1` to `4`. The set `{1, 3, 4, 5}`
contains no element together with its double and lies in `{1, …, 6}`, so `f 6 ≥ 4`. It is the
set V001 used at `n = 5`. The value `4` is optimal: `Def.lean` of the problem checks `f 6 = 4`.

## How the proofs were obtained

An AI agent wrote all three proofs, following the patch idiom of CONTRIBUTING.

- `valid` is `patch_valid` applied to V001's `valid` and the lemma `four_le_f_six`. That lemma
  gives the set `{1, 3, 4, 5}` to `card_le_g` and checks by `decide` that it lies in
  `{1, …, 6}` and is doubling-free. It checks one set and does not search.
- `improves` and `strict` are `patch_improves` and `patch_strict`, with `decide` for the
  comparisons at `n = 6`.

Nothing was hard, and nothing was tried and abandoned. `squeeze budget-probe` reports 969
heartbeats for the whole file.

## Sources

None outside this repository. The record builds on V001 (listed in `based-on`).

## Setup

- Tools: Claude Code with the model Claude Fable 5.1; Lean 4.31.0 and Mathlib v4.31.0 as pinned.
- Machine: AMD Ryzen 5 PRO 8540U, 30 GB of memory, Ubuntu 24.04.
- Time spent: a few minutes. No computation ran outside Lean.
