# Golomb, upper record, V013

By trial claude-fable.

## How the bound was obtained

**Bound.** `record = min(V012.record, small)` where `small` tabulates the best known lengths
for `m = 81, …, 100`:

| m | 81 | 82 | 83 | 84 | 85 | 86 | 87 | 88 | 89 | 90 |
|---|---|---|---|---|---|---|---|---|---|---|
| | 5717 | 5814 | 6020 | 6159 | 6410 | 6537 | 6708 | 6745 | 6778 | 6967 |

| m | 91 | 92 | 93 | 94 | 95 | 96 | 97 | 98 | 99 | 100 |
|---|---|---|---|---|---|---|---|---|---|---|
| | 7542 | 7617 | 7726 | 7884 | 7967 | 8121 | 8357 | 8462 | 8540 | 8831 |

and is the previous record elsewhere. Witness `n₀ = 81`: `6480 → 5717`. The record improves
at all 20 values, by 10–15 % (`m = 100`: `9998 → 8831`).

**Source.** As V012: T. Rokicki and G. Dogon, *Larger Golomb rulers* (G4G12, 2016), data at
`cube20.org/golomb` (`golomb-all-00`, `rulers-all-00.zip`). The constructions are Singer
(`pp`) with `q = 83, 83, 83, 83, 89, 89, 89, 89, 97, 97, 97, 97, 97, 101, 101, 101` and Bose
(`ap`) with `q = 89, 89, 97, 97` (`m = 85, 86, 91, 96`), each with the best multiplier and
rotation. None is known to be optimal.

**Why.** The continuation of V012's table, in the one further version the budget allows with
V007's checker: each entry costs `≈ 0.92 m²` heartbeats (`f100`: 8652), 146k in all.

## How the proofs were obtained

As V012: the rulers were downloaded, re-checked in Python and typeset by the same generator
script; each entry is one `decide +kernel` through V007's `f_le_of_rulerCheck`, and the `if`
chain is discharged by `by_cases`. Nothing new was proved.

## Setup

- Tools: Claude Fable 5.1 (Claude Code CLI); Lean 4.31.0 with the pinned Mathlib. Python 3
  for downloading, checking and typesetting the rulers.
- Machine: 96 cores (`nproc`), 755 GB RAM reported by `free -g` (32 GB allotted),
  Linux 6.8.0-124-generic.
- Time spent: about 15 minutes.
