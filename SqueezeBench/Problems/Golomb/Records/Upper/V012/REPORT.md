# Golomb, upper record, V012

By trial claude-fable.

## How the bound was obtained

**Bound.** `record = min(V011.record, small)` where `small` tabulates the best known lengths
for `m = 29, …, 80`:

| m | 29 | 30 | 31 | 32 | 33 | 34 | 35 | 36 | 37 | 38 | 39 | 40 | 41 | 42 | 43 | 44 | 45 | 46 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| | 623 | 680 | 747 | 784 | 859 | 938 | 987 | 1005 | 1099 | 1146 | 1252 | 1282 | 1305 | 1397 | 1507 | 1596 | 1687 | 1703 |

| m | 47 | 48 | 49 | 50 | 51 | 52 | 53 | 54 | 55 | 56 | 57 | 58 | 59 | 60 | 61 | 62 | 63 | 64 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| | 1804 | 1887 | 1958 | 2094 | 2190 | 2270 | 2347 | 2373 | 2598 | 2725 | 2773 | 2851 | 2911 | 3019 | 3134 | 3215 | 3391 | 3527 |

| m | 65 | 66 | 67 | 68 | 69 | 70 | 71 | 72 | 73 | 74 | 75 | 76 | 77 | 78 | 79 | 80 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| | 3593 | 3757 | 3819 | 3956 | 4145 | 4217 | 4330 | 4473 | 4513 | 4753 | 4982 | 5089 | 5204 | 5299 | 5408 | 5563 |

and is the previous record elsewhere. Witness `n₀ = 29`: `811 → 623`. The record improves
at all 52 values, by 11–25 % (`m = 50`: `2401 → 2094`; `m = 80`: `6241 → 5563`).

**Source.** T. Rokicki and G. Dogon, *Larger Golomb rulers* (Gathering 4 Gardner 12, 2016)
and their data at `cube20.org/golomb`: the files `golomb-all-00` (marks, length,
construction, `q`, multiplier) and `rulers-all-00.zip` (the rulers). Each ruler is a window
of `m` consecutive residues of a Singer (`pp`, `q + 1` residues modulo `q² + q + 1`) or Bose
(`ap`, `q` residues modulo `q² − 1`) modular ruler for a prime power `q` near `m`, after the
best multiplier and rotation found by exhaustive search over all units modulo the modulus;
the parameters used here are `q = 29, 29, 31, 31, 32, 37, 37 (ap), 37 (ap), 37, 37, 41,
41 (ap), 41, 41, 43 (ap), 43, 47, 47, 47 (ap), 49, 49, 49, 53, 53, 53, 53, 59 × 6, 61 (ap),
61, 64, 64, 64, 67, 67, 67, 71, 71, 71, 73, 73, 73, 79 × 6` for `m = 29, …, 80`. These agree
with J. B. Shearer's older table of shortest known rulers and are the best known; none is
known to be optimal (`f` is known only through `m = 28`).

**Why.** V008–V011 give the general bound `(m−1)·q`, the *average* window of these modular
rulers; the *best* window is much shorter, and for `m ≤ 80` it is explicit data the kernel
can check. An improvement at 52 consecutive `m`, each by several hundred to a thousand.

## How the proofs were obtained

By an AI agent (see Setup). The rulers were downloaded (Python `urllib`/`unzip`), re-checked
in Python (length, `m` marks, distinct positive differences) and written into `Proof.lean`
by a short generator script; the mathematics is V007's `f_le_of_rulerCheck` (bitset check of
all pairwise sums, kernel-evaluated), so each entry is one `decide +kernel`. The cost is about
`0.92 m²` heartbeats per entry (`f80`: 5723), 163k in all for the 52 entries, which is why the
table stops at `m = 80`; `m = 81, …, 100` fit in one more version. The `if` chain is
discharged by `by_cases` as in V007.

An independent Python re-derivation of the Singer/Bose windows for prime powers `q ≤ 61`
(all multipliers and rotations, own `GF(q³)`/`GF(q²)` arithmetic) reproduced the published
length at all 34 of the tabulated `m` whose best ruler has `q ≤ 61`; it was not needed for
the proof and is not part of it.

## Setup

- Tools: Claude Fable 5.1 (Claude Code CLI) writing all Lean; Lean 4.31.0 with the pinned
  Mathlib. Python 3 for downloading, checking and typesetting the rulers.
- Machine: 96 cores (`nproc`), 755 GB RAM reported by `free -g` (32 GB allotted),
  Linux 6.8.0-124-generic.
- Time spent: about one hour, including the literature search.
