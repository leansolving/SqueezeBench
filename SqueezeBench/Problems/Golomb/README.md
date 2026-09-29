# Optimal Golomb rulers

An `m`-mark Golomb ruler is a set of `m` integers whose pairwise differences are all
distinct — equivalently a Sidon (B₂) set. `f(m)` is the least possible length, with marks
normalised to start at `0`, so the length is the largest mark.

Example: `{0, 1, 4, 6}` is a 4-mark ruler of length 6. Its differences are
`1, 4, 6, 3, 5, 2` — all distinct — and no 4-mark ruler is shorter, so `f(4) = 6`.

Exact values are known through `m = 28` and the problem is open beyond that.

`nMin = 1`.

## Known values

**Reporting only. These are never a source of theorems** (`docs/DESIGN.md` §2.2): proving
`G(28) = 585` in Lean would mean redoing distributed.net's exhaustive search.

Differences are the **positive** ones; the signed differences are never all distinct,
since `a − b` and `b − a` both occur. OEIS A003022 has offset 2, so `G(1) = 0` below is
the natural trivial extension rather than an OEIS term.

| m | f(m) | source |
|---|---|---|
| 1 | 0 | trivial |
| 2 | 1 | trivial |
| 3 | 3 | exhaustive |
| 4 | 6 | exhaustive |
| 5 | 11 | exhaustive |
| 6 | 17 | exhaustive |
| 7 | 25 | exhaustive |
| 8 | 34 | exhaustive |
| 9 | 44 | exhaustive |
| 10 | 55 | exhaustive |
| 11 | 72 | exhaustive |
| 27 | 553 | distributed.net OGR-27, 2014 |
| 28 | 585 | distributed.net OGR-28, 2022 |

Citation: OEIS A003022.

## Formalisation status

`f` is defined in `Def.lean` as

```lean
sInf {L | ∃ S, S ⊆ range (L+1) ∧ S.card = m ∧ IsSidon S ∧ L ∈ S}
```

**Well posed.** `rulerLengths_nonempty` is proved, via the binary ruler
`{0, 1, 3, 7, …, 2^(m-1) − 1}`, whose Sidon property comes from uniqueness of binary
representations (`pow2_sidon`). Both bound directions are therefore open, and `le_f` is
unconditional.

Note the definition does not require `0 ∈ S`. That is harmless: Sidon sets are
translation-invariant, so any minimiser translates down to one containing `0`, and the
infimum is unchanged.

Nothing Golomb- or Sidon-related exists in Mathlib, so all of this is built from scratch.

## Seeded records

Both directions are seeded, in `Records/Lower/V000/` and `Records/Upper/V000/`.

| direction | bound | source |
|---|---|---|
| lower | `m(m−1)/2` | the `C(m,2)` gaps are distinct and lie in `[1, L]` |
| upper | `min (2^(m−1) − 1) (2m³ − m² − 2m + 1)`, and `11`, `17` at `m = 5, 6` | binary ruler, quadratic ruler, two optimal rulers |

The lower bound injects `S.powersetCard 2` into `Icc 1 L` by the gap `max − min`, written
`2 * T.sup id - T.sum id` so that it is total in `T`. Distinctness is exactly the Sidon
property: `b − a = d − c` rearranges to `b + c = a + d`.

Neither upper construction dominates — the binary ruler `{0,1,3,7,…}` wins below about
`m = 13`, the quadratic ruler `aᵢ = 2m²·i + i²` above it — so the record folds both with
`minWith`. The multiplier is `2m²` rather than `m²` because `IsSidon` is stated on **sums**,
so the residue to separate is `i² + j² ≤ 2(m−1)²`. On top of that the record is patched with two
optimal rulers found by search, `{0, 1, 4, 9, 11}` at `m = 5` and `{0, 1, 4, 10, 12, 17}` at
`m = 6`.

What the pair brackets, against the known values above:

| m | 1 | 2 | 3 | 4 | 5 | 6 | 8 | 11 |
|---|---|---|---|---|---|---|---|---|
| lower | 0 | 1 | 3 | 6 | 10 | 15 | 28 | 55 |
| f(m) | 0 | 1 | 3 | 6 | 11 | 17 | 34 | 72 |
| upper | 0 | 1 | 3 | 7 | 11 | 17 | 127 | 1023 |

Both records are exact at `m = 1, 2, 3`; the lower record is also exact at `m = 4`, and the
upper record at `m = 5` and `m = 6` (the two patches).

## Where the next improvement lies

The upper side. The literature's `m² − m` needs the Singer difference-set construction and
only applies when `m − 1` is a prime power, so it is not a total bound; the Erdős–Turán
construction `{2pk + (k² mod p)}` gives a total `O(m²)` bound but needs a prime between `m`
and `2m`, so it routes through Bertrand's postulate (`Nat.exists_prime_lt_and_le_two_mul`).

## Current state

| | |
|---|---|
| Well posed | **yes** — `wellPosed` proved |
| Lower record | `Records/Lower/V008/` — beats V007 at witness `100` (trial claude-opus-5.5; based on V001, V006, V007, 2026-09-25) |
| Upper record | `Records/Upper/V013/` — beats V012 at witness `81` (trial claude-fable; based on V007, 2026-09-24) |
| Live | yes |

## Record history

One row per accepted version, oldest first, appended by `lake exe squeeze accept`.
The author is the `name` in the record's `metadata.toml`.

### Upper

| version | date | author | witness | value at the witness |
|---|---|---|---|---|
| V001 | 2026-09-24 | baseline claude-opus-5; based on V000 | 10 | 511 → 379 |
| V002 | 2026-09-24 | baseline claude-opus-5; based on V001 | 10 | 379 → 202 |
| V003 | 2026-09-24 | baseline claude-opus-5; based on V002, V000 | 10 | 202 → 55 |
| V004 | 2026-09-24 | baseline claude-opus-5; based on V003 | 12 | 290 → 85 |
| V005 | 2026-09-24 | baseline claude-opus-5; based on V004 | 16 | 514 → 177 |
| V006 | 2026-09-24 | trial claude-fable; based on V002 | 18 | 650 → 341 |
| V007 | 2026-09-24 | trial claude-fable; based on V003, V005 | 28 | 811 → 585 |
| V008 | 2026-09-24 | trial claude-fable; based on V002, V006 | 29 | 929 → 868 |
| V009 | 2026-09-24 | trial claude-fable; based on V002, V008 | 31 | 1110 → 929 |
| V010 | 2026-09-24 | trial claude-fable; based on V008, V009 | 30 | 898 → 841 |
| V011 | 2026-09-24 | trial claude-fable; based on V008, V009, V010 | 33 | 1183 → 1024 |
| V012 | 2026-09-24 | trial claude-fable; based on V007 | 29 | 811 → 623 |
| V013 | 2026-09-24 | trial claude-fable; based on V007 | 81 | 6480 → 5717 |

### Lower

| version | date | author | witness | value at the witness |
|---|---|---|---|---|
| V001 | 2026-09-24 | baseline claude-opus-5; based on V000 | 11 | 55 → 63 |
| V002 | 2026-09-24 | baseline claude-opus-5; based on V000, V001 | 9 | 38 → 40 |
| V003 | 2026-09-24 | baseline claude-opus-5; based on V000, V001, V002 | 8 | 30 → 31 |
| V004 | 2026-09-24 | baseline claude-opus-5; based on V000, V001, V002, V003 | 12 | 78 → 79 |
| V005 | 2026-09-24 | baseline claude-opus-5; based on V000, V001, V002, V003, V004 | 18 | 197 → 198 |
| V006 | 2026-09-25 | trial claude-opus-5.5; based on V001, V005 | 100 | 8143 → 8148 |
| V007 | 2026-09-25 | trial claude-opus-5.5; based on V001, V006 | 100 | 8148 → 8165 |
| V008 | 2026-09-25 | trial claude-opus-5.5; based on V001, V006, V007 | 100 | 8165 → 8210 |
