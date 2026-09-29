# Schur numbers S(k)

`f(k)` is the largest `N` such that `{1, …, N}` can be partitioned into `k` sum-free
parts — where sum-free forbids `x + y = z` within a part, **including** `x = y`, so `2x = z`
is also forbidden.

`nMin = 1`.

## Conventions — these differ between sources

- **OEIS A045652** (used here): max-partitionable, giving `S(4) = 44`.
- **OEIS A030126**: least-forcing, equal to `A045652 + 1`. This is exactly the bare
  `sInf {N | Forces k N}` in our definition, before the `− 1`.
- **OEIS A072842**: *weak* Schur numbers, which forbid only `x ≠ y` solutions. A
  different object — do not conflate.

Bare notation `S(k)` is ambiguous by one between the first two conventions; state which
you mean.

## Known values

**Reporting only. These are never a source of theorems** (`docs/DESIGN.md` §2.2): proving
`S(5) = 160` in Lean would mean redoing Heule's SAT proof.

| k | f(k) | source |
|---|---|---|
| 1 | 1 | trivial |
| 2 | 4 | exhaustive |
| 3 | 13 | exhaustive |
| 4 | 44 | Golomb & Baumert, *Backtrack Programming*, JACM 12:4 (1965) |
| 5 | 160 | Heule 2017, DRAT-verified |

`S(6)` is unknown, with `536 ≤ S(6) ≤ 1836`.

Citation: OEIS A045652.

## Formalisation status

`f` is defined in `Def.lean` as `sInf {N | Forces k N} − 1`, keeping a single `sInf` idiom
across the least-`N` problems while landing on the literature numbers.

Mathlib has nothing here: `grep` for `SumFree`, `IsSumFree` or `schurNumber` returns
nothing, and every `Schur` hit is Schur's lemma for modules or the Schur complement.

## Well posed

`WellPosed k` — Schur's theorem — is proved in `Finite.lean`, via the classical reduction:
colour the edge `{i, j}` of `K_N` by `c(|i − j|)`; a monochromatic triangle `i < j < l`
yields `x = j − i`, `y = l − j`, `z = l − i` with `x + y = z`, all of the same colour.

That needs `R_k(3)`, the **`k`-colour** Ramsey number for triangles, and the finite Ramsey
theorem in `SqueezeBench/Problems/Ramsey/` is **2-colour** — `Forces` is phrased with
`G` and `Gᶜ`, which cannot express three or more colours. Rather than generalise that
development, `Finite.lean` proves the triangle case directly as `MonoTriangle`, by
pigeonhole on the edges at one vertex: some colour class of the `3(k+1)! − 1` incident
edges has at least `3·k!` members, and either it contains an edge of the same colour —
closing a triangle — or it uses one colour fewer and the induction applies. That is shorter
than the generalisation and gives the better bound `R_k(3) ≤ 3·k!`.

## Seeded records

Both directions are seeded, in `Records/Lower/V000/` and `Records/Upper/V000/`.

| direction | bound | source |
|---|---|---|
| lower | `(3^k − 1)/2` | the tripling construction, from `S(k+1) ≥ 3·S(k) + 1` |
| upper | `3·k! − 2` | `R_k(3) ≤ 3·k!`, then `S(k) ≤ R_k(3) − 2` |

`schurColour` realises the lower bound as an explicit colouring. Writing
`M = (3^(k-1) − 1)/2`, the range `[1, 3M+1]` splits into `[1, M]` carrying the previous
colouring, `[M+1, 2M+1]` carrying one fresh colour, and `[2M+2, 3M+1]` carrying the
previous colouring translated by `2M+1`.

The **translation** `x ↦ x + (2M+1)` is used rather than the reflection `x ↦ 3M+2−x` that
older write-ups of this construction use. Both reach the same block and give the same
bound, but the translation keeps natural subtraction out of three of the four sum-freeness
cases.

Note `3^k − 1` is **not** a lower bound — `3² − 1 = 8 > 4 = S(2)`. Neither record needs a
`pin`: both are valid at `k = 0`.

What the pair brackets, against the known values above:

| k | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|
| lower | 1 | 4 | 13 | 40 | 121 |
| f(k) | 1 | 4 | 13 | 44 | 160 |
| upper | 1 | 4 | 16 | 70 | 358 |

Both records are exact at `k = 1, 2`, and the lower record is exact at `k = 3`.

## Where the next improvement lies

The upper side. Sharpening the pigeonhole recurrence to `R_k(3) ≤ k(R_{k-1}(3) − 1) + 2`
and solving it gives `R_k(3) ≤ ⌊e·k!⌋ + 1`, hence `S(k) ≤ ⌊e·k!⌋ − 1`, computable as
`2·k! − 1 + ∑_{i=2}^{k} k!/i!`. The graph argument is already in place; only the arithmetic
changes.

## Current state

| | |
|---|---|
| Well posed | **yes** — `wellPosed` proved |
| Lower record | `Records/Lower/V003/` — beats V002 at witness `7` (trial claude-fable; based on V002, 2026-09-25) |
| Upper record | `Records/Upper/V003/` — beats V002 at witness `3` (baseline claude-opus-5; based on V001, V002, 2026-09-24) |
| Live | yes |

## Record history

One row per accepted version, oldest first, appended by `lake exe squeeze accept`.
The author is the `name` in the record's `metadata.toml`.

### Lower

| version | date | author | witness | value at the witness |
|---|---|---|---|---|
| V001 | 2026-09-24 | baseline claude-opus-5; based on V000 | 4 | 40 → 44 |
| V002 | 2026-09-25 | trial claude-fable; based on V001 | 5 | 133 → 160 |
| V003 | 2026-09-25 | trial claude-fable; based on V002 | 7 | 1680 → 1696 |

### Upper

| version | date | author | witness | value at the witness |
|---|---|---|---|---|
| V001 | 2026-09-24 | baseline claude-opus-5; based on V000 | 4 | 70 → 64 |
| V002 | 2026-09-24 | baseline claude-opus-5; based on V001 | 3 | 15 → 14 |
| V003 | 2026-09-24 | baseline claude-opus-5; based on V001, V002 | 3 | 14 → 13 |
