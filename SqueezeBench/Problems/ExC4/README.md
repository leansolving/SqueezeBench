# Graphs with no four-cycle — `ex(n; C₄)`

`f(n)` is the largest number of edges in a simple graph on `n` vertices containing no `C₄` as a
subgraph. Triangles are allowed; only the 4-cycle is forbidden.

The asymptotics are settled at the leading term, `f(n) ~ ½·n^{3/2}`: the upper bound is
Kővári–Sós–Turán (1954), sharpened by Reiman (1958) to `f(n) ≤ n(1 + √(4n−3))/4`, and the
matching construction is the polarity graph of Erdős–Rényi–Sós and, independently, Brown (1966).
What remains open is the exact value for general `n` and the correct linear term: Ma–Yang (2023)
disproved the conjectured `½·n^{3/2} + n/4 + O(√n)`.

`nMin = 1`.

## Known values

**Reporting only. These are never a source of theorems.**

| n | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|---|---|---|---|
| f(n) | 0 | 1 | 3 | 4 | 6 | 7 | 9 | 11 | 13 | 16 |

| n | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 |
|---|---|---|---|---|---|---|---|---|---|---|
| f(n) | 18 | 21 | 24 | 27 | 30 | 33 | 36 | 39 | 42 | 46 |

Exact values are known for `n ≤ 40`; from `n = 41` the literature has only bounds
(`132 ≤ f(41) ≤ 133`). Provenance: Clapham–Flockhart–Sheehan 1989 for `n ≤ 21`,
Yang–Rowlinson 1992 for `22 ≤ n ≤ 31`, Shao–Xu–Xu for `n = 32`, and McKay's computer searches
for `33 ≤ n ≤ 40`.

At the orders `n = q² + q + 1` with `q` a prime power, Füredi (1996) proved the polarity graph
optimal for every `q > 13`, so `f(q² + q + 1) = q(q+1)²/2` there.

Citation: OEIS A006855. The values for `n ≤ 9` were also re-derived here by exhaustive search
and agree.

## Formalisation status

`f` is `SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph 4)`, pinned to `0` below `nMin`.
Mathlib's `extremalNumber n H` is the supremum of `#G.edgeFinset` over graphs `G` on `Fin n`
with `H.Free G`, and `Free` is containment by subgraph, which is the intended reading.

`f` is noncomputable and total by construction — a supremum over a `Fintype`, with the empty
graph always qualifying — so there is no `Finite.lean` and no well-posedness obligation. Because
`f` is noncomputable the known values cannot be checked by `decide`, so they are cited above —
except `f(1) = 0` and `f(3) = 3`, which are proved in `Def.lean` and agree with A006855.

`Def.lean` supplies:

| lemma | use |
|---|---|
| `le_f_of_free` | a lower record exhibits a `C₄`-free graph and counts its edges |
| `f_le_of_forall_free` | an upper record bounds the edges of every `C₄`-free graph |
| `free_cycleGraph_four_iff` | `C₄`-freeness ↔ no two distinct vertices have two distinct common neighbours |
| `f_le_choose_two` | the ambient bound `C(n, 2)` |

`free_cycleGraph_four_iff` is the lemma that makes submissions tractable: it turns a statement
about copies of `cycleGraph 4` into the counting condition both directions actually use.

## Seeded records

Both directions are seeded, in `Records/Lower/V000/` and `Records/Upper/V000/`, with trivial
bounds.

| direction | record | source |
|---|---|---|
| lower | `0` | the empty graph |
| upper | `C(n, 2)` | `f_le_choose_two` |

## Current state

| | |
|---|---|
| Well posed | **yes** — total by construction |
| Lower record | `Records/Lower/V008/` — beats V007 at witness `109` (trial claude-fable; based on V006, V007, 2026-09-24) |
| Upper record | `Records/Upper/V005/` — beats V004 at witness `15` (trial claude-fable; based on V001, V003, V004, 2026-09-25) |
| Live | yes |

## Record history

One row per accepted version, oldest first, appended by `lake exe squeeze accept`.
The author is the `name` in the record's `metadata.toml`.

### Lower

| version | date | author | witness | value at the witness |
|---|---|---|---|---|
| V001 | 2026-09-24 | baseline claude-opus-5 | 2 | 0 → 1 |
| V002 | 2026-09-24 | baseline claude-opus-5; based on V001 | 3 | 2 → 3 |
| V003 | 2026-09-24 | baseline claude-opus-5; based on V002 | 21 | 30 → 50 |
| V004 | 2026-09-24 | baseline claude-opus-5; based on V003 | 31 | 50 → 90 |
| V005 | 2026-09-24 | baseline claude-opus-5; based on V004 | 57 | 100 → 224 |
| V006 | 2026-09-24 | trial claude-fable | 133 | 448 → 792 |
| V007 | 2026-09-24 | trial claude-fable; based on V005, V006 | 40 | 115 → 127 |
| V008 | 2026-09-24 | trial claude-fable; based on V006, V007 | 109 | 540 → 549 |

### Upper

| version | date | author | witness | value at the witness |
|---|---|---|---|---|
| V001 | 2026-09-24 | baseline claude-opus-5 | 10 | 45 → 17 |
| V002 | 2026-09-24 | baseline claude-opus-5; based on V001 | 15 | 32 → 31 |
| V003 | 2026-09-24 | baseline claude-opus-5; based on V001, V002 | 6 | 8 → 7 |
| V004 | 2026-09-25 | trial claude-fable; based on V001, V003 | 27 | 75 → 74 |
| V005 | 2026-09-25 | trial claude-fable; based on V001, V003, V004 | 15 | 31 → 30 |
