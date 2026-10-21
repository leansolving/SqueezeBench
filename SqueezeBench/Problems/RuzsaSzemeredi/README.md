# The Ruzsa–Szemerédi number

`f(n)` is the largest number of **triangles** in a locally linear graph on `n` vertices — a
graph in which every edge lies in exactly one triangle.

The problem is the `(6,3)`-problem of Ruzsa and Szemerédi. Its growth is famously strange:
`f(n) = n²⁻ᵒ⁽¹⁾` but also `f(n) = o(n²)`, and pinning down the truth between those is open.

`nMin = 3`.

## A naming trap in Mathlib

Mathlib's docstrings for `ruzsaSzemerediNumber` say *"the maximum number of **edges** a locally
linear graph can have"*. The definition counts **triangles**:

```lean
Nat.findGreatest (fun m ↦ ∃ G (_ : DecidableRel G.Adj), #(G.cliqueFinset 3) = m ∧ G.LocallyLinear) …
```

`ruzsaSzemerediNumberNat_le : ≤ n.choose 3` confirms it — an edge count would be bounded by
`n.choose 2`. Since a locally linear graph has `#edges = 3 · #triangles`, taking the docstring
at face value gives a quantity three times too large. `f` here follows the definition. Worth
reporting upstream.

## Known values

**Reporting only. These are never a source of theorems.**

We have found few published values: the literature is about the asymptotics, and OEIS has no
entry. The values below were computed by us, by an exhaustive search.

| n | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| f(n) | 1 | 1 | 2 | 2 | 3 | 4 | 6 | 6 | 7 | 9 | 10 |

`f(9) = 6` is attained by the 3×3 rook's graph, whose triangles are its rows and columns.

`f` is `noncomputable`, and its defining predicate existentially quantifies a `DecidableRel`
instance, so it is not decidable either — small values cannot be obtained by `decide` the way
Roth's can. `f(3) = 1` is immediate and is proved in `Def.lean`.

## Formalisation status

`f` is `ruzsaSzemerediNumberNat`, pinned below `nMin`. Nothing is redefined. Total by
construction — a `Nat.findGreatest` over a `Fintype` — so there is no `Finite.lean`.

Transfer lemmas: `le_f_of_locallyLinear` (exhibit a locally linear graph, count its triangles)
and `f_le_choose_three`. `f_mono` carries a bound at one `n` to every larger one.

> **Mathlib's own lower bound cannot be a record.** `ruzsaSzemerediNumberNat_lower_bound` is
> stated over `ℝ` and routes through `Behrend.roth_lower_bound`, so it involves `Real.exp` and
> `Real.log` — noncomputable, while a record must be computable (gate 5). The same obstacle
> applies to `rothNumberNat_le_ruzsaSzemerediNumberNat`, which *is* ℕ-valued
> (`(2n+1) · r₃(n) ≤ f(6n+3)`) but routes through `rothNumberNat`, an exponential search that
> would blow the fuel budget. Both are listed as oracles for that reason.

## Seeded records

| direction | record | `n=3` | `n=6` | `n=9` |
|---|---|---|---|---|
| lower | `pin nMin 1` | **1** | 1 | 1 |
| upper | `C(n,3)` | **1** | 20 | 84 |

**The records meet at `n = 3`**: `f(3) = 1`, proved from both sides, so their conjunction
determines it. After that the gap opens immediately and widely.

The lower seed is `K₃`, which is locally linear with one triangle. Both facts about it are
concrete, so `decide` settles them; monotonicity does the rest.

## Current state

| | |
|---|---|
| Well posed | **yes** — total by construction |
| Lower record | `Records/Lower/V009/` — beats V008 at witness `15` (Pablo Manrique; based on V007, V008, 2026-10-02) |
| Upper record | `Records/Upper/V008/` — beats V007 at witness `40` (trial claude-fable; based on V001, V002, V003, V004, V005, V006, V007, 2026-09-25) |
| Live | yes |

## Record history

One row per accepted version, oldest first, appended by `lake exe squeeze accept`.
The author is the `name` in the record's `metadata.toml`.

### Lower

| version | date | author | witness | value at the witness |
|---|---|---|---|---|
| V001 | 2026-09-24 | baseline claude-opus-5 | 15 | 1 → 10 |
| V002 | 2026-09-24 | baseline claude-opus-5; based on V001 | 57 | 38 → 76 |
| V003 | 2026-09-24 | baseline claude-opus-5; based on V001, V002 | 165 | 440 → 550 |
| V004 | 2026-09-24 | baseline claude-opus-5; based on V001, V002, V003 | 249 | 830 → 1328 |
| V005 | 2026-09-24 | baseline claude-opus-5; based on V001, V003, V004 | 195 | 650 → 845 |
| V006 | 2026-09-24 | baseline claude-opus-5; based on V001, V004, V005 | 417 | 2502 → 2780 |
| V007 | 2026-09-25 | trial claude-fable; based on V006 | 729 | 7533 → 13608 |
| V008 | 2026-09-25 | trial claude-fable; based on V006, V007 | 21 | 14 → 21 |
| V009 | 2026-10-02 | Pablo Manrique; based on V007, V008 | 15 | 10 → 15 |

### Upper

| version | date | author | witness | value at the witness |
|---|---|---|---|---|
| V001 | 2026-09-24 | baseline claude-opus-5 | 6 | 20 → 5 |
| V002 | 2026-09-24 | baseline claude-opus-5; based on V001 | 6 | 5 → 4 |
| V003 | 2026-09-24 | baseline claude-opus-5; based on V001, V002 | 5 | 3 → 2 |
| V004 | 2026-09-24 | baseline claude-opus-5; based on V001, V002, V003 | 8 | 6 → 5 |
| V005 | 2026-09-24 | baseline claude-opus-5; based on V001, V002, V003, V004 | 7 | 4 → 3 |
| V006 | 2026-09-25 | trial claude-fable; based on V001, V002, V003, V004, V005 | 10 | 7 → 6 |
| V007 | 2026-09-25 | trial claude-fable; based on V001, V002, V003, V004, V005, V006 | 13 | 11 → 10 |
| V008 | 2026-09-25 | trial claude-fable; based on V001, V002, V003, V004, V005, V006, V007 | 40 | 93 → 92 |
