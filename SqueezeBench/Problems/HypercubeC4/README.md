# `C₄`-free subgraphs of the hypercube — `ex(Qₙ, C₄)`

`f(n)` is the largest number of edges in a subgraph of the `n`-dimensional hypercube `Qₙ` that
contains no `C₄`. `Qₙ` has the `2ⁿ` binary words of length `n` as vertices, two words adjacent
when they differ in exactly one bit, and `n · 2ⁿ⁻¹` edges.

Every 4-cycle of `Qₙ` is a square: a word `x`, `x` with bit `i` flipped, `x` with bits `i` and
`j` flipped, `x` with bit `j` flipped, for `i ≠ j`. So `f(n)` is the number of edges left after
deleting as few edges as possible so that every square loses at least one.

This is Erdős Problem [#86](https://www.erdosproblems.com/86), open, with a \$100 prize. Erdős
conjectured `f(n) ≤ (½ + o(1)) · n2ⁿ⁻¹`. The best bounds are:

- **Lower:** `f(n) ≥ ½(n + √n) · 2ⁿ⁻¹` for `n = 4ʳ`, and `f(n) ≥ ½(n + 0.9√n) · 2ⁿ⁻¹` for all
  `n ≥ 9` — Brass, Harborth and Nienborg, *J. Graph Theory* 19 (1995) 17–23. This improves
  Guan's construction with `(n + 3) · 2ⁿ⁻²` edges plus lower-order terms, which both Chung
  (1992) and Erdős (1991) credit to Guan. The Erdős Problems page credits this `(½ + c/n)` bound
  to Erdős himself.
- **Upper:** edge density at most `0.60318`, i.e. `f(n) ≤ (0.60318 + o(1)) · n2ⁿ⁻¹` — Baber,
  arXiv:1201.3587, by flag algebras. Balogh, Hu, Lidický and Liu, *European J. Combin.* 35
  (2014) 75–85, give `0.6068 · n2ⁿ⁻¹`. The first bound of this kind is Chung, *J. Graph Theory*
  16 (1992) 273–286: `(α + o(1)) · n2ⁿ⁻¹`, where `α ≈ 0.623` is the root of
  `9α³ + 5α² − 5α − 1 = 0`.

The leading constant is open between `0.5` and `0.603`.

`nMin = 1`.

## Known values

**Reporting only. These are never a source of theorems.**

| n | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|
| `n2ⁿ⁻¹` (edges of `Qₙ`) | 1 | 4 | 12 | 32 | 80 | 192 | 448 |
| f(n) | 1 | 3 | 9 | 24 | 56 | 132 | 304–308 |

Citation: OEIS [A245762](https://oeis.org/A245762), offset 1. `f(6) = 132` is Harborth and
Nienborg, *Bull. ICA* 12 (1994) 55–60. At `n = 7`, the lower bound `304` is an explicit
construction (Minamoto, arXiv:2603.29127, 2026). The upper bound `308` is the averaging bound
below applied to `f(6) = 132`. The same construction paper gives `f(8) ≥ 680`.

Only 6 exact values are known, all transitions. The open case `n = 7` has a gap of 4.

## Formalisation status

Mathlib at the pin has no hypercube graph, so `Def.lean` defines one:
`hypercube n : SimpleGraph (Fin n → Bool)`, with adjacency `hammingDist x y = 1`.

`f` cannot reuse Mathlib's `extremalNumber`: that is a supremum over *every* graph on `Fin n`,
while here the graph must be a subgraph of a fixed host. `f` is defined the same way, a
supremum of `#G.edgeFinset` over `G ≤ hypercube n` with `(cycleGraph 4).Free G`, and pinned to
`0` below `nMin`. `Free` is Mathlib's containment by subgraph, the intended reading.

`f` is noncomputable and total by construction — a supremum over a `Fintype`, with the empty
graph always qualifying — so there is no `Finite.lean`. `f(1) = 1` and `f(2) = 3` are proved in
`Def.lean`; the rest are cited above.

The problem is self-contained: `Def.lean` imports only Mathlib and `Core`. The `C₄`
characterisation it shares with `ExC4` is copied, not imported.

`Def.lean` supplies:

| lemma | use |
|---|---|
| `le_f_of_free` | a lower record exhibits a `C₄`-free subgraph of the cube and counts its edges |
| `f_le_of_forall_free` | an upper record bounds the edges of every `C₄`-free subgraph of the cube |
| `free_cycleGraph_four_iff` | `C₄`-freeness ↔ no two distinct vertices have two distinct common neighbours (any graph) |
| `free_iff_not_hasSquare` | for `G ≤ hypercube n`: `C₄`-freeness ↔ `G` contains no whole square |
| `le_f_of_not_hasSquare`, `f_le_of_forall_not_hasSquare` | the transfer lemmas in terms of squares |
| `le_f_of_noTwoCommonNeighbours`, `f_le_of_forall_noTwoCommonNeighbours` | the transfer lemmas in terms of common neighbours |
| `f_le_card_edgeFinset_hypercube` | the ambient bound `f(n) ≤ #edges of Qₙ` |
| `hypercube_adj_iff` | adjacency in the cube is flipping one bit (`flip x i`) |

`free_iff_not_hasSquare` is the lemma submissions should use: it turns a statement about copies
of `cycleGraph 4` into a statement about squares, which is how both directions are argued.

## Seeded records

Both directions are seeded, in `Records/Lower/V000/` and `Records/Upper/V000/`, with trivial
bounds.

| direction | record | source |
|---|---|---|
| lower | `0` | the empty graph |
| upper | `C(2ⁿ, 2)` | `f_le_card_edgeFinset_hypercube` and `card_edgeFinset_le_card_choose_two` |

## Current state

| | |
|---|---|
| Well posed | **yes** — total by construction |
| Lower record | `Records/Lower/V008/` — beats V007 at witness `8` (SB maintainers; based on V001, V005, V007, 2026-10-22) |
| Upper record | `Records/Upper/V007/` — beats V006 at witness `12` (trial claude-fable; based on V002, V005, V006, 2026-09-25) |
| Live | yes |

## Record history

One row per accepted version, oldest first, appended by `lake exe squeeze accept`.
The author is the `name` in the record's `metadata.toml`.

### Upper

| version | date | author | witness | value at the witness |
|---|---|---|---|---|
| V001 | 2026-09-24 | baseline claude-opus-5 | 3 | 28 → 12 |
| V002 | 2026-09-24 | baseline claude-opus-5; based on V001 | 5 | 80 → 60 |
| V003 | 2026-09-24 | baseline claude-opus-5 | 2 | 4 → 3 |
| V004 | 2026-09-24 | baseline claude-opus-5; based on V002, V003 | 5 | 60 → 59 |
| V005 | 2026-09-24 | baseline claude-opus-5; based on V002, V004 | 5 | 59 → 58 |
| V006 | 2026-09-25 | trial claude-fable; based on V002, V005 | 7 | 320 → 306 |
| V007 | 2026-09-25 | trial claude-fable; based on V002, V005, V006 | 12 | 16286 → 16283 |

### Lower

| version | date | author | witness | value at the witness |
|---|---|---|---|---|
| V001 | 2026-09-24 | baseline claude-opus-5 | 6 | 0 → 96 |
| V002 | 2026-09-24 | baseline claude-opus-5; based on V001 | 6 | 96 → 112 |
| V003 | 2026-09-24 | baseline claude-opus-5; based on V002 | 4 | 20 → 24 |
| V004 | 2026-09-24 | baseline claude-opus-5; based on V003 | 5 | 48 → 55 |
| V005 | 2026-09-24 | baseline claude-opus-5; based on V001, V004 | 6 | 112 → 120 |
| V006 | 2026-09-25 | trial claude-fable; based on V001, V005 | 16 | 286720 → 327680 |
| V007 | 2026-09-25 | trial claude-fable; based on V006 | 7 | 288 → 304 |
| V008 | 2026-10-22 | SB maintainers; based on V001, V005, V007 | 8 | 672 → 682 |
