# Ramsey, lower record, V009

By trial claude-fable.

## How the bound was obtained

A point patch: `f 5 ≥ 43`, the best known lower bound on `R(5,5)` (G. Exoo, *A lower bound
for R(5,5)*, J. Graph Theory 13 (1989) 97–98; `43 ≤ R(5,5) ≤ 46`). The witness graph is
one of the 656 known `(5,5,42)`-graphs — 42 vertices, no clique and no independent set of
size 5 — taken from the graph6 file `r55_42some.g6` on B. D. McKay's Ramsey graph data page
(users.cecs.anu.edu.au/~bdm/data/ramsey.html; McKay and Radziszowski, *Subgraph counting
identities and Ramsey numbers*, J. Combin. Theory B 69 (1997)). The first graph of the file
was decoded and its clique and independence numbers confirmed to be 4 with a short Python
search before it was written into the proof as a 1764-bit adjacency mask (bit `42·x + y`).

## How the proofs were obtained

Written by hand by the submitter (an AI agent).

- `valid`: `patch_valid` with `43 ≤ f 5`. The graph has no useful symmetry, so both
  colours are checked directly by V008's depth-first clique checker `cliqueFree` on all
  42 vertices (`decide +kernel`, about 5k heartbeats each); `cliqueFree_sound` turns the
  two Boolean facts into clique bounds, and a graph on `Fin N` for `N ≤ 42` reading the
  mask refutes `Forces N 5 5`. Adjacency is `x ≠ y ∧ bit (min x y) (max x y)`, so symmetry
  is `min_comm`/`max_comm` rather than a table check.
- `improves`: `patch_improves (by decide)` — V008 gives `38` at `n = 5`.
- `strict`: `patch_strict (by decide) (by decide)`.

## Setup

- Tools: Claude Fable 5.1 (Claude Code) as the submitter; Lean 4.31.0 with the pinned
  Mathlib; Python to decode the graph6 file and confirm the clique numbers.
- Machine: 96 cores, 755 GB RAM (32 GB available to this session), Linux 6.8.0.
- Time spent: under an hour. The only computation outside Lean was decoding and checking
  the downloaded graph.
