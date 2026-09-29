# ExGirthFive, lower record, V011

By trial claude-fable.

## How the bound was obtained

**Bound.** `record n = max (V010 n) (hs n)` with `hs n = 175` for `n ≥ 50` and `hs n = tab[n]` for
`n < 50`, where

```
tab = [0, 0, 1, 2, 3, 5, 6, 8, 10, 12, 15, 16, 18, 20, 22, 25, 27, 29, 32, 36, 40, 42, 45, 48, 51,
       55, 58, 62, 66, 70, 75, 78, 82, 86, 90, 95, 99, 104, 109, 114, 120, 124, 129, 134, 139, 145,
       150, 156, 162, 168, 175]
```

is the number of edges of the Hoffman–Singleton graph induced on the first `n` vertices of a fixed
ordering of its 50 vertices.

**Idea.** The Hoffman–Singleton graph is the unique `(7,5)`-Moore graph: `7`-regular on `50`
vertices, `175` edges, girth `5`, so `f(50) = 175` (Hoffman–Singleton 1960). Robertson's
description is used: five pentagons `P_h` and five pentagrams `Q_i` on `ZMod 5` (`j ~ j ± 1` in a
pentagon, `j ~ j ± 2` in a pentagram), and vertex `j` of `P_h` adjacent to vertex `h·i + j` of
`Q_i`. Every induced subgraph keeps girth `≥ 5`, so one ordering of the vertices yields 50 graphs:
the prefix of length `n` has `tab[n]` edges. The ordering is pentagon `0`, pentagram `0`, pentagon
`1`, pentagram `1`, …, each block in an affine order `j ↦ a·j + c`; the ten pairs `(a, c)` were
chosen by a small random search (4000 trials) to maximise the number of `n` at which the prefix
beats V010 and the total edge count. With this order the first 10 vertices form the Petersen graph
(`15` edges), the first 40 the `(6,5)`-cage (`120` edges, Hoffman–Singleton minus a Petersen
graph), the first 45 the graph minus a pentagon (`145`), and `tab[n] = f(n)` for `n ≤ 12` and
`34 ≤ n ≤ 50` (OEIS A006856: `90, 95, 99, 104, 109, 114, 120, 124, 129, 134, 139, 145, 150, 156,
162, 168, 175`). For `n > 50` the graph is used with isolated vertices.

**Values.** The record beats V010 at every `n` from `5` to `60` (`56` values), e.g. `n = 10`:
`12 → 15`, `n = 20`: `33 → 40`, `n = 30`: `52 → 75`, `n = 40`: `84 → 120`, `n = 45`: `104 → 145`,
`n = 50`: `125 → 175`, `n = 55`: `150 → 175`, `n = 60`: `174 → 175`; the prime-table bound takes
over at `n = 61` (`180`) and `n = 62` (`186`, the plane `PG(2,5)`).

## How the proofs were obtained

Written by the AI agent named below, in Lean, with Mathlib's tactics; the checks of the fixed
graph are kernel computations (`decide +kernel`), as `docs/CONTRIBUTING.md` allows for data the
record provides.

- `hsAdj`, `HS`: adjacency by cases on the two kinds of vertices; symmetry and irreflexivity by
  `decide +kernel` (`2500` and `50` cases).
- `hs_check`: for all `x ≠ y`, at most one common neighbour, and none if `x ~ y`, as a count over
  the 50 candidates (`decide +kernel`, about 70000 heartbeats — the heaviest check). `HS_noTwo`
  and `HS_cliqueFree` follow by `Finset.card_le_card` and `Finset.card_pos`.
- `rank`: the ordering as a formula; `edgeOf : HE → HV × HV` lists the 175 edges (pentagon,
  pentagram and cross edges) as pairs sorted by rank. `edgeOf_adj`, `edgeOf_sorted`, `rank_inj`
  are `decide +kernel`; injectivity of `edgeOf` is `#(univ.image edgeOf) = 175` plus
  `Finset.card_image_iff`, cheaper than comparing all pairs.
- `count_edges`, `count_verts`: `∀ n < 51`, the prefix of length `n` has `n` vertices and `tab[n]`
  edges among the 175, one `decide +kernel` each.
- `prefix_le`: the graph induced on the first `m` vertices, `HS.comap Subtype.val`, has girth `≥ 5`
  by V008's `comap_cliqueFree`/`comap_noTwo`; its edges are indexed by the sorted pairs with second
  rank `< m`, injective because the ranks are sorted; V008's `transport_le` puts it into `Fin n`
  for any `n ≥ m`. `hs_valid` uses `m = n` for `n < 50` and `m = 50` beyond.
- `strict`: `decide +kernel` at `n₀ = 50`.

The file costs 122878 heartbeats (`hs_check` 69910, `edgeOf_img` 24532, `count_edges` 8040).

## Sources

- The Hoffman–Singleton graph and Robertson's pentagon–pentagram description are classical
  (A. J. Hoffman, R. R. Singleton, *On Moore graphs with diameters 2 and 3*, IBM J. Res. Develop.
  4 (1960); the description appears e.g. in Wikipedia's article "Hoffman–Singleton graph").
  Mathematical data only; no code was used.
- The exact values of `f` for comparison are from OEIS A006856 (data, cited above).

## Setup

- Tools: Claude Fable 5.1 (`claude-fable-5-1`) running in Claude Code, Lean 4.31.0 with the
  pinned Mathlib; Python 3 for the search over vertex orderings and to model the record's values.
- Machine: 96 CPUs, 755 GB memory (32 GB allotted), Linux 6.8.0-124-generic.
- Time spent: about one and a half hours. Computation outside Lean: the ordering search
  (4000 random trials over ten affine orders, a few seconds).
