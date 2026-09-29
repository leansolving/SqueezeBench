# RuzsaSzemeredi, upper record, V006

By trial claude-fable.

## How the bound was obtained

**Bound.** `record n = n · (n + 2 + n % 2) / 18`, i.e. `⌊n(n+2)/18⌋` for even `n` and V005's
`⌊n(n+3)/18⌋` for odd `n`.

**Idea.** V005 proved `deg u + deg v + deg w ≤ n + 3` along every triangle `{u, v, w}` (the
three neighbourhoods pairwise meet in one vertex and cover at most `n` vertices), and turned it
into `18 · T ≤ n(n+3)` by double counting and Cauchy–Schwarz on the triangle counts
`t_v = deg v / 2`. V004 proved that every degree of a locally linear graph is even. So the sum
of the three degrees of a triangle is even, and for even `n` the bound `n + 3` is odd and
sharpens to `n + 2`. Running V005's count with `n + 2` in place of `n + 3` gives
`18 · T ≤ n(n+2)` for even `n`.

Equivalently: `|N(u) ∪ N(v) ∪ N(w)| = deg u + deg v + deg w − 3` is odd, so for even `n` the
three neighbourhoods of a triangle always miss at least one vertex.

**Why this bound.** It gains about `n/18` at every even `n ≥ 10` (and at `n = 6`), so it
improves the record at infinitely many `n`; and it is tight at every even `n` where `f` is
known: `f(6) = 2`, `f(8) = 4`, `f(10) = 6`, `f(12) = 9` are exactly `⌊n(n+2)/18⌋`. For odd `n`
the record is unchanged; the bound `⌊n(n+3)/18⌋` is attained at `n = 9, 15, 27` by the
collinearity graphs of the generalized quadrangles `GQ(2,1)`, `GQ(2,2)`, `GQ(2,4)` (the 3×3
rook's graph, the complement of the triangular graph `T(6)`, and the complement of the Schläfli
graph), so no bound of the form `c · n²` with `c < 1/18` holds at all `n`.

**Sources.** The elementary ingredients are the ones of V002–V005 (edge-disjoint triangles,
even degrees, one common neighbour along an edge, the union bound along a triangle) plus
parity. The generalized-quadrangle examples are standard (S. E. Payne, J. A. Thas, *Finite
Generalized Quadrangles*, 2nd ed., EMS 2009, §1.2 and §6.1: `GQ(2,t)` exists iff
`t ∈ {1, 2, 4}`).

## How the proofs were obtained

Written by the AI agent named below, by hand, on top of V005's proof. The lemma library of
V002–V005 (`trianglesAt`, `degree_eq`, `card_inter_neighborFinset_le`,
`degree_sum_triangle_le`, `sum_swap`) is copied from V005 and made public, so that later
versions can import it instead of copying it again. The only new lemma is
`degree_sum_triangle_le'`: the sum of the three degrees equals `2 · Σ t_v` by `degree_eq`, and
`omega` closes `2k ≤ m + 3 → 2k ≤ m + 2 + m % 2`. The main estimate is V005's, with
`m + 2 + m % 2` in place of `m + 3` throughout. `exists_counts` exports the triangle counts of
an extremal graph with the two inequalities they satisfy, for the integrality refinement
planned as the next version. `improves` is `Nat.div_le_div_right` and `omega`; `strict` is
`decide` at `n₀ = 10`, where the record drops from `7` to `6 = f(10)`.

Nothing was tried and abandoned; the file built at the first attempt.

## Setup

- Tools: Claude Fable 5.1 (Anthropic, `claude-fable-5-1`) as the submitting agent, run through
  Claude Code; Lean 4 with Mathlib as pinned by the project. A Python script computed the
  values of the candidate bounds up to `n = 100` to choose the version; no search outside Lean.
- Machine: 96 logical CPUs, 755 GB RAM (32 GB available to this session), Linux 6.8.0-124-generic.
- Time spent: about one hour, including reading the previous versions.
