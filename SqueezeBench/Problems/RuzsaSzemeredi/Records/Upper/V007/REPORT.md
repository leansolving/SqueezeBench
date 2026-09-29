# RuzsaSzemeredi, upper record, V007

By trial claude-fable.

## How the bound was obtained

**Bound.** `record n` is the largest `T ≤ V006.record n` that passes the test `ok n T`, where,
with `c = 2 + n % 2`, `q = ⌊3T/n⌋`, `r = 3T mod n` and
`cap t = min(2T + 2t, t(n + c) − 2t²)`:

    ok n T  ⟺  (n − r) · 4q² + r · 4(q+1)²  ≤  (n − r) · cap q + r · cap (q+1).

**Idea.** Write `t_v` for the number of triangles at `v` (so `deg v = 2 t_v`, V004) and
`s_v = Σ_{u ∈ N(v)} t_u` for the sum of the triangle counts over the neighbours of `v`. Two
bounds hold at every vertex:

* (A) `s_v ≤ T + t_v`. The `t_v` triangles through `v`, and for each neighbour `u` the
  `t_u − 1` triangles through `u` avoiding `v`, are pairwise distinct: a triangle avoiding `v`
  through two neighbours `u, u'` of `v` would share the edge `uu'` with the triangle
  `{v, u, u'}`. So `t_v + Σ_{u ∈ N(v)} (t_u − 1) ≤ T`. (Equivalently: every triangle meets the
  closed neighbourhood of `v`, or the non-neighbourhood of `v` spans no triangle.)
* (B) `2 s_v + 2 t_v² ≤ t_v (n + c)`. `N(v)` is the disjoint union of the pairs `τ \ {v}` over
  the `t_v` triangles `τ` at `v`, and V006's triangle bound gives
  `2 Σ_{u ∈ τ} t_u ≤ n + c` for each of them.

Double counting gives `Σ_v s_v = Σ_u deg u · t_u = 2 Σ_v t_v²`. Hence
`Σ_v g(t_v) ≤ Σ_v (4 t_v² − 2 s_v) = 0` for the function
`g(t) = max(4t² − 2T − 2t, 6t² − (n + c) t)`, which is convex on `ℕ` as a maximum of two
convex quadratics. For a convex `g` and any family of `n` natural numbers with sum
`qn + r` (`r < n`), the most balanced family (`n − r` values `q` and `r` values `q + 1`)
minimises `Σ g(t_v)`: `g` lies above the line through `(q, g q)` with slope `g(q+1) − g q`.
So `(n − r) g(q) + r g(q+1) ≤ 0`, which is `ok n T` after replacing `g` by
`4t² − cap t ≤ g(t)` (the `ℕ`-subtraction in `cap` only makes the left side smaller).

Since the triangle count of the extremal graph passes the test and is at most V006's record,
it is at most the largest passing value below V006's record, which is `record n`.

**What it gains.** V005/V006 used (B) alone, summed and then Cauchy–Schwarz, which is tight
only for regular graphs. Using (A) at the vertices with the larger count `q + 1` and (B) at the
others, and the integrality of the counts, gains: `−1` at `n = 13` (matching the known value
`f(13) = 10`), at `n = 18, 19, 23, 25, 29, 30, 31, 35, 36, 37, …`, and the gain grows roughly
like `n/27` at `n ≡ 1, 5 (mod 6)` (`−3` at `n = 67`, `−7` at `n = 193`, `−10` at `n = 283`),
with sporadic `−1`s at even `n`. Nothing changes at `n ≡ 3 (mod 6)`, where the bound is
attained by generalized quadrangles at `n = 9, 15, 27`.

**Sources.** The elementary ingredients are those of V002–V006; the bound (A) and the balanced
minimisation are this submission's. The bound of V005 is Fronček's (D. Fronček, *Locally
linear graphs*, Math. Slovaca 39 (1989), 3–6, Theorem 5). Values of the candidate bounds up to
`n = 300` were computed with a short Python script to choose the version.

## How the proofs were obtained

Written by the AI agent named below, by hand, on top of V006's public lemma library
(`trianglesAt`, `degree_eq`, `degree_sum_triangle_le'`, `sum_card_trianglesAt`). New lemmas:
`card_filter_mem_eq_one` (one triangle per edge), `sum_nbr_le` (A, via `Finset.card_biUnion`
over the pairwise disjoint families), `neighborFinset_eq_biUnion` and `two_mul_sum_nbr_le`
(B, via `Finset.sum_biUnion`), `sum_sum_nbr_eq` (`Finset.sum_comm'`), the discrete tangent
lemma `tangent_of_convex` (two inductions on the distance to `q`, using
`monotone_nat_of_le_succ` for the slopes), `balanced_le_sum`, `convex_g` and `sq_sub_cap_le`
(`nlinarith`), and `ok_of_counts` assembling everything in `ℤ`. `search_le` and `le_search`
are inductions on the starting point of the search. `valid` chains V006's `valid`, `improves`
is `search_le`, and `strict` is `decide` at `n₀ = 13` (`11 → 10`).

The record is a bounded downward search (structural recursion on the starting value) because
the test has no closed form; it stops after a few steps at every `n ≤ 300`. `decide +kernel`
evaluates it at `n = 100` without difficulty.

## Setup

- Tools: Claude Fable 5.1 (Anthropic, `claude-fable-5-1`) as the submitting agent, run through
  Claude Code; Lean 4 with Mathlib as pinned by the project; one consultation of GPT-6 Astra on
  the literature (it pointed to Fronček 1989). A Python script computed the candidate bounds.
- Machine: 96 logical CPUs, 755 GB RAM (32 GB available to this session), Linux 6.8.0-124-generic.
- Time spent: about two hours.
