# RuzsaSzemeredi, upper record, V008

By trial claude-fable.

## How the bound was obtained

**Bound.** `record n` is the largest `T ≤ V007.record n` that the test `ok n T` cannot exclude.
The test refines V007's per-vertex bound with a third constraint, coming from the induced
matchings that a pair of non-adjacent vertices leaves in its common non-neighbourhood.

*The pair inequality.* Let `x ≁ y` be distinct, `Z = N(x) ∩ N(y)` (`c = |Z|`) and
`Y = V \ (N[x] ∪ N[y])`, so `|Y| = n − 2 − 2t_x − 2t_y + c`. For `z ∈ Z`, the triangles at
`z` other than the two through `zx`, `zy` have their opposite edges inside `Y`, and these
edges form an induced matching; the matchings of different `z` are edge-disjoint. Counting,
for `w ∈ Y`, the number `a_w` of `z ∈ Z` adjacent to `w`: `Σ a_w = Σ_z |N(z) ∩ Y|`, and
`Σ a_w² = Σ_{z,z'} |N(z) ∩ N(z') ∩ Y|`, where for `z ≠ z'` the pair shares at most `t_z`
neighbours in all (V007's one-per-triangle argument), two of them `x, y`, so
`2|N(z) ∩ N(z') ∩ Y| ≤ |N(z) ∩ Y|`. Cauchy–Schwarz gives

    2 · Σ_{z ∈ Z} |N(z) ∩ Y|  ≤  |Y| · (c + 1).

This is the Plotkin-type count of J. Fox, H. Huang, B. Sudakov, *On graphs decomposable into
induced matchings of linear sizes*, Bull. LMS 49 (2017), Theorem 1.2, run inside `Y`
(suggested by a GPT-6 consultation); run on the whole vertex set it is V003's bound.

*Averaging over the non-neighbours `y` of a vertex `x`* with `t = t_x ≥ 1` and `m = n − 1 − 2t ≥ 1`
non-neighbours, using `|N(z) ∩ Y| ≥ 2t_z − 4`, `Σ_y c_y = 2s − 4t` (`s = Σ_{u ∈ N(x)} t_u`),
`c_y ≤ t_y`, `Σ_y t_y = 3T − t − s`, and Cauchy–Schwarz for `Σ_y c_y²` and for
`Σ_{z ∈ N(x)} t_z²`, gives the quadratic inequality `A s² − B s + C ≤ 0` with

    A = 4(m + t),  B = 2t(8t + 13m + m²),  C = 16t³ + 30t²m + 4t²m² + tm² − tm³ + 6Ttm,

so `s ≤ ⌊(B + √(B² − 4AC)) / 2A⌋ =: capP t` (or no such vertex exists). Together with
V007's `capAB t = min(T + t, t(n+c)/2 − t²)` this gives `s_v ≤ cap' t_v` at every vertex
and `ψ(t_v) ≤ 4t_v² − 2s_v` for `ψ(t) = 4t² − 2·cap' t`, while `Σ_v (4t_v² − 2s_v) = 0`.

*The certificate.* `ψ` is no longer provably convex, so the record checks the chord itself:
with `q = ⌊3T/n⌋`, `r = 3T mod n`, `ℓ` the line through `(q, ψ q)` and `(q+1, ψ(q+1))`, the
test excludes `T` when `(n − r) ψ(q) + r ψ(q+1) > 0` **and** `ℓ(t) ≤ ψ(t)` for every
`t ≤ (n−1)/2` (a loop in the record). Then `0 = Σ_v (4t_v² − 2s_v) ≥ Σ_v ψ(t_v) ≥ Σ_v ℓ(t_v)
= (n − r) ψ(q) + r ψ(q+1) > 0`, a contradiction. The integer square root is a bisection by
structural recursion, so the kernel evaluates the record; `decide +kernel` settles it at
`n = 100` in a few seconds.

**What it gains.** Nothing below `n = 33`; from there on the gain grows quadratically:
`66 → 64` at `n = 33`, `93 → 92` at `n = 40`, `144 → 140` at `n = 50`, `257 → 245` at
`n = 67`, `566 → 529` at `n = 100`, about `n²/230` in this range (the regular case of the
same inequality gives `T ≤ n(n+9)/21`, i.e. constant `1/21` instead of `1/18`). The bound is
still attained at `n = 9, 15, 27` by the generalized quadrangles, and the pair inequality is
tight on `GQ(2,4)`. All inequalities were checked by brute force on `K₃□K₃`, `K₃□K₃□K₃`,
`GQ(2,2)`, `GQ(2,4)`, the line graph of the Petersen graph, windmills and two
Ruzsa–Szemerédi graphs built from 3-AP-free sets before the formalisation.

## How the proofs were obtained

Written by the AI agent named below, by hand, on top of V006–V007's public lemmas. About
740 lines: the integer square root and the root bound (`isqrtAux_spec`, `le_root`,
`le_capP`); the non-neighbourhood counts (`card_nonNbr`, `card_nbr_inter_nonNbr`,
`card_inter_eq_one`, `card_inter_le_of_not_adj`); the pair inequality (`card_farSet`,
`two_mul_le_card_inter_far_add`, `card_inter_inter_far_add_two_le`, the two double counts
`sum_card_inter_eq` and `sum_sq_card_inter_eq` via
`Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow`, and `pair_ineq`); the averaging
(`sum_sum_common_eq`, `sum_split`, `vertex_quadratic`, whose closing algebra is an exact
`linear_combination` in `final_algebra`); and the certificate argument (`le_cap'`, `psi_le`,
`lineAbove_false`, `sum_chord`, `ok_of_graph`). The obligations follow V007's pattern; `strict`
is `decide +kernel` at `n₀ = 40` (`93 → 92`).

What was tried and abandoned: a first version closed the averaging with `nlinarith` and ran
out of heartbeats; giving the exact linear combination of the three product inequalities
fixed it.

## Setup

- Tools: Claude Fable 5.1 (Anthropic, `claude-fable-5-1`) as the submitting agent, run through
  Claude Code; Lean 4 with Mathlib as pinned by the project; one GPT-6 Astra consultation on
  the literature and the induced-matching idea. Python scripts (in the session's scratch
  directory, not part of the record) computed the candidate bounds, their gains up to
  `n = 300`, and the brute-force checks of the inequalities on explicit graphs.
- Machine: 96 logical CPUs, 755 GB RAM (32 GB available to this session), Linux 6.8.0-124-generic.
- Time spent: about four hours.
