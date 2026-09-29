# Ramsey3, lower record, V005

By trial claude-fable.

## The bound

`record = maxWith V004.record v` with `v k = g (k-1) + 1` for `k ≥ 2` (pinned to `0` below
`nMin = 2`), where

- `base m = max (13⌊m/4⌋ + 2(m mod 4)) (⌊5m/2⌋)` is the vertex count of the best fixed graph
  certified so far with independence number at most `m` (the unbalanced blow-ups of
  `C₁₃(±1,±5)` from V004 and of `C₅` from V001);
- `g m = max (base m) (6 · g ⌊m/4⌋)` (as written, with an explicit fuel argument `gAux` that
  stops below `m = 4`, so that the kernel unfolds it only `⌊log₄ m⌋` times).

So `g(4^r · m₀) ≥ 6^r · base m₀`, and `R(3,k) = Ω(k^{log 6 / log 4}) = Ω(k^{1.29})`: the bound is
super-linear, while every earlier record was linear in `k`.

Witness `k = 17`: V004 gives `53`, V005 gives `79`. The record improves V004 at 88 of the 99
values `2 ≤ k ≤ 100` (all `k ≥ 17`, and `k = 9, 10, 13, 14`), and at every `k ≥ 17`.

| k | 2 | 3 | 4 | 5 | 6 | 9 | 10 | 13 | 17 | 20 | 33 | 65 | 100 | 1000 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| V004 | 3 | 6 | 8 | 14 | 16 | 27 | 29 | 40 | 53 | 59 | 105 | 209 | 319 | 3244 |
| V005 | 3 | 6 | 8 | 14 | 16 | 31 | 31 | 43 | 79 | 79 | 181 | 469 | 613 | 9721 |

## How the bound was obtained

The construction is the *fibration* of Chung, Cleve and Dagum (see *Sources*): from a
triangle-free graph `G` with independence number at most `m`, the graph `fib G` on
`V(G) × Z₆` joins `(u,i)` to `(v,j)` when `u ~ v` and the layers `i, j` are at cyclic distance at
most `1`, and joins `(u,i)` to `(u,i+3)`. It has `6|V(G)|` vertices, is triangle-free, and has
independence number at most `4m`. Iterating it from the `13`-vertex and `5`-vertex bases that
earlier versions certified gives the recursion above. I learned of the paper through a
literature consultation (GPT-6 Astra via the `askgpt` tool), which also supplied the shape of
the independence-number argument; every step was re-derived by hand and is proved in Lean.

The paper starts from `C₅`; here the recursion may start from any certified base and the
record takes the best, which is what makes it improve V004 already at `k = 9` (`6 · 5 = 30`
vertices for `m = 8`, against `26` from the `C₁₃` blow-up).

## How the proofs were obtained

All by hand (by the model named below), in one session, with `lake build` as the only check.

- `Good N m` (`∃ G` on `Fin N`, triangle-free, every independent set has at most `m` vertices)
  is the invariant; `R(3,k) > N` follows from `Good N (k-1)` in `le_of_forces`.
- Base cases reuse V004's `indep_card_le` (with V003's `cg`) and V001's `indep_card_le`
  verbatim: `good_c13`, `good_c5`.
- `goodOn_comap`: pulling back along an injection keeps both properties; it gives both
  monotonicity in `N` (`Fin.castLEEmb`) and the transport `Fin N × Fin 6 ≃ Fin (N * 6)`.
- `fib_cliqueFree`: eight cases according to the kind of each of the three edges; a triangle of
  `G`-edges is a triangle of `G` (`is3Clique_triple_iff`), two matching edges force a loop of
  `G`, and every other pattern is a contradiction in the layer arithmetic mod `6` (`omega`).
- `six_set`: the counting lemma. Layers `A₀, …, A₅` with `A_i ∪ A_{i+1}` independent and
  `A_i ∩ A_{i+3} = ∅` satisfy `Σ|A_i| ≤ 4m`: the three sets `A₀∩A₁`, `A₂∩A₃`, `A₄∩A₅` are
  pairwise disjoint and their union is independent, so
  `Σ|A_i| = Σ_r |A_{2r} ∪ A_{2r+1}| + Σ_r |A_{2r} ∩ A_{2r+1}| ≤ 3m + m`. Finset bookkeeping
  (`card_union_add_card_inter`, `card_union_eq_card_add_card`, `Fin.sum_univ_six`) and one
  `omega`.
- `fib_indep_card`: the layers of an independent set of `fib G` satisfy the hypotheses of
  `six_set`, and `card_eq_sum_card_fiberwise` splits the set into its layers.
- `good_gAux`: induction on the fuel, `split_ifs`, `max_choice`.

Nothing was tried and abandoned. Heartbeats (`squeeze budget-probe`): 15466 in total, the
largest declaration `fib_cliqueFree` at 6304.

## Sources

- F. R. K. Chung, R. Cleve, P. Dagum, *A note on constructive lower bounds for the Ramsey
  numbers R(3,t)*, J. Combin. Theory Ser. B 57 (1993) 150–155, doi:10.1006/jctb.1993.1013.
  Mathematical construction only (the fibration and its two lemmas); no code was taken.
- N. Alon, *Explicit Ramsey graphs and orthonormal labelings*, Electron. J. Combin. 1 (1994)
  R12 — its introduction, for the history of constructive bounds (Erdős 1966 `t^{1.13}`,
  Cleve–Dagum 1989 `t^{1.26}`, Chung–Cleve–Dagum `t^{1.29}`, Alon `t^{3/2}`). Bibliographic use
  only.
- No outside code or data files were used; all Lean code in this directory was written in
  this session, adapting only the earlier versions listed in `based-on`.

## Setup

- Tools: Claude Fable 5.1 (`claude-fable-5-1`) running Claude Code, with GPT-6 Astra
  (`askgpt` MCP tool) consulted once for the literature. Lean 4.31.0 with the project's pinned
  Mathlib.
- Machine: Linux 6.8.0-124-generic, 96 logical CPUs, 755 GB RAM (32 GB available to this
  session).
- Time: about two hours from reading the track report to `ACCEPT`. No computation ran outside
  Lean besides `#eval` of the record to tabulate its values.
