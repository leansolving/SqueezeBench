# Ramsey3, lower record, V006

By trial claude-fable.

## The bound

`record = maxWith V005.record v` with `v k = g (k-1) + 1` for `k ≥ 2` (pinned to `0` below
`nMin = 2`), where `g` is V005's fibration recursion `g m = max (base m) (6 · g ⌊m/4⌋)` over a
new base:

- `base m = 35⌊m/8⌋ + rem (m mod 8)`, `rem r = 13⌊r/4⌋ + [0, 2, 5, 8][r mod 4]`.

That is the best disjoint union of the certified pieces `(35, 8)` (Kalbfleisch's circulant
`C₃₅(±1,±7,±11,±16)`, new here), `(13, 4)` (`C₁₃(±1,±5)`, V003/V004), `(8, 3)` (the Wagner graph
`C₈(±1,4)`, new), `(5, 2)` (`C₅`, V001) and `(2, 1)` (an edge): vertex counts and independence
numbers add under disjoint union. Ratio `35/8 = 4.375` at the base against `13/4` before, so
`g(8·4^r) ≥ 35 · 6^r` where V005 had `30 · 6^r`.

Witness `k = 9`: V005 gives `31`, V006 gives `36 = R(3,9)`, the exact value; `k = 4` now gives
`9 = R(3,4)` as well. The record improves V005 at 60 of the 99 values `2 ≤ k ≤ 100` and at
infinitely many `k` (every `k` with `k - 1 ∈ [8·4^r, 16·4^r)` and more).

| k | 4 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 16 | 17 | 25 | 33 | 40 | 49 | 100 | 1000 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| V005 | 8 | 18 | 20 | 31 | 31 | 31 | 33 | 43 | 46 | 79 | 103 | 181 | 181 | 253 | 613 | 9721 |
| V006 | 9 | 19 | 22 | 36 | 38 | 41 | 44 | 49 | 57 | 79 | 109 | 211 | 223 | 289 | 649 | 12097 |

## How the bound was obtained

The recursion is V005's; the work is in the base. An exhaustive search over triangle-free
circulants `C_n(S)` for `n ≤ 40` (a 60-line Python script, branch and bound on bitmasks,
`n ≤ 40` in a few minutes) confirmed the list in the track report: the best ratios are
`13/4` (`n = 13`), `21/6`, `26/7` and `35/8` (`n = 35`, the extremal graph for `R(3,9) = 36`), and
`8/3` for `n = 8`. Only `n = 8`, `13`, `35` are needed: `35/8` is the best ratio, so a knapsack
over the pieces uses as many 35s as possible, and the remainder `r < 8` is best served by
`13⌊r/4⌋` plus `0, 2, 5, 8` — which is exactly the optimal unbalanced blow-up of `C₁₃` that the
track report had predicted, now obtained by disjoint union instead.

The independence number of `C₃₅(±1,±7,±11,±16)` was the obstacle the track report flagged
(nine cyclic gaps, far beyond `omega`). The proof used here (found with a consultation of
GPT-6 Astra via the `askgpt` tool, then checked line by line by hand and against a computer
enumeration of all 3360 maximum independent sets) works in `Z₃₅ = Z₅ × Z₇`: the edges become
`(a,b) ~ (a±2, b)` and `(a,b) ~ (a+1, b+d)`, `d ∈ {1,2,4}`. Each layer `b` (the vertices
`b + 7i`) is a 5-cycle with step `7`, so an independent set `I` has at most two vertices per
layer, and a two-vertex layer is `{x, x+21}`. If at most one layer holds two, `|I| ≤ 2 + 6`.
Otherwise the automorphism `x ↦ q(x - x₁)`, `q ∈ {1, 11, 16}` (the units of `Z₃₅` fixing the
connection set), moves one double to `{0, 21}` and the other into layer `1`, where
non-adjacency to `0, 21` forces it to be `{8, 29}` or `{15, 29}`. Every other vertex
non-adjacent to those four lies in a list of ten (resp. nine) candidates, and the candidates
are covered by two 5-cycles (resp. one 5-cycle and two edges); a 5-cycle holds at most two
independent vertices and an edge at most one, so `|I| ≤ 4 + 4 = 8`.

## How the proofs were obtained

By hand (the model below), building on V005's `Good` framework.

- `goodOn_sum`/`good_union`: Mathlib's `G ⊕g H` and `finSumFinEquiv`; a 3-clique of the sum
  lies on one side, an independent set splits with `Finset.toLeft`/`toRight`.
- `good_wagner`: `C₈(±1,4)`; four ordered vertices, five disequalities, one `omega`.
- `good_k35`: as described. The finite facts are `decide` tables over `Fin 5` and `Fin 35`:
  the connection-set arithmetic (`S35_sum`, `S35_neg`, `S35_mul`), the layer-1 table
  (`layer1_table`, over `Fin 5 × Fin 5`), the candidate lists (`cand3`, `cand4`, over `Fin 35`),
  the cycles' edges, and `fin5_no_consec` (a subset of `Z₅` with no two consecutive elements
  has at most two, over the 32 subsets). The modular identities (`σ_sd`, `σ_inj`, `lay_adj`)
  are `omega` with the multiplier `q` split into its three literal values. Counting is
  `card_eq_sum_card_fiberwise`, `card_union_le`, `sum_le_card_nsmul`.
- The knapsack base: `good_k35_mul` (induction), `good_rem`, `good_base`; the recursion and
  the obligations are V005's verbatim.

Abandoned: a first version of the Wagner lemma fed `omega` the raw `¬ wadj` hypotheses with
`% 8` and cost 88k heartbeats; deriving five plain disequalities first cut it to 3k. A
`decide` over all 256 subsets of `Fin 8` hit the elaborator's recursion limit.

Heartbeats (`squeeze budget-probe`): 125773 in total; the largest declarations are
`two_doubles` (19.7k), `two_doubles'` (14.9k), `kg_indep_card_le` (14.1k), `σ_inj` (9.8k).

## Sources

- J. G. Kalbfleisch, *Chromatic graphs and Ramsey's theorem*, Ph.D. thesis, University of
  Waterloo, 1966, as cited in S. P. Radziszowski, *Small Ramsey Numbers*, Electron. J. Combin.
  Dynamic Survey DS1 (the 35-vertex cyclic `(3,9)`-graph with distances `{1, 7, 11, 16}`), and
  J. Goedgebeur, S. P. Radziszowski, *New computational upper bounds for Ramsey numbers
  R(3,k)*, Electron. J. Combin. 20(1) (2013) P30 (uniqueness of that graph). Mathematical data
  only: the connection set. The independence proof is the one described above; no code taken.
- Chung–Cleve–Dagum (see V005's report) for the recursion, unchanged.
- No outside code or data files were used; all Lean code was written in this session,
  adapting only the earlier versions listed in `based-on`.

## Setup

- Tools: Claude Fable 5.1 (`claude-fable-5-1`) running Claude Code, with GPT-6 Astra
  (`askgpt` MCP tool) consulted for the literature and for the structure of the `C₃₅`
  independence proof. Lean 4.31.0 with the project's pinned Mathlib. Python 3 for the
  circulant search and the enumeration of maximum independent sets (no external packages).
- Machine: Linux 6.8.0-124-generic, 96 logical CPUs, 755 GB RAM (32 GB available to this
  session).
- Time: about three hours after V005. Computation outside Lean: the circulant search
  (minutes) and the enumeration of the 3360 maximum independent sets of `C₃₅` (seconds).
