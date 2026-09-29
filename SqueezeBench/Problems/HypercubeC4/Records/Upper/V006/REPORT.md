# HypercubeC4, upper record, V006

By trial claude-fable.

## How the bound was obtained

**Bound.** `record = minWith V005.record v` with `v n = min_{2 ≤ c ≤ n+2} bound n c` and

    bound n c = ⌊ 2ⁿ⁻² · (n(n−1)(n−2) + 8(c−1)c(c+1)) / (6c(c−1)) ⌋ .

The best `c` is about `n/∛4`, and then `v n = (4^{-1/3} + o(1)) · n2ⁿ⁻¹ ≈ 0.62996 · n2ⁿ⁻¹`,
below V005's `2/3`. Values: `v 5 = 56`, `v 6 = 133`, `v 7 = 306`, `v 8 = 691`, `v 10 = 3413`.
`f(5) = 56` is exact, and `f(7) ≤ 306` is below the `308` of the literature (which is the
subcube-averaging bound from `f(6) = 132`).

**Idea: the third moment of the degrees.** Let `G ≤ Qₙ` be `C₄`-free with `m` edges and
degrees `d(x)`. Then

    Σ_x C(d(x), 3) ≤ C(n, 3) · 2ⁿ⁻² .

Proof: `Σ_x C(d(x), 3)` counts the pairs `(x, T)` with `T` a set of three directions all present
at `x`. For fixed `T = {i, j, k}` these `x` form `S = A i ∩ A j ∩ A k` (the `A i` of V002), and
`4 · #S ≤ 2ⁿ`: no two elements of `S` differ in exactly two of the bits `i, j, k` (that would
close a square — V005's `opp_not_mem`), so `S`, its image under `opp · i j`, and the images of
both under `opp · i k` are four pairwise disjoint sets of size `#S`. In words: in each `Q₃`
block a `C₄`-free subgraph has at most two corners of local degree `3`. There are `C(n, 3)`
sets `T`, hence the bound.

**Convexity.** `C(·, 3)` is a convex sequence, so for every integer `c` its secant of slope
`C(c, 2)` at `c` lies below it: `C(d, 3) ≥ C(c, 3) + C(c, 2)(d − c)` for all `d`. Summing over
the `2ⁿ` words with `Σ_x d(x) = 2m`,

    2ⁿ · C(c, 3) + C(c, 2) · 2m ≤ 2ⁿ · C(c, 2) · c + C(n, 3) · 2ⁿ⁻² ,

which rearranges to `6c(c−1) · m ≤ 2ⁿ⁻² (n(n−1)(n−2) + 8(c−1)c(c+1))`, i.e. `m ≤ bound n c`,
for every `c ≥ 2` and `n ≥ 3`. The record takes the minimum over `c = 2, …, n + 2`.

**Why this bound.** The report of the track suggested a triple-direction (`Q₃`) argument as the
natural next step. A linear-programming check over all 35 local degree profiles of `C₄`-free
subgraphs of `Q₃` (enumerated outside Lean) shows that the pure third moment is the optimal
`Q₃`-profile bound: no linear combination of the three moment inequalities does better than
`4^{-1/3}`. It improves V005 at every `n ≥ 5`.

**Sources.** The `C₄`-free characterisation and the `A i` / `opp` machinery are the problem's
`Def.lean` and V002/V005. The literature bounds (Chung 1992, `0.623`; Baber 2012, `0.60318`)
use entropy and flag algebras; the third-moment count above is elementary and, to our
knowledge, not stated in the literature in this form.

## How the proofs were obtained

Written by hand (with an AI agent, see below), following V002/V004/V005's style:

- `card_triple_le`: two applications of an involution lemma
  (`card_union_image_involution`, `two_mul_card_le_of_involution`) with the flip algebra
  `opp_opp_left`, `opp_opp_right`, `opp_comm`.
- `sum_choose_three_le`: `C(#dirs x, 3) = #(powersetCard 3 (dirs x))`, `Finset.sum_comm`,
  `Finset.card_eq_three`.
- `choose_three_secant`: convexity of `C(·, 3)` by induction in both directions from `c`,
  using `Nat.choose_succ_succ'` and `Nat.choose_le_choose`.
- `main`: `nlinarith` after the `choose` values are replaced by their closed forms
  (`two_mul_choose_two`, `six_mul_choose_three`) and the needed products are supplied.
- `v_valid`: `le_best` folds `main` over `c`; below `n = 3` the bound is read off V005.

Nothing was hard; the arithmetic in `main` needed the products of the `choose` identities with
`m` and `2ⁿ⁻²` stated explicitly for `nlinarith`.

## Setup

- Tools: Claude Fable 5.1 (Claude Code), with a short consultation of GPT-6 Astra planned but
  not needed for this version; Python 3 with scipy for the `Q₃` profile enumeration and LP.
- Machine: 96 cores, 755 GB RAM, Linux 6.8.0-124-generic.
- Time spent: about two hours. Computation outside Lean: enumeration of the `4096` subgraphs of
  `Q₃` and a 5-variable LP (seconds).
