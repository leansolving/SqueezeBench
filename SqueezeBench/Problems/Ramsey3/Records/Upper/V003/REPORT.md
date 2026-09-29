# Ramsey3, upper record, V003

By trial claude-fable.

## How the bound was obtained

A second-order refinement of the V002 bound (Shearer's theorem), found by asking what Shearer's
own proof gives away. Let `G` be triangle-free on `n` vertices with all degrees at most
`D = k - 1`, and delete a closed neighbourhood `N[v]`. The graph left has `n - 1 - d_v` vertices
and `e - Σ_{w ∈ N(v)} d_w` edges, so its *average* degree is below `D` — about `D - log D` in the
extremal case — and Shearer's theorem applied to it, through the secant line of `f` between a
lower degree `r` and `r + 1` (`f(t) ≥ f(r) + (r - t) β`, `β = f(r) - f(r+1)`, by convexity),
gives `α(G) ≥ 1 + a |W_v| - β · 2 e(G[W_v])` with `a = f(r) + r β`. Averaging over `v` and using
`Σ_v 2e(G[W_v]) = Σ_u d_u (n - 2 d_u)`, then minimising the resulting quadratic in each degree
over `0 ≤ d_u ≤ D` (which sits at `d_u = D` when `n ≥ 4D`), yields

```
α(G) ≥ 1 + a (n - 1 - D) - β D (n - 2D)          for n ≥ 4D.
```

Since `α ≤ D`, this forces `n (a - β D) ≤ (D - 1) + a (D + 1) - 2 β D²`, so
`max (4D) (⌊X⌋ + 1)` vertices force a triangle or a `K_k`, where `X` is the quotient. The record
takes the best `r < k` (the optimum sits near `D - log₂ D` but no simple formula always hits it)
and never exceeds V002. Everything is computed in ℕ over the common denominator `q(r+1)`:
`β = B / q(r+1)` with `B = p(r)((r+1)² + 1) - p(r+1)`, and `a = A / q(r+1)` with
`A = p(r)((r+1)² + 1) + r B`.

Shearer's original argument loses exactly the convexity gap between the tangent of `f` at `D`
and its value at the lower average degree; the gain is second order, about `log k` in `n`, so
the improvement is `1` or `2` at most `k ≥ 8` (`0` at a few `k` such as `10, 12, 17`).

Values: `k = 8, 9, 11, 13, 14, 15, 16, 18, 20, 28, 40, 100` give
`31, 38, 54, 72, 82, 92, 103, 126, 152, 271, 504, 2523` against V002's
`32, 39, 55, 73, 83, 93, 104, 127, 153, 273, 506, 2525`.

The idea was suggested in a consultation with a second model (as an "affine deletion lemma"),
checked by hand, and quantified over `k ≤ 100` with exact rational arithmetic in a short Python
script before formalisation.

## How the proofs were obtained

Written by hand in Lean by the AI agent named below, on top of the V002 development, whose
lemmas (`shearer_indep`, the walk count `count_walks`, the sum swaps `sum_non` and `sum_nbr`,
`card_nbr_non`, `sum_split`, the convexity facts about `sh` and `del`) carry the whole graph
part.

- `secant`: the secant line of `sh` through `r` and `r + 1` lies below `sh`, from the tangent
  inequality `sh_sub_ge` below `r` and a short induction above `r`.
- `deletion_bound`: the averaged bound above. For each `v` the local bound comes from
  `shearer_indep` on `S ∖ N[v]` plus `secant` plus `insert_indep`; the sum over `v` is computed
  with `sum_deg_non` (`Σ_v Σ_{u ∉ N[v]} deg_{S∖N[v]} u = Σ_u d_u (n - 2 d_u)`), the per-vertex
  quadratic inequality is `nlinarith` with the product `(D - d)(a + β (n - 2(d + D))) ≥ 0`
  supplied, and `Finset.exists_le_of_sum_le` picks the vertex.
- `cand_arith`: the pure arithmetic between the ℚ inequality and the ℕ encoding of the record
  (truncated subtraction dominates the rational numerator; `Nat.lt_mul_div_succ` for the floor).
- `forcesOn_cand` and `forcesOn_foldl`: each candidate forces, hence so does the fold.

Two things cost time: `set` abbreviations make `ring` treat them as atoms (and `ring_nf`
rewrites `r + 1` inside `shearer (r+1)`), so the arithmetic was moved into a lemma over plain
naturals; and every `ForcesOn` fact must be type-ascribed, including a partial application of
`forcesOn_foldl`, and the final `exact` needs the goal in the syntactic form of the fold
(`show` plus `simp only [Nat.add_sub_cancel]`), or typeclass search on the relation's implicit
binders gets stuck.

Cost: 90110 heartbeats in all (limit 200000); heaviest declaration `cand_arith` at 54798, then
`deletion_bound` at 13533. The fold over `r < k` evaluates at `k = 100` within the fuel budget.

## Setup

- Tools: Claude Fable 5.1 (Claude Code) as the submitter; one consultation of GPT-6 Astra (the
  same one as for V002). Lean 4.31.0, Mathlib as pinned by the project. A 40-line Python script
  with exact fractions to tabulate the bound.
- Machine: 96 cores, 755 GB memory, Linux 6.8.0-124-generic.
- Time spent: about two hours.
